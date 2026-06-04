import Shader.MaterialX
import Shader.Vector

/-!
# All PBR + NPR shaders + vector primitives as MaterialX

The synthesis of `Shader.Toon`, `Shader.Vector` and `Shader.MaterialX` — every
shader class in the pipeline reduced to one representation:

* **PBR is MaterialX's *native* domain.** `Shader.MaterialX.convert` already maps
  a glTF PBR material to a stock `gltf_pbr` graph; nothing custom needed.
* **NPR toon shaders (MToon, SCSS) are *already* stock MaterialX** — their ramps
  are pure math (`dotproduct`, `linearstep`/`smoothstep`, `mix`), so they need
  **no** custom node and run on any conformant renderer.
* **Vector primitives that stock MaterialX can't express** (Slug's per-pixel
  curve loop, and `Splat` — bounded instance-splatting; named generically since
  "FX-Map" is an Adobe Substance trademark) become **custom nodes**
  (`<implementation file=…>`) that each ship a **stock fallback graph** (the
  in-Lean MSDF decode). Capable renderers take the custom fast path; everyone
  else gets the portable fallback.

⇒ the entire PBR + NPR + vector pipeline is representable as MaterialX, hence
emittable through `KHR_texture_procedurals` (the pure-graph parts portably; the
custom parts with graceful MSDF degradation).
-/

namespace Shader.MaterialX

/-- A MaterialX nodedef may carry a portable functional `fallback` node graph
    and/or a `native` source-code implementation. A renderer uses `native` when
    it supports the category, else `fallback`. -/
structure NodeDef where
  category : String
  fallback : Option NodeGraph := none   -- stock-MaterialX (portable) impl
  native   : Option String := none      -- custom <implementation file="…">
  deriving Inhabited

/-- Portable iff it has a stock fallback graph (runs on any renderer). -/
def NodeDef.portable (d : NodeDef) : Bool := d.fallback.isSome

/-! ## Vector primitives — custom node + stock MSDF fallback -/

/-- Portable MSDF decode: sample the baked field, reconstruct with a median,
    threshold with `smoothstep`. `median3` expands to stock `min`/`max`; the
    bake itself is `Shader.Vector.bakeMSDF` (pure Lean, no msdfgen). -/
def msdfDecodeGraph : NodeGraph :=
  ⟨[ ⟨"msdf", "image",      .color3, [.value "file" (.str "glyph.msdf")]⟩,
     ⟨"m",    "median3",    .float,  [.connect "in" "msdf"]⟩,
     ⟨"cov",  "smoothstep", .float,  [.connect "in" "m",
                                       .value "low" (.f 0.44), .value "high" (.f 0.56)]⟩ ],
    "cov"⟩

/-- **Slug** — public-domain (Mar 2026) banded-Bézier custom node; runtime in
    `Shader.Vector.slugCoverage`. Stock fallback = the MSDF graph. -/
def slug : NodeDef :=
  { category := "slug_path", native := some "slug_path.glsl", fallback := some msdfDecodeGraph }

/-- **Splat** — bounded instance-splatting (the capability Substance calls
    "FX-Map", a trademark; renamed here). A custom node; stock fallback is the
    baked MSDF atlas of the splatted result. -/
def splat : NodeDef :=
  { category := "splat", native := some "splat.glsl", fallback := some msdfDecodeGraph }

/-! ## NPR shaders — already stock MaterialX (no custom impl) -/

/-- MToon ramp: `dot → +shift → linearstep → mix(shade,lit)` (linearstep expands
    to `divide`/`clamp`). Pure stock nodes. -/
def mtoonRampGraph : NodeGraph :=
  ⟨[ ⟨"ndotl", "dotproduct", .float,  [.connect "in1" "N", .connect "in2" "L"]⟩,
     ⟨"shift", "add",        .float,  [.connect "in1" "ndotl", .value "in2" (.f 0.0)]⟩,
     ⟨"toon",  "linearstep", .float,  [.connect "in" "shift",
                                        .value "low" (.f (-0.1)), .value "high" (.f 0.1)]⟩,
     ⟨"col",   "mix",        .color3, [.connect "bg" "shadeColor",
                                        .connect "fg" "litColor", .connect "mix" "toon"]⟩ ],
    "col"⟩

def mtoon : NodeDef := { category := "mtoon", fallback := some mtoonRampGraph }

/-- SCSS crosstone: two `smoothstep` boundaries + two `mix`es (`2nd→1st→base`).
    Also pure stock nodes. -/
def scssCrosstoneGraph : NodeGraph :=
  ⟨[ ⟨"coord", "dotproduct", .float,  [.connect "in1" "N", .connect "in2" "L"]⟩,
     ⟨"t2",    "smoothstep", .float,  [.connect "in" "coord",
                                        .value "low" (.f 0.15), .value "high" (.f 0.25)]⟩,
     ⟨"t1",    "smoothstep", .float,  [.connect "in" "coord",
                                        .value "low" (.f 0.40), .value "high" (.f 0.50)]⟩,
     ⟨"s",     "mix",        .color3, [.connect "bg" "second", .connect "fg" "first",
                                        .connect "mix" "t2"]⟩,
     ⟨"col",   "mix",        .color3, [.connect "bg" "s", .connect "fg" "base",
                                        .connect "mix" "t1"]⟩ ],
    "col"⟩

def scss : NodeDef := { category := "scss", fallback := some scssCrosstoneGraph }

/-! ## PBR — MaterialX's native domain -/

/-- PBR needs no custom node: `convert` maps a glTF PBR material to a stock
    `gltf_pbr` graph (here the default material). -/
def pbr : NodeDef := { category := "gltf_pbr", fallback := some (convert {}) }

/-! ## The library + capstone theorems -/

/-- The whole PBR + NPR + vector library as MaterialX nodedefs. -/
def library : List NodeDef := [pbr, mtoon, scss, slug, splat]

/-- **Every** entry is portable: NPR shaders are pure stock graphs and each
    vector custom node carries a stock MSDF fallback. So the entire pipeline runs
    on any conformant MaterialX/`KHR_texture_procedurals` renderer. -/
theorem library_all_portable : library.all NodeDef.portable = true := by decide

/-- PBR and NPR shaders need **no** custom implementation — pure stock MaterialX. -/
theorem pbr_npr_is_pure : pbr.native = none ∧ mtoon.native = none ∧ scss.native = none :=
  ⟨rfl, rfl, rfl⟩

/-- The vector primitives *do* need a custom impl (the loop stock MaterialX
    can't express) but never lose portability — they always have a fallback. -/
theorem vector_custom_but_portable :
    (slug.native ≠ none ∧ slug.portable = true) ∧
    (splat.native ≠ none ∧ splat.portable = true) := by
  refine ⟨⟨?_, rfl⟩, ⟨?_, rfl⟩⟩ <;> simp [slug, splat]

end Shader.MaterialX

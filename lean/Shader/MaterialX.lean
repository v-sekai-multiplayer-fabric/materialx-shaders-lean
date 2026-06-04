import Shader.Toon.Math

/-!
# glTF ⇄ MaterialX (Lean 4 model)

A formalisation of the Khronos **glTF-MaterialX-Converter** mapping and the
**KHR_texture_procedurals** extension.

* A small MaterialX node-graph AST (`MtlxNode` / `NodeGraph`) — the in-memory
  shape `glTF-MaterialX-Converter` reads/writes.
* `GltfPbrMaterial` — glTF `pbrMetallicRoughness` (+ emissive/normal/occlusion).
* `convert` — glTF material → a MaterialX `gltf_pbr` surface node, the converter's
  core mapping. Each glTF input becomes either a constant value, an `image` node
  connection, or — under **KHR_texture_procedurals** — a connection to an
  embedded MaterialX node graph (the procedural *is* MaterialX, so the
  conversion is the identity on that subgraph).

References: KhronosGroup/glTF-MaterialX-Converter; KHR_texture_procedurals
(`extensions/2.0/Khronos/KHR_texture_procedurals`); MaterialX `gltf_pbr` nodedef.
-/

namespace Shader.MaterialX

open Shader.Toon (Vec3)

/-- MaterialX value types (subset the PBR mapping needs). -/
inductive MtlxType
  | float | color3 | color4 | vector3 | surfaceshader | filename
  deriving Repr, DecidableEq, Inhabited

/-- A constant input value. -/
inductive MtlxValue
  | f  (x : Float)
  | c3 (v : Vec3)
  | str (s : String)
  | none
  deriving Repr, Inhabited

/-- A node input: a constant value, or a connection to another node's output. -/
inductive MtlxInput
  | value   (name : String) (v : MtlxValue)
  | connect (name : String) (nodeName : String)
  deriving Repr, Inhabited

/-- A MaterialX node: a category (`gltf_pbr`, `image`, `multiply`, `mix`, …),
    an output type, and named inputs. -/
structure MtlxNode where
  name     : String
  category : String
  type     : MtlxType
  inputs   : List MtlxInput
  deriving Repr, Inhabited

/-- A MaterialX node graph: its nodes and the name of the output node. This is
    exactly what `KHR_texture_procedurals` embeds in a glTF document. -/
structure NodeGraph where
  nodes  : List MtlxNode
  output : String
  deriving Repr, Inhabited

/-! ## glTF side -/

/-- A glTF texture source. Normally an `image`; under **KHR_texture_procedurals**
    it is a MaterialX `NodeGraph` evaluated procedurally. -/
inductive TextureSource
  | image      (uri : String)
  | procedural (graph : NodeGraph)   -- KHR_texture_procedurals
  deriving Repr, Inhabited

/-- glTF `pbrMetallicRoughness` (+ the common additional maps). `Option` texture
    refs; `none` ⇒ the factor is used directly. -/
structure GltfPbrMaterial where
  baseColorFactor  : Vec3 := Vec3.white
  baseColorAlpha   : Float := 1.0
  baseColorTex     : Option TextureSource := Option.none
  metallicFactor   : Float := 1.0
  roughnessFactor  : Float := 1.0
  metalRoughTex    : Option TextureSource := Option.none
  emissiveFactor   : Vec3 := Vec3.black
  normalTex        : Option TextureSource := Option.none
  occlusionTex     : Option TextureSource := Option.none
  deriving Repr, Inhabited

/-! ## Conversion -/

/-- Fresh `image`/procedural nodes the conversion appends to the graph. -/
private def texNode (name : String) (src : TextureSource) : List MtlxNode :=
  match src with
  | .image uri => [⟨name, "image", .color3, [.value "file" (.str uri)]⟩]
  -- KHR_texture_procedurals: the embedded MaterialX graph is spliced in
  -- verbatim — MaterialX→MaterialX is the identity, the whole point of the ext.
  | .procedural g => g.nodes

/-- The output node name a texture source presents to the surface shader. -/
private def texOutput (name : String) (src : TextureSource) : String :=
  match src with
  | .image _ => name
  | .procedural g => g.output

/-- Build a surface input: connected to a texture/procedural node when present,
    else the constant factor. -/
private def pbrInput (inputName texName : String) (factor : MtlxValue)
    (tex : Option TextureSource) : MtlxInput :=
  match tex with
  | some src => .connect inputName (texOutput texName src)
  | Option.none => .value inputName factor

/-- The converter's core mapping: a glTF PBR material → a MaterialX `gltf_pbr`
    surface node, plus any image/procedural nodes its textures introduce. -/
def convert (m : GltfPbrMaterial) : NodeGraph :=
  let extra :=
    (m.baseColorTex.map (texNode "base_color_tex") |>.getD []) ++
    (m.metalRoughTex.map (texNode "metal_rough_tex") |>.getD []) ++
    (m.normalTex.map (texNode "normal_tex") |>.getD []) ++
    (m.occlusionTex.map (texNode "occlusion_tex") |>.getD [])
  let surf : MtlxNode :=
    { name := "SR_gltf", category := "gltf_pbr", type := .surfaceshader,
      inputs :=
        [ pbrInput "base_color" "base_color_tex" (.c3 m.baseColorFactor) m.baseColorTex
        , .value "alpha" (.f m.baseColorAlpha)
        , pbrInput "metallic" "metal_rough_tex" (.f m.metallicFactor) m.metalRoughTex
        , pbrInput "roughness" "metal_rough_tex" (.f m.roughnessFactor) m.metalRoughTex
        , .value "emissive" (.c3 m.emissiveFactor) ] }
  ⟨extra ++ [surf], "SR_gltf"⟩

/-! ## Mapping faithfulness -/

/-- The converted graph's output is always the `gltf_pbr` surface node. -/
theorem convert_output (m : GltfPbrMaterial) : (convert m).output = "SR_gltf" := rfl

/-- With no base-colour texture, `base_color` carries the glTF factor verbatim. -/
theorem base_color_is_factor (m : GltfPbrMaterial) (h : m.baseColorTex = Option.none) :
    pbrInput "base_color" "base_color_tex" (.c3 m.baseColorFactor) m.baseColorTex
      = .value "base_color" (.c3 m.baseColorFactor) := by
  simp [pbrInput, h]

/-- KHR_texture_procedurals is identity on MaterialX: a procedural base-colour
    source contributes its own graph's nodes unchanged. -/
theorem procedural_is_embedded_graph (g : NodeGraph) :
    texNode "base_color_tex" (.procedural g) = g.nodes := rfl

end Shader.MaterialX

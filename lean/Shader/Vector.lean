import Shader.Toon.Math

/-!
# Vector rendering in Lean — Slug coverage + MSDF (no external tools)

Everything here is pure Lean over Bézier outlines — no `msdfgen`, no native
library. Two consumers of the same source (`Outline`):

* **Slug** (`slugCoverage`) — exact per-pixel coverage straight from the curves
  (the now-public-domain Slug algorithm; Mar 2026). No baked texture.
* **MSDF** (`bakeMSDF` / `decodeMSDF`) — the multi-channel signed-distance bake
  (edge-colouring + per-channel nearest signed distance) and the portable decode
  (`median3` + `smoothstep`). The whole encoder is in Lean.

Both *decode* the same signed-distance shape; the only difference is Slug reads
it exactly from the curves while MSDF reads it from a baked grid. Closest-point
on a quadratic is modelled by uniform `t`-sampling (the exact solve is a cubic);
fidelity rises with `steps`.
-/

namespace Shader.Vector

open Shader.Toon (Vec3 saturate smoothstep fmin fmax)

/-! ## 2D primitives -/

structure Vec2 where
  x : Float
  y : Float
  deriving Repr

namespace Vec2
def sub (a b : Vec2) : Vec2 := ⟨a.x - b.x, a.y - b.y⟩
def dot (a b : Vec2) : Float := a.x * b.x + a.y * b.y
def cross (a b : Vec2) : Float := a.x * b.y - a.y * b.x
def len (a : Vec2) : Float := Float.sqrt (dot a a)
def dist (a b : Vec2) : Float := len (sub a b)
end Vec2

/-- A quadratic Bézier edge (TrueType outlines are quadratics). -/
structure QBezier where
  p0 : Vec2
  p1 : Vec2
  p2 : Vec2
  deriving Repr

namespace QBezier

/-- `B(t) = (1-t)²p₀ + 2(1-t)t p₁ + t²p₂`. -/
def eval (b : QBezier) (t : Float) : Vec2 :=
  let u := 1.0 - t
  ⟨u*u*b.p0.x + 2.0*u*t*b.p1.x + t*t*b.p2.x,
   u*u*b.p0.y + 2.0*u*t*b.p1.y + t*t*b.p2.y⟩

/-- `B'(t) = 2(1-t)(p₁-p₀) + 2t(p₂-p₁)`. -/
def tangent (b : QBezier) (t : Float) : Vec2 :=
  let u := 1.0 - t
  ⟨2.0*u*(b.p1.x - b.p0.x) + 2.0*t*(b.p2.x - b.p1.x),
   2.0*u*(b.p1.y - b.p0.y) + 2.0*t*(b.p2.y - b.p1.y)⟩

/-- Closest `(t, distance)` over `steps+1` uniform samples. -/
def closest (b : QBezier) (p : Vec2) (steps : Nat) : Float × Float :=
  (List.range (steps + 1)).foldl
    (fun acc i =>
      let t := Float.ofNat i / Float.ofNat steps
      let d := Vec2.dist p (b.eval t)
      if d < acc.2 then (t, d) else acc)
    (0.0, 1.0e30)

/-- Signed distance: unsigned distance, signed by the edge orientation
    (`cross(tangent, p − closest)`). -/
def signedDist (b : QBezier) (p : Vec2) (steps : Nat) : Float :=
  let (t, d) := b.closest p steps
  let c := b.eval t
  if Vec2.cross (b.tangent t) (Vec2.sub p c) < 0.0 then -d else d

end QBezier

abbrev Contour := List QBezier
abbrev Outline := List Contour

/-! ## Slug — exact per-pixel coverage -/

/-- Nearest signed distance from `p` to the whole outline (smallest `|·|`). -/
def signedDistOutline (o : Outline) (p : Vec2) (steps : Nat) : Float :=
  o.foldl
    (fun acc c => c.foldl
      (fun a e => let sd := e.signedDist p steps
                  if Float.abs sd < Float.abs a then sd else a) acc)
    1.0e30

/-- Slug coverage: a smooth boundary on the *exact* signed distance — no baked
    texture. `range` is the antialias width in the outline's units. -/
def slugCoverage (o : Outline) (p : Vec2) (steps : Nat) (range : Float) : Float :=
  saturate (0.5 - signedDistOutline o p steps / range)

/-! ## MSDF — edge colouring + per-channel signed distance (the bake) -/

/-- Which RGB channels an edge contributes its distance to. -/
structure Mask where
  r : Bool
  g : Bool
  b : Bool
  deriving Repr, DecidableEq

/-- Rotate the channel mask at a corner: `(r,g,b) ↦ (b,r,g)` cycles RG→GB→BR. -/
def Mask.rotate (m : Mask) : Mask := ⟨m.b, m.r, m.g⟩

/-- Colour a contour: keep the mask across smooth joins, rotate it at a corner
    (tangent turn sharper than `cosThresh`). The msdfgen idea, minimal form. -/
def colorContour : Contour → Option QBezier → Mask → Float → List (QBezier × Mask)
  | [], _, _, _ => []
  | e :: rest, prev, m, cosThresh =>
    let m' :=
      match prev with
      | none => m
      | some pe =>
        let t1 := pe.tangent 1.0
        let t2 := e.tangent 0.0
        let d := Vec2.dot t1 t2 / (Vec2.len t1 * Vec2.len t2 + 1.0e-9)
        if d < cosThresh then m.rotate else m
    (e, m') :: colorContour rest (some e) m' cosThresh

/-- Colour every contour of an outline (start mask = RG). -/
def colorOutline (o : Outline) (cosThresh : Float := 0.99) : List (QBezier × Mask) :=
  (o.map (fun c => colorContour c none ⟨true, true, false⟩ cosThresh)).flatten

/-- Nearest signed distance among the edges that include channel `pick`. -/
def channelSD (edges : List (QBezier × Mask)) (p : Vec2) (steps : Nat)
    (pick : Mask → Bool) : Float :=
  edges.foldl
    (fun acc em =>
      if pick em.2 then
        let sd := em.1.signedDist p steps
        if Float.abs sd < Float.abs acc then sd else acc
      else acc)
    1.0e30

/-- The MSDF triple at a point: per-channel nearest signed distance, mapped into
    `[0,1]` by the field `range` (`0.5 + sd/range`). -/
def msdfAt (edges : List (QBezier × Mask)) (p : Vec2) (steps : Nat)
    (range : Float) : Vec3 :=
  ⟨ saturate (0.5 + channelSD edges p steps (·.r) / range),
    saturate (0.5 + channelSD edges p steps (·.g) / range),
    saturate (0.5 + channelSD edges p steps (·.b) / range) ⟩

/-- Bake an MSDF grid (`w×h`) over the box `[lo,hi]` — the whole encoder, in
    Lean. Row-major list of texels. -/
def bakeMSDF (edges : List (QBezier × Mask)) (w h : Nat) (lo hi : Vec2)
    (steps : Nat) (range : Float) : List (List Vec3) :=
  (List.range h).map fun j =>
    (List.range w).map fun i =>
      let u := (Float.ofNat i + 0.5) / Float.ofNat w
      let v := (Float.ofNat j + 0.5) / Float.ofNat h
      msdfAt edges ⟨lo.x + u*(hi.x-lo.x), lo.y + v*(hi.y-lo.y)⟩ steps range

/-! ## MSDF — decode (the portable runtime side) -/

/-- Median of three (the MSDF reconstruction operator). -/
def med3 (a b c : Float) : Float :=
  fmax (fmin a b) (fmin (fmax a b) c)

/-- Decode an MSDF texel to crisp coverage: `smoothstep` around `0.5` of the
    median. This is the part expressible as a *portable* MaterialX node graph. -/
def decodeMSDF (sample : Vec3) (smoothing : Float := 0.06) : Float :=
  smoothstep (0.5 - smoothing) (0.5 + smoothing) (med3 sample.x sample.y sample.z)

/-- A degenerate single-edge outline has all three MSDF channels equal, so the
    median is that channel and MSDF degrades to a plain SDF — the documented
    “MSDF needs ≥2 channels of corner info” boundary case. -/
theorem med3_eq_of_all_eq (x : Float) : med3 x x x = x := by
  simp [med3, fmin, fmax]

end Shader.Vector

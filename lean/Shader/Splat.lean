import Shader.Vector

/-!
# Splat — bounded instance-splatting (the algorithm)

The semantics behind the `splat` MaterialX custom node: place a `shape` at each
of a **finite** list of `Instance`s (affine placements) and take the union
(`max`) of their coverage. Because the instance list is fixed-length, `splatEval`
is a fold over a finite list — i.e. **unrollable to a loop-free graph**, which is
exactly why stock MaterialX (no iteration) needs this as a custom node, and why a
fixed-budget version still has a portable fallback.

("Splat" is our untrademarked name for the capability Substance calls "FX-Map".)
-/

namespace Shader.Splat

open Shader.Vector (Vec2)
open Shader.Toon (fmax)

/-- An affine instance placement (axis-aligned scale + translation). -/
structure Instance where
  tx : Float := 0.0
  ty : Float := 0.0
  sx : Float := 1.0
  sy : Float := 1.0
  deriving Repr, Inhabited

/-- Map a world point into this instance's local frame. -/
def Instance.toLocal (i : Instance) (p : Vec2) : Vec2 :=
  ⟨(p.x - i.tx) / i.sx, (p.y - i.ty) / i.sy⟩

/-- Splat: union (max coverage) of `shape` placed at every instance. `shape` is
    coverage/SDF evaluated in an instance's local space — e.g. a unit circle, or
    `Shader.Vector.slugCoverage` of an outline. -/
def splatEval (instances : List Instance) (shape : Vec2 → Float) (p : Vec2) : Float :=
  instances.foldl (fun acc i => fmax acc (shape (i.toLocal p))) 0.0

/-- The empty splat is empty everywhere. -/
@[simp] theorem splatEval_nil (shape : Vec2 → Float) (p : Vec2) :
    splatEval [] shape p = 0.0 := rfl

/-- A single instance is just the shape in that instance's local frame, unioned
    with the empty background. -/
theorem splatEval_single (i : Instance) (shape : Vec2 → Float) (p : Vec2) :
    splatEval [i] shape p = fmax 0.0 (shape (i.toLocal p)) := rfl

/-- Splatting is the left fold, so a cons unfolds one instance at a time —
    the structural witness that an N-instance splat unrolls to N `max` steps. -/
theorem splatEval_cons (i : Instance) (rest : List Instance)
    (shape : Vec2 → Float) (p : Vec2) :
    splatEval (i :: rest) shape p
      = rest.foldl (fun acc j => fmax acc (shape (j.toLocal p)))
          (fmax 0.0 (shape (i.toLocal p))) := rfl

end Shader.Splat

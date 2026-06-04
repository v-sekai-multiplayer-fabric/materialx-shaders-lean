import Shader.MaterialXNPR

/-!
# A node-graph evaluator — structural ⇒ semantic

`Shader.MaterialXNPR` builds the MToon / SCSS / MSDF node graphs and proves
*structural* facts (portability). This module gives a small **interpreter** over
the node subset they use (`dotproduct`, `add`, `linearstep`, `smoothstep`, `mix`,
`median3`, `image`) and proves each graph **evaluates to its `Shader.Toon` /
`Shader.Vector` reference function** — promoting the structural claim to a
semantic one. (Codegen MaterialX↔Slang lives elsewhere; this is just denotation.)
-/

namespace Shader.MaterialX

open Shader.Toon
open Shader.Vector (med3)

/-- A value on a graph wire. -/
inductive Val where
  | f (x : Float)
  | c (v : Vec3)
  deriving Inhabited

def Val.toF : Val → Float | .f x => x | .c v => v.x
def Val.toC : Val → Vec3  | .c v => v | .f x => ⟨x, x, x⟩

/-- Interface inputs and node outputs, by name. -/
abbrev Env := String → Val

def MtlxValue.toVal : MtlxValue → Val
  | .f x  => .f x
  | .c3 v => .c v
  | _     => .f 0.0

/-- Resolve one input: a literal is its value, a connection reads the env. -/
def inputVal (env : Env) : MtlxInput → String × Val
  | .value n v       => (n, v.toVal)
  | .connect n which => (n, env which)

/-- Look up a resolved input by port name. -/
def arg (args : List (String × Val)) (name : String) : Val :=
  match args.find? (fun a => a.1 == name) with
  | some a => a.2
  | none   => .f 0.0

/-- Evaluate one node category over its resolved inputs (stock-MaterialX subset). -/
def evalCat (cat : String) (a : List (String × Val)) : Val :=
  if cat == "dotproduct" then .f (Vec3.dot (arg a "in1").toC (arg a "in2").toC)
  else if cat == "add" then .f ((arg a "in1").toF + (arg a "in2").toF)
  else if cat == "linearstep" then
    .f (linearstep (arg a "low").toF (arg a "high").toF (arg a "in").toF)
  else if cat == "smoothstep" then
    .f (smoothstep (arg a "low").toF (arg a "high").toF (arg a "in").toF)
  else if cat == "mix" then
    .c (lerp3 (arg a "bg").toC (arg a "fg").toC (arg a "mix").toF)
  else if cat == "median3" then
    let v := (arg a "in").toC; .f (med3 v.x v.y v.z)
  else .f 0.0

/-- Evaluate a graph: fold the (dependency-ordered) nodes, keying each output by
    node name. An `image` node pulls its sampled value from `env0` by name (the
    texture sample is an input to the procedural evaluation). -/
def evalGraph (g : NodeGraph) (env0 : Env) : Val :=
  (g.nodes.foldl
    (fun env node =>
      let out :=
        if node.category == "image" then env0 node.name
        else evalCat node.category (node.inputs.map (inputVal env))
      fun nm => if nm == node.name then out else env nm)
    env0) g.output

/-! ## Equivalences: each graph = its reference function -/

/-- The MToon ramp graph denotes `mix(shade, lit, linearstep(…, N·L + shift))`,
    i.e. `Shader.Toon`'s `toonBase` over the spec ramp. -/
theorem eval_mtoonRamp (env : Env) :
    evalGraph mtoonRampGraph env =
      .c (lerp3 (env "shadeColor").toC (env "litColor").toC
            (linearstep (-0.1) 0.1 (Vec3.dot (env "N").toC (env "L").toC + 0.0))) := by
  simp [evalGraph, mtoonRampGraph, evalCat, inputVal, arg, MtlxValue.toVal,
        Val.toF, Val.toC]

/-- The SCSS crosstone graph denotes the two-`smoothstep` / two-`mix` layering of
    `Shader.Toon`'s `crosstone` (`2nd → 1st → base`). -/
theorem eval_scssCrosstone (env : Env) :
    evalGraph scssCrosstoneGraph env =
      .c (lerp3 (lerp3 (env "second").toC (env "first").toC
                  (smoothstep 0.15 0.25 (Vec3.dot (env "N").toC (env "L").toC)))
            (env "base").toC
            (smoothstep 0.40 0.50 (Vec3.dot (env "N").toC (env "L").toC))) := by
  simp [evalGraph, scssCrosstoneGraph, evalCat, inputVal, arg, MtlxValue.toVal,
        Val.toF, Val.toC]

/-- The MSDF decode graph denotes `median3` of the sampled texel thresholded by
    `smoothstep 0.44 0.56` — i.e. `Shader.Vector.decodeMSDF` at smoothing `0.06`
    (`0.5 ∓ 0.06`), written here with the graph's literal edges. -/
theorem eval_msdfDecode (env : Env) :
    evalGraph msdfDecodeGraph env =
      .f (smoothstep 0.44 0.56
            (med3 (env "msdf").toC.x (env "msdf").toC.y (env "msdf").toC.z)) := by
  simp [evalGraph, msdfDecodeGraph, evalCat, inputVal, arg, MtlxValue.toVal,
        Val.toF, Val.toC]

end Shader.MaterialX

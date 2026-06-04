# materialx-shaders (Lean 4)

A Lean 4 formalization that models **PBR, NPR, and vector** shaders under a
single representation: **MaterialX**.

* `Shader/Toon/MToon.lean` — VRM **MToon** (UniVRM / three-vrm 1.0 ramp vs the
  legacy 0.x ramp used by godot-vrm).
* `Shader/Toon/SCSS.lean` — Silent's **SCSS / Crosstone** (Unity) + its Godot port.
* `Shader/Vector.lean` — **Slug** exact coverage + **MSDF** bake/decode, all in
  Lean (no `msdfgen`), over shared Bézier outlines.
* `Shader/MaterialX.lean` — glTF ⇄ MaterialX (`KHR_texture_procedurals`).
* `Shader/MaterialXNPR.lean` — the capstone: **PBR + NPR are stock MaterialX
  node graphs; Slug / Splat are custom nodes with a stock MSDF fallback** — so
  the whole pipeline is portable MaterialX.

`Splat` is our (untrademarked) name for the bounded instance-splatting primitive.

```
lake build
```

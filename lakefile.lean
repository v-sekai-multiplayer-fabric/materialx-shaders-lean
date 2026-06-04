import Lake
open Lake DSL

package «materialx-shaders» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «MtlxShader» where
  srcDir := "lean"
  globs  := #[.andSubmodules `Shader]

import Lake
open Lake DSL

package «carmichael» where
  -- 项目基础配置

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

@[default_target]
lean_lib «Carmichael» where

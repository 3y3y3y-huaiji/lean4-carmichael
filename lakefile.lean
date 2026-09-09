import Lake
open Lake DSL

package «ai_for_math» where
  -- 项目基础配置

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

@[default_target]
lean_lib «AiForMath» where
  -- 库配置

lean_lib «Sylvester» where

@[default_target]
lean_lib «Carmichael» where


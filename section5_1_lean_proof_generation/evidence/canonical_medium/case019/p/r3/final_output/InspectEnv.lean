import Stage3Model
open Lean
elab "#list_genlimit" : command => do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "GenLimit" || name.toString.startsWith "Stage3Case019" then
      logInfo m!"{name} : {info.type}"
#list_genlimit

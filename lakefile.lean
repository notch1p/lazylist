import Lake
open Lake DSL

package "lazylist" where
  version := v!"0.1.0"

@[default_target]
lean_lib «Lazylist» where
  -- add library configuration options here

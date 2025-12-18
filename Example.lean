import Lustrean

set_option trace.Lustrean.Elab.Compile true

lustre (domain := Sign)
  node u(x) = o
  guard x ≥ 0
  where
    o = x + 1
  assert
    o ≥ 1

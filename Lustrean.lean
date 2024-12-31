-- This module serves as the root of the `Lustrean` library.
-- Import modules here that should be built as part of the library.
import Lustrean.Domain
import Lustrean.Interpreter
import Lustrean.Parsing.Elaboration

lustre
  node u(x) = o
    guard
      -- x + 2 ≥ 8
    where
      o = x
    assert
      x ≤ 0

lustre
  node f(c, z) = y
    guard
      z = 3
    where
      y = if c = 0 then x else z
      x = if c = 0 then z else y
    assert
      y = x

lustre
  node f() = x where
    x = y
    y = x

lustre
  node f(x) = o
    guard
      x ≥ 0
    where
      o = if x > 3 then 3 else x
    assert
      0 ≤ o
      o ≤ 3

lustre
  node f() = o, o where
    o = o
  -- node u(x) = o where
  --   o = 0 fby x

  -- node f(x) = o
  --   guard
  --     x ≥ 0
  --   where
  --     o = if x > 3 then 3 else x
  --   assert
  --     0 ≤ x ∧ x ≤ 4

  -- node g() = o where
  --   o = f(5) + f(5)

  node h() = o, i where
    o = 0 fby 1 fby i+1
    i =
      if o = 5 then
        o + if 0 ≠ 0 then 1 else 2
      else
        0

-- lustre
--   node e₁(x) = o
--     guard
--       x ≥ 0
--     where
--       o = 3 + x * [2, ∞]
--     assert
--       o ≠ 0

--   node e₂(x) = o where
--     v = e₁(x)
--     o = v + v

--   node e₃(x) = o where
--     v = e₂(x)
--     o = v + v

--   node e₄(x) = o
--     guard
--       x ≥ 0
--     where
--       o = v + v
--       v = e₃(x)
--     assert
--       o ≥ 0

--   -- node main() = o where
--   --   o = e₄(5)


-- lustre
--   node a() = o₁, o₂ where
--     o₁ = 3
--     o₂ = 5

--   node b() = o₁ where
--     o₁, o₂ = a()

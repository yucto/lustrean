import Lustrean

lustre
  node u(x) = o where
    o = x * x + 3
  assert
    o ≤ 1

lustre
  node u(x) = o where
    -- o = if x ≥ 0 then x * x else x * x
    o = x * x
  assert
    o ≥ 0

lustre
  node f() = x where
    x = y
    y = x

lustre
  node f(c, z) = y where
    x = if c = 0 then z else y
    y = if c = 0 then x else z

lustre
  node l() = o where
    up = 1 fby if (up = 1 ∧ o < 10) ∨ (up = 0 ∧ o = 0) then 1 else 0
    o = 0 fby if up = 1 then o + 1 else o - 1
  assert
    0 ≤ o

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

  node u(x) = o where
    o = 0 fby x

  -- shadowing
  node f(x) = o
    guard
      x ≥ 0
    where
      o = if x > 3 then 3 else x
    assert
      0 ≤ x
      x ≤ 4

  node g() = o where
    o = f(5) + f(5)

  node h() = o, i where
    o = 0 fby 1 fby i+1
    i =
      if o = 5 then
        if 0 ≠ 0 then 1 else 2
      else
        0

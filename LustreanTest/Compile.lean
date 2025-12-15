import Lustrean

set_option trace.Lustrean.Elab.Compile true

/--
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node inc(x) = o
      where ⏎
        o = (x + [1, 1])
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_12
    node f_2 where
      x_2 := nil ⇒ f_3
    node f_3 where
      x_3 := x_2 ⇒ f_4
    node f_4 where
      x_1 := [-∞, ∞] ⇒ f_5
    node f_5 where
      x_2 := nil ⇒ f_6
    node f_6 where
      x_2 := (x_1 + [1, 1]) ⇒ f_7
    node f_7 where
      skip ⇒ f_6
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_8
    node f_8 where
      x_3 := x_2 ⇒ f_9
    node f_9 where
      x_1 := [-∞, ∞] ⇒ f_10
    node f_10 where
      x_2 := (x_1 + [1, 1]) ⇒ f_11
    node f_11 where
      step := (step + [1, 1]) ⇒ f_8
      skip ⇒ f_10
      skip ⇒ f_12
    node f_12 where
      ⏎
[Lustrean.Elab.Compile] ✅️ elabExpr
    node plus2(x) = o
      where ⏎
        o.0.x.1.x = x
        o.0.x.1.o = (o.0.x.1.x + [1, 1])
        o.0.x = o.0.x.1.o
        o.0.o = (o.0.x + [1, 1])
        o = o.0.o
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_36
    node f_2 where
      x_2 := nil ⇒ f_3
    node f_3 where
      x_3 := nil ⇒ f_4
    node f_4 where
      x_4 := nil ⇒ f_5
    node f_5 where
      x_5 := nil ⇒ f_6
    node f_6 where
      x_6 := nil ⇒ f_7
    node f_7 where
      x_7 := x_2 ⇒ f_8
    node f_8 where
      x_8 := x_3 ⇒ f_9
    node f_9 where
      x_9 := x_4 ⇒ f_10
    node f_10 where
      x_10 := x_5 ⇒ f_11
    node f_11 where
      x_11 := x_6 ⇒ f_12
    node f_12 where
      x_1 := [-∞, ∞] ⇒ f_13
    node f_13 where
      x_2 := nil ⇒ f_14
    node f_14 where
      x_3 := nil ⇒ f_15
    node f_15 where
      x_4 := nil ⇒ f_16
    node f_16 where
      x_5 := nil ⇒ f_17
    node f_17 where
      x_6 := nil ⇒ f_18
    node f_18 where
      x_2 := x_1 ⇒ f_19
    node f_19 where
      x_3 := (x_2 + [1, 1]) ⇒ f_20
    node f_20 where
      x_4 := x_3 ⇒ f_21
    node f_21 where
      x_5 := (x_4 + [1, 1]) ⇒ f_22
    node f_22 where
      x_6 := x_5 ⇒ f_23
    node f_23 where
      skip ⇒ f_18
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_24
    node f_24 where
      x_7 := x_2 ⇒ f_25
    node f_25 where
      x_8 := x_3 ⇒ f_26
    node f_26 where
      x_9 := x_4 ⇒ f_27
    node f_27 where
      x_10 := x_5 ⇒ f_28
    node f_28 where
      x_11 := x_6 ⇒ f_29
    node f_29 where
      x_1 := [-∞, ∞] ⇒ f_30
    node f_30 where
      x_2 := x_1 ⇒ f_31
    node f_31 where
      x_3 := (x_2 + [1, 1]) ⇒ f_32
    node f_32 where
      x_4 := x_3 ⇒ f_33
    node f_33 where
      x_5 := (x_4 + [1, 1]) ⇒ f_34
    node f_34 where
      x_6 := x_5 ⇒ f_35
    node f_35 where
      step := (step + [1, 1]) ⇒ f_24
      skip ⇒ f_30
      skip ⇒ f_36
    node f_36 where
-/
#guard_msgs in
lustre
  node inc(x) = o where
    o = x + 1

  node plus2(x) = o where
    o = inc(inc(x))

/--
error: assert failed, got #[[1; +∞], [-∞; +∞], [2; +∞], [-∞; +∞]]
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node u(x) = o
      where ⏎
        o = ((x * x) + [3, 3])
      assert
        (o ≤ [1, 1])
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_13
    node f_2 where
      x_2 := nil ⇒ f_3
    node f_3 where
      x_3 := x_2 ⇒ f_4
    node f_4 where
      x_1 := [-∞, ∞] ⇒ f_5
    node f_5 where
      x_2 := nil ⇒ f_6
    node f_6 where
      x_2 := ((x_1 * x_1) + [3, 3]) ⇒ f_7
    node f_7 where
      skip ⇒ f_6
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_8
    node f_8 where
      x_3 := x_2 ⇒ f_9
    node f_9 where
      x_1 := [-∞, ∞] ⇒ f_10
    node f_10 where
      x_2 := ((x_1 * x_1) + [3, 3]) ⇒ f_11
    node f_11 where
      step := (step + [1, 1]) ⇒ f_8
      skip ⇒ f_10
      skip ⇒ f_12
    node f_12 where
      assert (x_2 ≤ [1, 1]) ⇒ f_13
    node f_13 where
-/
#guard_msgs in
lustre
  node u(x) = o where
    o = x * x + 3
  assert
    o ≤ 1

/--
error: assert failed, got #[[1; +∞], [-∞; +∞], [-∞; -1], [-∞; +∞]]
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node u(x) = o
      where ⏎
        o = (x * x)
      assert
        ([0, 0] ≤ o)
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_13
    node f_2 where
      x_2 := nil ⇒ f_3
    node f_3 where
      x_3 := x_2 ⇒ f_4
    node f_4 where
      x_1 := [-∞, ∞] ⇒ f_5
    node f_5 where
      x_2 := nil ⇒ f_6
    node f_6 where
      x_2 := (x_1 * x_1) ⇒ f_7
    node f_7 where
      skip ⇒ f_6
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_8
    node f_8 where
      x_3 := x_2 ⇒ f_9
    node f_9 where
      x_1 := [-∞, ∞] ⇒ f_10
    node f_10 where
      x_2 := (x_1 * x_1) ⇒ f_11
    node f_11 where
      step := (step + [1, 1]) ⇒ f_8
      skip ⇒ f_10
      skip ⇒ f_12
    node f_12 where
      assert ([0, 0] ≤ x_2) ⇒ f_13
    node f_13 where
      ⏎
[Lustrean.Elab.Compile] ✅️ elabExpr
    node v(x)
      where ⏎
        x2 = (if ([0, 0] ≤ x) then (x * x) else (x * x))
        o = (x2 + [3, 3])
      assert
        ([3, 3] ≤ o)
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_23
    node f_2 where
      x_2 := nil ⇒ f_3
    node f_3 where
      x_3 := nil ⇒ f_4
    node f_4 where
      x_4 := x_2 ⇒ f_5
    node f_5 where
      x_5 := x_3 ⇒ f_6
    node f_6 where
      x_1 := [-∞, ∞] ⇒ f_7
    node f_7 where
      x_2 := nil ⇒ f_8
    node f_8 where
      x_3 := nil ⇒ f_9
    node f_9 where
      guard ([0, 0] ≤ x_1) ⇒ f_10
      guard ([0, 0] > x_1) ⇒ f_11
    node f_10 where
      x_2 := (x_1 * x_1) ⇒ f_12
    node f_11 where
      x_2 := (x_1 * x_1) ⇒ f_12
    node f_12 where
      x_3 := (x_2 + [3, 3]) ⇒ f_13
    node f_13 where
      skip ⇒ f_9
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_14
    node f_14 where
      x_4 := x_2 ⇒ f_15
    node f_15 where
      x_5 := x_3 ⇒ f_16
    node f_16 where
      x_1 := [-∞, ∞] ⇒ f_17
    node f_17 where
      guard ([0, 0] ≤ x_1) ⇒ f_18
      guard ([0, 0] > x_1) ⇒ f_19
    node f_18 where
      x_2 := (x_1 * x_1) ⇒ f_20
    node f_19 where
      x_2 := (x_1 * x_1) ⇒ f_20
    node f_20 where
      x_3 := (x_2 + [3, 3]) ⇒ f_21
    node f_21 where
      step := (step + [1, 1]) ⇒ f_14
      skip ⇒ f_17
      skip ⇒ f_22
    node f_22 where
      assert ([3, 3] ≤ x_3) ⇒ f_23
    node f_23 where
-/
#guard_msgs in
lustre
  node u(x) = o where
    -- o = if x ≥ 0 then x * x else x * x
    o = x * x
  assert
    o ≥ 0

  node v(x) where
    x2 = if x ≥ 0 then x * x else x * x
    o = x2 + 3
  assert
    o ≥ 3

/--
error: variable x could be nil
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node f() = x
      where ⏎
        x = y
        y = x
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_16
    node f_2 where
      x_1 := nil ⇒ f_3
    node f_3 where
      x_2 := nil ⇒ f_4
    node f_4 where
      x_3 := x_1 ⇒ f_5
    node f_5 where
      x_4 := x_2 ⇒ f_6
    node f_6 where
      x_1 := nil ⇒ f_7
    node f_7 where
      x_2 := nil ⇒ f_8
    node f_8 where
      x_1 := x_2 ⇒ f_9
    node f_9 where
      x_2 := x_1 ⇒ f_10
    node f_10 where
      skip ⇒ f_8
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_11
    node f_11 where
      x_3 := x_1 ⇒ f_12
    node f_12 where
      x_4 := x_2 ⇒ f_13
    node f_13 where
      x_1 := x_2 ⇒ f_14
    node f_14 where
      x_2 := x_1 ⇒ f_15
    node f_15 where
      step := (step + [1, 1]) ⇒ f_11
      skip ⇒ f_13
      skip ⇒ f_16
    node f_16 where
-/
#guard_msgs in
lustre
  node f() = x where
    x = y
    y = x

/--
error: variable x could be nil
---
error: variable y could be nil
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node f(c,z) = x,y
      where ⏎
        x = (if (c = [0, 0]) then z else y)
        y = (if (c = [0, 0]) then x else z)
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_28
    node f_2 where
      x_3 := nil ⇒ f_3
    node f_3 where
      x_4 := nil ⇒ f_4
    node f_4 where
      x_5 := x_3 ⇒ f_5
    node f_5 where
      x_6 := x_4 ⇒ f_6
    node f_6 where
      x_1 := [-∞, ∞] ⇒ f_7
    node f_7 where
      x_2 := [-∞, ∞] ⇒ f_8
    node f_8 where
      x_3 := nil ⇒ f_9
    node f_9 where
      x_4 := nil ⇒ f_10
    node f_10 where
      guard (x_1 = [0, 0]) ⇒ f_11
      guard (x_1 ≠ [0, 0]) ⇒ f_12
    node f_11 where
      x_3 := x_2 ⇒ f_13
    node f_12 where
      x_3 := x_4 ⇒ f_13
    node f_13 where
      guard (x_1 = [0, 0]) ⇒ f_14
      guard (x_1 ≠ [0, 0]) ⇒ f_15
    node f_14 where
      x_4 := x_3 ⇒ f_16
    node f_15 where
      x_4 := x_2 ⇒ f_16
    node f_16 where
      skip ⇒ f_10
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_17
    node f_17 where
      x_5 := x_3 ⇒ f_18
    node f_18 where
      x_6 := x_4 ⇒ f_19
    node f_19 where
      x_1 := [-∞, ∞] ⇒ f_20
    node f_20 where
      x_2 := [-∞, ∞] ⇒ f_21
    node f_21 where
      guard (x_1 = [0, 0]) ⇒ f_22
      guard (x_1 ≠ [0, 0]) ⇒ f_23
    node f_22 where
      x_3 := x_2 ⇒ f_24
    node f_23 where
      x_3 := x_4 ⇒ f_24
    node f_24 where
      guard (x_1 = [0, 0]) ⇒ f_25
      guard (x_1 ≠ [0, 0]) ⇒ f_26
    node f_25 where
      x_4 := x_3 ⇒ f_27
    node f_26 where
      x_4 := x_2 ⇒ f_27
    node f_27 where
      step := (step + [1, 1]) ⇒ f_17
      skip ⇒ f_21
      skip ⇒ f_28
    node f_28 where
-/
#guard_msgs in
lustre
  -- this would require a relational domain
  node f(c, z) = x, y where
    x = if c = 0 then z else y
    y = if c = 0 then x else z


/--
error: assert failed, got #[[1; +∞], [-∞; 1], [-∞; -1], [-∞; 1], [-∞; +∞], [-∞; 1], [-∞; +∞], [-∞; 1], [-∞; +∞]]
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node l() = o
      where ⏎
        up = (if (step = [0, 0]) then [1, 1] else (pre x_0))
        o = (if (step = [0, 0]) then [0, 0] else (pre x_1))
        x_0 = (if (((up = [1, 1]) ∧ (o < [10, 10])) ∨ ((up = [0, 0]) ∧ (o = [0, 0]))) then [1, 1] else [0, 0])
        x_1 = (if (up = [1, 1]) then (o + [1, 1]) else (o - [1, 1]))
      assert
        ([0, 0] ≤ o)
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_45
    node f_2 where
      x_1 := nil ⇒ f_3
    node f_3 where
      x_2 := nil ⇒ f_4
    node f_4 where
      x_3 := nil ⇒ f_5
    node f_5 where
      x_4 := nil ⇒ f_6
    node f_6 where
      x_5 := x_1 ⇒ f_7
    node f_7 where
      x_6 := x_2 ⇒ f_8
    node f_8 where
      x_7 := x_3 ⇒ f_9
    node f_9 where
      x_8 := x_4 ⇒ f_10
    node f_10 where
      x_1 := nil ⇒ f_11
    node f_11 where
      x_2 := nil ⇒ f_12
    node f_12 where
      x_3 := nil ⇒ f_13
    node f_13 where
      x_4 := nil ⇒ f_14
    node f_14 where
      guard (step = [0, 0]) ⇒ f_15
      guard (step ≠ [0, 0]) ⇒ f_16
    node f_15 where
      x_1 := [1, 1] ⇒ f_17
    node f_16 where
      x_1 := x_7 ⇒ f_17
    node f_17 where
      guard (step = [0, 0]) ⇒ f_18
      guard (step ≠ [0, 0]) ⇒ f_19
    node f_18 where
      x_2 := [0, 0] ⇒ f_20
    node f_19 where
      x_2 := x_8 ⇒ f_20
    node f_20 where
      guard (((x_1 = [1, 1]) && (x_2 < [10, 10])) || ((x_1 = [0, 0]) && (x_2 = [0, 0]))) ⇒ f_21
      guard (((x_1 ≠ [1, 1]) || (x_2 ≥ [10, 10])) && ((x_1 ≠ [0, 0]) || (x_2 ≠ [0, 0]))) ⇒ f_22
    node f_21 where
      x_3 := [1, 1] ⇒ f_23
    node f_22 where
      x_3 := [0, 0] ⇒ f_23
    node f_23 where
      guard (x_1 = [1, 1]) ⇒ f_24
      guard (x_1 ≠ [1, 1]) ⇒ f_25
    node f_24 where
      x_4 := (x_2 + [1, 1]) ⇒ f_26
    node f_25 where
      x_4 := (x_2 - [1, 1]) ⇒ f_26
    node f_26 where
      skip ⇒ f_14
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_27
    node f_27 where
      x_5 := x_1 ⇒ f_28
    node f_28 where
      x_6 := x_2 ⇒ f_29
    node f_29 where
      x_7 := x_3 ⇒ f_30
    node f_30 where
      x_8 := x_4 ⇒ f_31
    node f_31 where
      guard (step = [0, 0]) ⇒ f_32
      guard (step ≠ [0, 0]) ⇒ f_33
    node f_32 where
      x_1 := [1, 1] ⇒ f_34
    node f_33 where
      x_1 := x_7 ⇒ f_34
    node f_34 where
      guard (step = [0, 0]) ⇒ f_35
      guard (step ≠ [0, 0]) ⇒ f_36
    node f_35 where
      x_2 := [0, 0] ⇒ f_37
    node f_36 where
      x_2 := x_8 ⇒ f_37
    node f_37 where
      guard (((x_1 = [1, 1]) && (x_2 < [10, 10])) || ((x_1 = [0, 0]) && (x_2 = [0, 0]))) ⇒ f_38
      guard (((x_1 ≠ [1, 1]) || (x_2 ≥ [10, 10])) && ((x_1 ≠ [0, 0]) || (x_2 ≠ [0, 0]))) ⇒ f_39
    node f_38 where
      x_3 := [1, 1] ⇒ f_40
    node f_39 where
      x_3 := [0, 0] ⇒ f_40
    node f_40 where
      guard (x_1 = [1, 1]) ⇒ f_41
      guard (x_1 ≠ [1, 1]) ⇒ f_42
    node f_41 where
      x_4 := (x_2 + [1, 1]) ⇒ f_43
    node f_42 where
      x_4 := (x_2 - [1, 1]) ⇒ f_43
    node f_43 where
      step := (step + [1, 1]) ⇒ f_27
      skip ⇒ f_31
      skip ⇒ f_44
    node f_44 where
      assert ([0, 0] ≤ x_2) ⇒ f_45
    node f_45 where
-/
#guard_msgs in
lustre
  node l() = o where
    up = 1 fby if (up = 1 ∧ o < 10) ∨ (up = 0 ∧ o = 0) then 1 else 0
    o = 0 fby if up = 1 then o + 1 else o - 1
  assert
    0 ≤ o

/--
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node f(x) = o
      guard
        ([0, 0] ≤ x)
      where ⏎
        o = (if ([3, 3] < x) then [3, 3] else x)
      assert
        ([0, 0] ≤ o)
        (o ≤ [3, 3])
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_20
    node f_2 where
      x_2 := nil ⇒ f_3
    node f_3 where
      x_3 := x_2 ⇒ f_4
    node f_4 where
      x_1 := [-∞, ∞] ⇒ f_5
    node f_5 where
      guard ([0, 0] ≤ x_1) ⇒ f_6
    node f_6 where
      x_2 := nil ⇒ f_7
    node f_7 where
      guard ([3, 3] < x_1) ⇒ f_8
      guard ([3, 3] ≥ x_1) ⇒ f_9
    node f_8 where
      x_2 := [3, 3] ⇒ f_10
    node f_9 where
      x_2 := x_1 ⇒ f_10
    node f_10 where
      skip ⇒ f_7
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_11
    node f_11 where
      x_3 := x_2 ⇒ f_12
    node f_12 where
      x_1 := [-∞, ∞] ⇒ f_13
    node f_13 where
      guard ([0, 0] ≤ x_1) ⇒ f_14
    node f_14 where
      guard ([3, 3] < x_1) ⇒ f_15
      guard ([3, 3] ≥ x_1) ⇒ f_16
    node f_15 where
      x_2 := [3, 3] ⇒ f_17
    node f_16 where
      x_2 := x_1 ⇒ f_17
    node f_17 where
      step := (step + [1, 1]) ⇒ f_11
      skip ⇒ f_14
      skip ⇒ f_18
    node f_18 where
      assert ([0, 0] ≤ x_2) ⇒ f_19
    node f_19 where
      assert (x_2 ≤ [3, 3]) ⇒ f_20
    node f_20 where
      ⏎
[Lustrean.Elab.Compile] ✅️ elabExpr
    node g(x) = o
      guard
        ([0, 0] ≤ x)
      where ⏎
        y = (if (step = [0, 0]) then x else (pre x_0))
        o = (if ([3, 3] < y) then [3, 3] else y)
        x_0 = (y + [1, 1])
      assert
        ([0, 0] ≤ o)
        (o ≤ [3, 3])
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_36
    node f_2 where
      x_2 := nil ⇒ f_3
    node f_3 where
      x_3 := nil ⇒ f_4
    node f_4 where
      x_4 := nil ⇒ f_5
    node f_5 where
      x_5 := x_2 ⇒ f_6
    node f_6 where
      x_6 := x_3 ⇒ f_7
    node f_7 where
      x_7 := x_4 ⇒ f_8
    node f_8 where
      x_1 := [-∞, ∞] ⇒ f_9
    node f_9 where
      guard ([0, 0] ≤ x_1) ⇒ f_10
    node f_10 where
      x_2 := nil ⇒ f_11
    node f_11 where
      x_3 := nil ⇒ f_12
    node f_12 where
      x_4 := nil ⇒ f_13
    node f_13 where
      guard (step = [0, 0]) ⇒ f_14
      guard (step ≠ [0, 0]) ⇒ f_15
    node f_14 where
      x_2 := x_1 ⇒ f_16
    node f_15 where
      x_2 := x_7 ⇒ f_16
    node f_16 where
      guard ([3, 3] < x_2) ⇒ f_17
      guard ([3, 3] ≥ x_2) ⇒ f_18
    node f_17 where
      x_3 := [3, 3] ⇒ f_19
    node f_18 where
      x_3 := x_2 ⇒ f_19
    node f_19 where
      x_4 := (x_2 + [1, 1]) ⇒ f_20
    node f_20 where
      skip ⇒ f_13
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_21
    node f_21 where
      x_5 := x_2 ⇒ f_22
    node f_22 where
      x_6 := x_3 ⇒ f_23
    node f_23 where
      x_7 := x_4 ⇒ f_24
    node f_24 where
      x_1 := [-∞, ∞] ⇒ f_25
    node f_25 where
      guard ([0, 0] ≤ x_1) ⇒ f_26
    node f_26 where
      guard (step = [0, 0]) ⇒ f_27
      guard (step ≠ [0, 0]) ⇒ f_28
    node f_27 where
      x_2 := x_1 ⇒ f_29
    node f_28 where
      x_2 := x_7 ⇒ f_29
    node f_29 where
      guard ([3, 3] < x_2) ⇒ f_30
      guard ([3, 3] ≥ x_2) ⇒ f_31
    node f_30 where
      x_3 := [3, 3] ⇒ f_32
    node f_31 where
      x_3 := x_2 ⇒ f_32
    node f_32 where
      x_4 := (x_2 + [1, 1]) ⇒ f_33
    node f_33 where
      step := (step + [1, 1]) ⇒ f_21
      skip ⇒ f_26
      skip ⇒ f_34
    node f_34 where
      assert ([0, 0] ≤ x_3) ⇒ f_35
    node f_35 where
      assert (x_3 ≤ [3, 3]) ⇒ f_36
    node f_36 where
-/
#guard_msgs in
lustre
  node f(x) = o
    guard
      x ≥ 0
    where
      o = if x > 3 then 3 else x
    assert
      0 ≤ o
      o ≤ 3

  node g(x) = o
    guard
      x ≥ 0
    where
      y = x fby y + 1
      o = if y > 3 then 3 else y
    assert
      o ≥ 0
      o ≤ 3

/--
error: variable o could be nil
---
error: variable o could be nil
---
error: assert failed, got #[[1; +∞], [5; +∞], [0; 3], [0; 3]]
---
error: assert failed, got #[[1; +∞], [5; 5], [3; 3], [5; 5], [3; 3], [6; 6], [5; 5], [3; 3], [5; 5], [3; 3], [6; 6]]
---
error: assert failed, got #[[1; +∞], [5; 5], [3; 3], [5; 5], [3; 3], [6; 6], [5; 5], [3; 3], [5; 5], [3; 3], [6; 6]]
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node f() = o,o
      where ⏎
        o = o
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_10
    node f_2 where
      x_1 := nil ⇒ f_3
    node f_3 where
      x_2 := x_1 ⇒ f_4
    node f_4 where
      x_1 := nil ⇒ f_5
    node f_5 where
      x_1 := x_1 ⇒ f_6
    node f_6 where
      skip ⇒ f_5
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_7
    node f_7 where
      x_2 := x_1 ⇒ f_8
    node f_8 where
      x_1 := x_1 ⇒ f_9
    node f_9 where
      step := (step + [1, 1]) ⇒ f_7
      skip ⇒ f_8
      skip ⇒ f_10
    node f_10 where
      ⏎
[Lustrean.Elab.Compile] ✅️ elabExpr
    node u(x) = o
      where ⏎
        o = (if (step = [0, 0]) then [0, 0] else (pre x_0))
        x_0 = x
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_22
    node f_2 where
      x_2 := nil ⇒ f_3
    node f_3 where
      x_3 := nil ⇒ f_4
    node f_4 where
      x_4 := x_2 ⇒ f_5
    node f_5 where
      x_5 := x_3 ⇒ f_6
    node f_6 where
      x_1 := [-∞, ∞] ⇒ f_7
    node f_7 where
      x_2 := nil ⇒ f_8
    node f_8 where
      x_3 := nil ⇒ f_9
    node f_9 where
      guard (step = [0, 0]) ⇒ f_10
      guard (step ≠ [0, 0]) ⇒ f_11
    node f_10 where
      x_2 := [0, 0] ⇒ f_12
    node f_11 where
      x_2 := x_5 ⇒ f_12
    node f_12 where
      x_3 := x_1 ⇒ f_13
    node f_13 where
      skip ⇒ f_9
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_14
    node f_14 where
      x_4 := x_2 ⇒ f_15
    node f_15 where
      x_5 := x_3 ⇒ f_16
    node f_16 where
      x_1 := [-∞, ∞] ⇒ f_17
    node f_17 where
      guard (step = [0, 0]) ⇒ f_18
      guard (step ≠ [0, 0]) ⇒ f_19
    node f_18 where
      x_2 := [0, 0] ⇒ f_20
    node f_19 where
      x_2 := x_5 ⇒ f_20
    node f_20 where
      x_3 := x_1 ⇒ f_21
    node f_21 where
      step := (step + [1, 1]) ⇒ f_14
      skip ⇒ f_17
      skip ⇒ f_22
    node f_22 where
      ⏎
[Lustrean.Elab.Compile] ✅️ elabExpr
    node f(x) = o
      guard
        ([0, 0] ≤ x)
      where ⏎
        o = (if ([3, 3] < x) then [3, 3] else x)
      assert
        ([0, 0] ≤ x)
        (x ≤ [4, 4])
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_20
    node f_2 where
      x_2 := nil ⇒ f_3
    node f_3 where
      x_3 := x_2 ⇒ f_4
    node f_4 where
      x_1 := [-∞, ∞] ⇒ f_5
    node f_5 where
      guard ([0, 0] ≤ x_1) ⇒ f_6
    node f_6 where
      x_2 := nil ⇒ f_7
    node f_7 where
      guard ([3, 3] < x_1) ⇒ f_8
      guard ([3, 3] ≥ x_1) ⇒ f_9
    node f_8 where
      x_2 := [3, 3] ⇒ f_10
    node f_9 where
      x_2 := x_1 ⇒ f_10
    node f_10 where
      skip ⇒ f_7
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_11
    node f_11 where
      x_3 := x_2 ⇒ f_12
    node f_12 where
      x_1 := [-∞, ∞] ⇒ f_13
    node f_13 where
      guard ([0, 0] ≤ x_1) ⇒ f_14
    node f_14 where
      guard ([3, 3] < x_1) ⇒ f_15
      guard ([3, 3] ≥ x_1) ⇒ f_16
    node f_15 where
      x_2 := [3, 3] ⇒ f_17
    node f_16 where
      x_2 := x_1 ⇒ f_17
    node f_17 where
      step := (step + [1, 1]) ⇒ f_11
      skip ⇒ f_14
      skip ⇒ f_18
    node f_18 where
      assert ([0, 0] ≤ x_1) ⇒ f_19
    node f_19 where
      assert (x_1 ≤ [4, 4]) ⇒ f_20
    node f_20 where
      ⏎
[Lustrean.Elab.Compile] ✅️ elabExpr
    node g() = o
      where ⏎
        o.0.x = [5, 5]
        o.0.o = (if ([3, 3] < o.0.x) then [3, 3] else o.0.x)
        o.1.x = [5, 5]
        o.1.o = (if ([3, 3] < o.1.x) then [3, 3] else o.1.x)
        o = (o.0.o + o.1.o)
      assert
        ([0, 0] ≤ o.0.x)
        ([0, 0] ≤ o.0.x)
        (o.0.x ≤ [4, 4])
        ([0, 0] ≤ o.1.x)
        ([0, 0] ≤ o.1.x)
        (o.1.x ≤ [4, 4])
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_48
    node f_2 where
      x_1 := nil ⇒ f_3
    node f_3 where
      x_2 := nil ⇒ f_4
    node f_4 where
      x_3 := nil ⇒ f_5
    node f_5 where
      x_4 := nil ⇒ f_6
    node f_6 where
      x_5 := nil ⇒ f_7
    node f_7 where
      x_6 := x_1 ⇒ f_8
    node f_8 where
      x_7 := x_2 ⇒ f_9
    node f_9 where
      x_8 := x_3 ⇒ f_10
    node f_10 where
      x_9 := x_4 ⇒ f_11
    node f_11 where
      x_10 := x_5 ⇒ f_12
    node f_12 where
      x_1 := nil ⇒ f_13
    node f_13 where
      x_2 := nil ⇒ f_14
    node f_14 where
      x_3 := nil ⇒ f_15
    node f_15 where
      x_4 := nil ⇒ f_16
    node f_16 where
      x_5 := nil ⇒ f_17
    node f_17 where
      x_1 := [5, 5] ⇒ f_18
    node f_18 where
      guard ([3, 3] < x_1) ⇒ f_19
      guard ([3, 3] ≥ x_1) ⇒ f_20
    node f_19 where
      x_2 := [3, 3] ⇒ f_21
    node f_20 where
      x_2 := x_1 ⇒ f_21
    node f_21 where
      x_3 := [5, 5] ⇒ f_22
    node f_22 where
      guard ([3, 3] < x_3) ⇒ f_23
      guard ([3, 3] ≥ x_3) ⇒ f_24
    node f_23 where
      x_4 := [3, 3] ⇒ f_25
    node f_24 where
      x_4 := x_3 ⇒ f_25
    node f_25 where
      x_5 := (x_2 + x_4) ⇒ f_26
    node f_26 where
      skip ⇒ f_17
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_27
    node f_27 where
      x_6 := x_1 ⇒ f_28
    node f_28 where
      x_7 := x_2 ⇒ f_29
    node f_29 where
      x_8 := x_3 ⇒ f_30
    node f_30 where
      x_9 := x_4 ⇒ f_31
    node f_31 where
      x_10 := x_5 ⇒ f_32
    node f_32 where
      x_1 := [5, 5] ⇒ f_33
    node f_33 where
      guard ([3, 3] < x_1) ⇒ f_34
      guard ([3, 3] ≥ x_1) ⇒ f_35
    node f_34 where
      x_2 := [3, 3] ⇒ f_36
    node f_35 where
      x_2 := x_1 ⇒ f_36
    node f_36 where
      x_3 := [5, 5] ⇒ f_37
    node f_37 where
      guard ([3, 3] < x_3) ⇒ f_38
      guard ([3, 3] ≥ x_3) ⇒ f_39
    node f_38 where
      x_4 := [3, 3] ⇒ f_40
    node f_39 where
      x_4 := x_3 ⇒ f_40
    node f_40 where
      x_5 := (x_2 + x_4) ⇒ f_41
    node f_41 where
      step := (step + [1, 1]) ⇒ f_27
      skip ⇒ f_32
      skip ⇒ f_42
    node f_42 where
      assert ([0, 0] ≤ x_1) ⇒ f_43
    node f_43 where
      assert ([0, 0] ≤ x_1) ⇒ f_44
    node f_44 where
      assert (x_1 ≤ [4, 4]) ⇒ f_45
    node f_45 where
      assert ([0, 0] ≤ x_3) ⇒ f_46
    node f_46 where
      assert ([0, 0] ≤ x_3) ⇒ f_47
    node f_47 where
      assert (x_3 ≤ [4, 4]) ⇒ f_48
    node f_48 where
-/
#guard_msgs in
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

/--
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node a() = o
      where ⏎
        o = (if (step = [0, 0]) then [0, 0] else (pre x_0))
        x_0 = ([1, 1] + o)
      assert
        ([0, 0] ≤ o)
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_21
    node f_2 where
      x_1 := nil ⇒ f_3
    node f_3 where
      x_2 := nil ⇒ f_4
    node f_4 where
      x_3 := x_1 ⇒ f_5
    node f_5 where
      x_4 := x_2 ⇒ f_6
    node f_6 where
      x_1 := nil ⇒ f_7
    node f_7 where
      x_2 := nil ⇒ f_8
    node f_8 where
      guard (step = [0, 0]) ⇒ f_9
      guard (step ≠ [0, 0]) ⇒ f_10
    node f_9 where
      x_1 := [0, 0] ⇒ f_11
    node f_10 where
      x_1 := x_4 ⇒ f_11
    node f_11 where
      x_2 := ([1, 1] + x_1) ⇒ f_12
    node f_12 where
      skip ⇒ f_8
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_13
    node f_13 where
      x_3 := x_1 ⇒ f_14
    node f_14 where
      x_4 := x_2 ⇒ f_15
    node f_15 where
      guard (step = [0, 0]) ⇒ f_16
      guard (step ≠ [0, 0]) ⇒ f_17
    node f_16 where
      x_1 := [0, 0] ⇒ f_18
    node f_17 where
      x_1 := x_4 ⇒ f_18
    node f_18 where
      x_2 := ([1, 1] + x_1) ⇒ f_19
    node f_19 where
      step := (step + [1, 1]) ⇒ f_13
      skip ⇒ f_15
      skip ⇒ f_20
    node f_20 where
      assert ([0, 0] ≤ x_1) ⇒ f_21
    node f_21 where
-/
#guard_msgs in
lustre
  node a() = o where
    o = 0 fby 1 + o
  assert
    o ≥ 0

/--
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node h() = o,i
      where ⏎
        o = (if (step = [0, 0]) then [0, 0] else (pre x_1))
        i = (if (o = [5, 5]) then x_2 else [0, 0])
        x_0 = (i + [1, 1])
        x_1 = (if (step = [0, 0]) then [1, 1] else (pre x_0))
        x_2 = (if (([0, 0] < [0, 0]) ∨ ([0, 0] < [0, 0])) then [1, 1] else [2, 2])
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_50
    node f_2 where
      x_1 := nil ⇒ f_3
    node f_3 where
      x_2 := nil ⇒ f_4
    node f_4 where
      x_3 := nil ⇒ f_5
    node f_5 where
      x_4 := nil ⇒ f_6
    node f_6 where
      x_5 := nil ⇒ f_7
    node f_7 where
      x_6 := x_1 ⇒ f_8
    node f_8 where
      x_7 := x_2 ⇒ f_9
    node f_9 where
      x_8 := x_3 ⇒ f_10
    node f_10 where
      x_9 := x_4 ⇒ f_11
    node f_11 where
      x_10 := x_5 ⇒ f_12
    node f_12 where
      x_1 := nil ⇒ f_13
    node f_13 where
      x_2 := nil ⇒ f_14
    node f_14 where
      x_3 := nil ⇒ f_15
    node f_15 where
      x_4 := nil ⇒ f_16
    node f_16 where
      x_5 := nil ⇒ f_17
    node f_17 where
      guard (step = [0, 0]) ⇒ f_18
      guard (step ≠ [0, 0]) ⇒ f_19
    node f_18 where
      x_1 := [0, 0] ⇒ f_20
    node f_19 where
      x_1 := x_9 ⇒ f_20
    node f_20 where
      guard (x_1 = [5, 5]) ⇒ f_21
      guard (x_1 ≠ [5, 5]) ⇒ f_22
    node f_21 where
      x_2 := x_5 ⇒ f_23
    node f_22 where
      x_2 := [0, 0] ⇒ f_23
    node f_23 where
      x_3 := (x_2 + [1, 1]) ⇒ f_24
    node f_24 where
      guard (step = [0, 0]) ⇒ f_25
      guard (step ≠ [0, 0]) ⇒ f_26
    node f_25 where
      x_4 := [1, 1] ⇒ f_27
    node f_26 where
      x_4 := x_8 ⇒ f_27
    node f_27 where
      guard (([0, 0] < [0, 0]) || ([0, 0] < [0, 0])) ⇒ f_28
      guard (([0, 0] ≥ [0, 0]) && ([0, 0] ≥ [0, 0])) ⇒ f_29
    node f_28 where
      x_5 := [1, 1] ⇒ f_30
    node f_29 where
      x_5 := [2, 2] ⇒ f_30
    node f_30 where
      skip ⇒ f_17
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_31
    node f_31 where
      x_6 := x_1 ⇒ f_32
    node f_32 where
      x_7 := x_2 ⇒ f_33
    node f_33 where
      x_8 := x_3 ⇒ f_34
    node f_34 where
      x_9 := x_4 ⇒ f_35
    node f_35 where
      x_10 := x_5 ⇒ f_36
    node f_36 where
      guard (step = [0, 0]) ⇒ f_37
      guard (step ≠ [0, 0]) ⇒ f_38
    node f_37 where
      x_1 := [0, 0] ⇒ f_39
    node f_38 where
      x_1 := x_9 ⇒ f_39
    node f_39 where
      guard (x_1 = [5, 5]) ⇒ f_40
      guard (x_1 ≠ [5, 5]) ⇒ f_41
    node f_40 where
      x_2 := x_5 ⇒ f_42
    node f_41 where
      x_2 := [0, 0] ⇒ f_42
    node f_42 where
      x_3 := (x_2 + [1, 1]) ⇒ f_43
    node f_43 where
      guard (step = [0, 0]) ⇒ f_44
      guard (step ≠ [0, 0]) ⇒ f_45
    node f_44 where
      x_4 := [1, 1] ⇒ f_46
    node f_45 where
      x_4 := x_8 ⇒ f_46
    node f_46 where
      guard (([0, 0] < [0, 0]) || ([0, 0] < [0, 0])) ⇒ f_47
      guard (([0, 0] ≥ [0, 0]) && ([0, 0] ≥ [0, 0])) ⇒ f_48
    node f_47 where
      x_5 := [1, 1] ⇒ f_49
    node f_48 where
      x_5 := [2, 2] ⇒ f_49
    node f_49 where
      step := (step + [1, 1]) ⇒ f_31
      skip ⇒ f_36
      skip ⇒ f_50
    node f_50 where
-/
#guard_msgs in
lustre
  node h() = o, i where
    o = 0 fby 1 fby i+1
    i =
      if o = 5 then
        if 0 ≠ 0 then 1 else 2
      else
        0
/--
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node f()
      where ⏎
        ⏎
    ⇒
    node f_0 where
      step := [0, 0] ⇒ f_2
    node f_1 where
      skip ⇒ f_4
    node f_2 where
      skip ⇒ f_2
      skip ⇒ f_1
      step := (step + [1, 1]) ⇒ f_3
    node f_3 where
      step := (step + [1, 1]) ⇒ f_3
      skip ⇒ f_3
      skip ⇒ f_4
    node f_4 where
-/
#guard_msgs in
lustre
  node f() where

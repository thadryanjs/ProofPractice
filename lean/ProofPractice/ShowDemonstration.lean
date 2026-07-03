def foo (n : Nat) : Nat := n + n

-- TEST 1: show SAME form as goal → redundant no-op.
-- PREDICT: ✅ (matches exactly)
example : 2 + 2 = 4 := by
  show 2 + 2 = 4
  rfl

-- TEST 2: show a DEFINITIONALLY-EQUAL different-looking form.
-- PREDICT: ✅ (2+2 reduces to 4, so `4 = 4` is defeq to goal)
example : 2 + 2 = 4 := by
  show 4 = 4
  rfl

-- TEST 3: show a NOT-defeq (false-shaped) form.
-- PREDICT: ❌ (2+2 reduces to 4, not 5 — mismatch)
example : 2 + 2 = 4 := by
  show 2 + 2 = 5
  rfl

-- TEST 4: show a form needing a THEOREM (flipped sides).
-- PREDICT: ❌ (flipping needs Eq.symm — not a definitional move)
example : 2 + 2 = 4 := by
  show 4 = 2 + 2
  rfl

-- TEST 5: does `exact` need `show` to see through a definition?
-- (The one I got WRONG earlier.) PREDICT: ✅ WITHOUT show
theorem about_sum : 3 + 3 = 6 := rfl
example : foo 3 = 6 := by
  exact about_sum

-- TEST 6: same but WITH show. PREDICT: ✅, show was REDUNDANT
example : foo 3 = 6 := by
  show 3 + 3 = 6
  exact about_sum

-- TEST 7: show unfolds foo to defeq form, then rfl.
-- PREDICT: ✅ (foo 3 defeq 3+3 defeq 6)
example : foo 3 = 6 := by
  show 3 + 3 = 6
  rfl

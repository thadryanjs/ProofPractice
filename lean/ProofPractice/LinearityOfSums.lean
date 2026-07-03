import Mathlib.Tactic.Ring

/- Stats Concept: Linearity of Sums. -/
-- If you add a constant 'c' to two data points 'x' and 'y', the total sum
-- increases by 2 * c.
theorem shift_sum (x y c : Nat) : (x + c) + (y + c) = (x + y) + (2 * c) := by
  -- ring is a "tactic" that normalizes addition and multiplication to "normal" form
  ring

-- This works by automating a bunch of algebraic simplifications.
-- If we were to do this explicity, using "rw" instead of "ring", we could
-- show our work more clearly at the expense of some tedium
-- The "Normal Form" we're looking for is:
--   x + y + 2 * c = x + y + 2 * c

theorem shift_sum_calc (x y c : Nat) :
    (x + c) + (y + c) = (x + y) + (2 * c) := by
  calc (x + c) + (y + c)
      -- start: parens group each variable with its own c.
      -- plan: shuffle parens until x and y sit together and the two c's sit together.
      = x + (c + (y + c))   := by rw [Nat.add_assoc x c (y + c)]
      -- have X = (x+c)+(y+c), want Y = x+(c+(y+c))  -> default (as written).
      -- moves the grouping to the right pair, so x is left alone out front.
    _ = x + ((c + y) + c)   := by rw [← Nat.add_assoc c y c]
      -- have Y = c+(y+c), want X = (c+y)+c  -> `←` (backward).
      -- regroups the inner part onto the left pair (c+y).
      -- args c y c pin it to the inner group; bare rw would grab the outer one (the error you hit).
    _ = x + ((y + c) + c)   := by rw [Nat.add_comm c y]
      -- the only real "move": swap c+y into y+c.
      -- this is commute, not regroup — no parens change here.
    _ = x + (y + (c + c))   := by rw [Nat.add_assoc y c c]
      -- have X = (y+c)+c, want Y = y+(c+c)  -> default (as written).
      -- moves the grouping to the right pair, collecting the two c's together.
    _ = (x + y) + (c + c)   := by rw [← Nat.add_assoc x y (c + c)]
      -- have Y = x+(y+(c+c)), want X = (x+y)+(c+c)  -> `←` (backward).
      -- regroups onto the left pair, so x and y are grouped and c+c is grouped.
    _ = (x + y) + (2 * c)   := by rw [← Nat.two_mul c]
      -- have Y = c+c, want X = 2*c  -> `←` (backward), folds the doubling back up.
      -- lhs now equals rhs exactly, so the calc is complete.
-- Note:
-- the direction rule for `rw`, the thing to keep in your head:
--   every lemma is stated as  X = Y.
--   default (no arrow)  = apply as written, turn X into Y.
--   with `←`            = apply backward, turn Y into X.
-- so the question at each step is just: "do i have X and want Y?" -> default.
--                                       "do i have Y and want X?" -> `←`.
--
-- add_assoc, stated  (a+b)+c = a+(b+c), just MOVES the one pair of parens
-- between the two adjacent pairs — it never adds or removes grouping:
--   default groups the RIGHT pair:  (a+b)+c -> a+(b+c)
--   `←`     groups the LEFT pair:   a+(b+c) -> (a+b)+c
-- (there's no "tighter/looser" — same two +'s, same one pair of parens,
--  just sitting around a different pair of terms.)
--
-- two_mul, stated  2*c = c+c:
--   default expands 2*c into c+c, `←` folds c+c back into 2*c.
--
-- the arrow isn't "left vs right" in space — it's "which side of the = am i
-- turning into which." for add_assoc that happens to come out as group-left
-- vs group-right


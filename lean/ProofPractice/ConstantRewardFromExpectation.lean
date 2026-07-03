import Mathlib
open Finset

/-
MDP lemma: a constant reward comes out of an expectation.
This is the everyday hand-wave  E[R + γV(s')] = R + γ E[V(s')]  written honestly.

The reward R survives as plain R ONLY because the transition probabilities sum
to 1 (hypothesis hP). Papers omit this; Lean forces it into the open.

This version is instrumented with trace_state at every legal slot so you can watch
the goal evolve. trace_state is a TACTIC, so it only lives inside a `by` block:
  • once at the top of the outer `by` (shows the opening state), and
  • inside each calc step's own `by` (shows that step's goal).
It can NOT go in the gap between calc steps — that gap isn't a tactic context.
Indentation is significant (like Python): the `by` body must be indented under it,
and trace_state must line up with the other tactics in its block.
-/

variable {S : Type*} [Fintype S]      -- S = next states, finitely many

theorem expectation_const_out
    (P : S → ℝ) (V : S → ℝ) (R γ : ℝ)
    (hP : ∑ s, P s = 1) :              -- the hidden assumption, made explicit
    ∑ s, P s * (R + γ * V s) = R + γ * ∑ s, P s * V s := by
  -- this indentation is syntactic!!!
  trace_state                         -- opening state: context + the full goal
  calc ∑ s, P s * (R + γ * V s)
      -- (1) distribute inside the sum; algebra on one term, so sum_congr + ring
      = ∑ s, (P s * R + γ * (P s * V s)) := Finset.sum_congr rfl (fun s _ => by ring)
      -- (2) split the sum over the + :  ∑(f+g) = ∑f + ∑g   (default direction)
    _ = (∑ s, P s * R) + ∑ s, γ * (P s * V s) := by
      trace_state
      rw [Finset.sum_add_distrib]
      -- (3) pull constants out of each sum (both backward: have Y, want X → ←)
      --     ← sum_mul : ∑ (Pₛ * R) → (∑ Pₛ) * R
      --     ← mul_sum : ∑ (γ * x)  → γ * ∑ x
    _ = (∑ s, P s) * R + γ * ∑ s, P s * V s := by
      trace_state
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      -- (4) THE key step: use ∑ P = 1, the reason R stays R
    _ = 1 * R + γ * ∑ s, P s * V s := by
      trace_state
      rw [hP]
      -- (5) tidy 1 * R = R
    _ = R + γ * ∑ s, P s * V s := by
      trace_state
      rw [one_mul]

/-
When you trust the proof, delete the trace_state lines — they're scaffolding and
do nothing to the logic. The clean five-line calc underneath IS your paper's proof:
it transcribes almost 1:1 into a LaTeX align environment.
-/


import Mathlib
open Finset

/- Fard & Pineau (2011), Theorem 1, step (20)→(21): the max→min negation flip.

   The proof negates the Bellman eqn on M' and pushes the negation inside the
   optimization. Two parts are accounting (−R'=R̄ and A'=Π, both definitional);
   the one real step is:  − max f = min (−f)  — negation reverses the order, so
   the max's winner becomes the min's. That step is what's proved here.

   The MDP collapses to: `actions` = Π(s') (a Finset), `Q` = Q*(s',·) (black box).
   Hidden hypothesis surfaced by formalizing: `actions` must be NONEMPTY
   (Def 1: Π(s)≠∅) — `sup'`/`inf'` require the proof as an argument. -/

#eval IO.println "====================| Normal version:|===================="

theorem neg_max_eq_min_neg
    {Action : Type*} (actions : Finset Action) (h_nonempty : actions.Nonempty)
    (Q : Action → ℝ) :
    - actions.sup' h_nonempty Q
      = actions.inf' h_nonempty (fun a => - Q a) := by
  apply le_antisymm
  -- ≤ : bound the min below by every element; negation turns it into Q a ≤ max Q
  · apply Finset.le_inf'
    intro a ha
    -- show - actions.sup' h_nonempty Q ≤ - Q a
    simp only [neg_le_neg_iff]
    -- show Q a ≤ actions.sup' h_nonempty Q
    exact Finset.le_sup' Q ha
  -- ≥ : bound the max above by every element; negation turns it into min ≤ −Q a
  · rw [le_neg]
    apply Finset.sup'_le
    intro a ha
    -- show Q a ≤ - actions.inf' h_nonempty (fun a => - Q a)
    rw [le_neg]
    -- show actions.inf' h_nonempty (fun a => - Q a) ≤ - Q a
    exact Finset.inf'_le (fun a => - Q a) ha

-- Expect: [propext, Classical.choice, Quot.sound]  (no sorryAx)
#print axioms neg_max_eq_min_neg
#print neg_max_eq_min_neg


/-
  neg_max_eq_min_neg  (LOGGING version)

  Same proof as before, but instrumented with `trace_state`.

  `trace_state` is Lean's equivalent of a `print()` / `console.log` inserted
  between statements: it does nothing to the proof (it's a no-op tactic), it
  just DUMPS the current goal state into the Infoview / build output at the
  point where it sits. So you get a running log of what the goal looks like
  BEFORE and AFTER every real step, exactly like logging a variable's value
  before and after each line of ordinary code.

  Read the emitted trace top-to-bottom and you'll see the goal morph:
    -x ≤ -y   -->   y ≤ x   (after neg_le_neg_iff), etc.

  HOW TO SEE THE OUTPUT:
    - In VS Code (Lean 4 extension): click inside the theorem; the trace
      messages appear in the Infoview panel, each tagged with its line.
    - On the command line (`lake build`): the trace lines are printed to
      stdout as `trace: ...` messages during compilation.

  Note: `trace_state` prints Lean's own rendering of the goal, so the ∀ bound
  variable may show as `a✝` or `x` etc. — that's Lean naming it, not you.
-/

#eval IO.println "====================| trace_state version: |===================="

theorem neg_max_eq_min_neg_debug
    {Action : Type*}
    (actions : Finset Action)
    (h_nonempty : actions.Nonempty)
    (Q : Action → ℝ) :
    - actions.sup' h_nonempty Q
      = actions.inf' h_nonempty (fun x => - Q x) := by
  trace_state                       -- LOG: the very first goal (the equality)
  apply le_antisymm
  trace_state                       -- LOG: now TWO goals (<= each direction)

  -- ===== DIRECTION 1:  - sup' Q  <=  inf' (-Q) =====
  · trace_state                     -- LOG: entering direction 1
    apply Finset.le_inf'

    trace_state                     -- LOG: goal became a ∀ (bound below by every elt)
    intro a ha

    trace_state                     -- LOG: arbitrary element introduced (a, ha in ctx)
    rw [neg_le_neg_iff]

    trace_state                     -- LOG: negations stripped, sides flipped
    exact Finset.le_sup' Q ha       -- CLOSE (no trace after: goal is gone)

  -- ===== DIRECTION 2:  inf' (-Q)  <=  - sup' Q =====
  · trace_state                     -- LOG: entering direction 2
    rw [le_neg]
    trace_state                     -- LOG: negation moved; sup' now exposed on left

    apply Finset.sup'_le
    trace_state                     -- LOG: goal became a ∀ (bound above by every elt)

    intro a ha
    trace_state                     -- LOG: arbitrary element introduced

    rw [le_neg]
    trace_state                     -- LOG: negation moved; inf' now exposed on left
    exact Finset.inf'_le (fun x => - Q x) ha   -- CLOSE

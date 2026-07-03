# Recap: `neg_max_eq_min_neg`

- **What the theorem proves.** `-(max of Q over actions) = (min of -Q over actions)`. This is the one real inference in Fard & Pineau's step (20)→(21): negating a maximization turns it into a minimization. Everything else in that paper step was just substituting definitions.

- **The overall shape.** To prove an equality of two reals, prove `≤` in both directions (`le_antisymm`). The two directions are mirror images of each other across the max↔min axis — the same reasoning reflected.

- **The only two moves, used repeatedly.**
  - **(A) Reshape:** use a reversible sign-flip fact (`neg_le_neg_iff : -x ≤ -y ↔ y ≤ x`, or `le_neg : x ≤ -y ↔ y ≤ -x`) to move negations across `≤` until the buried `sup'`/`inf'` sits on the side the next lemma needs. Never changes truth, only presentation.
  - **(B) Close:** use a defining fact about max/min — "any element's value ≤ the max" (`le_sup'`), "the min ≤ any element's value" (`inf'_le`), and their bound-from-the-other-side duals (`le_inf'`, `sup'_le`).

- **`sup' actions h_nonempty Q` = one number.** It applies `Q` to every element of `actions` and returns the biggest result (max *over the outputs*, not over the actions). `inf'` is the same for the smallest. The iteration lives inside the function's definition; the call site just hands over three things.

- **Syntax that tripped me up.** `f x y` (space-separated) is function application, not multiplication — same as `f(x,y)` elsewhere. `actions.sup' h_nonempty Q` is dot notation, a purely textual shorthand for `Finset.sup' actions h_nonempty Q` (the value before the dot becomes the first argument). No OOP dispatch involved.

- **`h_nonempty` is a proof-as-value.** Its type is `actions.Nonempty` (= "there exists an element in actions"). It's required because max/min of an empty set is meaningless; `sup'` unpacks it internally to grab a real starting element for the fold. It carries no numeric info — it's threaded through every lemma purely so expressions mentioning `sup'`/`inf'` stay well-formed. It's the paper's Definition 1 requirement (Π(s) ≠ ∅) made unskippable.

- **`intro a ha` is destructuring, not declaring.** When the goal is `∀ a ∈ actions, …`, you prove it for an *arbitrary* `a` using nothing specific about which one — that single argument then covers all elements at once (no iteration, unlike a `for` loop). `a`'s type is read off the goal's `∀`; `ha : a ∈ actions` is the membership certificate that licenses comparing against that element.

- **`exact <term>` is the "check me" line.** It doesn't transform the goal — it submits a fully-built proof term and Lean mechanically verifies its type is *identical* to the goal. In the final line, `Finset.inf'_le (fun x => -Q x) ha` takes the function and the membership proof as two separate arguments; the function-applied-to-element part beta-reduces to `-Q a`, matching the goal.

- **The goal is the source of truth.** Tactics mostly read from or reshape the current goal: `intro` destructures its `∀`, `apply` matches a lemma's conclusion against it, `rw`/`simp` reshape it, `exact` checks a term against it.

- **On making it readable.** The tactic steps *are* the reasoning, so you can't refactor them into something clearer the way you can with ordinary code — clarity comes from comments, `trace_state` (logs the goal at each step, like `print()` for goal states), and `#eval IO.println "..."` for section labels. The build log confirmed every intermediate goal, so the annotations all checked out against ground truth.

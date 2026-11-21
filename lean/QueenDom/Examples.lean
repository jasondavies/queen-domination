/-
Sanity checks of the definitions on a small board (not used by the main theorems).
-/
module

public import QueenDom.Main

@[expose] public section

namespace QueenDom

open Finset

/-- Three queens dominating the `6 × 6` board. -/
def ex6 : Finset (Sq 6) := {(0, 0), (2, 4), (4, 2)}

set_option maxRecDepth 10000 in
theorem ex6_dominating : Dominating ex6 := by decide

theorem ex6_card : ex6.card = 3 := by decide

theorem gamma_6_le : gamma 6 ≤ 3 := ex6_card ▸ gamma_le ex6_dominating

/-- The case-split theorem applied to `ex6`: some case formula for `(n, k) = (6, 3)` is satisfiable
(so the hypotheses of `half_lt_gamma_of_cases_unsat` are not vacuous in general). -/
theorem ex6_case : ∃ g : Sym, ∃ cs ∈ enumCases 6 3, CaseSat 6 3 cs (g.image ex6) :=
  main_even (k := 3) (by norm_num) ex6 ex6_dominating ex6_card

end QueenDom

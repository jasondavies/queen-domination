import QueenDom
import QueenDom.SymmetryCase

/-! Axiom report for the main theorems.  Expected: only `propext`, `Classical.choice`, `Quot.sound`
(or a subset).  In particular no `sorryAx` and no `Lean.ofReduceBool` (no `native_decide`).
The 343 piece theorems `piece32_*`, `piece35_*` are checked by the loop at the end. -/

-- padding lemma, frame
#print axioms QueenDom.dominating_iff
#print axioms QueenDom.dominating_iff_adj
#print axioms QueenDom.exists_dominating_card_eq
#print axioms QueenDom.exists_isFrame_of_card
#print axioms QueenDom.IsFrame.unique
-- geometry (E1)-(E5)
#print axioms QueenDom.IsFrame.margin_cols
#print axioms QueenDom.IsFrame.margin_rows
#print axioms QueenDom.IsFrame.border_not_mem
#print axioms QueenDom.card_border
#print axioms QueenDom.card_vsides
#print axioms QueenDom.card_hsides
#print axioms QueenDom.IsFrame.card_needy_vsides
#print axioms QueenDom.IsFrame.card_needy_hsides
#print axioms QueenDom.IsFrame.card_needy_border
#print axioms QueenDom.betaT_border_le_two
#print axioms QueenDom.betaS_border_le_two
#print axioms QueenDom.betaT_vsides_le_one
#print axioms QueenDom.betaS_vsides_le_one
#print axioms QueenDom.betaT_hsides_le_one
#print axioms QueenDom.betaS_hsides_le_one
#print axioms QueenDom.vsides_filter_u0
#print axioms QueenDom.vsides_filter_v0
#print axioms QueenDom.hsides_filter_u0
#print axioms QueenDom.hsides_filter_v0
-- identities
#print axioms QueenDom.double_count
#print axioms QueenDom.waste2_eq_card_pairs
#print axioms QueenDom.IsFrame.frame_identity
#print axioms QueenDom.IsFrame.side_identity_V
#print axioms QueenDom.IsFrame.side_identity_H
-- consequences
#print axioms QueenDom.IsFrame.deficit_bound
#print axioms QueenDom.IsFrame.deficit_bound_V
#print axioms QueenDom.IsFrame.deficit_bound_H
#print axioms QueenDom.IsFrame.deficit_sum_le_two
#print axioms QueenDom.IsFrame.deficit_square
#print axioms QueenDom.IsFrame.rigid_V
#print axioms QueenDom.IsFrame.rigid_H
#print axioms QueenDom.IsFrame.rigid_V_counts
#print axioms QueenDom.IsFrame.rigid_V_needy
#print axioms QueenDom.IsFrame.rigid_H_counts
#print axioms QueenDom.IsFrame.rigid_H_needy
#print axioms QueenDom.IsFrame.deficit_sum_le_four
#print axioms QueenDom.IsFrame.deficit_V_odd
#print axioms QueenDom.IsFrame.deficit_H_odd
#print axioms QueenDom.IsFrame.odd_minus
-- symmetries and cases
#print axioms QueenDom.Dominating.sym
#print axioms QueenDom.HasMargins.sym
#print axioms QueenDom.HasCase.sym
#print axioms QueenDom.exists_canon
#print axioms QueenDom.canon_iff_forall
#print axioms QueenDom.admissible_iff_py
#print axioms QueenDom.admissible_half_iff
#print axioms QueenDom.exists_canonAdm_actCase
#print axioms QueenDom.caseSat_of_frame
#print axioms QueenDom.admissible_of_frame
#print axioms QueenDom.case_split
#print axioms QueenDom.no_dominating_of_cases_unsat
#print axioms QueenDom.mem_enumCases
#print axioms QueenDom.enumCases_eq_pieces
#print axioms QueenDom.enumCases_eq_table
-- main theorems, general (n, k), even and odd boards
#print axioms QueenDom.lt_gamma_of_cases_unsat
#print axioms QueenDom.case_split_enum
#print axioms QueenDom.main_even
#print axioms QueenDom.half_lt_gamma_of_cases_unsat
#print axioms QueenDom.admissible_odd_iff
#print axioms QueenDom.main_odd
#print axioms QueenDom.odd_lt_gamma_of_cases_unsat
#print axioms QueenDom.gamma_eq_of_lt_of_dominating
#print axioms QueenDom.mem_of_enumCases_eq
#print axioms QueenDom.case_split_of_enumCases_eq
#print axioms QueenDom.cover_of_enumCases_eq
#print axioms QueenDom.card_lt_of_enumCases_eq
#print axioms QueenDom.lt_gamma_of_enumCases_eq
#print axioms QueenDom.frames_of_enumCases_eq
#print axioms QueenDom.card_frames_of_enumCases_eq
-- F.6, Lemma R (semantic part)
#print axioms QueenDom.CaseSat.hasCase
#print axioms QueenDom.CaseSat.sym
#print axioms QueenDom.lemmaR
#print axioms QueenDom.lt_gamma_of_cases_unsat_symBreak
#print axioms QueenDom.lt_gamma_of_cases_unsat_mixed
-- n = 32
#print axioms QueenDom.cases32_length
#print axioms QueenDom.enumFrames_32_16_length
#print axioms QueenDom.enumFrames_32_16_nodup
#print axioms QueenDom.card_frames_cases32
#print axioms QueenDom.enumCases_32_16
#print axioms QueenDom.mem_cases32
#print axioms QueenDom.cases32_cover
#print axioms QueenDom.case_split_32
#print axioms QueenDom.seventeen_le_card_of_cases32_unsat
#print axioms QueenDom.seventeen_le_gamma_32_of_cases32_unsat
#print axioms QueenDom.q32_dominating
#print axioms QueenDom.gamma_32_le
#print axioms QueenDom.gamma_32_eq_17_of_cases32_unsat
-- n = 35
#print axioms QueenDom.marginPairs_18
#print axioms QueenDom.piece35_0_0
#print axioms QueenDom.enumCases_35_18_table
#print axioms QueenDom.cases35_length
#print axioms QueenDom.enumFrames_35_18_length
#print axioms QueenDom.enumFrames_35_18_nodup
#print axioms QueenDom.card_frames_cases35
#print axioms QueenDom.enumCases_35_18
#print axioms QueenDom.mem_cases35
#print axioms QueenDom.cases35_cover
#print axioms QueenDom.case_split_35
#print axioms QueenDom.nineteen_le_card_of_cases35_unsat
#print axioms QueenDom.nineteen_le_gamma_35_of_cases35_unsat
#print axioms QueenDom.nineteen_le_gamma_35_of_cases35_unsat_mixed
#print axioms QueenDom.q35_card
#print axioms QueenDom.q35_dominating
#print axioms QueenDom.gamma_35_le
#print axioms QueenDom.gamma_35_eq_19_of_cases35_unsat
#print axioms QueenDom.gamma_35_eq_19_of_cases35_unsat_mixed
-- optional constraints of the encoder (not used for n = 32)
#print axioms QueenDom.colour_balance
#print axioms QueenDom.moment_T
#print axioms QueenDom.moment_S
#print axioms QueenDom.moment_sq
-- sanity example
#print axioms QueenDom.ex6_case

-- every piece theorem of the two case lists (kernel computations), checked mechanically
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut cnt : Nat := 0
  let mut bad : Array Name := #[]
  for (nm, _) in env.constants.toList do
    let s := nm.toString
    if s.startsWith "QueenDom.piece32_" || s.startsWith "QueenDom.piece35_" then
      cnt := cnt + 1
      let axs ← collectAxioms nm
      for ax in axs do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          bad := bad.push nm
  logInfo m!"piece theorems checked: {cnt}; with an axiom outside [propext, Classical.choice, Quot.sound]: {bad.size}"

/-
The case list for `n = 35`, `k = 18` (odd board, `k = (n+1)/2`): the 128,941 cases refuted by the
referee's run (`frame/out/d_35_18.jsonl`, `d_35_18_sq.jsonl`, `h_35_18.jsonl`) coincide with the case list
`L(35, 18)`; kernel computation (`decide +kernel`, no `native_decide`).  Final theorems for `n = 35`
(instances of the generic statements of `Main.lean`), and the upper bound `γ(Q_35) ≤ 19`.
-/
module

public import QueenDom.Cases35Pieces
public import QueenDom.LemmaR

@[expose] public section

namespace QueenDom

/-- The case codes of the `n = 35`, `k = 18` run (`QueenDom/Cases35Data.lean`), in lexicographic order. -/
def caseCodes35 : List ℕ := tableList 18 caseCodes35T

/-- The cases of the `n = 35`, `k = 18` run, sorted. -/
def cases35 : List Case := caseCodes35.map Case.ofCode

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The run refuted 128,941 cases. -/
theorem cases35_length : cases35.length = 128941 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- There are 5050 canonical frames for `n = 35`, `k = 18`. -/
theorem enumFrames_35_18_length : (enumFrames 35 18).length = 5050 := by decide +kernel

/-- **The case list of the run is the case list `L(35, 18)`** (kernel computation, assembled from one
computation per pair of horizontal margins in `Cases35Pieces.lean`). -/
theorem enumCases_35_18 : enumCases 35 18 = cases35 := enumCases_35_18_table

/-- A case is in the list of the run iff its frame is canonical and it is admissible for `(35, 18)`. -/
theorem mem_cases35 {cs : Case} : cs ∈ cases35 ↔ CanonAdm 35 18 cs :=
  mem_of_enumCases_eq enumCases_35_18

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The codes of the 5050 canonical frames are strictly increasing (kernel computation). -/
theorem enumFrames_35_18_chain : ((enumFrames 35 18).map frameCode).IsChain (· < ·) := by
  decide +kernel

/-- The 5050 canonical frames are pairwise distinct. -/
theorem enumFrames_35_18_nodup : (enumFrames 35 18).Nodup :=
  nodup_of_frameCode_chain enumFrames_35_18_chain

/-- The frames occurring in the run are exactly the canonical frames for `(35, 18)`. -/
theorem frames_cases35 : (cases35.map Case.frame).toFinset = (enumFrames 35 18).toFinset :=
  frames_of_enumCases_eq enumCases_35_18 (by norm_num) (by norm_num)

/-- The run has exactly 5050 distinct frames. -/
theorem card_frames_cases35 : (cases35.map Case.frame).toFinset.card = 5050 := by
  rw [card_frames_of_enumCases_eq enumCases_35_18 (by norm_num) (by norm_num) enumFrames_35_18_chain,
    enumFrames_35_18_length]

/-- **Case split for `n = 35`.**  Every dominating set of 18 queens on the `35 × 35` board has a
symmetric image satisfying all constraints of one of the 128,941 cases of the run. -/
theorem case_split_35 (D : Finset (Sq 35)) (hD : Dominating D) (hc : D.card = 18) :
    ∃ g : Sym, ∃ cs ∈ cases35, CaseSat 35 18 cs (g.image D) :=
  case_split_of_enumCases_eq enumCases_35_18 (by norm_num) D hD hc

/-- **The run covers every admissible case up to symmetry**: every admissible (frame, deficit vector)
for `(35, 18)` has an image under one of the eight symmetries in the list of the 128,941 cases. -/
theorem cases35_cover (cs : Case) (h : Admissible 35 18 cs) : ∃ g : Sym, g.actCase cs ∈ cases35 :=
  cover_of_enumCases_eq enumCases_35_18 cs h

/-- **`γ(Q_35) ≥ 19`, modulo the SAT certificates.**  If each of the 128,941 cases of the run is
unsatisfiable (this is what the DRAT certificates establish, via the CNF encoding of `CaseSat`, outside
Lean), then every dominating set of `Q_35` has at least 19 queens. -/
theorem nineteen_le_card_of_cases35_unsat
    (H : ∀ cs ∈ cases35, ¬ ∃ D : Finset (Sq 35), CaseSat 35 18 cs D) :
    ∀ D : Finset (Sq 35), Dominating D → 19 ≤ D.card :=
  card_lt_of_enumCases_eq enumCases_35_18 (by norm_num) H

/-- The same statement in terms of the domination number. -/
theorem nineteen_le_gamma_35_of_cases35_unsat
    (H : ∀ cs ∈ cases35, ¬ ∃ D : Finset (Sq 35), CaseSat 35 18 cs D) : 19 ≤ gamma 35 :=
  lt_gamma_of_enumCases_eq enumCases_35_18 (by norm_num) H

/-- **The same with the residual symmetry breaking of F.6 (Lemma R)**, in the form used by the run: 128,356
cases were refuted with the plain formula, 585 (by `run_hard.py`) with the formula plus the lex-leader
clauses (and cubes, a propositional split).  It suffices that for each case either the constraints or the
constraints with the lex-leader condition `SymBreak` are unsatisfiable. -/
theorem nineteen_le_gamma_35_of_cases35_unsat_mixed
    (H : ∀ cs ∈ cases35, (¬ ∃ D : Finset (Sq 35), CaseSat 35 18 cs D) ∨
      ¬ ∃ D : Finset (Sq 35), CaseSat 35 18 cs D ∧ SymBreak cs D) : 19 ≤ gamma 35 :=
  lt_gamma_of_cases_unsat_mixed (by norm_num) fun cs hcs => H cs (enumCases_35_18 ▸ hcs)

/-! ### Upper bound: 19 queens dominate `Q_35` -/

/-- The dominating set of 19 queens of `frame/out/q35_19.json` (squares `(column, row)`). -/
def q35 : Finset (Sq 35) :=
  {(1, 19), (3, 7), (5, 27), (7, 9), (9, 17), (11, 1), (13, 23), (15, 15), (17, 31), (19, 5), (21, 13),
   (23, 21), (25, 3), (27, 33), (29, 11), (31, 25), (32, 32), (33, 29), (34, 34)}

theorem q35_card : q35.card = 19 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The 19 queens dominate `Q_35` (kernel computation over the 1225 squares). -/
theorem q35_dominating : Dominating q35 := by decide +kernel

/-- `γ(Q_35) ≤ 19` (unconditional). -/
theorem gamma_35_le : gamma 35 ≤ 19 := q35_card ▸ gamma_le q35_dominating

/-- **`γ(Q_35) = 19`, modulo the SAT certificates.**  (`gamma_35_le` is unconditional; the hypothesis is
used only for the lower bound.) -/
theorem gamma_35_eq_19_of_cases35_unsat
    (H : ∀ cs ∈ cases35, ¬ ∃ D : Finset (Sq 35), CaseSat 35 18 cs D) : gamma 35 = 19 :=
  gamma_eq_of_lt_of_dominating (nineteen_le_gamma_35_of_cases35_unsat H) q35_dominating q35_card

/-- `γ(Q_35) = 19` from the mixed hypothesis (plain or symmetry-broken constraints unsatisfiable). -/
theorem gamma_35_eq_19_of_cases35_unsat_mixed
    (H : ∀ cs ∈ cases35, (¬ ∃ D : Finset (Sq 35), CaseSat 35 18 cs D) ∨
      ¬ ∃ D : Finset (Sq 35), CaseSat 35 18 cs D ∧ SymBreak cs D) : gamma 35 = 19 :=
  gamma_eq_of_lt_of_dominating (nineteen_le_gamma_35_of_cases35_unsat_mixed H) q35_dominating q35_card

end QueenDom

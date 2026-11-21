/-
The case list for `n = 32`, `k = 16`: the 11,466 cases of the referee's run log coincide with the
case list `L(32, 16)`; the comparison is a kernel computation (`decide +kernel`, no `native_decide`,
one computation per pair of horizontal margins, see `Cases32Pieces.lean`).
Final theorems for `n = 32` (instances of the generic statements of `Main.lean`).
-/
module

public import QueenDom.Cases32Pieces

@[expose] public section

namespace QueenDom

/-- The case codes of the `n = 32`, `k = 16` run log (`QueenDom/Cases32Data.lean`), in lexicographic
order. -/
def caseCodes32 : List ℕ := tableList 16 caseCodes32T

/-- The cases of the `n = 32`, `k = 16` run log (`frame/out/d_32_16.jsonl`), sorted. -/
def cases32 : List Case := caseCodes32.map Case.ofCode

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The log contains 11,466 cases. -/
theorem cases32_length : cases32.length = 11466 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- There are 3321 canonical frames for `n = 32`, `k = 16`. -/
theorem enumFrames_32_16_length : (enumFrames 32 16).length = 3321 := by decide +kernel

/-- **The case list of the run is the case list `L(32, 16)`** (kernel computation, assembled from one
computation per pair of horizontal margins in `Cases32Pieces.lean`). -/
theorem enumCases_32_16 : enumCases 32 16 = cases32 := enumCases_32_16_table

/-- A case is in the run log iff its frame is canonical and it is admissible for `(32, 16)`. -/
theorem mem_cases32 {cs : Case} : cs ∈ cases32 ↔ CanonAdm 32 16 cs :=
  mem_of_enumCases_eq enumCases_32_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The codes of the 3321 canonical frames are strictly increasing (kernel computation). -/
theorem enumFrames_32_16_chain : ((enumFrames 32 16).map frameCode).IsChain (· < ·) := by
  decide +kernel

/-- The 3321 canonical frames are pairwise distinct. -/
theorem enumFrames_32_16_nodup : (enumFrames 32 16).Nodup :=
  nodup_of_frameCode_chain enumFrames_32_16_chain

/-- The frames occurring in the run log are exactly the canonical frames for `(32, 16)`. -/
theorem frames_cases32 : (cases32.map Case.frame).toFinset = (enumFrames 32 16).toFinset :=
  frames_of_enumCases_eq enumCases_32_16 (by norm_num) (by norm_num)

/-- The run log contains exactly 3321 distinct frames. -/
theorem card_frames_cases32 : (cases32.map Case.frame).toFinset.card = 3321 := by
  rw [card_frames_of_enumCases_eq enumCases_32_16 (by norm_num) (by norm_num) enumFrames_32_16_chain,
    enumFrames_32_16_length]

/-- **Case split for `n = 32`.**  Every dominating set of 16 queens on the `32 × 32` board has a
symmetric image satisfying all constraints of one of the 11,466 cases of the run log. -/
theorem case_split_32 (D : Finset (Sq 32)) (hD : Dominating D) (hc : D.card = 16) :
    ∃ g : Sym, ∃ cs ∈ cases32, CaseSat 32 16 cs (g.image D) :=
  case_split_of_enumCases_eq enumCases_32_16 (by norm_num) D hD hc

/-- **The run log covers every admissible case up to symmetry**: every admissible
(frame, deficit vector) for `(32, 16)` has an image under one of the eight symmetries (acting on cases
by the table `geom.case_images`) in the list of the 11,466 cases of the run. -/
theorem cases32_cover (cs : Case) (h : Admissible 32 16 cs) : ∃ g : Sym, g.actCase cs ∈ cases32 :=
  cover_of_enumCases_eq enumCases_32_16 cs h

/-- **`γ(Q_32) ≥ 17`, modulo the SAT certificates.**  If each of the 11,466 cases of the run log is
unsatisfiable (this is what the DRAT certificates establish, via the CNF encoding of `CaseSat`, outside
Lean), then every dominating set of `Q_32` has at least 17 queens. -/
theorem seventeen_le_card_of_cases32_unsat
    (H : ∀ cs ∈ cases32, ¬ ∃ D : Finset (Sq 32), CaseSat 32 16 cs D) :
    ∀ D : Finset (Sq 32), Dominating D → 17 ≤ D.card :=
  card_lt_of_enumCases_eq enumCases_32_16 (by norm_num) H

/-- The same statement in terms of the domination number. -/
theorem seventeen_le_gamma_32_of_cases32_unsat
    (H : ∀ cs ∈ cases32, ¬ ∃ D : Finset (Sq 32), CaseSat 32 16 cs D) : 17 ≤ gamma 32 :=
  lt_gamma_of_enumCases_eq enumCases_32_16 (by norm_num) H

/-! ### Upper bound: 17 queens dominate `Q_32` -/

/-- The dominating set of 17 queens of `frame/out/plus1_32.json` (squares `(column, row)`). -/
def q32 : Finset (Sq 32) :=
  {(1, 23), (3, 11), (5, 17), (7, 27), (9, 1), (11, 7), (13, 15), (15, 31), (17, 21), (19, 25),
   (21, 9), (23, 3), (25, 19), (27, 5), (29, 13), (30, 30), (31, 29)}

theorem q32_card : q32.card = 17 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The 17 queens dominate `Q_32` (kernel computation over the 1024 squares). -/
theorem q32_dominating : Dominating q32 := by decide +kernel

theorem gamma_32_le : gamma 32 ≤ 17 := q32_card ▸ gamma_le q32_dominating

/-- **`γ(Q_32) = 17`, modulo the SAT certificates.** -/
theorem gamma_32_eq_17_of_cases32_unsat
    (H : ∀ cs ∈ cases32, ¬ ∃ D : Finset (Sq 32), CaseSat 32 16 cs D) : gamma 32 = 17 :=
  gamma_eq_of_lt_of_dominating (seventeen_le_gamma_32_of_cases32_unsat H) q32_dominating q32_card

end QueenDom

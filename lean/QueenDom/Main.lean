/-
Final statements for general `(n, k)`: the domination number, Proposition C in terms of `γ`, the cases
`k = n/2` (even `n`) and `k = (n+1)/2` (odd `n`), and the generic link between an explicit case list `L`
and the enumeration `enumCases n k` (used for `n = 32` in `Cases32.lean` and for `n = 35` in
`Cases35.lean`).
-/
module

public import QueenDom.Enum
public import QueenDom.SymmetryCase

@[expose] public section

namespace QueenDom

open Finset

variable {n : ℕ}

/-- The whole board dominates. -/
theorem dominating_univ (n : ℕ) : Dominating (univ : Finset (Sq n)) := fun p => Or.inl (mem_univ p)

/-- The domination number `γ(Q_n)` of the queen's graph. -/
noncomputable def gamma (n : ℕ) : ℕ := sInf {k | ∃ D : Finset (Sq n), Dominating D ∧ D.card = k}

theorem gamma_le {D : Finset (Sq n)} (hD : Dominating D) : gamma n ≤ D.card :=
  Nat.sInf_le ⟨D, hD, rfl⟩

theorem lt_gamma_iff {k : ℕ} : k < gamma n ↔ ∀ D : Finset (Sq n), Dominating D → k < D.card := by
  constructor
  · intro h D hD
    exact lt_of_lt_of_le h (gamma_le hD)
  · intro h
    obtain ⟨D, hD, hc⟩ := Nat.sInf_mem (s := {k | ∃ D : Finset (Sq n), Dominating D ∧ D.card = k})
      ⟨_, univ, dominating_univ n, rfl⟩
    have := h D hD
    unfold gamma
    omega

/-- A lower bound `γ(Q_n) > k` and an explicit dominating set of `k + 1` queens give `γ(Q_n) = k + 1`. -/
theorem gamma_eq_of_lt_of_dominating {k : ℕ} (hlt : k < gamma n) {D : Finset (Sq n)}
    (hD : Dominating D) (hc : D.card = k + 1) : gamma n = k + 1 := by
  have := gamma_le hD
  omega

/-- **Proposition C** in terms of `γ`: for `k ≤ n - 2`, if every case of the case list `L(n, k)` is
unsatisfiable then `γ(Q_n) > k`. -/
theorem lt_gamma_of_cases_unsat {k : ℕ} (hk : k + 2 ≤ n)
    (H : ∀ cs ∈ enumCases n k, ¬ ∃ D : Finset (Sq n), CaseSat n k cs D) : k < gamma n :=
  lt_gamma_iff.mpr (no_dominating_of_cases_unsat hk fun cs hcs => H cs (mem_enumCases.mpr hcs))

/-- **Case split, list form** (general `n`, `k ≤ n - 2`): every dominating `k`-set has a symmetric image
satisfying all constraints `CaseSat` of some case of the enumerated list `enumCases n k`. -/
theorem case_split_enum {k : ℕ} (hk : k + 2 ≤ n) (D : Finset (Sq n)) (hD : Dominating D)
    (hc : D.card = k) : ∃ g : Sym, ∃ cs ∈ enumCases n k, CaseSat n k cs (g.image D) := by
  obtain ⟨g, cs, hcs, hsat⟩ := case_split hk D hD hc
  exact ⟨g, cs, mem_enumCases.mpr hcs, hsat⟩

/-! ### Even boards, `k = n/2` -/

/-- **Main theorem for even boards.**  Let `n = 2k ≥ 4`.  If `D` is a dominating set of `Q_n` with
`|D| = n/2`, then some image of `D` under one of the eight symmetries of the board satisfies all
constraints `CaseSat` of some case of the case list (canonical frame, admissible deficits). -/
theorem main_even {k : ℕ} (hk : 2 ≤ k) (D : Finset (Sq (2 * k))) (hD : Dominating D)
    (hc : D.card = k) :
    ∃ g : Sym, ∃ cs ∈ enumCases (2 * k) k, CaseSat (2 * k) k cs (g.image D) :=
  case_split_enum (by omega) D hD hc

/-- For `n = 2k ≥ 4`: if every case formula is unsatisfiable then `γ(Q_n) > n/2`. -/
theorem half_lt_gamma_of_cases_unsat {k : ℕ} (hk : 2 ≤ k)
    (H : ∀ cs ∈ enumCases (2 * k) k, ¬ ∃ D : Finset (Sq (2 * k)), CaseSat (2 * k) k cs D) :
    k < gamma (2 * k) :=
  lt_gamma_of_cases_unsat (by omega) H

/-! ### Odd boards, `k = (n+1)/2` (PROOFS.md F.4) -/

/-- **Admissibility for odd `n` and `k = (n+1)/2`** (the constants of F.4): (F) reads
`8 - 2(dR+dC+dT+dS) ≥ 0`, i.e. the deficits sum to at most `4`; (V) reads `2 - dT - dS - 2dR + [w=h]·2 ≥ 0`
and (H) the same with `dC`.  So: if `w > h` then `dT + dS + 2dR ≤ 2`; if `h > w` then `dT + dS + 2dC ≤ 2`;
if `w = h` then `dT + dS + 2dR ≤ 4` and `dT + dS + 2dC ≤ 4`. -/
theorem admissible_odd_iff {n k : ℕ} (hn : n + 1 = 2 * k) (cs : Case) :
    Admissible n k cs ↔
      cs.dR + 1 ≤ k ∧ cs.dC + 1 ≤ k ∧ cs.dT + 1 ≤ k ∧ cs.dS + 1 ≤ k ∧
      cs.ml + cs.mr + cs.dC ≤ k ∧ cs.mb + cs.mt + cs.dR ≤ k ∧
      cs.ml + cs.mr + 2 ≤ n ∧ cs.mb + cs.mt + 2 ≤ n ∧
      cs.dR + cs.dC + cs.dT + cs.dS ≤ 4 ∧
      (cs.ml + cs.mr < cs.mb + cs.mt → cs.dT + cs.dS + 2 * cs.dR ≤ 2) ∧
      (cs.mb + cs.mt < cs.ml + cs.mr → cs.dT + cs.dS + 2 * cs.dC ≤ 2) ∧
      (cs.ml + cs.mr = cs.mb + cs.mt →
        cs.dT + cs.dS + 2 * cs.dR ≤ 4 ∧ cs.dT + cs.dS + 2 * cs.dC ≤ 4) := by
  unfold Admissible
  split_ifs <;> omega

/-- **Main theorem for odd boards.**  Let `n = 2k - 1 ≥ 5` (so `k = (n+1)/2 ≤ n - 2`).  If `D` is a
dominating set of `Q_n` with `|D| = (n+1)/2`, then some image of `D` under one of the eight symmetries of
the board satisfies all constraints `CaseSat` of some case of the case list. -/
theorem main_odd {k : ℕ} (hn : n + 1 = 2 * k) (hk : 3 ≤ k) (D : Finset (Sq n)) (hD : Dominating D)
    (hc : D.card = k) : ∃ g : Sym, ∃ cs ∈ enumCases n k, CaseSat n k cs (g.image D) :=
  case_split_enum (by omega) D hD hc

/-- For odd `n = 2k - 1 ≥ 5`: if every case formula is unsatisfiable then `γ(Q_n) > (n+1)/2`. -/
theorem odd_lt_gamma_of_cases_unsat {k : ℕ} (hn : n + 1 = 2 * k) (hk : 3 ≤ k)
    (H : ∀ cs ∈ enumCases n k, ¬ ∃ D : Finset (Sq n), CaseSat n k cs D) : k < gamma n :=
  lt_gamma_of_cases_unsat (by omega) H

/-! ### An explicit case list `L` with `enumCases n k = L`

For a concrete pair `(n, k)` the case list of a computer run is given as an explicit list `L` (decoded from
the run log), and `enumCases n k = L` is proved by a kernel computation.  The statements below turn such
an equation into the final theorems; `Cases32.lean` and `Cases35.lean` only instantiate them. -/

/-- Decode a case from its decimal code `ml mr mb mt` (two digits each) `dR dC dT dS` (one digit
each); see `scripts/gen_cases.py`. -/
def Case.ofCode (c : ℕ) : Case :=
  ⟨c / 10000000000 % 100, c / 100000000 % 100, c / 1000000 % 100, c / 10000 % 100,
   c / 1000 % 10, c / 100 % 10, c / 10 % 10, c % 10⟩

/-- The frame `(ml, mr, mb, mt)` of a case. -/
def Case.frame (cs : Case) : ℕ × ℕ × ℕ × ℕ := (cs.ml, cs.mr, cs.mb, cs.mt)

/-- Decimal code of a frame (two digits per margin), used only to compare frames quickly. -/
def frameCode (f : ℕ × ℕ × ℕ × ℕ) : ℕ := ((f.1 * 100 + f.2.1) * 100 + f.2.2.1) * 100 + f.2.2.2

/-- A table of case codes, indexed by the horizontal margins: `T[p][q]` holds the codes of the cases with
`(ml, mr) = (p, q)` (missing entries are empty). -/
def tableCodes (T : List (List (List ℕ))) (p q : ℕ) : List ℕ := (T.getD p []).getD q []

/-- The codes of a table, concatenated in the order of `marginPairs k`. -/
def tableList (k : ℕ) (T : List (List (List ℕ))) : List ℕ :=
  (marginPairs k).flatMap fun pq => tableCodes T pq.1 pq.2

/-- If every piece `casesPQ n k p q` agrees with the table entry `T[p][q]`, then `L(n, k)` is the
decoded table.  (The hypotheses are the per-piece kernel computations of `Cases<N>Pieces.lean`.) -/
theorem enumCases_eq_table {n k : ℕ} {T : List (List (List ℕ))}
    (h : ∀ pq ∈ marginPairs k, casesPQ n k pq.1 pq.2 = (tableCodes T pq.1 pq.2).map Case.ofCode) :
    enumCases n k = (tableList k T).map Case.ofCode := by
  rw [enumCases_eq_pieces, tableList, List.map_flatMap]
  exact List.flatMap_congr h

section CaseList

variable {k : ℕ} {L : List Case}

/-- A case is in `L` iff its frame is canonical and it is admissible for `(n, k)`. -/
theorem mem_of_enumCases_eq (hL : enumCases n k = L) {cs : Case} : cs ∈ L ↔ CanonAdm n k cs := by
  rw [← hL, mem_enumCases]

/-- Case split with the explicit list `L`. -/
theorem case_split_of_enumCases_eq (hL : enumCases n k = L) (hk : k + 2 ≤ n) (D : Finset (Sq n))
    (hD : Dominating D) (hc : D.card = k) : ∃ g : Sym, ∃ cs ∈ L, CaseSat n k cs (g.image D) := by
  obtain ⟨g, cs, hcs, hsat⟩ := case_split_enum hk D hD hc
  exact ⟨g, cs, hL ▸ hcs, hsat⟩

/-- `L` covers every admissible (frame, deficit vector) up to symmetry (action `geom.case_images`). -/
theorem cover_of_enumCases_eq (hL : enumCases n k = L) (cs : Case) (h : Admissible n k cs) :
    ∃ g : Sym, g.actCase cs ∈ L := by
  obtain ⟨g, hg⟩ := exists_canonAdm_actCase h
  exact ⟨g, (mem_of_enumCases_eq hL).mpr hg⟩

/-- If every case of `L` is unsatisfiable, every dominating set has more than `k` queens. -/
theorem card_lt_of_enumCases_eq (hL : enumCases n k = L) (hk : k + 2 ≤ n)
    (H : ∀ cs ∈ L, ¬ ∃ D : Finset (Sq n), CaseSat n k cs D) :
    ∀ D : Finset (Sq n), Dominating D → k < D.card :=
  no_dominating_of_cases_unsat hk fun cs hcs => H cs ((mem_of_enumCases_eq hL).mpr hcs)

/-- If every case of `L` is unsatisfiable, `γ(Q_n) > k`. -/
theorem lt_gamma_of_enumCases_eq (hL : enumCases n k = L) (hk : k + 2 ≤ n)
    (H : ∀ cs ∈ L, ¬ ∃ D : Finset (Sq n), CaseSat n k cs D) : k < gamma n :=
  lt_gamma_iff.mpr (card_lt_of_enumCases_eq hL hk H)

/-- A frame with zero deficits is admissible as soon as `1 ≤ k` and `n ≤ 2k`. -/
theorem admissible_zero_deficits {p q r s : ℕ} (hk1 : 1 ≤ k) (hnk : n ≤ 2 * k) (hpq : p + q ≤ k)
    (hrs : r + s ≤ k) (h7 : p + q + 2 ≤ n) (h8 : r + s + 2 ≤ n) :
    Admissible n k ⟨p, q, r, s, 0, 0, 0, 0⟩ := by
  unfold Admissible
  simp only
  split_ifs <;> omega

/-- The frames occurring in `L` are exactly the canonical frames for `(n, k)` (if `1 ≤ k`, `n ≤ 2k`). -/
theorem frames_of_enumCases_eq (hL : enumCases n k = L) (hk1 : 1 ≤ k) (hnk : n ≤ 2 * k) :
    (L.map Case.frame).toFinset = (enumFrames n k).toFinset := by
  ext ⟨p, q, r, s⟩
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨cs, hcs, hf⟩
    obtain ⟨hcan, hadm⟩ := (mem_of_enumCases_eq hL).mp hcs
    simp only [Case.frame, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hf
    obtain ⟨-, -, -, -, h5, h6, h7, h8, -⟩ := hadm
    exact mem_enumFrames.mpr ⟨by omega, by omega, hcan, h7, h8⟩
  · intro hf
    obtain ⟨h1, h2, hcan, h3, h4⟩ := mem_enumFrames.mp hf
    exact ⟨⟨p, q, r, s, 0, 0, 0, 0⟩, (mem_of_enumCases_eq hL).mpr
      ⟨hcan, admissible_zero_deficits hk1 hnk h1 h2 h3 h4⟩, rfl⟩

/-- A list of frames whose codes increase strictly has no duplicates. -/
theorem nodup_of_frameCode_chain {fs : List (ℕ × ℕ × ℕ × ℕ)} (h : (fs.map frameCode).IsChain (· < ·)) :
    fs.Nodup :=
  List.Nodup.of_map frameCode (h.pairwise.imp fun h => ne_of_lt h)

/-- Number of distinct frames of `L`, given that the frame codes of `enumFrames n k` increase strictly
(kernel computation for concrete `(n, k)`). -/
theorem card_frames_of_enumCases_eq (hL : enumCases n k = L) (hk1 : 1 ≤ k) (hnk : n ≤ 2 * k)
    (hchain : ((enumFrames n k).map frameCode).IsChain (· < ·)) :
    (L.map Case.frame).toFinset.card = (enumFrames n k).length := by
  rw [frames_of_enumCases_eq hL hk1 hnk,
    List.toFinset_card_of_nodup (nodup_of_frameCode_chain hchain)]

end CaseList

end QueenDom

/-
Cases, admissibility and the case-split completeness theorem (PROOFS.md F.2, Proposition C, and the
part of Lemma E (F.3) that does not concern the CNF encoding).
-/
module

public import QueenDom.Consequences
public import QueenDom.Symmetry

@[expose] public section

namespace QueenDom

open Finset

variable {n : ℕ}

/-- A *case* `(ml, mr, mb, mt; dR, dC, dT, dS)`: the four margins of the frame and the four
deficits. -/
structure Case where
  ml : ℕ
  mr : ℕ
  mb : ℕ
  mt : ℕ
  dR : ℕ
  dC : ℕ
  dT : ℕ
  dS : ℕ
deriving DecidableEq, Repr

/-- The admissibility conditions of F.2 (`geom.admissible`), written without subtraction:
* each deficit is at most `k - 1`;
* `ml + mr ≤ k - dC`, `mb + mt ≤ k - dR`  (E1);
* `w = n-1-ml-mr ≥ 1`, `h = n-1-mb-mt ≥ 1`;
* (C1): `8k - 4n + 4 - 2(dR+dC+dT+dS) ≥ 0`;
* (C2): if `w ≥ h` then `4k - 2n - dT - dS - 2dR + 2[w = h] ≥ 0`;
        if `h ≥ w` then `4k - 2n - dT - dS - 2dC + 2[w = h] ≥ 0`.
(`w ≥ h` iff `ml + mr ≤ mb + mt`.)  `admissible_iff_py` is the comparison with the Python text. -/
def Admissible (n k : ℕ) (cs : Case) : Prop :=
  cs.dR + 1 ≤ k ∧ cs.dC + 1 ≤ k ∧ cs.dT + 1 ≤ k ∧ cs.dS + 1 ≤ k ∧
  cs.ml + cs.mr + cs.dC ≤ k ∧ cs.mb + cs.mt + cs.dR ≤ k ∧
  cs.ml + cs.mr + 2 ≤ n ∧ cs.mb + cs.mt + 2 ≤ n ∧
  4 * n + 2 * (cs.dR + cs.dC + cs.dT + cs.dS) ≤ 8 * k + 4 ∧
  (cs.ml + cs.mr ≤ cs.mb + cs.mt →
    2 * n + cs.dT + cs.dS + 2 * cs.dR ≤ 4 * k + (if cs.ml + cs.mr = cs.mb + cs.mt then 2 else 0)) ∧
  (cs.mb + cs.mt ≤ cs.ml + cs.mr →
    2 * n + cs.dT + cs.dS + 2 * cs.dC ≤ 4 * k + (if cs.ml + cs.mr = cs.mb + cs.mt then 2 else 0))

instance (n k : ℕ) (cs : Case) : Decidable (Admissible n k cs) := by
  unfold Admissible; infer_instance

/-- `geom.admissible(n, k, case)` transcribed literally over the integers (each `if ...: return False`
of the Python function is one negated conjunct). -/
def AdmissiblePy (n k ml mr mb mt dR dC dT dS : ℤ) : Prop :=
  ¬ (min (min dR dC) (min dT dS) < 0 ∨ max (max dR dC) (max dT dS) > k - 1) ∧
  ¬ (ml + mr > k - dC ∨ mb + mt > k - dR) ∧
  ¬ (n - 1 - ml - mr < 1 ∨ n - 1 - mb - mt < 1) ∧
  ¬ (8 * k - 4 * n + 4 - 2 * (dR + dC + dT + dS) < 0) ∧
  ¬ (n - 1 - ml - mr ≥ n - 1 - mb - mt ∧
      4 * k - 2 * n - dT - dS - 2 * dR + (if n - 1 - ml - mr = n - 1 - mb - mt then 2 else 0) < 0) ∧
  ¬ (n - 1 - mb - mt ≥ n - 1 - ml - mr ∧
      4 * k - 2 * n - dT - dS - 2 * dC + (if n - 1 - ml - mr = n - 1 - mb - mt then 2 else 0) < 0)

theorem admissible_iff_py (n k : ℕ) (cs : Case) :
    Admissible n k cs ↔ AdmissiblePy n k cs.ml cs.mr cs.mb cs.mt cs.dR cs.dC cs.dT cs.dS := by
  unfold Admissible AdmissiblePy
  simp only [min_lt_iff, lt_max_iff, gt_iff_lt, ge_iff_le]
  split_ifs <;> omega

/-- A case of the case list `L(n, k)`: canonical frame and admissible. -/
def CanonAdm (n k : ℕ) (cs : Case) : Prop := Canon cs.ml cs.mr cs.mb cs.mt ∧ Admissible n k cs

instance (n k : ℕ) (cs : Case) : Decidable (CanonAdm n k cs) := by
  unfold CanonAdm; infer_instance

/-- For `k = n/2` admissibility reads: the deficits sum to at most `2`; if `w > h` then
`dR = dT = dS = 0`; if `h > w` then `dC = dT = dS = 0`; if `w = h` then `dT + dS + 2 dR ≤ 2` and
`dT + dS + 2 dC ≤ 2`. -/
theorem admissible_half_iff (k : ℕ) (cs : Case) :
    Admissible (2 * k) k cs ↔
      cs.dR + 1 ≤ k ∧ cs.dC + 1 ≤ k ∧ cs.dT + 1 ≤ k ∧ cs.dS + 1 ≤ k ∧
      cs.ml + cs.mr + cs.dC ≤ k ∧ cs.mb + cs.mt + cs.dR ≤ k ∧
      cs.ml + cs.mr + 2 ≤ 2 * k ∧ cs.mb + cs.mt + 2 ≤ 2 * k ∧
      cs.dR + cs.dC + cs.dT + cs.dS ≤ 2 ∧
      (cs.ml + cs.mr < cs.mb + cs.mt → cs.dR = 0 ∧ cs.dT = 0 ∧ cs.dS = 0) ∧
      (cs.mb + cs.mt < cs.ml + cs.mr → cs.dC = 0 ∧ cs.dT = 0 ∧ cs.dS = 0) ∧
      (cs.ml + cs.mr = cs.mb + cs.mt →
        cs.dT + cs.dS + 2 * cs.dR ≤ 2 ∧ cs.dT + cs.dS + 2 * cs.dC ≤ 2) := by
  unfold Admissible
  split_ifs <;> omega

/-- The case of a set `D` with frame `(a, b, c, d)` (`geom.case_of`). -/
def caseOf (D : Finset (Sq n)) (a b c d : Fin n) : Case :=
  ⟨(a : ℕ), n - 1 - (b : ℕ), (c : ℕ), n - 1 - (d : ℕ), defR D, defC D, defT D, defS D⟩

/-- The frame-dependent constraints of the formula `Φ(case)` (F.3), for a frame `(a, b, c, d)`:
* FRAME: `a < b` are the extreme empty columns, `c < d` the extreme empty rows, and
  `a = ml`, `b = n-1-mr`, `c = mb`, `d = n-1-mt`;
* (F): the three waste terms of the border sum to `8k - 4n + 4 - 2(dR+dC+dT+dS)`;
* (V): if `w ≥ h`, the three waste terms of the vertical sides sum to
  `4k - 2n - dT - dS - 2dR + [w = h]([u0] + [v0])`;
* (H): if `h ≥ w`, the same for the horizontal sides with `dC`.
(The CNF imposes (F), (V), (H) as upper bounds; the equalities proved here imply them.) -/
def FrameConstraints (n k : ℕ) (cs : Case) (D : Finset (Sq n)) (a b c d : Fin n) : Prop :=
  IsFrame D a b c d ∧
  (a : ℕ) = cs.ml ∧ (b : ℕ) + cs.mr + 1 = n ∧ (c : ℕ) = cs.mb ∧ (d : ℕ) + cs.mt + 1 = n ∧
  wasteF D (border a b c d) + waste2 D (border a b c d) + needy2 D (border a b c d) + 4 * n
      + 2 * (cs.dR + cs.dC + cs.dT + cs.dS) = 8 * k + 4 ∧
  ((d : ℕ) - c ≤ (b : ℕ) - a →
    zeros D (vsides a b c d) + waste2 D (vsides a b c d) + needy2 D (vsides a b c d) + 2 * n
      + cs.dT + cs.dS + 2 * cs.dR = 4 * k + sqTerm D a b c d) ∧
  ((b : ℕ) - a ≤ (d : ℕ) - c →
    zeros D (hsides a b c d) + waste2 D (hsides a b c d) + needy2 D (hsides a b c d) + 2 * n
      + cs.dT + cs.dS + 2 * cs.dC = 4 * k + sqTerm D a b c d)

/-- `D` satisfies all constraints of the case `cs` for `(n, k)`: this is the semantic content of the
formula `Φ(case)` of F.3 (one field per clause group of `frame/enc.py`). -/
structure CaseSat (n k : ℕ) (cs : Case) (D : Finset (Sq n)) : Prop where
  /-- exactly `k` queens -/
  card : D.card = k
  /-- DOM -/
  dom : Dominating D
  /-- CARD: exactly `k - dR` occupied rows, etc. -/
  cardR : (occR D).card + cs.dR = k
  cardC : (occC D).card + cs.dC = k
  cardT : (occT D).card + cs.dT = k
  cardS : (occS D).card + cs.dS = k
  /-- AMO: for a type with deficit `0`, no two queens on a line of this type -/
  amoR : cs.dR = 0 → Set.InjOn Prod.snd (D : Set (Sq n))
  amoC : cs.dC = 0 → Set.InjOn Prod.fst (D : Set (Sq n))
  amoT : cs.dT = 0 → Set.InjOn dg (D : Set (Sq n))
  amoS : cs.dS = 0 → Set.InjOn sm (D : Set (Sq n))
  /-- FRAME, (F), (V), (H) -/
  frame : ∃ a b c d : Fin n, FrameConstraints n k cs D a b c d

section

variable {k : ℕ} {D : Finset (Sq n)} {a b c d : Fin n}

/-- **Lemma E, semantic part.**  A dominating `k`-set with frame `(a, b, c, d)` satisfies all
constraints of its case. -/
theorem caseSat_of_frame (hD : Dominating D) (hc : D.card = k) (h : IsFrame D a b c d) :
    CaseSat n k (caseOf D a b c d) D := by
  subst hc
  have hb := b.isLt
  have hd := d.isLt
  refine ⟨rfl, hD, occR_card_add_defR D, occC_card_add_defC D, occT_card_add_defT D,
    occS_card_add_defS D, (defR_eq_zero_iff D).mp, (defC_eq_zero_iff D).mp, (defT_eq_zero_iff D).mp,
    (defS_eq_zero_iff D).mp, a, b, c, d, h, rfl, ?_, rfl, ?_, h.frame_identity_dom hD,
    fun hwh => h.side_identity_V_dom hD hwh, fun hhw => h.side_identity_H_dom hD hhw⟩
  · show (b : ℕ) + (n - 1 - (b : ℕ)) + 1 = n
    omega
  · show (d : ℕ) + (n - 1 - (d : ℕ)) + 1 = n
    omega

/-- The case of a dominating `k`-set is admissible (F.2). -/
theorem admissible_of_frame (hD : Dominating D) (hc : D.card = k) (h : IsFrame D a b c d) :
    Admissible n k (caseOf D a b c d) := by
  subst hc
  have hb := b.isLt
  have hd := d.isLt
  have hab : (a : ℕ) < b := h.hab
  have hcd : (c : ℕ) < d := h.hcd
  have hne : D.Nonempty := hD.nonempty (by omega)
  have hR := occR_card_add_defR D
  have hC := occC_card_add_defC D
  have hT := occT_card_add_defT D
  have hS := occS_card_add_defS D
  have hR0 := occR_card_pos hne
  have hC0 := occC_card_pos hne
  have hT0 := occT_card_pos hne
  have hS0 := occS_card_pos hne
  have hmc := h.margin_cols
  have hmr := h.margin_rows
  have hF := h.frame_identity_dom hD
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show defR D + 1 ≤ D.card; omega
  · show defC D + 1 ≤ D.card; omega
  · show defT D + 1 ≤ D.card; omega
  · show defS D + 1 ≤ D.card; omega
  · show (a : ℕ) + (n - 1 - (b : ℕ)) + defC D ≤ D.card; omega
  · show (c : ℕ) + (n - 1 - (d : ℕ)) + defR D ≤ D.card; omega
  · show (a : ℕ) + (n - 1 - (b : ℕ)) + 2 ≤ n; omega
  · show (c : ℕ) + (n - 1 - (d : ℕ)) + 2 ≤ n; omega
  · show 4 * n + 2 * (defR D + defC D + defT D + defS D) ≤ 8 * D.card + 4; omega
  · show (a : ℕ) + (n - 1 - (b : ℕ)) ≤ (c : ℕ) + (n - 1 - (d : ℕ)) →
      2 * n + defT D + defS D + 2 * defR D ≤ 4 * D.card
        + (if (a : ℕ) + (n - 1 - (b : ℕ)) = (c : ℕ) + (n - 1 - (d : ℕ)) then 2 else 0)
    intro hle
    have := h.deficit_bound_V hD (by omega)
    split_ifs at this ⊢ <;> omega
  · show (c : ℕ) + (n - 1 - (d : ℕ)) ≤ (a : ℕ) + (n - 1 - (b : ℕ)) →
      2 * n + defT D + defS D + 2 * defC D ≤ 4 * D.card
        + (if (a : ℕ) + (n - 1 - (b : ℕ)) = (c : ℕ) + (n - 1 - (d : ℕ)) then 2 else 0)
    intro hle
    have := h.deficit_bound_H hD (by omega)
    split_ifs at this ⊢ <;> omega

end

/-- **Case-split completeness theorem** (general `n`, `k ≤ n - 2`).  Every dominating `k`-set of `Q_n`
has an image under one of the eight symmetries of the board that satisfies all constraints of some
case with canonical frame and admissible (frame, deficits). -/
theorem case_split {k : ℕ} (hk : k + 2 ≤ n) (D : Finset (Sq n)) (hD : Dominating D)
    (hc : D.card = k) :
    ∃ g : Sym, ∃ cs : Case, CanonAdm n k cs ∧ CaseSat n k cs (g.image D) := by
  obtain ⟨a, b, c, d, hF⟩ := exists_isFrame_of_card D (by omega)
  obtain ⟨g, hg⟩ := exists_canon (margins a b c d)
  obtain ⟨a', b', c', d', hF', hm⟩ := HasMargins.sym ⟨a, b, c, d, hF, rfl⟩ g
  have hD' := hD.sym g
  have hc' : (g.image D).card = k := by rw [g.card_image, hc]
  refine ⟨g, caseOf (g.image D) a' b' c' d', ⟨?_, admissible_of_frame hD' hc' hF'⟩,
    caseSat_of_frame hD' hc' hF'⟩
  rw [← hm] at hg
  exact hg

/-- **Proposition C.**  Let `k ≤ n - 2`.  If no case of the case list is satisfiable, then `Q_n` has
no dominating set of size `≤ k`, i.e. `γ(Q_n) > k`. -/
theorem no_dominating_of_cases_unsat {k : ℕ} (hk : k + 2 ≤ n)
    (H : ∀ cs : Case, CanonAdm n k cs → ¬ ∃ D : Finset (Sq n), CaseSat n k cs D) :
    ∀ D : Finset (Sq n), Dominating D → k < D.card := by
  intro D hD
  by_contra hlt
  have hkn : k ≤ n * n := le_trans (by omega) (Nat.le_mul_self n)
  obtain ⟨D', hD', hc'⟩ := exists_dominating_card_eq hD (not_lt.mp hlt) hkn
  obtain ⟨g, cs, hcs, hsat⟩ := case_split hk D' hD' hc'
  exact H cs hcs ⟨_, hsat⟩

/-- **The case `k = n/2`** (even `n ≥ 4`): if `D` is a dominating set of `Q_n` with `|D| = n/2`, then
some symmetric image of `D` satisfies all constraints of a case with canonical frame and admissible
(frame, deficits). -/
theorem case_split_half {k : ℕ} (hk : 2 ≤ k) (D : Finset (Sq (2 * k))) (hD : Dominating D)
    (hc : D.card = k) :
    ∃ g : Sym, ∃ cs : Case, CanonAdm (2 * k) k cs ∧ CaseSat (2 * k) k cs (g.image D) :=
  case_split (by omega) D hD hc

/-- For even `n = 2k ≥ 4`: if every case of the case list is unsatisfiable then `γ(Q_n) > n/2`. -/
theorem gamma_gt_half_of_cases_unsat {k : ℕ} (hk : 2 ≤ k)
    (H : ∀ cs : Case, CanonAdm (2 * k) k cs → ¬ ∃ D : Finset (Sq (2 * k)), CaseSat (2 * k) k cs D) :
    ∀ D : Finset (Sq (2 * k)), Dominating D → k < D.card :=
  no_dominating_of_cases_unsat (by omega) H

end QueenDom

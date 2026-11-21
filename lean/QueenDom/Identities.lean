/-
The frame identity (F) and the side identities (V), (H)  (PROOFS.md F.0 (E5) and F.1).

All three are exact equalities, valid for every set `D` with a frame (dominating or not); the term
`uncov D X` is the `U_X` of the hand proofs.
-/
module

public import QueenDom.Geometry

@[expose] public section

namespace QueenDom

open Finset

variable {n : ℕ}

/-! ### Double counting of incidences between occupied diagonals and a set `X` of squares -/

/-- Incidences (occupied difference diagonal, square of `X`), counted by diagonals and by squares. -/
theorem sum_betaT (D X : Finset (Sq n)) :
    ∑ t ∈ occT D, betaT X t = (X.filter fun p => dg p ∈ occT D).card := by
  have h := card_eq_sum_card_fiberwise (f := dg) (s := X.filter fun p => dg p ∈ occT D)
    (t := occT D) (by intro p hp; exact mem_coe.mpr (mem_filter.mp (mem_coe.mp hp)).2)
  rw [h]
  refine sum_congr rfl fun t ht => ?_
  unfold betaT
  congr 1
  ext p
  simp only [mem_filter]
  constructor
  · rintro ⟨hp, e⟩; exact ⟨⟨hp, e ▸ ht⟩, e⟩
  · rintro ⟨⟨hp, -⟩, e⟩; exact ⟨hp, e⟩

/-- Incidences (occupied sum diagonal, square of `X`), counted by diagonals and by squares. -/
theorem sum_betaS (D X : Finset (Sq n)) :
    ∑ s ∈ occS D, betaS X s = (X.filter fun p => sm p ∈ occS D).card := by
  have h := card_eq_sum_card_fiberwise (f := sm) (s := X.filter fun p => sm p ∈ occS D)
    (t := occS D) (by intro p hp; exact mem_coe.mpr (mem_filter.mp (mem_coe.mp hp)).2)
  rw [h]
  refine sum_congr rfl fun t ht => ?_
  unfold betaS
  congr 1
  ext p
  simp only [mem_filter]
  constructor
  · rintro ⟨hp, e⟩; exact ⟨⟨hp, e ▸ ht⟩, e⟩
  · rintro ⟨⟨hp, -⟩, e⟩; exact ⟨hp, e⟩

/-- Counting the incidences by squares: a needy square contributes `1 + [m = 2] - [m = 0]`, the
non-needy squares contribute `waste2`. -/
theorem incidences_by_squares (D X : Finset (Sq n)) :
    (X.filter fun p => dg p ∈ occT D).card + (X.filter fun p => sm p ∈ occS D).card + uncov D X
      = (X.filter (Needy D)).card + needy2 D X + waste2 D X := by
  unfold uncov needy2 waste2
  simp only [card_filter, ← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  by_cases h1 : Needy D p <;> by_cases h2 : dg p ∈ occT D <;> by_cases h3 : sm p ∈ occS D <;>
    simp [h1, h2, h3]

/-- The double count: `I + U_X = #needy(X) + #{needy, m = 2} + #{(L, s) : s non-needy}`. -/
theorem double_count (D X : Finset (Sq n)) :
    ∑ t ∈ occT D, betaT X t + ∑ s ∈ occS D, betaS X s + uncov D X
      = (X.filter (Needy D)).card + needy2 D X + waste2 D X := by
  rw [sum_betaT, sum_betaS, incidences_by_squares]

/-- `waste2` is literally the number of pairs (occupied diagonal `L`, non-needy square of `X` on `L`). -/
theorem waste2_eq_card_pairs (D X : Finset (Sq n)) :
    waste2 D X = ((occT D ×ˢ X).filter fun q => ¬ Needy D q.2 ∧ dg q.2 = q.1).card
      + ((occS D ×ˢ X).filter fun q => ¬ Needy D q.2 ∧ sm q.2 = q.1).card := by
  unfold waste2
  congr 1
  · refine card_bij (fun p _ => (dg p, p)) ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_product] at hp ⊢
      exact ⟨⟨hp.2.2, hp.1⟩, hp.2.1, trivial⟩
    · intro p _ q _ h
      exact (Prod.mk.inj h).2
    · rintro ⟨t, p⟩ hq
      simp only [mem_filter, mem_product] at hq
      refine ⟨p, ?_, ?_⟩
      · simp only [mem_filter]
        exact ⟨hq.1.2, hq.2.1, hq.2.2 ▸ hq.1.1⟩
      · rw [hq.2.2]
  · refine card_bij (fun p _ => (sm p, p)) ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_product] at hp ⊢
      exact ⟨⟨hp.2.2, hp.1⟩, hp.2.1, trivial⟩
    · intro p _ q _ h
      exact (Prod.mk.inj h).2
    · rintro ⟨t, p⟩ hq
      simp only [mem_filter, mem_product] at hq
      refine ⟨p, ?_, ?_⟩
      · simp only [mem_filter]
        exact ⟨hq.1.2, hq.2.1, hq.2.2 ▸ hq.1.1⟩
      · rw [hq.2.2]

/-! ### Theorem F (frame identity) -/

theorem wasteF_add (D X : Finset (Sq n)) (hT : ∀ t, betaT X t ≤ 2) (hS : ∀ s, betaS X s ≤ 2) :
    wasteF D X + (∑ t ∈ occT D, betaT X t + ∑ s ∈ occS D, betaS X s)
      = 2 * (occT D).card + 2 * (occS D).card := by
  have h1 : ∑ t ∈ occT D, (2 - betaT X t) + ∑ t ∈ occT D, betaT X t = 2 * (occT D).card := by
    rw [← sum_add_distrib, sum_congr rfl (fun t _ => Nat.sub_add_cancel (hT t)), sum_const,
      smul_eq_mul, mul_comm]
  have h2 : ∑ s ∈ occS D, (2 - betaS X s) + ∑ s ∈ occS D, betaS X s = 2 * (occS D).card := by
    rw [← sum_add_distrib, sum_congr rfl (fun s _ => Nat.sub_add_cancel (hS s)), sum_const,
      smul_eq_mul, mul_comm]
  unfold wasteF
  omega

section frame

variable {D : Finset (Sq n)} {a b c d : Fin n}

/-- **Theorem F**, in natural numbers, in terms of `|R|, |C|, |T|, |S|`:
`∑_L (2 - β(L)) + #{(L, s) : s non-needy} + #{needy, m = 2} + N = 2(|T| + |S|) + U`,
with `N + 4 = 2(n - |R|) + 2(n - |C|)`. -/
theorem IsFrame.frame_identity_nat (h : IsFrame D a b c d) :
    wasteF D (border a b c d) + waste2 D (border a b c d) + needy2 D (border a b c d)
        + 2 * (n - (occR D).card) + 2 * (n - (occC D).card)
      = 2 * (occT D).card + 2 * (occS D).card + 4 + uncov D (border a b c d) := by
  have h1 := wasteF_add D (border a b c d) (betaT_border_le_two a b c d) (betaS_border_le_two a b c d)
  have h2 := double_count D (border a b c d)
  have h3 := h.card_needy_border
  omega

/-- **Theorem F (frame identity)** as in PROOFS.md F.1:
`∑_L (2 - β(L)) + #{(L, s) : s non-needy} + #{needy, m = 2}
   = 8k - 4n + 4 - 2(dR + dC + dT + dS) + U`,  with `k = |D|`. -/
theorem IsFrame.frame_identity (h : IsFrame D a b c d) :
    ((wasteF D (border a b c d) + waste2 D (border a b c d) + needy2 D (border a b c d) : ℕ) : ℤ)
      = 8 * (D.card : ℤ) - 4 * (n : ℤ) + 4 - 2 * ((defR D : ℤ) + defC D + defT D + defS D)
        + uncov D (border a b c d) := by
  have h0 := h.frame_identity_nat
  have hR := occR_card_add_defR D
  have hC := occC_card_add_defC D
  have hT := occT_card_add_defT D
  have hS := occS_card_add_defS D
  have hRn := occR_card_le_n D
  have hCn := occC_card_le_n D
  omega

end frame

/-! ### (E5): diagonals and the vertical / horizontal sides -/

section E5

variable {a b c d : Fin n}

/-- (E5) If `w ≥ h`, a difference diagonal other than `u0` (when `w = h`) contains at most one square
of the vertical sides. -/
theorem betaT_vsides_le_one (hab : a < b) (hcd : c < d) (hwh : (d : ℕ) - c ≤ (b : ℕ) - a) (t : ℤ)
    (hne : ¬ ((b : ℕ) - a = (d : ℕ) - c ∧ t = (c : ℤ) - (a : ℤ))) : betaT (vsides a b c d) t ≤ 1 := by
  unfold betaT
  rw [card_le_one]
  intro p hp q hq
  simp only [mem_filter, mem_vsides] at hp hq
  simp only [dg, Fin.le_def, Fin.lt_def, Fin.ext_iff] at *
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> omega

/-- (E5) If `w ≥ h`, a sum diagonal other than `v0` (when `w = h`) contains at most one square of the
vertical sides. -/
theorem betaS_vsides_le_one (hab : a < b) (hcd : c < d) (hwh : (d : ℕ) - c ≤ (b : ℕ) - a) (s : ℕ)
    (hne : ¬ ((b : ℕ) - a = (d : ℕ) - c ∧ s = (a : ℕ) + (d : ℕ))) : betaS (vsides a b c d) s ≤ 1 := by
  unfold betaS
  rw [card_le_one]
  intro p hp q hq
  simp only [mem_filter, mem_vsides] at hp hq
  simp only [sm, Fin.le_def, Fin.lt_def, Fin.ext_iff] at *
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> omega

/-- (E5) If `h ≥ w`, a difference diagonal other than `u0` (when `w = h`) contains at most one square
of the horizontal sides. -/
theorem betaT_hsides_le_one (hab : a < b) (hcd : c < d) (hhw : (b : ℕ) - a ≤ (d : ℕ) - c) (t : ℤ)
    (hne : ¬ ((b : ℕ) - a = (d : ℕ) - c ∧ t = (c : ℤ) - (a : ℤ))) : betaT (hsides a b c d) t ≤ 1 := by
  unfold betaT
  rw [card_le_one]
  intro p hp q hq
  simp only [mem_filter, mem_hsides] at hp hq
  simp only [dg, Fin.le_def, Fin.lt_def, Fin.ext_iff] at *
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> omega

/-- (E5) If `h ≥ w`, a sum diagonal other than `v0` (when `w = h`) contains at most one square of the
horizontal sides. -/
theorem betaS_hsides_le_one (hab : a < b) (hcd : c < d) (hhw : (b : ℕ) - a ≤ (d : ℕ) - c) (s : ℕ)
    (hne : ¬ ((b : ℕ) - a = (d : ℕ) - c ∧ s = (a : ℕ) + (d : ℕ))) : betaS (hsides a b c d) s ≤ 1 := by
  unfold betaS
  rw [card_le_one]
  intro p hp q hq
  simp only [mem_filter, mem_hsides] at hp hq
  simp only [sm, Fin.le_def, Fin.lt_def, Fin.ext_iff] at *
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> omega

/-- (E5) If `w = h`, the difference diagonal `u0 = {t = c - a}` meets the vertical sides exactly in
the two corners `(a, c)`, `(b, d)`. -/
theorem vsides_filter_u0 (hab : a < b) (hcd : c < d) (hsq : (b : ℕ) - a = (d : ℕ) - c) :
    ((vsides a b c d).filter fun p => dg p = (c : ℤ) - (a : ℤ)) = {(a, c), (b, d)} := by
  ext ⟨x, y⟩
  simp only [mem_filter, mem_vsides, mem_insert, mem_singleton, Prod.mk.injEq]
  simp only [dg, Fin.le_def, Fin.lt_def, Fin.ext_iff] at *
  omega

/-- (E5) If `w = h`, the sum diagonal `v0 = {s = a + d}` meets the vertical sides exactly in the two
corners `(a, d)`, `(b, c)`. -/
theorem vsides_filter_v0 (hab : a < b) (hcd : c < d) (hsq : (b : ℕ) - a = (d : ℕ) - c) :
    ((vsides a b c d).filter fun p => sm p = (a : ℕ) + (d : ℕ)) = {(a, d), (b, c)} := by
  ext ⟨x, y⟩
  simp only [mem_filter, mem_vsides, mem_insert, mem_singleton, Prod.mk.injEq]
  simp only [sm, Fin.le_def, Fin.lt_def, Fin.ext_iff] at *
  omega

/-- (E5) If `w = h`, `u0` meets the horizontal sides exactly in the corners `(a, c)`, `(b, d)`. -/
theorem hsides_filter_u0 (hab : a < b) (hcd : c < d) (hsq : (b : ℕ) - a = (d : ℕ) - c) :
    ((hsides a b c d).filter fun p => dg p = (c : ℤ) - (a : ℤ)) = {(a, c), (b, d)} := by
  ext ⟨x, y⟩
  simp only [mem_filter, mem_hsides, mem_insert, mem_singleton, Prod.mk.injEq]
  simp only [dg, Fin.le_def, Fin.lt_def, Fin.ext_iff] at *
  omega

/-- (E5) If `w = h`, `v0` meets the horizontal sides exactly in the corners `(a, d)`, `(b, c)`. -/
theorem hsides_filter_v0 (hab : a < b) (hcd : c < d) (hsq : (b : ℕ) - a = (d : ℕ) - c) :
    ((hsides a b c d).filter fun p => sm p = (a : ℕ) + (d : ℕ)) = {(a, d), (b, c)} := by
  ext ⟨x, y⟩
  simp only [mem_filter, mem_hsides, mem_insert, mem_singleton, Prod.mk.injEq]
  simp only [sm, Fin.le_def, Fin.lt_def, Fin.ext_iff] at *
  omega

theorem card_corner_pair {x x' y y' : Fin n} (h : x < x') :
    ({(x, y), (x', y')} : Finset (Sq n)).card = 2 :=
  card_pair fun e => absurd (Prod.mk.inj e).1 (ne_of_lt h)

theorem betaT_vsides_u0 (hab : a < b) (hcd : c < d) (hsq : (b : ℕ) - a = (d : ℕ) - c) :
    betaT (vsides a b c d) ((c : ℤ) - (a : ℤ)) = 2 := by
  unfold betaT; rw [vsides_filter_u0 hab hcd hsq, card_corner_pair hab]

theorem betaS_vsides_v0 (hab : a < b) (hcd : c < d) (hsq : (b : ℕ) - a = (d : ℕ) - c) :
    betaS (vsides a b c d) ((a : ℕ) + (d : ℕ)) = 2 := by
  unfold betaS; rw [vsides_filter_v0 hab hcd hsq, card_corner_pair hab]

theorem betaT_hsides_u0 (hab : a < b) (hcd : c < d) (hsq : (b : ℕ) - a = (d : ℕ) - c) :
    betaT (hsides a b c d) ((c : ℤ) - (a : ℤ)) = 2 := by
  unfold betaT; rw [hsides_filter_u0 hab hcd hsq, card_corner_pair hab]

theorem betaS_hsides_v0 (hab : a < b) (hcd : c < d) (hsq : (b : ℕ) - a = (d : ℕ) - c) :
    betaS (hsides a b c d) ((a : ℕ) + (d : ℕ)) = 2 := by
  unfold betaS; rw [hsides_filter_v0 hab hcd hsq, card_corner_pair hab]

end E5

/-! ### Counting incidences with the sides by diagonals -/

/-- If `β(L) ≤ 1` for all diagonals except `β(u0) = β(v0) = 2` when the box is square, then
`I = |T| + |S| - #{occupied L : β(L) = 0} + [w = h]([u0 occupied] + [v0 occupied])`. -/
theorem incidences_sides (D X : Finset (Sq n)) (a b c d : Fin n)
    (hT1 : ∀ t, ¬ ((b : ℕ) - a = (d : ℕ) - c ∧ t = (c : ℤ) - (a : ℤ)) → betaT X t ≤ 1)
    (hS1 : ∀ s, ¬ ((b : ℕ) - a = (d : ℕ) - c ∧ s = (a : ℕ) + (d : ℕ)) → betaS X s ≤ 1)
    (hT2 : (b : ℕ) - a = (d : ℕ) - c → betaT X ((c : ℤ) - (a : ℤ)) = 2)
    (hS2 : (b : ℕ) - a = (d : ℕ) - c → betaS X ((a : ℕ) + (d : ℕ)) = 2) :
    ∑ t ∈ occT D, betaT X t + ∑ s ∈ occS D, betaS X s + zeros D X
      = (occT D).card + (occS D).card + sqTerm D a b c d := by
  have hT : ∑ t ∈ occT D, betaT X t + ((occT D).filter fun t => betaT X t = 0).card
      = (occT D).card + (if (b : ℕ) - a = (d : ℕ) - c then
          (if (c : ℤ) - (a : ℤ) ∈ occT D then 1 else 0) else 0) := by
    have hpt : ∀ t ∈ occT D, betaT X t + (if betaT X t = 0 then 1 else 0)
        = 1 + (if (b : ℕ) - a = (d : ℕ) - c ∧ t = (c : ℤ) - (a : ℤ) then 1 else 0) := by
      intro t _
      by_cases hsq : (b : ℕ) - a = (d : ℕ) - c ∧ t = (c : ℤ) - (a : ℤ)
      · have := hT2 hsq.1
        rw [← hsq.2] at this
        split_ifs <;> omega
      · have := hT1 t hsq
        split_ifs <;> omega
    rw [card_filter, ← sum_add_distrib, sum_congr rfl hpt, sum_add_distrib, sum_const, smul_eq_mul,
      mul_one]
    congr 1
    by_cases hsq : (b : ℕ) - a = (d : ℕ) - c
    · simp [hsq]
    · simp [hsq]
  have hS : ∑ s ∈ occS D, betaS X s + ((occS D).filter fun s => betaS X s = 0).card
      = (occS D).card + (if (b : ℕ) - a = (d : ℕ) - c then
          (if (a : ℕ) + (d : ℕ) ∈ occS D then 1 else 0) else 0) := by
    have hpt : ∀ s ∈ occS D, betaS X s + (if betaS X s = 0 then 1 else 0)
        = 1 + (if (b : ℕ) - a = (d : ℕ) - c ∧ s = (a : ℕ) + (d : ℕ) then 1 else 0) := by
      intro s _
      by_cases hsq : (b : ℕ) - a = (d : ℕ) - c ∧ s = (a : ℕ) + (d : ℕ)
      · have := hS2 hsq.1
        rw [← hsq.2] at this
        split_ifs <;> omega
      · have := hS1 s hsq
        split_ifs <;> omega
    rw [card_filter, ← sum_add_distrib, sum_congr rfl hpt, sum_add_distrib, sum_const, smul_eq_mul,
      mul_one]
    congr 1
    by_cases hsq : (b : ℕ) - a = (d : ℕ) - c
    · simp [hsq]
    · simp [hsq]
  unfold zeros sqTerm
  split_ifs at hT hS ⊢ <;> omega

section frame

variable {D : Finset (Sq n)} {a b c d : Fin n}

/-! ### Theorem V (vertical sides, `w ≥ h`) -/

/-- **Theorem V**, in natural numbers, in terms of `|R|, |T|, |S|`. -/
theorem IsFrame.side_identity_V_nat (h : IsFrame D a b c d) (hwh : (d : ℕ) - c ≤ (b : ℕ) - a) :
    zeros D (vsides a b c d) + waste2 D (vsides a b c d) + needy2 D (vsides a b c d)
        + 2 * (n - (occR D).card)
      = (occT D).card + (occS D).card + sqTerm D a b c d + uncov D (vsides a b c d) := by
  have h1 := incidences_sides D (vsides a b c d) a b c d
    (fun t ht => betaT_vsides_le_one h.hab h.hcd hwh t ht)
    (fun s hs => betaS_vsides_le_one h.hab h.hcd hwh s hs)
    (betaT_vsides_u0 h.hab h.hcd) (betaS_vsides_v0 h.hab h.hcd)
  have h2 := double_count D (vsides a b c d)
  have h3 := h.card_needy_vsides
  omega

/-- **Theorem V (side identity)** as in PROOFS.md F.1.  Assume `w ≥ h`, `X` = the vertical sides:
`#{occupied L : β_X(L) = 0} + #{(L, s) : s non-needy} + #{needy, m = 2}
   = 4k - 2n - dT - dS - 2 dR + [w = h]([u0 occupied] + [v0 occupied]) + U_X`. -/
theorem IsFrame.side_identity_V (h : IsFrame D a b c d) (hwh : (d : ℕ) - c ≤ (b : ℕ) - a) :
    ((zeros D (vsides a b c d) + waste2 D (vsides a b c d) + needy2 D (vsides a b c d) : ℕ) : ℤ)
      = 4 * (D.card : ℤ) - 2 * (n : ℤ) - defT D - defS D - 2 * (defR D : ℤ) + sqTerm D a b c d
        + uncov D (vsides a b c d) := by
  have h0 := h.side_identity_V_nat hwh
  have hR := occR_card_add_defR D
  have hT := occT_card_add_defT D
  have hS := occS_card_add_defS D
  have hRn := occR_card_le_n D
  omega

/-! ### Theorem H (horizontal sides, `h ≥ w`) -/

/-- **Theorem H**, in natural numbers, in terms of `|C|, |T|, |S|`. -/
theorem IsFrame.side_identity_H_nat (h : IsFrame D a b c d) (hhw : (b : ℕ) - a ≤ (d : ℕ) - c) :
    zeros D (hsides a b c d) + waste2 D (hsides a b c d) + needy2 D (hsides a b c d)
        + 2 * (n - (occC D).card)
      = (occT D).card + (occS D).card + sqTerm D a b c d + uncov D (hsides a b c d) := by
  have h1 := incidences_sides D (hsides a b c d) a b c d
    (fun t ht => betaT_hsides_le_one h.hab h.hcd hhw t ht)
    (fun s hs => betaS_hsides_le_one h.hab h.hcd hhw s hs)
    (betaT_hsides_u0 h.hab h.hcd) (betaS_hsides_v0 h.hab h.hcd)
  have h2 := double_count D (hsides a b c d)
  have h3 := h.card_needy_hsides
  omega

/-- **Theorem H** as in PROOFS.md F.1.  Assume `h ≥ w`, `X` = the horizontal sides: the identity of
Theorem V with `dC` in place of `dR`. -/
theorem IsFrame.side_identity_H (h : IsFrame D a b c d) (hhw : (b : ℕ) - a ≤ (d : ℕ) - c) :
    ((zeros D (hsides a b c d) + waste2 D (hsides a b c d) + needy2 D (hsides a b c d) : ℕ) : ℤ)
      = 4 * (D.card : ℤ) - 2 * (n : ℤ) - defT D - defS D - 2 * (defC D : ℤ) + sqTerm D a b c d
        + uncov D (hsides a b c d) := by
  have h0 := h.side_identity_H_nat hhw
  have hC := occC_card_add_defC D
  have hT := occT_card_add_defT D
  have hS := occS_card_add_defS D
  have hCn := occC_card_le_n D
  omega

end frame

end QueenDom

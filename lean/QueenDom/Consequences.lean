/-
Consequences of the identities for dominating sets (PROOFS.md F.1, corollaries (C1), (C2), and the
rigidity statements for `k = n/2`).
-/
module

public import QueenDom.Identities

@[expose] public section

namespace QueenDom

open Finset

variable {n : ℕ} {D : Finset (Sq n)} {a b c d : Fin n}

/-- If `D` dominates then `U_X = 0` for every `X` (by (N)). -/
theorem Dominating.uncov_eq_zero (hD : Dominating D) (X : Finset (Sq n)) : uncov D X = 0 := by
  unfold uncov
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro p - ⟨hN, hT, hS⟩
  rcases hD.needy_covered hN with h | h
  · exact hT h
  · exact hS h

/-- The term `[w = h]([u0] + [v0])` is at most `2`, and vanishes unless the box is square. -/
theorem sqTerm_le_two (D : Finset (Sq n)) (a b c d : Fin n) : sqTerm D a b c d ≤ 2 := by
  unfold sqTerm; split_ifs <;> omega

theorem sqTerm_eq_zero (D : Finset (Sq n)) {a b c d : Fin n} (h : (b : ℕ) - a ≠ (d : ℕ) - c) :
    sqTerm D a b c d = 0 := by
  unfold sqTerm; split_ifs <;> omega

/-! ### General `k` -/

/-- Theorem F for a dominating set (`U = 0`), with `k = |D|`. -/
theorem IsFrame.frame_identity_dom (h : IsFrame D a b c d) (hD : Dominating D) :
    wasteF D (border a b c d) + waste2 D (border a b c d) + needy2 D (border a b c d) + 4 * n
        + 2 * (defR D + defC D + defT D + defS D) = 8 * D.card + 4 := by
  have h0 := h.frame_identity_nat
  rw [hD.uncov_eq_zero] at h0
  have hR := occR_card_add_defR D
  have hC := occC_card_add_defC D
  have hT := occT_card_add_defT D
  have hS := occS_card_add_defS D
  have hRn := occR_card_le_n D
  have hCn := occC_card_le_n D
  omega

/-- Theorem V for a dominating set (`U = 0`), with `k = |D|`. -/
theorem IsFrame.side_identity_V_dom (h : IsFrame D a b c d) (hD : Dominating D)
    (hwh : (d : ℕ) - c ≤ (b : ℕ) - a) :
    zeros D (vsides a b c d) + waste2 D (vsides a b c d) + needy2 D (vsides a b c d) + 2 * n
        + defT D + defS D + 2 * defR D = 4 * D.card + sqTerm D a b c d := by
  have h0 := h.side_identity_V_nat hwh
  rw [hD.uncov_eq_zero] at h0
  have hR := occR_card_add_defR D
  have hT := occT_card_add_defT D
  have hS := occS_card_add_defS D
  have hRn := occR_card_le_n D
  omega

/-- Theorem H for a dominating set (`U = 0`), with `k = |D|`. -/
theorem IsFrame.side_identity_H_dom (h : IsFrame D a b c d) (hD : Dominating D)
    (hhw : (b : ℕ) - a ≤ (d : ℕ) - c) :
    zeros D (hsides a b c d) + waste2 D (hsides a b c d) + needy2 D (hsides a b c d) + 2 * n
        + defT D + defS D + 2 * defC D = 4 * D.card + sqTerm D a b c d := by
  have h0 := h.side_identity_H_nat hhw
  rw [hD.uncov_eq_zero] at h0
  have hC := occC_card_add_defC D
  have hT := occT_card_add_defT D
  have hS := occS_card_add_defS D
  have hCn := occC_card_le_n D
  omega

/-- (C1) `dR + dC + dT + dS ≤ 4k - 2n + 2`. -/
theorem IsFrame.deficit_bound (h : IsFrame D a b c d) (hD : Dominating D) :
    2 * n + (defR D + defC D + defT D + defS D) ≤ 4 * D.card + 2 := by
  have := h.frame_identity_dom hD
  omega

/-- (C2), vertical: if `w ≥ h` then `dT + dS + 2 dR ≤ 4k - 2n + 2[w = h]`. -/
theorem IsFrame.deficit_bound_V (h : IsFrame D a b c d) (hD : Dominating D)
    (hwh : (d : ℕ) - c ≤ (b : ℕ) - a) :
    2 * n + defT D + defS D + 2 * defR D
      ≤ 4 * D.card + (if (b : ℕ) - a = (d : ℕ) - c then 2 else 0) := by
  have h0 := h.side_identity_V_dom hD hwh
  have h1 := sqTerm_le_two D a b c d
  split_ifs with hsq
  · omega
  · have := sqTerm_eq_zero D hsq
    omega

/-- (C2), horizontal: if `h ≥ w` then `dT + dS + 2 dC ≤ 4k - 2n + 2[w = h]`. -/
theorem IsFrame.deficit_bound_H (h : IsFrame D a b c d) (hD : Dominating D)
    (hhw : (b : ℕ) - a ≤ (d : ℕ) - c) :
    2 * n + defT D + defS D + 2 * defC D
      ≤ 4 * D.card + (if (b : ℕ) - a = (d : ℕ) - c then 2 else 0) := by
  have h0 := h.side_identity_H_dom hD hhw
  have h1 := sqTerm_le_two D a b c d
  split_ifs with hsq
  · omega
  · have := sqTerm_eq_zero D hsq
    omega

/-! ### The case `k = n/2` -/

/-- For `k = n/2` the deficits sum to at most `2`. -/
theorem IsFrame.deficit_sum_le_two (h : IsFrame D a b c d) (hD : Dominating D)
    (hn : n = 2 * D.card) : defR D + defC D + defT D + defS D ≤ 2 := by
  have := h.deficit_bound hD
  omega

/-- For `k = n/2` and a square box: `dT + dS + 2 dR ≤ 2` and `dT + dS + 2 dC ≤ 2`. -/
theorem IsFrame.deficit_square (h : IsFrame D a b c d) (hD : Dominating D)
    (hn : n = 2 * D.card) (hsq : (b : ℕ) - a = (d : ℕ) - c) :
    defT D + defS D + 2 * defR D ≤ 2 ∧ defT D + defS D + 2 * defC D ≤ 2 := by
  have h1 := h.deficit_bound_V hD (le_of_eq hsq.symm)
  have h2 := h.deficit_bound_H hD (le_of_eq hsq)
  split_ifs at h1 h2
  omega

/-- **Rigidity of the vertical sides** (`k = n/2`, `w > h`): `dR = dT = dS = 0` and every term of
Theorem V vanishes: every occupied diagonal passes through exactly one square of the vertical sides,
every vertical-side square on an occupied diagonal is needy, and no vertical-side square lies on two
occupied diagonals. -/
theorem IsFrame.rigid_V (h : IsFrame D a b c d) (hD : Dominating D) (hn : n = 2 * D.card)
    (hwh : (d : ℕ) - c < (b : ℕ) - a) :
    defR D = 0 ∧ defT D = 0 ∧ defS D = 0 ∧
    (∀ t ∈ occT D, betaT (vsides a b c d) t = 1) ∧
    (∀ s ∈ occS D, betaS (vsides a b c d) s = 1) ∧
    (∀ p ∈ vsides a b c d, dg p ∈ occT D ∨ sm p ∈ occS D → Needy D p) ∧
    (∀ p ∈ vsides a b c d, ¬ (dg p ∈ occT D ∧ sm p ∈ occS D)) := by
  have h0 := h.side_identity_V_dom hD hwh.le
  rw [sqTerm_eq_zero D (by omega)] at h0
  have hz : zeros D (vsides a b c d) = 0 := by omega
  have hw : waste2 D (vsides a b c d) = 0 := by omega
  have hn2 : needy2 D (vsides a b c d) = 0 := by omega
  unfold zeros at hz
  unfold waste2 at hw
  unfold needy2 at hn2
  have hz1 : ((occT D).filter fun t => betaT (vsides a b c d) t = 0).card = 0 := by omega
  have hz2 : ((occS D).filter fun s => betaS (vsides a b c d) s = 0).card = 0 := by omega
  have hw1 : ((vsides a b c d).filter fun p => ¬ Needy D p ∧ dg p ∈ occT D).card = 0 := by omega
  have hw2 : ((vsides a b c d).filter fun p => ¬ Needy D p ∧ sm p ∈ occS D).card = 0 := by omega
  rw [card_eq_zero, filter_eq_empty_iff] at hz1 hz2 hw1 hw2 hn2
  have hneedy : ∀ p ∈ vsides a b c d, dg p ∈ occT D ∨ sm p ∈ occS D → Needy D p := by
    intro p hp hor
    by_contra hN
    rcases hor with h1 | h1
    · exact hw1 hp ⟨hN, h1⟩
    · exact hw2 hp ⟨hN, h1⟩
  refine ⟨by omega, by omega, by omega, ?_, ?_, hneedy, ?_⟩
  · intro t ht
    have h1 := betaT_vsides_le_one h.hab h.hcd hwh.le t (by omega)
    have h2 := hz1 ht
    omega
  · intro s hs
    have h1 := betaS_vsides_le_one h.hab h.hcd hwh.le s (by omega)
    have h2 := hz2 hs
    omega
  · intro p hp hboth
    exact hn2 hp ⟨hneedy p hp (Or.inl hboth.1), hboth⟩

/-- **Rigidity of the horizontal sides** (`k = n/2`, `h > w`): `dC = dT = dS = 0` and every term of
Theorem H vanishes. -/
theorem IsFrame.rigid_H (h : IsFrame D a b c d) (hD : Dominating D) (hn : n = 2 * D.card)
    (hhw : (b : ℕ) - a < (d : ℕ) - c) :
    defC D = 0 ∧ defT D = 0 ∧ defS D = 0 ∧
    (∀ t ∈ occT D, betaT (hsides a b c d) t = 1) ∧
    (∀ s ∈ occS D, betaS (hsides a b c d) s = 1) ∧
    (∀ p ∈ hsides a b c d, dg p ∈ occT D ∨ sm p ∈ occS D → Needy D p) ∧
    (∀ p ∈ hsides a b c d, ¬ (dg p ∈ occT D ∧ sm p ∈ occS D)) := by
  have h0 := h.side_identity_H_dom hD hhw.le
  rw [sqTerm_eq_zero D (by omega)] at h0
  have hz : zeros D (hsides a b c d) = 0 := by omega
  have hw : waste2 D (hsides a b c d) = 0 := by omega
  have hn2 : needy2 D (hsides a b c d) = 0 := by omega
  unfold zeros at hz
  unfold waste2 at hw
  unfold needy2 at hn2
  have hz1 : ((occT D).filter fun t => betaT (hsides a b c d) t = 0).card = 0 := by omega
  have hz2 : ((occS D).filter fun s => betaS (hsides a b c d) s = 0).card = 0 := by omega
  have hw1 : ((hsides a b c d).filter fun p => ¬ Needy D p ∧ dg p ∈ occT D).card = 0 := by omega
  have hw2 : ((hsides a b c d).filter fun p => ¬ Needy D p ∧ sm p ∈ occS D).card = 0 := by omega
  rw [card_eq_zero, filter_eq_empty_iff] at hz1 hz2 hw1 hw2 hn2
  have hneedy : ∀ p ∈ hsides a b c d, dg p ∈ occT D ∨ sm p ∈ occS D → Needy D p := by
    intro p hp hor
    by_contra hN
    rcases hor with h1 | h1
    · exact hw1 hp ⟨hN, h1⟩
    · exact hw2 hp ⟨hN, h1⟩
  refine ⟨by omega, by omega, by omega, ?_, ?_, hneedy, ?_⟩
  · intro t ht
    have h1 := betaT_hsides_le_one h.hab h.hcd hhw.le t (by omega)
    have h2 := hz1 ht
    omega
  · intro s hs
    have h1 := betaS_hsides_le_one h.hab h.hcd hhw.le s (by omega)
    have h2 := hz2 hs
    omega
  · intro p hp hboth
    exact hn2 hp ⟨hneedy p hp (Or.inl hboth.1), hboth⟩

/-- For `k = n/2` and `w > h` there are exactly `2k` needy squares on the vertical sides and exactly
`2k` occupied diagonals (`|T| = |S| = k`); by `rigid_V` they correspond bijectively. -/
theorem IsFrame.rigid_V_counts (h : IsFrame D a b c d) (hD : Dominating D) (hn : n = 2 * D.card)
    (hwh : (d : ℕ) - c < (b : ℕ) - a) :
    ((vsides a b c d).filter (Needy D)).card = 2 * D.card ∧ (occT D).card = D.card ∧
      (occS D).card = D.card := by
  obtain ⟨hR, hT, hS, -⟩ := h.rigid_V hD hn hwh
  have h1 := h.card_needy_vsides
  have := occR_card_add_defR D
  have := occT_card_add_defT D
  have := occS_card_add_defS D
  omega

/-- For `k = n/2` and `w > h`: every needy square of the vertical sides lies on exactly one occupied
diagonal.  Together with `rigid_V` and `rigid_V_counts` this is the bijection between the `2k`
occupied diagonals and the `2k` needy squares of the vertical sides. -/
theorem IsFrame.rigid_V_needy (h : IsFrame D a b c d) (hD : Dominating D) (hn : n = 2 * D.card)
    (hwh : (d : ℕ) - c < (b : ℕ) - a) {p : Sq n} (hp : p ∈ vsides a b c d) (hN : Needy D p) :
    (dg p ∈ occT D ∧ sm p ∉ occS D) ∨ (dg p ∉ occT D ∧ sm p ∈ occS D) := by
  obtain ⟨-, -, -, -, -, -, hboth⟩ := h.rigid_V hD hn hwh
  have h1 := hD.needy_covered hN
  have h2 := hboth p hp
  tauto

/-- The same for the horizontal sides (`k = n/2`, `h > w`). -/
theorem IsFrame.rigid_H_needy (h : IsFrame D a b c d) (hD : Dominating D) (hn : n = 2 * D.card)
    (hhw : (b : ℕ) - a < (d : ℕ) - c) {p : Sq n} (hp : p ∈ hsides a b c d) (hN : Needy D p) :
    (dg p ∈ occT D ∧ sm p ∉ occS D) ∨ (dg p ∉ occT D ∧ sm p ∈ occS D) := by
  obtain ⟨-, -, -, -, -, -, hboth⟩ := h.rigid_H hD hn hhw
  have h1 := hD.needy_covered hN
  have h2 := hboth p hp
  tauto

/-- Counts for the horizontal sides (`k = n/2`, `h > w`). -/
theorem IsFrame.rigid_H_counts (h : IsFrame D a b c d) (hD : Dominating D) (hn : n = 2 * D.card)
    (hhw : (b : ℕ) - a < (d : ℕ) - c) :
    ((hsides a b c d).filter (Needy D)).card = 2 * D.card ∧ (occT D).card = D.card ∧
      (occS D).card = D.card := by
  obtain ⟨hC, hT, hS, -⟩ := h.rigid_H hD hn hhw
  have h1 := h.card_needy_hsides
  have := occC_card_add_defC D
  have := occT_card_add_defT D
  have := occS_card_add_defS D
  omega

/-! ### Odd boards (PROOFS.md F.4) -/

theorem sqTerm_eq_two_iff (D : Finset (Sq n)) (a b c d : Fin n) :
    sqTerm D a b c d = 2 ↔
      (b : ℕ) - a = (d : ℕ) - c ∧ (c : ℤ) - (a : ℤ) ∈ occT D ∧ (a : ℕ) + (d : ℕ) ∈ occS D := by
  unfold sqTerm
  by_cases h1 : (b : ℕ) - a = (d : ℕ) - c <;> by_cases h2 : (c : ℤ) - (a : ℤ) ∈ occT D <;>
    by_cases h3 : (a : ℕ) + (d : ℕ) ∈ occS D <;> simp [h1, h2, h3]

/-- `n` odd, `k = (n+1)/2`: the deficits sum to at most `4`. -/
theorem IsFrame.deficit_sum_le_four (h : IsFrame D a b c d) (hD : Dominating D)
    (hn : n + 1 = 2 * D.card) : defR D + defC D + defT D + defS D ≤ 4 := by
  have := h.deficit_bound hD
  omega

/-- `n` odd, `k = (n+1)/2`, `w > h`: `dT + dS + 2 dR ≤ 2`. -/
theorem IsFrame.deficit_V_odd (h : IsFrame D a b c d) (hD : Dominating D)
    (hn : n + 1 = 2 * D.card) (hwh : (d : ℕ) - c < (b : ℕ) - a) :
    defT D + defS D + 2 * defR D ≤ 2 := by
  have h1 := h.deficit_bound_V hD hwh.le
  split_ifs at h1 <;> omega

/-- `n` odd, `k = (n+1)/2`, `h > w`: `dT + dS + 2 dC ≤ 2`. -/
theorem IsFrame.deficit_H_odd (h : IsFrame D a b c d) (hD : Dominating D)
    (hn : n + 1 = 2 * D.card) (hhw : (b : ℕ) - a < (d : ℕ) - c) :
    defT D + defS D + 2 * defC D ≤ 2 := by
  have h1 := h.deficit_bound_H hD hhw.le
  split_ifs at h1 <;> omega

/-- `n` odd, `k = (n-1)/2`: a dominating set of `(n-1)/2` queens has a square box, both box diagonals
`u0`, `v0` occupied, all deficits `0`, and no waste at all in the frame identity. -/
theorem IsFrame.odd_minus (h : IsFrame D a b c d) (hD : Dominating D) (hn : n = 2 * D.card + 1) :
    (b : ℕ) - a = (d : ℕ) - c ∧ (c : ℤ) - (a : ℤ) ∈ occT D ∧ (a : ℕ) + (d : ℕ) ∈ occS D ∧
    defR D = 0 ∧ defC D = 0 ∧ defT D = 0 ∧ defS D = 0 ∧
    wasteF D (border a b c d) = 0 ∧ waste2 D (border a b c d) = 0 ∧
    needy2 D (border a b c d) = 0 := by
  have hF := h.frame_identity_dom hD
  have h2 := sqTerm_le_two D a b c d
  have hsq : sqTerm D a b c d = 2 := by
    rcases le_total ((d : ℕ) - c) ((b : ℕ) - a) with hwh | hhw
    · have := h.side_identity_V_dom hD hwh
      omega
    · have := h.side_identity_H_dom hD hhw
      omega
  obtain ⟨e1, e2, e3⟩ := (sqTerm_eq_two_iff D a b c d).mp hsq
  exact ⟨e1, e2, e3, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

end QueenDom

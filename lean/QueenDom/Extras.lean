/-
PROOFS.md F.5: two further sound constraints, Lemma P and Lemma M.  The referee's encoder
`frame/enc.py` offers them as OPTIONS (`use_P`, `use_M`, both off by default); they are not used in
any reported run (in particular not for n = 32) and are not part of `CaseSat`.

* Lemma P (colour balance), for every set `D`:
    -dT ≤ #(occupied even difference diagonals) - #(occupied even sum diagonals) ≤ dS.
* Lemma M (moment identities), when all four deficits are 0:
    Σ_T t = Σ_R y - Σ_C x,   Σ_S s = Σ_R y + Σ_C x,   Σ_T t² + Σ_S s² = 2 Σ_R y² + 2 Σ_C x².
  (The encoder imposes them modulo small moduli.)
-/
module

public import QueenDom.Basic

@[expose] public section

namespace QueenDom

open Finset

variable {n : ℕ}

/-- The occupied difference diagonals with even index. -/
def evenT (D : Finset (Sq n)) : Finset ℤ := (occT D).filter fun t => t % 2 = 0
/-- The occupied sum diagonals with even index. -/
def evenS (D : Finset (Sq n)) : Finset ℕ := (occS D).filter fun s => s % 2 = 0

/-- The two diagonals through a square have indices of the same parity (the colour of the square). -/
theorem dg_even_iff_sm_even (p : Sq n) : dg p % 2 = 0 ↔ sm p % 2 = 0 := by
  unfold dg sm; omega

/-- **Lemma P (colour balance).**  `-dT ≤ |T_even| - |S_even| ≤ dS` for every set `D`. -/
theorem colour_balance (D : Finset (Sq n)) :
    -(defT D : ℤ) ≤ ((evenT D).card : ℤ) - (evenS D).card ∧
      ((evenT D).card : ℤ) - (evenS D).card ≤ defS D := by
  have hq := card_filter_add_card_filter_not (s := D) (fun p : Sq n => sm p % 2 = 0)
  have hT := card_filter_add_card_filter_not (s := occT D) (fun t : ℤ => t % 2 = 0)
  have hS := card_filter_add_card_filter_not (s := occS D) (fun s : ℕ => s % 2 = 0)
  have hT0 : (evenT D).card ≤ (D.filter fun p => sm p % 2 = 0).card := by
    refine le_trans (card_le_card ?_) (card_image_le (f := dg))
    intro t ht
    obtain ⟨ht1, ht2⟩ := mem_filter.mp ht
    obtain ⟨p, hp, rfl⟩ := mem_occT.mp ht1
    exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, (dg_even_iff_sm_even p).mp ht2⟩, rfl⟩
  have hT1 : ((occT D).filter fun t => ¬ t % 2 = 0).card
      ≤ (D.filter fun p => ¬ sm p % 2 = 0).card := by
    refine le_trans (card_le_card ?_) (card_image_le (f := dg))
    intro t ht
    obtain ⟨ht1, ht2⟩ := mem_filter.mp ht
    obtain ⟨p, hp, rfl⟩ := mem_occT.mp ht1
    exact mem_image.mpr
      ⟨p, mem_filter.mpr ⟨hp, fun h => ht2 ((dg_even_iff_sm_even p).mpr h)⟩, rfl⟩
  have hS0 : (evenS D).card ≤ (D.filter fun p => sm p % 2 = 0).card := by
    refine le_trans (card_le_card ?_) (card_image_le (f := sm))
    intro s hs
    obtain ⟨hs1, hs2⟩ := mem_filter.mp hs
    obtain ⟨p, hp, rfl⟩ := mem_occS.mp hs1
    exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, hs2⟩, rfl⟩
  have hS1 : ((occS D).filter fun s => ¬ s % 2 = 0).card
      ≤ (D.filter fun p => ¬ sm p % 2 = 0).card := by
    refine le_trans (card_le_card ?_) (card_image_le (f := sm))
    intro s hs
    obtain ⟨hs1, hs2⟩ := mem_filter.mp hs
    obtain ⟨p, hp, rfl⟩ := mem_occS.mp hs1
    exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, hs2⟩, rfl⟩
  have hdT := occT_card_add_defT D
  have hdS := occS_card_add_defS D
  unfold evenT evenS at *
  omega

/-! ### Lemma M: moment identities when all deficits vanish -/

theorem sum_occR_of_defR_eq_zero {D : Finset (Sq n)} (h : defR D = 0) (f : Fin n → ℤ) :
    ∑ y ∈ occR D, f y = ∑ p ∈ D, f p.2 :=
  sum_image ((defR_eq_zero_iff D).mp h)

theorem sum_occC_of_defC_eq_zero {D : Finset (Sq n)} (h : defC D = 0) (f : Fin n → ℤ) :
    ∑ x ∈ occC D, f x = ∑ p ∈ D, f p.1 :=
  sum_image ((defC_eq_zero_iff D).mp h)

theorem sum_occT_of_defT_eq_zero {D : Finset (Sq n)} (h : defT D = 0) (f : ℤ → ℤ) :
    ∑ t ∈ occT D, f t = ∑ p ∈ D, f (dg p) :=
  sum_image ((defT_eq_zero_iff D).mp h)

theorem sum_occS_of_defS_eq_zero {D : Finset (Sq n)} (h : defS D = 0) (f : ℕ → ℤ) :
    ∑ s ∈ occS D, f s = ∑ p ∈ D, f (sm p) :=
  sum_image ((defS_eq_zero_iff D).mp h)

/-- **Lemma M (first moments, difference diagonals).**  If `dR = dC = dT = 0` then
`Σ_{t ∈ T} t = Σ_{y ∈ R} y - Σ_{x ∈ C} x`. -/
theorem moment_T {D : Finset (Sq n)} (hR : defR D = 0) (hC : defC D = 0) (hT : defT D = 0) :
    ∑ t ∈ occT D, t = ∑ y ∈ occR D, ((y : ℕ) : ℤ) - ∑ x ∈ occC D, ((x : ℕ) : ℤ) := by
  rw [sum_occT_of_defT_eq_zero hT fun t => t, sum_occR_of_defR_eq_zero hR fun y => ((y : ℕ) : ℤ),
    sum_occC_of_defC_eq_zero hC fun x => ((x : ℕ) : ℤ), ← sum_sub_distrib]
  rfl

/-- **Lemma M (first moments, sum diagonals).**  If `dR = dC = dS = 0` then
`Σ_{s ∈ S} s = Σ_{y ∈ R} y + Σ_{x ∈ C} x`. -/
theorem moment_S {D : Finset (Sq n)} (hR : defR D = 0) (hC : defC D = 0) (hS : defS D = 0) :
    ∑ s ∈ occS D, (s : ℤ) = ∑ y ∈ occR D, ((y : ℕ) : ℤ) + ∑ x ∈ occC D, ((x : ℕ) : ℤ) := by
  rw [sum_occS_of_defS_eq_zero hS fun s => (s : ℤ), sum_occR_of_defR_eq_zero hR fun y => ((y : ℕ) : ℤ),
    sum_occC_of_defC_eq_zero hC fun x => ((x : ℕ) : ℤ), ← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  unfold sm
  push_cast
  ring

/-- **Lemma M (second moments).**  If all four deficits are `0` then
`Σ_{t ∈ T} t² + Σ_{s ∈ S} s² = 2 Σ_{y ∈ R} y² + 2 Σ_{x ∈ C} x²`. -/
theorem moment_sq {D : Finset (Sq n)} (hR : defR D = 0) (hC : defC D = 0) (hT : defT D = 0)
    (hS : defS D = 0) :
    ∑ t ∈ occT D, t ^ 2 + ∑ s ∈ occS D, (s : ℤ) ^ 2
      = 2 * ∑ y ∈ occR D, ((y : ℕ) : ℤ) ^ 2 + 2 * ∑ x ∈ occC D, ((x : ℕ) : ℤ) ^ 2 := by
  rw [sum_occT_of_defT_eq_zero hT fun t => t ^ 2, sum_occS_of_defS_eq_zero hS fun s => (s : ℤ) ^ 2,
    sum_occR_of_defR_eq_zero hR fun y => ((y : ℕ) : ℤ) ^ 2,
    sum_occC_of_defC_eq_zero hC fun x => ((x : ℕ) : ℤ) ^ 2, mul_sum, mul_sum, ← sum_add_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  unfold dg sm
  push_cast
  ring

end QueenDom

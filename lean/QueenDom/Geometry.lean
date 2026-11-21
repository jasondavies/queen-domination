/-
Geometry of the box (PROOFS.md F.0, facts (E1)-(E5)).
-/
module

public import QueenDom.Basic

@[expose] public section

namespace QueenDom

open Finset

variable {n : ℕ}

/-! ### Membership lemmas -/

theorem mem_border {a b c d : Fin n} {p : Sq n} :
    p ∈ border a b c d ↔
      (a ≤ p.1 ∧ p.1 ≤ b ∧ c ≤ p.2 ∧ p.2 ≤ d) ∧ (p.1 = a ∨ p.1 = b ∨ p.2 = c ∨ p.2 = d) := by
  simp [border]

theorem mem_vsides {a b c d : Fin n} {p : Sq n} :
    p ∈ vsides a b c d ↔ (c ≤ p.2 ∧ p.2 ≤ d) ∧ (p.1 = a ∨ p.1 = b) := by
  simp [vsides]

theorem mem_hsides {a b c d : Fin n} {p : Sq n} :
    p ∈ hsides a b c d ↔ (a ≤ p.1 ∧ p.1 ≤ b) ∧ (p.2 = c ∨ p.2 = d) := by
  simp [hsides]

theorem vsides_eq_product (a b c d : Fin n) : vsides a b c d = ({a, b} : Finset (Fin n)) ×ˢ Icc c d := by
  ext ⟨x, y⟩; simp [vsides, and_comm]

theorem hsides_eq_product (a b c d : Fin n) : hsides a b c d = Icc a b ×ˢ ({c, d} : Finset (Fin n)) := by
  ext ⟨x, y⟩; simp [hsides]

/-- The border is the union of the vertical and the horizontal sides. -/
theorem border_eq_union {a b c d : Fin n} (hab : a ≤ b) (hcd : c ≤ d) :
    border a b c d = vsides a b c d ∪ hsides a b c d := by
  ext ⟨x, y⟩
  simp only [mem_border, mem_union, mem_vsides, mem_hsides]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h | h | h | h⟩
    · exact Or.inl ⟨⟨h3, h4⟩, Or.inl h⟩
    · exact Or.inl ⟨⟨h3, h4⟩, Or.inr h⟩
    · exact Or.inr ⟨⟨h1, h2⟩, Or.inl h⟩
    · exact Or.inr ⟨⟨h1, h2⟩, Or.inr h⟩
  · rintro (⟨⟨h3, h4⟩, h | h⟩ | ⟨⟨h1, h2⟩, h | h⟩)
    · exact ⟨⟨h ▸ le_rfl, h ▸ hab, h3, h4⟩, Or.inl h⟩
    · exact ⟨⟨h ▸ hab, h ▸ le_rfl, h3, h4⟩, Or.inr (Or.inl h)⟩
    · exact ⟨⟨h1, h2, h ▸ le_rfl, h ▸ hcd⟩, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨⟨h1, h2, h ▸ hcd, h ▸ le_rfl⟩, Or.inr (Or.inr (Or.inr h))⟩

/-- The squares common to the vertical and horizontal sides are the four corners. -/
theorem vsides_inter_hsides {a b c d : Fin n} (hab : a ≤ b) (hcd : c ≤ d) :
    vsides a b c d ∩ hsides a b c d = ({a, b} : Finset (Fin n)) ×ˢ ({c, d} : Finset (Fin n)) := by
  ext ⟨x, y⟩
  simp only [mem_inter, mem_vsides, mem_hsides, mem_product, mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨-, hx⟩, -, hy⟩; exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    refine ⟨⟨?_, hx⟩, ?_, hy⟩
    · rcases hy with rfl | rfl
      · exact ⟨le_rfl, hcd⟩
      · exact ⟨hcd, le_rfl⟩
    · rcases hx with rfl | rfl
      · exact ⟨le_rfl, hab⟩
      · exact ⟨hab, le_rfl⟩

/-- The vertical sides consist of `2(h+1)` squares, `h = d - c`. -/
theorem card_vsides {a b c d : Fin n} (hab : a < b) (hcd : c ≤ d) :
    (vsides a b c d).card = 2 * ((d : ℕ) - c + 1) := by
  rw [vsides_eq_product, card_product, card_pair (ne_of_lt hab), Fin.card_Icc]
  have : (c : ℕ) ≤ d := hcd
  omega

/-- The horizontal sides consist of `2(w+1)` squares, `w = b - a`. -/
theorem card_hsides {a b c d : Fin n} (hab : a ≤ b) (hcd : c < d) :
    (hsides a b c d).card = 2 * ((b : ℕ) - a + 1) := by
  rw [hsides_eq_product, card_product, card_pair (ne_of_lt hcd), Fin.card_Icc]
  have : (a : ℕ) ≤ b := hab
  omega

/-- The border consists of `2w + 2h` squares (corners counted once). -/
theorem card_border {a b c d : Fin n} (hab : a < b) (hcd : c < d) :
    (border a b c d).card = 2 * ((b : ℕ) - a) + 2 * ((d : ℕ) - c) := by
  have h := card_union_add_card_inter (vsides a b c d) (hsides a b c d)
  rw [← border_eq_union hab.le hcd.le, vsides_inter_hsides hab.le hcd.le, card_product,
    card_pair (ne_of_lt hab), card_pair (ne_of_lt hcd), card_vsides hab hcd.le,
    card_hsides hab.le hcd] at h
  omega

/-! ### (E1), (E2): margins and the border -/

section frame

variable {D : Finset (Sq n)} {a b c d : Fin n}

/-- (E1) The `ml + mr` columns outside `[a, b]` are occupied: `ml + mr ≤ |C|`. -/
theorem IsFrame.margin_cols (h : IsFrame D a b c d) : (a : ℕ) + (n - 1 - b) ≤ (occC D).card := by
  have hsub : Iio a ∪ Ioi b ⊆ occC D := by
    intro x hx
    by_contra hx'
    have := h.hcol x hx'
    rcases mem_union.mp hx with h1 | h1
    · exact absurd (mem_Iio.mp h1) (not_lt.mpr this.1)
    · exact absurd (mem_Ioi.mp h1) (not_lt.mpr this.2)
  have hdisj : Disjoint (Iio a) (Ioi b) := by
    rw [disjoint_left]
    intro x h1 h2
    exact absurd (lt_trans (mem_Ioi.mp h2) (mem_Iio.mp h1)) (not_lt.mpr h.hab.le)
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj, Fin.card_Iio, Fin.card_Ioi] at this
  exact this

/-- (E1) The `mb + mt` rows outside `[c, d]` are occupied: `mb + mt ≤ |R|`. -/
theorem IsFrame.margin_rows (h : IsFrame D a b c d) : (c : ℕ) + (n - 1 - d) ≤ (occR D).card := by
  have hsub : Iio c ∪ Ioi d ⊆ occR D := by
    intro y hy
    by_contra hy'
    have := h.hrow y hy'
    rcases mem_union.mp hy with h1 | h1
    · exact absurd (mem_Iio.mp h1) (not_lt.mpr this.1)
    · exact absurd (mem_Ioi.mp h1) (not_lt.mpr this.2)
  have hdisj : Disjoint (Iio c) (Ioi d) := by
    rw [disjoint_left]
    intro y h1 h2
    exact absurd (lt_trans (mem_Ioi.mp h2) (mem_Iio.mp h1)) (not_lt.mpr h.hcd.le)
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj, Fin.card_Iio, Fin.card_Ioi] at this
  exact this

/-- (E1) `w + 1 ≥ n - |C|`: the box is at least as wide as the number of empty columns. -/
theorem IsFrame.width_ge (h : IsFrame D a b c d) : n ≤ ((b : ℕ) - a) + 1 + (occC D).card := by
  have := h.margin_cols
  have : (a : ℕ) < b := h.hab
  have := b.isLt
  omega

/-- (E1) `h + 1 ≥ n - |R|`: the box is at least as high as the number of empty rows. -/
theorem IsFrame.height_ge (h : IsFrame D a b c d) : n ≤ ((d : ℕ) - c) + 1 + (occR D).card := by
  have := h.margin_rows
  have : (c : ℕ) < d := h.hcd
  have := d.isLt
  omega

/-- (E2) No border square is occupied. -/
theorem IsFrame.border_not_mem (h : IsFrame D a b c d) {p : Sq n} (hp : p ∈ border a b c d) :
    p ∉ D := by
  intro hpD
  rcases (mem_border.mp hp).2 with e | e | e | e
  · exact h.ha (mem_occC.mpr ⟨p, hpD, e⟩)
  · exact h.hb (mem_occC.mpr ⟨p, hpD, e⟩)
  · exact h.hc (mem_occR.mpr ⟨p, hpD, e⟩)
  · exact h.hd (mem_occR.mpr ⟨p, hpD, e⟩)

/-! ### (E3): needy squares on the sides and on the border -/

/-- (E3) A square of a vertical side is needy iff its row is empty. -/
theorem IsFrame.needy_vsides_iff (h : IsFrame D a b c d) {p : Sq n} (hp : p ∈ vsides a b c d) :
    Needy D p ↔ p.2 ∉ occR D := by
  refine ⟨fun hN => hN.2, fun hy => ⟨?_, hy⟩⟩
  rcases (mem_vsides.mp hp).2 with e | e
  · rw [e]; exact h.ha
  · rw [e]; exact h.hb

/-- (E3) A square of a horizontal side is needy iff its column is empty. -/
theorem IsFrame.needy_hsides_iff (h : IsFrame D a b c d) {p : Sq n} (hp : p ∈ hsides a b c d) :
    Needy D p ↔ p.1 ∉ occC D := by
  refine ⟨fun hN => hN.1, fun hx => ⟨hx, ?_⟩⟩
  rcases (mem_hsides.mp hp).2 with e | e
  · rw [e]; exact h.hc
  · rw [e]; exact h.hd

theorem IsFrame.needy_vsides_eq (h : IsFrame D a b c d) :
    (vsides a b c d).filter (Needy D) = ({a, b} : Finset (Fin n)) ×ˢ (occR D)ᶜ := by
  ext ⟨x, y⟩
  simp only [mem_filter, mem_vsides, mem_product, mem_insert, mem_singleton, mem_compl, Needy]
  constructor
  · rintro ⟨⟨-, hx⟩, -, hy⟩; exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    refine ⟨⟨h.hrow y hy, hx⟩, ?_, hy⟩
    rcases hx with rfl | rfl
    · exact h.ha
    · exact h.hb

theorem IsFrame.needy_hsides_eq (h : IsFrame D a b c d) :
    (hsides a b c d).filter (Needy D) = (occC D)ᶜ ×ˢ ({c, d} : Finset (Fin n)) := by
  ext ⟨x, y⟩
  simp only [mem_filter, mem_hsides, mem_product, mem_insert, mem_singleton, mem_compl, Needy]
  constructor
  · rintro ⟨⟨-, hy⟩, hx, -⟩; exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    refine ⟨⟨h.hcol x hx, hy⟩, hx, ?_⟩
    rcases hy with rfl | rfl
    · exact h.hc
    · exact h.hd

/-- (E3) The vertical sides contain exactly `2(n - |R|)` needy squares. -/
theorem IsFrame.card_needy_vsides (h : IsFrame D a b c d) :
    ((vsides a b c d).filter (Needy D)).card = 2 * (n - (occR D).card) := by
  rw [h.needy_vsides_eq, card_product, card_pair (ne_of_lt h.hab), card_compl, Fintype.card_fin]

/-- (E3) The horizontal sides contain exactly `2(n - |C|)` needy squares. -/
theorem IsFrame.card_needy_hsides (h : IsFrame D a b c d) :
    ((hsides a b c d).filter (Needy D)).card = 2 * (n - (occC D).card) := by
  rw [h.needy_hsides_eq, card_product, card_pair (ne_of_lt h.hcd), card_compl, Fintype.card_fin,
    mul_comm]

/-- (E3) The four corners are needy. -/
theorem IsFrame.needy_corner (h : IsFrame D a b c d) {p : Sq n}
    (hx : p.1 = a ∨ p.1 = b) (hy : p.2 = c ∨ p.2 = d) : Needy D p := by
  constructor
  · rcases hx with e | e
    · rw [e]; exact h.ha
    · rw [e]; exact h.hb
  · rcases hy with e | e
    · rw [e]; exact h.hc
    · rw [e]; exact h.hd

/-- (E3) The border contains exactly `N = 2(n - |R|) + 2(n - |C|) - 4` needy squares
(stated without subtraction). -/
theorem IsFrame.card_needy_border (h : IsFrame D a b c d) :
    ((border a b c d).filter (Needy D)).card + 4
      = 2 * (n - (occR D).card) + 2 * (n - (occC D).card) := by
  have hu := card_union_add_card_inter ((vsides a b c d).filter (Needy D))
    ((hsides a b c d).filter (Needy D))
  rw [← filter_union, ← border_eq_union h.hab.le h.hcd.le, h.card_needy_vsides,
    h.card_needy_hsides] at hu
  have hi : (vsides a b c d).filter (Needy D) ∩ (hsides a b c d).filter (Needy D)
      = ({a, b} : Finset (Fin n)) ×ˢ ({c, d} : Finset (Fin n)) := by
    ext p
    simp only [mem_inter, mem_filter, mem_product, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨hv, -⟩, hh, -⟩
      exact ⟨(mem_vsides.mp hv).2, (mem_hsides.mp hh).2⟩
    · rintro ⟨hx, hy⟩
      have hm : p ∈ vsides a b c d ∩ hsides a b c d := by
        rw [vsides_inter_hsides h.hab.le h.hcd.le]
        simp only [mem_product, mem_insert, mem_singleton]
        exact ⟨hx, hy⟩
      rw [mem_inter] at hm
      exact ⟨⟨hm.1, h.needy_corner hx hy⟩, hm.2, h.needy_corner hx hy⟩
  rw [hi, card_product, card_pair (ne_of_lt h.hab), card_pair (ne_of_lt h.hcd)] at hu
  omega

end frame

/-! ### (E4): a diagonal meets the border in at most two squares -/

/-- (E4) A difference diagonal meets the border in at most two squares. -/
theorem betaT_border_le_two (a b c d : Fin n) (t : ℤ) : betaT (border a b c d) t ≤ 2 := by
  unfold betaT
  have key : ∀ p ∈ (border a b c d).filter (fun p => dg p = t),
      ((p.1 : ℕ) : ℤ) ∈ ({max (a : ℤ) (c - t), min (b : ℤ) (d - t)} : Finset ℤ) := by
    intro p hp
    simp only [mem_filter, mem_border] at hp
    simp only [dg, Fin.le_def, Fin.ext_iff] at hp
    simp only [mem_insert, mem_singleton]
    rcases le_total ((a : ℕ) : ℤ) (c - t) with h1 | h1 <;>
      rcases le_total ((b : ℕ) : ℤ) (d - t) with h2 | h2 <;>
      simp only [max_eq_right, max_eq_left, min_eq_left, min_eq_right, h1, h2] <;> omega
  refine le_trans (card_le_card_of_injOn (fun p : Sq n => ((p.1 : ℕ) : ℤ)) key ?_) card_le_two
  intro p hp q hq hpq
  rw [mem_coe, mem_filter] at hp hq
  have h1 := hp.2
  have h2 := hq.2
  simp only [dg] at h1 h2
  simp only at hpq
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> omega

/-- (E4) A sum diagonal meets the border in at most two squares. -/
theorem betaS_border_le_two (a b c d : Fin n) (s : ℕ) : betaS (border a b c d) s ≤ 2 := by
  unfold betaS
  have key : ∀ p ∈ (border a b c d).filter (fun p => sm p = s),
      ((p.1 : ℕ) : ℤ) ∈ ({max (a : ℤ) (s - d), min (b : ℤ) (s - c)} : Finset ℤ) := by
    intro p hp
    simp only [mem_filter, mem_border] at hp
    simp only [sm, Fin.le_def, Fin.ext_iff] at hp
    simp only [mem_insert, mem_singleton]
    rcases le_total ((a : ℕ) : ℤ) (s - d) with h1 | h1 <;>
      rcases le_total ((b : ℕ) : ℤ) (s - c) with h2 | h2 <;>
      simp only [max_eq_right, max_eq_left, min_eq_left, min_eq_right, h1, h2] <;> omega
  refine le_trans (card_le_card_of_injOn (fun p : Sq n => ((p.1 : ℕ) : ℤ)) key ?_) card_le_two
  intro p hp q hq hpq
  rw [mem_coe, mem_filter] at hp hq
  have h1 := hp.2
  have h2 := hq.2
  simp only [sm] at h1 h2
  simp only at hpq
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> omega

end QueenDom

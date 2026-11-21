/-
Basic facts: occupied lines, domination, the padding lemma, existence and uniqueness of the frame.
(PROOFS.md F.0: (N), the standing assumption, and the padding step in the proof of Proposition C.)
-/
module

public import QueenDom.Defs

@[expose] public section

namespace QueenDom

open Finset

variable {n : ℕ}

/-! ### Occupied lines and deficits -/

theorem mem_occR {D : Finset (Sq n)} {y : Fin n} : y ∈ occR D ↔ ∃ p ∈ D, p.2 = y := by
  simp [occR]

theorem mem_occC {D : Finset (Sq n)} {x : Fin n} : x ∈ occC D ↔ ∃ p ∈ D, p.1 = x := by
  simp [occC]

theorem mem_occT {D : Finset (Sq n)} {t : ℤ} : t ∈ occT D ↔ ∃ p ∈ D, dg p = t := by
  simp [occT]

theorem mem_occS {D : Finset (Sq n)} {s : ℕ} : s ∈ occS D ↔ ∃ p ∈ D, sm p = s := by
  simp [occS]

theorem occR_card_le (D : Finset (Sq n)) : (occR D).card ≤ D.card := card_image_le
theorem occC_card_le (D : Finset (Sq n)) : (occC D).card ≤ D.card := card_image_le
theorem occT_card_le (D : Finset (Sq n)) : (occT D).card ≤ D.card := card_image_le
theorem occS_card_le (D : Finset (Sq n)) : (occS D).card ≤ D.card := card_image_le

theorem occR_card_add_defR (D : Finset (Sq n)) : (occR D).card + defR D = D.card := by
  have := occR_card_le D; unfold defR; omega
theorem occC_card_add_defC (D : Finset (Sq n)) : (occC D).card + defC D = D.card := by
  have := occC_card_le D; unfold defC; omega
theorem occT_card_add_defT (D : Finset (Sq n)) : (occT D).card + defT D = D.card := by
  have := occT_card_le D; unfold defT; omega
theorem occS_card_add_defS (D : Finset (Sq n)) : (occS D).card + defS D = D.card := by
  have := occS_card_le D; unfold defS; omega

theorem occR_card_le_n (D : Finset (Sq n)) : (occR D).card ≤ n := by
  simpa using card_le_univ (occR D)
theorem occC_card_le_n (D : Finset (Sq n)) : (occC D).card ≤ n := by
  simpa using card_le_univ (occC D)

theorem occR_card_pos {D : Finset (Sq n)} (h : D.Nonempty) : 0 < (occR D).card :=
  card_pos.mpr (h.image _)
theorem occC_card_pos {D : Finset (Sq n)} (h : D.Nonempty) : 0 < (occC D).card :=
  card_pos.mpr (h.image _)
theorem occT_card_pos {D : Finset (Sq n)} (h : D.Nonempty) : 0 < (occT D).card :=
  card_pos.mpr (h.image _)
theorem occS_card_pos {D : Finset (Sq n)} (h : D.Nonempty) : 0 < (occS D).card :=
  card_pos.mpr (h.image _)

/-- A deficit is `0` iff no two queens share a line of that type (the AMO constraint of the CNF). -/
theorem defR_eq_zero_iff (D : Finset (Sq n)) : defR D = 0 ↔ Set.InjOn Prod.snd (D : Set (Sq n)) := by
  rw [← card_image_iff]; have := occR_card_le D; unfold defR occR at *; omega
theorem defC_eq_zero_iff (D : Finset (Sq n)) : defC D = 0 ↔ Set.InjOn Prod.fst (D : Set (Sq n)) := by
  rw [← card_image_iff]; have := occC_card_le D; unfold defC occC at *; omega
theorem defT_eq_zero_iff (D : Finset (Sq n)) : defT D = 0 ↔ Set.InjOn dg (D : Set (Sq n)) := by
  rw [← card_image_iff]; have := occT_card_le D; unfold defT occT at *; omega
theorem defS_eq_zero_iff (D : Finset (Sq n)) : defS D = 0 ↔ Set.InjOn sm (D : Set (Sq n)) := by
  rw [← card_image_iff]; have := occS_card_le D; unfold defS occS at *; omega

/-! ### Domination -/

/-- Domination in terms of occupied lines (this is the clause DOM of the CNF). -/
theorem dominating_iff (D : Finset (Sq n)) :
    Dominating D ↔ ∀ p : Sq n, p.2 ∈ occR D ∨ p.1 ∈ occC D ∨ dg p ∈ occT D ∨ sm p ∈ occS D := by
  constructor
  · intro h p
    rcases h p with hp | ⟨q, hq, -, hl⟩
    · exact Or.inl (mem_occR.mpr ⟨p, hp, rfl⟩)
    · rcases hl with h1 | h2 | h3 | h4
      · exact Or.inr (Or.inl (mem_occC.mpr ⟨q, hq, h1⟩))
      · exact Or.inl (mem_occR.mpr ⟨q, hq, h2⟩)
      · exact Or.inr (Or.inr (Or.inl (mem_occT.mpr ⟨q, hq, h3⟩)))
      · exact Or.inr (Or.inr (Or.inr (mem_occS.mpr ⟨q, hq, h4⟩)))
  · intro h p
    by_cases hp : p ∈ D
    · exact Or.inl hp
    · right
      have key : ∀ q ∈ D, SameLine q p → ∃ q ∈ D, Attacks q p := fun q hq hl =>
        ⟨q, hq, fun e => hp (e ▸ hq), hl⟩
      rcases h p with h | h | h | h
      · obtain ⟨q, hq, e⟩ := mem_occR.mp h
        exact key q hq (Or.inr (Or.inl e))
      · obtain ⟨q, hq, e⟩ := mem_occC.mp h
        exact key q hq (Or.inl e)
      · obtain ⟨q, hq, e⟩ := mem_occT.mp h
        exact key q hq (Or.inr (Or.inr (Or.inl e)))
      · obtain ⟨q, hq, e⟩ := mem_occS.mp h
        exact key q hq (Or.inr (Or.inr (Or.inr e)))

/-- `Dominating` is domination in the queen's graph: every square outside `D` is adjacent to a
square of `D`. -/
theorem dominating_iff_adj (D : Finset (Sq n)) :
    Dominating D ↔ ∀ p : Sq n, p ∉ D → ∃ q ∈ D, (queenGraph n).Adj q p := by
  constructor
  · intro h p hp
    rcases h p with h1 | h1
    · exact absurd h1 hp
    · exact h1
  · intro h p
    by_cases hp : p ∈ D
    · exact Or.inl hp
    · exact Or.inr (h p hp)

/-- (N): if `D` dominates, every needy square lies on an occupied diagonal. -/
theorem Dominating.needy_covered {D : Finset (Sq n)} (hD : Dominating D) {p : Sq n}
    (hp : Needy D p) : dg p ∈ occT D ∨ sm p ∈ occS D := by
  rcases (dominating_iff D).mp hD p with h | h | h | h
  · exact absurd h hp.2
  · exact absurd h hp.1
  · exact Or.inl h
  · exact Or.inr h

/-- A needy square is not occupied. -/
theorem Needy.not_mem {D : Finset (Sq n)} {p : Sq n} (hp : Needy D p) : p ∉ D :=
  fun h => hp.1 (mem_occC.mpr ⟨p, h, rfl⟩)

/-- Supersets of dominating sets are dominating. -/
theorem Dominating.mono {D D' : Finset (Sq n)} (hD : Dominating D) (h : D ⊆ D') : Dominating D' := by
  intro p
  rcases hD p with hp | ⟨q, hq, ha⟩
  · exact Or.inl (h hp)
  · exact Or.inr ⟨q, h hq, ha⟩

/-- **Padding lemma.**  If there is a dominating set of size `≤ k ≤ n²`, there is one of size exactly
`k`. -/
theorem exists_dominating_card_eq {D : Finset (Sq n)} (hD : Dominating D) {k : ℕ}
    (h1 : D.card ≤ k) (h2 : k ≤ n * n) : ∃ D' : Finset (Sq n), Dominating D' ∧ D'.card = k := by
  have hu : k ≤ (univ : Finset (Sq n)).card := by simpa using h2
  obtain ⟨D', hsub, -, hcard⟩ := exists_subsuperset_card_eq (subset_univ D) h1 hu
  exact ⟨D', hD.mono hsub, hcard⟩

/-- A dominating set of a nonempty board is nonempty. -/
theorem Dominating.nonempty {D : Finset (Sq n)} (hD : Dominating D) (hn : 0 < n) : D.Nonempty := by
  rcases hD (⟨0, hn⟩, ⟨0, hn⟩) with h | ⟨q, hq, -⟩
  · exact ⟨_, h⟩
  · exact ⟨_, hq⟩

/-! ### The frame: extreme empty columns and rows -/

/-- The frame is unique. -/
theorem IsFrame.unique {D : Finset (Sq n)} {a b c d a' b' c' d' : Fin n}
    (h : IsFrame D a b c d) (h' : IsFrame D a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' :=
  ⟨le_antisymm (h.hcol a' h'.ha).1 (h'.hcol a h.ha).1, le_antisymm (h'.hcol b h.hb).2 (h.hcol b' h'.hb).2,
   le_antisymm (h.hrow c' h'.hc).1 (h'.hrow c h.hc).1, le_antisymm (h'.hrow d h.hd).2 (h.hrow d' h'.hd).2⟩

/-- If at least two columns and at least two rows are empty, the frame exists. -/
theorem exists_isFrame (D : Finset (Sq n)) (hC : (occC D).card + 2 ≤ n) (hR : (occR D).card + 2 ≤ n) :
    ∃ a b c d : Fin n, IsFrame D a b c d := by
  have hEC : 1 < ((occC D)ᶜ).card := by rw [card_compl, Fintype.card_fin]; omega
  have hER : 1 < ((occR D)ᶜ).card := by rw [card_compl, Fintype.card_fin]; omega
  have neC : ((occC D)ᶜ).Nonempty := card_pos.mp (by omega)
  have neR : ((occR D)ᶜ).Nonempty := card_pos.mp (by omega)
  refine ⟨(occC D)ᶜ.min' neC, (occC D)ᶜ.max' neC, (occR D)ᶜ.min' neR, (occR D)ᶜ.max' neR, ?_⟩
  refine ⟨min'_lt_max'_of_card _ hEC, min'_lt_max'_of_card _ hER, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_compl.mp (min'_mem _ neC)
  · exact mem_compl.mp (max'_mem _ neC)
  · exact mem_compl.mp (min'_mem _ neR)
  · exact mem_compl.mp (max'_mem _ neR)
  · exact fun x hx => ⟨min'_le _ x (mem_compl.mpr hx), le_max' _ x (mem_compl.mpr hx)⟩
  · exact fun y hy => ⟨min'_le _ y (mem_compl.mpr hy), le_max' _ y (mem_compl.mpr hy)⟩

/-- The standing assumption is automatic for `k ≤ n - 2`. -/
theorem exists_isFrame_of_card (D : Finset (Sq n)) (h : D.card + 2 ≤ n) :
    ∃ a b c d : Fin n, IsFrame D a b c d :=
  exists_isFrame D (by have := occC_card_le D; omega) (by have := occR_card_le D; omega)

end QueenDom

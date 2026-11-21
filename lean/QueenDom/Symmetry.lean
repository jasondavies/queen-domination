/-
The eight symmetries of the board and their action on dominating sets and frames
(PROOFS.md F.2: `geom.sym_maps`, `geom.case_images` restricted to the frame part).
-/
module

public import QueenDom.Basic

@[expose] public section

namespace QueenDom

open Finset

variable {n : ℕ}

/-! ### The generators -/

/-- Reflection of the columns: `(x, y) ↦ (n-1-x, y)`. -/
def reflX : Sq n ≃ Sq n := Equiv.prodCongr Fin.revPerm (Equiv.refl _)
/-- Reflection of the rows: `(x, y) ↦ (x, n-1-y)`. -/
def reflY : Sq n ≃ Sq n := Equiv.prodCongr (Equiv.refl _) Fin.revPerm
/-- Transposition: `(x, y) ↦ (y, x)`. -/
def transp : Sq n ≃ Sq n := Equiv.prodComm _ _

@[simp] theorem reflX_apply (p : Sq n) : reflX p = (Fin.rev p.1, p.2) := rfl
@[simp] theorem reflY_apply (p : Sq n) : reflY p = (p.1, Fin.rev p.2) := rfl
@[simp] theorem transp_apply (p : Sq n) : transp p = (p.2, p.1) := rfl

theorem sameLine_reflX {p q : Sq n} (h : SameLine p q) : SameLine (reflX p) (reflX q) := by
  have := p.1.isLt
  have := q.1.isLt
  unfold SameLine at *
  simp only [reflX_apply, dg, sm, Fin.val_rev, Fin.rev_inj] at *
  omega

theorem sameLine_reflY {p q : Sq n} (h : SameLine p q) : SameLine (reflY p) (reflY q) := by
  have := p.2.isLt
  have := q.2.isLt
  unfold SameLine at *
  simp only [reflY_apply, dg, sm, Fin.val_rev, Fin.rev_inj] at *
  omega

theorem sameLine_transp {p q : Sq n} (h : SameLine p q) : SameLine (transp p) (transp q) := by
  unfold SameLine at *
  simp only [transp_apply, dg, sm] at *
  omega

section map

variable {D : Finset (Sq n)}

/-- The image of a dominating set under a bijection of the board that preserves lines is
dominating. -/
theorem Dominating.map (hD : Dominating D) (σ : Sq n ≃ Sq n)
    (hσ : ∀ p q, SameLine p q → SameLine (σ p) (σ q)) : Dominating (D.map σ.toEmbedding) := by
  intro p
  rcases hD (σ.symm p) with h | ⟨q, hq, hne, hl⟩
  · left
    rw [mem_map_equiv]; exact h
  · right
    refine ⟨σ q, mem_map_of_mem _ hq, ?_, ?_⟩
    · intro e
      apply hne
      rw [← e]; simp
    · have := hσ q (σ.symm p) hl
      simpa using this

theorem mem_occC_map (σ : Sq n ≃ Sq n) {x : Fin n} :
    x ∈ occC (D.map σ.toEmbedding) ↔ ∃ p ∈ D, (σ p).1 = x := by
  unfold occC
  simp only [mem_image, mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨σ p, ⟨p, hp, rfl⟩, rfl⟩

theorem mem_occR_map (σ : Sq n ≃ Sq n) {y : Fin n} :
    y ∈ occR (D.map σ.toEmbedding) ↔ ∃ p ∈ D, (σ p).2 = y := by
  unfold occR
  simp only [mem_image, mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨σ p, ⟨p, hp, rfl⟩, rfl⟩

theorem mem_occC_map_reflX {x : Fin n} : x ∈ occC (D.map reflX.toEmbedding) ↔ Fin.rev x ∈ occC D := by
  rw [mem_occC_map, mem_occC]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, by simp⟩
  · rintro ⟨p, hp, e⟩; exact ⟨p, hp, by simp [e]⟩

theorem mem_occR_map_reflX {y : Fin n} : y ∈ occR (D.map reflX.toEmbedding) ↔ y ∈ occR D := by
  rw [mem_occR_map, mem_occR]; rfl

theorem mem_occC_map_reflY {x : Fin n} : x ∈ occC (D.map reflY.toEmbedding) ↔ x ∈ occC D := by
  rw [mem_occC_map, mem_occC]; rfl

theorem mem_occR_map_reflY {y : Fin n} : y ∈ occR (D.map reflY.toEmbedding) ↔ Fin.rev y ∈ occR D := by
  rw [mem_occR_map, mem_occR]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, by simp⟩
  · rintro ⟨p, hp, e⟩; exact ⟨p, hp, by simp [e]⟩

theorem mem_occC_map_transp {x : Fin n} : x ∈ occC (D.map transp.toEmbedding) ↔ x ∈ occR D := by
  rw [mem_occC_map, mem_occR]; rfl

theorem mem_occR_map_transp {y : Fin n} : y ∈ occR (D.map transp.toEmbedding) ↔ y ∈ occC D := by
  rw [mem_occR_map, mem_occC]; rfl

/-! ### Action on frames -/

variable {a b c d : Fin n}

/-- `x ↦ n-1-x` maps the frame `(a, b, c, d)` to `(n-1-b, n-1-a, c, d)`. -/
theorem IsFrame.map_reflX (h : IsFrame D a b c d) :
    IsFrame (D.map reflX.toEmbedding) (Fin.rev b) (Fin.rev a) c d where
  hab := Fin.rev_lt_rev.mpr h.hab
  hcd := h.hcd
  ha := by rw [mem_occC_map_reflX, Fin.rev_rev]; exact h.hb
  hb := by rw [mem_occC_map_reflX, Fin.rev_rev]; exact h.ha
  hc := by rw [mem_occR_map_reflX]; exact h.hc
  hd := by rw [mem_occR_map_reflX]; exact h.hd
  hcol := by
    intro x hx
    rw [mem_occC_map_reflX] at hx
    have := h.hcol _ hx
    have := x.isLt
    simp only [Fin.le_def, Fin.val_rev] at *
    omega
  hrow := by
    intro y hy
    rw [mem_occR_map_reflX] at hy
    exact h.hrow y hy

/-- `y ↦ n-1-y` maps the frame `(a, b, c, d)` to `(a, b, n-1-d, n-1-c)`. -/
theorem IsFrame.map_reflY (h : IsFrame D a b c d) :
    IsFrame (D.map reflY.toEmbedding) a b (Fin.rev d) (Fin.rev c) where
  hab := h.hab
  hcd := Fin.rev_lt_rev.mpr h.hcd
  ha := by rw [mem_occC_map_reflY]; exact h.ha
  hb := by rw [mem_occC_map_reflY]; exact h.hb
  hc := by rw [mem_occR_map_reflY, Fin.rev_rev]; exact h.hd
  hd := by rw [mem_occR_map_reflY, Fin.rev_rev]; exact h.hc
  hcol := by
    intro x hx
    rw [mem_occC_map_reflY] at hx
    exact h.hcol x hx
  hrow := by
    intro y hy
    rw [mem_occR_map_reflY] at hy
    have := h.hrow _ hy
    have := y.isLt
    simp only [Fin.le_def, Fin.val_rev] at *
    omega

/-- The transposition maps the frame `(a, b, c, d)` to `(c, d, a, b)`. -/
theorem IsFrame.map_transp (h : IsFrame D a b c d) : IsFrame (D.map transp.toEmbedding) c d a b where
  hab := h.hcd
  hcd := h.hab
  ha := by rw [mem_occC_map_transp]; exact h.hc
  hb := by rw [mem_occC_map_transp]; exact h.hd
  hc := by rw [mem_occR_map_transp]; exact h.ha
  hd := by rw [mem_occR_map_transp]; exact h.hb
  hcol := by
    intro x hx
    rw [mem_occC_map_transp] at hx
    exact h.hrow x hx
  hrow := by
    intro y hy
    rw [mem_occR_map_transp] at hy
    exact h.hcol y hy

end map

/-! ### Margins -/

/-- The margins `(ml, mr, mb, mt) = (a, n-1-b, c, n-1-d)` of a frame. -/
def margins (a b c d : Fin n) : ℕ × ℕ × ℕ × ℕ := ((a : ℕ), n - 1 - (b : ℕ), (c : ℕ), n - 1 - (d : ℕ))

/-- `D` has a frame with margins `f = (ml, mr, mb, mt)`. -/
def HasMargins (D : Finset (Sq n)) (f : ℕ × ℕ × ℕ × ℕ) : Prop :=
  ∃ a b c d : Fin n, IsFrame D a b c d ∧ margins a b c d = f

/-- Action of `x ↦ n-1-x` on margins: `ml ↔ mr`. -/
def swapX (f : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ := (f.2.1, f.1, f.2.2.1, f.2.2.2)
/-- Action of `y ↦ n-1-y` on margins: `mb ↔ mt`. -/
def swapY (f : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ := (f.1, f.2.1, f.2.2.2, f.2.2.1)
/-- Action of the transposition on margins: `(ml, mr) ↔ (mb, mt)`. -/
def swapT (f : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ := (f.2.2.1, f.2.2.2, f.1, f.2.1)

theorem HasMargins.map_reflX {D : Finset (Sq n)} {f : ℕ × ℕ × ℕ × ℕ} (h : HasMargins D f) :
    HasMargins (D.map reflX.toEmbedding) (swapX f) := by
  obtain ⟨a, b, c, d, hF, rfl⟩ := h
  refine ⟨Fin.rev b, Fin.rev a, c, d, hF.map_reflX, ?_⟩
  have := a.isLt
  have := b.isLt
  simp only [margins, swapX, Fin.val_rev, Prod.mk.injEq, and_true]
  omega

theorem HasMargins.map_reflY {D : Finset (Sq n)} {f : ℕ × ℕ × ℕ × ℕ} (h : HasMargins D f) :
    HasMargins (D.map reflY.toEmbedding) (swapY f) := by
  obtain ⟨a, b, c, d, hF, rfl⟩ := h
  refine ⟨a, b, Fin.rev d, Fin.rev c, hF.map_reflY, ?_⟩
  have := c.isLt
  have := d.isLt
  simp only [margins, swapY, Fin.val_rev, Prod.mk.injEq, true_and]
  omega

theorem HasMargins.map_transp {D : Finset (Sq n)} {f : ℕ × ℕ × ℕ × ℕ} (h : HasMargins D f) :
    HasMargins (D.map transp.toEmbedding) (swapT f) := by
  obtain ⟨a, b, c, d, hF, rfl⟩ := h
  exact ⟨c, d, a, b, hF.map_transp, rfl⟩

/-! ### The group of eight symmetries -/

/-- A symmetry of the board, coded by three bits: reflect the columns (`fx`), then reflect the rows
(`fy`), then transpose (`tr`).  These are the eight symmetries of the square. -/
structure Sym where
  fx : Bool
  fy : Bool
  tr : Bool
deriving DecidableEq, Repr

/-- The symmetry as a bijection of the board. -/
def Sym.toEquiv (g : Sym) : Sq n ≃ Sq n :=
  ((bif g.fx then reflX else Equiv.refl _).trans (bif g.fy then reflY else Equiv.refl _)).trans
    (bif g.tr then transp else Equiv.refl _)

/-- Explicit formula for the eight maps. -/
theorem Sym.toEquiv_apply (g : Sym) (p : Sq n) :
    g.toEquiv p =
      (bif g.tr then ((bif g.fy then Fin.rev p.2 else p.2), (bif g.fx then Fin.rev p.1 else p.1))
       else ((bif g.fx then Fin.rev p.1 else p.1), (bif g.fy then Fin.rev p.2 else p.2))) := by
  rcases g with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

/-- The image of a set of squares under a symmetry. -/
def Sym.image (g : Sym) (D : Finset (Sq n)) : Finset (Sq n) :=
  let D1 := bif g.fx then D.map reflX.toEmbedding else D
  let D2 := bif g.fy then D1.map reflY.toEmbedding else D1
  bif g.tr then D2.map transp.toEmbedding else D2

theorem map_map_equiv (D : Finset (Sq n)) (e₁ e₂ : Sq n ≃ Sq n) :
    (D.map e₁.toEmbedding).map e₂.toEmbedding = D.map (e₁.trans e₂).toEmbedding := by
  rw [Finset.map_map]; rfl

theorem cond_map_equiv (D : Finset (Sq n)) (b : Bool) (e : Sq n ≃ Sq n) :
    (bif b then D.map e.toEmbedding else D) = D.map (bif b then e else Equiv.refl _).toEmbedding := by
  cases b
  · ext p; simp
  · rfl

theorem Sym.image_eq_map (g : Sym) (D : Finset (Sq n)) :
    g.image D = D.map (g.toEquiv (n := n)).toEmbedding := by
  rcases g with ⟨_ | _, _ | _, _ | _⟩ <;>
    simp only [Sym.image, Sym.toEquiv, Bool.cond_true, Bool.cond_false, map_map_equiv, Equiv.refl_trans,
      Equiv.trans_refl]
  ext p; simp

theorem Sym.card_image (g : Sym) (D : Finset (Sq n)) : (g.image D).card = D.card := by
  rw [g.image_eq_map, card_map]

/-- The symmetries preserve domination. -/
theorem Dominating.sym {D : Finset (Sq n)} (hD : Dominating D) (g : Sym) : Dominating (g.image D) := by
  rcases g with ⟨fx, fy, tr⟩
  have h1 : Dominating (bif fx then D.map reflX.toEmbedding else D) := by
    cases fx
    · exact hD
    · exact hD.map reflX fun _ _ => sameLine_reflX
  have h2 : Dominating (bif fy then (bif fx then D.map reflX.toEmbedding else D).map reflY.toEmbedding
      else (bif fx then D.map reflX.toEmbedding else D)) := by
    cases fy
    · exact h1
    · exact h1.map reflY fun _ _ => sameLine_reflY
  cases tr
  · exact h2
  · exact h2.map transp fun _ _ => sameLine_transp

/-- Action of a symmetry on margins `(ml, mr, mb, mt)` (the frame part of `geom.case_images`). -/
def Sym.actFrame (g : Sym) (f : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let f1 := bif g.fx then swapX f else f
  let f2 := bif g.fy then swapY f1 else f1
  bif g.tr then swapT f2 else f2

/-- The frame of the image is the image of the frame. -/
theorem HasMargins.sym {D : Finset (Sq n)} {f : ℕ × ℕ × ℕ × ℕ} (h : HasMargins D f) (g : Sym) :
    HasMargins (g.image D) (g.actFrame f) := by
  rcases g with ⟨fx, fy, tr⟩
  have h1 : HasMargins (bif fx then D.map reflX.toEmbedding else D) (bif fx then swapX f else f) := by
    cases fx
    · exact h
    · exact h.map_reflX
  have h2 : HasMargins
      (bif fy then (bif fx then D.map reflX.toEmbedding else D).map reflY.toEmbedding
        else (bif fx then D.map reflX.toEmbedding else D))
      (bif fy then swapY (bif fx then swapX f else f) else (bif fx then swapX f else f)) := by
    cases fy
    · exact h1
    · exact h1.map_reflY
  cases tr
  · exact h2
  · exact h2.map_transp

/-! ### Canonical frames -/

/-- Lexicographic order on 4-tuples of natural numbers. -/
def LexLe (a1 a2 a3 a4 b1 b2 b3 b4 : ℕ) : Prop :=
  a1 < b1 ∨ a1 = b1 ∧ (a2 < b2 ∨ a2 = b2 ∧ (a3 < b3 ∨ a3 = b3 ∧ a4 ≤ b4))

instance (a1 a2 a3 a4 b1 b2 b3 b4 : ℕ) : Decidable (LexLe a1 a2 a3 a4 b1 b2 b3 b4) := by
  unfold LexLe; infer_instance

/-- A frame `(ml, mr, mb, mt) = (p, q, r, s)` is *canonical* if it is lexicographically least among
its eight images (`geom.canonical`); the seven non-trivial images are listed. -/
def Canon (p q r s : ℕ) : Prop :=
  LexLe p q r s q p r s ∧ LexLe p q r s p q s r ∧ LexLe p q r s q p s r ∧
  LexLe p q r s r s p q ∧ LexLe p q r s s r p q ∧ LexLe p q r s r s q p ∧ LexLe p q r s s r q p

instance (p q r s : ℕ) : Decidable (Canon p q r s) := by unfold Canon; infer_instance

/-- `Canon` really is "least among all eight images". -/
theorem canon_iff_forall (p q r s : ℕ) :
    Canon p q r s ↔ ∀ g : Sym, LexLe p q r s (g.actFrame (p, q, r, s)).1 (g.actFrame (p, q, r, s)).2.1
      (g.actFrame (p, q, r, s)).2.2.1 (g.actFrame (p, q, r, s)).2.2.2 := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩ ⟨_ | _, _ | _, _ | _⟩
    · show LexLe p q r s p q r s
      unfold LexLe; omega
    · exact h4
    · exact h2
    · exact h5
    · exact h1
    · exact h6
    · exact h3
    · exact h7
  · intro h
    exact ⟨h ⟨true, false, false⟩, h ⟨false, true, false⟩, h ⟨true, true, false⟩,
      h ⟨false, false, true⟩, h ⟨false, true, true⟩, h ⟨true, false, true⟩, h ⟨true, true, true⟩⟩

/-- Closed form of canonicity. -/
theorem canon_iff (p q r s : ℕ) : Canon p q r s ↔ p ≤ q ∧ r ≤ s ∧ (p < r ∨ p = r ∧ q ≤ s) := by
  unfold Canon LexLe; omega

/-- Every frame has a canonical image. -/
theorem exists_canon (f : ℕ × ℕ × ℕ × ℕ) :
    ∃ g : Sym, Canon (g.actFrame f).1 (g.actFrame f).2.1 (g.actFrame f).2.2.1 (g.actFrame f).2.2.2 := by
  obtain ⟨p, q, r, s⟩ := f
  rcases Nat.lt_or_ge q p with h1 | h1 <;> rcases Nat.lt_or_ge s r with h2 | h2
  · by_cases h3 : q < s ∨ q = s ∧ p ≤ r
    · exact ⟨⟨true, true, false⟩, by show Canon q p s r; rw [canon_iff]; omega⟩
    · exact ⟨⟨true, true, true⟩, by show Canon s r q p; rw [canon_iff]; omega⟩
  · by_cases h3 : q < r ∨ q = r ∧ p ≤ s
    · exact ⟨⟨true, false, false⟩, by show Canon q p r s; rw [canon_iff]; omega⟩
    · exact ⟨⟨true, false, true⟩, by show Canon r s q p; rw [canon_iff]; omega⟩
  · by_cases h3 : p < s ∨ p = s ∧ q ≤ r
    · exact ⟨⟨false, true, false⟩, by show Canon p q s r; rw [canon_iff]; omega⟩
    · exact ⟨⟨false, true, true⟩, by show Canon s r p q; rw [canon_iff]; omega⟩
  · by_cases h3 : p < r ∨ p = r ∧ q ≤ s
    · exact ⟨⟨false, false, false⟩, by show Canon p q r s; rw [canon_iff]; omega⟩
    · exact ⟨⟨false, false, true⟩, by show Canon r s p q; rw [canon_iff]; omega⟩

end QueenDom

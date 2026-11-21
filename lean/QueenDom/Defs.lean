/-
Queen domination: basic definitions (PROOFS.md, section F.0).

Board squares are pairs `(x, y) : Fin n × Fin n`, `x` = column, `y` = row, as in the hand proofs and in
the referee's code (`frame/geom.py`).
-/
module

public import Mathlib

@[expose] public section

namespace QueenDom

open Finset

variable {n : ℕ}

/-- A square of the `n × n` board: `(x, y) = (column, row)`. -/
abbrev Sq (n : ℕ) := Fin n × Fin n

/-- Index of the difference diagonal through a square: `t = y - x`. -/
def dg (p : Sq n) : ℤ := (p.2 : ℤ) - (p.1 : ℤ)

/-- Index of the sum diagonal through a square: `s = x + y`. -/
def sm (p : Sq n) : ℕ := (p.1 : ℕ) + (p.2 : ℕ)

/-- Two squares lie on a common line (column, row, difference diagonal or sum diagonal). -/
def SameLine (p q : Sq n) : Prop := p.1 = q.1 ∨ p.2 = q.2 ∨ dg p = dg q ∨ sm p = sm q

/-- A queen on `p` attacks the square `q`: they are distinct and lie on a common line.
This is the adjacency relation of the queen's graph `Q_n`. -/
def Attacks (p q : Sq n) : Prop := p ≠ q ∧ SameLine p q

instance : DecidableRel (SameLine (n := n)) := fun p q => by unfold SameLine; infer_instance
instance : DecidableRel (Attacks (n := n)) := fun p q => by unfold Attacks; infer_instance

/-- The queen's graph `Q_n` as a `SimpleGraph`. -/
def queenGraph (n : ℕ) : SimpleGraph (Sq n) where
  Adj := Attacks
  symm := ⟨by
    rintro p q ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    unfold SameLine at *
    rcases h with h | h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inr (Or.inr h.symm))⟩
  loopless := ⟨fun p h => h.1 rfl⟩

/-- `D` is a dominating set of `Q_n`: every square is in `D` or attacked by a square of `D`. -/
def Dominating (D : Finset (Sq n)) : Prop := ∀ p : Sq n, p ∈ D ∨ ∃ q ∈ D, Attacks q p

instance (D : Finset (Sq n)) : Decidable (Dominating D) := by unfold Dominating; infer_instance

/-- The set of occupied rows. -/
def occR (D : Finset (Sq n)) : Finset (Fin n) := D.image Prod.snd
/-- The set of occupied columns. -/
def occC (D : Finset (Sq n)) : Finset (Fin n) := D.image Prod.fst
/-- The set of occupied difference diagonals. -/
def occT (D : Finset (Sq n)) : Finset ℤ := D.image dg
/-- The set of occupied sum diagonals. -/
def occS (D : Finset (Sq n)) : Finset ℕ := D.image sm

/-- Row deficit `dR = |D| - |R|` (natural subtraction; `|R| ≤ |D|` is `occR_card_le`). -/
def defR (D : Finset (Sq n)) : ℕ := D.card - (occR D).card
/-- Column deficit `dC = |D| - |C|`. -/
def defC (D : Finset (Sq n)) : ℕ := D.card - (occC D).card
/-- Difference-diagonal deficit `dT = |D| - |T|`. -/
def defT (D : Finset (Sq n)) : ℕ := D.card - (occT D).card
/-- Sum-diagonal deficit `dS = |D| - |S|`. -/
def defS (D : Finset (Sq n)) : ℕ := D.card - (occS D).card

/-- A square is *needy* if its column and its row are both empty. -/
def Needy (D : Finset (Sq n)) (p : Sq n) : Prop := p.1 ∉ occC D ∧ p.2 ∉ occR D

instance (D : Finset (Sq n)) : DecidablePred (Needy D) := fun p => by unfold Needy; infer_instance

/-- `a < b` are the least and greatest empty columns and `c < d` the least and greatest empty rows of
`D`.  (The *standing assumption* of F.0: at least two empty rows and columns.) -/
structure IsFrame (D : Finset (Sq n)) (a b c d : Fin n) : Prop where
  hab : a < b
  hcd : c < d
  ha : a ∉ occC D
  hb : b ∉ occC D
  hc : c ∉ occR D
  hd : d ∉ occR D
  /-- every empty column lies in `[a, b]` -/
  hcol : ∀ x, x ∉ occC D → a ≤ x ∧ x ≤ b
  /-- every empty row lies in `[c, d]` -/
  hrow : ∀ y, y ∉ occR D → c ≤ y ∧ y ≤ d

/-- The box `[a, b] × [c, d]`. -/
def box (a b c d : Fin n) : Finset (Sq n) :=
  univ.filter fun p => a ≤ p.1 ∧ p.1 ≤ b ∧ c ≤ p.2 ∧ p.2 ≤ d

/-- The border of the box: the box squares with `x ∈ {a, b}` or `y ∈ {c, d}` (each square once). -/
def border (a b c d : Fin n) : Finset (Sq n) :=
  univ.filter fun p => (a ≤ p.1 ∧ p.1 ≤ b ∧ c ≤ p.2 ∧ p.2 ≤ d) ∧ (p.1 = a ∨ p.1 = b ∨ p.2 = c ∨ p.2 = d)

/-- The vertical sides: the box squares with `x ∈ {a, b}`. -/
def vsides (a b c d : Fin n) : Finset (Sq n) :=
  univ.filter fun p => (c ≤ p.2 ∧ p.2 ≤ d) ∧ (p.1 = a ∨ p.1 = b)

/-- The horizontal sides: the box squares with `y ∈ {c, d}`. -/
def hsides (a b c d : Fin n) : Finset (Sq n) :=
  univ.filter fun p => (a ≤ p.1 ∧ p.1 ≤ b) ∧ (p.2 = c ∨ p.2 = d)

/-- `β_X(L)` for a difference diagonal: the number of squares of `X` on the diagonal `t`. -/
def betaT (X : Finset (Sq n)) (t : ℤ) : ℕ := (X.filter fun p => dg p = t).card
/-- `β_X(L)` for a sum diagonal: the number of squares of `X` on the diagonal `s`. -/
def betaS (X : Finset (Sq n)) (s : ℕ) : ℕ := (X.filter fun p => sm p = s).card

/-- Second term of the identities: the number of pairs `(L, s)`, `L` an occupied diagonal and `s` a
non-needy square of `X` on `L`.  (Each square lies on exactly one diagonal of each kind, so the pairs
are counted by squares; `waste2_eq_card_pairs` is the literal pair count.) -/
def waste2 (D X : Finset (Sq n)) : ℕ :=
  (X.filter fun p => ¬ Needy D p ∧ dg p ∈ occT D).card + (X.filter fun p => ¬ Needy D p ∧ sm p ∈ occS D).card

/-- Third term: the number of needy squares of `X` lying on two occupied diagonals (`m(s) = 2`). -/
def needy2 (D X : Finset (Sq n)) : ℕ :=
  (X.filter fun p => Needy D p ∧ dg p ∈ occT D ∧ sm p ∈ occS D).card

/-- `U_X`: the number of needy squares of `X` on no occupied diagonal (`m(s) = 0`). -/
def uncov (D X : Finset (Sq n)) : ℕ :=
  (X.filter fun p => Needy D p ∧ dg p ∉ occT D ∧ sm p ∉ occS D).card

/-- First term of the frame identity (F): `∑ (2 - β_X(L))` over the occupied diagonals `L`. -/
def wasteF (D X : Finset (Sq n)) : ℕ :=
  ∑ t ∈ occT D, (2 - betaT X t) + ∑ s ∈ occS D, (2 - betaS X s)

/-- First term of the side identities (V), (H): the number of occupied diagonals with `β_X(L) = 0`. -/
def zeros (D X : Finset (Sq n)) : ℕ :=
  ((occT D).filter fun t => betaT X t = 0).card + ((occS D).filter fun s => betaS X s = 0).card

/-- The term `[w = h]([u0 occupied] + [v0 occupied])` of the side identities, where `u0` is the
difference diagonal `t = c - a` and `v0` the sum diagonal `s = a + d` (the two diagonals of a square
box). -/
def sqTerm (D : Finset (Sq n)) (a b c d : Fin n) : ℕ :=
  if (b : ℕ) - a = (d : ℕ) - c then
    (if (c : ℤ) - (a : ℤ) ∈ occT D then 1 else 0) + (if (a : ℕ) + (d : ℕ) ∈ occS D then 1 else 0)
  else 0

end QueenDom

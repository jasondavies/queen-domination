import QueenDom
/-! Cross-check of `QueenDom.enumCases` against `geom.cases_by_frame` (code/frame/geom.py) for many `(n, k)`.
Run as `lake env lean scripts/CrossCheck.lean | python3 -B scripts/crosscheck.py ../code/frame`; prints one line `n k [codes...]` per pair. -/
open QueenDom

def Case.code' (c : Case) : Nat :=
  (((c.ml * 100 + c.mr) * 100 + c.mb) * 100 + c.mt) * 100000000 + c.dR * 1000000 + c.dC * 10000
    + c.dT * 100 + c.dS

def pairs : List (Nat × Nat) :=
  [(4, 2), (6, 3), (8, 4), (10, 5), (12, 6), (14, 7), (16, 8), (18, 9), (20, 10), (24, 12), (32, 16), (35, 18),
   (5, 3), (7, 4), (9, 5), (11, 6), (13, 7), (7, 3), (9, 4), (11, 5), (13, 6),
   (6, 4), (8, 5), (10, 6), (8, 6), (9, 7), (5, 2), (6, 2), (10, 3), (3, 1), (4, 1)]

def main : IO Unit := do
  for (n, k) in pairs do
    IO.println s!"{n} {k} {(enumCases n k).map Case.code'}"

#eval main

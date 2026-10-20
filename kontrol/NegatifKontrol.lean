/-
  kontrol/NegatifKontrol.lean  v1.1 -- negative control (not part of the library build).
  Run:  lake env lean kontrol/NegatifKontrol.lean
  Expected: the CORRECT line is accepted, the CORRUPTED line is rejected with one error.
-/
import CvsIndexLaw

-- CORRECT input: index 0 of Fin 3 (N = 1) carries label 0 - 1 = -1.
example : CvS.lab (0 : CvS.Idx 1) = -1 := by decide

-- CORRUPTED input: claims label 0. This must FAIL.
example : CvS.lab (0 : CvS.Idx 1) = 0 := by decide

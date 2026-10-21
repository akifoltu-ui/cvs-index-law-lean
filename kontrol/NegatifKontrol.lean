/-
  kontrol/NegatifKontrol.lean  v1.2 -- negative control (not part of the library build).
  Run:  lake env lean kontrol/NegatifKontrol.lean
  Expected: exactly TWO errors, one per CORRUPTED block; every CORRECT line is accepted.
-/
import CvsIndexLaw

-- CORRECT input: index 0 of Fin 3 (N = 1) carries label 0 - 1 = -1.
example : CvS.lab (0 : CvS.Idx 1) = -1 := by decide

-- CORRUPTED input: claims label 0. This must FAIL.
example : CvS.lab (0 : CvS.Idx 1) = 0 := by decide

-- CORRECT input: the library proof of symmetry is accepted.
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) : Q.IsSymm := CvS.isSymm_of_isCvS hC

-- CORRUPTED proof: drops the sign-flip step. This must FAIL (unsolved goals).
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) (i j : CvS.Idx N) (h : i ≠ j) : Q j i = Q i j := by
  rw [hC.off j i (Ne.symm h), hC.off i j h]

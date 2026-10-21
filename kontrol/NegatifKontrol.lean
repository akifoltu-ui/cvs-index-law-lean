/-
  kontrol/NegatifKontrol.lean  v1.4 -- negative control (not part of the library build).
  Run:  lake env lean kontrol/NegatifKontrol.lean
  Expected: exactly FOUR errors, one per CORRUPTED block; every CORRECT line is accepted.
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

-- CORRECT input: the commutator identity is accepted.
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) : CvS.D N * Q - Q * CvS.D N = CvS.wedge b (fun _ => 1) :=
  CvS.commutator hC

-- CORRUPTED input: wedge with the factors swapped (wrong sign). This must FAIL.
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) : CvS.D N * Q - Q * CvS.D N = CvS.wedge (fun _ => 1) b :=
  CvS.commutator hC

-- CORRECT input: Lemma 5.2(b) is accepted.
example {N : ℕ} (φ ξ : CvS.Idx N → ℝ) (hc : ∑ k, φ k * ξ k ≠ 0) (s : ℝ) :
    (CvS.Dprime φ ξ - s • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).det
      = -(s / ∑ k, φ k * ξ k) * (CvS.P fun k => φ k * ξ k).eval s :=
  CvS.det_Dprime φ ξ hc s

-- CORRUPTED input: Lemma 5.2(b) with the sign of s/c flipped. This must FAIL.
example {N : ℕ} (φ ξ : CvS.Idx N → ℝ) (hc : ∑ k, φ k * ξ k ≠ 0) (s : ℝ) :
    (CvS.Dprime φ ξ - s • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).det
      = (s / ∑ k, φ k * ξ k) * (CvS.P fun k => φ k * ξ k).eval s :=
  CvS.det_Dprime φ ξ hc s

/-
  kontrol/NegatifKontrol.lean  v1.7 -- negative control (not part of the library build).
  Run:  lake env lean kontrol/NegatifKontrol.lean
  Expected: exactly SEVEN errors, one per CORRUPTED block; every CORRECT line is accepted.
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

-- CORRECT input: Lemma 5.3 for φ = x η + y β is accepted.
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) (lam : ℝ) (ξ : CvS.Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).mulVec ξ = 0) (x y : ℝ)
    (hc : ∑ k, (x + y * b k) * ξ k ≠ 0) :
    ((Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ))
      * CvS.Dprime (fun k => x + y * b k) ξ).IsSymm :=
  CvS.Qlam_Dprime_isSymm hC lam ξ hξ x y hc

-- CORRUPTED input: Lemma 5.3 claimed for an arbitrary φ outside span{η, β}.
-- Numerically the asymmetry is 0.06–21 there. This must FAIL.
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) (lam : ℝ) (ξ φ : CvS.Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).mulVec ξ = 0) (x y : ℝ)
    (hc : ∑ k, (x + y * b k) * ξ k ≠ 0) :
    ((Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) * CvS.Dprime φ ξ).IsSymm :=
  CvS.Qlam_Dprime_isSymm hC lam ξ hξ x y hc

-- CORRECT input: Lemma 5.4 for an even eigenvector is accepted.
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) (lam : ℝ) (ξ : CvS.Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).mulVec ξ = 0)
    (hsimple : ∀ w : CvS.Idx N → ℝ,
      (Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).mulVec w = 0 → ∃ t : ℝ, w = t • ξ)
    (heven : ∀ i, ξ (Fin.rev i) = ξ i) (hne : ∃ k, k ≠ CvS.e0 N ∧ ξ k ≠ 0) :
    ∑ k, ξ k ≠ 0 :=
  (CvS.nondeg_even hC lam ξ hξ hsimple heven hne).2

-- CORRUPTED input: the same conclusion for an ODD eigenvector.
-- Numerically <eta, xi> = 0 there (max 2.6e-14). This must FAIL.
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) (lam : ℝ) (ξ : CvS.Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).mulVec ξ = 0)
    (hsimple : ∀ w : CvS.Idx N → ℝ,
      (Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).mulVec w = 0 → ∃ t : ℝ, w = t • ξ)
    (hodd : ∀ i, ξ (Fin.rev i) = - ξ i) (hne : ∃ k, k ≠ CvS.e0 N ∧ ξ k ≠ 0) :
    ∑ k, ξ k ≠ 0 :=
  (CvS.nondeg_even hC lam ξ hξ hsimple hodd hne).2

-- CORRECT input: Lemma 5.5, Q_λ(w,w) = F G' - F' G, is accepted.
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) (lam : ℝ) (ξ : CvS.Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).mulVec ξ = 0)
    (s : ℝ) (hs : ∀ j : CvS.Idx N, (CvS.lab j : ℝ) - s ≠ 0) :
    ∑ i, ∑ j, ξ i / ((CvS.lab i : ℝ) - s) * (Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) i j
        * (ξ j / ((CvS.lab j : ℝ) - s))
      = (∑ k, ξ k / ((CvS.lab k : ℝ) - s)) * (∑ k, b k * ξ k / ((CvS.lab k : ℝ) - s) ^ 2)
        - (∑ k, ξ k / ((CvS.lab k : ℝ) - s) ^ 2) * (∑ k, b k * (ξ k / ((CvS.lab k : ℝ) - s))) :=
  CvS.Qlam_norm hC lam ξ hξ s hs

-- CORRUPTED input: the sign-flipped formula F' G - F G'.
-- Numerically it fails at all 300 test points (median deviation 1.2). This must FAIL.
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) (lam : ℝ) (ξ : CvS.Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).mulVec ξ = 0)
    (s : ℝ) (hs : ∀ j : CvS.Idx N, (CvS.lab j : ℝ) - s ≠ 0) :
    ∑ i, ∑ j, ξ i / ((CvS.lab i : ℝ) - s) * (Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) i j
        * (ξ j / ((CvS.lab j : ℝ) - s))
      = (∑ k, ξ k / ((CvS.lab k : ℝ) - s) ^ 2) * (∑ k, b k * (ξ k / ((CvS.lab k : ℝ) - s)))
        - (∑ k, ξ k / ((CvS.lab k : ℝ) - s)) * (∑ k, b k * ξ k / ((CvS.lab k : ℝ) - s) ^ 2) :=
  CvS.Qlam_norm hC lam ξ hξ s hs

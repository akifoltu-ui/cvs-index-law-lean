/-
  kontrol/NegatifKontrol.lean  v1.13 -- negative control (not part of the library build).
  Run:  lake env lean kontrol/NegatifKontrol.lean
  Expected: exactly TWENTY-FOUR errors, one per CORRUPTED block; every CORRECT line is accepted.
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

-- CORRECT input: the bridge lemma applied as stated is accepted.
open Matrix in
example {N : ℕ} (Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ) (hQ : Q.IsHermitian) (μ : ℝ)
    (q : QuadraticForm ℝ (CvS.Idx N → ℝ))
    (hq : ∀ x, q x = x ⬝ᵥ ((Q - μ • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) *ᵥ x)) :
    sigNeg q = (Finset.univ.filter (fun i => hQ.eigenvalues i < μ)).card :=
  CvS.kappa_eq_sigNeg Q hQ μ q hq

-- CORRUPTED input (bridge 1): inequality flipped (counts eigenvalues ABOVE μ). This must FAIL.
open Matrix in
example {N : ℕ} (Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ) (hQ : Q.IsHermitian) (μ : ℝ)
    (q : QuadraticForm ℝ (CvS.Idx N → ℝ))
    (hq : ∀ x, q x = x ⬝ᵥ ((Q - μ • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) *ᵥ x)) :
    sigNeg q = (Finset.univ.filter (fun i => μ < hQ.eigenvalues i)).card :=
  CvS.kappa_eq_sigNeg Q hQ μ q hq

-- CORRUPTED input (bridge 2): form built from Q + μ instead of Q - μ. This must FAIL.
open Matrix in
example {N : ℕ} (Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ) (hQ : Q.IsHermitian) (μ : ℝ)
    (q : QuadraticForm ℝ (CvS.Idx N → ℝ))
    (hq : ∀ x, q x = x ⬝ᵥ ((Q + μ • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) *ᵥ x)) :
    sigNeg q = (Finset.univ.filter (fun i => hQ.eigenvalues i < μ)).card :=
  CvS.kappa_eq_sigNeg Q hQ μ q hq

-- CORRUPTED input (balance 1): orthogonality claimed for EQUAL eigenvalues. This must FAIL.
open Matrix in
example {n : Type*} [Fintype n] {B T : Matrix n n ℝ} (hB : Bᵀ = B)
    (hBT : (B * T)ᵀ = B * T) {v w : n → ℝ} {r : ℝ}
    (hv : T *ᵥ v = r • v) (hw : T *ᵥ w = r • w) (hrr : r = r) :
    v ⬝ᵥ (B *ᵥ w) = 0 :=
  CvS.eigvec_orth hB hBT hv hw hrr

-- CORRUPTED input (balance 2): 2x2 block with POSITIVE determinant claimed to have one negative direction.
open Matrix in
example (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.IsHermitian) (hdet : 0 < M.det)
    (q : QuadraticForm ℝ (Fin 2 → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (M *ᵥ x)) :
    sigNeg q = 1 :=
  CvS.block2_sigNeg M hM hdet q hq

-- CORRUPTED input (balance 3): block claimed to have TWO negative directions. This must FAIL.
open Matrix in
example (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.IsHermitian) (hdet : M.det < 0)
    (q : QuadraticForm ℝ (Fin 2 → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (M *ᵥ x)) :
    sigNeg q = 2 :=
  CvS.block2_sigNeg M hM hdet q hq

-- CORRUPTED input (counting 1): congruence lemma claimed to count POSITIVE entries. This must FAIL.
open Matrix in
example {n : Type*} [Fintype n] [DecidableEq n] (A P : Matrix n n ℝ)
    (d : n → ℝ) (hP : IsUnit P.det) (hD : Pᵀ * A * P = diagonal d)
    (q : QuadraticForm ℝ (n → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (A *ᵥ x)) :
    sigNeg q = (Finset.univ.filter (fun i => 0 < d i)).card :=
  CvS.sigNeg_of_congr_diag A P d hP hD q hq

-- CORRUPTED input (counting 2): family without the orthogonality hypothesis. This must FAIL.
open Matrix in
example {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ)
    (v : n → n → ℝ) (hnz : ∀ i, v i ⬝ᵥ (B *ᵥ v i) ≠ 0)
    (q : QuadraticForm ℝ (n → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (B *ᵥ x)) :
    sigNeg q = (Finset.univ.filter (fun i => v i ⬝ᵥ (B *ᵥ v i) < 0)).card :=
  CvS.sigNeg_of_orth_family B v hnz q hq

-- CORRUPTED input (counting 3): congruence lemma used without invertibility of P. This must FAIL.
open Matrix in
example {n : Type*} [Fintype n] [DecidableEq n] (A P : Matrix n n ℝ)
    (d : n → ℝ) (hD : Pᵀ * A * P = diagonal d)
    (q : QuadraticForm ℝ (n → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (A *ᵥ x)) :
    sigNeg q = (Finset.univ.filter (fun i => d i < 0)).card :=
  CvS.sigNeg_of_congr_diag A P d hD q hq

-- CORRUPTED input (complex 1): field orthogonality for EQUAL eigenvalues. This must FAIL.
open Matrix in
example {K : Type*} [Field K] {n : Type*} [Fintype n] {B T : Matrix n n K}
    (hB : Bᵀ = B) (hBT : (B * T)ᵀ = B * T) {v w : n → K} {r : K}
    (hv : T *ᵥ v = r • v) (hw : T *ᵥ w = r • w) (hrr : r = r) :
    v ⬝ᵥ (B *ᵥ w) = 0 :=
  CvS.eigvec_orth_field hB hBT hv hw hrr

-- CORRUPTED input (complex 2): conjugate eigenvector claimed with the UNconjugated eigenvalue.
open Matrix in
example {n : Type*} [Fintype n] {T : Matrix n n ℝ} {z : n → ℂ} {ζ : ℂ}
    (hz : T.map (algebraMap ℝ ℂ) *ᵥ z = ζ • z) :
    T.map (algebraMap ℝ ℂ) *ᵥ star z = ζ • star z :=
  CvS.conj_eigvec hz

-- CORRUPTED input (complex 3): hermitian norm zero claimed for a REAL eigenvalue (ζ = conj ζ).
open Matrix in
example {n : Type*} [Fintype n] {B T : Matrix n n ℝ}
    (hB : Bᵀ = B) (hBT : (B * T)ᵀ = B * T) {z : n → ℂ} {ζ : ℂ}
    (hz : T.map (algebraMap ℝ ℂ) *ᵥ z = ζ • z) (hζ : ζ = star ζ) :
    z ⬝ᵥ (B.map (algebraMap ℝ ℂ) *ᵥ star z) = 0 :=
  CvS.herm_norm_zero hB hBT hz hζ

-- CORRUPTED input (parts 1): the two norms claimed EQUAL (u-norm minus w-norm = 0). This must FAIL.
open Matrix in
example {n : Type*} [Fintype n] {B T : Matrix n n ℝ}
    (hB : Bᵀ = B) (hBT : (B * T)ᵀ = B * T) {z : n → ℂ} {ζ : ℂ}
    (hz : T.map (algebraMap ℝ ℂ) *ᵥ z = ζ • z) (hζ : ζ ≠ star ζ) :
    (fun i => (z i).re) ⬝ᵥ (B *ᵥ fun i => (z i).re)
      - (fun i => (z i).im) ⬝ᵥ (B *ᵥ fun i => (z i).im) = 0 :=
  CvS.herm_split hB hBT hz hζ

-- CORRUPTED input (parts 2): real and imaginary parts swapped. This must FAIL.
open Matrix in
example {n : Type*} [Fintype n] (B : Matrix n n ℝ) (v : n → ℝ) (z : n → ℂ) :
    ((fun i => (v i : ℂ)) ⬝ᵥ (B.map (algebraMap ℝ ℂ) *ᵥ z)).re
        = v ⬝ᵥ (B *ᵥ fun i => (z i).im) ∧
      ((fun i => (v i : ℂ)) ⬝ᵥ (B.map (algebraMap ℝ ℂ) *ᵥ z)).im
        = v ⬝ᵥ (B *ᵥ fun i => (z i).re) :=
  CvS.real_pair_re_im B v z

-- CORRUPTED input (parts 3): cross orthogonality with EQUAL eigenvalues. This must FAIL.
open Matrix in
example {n : Type*} [Fintype n] {B T : Matrix n n ℝ}
    (hB : Bᵀ = B) (hBT : (B * T)ᵀ = B * T) {v : n → ℝ} {r : ℝ} (hv : T *ᵥ v = r • v)
    {z : n → ℂ} {ζ : ℂ} (hz : T.map (algebraMap ℝ ℂ) *ᵥ z = ζ • z) (hne : (r : ℂ) = ζ) :
    v ⬝ᵥ (B *ᵥ fun i => (z i).re) = 0 ∧ v ⬝ᵥ (B *ᵥ fun i => (z i).im) = 0 :=
  CvS.cross_orth hB hBT hv hz hne

-- CORRUPTED input (plane 1): pair orthogonality without excluding the conjugate (ζ = conj ω).
open Matrix in
example {n : Type*} [Fintype n] {B T : Matrix n n ℝ}
    (hB : Bᵀ = B) (hBT : (B * T)ᵀ = B * T) {z y : n → ℂ} {ζ ω : ℂ}
    (hz : T.map (algebraMap ℝ ℂ) *ᵥ z = ζ • z) (hy : T.map (algebraMap ℝ ℂ) *ᵥ y = ω • y)
    (h1 : ζ ≠ ω) (h2 : ζ = star ω) :
    (fun i => (z i).re) ⬝ᵥ (B *ᵥ fun i => (y i).re) = 0 ∧
      (fun i => (z i).re) ⬝ᵥ (B *ᵥ fun i => (y i).im) = 0 ∧
      (fun i => (z i).im) ⬝ᵥ (B *ᵥ fun i => (y i).re) = 0 ∧
      (fun i => (z i).im) ⬝ᵥ (B *ᵥ fun i => (y i).im) = 0 :=
  CvS.pair_orth hB hBT hz hy h1 h2

-- CORRUPTED input (plane 2): plane split claimed with norms of the SAME sign. This must FAIL.
open Matrix in
example (a c : ℝ) (h : a ≠ 0 ∨ c ≠ 0) :
    ∃ α β γ δ : ℝ, α * γ * a + (α * δ + β * γ) * c - β * δ * a = 0 ∧
      0 < (α ^ 2 * a + 2 * α * β * c - β ^ 2 * a) * (γ ^ 2 * a + 2 * γ * δ * c - δ ^ 2 * a) ∧
      α * δ - β * γ ≠ 0 :=
  CvS.plane_split_num a c h

-- CORRUPTED input (plane 3): wrong sign in the real part of the bilinear pairing. This must FAIL.
open Matrix in
example {n : Type*} [Fintype n] (B : Matrix n n ℝ) (z y : n → ℂ) :
    (z ⬝ᵥ (B.map (algebraMap ℝ ℂ) *ᵥ y)).re
        = (fun i => (z i).re) ⬝ᵥ (B *ᵥ fun i => (y i).re)
          + (fun i => (z i).im) ⬝ᵥ (B *ᵥ fun i => (y i).im) ∧
      (z ⬝ᵥ (B.map (algebraMap ℝ ℂ) *ᵥ y)).im
        = (fun i => (z i).re) ⬝ᵥ (B *ᵥ fun i => (y i).im)
          + (fun i => (z i).im) ⬝ᵥ (B *ᵥ fun i => (y i).re) :=
  CvS.cc_re_im B z y

/-
  kontrol/NegatifKontrol.lean  v1.25 -- negative control (not part of the library build).
  Run:  lake env lean kontrol/NegatifKontrol.lean
  Expected: exactly SIXTY errors, one per CORRUPTED block; every CORRECT line is accepted.
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

-- CORRECT input: Lemma 2(b) is accepted.
example {N : ℕ} (φ ξ : CvS.Idx N → ℝ) (hc : ∑ k, φ k * ξ k ≠ 0) (s : ℝ) :
    (CvS.Dprime φ ξ - s • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).det
      = -(s / ∑ k, φ k * ξ k) * (CvS.P fun k => φ k * ξ k).eval s :=
  CvS.det_Dprime φ ξ hc s

-- CORRUPTED input: Lemma 2(b) with the sign of s/c flipped. This must FAIL.
example {N : ℕ} (φ ξ : CvS.Idx N → ℝ) (hc : ∑ k, φ k * ξ k ≠ 0) (s : ℝ) :
    (CvS.Dprime φ ξ - s • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).det
      = (s / ∑ k, φ k * ξ k) * (CvS.P fun k => φ k * ξ k).eval s :=
  CvS.det_Dprime φ ξ hc s

-- CORRECT input: Lemma 3 for φ = x η + y β is accepted.
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) (lam : ℝ) (ξ : CvS.Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).mulVec ξ = 0) (x y : ℝ)
    (hc : ∑ k, (x + y * b k) * ξ k ≠ 0) :
    ((Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ))
      * CvS.Dprime (fun k => x + y * b k) ξ).IsSymm :=
  CvS.Qlam_Dprime_isSymm hC lam ξ hξ x y hc

-- CORRUPTED input: Lemma 3 claimed for an arbitrary φ outside span{η, β}.
-- Numerically the asymmetry is 0.06–21 there. This must FAIL.
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) (lam : ℝ) (ξ φ : CvS.Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).mulVec ξ = 0) (x y : ℝ)
    (hc : ∑ k, (x + y * b k) * ξ k ≠ 0) :
    ((Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) * CvS.Dprime φ ξ).IsSymm :=
  CvS.Qlam_Dprime_isSymm hC lam ξ hξ x y hc

-- CORRECT input: Lemma 4 for an even eigenvector is accepted.
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

-- CORRECT input: Lemma 6, Q_λ(w,w) = F G' - F' G, is accepted.
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

-- CORRUPTED input (indep 1): injectivity stated with ζ twice (conjugates missing). This must FAIL.
open Matrix in
example {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]
    (T : Matrix n n ℝ) (r : ι → ℝ) (v : ι → n → ℝ)
    (hv : ∀ i, T *ᵥ v i = r i • v i) (hv0 : ∀ i, v i ≠ 0)
    (ζ : κ → ℂ) (z : κ → n → ℂ)
    (hz : ∀ k, T.map (algebraMap ℝ ℂ) *ᵥ z k = ζ k • z k) (hz0 : ∀ k, z k ≠ 0)
    (hinj : Function.Injective (Sum.elim (fun i => (r i : ℂ)) (Sum.elim ζ ζ))) :
    LinearIndependent ℝ
      (Sum.elim v (Sum.elim (fun k j => (z k j).re) (fun k j => (z k j).im))) :=
  CvS.real_family_indep T r v hv hv0 ζ z hz hz0 hinj

-- CORRUPTED input (indep 2): the nonzero hypothesis on real eigenvectors dropped. This must FAIL.
open Matrix in
example {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]
    (T : Matrix n n ℝ) (r : ι → ℝ) (v : ι → n → ℝ)
    (hv : ∀ i, T *ᵥ v i = r i • v i)
    (ζ : κ → ℂ) (z : κ → n → ℂ)
    (hz : ∀ k, T.map (algebraMap ℝ ℂ) *ᵥ z k = ζ k • z k) (hz0 : ∀ k, z k ≠ 0)
    (hinj : Function.Injective
      (Sum.elim (fun i => (r i : ℂ)) (Sum.elim ζ (fun k => star (ζ k))))) :
    LinearIndependent ℝ
      (Sum.elim v (Sum.elim (fun k j => (z k j).re) (fun k j => (z k j).im))) :=
  CvS.real_family_indep T r v hv hz ζ z hz hz0 hinj

-- CORRUPTED input (indep 3): wrong per-term identity (factor 2 dropped). This must FAIL.
open Matrix in
example (g₁ g₂ : ℝ) (z : ℂ) :
    ((g₁ : ℂ) - Complex.I * g₂) * z + ((g₁ : ℂ) + Complex.I * g₂) * star z
      = (((g₁ * z.re + g₂ * z.im) : ℝ) : ℂ) :=
  CvS.re_im_combo g₁ g₂ z

-- CORRUPTED input (null 1): determinant hypothesis dropped. This must FAIL.
open Matrix in
example {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ)
    (W : n → n → ℝ) (hW : LinearIndependent ℝ W) (y : n → ℝ)
    (hy : ∀ b, y ⬝ᵥ (B *ᵥ W b) = 0) : y = 0 :=
  CvS.null_vec_zero B hW W hW y hy

-- CORRUPTED input (null 2): conclusion inverted (y ≠ 0). This must FAIL.
open Matrix in
example {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ)
    (hBdet : B.det ≠ 0) (W : n → n → ℝ) (hW : LinearIndependent ℝ W) (y : n → ℝ)
    (hy : ∀ b, y ⬝ᵥ (B *ᵥ W b) = 0) : y ≠ 0 :=
  CvS.null_vec_zero B hBdet W hW y hy

-- CORRUPTED input (null 3): orthogonality to all members replaced by orthogonality to one. This must FAIL.
open Matrix in
example {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ)
    (hBdet : B.det ≠ 0) (W : n → n → ℝ) (hW : LinearIndependent ℝ W) (a : n)
    (ha : W a ⬝ᵥ (B *ᵥ W a) = 0) : False :=
  CvS.not_null_member B hBdet W hW a ha

-- CORRUPTED input (balance 4): the |κ| contribution of the non-real pairs omitted. This must FAIL.
open Matrix in
example {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]
    {B T : Matrix n n ℝ} (hB : Bᵀ = B) (hBdet : B.det ≠ 0) (hBT : (B * T)ᵀ = B * T)
    (r : ι → ℝ) (v : ι → n → ℝ) (hv : ∀ i, T *ᵥ v i = r i • v i) (hv0 : ∀ i, v i ≠ 0)
    (ζ : κ → ℂ) (z : κ → n → ℂ)
    (hz : ∀ k, T.map (algebraMap ℝ ℂ) *ᵥ z k = ζ k • z k) (hz0 : ∀ k, z k ≠ 0)
    (hinj : Function.Injective
      (Sum.elim (fun i => (r i : ℂ)) (Sum.elim ζ (fun k => star (ζ k)))))
    (hcard : Fintype.card ι + 2 * Fintype.card κ = Fintype.card n)
    (q : QuadraticForm ℝ (n → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (B *ᵥ x)) :
    sigNeg q = (Finset.univ.filter (fun i => v i ⬝ᵥ (B *ᵥ v i) < 0)).card :=
  CvS.pontryagin_balance hB hBdet hBT r v hv hv0 ζ z hz hz0 hinj hcard q hq

-- CORRUPTED input (balance 5): wrong dimension count (pairs counted once). This must FAIL.
open Matrix in
example {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]
    {B T : Matrix n n ℝ} (hB : Bᵀ = B) (hBdet : B.det ≠ 0) (hBT : (B * T)ᵀ = B * T)
    (r : ι → ℝ) (v : ι → n → ℝ) (hv : ∀ i, T *ᵥ v i = r i • v i) (hv0 : ∀ i, v i ≠ 0)
    (ζ : κ → ℂ) (z : κ → n → ℂ)
    (hz : ∀ k, T.map (algebraMap ℝ ℂ) *ᵥ z k = ζ k • z k) (hz0 : ∀ k, z k ≠ 0)
    (hinj : Function.Injective
      (Sum.elim (fun i => (r i : ℂ)) (Sum.elim ζ (fun k => star (ζ k)))))
    (hcard : Fintype.card ι + Fintype.card κ = Fintype.card n)
    (q : QuadraticForm ℝ (n → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (B *ᵥ x)) :
    sigNeg q = (Finset.univ.filter (fun i => v i ⬝ᵥ (B *ᵥ v i) < 0)).card + Fintype.card κ :=
  CvS.pontryagin_balance hB hBdet hBT r v hv hv0 ζ z hz hz0 hinj hcard q hq

-- CORRUPTED input (balance 6): real eigenvectors counted by POSITIVE norm. This must FAIL.
open Matrix in
example {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]
    {B T : Matrix n n ℝ} (hB : Bᵀ = B) (hBdet : B.det ≠ 0) (hBT : (B * T)ᵀ = B * T)
    (r : ι → ℝ) (v : ι → n → ℝ) (hv : ∀ i, T *ᵥ v i = r i • v i) (hv0 : ∀ i, v i ≠ 0)
    (ζ : κ → ℂ) (z : κ → n → ℂ)
    (hz : ∀ k, T.map (algebraMap ℝ ℂ) *ᵥ z k = ζ k • z k) (hz0 : ∀ k, z k ≠ 0)
    (hinj : Function.Injective
      (Sum.elim (fun i => (r i : ℂ)) (Sum.elim ζ (fun k => star (ζ k)))))
    (hcard : Fintype.card ι + 2 * Fintype.card κ = Fintype.card n)
    (q : QuadraticForm ℝ (n → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (B *ᵥ x)) :
    sigNeg q = (Finset.univ.filter (fun i => 0 < v i ⬝ᵥ (B *ᵥ v i))).card + Fintype.card κ :=
  CvS.pontryagin_balance hB hBdet hBT r v hv hv0 ζ z hz hz0 hinj hcard q hq

-- CORRUPTED input (lock 1): eigenvalue shifted by one. This must FAIL.
open Matrix in
example {N : ℕ} (x : CvS.Idx N → ℝ) (hc : ∑ k, x k ≠ 0) (s : ℝ)
    (hs : ∀ j : CvS.Idx N, (CvS.lab j : ℝ) - s ≠ 0) (hF : ∑ k, x k / ((CvS.lab k : ℝ) - s) = 0) :
    CvS.Dprime (fun _ => (1 : ℝ)) x *ᵥ (fun i => (CvS.lab i : ℝ) * x i / ((CvS.lab i : ℝ) - s))
      = (s + 1) • (fun i => (CvS.lab i : ℝ) * x i / ((CvS.lab i : ℝ) - s)) :=
  CvS.Dprime_eigvec_r x hc s hs hF

-- CORRUPTED input (lock 2): eigenvector without the label factor. This must FAIL.
open Matrix in
example {N : ℕ} (x : CvS.Idx N → ℝ) (hc : ∑ k, x k ≠ 0) (s : ℝ)
    (hs : ∀ j : CvS.Idx N, (CvS.lab j : ℝ) - s ≠ 0) (hF : ∑ k, x k / ((CvS.lab k : ℝ) - s) = 0) :
    CvS.Dprime (fun _ => (1 : ℝ)) x *ᵥ (fun i => x i / ((CvS.lab i : ℝ) - s))
      = s • (fun i => x i / ((CvS.lab i : ℝ) - s)) :=
  CvS.Dprime_eigvec_r x hc s hs hF

-- CORRUPTED input (lock 3): wrong resolvent sign in F. This must FAIL.
open Matrix in
example {N : ℕ} (x : CvS.Idx N → ℝ) (s : ℝ)
    (hs : ∀ j : CvS.Idx N, (CvS.lab j : ℝ) - s ≠ 0) (hroot : (CvS.P x).eval s = 0) :
    ∑ k, x k / ((CvS.lab k : ℝ) + s) = 0 :=
  CvS.F_zero_of_root x s hs hroot

-- CORRUPTED input (norm 1): lock norm with the sign flipped. This must FAIL.
open Matrix in
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) (μ : ℝ) (x : CvS.Idx N → ℝ)
    (hx : (Q - μ • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) *ᵥ x = Pi.single (CvS.e0 N) 1)
    (s : ℝ) (hs : ∀ j : CvS.Idx N, (CvS.lab j : ℝ) - s ≠ 0) :
    ∑ i, ∑ j, ((CvS.lab i : ℝ) * x i / ((CvS.lab i : ℝ) - s))
        * (Q - μ • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) i j
        * ((CvS.lab j : ℝ) * x j / ((CvS.lab j : ℝ) - s))
      = -(s ^ 2 * ((∑ k, x k / ((CvS.lab k : ℝ) - s))
            * (∑ k, b k * x k / ((CvS.lab k : ℝ) - s) ^ 2)
          - (∑ k, x k / ((CvS.lab k : ℝ) - s) ^ 2)
            * (∑ k, b k * (x k / ((CvS.lab k : ℝ) - s))))) :=
  CvS.lock_norm hC μ x hx s hs

-- CORRUPTED input (norm 2): lock norm without the s² factor. This must FAIL.
open Matrix in
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) (μ : ℝ) (x : CvS.Idx N → ℝ)
    (hx : (Q - μ • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) *ᵥ x = Pi.single (CvS.e0 N) 1)
    (s : ℝ) (hs : ∀ j : CvS.Idx N, (CvS.lab j : ℝ) - s ≠ 0) :
    ∑ i, ∑ j, ((CvS.lab i : ℝ) * x i / ((CvS.lab i : ℝ) - s))
        * (Q - μ • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) i j
        * ((CvS.lab j : ℝ) * x j / ((CvS.lab j : ℝ) - s))
      = (∑ k, x k / ((CvS.lab k : ℝ) - s)) * (∑ k, b k * x k / ((CvS.lab k : ℝ) - s) ^ 2)
          - (∑ k, x k / ((CvS.lab k : ℝ) - s) ^ 2) * (∑ k, b k * (x k / ((CvS.lab k : ℝ) - s))) :=
  CvS.lock_norm hC μ x hx s hs

-- CORRUPTED input (norm 3): Q_μ(x, x) claimed equal to the wrong coordinate. This must FAIL.
open Matrix in
example {N : ℕ} (A : Matrix (CvS.Idx N) (CvS.Idx N) ℝ) (x : CvS.Idx N → ℝ)
    (hx : A *ᵥ x = Pi.single (CvS.e0 N) 1) (i : CvS.Idx N) : x ⬝ᵥ (A *ᵥ x) = x i :=
  CvS.lock_norm_x A x hx

-- CORRUPTED input (sign 1): sign condition reversed (negative norm ↔ P'·P_β < 0). This must FAIL.
open Matrix in
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) (μ : ℝ) (x : CvS.Idx N → ℝ)
    (hx : (Q - μ • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) *ᵥ x = Pi.single (CvS.e0 N) 1)
    (s : ℝ) (hs : ∀ j : CvS.Idx N, (CvS.lab j : ℝ) - s ≠ 0) (hroot : (CvS.P x).eval s = 0) :
    (∑ i, ∑ j, ((CvS.lab i : ℝ) * x i / ((CvS.lab i : ℝ) - s))
        * (Q - μ • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) i j
        * ((CvS.lab j : ℝ) * x j / ((CvS.lab j : ℝ) - s)) < 0)
      ↔ (Polynomial.derivative (CvS.P x)).eval s * (CvS.P (fun k => b k * x k)).eval s < 0 :=
  CvS.lock_sign hC μ x hx s hs hroot

-- CORRUPTED input (sign 2): derivative formula without the F·S term. This must FAIL.
open Matrix in
example {N : ℕ} (x : CvS.Idx N → ℝ) (s : ℝ) (hs : ∀ j : CvS.Idx N, (CvS.lab j : ℝ) - s ≠ 0) :
    (Polynomial.derivative (CvS.P x)).eval s
      = (∏ j : CvS.Idx N, ((CvS.lab j : ℝ) - s)) * ∑ k, x k / ((CvS.lab k : ℝ) - s) ^ 2 :=
  CvS.P_deriv_eval x s hs

-- CORRUPTED input (sign 3): P_w(s) with the product omitted. This must FAIL.
open Matrix in
example {N : ℕ} (w : CvS.Idx N → ℝ) (s : ℝ) (hs : ∀ j : CvS.Idx N, (CvS.lab j : ℝ) - s ≠ 0) :
    (CvS.P w).eval s = ∑ k, w k / ((CvS.lab k : ℝ) - s) :=
  CvS.P_eval_div w s hs

-- CORRUPTED input (deg 1): degree claimed 2N + 1. This must FAIL.
example {N : ℕ} (x : CvS.Idx N → ℝ) (hc : ∑ k, x k ≠ 0) :
    (CvS.P x).natDegree = 2 * N + 1 :=
  CvS.natDegree_P_lock x hc

-- CORRUPTED input (deg 2): characteristic polynomial without the factor X. This must FAIL.
example {N : ℕ} (x : CvS.Idx N → ℝ) (hc : ∑ k, x k ≠ 0) :
    (CvS.Dprime (fun _ => (1 : ℝ)) x).charpoly = Polynomial.C (1 / ∑ k, x k) * CvS.P x :=
  CvS.charpoly_lock x hc

-- CORRUPTED input (deg 3): complex root count claimed 2N + 1. This must FAIL.
example {N : ℕ} (x : CvS.Idx N → ℝ) (hc : ∑ k, x k ≠ 0) :
    ((CvS.P x).map (algebraMap ℝ ℂ)).roots.card = 2 * N + 1 :=
  CvS.card_roots_lock x hc

-- CORRUPTED input (roots 1): the non-real roots counted once instead of twice. This must FAIL.
example {p : Polynomial ℝ} (hp : p.Separable) :
    p.roots.toFinset.card
        + ((p.map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z => 0 < z.im)).card
      = p.natDegree :=
  CvS.card_roots_split hp

-- CORRUPTED input (roots 2): p(z̄) = p(z) (conjugation dropped). This must FAIL.
example (p : Polynomial ℝ) (z : ℂ) :
    (p.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = (p.map (algebraMap ℝ ℂ)).eval z :=
  CvS.eval_map_conj p z

-- CORRUPTED input (roots 3): -z claimed to be a root instead of z̄. This must FAIL.
example {p : Polynomial ℝ} (hp : p ≠ 0) {z : ℂ} (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots) :
    -z ∈ (p.map (algebraMap ℝ ℂ)).roots :=
  CvS.mem_roots_conj hp hz

-- CORRUPTED input (family 1): conjugates dropped (ζ listed twice) yet injectivity claimed. This must FAIL.
example {ι κ : Type*} (r : ι → ℝ) (hr : Function.Injective r) (ζ : κ → ℂ)
    (hζ : Function.Injective ζ) (hpos : ∀ k, 0 < (ζ k).im) :
    Function.Injective (Sum.elim (fun i => (r i : ℂ)) (Sum.elim ζ ζ)) :=
  CvS.inj_sum_elim r hr ζ hζ hpos

-- CORRUPTED input (family 2): v_s claimed to vanish. This must FAIL.
example {N : ℕ} (x : CvS.Idx N → ℝ) (hx0 : x (CvS.e0 N) ≠ 0) (s : ℝ)
    (hs : ∀ j : CvS.Idx N, (CvS.lab j : ℝ) - s ≠ 0)
    (hF : ∑ k, x k / ((CvS.lab k : ℝ) - s) = 0) :
    (fun i => (CvS.lab i : ℝ) * x i / ((CvS.lab i : ℝ) - s)) = 0 :=
  CvS.vr_ne_zero x hx0 s hs hF

-- CORRUPTED input (family 3): N_c claimed to count every non-real root (no pairing). This must FAIL.
example {N : ℕ} (ξ : CvS.Idx N → ℝ) (hsep : (CvS.P ξ).Separable) :
    CvS.Nc ξ
      = 2 * (((CvS.P ξ).map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z => 0 < z.im)).card :=
  CvS.Nc_eq ξ hsep

-- CORRUPTED input (theorem6 1): lock with the sign indicator reversed ([x₀ > 0]). This must FAIL.
open Classical in
example {N : ℕ} (Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ) (a b : CvS.Idx N → ℝ)
    (hC : CvS.IsCvS Q a b) (hQ : Q.IsHermitian) (μ : ℝ)
    (hμ : IsUnit (Q - μ • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).det)
    (x : CvS.Idx N → ℝ)
    (hx : x = Matrix.mulVec (Q - μ • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ))⁻¹
      (Pi.single (CvS.e0 N) 1))
    (hx0 : x (CvS.e0 N) ≠ 0) (hηx : ∑ k, x k ≠ 0)
    (hsep : (CvS.P x).Separable) (hout : ∀ j : CvS.Idx N, (CvS.P x).eval (CvS.lab j : ℝ) ≠ 0) :
    CvS.Nc x + CvS.d b x + (if 0 < x (CvS.e0 N) then 1 else 0)
      = (Finset.univ.filter (fun i => hQ.eigenvalues i < μ)).card :=
  CvS.lock Q a b hC hQ μ hμ x hx hx0 hηx hsep hout

-- CORRUPTED input (theorem6 2): lock without the complex pairs N_c. This must FAIL.
open Classical in
example {N : ℕ} (Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ) (a b : CvS.Idx N → ℝ)
    (hC : CvS.IsCvS Q a b) (hQ : Q.IsHermitian) (μ : ℝ)
    (hμ : IsUnit (Q - μ • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)).det)
    (x : CvS.Idx N → ℝ)
    (hx : x = Matrix.mulVec (Q - μ • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ))⁻¹
      (Pi.single (CvS.e0 N) 1))
    (hx0 : x (CvS.e0 N) ≠ 0) (hηx : ∑ k, x k ≠ 0)
    (hsep : (CvS.P x).Separable) (hout : ∀ j : CvS.Idx N, (CvS.P x).eval (CvS.lab j : ℝ) ≠ 0) :
    CvS.d b x + (if x (CvS.e0 N) < 0 then 1 else 0)
      = (Finset.univ.filter (fun i => hQ.eigenvalues i < μ)).card :=
  CvS.lock Q a b hC hQ μ hμ x hx hx0 hηx hsep hout

-- CORRUPTED input (theorem6 3): q(w) = w ⬝ w (matrix dropped) claimed from exists_qform. This must FAIL.
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    ∃ q : QuadraticForm ℝ (n → ℝ), ∀ w, q w = w ⬝ᵥ w :=
  CvS.exists_qform A

-- CORRUPTED input (kernel 1): the singular balance without the complex pairs. This must FAIL.
open Matrix in
example {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]
    {B T : Matrix n n ℝ} (hB : Bᵀ = B) (hBT : (B * T)ᵀ = B * T)
    (r : ι → ℝ) (v : ι → n → ℝ) (hv : ∀ i, T *ᵥ v i = r i • v i) (hv0 : ∀ i, v i ≠ 0)
    (i₀ : ι) (hker : ∀ y, B *ᵥ y = 0 → ∃ t : ℝ, y = t • v i₀)
    (ζ : κ → ℂ) (z : κ → n → ℂ)
    (hz : ∀ k, T.map (algebraMap ℝ ℂ) *ᵥ z k = ζ k • z k) (hz0 : ∀ k, z k ≠ 0)
    (hinj : Function.Injective
      (Sum.elim (fun i => (r i : ℂ)) (Sum.elim ζ (fun k => star (ζ k)))))
    (hcard : Fintype.card ι + 2 * Fintype.card κ = Fintype.card n)
    (q : QuadraticForm ℝ (n → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (B *ᵥ x)) :
    sigNeg q = (Finset.univ.filter (fun i => v i ⬝ᵥ (B *ᵥ v i) < 0)).card :=
  CvS.pontryagin_balance_ker hB hBT r v hv hv0 i₀ hker ζ z hz hz0 hinj hcard q hq

-- CORRUPTED input (kernel 2): orthogonality to a basis claimed to force y = 0 (singular B). This must FAIL.
open Matrix in
example {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ) (hB : Bᵀ = B)
    (W : n → n → ℝ) (hW : LinearIndependent ℝ W) (y : n → ℝ)
    (hy : ∀ b, y ⬝ᵥ (B *ᵥ W b) = 0) : y = 0 :=
  CvS.orth_all_ker B hB W hW y hy

-- CORRUPTED input (kernel 3): non-positive norms counted instead of negative ones. This must FAIL.
open Matrix in
example {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ)
    (v : n → n → ℝ) (horth : ∀ i j, i ≠ j → v i ⬝ᵥ (B *ᵥ v j) = 0) (i₀ : n)
    (hnz : ∀ i, i ≠ i₀ → v i ⬝ᵥ (B *ᵥ v i) ≠ 0) (hv0 : v i₀ ≠ 0)
    (q : QuadraticForm ℝ (n → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (B *ᵥ x)) :
    sigNeg q = (Finset.univ.filter (fun i => v i ⬝ᵥ (B *ᵥ v i) ≤ 0)).card :=
  CvS.sigNeg_of_orth_family_ker B v horth i₀ hnz hv0 q hq

-- CORRUPTED input (theorem5a 1): index law without the complex pairs. This must FAIL.
open Classical in
example {N : ℕ} (Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ) (a b : CvS.Idx N → ℝ)
    (hC : CvS.IsCvS Q a b) (hQ : Q.IsHermitian) (lam : ℝ) (ξ : CvS.Idx N → ℝ)
    (hvec : Q.mulVec ξ = lam • ξ) (hne : ∃ k, k ≠ CvS.e0 N ∧ ξ k ≠ 0)
    (hsimple : Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' Q) lam) = 1)
    (heven : ∀ i, ξ (Fin.rev i) = ξ i)
    (hsep : (CvS.P ξ).Separable) (hout : ∀ j : CvS.Idx N, (CvS.P ξ).eval (CvS.lab j : ℝ) ≠ 0) :
    CvS.d b ξ = (Finset.univ.filter (fun i => hQ.eigenvalues i < lam)).card :=
  CvS.index_even Q a b hC hQ lam ξ hvec hne hsimple heven hsep hout

-- CORRUPTED input (theorem5a 2): the kernel claimed to be {ξ} itself (t = 1). This must FAIL.
open Matrix in
example {N : ℕ} (Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ) (lam : ℝ) (ξ : CvS.Idx N → ℝ)
    (hvec : Q.mulVec ξ = lam • ξ) (hξ0 : ξ ≠ 0)
    (hsimple : Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' Q) lam) = 1) :
    ∀ w : CvS.Idx N → ℝ, (Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) *ᵥ w = 0 → w = ξ :=
  CvS.simple_ker Q lam ξ hvec hξ0 hsimple

-- CORRUPTED input (theorem5a 3): sign condition reversed in the eigen case. This must FAIL.
open Matrix in
example {N : ℕ} {Q : Matrix (CvS.Idx N) (CvS.Idx N) ℝ} {a b : CvS.Idx N → ℝ}
    (hC : CvS.IsCvS Q a b) (lam : ℝ) (ξ : CvS.Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ)) *ᵥ ξ = 0)
    (s : ℝ) (hs : ∀ j : CvS.Idx N, (CvS.lab j : ℝ) - s ≠ 0) (hroot : (CvS.P ξ).eval s = 0) :
    ((fun i => (CvS.lab i : ℝ) * ξ i / ((CvS.lab i : ℝ) - s))
        ⬝ᵥ ((Q - lam • (1 : Matrix (CvS.Idx N) (CvS.Idx N) ℝ))
          *ᵥ (fun i => (CvS.lab i : ℝ) * ξ i / ((CvS.lab i : ℝ) - s))) < 0)
      ↔ (Polynomial.derivative (CvS.P ξ)).eval s * (CvS.P (fun k => b k * ξ k)).eval s < 0 :=
  CvS.eig_sign hC lam ξ hξ s hs hroot

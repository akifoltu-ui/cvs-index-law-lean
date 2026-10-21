/-
Copyright (c) 2026 Mehmet Akif Oltulu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mehmet Akif Oltulu
-/
import Mathlib

/-!
# Index law and resolvent lock for matrices of Connes--van Suijlekom type

Statements of Theorem 5(a) (index law) and Theorem 6 (resolvent lock) from
M. A. Oltulu, *Odd-sector, Pontryagin-space and index-law extensions of the
Connes--van Suijlekom real-zeros theorem*, Zenodo, doi:10.5281/zenodo.23459269 (2026).

The setting is finite-dimensional linear algebra over `ℝ`.

## Main declarations

* `CvS.IsCvS`: matrices of Connes--van Suijlekom type.
* `CvS.P`: the polynomial `P_ξ(s) = ∑_k ξ_k ∏_{j ≠ k} (j - s)`.
* `CvS.commutator`: CvS Lemma 5.1, `[D, Q] = β ∧ η` (also for `Q - μ`).
* `CvS.Dprime`, `CvS.det_Dprime`: Lemma 5.2, the rank-one determinant.
* `CvS.Qlam_Dprime_isSymm`: Lemma 5.3, `D'_φ` is self-adjoint for the form of `Q_λ`.
* `CvS.nondeg_even`: Lemma 5.4, `⟨β, ξ⟩ = 0` and `⟨η, ξ⟩ ≠ 0` in the even sector.
* `CvS.Qlam_norm`: Lemma 5.5, `Q_λ(w_s, w_s) = F G' - F' G`.
* `CvS.kappa_eq_sigNeg`: eigenvalue count below `μ` equals `sigNeg` of `Q - μ`.
* `CvS.eigvec_orth`, `CvS.block2_sigNeg`: Lemma 5.6 (Pontryagin balance), steps 1-2.
* `CvS.sigNeg_of_congr_diag`, `CvS.sigNeg_of_orth_family`: Lemma 5.6, step 3 (counting).
* `CvS.eigvec_orth_field`, `CvS.conj_eigvec`, `CvS.herm_norm_zero`: Lemma 5.6, step 4a.
* `CvS.herm_re`, `CvS.herm_split`, `CvS.real_pair_re_im`, `CvS.cross_orth`: Lemma 5.6, step 4b.
* `CvS.pair_orth`, `CvS.plane_split` (+ helpers): Lemma 5.6, step 4c.
* `CvS.re_im_combo`, `CvS.real_family_indep`: Lemma 5.6, step 4d (independence).
* `CvS.lock`: Theorem 6, the resolvent lock.
* `CvS.index_even`: Theorem 5(a), the index law in the even sector.
-/

open Matrix Polynomial Finset
noncomputable section

namespace CvS

/-- Index set `I = {-N, …, N}`, realised as `Fin (2N+1)`. -/
abbrev Idx (N : ℕ) := Fin (2 * N + 1)

/-- Integer label `j ∈ {-N, …, N}` of an index. -/
def lab {N : ℕ} (i : Idx N) : ℤ := (i.val : ℤ) - (N : ℤ)

/-- The index with label `0`. -/
def e0 (N : ℕ) : Idx N := ⟨N, by omega⟩

/-- CvS type (Connes--van Suijlekom, eq. (11)):
`q_ii = a_i`, `q_ij = (b_i - b_j)/(i - j)`, `a` even, `b` odd. -/
structure IsCvS {N : ℕ} (Q : Matrix (Idx N) (Idx N) ℝ) (a b : Idx N → ℝ) : Prop where
  diag   : ∀ i, Q i i = a i
  off    : ∀ i j, i ≠ j → Q i j = (b i - b j) / ((lab i : ℝ) - (lab j : ℝ))
  a_even : ∀ i, a (Fin.rev i) = a i
  b_odd  : ∀ i, b (Fin.rev i) = - b i

/-- `P_ξ(s) = ∑_k ξ_k ∏_{j ≠ k} (j - s)`. -/
def P {N : ℕ} (ξ : Idx N → ℝ) : ℝ[X] :=
  ∑ k, C (ξ k) * ∏ j ∈ univ.erase k, (C (lab j : ℝ) - X)

open Classical in
/-- `N_c`: number of pairs of non-real zeros of `P_ξ`. -/
def Nc {N : ℕ} (ξ : Idx N → ℝ) : ℕ :=
  (((P ξ).map (algebraMap ℝ ℂ)).roots.filter (fun z => z.im ≠ 0)).card / 2

open Classical in
/-- Defect `d(ξ) = #{ s ∈ ℝ \ {0} : P_ξ(s) = 0, P_ξ'(s) · P_{β⊙ξ}(s) > 0 }`. -/
def d {N : ℕ} (b ξ : Idx N → ℝ) : ℕ :=
  ((P ξ).roots.toFinset.filter (fun s =>
      s ≠ 0 ∧ 0 < (derivative (P ξ)).eval s * (P (fun k => b k * ξ k)).eval s)).card

/-- A CvS matrix is symmetric. -/
theorem isSymm_of_isCvS {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsCvS Q a b) : Q.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  by_cases h : i = j
  · subst h
    rfl
  · -- (b_j - b_i)/(j - i) = (b_i - b_j)/(i - j): numerator and denominator both flip sign.
    rw [hC.off j i (Ne.symm h), hC.off i j h, ← neg_sub (b i) (b j),
      ← neg_sub (lab i : ℝ) (lab j : ℝ), neg_div_neg_eq]

/-- Labels are distinct: `lab i = lab j → i = j`. -/
theorem lab_injective {N : ℕ} : Function.Injective (lab (N := N)) := by
  intro i j h
  apply Fin.ext
  unfold lab at h
  omega

/-- The position operator `D e_j = j e_j`. -/
def D (N : ℕ) : Matrix (Idx N) (Idx N) ℝ := Matrix.diagonal fun i => (lab i : ℝ)

/-- The wedge `u ∧ v = |u⟩⟨v| - |v⟩⟨u|`. -/
def wedge {N : ℕ} (u v : Idx N → ℝ) : Matrix (Idx N) (Idx N) ℝ :=
  Matrix.of fun i j => u i * v j - v i * u j

/-- CvS Lemma 5.1: `[D, Q] = β ∧ η`, with `β = (b_j)` and `η = (1, …, 1)`. -/
theorem commutator {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsCvS Q a b) : D N * Q - Q * D N = wedge b (fun _ => 1) := by
  ext i j
  simp only [D, wedge, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.of_apply, mul_one, one_mul]
  by_cases h : i = j
  · subst h
    ring
  · rw [hC.off i j h]
    have hlab : (lab i : ℝ) ≠ (lab j : ℝ) := by
      have := lab_injective.ne h
      exact_mod_cast this
    have hne : (lab i : ℝ) - (lab j : ℝ) ≠ 0 := sub_ne_zero.mpr hlab
    field_simp

/-- The same identity for the shifted matrix `Q - μ`. -/
theorem commutator_shift {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsCvS Q a b) (μ : ℝ) :
    D N * (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) - (Q - μ • 1) * D N
      = wedge b (fun _ => 1) := by
  rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul,
    ← commutator hC]
  abel

/-- `D'_φ = D - |Dξ⟩⟨φ| / c` with `c = ⟨φ, ξ⟩`. -/
def Dprime {N : ℕ} (φ ξ : Idx N → ℝ) : Matrix (Idx N) (Idx N) ℝ :=
  D N - (1 / ∑ k, φ k * ξ k) • Matrix.of fun i j => (lab i : ℝ) * ξ i * φ j

/-- Lemma 5.2 (a): `D'_φ ξ = 0`. -/
theorem Dprime_mulVec_self {N : ℕ} (φ ξ : Idx N → ℝ) (hc : ∑ k, φ k * ξ k ≠ 0) :
    (Dprime φ ξ).mulVec ξ = 0 := by
  ext i
  simp only [Dprime, D, Matrix.mulVec, dotProduct, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.diagonal_apply, Matrix.of_apply, smul_eq_mul,
    Pi.zero_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have key : ∑ x, 1 / (∑ k, φ k * ξ k) * ((lab i : ℝ) * ξ i * φ x) * ξ x
      = (lab i : ℝ) * ξ i * ((∑ k, φ k * ξ k) / ∑ k, φ k * ξ k) := by
    rw [div_eq_mul_one_div (∑ k, φ k * ξ k), Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [key, div_self hc, mul_one, sub_self]

-- Lemma 5.2 helper: evaluation of P_w at s.
theorem P_eval {N : ℕ} (w : Idx N → ℝ) (s : ℝ) :
    (P w).eval s = ∑ k, w k * ∏ j ∈ univ.erase k, ((lab j : ℝ) - s) := by
  simp [P, Polynomial.eval_finsetSum, Polynomial.eval_prod]

-- Lemma 5.2 helper: D'_φ - s = diag(j - s) + (rank one).  Stated for any one-point type ι.
theorem Dprime_sub_eq {N : ℕ} {ι : Type} [Unique ι] (φ ξ : Idx N → ℝ) (s : ℝ) :
    Dprime φ ξ - s • (1 : Matrix (Idx N) (Idx N) ℝ)
      = diagonal (fun i : Idx N => (lab i : ℝ) - s)
        + replicateCol ι (fun i => -(1 / ∑ k, φ k * ξ k) * ((lab i : ℝ) * ξ i))
          * replicateRow ι φ := by
  ext i j
  simp only [Dprime, D, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.diagonal_apply, Matrix.of_apply, smul_eq_mul,
    Matrix.mul_apply, replicateCol_apply, replicateRow_apply,
    Finset.univ_unique, Finset.sum_singleton]
  split_ifs <;> ring

-- Lemma 5.2 helper: ∏_{j≠k} (j - s) = (∏_j (j - s)) / (k - s).
theorem prod_erase_eq_div {N : ℕ} (s : ℝ) (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0)
    (k : Idx N) :
    ∏ j ∈ univ.erase k, ((lab j : ℝ) - s)
      = (∏ j : Idx N, ((lab j : ℝ) - s)) / ((lab k : ℝ) - s) := by
  rw [eq_div_iff (hs k)]
  exact Finset.prod_erase_mul univ (fun j : Idx N => (lab j : ℝ) - s) (mem_univ k)

-- Lemma 5.2 helper: the single entry of the 1×1 matrix in the determinant lemma.
theorem rankOne_entry {N : ℕ} {ι : Type} [Unique ι] (φ ξ : Idx N → ℝ) (s : ℝ) :
    ((1 + replicateRow ι φ * diagonal (fun i : Idx N => ((lab i : ℝ) - s)⁻¹)
        * replicateCol ι (fun i => -(1 / ∑ k, φ k * ξ k) * ((lab i : ℝ) * ξ i))
          : Matrix ι ι ℝ) default default)
      = 1 + ∑ k, φ k * ((lab k : ℝ) - s)⁻¹ * (-(1 / ∑ k, φ k * ξ k) * ((lab k : ℝ) * ξ k)) := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, Finset.sum_ite_eq']

-- Lemma 5.2 helper: the j/(j - s) = 1 + s/(j - s) rewriting of the sum.
theorem rankOne_sum {N : ℕ} (φ ξ : Idx N → ℝ) (s : ℝ) (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0)
    (hc : ∑ k, φ k * ξ k ≠ 0) :
    ∑ k, φ k * ((lab k : ℝ) - s)⁻¹ * (-(1 / ∑ k, φ k * ξ k) * ((lab k : ℝ) * ξ k))
      = -1 - (s / ∑ k, φ k * ξ k) * ∑ k, φ k * ξ k * ((lab k : ℝ) - s)⁻¹ := by
  have hk : ∀ k, φ k * ((lab k : ℝ) - s)⁻¹ * (-(1 / ∑ k, φ k * ξ k) * ((lab k : ℝ) * ξ k))
      = -(1 / ∑ k, φ k * ξ k) * (φ k * ξ k)
        - (s / ∑ k, φ k * ξ k) * (φ k * ξ k * ((lab k : ℝ) - s)⁻¹) := by
    intro k
    field_simp [hs k]
    ring
  rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, neg_mul, one_div, inv_mul_cancel₀ hc]

-- Lemma 5.2 helper: pull the full product out of the sum.
theorem prod_sum_div {N : ℕ} (φ ξ : Idx N → ℝ) (s : ℝ) :
    ∑ k, φ k * ξ k * ((∏ j : Idx N, ((lab j : ℝ) - s)) / ((lab k : ℝ) - s))
      = (∏ j : Idx N, ((lab j : ℝ) - s)) * ∑ k, φ k * ξ k * ((lab k : ℝ) - s)⁻¹ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_eq_mul_inv]
  ring

-- Lemma 5.2 helper: the determinant identity away from the labels, over any one-point type ι,
-- so that every instance on ι comes from `Unique ι` exactly as in Mathlib's lemma.
theorem det_Dprime_aux {N : ℕ} {ι : Type} [Unique ι] (φ ξ : Idx N → ℝ)
    (hc : ∑ k, φ k * ξ k ≠ 0) (s : ℝ) (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0) :
    (Dprime φ ξ - s • (1 : Matrix (Idx N) (Idx N) ℝ)).det
      = -(s / ∑ k, φ k * ξ k) * (P fun k => φ k * ξ k).eval s := by
  have hA : IsUnit (diagonal (fun i : Idx N => (lab i : ℝ) - s)).det := by
    rw [det_diagonal]
    exact (Finset.prod_ne_zero_iff.mpr fun j _ => hs j).isUnit
  have hinv : (diagonal (fun i : Idx N => (lab i : ℝ) - s))⁻¹
      = diagonal (fun i : Idx N => ((lab i : ℝ) - s)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hs i)
  rw [Dprime_sub_eq (ι := ι) φ ξ s, det_add_replicateCol_mul_replicateRow hA,
    det_diagonal, hinv, det_unique, rankOne_entry, rankOne_sum φ ξ s hs hc]
  simp only [P_eval]
  simp_rw [prod_erase_eq_div s hs]
  rw [prod_sum_div]
  ring

-- Lemma 5.2 helper: the same statement; ι no longer appears, so any one-point type will do.
theorem det_Dprime_off_labels {N : ℕ} (φ ξ : Idx N → ℝ) (hc : ∑ k, φ k * ξ k ≠ 0) (s : ℝ)
    (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0) :
    (Dprime φ ξ - s • (1 : Matrix (Idx N) (Idx N) ℝ)).det
      = -(s / ∑ k, φ k * ξ k) * (P fun k => φ k * ξ k).eval s :=
  det_Dprime_aux (ι := Unit) φ ξ hc s hs

/-- Lemma 5.2 (b): `det (D'_φ - s) = -(s / c) · P_{φ⊙ξ}(s)` for every real `s`.
Away from the labels this is the matrix determinant lemma; at the finitely many
labels it follows by continuity. -/
theorem det_Dprime {N : ℕ} (φ ξ : Idx N → ℝ) (hc : ∑ k, φ k * ξ k ≠ 0) (s : ℝ) :
    (Dprime φ ξ - s • (1 : Matrix (Idx N) (Idx N) ℝ)).det
      = -(s / ∑ k, φ k * ξ k) * (P fun k => φ k * ξ k).eval s := by
  have h1 : Continuous fun s : ℝ => (Dprime φ ξ - s • (1 : Matrix (Idx N) (Idx N) ℝ)).det :=
    (continuous_const.sub (continuous_id.smul continuous_const)).matrix_det
  have h2 : Continuous fun s : ℝ =>
      -(s / ∑ k, φ k * ξ k) * (P fun k => φ k * ξ k).eval s :=
    (continuous_id.div_const _).neg.mul (Polynomial.continuous _)
  have hset : {s : ℝ | ∀ j : Idx N, (lab j : ℝ) - s ≠ 0}
      = Set.univ \ Set.range (fun j : Idx N => (lab j : ℝ)) := by
    ext t
    simp [sub_eq_zero]
  have hdense : Dense {s : ℝ | ∀ j : Idx N, (lab j : ℝ) - s ≠ 0} := by
    rw [hset]
    exact dense_univ.sdiff_finite (Set.finite_range _)
  have heq := Continuous.ext_on hdense h1 h2 fun t ht => det_Dprime_off_labels φ ξ hc t ht
  exact congrFun heq s

/-- Lemma 5.3 (Q_λ-symmetry criterion). If `Q_λ ξ = 0` and `φ = x η + y β` with
`c = ⟨φ, ξ⟩ ≠ 0`, then `Q_λ D'_φ` is symmetric. -/
theorem Qlam_Dprime_isSymm {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsCvS Q a b) (lam : ℝ) (ξ : Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)).mulVec ξ = 0) (x y : ℝ)
    (hc : ∑ k, (x + y * b k) * ξ k ≠ 0) :
    ((Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)) * Dprime (fun k => x + y * b k) ξ).IsSymm := by
  have hcs := commutator_shift hC lam
  set A := Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ) with hA
  -- A is symmetric
  have hAsym : ∀ i j, A j i = A i j := by
    intro i j
    have hs := (isSymm_of_isCvS hC).apply i j
    by_cases h : i = j
    · subst h
      rfl
    · simp [hA, Matrix.sub_apply, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), hs]
  -- entrywise commutator: lab i * A i j - A i j * lab j = b i - b j
  have hcomm : ∀ i j, (lab i : ℝ) * A i j - A i j * (lab j : ℝ) = b i - b j := by
    intro i j
    have := congrArg (fun M => M i j) hcs
    simpa [D, wedge, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.of_apply] using this
  -- v_i := (A D ξ)_i = ⟨β, ξ⟩ - b_i ⟨η, ξ⟩
  have hv : ∀ i, ∑ k, A i k * ((lab k : ℝ) * ξ k)
      = (∑ k, b k * ξ k) - b i * ∑ k, ξ k := by
    intro i
    have h0 : ∑ k, A i k * ξ k = 0 := by
      have := congrFun hξ i
      simpa [Matrix.mulVec, dotProduct] using this
    have h1 : ∑ k, ((lab i : ℝ) * A i k - A i k * (lab k : ℝ)) * ξ k
        = ∑ k, (b i - b k) * ξ k :=
      Finset.sum_congr rfl fun k _ => by rw [hcomm i k]
    have e1 : ∑ k, ((lab i : ℝ) * A i k - A i k * (lab k : ℝ)) * ξ k
        = (lab i : ℝ) * ∑ k, A i k * ξ k - ∑ k, A i k * ((lab k : ℝ) * ξ k) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have e2 : ∑ k, (b i - b k) * ξ k = b i * ∑ k, ξ k - ∑ k, b k * ξ k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e1, e2, h0] at h1
    linarith
  -- entry formula: (A D')_{ij} = A_ij j - (1/c) φ_j v_i
  have hentry : ∀ i j, (A * Dprime (fun k => x + y * b k) ξ) i j
      = A i j * (lab j : ℝ)
        - 1 / (∑ k, (x + y * b k) * ξ k) * (x + y * b j)
          * ∑ k, A i k * ((lab k : ℝ) * ξ k) := by
    intro i j
    rw [Matrix.mul_apply]
    have hk : ∀ k, A i k * Dprime (fun k => x + y * b k) ξ k j
        = (if k = j then A i k * (lab k : ℝ) else 0)
          - 1 / (∑ k, (x + y * b k) * ξ k) * (x + y * b j) * (A i k * ((lab k : ℝ) * ξ k)) := by
      intro k
      simp only [Dprime, D, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply,
        Matrix.of_apply, smul_eq_mul]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    rw [← Finset.mul_sum]
  -- c = x ⟨η, ξ⟩ + y ⟨β, ξ⟩
  have hcexp : ∑ k, (x + y * b k) * ξ k = x * ∑ k, ξ k + y * ∑ k, b k * ξ k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hcinv : (∑ k, (x + y * b k) * ξ k)⁻¹ * (∑ k, (x + y * b k) * ξ k) = 1 :=
    inv_mul_cancel₀ hc
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [hentry j i, hentry i j, hv i, hv j, hAsym i j]
  linear_combination hcomm i j - (b i - b j) * hcinv
    + (b i - b j) * (∑ k, (x + y * b k) * ξ k)⁻¹ * hcexp

/-- Labels are odd under the reflection: `lab (rev i) = - lab i`. -/
theorem lab_rev {N : ℕ} (i : Idx N) : lab (Fin.rev i) = -lab i := by
  have := i.isLt
  simp only [lab, Fin.val_rev]
  omega

/-- The only index with label `0` is `e₀`. -/
theorem lab_eq_zero_iff {N : ℕ} (i : Idx N) : lab i = 0 ↔ i = e0 N := by
  constructor
  · intro h
    apply Fin.ext
    change (i : ℕ) = N
    simp only [lab] at h
    omega
  · rintro rfl
    simp [lab, e0]

/-- An odd vector is orthogonal to an even one: `∑ b_k ξ_k = 0`. -/
theorem sum_odd_mul_even_eq_zero {N : ℕ} (b ξ : Idx N → ℝ)
    (hb : ∀ i, b (Fin.rev i) = -b i) (hξ : ∀ i, ξ (Fin.rev i) = ξ i) :
    ∑ k, b k * ξ k = 0 := by
  have h : ∑ k, b (Fin.rev k) * ξ (Fin.rev k) = ∑ k, b k * ξ k :=
    Fintype.sum_equiv Fin.revPerm _ _ (fun k => rfl)
  simp only [hb, hξ, neg_mul, Finset.sum_neg_distrib] at h
  linarith

/-- `(Q_λ D ξ)_i = ⟨β, ξ⟩ - b_i ⟨η, ξ⟩` whenever `Q_λ ξ = 0`. -/
theorem Qlam_D_apply {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsCvS Q a b) (lam : ℝ) (ξ : Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)).mulVec ξ = 0) (i : Idx N) :
    ∑ k, (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)) i k * ((lab k : ℝ) * ξ k)
      = (∑ k, b k * ξ k) - b i * ∑ k, ξ k := by
  have hcs := commutator_shift hC lam
  set A := Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ) with hA
  have hcomm : ∀ i j, (lab i : ℝ) * A i j - A i j * (lab j : ℝ) = b i - b j := by
    intro i j
    have := congrArg (fun M => M i j) hcs
    simpa [D, wedge, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.of_apply] using this
  have h0 : ∑ k, A i k * ξ k = 0 := by
    have := congrFun hξ i
    simpa [Matrix.mulVec, dotProduct] using this
  have h1 : ∑ k, ((lab i : ℝ) * A i k - A i k * (lab k : ℝ)) * ξ k
      = ∑ k, (b i - b k) * ξ k :=
    Finset.sum_congr rfl fun k _ => by rw [hcomm i k]
  have e1 : ∑ k, ((lab i : ℝ) * A i k - A i k * (lab k : ℝ)) * ξ k
      = (lab i : ℝ) * ∑ k, A i k * ξ k - ∑ k, A i k * ((lab k : ℝ) * ξ k) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have e2 : ∑ k, (b i - b k) * ξ k = b i * ∑ k, ξ k - ∑ k, b k * ξ k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e1, e2, h0] at h1
  linarith

/-- Lemma 5.4 (non-degeneracy), even sector. If `λ` is simple with even eigenvector
`ξ ∉ ℝ e₀`, then `⟨β, ξ⟩ = 0` and `⟨η, ξ⟩ ≠ 0`. Simplicity is stated as: every vector
in the kernel of `Q - λ` is a multiple of `ξ`. -/
theorem nondeg_even {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsCvS Q a b) (lam : ℝ) (ξ : Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)).mulVec ξ = 0)
    (hsimple : ∀ w : Idx N → ℝ,
      (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)).mulVec w = 0 → ∃ t : ℝ, w = t • ξ)
    (heven : ∀ i, ξ (Fin.rev i) = ξ i) (hne : ∃ k, k ≠ e0 N ∧ ξ k ≠ 0) :
    ∑ k, b k * ξ k = 0 ∧ ∑ k, ξ k ≠ 0 := by
  have hB : ∑ k, b k * ξ k = 0 := sum_odd_mul_even_eq_zero b ξ hC.b_odd heven
  refine ⟨hB, fun hE => ?_⟩
  have hv : (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)).mulVec
      (fun k => (lab k : ℝ) * ξ k) = 0 := by
    ext i
    have := Qlam_D_apply hC lam ξ hξ i
    rw [hB, hE] at this
    simpa [Matrix.mulVec, dotProduct] using this
  obtain ⟨t, ht⟩ := hsimple _ hv
  have hpt : ∀ i, (lab i : ℝ) * ξ i = t * ξ i := fun i => by
    have := congrFun ht i
    simpa using this
  have hzero : ∀ i, (lab i : ℝ) * ξ i = 0 := by
    intro i
    have h1 := hpt i
    have h2 := hpt (Fin.rev i)
    rw [lab_rev, heven] at h2
    push_cast at h2
    linarith
  obtain ⟨k, hk, hξk⟩ := hne
  have hz : lab k ≠ 0 := fun h => hk ((lab_eq_zero_iff k).mp h)
  have hlab : (lab k : ℝ) ≠ 0 := by exact_mod_cast hz
  exact hξk ((mul_eq_zero.mp (hzero k)).resolve_left hlab)

/-- Lemma 5.5 (normalization). With `w_s = (D - s)⁻¹ ξ`, `F = ⟨η, w_s⟩`, `G = ⟨β, w_s⟩`
and the derivatives written as finite sums `F' = Σ ξ_k/(k-s)²`, `G' = Σ b_k ξ_k/(k-s)²`:
`Q_λ(w_s, w_s) = F G' - F' G`. -/
theorem Qlam_norm {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsCvS Q a b) (lam : ℝ) (ξ : Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)).mulVec ξ = 0)
    (s : ℝ) (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0) :
    ∑ i, ∑ j, ξ i / ((lab i : ℝ) - s) * (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)) i j
        * (ξ j / ((lab j : ℝ) - s))
      = (∑ k, ξ k / ((lab k : ℝ) - s)) * (∑ k, b k * ξ k / ((lab k : ℝ) - s) ^ 2)
        - (∑ k, ξ k / ((lab k : ℝ) - s) ^ 2) * (∑ k, b k * (ξ k / ((lab k : ℝ) - s))) := by
  have hcs := commutator_shift hC lam
  set A := Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ) with hA
  have hcomm : ∀ i j, (lab i : ℝ) * A i j - A i j * (lab j : ℝ) = b i - b j := by
    intro i j
    have := congrArg (fun M => M i j) hcs
    simpa [D, wedge, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.of_apply] using this
  have h0 : ∀ i, ∑ j, A i j * ξ j = 0 := fun i => by
    have := congrFun hξ i
    simpa [Matrix.mulVec, dotProduct] using this
  -- j w_j = ξ_j + s w_j
  have hlw : ∀ j, (lab j : ℝ) * (ξ j / ((lab j : ℝ) - s))
      = ξ j + s * (ξ j / ((lab j : ℝ) - s)) := by
    intro j
    have := hs j
    field_simp
    ring
  -- (Q_λ w)_i = (b_i F - G) / (i - s)
  have hAw : ∀ i, ∑ j, A i j * (ξ j / ((lab j : ℝ) - s))
      = (b i * ∑ k, ξ k / ((lab k : ℝ) - s) - ∑ k, b k * (ξ k / ((lab k : ℝ) - s)))
        / ((lab i : ℝ) - s) := by
    intro i
    rw [eq_div_iff (hs i)]
    have h1 : ∑ j, ((lab i : ℝ) * A i j - A i j * (lab j : ℝ)) * (ξ j / ((lab j : ℝ) - s))
        = ∑ j, (b i - b j) * (ξ j / ((lab j : ℝ) - s)) :=
      Finset.sum_congr rfl fun j _ => by rw [hcomm i j]
    have hterm : ∀ j, ((lab i : ℝ) * A i j - A i j * (lab j : ℝ)) * (ξ j / ((lab j : ℝ) - s))
        = ((lab i : ℝ) - s) * (A i j * (ξ j / ((lab j : ℝ) - s))) - A i j * ξ j := by
      intro j
      linear_combination (-(A i j)) * hlw j
    have e1 : ∑ j, ((lab i : ℝ) * A i j - A i j * (lab j : ℝ)) * (ξ j / ((lab j : ℝ) - s))
        = ((lab i : ℝ) - s) * ∑ j, A i j * (ξ j / ((lab j : ℝ) - s)) := by
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib, ← Finset.mul_sum,
        h0 i, sub_zero]
    have e2 : ∑ j, (b i - b j) * (ξ j / ((lab j : ℝ) - s))
        = b i * ∑ k, ξ k / ((lab k : ℝ) - s) - ∑ k, b k * (ξ k / ((lab k : ℝ) - s)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e1, e2] at h1
    linarith
  have hL : ∀ i, ∑ j, ξ i / ((lab i : ℝ) - s) * A i j * (ξ j / ((lab j : ℝ) - s))
      = ξ i / ((lab i : ℝ) - s) * ∑ j, A i j * (ξ j / ((lab j : ℝ) - s)) := by
    intro i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hT : ∀ i, ξ i / ((lab i : ℝ) - s)
        * ((b i * ∑ k, ξ k / ((lab k : ℝ) - s) - ∑ k, b k * (ξ k / ((lab k : ℝ) - s)))
          / ((lab i : ℝ) - s))
      = (∑ k, ξ k / ((lab k : ℝ) - s)) * (b i * ξ i / ((lab i : ℝ) - s) ^ 2)
        - (∑ k, b k * (ξ k / ((lab k : ℝ) - s))) * (ξ i / ((lab i : ℝ) - s) ^ 2) := by
    intro i
    have := hs i
    field_simp
  simp_rw [hL, hAw, hT]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

open QuadraticMap in
/-- Bridge to Mathlib's signature, any finite index type: the number of eigenvalues of `Q`
below `μ` equals `sigNeg` of any form `x ↦ x ⬝ᵥ (Q - μ) x` (Sylvester uniqueness). -/
theorem kappa_eq_sigNeg' {n : Type*} [Fintype n] [DecidableEq n] (Q : Matrix n n ℝ)
    (hQ : Q.IsHermitian) (μ : ℝ)
    (q : QuadraticForm ℝ (n → ℝ))
    (hq : ∀ x, q x = x ⬝ᵥ ((Q - μ • (1 : Matrix n n ℝ)) *ᵥ x)) :
    sigNeg q = (univ.filter (fun i => hQ.eigenvalues i < μ)).card := by
  set U : Matrix n n ℝ := (hQ.eigenvectorUnitary : Matrix n n ℝ) with hUdef
  set w : n → ℝ := fun i => hQ.eigenvalues i - μ with hw
  have hUU : Uᵀ * U = 1 := by
    have h := Unitary.coe_star_mul_self hQ.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using h
  have hUUt : U * Uᵀ = 1 := by
    have h := Unitary.coe_mul_star_self hQ.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using h
  have hcol : ∀ j, Q *ᵥ (fun i => U i j) = hQ.eigenvalues j • (fun i => U i j) := by
    intro j
    have h := hQ.mulVec_eigenvectorBasis j
    have hc : (fun i => U i j) = ⇑(hQ.eigenvectorBasis j) := funext fun i => rfl
    rw [hc]
    exact h
  have hQU : Q * U = U * diagonal hQ.eigenvalues := by
    ext i j
    rw [Matrix.mul_diagonal]
    have h := congrFun (hcol j) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm] using h
  have hdiag : Uᵀ * Q * U = diagonal hQ.eigenvalues := by
    rw [Matrix.mul_assoc, hQU, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hD : Uᵀ * (Q - μ • (1 : Matrix n n ℝ)) * U = diagonal w := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hdiag, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hUU]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [w]
    · simp [hij]
  have hD' : Uᵀ * ((Q - μ • (1 : Matrix n n ℝ)) * U) = diagonal w := by
    rw [← Matrix.mul_assoc, hD]
  have key : ∀ (c y : n → ℝ), (U *ᵥ c) ⬝ᵥ y = c ⬝ᵥ (Uᵀ *ᵥ y) := by
    intro c y
    rw [← vecMul_transpose, dotProduct_mulVec]
  let L : (n → ℝ) ≃ₗ[ℝ] (n → ℝ) :=
    LinearEquiv.ofLinear (Matrix.toLin' U) (Matrix.toLin' Uᵀ)
      (by rw [← Matrix.toLin'_mul, hUUt, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, hUU, Matrix.toLin'_one])
  let e : (weightedSumSquares ℝ w).IsometryEquiv q :=
    { L with
      map_app' := by
        intro c
        change q (U *ᵥ c) = weightedSumSquares ℝ w c
        rw [hq, weightedSumSquares_apply, key]
        simp only [Matrix.mulVec_mulVec]
        rw [hD']
        simp only [dotProduct, Matrix.mulVec_diagonal, smul_eq_mul]
        exact Finset.sum_congr rfl fun i _ => by ring }
  have hE : QuadraticMap.Equivalent q (weightedSumSquares ℝ w) := ⟨e.symm⟩
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares hE]
  have hset :
      {i | w i < 0} = (↑(univ.filter (fun i => hQ.eigenvalues i < μ)) : Set n) := by
    ext i
    simp [w, sub_neg]
  rw [hset, Set.ncard_coe_finset]

/-- Bridge to Mathlib's signature for CvS-sized matrices (specialisation of `kappa_eq_sigNeg'`). -/
theorem kappa_eq_sigNeg {N : ℕ} (Q : Matrix (Idx N) (Idx N) ℝ) (hQ : Q.IsHermitian) (μ : ℝ)
    (q : QuadraticForm ℝ (Idx N → ℝ))
    (hq : ∀ x, q x = x ⬝ᵥ ((Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ x)) :
    sigNeg q = (univ.filter (fun i => hQ.eigenvalues i < μ)).card :=
  kappa_eq_sigNeg' Q hQ μ q hq

/-- Lemma 5.6, step 1: eigenvectors of a `B`-self-adjoint `T` for distinct real eigenvalues
are `B`-orthogonal. -/
theorem eigvec_orth {n : Type*} [Fintype n] {B T : Matrix n n ℝ} (hB : Bᵀ = B)
    (hBT : (B * T)ᵀ = B * T) {v w : n → ℝ} {r s : ℝ}
    (hv : T *ᵥ v = r • v) (hw : T *ᵥ w = s • w) (hrs : r ≠ s) :
    v ⬝ᵥ (B *ᵥ w) = 0 := by
  have key : v ⬝ᵥ ((B * T) *ᵥ w) = (T *ᵥ v) ⬝ᵥ (B *ᵥ w) := by
    rw [← hBT, transpose_mul, hB, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm v,
      ← dotProduct_mulVec, dotProduct_comm]
  have hs : v ⬝ᵥ ((B * T) *ᵥ w) = s * (v ⬝ᵥ (B *ᵥ w)) := by
    rw [← mulVec_mulVec, hw, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hr : (T *ᵥ v) ⬝ᵥ (B *ᵥ w) = r * (v ⬝ᵥ (B *ᵥ w)) := by
    rw [hv, smul_dotProduct, smul_eq_mul]
  have h0 : (r - s) * (v ⬝ᵥ (B *ᵥ w)) = 0 := by
    rw [sub_mul]; linarith [key, hs, hr]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h) hrs
  · exact h

/-- Lemma 5.6, step 2: a symmetric 2x2 block with negative determinant has signature (1,1). -/
theorem block2_sigNeg (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.IsHermitian)
    (hdet : M.det < 0)
    (q : QuadraticForm ℝ (Fin 2 → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (M *ᵥ x)) :
    sigNeg q = 1 := by
  have hq0 : ∀ x, q x = x ⬝ᵥ ((M - (0 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ x) := by
    intro x; rw [zero_smul, sub_zero]; exact hq x
  rw [kappa_eq_sigNeg' M hM 0 q hq0]
  have hprod : hM.eigenvalues 0 * hM.eigenvalues 1 < 0 := by
    have h := hM.det_eq_prod_eigenvalues
    simp only [Fin.prod_univ_two, RCLike.ofReal_real_eq_id, id] at h
    rw [← h]; exact hdet
  rw [Finset.card_filter, Fin.sum_univ_two]
  rcases mul_neg_iff.mp hprod with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [if_neg (not_lt.mpr h0.le), if_pos h1]
  · rw [if_pos h0, if_neg (not_lt.mpr h1.le)]

open QuadraticMap in
/-- Lemma 5.6, step 3a: if `Pᵀ A P = diagonal d` with `P` invertible, then `sigNeg` of
`x ↦ x ⬝ᵥ A x` counts the negative entries of `d`. -/
theorem sigNeg_of_congr_diag {n : Type*} [Fintype n] [DecidableEq n] (A P : Matrix n n ℝ)
    (d : n → ℝ) (hP : IsUnit P.det) (hD : Pᵀ * A * P = diagonal d)
    (q : QuadraticForm ℝ (n → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (A *ᵥ x)) :
    sigNeg q = (univ.filter (fun i => d i < 0)).card := by
  have hD' : Pᵀ * (A * P) = diagonal d := by rw [← Matrix.mul_assoc, hD]
  have key : ∀ (c y : n → ℝ), (P *ᵥ c) ⬝ᵥ y = c ⬝ᵥ (Pᵀ *ᵥ y) := by
    intro c y
    rw [← vecMul_transpose, dotProduct_mulVec]
  let L : (n → ℝ) ≃ₗ[ℝ] (n → ℝ) :=
    LinearEquiv.ofLinear (Matrix.toLin' P) (Matrix.toLin' P⁻¹)
      (by rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv P hP, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul P hP, Matrix.toLin'_one])
  let e : (weightedSumSquares ℝ d).IsometryEquiv q :=
    { L with
      map_app' := by
        intro c
        change q (P *ᵥ c) = weightedSumSquares ℝ d c
        rw [hq, weightedSumSquares_apply, key]
        simp only [Matrix.mulVec_mulVec]
        rw [hD']
        simp only [dotProduct, Matrix.mulVec_diagonal, smul_eq_mul]
        exact Finset.sum_congr rfl fun i _ => by ring }
  have hE : QuadraticMap.Equivalent q (weightedSumSquares ℝ d) := ⟨e.symm⟩
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares hE]
  have hset : {i | d i < 0} = (↑(univ.filter (fun i => d i < 0)) : Set n) := by
    ext i; simp
  rw [hset, Set.ncard_coe_finset]

/-- Lemma 5.6, step 3b: `n` pairwise `B`-orthogonal vectors with nonzero norms: `sigNeg`
counts the negative norms. -/
theorem sigNeg_of_orth_family {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ)
    (v : n → n → ℝ) (horth : ∀ i j, i ≠ j → v i ⬝ᵥ (B *ᵥ v j) = 0)
    (hnz : ∀ i, v i ⬝ᵥ (B *ᵥ v i) ≠ 0)
    (q : QuadraticForm ℝ (n → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (B *ᵥ x)) :
    sigNeg q = (univ.filter (fun i => v i ⬝ᵥ (B *ᵥ v i) < 0)).card := by
  set P : Matrix n n ℝ := Matrix.of fun a i => v i a with hPdef
  set d : n → ℝ := fun i => v i ⬝ᵥ (B *ᵥ v i) with hd
  have hentry : ∀ i j, (Pᵀ * B * P) i j = v i ⬝ᵥ (B *ᵥ v j) := by
    intro i j
    simp only [P, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct,
      Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hD : Pᵀ * B * P = diagonal d := by
    ext i j
    rw [hentry]
    by_cases hij : i = j
    · subst hij; simp [d]
    · rw [horth i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : P.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hD
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, Matrix.det_diagonal] at h1
    simp only [zero_mul, mul_zero] at h1
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => hnz i) h1.symm
  exact sigNeg_of_congr_diag B P d (isUnit_iff_ne_zero.mpr hdet) hD q hq

/-- Lemma 5.6, step 4a(i): step 1 over an arbitrary field. -/
theorem eigvec_orth_field {K : Type*} [Field K] {n : Type*} [Fintype n] {B T : Matrix n n K}
    (hB : Bᵀ = B) (hBT : (B * T)ᵀ = B * T) {v w : n → K} {r s : K}
    (hv : T *ᵥ v = r • v) (hw : T *ᵥ w = s • w) (hrs : r ≠ s) :
    v ⬝ᵥ (B *ᵥ w) = 0 := by
  have key : v ⬝ᵥ ((B * T) *ᵥ w) = (T *ᵥ v) ⬝ᵥ (B *ᵥ w) := by
    rw [← hBT, transpose_mul, hB, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm v,
      ← dotProduct_mulVec, dotProduct_comm]
  have hs : v ⬝ᵥ ((B * T) *ᵥ w) = s * (v ⬝ᵥ (B *ᵥ w)) := by
    rw [← mulVec_mulVec, hw, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hr : (T *ᵥ v) ⬝ᵥ (B *ᵥ w) = r * (v ⬝ᵥ (B *ᵥ w)) := by
    rw [hv, smul_dotProduct, smul_eq_mul]
  have h0 : (r - s) * (v ⬝ᵥ (B *ᵥ w)) = 0 := by
    rw [sub_mul, sub_eq_zero, ← hr, ← key, hs]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h) hrs
  · exact h

/-- Lemma 5.6, step 4a(ii): for a real matrix, conjugating an eigenvector conjugates the
eigenvalue. -/
theorem conj_eigvec {n : Type*} [Fintype n] {T : Matrix n n ℝ} {z : n → ℂ} {ζ : ℂ}
    (hz : T.map (algebraMap ℝ ℂ) *ᵥ z = ζ • z) :
    T.map (algebraMap ℝ ℂ) *ᵥ star z = star ζ • star z := by
  ext i
  have h := congrArg star (congrFun hz i)
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
    star_sum, star_mul', Pi.star_apply] at h ⊢
  simpa [Complex.star_def, Complex.conj_ofReal, mul_comm] using h

/-- Lemma 5.6, step 4a(iii): a complex eigenvector of a `B`-self-adjoint real `T` with
non-real eigenvalue has zero hermitian `B`-norm: `z ⬝ᵥ B (conj z) = 0`. -/
theorem herm_norm_zero {n : Type*} [Fintype n] {B T : Matrix n n ℝ}
    (hB : Bᵀ = B) (hBT : (B * T)ᵀ = B * T) {z : n → ℂ} {ζ : ℂ}
    (hz : T.map (algebraMap ℝ ℂ) *ᵥ z = ζ • z) (hζ : ζ ≠ star ζ) :
    z ⬝ᵥ (B.map (algebraMap ℝ ℂ) *ᵥ star z) = 0 := by
  have hBc : (B.map (algebraMap ℝ ℂ))ᵀ = B.map (algebraMap ℝ ℂ) := by
    rw [← Matrix.transpose_map, hB]
  have hBTc : (B.map (algebraMap ℝ ℂ) * T.map (algebraMap ℝ ℂ))ᵀ
      = B.map (algebraMap ℝ ℂ) * T.map (algebraMap ℝ ℂ) := by
    rw [← Matrix.map_mul, ← Matrix.transpose_map, hBT]
  exact eigvec_orth_field hBc hBTc hz (conj_eigvec hz) hζ

/-- Lemma 5.6, step 4b: `Re (z ⬝ B conj z) = B(u,u) + B(w,w)` for `z = u + i w`. -/
theorem herm_re {n : Type*} [Fintype n] (B : Matrix n n ℝ) (z : n → ℂ) :
    (z ⬝ᵥ (B.map (algebraMap ℝ ℂ) *ᵥ star z)).re
      = (fun i => (z i).re) ⬝ᵥ (B *ᵥ fun i => (z i).re)
        + (fun i => (z i).im) ⬝ᵥ (B *ᵥ fun i => (z i).im) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum,
    Complex.re_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re, Complex.mul_im]

/-- Lemma 5.6, step 4b: for a non-real eigenvalue, `B(u,u) + B(w,w) = 0`. -/
theorem herm_split {n : Type*} [Fintype n] {B T : Matrix n n ℝ}
    (hB : Bᵀ = B) (hBT : (B * T)ᵀ = B * T) {z : n → ℂ} {ζ : ℂ}
    (hz : T.map (algebraMap ℝ ℂ) *ᵥ z = ζ • z) (hζ : ζ ≠ star ζ) :
    (fun i => (z i).re) ⬝ᵥ (B *ᵥ fun i => (z i).re)
      + (fun i => (z i).im) ⬝ᵥ (B *ᵥ fun i => (z i).im) = 0 := by
  have h := congrArg Complex.re (herm_norm_zero hB hBT hz hζ)
  rw [herm_re B z] at h
  simpa using h

/-- Lemma 5.6, step 4b: real and imaginary parts of `v ⬝ B z` for real `v`. -/
theorem real_pair_re_im {n : Type*} [Fintype n] (B : Matrix n n ℝ) (v : n → ℝ) (z : n → ℂ) :
    ((fun i => (v i : ℂ)) ⬝ᵥ (B.map (algebraMap ℝ ℂ) *ᵥ z)).re
        = v ⬝ᵥ (B *ᵥ fun i => (z i).re) ∧
      ((fun i => (v i : ℂ)) ⬝ᵥ (B.map (algebraMap ℝ ℂ) *ᵥ z)).im
        = v ⬝ᵥ (B *ᵥ fun i => (z i).im) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Complex.re_sum,
    Complex.im_sum]
  constructor
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re, Complex.mul_im]

/-- Lemma 5.6, step 4b: a real eigenvector is `B`-orthogonal to both parts of `z`. -/
theorem cross_orth {n : Type*} [Fintype n] {B T : Matrix n n ℝ}
    (hB : Bᵀ = B) (hBT : (B * T)ᵀ = B * T) {v : n → ℝ} {r : ℝ} (hv : T *ᵥ v = r • v)
    {z : n → ℂ} {ζ : ℂ} (hz : T.map (algebraMap ℝ ℂ) *ᵥ z = ζ • z) (hne : (r : ℂ) ≠ ζ) :
    v ⬝ᵥ (B *ᵥ fun i => (z i).re) = 0 ∧ v ⬝ᵥ (B *ᵥ fun i => (z i).im) = 0 := by
  have hBc : (B.map (algebraMap ℝ ℂ))ᵀ = B.map (algebraMap ℝ ℂ) := by
    rw [← Matrix.transpose_map, hB]
  have hBTc : (B.map (algebraMap ℝ ℂ) * T.map (algebraMap ℝ ℂ))ᵀ
      = B.map (algebraMap ℝ ℂ) * T.map (algebraMap ℝ ℂ) := by
    rw [← Matrix.map_mul, ← Matrix.transpose_map, hBT]
  have hvc : T.map (algebraMap ℝ ℂ) *ᵥ (fun i => (v i : ℂ)) = (r : ℂ) • (fun i => (v i : ℂ)) := by
    ext i
    have h := congrArg (fun x : ℝ => (x : ℂ)) (congrFun hv i)
    simpa [Matrix.mulVec, dotProduct, Complex.ofReal_sum] using h
  have h0 := eigvec_orth_field hBc hBTc hvc hz hne
  obtain ⟨hre, him⟩ := real_pair_re_im B v z
  rw [h0] at hre him
  exact ⟨by simpa using hre.symm, by simpa using him.symm⟩

/-- Lemma 5.6, step 4c: Re/Im of the bilinear pairing of two complex vectors, in terms of
real and imaginary parts. -/
theorem cc_re_im {n : Type*} [Fintype n] (B : Matrix n n ℝ) (z y : n → ℂ) :
    (z ⬝ᵥ (B.map (algebraMap ℝ ℂ) *ᵥ y)).re
        = (fun i => (z i).re) ⬝ᵥ (B *ᵥ fun i => (y i).re)
          - (fun i => (z i).im) ⬝ᵥ (B *ᵥ fun i => (y i).im) ∧
      (z ⬝ᵥ (B.map (algebraMap ℝ ℂ) *ᵥ y)).im
        = (fun i => (z i).re) ⬝ᵥ (B *ᵥ fun i => (y i).im)
          + (fun i => (z i).im) ⬝ᵥ (B *ᵥ fun i => (y i).re) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Complex.re_sum,
    Complex.im_sum]
  constructor
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re, Complex.mul_im]

/-- Same with the second vector conjugated. -/
theorem cc_conj_re_im {n : Type*} [Fintype n] (B : Matrix n n ℝ) (z y : n → ℂ) :
    (z ⬝ᵥ (B.map (algebraMap ℝ ℂ) *ᵥ star y)).re
        = (fun i => (z i).re) ⬝ᵥ (B *ᵥ fun i => (y i).re)
          + (fun i => (z i).im) ⬝ᵥ (B *ᵥ fun i => (y i).im) ∧
      (z ⬝ᵥ (B.map (algebraMap ℝ ℂ) *ᵥ star y)).im
        = (fun i => (z i).im) ⬝ᵥ (B *ᵥ fun i => (y i).re)
          - (fun i => (z i).re) ⬝ᵥ (B *ᵥ fun i => (y i).im) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum,
    Complex.re_sum, Complex.im_sum]
  constructor
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
    ring

/-- Lemma 5.6, step 4c(1): two complex eigenvectors from different non-real pairs: their real
and imaginary parts are pairwise `B`-orthogonal. -/
theorem pair_orth {n : Type*} [Fintype n] {B T : Matrix n n ℝ}
    (hB : Bᵀ = B) (hBT : (B * T)ᵀ = B * T) {z y : n → ℂ} {ζ ω : ℂ}
    (hz : T.map (algebraMap ℝ ℂ) *ᵥ z = ζ • z) (hy : T.map (algebraMap ℝ ℂ) *ᵥ y = ω • y)
    (h1 : ζ ≠ ω) (h2 : ζ ≠ star ω) :
    (fun i => (z i).re) ⬝ᵥ (B *ᵥ fun i => (y i).re) = 0 ∧
      (fun i => (z i).re) ⬝ᵥ (B *ᵥ fun i => (y i).im) = 0 ∧
      (fun i => (z i).im) ⬝ᵥ (B *ᵥ fun i => (y i).re) = 0 ∧
      (fun i => (z i).im) ⬝ᵥ (B *ᵥ fun i => (y i).im) = 0 := by
  have hBc : (B.map (algebraMap ℝ ℂ))ᵀ = B.map (algebraMap ℝ ℂ) := by
    rw [← Matrix.transpose_map, hB]
  have hBTc : (B.map (algebraMap ℝ ℂ) * T.map (algebraMap ℝ ℂ))ᵀ
      = B.map (algebraMap ℝ ℂ) * T.map (algebraMap ℝ ℂ) := by
    rw [← Matrix.map_mul, ← Matrix.transpose_map, hBT]
  have e1 := eigvec_orth_field hBc hBTc hz hy h1
  have e2 := eigvec_orth_field hBc hBTc hz (conj_eigvec hy) h2
  obtain ⟨r1, i1⟩ := cc_re_im B z y
  obtain ⟨r2, i2⟩ := cc_conj_re_im B z y
  rw [e1] at r1 i1
  rw [e2] at r2 i2
  simp only [Complex.zero_re, Complex.zero_im] at r1 i1 r2 i2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Lemma 5.6, step 4c: numerical core of the plane split (no square roots). -/
theorem plane_split_num (a c : ℝ) (h : a ≠ 0 ∨ c ≠ 0) :
    ∃ α β γ δ : ℝ, α * γ * a + (α * δ + β * γ) * c - β * δ * a = 0 ∧
      (α ^ 2 * a + 2 * α * β * c - β ^ 2 * a) * (γ ^ 2 * a + 2 * γ * δ * c - δ ^ 2 * a) < 0 ∧
      α * δ - β * γ ≠ 0 := by
  by_cases ha : a = 0
  · have hc : c ≠ 0 := h.resolve_left (fun h' => h' ha)
    refine ⟨1, 1, 1, -1, ?_, ?_, ?_⟩
    · rw [ha]; ring
    · rw [ha]; nlinarith [mul_self_pos.mpr hc]
    · norm_num
  · refine ⟨1, 0, -c, a, ?_, ?_, ?_⟩
    · ring
    · nlinarith [mul_pos (mul_self_pos.mpr ha) (mul_self_pos.mpr ha), mul_self_nonneg (a * c)]
    · simpa using ha

theorem bil_expand {n : Type*} [Fintype n] (B : Matrix n n ℝ) (u w : n → ℝ) (α β γ δ : ℝ) :
    (α • u + β • w) ⬝ᵥ (B *ᵥ (γ • u + δ • w))
      = α * γ * (u ⬝ᵥ (B *ᵥ u)) + α * δ * (u ⬝ᵥ (B *ᵥ w))
        + β * γ * (w ⬝ᵥ (B *ᵥ u)) + β * δ * (w ⬝ᵥ (B *ᵥ w)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem bil_symm {n : Type*} [Fintype n] {B : Matrix n n ℝ} (hB : Bᵀ = B) (x y : n → ℝ) :
    x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hB, dotProduct_comm]

/-- Lemma 5.6, step 4c(2): inside the plane of `u, w` with `B(u,u) + B(w,w) = 0` (and `B` not
identically zero there), two `B`-orthogonal combinations with norms of opposite sign. -/
theorem plane_split {n : Type*} [Fintype n] {B : Matrix n n ℝ} (hB : Bᵀ = B) (u w : n → ℝ)
    (hsum : u ⬝ᵥ (B *ᵥ u) + w ⬝ᵥ (B *ᵥ w) = 0)
    (hnd : u ⬝ᵥ (B *ᵥ u) ≠ 0 ∨ u ⬝ᵥ (B *ᵥ w) ≠ 0) :
    ∃ α β γ δ : ℝ, (α • u + β • w) ⬝ᵥ (B *ᵥ (γ • u + δ • w)) = 0 ∧
      ((α • u + β • w) ⬝ᵥ (B *ᵥ (α • u + β • w)))
        * ((γ • u + δ • w) ⬝ᵥ (B *ᵥ (γ • u + δ • w))) < 0 ∧
      α * δ - β * γ ≠ 0 := by
  obtain ⟨α, β, γ, δ, h1, h2, h3⟩ :=
    plane_split_num (u ⬝ᵥ (B *ᵥ u)) (u ⬝ᵥ (B *ᵥ w)) hnd
  have hw : w ⬝ᵥ (B *ᵥ w) = -(u ⬝ᵥ (B *ᵥ u)) := by linarith
  refine ⟨α, β, γ, δ, ?_, ?_, h3⟩
  · rw [bil_expand, bil_symm hB w u, hw]
    linear_combination h1
  · rw [bil_expand, bil_expand, bil_symm hB w u, hw]
    convert h2 using 1
    ring

/-- Lemma 5.6, step 4d: per-term identity behind the real/complex switch:
`(g₁ - i g₂) z + (g₁ + i g₂) conj z = 2 (g₁ Re z + g₂ Im z)`. -/
theorem re_im_combo (g₁ g₂ : ℝ) (z : ℂ) :
    ((g₁ : ℂ) - Complex.I * g₂) * z + ((g₁ : ℂ) + Complex.I * g₂) * star z
      = ((2 * (g₁ * z.re + g₂ * z.im) : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Lemma 5.6, step 4d: the real family `{v_i, Re z_k, Im z_k}` is linearly independent over `ℝ`
(from complex independence of eigenvectors with distinct eigenvalues). -/
theorem real_family_indep {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]
    (T : Matrix n n ℝ) (r : ι → ℝ) (v : ι → n → ℝ)
    (hv : ∀ i, T *ᵥ v i = r i • v i) (hv0 : ∀ i, v i ≠ 0)
    (ζ : κ → ℂ) (z : κ → n → ℂ)
    (hz : ∀ k, T.map (algebraMap ℝ ℂ) *ᵥ z k = ζ k • z k) (hz0 : ∀ k, z k ≠ 0)
    (hinj : Function.Injective
      (Sum.elim (fun i => (r i : ℂ)) (Sum.elim ζ (fun k => star (ζ k))))) :
    LinearIndependent ℝ
      (Sum.elim v (Sum.elim (fun k j => (z k j).re) (fun k j => (z k j).im))) := by
  have hV : ∀ a : ι ⊕ (κ ⊕ κ), Module.End.HasEigenvector (Matrix.toLin' (T.map (algebraMap ℝ ℂ)))
      (Sum.elim (fun i => (r i : ℂ)) (Sum.elim ζ (fun k => star (ζ k))) a)
      (Sum.elim (fun i j => ((v i j : ℝ) : ℂ)) (Sum.elim z (fun k => star (z k))) a) := by
    intro a
    rcases a with i | k | k
    · simp only [Sum.elim_inl]
      refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
      · rw [Matrix.toLin'_apply]
        ext j
        have h := congrArg (fun x : ℝ => (x : ℂ)) (congrFun (hv i) j)
        simpa [Matrix.mulVec, dotProduct, Complex.ofReal_sum] using h
      · intro h0
        apply hv0 i
        ext j
        have h := congrFun h0 j
        simpa using h
    · simp only [Sum.elim_inr, Sum.elim_inl]
      exact ⟨Module.End.mem_eigenspace_iff.mpr (by rw [Matrix.toLin'_apply]; exact hz k), hz0 k⟩
    · simp only [Sum.elim_inr]
      refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
      · rw [Matrix.toLin'_apply]; exact conj_eigvec (hz k)
      · intro h0
        apply hz0 k
        ext j
        have h := congrFun h0 j
        simpa using h
  have hL := Module.End.eigenvectors_linearIndependent' (Matrix.toLin' (T.map (algebraMap ℝ ℂ)))
    _ hinj _ hV
  rw [Fintype.linearIndependent_iff] at hL ⊢
  intro g hg
  set h : ι ⊕ (κ ⊕ κ) → ℂ := Sum.elim (fun i => ((2 * g (Sum.inl i) : ℝ) : ℂ))
    (Sum.elim (fun k => (g (Sum.inr (Sum.inl k)) : ℂ) - Complex.I * g (Sum.inr (Sum.inr k)))
      (fun k => (g (Sum.inr (Sum.inl k)) : ℂ) + Complex.I * g (Sum.inr (Sum.inr k)))) with hh
  have hsum : ∑ a, h a • (Sum.elim (fun i j => ((v i j : ℝ) : ℂ))
      (Sum.elim z (fun k => star (z k))) a) = 0 := by
    ext j
    have hj := congrFun hg j
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hh, Pi.star_apply] at hj ⊢
    rw [← Finset.sum_add_distrib]
    simp only [re_im_combo]
    have h_real : ∑ a, 2 * g (Sum.inl a) * v a j
        + ∑ k, 2 * (g (Sum.inr (Sum.inl k)) * (z k j).re
          + g (Sum.inr (Sum.inr k)) * (z k j).im) = 0 := by
      have e : ∀ a, 2 * g (Sum.inl a) * v a j = 2 * (g (Sum.inl a) * v a j) := fun a => by ring
      simp only [e]
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← mul_add, hj, mul_zero]
    exact_mod_cast h_real
  have h0 := hL h hsum
  intro a
  rcases a with i | k | k
  · have e := h0 (Sum.inl i)
    simp only [hh, Sum.elim_inl] at e
    have e2 : 2 * g (Sum.inl i) = 0 := by exact_mod_cast e
    linarith
  · have e := congrArg Complex.re (h0 (Sum.inr (Sum.inl k)))
    simp [hh] at e
    exact e
  · have e := congrArg Complex.im (h0 (Sum.inr (Sum.inl k)))
    simp [hh] at e
    exact e

open Classical in
/-- Theorem 6 (resolvent lock). For `μ` not an eigenvalue and `x = (Q - μ)⁻¹ e₀`:
`N_c(P_x) + d(x) + [x₀ < 0] = κ(μ)`, the number of eigenvalues of `Q` below `μ`. -/
theorem lock {N : ℕ} (Q : Matrix (Idx N) (Idx N) ℝ) (a b : Idx N → ℝ)
    (hC : IsCvS Q a b) (hQ : Q.IsHermitian) (μ : ℝ)
    (hμ : IsUnit (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)).det)
    (x : Idx N → ℝ)
    (hx : x = Matrix.mulVec (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ))⁻¹ (Pi.single (e0 N) 1))
    (hx0 : x (e0 N) ≠ 0) (hηx : ∑ k, x k ≠ 0)
    (hsep : (P x).Separable) (hout : ∀ j : Idx N, (P x).eval (lab j : ℝ) ≠ 0) :
    Nc x + d b x + (if x (e0 N) < 0 then 1 else 0)
      = (univ.filter (fun i => hQ.eigenvalues i < μ)).card := by
  sorry

open Classical in
/-- Theorem 5(a) (index law, even sector). For a simple eigenvalue `λ` with even
eigenvector `ξ ∉ ℝ e₀` whose `P_ξ` has simple zeros outside `I`:
`N_c + d(ξ) = κ(λ)`. -/
theorem index_even {N : ℕ} (Q : Matrix (Idx N) (Idx N) ℝ) (a b : Idx N → ℝ)
    (hC : IsCvS Q a b) (hQ : Q.IsHermitian) (lam : ℝ) (ξ : Idx N → ℝ)
    (hvec : Q.mulVec ξ = lam • ξ) (hne : ∃ k, k ≠ e0 N ∧ ξ k ≠ 0)
    (hsimple : Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' Q) lam) = 1)
    (heven : ∀ i, ξ (Fin.rev i) = ξ i)
    (hsep : (P ξ).Separable) (hout : ∀ j : Idx N, (P ξ).eval (lab j : ℝ) ≠ 0) :
    Nc ξ + d b ξ = (univ.filter (fun i => hQ.eigenvalues i < lam)).card := by
  sorry

end CvS

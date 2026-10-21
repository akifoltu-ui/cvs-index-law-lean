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

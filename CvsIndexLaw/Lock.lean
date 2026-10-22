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

* `CvS.IsLoewner`: Loewner-type matrices `q_ij = (b_i - b_j)/(i - j)`, no parity condition.
* `CvS.IsCvS`: matrices of Connes--van Suijlekom type (`a` even, `b` odd); `IsCvS.toLoewner`.
* `CvS.P`: the polynomial `P_ξ(s) = ∑_k ξ_k ∏_{j ≠ k} (j - s)`.
* `CvS.commutator`: CvS Lemma 5.1, `[D, Q] = β ∧ η` (also for `Q - μ`).
* `CvS.Dprime`, `CvS.det_Dprime`: Lemma 2, the rank-one determinant.
* `CvS.Qlam_Dprime_isSymm`: Lemma 3, `D'_φ` is self-adjoint for the form of `Q_λ`.
* `CvS.nondeg_even`: Lemma 4, `⟨β, ξ⟩ = 0` and `⟨η, ξ⟩ ≠ 0` in the even sector.
* `CvS.Qlam_norm`: Lemma 6, `Q_λ(w_s, w_s) = F G' - F' G`.
* `CvS.kappa_eq_sigNeg`: eigenvalue count below `μ` equals `sigNeg` of `Q - μ`.
* `CvS.eigvec_orth`, `CvS.block2_sigNeg`: Lemma 7 (Pontryagin balance), steps 1-2.
* `CvS.sigNeg_of_congr_diag`, `CvS.sigNeg_of_orth_family`: Lemma 7, step 3 (counting).
* `CvS.eigvec_orth_field`, `CvS.conj_eigvec`, `CvS.herm_norm_zero`: Lemma 7, step 4a.
* `CvS.herm_re`, `CvS.herm_split`, `CvS.real_pair_re_im`, `CvS.cross_orth`: Lemma 7, step 4b.
* `CvS.pair_orth`, `CvS.plane_split` (+ helpers): Lemma 7, step 4c.
* `CvS.re_im_combo`, `CvS.real_family_indep`: Lemma 7, step 4d (independence).
* `CvS.null_vec_zero`, `CvS.not_null_member`: Lemma 7, step 4d (no null member).
* `CvS.pontryagin_balance`: **Lemma 7 (Pontryagin balance)**.
* `CvS.Qmu_Dprime_lock_isSymm`, `CvS.F_zero_of_root`, `CvS.Dprime_eigvec_r/_c`:
  Theorem 6, T6.1-T6.2.
* `CvS.lock_norm_x`, `CvS.lock_norm`: Theorem 6, T6.3 (norms).
* `CvS.P_deriv_eval`, `CvS.lock_sign`: Theorem 6, T6.4 (sign of the norm = sign of `-P' P_β`).
* `CvS.charpoly_lock`, `CvS.natDegree_P_lock`, `CvS.card_roots_lock`: Theorem 6, T6.5 (degree).
* `CvS.eval_map_conj`, `CvS.mem_roots_conj`, `CvS.card_roots_split`: Theorem 6, T6.6 (root count).
* `CvS.F_zero_of_root_c`, `CvS.vr_ne_zero`, `CvS.vc_ne_zero`, `CvS.inj_sum_elim`, `CvS.Nc_eq`:
  Theorem 6, T6.6 (hypotheses of Lemma 7 in the lock setting).
* `CvS.lock`: **Theorem 6 (resolvent lock)**, assembled from Lemma 7 and the steps above.
* `CvS.orth_all_ker`, `CvS.sigNeg_of_orth_family_ker`, `CvS.pontryagin_balance_ker`:
  Theorem 5(a), step E1 (Lemma 7 with a one-dimensional kernel).
* `CvS.simple_ker`, `CvS.eig_sign`: Theorem 5(a), steps E2-E3.
* `CvS.index_even`: **Theorem 5(a) (index law, even sector)**, assembled like Theorem 6.
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

/-- Loewner type: `q_ii = a_i`, `q_ij = (b_i - b_j)/(i - j)`, with no parity condition.
Theorem 6 (`lock`) holds for every matrix of this type. -/
structure IsLoewner {N : ℕ} (Q : Matrix (Idx N) (Idx N) ℝ) (a b : Idx N → ℝ) : Prop where
  diag : ∀ i, Q i i = a i
  off  : ∀ i j, i ≠ j → Q i j = (b i - b j) / ((lab i : ℝ) - (lab j : ℝ))

/-- CvS type (Connes--van Suijlekom, eq. (11)):
`q_ii = a_i`, `q_ij = (b_i - b_j)/(i - j)`, `a` even, `b` odd. -/
structure IsCvS {N : ℕ} (Q : Matrix (Idx N) (Idx N) ℝ) (a b : Idx N → ℝ) : Prop where
  diag   : ∀ i, Q i i = a i
  off    : ∀ i j, i ≠ j → Q i j = (b i - b j) / ((lab i : ℝ) - (lab j : ℝ))
  a_even : ∀ i, a (Fin.rev i) = a i
  b_odd  : ∀ i, b (Fin.rev i) = - b i

/-- Every CvS matrix is of Loewner type. -/
theorem IsCvS.toLoewner {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsCvS Q a b) : IsLoewner Q a b := ⟨hC.diag, hC.off⟩

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
    (hC : IsLoewner Q a b) : Q.IsSymm := by
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
    (hC : IsLoewner Q a b) : D N * Q - Q * D N = wedge b (fun _ => 1) := by
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
    (hC : IsLoewner Q a b) (μ : ℝ) :
    D N * (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) - (Q - μ • 1) * D N
      = wedge b (fun _ => 1) := by
  rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul,
    ← commutator hC]
  abel

/-- `D'_φ = D - |Dξ⟩⟨φ| / c` with `c = ⟨φ, ξ⟩`. -/
def Dprime {N : ℕ} (φ ξ : Idx N → ℝ) : Matrix (Idx N) (Idx N) ℝ :=
  D N - (1 / ∑ k, φ k * ξ k) • Matrix.of fun i j => (lab i : ℝ) * ξ i * φ j

/-- Lemma 2 (a): `D'_φ ξ = 0`. -/
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

-- Lemma 2 helper: evaluation of P_w at s.
theorem P_eval {N : ℕ} (w : Idx N → ℝ) (s : ℝ) :
    (P w).eval s = ∑ k, w k * ∏ j ∈ univ.erase k, ((lab j : ℝ) - s) := by
  simp [P, Polynomial.eval_finsetSum, Polynomial.eval_prod]

-- Lemma 2 helper: D'_φ - s = diag(j - s) + (rank one).  Stated for any one-point type ι.
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

-- Lemma 2 helper: ∏_{j≠k} (j - s) = (∏_j (j - s)) / (k - s).
theorem prod_erase_eq_div {N : ℕ} (s : ℝ) (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0)
    (k : Idx N) :
    ∏ j ∈ univ.erase k, ((lab j : ℝ) - s)
      = (∏ j : Idx N, ((lab j : ℝ) - s)) / ((lab k : ℝ) - s) := by
  rw [eq_div_iff (hs k)]
  exact Finset.prod_erase_mul univ (fun j : Idx N => (lab j : ℝ) - s) (mem_univ k)

-- Lemma 2 helper: the single entry of the 1×1 matrix in the determinant lemma.
theorem rankOne_entry {N : ℕ} {ι : Type} [Unique ι] (φ ξ : Idx N → ℝ) (s : ℝ) :
    ((1 + replicateRow ι φ * diagonal (fun i : Idx N => ((lab i : ℝ) - s)⁻¹)
        * replicateCol ι (fun i => -(1 / ∑ k, φ k * ξ k) * ((lab i : ℝ) * ξ i))
          : Matrix ι ι ℝ) default default)
      = 1 + ∑ k, φ k * ((lab k : ℝ) - s)⁻¹ * (-(1 / ∑ k, φ k * ξ k) * ((lab k : ℝ) * ξ k)) := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, Finset.sum_ite_eq']

-- Lemma 2 helper: the j/(j - s) = 1 + s/(j - s) rewriting of the sum.
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

-- Lemma 2 helper: pull the full product out of the sum.
theorem prod_sum_div {N : ℕ} (φ ξ : Idx N → ℝ) (s : ℝ) :
    ∑ k, φ k * ξ k * ((∏ j : Idx N, ((lab j : ℝ) - s)) / ((lab k : ℝ) - s))
      = (∏ j : Idx N, ((lab j : ℝ) - s)) * ∑ k, φ k * ξ k * ((lab k : ℝ) - s)⁻¹ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_eq_mul_inv]
  ring

-- Lemma 2 helper: the determinant identity away from the labels, over any one-point type ι,
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

-- Lemma 2 helper: the same statement; ι no longer appears, so any one-point type will do.
theorem det_Dprime_off_labels {N : ℕ} (φ ξ : Idx N → ℝ) (hc : ∑ k, φ k * ξ k ≠ 0) (s : ℝ)
    (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0) :
    (Dprime φ ξ - s • (1 : Matrix (Idx N) (Idx N) ℝ)).det
      = -(s / ∑ k, φ k * ξ k) * (P fun k => φ k * ξ k).eval s :=
  det_Dprime_aux (ι := Unit) φ ξ hc s hs

/-- Lemma 2 (b): `det (D'_φ - s) = -(s / c) · P_{φ⊙ξ}(s)` for every real `s`.
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

/-- Lemma 3 (Q_λ-symmetry criterion). If `Q_λ ξ = 0` and `φ = x η + y β` with
`c = ⟨φ, ξ⟩ ≠ 0`, then `Q_λ D'_φ` is symmetric. -/
theorem Qlam_Dprime_isSymm {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsLoewner Q a b) (lam : ℝ) (ξ : Idx N → ℝ)
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
    (hC : IsLoewner Q a b) (lam : ℝ) (ξ : Idx N → ℝ)
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

/-- Lemma 4 (non-degeneracy), even sector, for `b` odd. If `λ` is simple with even eigenvector
`ξ ∉ ℝ e₀`, then `⟨β, ξ⟩ = 0` and `⟨η, ξ⟩ ≠ 0`. Simplicity is stated as: every vector
in the kernel of `Q - λ` is a multiple of `ξ`. -/
theorem nondeg_even {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsLoewner Q a b) (hb : ∀ i, b (Fin.rev i) = - b i) (lam : ℝ) (ξ : Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)).mulVec ξ = 0)
    (hsimple : ∀ w : Idx N → ℝ,
      (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)).mulVec w = 0 → ∃ t : ℝ, w = t • ξ)
    (heven : ∀ i, ξ (Fin.rev i) = ξ i) (hne : ∃ k, k ≠ e0 N ∧ ξ k ≠ 0) :
    ∑ k, b k * ξ k = 0 ∧ ∑ k, ξ k ≠ 0 := by
  have hB : ∑ k, b k * ξ k = 0 := sum_odd_mul_even_eq_zero b ξ hb heven
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

/-- Lemma 6 (normalization). With `w_s = (D - s)⁻¹ ξ`, `F = ⟨η, w_s⟩`, `G = ⟨β, w_s⟩`
and the derivatives written as finite sums `F' = Σ ξ_k/(k-s)²`, `G' = Σ b_k ξ_k/(k-s)²`:
`Q_λ(w_s, w_s) = F G' - F' G`. -/
theorem Qlam_norm {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsLoewner Q a b) (lam : ℝ) (ξ : Idx N → ℝ)
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

/-- Lemma 7, step 1: eigenvectors of a `B`-self-adjoint `T` for distinct real eigenvalues
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

/-- Lemma 7, step 2: a symmetric 2x2 block with negative determinant has signature (1,1). -/
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
/-- Lemma 7, step 3a: if `Pᵀ A P = diagonal d` with `P` invertible, then `sigNeg` of
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

/-- Lemma 7, step 3b: `n` pairwise `B`-orthogonal vectors with nonzero norms: `sigNeg`
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

/-- Lemma 7, step 4a(i): step 1 over an arbitrary field. -/
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

/-- Lemma 7, step 4a(ii): for a real matrix, conjugating an eigenvector conjugates the
eigenvalue. -/
theorem conj_eigvec {n : Type*} [Fintype n] {T : Matrix n n ℝ} {z : n → ℂ} {ζ : ℂ}
    (hz : T.map (algebraMap ℝ ℂ) *ᵥ z = ζ • z) :
    T.map (algebraMap ℝ ℂ) *ᵥ star z = star ζ • star z := by
  ext i
  have h := congrArg star (congrFun hz i)
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
    star_sum, star_mul', Pi.star_apply] at h ⊢
  simpa [Complex.star_def, Complex.conj_ofReal, mul_comm] using h

/-- Lemma 7, step 4a(iii): a complex eigenvector of a `B`-self-adjoint real `T` with
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

/-- Lemma 7, step 4b: `Re (z ⬝ B conj z) = B(u,u) + B(w,w)` for `z = u + i w`. -/
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

/-- Lemma 7, step 4b: for a non-real eigenvalue, `B(u,u) + B(w,w) = 0`. -/
theorem herm_split {n : Type*} [Fintype n] {B T : Matrix n n ℝ}
    (hB : Bᵀ = B) (hBT : (B * T)ᵀ = B * T) {z : n → ℂ} {ζ : ℂ}
    (hz : T.map (algebraMap ℝ ℂ) *ᵥ z = ζ • z) (hζ : ζ ≠ star ζ) :
    (fun i => (z i).re) ⬝ᵥ (B *ᵥ fun i => (z i).re)
      + (fun i => (z i).im) ⬝ᵥ (B *ᵥ fun i => (z i).im) = 0 := by
  have h := congrArg Complex.re (herm_norm_zero hB hBT hz hζ)
  rw [herm_re B z] at h
  simpa using h

/-- Lemma 7, step 4b: real and imaginary parts of `v ⬝ B z` for real `v`. -/
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

/-- Lemma 7, step 4b: a real eigenvector is `B`-orthogonal to both parts of `z`. -/
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

/-- Lemma 7, step 4c: Re/Im of the bilinear pairing of two complex vectors, in terms of
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

/-- Lemma 7, step 4c(1): two complex eigenvectors from different non-real pairs: their real
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

/-- Lemma 7, step 4c: numerical core of the plane split (no square roots). -/
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

/-- Lemma 7, step 4c(2): inside the plane of `u, w` with `B(u,u) + B(w,w) = 0` (and `B` not
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

/-- Lemma 7, step 4d: per-term identity behind the real/complex switch:
`(g₁ - i g₂) z + (g₁ + i g₂) conj z = 2 (g₁ Re z + g₂ Im z)`. -/
theorem re_im_combo (g₁ g₂ : ℝ) (z : ℂ) :
    ((g₁ : ℂ) - Complex.I * g₂) * z + ((g₁ : ℂ) + Complex.I * g₂) * star z
      = ((2 * (g₁ * z.re + g₂ * z.im) : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Lemma 7, step 4d: the real family `{v_i, Re z_k, Im z_k}` is linearly independent over `ℝ`
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

/-- Lemma 7, step 4d: with an independent family and `det B ≠ 0`, only `0` is `B`-orthogonal
to every member. -/
theorem null_vec_zero {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ)
    (hBdet : B.det ≠ 0) (W : n → n → ℝ) (hW : LinearIndependent ℝ W) (y : n → ℝ)
    (hy : ∀ b, y ⬝ᵥ (B *ᵥ W b) = 0) : y = 0 := by
  set P : Matrix n n ℝ := Matrix.of fun i j => W j i with hP
  have hPdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [Fintype.linearIndependent_iff] at hW
    have hsum : ∑ j, c j • W j = 0 := by
      funext i
      have h := congrFun hc i
      simpa [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using h
    exact hc0 (funext fun j => hW c hsum j)
  have hz : (Pᵀ * Bᵀ) *ᵥ y = 0 := by
    funext b
    rw [← Matrix.mulVec_mulVec]
    have h := hy b
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm] at h
    simpa [P, Matrix.mulVec, dotProduct] using h
  by_contra hy0
  have hdet : (Pᵀ * Bᵀ).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨y, hy0, hz⟩
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose] at hdet
  exact mul_ne_zero hPdet hBdet hdet

/-- Lemma 7, step 4d: no member of an independent family is `B`-orthogonal to every member
(`det B ≠ 0`). -/
theorem not_null_member {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ)
    (hBdet : B.det ≠ 0) (W : n → n → ℝ) (hW : LinearIndependent ℝ W) (a : n)
    (ha : ∀ b, W a ⬝ᵥ (B *ᵥ W b) = 0) : False :=
  hW.ne_zero a (null_vec_zero B hBdet W hW (W a) ha)

/-- **Lemma 7 (Pontryagin balance).** For `B` symmetric and invertible and `T` `B`-self-adjoint
with an explicit eigen-system — real pairs `(r_i, v_i)`, complex pairs `(ζ_k, z_k)`, all values
`r_i, ζ_k, conj ζ_k` distinct, `|ι| + 2|κ| = n` — the negative index of `B` equals the number of
real eigenvectors of negative norm plus the number of non-real pairs. -/
theorem pontryagin_balance {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]
    {B T : Matrix n n ℝ} (hB : Bᵀ = B) (hBdet : B.det ≠ 0) (hBT : (B * T)ᵀ = B * T)
    (r : ι → ℝ) (v : ι → n → ℝ) (hv : ∀ i, T *ᵥ v i = r i • v i) (hv0 : ∀ i, v i ≠ 0)
    (ζ : κ → ℂ) (z : κ → n → ℂ)
    (hz : ∀ k, T.map (algebraMap ℝ ℂ) *ᵥ z k = ζ k • z k) (hz0 : ∀ k, z k ≠ 0)
    (hinj : Function.Injective
      (Sum.elim (fun i => (r i : ℂ)) (Sum.elim ζ (fun k => star (ζ k)))))
    (hcard : Fintype.card ι + 2 * Fintype.card κ = Fintype.card n)
    (q : QuadraticForm ℝ (n → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (B *ᵥ x)) :
    sigNeg q = (univ.filter (fun i => v i ⬝ᵥ (B *ᵥ v i) < 0)).card + Fintype.card κ := by
  classical
  set U : κ → n → ℝ := fun k j => (z k j).re with hU
  set Wm : κ → n → ℝ := fun k j => (z k j).im with hWm
  -- distinct eigenvalues, from injectivity
  have hrr : ∀ i j, i ≠ j → r i ≠ r j := by
    intro i j hij hr
    apply hij
    have h := hinj (a₁ := Sum.inl i) (a₂ := Sum.inl j) (by simp [hr])
    exact Sum.inl_injective h
  have hrz : ∀ i k, (r i : ℂ) ≠ ζ k := by
    intro i k h
    have h' := hinj (a₁ := Sum.inl i) (a₂ := Sum.inr (Sum.inl k)) (by simp [h])
    exact Sum.inl_ne_inr h'
  have hzz : ∀ k l, k ≠ l → ζ k ≠ ζ l := by
    intro k l hkl h
    apply hkl
    have h' := hinj (a₁ := Sum.inr (Sum.inl k)) (a₂ := Sum.inr (Sum.inl l)) (by simp [h])
    simpa using h'
  have hzc : ∀ k l, ζ k ≠ star (ζ l) := by
    intro k l h
    have h' := hinj (a₁ := Sum.inr (Sum.inl k)) (a₂ := Sum.inr (Sum.inr l)) (by simp [h])
    simp at h'
  -- orthogonality facts for the unsplit family
  have O1 : ∀ i j, i ≠ j → v i ⬝ᵥ (B *ᵥ v j) = 0 := fun i j hij =>
    eigvec_orth hB hBT (hv i) (hv j) (hrr i j hij)
  have O2 : ∀ i k, v i ⬝ᵥ (B *ᵥ U k) = 0 ∧ v i ⬝ᵥ (B *ᵥ Wm k) = 0 := fun i k =>
    cross_orth hB hBT (hv i) (hz k) (hrz i k)
  have O3 : ∀ k l, k ≠ l → U k ⬝ᵥ (B *ᵥ U l) = 0 ∧ U k ⬝ᵥ (B *ᵥ Wm l) = 0 ∧
      Wm k ⬝ᵥ (B *ᵥ U l) = 0 ∧ Wm k ⬝ᵥ (B *ᵥ Wm l) = 0 := fun k l hkl =>
    pair_orth hB hBT (hz k) (hz l) (hzz k l hkl) (hzc k l)
  have O4 : ∀ k, U k ⬝ᵥ (B *ᵥ U k) + Wm k ⬝ᵥ (B *ᵥ Wm k) = 0 := fun k =>
    herm_split hB hBT (hz k) (hzc k k)
  have S : ∀ x y : n → ℝ, x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := bil_symm hB
  -- the unsplit real family is independent; transport it to the index type `n`
  set W : ι ⊕ (κ ⊕ κ) → n → ℝ := Sum.elim v (Sum.elim U Wm) with hWdef
  have hWi : LinearIndependent ℝ W := real_family_indep T r v hv hv0 ζ z hz hz0 hinj
  have hcardS : Fintype.card (ι ⊕ (κ ⊕ κ)) = Fintype.card n := by
    simp only [Fintype.card_sum]; omega
  let e : ι ⊕ (κ ⊕ κ) ≃ n := Fintype.equivOfCardEq hcardS
  have hW' : LinearIndependent ℝ (W ∘ e.symm) := hWi.comp e.symm e.symm.injective
  have nonull : ∀ a, (∀ b, W a ⬝ᵥ (B *ᵥ W b) = 0) → False := by
    intro a ha
    apply not_null_member B hBdet (W ∘ e.symm) hW' (e a)
    intro b
    simpa [Function.comp] using ha (e.symm b)
  -- nonzero real norms
  have Nv : ∀ i, v i ⬝ᵥ (B *ᵥ v i) ≠ 0 := by
    intro i h0
    apply nonull (Sum.inl i)
    intro b
    rcases b with j | k | k
    · by_cases hij : i = j
      · subst hij; exact h0
      · exact O1 i j hij
    · exact (O2 i k).1
    · exact (O2 i k).2
  -- each plane is not B-null
  have Nd : ∀ k, U k ⬝ᵥ (B *ᵥ U k) ≠ 0 ∨ U k ⬝ᵥ (B *ᵥ Wm k) ≠ 0 := by
    intro k
    by_contra h
    push_neg at h
    apply nonull (Sum.inr (Sum.inl k))
    intro b
    rcases b with j | l | l
    · change U k ⬝ᵥ (B *ᵥ v j) = 0
      rw [S]; exact (O2 j k).1
    · by_cases hkl : k = l
      · subst hkl; exact h.1
      · exact (O3 k l hkl).1
    · by_cases hkl : k = l
      · subst hkl; exact h.2
      · exact (O3 k l hkl).2.1
  -- split each plane
  have hps : ∀ k, ∃ α β γ δ : ℝ, (α • U k + β • Wm k) ⬝ᵥ (B *ᵥ (γ • U k + δ • Wm k)) = 0 ∧
      ((α • U k + β • Wm k) ⬝ᵥ (B *ᵥ (α • U k + β • Wm k)))
        * ((γ • U k + δ • Wm k) ⬝ᵥ (B *ᵥ (γ • U k + δ • Wm k))) < 0 ∧
      α * δ - β * γ ≠ 0 := fun k => plane_split hB (U k) (Wm k) (O4 k) (Nd k)
  choose α β γ δ hp1 hp2 _hp3 using hps
  set f1 : κ → n → ℝ := fun k => α k • U k + β k • Wm k with hf1
  set f2 : κ → n → ℝ := fun k => γ k • U k + δ k • Wm k with hf2
  set F : ι ⊕ (κ ⊕ κ) → n → ℝ := Sum.elim v (Sum.elim f1 f2) with hFdef
  have L : ∀ (a b : ℝ) (x y w : n → ℝ),
      (a • x + b • y) ⬝ᵥ (B *ᵥ w) = a * (x ⬝ᵥ (B *ᵥ w)) + b * (y ⬝ᵥ (B *ᵥ w)) := by
    intro a b x y w
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  have R : ∀ (a b : ℝ) (x y w : n → ℝ),
      w ⬝ᵥ (B *ᵥ (a • x + b • y)) = a * (w ⬝ᵥ (B *ᵥ x)) + b * (w ⬝ᵥ (B *ᵥ y)) := by
    intro a b x y w
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
  -- the split family is B-orthogonal
  have horthF : ∀ a b, a ≠ b → F a ⬝ᵥ (B *ᵥ F b) = 0 := by
    intro a b hab
    rcases a with i | k | k <;> rcases b with j | l | l
    · exact O1 i j (fun h => hab (by rw [h]))
    · change v i ⬝ᵥ (B *ᵥ (α l • U l + β l • Wm l)) = 0
      rw [R, (O2 i l).1, (O2 i l).2]; ring
    · change v i ⬝ᵥ (B *ᵥ (γ l • U l + δ l • Wm l)) = 0
      rw [R, (O2 i l).1, (O2 i l).2]; ring
    · change (α k • U k + β k • Wm k) ⬝ᵥ (B *ᵥ v j) = 0
      rw [L, S (U k), S (Wm k), (O2 j k).1, (O2 j k).2]; ring
    · have hkl : k ≠ l := fun h => hab (by rw [h])
      obtain ⟨h1, h2, h3, h4⟩ := O3 k l hkl
      change (α k • U k + β k • Wm k) ⬝ᵥ (B *ᵥ (α l • U l + β l • Wm l)) = 0
      rw [L, R, R, h1, h2, h3, h4]; ring
    · by_cases hkl : k = l
      · subst hkl; exact hp1 _
      · obtain ⟨h1, h2, h3, h4⟩ := O3 k l hkl
        change (α k • U k + β k • Wm k) ⬝ᵥ (B *ᵥ (γ l • U l + δ l • Wm l)) = 0
        rw [L, R, R, h1, h2, h3, h4]; ring
    · change (γ k • U k + δ k • Wm k) ⬝ᵥ (B *ᵥ v j) = 0
      rw [L, S (U k), S (Wm k), (O2 j k).1, (O2 j k).2]; ring
    · by_cases hkl : k = l
      · subst hkl; rw [S]; exact hp1 _
      · obtain ⟨h1, h2, h3, h4⟩ := O3 k l hkl
        change (γ k • U k + δ k • Wm k) ⬝ᵥ (B *ᵥ (α l • U l + β l • Wm l)) = 0
        rw [L, R, R, h1, h2, h3, h4]; ring
    · have hkl : k ≠ l := fun h => hab (by rw [h])
      obtain ⟨h1, h2, h3, h4⟩ := O3 k l hkl
      change (γ k • U k + δ k • Wm k) ⬝ᵥ (B *ᵥ (γ l • U l + δ l • Wm l)) = 0
      rw [L, R, R, h1, h2, h3, h4]; ring
  -- nonzero norms of the split family
  have hnzF : ∀ a, F a ⬝ᵥ (B *ᵥ F a) ≠ 0 := by
    intro a
    rcases a with i | k | k
    · exact Nv i
    · intro h0
      have h := hp2 k
      have h0' : (α k • U k + β k • Wm k) ⬝ᵥ (B *ᵥ (α k • U k + β k • Wm k)) = 0 := h0
      rw [h0', zero_mul] at h
      exact lt_irrefl 0 h
    · intro h0
      have h := hp2 k
      have h0' : (γ k • U k + δ k • Wm k) ⬝ᵥ (B *ᵥ (γ k • U k + δ k • Wm k)) = 0 := h0
      rw [h0', mul_zero] at h
      exact lt_irrefl 0 h
  -- count with step 3
  have hort' : ∀ i j : n, i ≠ j → (F ∘ e.symm) i ⬝ᵥ (B *ᵥ (F ∘ e.symm) j) = 0 :=
    fun i j hij => horthF _ _ (fun h => hij (e.symm.injective h))
  have hnz' : ∀ i : n, (F ∘ e.symm) i ⬝ᵥ (B *ᵥ (F ∘ e.symm) i) ≠ 0 := fun i => hnzF _
  rw [sigNeg_of_orth_family B (F ∘ e.symm) hort' hnz' q hq]
  have hc1 : (univ.filter fun i : n => (F ∘ e.symm) i ⬝ᵥ (B *ᵥ (F ∘ e.symm) i) < 0).card
      = (univ.filter fun a => F a ⬝ᵥ (B *ᵥ F a) < 0).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Equiv.sum_comp e.symm (fun a => if F a ⬝ᵥ (B *ᵥ F a) < 0 then 1 else 0)
  have hk : ∀ k, ((if f1 k ⬝ᵥ (B *ᵥ f1 k) < 0 then 1 else 0)
      + (if f2 k ⬝ᵥ (B *ᵥ f2 k) < 0 then 1 else 0) : ℕ) = 1 := by
    intro k
    have h := hp2 k
    have e1 : f1 k = α k • U k + β k • Wm k := rfl
    have e2 : f2 k = γ k • U k + δ k • Wm k := rfl
    rw [e1, e2]
    rcases mul_neg_iff.mp h with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [if_neg (not_lt.mpr h0.le), if_pos h1]
    · rw [if_pos h0, if_neg (not_lt.mpr h1.le)]
  rw [hc1, Finset.card_filter, Finset.card_filter]
  simp only [Fintype.sum_sum_type]
  rw [← Finset.sum_add_distrib]
  congr 1
  exact (Finset.sum_congr rfl fun k _ => hk k).trans (by simp)

/-- Theorem 6, step T6.1: in the lock setting `(Q - μ) x = e₀`, `(Q - μ) D'_η` is symmetric
(uses `lab e₀ = 0`). -/
theorem Qmu_Dprime_lock_isSymm {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsLoewner Q a b) (μ : ℝ) (x : Idx N → ℝ)
    (hx : (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ x = Pi.single (e0 N) 1)
    (hc : ∑ k, (1 : ℝ) * x k ≠ 0) :
    ((Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) * Dprime (fun _ => (1 : ℝ)) x).IsSymm := by
  have hcs := commutator_shift hC μ
  set A := Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ) with hA
  have hAsym : ∀ i j, A j i = A i j := by
    intro i j
    have hs := (isSymm_of_isCvS hC).apply i j
    by_cases h : i = j
    · subst h
      rfl
    · simp [hA, Matrix.sub_apply, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), hs]
  have hcomm : ∀ i j, (lab i : ℝ) * A i j - A i j * (lab j : ℝ) = b i - b j := by
    intro i j
    have := congrArg (fun M => M i j) hcs
    simpa [D, wedge, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.of_apply] using this
  have hv : ∀ i, ∑ k, A i k * ((lab k : ℝ) * x k)
      = (∑ k, b k * x k) - b i * ∑ k, x k := by
    intro i
    have h0 : (lab i : ℝ) * ∑ k, A i k * x k = 0 := by
      have h := congrFun hx i
      simp only [Matrix.mulVec, dotProduct] at h
      rw [h]
      by_cases hi : i = e0 N
      · subst hi
        rw [show lab (e0 N) = 0 from (lab_eq_zero_iff _).mpr rfl]
        simp
      · simp [hi]
    have h1 : ∑ k, ((lab i : ℝ) * A i k - A i k * (lab k : ℝ)) * x k
        = ∑ k, (b i - b k) * x k :=
      Finset.sum_congr rfl fun k _ => by rw [hcomm i k]
    have e1 : ∑ k, ((lab i : ℝ) * A i k - A i k * (lab k : ℝ)) * x k
        = (lab i : ℝ) * ∑ k, A i k * x k - ∑ k, A i k * ((lab k : ℝ) * x k) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have e2 : ∑ k, (b i - b k) * x k = b i * ∑ k, x k - ∑ k, b k * x k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e1, e2] at h1
    linarith
  have hentry : ∀ i j, (A * Dprime (fun _ => (1 : ℝ)) x) i j
      = A i j * (lab j : ℝ)
        - 1 / (∑ k, (1 : ℝ) * x k) * 1 * ∑ k, A i k * ((lab k : ℝ) * x k) := by
    intro i j
    rw [Matrix.mul_apply]
    have hk : ∀ k, A i k * Dprime (fun _ => (1 : ℝ)) x k j
        = (if k = j then A i k * (lab k : ℝ) else 0)
          - 1 / (∑ k, (1 : ℝ) * x k) * 1 * (A i k * ((lab k : ℝ) * x k)) := by
      intro k
      simp only [Dprime, D, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply,
        Matrix.of_apply, smul_eq_mul]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    rw [← Finset.mul_sum]
  have hcexp : ∑ k, (1 : ℝ) * x k = ∑ k, x k := by simp
  have hcinv : (∑ k, (1 : ℝ) * x k)⁻¹ * (∑ k, (1 : ℝ) * x k) = 1 := inv_mul_cancel₀ hc
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [hentry j i, hentry i j, hv i, hv j, hAsym i j]
  linear_combination hcomm i j - (b i - b j) * hcinv
    + (b i - b j) * (∑ k, (1 : ℝ) * x k)⁻¹ * hcexp

/-- Theorem 6, step T6.2 (a): `T x = 0`. -/
theorem Dprime_lock_kernel {N : ℕ} (x : Idx N → ℝ) (hc : ∑ k, (1 : ℝ) * x k ≠ 0) :
    Dprime (fun _ => (1 : ℝ)) x *ᵥ x = 0 :=
  Dprime_mulVec_self (fun _ => (1 : ℝ)) x hc

/-- Theorem 6, step T6.2 (b): a real zero `s` of `P_x` off the labels is a zero of
`F(s) = Σ x_k/(k - s)`. -/
theorem F_zero_of_root {N : ℕ} (x : Idx N → ℝ) (s : ℝ)
    (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0) (hroot : (P x).eval s = 0) :
    ∑ k, x k / ((lab k : ℝ) - s) = 0 := by
  have hΔ : ∏ j : Idx N, ((lab j : ℝ) - s) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hs j
  have hP : (P x).eval s = (∏ j : Idx N, ((lab j : ℝ) - s)) * ∑ k, x k / ((lab k : ℝ) - s) := by
    rw [P_eval, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [prod_erase_eq_div s hs k]
    ring
  rw [hP] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left hΔ

/-- Theorem 6, step T6.2 (c), real: `F(s) = 0` makes `v_s = lab·x/(lab - s)` an eigenvector
of `T` for `s`. -/
theorem Dprime_eigvec_r {N : ℕ} (x : Idx N → ℝ) (hc : ∑ k, x k ≠ 0) (s : ℝ)
    (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0) (hF : ∑ k, x k / ((lab k : ℝ) - s) = 0) :
    Dprime (fun _ => (1 : ℝ)) x *ᵥ (fun i => (lab i : ℝ) * x i / ((lab i : ℝ) - s))
      = s • (fun i => (lab i : ℝ) * x i / ((lab i : ℝ) - s)) := by
  set v : Idx N → ℝ := fun i => (lab i : ℝ) * x i / ((lab i : ℝ) - s) with hvdef
  have hT : ∀ i j, Dprime (fun _ => (1 : ℝ)) x i j
      = (if i = j then (lab i : ℝ) else 0) - (∑ k, x k)⁻¹ * ((lab i : ℝ) * x i) := by
    intro i j
    simp only [Dprime, D, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply,
      Matrix.of_apply, smul_eq_mul, one_mul, mul_one, one_div]
  have hterm : ∀ j, v j = x j + s * (x j / ((lab j : ℝ) - s)) := by
    intro j
    simp only [hvdef]
    have := hs j
    field_simp
    ring
  have hsum : ∑ j, v j = ∑ k, x k := by
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, ← Finset.mul_sum, hF,
      mul_zero, add_zero]
  ext i
  simp only [Matrix.mulVec, dotProduct, hT, Pi.smul_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, hsum]
  simp only [hvdef]
  have := hs i
  field_simp
  ring

/-- Theorem 6, step T6.2 (c), complex: the same eigenvector formula for a complex zero `s`
of `F`. -/
theorem Dprime_eigvec_c {N : ℕ} (x : Idx N → ℝ) (hc : ∑ k, x k ≠ 0) (s : ℂ)
    (hs : ∀ j : Idx N, ((lab j : ℝ) : ℂ) - s ≠ 0)
    (hF : ∑ k, (x k : ℂ) / (((lab k : ℝ) : ℂ) - s) = 0) :
    (Dprime (fun _ => (1 : ℝ)) x).map (algebraMap ℝ ℂ)
        *ᵥ (fun i => ((lab i : ℝ) : ℂ) * x i / (((lab i : ℝ) : ℂ) - s))
      = s • (fun i => ((lab i : ℝ) : ℂ) * x i / (((lab i : ℝ) : ℂ) - s)) := by
  set v : Idx N → ℂ := fun i => ((lab i : ℝ) : ℂ) * x i / (((lab i : ℝ) : ℂ) - s) with hvdef
  have hT : ∀ i j, (Dprime (fun _ => (1 : ℝ)) x).map (algebraMap ℝ ℂ) i j
      = (if i = j then ((lab i : ℝ) : ℂ) else 0)
        - ((∑ k, x k : ℝ) : ℂ)⁻¹ * (((lab i : ℝ) : ℂ) * x i) := by
    intro i j
    simp only [Matrix.map_apply, Dprime, D, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.diagonal_apply, Matrix.of_apply, smul_eq_mul, one_mul, mul_one, one_div]
    split_ifs <;> simp
  have hterm : ∀ j, v j = (x j : ℂ) + s * ((x j : ℂ) / (((lab j : ℝ) : ℂ) - s)) := by
    intro j
    simp only [hvdef]
    have := hs j
    field_simp
    ring
  have hsum : ∑ j, v j = ((∑ k, x k : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, ← Finset.mul_sum, hF,
      mul_zero, add_zero]
    simp
  have hc' : ((∑ k, x k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  ext i
  simp only [Matrix.mulVec, dotProduct, hT, Pi.smul_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, hsum]
  simp only [hvdef]
  have := hs i
  field_simp
  ring

/-- Theorem 6, step T6.3: `Q_μ(x, x) = x₀`. -/
theorem lock_norm_x {N : ℕ} (A : Matrix (Idx N) (Idx N) ℝ) (x : Idx N → ℝ)
    (hx : A *ᵥ x = Pi.single (e0 N) 1) : x ⬝ᵥ (A *ᵥ x) = x (e0 N) := by
  rw [hx]
  simp

/-- Theorem 6, step T6.3: `Q_μ(v_s, v_s) = s² (F G₂ - F₂ G)` in the lock setting
(the `e₀`-terms cancel). -/
theorem lock_norm {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsLoewner Q a b) (μ : ℝ) (x : Idx N → ℝ)
    (hx : (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ x = Pi.single (e0 N) 1)
    (s : ℝ) (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0) :
    ∑ i, ∑ j, ((lab i : ℝ) * x i / ((lab i : ℝ) - s))
        * (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) i j * ((lab j : ℝ) * x j / ((lab j : ℝ) - s))
      = s ^ 2 * ((∑ k, x k / ((lab k : ℝ) - s)) * (∑ k, b k * x k / ((lab k : ℝ) - s) ^ 2)
          - (∑ k, x k / ((lab k : ℝ) - s) ^ 2) * (∑ k, b k * (x k / ((lab k : ℝ) - s)))) := by
  have hcs := commutator_shift hC μ
  set A := Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ) with hA
  have hcomm : ∀ i j, (lab i : ℝ) * A i j - A i j * (lab j : ℝ) = b i - b j := by
    intro i j
    have := congrArg (fun M => M i j) hcs
    simpa [D, wedge, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.of_apply] using this
  have hAx : ∀ i, ∑ j, A i j * x j = if i = e0 N then 1 else 0 := by
    intro i
    have h := congrFun hx i
    simp only [Matrix.mulVec, dotProduct] at h
    rw [h, Pi.single_apply]
  have hl0 : (lab (e0 N) : ℝ) = 0 := by
    rw [show lab (e0 N) = 0 from (lab_eq_zero_iff _).mpr rfl]
    simp
  have hlw : ∀ j, (lab j : ℝ) * (x j / ((lab j : ℝ) - s))
      = x j + s * (x j / ((lab j : ℝ) - s)) := by
    intro j
    have := hs j
    field_simp
    ring
  -- (Q_μ w)_i = (b_i F - G + [i = e₀]) / (i - s)
  have hAw : ∀ i, ∑ j, A i j * (x j / ((lab j : ℝ) - s))
      = (b i * ∑ k, x k / ((lab k : ℝ) - s) - ∑ k, b k * (x k / ((lab k : ℝ) - s))
          + (if i = e0 N then 1 else 0)) / ((lab i : ℝ) - s) := by
    intro i
    rw [eq_div_iff (hs i)]
    have h1 : ∑ j, ((lab i : ℝ) * A i j - A i j * (lab j : ℝ)) * (x j / ((lab j : ℝ) - s))
        = ∑ j, (b i - b j) * (x j / ((lab j : ℝ) - s)) :=
      Finset.sum_congr rfl fun j _ => by rw [hcomm i j]
    have hterm : ∀ j, ((lab i : ℝ) * A i j - A i j * (lab j : ℝ)) * (x j / ((lab j : ℝ) - s))
        = ((lab i : ℝ) - s) * (A i j * (x j / ((lab j : ℝ) - s))) - A i j * x j := by
      intro j
      linear_combination (-(A i j)) * hlw j
    have e1 : ∑ j, ((lab i : ℝ) * A i j - A i j * (lab j : ℝ)) * (x j / ((lab j : ℝ) - s))
        = ((lab i : ℝ) - s) * ∑ j, A i j * (x j / ((lab j : ℝ) - s))
          - (if i = e0 N then 1 else 0) := by
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hAx i]
    have e2 : ∑ j, (b i - b j) * (x j / ((lab j : ℝ) - s))
        = b i * ∑ k, x k / ((lab k : ℝ) - s) - ∑ k, b k * (x k / ((lab k : ℝ) - s)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e1, e2] at h1
    linarith
  -- v = x + s w
  have hv : ∀ i, (lab i : ℝ) * x i / ((lab i : ℝ) - s) = x i + s * (x i / ((lab i : ℝ) - s)) :=
    fun i => by rw [mul_div_assoc]; exact hlw i
  -- row sums: Σ_j v_i A_ij v_j = v_i ([i = e₀] + s (Q_μ w)_i)
  have hrow : ∀ i, ∑ j, ((lab i : ℝ) * x i / ((lab i : ℝ) - s)) * A i j
        * ((lab j : ℝ) * x j / ((lab j : ℝ) - s))
      = ((lab i : ℝ) * x i / ((lab i : ℝ) - s))
        * ((if i = e0 N then 1 else 0) + s * ∑ j, A i j * (x j / ((lab j : ℝ) - s))) := by
    intro i
    have ht : ∀ j, ((lab i : ℝ) * x i / ((lab i : ℝ) - s)) * A i j
          * ((lab j : ℝ) * x j / ((lab j : ℝ) - s))
        = ((lab i : ℝ) * x i / ((lab i : ℝ) - s)) * (A i j * x j)
          + ((lab i : ℝ) * x i / ((lab i : ℝ) - s)) * s * (A i j * (x j / ((lab j : ℝ) - s))) := by
      intro j
      rw [hv j]
      ring
    rw [Finset.sum_congr rfl fun j _ => ht j, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hAx i]
    ring
  rw [Finset.sum_congr rfl fun i _ => hrow i]
  simp only [hAw]
  -- per-term split: the e₀-part vanishes because lab e₀ = 0
  have hper : ∀ i, ((lab i : ℝ) * x i / ((lab i : ℝ) - s))
        * ((if i = e0 N then 1 else 0)
          + s * ((b i * ∑ k, x k / ((lab k : ℝ) - s) - ∑ k, b k * (x k / ((lab k : ℝ) - s))
            + (if i = e0 N then 1 else 0)) / ((lab i : ℝ) - s)))
      = (b i * ∑ k, x k / ((lab k : ℝ) - s) - ∑ k, b k * (x k / ((lab k : ℝ) - s)))
          * (s * (x i / ((lab i : ℝ) - s)) + s ^ 2 * (x i / ((lab i : ℝ) - s) ^ 2))
        + (if i = e0 N then
            (lab i : ℝ) * x i / ((lab i : ℝ) - s) * (1 + s / ((lab i : ℝ) - s)) else 0) := by
    intro i
    have := hs i
    split_ifs
    · field_simp
      ring
    · field_simp
      ring
  rw [Finset.sum_congr rfl fun i _ => hper i, Finset.sum_add_distrib]
  have hite : ∑ i, (if i = e0 N then
      (lab i : ℝ) * x i / ((lab i : ℝ) - s) * (1 + s / ((lab i : ℝ) - s)) else 0) = 0 := by
    rw [Finset.sum_ite_eq']
    simp [hl0]
  rw [hite, add_zero]
  have hexp : ∀ i, (b i * ∑ k, x k / ((lab k : ℝ) - s) - ∑ k, b k * (x k / ((lab k : ℝ) - s)))
        * (s * (x i / ((lab i : ℝ) - s)) + s ^ 2 * (x i / ((lab i : ℝ) - s) ^ 2))
      = s * (∑ k, x k / ((lab k : ℝ) - s)) * (b i * (x i / ((lab i : ℝ) - s)))
        - s * (∑ k, b k * (x k / ((lab k : ℝ) - s))) * (x i / ((lab i : ℝ) - s))
        + s ^ 2 * (∑ k, x k / ((lab k : ℝ) - s)) * (b i * x i / ((lab i : ℝ) - s) ^ 2)
        - s ^ 2 * (∑ k, b k * (x k / ((lab k : ℝ) - s))) * (x i / ((lab i : ℝ) - s) ^ 2) := by
    intro i
    ring
  rw [Finset.sum_congr rfl fun i _ => hexp i]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Derivative of a finite product (Finset form of `Polynomial.derivative_prod`). -/
theorem derivative_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ[X]) :
    derivative (∏ b ∈ s, f b) = ∑ b ∈ s, (∏ a ∈ s.erase b, f a) * derivative (f b) := by
  rw [Finset.prod_eq_multiset_prod, derivative_prod, Finset.sum_eq_multiset_sum]
  congr 1

/-- `P_w(s) = Δ(s) · Σ w_k/(k - s)` off the labels. -/
theorem P_eval_div {N : ℕ} (w : Idx N → ℝ) (s : ℝ) (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0) :
    (P w).eval s = (∏ j : Idx N, ((lab j : ℝ) - s)) * ∑ k, w k / ((lab k : ℝ) - s) := by
  rw [P_eval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [prod_erase_eq_div s hs k]
  ring

/-- Theorem 6, step T6.4: `P_x'(s) = Δ(s) (F₂ - F · S)` with `S = Σ 1/(i - s)`. -/
theorem P_deriv_eval {N : ℕ} (x : Idx N → ℝ) (s : ℝ) (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0) :
    (derivative (P x)).eval s
      = (∏ j : Idx N, ((lab j : ℝ) - s))
        * (∑ k, x k / ((lab k : ℝ) - s) ^ 2
          - (∑ k, x k / ((lab k : ℝ) - s)) * ∑ i : Idx N, ((lab i : ℝ) - s)⁻¹) := by
  have hΔk : ∀ k : Idx N, ∏ j ∈ univ.erase k, ((lab j : ℝ) - s)
      = (∏ j : Idx N, ((lab j : ℝ) - s)) / ((lab k : ℝ) - s) := prod_erase_eq_div s hs
  have hΔki : ∀ k i : Idx N, i ∈ univ.erase k →
      ∏ j ∈ (univ.erase k).erase i, ((lab j : ℝ) - s)
        = (∏ j ∈ univ.erase k, ((lab j : ℝ) - s)) / ((lab i : ℝ) - s) := by
    intro k i hi
    rw [eq_div_iff (hs i), mul_comm]
    exact Finset.mul_prod_erase (univ.erase k) (fun j => (lab j : ℝ) - s) hi
  have hder : derivative (P x) = ∑ k, C (x k)
      * ∑ i ∈ univ.erase k, (∏ j ∈ (univ.erase k).erase i, (C (lab j : ℝ) - X)) * (-1) := by
    unfold P
    rw [derivative_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_finset_prod]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [derivative_sub, derivative_C, derivative_X, zero_sub]
  rw [hder, Polynomial.eval_finsetSum]
  simp only [eval_mul, eval_C, Polynomial.eval_finsetSum, eval_prod, eval_sub, eval_X, eval_neg,
    eval_one]
  have hk : ∀ k : Idx N, x k * ∑ i ∈ univ.erase k,
        (∏ j ∈ (univ.erase k).erase i, ((lab j : ℝ) - s)) * (-1)
      = (∏ j : Idx N, ((lab j : ℝ) - s))
        * (x k / ((lab k : ℝ) - s) ^ 2
          - x k / ((lab k : ℝ) - s) * ∑ i : Idx N, ((lab i : ℝ) - s)⁻¹) := by
    intro k
    have hin : ∀ i ∈ univ.erase k, (∏ j ∈ (univ.erase k).erase i, ((lab j : ℝ) - s)) * (-1)
        = (∏ j : Idx N, ((lab j : ℝ) - s)) / ((lab k : ℝ) - s) / ((lab i : ℝ) - s) * (-1) := by
      intro i hi
      rw [hΔki k i hi, hΔk k]
    rw [Finset.sum_congr rfl hin, Finset.sum_erase_eq_sub (Finset.mem_univ k)]
    have hS : ∑ i : Idx N,
          (∏ j : Idx N, ((lab j : ℝ) - s)) / ((lab k : ℝ) - s) / ((lab i : ℝ) - s) * (-1)
        = -((∏ j : Idx N, ((lab j : ℝ) - s)) / ((lab k : ℝ) - s))
          * ∑ i : Idx N, ((lab i : ℝ) - s)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hS]
    have := hs k
    field_simp
    ring
  rw [Finset.sum_congr rfl fun k _ => hk k, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.sum_mul]

/-- Theorem 6, step T6.4: at a real zero of `P_x`, `Q_μ(v_s, v_s) < 0 ↔ P_x'(s) P_{β⊙x}(s) > 0`. -/
theorem lock_sign {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsLoewner Q a b) (μ : ℝ) (x : Idx N → ℝ)
    (hx : (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ x = Pi.single (e0 N) 1)
    (s : ℝ) (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0) (hroot : (P x).eval s = 0) :
    (∑ i, ∑ j, ((lab i : ℝ) * x i / ((lab i : ℝ) - s))
        * (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) i j * ((lab j : ℝ) * x j / ((lab j : ℝ) - s))
        < 0)
      ↔ 0 < (derivative (P x)).eval s * (P (fun k => b k * x k)).eval s := by
  have hF := F_zero_of_root x s hs hroot
  have hl0 : (lab (e0 N) : ℝ) = 0 := by
    rw [show lab (e0 N) = 0 from (lab_eq_zero_iff _).mpr rfl]
    simp
  have hs0 : s ≠ 0 := by
    have h := hs (e0 N)
    rw [hl0, zero_sub, neg_ne_zero] at h
    exact h
  have hΔ : ∏ j : Idx N, ((lab j : ℝ) - s) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hs j
  have hG : ∑ k, b k * x k / ((lab k : ℝ) - s) = ∑ k, b k * (x k / ((lab k : ℝ) - s)) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [lock_norm hC μ x hx s hs, hF, P_deriv_eval x s hs, P_eval_div _ s hs, hF, hG]
  have hs2 : 0 < s * s := mul_self_pos.mpr hs0
  have hΔ2 : 0 < (∏ j : Idx N, ((lab j : ℝ) - s)) * (∏ j : Idx N, ((lab j : ℝ) - s)) :=
    mul_self_pos.mpr hΔ
  set F₂ := ∑ k, x k / ((lab k : ℝ) - s) ^ 2 with hF₂
  set G := ∑ k, b k * (x k / ((lab k : ℝ) - s)) with hGdef
  set Δ := ∏ j : Idx N, ((lab j : ℝ) - s) with hΔdef
  have e1 : s ^ 2 * (0 * ∑ k, b k * x k / ((lab k : ℝ) - s) ^ 2 - F₂ * G)
      = -((s * s) * (F₂ * G)) := by ring
  have e2 : Δ * (F₂ - 0 * ∑ i : Idx N, ((lab i : ℝ) - s)⁻¹) * (Δ * G) = (Δ * Δ) * (F₂ * G) := by
    ring
  rw [e1, e2, neg_lt_zero, mul_pos_iff_of_pos_left hs2, mul_pos_iff_of_pos_left hΔ2]

/-- Theorem 6, step T6.5: `χ(D'_η) = C(1/c) · X · P_x` with `c = Σ x_k`. -/
theorem charpoly_lock {N : ℕ} (x : Idx N → ℝ) (hc : ∑ k, x k ≠ 0) :
    (Dprime (fun _ => (1 : ℝ)) x).charpoly = C (1 / ∑ k, x k) * (X * P x) := by
  apply Polynomial.funext
  intro s
  have hd := det_Dprime (fun _ => (1 : ℝ)) x (by simpa using hc) s
  simp only [one_mul] at hd
  rw [Matrix.eval_charpoly]
  have hsc : Matrix.scalar (Idx N) s - Dprime (fun _ => (1 : ℝ)) x
      = -(Dprime (fun _ => (1 : ℝ)) x - s • (1 : Matrix (Idx N) (Idx N) ℝ)) := by
    rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hcard : Fintype.card (Idx N) = 2 * N + 1 := Fintype.card_fin _
  have hpow : ((-1 : ℝ)) ^ (2 * N + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [hsc, Matrix.det_neg, hd, hcard, hpow]
  simp only [eval_mul, eval_C, eval_X]
  ring

/-- Theorem 6, step T6.5: `deg P_x = 2N`. -/
theorem natDegree_P_lock {N : ℕ} (x : Idx N → ℝ) (hc : ∑ k, x k ≠ 0) :
    (P x).natDegree = 2 * N := by
  have h := charpoly_lock x hc
  have hdeg := Matrix.charpoly_natDegree_eq_dim (Dprime (fun _ => (1 : ℝ)) x)
  have hcard : Fintype.card (Idx N) = 2 * N + 1 := Fintype.card_fin _
  have hc' : (1 / ∑ k, x k) ≠ 0 := one_div_ne_zero hc
  have hP0 : P x ≠ 0 := by
    intro h0
    have hm := Matrix.charpoly_monic (Dprime (fun _ => (1 : ℝ)) x)
    rw [h, h0, mul_zero, mul_zero] at hm
    exact Polynomial.not_monic_zero hm
  rw [h, hcard, natDegree_C_mul hc', natDegree_X_mul hP0] at hdeg
  omega

/-- Theorem 6, step T6.5: `P_x` has `2N` complex roots counted with multiplicity. -/
theorem card_roots_lock {N : ℕ} (x : Idx N → ℝ) (hc : ∑ k, x k ≠ 0) :
    ((P x).map (algebraMap ℝ ℂ)).roots.card = 2 * N := by
  rw [IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map, natDegree_P_lock x hc]

/-- `#{a ∈ s | P a} + #{a ∈ s | ¬ P a} = #s`. -/
theorem card_filter_split {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (s.filter P).card + (s.filter (fun a => ¬ P a)).card = s.card := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : P a <;> simp [h]

/-- For a real polynomial, `p(z̄) = conj p(z)`. -/
theorem eval_map_conj (p : ℝ[X]) (z : ℂ) :
    (p.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z)
      = starRingEnd ℂ ((p.map (algebraMap ℝ ℂ)).eval z) := by
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range,
    Polynomial.eval₂_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow]
  congr 1
  simp

/-- Complex roots of a real polynomial come in conjugate pairs. -/
theorem mem_roots_conj {p : ℝ[X]} (hp : p ≠ 0) {z : ℂ}
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots) :
    starRingEnd ℂ z ∈ (p.map (algebraMap ℝ ℂ)).roots := by
  have hm : p.map (algebraMap ℝ ℂ) ≠ 0 := Polynomial.map_ne_zero hp
  rw [Polynomial.mem_roots hm, Polynomial.IsRoot.def] at hz ⊢
  rw [eval_map_conj, hz, map_zero]

/-- Theorem 6, step T6.6: for a separable real `p`,
`#real roots + 2 · #{roots with Im > 0} = deg p`. -/
theorem card_roots_split {p : ℝ[X]} (hp : p.Separable) :
    p.roots.toFinset.card
        + 2 * ((p.map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z => 0 < z.im)).card
      = p.natDegree := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  have hm : p.map (algebraMap ℝ ℂ) ≠ 0 := Polynomial.map_ne_zero hp0
  have hnd : (p.map (algebraMap ℝ ℂ)).roots.Nodup := Polynomial.nodup_roots hp.map
  set Cc := (p.map (algebraMap ℝ ℂ)).roots.toFinset with hCc
  have hcardC : Cc.card = p.natDegree := by
    rw [hCc, Multiset.toFinset_card_of_nodup hnd, IsAlgClosed.card_roots_eq_natDegree,
      natDegree_map]
  have hmemC : ∀ z, z ∈ Cc ↔ (p.map (algebraMap ℝ ℂ)).eval z = 0 := by
    intro z
    rw [hCc, Multiset.mem_toFinset, Polynomial.mem_roots hm, Polynomial.IsRoot.def]
  have hmemR : ∀ r, r ∈ p.roots.toFinset ↔ p.eval r = 0 := by
    intro r
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def]
  have key : ∀ r : ℝ, (p.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r)
      = algebraMap ℝ ℂ (p.eval r) := fun r => by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  -- real roots ↔ complex roots with Im = 0
  have hreal : (Cc.filter (fun z => z.im = 0)).card = p.roots.toFinset.card := by
    apply Finset.card_nbij' (fun z => z.re) (fun r => algebraMap ℝ ℂ r)
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
      have hz' : algebraMap ℝ ℂ z.re = z := Complex.ext (by simp) (by simp [hz.2])
      rw [hmemR]
      have h := (hmemC z).mp hz.1
      rw [← hz', key] at h
      exact (map_eq_zero (algebraMap ℝ ℂ)).mp h
    · intro r hr
      simp only [Finset.mem_coe, Finset.mem_filter]
      rw [hmemC, key, (hmemR r).mp hr, map_zero]
      exact ⟨rfl, by simp⟩
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter] at hz
      exact Complex.ext (by simp) (by simp [hz.2])
    · intro r _
      simp
  -- conjugation pairs the roots with Im < 0 and Im > 0
  have hconj : (Cc.filter (fun z => z.im < 0)).card = (Cc.filter (fun z => 0 < z.im)).card := by
    apply Finset.card_nbij' (starRingEnd ℂ) (starRingEnd ℂ)
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
      refine ⟨?_, ?_⟩
      · rw [hCc, Multiset.mem_toFinset]
        exact mem_roots_conj hp0 (Multiset.mem_toFinset.mp hz.1)
      · rw [Complex.conj_im]
        linarith [hz.2]
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
      refine ⟨?_, ?_⟩
      · rw [hCc, Multiset.mem_toFinset]
        exact mem_roots_conj hp0 (Multiset.mem_toFinset.mp hz.1)
      · rw [Complex.conj_im]
        linarith [hz.2]
    · intro z _
      exact Complex.conj_conj z
    · intro z _
      exact Complex.conj_conj z
  -- three-way split of the complex roots by the sign of Im
  have h1 := card_filter_split Cc (fun z : ℂ => z.im = 0)
  have h2 := card_filter_split (Cc.filter (fun z : ℂ => ¬ z.im = 0)) (fun z : ℂ => 0 < z.im)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have e1 : Cc.filter (fun z : ℂ => ¬ z.im = 0 ∧ 0 < z.im) = Cc.filter (fun z => 0 < z.im) :=
    Finset.filter_congr fun z _ => ⟨fun h => h.2, fun h => ⟨h.ne', h⟩⟩
  have e2 : Cc.filter (fun z : ℂ => ¬ z.im = 0 ∧ ¬ 0 < z.im) = Cc.filter (fun z => z.im < 0) :=
    Finset.filter_congr fun z _ =>
      ⟨fun h => lt_of_le_of_ne (not_lt.mp h.2) h.1, fun h => ⟨h.ne, not_lt.mpr h.le⟩⟩
  rw [e1, e2] at h2
  omega

/-- Theorem 6, step T6.6: a complex zero `ζ` of `P_x` off the labels has `F(ζ) = 0`. -/
theorem F_zero_of_root_c {N : ℕ} (x : Idx N → ℝ) (s : ℂ)
    (hs : ∀ j : Idx N, ((lab j : ℝ) : ℂ) - s ≠ 0)
    (hroot : ((P x).map (algebraMap ℝ ℂ)).eval s = 0) :
    ∑ k, (x k : ℂ) / (((lab k : ℝ) : ℂ) - s) = 0 := by
  have hΔ : ∏ j : Idx N, (((lab j : ℝ) : ℂ) - s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hs j
  have hev : ((P x).map (algebraMap ℝ ℂ)).eval s
      = ∑ k, (x k : ℂ) * ∏ j ∈ univ.erase k, (((lab j : ℝ) : ℂ) - s) := by
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    simp only [P, map_sum, map_mul, map_prod, map_sub, Polynomial.aeval_C, Polynomial.aeval_X]
    rfl
  have hP : ((P x).map (algebraMap ℝ ℂ)).eval s
      = (∏ j : Idx N, (((lab j : ℝ) : ℂ) - s)) * ∑ k, (x k : ℂ) / (((lab k : ℝ) : ℂ) - s) := by
    rw [hev, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : ∏ j ∈ univ.erase k, (((lab j : ℝ) : ℂ) - s)
        = (∏ j : Idx N, (((lab j : ℝ) : ℂ) - s)) / (((lab k : ℝ) : ℂ) - s) := by
      rw [eq_div_iff (hs k)]
      exact Finset.prod_erase_mul univ (fun j : Idx N => ((lab j : ℝ) : ℂ) - s) (mem_univ k)
    rw [hk]
    ring
  rw [hP] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left hΔ

/-- Theorem 6, step T6.6: `v_s ≠ 0` for a real `s` with `F(s) = 0` (needs `x₀ ≠ 0`). -/
theorem vr_ne_zero {N : ℕ} (x : Idx N → ℝ) (hx0 : x (e0 N) ≠ 0) (s : ℝ)
    (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0) (hF : ∑ k, x k / ((lab k : ℝ) - s) = 0) :
    (fun i => (lab i : ℝ) * x i / ((lab i : ℝ) - s)) ≠ 0 := by
  intro hv
  have hl0 : (lab (e0 N) : ℝ) = 0 := by
    rw [show lab (e0 N) = 0 from (lab_eq_zero_iff _).mpr rfl]
    simp
  have hs0 : s ≠ 0 := by
    have h := hs (e0 N)
    rw [hl0, zero_sub, neg_ne_zero] at h
    exact h
  have hxi : ∀ i, i ≠ e0 N → x i = 0 := by
    intro i hi
    have h := congrFun hv i
    simp only [Pi.zero_apply] at h
    have hli : (lab i : ℝ) ≠ 0 := by
      intro h0
      apply hi
      exact (lab_eq_zero_iff i).mp (by exact_mod_cast h0)
    rcases div_eq_zero_iff.mp h with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_left hli
    · exact absurd h1 (hs i)
  have hsum : ∑ k, x k / ((lab k : ℝ) - s) = x (e0 N) / ((lab (e0 N) : ℝ) - s) :=
    Finset.sum_eq_single (e0 N) (fun k _ hk => by rw [hxi k hk, zero_div])
      (fun h => absurd (Finset.mem_univ _) h)
  rw [hsum, hl0, zero_sub] at hF
  rcases div_eq_zero_iff.mp hF with h | h
  · exact hx0 h
  · exact hs0 (neg_eq_zero.mp h)

/-- Theorem 6, step T6.6: `v_ζ ≠ 0` for a complex `ζ` with `F(ζ) = 0`. -/
theorem vc_ne_zero {N : ℕ} (x : Idx N → ℝ) (hx0 : x (e0 N) ≠ 0) (s : ℂ)
    (hs : ∀ j : Idx N, ((lab j : ℝ) : ℂ) - s ≠ 0)
    (hF : ∑ k, (x k : ℂ) / (((lab k : ℝ) : ℂ) - s) = 0) :
    (fun i => ((lab i : ℝ) : ℂ) * x i / (((lab i : ℝ) : ℂ) - s)) ≠ 0 := by
  intro hv
  have hl0 : ((lab (e0 N) : ℝ) : ℂ) = 0 := by
    rw [show lab (e0 N) = 0 from (lab_eq_zero_iff _).mpr rfl]
    simp
  have hs0 : s ≠ 0 := by
    have h := hs (e0 N)
    rw [hl0, zero_sub, neg_ne_zero] at h
    exact h
  have hxi : ∀ i, i ≠ e0 N → x i = 0 := by
    intro i hi
    have h := congrFun hv i
    simp only [Pi.zero_apply] at h
    have hli : ((lab i : ℝ) : ℂ) ≠ 0 := by
      intro h0
      apply hi
      exact (lab_eq_zero_iff i).mp (by exact_mod_cast h0)
    rcases div_eq_zero_iff.mp h with h1 | h1
    · exact_mod_cast (mul_eq_zero.mp h1).resolve_left hli
    · exact absurd h1 (hs i)
  have hsum : ∑ k, (x k : ℂ) / (((lab k : ℝ) : ℂ) - s)
      = (x (e0 N) : ℂ) / (((lab (e0 N) : ℝ) : ℂ) - s) :=
    Finset.sum_eq_single (e0 N) (fun k _ hk => by rw [hxi k hk, Complex.ofReal_zero, zero_div])
      (fun h => absurd (Finset.mem_univ _) h)
  rw [hsum, hl0, zero_sub] at hF
  rcases div_eq_zero_iff.mp hF with h | h
  · exact hx0 (by exact_mod_cast h)
  · exact hs0 (neg_eq_zero.mp h)

/-- Theorem 6, step T6.6: real values, values with `Im > 0` and their conjugates are pairwise
distinct. -/
theorem inj_sum_elim {ι κ : Type*} (r : ι → ℝ) (hr : Function.Injective r) (ζ : κ → ℂ)
    (hζ : Function.Injective ζ) (hpos : ∀ k, 0 < (ζ k).im) :
    Function.Injective (Sum.elim (fun i => (r i : ℂ)) (Sum.elim ζ (fun k => star (ζ k)))) := by
  have hst : ∀ k, (star (ζ k)).im = -(ζ k).im := fun k => Complex.conj_im (ζ k)
  rintro (i | k | k) (j | l | l) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
  · rw [hr (Complex.ofReal_injective h)]
  · have := congrArg Complex.im h
    rw [Complex.ofReal_im] at this
    linarith [hpos l]
  · have := congrArg Complex.im h
    rw [Complex.ofReal_im, hst] at this
    linarith [hpos l]
  · have := congrArg Complex.im h
    rw [Complex.ofReal_im] at this
    linarith [hpos k]
  · rw [hζ h]
  · have := congrArg Complex.im h
    rw [hst] at this
    linarith [hpos k, hpos l]
  · have := congrArg Complex.im h
    rw [hst, Complex.ofReal_im] at this
    linarith [hpos k]
  · have := congrArg Complex.im h
    rw [hst] at this
    linarith [hpos k, hpos l]
  · rw [hζ (star_injective h)]

/-- Conjugation pairs the roots with `Im < 0` and `Im > 0`. -/
theorem card_im_neg_eq_pos {p : ℝ[X]} (hp0 : p ≠ 0) :
    ((p.map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z => z.im < 0)).card
      = ((p.map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z => 0 < z.im)).card := by
  apply Finset.card_nbij' (starRingEnd ℂ) (starRingEnd ℂ)
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
    refine ⟨?_, ?_⟩
    · rw [Multiset.mem_toFinset]
      exact mem_roots_conj hp0 (Multiset.mem_toFinset.mp hz.1)
    · rw [Complex.conj_im]
      linarith [hz.2]
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
    refine ⟨?_, ?_⟩
    · rw [Multiset.mem_toFinset]
      exact mem_roots_conj hp0 (Multiset.mem_toFinset.mp hz.1)
    · rw [Complex.conj_im]
      linarith [hz.2]
  · intro z _
    exact Complex.conj_conj z
  · intro z _
    exact Complex.conj_conj z

/-- Theorem 6, step T6.6: `N_c(P_ξ) = #{roots with Im > 0}` for separable `P_ξ`. -/
theorem Nc_eq {N : ℕ} (ξ : Idx N → ℝ) (hsep : (P ξ).Separable) :
    Nc ξ = (((P ξ).map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z => 0 < z.im)).card := by
  classical
  have hp0 : P ξ ≠ 0 := hsep.ne_zero
  have hnd : ((P ξ).map (algebraMap ℝ ℂ)).roots.Nodup := Polynomial.nodup_roots hsep.map
  have hfil : (((P ξ).map (algebraMap ℝ ℂ)).roots.filter (fun z => z.im ≠ 0)).card
      = (((P ξ).map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z => z.im ≠ 0)).card := by
    rw [← Multiset.toFinset_filter, Multiset.toFinset_card_of_nodup (hnd.filter _)]
  have h2 := card_filter_split
    (((P ξ).map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z : ℂ => z.im ≠ 0))
    (fun z : ℂ => 0 < z.im)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have e1 : ((P ξ).map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z : ℂ => z.im ≠ 0 ∧ 0 < z.im)
      = ((P ξ).map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z => 0 < z.im) :=
    Finset.filter_congr fun z _ => ⟨fun h => h.2, fun h => ⟨h.ne', h⟩⟩
  have e2 : ((P ξ).map (algebraMap ℝ ℂ)).roots.toFinset.filter
        (fun z : ℂ => z.im ≠ 0 ∧ ¬ 0 < z.im)
      = ((P ξ).map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z => z.im < 0) :=
    Finset.filter_congr fun z _ =>
      ⟨fun h => lt_of_le_of_ne (not_lt.mp h.2) h.1, fun h => ⟨h.ne, not_lt.mpr h.le⟩⟩
  rw [e1, e2] at h2
  have hc := card_im_neg_eq_pos hp0
  unfold Nc
  rw [hfil]
  omega

/-- Theorem 5(a), step E1: a vector `B`-orthogonal to a basis lies in `ker B` (`B` symmetric). -/
theorem orth_all_ker {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ) (hB : Bᵀ = B)
    (W : n → n → ℝ) (hW : LinearIndependent ℝ W) (y : n → ℝ)
    (hy : ∀ b, y ⬝ᵥ (B *ᵥ W b) = 0) : B *ᵥ y = 0 := by
  set P : Matrix n n ℝ := Matrix.of fun i j => W j i with hP
  have hPdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [Fintype.linearIndependent_iff] at hW
    have hsum : ∑ j, c j • W j = 0 := by
      funext i
      have h := congrFun hc i
      simpa [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using h
    exact hc0 (funext fun j => hW c hsum j)
  have hz : (Pᵀ * Bᵀ) *ᵥ y = 0 := by
    funext b
    rw [← Matrix.mulVec_mulVec]
    have h := hy b
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm] at h
    simpa [P, Matrix.mulVec, dotProduct] using h
  have hPt : IsUnit (Pᵀ).det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hPdet
  have hBy : Bᵀ *ᵥ y = 0 := by
    have e : Bᵀ = (Pᵀ)⁻¹ * (Pᵀ * Bᵀ) := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPt, Matrix.one_mul]
    rw [e, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  rwa [hB] at hBy

/-- Theorem 5(a), step E1: a `B`-orthogonal family whose norms are nonzero except at one
nonzero member is a basis, and `sigNeg` counts its negative norms. -/
theorem sigNeg_of_orth_family_ker {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ)
    (v : n → n → ℝ) (horth : ∀ i j, i ≠ j → v i ⬝ᵥ (B *ᵥ v j) = 0) (i₀ : n)
    (hnz : ∀ i, i ≠ i₀ → v i ⬝ᵥ (B *ᵥ v i) ≠ 0) (hv0 : v i₀ ≠ 0)
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
  have hlin : ∀ (c : n → ℝ) (w : n → ℝ), (∑ j, c j • v j) ⬝ᵥ w = ∑ j, c j * (v j ⬝ᵥ w) := by
    intro c w
    simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hsum : ∑ j, c j • v j = 0 := by
      funext i
      have h := congrFun hc i
      simpa [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using h
    have hpair : ∀ b, b ≠ i₀ → c b = 0 := by
      intro b hb
      have h1 : (∑ j, c j • v j) ⬝ᵥ (B *ᵥ v b) = c b * (v b ⬝ᵥ (B *ᵥ v b)) := by
        rw [hlin]
        exact Finset.sum_eq_single b (fun j _ hj => by rw [horth j b hj, mul_zero])
          (fun h => absurd (Finset.mem_univ b) h)
      rw [hsum, zero_dotProduct] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right (hnz b hb)
    have hc00 : c i₀ = 0 := by
      have h2 : ∑ j, c j • v j = c i₀ • v i₀ :=
        Finset.sum_eq_single i₀ (fun j _ hj => by rw [hpair j hj, zero_smul])
          (fun h => absurd (Finset.mem_univ i₀) h)
      rw [hsum] at h2
      exact (smul_eq_zero.mp h2.symm).resolve_right hv0
    apply hc0
    funext b
    by_cases hb : b = i₀
    · subst hb
      exact hc00
    · exact hpair b hb
  exact sigNeg_of_congr_diag B P d (isUnit_iff_ne_zero.mpr hdet) hD q hq

/-- Theorem 5(a), step E1: **Lemma 7 for a singular form** whose kernel is spanned by one
member `v i₀` of the real family (replaces `det B ≠ 0`). -/
theorem pontryagin_balance_ker {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]
    {B T : Matrix n n ℝ} (hB : Bᵀ = B) (hBT : (B * T)ᵀ = B * T)
    (r : ι → ℝ) (v : ι → n → ℝ) (hv : ∀ i, T *ᵥ v i = r i • v i) (hv0 : ∀ i, v i ≠ 0)
    (i₀ : ι) (hker : ∀ y, B *ᵥ y = 0 → ∃ t : ℝ, y = t • v i₀)
    (ζ : κ → ℂ) (z : κ → n → ℂ)
    (hz : ∀ k, T.map (algebraMap ℝ ℂ) *ᵥ z k = ζ k • z k) (hz0 : ∀ k, z k ≠ 0)
    (hinj : Function.Injective
      (Sum.elim (fun i => (r i : ℂ)) (Sum.elim ζ (fun k => star (ζ k)))))
    (hcard : Fintype.card ι + 2 * Fintype.card κ = Fintype.card n)
    (q : QuadraticForm ℝ (n → ℝ)) (hq : ∀ x, q x = x ⬝ᵥ (B *ᵥ x)) :
    sigNeg q = (univ.filter (fun i => v i ⬝ᵥ (B *ᵥ v i) < 0)).card + Fintype.card κ := by
  classical
  set U : κ → n → ℝ := fun k j => (z k j).re with hU
  set Wm : κ → n → ℝ := fun k j => (z k j).im with hWm
  -- distinct eigenvalues, from injectivity
  have hrr : ∀ i j, i ≠ j → r i ≠ r j := by
    intro i j hij hr
    apply hij
    have h := hinj (a₁ := Sum.inl i) (a₂ := Sum.inl j) (by simp [hr])
    exact Sum.inl_injective h
  have hrz : ∀ i k, (r i : ℂ) ≠ ζ k := by
    intro i k h
    have h' := hinj (a₁ := Sum.inl i) (a₂ := Sum.inr (Sum.inl k)) (by simp [h])
    exact Sum.inl_ne_inr h'
  have hzz : ∀ k l, k ≠ l → ζ k ≠ ζ l := by
    intro k l hkl h
    apply hkl
    have h' := hinj (a₁ := Sum.inr (Sum.inl k)) (a₂ := Sum.inr (Sum.inl l)) (by simp [h])
    simpa using h'
  have hzc : ∀ k l, ζ k ≠ star (ζ l) := by
    intro k l h
    have h' := hinj (a₁ := Sum.inr (Sum.inl k)) (a₂ := Sum.inr (Sum.inr l)) (by simp [h])
    simp at h'
  -- orthogonality facts for the unsplit family
  have O1 : ∀ i j, i ≠ j → v i ⬝ᵥ (B *ᵥ v j) = 0 := fun i j hij =>
    eigvec_orth hB hBT (hv i) (hv j) (hrr i j hij)
  have O2 : ∀ i k, v i ⬝ᵥ (B *ᵥ U k) = 0 ∧ v i ⬝ᵥ (B *ᵥ Wm k) = 0 := fun i k =>
    cross_orth hB hBT (hv i) (hz k) (hrz i k)
  have O3 : ∀ k l, k ≠ l → U k ⬝ᵥ (B *ᵥ U l) = 0 ∧ U k ⬝ᵥ (B *ᵥ Wm l) = 0 ∧
      Wm k ⬝ᵥ (B *ᵥ U l) = 0 ∧ Wm k ⬝ᵥ (B *ᵥ Wm l) = 0 := fun k l hkl =>
    pair_orth hB hBT (hz k) (hz l) (hzz k l hkl) (hzc k l)
  have O4 : ∀ k, U k ⬝ᵥ (B *ᵥ U k) + Wm k ⬝ᵥ (B *ᵥ Wm k) = 0 := fun k =>
    herm_split hB hBT (hz k) (hzc k k)
  have S : ∀ x y : n → ℝ, x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := bil_symm hB
  -- the unsplit real family is independent; transport it to the index type `n`
  set W : ι ⊕ (κ ⊕ κ) → n → ℝ := Sum.elim v (Sum.elim U Wm) with hWdef
  have hWi : LinearIndependent ℝ W := real_family_indep T r v hv hv0 ζ z hz hz0 hinj
  have hcardS : Fintype.card (ι ⊕ (κ ⊕ κ)) = Fintype.card n := by
    simp only [Fintype.card_sum]; omega
  let e : ι ⊕ (κ ⊕ κ) ≃ n := Fintype.equivOfCardEq hcardS
  have hW' : LinearIndependent ℝ (W ∘ e.symm) := hWi.comp e.symm e.symm.injective
  have nonull : ∀ a, a ≠ Sum.inl i₀ → (∀ b, W a ⬝ᵥ (B *ᵥ W b) = 0) → False := by
    intro a ha0 ha
    have hBy : B *ᵥ W a = 0 :=
      orth_all_ker B hB (W ∘ e.symm) hW' (W a) (fun b => by
        simpa [Function.comp] using ha (e.symm b))
    obtain ⟨t, ht⟩ := hker (W a) hBy
    have hsum : ∑ c, ((if c = a then (1 : ℝ) else 0) - (if c = Sum.inl i₀ then t else 0)) • W c
        = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [ht]
      exact sub_self _
    have h := (Fintype.linearIndependent_iff.mp hWi) _ hsum a
    simp [ha0] at h
  -- nonzero real norms
  have Nv : ∀ i, i ≠ i₀ → v i ⬝ᵥ (B *ᵥ v i) ≠ 0 := by
    intro i hi h0
    apply nonull (Sum.inl i) (fun h => hi (Sum.inl_injective h))
    intro b
    rcases b with j | k | k
    · by_cases hij : i = j
      · subst hij; exact h0
      · exact O1 i j hij
    · exact (O2 i k).1
    · exact (O2 i k).2
  -- each plane is not B-null
  have Nd : ∀ k, U k ⬝ᵥ (B *ᵥ U k) ≠ 0 ∨ U k ⬝ᵥ (B *ᵥ Wm k) ≠ 0 := by
    intro k
    by_contra h
    push_neg at h
    apply nonull (Sum.inr (Sum.inl k)) Sum.inr_ne_inl
    intro b
    rcases b with j | l | l
    · change U k ⬝ᵥ (B *ᵥ v j) = 0
      rw [S]; exact (O2 j k).1
    · by_cases hkl : k = l
      · subst hkl; exact h.1
      · exact (O3 k l hkl).1
    · by_cases hkl : k = l
      · subst hkl; exact h.2
      · exact (O3 k l hkl).2.1
  -- split each plane
  have hps : ∀ k, ∃ α β γ δ : ℝ, (α • U k + β • Wm k) ⬝ᵥ (B *ᵥ (γ • U k + δ • Wm k)) = 0 ∧
      ((α • U k + β • Wm k) ⬝ᵥ (B *ᵥ (α • U k + β • Wm k)))
        * ((γ • U k + δ • Wm k) ⬝ᵥ (B *ᵥ (γ • U k + δ • Wm k))) < 0 ∧
      α * δ - β * γ ≠ 0 := fun k => plane_split hB (U k) (Wm k) (O4 k) (Nd k)
  choose α β γ δ hp1 hp2 _hp3 using hps
  set f1 : κ → n → ℝ := fun k => α k • U k + β k • Wm k with hf1
  set f2 : κ → n → ℝ := fun k => γ k • U k + δ k • Wm k with hf2
  set F : ι ⊕ (κ ⊕ κ) → n → ℝ := Sum.elim v (Sum.elim f1 f2) with hFdef
  have L : ∀ (a b : ℝ) (x y w : n → ℝ),
      (a • x + b • y) ⬝ᵥ (B *ᵥ w) = a * (x ⬝ᵥ (B *ᵥ w)) + b * (y ⬝ᵥ (B *ᵥ w)) := by
    intro a b x y w
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  have R : ∀ (a b : ℝ) (x y w : n → ℝ),
      w ⬝ᵥ (B *ᵥ (a • x + b • y)) = a * (w ⬝ᵥ (B *ᵥ x)) + b * (w ⬝ᵥ (B *ᵥ y)) := by
    intro a b x y w
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
  -- the split family is B-orthogonal
  have horthF : ∀ a b, a ≠ b → F a ⬝ᵥ (B *ᵥ F b) = 0 := by
    intro a b hab
    rcases a with i | k | k <;> rcases b with j | l | l
    · exact O1 i j (fun h => hab (by rw [h]))
    · change v i ⬝ᵥ (B *ᵥ (α l • U l + β l • Wm l)) = 0
      rw [R, (O2 i l).1, (O2 i l).2]; ring
    · change v i ⬝ᵥ (B *ᵥ (γ l • U l + δ l • Wm l)) = 0
      rw [R, (O2 i l).1, (O2 i l).2]; ring
    · change (α k • U k + β k • Wm k) ⬝ᵥ (B *ᵥ v j) = 0
      rw [L, S (U k), S (Wm k), (O2 j k).1, (O2 j k).2]; ring
    · have hkl : k ≠ l := fun h => hab (by rw [h])
      obtain ⟨h1, h2, h3, h4⟩ := O3 k l hkl
      change (α k • U k + β k • Wm k) ⬝ᵥ (B *ᵥ (α l • U l + β l • Wm l)) = 0
      rw [L, R, R, h1, h2, h3, h4]; ring
    · by_cases hkl : k = l
      · subst hkl; exact hp1 _
      · obtain ⟨h1, h2, h3, h4⟩ := O3 k l hkl
        change (α k • U k + β k • Wm k) ⬝ᵥ (B *ᵥ (γ l • U l + δ l • Wm l)) = 0
        rw [L, R, R, h1, h2, h3, h4]; ring
    · change (γ k • U k + δ k • Wm k) ⬝ᵥ (B *ᵥ v j) = 0
      rw [L, S (U k), S (Wm k), (O2 j k).1, (O2 j k).2]; ring
    · by_cases hkl : k = l
      · subst hkl; rw [S]; exact hp1 _
      · obtain ⟨h1, h2, h3, h4⟩ := O3 k l hkl
        change (γ k • U k + δ k • Wm k) ⬝ᵥ (B *ᵥ (α l • U l + β l • Wm l)) = 0
        rw [L, R, R, h1, h2, h3, h4]; ring
    · have hkl : k ≠ l := fun h => hab (by rw [h])
      obtain ⟨h1, h2, h3, h4⟩ := O3 k l hkl
      change (γ k • U k + δ k • Wm k) ⬝ᵥ (B *ᵥ (γ l • U l + δ l • Wm l)) = 0
      rw [L, R, R, h1, h2, h3, h4]; ring
  -- nonzero norms of the split family
  have hnzF : ∀ a, a ≠ Sum.inl i₀ → F a ⬝ᵥ (B *ᵥ F a) ≠ 0 := by
    intro a ha0
    rcases a with i | k | k
    · exact Nv i (fun h => ha0 (by rw [h]))
    · intro h0
      have h := hp2 k
      have h0' : (α k • U k + β k • Wm k) ⬝ᵥ (B *ᵥ (α k • U k + β k • Wm k)) = 0 := h0
      rw [h0', zero_mul] at h
      exact lt_irrefl 0 h
    · intro h0
      have h := hp2 k
      have h0' : (γ k • U k + δ k • Wm k) ⬝ᵥ (B *ᵥ (γ k • U k + δ k • Wm k)) = 0 := h0
      rw [h0', mul_zero] at h
      exact lt_irrefl 0 h
  -- count with step 3
  have hort' : ∀ i j : n, i ≠ j → (F ∘ e.symm) i ⬝ᵥ (B *ᵥ (F ∘ e.symm) j) = 0 :=
    fun i j hij => horthF _ _ (fun h => hij (e.symm.injective h))
  have hnz' : ∀ i : n, i ≠ e (Sum.inl i₀) → (F ∘ e.symm) i ⬝ᵥ (B *ᵥ (F ∘ e.symm) i) ≠ 0 :=
    fun i hi => hnzF _ (fun h => hi (by rw [← h, e.apply_symm_apply]))
  have hF0 : (F ∘ e.symm) (e (Sum.inl i₀)) ≠ 0 := by
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact hv0 i₀
  rw [sigNeg_of_orth_family_ker B (F ∘ e.symm) hort' (e (Sum.inl i₀)) hnz' hF0 q hq]
  have hc1 : (univ.filter fun i : n => (F ∘ e.symm) i ⬝ᵥ (B *ᵥ (F ∘ e.symm) i) < 0).card
      = (univ.filter fun a => F a ⬝ᵥ (B *ᵥ F a) < 0).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Equiv.sum_comp e.symm (fun a => if F a ⬝ᵥ (B *ᵥ F a) < 0 then 1 else 0)
  have hk : ∀ k, ((if f1 k ⬝ᵥ (B *ᵥ f1 k) < 0 then 1 else 0)
      + (if f2 k ⬝ᵥ (B *ᵥ f2 k) < 0 then 1 else 0) : ℕ) = 1 := by
    intro k
    have h := hp2 k
    have e1 : f1 k = α k • U k + β k • Wm k := rfl
    have e2 : f2 k = γ k • U k + δ k • Wm k := rfl
    rw [e1, e2]
    rcases mul_neg_iff.mp h with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [if_neg (not_lt.mpr h0.le), if_pos h1]
    · rw [if_pos h0, if_neg (not_lt.mpr h1.le)]
  rw [hc1, Finset.card_filter, Finset.card_filter]
  simp only [Fintype.sum_sum_type]
  rw [← Finset.sum_add_distrib]
  congr 1
  exact (Finset.sum_congr rfl fun k _ => hk k).trans (by simp)

/-- Every real square matrix `A` defines a quadratic form `q(w) = wᵀ A w`. -/
theorem exists_qform {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    ∃ q : QuadraticForm ℝ (n → ℝ), ∀ w, q w = w ⬝ᵥ (A *ᵥ w) :=
  ⟨LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' ℝ A), fun w => by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']⟩

open Classical in
/-- Theorem 6 (resolvent lock), for every Loewner matrix (no parity condition).
For `μ` not an eigenvalue and `x = (Q - μ)⁻¹ e₀`:
`N_c(P_x) + d(x) + [x₀ < 0] = κ(μ)`, the number of eigenvalues of `Q` below `μ`. -/
theorem lock {N : ℕ} (Q : Matrix (Idx N) (Idx N) ℝ) (a b : Idx N → ℝ)
    (hC : IsLoewner Q a b) (hQ : Q.IsHermitian) (μ : ℝ)
    (hμ : IsUnit (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)).det)
    (x : Idx N → ℝ)
    (hx : x = Matrix.mulVec (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ))⁻¹ (Pi.single (e0 N) 1))
    (hx0 : x (e0 N) ≠ 0) (hηx : ∑ k, x k ≠ 0)
    (hsep : (P x).Separable) (hout : ∀ j : Idx N, (P x).eval (lab j : ℝ) ≠ 0) :
    Nc x + d b x + (if x (e0 N) < 0 then 1 else 0)
      = (univ.filter (fun i => hQ.eigenvalues i < μ)).card := by
  -- the resolvent vector solves (Q - μ) x = e₀
  have hAx : (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ x = Pi.single (e0 N) 1 := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hμ, Matrix.one_mulVec]
  have hc1 : ∑ k, (1 : ℝ) * x k ≠ 0 := by simpa using hηx
  have hB : (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ))ᵀ = Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ) := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
      (isSymm_of_isCvS hC).eq]
  have hBdet : (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)).det ≠ 0 := hμ.ne_zero
  have hBT := (Qmu_Dprime_lock_isSymm hC μ x hAx hc1).eq
  -- roots of P_x
  have hp0 : P x ≠ 0 := hsep.ne_zero
  have hm : (P x).map (algebraMap ℝ ℂ) ≠ 0 := Polynomial.map_ne_zero hp0
  have hl0 : (lab (e0 N) : ℝ) = 0 := by
    rw [show lab (e0 N) = 0 from (lab_eq_zero_iff _).mpr rfl]
    simp
  have hsplit := card_roots_split hsep
  have hdeg := natDegree_P_lock x hηx
  have hNc := Nc_eq x hsep
  set R := (P x).roots.toFinset with hR
  set K := ((P x).map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z => 0 < z.im) with hK
  have hrootR : ∀ s ∈ R, (P x).eval s = 0 := fun s hs => by
    rw [hR, Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def] at hs
    exact hs
  have hslR : ∀ s ∈ R, ∀ j : Idx N, (lab j : ℝ) - s ≠ 0 := by
    intro s hs j h
    apply hout j
    rw [sub_eq_zero.mp h]
    exact hrootR s hs
  have h0R : (0 : ℝ) ∉ R := by
    intro h
    apply hout (e0 N)
    rw [hl0]
    exact hrootR 0 h
  have hrootK : ∀ w ∈ K, ((P x).map (algebraMap ℝ ℂ)).eval w = 0 := fun w hw => by
    rw [hK, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hm,
      Polynomial.IsRoot.def] at hw
    exact hw.1
  have hposK : ∀ w ∈ K, 0 < w.im := fun w hw => by
    rw [hK, Finset.mem_filter] at hw
    exact hw.2
  have hslK : ∀ w ∈ K, ∀ j : Idx N, ((lab j : ℝ) : ℂ) - w ≠ 0 := by
    intro w hw j h
    have him := congrArg Complex.im h
    rw [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at him
    linarith [hposK w hw]
  -- the eigen-family of T = D'_η
  set T := Dprime (fun _ => (1 : ℝ)) x with hT
  let r : Option R → ℝ := fun i => i.elim 0 (fun s => (s : ℝ))
  let v : Option R → Idx N → ℝ :=
    fun i => i.elim x (fun s => fun j => (lab j : ℝ) * x j / ((lab j : ℝ) - (s : ℝ)))
  let ζ : K → ℂ := fun k => (k : ℂ)
  let z : K → Idx N → ℂ :=
    fun k => fun j => ((lab j : ℝ) : ℂ) * x j / (((lab j : ℝ) : ℂ) - (k : ℂ))
  have hv : ∀ i, T *ᵥ v i = r i • v i := by
    rintro (_ | ⟨s, hs⟩)
    · show T *ᵥ x = (0 : ℝ) • x
      rw [zero_smul]
      exact Dprime_lock_kernel x hc1
    · exact Dprime_eigvec_r x hηx s (hslR s hs) (F_zero_of_root x s (hslR s hs) (hrootR s hs))
  have hv0 : ∀ i, v i ≠ 0 := by
    rintro (_ | ⟨s, hs⟩)
    · intro h
      exact hx0 (congrFun h (e0 N))
    · exact vr_ne_zero x hx0 s (hslR s hs) (F_zero_of_root x s (hslR s hs) (hrootR s hs))
  have hz : ∀ k, T.map (algebraMap ℝ ℂ) *ᵥ z k = ζ k • z k := by
    rintro ⟨w, hw⟩
    exact Dprime_eigvec_c x hηx w (hslK w hw) (F_zero_of_root_c x w (hslK w hw) (hrootK w hw))
  have hz0 : ∀ k, z k ≠ 0 := by
    rintro ⟨w, hw⟩
    exact vc_ne_zero x hx0 w (hslK w hw) (F_zero_of_root_c x w (hslK w hw) (hrootK w hw))
  have hr : Function.Injective r := by
    rintro (_ | ⟨s, hs⟩) (_ | ⟨t, ht⟩) h
    · rfl
    · have h' : (0 : ℝ) = t := h
      exact (h0R (by rw [h']; exact ht)).elim
    · have h' : s = (0 : ℝ) := h
      exact (h0R (by rw [← h']; exact hs)).elim
    · have h' : s = t := h
      subst h'
      rfl
  have hinj := inj_sum_elim r hr ζ Subtype.val_injective (fun k => hposK k k.2)
  have hcard : Fintype.card (Option R) + 2 * Fintype.card K = Fintype.card (Idx N) := by
    rw [Fintype.card_option, Fintype.card_coe, Fintype.card_coe, Fintype.card_fin]
    omega
  obtain ⟨q, hq⟩ := exists_qform (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ))
  have hpb := pontryagin_balance hB hBdet hBT r v hv hv0 ζ z hz hz0 hinj hcard q hq
  have hk := kappa_eq_sigNeg Q hQ μ q hq
  -- negative norms: x ↔ x₀ < 0, and v_s ↔ the defect condition
  have hdot : ∀ w : Idx N → ℝ, w ⬝ᵥ ((Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ w)
      = ∑ i, ∑ j, w i * (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) i j * w j := by
    intro w
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hcount : (univ.filter (fun i =>
        v i ⬝ᵥ ((Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ v i) < 0)).card
      = (if x (e0 N) < 0 then 1 else 0) + d b x := by
    rw [Finset.card_filter, Fintype.sum_option]
    congr 1
    · show (if x ⬝ᵥ ((Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ x) < 0 then 1 else 0) = _
      rw [lock_norm_x _ x hAx]
    · unfold d
      rw [Finset.card_filter, ← Finset.sum_coe_sort R]
      refine Finset.sum_congr rfl fun s _ => ?_
      obtain ⟨s, hs⟩ := s
      have hiff : (v (some ⟨s, hs⟩) ⬝ᵥ ((Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ))
            *ᵥ v (some ⟨s, hs⟩)) < 0)
          ↔ (s ≠ 0 ∧ 0 < (derivative (P x)).eval s * (P (fun k => b k * x k)).eval s) := by
        rw [show v (some ⟨s, hs⟩) = (fun j => (lab j : ℝ) * x j / ((lab j : ℝ) - s)) from rfl,
          hdot, lock_sign hC μ x hAx s (hslR s hs) (hrootR s hs)]
        exact ⟨fun h => ⟨fun h0 => h0R (by rw [← h0]; exact hs), h⟩, fun h => h.2⟩
      by_cases h1 : v (some ⟨s, hs⟩) ⬝ᵥ ((Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ))
          *ᵥ v (some ⟨s, hs⟩)) < 0
      · rw [if_pos h1, if_pos (hiff.mp h1)]
      · rw [if_neg h1, if_neg (fun h => h1 (hiff.mpr h))]
  rw [← hk, hpb, hcount, Fintype.card_coe, ← hNc]
  omega

/-- `(c • 1) *ᵥ u = c • u`. -/
theorem smul_one_mulVec {N : ℕ} (c : ℝ) (u : Idx N → ℝ) :
    (c • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ u = c • u := by
  first
    | (rw [Matrix.smul_one_eq_diagonal]; ext i; simp [Matrix.mulVec_diagonal])
    | (ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])

/-- Theorem 5(a), step E2: a simple eigenvalue has kernel `ℝ ξ`. -/
theorem simple_ker {N : ℕ} (Q : Matrix (Idx N) (Idx N) ℝ) (lam : ℝ) (ξ : Idx N → ℝ)
    (hvec : Q.mulVec ξ = lam • ξ) (hξ0 : ξ ≠ 0)
    (hsimple : Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' Q) lam) = 1) :
    ∀ w : Idx N → ℝ, (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ w = 0 →
      ∃ t : ℝ, w = t • ξ := by
  have hmem : ∀ u : Idx N → ℝ, (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ u = 0 →
      u ∈ Module.End.eigenspace (Matrix.toLin' Q) lam := by
    intro u hu
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    rw [Matrix.sub_mulVec, smul_one_mulVec, sub_eq_zero] at hu
    exact hu
  have hξm : ξ ∈ Module.End.eigenspace (Matrix.toLin' Q) lam :=
    hmem ξ (by rw [Matrix.sub_mulVec, smul_one_mulVec, hvec, sub_self])
  intro w hw
  have hnz : (⟨ξ, hξm⟩ : Module.End.eigenspace (Matrix.toLin' Q) lam) ≠ 0 := by
    intro h
    apply hξ0
    have h' := congrArg Subtype.val h
    simpa using h'
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hnz).mp hsimple ⟨w, hmem w hw⟩
  refine ⟨c, ?_⟩
  have h' := congrArg Subtype.val hc
  first
    | exact h'.symm
    | (simp only [SetLike.val_smul] at h'; exact h'.symm)
    | simpa using h'.symm

/-- Theorem 5(a), step E3: at a real zero of `P_ξ`, `Q_λ(v_s, v_s) < 0 ↔ P_ξ'(s) P_{β⊙ξ}(s) > 0`
(Lemma 6 with `Q_λ ξ = 0`). -/
theorem eig_sign {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsLoewner Q a b) (lam : ℝ) (ξ : Idx N → ℝ)
    (hξ : (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ ξ = 0)
    (s : ℝ) (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0) (hroot : (P ξ).eval s = 0) :
    ((fun i => (lab i : ℝ) * ξ i / ((lab i : ℝ) - s))
        ⬝ᵥ ((Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ))
          *ᵥ (fun i => (lab i : ℝ) * ξ i / ((lab i : ℝ) - s))) < 0)
      ↔ 0 < (derivative (P ξ)).eval s * (P (fun k => b k * ξ k)).eval s := by
  have hAsym : (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ))ᵀ
      = Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ) := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
      (isSymm_of_isCvS hC).eq]
  have hv : (fun i => (lab i : ℝ) * ξ i / ((lab i : ℝ) - s))
      = ξ + s • (fun i => ξ i / ((lab i : ℝ) - s)) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hs i
    field_simp
    ring
  have hnorm : (fun i => (lab i : ℝ) * ξ i / ((lab i : ℝ) - s))
        ⬝ᵥ ((Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ))
          *ᵥ (fun i => (lab i : ℝ) * ξ i / ((lab i : ℝ) - s)))
      = s ^ 2 * ((fun i => ξ i / ((lab i : ℝ) - s))
        ⬝ᵥ ((Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ))
          *ᵥ (fun i => ξ i / ((lab i : ℝ) - s)))) := by
    rw [hv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hξ, zero_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [bil_symm hAsym ξ, hξ, dotProduct_zero]
    ring
  have hdot : ∀ w : Idx N → ℝ, w ⬝ᵥ ((Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ w)
      = ∑ i, ∑ j, w i * (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)) i j * w j := by
    intro w
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hF := F_zero_of_root ξ s hs hroot
  have hl0 : (lab (e0 N) : ℝ) = 0 := by
    rw [show lab (e0 N) = 0 from (lab_eq_zero_iff _).mpr rfl]
    simp
  have hs0 : s ≠ 0 := by
    have h := hs (e0 N)
    rw [hl0, zero_sub, neg_ne_zero] at h
    exact h
  have hΔ : ∏ j : Idx N, ((lab j : ℝ) - s) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hs j
  have hG : ∑ k, b k * ξ k / ((lab k : ℝ) - s) = ∑ k, b k * (ξ k / ((lab k : ℝ) - s)) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [hnorm, hdot, Qlam_norm hC lam ξ hξ s hs, hF, P_deriv_eval ξ s hs, P_eval_div _ s hs, hF,
    hG]
  have hs2 : 0 < s * s := mul_self_pos.mpr hs0
  have hΔ2 : 0 < (∏ j : Idx N, ((lab j : ℝ) - s)) * (∏ j : Idx N, ((lab j : ℝ) - s)) :=
    mul_self_pos.mpr hΔ
  set F₂ := ∑ k, ξ k / ((lab k : ℝ) - s) ^ 2 with hF₂
  set G := ∑ k, b k * (ξ k / ((lab k : ℝ) - s)) with hGdef
  set Δ := ∏ j : Idx N, ((lab j : ℝ) - s) with hΔdef
  have e1 : s ^ 2 * (0 * ∑ k, b k * ξ k / ((lab k : ℝ) - s) ^ 2 - F₂ * G)
      = -((s * s) * (F₂ * G)) := by ring
  have e2 : Δ * (F₂ - 0 * ∑ i : Idx N, ((lab i : ℝ) - s)⁻¹) * (Δ * G) = (Δ * Δ) * (F₂ * G) := by
    ring
  rw [e1, e2, neg_lt_zero, mul_pos_iff_of_pos_left hs2, mul_pos_iff_of_pos_left hΔ2]

/-- Theorem 5(a): `v_s ≠ 0` when `ξ ∉ ℝ e₀`. -/
theorem vr_ne_zero' {N : ℕ} (x : Idx N → ℝ) (hne : ∃ k, k ≠ e0 N ∧ x k ≠ 0) (s : ℝ)
    (hs : ∀ j : Idx N, (lab j : ℝ) - s ≠ 0) :
    (fun i => (lab i : ℝ) * x i / ((lab i : ℝ) - s)) ≠ 0 := by
  intro hv
  obtain ⟨k, hk, hxk⟩ := hne
  have h := congrFun hv k
  simp only [Pi.zero_apply] at h
  have hlk : (lab k : ℝ) ≠ 0 := by
    intro h0
    apply hk
    exact (lab_eq_zero_iff k).mp (by exact_mod_cast h0)
  rcases div_eq_zero_iff.mp h with h1 | h1
  · exact hxk ((mul_eq_zero.mp h1).resolve_left hlk)
  · exact hs k h1

/-- Theorem 5(a): `v_ζ ≠ 0` when `ξ ∉ ℝ e₀` (complex `ζ`). -/
theorem vc_ne_zero' {N : ℕ} (x : Idx N → ℝ) (hne : ∃ k, k ≠ e0 N ∧ x k ≠ 0) (s : ℂ)
    (hs : ∀ j : Idx N, ((lab j : ℝ) : ℂ) - s ≠ 0) :
    (fun i => ((lab i : ℝ) : ℂ) * x i / (((lab i : ℝ) : ℂ) - s)) ≠ 0 := by
  intro hv
  obtain ⟨k, hk, hxk⟩ := hne
  have h := congrFun hv k
  simp only [Pi.zero_apply] at h
  have hlk : ((lab k : ℝ) : ℂ) ≠ 0 := by
    intro h0
    apply hk
    exact (lab_eq_zero_iff k).mp (by exact_mod_cast h0)
  rcases div_eq_zero_iff.mp h with h1 | h1
  · exact hxk (by exact_mod_cast (mul_eq_zero.mp h1).resolve_left hlk)
  · exact hs k h1

open Classical in
/-- Theorem 5(a) (index law, even sector), for a Loewner matrix with `b` odd
(`a` need not be even). For a simple eigenvalue `λ` with even
eigenvector `ξ ∉ ℝ e₀` whose `P_ξ` has simple zeros outside `I`:
`N_c + d(ξ) = κ(λ)`. -/
theorem index_even {N : ℕ} (Q : Matrix (Idx N) (Idx N) ℝ) (a b : Idx N → ℝ)
    (hC : IsLoewner Q a b) (hb : ∀ i, b (Fin.rev i) = - b i)
    (hQ : Q.IsHermitian) (lam : ℝ) (ξ : Idx N → ℝ)
    (hvec : Q.mulVec ξ = lam • ξ) (hne : ∃ k, k ≠ e0 N ∧ ξ k ≠ 0)
    (hsimple : Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' Q) lam) = 1)
    (heven : ∀ i, ξ (Fin.rev i) = ξ i)
    (hsep : (P ξ).Separable) (hout : ∀ j : Idx N, (P ξ).eval (lab j : ℝ) ≠ 0) :
    Nc ξ + d b ξ = (univ.filter (fun i => hQ.eigenvalues i < lam)).card := by
  -- ξ spans the kernel of Q - λ (simple eigenvalue); Lemma 4 gives ⟨η, ξ⟩ ≠ 0
  have hξ : (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ ξ = 0 := by
    rw [Matrix.sub_mulVec, smul_one_mulVec, hvec, sub_self]
  have hξ0 : ξ ≠ 0 := by
    obtain ⟨k, _, hk⟩ := hne
    intro h
    exact hk (by simp [h])
  have hker := simple_ker Q lam ξ hvec hξ0 hsimple
  have hnd := nondeg_even hC hb lam ξ hξ hker heven hne
  have hηx : ∑ k, ξ k ≠ 0 := hnd.2
  have hc1 : ∑ k, (1 : ℝ) * ξ k ≠ 0 := by simpa using hηx
  have hB : (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ))ᵀ
      = Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ) := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
      (isSymm_of_isCvS hC).eq]
  have hφ : (fun k => (1 : ℝ) + 0 * b k) = fun _ => (1 : ℝ) := funext fun k => by ring
  have hBT : ((Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)) * Dprime (fun _ => (1 : ℝ)) ξ)ᵀ
      = (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)) * Dprime (fun _ => (1 : ℝ)) ξ := by
    have h := (Qlam_Dprime_isSymm hC lam ξ hξ 1 0 (by simpa using hηx)).eq
    rwa [hφ] at h
  -- roots of P_ξ
  have hp0 : P ξ ≠ 0 := hsep.ne_zero
  have hm : (P ξ).map (algebraMap ℝ ℂ) ≠ 0 := Polynomial.map_ne_zero hp0
  have hl0 : (lab (e0 N) : ℝ) = 0 := by
    rw [show lab (e0 N) = 0 from (lab_eq_zero_iff _).mpr rfl]
    simp
  have hsplit := card_roots_split hsep
  have hdeg := natDegree_P_lock ξ hηx
  have hNc := Nc_eq ξ hsep
  set R := (P ξ).roots.toFinset with hR
  set K := ((P ξ).map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z => 0 < z.im) with hK
  have hrootR : ∀ s ∈ R, (P ξ).eval s = 0 := fun s hs => by
    rw [hR, Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def] at hs
    exact hs
  have hslR : ∀ s ∈ R, ∀ j : Idx N, (lab j : ℝ) - s ≠ 0 := by
    intro s hs j h
    apply hout j
    rw [sub_eq_zero.mp h]
    exact hrootR s hs
  have h0R : (0 : ℝ) ∉ R := by
    intro h
    apply hout (e0 N)
    rw [hl0]
    exact hrootR 0 h
  have hrootK : ∀ w ∈ K, ((P ξ).map (algebraMap ℝ ℂ)).eval w = 0 := fun w hw => by
    rw [hK, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hm,
      Polynomial.IsRoot.def] at hw
    exact hw.1
  have hposK : ∀ w ∈ K, 0 < w.im := fun w hw => by
    rw [hK, Finset.mem_filter] at hw
    exact hw.2
  have hslK : ∀ w ∈ K, ∀ j : Idx N, ((lab j : ℝ) : ℂ) - w ≠ 0 := by
    intro w hw j h
    have him := congrArg Complex.im h
    rw [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at him
    linarith [hposK w hw]
  -- the eigen-family of T = D'_η
  set T := Dprime (fun _ => (1 : ℝ)) ξ with hT
  let r : Option R → ℝ := fun i => i.elim 0 (fun s => (s : ℝ))
  let v : Option R → Idx N → ℝ :=
    fun i => i.elim ξ (fun s => fun j => (lab j : ℝ) * ξ j / ((lab j : ℝ) - (s : ℝ)))
  let ζ : K → ℂ := fun k => (k : ℂ)
  let z : K → Idx N → ℂ :=
    fun k => fun j => ((lab j : ℝ) : ℂ) * ξ j / (((lab j : ℝ) : ℂ) - (k : ℂ))
  have hv : ∀ i, T *ᵥ v i = r i • v i := by
    rintro (_ | ⟨s, hs⟩)
    · show T *ᵥ ξ = (0 : ℝ) • ξ
      rw [zero_smul]
      exact Dprime_lock_kernel ξ hc1
    · exact Dprime_eigvec_r ξ hηx s (hslR s hs) (F_zero_of_root ξ s (hslR s hs) (hrootR s hs))
  have hv0 : ∀ i, v i ≠ 0 := by
    rintro (_ | ⟨s, hs⟩)
    · exact hξ0
    · exact vr_ne_zero' ξ hne s (hslR s hs)
  have hz : ∀ k, T.map (algebraMap ℝ ℂ) *ᵥ z k = ζ k • z k := by
    rintro ⟨w, hw⟩
    exact Dprime_eigvec_c ξ hηx w (hslK w hw) (F_zero_of_root_c ξ w (hslK w hw) (hrootK w hw))
  have hz0 : ∀ k, z k ≠ 0 := by
    rintro ⟨w, hw⟩
    exact vc_ne_zero' ξ hne w (hslK w hw)
  have hr : Function.Injective r := by
    rintro (_ | ⟨s, hs⟩) (_ | ⟨t, ht⟩) h
    · rfl
    · have h' : (0 : ℝ) = t := h
      exact (h0R (by rw [h']; exact ht)).elim
    · have h' : s = (0 : ℝ) := h
      exact (h0R (by rw [← h']; exact hs)).elim
    · have h' : s = t := h
      subst h'
      rfl
  have hinj := inj_sum_elim r hr ζ Subtype.val_injective (fun k => hposK k k.2)
  have hcard : Fintype.card (Option R) + 2 * Fintype.card K = Fintype.card (Idx N) := by
    rw [Fintype.card_option, Fintype.card_coe, Fintype.card_coe, Fintype.card_fin]
    omega
  obtain ⟨q, hq⟩ := exists_qform (Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ))
  have hpb := pontryagin_balance_ker hB hBT r v hv hv0 none (fun y hy => hker y hy)
    ζ z hz hz0 hinj hcard q hq
  have hk := kappa_eq_sigNeg Q hQ lam q hq
  -- negative norms: ξ is null (kernel), v_s is negative iff the defect condition holds
  have hcount : (univ.filter (fun i =>
        v i ⬝ᵥ ((Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ v i) < 0)).card = d b ξ := by
    rw [Finset.card_filter, Fintype.sum_option]
    have hnone : (if v none ⬝ᵥ ((Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ v none) < 0
        then 1 else 0) = 0 := by
      show (if ξ ⬝ᵥ ((Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ ξ) < 0 then 1 else 0) = 0
      rw [hξ, dotProduct_zero, if_neg (lt_irrefl 0)]
    rw [hnone, zero_add]
    unfold d
    rw [Finset.card_filter, ← Finset.sum_coe_sort R]
    refine Finset.sum_congr rfl fun s _ => ?_
    obtain ⟨s, hs⟩ := s
    have hiff : (v (some ⟨s, hs⟩) ⬝ᵥ ((Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ))
          *ᵥ v (some ⟨s, hs⟩)) < 0)
        ↔ (s ≠ 0 ∧ 0 < (derivative (P ξ)).eval s * (P (fun k => b k * ξ k)).eval s) := by
      rw [show v (some ⟨s, hs⟩) = (fun j => (lab j : ℝ) * ξ j / ((lab j : ℝ) - s)) from rfl,
        eig_sign hC lam ξ hξ s (hslR s hs) (hrootR s hs)]
      exact ⟨fun h => ⟨fun h0 => h0R (by rw [← h0]; exact hs), h⟩, fun h => h.2⟩
    by_cases h1 : v (some ⟨s, hs⟩) ⬝ᵥ ((Q - lam • (1 : Matrix (Idx N) (Idx N) ℝ))
        *ᵥ v (some ⟨s, hs⟩)) < 0
    · rw [if_pos h1, if_pos (hiff.mp h1)]
    · rw [if_neg h1, if_neg (fun h => h1 (hiff.mpr h))]
  rw [← hk, hpb, hcount, Fintype.card_coe, ← hNc]
  omega

open Classical in
/-- Theorem 6 for CvS matrices, as stated in the note. -/
theorem lock_cvs {N : ℕ} (Q : Matrix (Idx N) (Idx N) ℝ) (a b : Idx N → ℝ)
    (hC : IsCvS Q a b) (hQ : Q.IsHermitian) (μ : ℝ)
    (hμ : IsUnit (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ)).det)
    (x : Idx N → ℝ)
    (hx : x = Matrix.mulVec (Q - μ • (1 : Matrix (Idx N) (Idx N) ℝ))⁻¹ (Pi.single (e0 N) 1))
    (hx0 : x (e0 N) ≠ 0) (hηx : ∑ k, x k ≠ 0)
    (hsep : (P x).Separable) (hout : ∀ j : Idx N, (P x).eval (lab j : ℝ) ≠ 0) :
    Nc x + d b x + (if x (e0 N) < 0 then 1 else 0)
      = (univ.filter (fun i => hQ.eigenvalues i < μ)).card :=
  lock Q a b hC.toLoewner hQ μ hμ x hx hx0 hηx hsep hout

open Classical in
/-- Theorem 5(a) for CvS matrices, as stated in the note. -/
theorem index_even_cvs {N : ℕ} (Q : Matrix (Idx N) (Idx N) ℝ) (a b : Idx N → ℝ)
    (hC : IsCvS Q a b)
    (hQ : Q.IsHermitian) (lam : ℝ) (ξ : Idx N → ℝ)
    (hvec : Q.mulVec ξ = lam • ξ) (hne : ∃ k, k ≠ e0 N ∧ ξ k ≠ 0)
    (hsimple : Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' Q) lam) = 1)
    (heven : ∀ i, ξ (Fin.rev i) = ξ i)
    (hsep : (P ξ).Separable) (hout : ∀ j : Idx N, (P ξ).eval (lab j : ℝ) ≠ 0) :
    Nc ξ + d b ξ = (univ.filter (fun i => hQ.eigenvalues i < lam)).card :=
  index_even Q a b hC.toLoewner hC.b_odd hQ lam ξ hvec hne hsimple heven hsep hout

end CvS

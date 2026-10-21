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
    ∏ j ∈ univ.erase k, ((lab j : ℝ) - s) = (∏ j : Idx N, ((lab j : ℝ) - s)) / ((lab k : ℝ) - s) := by
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

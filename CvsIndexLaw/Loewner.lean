import CvsIndexLaw.Lock

/-!
# Theorem 6 (resolvent lock) for arbitrary distinct real nodes

`LoewnerLock.lock`: for every real symmetric Loewner matrix `q_ii = a_i`,
`q_ij = (b_i - b_j)/(ν_i - ν_j)` on a finite set of pairwise distinct real nodes `ν`
with a node `ν_{k₀} = 0`, and `μ` outside the spectrum, `x = (Q - μ)⁻¹ e_{k₀}`:
`N_c(P_x) + d(x) + [x_{k₀} < 0] = κ(μ)`.
Any finite node set and any index `k` reduce to this form by the shift `ν ↦ ν - ν_k`.

The proof is the one of `CvS.lock`. The integer labels `-N, …, N` enter it only through
their distinctness, the zero label and their number (here `n = #V`, and `deg P_x = n - 1`).
The integer nodes of `CvS` are the instance `LoewnerLock.instNodesIdx`.
-/

set_option linter.style.longLine false

open Matrix Polynomial Finset

noncomputable section

namespace LoewnerLock

/-- A finite set of pairwise distinct real nodes with a distinguished node of value `0`. -/
class Nodes (V : Type*) where
  node : V → ℝ
  node_inj : Function.Injective node
  k0 : V
  node_k0 : node k0 = 0

export Nodes (node node_inj)

/-- The distinguished node, of value `0`. -/
def z0 (V : Type*) [Nodes V] : V := Nodes.k0

theorem node_z0 (V : Type*) [Nodes V] : node (z0 V) = 0 := Nodes.node_k0

/-- The node value vanishes exactly at the distinguished node. -/
theorem node_eq_zero_iff {V : Type*} [Nodes V] (i : V) : node i = 0 ↔ i = z0 V := by
  constructor
  · intro h
    exact node_inj (h.trans (node_z0 V).symm)
  · rintro rfl
    exact node_z0 V

/-- The integer nodes `-N, …, N` of `CvS` (labels `CvS.lab`, zero at `CvS.e0 N`). -/
noncomputable instance instNodesIdx (N : ℕ) : Nodes (CvS.Idx N) where
  node := fun i => (CvS.lab i : ℝ)
  node_inj := fun i j h => by
    have h' : ((CvS.lab i : ℤ) : ℝ) = ((CvS.lab j : ℤ) : ℝ) := h
    exact CvS.lab_injective (by exact_mod_cast h')
  k0 := CvS.e0 N
  node_k0 := by
    have h := (CvS.lab_eq_zero_iff (CvS.e0 N)).mpr rfl
    exact_mod_cast h

/-- Loewner type: `q_ii = a_i`, `q_ij = (b_i - b_j)/(i - j)`, with no parity condition.
Theorem 6 (`lock`) holds for every matrix of this type. -/
structure IsLoewner {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (Q : Matrix (V) (V) ℝ) (a b : V → ℝ) : Prop where
  diag : ∀ i, Q i i = a i
  off  : ∀ i j, i ≠ j → Q i j = (b i - b j) / ((node i) - (node j))

/-- `P_ξ(s) = ∑_k ξ_k ∏_{j ≠ k} (j - s)`. -/
def P {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (ξ : V → ℝ) : ℝ[X] :=
  ∑ k, C (ξ k) * ∏ j ∈ univ.erase k, (C (node j) - X)

open Classical in
/-- `N_c`: number of pairs of non-real zeros of `P_ξ`. -/
def Nc {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (ξ : V → ℝ) : ℕ :=
  (((P ξ).map (algebraMap ℝ ℂ)).roots.filter (fun z => z.im ≠ 0)).card / 2

open Classical in
/-- Defect `d(ξ) = #{ s ∈ ℝ \ {0} : P_ξ(s) = 0, P_ξ'(s) · P_{β⊙ξ}(s) > 0 }`. -/
def d {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (b ξ : V → ℝ) : ℕ :=
  ((P ξ).roots.toFinset.filter (fun s =>
      s ≠ 0 ∧ 0 < (derivative (P ξ)).eval s * (P (fun k => b k * ξ k)).eval s)).card

/-- A CvS matrix is symmetric. -/
theorem isSymm_of_isCvS {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] {Q : Matrix (V) (V) ℝ} {a b : V → ℝ}
    (hC : IsLoewner Q a b) : Q.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  by_cases h : i = j
  · subst h
    rfl
  · -- (b_j - b_i)/(j - i) = (b_i - b_j)/(i - j): numerator and denominator both flip sign.
    rw [hC.off j i (Ne.symm h), hC.off i j h, ← neg_sub (b i) (b j),
      ← neg_sub (node i) (node j), neg_div_neg_eq]

/-- The position operator `D e_j = j e_j`. -/
def D (V : Type*) [Fintype V] [DecidableEq V] [Nodes V] : Matrix (V) (V) ℝ := Matrix.diagonal fun i => (node i)

/-- The wedge `u ∧ v = |u⟩⟨v| - |v⟩⟨u|`. -/
def wedge {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (u v : V → ℝ) : Matrix (V) (V) ℝ :=
  Matrix.of fun i j => u i * v j - v i * u j

/-- CvS Lemma 5.1: `[D, Q] = β ∧ η`, with `β = (b_j)` and `η = (1, …, 1)`. -/
theorem commutator {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] {Q : Matrix (V) (V) ℝ} {a b : V → ℝ}
    (hC : IsLoewner Q a b) : D V * Q - Q * D V = wedge b (fun _ => 1) := by
  ext i j
  simp only [D, wedge, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.of_apply, mul_one, one_mul]
  by_cases h : i = j
  · subst h
    ring
  · rw [hC.off i j h]
    have hlab : node i ≠ node j := node_inj.ne h
    have hne : (node i) - (node j) ≠ 0 := sub_ne_zero.mpr hlab
    field_simp

/-- The same identity for the shifted matrix `Q - μ`. -/
theorem commutator_shift {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] {Q : Matrix (V) (V) ℝ} {a b : V → ℝ}
    (hC : IsLoewner Q a b) (μ : ℝ) :
    D V * (Q - μ • (1 : Matrix (V) (V) ℝ)) - (Q - μ • 1) * D V
      = wedge b (fun _ => 1) := by
  rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul,
    ← commutator hC]
  abel

/-- `D'_φ = D - |Dξ⟩⟨φ| / c` with `c = ⟨φ, ξ⟩`. -/
def Dprime {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (φ ξ : V → ℝ) : Matrix (V) (V) ℝ :=
  D V - (1 / ∑ k, φ k * ξ k) • Matrix.of fun i j => (node i) * ξ i * φ j

/-- Lemma 2 (a): `D'_φ ξ = 0`. -/
theorem Dprime_mulVec_self {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (φ ξ : V → ℝ) (hc : ∑ k, φ k * ξ k ≠ 0) :
    (Dprime φ ξ).mulVec ξ = 0 := by
  ext i
  simp only [Dprime, D, Matrix.mulVec, dotProduct, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.diagonal_apply, Matrix.of_apply, smul_eq_mul,
    Pi.zero_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have key : ∑ x, 1 / (∑ k, φ k * ξ k) * ((node i) * ξ i * φ x) * ξ x
      = (node i) * ξ i * ((∑ k, φ k * ξ k) / ∑ k, φ k * ξ k) := by
    rw [div_eq_mul_one_div (∑ k, φ k * ξ k), Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [key, div_self hc, mul_one, sub_self]

-- Lemma 2 helper: evaluation of P_w at s.

theorem P_eval {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (w : V → ℝ) (s : ℝ) :
    (P w).eval s = ∑ k, w k * ∏ j ∈ univ.erase k, ((node j) - s) := by
  simp [P, Polynomial.eval_finsetSum, Polynomial.eval_prod]

-- Lemma 2 helper: D'_φ - s = diag(j - s) + (rank one).  Stated for any one-point type ι.

theorem Dprime_sub_eq {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] {ι : Type} [Unique ι] (φ ξ : V → ℝ) (s : ℝ) :
    Dprime φ ξ - s • (1 : Matrix (V) (V) ℝ)
      = diagonal (fun i : V => (node i) - s)
        + replicateCol ι (fun i => -(1 / ∑ k, φ k * ξ k) * ((node i) * ξ i))
          * replicateRow ι φ := by
  ext i j
  simp only [Dprime, D, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.diagonal_apply, Matrix.of_apply, smul_eq_mul,
    Matrix.mul_apply, replicateCol_apply, replicateRow_apply,
    Finset.univ_unique, Finset.sum_singleton]
  split_ifs <;> ring

-- Lemma 2 helper: ∏_{j≠k} (j - s) = (∏_j (j - s)) / (k - s).

theorem prod_erase_eq_div {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (s : ℝ) (hs : ∀ j : V, (node j) - s ≠ 0)
    (k : V) :
    ∏ j ∈ univ.erase k, ((node j) - s)
      = (∏ j : V, ((node j) - s)) / ((node k) - s) := by
  rw [eq_div_iff (hs k)]
  exact Finset.prod_erase_mul univ (fun j : V => (node j) - s) (mem_univ k)

-- Lemma 2 helper: the single entry of the 1×1 matrix in the determinant lemma.

theorem rankOne_entry {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] {ι : Type} [Unique ι] (φ ξ : V → ℝ) (s : ℝ) :
    ((1 + replicateRow ι φ * diagonal (fun i : V => ((node i) - s)⁻¹)
        * replicateCol ι (fun i => -(1 / ∑ k, φ k * ξ k) * ((node i) * ξ i))
          : Matrix ι ι ℝ) default default)
      = 1 + ∑ k, φ k * ((node k) - s)⁻¹ * (-(1 / ∑ k, φ k * ξ k) * ((node k) * ξ k)) := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, Finset.sum_ite_eq']

-- Lemma 2 helper: the j/(j - s) = 1 + s/(j - s) rewriting of the sum.

theorem rankOne_sum {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (φ ξ : V → ℝ) (s : ℝ) (hs : ∀ j : V, (node j) - s ≠ 0)
    (hc : ∑ k, φ k * ξ k ≠ 0) :
    ∑ k, φ k * ((node k) - s)⁻¹ * (-(1 / ∑ k, φ k * ξ k) * ((node k) * ξ k))
      = -1 - (s / ∑ k, φ k * ξ k) * ∑ k, φ k * ξ k * ((node k) - s)⁻¹ := by
  have hk : ∀ k, φ k * ((node k) - s)⁻¹ * (-(1 / ∑ k, φ k * ξ k) * ((node k) * ξ k))
      = -(1 / ∑ k, φ k * ξ k) * (φ k * ξ k)
        - (s / ∑ k, φ k * ξ k) * (φ k * ξ k * ((node k) - s)⁻¹) := by
    intro k
    field_simp [hs k]
    ring
  rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, neg_mul, one_div, inv_mul_cancel₀ hc]

-- Lemma 2 helper: pull the full product out of the sum.

theorem prod_sum_div {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (φ ξ : V → ℝ) (s : ℝ) :
    ∑ k, φ k * ξ k * ((∏ j : V, ((node j) - s)) / ((node k) - s))
      = (∏ j : V, ((node j) - s)) * ∑ k, φ k * ξ k * ((node k) - s)⁻¹ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_eq_mul_inv]
  ring

-- Lemma 2 helper: the determinant identity away from the labels, over any one-point type ι,
-- so that every instance on ι comes from `Unique ι` exactly as in Mathlib's lemma.

theorem det_Dprime_aux {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] {ι : Type} [Unique ι] (φ ξ : V → ℝ)
    (hc : ∑ k, φ k * ξ k ≠ 0) (s : ℝ) (hs : ∀ j : V, (node j) - s ≠ 0) :
    (Dprime φ ξ - s • (1 : Matrix (V) (V) ℝ)).det
      = -(s / ∑ k, φ k * ξ k) * (P fun k => φ k * ξ k).eval s := by
  have hA : IsUnit (diagonal (fun i : V => (node i) - s)).det := by
    rw [det_diagonal]
    exact (Finset.prod_ne_zero_iff.mpr fun j _ => hs j).isUnit
  have hinv : (diagonal (fun i : V => (node i) - s))⁻¹
      = diagonal (fun i : V => ((node i) - s)⁻¹) := by
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

theorem det_Dprime_off_labels {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (φ ξ : V → ℝ) (hc : ∑ k, φ k * ξ k ≠ 0) (s : ℝ)
    (hs : ∀ j : V, (node j) - s ≠ 0) :
    (Dprime φ ξ - s • (1 : Matrix (V) (V) ℝ)).det
      = -(s / ∑ k, φ k * ξ k) * (P fun k => φ k * ξ k).eval s :=
  det_Dprime_aux (ι := Unit) φ ξ hc s hs

/-- Lemma 2 (b): `det (D'_φ - s) = -(s / c) · P_{φ⊙ξ}(s)` for every real `s`.
Away from the labels this is the matrix determinant lemma; at the finitely many
labels it follows by continuity. -/
theorem det_Dprime {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (φ ξ : V → ℝ) (hc : ∑ k, φ k * ξ k ≠ 0) (s : ℝ) :
    (Dprime φ ξ - s • (1 : Matrix (V) (V) ℝ)).det
      = -(s / ∑ k, φ k * ξ k) * (P fun k => φ k * ξ k).eval s := by
  have h1 : Continuous fun s : ℝ => (Dprime φ ξ - s • (1 : Matrix (V) (V) ℝ)).det :=
    (continuous_const.sub (continuous_id.smul continuous_const)).matrix_det
  have h2 : Continuous fun s : ℝ =>
      -(s / ∑ k, φ k * ξ k) * (P fun k => φ k * ξ k).eval s :=
    (continuous_id.div_const _).neg.mul (Polynomial.continuous _)
  have hset : {s : ℝ | ∀ j : V, (node j) - s ≠ 0}
      = Set.univ \ Set.range (fun j : V => (node j)) := by
    ext t
    simp [sub_eq_zero]
  have hdense : Dense {s : ℝ | ∀ j : V, (node j) - s ≠ 0} := by
    rw [hset]
    exact dense_univ.sdiff_finite (Set.finite_range _)
  have heq := Continuous.ext_on hdense h1 h2 fun t ht => det_Dprime_off_labels φ ξ hc t ht
  exact congrFun heq s

/-- Theorem 6, step T6.1: in the lock setting `(Q - μ) x = e₀`, `(Q - μ) D'_η` is symmetric
(uses `node (z0 V) = 0`). -/
theorem Qmu_Dprime_lock_isSymm {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] {Q : Matrix (V) (V) ℝ} {a b : V → ℝ}
    (hC : IsLoewner Q a b) (μ : ℝ) (x : V → ℝ)
    (hx : (Q - μ • (1 : Matrix (V) (V) ℝ)) *ᵥ x = Pi.single (z0 V) 1)
    (hc : ∑ k, (1 : ℝ) * x k ≠ 0) :
    ((Q - μ • (1 : Matrix (V) (V) ℝ)) * Dprime (fun _ => (1 : ℝ)) x).IsSymm := by
  have hcs := commutator_shift hC μ
  set A := Q - μ • (1 : Matrix (V) (V) ℝ) with hA
  have hAsym : ∀ i j, A j i = A i j := by
    intro i j
    have hs := (isSymm_of_isCvS hC).apply i j
    by_cases h : i = j
    · subst h
      rfl
    · simp [hA, Matrix.sub_apply, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), hs]
  have hcomm : ∀ i j, (node i) * A i j - A i j * (node j) = b i - b j := by
    intro i j
    have := congrArg (fun M => M i j) hcs
    simpa [D, wedge, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.of_apply] using this
  have hv : ∀ i, ∑ k, A i k * ((node k) * x k)
      = (∑ k, b k * x k) - b i * ∑ k, x k := by
    intro i
    have h0 : (node i) * ∑ k, A i k * x k = 0 := by
      have h := congrFun hx i
      simp only [Matrix.mulVec, dotProduct] at h
      rw [h]
      by_cases hi : i = z0 V
      · subst hi
        simp [node_z0]
      · simp [hi]
    have h1 : ∑ k, ((node i) * A i k - A i k * (node k)) * x k
        = ∑ k, (b i - b k) * x k :=
      Finset.sum_congr rfl fun k _ => by rw [hcomm i k]
    have e1 : ∑ k, ((node i) * A i k - A i k * (node k)) * x k
        = (node i) * ∑ k, A i k * x k - ∑ k, A i k * ((node k) * x k) := by
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
      = A i j * (node j)
        - 1 / (∑ k, (1 : ℝ) * x k) * 1 * ∑ k, A i k * ((node k) * x k) := by
    intro i j
    rw [Matrix.mul_apply]
    have hk : ∀ k, A i k * Dprime (fun _ => (1 : ℝ)) x k j
        = (if k = j then A i k * (node k) else 0)
          - 1 / (∑ k, (1 : ℝ) * x k) * 1 * (A i k * ((node k) * x k)) := by
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
theorem Dprime_lock_kernel {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (x : V → ℝ) (hc : ∑ k, (1 : ℝ) * x k ≠ 0) :
    Dprime (fun _ => (1 : ℝ)) x *ᵥ x = 0 :=
  Dprime_mulVec_self (fun _ => (1 : ℝ)) x hc

/-- Theorem 6, step T6.2 (b): a real zero `s` of `P_x` off the labels is a zero of
`F(s) = Σ x_k/(k - s)`. -/
theorem F_zero_of_root {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (x : V → ℝ) (s : ℝ)
    (hs : ∀ j : V, (node j) - s ≠ 0) (hroot : (P x).eval s = 0) :
    ∑ k, x k / ((node k) - s) = 0 := by
  have hΔ : ∏ j : V, ((node j) - s) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hs j
  have hP : (P x).eval s = (∏ j : V, ((node j) - s)) * ∑ k, x k / ((node k) - s) := by
    rw [P_eval, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [prod_erase_eq_div s hs k]
    ring
  rw [hP] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left hΔ

/-- Theorem 6, step T6.2 (c), real: `F(s) = 0` makes `v_s = node·x/(node - s)` an eigenvector
of `T` for `s`. -/
theorem Dprime_eigvec_r {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (x : V → ℝ) (hc : ∑ k, x k ≠ 0) (s : ℝ)
    (hs : ∀ j : V, (node j) - s ≠ 0) (hF : ∑ k, x k / ((node k) - s) = 0) :
    Dprime (fun _ => (1 : ℝ)) x *ᵥ (fun i => (node i) * x i / ((node i) - s))
      = s • (fun i => (node i) * x i / ((node i) - s)) := by
  set v : V → ℝ := fun i => (node i) * x i / ((node i) - s) with hvdef
  have hT : ∀ i j, Dprime (fun _ => (1 : ℝ)) x i j
      = (if i = j then (node i) else 0) - (∑ k, x k)⁻¹ * ((node i) * x i) := by
    intro i j
    simp only [Dprime, D, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply,
      Matrix.of_apply, smul_eq_mul, one_mul, mul_one, one_div]
  have hterm : ∀ j, v j = x j + s * (x j / ((node j) - s)) := by
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
theorem Dprime_eigvec_c {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (x : V → ℝ) (hc : ∑ k, x k ≠ 0) (s : ℂ)
    (hs : ∀ j : V, ((node j) : ℂ) - s ≠ 0)
    (hF : ∑ k, (x k : ℂ) / (((node k) : ℂ) - s) = 0) :
    (Dprime (fun _ => (1 : ℝ)) x).map (algebraMap ℝ ℂ)
        *ᵥ (fun i => ((node i) : ℂ) * x i / (((node i) : ℂ) - s))
      = s • (fun i => ((node i) : ℂ) * x i / (((node i) : ℂ) - s)) := by
  set v : V → ℂ := fun i => ((node i) : ℂ) * x i / (((node i) : ℂ) - s) with hvdef
  have hT : ∀ i j, (Dprime (fun _ => (1 : ℝ)) x).map (algebraMap ℝ ℂ) i j
      = (if i = j then ((node i) : ℂ) else 0)
        - ((∑ k, x k : ℝ) : ℂ)⁻¹ * (((node i) : ℂ) * x i) := by
    intro i j
    simp only [Matrix.map_apply, Dprime, D, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.diagonal_apply, Matrix.of_apply, smul_eq_mul, one_mul, mul_one, one_div]
    split_ifs <;> simp
  have hterm : ∀ j, v j = (x j : ℂ) + s * ((x j : ℂ) / (((node j) : ℂ) - s)) := by
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
theorem lock_norm_x {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (A : Matrix (V) (V) ℝ) (x : V → ℝ)
    (hx : A *ᵥ x = Pi.single (z0 V) 1) : x ⬝ᵥ (A *ᵥ x) = x (z0 V) := by
  rw [hx]
  simp

/-- Theorem 6, step T6.3: `Q_μ(v_s, v_s) = s² (F G₂ - F₂ G)` in the lock setting
(the `e₀`-terms cancel). -/
theorem lock_norm {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] {Q : Matrix (V) (V) ℝ} {a b : V → ℝ}
    (hC : IsLoewner Q a b) (μ : ℝ) (x : V → ℝ)
    (hx : (Q - μ • (1 : Matrix (V) (V) ℝ)) *ᵥ x = Pi.single (z0 V) 1)
    (s : ℝ) (hs : ∀ j : V, (node j) - s ≠ 0) :
    ∑ i, ∑ j, ((node i) * x i / ((node i) - s))
        * (Q - μ • (1 : Matrix (V) (V) ℝ)) i j * ((node j) * x j / ((node j) - s))
      = s ^ 2 * ((∑ k, x k / ((node k) - s)) * (∑ k, b k * x k / ((node k) - s) ^ 2)
          - (∑ k, x k / ((node k) - s) ^ 2) * (∑ k, b k * (x k / ((node k) - s)))) := by
  have hcs := commutator_shift hC μ
  set A := Q - μ • (1 : Matrix (V) (V) ℝ) with hA
  have hcomm : ∀ i j, (node i) * A i j - A i j * (node j) = b i - b j := by
    intro i j
    have := congrArg (fun M => M i j) hcs
    simpa [D, wedge, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.of_apply] using this
  have hAx : ∀ i, ∑ j, A i j * x j = if i = z0 V then 1 else 0 := by
    intro i
    have h := congrFun hx i
    simp only [Matrix.mulVec, dotProduct] at h
    rw [h, Pi.single_apply]
  have hl0 : node (z0 V) = 0 := node_z0 V
  have hlw : ∀ j, (node j) * (x j / ((node j) - s))
      = x j + s * (x j / ((node j) - s)) := by
    intro j
    have := hs j
    field_simp
    ring
  -- (Q_μ w)_i = (b_i F - G + [i = e₀]) / (i - s)
  have hAw : ∀ i, ∑ j, A i j * (x j / ((node j) - s))
      = (b i * ∑ k, x k / ((node k) - s) - ∑ k, b k * (x k / ((node k) - s))
          + (if i = z0 V then 1 else 0)) / ((node i) - s) := by
    intro i
    rw [eq_div_iff (hs i)]
    have h1 : ∑ j, ((node i) * A i j - A i j * (node j)) * (x j / ((node j) - s))
        = ∑ j, (b i - b j) * (x j / ((node j) - s)) :=
      Finset.sum_congr rfl fun j _ => by rw [hcomm i j]
    have hterm : ∀ j, ((node i) * A i j - A i j * (node j)) * (x j / ((node j) - s))
        = ((node i) - s) * (A i j * (x j / ((node j) - s))) - A i j * x j := by
      intro j
      linear_combination (-(A i j)) * hlw j
    have e1 : ∑ j, ((node i) * A i j - A i j * (node j)) * (x j / ((node j) - s))
        = ((node i) - s) * ∑ j, A i j * (x j / ((node j) - s))
          - (if i = z0 V then 1 else 0) := by
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hAx i]
    have e2 : ∑ j, (b i - b j) * (x j / ((node j) - s))
        = b i * ∑ k, x k / ((node k) - s) - ∑ k, b k * (x k / ((node k) - s)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e1, e2] at h1
    linarith
  -- v = x + s w
  have hv : ∀ i, (node i) * x i / ((node i) - s) = x i + s * (x i / ((node i) - s)) :=
    fun i => by rw [mul_div_assoc]; exact hlw i
  -- row sums: Σ_j v_i A_ij v_j = v_i ([i = e₀] + s (Q_μ w)_i)
  have hrow : ∀ i, ∑ j, ((node i) * x i / ((node i) - s)) * A i j
        * ((node j) * x j / ((node j) - s))
      = ((node i) * x i / ((node i) - s))
        * ((if i = z0 V then 1 else 0) + s * ∑ j, A i j * (x j / ((node j) - s))) := by
    intro i
    have ht : ∀ j, ((node i) * x i / ((node i) - s)) * A i j
          * ((node j) * x j / ((node j) - s))
        = ((node i) * x i / ((node i) - s)) * (A i j * x j)
          + ((node i) * x i / ((node i) - s)) * s * (A i j * (x j / ((node j) - s))) := by
      intro j
      rw [hv j]
      ring
    rw [Finset.sum_congr rfl fun j _ => ht j, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hAx i]
    ring
  rw [Finset.sum_congr rfl fun i _ => hrow i]
  simp only [hAw]
  -- per-term split: the z0-part vanishes because node (z0 V) = 0
  have hper : ∀ i, ((node i) * x i / ((node i) - s))
        * ((if i = z0 V then 1 else 0)
          + s * ((b i * ∑ k, x k / ((node k) - s) - ∑ k, b k * (x k / ((node k) - s))
            + (if i = z0 V then 1 else 0)) / ((node i) - s)))
      = (b i * ∑ k, x k / ((node k) - s) - ∑ k, b k * (x k / ((node k) - s)))
          * (s * (x i / ((node i) - s)) + s ^ 2 * (x i / ((node i) - s) ^ 2))
        + (if i = z0 V then
            (node i) * x i / ((node i) - s) * (1 + s / ((node i) - s)) else 0) := by
    intro i
    have := hs i
    split_ifs
    · field_simp
      ring
    · field_simp
      ring
  rw [Finset.sum_congr rfl fun i _ => hper i, Finset.sum_add_distrib]
  have hite : ∑ i, (if i = z0 V then
      (node i) * x i / ((node i) - s) * (1 + s / ((node i) - s)) else 0) = 0 := by
    rw [Finset.sum_ite_eq']
    simp [hl0]
  rw [hite, add_zero]
  have hexp : ∀ i, (b i * ∑ k, x k / ((node k) - s) - ∑ k, b k * (x k / ((node k) - s)))
        * (s * (x i / ((node i) - s)) + s ^ 2 * (x i / ((node i) - s) ^ 2))
      = s * (∑ k, x k / ((node k) - s)) * (b i * (x i / ((node i) - s)))
        - s * (∑ k, b k * (x k / ((node k) - s))) * (x i / ((node i) - s))
        + s ^ 2 * (∑ k, x k / ((node k) - s)) * (b i * x i / ((node i) - s) ^ 2)
        - s ^ 2 * (∑ k, b k * (x k / ((node k) - s))) * (x i / ((node i) - s) ^ 2) := by
    intro i
    ring
  rw [Finset.sum_congr rfl fun i _ => hexp i]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- `P_w(s) = Δ(s) · Σ w_k/(k - s)` off the labels. -/
theorem P_eval_div {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (w : V → ℝ) (s : ℝ) (hs : ∀ j : V, (node j) - s ≠ 0) :
    (P w).eval s = (∏ j : V, ((node j) - s)) * ∑ k, w k / ((node k) - s) := by
  rw [P_eval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [prod_erase_eq_div s hs k]
  ring

/-- Theorem 6, step T6.4: `P_x'(s) = Δ(s) (F₂ - F · S)` with `S = Σ 1/(i - s)`. -/
theorem P_deriv_eval {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (x : V → ℝ) (s : ℝ) (hs : ∀ j : V, (node j) - s ≠ 0) :
    (derivative (P x)).eval s
      = (∏ j : V, ((node j) - s))
        * (∑ k, x k / ((node k) - s) ^ 2
          - (∑ k, x k / ((node k) - s)) * ∑ i : V, ((node i) - s)⁻¹) := by
  have hΔk : ∀ k : V, ∏ j ∈ univ.erase k, ((node j) - s)
      = (∏ j : V, ((node j) - s)) / ((node k) - s) := prod_erase_eq_div s hs
  have hΔki : ∀ k i : V, i ∈ univ.erase k →
      ∏ j ∈ (univ.erase k).erase i, ((node j) - s)
        = (∏ j ∈ univ.erase k, ((node j) - s)) / ((node i) - s) := by
    intro k i hi
    rw [eq_div_iff (hs i), mul_comm]
    exact Finset.mul_prod_erase (univ.erase k) (fun j => (node j) - s) hi
  have hder : derivative (P x) = ∑ k, C (x k)
      * ∑ i ∈ univ.erase k, (∏ j ∈ (univ.erase k).erase i, (C (node j) - X)) * (-1) := by
    unfold P
    rw [derivative_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [derivative_mul, derivative_C, zero_mul, zero_add, CvS.derivative_finset_prod]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [derivative_sub, derivative_C, derivative_X, zero_sub]
  rw [hder, Polynomial.eval_finsetSum]
  simp only [eval_mul, eval_C, Polynomial.eval_finsetSum, eval_prod, eval_sub, eval_X, eval_neg,
    eval_one]
  have hk : ∀ k : V, x k * ∑ i ∈ univ.erase k,
        (∏ j ∈ (univ.erase k).erase i, ((node j) - s)) * (-1)
      = (∏ j : V, ((node j) - s))
        * (x k / ((node k) - s) ^ 2
          - x k / ((node k) - s) * ∑ i : V, ((node i) - s)⁻¹) := by
    intro k
    have hin : ∀ i ∈ univ.erase k, (∏ j ∈ (univ.erase k).erase i, ((node j) - s)) * (-1)
        = (∏ j : V, ((node j) - s)) / ((node k) - s) / ((node i) - s) * (-1) := by
      intro i hi
      rw [hΔki k i hi, hΔk k]
    rw [Finset.sum_congr rfl hin, Finset.sum_erase_eq_sub (Finset.mem_univ k)]
    have hS : ∑ i : V,
          (∏ j : V, ((node j) - s)) / ((node k) - s) / ((node i) - s) * (-1)
        = -((∏ j : V, ((node j) - s)) / ((node k) - s))
          * ∑ i : V, ((node i) - s)⁻¹ := by
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
theorem lock_sign {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] {Q : Matrix (V) (V) ℝ} {a b : V → ℝ}
    (hC : IsLoewner Q a b) (μ : ℝ) (x : V → ℝ)
    (hx : (Q - μ • (1 : Matrix (V) (V) ℝ)) *ᵥ x = Pi.single (z0 V) 1)
    (s : ℝ) (hs : ∀ j : V, (node j) - s ≠ 0) (hroot : (P x).eval s = 0) :
    (∑ i, ∑ j, ((node i) * x i / ((node i) - s))
        * (Q - μ • (1 : Matrix (V) (V) ℝ)) i j * ((node j) * x j / ((node j) - s))
        < 0)
      ↔ 0 < (derivative (P x)).eval s * (P (fun k => b k * x k)).eval s := by
  have hF := F_zero_of_root x s hs hroot
  have hl0 : node (z0 V) = 0 := node_z0 V
  have hs0 : s ≠ 0 := by
    have h := hs (z0 V)
    rw [hl0, zero_sub, neg_ne_zero] at h
    exact h
  have hΔ : ∏ j : V, ((node j) - s) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hs j
  have hG : ∑ k, b k * x k / ((node k) - s) = ∑ k, b k * (x k / ((node k) - s)) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [lock_norm hC μ x hx s hs, hF, P_deriv_eval x s hs, P_eval_div _ s hs, hF, hG]
  have hs2 : 0 < s * s := mul_self_pos.mpr hs0
  have hΔ2 : 0 < (∏ j : V, ((node j) - s)) * (∏ j : V, ((node j) - s)) :=
    mul_self_pos.mpr hΔ
  set F₂ := ∑ k, x k / ((node k) - s) ^ 2 with hF₂
  set G := ∑ k, b k * (x k / ((node k) - s)) with hGdef
  set Δ := ∏ j : V, ((node j) - s) with hΔdef
  have e1 : s ^ 2 * (0 * ∑ k, b k * x k / ((node k) - s) ^ 2 - F₂ * G)
      = -((s * s) * (F₂ * G)) := by ring
  have e2 : Δ * (F₂ - 0 * ∑ i : V, ((node i) - s)⁻¹) * (Δ * G) = (Δ * Δ) * (F₂ * G) := by
    ring
  rw [e1, e2, neg_lt_zero, mul_pos_iff_of_pos_left hs2, mul_pos_iff_of_pos_left hΔ2]

/-- Theorem 6, step T6.5: `χ(D'_η) = C((-1)^(n+1)/c) · X · P_x` with `c = Σ x_k`, `n = #V`. -/
theorem charpoly_lock {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (x : V → ℝ) (hc : ∑ k, x k ≠ 0) :
    (Dprime (fun _ => (1 : ℝ)) x).charpoly
      = C ((-1 : ℝ) ^ (Fintype.card (V) + 1) / ∑ k, x k) * (X * P x) := by
  apply Polynomial.funext
  intro s
  have hd := det_Dprime (fun _ => (1 : ℝ)) x (by simpa using hc) s
  simp only [one_mul] at hd
  rw [Matrix.eval_charpoly]
  have hsc : Matrix.scalar (V) s - Dprime (fun _ => (1 : ℝ)) x
      = -(Dprime (fun _ => (1 : ℝ)) x - s • (1 : Matrix (V) (V) ℝ)) := by
    rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [hsc, Matrix.det_neg, hd]
  simp only [eval_mul, eval_C, eval_X]
  ring

/-- Theorem 6, step T6.5: `deg P_x = n - 1`, `n = #V`. -/
theorem natDegree_P_lock {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (x : V → ℝ) (hc : ∑ k, x k ≠ 0) :
    (P x).natDegree = Fintype.card (V) - 1 := by
  have h := charpoly_lock x hc
  have hdeg := Matrix.charpoly_natDegree_eq_dim (Dprime (fun _ => (1 : ℝ)) x)
  have hc' : ((-1 : ℝ) ^ (Fintype.card (V) + 1) / ∑ k, x k) ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (by norm_num)) hc
  have hP0 : P x ≠ 0 := by
    intro h0
    have hm := Matrix.charpoly_monic (Dprime (fun _ => (1 : ℝ)) x)
    rw [h, h0, mul_zero, mul_zero] at hm
    exact Polynomial.not_monic_zero hm
  rw [h, natDegree_C_mul hc', natDegree_X_mul hP0] at hdeg
  omega

/-- Theorem 6, step T6.6: a complex zero `ζ` of `P_x` off the labels has `F(ζ) = 0`. -/
theorem F_zero_of_root_c {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (x : V → ℝ) (s : ℂ)
    (hs : ∀ j : V, ((node j) : ℂ) - s ≠ 0)
    (hroot : ((P x).map (algebraMap ℝ ℂ)).eval s = 0) :
    ∑ k, (x k : ℂ) / (((node k) : ℂ) - s) = 0 := by
  have hΔ : ∏ j : V, (((node j) : ℂ) - s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hs j
  have hev : ((P x).map (algebraMap ℝ ℂ)).eval s
      = ∑ k, (x k : ℂ) * ∏ j ∈ univ.erase k, (((node j) : ℂ) - s) := by
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    simp only [P, map_sum, map_mul, map_prod, map_sub, Polynomial.aeval_C, Polynomial.aeval_X]
    rfl
  have hP : ((P x).map (algebraMap ℝ ℂ)).eval s
      = (∏ j : V, (((node j) : ℂ) - s)) * ∑ k, (x k : ℂ) / (((node k) : ℂ) - s) := by
    rw [hev, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : ∏ j ∈ univ.erase k, (((node j) : ℂ) - s)
        = (∏ j : V, (((node j) : ℂ) - s)) / (((node k) : ℂ) - s) := by
      rw [eq_div_iff (hs k)]
      exact Finset.prod_erase_mul univ (fun j : V => ((node j) : ℂ) - s) (mem_univ k)
    rw [hk]
    ring
  rw [hP] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left hΔ

/-- Theorem 6, step T6.6: `v_s ≠ 0` for a real `s` with `F(s) = 0` (needs `x₀ ≠ 0`). -/
theorem vr_ne_zero {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (x : V → ℝ) (hx0 : x (z0 V) ≠ 0) (s : ℝ)
    (hs : ∀ j : V, (node j) - s ≠ 0) (hF : ∑ k, x k / ((node k) - s) = 0) :
    (fun i => (node i) * x i / ((node i) - s)) ≠ 0 := by
  intro hv
  have hl0 : node (z0 V) = 0 := node_z0 V
  have hs0 : s ≠ 0 := by
    have h := hs (z0 V)
    rw [hl0, zero_sub, neg_ne_zero] at h
    exact h
  have hxi : ∀ i, i ≠ z0 V → x i = 0 := by
    intro i hi
    have h := congrFun hv i
    simp only [Pi.zero_apply] at h
    have hli : (node i) ≠ 0 := by
      intro h0
      apply hi
      exact (node_eq_zero_iff i).mp (by exact_mod_cast h0)
    rcases div_eq_zero_iff.mp h with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_left hli
    · exact absurd h1 (hs i)
  have hsum : ∑ k, x k / ((node k) - s) = x (z0 V) / ((node (z0 V)) - s) :=
    Finset.sum_eq_single (z0 V) (fun k _ hk => by rw [hxi k hk, zero_div])
      (fun h => absurd (Finset.mem_univ _) h)
  rw [hsum, hl0, zero_sub] at hF
  rcases div_eq_zero_iff.mp hF with h | h
  · exact hx0 h
  · exact hs0 (neg_eq_zero.mp h)

/-- Theorem 6, step T6.6: `v_ζ ≠ 0` for a complex `ζ` with `F(ζ) = 0`. -/
theorem vc_ne_zero {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (x : V → ℝ) (hx0 : x (z0 V) ≠ 0) (s : ℂ)
    (hs : ∀ j : V, ((node j) : ℂ) - s ≠ 0)
    (hF : ∑ k, (x k : ℂ) / (((node k) : ℂ) - s) = 0) :
    (fun i => ((node i) : ℂ) * x i / (((node i) : ℂ) - s)) ≠ 0 := by
  intro hv
  have hl0 : ((node (z0 V) : ℝ) : ℂ) = 0 := by simp [node_z0]
  have hs0 : s ≠ 0 := by
    have h := hs (z0 V)
    rw [hl0, zero_sub, neg_ne_zero] at h
    exact h
  have hxi : ∀ i, i ≠ z0 V → x i = 0 := by
    intro i hi
    have h := congrFun hv i
    simp only [Pi.zero_apply] at h
    have hli : ((node i) : ℂ) ≠ 0 := by
      intro h0
      apply hi
      exact (node_eq_zero_iff i).mp (by exact_mod_cast h0)
    rcases div_eq_zero_iff.mp h with h1 | h1
    · exact_mod_cast (mul_eq_zero.mp h1).resolve_left hli
    · exact absurd h1 (hs i)
  have hsum : ∑ k, (x k : ℂ) / (((node k) : ℂ) - s)
      = (x (z0 V) : ℂ) / (((node (z0 V)) : ℂ) - s) :=
    Finset.sum_eq_single (z0 V) (fun k _ hk => by rw [hxi k hk, Complex.ofReal_zero, zero_div])
      (fun h => absurd (Finset.mem_univ _) h)
  rw [hsum, hl0, zero_sub] at hF
  rcases div_eq_zero_iff.mp hF with h | h
  · exact hx0 (by exact_mod_cast h)
  · exact hs0 (neg_eq_zero.mp h)

/-- Theorem 6, step T6.6: `N_c(P_ξ) = #{roots with Im > 0}` for separable `P_ξ`. -/
theorem Nc_eq {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (ξ : V → ℝ) (hsep : (P ξ).Separable) :
    Nc ξ = (((P ξ).map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z => 0 < z.im)).card := by
  classical
  have hp0 : P ξ ≠ 0 := hsep.ne_zero
  have hnd : ((P ξ).map (algebraMap ℝ ℂ)).roots.Nodup := Polynomial.nodup_roots hsep.map
  have hfil : (((P ξ).map (algebraMap ℝ ℂ)).roots.filter (fun z => z.im ≠ 0)).card
      = (((P ξ).map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z => z.im ≠ 0)).card := by
    rw [← Multiset.toFinset_filter, Multiset.toFinset_card_of_nodup (hnd.filter _)]
  have h2 := CvS.card_filter_split
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
  have hc := CvS.card_im_neg_eq_pos hp0
  unfold Nc
  rw [hfil]
  omega

open Classical in
/-- Theorem 6 (resolvent lock), for every Loewner matrix (no parity condition).
For `μ` not an eigenvalue and `x = (Q - μ)⁻¹ e₀`:
`N_c(P_x) + d(x) + [x₀ < 0] = κ(μ)`, the number of eigenvalues of `Q` below `μ`. -/
theorem lock {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (Q : Matrix (V) (V) ℝ) (a b : V → ℝ)
    (hC : IsLoewner Q a b) (hQ : Q.IsHermitian) (μ : ℝ)
    (hμ : IsUnit (Q - μ • (1 : Matrix (V) (V) ℝ)).det)
    (x : V → ℝ)
    (hx : x = Matrix.mulVec (Q - μ • (1 : Matrix (V) (V) ℝ))⁻¹ (Pi.single (z0 V) 1))
    (hx0 : x (z0 V) ≠ 0) (hηx : ∑ k, x k ≠ 0)
    (hsep : (P x).Separable) (hout : ∀ j : V, (P x).eval (node j) ≠ 0) :
    Nc x + d b x + (if x (z0 V) < 0 then 1 else 0)
      = (univ.filter (fun i => hQ.eigenvalues i < μ)).card := by
  -- the resolvent vector solves (Q - μ) x = e₀
  have hAx : (Q - μ • (1 : Matrix (V) (V) ℝ)) *ᵥ x = Pi.single (z0 V) 1 := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hμ, Matrix.one_mulVec]
  have hc1 : ∑ k, (1 : ℝ) * x k ≠ 0 := by simpa using hηx
  have hB : (Q - μ • (1 : Matrix (V) (V) ℝ))ᵀ = Q - μ • (1 : Matrix (V) (V) ℝ) := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
      (isSymm_of_isCvS hC).eq]
  have hBdet : (Q - μ • (1 : Matrix (V) (V) ℝ)).det ≠ 0 := hμ.ne_zero
  have hBT := (Qmu_Dprime_lock_isSymm hC μ x hAx hc1).eq
  -- roots of P_x
  have hp0 : P x ≠ 0 := hsep.ne_zero
  have hm : (P x).map (algebraMap ℝ ℂ) ≠ 0 := Polynomial.map_ne_zero hp0
  have hl0 : node (z0 V) = 0 := node_z0 V
  have hsplit := CvS.card_roots_split hsep
  have hdeg := natDegree_P_lock x hηx
  have hNc := Nc_eq x hsep
  set R := (P x).roots.toFinset with hR
  set K := ((P x).map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z => 0 < z.im) with hK
  have hrootR : ∀ s ∈ R, (P x).eval s = 0 := fun s hs => by
    rw [hR, Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def] at hs
    exact hs
  have hslR : ∀ s ∈ R, ∀ j : V, (node j) - s ≠ 0 := by
    intro s hs j h
    apply hout j
    rw [sub_eq_zero.mp h]
    exact hrootR s hs
  have h0R : (0 : ℝ) ∉ R := by
    intro h
    apply hout (z0 V)
    rw [hl0]
    exact hrootR 0 h
  have hrootK : ∀ w ∈ K, ((P x).map (algebraMap ℝ ℂ)).eval w = 0 := fun w hw => by
    rw [hK, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hm,
      Polynomial.IsRoot.def] at hw
    exact hw.1
  have hposK : ∀ w ∈ K, 0 < w.im := fun w hw => by
    rw [hK, Finset.mem_filter] at hw
    exact hw.2
  have hslK : ∀ w ∈ K, ∀ j : V, ((node j) : ℂ) - w ≠ 0 := by
    intro w hw j h
    have him := congrArg Complex.im h
    rw [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at him
    linarith [hposK w hw]
  -- the eigen-family of T = D'_η
  set T := Dprime (fun _ => (1 : ℝ)) x with hT
  let r : Option R → ℝ := fun i => i.elim 0 (fun s => (s : ℝ))
  let v : Option R → V → ℝ :=
    fun i => i.elim x (fun s => fun j => (node j) * x j / ((node j) - (s : ℝ)))
  let ζ : K → ℂ := fun k => (k : ℂ)
  let z : K → V → ℂ :=
    fun k => fun j => ((node j) : ℂ) * x j / (((node j) : ℂ) - (k : ℂ))
  have hv : ∀ i, T *ᵥ v i = r i • v i := by
    rintro (_ | ⟨s, hs⟩)
    · show T *ᵥ x = (0 : ℝ) • x
      rw [zero_smul]
      exact Dprime_lock_kernel x hc1
    · exact Dprime_eigvec_r x hηx s (hslR s hs) (F_zero_of_root x s (hslR s hs) (hrootR s hs))
  have hv0 : ∀ i, v i ≠ 0 := by
    rintro (_ | ⟨s, hs⟩)
    · intro h
      exact hx0 (congrFun h (z0 V))
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
  have hinj := CvS.inj_sum_elim r hr ζ Subtype.val_injective (fun k => hposK k k.2)
  have hcard : Fintype.card (Option R) + 2 * Fintype.card K = Fintype.card (V) := by
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨z0 V⟩
    rw [Fintype.card_option, Fintype.card_coe, Fintype.card_coe]
    omega
  obtain ⟨q, hq⟩ := CvS.exists_qform (Q - μ • (1 : Matrix (V) (V) ℝ))
  have hpb := CvS.pontryagin_balance hB hBdet hBT r v hv hv0 ζ z hz hz0 hinj hcard q hq
  have hk := CvS.kappa_eq_sigNeg' Q hQ μ q hq
  -- negative norms: x ↔ x₀ < 0, and v_s ↔ the defect condition
  have hdot : ∀ w : V → ℝ, w ⬝ᵥ ((Q - μ • (1 : Matrix (V) (V) ℝ)) *ᵥ w)
      = ∑ i, ∑ j, w i * (Q - μ • (1 : Matrix (V) (V) ℝ)) i j * w j := by
    intro w
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hcount : (univ.filter (fun i =>
        v i ⬝ᵥ ((Q - μ • (1 : Matrix (V) (V) ℝ)) *ᵥ v i) < 0)).card
      = (if x (z0 V) < 0 then 1 else 0) + d b x := by
    rw [Finset.card_filter, Fintype.sum_option]
    congr 1
    · show (if x ⬝ᵥ ((Q - μ • (1 : Matrix (V) (V) ℝ)) *ᵥ x) < 0 then 1 else 0) = _
      rw [lock_norm_x _ x hAx]
    · unfold d
      rw [Finset.card_filter, ← Finset.sum_coe_sort R]
      refine Finset.sum_congr rfl fun s _ => ?_
      obtain ⟨s, hs⟩ := s
      have hiff : (v (some ⟨s, hs⟩) ⬝ᵥ ((Q - μ • (1 : Matrix (V) (V) ℝ))
            *ᵥ v (some ⟨s, hs⟩)) < 0)
          ↔ (s ≠ 0 ∧ 0 < (derivative (P x)).eval s * (P (fun k => b k * x k)).eval s) := by
        rw [show v (some ⟨s, hs⟩) = (fun j => (node j) * x j / ((node j) - s)) from rfl,
          hdot, lock_sign hC μ x hAx s (hslR s hs) (hrootR s hs)]
        exact ⟨fun h => ⟨fun h0 => h0R (by rw [← h0]; exact hs), h⟩, fun h => h.2⟩
      by_cases h1 : v (some ⟨s, hs⟩) ⬝ᵥ ((Q - μ • (1 : Matrix (V) (V) ℝ))
          *ᵥ v (some ⟨s, hs⟩)) < 0
      · rw [if_pos h1, if_pos (hiff.mp h1)]
      · rw [if_neg h1, if_neg (fun h => h1 (hiff.mpr h))]
  rw [← hk, hpb, hcount, Fintype.card_coe, ← hNc]
  omega

end LoewnerLock

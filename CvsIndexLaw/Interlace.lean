import CvsIndexLaw.Loewner

/-!
# Cross-scale interlacing of the lock roots: algebraic core

For a Loewner matrix `Q` (`q_ii = a_i`, `q_ij = (b_i - b_j)/(ν_i - ν_j)`) put
`S = Q D + b ηᵀ` (`η = (1, …, 1)`), entrywise `S i j = q_ij ν_j + b_i`.

* `Spen_isSymm` : `S` is symmetric.
* `Q_Dprime_eq` : in the lock setting `Q x = e₀`, `Q D'_x = S - β ηηᵀ` with
  `β = ⟨b, x⟩ / ⟨η, x⟩`.
* With a reflection `rf` of the nodes (`ν (rf i) = - ν i`), `a` even and `b` odd:
  `Q` is reflection invariant (`Q_rf`), `x` is even (`x_even`), `β = 0`, hence
  `Q D'_x = S` (`Q_Dprime_eq_Spen`): the lock is the symmetric pencil `(S, Q)`.
* `boundary_row` : if `⟨Q y, v⟩ = v_k + v_{rf k}` for every even `v`, then `⟨y, S u⟩ = 0`
  for every odd `u` with `u_k = 0`. This identity gives the triangular form
  `B' = [[B, c], [0, δ]]` and the nesting of the odd-sector operator, from which the
  cross-scale interlacing of the lock roots follows (CVS_ICICE_v02).
-/

set_option linter.style.longLine false

open Matrix Finset

noncomputable section

namespace LoewnerLock

/-- The lock pencil `S = Q D + b ηᵀ`: `S i j = Q i j * ν j + b i`. -/
def Spen {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] (Q : Matrix V V ℝ) (b : V → ℝ) :
    Matrix V V ℝ :=
  Matrix.of fun i j => Q i j * node j + b i

/-- Entrywise commutator: `ν_i q_ij - q_ij ν_j = b_i - b_j`. -/
theorem comm_entry {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] {Q : Matrix V V ℝ} {a b : V → ℝ}
    (hC : IsLoewner Q a b) (i j : V) : node i * Q i j - Q i j * node j = b i - b j := by
  have := congrArg (fun M => M i j) (commutator hC)
  simpa [D, wedge, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.of_apply] using this

/-- `S = Q D + b ηᵀ` is symmetric for every Loewner matrix. -/
theorem Spen_isSymm {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] {Q : Matrix V V ℝ} {a b : V → ℝ}
    (hC : IsLoewner Q a b) : (Spen Q b).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [Spen, Matrix.of_apply]
  rw [(isSymm_of_isCvS hC).apply i j]
  linear_combination comm_entry hC i j

/-- In the lock setting `Q x = e₀`: `Q D'_x = S - β ηηᵀ` with `β = ⟨b, x⟩ / ⟨η, x⟩`. -/
theorem Q_Dprime_eq {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] {Q : Matrix V V ℝ} {a b : V → ℝ}
    (hC : IsLoewner Q a b) (x : V → ℝ) (hx : Q *ᵥ x = Pi.single (z0 V) 1)
    (hc : ∑ k, x k ≠ 0) :
    Q * Dprime (fun _ => (1 : ℝ)) x
      = Spen Q b - ((∑ k, b k * x k) / ∑ k, x k) • Matrix.of fun (_ : V) (_ : V) => (1 : ℝ) := by
  have hcomm := comm_entry hC
  have hv : ∀ i, ∑ k, Q i k * ((node k) * x k) = (∑ k, b k * x k) - b i * ∑ k, x k := by
    intro i
    have h0 : (node i) * ∑ k, Q i k * x k = 0 := by
      have h := congrFun hx i
      simp only [Matrix.mulVec, dotProduct] at h
      rw [h]
      by_cases hi : i = z0 V
      · subst hi
        simp [node_z0]
      · simp [hi]
    have h1 : ∑ k, ((node i) * Q i k - Q i k * (node k)) * x k
        = ∑ k, (b i - b k) * x k :=
      Finset.sum_congr rfl fun k _ => by rw [hcomm i k]
    have e1 : ∑ k, ((node i) * Q i k - Q i k * (node k)) * x k
        = (node i) * ∑ k, Q i k * x k - ∑ k, Q i k * ((node k) * x k) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have e2 : ∑ k, (b i - b k) * x k = b i * ∑ k, x k - ∑ k, b k * x k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e1, e2] at h1
    linarith
  have hentry : ∀ i j, (Q * Dprime (fun _ => (1 : ℝ)) x) i j
      = Q i j * (node j)
        - 1 / (∑ k, (1 : ℝ) * x k) * 1 * ∑ k, Q i k * ((node k) * x k) := by
    intro i j
    rw [Matrix.mul_apply]
    have hk : ∀ k, Q i k * Dprime (fun _ => (1 : ℝ)) x k j
        = (if k = j then Q i k * (node k) else 0)
          - 1 / (∑ k, (1 : ℝ) * x k) * 1 * (Q i k * ((node k) * x k)) := by
      intro k
      simp only [Dprime, D, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply,
        Matrix.of_apply, smul_eq_mul]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    rw [← Finset.mul_sum]
  have hc1 : ∑ k, (1 : ℝ) * x k = ∑ k, x k := by simp
  have hcinv : (∑ k, x k)⁻¹ * (∑ k, x k) = 1 := inv_mul_cancel₀ hc
  ext i j
  rw [hentry i j, hv i, hc1]
  simp only [Spen, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  linear_combination (b i) * hcinv

/-- A reflection of the nodes: an involution `rf` with `ν (rf i) = - ν i`. -/
class Refl (V : Type*) [Nodes V] where
  rf : V → V
  rf_rf : ∀ i, rf (rf i) = i
  node_rf : ∀ i, node (rf i) = - node i

/-- The integer nodes `-N, …, N` carry the reflection `i ↦ -i` (`Fin.rev`). -/
noncomputable instance instReflIdx (N : ℕ) : Refl (CvS.Idx N) where
  rf := Fin.rev
  rf_rf := Fin.rev_rev
  node_rf := fun i => by
    show ((CvS.lab (Fin.rev i) : ℤ) : ℝ) = -((CvS.lab i : ℤ) : ℝ)
    rw [CvS.lab_rev, Int.cast_neg]

/-- The reflection fixes the zero node. -/
theorem rf_z0 {V : Type*} [Nodes V] [Refl V] : Refl.rf (z0 V) = z0 V := by
  apply node_inj
  rw [Refl.node_rf, node_z0, neg_zero]

/-- The reflection as a permutation of the nodes. -/
def rfPerm (V : Type*) [Nodes V] [Refl V] : Equiv.Perm V :=
  Function.Involutive.toPerm Refl.rf Refl.rf_rf

/-- An odd vector is orthogonal to an even one: `∑ b_k ξ_k = 0`. -/
theorem sum_odd_even {V : Type*} [Fintype V] [Nodes V] [Refl V] (b ξ : V → ℝ)
    (hb : ∀ i, b (Refl.rf i) = - b i) (hξ : ∀ i, ξ (Refl.rf i) = ξ i) :
    ∑ k, b k * ξ k = 0 := by
  have h : ∑ k, b (Refl.rf k) * ξ (Refl.rf k) = ∑ k, b k * ξ k :=
    Fintype.sum_equiv (rfPerm V) _ _ (fun k => rfl)
  simp only [hb, hξ, neg_mul, Finset.sum_neg_distrib] at h
  linarith

/-- With `a` even and `b` odd, a Loewner matrix is invariant under the reflection. -/
theorem Q_rf {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] [Refl V] {Q : Matrix V V ℝ} {a b : V → ℝ}
    (hC : IsLoewner Q a b) (ha : ∀ i, a (Refl.rf i) = a i) (hb : ∀ i, b (Refl.rf i) = - b i)
    (i j : V) : Q (Refl.rf i) (Refl.rf j) = Q i j := by
  by_cases h : i = j
  · subst h
    rw [hC.diag, hC.diag, ha]
  · have h' : Refl.rf i ≠ Refl.rf j := fun e => h (by
      have e' := congrArg Refl.rf e
      rwa [Refl.rf_rf, Refl.rf_rf] at e')
    rw [hC.off _ _ h', hC.off _ _ h, hb, hb, Refl.node_rf, Refl.node_rf]
    have e1 : -b i - -b j = -(b i - b j) := by ring
    have e2 : -node i - -node j = -(node i - node j) := by ring
    rw [e1, e2, neg_div_neg_eq]

/-- In the lock setting `Q x = e₀`, with `Q` reflection invariant and `Q *ᵥ ·` injective,
the vector `x` is even. -/
theorem x_even {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] [Refl V] {Q : Matrix V V ℝ}
    (hQ : ∀ i j, Q (Refl.rf i) (Refl.rf j) = Q i j) (hinj : Function.Injective (Q *ᵥ ·))
    (x : V → ℝ) (hx : Q *ᵥ x = Pi.single (z0 V) 1) : ∀ i, x (Refl.rf i) = x i := by
  have key : (Q *ᵥ fun i => x (Refl.rf i)) = Q *ᵥ x := by
    ext i
    have hs : ∑ j, Q i j * x (Refl.rf j) = ∑ j, Q (Refl.rf i) j * x j := by
      have h : ∑ j, Q (Refl.rf i) (Refl.rf j) * x (Refl.rf j) = ∑ j, Q (Refl.rf i) j * x j :=
        Fintype.sum_equiv (rfPerm V) _ _ (fun j => rfl)
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hQ i j]
    have hxi := congrFun hx (Refl.rf i)
    have hxi' := congrFun hx i
    simp only [Matrix.mulVec, dotProduct] at hxi hxi' ⊢
    rw [hs, hxi, hxi']
    by_cases hi : i = z0 V
    · subst hi
      rw [rf_z0]
    · have hne : Refl.rf i ≠ z0 V := by
        intro e
        apply hi
        calc i = Refl.rf (Refl.rf i) := (Refl.rf_rf i).symm
          _ = Refl.rf (z0 V) := by rw [e]
          _ = z0 V := rf_z0
      simp [Pi.single_apply, hi, hne]
  exact fun i => congrFun (hinj key) i

/-- Under parity (`a` even, `b` odd, reflected nodes) the lock is the symmetric pencil
`(S, Q)`: `Q D'_x = S`. -/
theorem Q_Dprime_eq_Spen {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] [Refl V]
    {Q : Matrix V V ℝ} {a b : V → ℝ} (hC : IsLoewner Q a b)
    (ha : ∀ i, a (Refl.rf i) = a i) (hb : ∀ i, b (Refl.rf i) = - b i)
    (hinj : Function.Injective (Q *ᵥ ·)) (x : V → ℝ) (hx : Q *ᵥ x = Pi.single (z0 V) 1)
    (hc : ∑ k, x k ≠ 0) :
    Q * Dprime (fun _ => (1 : ℝ)) x = Spen Q b := by
  have hxe := x_even (Q_rf hC ha hb) hinj x hx
  have h0 := sum_odd_even b x hb hxe
  rw [Q_Dprime_eq hC x hx hc, h0, zero_div, zero_smul, sub_zero]

/-- Boundary row. If `⟨Q y, v⟩ = v_k + v_{rf k}` for every even `v`, then `⟨y, S u⟩ = 0`
for every odd `u` with `u_k = 0`. -/
theorem boundary_row {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] [Refl V]
    {Q : Matrix V V ℝ} {a b : V → ℝ} (hC : IsLoewner Q a b) (k : V) (y u : V → ℝ)
    (hyQ : ∀ v : V → ℝ, (∀ i, v (Refl.rf i) = v i) → dotProduct (Q *ᵥ y) v = v k + v (Refl.rf k))
    (hu : ∀ i, u (Refl.rf i) = - u i) (huk : u k = 0) :
    dotProduct y (Spen Q b *ᵥ u) = 0 := by
  have hs := isSymm_of_isCvS hC
  have hu0 : ∑ j, u j = 0 := by
    have h := sum_odd_even u (fun _ => (1 : ℝ)) hu (fun _ => rfl)
    simpa using h
  have hDu : ∀ i, node (Refl.rf i) * u (Refl.rf i) = node i * u i := by
    intro i
    rw [Refl.node_rf, hu]
    ring
  have h1 : dotProduct (Q *ᵥ y) (fun j => node j * u j)
      = node k * u k + node (Refl.rf k) * u (Refl.rf k) := hyQ (fun j => node j * u j) hDu
  have hk : node k * u k + node (Refl.rf k) * u (Refl.rf k) = 0 := by
    rw [Refl.node_rf, hu, huk]
    ring
  -- ⟨y, S u⟩ = Σ_i Σ_j (q_ji y_i ν_j u_j + y_i b_i u_j), using q_ji = q_ij.
  have eL : dotProduct y (Spen Q b *ᵥ u)
      = ∑ i, ∑ j, (Q j i * y i * (node j * u j) + y i * b i * u j) := by
    simp only [dotProduct, Matrix.mulVec, Spen, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hs.apply i j]
    ring
  have eR1 : dotProduct (Q *ᵥ y) (fun j => node j * u j)
      = ∑ j, ∑ i, Q j i * y i * (node j * u j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
  have eR2 : (∑ i, y i * b i) * ∑ j, u j = ∑ i, ∑ j, y i * b i * u j := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hswap : ∑ j, ∑ i, Q j i * y i * (node j * u j)
      = ∑ i, ∑ j, Q j i * y i * (node j * u j) := Finset.sum_comm
  have expand : dotProduct y (Spen Q b *ᵥ u)
      = dotProduct (Q *ᵥ y) (fun j => node j * u j) + (∑ i, y i * b i) * ∑ j, u j := by
    rw [eL, eR1, eR2, hswap, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_add_distrib]
  rw [expand, h1, hk, hu0, mul_zero, add_zero]

end LoewnerLock

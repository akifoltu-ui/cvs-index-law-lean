/-
Copyright (c) 2026 Mehmet Akif Oltulu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mehmet Akif Oltulu
-/
import Mathlib

/-!
# Parity transport for Cauchy forms on reflection-symmetric nodes

Nodes `0, ±x 1, …, ±x M` with `x j ≠ 0`. For a node vector `c` and a pole `p` the Cauchy
transform is `cauchy x c p = ∑_n c_n / (p - ν_n)`. A finite family of poles `p k` with weights
`w k ≥ 0` gives the form `form x w p c = ∑_k w_k (cauchy x c (p k))²`; with poles in pairs `±a`
this is the zero side of a truncated Weil form. The even sector uses the basis `δ_0`,
`δ_{x_j} + δ_{-x_j}` (`evenVec`), the odd sector `δ_{x_j} - δ_{-x_j}` (`oddVec`).

* `transport_cauchy` : the transport `T z = (-2 ∑_j z_j / x_j ; z_j / x_j)` sends every odd
  vector to an even vector whose Cauchy transform at every pole is the odd one divided by the
  pole: `cauchy (E (T z)) p = cauchy (O z) p / p`. The extra centre coefficient cancels the top
  term of the even rational function.
* `transport_le` : hence `r · form (E (T z)) ≤ form (O z)` whenever `r ≤ p_k²` for all poles.
* `odd_le_even` : `‖O z‖² ≤ X · ‖E (T z)‖²` whenever `x_j² ≤ X` for all nodes.
* `rayleigh_transport`, `order_of_norm_bound` : with a norm bound of constant `X < r`, the
  transported even vector has a strictly smaller Rayleigh quotient than the odd vector.
* `band_out_order` : all poles beyond all nodes (`x_j² ≤ X < r ≤ p_k²`) suffice. Taking for `z`
  a lowest odd eigenvector, the lowest even eigenvalue lies strictly below the lowest odd one.
* `sharp_two_bound`, `sharp_two_order` : for the integer nodes `0, ±1, ±2` the norm constant
  `X = 5000/1849 = 2.70416…` works (the sharp value is `(15 + √145)/10 = 2.70415…`), so poles with
  `p_k² > 5000/1849`, i.e. `|p_k| > 1.64444`, suffice.
-/

set_option linter.style.longLine false

open Finset

noncomputable section

namespace LoewnerLock

namespace Transport

variable {M : ℕ}

/-- Node labels: the centre, the positive copies and the negative copies. -/
abbrev Node (M : ℕ) := Fin 1 ⊕ (Fin M ⊕ Fin M)

/-- Node values `0`, `x j`, `-x j`. -/
def nu (x : Fin M → ℝ) : Node M → ℝ :=
  Sum.elim (fun _ => 0) (Sum.elim x fun j => -x j)

/-- Cauchy transform of a node vector at a pole `p`. -/
def cauchy (x : Fin M → ℝ) (c : Node M → ℝ) (p : ℝ) : ℝ :=
  ∑ n, c n / (p - nu x n)

/-- Even vector `y0 δ_0 + ∑_j y_j (δ_{x_j} + δ_{-x_j})`. -/
def evenVec (y0 : ℝ) (y : Fin M → ℝ) : Node M → ℝ :=
  Sum.elim (fun _ => y0) (Sum.elim y y)

/-- Odd vector `∑_j z_j (δ_{x_j} - δ_{-x_j})`. -/
def oddVec (z : Fin M → ℝ) : Node M → ℝ :=
  Sum.elim (fun _ => 0) (Sum.elim z fun j => -z j)

/-- Centre coefficient of the transport. -/
def tCentre (x z : Fin M → ℝ) : ℝ := -2 * ∑ j, z j / x j

/-- Positive-node coefficients of the transport. -/
def tPos (x z : Fin M → ℝ) : Fin M → ℝ := fun j => z j / x j

/-- The form of a finite weighted pole family. -/
def form (x : Fin M → ℝ) {K : ℕ} (w p : Fin K → ℝ) (c : Node M → ℝ) : ℝ :=
  ∑ k, w k * cauchy x c (p k) ^ 2

/-- Squared Euclidean norm of a node vector. -/
def nsq (c : Node M → ℝ) : ℝ := ∑ n, c n ^ 2

theorem sq_sub_sq_ne (p a : ℝ) (h₁ : p - a ≠ 0) (h₂ : p + a ≠ 0) : p ^ 2 - a ^ 2 ≠ 0 := by
  have h : p ^ 2 - a ^ 2 = (p - a) * (p + a) := by ring
  rw [h]
  exact mul_ne_zero h₁ h₂

/-- Cauchy transform of an even vector. -/
theorem cauchy_evenVec (x y : Fin M → ℝ) (y0 p : ℝ) (h₁ : ∀ j, p - x j ≠ 0)
    (h₂ : ∀ j, p + x j ≠ 0) :
    cauchy x (evenVec y0 y) p = y0 / p + ∑ j, y j * (2 * p / (p ^ 2 - x j ^ 2)) := by
  simp only [cauchy, evenVec, nu, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fin.sum_univ_one, sub_zero, sub_neg_eq_add]
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have a1 := h₁ j
  have a2 := h₂ j
  have a3 := sq_sub_sq_ne p (x j) a1 a2
  first
    | (field_simp; ring)
    | field_simp

/-- Cauchy transform of an odd vector. -/
theorem cauchy_oddVec (x z : Fin M → ℝ) (p : ℝ) (h₁ : ∀ j, p - x j ≠ 0)
    (h₂ : ∀ j, p + x j ≠ 0) :
    cauchy x (oddVec z) p = ∑ j, z j * (2 * x j / (p ^ 2 - x j ^ 2)) := by
  simp only [cauchy, oddVec, nu, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fin.sum_univ_one, sub_zero, sub_neg_eq_add, zero_div, zero_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have a1 := h₁ j
  have a2 := h₂ j
  have a3 := sq_sub_sq_ne p (x j) a1 a2
  first
    | (field_simp; ring)
    | field_simp

/-- **Transport identity** in sector coordinates. -/
theorem transport (x z : Fin M → ℝ) (p : ℝ) (hp : p ≠ 0) (hx : ∀ j, x j ≠ 0)
    (hq : ∀ j, p ^ 2 - x j ^ 2 ≠ 0) :
    tCentre x z / p + ∑ j, tPos x z j * (2 * p / (p ^ 2 - x j ^ 2))
      = (∑ j, z j * (2 * x j / (p ^ 2 - x j ^ 2))) / p := by
  simp only [tCentre, tPos]
  rw [Finset.mul_sum, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have a1 := hx j
  have a2 := hq j
  first
    | (field_simp; ring)
    | field_simp

/-- **Transport identity** on the nodes: `cauchy (E (T z)) p = cauchy (O z) p / p`. -/
theorem transport_cauchy (x z : Fin M → ℝ) (p : ℝ) (hp : p ≠ 0) (hx : ∀ j, x j ≠ 0)
    (h₁ : ∀ j, p - x j ≠ 0) (h₂ : ∀ j, p + x j ≠ 0) :
    cauchy x (evenVec (tCentre x z) (tPos x z)) p = cauchy x (oddVec z) p / p := by
  rw [cauchy_evenVec x (tPos x z) (tCentre x z) p h₁ h₂, cauchy_oddVec x z p h₁ h₂]
  exact transport x z p hp hx fun j => sq_sub_sq_ne p (x j) (h₁ j) (h₂ j)

theorem form_nonneg (x : Fin M → ℝ) {K : ℕ} (w p : Fin K → ℝ) (hw : ∀ k, 0 ≤ w k)
    (c : Node M → ℝ) : 0 ≤ form x w p c := by
  unfold form
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (sq_nonneg _)

theorem nsq_nonneg (c : Node M → ℝ) : 0 ≤ nsq c := by
  unfold nsq
  exact Finset.sum_nonneg fun n _ => sq_nonneg _

theorem nsq_evenVec (y0 : ℝ) (y : Fin M → ℝ) :
    nsq (evenVec y0 y) = y0 ^ 2 + 2 * ∑ j, y j ^ 2 := by
  simp only [nsq, evenVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one]
  ring

theorem nsq_oddVec (z : Fin M → ℝ) : nsq (oddVec z) = 2 * ∑ j, z j ^ 2 := by
  simp only [nsq, oddVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one,
    neg_sq]
  ring

/-- **Form inequality**: `r · form (E (T z)) ≤ form (O z)` when `r ≤ p_k²` for every pole. -/
theorem transport_le (x z : Fin M → ℝ) {K : ℕ} (w p : Fin K → ℝ) (hx : ∀ j, x j ≠ 0)
    (hp0 : ∀ k, p k ≠ 0) (h₁ : ∀ k j, p k - x j ≠ 0) (h₂ : ∀ k j, p k + x j ≠ 0)
    (hw : ∀ k, 0 ≤ w k) (r : ℝ) (hr : ∀ k, r ≤ p k ^ 2) :
    r * form x w p (evenVec (tCentre x z) (tPos x z)) ≤ form x w p (oddVec z) := by
  unfold form
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [transport_cauchy x z (p k) (hp0 k) hx (h₁ k) (h₂ k)]
  have hpk := hp0 k
  have key : w k * cauchy x (oddVec z) (p k) ^ 2
        - r * (w k * (cauchy x (oddVec z) (p k) / p k) ^ 2)
      = w k * (cauchy x (oddVec z) (p k) / p k) ^ 2 * (p k ^ 2 - r) := by
    first
      | (field_simp; ring)
      | field_simp
  have h := mul_nonneg (mul_nonneg (hw k) (sq_nonneg (cauchy x (oddVec z) (p k) / p k)))
    (sub_nonneg.mpr (hr k))
  linarith

/-- **Norm bound**: `‖O z‖² ≤ X · ‖E (T z)‖²` when `x_j² ≤ X` for every node. -/
theorem odd_le_even (x z : Fin M → ℝ) (hx : ∀ j, x j ≠ 0) (X : ℝ) (hX0 : 0 ≤ X)
    (hX : ∀ j, x j ^ 2 ≤ X) :
    nsq (oddVec z) ≤ X * nsq (evenVec (tCentre x z) (tPos x z)) := by
  rw [nsq_oddVec, nsq_evenVec]
  have hterm : ∀ j, z j ^ 2 ≤ X * tPos x z j ^ 2 := by
    intro j
    have a1 := hx j
    have hx2 : 0 < x j ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 a1))
    have key : X * tPos x z j ^ 2 - z j ^ 2 = z j ^ 2 * (X - x j ^ 2) / x j ^ 2 := by
      simp only [tPos]
      first
        | (field_simp; ring)
        | field_simp
    have hnn : 0 ≤ z j ^ 2 * (X - x j ^ 2) / x j ^ 2 :=
      div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (hX j))) (le_of_lt hx2)
    linarith
  have hsum : ∑ j, z j ^ 2 ≤ X * ∑ j, tPos x z j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hterm j
  have ht : 0 ≤ X * tCentre x z ^ 2 := mul_nonneg hX0 (sq_nonneg _)
  calc 2 * ∑ j, z j ^ 2 ≤ 2 * (X * ∑ j, tPos x z j ^ 2) := by linarith
    _ ≤ X * tCentre x z ^ 2 + 2 * (X * ∑ j, tPos x z j ^ 2) := by linarith
    _ = X * (tCentre x z ^ 2 + 2 * ∑ j, tPos x z j ^ 2) := by ring

/-- **Rayleigh comparison** (cross-multiplied): from a norm bound with constant `X`,
`r · R(E (T z)) ≤ X · R(O z)` for the Rayleigh quotients `R = form / nsq`. -/
theorem rayleigh_transport (x z : Fin M → ℝ) {K : ℕ} (w p : Fin K → ℝ) (hx : ∀ j, x j ≠ 0)
    (hp0 : ∀ k, p k ≠ 0) (h₁ : ∀ k j, p k - x j ≠ 0) (h₂ : ∀ k j, p k + x j ≠ 0)
    (hw : ∀ k, 0 ≤ w k) (r X : ℝ) (hr : ∀ k, r ≤ p k ^ 2)
    (hN : nsq (oddVec z) ≤ X * nsq (evenVec (tCentre x z) (tPos x z))) :
    r * (form x w p (evenVec (tCentre x z) (tPos x z)) * nsq (oddVec z))
      ≤ X * (form x w p (oddVec z) * nsq (evenVec (tCentre x z) (tPos x z))) := by
  have h1 := transport_le x z w p hx hp0 h₁ h₂ hw r hr
  have hO := form_nonneg x w p hw (oddVec z)
  have hB := nsq_nonneg (oddVec z)
  calc r * (form x w p (evenVec (tCentre x z) (tPos x z)) * nsq (oddVec z))
      = (r * form x w p (evenVec (tCentre x z) (tPos x z))) * nsq (oddVec z) := by ring
    _ ≤ form x w p (oddVec z) * nsq (oddVec z) := by
        first
          | exact mul_le_mul_of_nonneg_right h1 hB
          | nlinarith [h1, hB]
    _ ≤ form x w p (oddVec z) * (X * nsq (evenVec (tCentre x z) (tPos x z))) := by
        first
          | exact mul_le_mul_of_nonneg_left hN hO
          | nlinarith [hN, hO]
    _ = X * (form x w p (oddVec z) * nsq (evenVec (tCentre x z) (tPos x z))) := by ring

/-- **Strict ordering** from a norm bound with constant `X < r`: the transported even vector
has a strictly smaller Rayleigh quotient than the odd vector. -/
theorem order_of_norm_bound (x z : Fin M → ℝ) {K : ℕ} (w p : Fin K → ℝ) (hx : ∀ j, x j ≠ 0)
    (hp0 : ∀ k, p k ≠ 0) (h₁ : ∀ k j, p k - x j ≠ 0) (h₂ : ∀ k j, p k + x j ≠ 0)
    (hw : ∀ k, 0 ≤ w k) (r X : ℝ) (hr : ∀ k, r ≤ p k ^ 2) (hX0 : 0 ≤ X) (hXr : X < r)
    (hN : nsq (oddVec z) ≤ X * nsq (evenVec (tCentre x z) (tPos x z)))
    (hpos : 0 < form x w p (oddVec z)) (hz : 0 < nsq (oddVec z)) :
    form x w p (evenVec (tCentre x z) (tPos x z)) * nsq (oddVec z)
      < form x w p (oddVec z) * nsq (evenVec (tCentre x z) (tPos x z)) := by
  have hR := rayleigh_transport x z w p hx hp0 h₁ h₂ hw r X hr hN
  have hE : 0 < nsq (evenVec (tCentre x z) (tPos x z)) := by
    by_contra hcon
    have h : nsq (evenVec (tCentre x z) (tPos x z)) ≤ 0 := not_lt.mp hcon
    have h5 : X * nsq (evenVec (tCentre x z) (tPos x z)) ≤ X * 0 :=
      mul_le_mul_of_nonneg_left h hX0
    rw [mul_zero] at h5
    linarith
  have hr0 : 0 < r := lt_of_le_of_lt hX0 hXr
  have hprod : 0 < form x w p (oddVec z) * nsq (evenVec (tCentre x z) (tPos x z)) :=
    mul_pos hpos hE
  have h3 : X * (form x w p (oddVec z) * nsq (evenVec (tCentre x z) (tPos x z)))
      < r * (form x w p (oddVec z) * nsq (evenVec (tCentre x z) (tPos x z))) :=
    mul_lt_mul_of_pos_right hXr hprod
  first
    | exact lt_of_mul_lt_mul_left (lt_of_le_of_lt hR h3) (le_of_lt hr0)
    | nlinarith [hR, h3, hr0, hprod]

/-- **Band-out ordering**: if every pole lies beyond every node (`x_j² ≤ X < r ≤ p_k²`), the
transported even vector has a strictly smaller Rayleigh quotient than the odd vector. -/
theorem band_out_order (x z : Fin M → ℝ) {K : ℕ} (w p : Fin K → ℝ) (hx : ∀ j, x j ≠ 0)
    (hp0 : ∀ k, p k ≠ 0) (h₁ : ∀ k j, p k - x j ≠ 0) (h₂ : ∀ k j, p k + x j ≠ 0)
    (hw : ∀ k, 0 ≤ w k) (r X : ℝ) (hr : ∀ k, r ≤ p k ^ 2) (hX0 : 0 ≤ X)
    (hX : ∀ j, x j ^ 2 ≤ X) (hXr : X < r)
    (hpos : 0 < form x w p (oddVec z)) (hz : 0 < nsq (oddVec z)) :
    form x w p (evenVec (tCentre x z) (tPos x z)) * nsq (oddVec z)
      < form x w p (oddVec z) * nsq (evenVec (tCentre x z) (tPos x z)) :=
  order_of_norm_bound x z w p hx hp0 h₁ h₂ hw r X hr hX0 hXr (odd_le_even x z hx X hX0 hX)
    hpos hz

/-- The integer nodes `0, ±1, ±2`. -/
def xTwo : Fin 2 → ℝ := ![1, 2]

theorem xTwo_ne : ∀ j : Fin 2, xTwo j ≠ 0 := by
  first
    | (rw [Fin.forall_fin_two]; norm_num [xTwo])
    | (intro j; fin_cases j <;> norm_num [xTwo])

/-- **Sharp norm constant for `M = 2`**: `‖O z‖² ≤ (5000/1849) · ‖E (T z)‖²`.
Certificate: `26302 · 1849 · (rhs - lhs) = (26302 z₀ + 10000 z₁)² + 204 z₁²`. -/
theorem sharp_two_bound (z : Fin 2 → ℝ) :
    nsq (oddVec z) ≤ (5000 / 1849 : ℝ) * nsq (evenVec (tCentre xTwo z) (tPos xTwo z)) := by
  rw [nsq_oddVec, nsq_evenVec]
  first
    | (simp only [tCentre, tPos, xTwo, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons];
       nlinarith [sq_nonneg (26302 * z 0 + 10000 * z 1), sq_nonneg (z 1)])
    | (norm_num [tCentre, tPos, xTwo, Fin.sum_univ_two];
       nlinarith [sq_nonneg (26302 * z 0 + 10000 * z 1), sq_nonneg (z 1)])

/-- **Sharp ordering for `M = 2`**: on the nodes `0, ±1, ±2`, poles with
`p_k² > 5000/1849` (`|p_k| > 1.64444`) already give the strict ordering. -/
theorem sharp_two_order (z : Fin 2 → ℝ) {K : ℕ} (w p : Fin K → ℝ) (hp0 : ∀ k, p k ≠ 0)
    (h₁ : ∀ k j, p k - xTwo j ≠ 0) (h₂ : ∀ k j, p k + xTwo j ≠ 0) (hw : ∀ k, 0 ≤ w k)
    (r : ℝ) (hr : ∀ k, r ≤ p k ^ 2) (hr2 : (5000 / 1849 : ℝ) < r)
    (hpos : 0 < form xTwo w p (oddVec z)) (hz : 0 < nsq (oddVec z)) :
    form xTwo w p (evenVec (tCentre xTwo z) (tPos xTwo z)) * nsq (oddVec z)
      < form xTwo w p (oddVec z) * nsq (evenVec (tCentre xTwo z) (tPos xTwo z)) :=
  order_of_norm_bound xTwo z w p xTwo_ne hp0 h₁ h₂ hw r (5000 / 1849) hr (by norm_num) hr2
    (sharp_two_bound z) hpos hz

end Transport

end LoewnerLock

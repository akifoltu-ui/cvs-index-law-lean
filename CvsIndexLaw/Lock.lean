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

/-- Warm-up target: a CvS matrix is symmetric. -/
theorem isSymm_of_isCvS {N : ℕ} {Q : Matrix (Idx N) (Idx N) ℝ} {a b : Idx N → ℝ}
    (hC : IsCvS Q a b) : Q.IsSymm := by
  sorry

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

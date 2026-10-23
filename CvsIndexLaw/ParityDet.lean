import CvsIndexLaw.Interlace

/-!
# The parity determinant identity for reflection-symmetric Loewner matrices

Nodes `0, ±x 1, …, ±x M` with `x i ≠ 0`, `x i ≠ x j` (`i ≠ j`) and `x i + x j ≠ 0`; a Loewner
matrix `q_ii = a_i`, `q_ij = (b_i - b_j)/(ν_i - ν_j)` with `a` even and `b` odd. In the
(unnormalised) bases `e_0 = δ_0`, `e_j = δ_{x_j} + δ_{-x_j}` (even) and `o_j = δ_{x_j} - δ_{-x_j}`
(odd) the two reflection sectors of the matrix are `Aeven` (centre node first) and `Aodd`;
`ParityDetLink.lean` reads them off any `IsLoewner` matrix with a reflection.

* `rowC_mul_diag`, `intertwine` : the odd-to-even intertwining
  `(Aeven - μ) D_eo = D_eo (Aodd - μ) + η (2b)ᵀ`, `D_eo = [0; diag x]`, block by block.
  It is the odd-even block of the commutator `[D, Q] = b ηᵀ - η bᵀ`.
* `det_odd_eq` : for every `μ`, `det (Aodd - μ) = det (Nmat μ)`, where `Nmat μ` is `Aeven - μ`
  with its centre column replaced by `η = (1, …, 1)`.

Reading (Cramer): `det (Aodd - μ) / det (Aeven - μ) = ((Aeven - μ)⁻¹ η)_0`, so the odd spectrum is
the zero set of `H(μ) = Σ_k (φ_k)_0 ⟨η, φ_k⟩ / (λ_k - μ)` built from the even spectrum.
-/

set_option linter.style.longLine false

open Matrix Finset

noncomputable section

namespace LoewnerLock

namespace ParityDet

variable {M : ℕ}

/-- Odd sector in the basis `o_j = δ_{x_j} - δ_{-x_j}`. -/
def Aodd (x b a : Fin M → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  Matrix.of fun i j => if i = j then a i - b i / x i
    else (b i - b j) / (x i - x j) - (b i + b j) / (x i + x j)

/-- Even sector on the positive nodes, basis `e_j = δ_{x_j} + δ_{-x_j}`. -/
def Aee (x b a : Fin M → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  Matrix.of fun i j => if i = j then a i + b i / x i
    else (b i - b j) / (x i - x j) + (b i + b j) / (x i + x j)

/-- Centre row of the even sector. -/
def rowC (x b : Fin M → ℝ) : Matrix (Fin 1) (Fin M) ℝ :=
  Matrix.of fun _ j => 2 * b j / x j

/-- Centre column of the even sector. -/
def colC (x b : Fin M → ℝ) : Matrix (Fin M) (Fin 1) ℝ :=
  Matrix.of fun i _ => b i / x i

/-- The even sector, centre node first. -/
def Aeven (x b a : Fin M → ℝ) (a0 : ℝ) : Matrix (Fin 1 ⊕ Fin M) (Fin 1 ⊕ Fin M) ℝ :=
  Matrix.fromBlocks (Matrix.of fun _ _ => a0) (rowC x b) (colC x b) (Aee x b a)

/-- The all-ones column `η`. -/
def onesCol (M : ℕ) : Matrix (Fin M) (Fin 1) ℝ :=
  Matrix.of fun _ _ => 1

/-- The row `2 bᵀ`. -/
def twoB (b : Fin M → ℝ) : Matrix (Fin 1) (Fin M) ℝ :=
  Matrix.of fun _ j => 2 * b j

/-- `Aeven - μ` with its centre column replaced by `η = (1, …, 1)`. -/
def Nmat (x b a : Fin M → ℝ) (μ : ℝ) : Matrix (Fin 1 ⊕ Fin M) (Fin 1 ⊕ Fin M) ℝ :=
  Matrix.fromBlocks 1 (rowC x b) (onesCol M) (Aee x b a - μ • (1 : Matrix (Fin M) (Fin M) ℝ))

/-- Centre row of the intertwining: `rowC · diag x = 2 bᵀ`. -/
theorem rowC_mul_diag (x b : Fin M → ℝ) (hx : ∀ i, x i ≠ 0) :
    rowC x b * diagonal x = twoB b := by
  ext i j
  have hj : x j ≠ 0 := hx j
  simp only [rowC, twoB, Matrix.mul_diagonal, Matrix.of_apply]
  first
    | (field_simp; ring)
    | field_simp

/-- Positive-node block of the intertwining:
`(Aee - μ) · diag x = η (2b)ᵀ + diag x · (Aodd - μ)`. -/
theorem intertwine (x b a : Fin M → ℝ) (μ : ℝ) (hx : ∀ i, x i ≠ 0)
    (hd : ∀ i j, i ≠ j → x i - x j ≠ 0) (hs : ∀ i j, x i + x j ≠ 0) :
    (Aee x b a - μ • (1 : Matrix (Fin M) (Fin M) ℝ)) * diagonal x
      = onesCol M * twoB b + diagonal x * (Aodd x b a - μ • (1 : Matrix (Fin M) (Fin M) ℝ)) := by
  ext i j
  rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply,
    Fin.sum_univ_one]
  simp only [Aee, Aodd, onesCol, twoB, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, smul_eq_mul]
  have hxi : x i ≠ 0 := hx i
  have hxj : x j ≠ 0 := hx j
  by_cases h : i = j
  · subst h
    simp only [eq_self_iff_true, if_true]
    first
      | (field_simp; ring)
      | field_simp
  · have h1 : x i - x j ≠ 0 := hd i j h
    have h2 : x i + x j ≠ 0 := hs i j
    simp only [h, if_false]
    first
      | (field_simp; ring)
      | field_simp

/-- **Parity determinant identity.** For every `μ`, the characteristic determinant of the odd
sector equals the determinant of `Aeven - μ` with its centre column replaced by `η`. -/
theorem det_odd_eq (x b a : Fin M → ℝ) (μ : ℝ) (hx : ∀ i, x i ≠ 0)
    (hd : ∀ i j, i ≠ j → x i - x j ≠ 0) (hs : ∀ i j, x i + x j ≠ 0) :
    (Aodd x b a - μ • (1 : Matrix (Fin M) (Fin M) ℝ)).det = (Nmat x b a μ).det := by
  have key :
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 (onesCol M)
          (diagonal x * (Aodd x b a - μ • (1 : Matrix (Fin M) (Fin M) ℝ)))
        * Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) (twoB b) 0 (1 : Matrix (Fin M) (Fin M) ℝ)
      = Nmat x b a μ * Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (diagonal x) := by
    rw [Nmat, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      intertwine x b a μ hx hd hs]
    congr 1
    all_goals simp [rowC_mul_diag x b hx]
  have hdet := congrArg Matrix.det key
  simp only [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_diagonal, Matrix.det_one, one_mul, mul_one] at hdet
  have hP : (∏ i, x i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hx i
  apply mul_left_cancel₀ hP
  linear_combination hdet

end ParityDet

end LoewnerLock

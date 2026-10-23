/-
  kontrol/ParityDetKontrol.lean  v1.0 -- negative control for CvsIndexLaw/ParityDet*.lean
  Run:  lake env lean kontrol/ParityDetKontrol.lean
  Expected: exactly THREE errors, one per CORRUPTED block; every CORRECT block is accepted.
  Each corrupted statement is numerically false (parite_det_dogrula_v1.py, 60 random cases:
  median deviation 0.53 / 2.95 / 0.33), so the errors separate true from false statements.
-/
import CvsIndexLaw

open Matrix

-- CORRECT input: the parity determinant identity.
example {M : ℕ} (x b a : Fin M → ℝ) (μ : ℝ) (hx : ∀ i, x i ≠ 0)
    (hd : ∀ i j, i ≠ j → x i - x j ≠ 0) (hs : ∀ i j, x i + x j ≠ 0) :
    (LoewnerLock.ParityDet.Aodd x b a - μ • (1 : Matrix (Fin M) (Fin M) ℝ)).det
      = (LoewnerLock.ParityDet.Nmat x b a μ).det :=
  LoewnerLock.ParityDet.det_odd_eq x b a μ hx hd hs

-- CORRUPTED input: the even block in place of the odd one. This must FAIL.
example {M : ℕ} (x b a : Fin M → ℝ) (μ : ℝ) (hx : ∀ i, x i ≠ 0)
    (hd : ∀ i j, i ≠ j → x i - x j ≠ 0) (hs : ∀ i j, x i + x j ≠ 0) :
    (LoewnerLock.ParityDet.Aee x b a - μ • (1 : Matrix (Fin M) (Fin M) ℝ)).det
      = (LoewnerLock.ParityDet.Nmat x b a μ).det :=
  LoewnerLock.ParityDet.det_odd_eq x b a μ hx hd hs

-- CORRECT input: the intertwining block.
example {M : ℕ} (x b a : Fin M → ℝ) (μ : ℝ) (hx : ∀ i, x i ≠ 0)
    (hd : ∀ i j, i ≠ j → x i - x j ≠ 0) (hs : ∀ i j, x i + x j ≠ 0) :
    (LoewnerLock.ParityDet.Aee x b a - μ • (1 : Matrix (Fin M) (Fin M) ℝ)) * diagonal x
      = LoewnerLock.ParityDet.onesCol M * LoewnerLock.ParityDet.twoB b
        + diagonal x * (LoewnerLock.ParityDet.Aodd x b a - μ • (1 : Matrix (Fin M) (Fin M) ℝ)) :=
  LoewnerLock.ParityDet.intertwine x b a μ hx hd hs

-- CORRUPTED input: the intertwining without the η (2b)ᵀ term. This must FAIL.
example {M : ℕ} (x b a : Fin M → ℝ) (μ : ℝ) (hx : ∀ i, x i ≠ 0)
    (hd : ∀ i j, i ≠ j → x i - x j ≠ 0) (hs : ∀ i j, x i + x j ≠ 0) :
    (LoewnerLock.ParityDet.Aee x b a - μ • (1 : Matrix (Fin M) (Fin M) ℝ)) * diagonal x
      = diagonal x * (LoewnerLock.ParityDet.Aodd x b a - μ • (1 : Matrix (Fin M) (Fin M) ℝ)) :=
  LoewnerLock.ParityDet.intertwine x b a μ hx hd hs

-- CORRECT input: the identity read on a reflection-symmetric IsLoewner matrix.
example {V : Type*} [Fintype V] [DecidableEq V] [LoewnerLock.Nodes V] [LoewnerLock.Refl V]
    {Q : Matrix V V ℝ} {a b : V → ℝ} (hC : LoewnerLock.IsLoewner Q a b)
    (hb : ∀ i, b (LoewnerLock.Refl.rf i) = - b i) {M : ℕ} (pos : Fin M → V)
    (hpos : ∀ j, 0 < LoewnerLock.Nodes.node (pos j)) (hinj : Function.Injective pos) (μ : ℝ) :
    (LoewnerLock.ParityDet.Qodd Q pos - μ • (1 : Matrix (Fin M) (Fin M) ℝ)).det
      = (LoewnerLock.ParityDet.Qn Q pos μ).det :=
  LoewnerLock.ParityDet.det_Qodd_eq hC hb pos hpos hinj μ

-- CORRUPTED input: the centre row without its factor 2. This must FAIL.
example {M : ℕ} (x b a : Fin M → ℝ) (μ : ℝ) (hx : ∀ i, x i ≠ 0)
    (hd : ∀ i j, i ≠ j → x i - x j ≠ 0) (hs : ∀ i j, x i + x j ≠ 0) :
    (LoewnerLock.ParityDet.Aodd x b a - μ • (1 : Matrix (Fin M) (Fin M) ℝ)).det
      = (Matrix.fromBlocks 1 (Matrix.of fun (_ : Fin 1) j => b j / x j) (LoewnerLock.ParityDet.onesCol M)
          (LoewnerLock.ParityDet.Aee x b a - μ • (1 : Matrix (Fin M) (Fin M) ℝ))).det :=
  LoewnerLock.ParityDet.det_odd_eq x b a μ hx hd hs

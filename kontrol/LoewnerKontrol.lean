/-
  kontrol/LoewnerKontrol.lean  v1.0 -- negative control for CvsIndexLaw/Loewner.lean
  Run:  lake env lean kontrol/LoewnerKontrol.lean
  Expected: exactly THREE errors, one per CORRUPTED block; every CORRECT block is accepted.
-/
import CvsIndexLaw

open Matrix Polynomial Finset

-- CORRECT input: Theorem 6 for an arbitrary finite set of distinct real nodes.
open Classical in
example {V : Type*} [Fintype V] [DecidableEq V] [LoewnerLock.Nodes V] (Q : Matrix (V) (V) ℝ) (a b : V → ℝ)
    (hC : LoewnerLock.IsLoewner Q a b) (hQ : Q.IsHermitian) (μ : ℝ)
    (hμ : IsUnit (Q - μ • (1 : Matrix (V) (V) ℝ)).det)
    (x : V → ℝ)
    (hx : x = Matrix.mulVec (Q - μ • (1 : Matrix (V) (V) ℝ))⁻¹ (Pi.single (LoewnerLock.z0 V) 1))
    (hx0 : x (LoewnerLock.z0 V) ≠ 0) (hηx : ∑ k, x k ≠ 0)
    (hsep : (LoewnerLock.P x).Separable) (hout : ∀ j : V, (LoewnerLock.P x).eval (LoewnerLock.node j) ≠ 0) :
    LoewnerLock.Nc x + LoewnerLock.d b x + (if x (LoewnerLock.z0 V) < 0 then 1 else 0)
      = (univ.filter (fun i => hQ.eigenvalues i < μ)).card :=
  LoewnerLock.lock Q a b hC hQ μ hμ x hx hx0 hηx hsep hout

-- CORRUPTED input: the same identity without the term [x_k0 < 0]. This must FAIL.
open Classical in
example {V : Type*} [Fintype V] [DecidableEq V] [LoewnerLock.Nodes V] (Q : Matrix (V) (V) ℝ) (a b : V → ℝ)
    (hC : LoewnerLock.IsLoewner Q a b) (hQ : Q.IsHermitian) (μ : ℝ)
    (hμ : IsUnit (Q - μ • (1 : Matrix (V) (V) ℝ)).det)
    (x : V → ℝ)
    (hx : x = Matrix.mulVec (Q - μ • (1 : Matrix (V) (V) ℝ))⁻¹ (Pi.single (LoewnerLock.z0 V) 1))
    (hx0 : x (LoewnerLock.z0 V) ≠ 0) (hηx : ∑ k, x k ≠ 0)
    (hsep : (LoewnerLock.P x).Separable) (hout : ∀ j : V, (LoewnerLock.P x).eval (LoewnerLock.node j) ≠ 0) :
    LoewnerLock.Nc x + LoewnerLock.d b x
      = (univ.filter (fun i => hQ.eigenvalues i < μ)).card :=
  LoewnerLock.lock Q a b hC hQ μ hμ x hx hx0 hηx hsep hout

-- CORRECT input: deg P_x = n - 1 for n nodes.
example {V : Type*} [Fintype V] [DecidableEq V] [LoewnerLock.Nodes V] (x : V → ℝ)
    (hc : ∑ k, x k ≠ 0) : (LoewnerLock.P x).natDegree = Fintype.card V - 1 :=
  LoewnerLock.natDegree_P_lock x hc

-- CORRUPTED input: deg P_x = n. This must FAIL.
example {V : Type*} [Fintype V] [DecidableEq V] [LoewnerLock.Nodes V] (x : V → ℝ)
    (hc : ∑ k, x k ≠ 0) : (LoewnerLock.P x).natDegree = Fintype.card V :=
  LoewnerLock.natDegree_P_lock x hc

-- CORRECT input: the integer nodes of CvS are an instance, and there P is CvS.P.
example (N : ℕ) (x : CvS.Idx N → ℝ) : LoewnerLock.P x = CvS.P x := rfl

-- CORRUPTED input: P claimed equal to CvS.P of 2x. This must FAIL.
example (N : ℕ) (x : CvS.Idx N → ℝ) : LoewnerLock.P x = CvS.P (fun k => 2 * x k) := rfl

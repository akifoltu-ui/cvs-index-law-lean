/-
  kontrol/InterlaceKontrol.lean  v1.0 -- negative control for CvsIndexLaw/Interlace.lean
  Run:  lake env lean kontrol/InterlaceKontrol.lean
  Expected: exactly THREE errors, one per CORRUPTED block; every CORRECT block is accepted.
-/
import CvsIndexLaw

open Matrix Finset

-- CORRECT input: the lock pencil identity Q D'_x = S - beta eta eta^T.
example {V : Type*} [Fintype V] [DecidableEq V] [LoewnerLock.Nodes V] {Q : Matrix V V ℝ} {a b : V → ℝ}
    (hC : LoewnerLock.IsLoewner Q a b) (x : V → ℝ)
    (hx : Q *ᵥ x = Pi.single (LoewnerLock.z0 V) 1) (hc : ∑ k, x k ≠ 0) :
    Q * LoewnerLock.Dprime (fun _ => (1 : ℝ)) x
      = LoewnerLock.Spen Q b - ((∑ k, b k * x k) / ∑ k, x k) • Matrix.of fun (_ : V) (_ : V) => (1 : ℝ) :=
  LoewnerLock.Q_Dprime_eq hC x hx hc

-- CORRUPTED input: the sign of beta flipped. This must FAIL.
example {V : Type*} [Fintype V] [DecidableEq V] [LoewnerLock.Nodes V] {Q : Matrix V V ℝ} {a b : V → ℝ}
    (hC : LoewnerLock.IsLoewner Q a b) (x : V → ℝ)
    (hx : Q *ᵥ x = Pi.single (LoewnerLock.z0 V) 1) (hc : ∑ k, x k ≠ 0) :
    Q * LoewnerLock.Dprime (fun _ => (1 : ℝ)) x
      = LoewnerLock.Spen Q b + ((∑ k, b k * x k) / ∑ k, x k) • Matrix.of fun (_ : V) (_ : V) => (1 : ℝ) :=
  LoewnerLock.Q_Dprime_eq hC x hx hc

-- CORRECT input: under parity the lock is the symmetric pencil (S, Q).
example {V : Type*} [Fintype V] [DecidableEq V] [LoewnerLock.Nodes V] [LoewnerLock.Refl V]
    {Q : Matrix V V ℝ} {a b : V → ℝ} (hC : LoewnerLock.IsLoewner Q a b)
    (ha : ∀ i, a (LoewnerLock.Refl.rf i) = a i) (hb : ∀ i, b (LoewnerLock.Refl.rf i) = - b i)
    (hinj : Function.Injective (Q *ᵥ ·)) (x : V → ℝ)
    (hx : Q *ᵥ x = Pi.single (LoewnerLock.z0 V) 1) (hc : ∑ k, x k ≠ 0) :
    Q * LoewnerLock.Dprime (fun _ => (1 : ℝ)) x = LoewnerLock.Spen Q b :=
  LoewnerLock.Q_Dprime_eq_Spen hC ha hb hinj x hx hc

-- CORRUPTED input: the same without `b` odd. This must FAIL.
example {V : Type*} [Fintype V] [DecidableEq V] [LoewnerLock.Nodes V] [LoewnerLock.Refl V]
    {Q : Matrix V V ℝ} {a b : V → ℝ} (hC : LoewnerLock.IsLoewner Q a b)
    (ha : ∀ i, a (LoewnerLock.Refl.rf i) = a i)
    (hinj : Function.Injective (Q *ᵥ ·)) (x : V → ℝ)
    (hx : Q *ᵥ x = Pi.single (LoewnerLock.z0 V) 1) (hc : ∑ k, x k ≠ 0) :
    Q * LoewnerLock.Dprime (fun _ => (1 : ℝ)) x = LoewnerLock.Spen Q b :=
  LoewnerLock.Q_Dprime_eq_Spen hC ha (by assumption) hinj x hx hc

-- CORRECT input: the boundary row.
example {V : Type*} [Fintype V] [DecidableEq V] [LoewnerLock.Nodes V] [LoewnerLock.Refl V]
    {Q : Matrix V V ℝ} {a b : V → ℝ} (hC : LoewnerLock.IsLoewner Q a b) (k : V) (y u : V → ℝ)
    (hyQ : ∀ v : V → ℝ, (∀ i, v (LoewnerLock.Refl.rf i) = v i) →
      dotProduct (Q *ᵥ y) v = v k + v (LoewnerLock.Refl.rf k))
    (hu : ∀ i, u (LoewnerLock.Refl.rf i) = - u i) (huk : u k = 0) :
    dotProduct y (LoewnerLock.Spen Q b *ᵥ u) = 0 :=
  LoewnerLock.boundary_row hC k y u hyQ hu huk

-- CORRUPTED input: the boundary row without `u k = 0`. This must FAIL.
example {V : Type*} [Fintype V] [DecidableEq V] [LoewnerLock.Nodes V] [LoewnerLock.Refl V]
    {Q : Matrix V V ℝ} {a b : V → ℝ} (hC : LoewnerLock.IsLoewner Q a b) (k : V) (y u : V → ℝ)
    (hyQ : ∀ v : V → ℝ, (∀ i, v (LoewnerLock.Refl.rf i) = v i) →
      dotProduct (Q *ᵥ y) v = v k + v (LoewnerLock.Refl.rf k))
    (hu : ∀ i, u (LoewnerLock.Refl.rf i) = - u i) :
    dotProduct y (LoewnerLock.Spen Q b *ᵥ u) = 0 :=
  LoewnerLock.boundary_row hC k y u hyQ hu (by assumption)

-- CORRECT input: the integer nodes -N..N carry the reflection i ↦ -i.
example (N : ℕ) (i : CvS.Idx N) :
    LoewnerLock.node (LoewnerLock.Refl.rf i) = - LoewnerLock.node i :=
  LoewnerLock.Refl.node_rf i

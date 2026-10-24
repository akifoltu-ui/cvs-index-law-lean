/-
  kontrol/TransportKontrol.lean  v1.0 -- negative control for CvsIndexLaw/ParityTransport.lean
  Run:  lake env lean kontrol/TransportKontrol.lean
  Expected: exactly FIVE errors, one per CORRUPTED block; every CORRECT block is accepted.
  Each corrupted statement is numerically false (exact rational check, on_sinav.py):
    sign   : x = (1), z = (1), p = 3          -> 17/12 vs 1/12
    2 r    : x = (1), z = (1), p = 3, r = 9   -> 1/8 vs 1/16
    X / 2  : x = (1, 2), z = (1, -2), X = 4   -> 10 vs 8
    order  : x = (1, 2), z = (1, -2), poles (5, -7/2), weights (1, 2): the reversed strict order fails
    27/10  : z = (10000, -26302)              -> 1583590408 vs 7905772881/5
-/
import CvsIndexLaw

open LoewnerLock.Transport

-- CORRECT input: the transport identity.
example {M : ℕ} (x z : Fin M → ℝ) (p : ℝ) (hp : p ≠ 0) (hx : ∀ j, x j ≠ 0)
    (h₁ : ∀ j, p - x j ≠ 0) (h₂ : ∀ j, p + x j ≠ 0) :
    cauchy x (evenVec (tCentre x z) (tPos x z)) p = cauchy x (oddVec z) p / p :=
  transport_cauchy x z p hp hx h₁ h₂

-- CORRUPTED input: centre coefficient with the wrong sign. This must FAIL.
example {M : ℕ} (x z : Fin M → ℝ) (p : ℝ) (hp : p ≠ 0) (hx : ∀ j, x j ≠ 0)
    (h₁ : ∀ j, p - x j ≠ 0) (h₂ : ∀ j, p + x j ≠ 0) :
    cauchy x (evenVec (-tCentre x z) (tPos x z)) p = cauchy x (oddVec z) p / p :=
  transport_cauchy x z p hp hx h₁ h₂

-- CORRECT input: the form inequality.
example {M K : ℕ} (x z : Fin M → ℝ) (w p : Fin K → ℝ) (hx : ∀ j, x j ≠ 0)
    (hp0 : ∀ k, p k ≠ 0) (h₁ : ∀ k j, p k - x j ≠ 0) (h₂ : ∀ k j, p k + x j ≠ 0)
    (hw : ∀ k, 0 ≤ w k) (r : ℝ) (hr : ∀ k, r ≤ p k ^ 2) :
    r * form x w p (evenVec (tCentre x z) (tPos x z)) ≤ form x w p (oddVec z) :=
  transport_le x z w p hx hp0 h₁ h₂ hw r hr

-- CORRUPTED input: twice the admissible constant. This must FAIL.
example {M K : ℕ} (x z : Fin M → ℝ) (w p : Fin K → ℝ) (hx : ∀ j, x j ≠ 0)
    (hp0 : ∀ k, p k ≠ 0) (h₁ : ∀ k j, p k - x j ≠ 0) (h₂ : ∀ k j, p k + x j ≠ 0)
    (hw : ∀ k, 0 ≤ w k) (r : ℝ) (hr : ∀ k, r ≤ p k ^ 2) :
    2 * r * form x w p (evenVec (tCentre x z) (tPos x z)) ≤ form x w p (oddVec z) :=
  transport_le x z w p hx hp0 h₁ h₂ hw r hr

-- CORRECT input: the norm bound.
example {M : ℕ} (x z : Fin M → ℝ) (hx : ∀ j, x j ≠ 0) (X : ℝ) (hX0 : 0 ≤ X)
    (hX : ∀ j, x j ^ 2 ≤ X) :
    nsq (oddVec z) ≤ X * nsq (evenVec (tCentre x z) (tPos x z)) :=
  odd_le_even x z hx X hX0 hX

-- CORRUPTED input: half the norm constant. This must FAIL.
example {M : ℕ} (x z : Fin M → ℝ) (hx : ∀ j, x j ≠ 0) (X : ℝ) (hX0 : 0 ≤ X)
    (hX : ∀ j, x j ^ 2 ≤ X) :
    nsq (oddVec z) ≤ X / 2 * nsq (evenVec (tCentre x z) (tPos x z)) :=
  odd_le_even x z hx X hX0 hX

-- CORRECT input: the band-out ordering.
example {M K : ℕ} (x z : Fin M → ℝ) (w p : Fin K → ℝ) (hx : ∀ j, x j ≠ 0)
    (hp0 : ∀ k, p k ≠ 0) (h₁ : ∀ k j, p k - x j ≠ 0) (h₂ : ∀ k j, p k + x j ≠ 0)
    (hw : ∀ k, 0 ≤ w k) (r X : ℝ) (hr : ∀ k, r ≤ p k ^ 2) (hX0 : 0 ≤ X)
    (hX : ∀ j, x j ^ 2 ≤ X) (hXr : X < r)
    (hpos : 0 < form x w p (oddVec z)) (hz : 0 < nsq (oddVec z)) :
    form x w p (evenVec (tCentre x z) (tPos x z)) * nsq (oddVec z)
      < form x w p (oddVec z) * nsq (evenVec (tCentre x z) (tPos x z)) :=
  band_out_order x z w p hx hp0 h₁ h₂ hw r X hr hX0 hX hXr hpos hz

-- CORRUPTED input: the reversed ordering. This must FAIL.
example {M K : ℕ} (x z : Fin M → ℝ) (w p : Fin K → ℝ) (hx : ∀ j, x j ≠ 0)
    (hp0 : ∀ k, p k ≠ 0) (h₁ : ∀ k j, p k - x j ≠ 0) (h₂ : ∀ k j, p k + x j ≠ 0)
    (hw : ∀ k, 0 ≤ w k) (r X : ℝ) (hr : ∀ k, r ≤ p k ^ 2) (hX0 : 0 ≤ X)
    (hX : ∀ j, x j ^ 2 ≤ X) (hXr : X < r)
    (hpos : 0 < form x w p (oddVec z)) (hz : 0 < nsq (oddVec z)) :
    form x w p (oddVec z) * nsq (evenVec (tCentre x z) (tPos x z))
      < form x w p (evenVec (tCentre x z) (tPos x z)) * nsq (oddVec z) :=
  band_out_order x z w p hx hp0 h₁ h₂ hw r X hr hX0 hX hXr hpos hz

-- CORRECT input: the sharp norm constant for the nodes 0, ±1, ±2.
example (z : Fin 2 → ℝ) :
    nsq (oddVec z) ≤ (5000 / 1849 : ℝ) * nsq (evenVec (tCentre xTwo z) (tPos xTwo z)) :=
  sharp_two_bound z

-- CORRUPTED input: a constant below the sharp value (27/10 < (15 + √145)/10). This must FAIL.
example (z : Fin 2 → ℝ) :
    nsq (oddVec z) ≤ (27 / 10 : ℝ) * nsq (evenVec (tCentre xTwo z) (tPos xTwo z)) :=
  sharp_two_bound z

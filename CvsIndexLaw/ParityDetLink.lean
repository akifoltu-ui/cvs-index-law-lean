import CvsIndexLaw.ParityDet

/-!
# Link: the sectors of a reflection-symmetric `IsLoewner` matrix

`Q` with `IsLoewner Q a b`, a reflection `rf` of the nodes, `b` odd, and a positive half
`pos : Fin M → V` (`0 < node (pos j)`, `pos` injective). Read on `pos`, the odd sector
`Q (pos i) (pos j) - Q (pos i) (rf (pos j))`, the even block `… + …`, the centre row
`Q 0 (pos j) + Q 0 (rf (pos j))` and the centre column `Q (pos i) 0` are the matrices `Aodd`,
`Aee`, `rowC`, `colC` of `ParityDet` with `x j = node (pos j)`, `b j = b (pos j)`, `a j = a (pos j)`
(`sector_entries`, `centre_entries`). Hence (`det_Qodd_eq`)

  `det (Q_odd - μ) = det (Q_even - μ, centre column replaced by η)`  for every `μ`.
-/

set_option linter.style.longLine false

open Matrix Finset

noncomputable section

namespace LoewnerLock

namespace ParityDet

variable {V : Type*} [Fintype V] [DecidableEq V] [Nodes V] [Refl V]

/-- An odd `b` vanishes at the zero node. -/
theorem b_z0 {b : V → ℝ} (hb : ∀ i, b (Refl.rf i) = - b i) : b (z0 V) = 0 := by
  have h := hb (z0 V)
  rw [rf_z0] at h
  linarith

/-- Entry between a positive node and a reflected positive node. -/
theorem Q_pos_rf {Q : Matrix V V ℝ} {a b : V → ℝ} (hC : IsLoewner Q a b)
    (hb : ∀ i, b (Refl.rf i) = - b i) {M : ℕ} (pos : Fin M → V) (hpos : ∀ j, 0 < node (pos j))
    (i j : Fin M) :
    Q (pos i) (Refl.rf (pos j)) = (b (pos i) + b (pos j)) / (node (pos i) + node (pos j)) := by
  have hne : pos i ≠ Refl.rf (pos j) := by
    intro h
    have h1 := congrArg node h
    rw [Refl.node_rf] at h1
    have := hpos i
    have := hpos j
    linarith
  rw [hC.off _ _ hne, hb, Refl.node_rf, sub_neg_eq_add, sub_neg_eq_add]

/-- The sector entries on the positive nodes. -/
theorem sector_entries {Q : Matrix V V ℝ} {a b : V → ℝ} (hC : IsLoewner Q a b)
    (hb : ∀ i, b (Refl.rf i) = - b i) {M : ℕ} (pos : Fin M → V)
    (hpos : ∀ j, 0 < node (pos j)) (hinj : Function.Injective pos) (i j : Fin M) :
    Aodd (fun k => node (pos k)) (fun k => b (pos k)) (fun k => a (pos k)) i j
        = Q (pos i) (pos j) - Q (pos i) (Refl.rf (pos j))
      ∧ Aee (fun k => node (pos k)) (fun k => b (pos k)) (fun k => a (pos k)) i j
        = Q (pos i) (pos j) + Q (pos i) (Refl.rf (pos j)) := by
  have hrf := Q_pos_rf hC hb pos hpos i j
  have hxi : node (pos i) ≠ 0 := (hpos i).ne'
  have hsum : node (pos i) + node (pos i) ≠ 0 := (add_pos (hpos i) (hpos i)).ne'
  by_cases h : i = j
  · subst h
    rw [hrf, hC.diag]
    constructor
    · simp only [Aodd, Matrix.of_apply, eq_self_iff_true, if_true]
      first
        | (field_simp; ring)
        | field_simp
    · simp only [Aee, Matrix.of_apply, eq_self_iff_true, if_true]
      first
        | (field_simp; ring)
        | field_simp
  · have hpq : pos i ≠ pos j := hinj.ne h
    rw [hrf, hC.off _ _ hpq]
    constructor
    · simp only [Aodd, Matrix.of_apply, h, if_false]
    · simp only [Aee, Matrix.of_apply, h, if_false]

/-- The centre row, centre column and centre entry. -/
theorem centre_entries {Q : Matrix V V ℝ} {a b : V → ℝ} (hC : IsLoewner Q a b)
    (hb : ∀ i, b (Refl.rf i) = - b i) {M : ℕ} (pos : Fin M → V)
    (hpos : ∀ j, 0 < node (pos j)) (i j : Fin M) :
    rowC (fun k => node (pos k)) (fun k => b (pos k)) 0 j
        = Q (z0 V) (pos j) + Q (z0 V) (Refl.rf (pos j))
      ∧ colC (fun k => node (pos k)) (fun k => b (pos k)) i 0 = Q (pos i) (z0 V)
      ∧ Q (z0 V) (z0 V) = a (z0 V) := by
  have hb0 := b_z0 hb
  have hxj : node (pos j) ≠ 0 := (hpos j).ne'
  have h1 : z0 V ≠ pos j := by
    intro h
    have e := congrArg node h
    rw [node_z0] at e
    linarith [hpos j]
  have h2 : z0 V ≠ Refl.rf (pos j) := by
    intro h
    have e := congrArg node h
    rw [node_z0, Refl.node_rf] at e
    linarith [hpos j]
  have h3 : pos i ≠ z0 V := by
    intro h
    have e := congrArg node h
    rw [node_z0] at e
    linarith [hpos i]
  refine ⟨?_, ?_, hC.diag _⟩
  · rw [hC.off _ _ h1, hC.off _ _ h2, hb, Refl.node_rf, hb0, node_z0]
    simp only [rowC, Matrix.of_apply, zero_sub, neg_neg, neg_div_neg_eq]
    first
      | ring
      | (rw [div_add_div_same, two_mul])
  · rw [hC.off _ _ h3, hb0, node_z0]
    simp only [colC, Matrix.of_apply, sub_zero]

/-- Odd sector of `Q` read on the positive half `pos`. -/
def Qodd (Q : Matrix V V ℝ) {M : ℕ} (pos : Fin M → V) : Matrix (Fin M) (Fin M) ℝ :=
  Matrix.of fun i j => Q (pos i) (pos j) - Q (pos i) (Refl.rf (pos j))

/-- Even sector of `Q` on the positive nodes. -/
def Qee (Q : Matrix V V ℝ) {M : ℕ} (pos : Fin M → V) : Matrix (Fin M) (Fin M) ℝ :=
  Matrix.of fun i j => Q (pos i) (pos j) + Q (pos i) (Refl.rf (pos j))

/-- Centre row of the even sector of `Q`. -/
def QrowC (Q : Matrix V V ℝ) {M : ℕ} (pos : Fin M → V) : Matrix (Fin 1) (Fin M) ℝ :=
  Matrix.of fun _ j => Q (z0 V) (pos j) + Q (z0 V) (Refl.rf (pos j))

/-- `Q_even - μ` with its centre column replaced by `η`. -/
def Qn (Q : Matrix V V ℝ) {M : ℕ} (pos : Fin M → V) (μ : ℝ) :
    Matrix (Fin 1 ⊕ Fin M) (Fin 1 ⊕ Fin M) ℝ :=
  Matrix.fromBlocks 1 (QrowC Q pos) (onesCol M) (Qee Q pos - μ • (1 : Matrix (Fin M) (Fin M) ℝ))

/-- **Parity determinant identity for a reflection-symmetric Loewner matrix.** -/
theorem det_Qodd_eq {Q : Matrix V V ℝ} {a b : V → ℝ} (hC : IsLoewner Q a b)
    (hb : ∀ i, b (Refl.rf i) = - b i) {M : ℕ} (pos : Fin M → V)
    (hpos : ∀ j, 0 < node (pos j)) (hinj : Function.Injective pos) (μ : ℝ) :
    (Qodd Q pos - μ • (1 : Matrix (Fin M) (Fin M) ℝ)).det = (Qn Q pos μ).det := by
  have hodd : Qodd Q pos
      = Aodd (fun k => node (pos k)) (fun k => b (pos k)) (fun k => a (pos k)) := by
    ext i j
    rw [(sector_entries hC hb pos hpos hinj i j).1]
    simp [Qodd]
  have hee : Qee Q pos
      = Aee (fun k => node (pos k)) (fun k => b (pos k)) (fun k => a (pos k)) := by
    ext i j
    rw [(sector_entries hC hb pos hpos hinj i j).2]
    simp [Qee]
  have hrow : QrowC Q pos = rowC (fun k => node (pos k)) (fun k => b (pos k)) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [(centre_entries hC hb pos hpos j j).1]
    simp [QrowC]
  have hn : Qn Q pos μ
      = Nmat (fun k => node (pos k)) (fun k => b (pos k)) (fun k => a (pos k)) μ := by
    rw [Qn, Nmat, hee, hrow]
  rw [hodd, hn]
  exact det_odd_eq _ _ _ μ (fun i => (hpos i).ne')
    (fun i j hij h => hij (hinj (node_inj (sub_eq_zero.mp h))))
    (fun i j => (add_pos (hpos i) (hpos j)).ne')

end ParityDet

end LoewnerLock

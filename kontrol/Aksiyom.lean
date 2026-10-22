/-
  kontrol/Aksiyom.lean -- axiom audit
  Run (after `lake build`):  lake env lean kontrol/Aksiyom.lean
  Expected:
    CvS.lock          : [propext, Classical.choice, Quot.sound]   (no sorryAx)
    CvS.index_even    : [propext, Classical.choice, Quot.sound]   (no sorryAx)
    aksiyom_kontrol   : [sorryAx]   (control: a deliberately open statement is detected)
-/
import CvsIndexLaw

#print axioms CvS.lock
#print axioms CvS.index_even

-- control: a deliberately unproved statement must show sorryAx
theorem aksiyom_kontrol : (1 : ℕ) = 2 := sorry
#print axioms aksiyom_kontrol

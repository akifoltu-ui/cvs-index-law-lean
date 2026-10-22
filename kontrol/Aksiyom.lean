/-
  kontrol/Aksiyom.lean -- axiom audit
  Run (after `lake build`):  lake env lean kontrol/Aksiyom.lean
  Expected:
    CvS.lock        : [propext, Classical.choice, Quot.sound]   (no sorryAx: fully proved)
    CvS.index_even  : contains sorryAx                         (control: the open statement is detected)
-/
import CvsIndexLaw

#print axioms CvS.lock
#print axioms CvS.index_even

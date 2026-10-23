/-
  kontrol/Aksiyom.lean -- axiom audit (v1.57)
  Run (after `lake build`):  lake env lean kontrol/Aksiyom.lean
  Expected:
    CvS.lock, CvS.index_even, CvS.lock_cvs, CvS.index_even_cvs : [propext, Classical.choice, Quot.sound]
    LoewnerLock.lock   (arbitrary distinct real nodes)          : [propext, Classical.choice, Quot.sound]
    LoewnerLock.Spen_isSymm, Q_Dprime_eq, Q_Dprime_eq_Spen, boundary_row (interlacing core) : [propext, Classical.choice, Quot.sound]
    LoewnerLock.ParityDet.intertwine, det_odd_eq, sector_entries, det_Qodd_eq (parity determinant identity) : [propext, Classical.choice, Quot.sound]
    aksiyom_kontrol    : [sorryAx]   (control: a deliberately open statement is detected)
-/
import CvsIndexLaw

#print axioms CvS.lock
#print axioms CvS.index_even
#print axioms CvS.lock_cvs
#print axioms CvS.index_even_cvs
#print axioms LoewnerLock.lock
#print axioms LoewnerLock.Spen_isSymm
#print axioms LoewnerLock.Q_Dprime_eq
#print axioms LoewnerLock.Q_Dprime_eq_Spen
#print axioms LoewnerLock.boundary_row
#print axioms LoewnerLock.ParityDet.intertwine
#print axioms LoewnerLock.ParityDet.det_odd_eq
#print axioms LoewnerLock.ParityDet.sector_entries
#print axioms LoewnerLock.ParityDet.det_Qodd_eq

-- control: a deliberately unproved statement must show sorryAx
theorem aksiyom_kontrol : (1 : ℕ) = 2 := sorry
#print axioms aksiyom_kontrol

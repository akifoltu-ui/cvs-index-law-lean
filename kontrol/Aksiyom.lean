/-
  kontrol/Aksiyom.lean -- axiom audit (v1.59)
  Run (after `lake build`):  lake env lean kontrol/Aksiyom.lean
  Expected:
    CvS.lock, CvS.index_even, CvS.lock_cvs, CvS.index_even_cvs : [propext, Classical.choice, Quot.sound]
    LoewnerLock.lock   (arbitrary distinct real nodes)          : [propext, Classical.choice, Quot.sound]
    LoewnerLock.Spen_isSymm, Q_Dprime_eq, Q_Dprime_eq_Spen, boundary_row (interlacing core) : [propext, Classical.choice, Quot.sound]
    LoewnerLock.ParityDet.intertwine, det_odd_eq, sector_entries, det_Qodd_eq (parity determinant identity) : [propext, Classical.choice, Quot.sound]
    LoewnerLock.Transport.transport, cauchy_evenVec, cauchy_oddVec, transport_cauchy, transport_le, odd_le_even,
      rayleigh_transport, order_of_norm_bound, band_out_order, sharp_two_bound, sharp_two_order (parity transport) : [propext, Classical.choice, Quot.sound]
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
#print axioms LoewnerLock.Transport.transport
#print axioms LoewnerLock.Transport.cauchy_evenVec
#print axioms LoewnerLock.Transport.cauchy_oddVec
#print axioms LoewnerLock.Transport.transport_cauchy
#print axioms LoewnerLock.Transport.transport_le
#print axioms LoewnerLock.Transport.odd_le_even
#print axioms LoewnerLock.Transport.rayleigh_transport
#print axioms LoewnerLock.Transport.order_of_norm_bound
#print axioms LoewnerLock.Transport.band_out_order
#print axioms LoewnerLock.Transport.sharp_two_bound
#print axioms LoewnerLock.Transport.sharp_two_order

-- control: a deliberately unproved statement must show sorryAx
theorem aksiyom_kontrol : (1 : ℕ) = 2 := sorry
#print axioms aksiyom_kontrol

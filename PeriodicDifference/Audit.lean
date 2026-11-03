/-
# `PeriodicDifference/Audit.lean` — the axiom audit of the headline theorems

Each line below must report exactly `[propext, Classical.choice, Quot.sound]`; anything else
(in particular `sorryAx`) would mean the proof is incomplete.  Run

    lake env lean PeriodicDifference/Audit.lean
-/
import PeriodicDifference.Problem11Complete
import PeriodicDifference.Problem11Converse
import PeriodicDifference.Problem11Iff
import PeriodicDifference.TropicalCor

#print axioms PeriodicDifference.Problem11.problem11_complete
#print axioms PeriodicDifference.Problem11.member_periodic
#print axioms PeriodicDifference.Problem11.problem11_iff
#print axioms PeriodicDifference.Trop.trop_nonperiodic

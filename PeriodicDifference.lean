/-
# Gasull's Problem 11, formalised

The main results, all with no hypotheses and no axioms beyond `propext`, `Classical.choice`
and `Quot.sound` (see `PeriodicDifference/Audit.lean`):

* `PeriodicDifference.Problem11.problem11_complete` (`PeriodicDifference/Problem11Complete.lean`) — every globally
  periodic equation of Gasull's family, of any order, is one of the five known equations up to
  rescaling and unfolding;
* `PeriodicDifference.Problem11.member_periodic` (`PeriodicDifference/Problem11Converse.lean`) — the converse;
* `PeriodicDifference.Problem11.problem11_iff` (`PeriodicDifference/Problem11Iff.lean`) — the equivalence;
* `PeriodicDifference.Trop.trop_nonperiodic` (`PeriodicDifference/TropicalCor.lean`, the paper's
  `cor:trop-nonperiodic`) — for every palindromic support `S` with `|S| ≥ 3` and either θ, no
  power of the min-plus map is the identity.

The header of `PeriodicDifference/Problem11Complete.lean` states the theorem, explains the order
convention (`Eqn k` has order `k + 1`; the min-plus side takes the order `K` directly) and maps
the modules to the sections of the paper (`paper/main.tex`, `paper/sections/*.tex`).
-/
import PeriodicDifference.Problem11Complete
import PeriodicDifference.Problem11Converse
import PeriodicDifference.Problem11Iff
import PeriodicDifference.TropicalCor
import PeriodicDifference.Audit

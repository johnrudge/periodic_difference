/-
# `PeriodicDifference/Problem11Iff.lean` — Problem 11 as an equivalence

`problem11_complete` (every globally periodic equation is a member) together with
`member_periodic` (every member is globally periodic).
-/
import PeriodicDifference.Problem11Complete
import PeriodicDifference.Problem11Converse

namespace PeriodicDifference
namespace Problem11

/-- **Gasull's Problem 11.**  An equation of the family is globally periodic on positive
states if and only if it is one of the five known equations, up to rescaling and
unfolding. -/
theorem problem11_iff {k : ℕ} (E : Eqn k) :
    (∃ p, 0 < p ∧ ∀ u, Pos u → E.F^[p] u = u) ↔ Member E :=
  ⟨fun ⟨_, hp, hper⟩ => problem11_complete E hp hper, member_periodic E⟩

end Problem11
end PeriodicDifference

/-
# `PeriodicDifference/AllOddBase.lean` — seventeen small all-odd supports (`lem:allodd-base`)

The supports of the paper's `tab:allodd-base`, each with the parameters `(d, t)` (the paper's
`(ν, t)`) of a half-arc carrier `Q(d;t)` (`HalfArc.halfQ`) that, with `σ = min S`, forms a σ-bump
(`tab_ok`, one kernel `decide`).  Five have three elements, of the form `{a, k/2, k − a}` with
`a + k/2 ≡ 0 (mod 4)` and `k/2 ≤ 11` (the pairs outside `thm:allodd-threeall`), and the other twelve have at least two elements
below `k/2` and no unit multiplier satisfying the three-point condition (T); they are the exceptions
of the base check of `thm:allodd-e3all` (`E3All.LeafOK`).  The multiplier need not be a unit.
-/
import PeriodicDifference.HalfArc

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace AllOddBase

open HalfArc

/-- A row of `tab:allodd-base`: order `k`, support `S`, its least element `a`, and the
parameters `(d, t)` of the carrier `Q(d;t)`. -/
structure Row where
  k : ℕ
  S : Finset ℕ
  a : ℕ
  d : ℕ
  t : ℕ

/-- `tab:allodd-base`. -/
def tab : List Row :=
  [⟨10, {3, 5, 7}, 3, 3, 0⟩,
   ⟨14, {5, 7, 9}, 5, 5, 14⟩,
   ⟨16, {3, 7, 9, 13}, 3, 3, 0⟩,
   ⟨18, {7, 9, 11}, 7, 5, 18⟩,
   ⟨22, {3, 9, 13, 19}, 3, 11, 22⟩,
   ⟨22, {3, 9, 11, 13, 19}, 3, 3, 0⟩,
   ⟨22, {5, 7, 15, 17}, 5, 11, 0⟩,
   ⟨22, {5, 11, 17}, 5, 5, 22⟩,
   ⟨22, {9, 11, 13}, 9, 7, 0⟩,
   ⟨24, {5, 9, 15, 19}, 5, 3, 24⟩,
   ⟨30, {7, 13, 17, 23}, 7, 3, 0⟩,
   ⟨30, {7, 13, 15, 17, 23}, 7, 3, 0⟩,
   ⟨36, {5, 13, 23, 31}, 5, 3, 36⟩,
   ⟨40, {3, 9, 31, 37}, 3, 5, 40⟩,
   ⟨40, {7, 19, 21, 33}, 7, 3, 0⟩,
   ⟨40, {9, 13, 27, 31}, 9, 11, 0⟩,
   ⟨42, {5, 15, 27, 37}, 5, 3, 42⟩]

/-- The orders and supports of `tab:allodd-base`. -/
def tabKS : List (ℕ × Finset ℕ) := tab.map fun r => (r.k, r.S)

/-- **`lem:allodd-base`.**  Every row of the table is a σ-bump carrier at `σ = min S`. -/
theorem tab_ok : ∀ r ∈ tab, BumpSat r.k r.S r.a (halfQ r.k r.S r.a r.d r.t) := by
  decide +kernel

/-- Every support of the table carries a σ-bump. -/
theorem base {k : ℕ} {S : Finset ℕ} (h : (k, S) ∈ tabKS) : ∃ σ Q, BumpSat k S σ Q := by
  obtain ⟨r, hr, e⟩ := List.mem_map.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨_, _, tab_ok r hr⟩

end AllOddBase
end Bump
end Trop
end PeriodicDifference

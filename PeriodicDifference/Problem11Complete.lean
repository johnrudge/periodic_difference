/-
# `PeriodicDifference/Problem11Complete.lean` — Gasull's Problem 11, with no hypotheses

## The statement

`PeriodicDifference.Eqn k` (`PeriodicDifference/GeneralK.lean`) is the equation

  `x_{n+k+1} = (a + Σ_{j=0}^{k} A_j x_{n+j}) / (b + Σ_{j=0}^{k} B_j x_{n+j})`

with nonnegative coefficients and nonzero numerator and denominator (the paper's `eq:family`),
acting on positive states `(x_n, …, x_{n+k})` by the state map `Eqn.F`.  **Problem 11** asks
which equations are globally periodic: `∃ p > 0, ∀ u, Pos u → E.F^[p] u = u`.  The answer
(`problem11_complete` below; the converse `member_periodic` in `PeriodicDifference/Problem11Converse.lean`;
both together as `problem11_iff` in `PeriodicDifference/Problem11Iff.lean`) is: exactly the five known
equations up to rescaling and unfolding (`Problem11.Member`, `PeriodicDifference/Problem11Defs.lean`,
the paper's `thm:main`) —
`x_{n+1} = xₙ`, `x_{n+1} = 1/xₙ`, `x_{n+2} = x_{n+1}/xₙ`, Lyness `x_{n+2} = (1 + x_{n+1})/xₙ`
and `x_{n+3} = (1 + x_{n+1} + x_{n+2})/xₙ`, each unfolded (`xₙ ↦ x_{mn}`) and rescaled.

## The order convention

`Eqn k` has **order `k + 1`**: its window is `x_n, …, x_{n+k}` and it determines `x_{n+k+1}`.
Everything on the min-plus side — `Trop.GloballyPeriodic K J co p`, the σ-bump predicate
`Trop.Bump.BumpSat K S σ Q`, `Problem11.Admissible K J co` — takes the order `K` directly,
and the bridge
`Eqn.Astar.trop_globallyPeriodic` passes from `E : Eqn k` to order `K = k + 1`.  The paper
writes `k` for the order, so the paper's `k` is the Lean `K`, i.e. `k + 1` for `E : Eqn k`.
(The modules for Lemma A, `APLemma*` and `E3All*`, also use the paper's `k`.)

## Where the proof lives

Paper `paper/main.tex`, sections in `paper/sections/*.tex`:

* `reduction.tex` (`thm:reduction`, `thm:spectral`, `thm:palindromy`, `lem:unfold`,
  `cor:red-primitive`): `GeneralK`, `KillBStar`, `FamilyA`, `Palindromic`,
  `Unfold`, `Problem11Fold` (`Eqn.classification`, `Eqn.Astar.coeff_rev`).
* `small.tex` (`thm:order2`, `thm:order3`, `thm:twoterm`): `Order2`, `Order3`, `Order3Zero`
  (through the two-term linearisation), `Problem11Small`; `TwoTerm*` (`TwoTerm.twoTerm`).
* `tropical.tex` (`thm:leading`, `thm:P`, `thm:tangent`, `prop:order6cert`, `thm:sigmabump`):
  `Tropical` (`tendsto_leading`, `theoremP`), `TropicalQpp` (`not_tropPeriodic_of_tangent`
  and `not_globallyPeriodic_of_tangent`, `thm:tangent` (i)/(ii); Theorem Q″), `Bridge`,
  `SigmaBump`, `QppCertsOrder6`, `Order6Cert`; the shared reads
  `TapRead`, `ModArith`.
* `fullsupport.tex` (`thm:fullsupport`, `lem:fs-carrier`, `lem:fs-ray`): `FullSupport`
  (`FS.not_globallyPeriodic`, through `Bump.not_globallyPeriodic_of_ray`).
* `oddk.tex` (`thm:oddk`): `OddK*`, `OddRows*`.
* `notallodd.tex` (`thm:notallodd`): `NotAllOdd*`, `EvenMin*`, `ParityCarrier` (the mirror
  `lem:nao-mirror` is `r0_of_mirror` in `TapRead`).
* `allodd.tex` (`thm:alloddall`): `AllOddOne` (`prop:allodd-one`), `HalfArc`
  (`def:allodd-halfarc`, `lem:allodd-oddhalf`), `ThreeAll*` (`thm:allodd-threeall`), `E3Suff`,
  `CosetFail` (`prop:allodd-e3bump`), `E3All*` (`thm:allodd-e3all`), `AllOddBase`
  (`lem:allodd-base`), `AllOddAll` (the proof); `BumpSat1Basic`; supports and their
  palindromes in `PerSupportDefs`.
* `lemmaA.tex` (`thm:lemmaA`): `APLemma*` — `APLemma.aplemma`, from `APLemma.good_finite`
  (`prop:lemmaA-finite`: the tables (C1), (C2) in `APLemmaCT*`, `APLemmaJT*` and the per-order
  check (C3) in `APLemmaOrd*`) and `APLemma.tailHyp` (`prop:lemmaA-tail`, `APLemmaTail*`).
* `assembly.tex` (the walk over `|S|`): `Problem11Defs` (statement), `Problem11Fold`
  (folding to the primitive support), `Problem11Prim` (the case walk, with `lemmaA` and
  `bump_even` assembling `notallodd.tex` and `allodd.tex`) and this file;
  `cor:trop-nonperiodic` is `TropicalCor` (`Trop.trop_nonperiodic`), the same walk for the
  min-plus map, through the `not_tropPeriodic` forms of the mechanisms.
* `lean.tex` describes the formalisation; the converse is `Problem11Converse`.

`PeriodicDifference/Audit.lean` prints the axioms of the headline theorems: only `propext`,
`Classical.choice` and `Quot.sound`.
-/
import PeriodicDifference.Problem11Prim
import PeriodicDifference.Palindromic
import PeriodicDifference.KillBStar
import PeriodicDifference.Bridge

namespace PeriodicDifference
namespace Problem11

open Trop

variable {k : ℕ} {E : Eqn k}

lemma coefAt_pal (h : E.Astar) {p : ℕ} (hp : 0 < p) (hper : ∀ u, Pos u → E.F^[p] u = u)
    {m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k) : E.coefAt (k + 1 - m) = E.coefAt m := by
  have hrev := h.coeff_rev hp hper ⟨m - 1, by omega⟩
  unfold Eqn.coefAt
  rw [if_neg (by omega), if_neg (by omega), dif_pos (by omega), dif_pos (by omega)]
  congr 1
  convert hrev.symm using 2 <;> ext <;> simp [Fin.rev] <;> omega

lemma admissible (h : E.Astar) {p : ℕ} (hp : 0 < p) (hper : ∀ u, Pos u → E.F^[p] u = u) :
    Admissible (k + 1) E.slots E.coefAt where
  K_pos := by omega
  nodup := List.Nodup.filter _ List.nodup_range
  lt := fun j hj => by have := E.slots_le j hj; omega
  pos := E.slots_pos
  pal := by
    intro j hj h0
    have hjk := E.slots_le j hj
    refine E.mem_slots_of (by omega) ?_
    rw [coefAt_pal h hp hper (by omega) hjk]
    exact E.slots_pos j hj
  copal := fun j hj h0 => coefAt_pal h hp hper (by omega) (E.slots_le j hj)

lemma coef_eq (h : E.Astar) {m : ℕ} (hm : m ≠ 0) : coef E m = E.coefAt m * E.B 0 := by
  have hB := h.B0_pos
  unfold coef Eqn.coefAt
  rw [if_neg hm]
  split_ifs <;> field_simp

lemma a_eq (h : E.Astar) : E.a = E.coefAt 0 * E.B 0 := by
  have hB := h.B0_pos
  unfold Eqn.coefAt
  rw [if_pos rfl]; field_simp

lemma coef_eq_zero (h : E.Astar) {m : ℕ} (hm : m ≠ 0) (hS : m ∉ supp E.slots) :
    coef E m = 0 := by
  have hB := h.B0_pos
  unfold coef
  split_ifs with hmk
  · have hn : ¬ 0 < E.A ⟨m, hmk⟩ := fun hpos =>
      hS (mem_supp.mpr ⟨hm, (Eqn.mem_slots_iff hB hm hmk).mpr hpos⟩)
    exact le_antisymm (not_lt.mp hn) (E.A_nonneg _)
  · rfl

/-- **Gasull's Problem 11.**  Every equation of the family, of any order `k + 1`, whose positive
solutions are all `p`-periodic for some `p > 0` is one of the five known equations up to
rescaling and unfolding.  `Eqn.classification` (`thm:reduction`) gives the shift or family A*; the
bridge `Eqn.Astar.trop_globallyPeriodic` and palindromy (`Eqn.Astar.coeff_rev`) give admissible
sequence data; `tropMember_of_prim` folds to the primitive support; `prim_member` walks the
cases (with Lemma A, the full support and the two-term supports proved there); the result is
read back as coefficients. -/
theorem problem11_complete {k : ℕ} (E : Eqn k) {p : ℕ} (hp : 0 < p)
    (hper : ∀ u, Pos u → E.F^[p] u = u) : Member E := by
  rcases E.classification hp hper with ⟨hA0, hb, hBs⟩ | hsh
  swap
  · exact Or.inl hsh
  have h : E.Astar := ⟨hA0, hb, hBs⟩
  have hB := h.B0_pos
  have tm := tropMember_of_prim (admissible h hp hper) (h.trop_globallyPeriodic hB hper)
    fun K' J' co' hA' hpr hg' => prim_member hA' hpr hp hg'
  have ha0 : 0 ∉ E.slots → E.a = 0 := fun h0 =>
    le_antisymm (not_lt.mp fun hpos => h0 ((Eqn.zero_mem_slots_iff hB).mpr hpos)) E.a_nonneg
  rcases tm with he | ⟨m, hK, hs, hθ⟩ | ⟨m, hK, hs, hc⟩
  · refine Or.inr (Or.inl ⟨h, fun m hm => coef_eq_zero h (by omega) (by simp [he])⟩)
  · have hz : ∀ j, 1 ≤ j → j ≠ m → coef E j = 0 := fun j hj hjm =>
      coef_eq_zero h (by omega) (by rw [hs]; simpa using hjm)
    rcases hθ with h0 | hc
    · exact Or.inr (Or.inr (Or.inl ⟨h, ha0 h0, m, hK, hz⟩))
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨h, m, hK, hz, ?_⟩)))
      rw [a_eq h, coef_eq h (by omega), hc]; ring
  · have hz : ∀ j, 1 ≤ j → j ≠ m → j ≠ 2 * m → coef E j = 0 := fun j hj hjm hj2 =>
      coef_eq_zero h (by omega) (by rw [hs]; simp [hjm, hj2])
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨h, m, hK, hz, ?_, ?_⟩)))
    · rw [coef_eq h (by omega), coef_eq h (by omega), show 2 * m = k + 1 - m by omega,
        coefAt_pal h hp hper (by omega) (by omega)]
    · rw [a_eq h, coef_eq h (by omega), hc]; ring

end Problem11
end PeriodicDifference

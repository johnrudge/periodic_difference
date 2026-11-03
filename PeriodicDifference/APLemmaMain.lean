/-
# `PeriodicDifference/APLemmaMain.lean` — `thm:lemmaA` (three-term progressions)

**Statement** (`thm:lemmaA`): for even `k > 90` and odd `a < x < k/2` with `x ≠ 3a` and
`gcd(a, x, k) = 1` there is a unit `d` (the paper's `ν`) modulo `2k` with
`H_d(2a − x) = H_d(a) ≠ H_d(x)`, `H_d(p) = [d p mod 2k < k]` (the paper's `H_ν`) — the predicate
`APLemma k a x` (`aplemma`).

The lattice argument: Hermite's bound in dimension 2 (`exists_frame`), the label facts
(`frame_facts`), the eight excluded directions (`zero_excluded`), the chords
(`good_of_chord`), the lattice classes (`good_of_class`); then `prop:lemmaA-finite` for
`92 ≤ k ≤ 2730` (`good_finite`, `APLemmaFinite`) and `prop:lemmaA-tail` for `k > 2730`
(`tailHyp`, `APLemmaTailFinal`).
-/
import PeriodicDifference.APLemmaFinite

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

/-- The hypotheses of `thm:lemmaA` give `Adm k a (x − a)`. -/
theorem adm_of {k a x : ℕ} (hk : k % 2 = 0) (ha : a % 2 = 1) (hx : x % 2 = 1) (hax : a < x)
    (hxk : 2*x < k) (h3 : x ≠ 3*a) (hcop : Nat.gcd (Nat.gcd a x) k = 1) :
    Adm k a ((x:ℤ) - a) where
  a_pos := by omega
  e_pos := by omega
  lt_half := by omega
  a_odd := by omega
  e_even := by omega
  k_even := by omega
  ne3 := by omega
  cop := by
    set c := Int.gcd (Int.gcd (a:ℤ) ((x:ℤ) - a)) (2*(k:ℤ))
    have hc1 : (c:ℤ) ∣ a := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
    have hc2 : (c:ℤ) ∣ (x:ℤ) - a := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
    have hc3 : (c:ℤ) ∣ 2*(k:ℤ) := Int.gcd_dvd_right _ _
    have hc4 : (c:ℤ) ∣ x := by have := dvd_add hc2 hc1; simpa using this
    have n1 : c ∣ a := by exact_mod_cast hc1
    have n2 : c ∣ x := by exact_mod_cast hc4
    have n3 : c ∣ 2*k := by exact_mod_cast hc3
    have hc2' : Nat.Coprime c 2 := by
      rw [Nat.coprime_two_right]
      rcases Nat.even_or_odd c with he | ho
      · exfalso; have := (even_iff_two_dvd.1 he).trans n1; omega
      · exact ho
    have n4 : c ∣ k := hc2'.dvd_of_dvd_mul_left n3
    have : c ∣ Nat.gcd (Nat.gcd a x) k := Nat.dvd_gcd (Nat.dvd_gcd n1 n2) n4
    rw [hcop] at this
    exact Nat.dvd_one.1 this

/-- **`thm:lemmaA`**, every even `k > 90`. -/
theorem aplemma {k a x : ℕ} (hk1 : 90 < k) (hk : k % 2 = 0)
    (ha : a % 2 = 1) (hx : x % 2 = 1) (hax : a < x) (hxk : 2*x < k) (h3 : x ≠ 3*a)
    (hcop : Nat.gcd (Nat.gcd a x) k = 1) : APLemma k a x := by
  have hadm := adm_of hk ha hx hax hxk h3 hcop
  refine apLemma_of_good (by omega) (by omega) ?_
  rcases (show k ≤ 2730 ∨ 2730 < k by omega) with h | h
  · exact good_finite (by omega) h hk hadm
  · exact tailHyp k h hk _ _ hadm

end APLemma
end Bump
end Trop
end PeriodicDifference

/-
# `PeriodicDifference/EvenMinParity.lean` — `lem:nao-dichotomy` and `lem:nao-ends`

`Setup k S a b`: even `k`, palindromic `S ⊆ (0, k)`, `a = min S`, `b` the least element of
parity opposite to `a`.  For `σ` in the class `c` of the carrier:

* `paritydichotomy`: a missing read `1` at `i > a` forces `i ≤ b` and `i ≡ a + c`;
* `parityextreme`: at `c ≡ a + 1`, every `i < a`, and `i = a` when `a` is even, satisfies its
  clause (both reads).
-/
import PeriodicDifference.EvenMinBasic

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace EvenMin

open Parity

/-- The standing hypotheses of the parity-carrier theorems. -/
structure Setup (k : ℕ) (S : Finset ℕ) (a b : ℕ) : Prop where
  keven : k % 2 = 0
  sub : ∀ j ∈ S, 0 < j ∧ j < k
  pal : ∀ j ∈ S, k - j ∈ S
  ha : a ∈ S
  amin : ∀ s ∈ S, a ≤ s
  hb : b ∈ S
  bpar : b % 2 ≠ a % 2
  bmin : ∀ s ∈ S, s % 2 = b % 2 → b ≤ s

namespace Setup

variable {k : ℕ} {S : Finset ℕ} {a b : ℕ} (H : Setup k S a b)
include H

lemma le_ka {s : ℕ} (hs : s ∈ S) : s ≤ k - a := by
  have h1 := H.amin _ (H.pal s hs); have h2 := H.sub s hs; omega

lemma le_kb {s : ℕ} (hs : s ∈ S) (hp : s % 2 = b % 2) : s ≤ k - b := by
  have h2 := H.sub s hs
  have h1 := H.bmin _ (H.pal s hs) (by have := H.keven; omega)
  omega

lemma a_lt_b : a < b := by
  have := H.amin b H.hb; have := H.bpar; omega

lemma b_le : b ≤ k - b := H.le_kb H.hb rfl

lemma bk : b < k := (H.sub b H.hb).2

lemma a_pos : 0 < a := (H.sub a H.ha).1

lemma two_a : 2 * a < k := by
  have := H.a_lt_b; have := H.b_le; have := H.bk; omega

lemma a_add_b : a + b < k := by
  have := H.a_lt_b; have := H.b_le; have := H.bk; omega

end Setup

variable {k : ℕ} {S : Finset ℕ} {a b σ c i : ℕ}

/-- **`lem:nao-dichotomy`** (Condition 1).  For `σ ∈ S` of class `c`, a missing read `1`
at an index `i > a` forces `i ≤ b` and `i ≡ a + c (mod 2)`. -/
theorem paritydichotomy (H : Setup k S a b) (hσc : σ % 2 = c) (hik : i < k)
    (hai : a < i) (hno : ¬ OneRead k S σ c i) : i ≤ b ∧ i % 2 = (a + c) % 2 := by
  have hak := H.sub a H.ha
  have hbk := H.sub b H.hb
  have hbp := H.bpar
  have hpar : i % 2 = (a + c) % 2 := by
    by_contra hp
    exact hno (oneRead_hi (H.pal a H.ha) (by omega) (by omega) (by omega) (by omega))
  refine ⟨?_, hpar⟩
  by_contra hb
  exact hno (oneRead_hi (H.pal b H.hb) (by omega) (by omega) (by omega) (by omega))

/-- **`lem:nao-ends`**, for `σ` in the carrier's class `c ≡ a + 1`: every index
`i < a`, and `i = a` when `a` is even, satisfies its clause. -/
theorem parityextreme (H : Setup k S a b) (hσ : σ ∈ S) (hc : c = (a + 1) % 2)
    (hσc : σ % 2 = c) (hi0 : 0 < i) (hi : i < a ∨ (i = a ∧ a % 2 = 0)) :
    Clause k S σ (parQ k S σ c) i := by
  have hak := H.sub a H.ha
  have hbk := H.sub b H.hb
  have hbp := H.bpar
  have hab := H.a_lt_b
  have h2a := H.two_a
  have hapb := H.a_add_b
  have hia : i ≤ a := by omega
  have hk2 := H.keven
  subst hc
  refine ⟨?_, ?_⟩
  · rcases Nat.even_or_odd i with ⟨r, hr⟩ | ⟨r, hr⟩
    · -- even `i`: the tap `k − b` reaches above `max S_{a+1} = k − b`
      refine oneRead_lo (H.pal b H.hb) (by omega) (by omega) ?_ ?_ (by omega)
      · intro h; rw [← h] at hσ; have := H.le_kb hσ (by omega); omega
      · intro h; have := H.le_kb h (by omega); omega
    · -- odd `i < a`: the tap `k − a` reaches above `max S = k − a`
      have hia' : i < a := by omega
      refine oneRead_lo (H.pal a H.ha) (by omega) (by omega) ?_ ?_ (by omega)
      · intro h; rw [← h] at hσ; have := H.le_ka hσ; omega
      · intro h; have := H.le_ka h; omega
  · rcases Nat.even_or_odd i with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact zeroRead_lo H.ha (by omega) (by omega) (by omega) (by omega)
    · exact zeroRead_lo H.hb (by omega) (by omega) (by omega) (by omega)

end EvenMin
end Bump
end Trop
end PeriodicDifference

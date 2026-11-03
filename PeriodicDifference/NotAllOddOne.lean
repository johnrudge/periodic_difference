/-
# `PeriodicDifference/NotAllOddOne.lean` — `lem:nao-bfone`, the both-failing supports with `M = 1`

`k = 2a + b`, `a` odd, `b` even, `a < b < 2a`; `S` palindromic with odd part `{a, a + b}` and
even part inside `[b, 2a]` containing `b` (and `2a = k − b`).  Then `σ = a` with

  `Q = {a, 3a, b − a} ∪ {even y ∈ (0, k) : y ∉ S}`

is a σ-bump carrier.  The proof is the paper's table: at every index two of the four taps
`a`, `b`, `2a`, `a + b` read safe positions with different values.
-/
import PeriodicDifference.NotAllOddBasic

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace NotAllOdd

/-- The carrier of `lem:nao-bfone`. -/
def oneQ (k : ℕ) (S : Finset ℕ) (a b : ℕ) : Finset ℕ :=
  (Finset.range k).filter
    (fun y => y = a ∨ y = 3 * a ∨ y = b - a ∨ (y % 2 = 0 ∧ 0 < y ∧ y ∉ S))

/-- The hypotheses of `lem:nao-bfone`. -/
structure OneHyp (k : ℕ) (S : Finset ℕ) (a b : ℕ) : Prop where
  sub : ∀ j ∈ S, 0 < j ∧ j < k
  pal : ∀ j ∈ S, k - j ∈ S
  hk : k = 2 * a + b
  hao : a % 2 = 1
  hbe : b % 2 = 0
  hab : a < b
  hb2 : b < 2 * a
  ha : a ∈ S
  hb : b ∈ S
  odd : ∀ s ∈ S, s % 2 = 1 → s = a ∨ s = a + b
  even : ∀ s ∈ S, s % 2 = 0 → b ≤ s ∧ s ≤ 2 * a

namespace OneHyp

variable {k : ℕ} {S : Finset ℕ} {a b : ℕ} (H : OneHyp k S a b)
include H

omit H in
lemma memQ {y : ℕ} (hy : y < k) :
    y ∈ oneQ k S a b ↔ (y = a ∨ y = 3 * a ∨ y = b - a ∨ (y % 2 = 0 ∧ 0 < y ∧ y ∉ S)) := by
  simp only [oneQ, Finset.mem_filter, Finset.mem_range]; tauto

lemma h2a : 2 * a ∈ S := by
  have := H.pal b H.hb; rwa [show k - b = 2 * a by have := H.hk; omega] at this

lemma hapb : a + b ∈ S := by
  have := H.pal a H.ha; rwa [show k - a = a + b by have := H.hk; omega] at this

omit H in
lemma notQ {y : ℕ} (hy : y < k) (hodd : y % 2 = 1 ∨ y ∈ S) (h1 : y ≠ a) (h2 : y ≠ 3 * a)
    (h3 : y ≠ b - a) : y ∉ oneQ k S a b := by
  rw [memQ hy]
  rintro (h | h | h | ⟨he, -, hn⟩)
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · rcases hodd with h | h
    · omega
    · exact hn h

lemma inQ_free {y : ℕ} (hy0 : 0 < y) (hy : y < k) (he : y % 2 = 0) (hr : y < b ∨ 2 * a < y) :
    y ∈ oneQ k S a b := by
  rw [memQ hy]
  refine Or.inr (Or.inr (Or.inr ⟨he, hy0, fun hm => ?_⟩))
  have := H.even y hm he
  omega

lemma inQ_3a : 3 * a ∈ oneQ k S a b := by
  have := H.hk; have := H.hab; rw [memQ (k := k) (S := S) (y := 3 * a) (by omega)]; tauto

lemma inQ_ba : b - a ∈ oneQ k S a b := by
  have h1 := H.hk; have h2 := H.hab; have h3 := H.hao
  have hlt : b - a < k := by omega
  rw [memQ hlt]; tauto

lemma B1 : oneQ k S a b ∩ insert 0 S = {a} := by
  have := H.hk; have := H.hab; have := H.hb2; have := H.hao; have := H.hbe
  ext y
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hQ, hS⟩
    have hyk : y < k := by simp only [oneQ, Finset.mem_filter, Finset.mem_range] at hQ; exact hQ.1
    rw [memQ hyk] at hQ
    rcases hS with rfl | hS
    · omega
    · rcases hQ with h | h | h | ⟨-, -, hn⟩
      · exact h
      · rcases H.odd y hS (by omega) with h' | h' <;> omega
      · rcases H.odd y hS (by omega) with h' | h' <;> omega
      · exact absurd hS hn
  · rintro rfl
    exact ⟨(memQ (by omega)).2 (Or.inl rfl), Or.inr H.ha⟩

/-- **The tap table of `lem:nao-bfone`.** -/
theorem clause {i : ℕ} (hi0 : 0 < i) (hik : i < k) :
    R1 k S a (oneQ k S a b) i ∧ R0 k S a (oneQ k S a b) i := by
  have hk := H.hk; have hao := H.hao; have hbe := H.hbe; have hab := H.hab; have hb2 := H.hb2
  have ha := H.ha; have hb := H.hb; have h2a := H.h2a; have hapb := H.hapb
  rcases Nat.mod_two_eq_zero_or_one i with he | ho
  · -- even `i`
    by_cases c1 : i < b
    · exact ⟨r1lo h2a (by omega) (by omega) (by omega)
          (H.inQ_free (by omega) (by omega) (by omega) (Or.inr (by omega))),
        r0lo ha (by omega) (by omega) (by omega)
          (notQ (by omega) (Or.inl (by omega)) (by omega) (by omega) (by omega))⟩
    by_cases c2 : i = b
    · exact ⟨r1lo hb (by omega) (by omega) (by omega)
          (H.inQ_free (by omega) (by omega) (by omega) (Or.inr (by omega))),
        r0lo ha (by omega) (by omega) (by omega)
          (notQ (by omega) (Or.inl (by omega)) (by omega) (by omega) (by omega))⟩
    by_cases c3 : i = 2 * a
    · exact ⟨r1lo ha (by omega) (by omega) (by omega)
          (by rw [show i + a = 3 * a by omega]; exact H.inQ_3a),
        r0hi h2a (by omega) (by omega) (by omega)
          (H.inQ_free (by omega) (by omega) (by omega) (Or.inl (by omega)))⟩
    by_cases c4 : i < a + b
    · exact ⟨r1hi hapb (by omega) (by omega) (by omega)
          (notQ (by omega) (Or.inl (by omega)) (by omega) (by omega) (by omega)),
        r0lo ha (by omega) (by omega) (by omega)
          (notQ (by omega) (Or.inl (by omega)) (by omega) (by omega) (by omega))⟩
    refine ⟨?_, r0hi hb (by omega) (by omega) (by omega)
      (H.inQ_free (by omega) (by omega) (by omega) (Or.inl (by omega)))⟩
    by_cases c5 : i = 2 * b
    · exact r1hi hapb (by omega) (by omega) (by omega)
        (notQ (by omega) (Or.inl (by omega)) (by omega) (by omega) (by omega))
    · exact r1hi ha (by omega) (by omega) (by omega)
        (notQ (by omega) (Or.inl (by omega)) (by omega) (by omega) (by omega))
  · -- odd `i`
    by_cases c1 : i < a
    · exact ⟨r1lo hapb (by omega) (by omega) (by omega)
          (H.inQ_free (by omega) (by omega) (by omega) (Or.inr (by omega))),
        r0lo h2a (by omega) (by omega) (by omega)
          (notQ (by omega) (Or.inl (by omega)) (by omega) (by omega) (by omega))⟩
    by_cases c2 : i = a
    · exact ⟨r1lo h2a (by omega) (by omega) (by omega)
          (by rw [show i + 2 * a = 3 * a by omega]; exact H.inQ_3a),
        r0lo ha (by omega) (by omega) (by omega)
          (notQ (by omega) (Or.inr (by rw [show i + a = 2 * a by omega]; exact h2a))
            (by omega) (by omega) (by omega))⟩
    by_cases c3 : i < a + b
    · exact ⟨r1lo ha (by omega) (by omega) (by omega)
          (H.inQ_free (by omega) (by omega) (by omega) (Or.inr (by omega))),
        r0hi hapb (by omega) (by omega) (by omega)
          (H.inQ_free (by omega) (by omega) (by omega) (Or.inl (by omega)))⟩
    by_cases c4 : i = a + b
    · exact ⟨r1hi hapb (by omega) (by omega) (by omega)
          (notQ (by omega) (Or.inr (by rw [show i + (a + b) - k = b by omega]; exact hb))
            (by omega) (by omega) (by omega)),
        r0hi hb (by omega) (by omega) (by omega)
          (by rw [show i + b - k = b - a by omega]; exact H.inQ_ba)⟩
    by_cases c5 : i = 3 * a
    · exact ⟨r1hi hapb (by omega) (by omega) (by omega)
          (notQ (by omega) (Or.inr (by rw [show i + (a + b) - k = 2 * a by omega]; exact h2a))
            (by omega) (by omega) (by omega)),
        r0hi ha (by omega) (by omega) (by omega)
          (H.inQ_free (by omega) (by omega) (by omega) (Or.inl (by omega)))⟩
    · exact ⟨r1hi hb (by omega) (by omega) (by omega)
          (notQ (by omega) (Or.inl (by omega)) (by omega) (by omega) (by omega)),
        r0hi ha (by omega) (by omega) (by omega)
          (H.inQ_free (by omega) (by omega) (by omega) (Or.inl (by omega)))⟩

/-- **`lem:nao-bfone`.** -/
theorem bumpSat : BumpSat k S a (oneQ k S a b) where
  S_sub := H.sub
  σ_mem := H.ha
  B1 := H.B1
  B2 := fun _ hi0 hik => H.clause hi0 hik

end OneHyp

end NotAllOdd
end Bump
end Trop
end PeriodicDifference

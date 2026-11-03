/-
# `PeriodicDifference/NotAllOddBasic.lean` — reads for an arbitrary carrier, the chain lemma, and the
failure containments of the parity carriers at odd minimum (`lem:nao-endend`, localisation)

Reads `R1`, `R0` and their producers `r1lo`, `r0lo`, `r1hi`, `r0hi` are in
`PeriodicDifference/TapRead.lean`.

`Cont k S c i`: every unwrapped tap of `S` at `i` landing in class `c` lands in `S`.  A
missing read `1` of the class-`c` parity carrier at `i` gives `Cont k S c i` (`cont_of_noread`).
-/
import PeriodicDifference.EvenMin

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace NotAllOdd

open Parity EvenMin

variable {k : ℕ} {S : Finset ℕ} {σ : ℕ} {Q : Finset ℕ}

/-! ## The chain lemma -/

/-- A finite set closed under `+ d` below its top `t` is a union of `d`-progressions ending
at `t`: every element is `≡ t (mod d)` and its whole progression up to `t` is present. -/
lemma chain {T : ℕ → Prop} {d t : ℕ} (hd : 0 < d) (htop : ∀ y, T y → y ≤ t)
    (hstep : ∀ y, T y → y ≠ t → T (y + d)) :
    ∀ y, T y → d ∣ t - y ∧ ∀ m, y + d * m ≤ t → T (y + d * m) := by
  have key : ∀ n y, T y → t - y ≤ n → d ∣ t - y ∧ ∀ m, y + d * m ≤ t → T (y + d * m) := by
    intro n
    induction n with
    | zero =>
      intro y hy hn
      have := htop y hy
      refine ⟨by rw [show t - y = 0 by omega]; exact dvd_zero d, fun m hm => ?_⟩
      have : d * m = 0 := by omega
      rw [this, Nat.add_zero]; exact hy
    | succ n ih =>
      intro y hy hn
      have hyt := htop y hy
      by_cases hyt' : y = t
      · subst hyt'
        refine ⟨by simp, fun m hm => ?_⟩
        have : d * m = 0 := by omega
        rw [this, Nat.add_zero]; exact hy
      · have hy' := hstep y hy hyt'
        have hyd := htop _ hy'
        obtain ⟨h1, h2⟩ := ih (y + d) hy' (by omega)
        refine ⟨?_, fun m hm => ?_⟩
        · have e : t - y = (t - (y + d)) + d := by omega
          rw [e]; exact dvd_add h1 (dvd_refl d)
        · rcases m with _ | m
          · simpa using hy
          · have := h2 m (by rw [Nat.mul_succ] at hm; omega)
            rwa [show y + d * (m + 1) = y + d + d * m by ring]
  exact fun y hy => key _ y hy le_rfl

/-! ## Failure containments -/

/-- Every unwrapped tap of `S` at `i` landing in class `c` lands in `S`. -/
def Cont (k : ℕ) (S : Finset ℕ) (c i : ℕ) : Prop :=
  ∀ j ∈ S, i + j < k → (i + j) % 2 = c → i + j ∈ S

lemma cont_of_noread (hσ : σ ∈ S) {c i : ℕ} (hno : ¬ OneRead k S σ c i) (hi0 : 0 < i) :
    Cont k S c i := by
  intro j hj hlt hpar
  by_cases hs : i + j = σ
  · rw [hs]; exact hσ
  · rcases lo_of_not_oneRead hno hj (by omega) hlt hs with h | h
    · exact h
    · exact absurd hpar h

/-- A wrapped tap landing on an element of `S` other than `σ` reads `1` on every parity
carrier. -/
lemma oneRead_hi_mem {c i j : ℕ} (hj : j ∈ S) (hlt : k < i + j) (h2 : i + j < 2 * k)
    (hne : i + j - k ≠ σ) (hmem : i + j - k ∈ S) : OneRead k S σ c i :=
  r1hi hj hlt h2 hne fun h => (mem_parQ.mp h).elim hne fun h => h.2.2.1 hmem

/-- **A failing parity carrier has a missing read `1`**, at `(σ, i)` or at the mirror
`(k − σ, k − i)`. -/
lemma missing_of_fail (hk2 : k % 2 = 0) (hS : ∀ j ∈ S, 0 < j ∧ j < k)
    (hpal : ∀ j ∈ S, k - j ∈ S) {c : ℕ} (hσ : σ ∈ S)
    (hnot : ¬ BumpSat k S σ (parQ k S σ c)) :
    ∃ σ' i, σ' ∈ S ∧ σ' % 2 = σ % 2 ∧ (σ' = σ ∨ σ' = k - σ) ∧ 0 < i ∧ i < k ∧
      ¬ OneRead k S σ' c i := by
  have hσk := hS σ hσ
  obtain ⟨i, hi0, hik, hcl⟩ : ∃ i, 0 < i ∧ i < k ∧ ¬ Clause k S σ (parQ k S σ c) i := by
    by_contra h
    push_neg at h
    exact hnot (bumpSat_parQ hS hσ h)
  by_cases hO : OneRead k S σ c i
  · refine ⟨k - σ, k - i, hpal σ hσ, by omega, Or.inr rfl, by omega, by omega, fun h => hcl ⟨hO, ?_⟩⟩
    exact zeroRead_of_mirror hk2 hS hpal hσ hi0 hik h
  · exact ⟨σ, i, hσ, rfl, Or.inl rfl, hi0, hik, hO⟩

end NotAllOdd
end Bump
end Trop
end PeriodicDifference

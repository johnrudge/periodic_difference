/-
# `PeriodicDifference/EvenMinBasic.lean` — reads of a parity carrier, the parity classes
(the parity classes of `sec:notallodd`) and the mirror

The clause of `def:bump` at index `i` for the parity carrier `parQ k S σ c` asks for a
read `1` (`OneRead`, the read `R1` of `PeriodicDifference/TapRead.lean` on `parQ`) and a read `0`
(`ZeroRead`) among the surviving taps.  At even `k` the
mirror `i ↦ k − i`, `j ↦ k − j`, `σ ↦ k − σ` turns a read `1` into a read `0`
(`zeroRead_of_mirror`), so every parity-carrier argument below needs only reads `1`.
-/
import PeriodicDifference.ParityCarrier

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace EvenMin

open Parity

variable {k : ℕ} {S : Finset ℕ} {σ c i : ℕ}

/-- A surviving tap at `i` reads `1` on the parity carrier of class `c`. -/
abbrev OneRead (k : ℕ) (S : Finset ℕ) (σ c i : ℕ) : Prop := R1 k S σ (parQ k S σ c) i

/-- A surviving tap at `i` reads `0` on the parity carrier of class `c`. -/
abbrev ZeroRead (k : ℕ) (S : Finset ℕ) (σ c i : ℕ) : Prop := R0 k S σ (parQ k S σ c) i

lemma clause_iff : Clause k S σ (parQ k S σ c) i ↔ OneRead k S σ c i ∧ ZeroRead k S σ c i :=
  Iff.rfl

/-- An unwrapped tap reaching a free position of class `c` reads `1`. -/
lemma oneRead_lo {j : ℕ} (hj : j ∈ S) (h0 : 0 < i + j) (hlt : i + j < k) (hne : i + j ≠ σ)
    (hfree : i + j ∉ S) (hpar : (i + j) % 2 = c) : OneRead k S σ c i :=
  r1lo hj h0 hlt hne (mem_parQ.mpr (Or.inr ⟨h0, hlt, hfree, hpar⟩))

/-- An unwrapped tap reaching a position of class `≠ c` reads `0`. -/
lemma zeroRead_lo {j : ℕ} (hj : j ∈ S) (h0 : 0 < i + j) (hlt : i + j < k) (hne : i + j ≠ σ)
    (hpar : (i + j) % 2 ≠ c) : ZeroRead k S σ c i :=
  r0lo hj h0 hlt hne fun h => (mem_parQ.mp h).elim hne fun h => hpar h.2.2.2

/-- A wrapped tap reaching a position of class `≠ c` reads `1`. -/
lemma oneRead_hi {j : ℕ} (hj : j ∈ S) (hlt : k < i + j) (h2 : i + j < 2 * k)
    (hne : i + j - k ≠ σ) (hpar : (i + j - k) % 2 ≠ c) : OneRead k S σ c i :=
  r1hi hj hlt h2 hne fun h => (mem_parQ.mp h).elim hne fun h => hpar h.2.2.2

/-- An unwrapped surviving tap with no read `1` lands in `S` or off class `c`. -/
lemma lo_of_not_oneRead (hno : ¬ OneRead k S σ c i) {j : ℕ} (hj : j ∈ S) (h0 : 0 < i + j)
    (hlt : i + j < k) (hne : i + j ≠ σ) : i + j ∈ S ∨ (i + j) % 2 ≠ c := by
  by_contra h
  push_neg at h
  exact hno (oneRead_lo hj h0 hlt hne h.1 h.2)

/-- The parity carrier of `k − σ` is the reflection of that of `σ`, at even `k`. -/
lemma mem_parQ_mirror (hk2 : k % 2 = 0) (hpal : ∀ j ∈ S, k - j ∈ S) (hσ : σ < k) {y : ℕ}
    (hy0 : 0 < y) (hyk : y < k) : y ∈ parQ k S (k - σ) c ↔ k - y ∈ parQ k S σ c := by
  have hsym : k - y ∈ S ↔ y ∈ S := ⟨fun h => by
    have := hpal _ h; rwa [show k - (k - y) = y by omega] at this, hpal y⟩
  rw [mem_parQ, mem_parQ, hsym]
  constructor
  · rintro (h | ⟨-, -, h1, h2⟩)
    · left; omega
    · right; exact ⟨by omega, by omega, h1, by omega⟩
  · rintro (h | ⟨-, -, h1, h2⟩)
    · left; omega
    · right; exact ⟨hy0, hyk, h1, by omega⟩

/-- **The mirror** (`lem:nao-mirror` for parity carriers).  At even `k`, a read `1` at
`(k − i, k − σ)` gives a read `0` at `(i, σ)`. -/
lemma zeroRead_of_mirror (hk2 : k % 2 = 0) (hS : ∀ j ∈ S, 0 < j ∧ j < k)
    (hpal : ∀ j ∈ S, k - j ∈ S) (hσ : σ ∈ S) (hi0 : 0 < i) (hik : i < k)
    (h : OneRead k S (k - σ) c (k - i)) : ZeroRead k S σ c i :=
  r0_of_mirror hS hpal (hS σ hσ).2
    (fun _ hy0 hyk => mem_parQ_mirror hk2 hpal (hS σ hσ).2 hy0 hyk) hi0 hik h

/-! ## the parity classes of `sec:notallodd` -/

/-- At even `k`, palindromy preserves parity. -/
lemma pal_parity (hk2 : k % 2 = 0) {s : ℕ} (hs : s < k) : (k - s) % 2 = s % 2 := by omega

/-- **the parity classes of `sec:notallodd`** (the primitivity half): a primitive support at even order has an
odd element. -/
lemma exists_odd_of_primitive (hk2 : k % 2 = 0)
    (hprim : ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ k → d = 1) : ∃ s ∈ S, s % 2 = 1 := by
  by_contra h
  push_neg at h
  have := hprim 2 (fun s hs => Nat.dvd_of_mod_eq_zero (by have := h s hs; omega))
    (Nat.dvd_of_mod_eq_zero hk2)
  omega

end EvenMin
end Bump
end Trop
end PeriodicDifference

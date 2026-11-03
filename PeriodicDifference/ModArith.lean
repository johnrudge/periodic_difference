/-
# `PeriodicDifference/ModArith.lean` — parities and phases modulo `2k`

Arithmetic shared by the carrier modules: reduction modulo an even number preserves parity
(`mod_parity`), and an odd multiplier `d` fixes `k` modulo `2k` and moves `y + k` half way
round (`mul_k_mod`, `phase_add_k`, `ph_add_k`, `phase_parity`, …).
-/
import Mathlib.Tactic

namespace PeriodicDifference
namespace Trop
namespace Bump

/-- Reducing modulo an even number preserves parity. -/
lemma mod_parity {k : ℕ} (hk : k % 2 = 0) (n : ℕ) : n % k % 2 = n % 2 :=
  Nat.mod_mod_of_dvd n (Nat.dvd_of_mod_eq_zero hk)

section Arith

variable {k d : ℕ}

/-- An odd multiplier fixes `k` modulo `2k`. -/
lemma mul_k_mod (hd : d % 2 = 1) (hk : 0 < k) : d * k % (2 * k) = k := by
  obtain ⟨m, rfl⟩ : ∃ m, d = 2 * m + 1 := ⟨d / 2, by omega⟩
  have : (2 * m + 1) * k = k + (2 * k) * m := by ring
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- The phase of `k + y` is the phase of `y` moved half way round. -/
lemma phase_add_k (hd : d % 2 = 1) (hk : 0 < k) (y : ℕ) :
    d * (k + y) % (2 * k) = (d * y % (2 * k) + k) % (2 * k) := by
  rw [Nat.mul_add, Nat.add_mod, mul_k_mod hd hk, Nat.add_comm (d * y % (2 * k)) k]

/-- The phase of a sum, as a sum of phases below `4k`. -/
lemma phase_add (y z : ℕ) : d * (y + z) % (2 * k) = (d * y % (2 * k) + d * z % (2 * k)) % (2 * k) := by
  rw [Nat.mul_add, Nat.add_mod]

/-- The phase of `k − y`: `k − x` modulo `2k`, written without subtraction below zero. -/
lemma phase_k_sub (hd : d % 2 = 1) (hk : 0 < k) {y : ℕ} (hy : y ≤ k) :
    (d * (k - y) % (2 * k) + d * y % (2 * k)) % (2 * k) = k := by
  rw [← Nat.add_mod, ← Nat.mul_add, Nat.sub_add_cancel hy, mul_k_mod hd hk]

/-- An odd multiplier preserves parity modulo the even modulus `2k`. -/
lemma phase_parity (hd : d % 2 = 1) (y : ℕ) : d * y % (2 * k) % 2 = y % 2 := by
  rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 2 k), Nat.mul_mod, hd, one_mul, Nat.mod_mod]

/-- The phase of `y + k`, as in `phase_add_k`. -/
lemma ph_add_k (hd : d % 2 = 1) (hk : 0 < k) (p : ℕ) :
    d * (p + k) % (2 * k) = (d * p % (2 * k) + k) % (2 * k) := by
  rw [Nat.add_comm p k, phase_add_k hd hk]

/-- The phase is `2k`-periodic. -/
lemma ph_add_2k (p : ℕ) : d * (p + 2 * k) % (2 * k) = d * p % (2 * k) := by
  rw [show d * (p + 2 * k) = d * p + (2 * k) * d by ring, Nat.add_mul_mod_self_left]

end Arith

end Bump
end Trop
end PeriodicDifference

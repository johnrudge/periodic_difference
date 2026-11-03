/-
# `PeriodicDifference/APLemmaTailFinal.lean` — `TailHyp`: `thm:lemmaA` for every even `k > 2730`

`jacTail` and `jacG` (`cor:lemmaA-jac`, the two Jacobsthal inputs of `good_of_jac`) follow
from the pattern bound (`jac_pattern`, `lem:lemmaA-pattern`, `ω ≤ 8`) and the crude bound
(`jac_crude`, `lem:lemmaA-crude`, `ω ≥ 9`); `tailHyp` is `prop:lemmaA-tail`.
-/
import PeriodicDifference.APLemmaTailMain
import PeriodicDifference.APLemmaTailPat
import PeriodicDifference.APLemmaTailCrude

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

theorem jacTail : JacTail := by
  intro k hk hk2
  have hk0 : 0 < k := by omega
  have h2k : 2 ∣ k := Nat.dvd_of_mod_eq_zero hk2
  have hprim : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2*k → ℓ ∣ k := by
    intro ℓ hℓ h
    rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h]; exact h2k
    · exact h
  rcases le_or_gt k.primeFactors.card 8 with hω | hω
  · obtain ⟨A, r, m, hJ, hA, hAk, h2A, htail, -⟩ := jac_pattern hk0 hω
    refine ⟨m, jacOK_of_primes hJ hprim, ?_⟩
    have hA2 := h2A h2k
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at htail
    rcases htail with h | h
    · exact absurd hA2 h
    · refine h.trans (Nat.mul_le_mul_left _ (max_le hAk ?_))
      obtain ⟨t, rfl⟩ := hA
      have hApos : 0 < A := Nat.pos_of_ne_zero (by rintro rfl; simp at hk0)
      have : 2730 / A < t := by
        rw [Nat.div_lt_iff_lt_mul hApos]; linarith
      nlinarith
  · obtain ⟨A, R, r, hJ, hAR, h178, -, hA⟩ := jac_crude hk0 (by omega)
    refine ⟨A*(r+1), jacOK_of_primes hJ hprim, ?_⟩
    have hle := Nat.le_of_dvd hk0 hAR
    calc 178*(A*(r+1))^2 = A*(178*A*(r+1)^2) := by ring
      _ ≤ A*(10*R) := Nat.mul_le_mul_left _ h178
      _ = 10*(A*R) := by ring
      _ ≤ 10*k := Nat.mul_le_mul_left _ hle

theorem jacG : JacG := by
  intro g hg
  rcases le_or_gt g.primeFactors.card 8 with hω | hω
  · obtain ⟨A, r, m, hJ, -, hAg, -, -, hgb⟩ := jac_pattern hg hω
    refine ⟨m, hJ, ?_⟩
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hgb
    rcases hgb with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans_le (Nat.mul_le_mul_left _ hAg))
  · obtain ⟨A, R, r, hJ, hAR, -, h1000, hA⟩ := jac_crude hg (by omega)
    refine ⟨A*(r+1), hJ, Or.inr ?_⟩
    have hle := Nat.le_of_dvd hg hAR
    calc 1000*(A*(r+1)) = A*(1000*(r+1)) := by ring
      _ < A*(102*R) := Nat.mul_lt_mul_of_pos_left h1000 hA
      _ = 102*(A*R) := by ring
      _ ≤ 102*g := Nat.mul_le_mul_left _ hle

/-- **`TailHyp`** (`prop:lemmaA-tail`): `thm:lemmaA` at every even `k > 2730`. -/
theorem tailHyp : TailHyp := by
  intro k hk hk2 a e hadm
  obtain ⟨J, hJ, hJk⟩ := jacTail k hk hk2
  refine good_of_jac jacG hJ hJk ?_ hadm
  rcases le_or_gt 10 J with h10 | h10
  · nlinarith
  · omega

end APLemma
end Bump
end Trop
end PeriodicDifference

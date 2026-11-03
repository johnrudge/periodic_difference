/-
# `PeriodicDifference/APLemmaJac.lean` — `thm:lemmaA`, stage 3: Jacobsthal windows along a lattice line

`JacOK n J`: every window of `J` consecutive integers contains one prime to `n`
(so `j(n) ≤ J`, Jacobsthal's function).  `jacCheck` decides it (one period suffices).

`exists_unit_on_line` is (3.3) of proof.md: on the line `j w + i v` of `Λ` the labels are
`j δ₀ + i δ`; if `g ∣ δ`, `j` and `δ₀` are prime to `g`, `δ` is prime to `n`, and every prime of
`N` divides `n` or `g`, then every window of `J` consecutive `i` contains a unit label.
-/
import Mathlib

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

/-- Every window of `J` consecutive integers contains one prime to `n`. -/
def JacOK (n J : ℕ) : Prop := ∀ X : ℤ, ∃ i : ℕ, i < J ∧ IsCoprime (X + i) (n : ℤ)

/-- Decision procedure for `JacOK` over one period. -/
def jacCheck (n J : ℕ) : Bool :=
  (List.range n).all fun x => (List.range J).any fun i => Nat.gcd (x+i) n == 1

theorem jacOK_of_check {n J : ℕ} (hn : 0 < n) (h : jacCheck n J = true) : JacOK n J := by
  intro X
  have hn' : (0:ℤ) < n := by exact_mod_cast hn
  set x := (X % n).toNat with hx
  have hxX : (x : ℤ) = X % n := Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')
  have hxn : x < n := by
    have := Int.emod_lt_of_pos X hn'; omega
  simp only [jacCheck, List.all_eq_true, List.mem_range, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨i, hi, hg⟩ := h x hxn
  refine ⟨i, hi, ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one, ← Int.gcd_emod, Int.add_emod, ← hxX]
  have : ((x:ℤ) + (i:ℤ) % n) % n = ((x + i : ℕ) : ℤ) % n := by
    push_cast; rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]
  rw [this, Int.gcd_emod, Int.gcd_natCast_natCast]; exact hg

/-- (3.3): a unit label among any `J` consecutive points of a good line. -/
theorem exists_unit_on_line {N g δ δ₀ j : ℤ} {n J : ℕ} (hJ : JacOK n J)
    (hδn : IsCoprime δ n) (hgδ : g ∣ δ) (hj : IsCoprime j g) (hδ₀ : IsCoprime δ₀ g)
    (hcover : ∀ ℓ : ℕ, ℓ.Prime → (ℓ:ℤ) ∣ N → (ℓ:ℤ) ∣ n ∨ (ℓ:ℤ) ∣ g) (i₀ : ℤ) :
    ∃ i : ℕ, i < J ∧ IsCoprime (j*δ₀ + (i₀ + i)*δ) N := by
  obtain ⟨ι, κ, hικ⟩ := hδn
  obtain ⟨i, hi, hcop⟩ := hJ (i₀ + ι*j*δ₀)
  refine ⟨i, hi, ?_⟩
  set L := j*δ₀ + (i₀ + i)*δ
  have hL : L = δ*(i₀ + ι*j*δ₀ + i) + n*(j*δ₀*κ) := by
    simp only [L]; linear_combination (-(j*δ₀)) * hικ
  rw [Int.isCoprime_iff_gcd_eq_one]
  apply Nat.coprime_of_dvd
  intro ℓ hℓ h1 h2
  have h1' : (ℓ:ℤ) ∣ L := Int.natCast_dvd.2 h1
  have h2' : (ℓ:ℤ) ∣ N := Int.natCast_dvd.2 h2
  have hnu : ¬ IsUnit (ℓ:ℤ) := by
    rw [Int.isUnit_iff_natAbs_eq]; simpa using hℓ.one_lt.ne'
  rcases hcover ℓ hℓ h2' with hn | hg
  · have : (ℓ:ℤ) ∣ δ*(i₀ + ι*j*δ₀ + i) := by
      have := dvd_sub h1' (dvd_mul_of_dvd_left hn (j*δ₀*κ))
      rwa [hL, add_sub_cancel_right] at this
    rcases Int.Prime.dvd_mul' hℓ this with h | h
    · exact hnu (IsCoprime.isUnit_of_dvd' ⟨ι, κ, hικ⟩ h hn)
    · exact hnu (IsCoprime.isUnit_of_dvd' hcop h hn)
  · have : (ℓ:ℤ) ∣ j*δ₀ := by
      have := dvd_sub h1' (dvd_mul_of_dvd_right (hg.trans hgδ) (i₀ + i))
      simpa [L] using this
    rcases Int.Prime.dvd_mul' hℓ this with h | h
    · exact hnu (IsCoprime.isUnit_of_dvd' hj h hg)
    · exact hnu (IsCoprime.isUnit_of_dvd' hδ₀ h hg)

end APLemma
end Bump
end Trop
end PeriodicDifference

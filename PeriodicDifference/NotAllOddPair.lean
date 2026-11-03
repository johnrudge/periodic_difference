/-
# `PeriodicDifference/NotAllOddPair.lean` — the two surviving pairings at odd minimum

* `full_of_E0E1` (`lem:nao-endend`): the class-`0` end failure `Cont 0 a` with a class-`1` end
  failure at an odd `i₁ ≤ a` forces, by primitivity, the full support.
* `struct_E0B1` (`thm:nao-struct`, the structure half): `Cont 0 a` with a class-`1` failure at
  an even `i₁` of the inner range `(a, μ]` (`μ` the paper's `b`) forces `i₁ = μ` and
  `S₁ = {a, a + μ, …, k − a}`.
-/
import PeriodicDifference.NotAllOddStruct

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace NotAllOdd

open Parity EvenMin

variable {k : ℕ} {S : Finset ℕ} {a μ : ℕ}

/-- `a ∣ t`, `a ∣ t − s`, `s ≤ t` give `a ∣ s`. -/
lemma dvd_of_sub {a t s : ℕ} (h1 : a ∣ t) (h2 : a ∣ t - s) (hst : s ≤ t) : a ∣ s := by
  have := Nat.dvd_sub h1 h2
  rwa [show t - (t - s) = s by omega] at this

/-- **`lem:nao-endend`.**  End failures of both classes force the full support. -/
theorem full_of_E0E1 (H : Setup k S a μ) (hao : a % 2 = 1)
    (hprim : ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ k → d = 1) {i₁ : ℕ}
    (hC0 : Cont k S 0 a) (hC1 : Cont k S 1 i₁) (h1o : i₁ % 2 = 1) (hi₁ : i₁ ≤ a) :
    ∀ y, 0 < y → y < k → y ∈ S := by
  have hk2 := H.keven
  have hak := H.sub a H.ha
  have hμe : μ % 2 = 0 := by have := H.bpar; omega
  have haμ := H.a_lt_b
  have hbl := H.b_le
  have h2a := H.two_a
  -- the odd chain, step `a + i₁`
  have stepO : ∀ y, (y ∈ S ∧ y % 2 = 1) → y ≠ k - a →
      (y + (a + i₁) ∈ S ∧ (y + (a + i₁)) % 2 = 1) := by
    rintro y ⟨hy, hyo⟩ hne
    have hyl := H.le_ka hy
    have h1 := hC0 y hy (by omega) (by omega)
    have h1l := H.le_kb h1 (by omega)
    have h2 := hC1 (a + y) h1 (by omega) (by omega)
    exact ⟨by rwa [show y + (a + i₁) = i₁ + (a + y) by omega], by omega⟩
  have chO := chain (T := fun y => y ∈ S ∧ y % 2 = 1) (d := a + i₁) (t := k - a) (by omega)
    (fun y hy => H.le_ka hy.1) stepO
  -- `μ = a + i₁`
  have hμd : μ = a + i₁ := by
    have hx := H.pal μ H.hb
    have h := hC1 (k - μ) hx (by omega) (by omega)
    have hl := H.le_ka h
    by_contra hne
    have h' := hC0 (i₁ + (k - μ)) h (by omega) (by omega)
    have := H.le_kb h' (by omega)
    omega
  -- the even chain, step `μ`
  have stepE : ∀ y, (y ∈ S ∧ y % 2 = 0) → y ≠ k - μ → (y + μ ∈ S ∧ (y + μ) % 2 = 0) := by
    rintro y ⟨hy, hye⟩ hne
    have hyl := H.le_kb hy (by omega)
    have h1 := hC1 y hy (by omega) (by omega)
    have h1l := H.le_ka h1
    have h2 := hC0 (i₁ + y) h1 (by omega) (by omega)
    exact ⟨by rwa [show y + μ = a + (i₁ + y) by omega], by omega⟩
  have chE := chain (T := fun y => y ∈ S ∧ y % 2 = 0) (d := μ) (t := k - μ) (by omega)
    (fun y hy => H.le_kb hy.1 (by omega)) stepE
  have d1 := (chO a ⟨H.ha, hao⟩).1
  have d2 := (chE μ ⟨H.hb, hμe⟩).1
  rw [← hμd] at d1
  have dk : μ ∣ k := by
    have := Nat.dvd_add d2 (dvd_mul_left μ 2)
    rwa [show k - μ - μ + 2 * μ = k by omega] at this
  have d2a : μ ∣ 2 * a := by
    have := Nat.dvd_sub dk d1
    rwa [show k - (k - a - a) = 2 * a by omega] at this
  obtain ⟨q, hq⟩ := d2a
  have hq1 : q = 1 := by
    rcases Nat.lt_or_ge q 2 with h | h
    · interval_cases q <;> omega
    · have : μ * 2 ≤ μ * q := Nat.mul_le_mul_left μ h
      omega
  subst hq1
  have hμ2 : μ = 2 * a := by omega
  have hi₁a : i₁ = a := by omega
  have hak' : a ∣ k := Nat.dvd_trans ⟨2, by ring⟩ (hμ2 ▸ dk)
  have hall : ∀ s ∈ S, a ∣ s := by
    intro s hs
    have hsk := H.sub s hs
    rcases Nat.mod_two_eq_zero_or_one s with hp | hp
    · have h := (chE s ⟨hs, hp⟩).1
      have hl := H.le_kb hs (by omega)
      refine dvd_of_sub (t := k - μ) ?_ ?_ hl
      · exact Nat.dvd_sub hak' ⟨2, by omega⟩
      · exact Nat.dvd_trans ⟨2, by omega⟩ h
    · have h := (chO s ⟨hs, hp⟩).1
      have hl := H.le_ka hs
      refine dvd_of_sub (t := k - a) ?_ ?_ hl
      · exact Nat.dvd_sub hak' (dvd_refl a)
      · exact Nat.dvd_trans ⟨2, by omega⟩ h
  have ha1 : a = 1 := hprim a hall hak'
  subst ha1
  subst hi₁a
  intro y hy0 hyk
  rcases Nat.mod_two_eq_zero_or_one y with hp | hp
  · have hm := (chO 1 ⟨H.ha, rfl⟩).2 ((y - 2) / 2) (by omega)
    have h := hC0 _ hm.1 (by omega) (by omega)
    rwa [show 1 + (1 + (1 + 1) * ((y - 2) / 2)) = y by omega] at h
  · have hm := (chO 1 ⟨H.ha, rfl⟩).2 (y / 2) (by omega)
    rw [show 1 + (1 + 1) * (y / 2) = y by omega] at hm
    exact hm.1

/-- **`thm:nao-struct`, the structure.**  `Cont 0 a` with a class-`1` failure at an even `i₁` of the
inner range `(a, μ]` forces `i₁ = μ`, `μ ∣ k − 2a`, and `S₁` the full progression. -/
theorem struct_E0B1 (H : Setup k S a μ) (hao : a % 2 = 1) {i₁ : ℕ}
    (hC0 : Cont k S 0 a) (hC1 : Cont k S 1 i₁) (h1e : i₁ % 2 = 0) (hai₁ : a < i₁)
    (hi₁ : i₁ ≤ μ) :
    i₁ = μ ∧ (∀ s ∈ S, s % 2 = 1 → μ ∣ (k - a) - s) ∧
      (∀ m, a + μ * m ≤ k - a → a + μ * m ∈ S) := by
  have hk2 := H.keven
  have hak := H.sub a H.ha
  have hμe : μ % 2 = 0 := by have := H.bpar; omega
  have haμ := H.a_lt_b
  have hbl := H.b_le
  have h2a := H.two_a
  -- the gap `S₁ ∩ (a, a + μ) = ∅`
  have gap : ∀ s ∈ S, s % 2 = 1 → a < s → a + μ ≤ s := by
    intro s hs hso has
    have hsk := H.sub s hs
    have h := hC0 (k - s) (H.pal s hs) (by omega) (by omega)
    have := H.le_kb h (by omega)
    omega
  have ha1 := hC1 a H.ha (by omega) (by omega)
  have hi₁μ : i₁ = μ := by have := gap _ ha1 (by omega) (by omega); omega
  subst hi₁μ
  have step : ∀ y, (y ∈ S ∧ y % 2 = 1) → y ≠ k - a → (y + i₁ ∈ S ∧ (y + i₁) % 2 = 1) := by
    rintro y ⟨hy, hyo⟩ hne
    have hyl := H.le_ka hy
    have hyk := H.sub y hy
    have hm := gap (k - y) (H.pal y hy) (by omega) (by omega)
    have h := hC1 y hy (by omega) (by omega)
    exact ⟨by rwa [Nat.add_comm], by omega⟩
  have ch := chain (T := fun y => y ∈ S ∧ y % 2 = 1) (d := i₁) (t := k - a) (by omega)
    (fun y hy => H.le_ka hy.1) step
  exact ⟨rfl, fun s hs hso => (ch s ⟨hs, hso⟩).1,
    fun m hm => ((ch a ⟨H.ha, hao⟩).2 m hm).1⟩

end NotAllOdd
end Bump
end Trop
end PeriodicDifference

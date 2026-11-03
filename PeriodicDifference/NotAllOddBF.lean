/-
# `PeriodicDifference/NotAllOddBF.lean` — `thm:nao-struct`: the both-failing structure

Even `k`, `S` primitive, palindromic, not all-odd, not the full support, `a = min S` odd.
If both parity carriers fail for every `σ` of their class, then (`bothfail_struct`), with
`μ = min S₀` (the paper's `b`) and `M = (k − 2a)/μ`:

  `k = 2a + μM`, `M ≥ 1`, `a < μ < 2a`, `S₁ = {a + μm : m ≤ M}`, `2a + μm ∈ S` for `m < M`.
-/
import PeriodicDifference.NotAllOddPair

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace NotAllOdd

open Parity EvenMin

/-- The structure of `thm:nao-struct`. -/
structure BF (k : ℕ) (S : Finset ℕ) (a μ M : ℕ) : Prop where
  keven : k % 2 = 0
  sub : ∀ j ∈ S, 0 < j ∧ j < k
  pal : ∀ j ∈ S, k - j ∈ S
  ha : a ∈ S
  amin : ∀ s ∈ S, a ≤ s
  hao : a % 2 = 1
  hμ : μ ∈ S
  hμe : μ % 2 = 0
  μmin : ∀ s ∈ S, s % 2 = 0 → μ ≤ s
  a_lt : a < μ
  lt_2a : μ < 2 * a
  hk : k = 2 * a + μ * M
  M_pos : 1 ≤ M
  odd_mem : ∀ s ∈ S, s % 2 = 1 → ∃ m ≤ M, s = a + μ * m
  ap_mem : ∀ m ≤ M, a + μ * m ∈ S
  core : ∀ m < M, 2 * a + μ * m ∈ S

variable {k : ℕ} {S : Finset ℕ} {a : ℕ}

/-- **`thm:nao-struct`.** -/
theorem bothfail_struct (hk2 : k % 2 = 0) (hS : ∀ j ∈ S, 0 < j ∧ j < k)
    (hpal : ∀ j ∈ S, k - j ∈ S) (hprim : ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ k → d = 1)
    (ha : a ∈ S) (hamin : ∀ s ∈ S, a ≤ s) (hao : a % 2 = 1)
    (heven : ∃ s ∈ S, s % 2 = 0) (hfull : ∃ y, 0 < y ∧ y < k ∧ y ∉ S)
    (F0 : ∀ σ ∈ S, σ % 2 = 0 → ¬ BumpSat k S σ (parQ k S σ 0))
    (F1 : ∀ σ ∈ S, σ % 2 = 1 → ¬ BumpSat k S σ (parQ k S σ 1)) :
    ∃ μ M, BF k S a μ M := by
  have hev : ∃ s, s ∈ S ∧ s % 2 = 0 := by obtain ⟨s, hs, h⟩ := heven; exact ⟨s, hs, h⟩
  have hb := Nat.find_spec hev
  set μ := Nat.find hev with hμdef
  have H : Setup k S a μ :=
    { keven := hk2, sub := hS, pal := hpal, ha := ha, amin := hamin, hb := hb.1
      bpar := by rw [hb.2, hao]; omega
      bmin := fun s hs hp => Nat.find_min' hev ⟨hs, by rw [hp, hb.2]⟩ }
  have hμe : μ % 2 = 0 := hb.2
  have hak := hS a ha
  have haμ := H.a_lt_b
  have hbl := H.b_le
  have h2a := H.two_a
  obtain ⟨y0, hy0, hy0k, hy0S⟩ := hfull
  have notfull : ∀ {i₁}, Cont k S 0 a → Cont k S 1 i₁ → i₁ % 2 = 1 → i₁ ≤ a → False :=
    fun hC0 hC1 h1 h2 => hy0S (full_of_E0E1 H hao hprim hC0 hC1 h1 h2 y0 hy0 hy0k)
  -- the class-0 failure
  obtain ⟨σ0, i0, hσ0, hσ0p, -, hi00, hi0k, hno0⟩ := missing_of_fail hk2 hS hpal hb.1 (F0 μ hb.1 hμe)
  obtain ⟨hC0', hloc0⟩ := loc0 H hao hσ0 (by omega) hi00 hi0k hno0
  -- the class-1 failure
  obtain ⟨σ1, i1, hσ1, hσ1p, -, hi10, hi1k, hno1⟩ := missing_of_fail hk2 hS hpal ha (F1 a ha hao)
  obtain ⟨hC1, hloc1⟩ := loc1 H hao hσ1 (by omega) hi10 hi1k hno1
  have hC0 : Cont k S 0 a := by
    rcases hloc0 with h | ⟨h1, h2, h3⟩
    · rwa [h] at hC0'
    · exfalso
      rcases hloc1 with ⟨g1, g2⟩ | ⟨g1, g2, g3⟩
      · exact no_B0_E1 H hao hC0' h1 h2 h3 hC1 g1 g2
      · exact no_B0_B1 H hao hC0' h1 h2 h3 hC1 g1 g2 g3
  -- the structure of the inner range `(a, μ]`
  have band : ∀ {σ i}, σ ∈ S → σ % 2 = 1 → 0 < i → i < k → ¬ OneRead k S σ 1 i →
      i = μ ∧ (∀ s ∈ S, s % 2 = 1 → μ ∣ (k - a) - s) ∧
        (∀ m, a + μ * m ≤ k - a → a + μ * m ∈ S) := by
    intro σ i hσ hσo hi0 hik hno
    obtain ⟨hC, hloc⟩ := loc1 H hao hσ hσo hi0 hik hno
    rcases hloc with ⟨g1, g2⟩ | ⟨g1, g2, g3⟩
    · exact (notfull hC0 hC g1 g2).elim
    · exact struct_E0B1 H hao hC0 hC g1 g2 g3
  obtain ⟨-, hodd, hap⟩ := band hσ1 (by omega) hi10 hi1k hno1
  obtain ⟨M, hM⟩ := hodd a ha hao
  have hμpos : 0 < μ := by omega
  have hk : k = 2 * a + μ * M := by omega
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; omega
    · exact h
  have hap' : ∀ m ≤ M, a + μ * m ∈ S := fun m hm =>
    hap m (by have := Nat.mul_le_mul_left μ hm; omega)
  have hcore : ∀ m < M, 2 * a + μ * m ∈ S := by
    intro m hm
    have h1 := hap' m hm.le
    have := Nat.mul_lt_mul_of_pos_left hm hμpos
    have hpe : (μ * m) % 2 = 0 := by rw [Nat.mul_mod, hμe, Nat.zero_mul, Nat.zero_mod]
    have h := hC0 _ h1 (by omega) (by omega)
    rwa [show a + (a + μ * m) = 2 * a + μ * m by ring] at h
  have hodd' : ∀ s ∈ S, s % 2 = 1 → ∃ m ≤ M, s = a + μ * m := by
    intro s hs hso
    obtain ⟨r, hr⟩ := hodd s hs hso
    have hsa := hamin s hs
    have hsl := H.le_ka hs
    have hrM : r ≤ M := by
      by_contra h
      have := Nat.mul_lt_mul_of_pos_left (show M < r by omega) hμpos
      omega
    refine ⟨M - r, by omega, ?_⟩
    rw [Nat.mul_sub]
    have := Nat.mul_le_mul_left μ hrM
    omega
  have h2aS := hcore 0 (by omega)
  rw [Nat.mul_zero, Nat.add_zero] at h2aS
  have hμ2a : μ ≤ 2 * a := H.bmin _ h2aS (by omega)
  have hlt : μ < 2 * a := by
    by_contra hne
    have hμ2 : μ = 2 * a := by omega
    rcases Nat.lt_or_ge M 2 with hM2 | hM2
    · -- `k = 4a`, `S = {a, 2a, 3a}`, so `a = 1` and `S` is full
      have hM1' : M = 1 := by omega
      subst hM1'
      have hall : ∀ s ∈ S, a ∣ s := by
        intro s hs
        rcases Nat.mod_two_eq_zero_or_one s with hp | hp
        · have := H.bmin s hs (by omega); have := H.le_kb hs (by omega)
          exact ⟨2, by omega⟩
        · obtain ⟨m, hm, rfl⟩ := hodd' s hs hp
          interval_cases m
          · exact ⟨1, by ring⟩
          · exact ⟨3, by omega⟩
      have ha1 : a = 1 := hprim a hall ⟨4, by omega⟩
      subst ha1
      have h3 := hap' 1 le_rfl
      have hk4 : k = 4 := by omega
      have : y0 = 1 ∨ y0 = 2 ∨ y0 = 3 := by omega
      rcases this with rfl | rfl | rfl
      · exact hy0S ha
      · exact hy0S (by rw [show (2 : ℕ) = μ by omega]; exact hb.1)
      · exact hy0S (by rw [show (3 : ℕ) = 1 + μ * 1 by omega]; exact h3)
    · -- `σ = 3a` has no failing index
      have hM2' := Nat.mul_le_mul_left μ hM2
      have h3 := hap' 1 (by omega)
      obtain ⟨σ3, i3, hσ3, hσ3p, hσ3e, hi30, hi3k, hno3⟩ :=
        missing_of_fail hk2 hS hpal h3 (F1 _ h3 (by omega))
      obtain ⟨hi3, -, -⟩ := band hσ3 (by omega) hi30 hi3k hno3
      refine hno3 (oneRead_hi_mem (j := k - a) (hpal a ha) (by omega) (by omega) ?_ ?_)
      · rcases hσ3e with h | h <;> omega
      · rw [show i3 + (k - a) - k = a by omega]; exact ha
  exact ⟨μ, M,
    { keven := hk2, sub := hS, pal := hpal, ha := ha, amin := hamin, hao := hao, hμ := hb.1
      hμe := hμe, μmin := fun s hs hp => H.bmin s hs (by rw [hp, hμe]), a_lt := haμ, lt_2a := hlt, hk := hk, M_pos := hM1
      odd_mem := hodd', ap_mem := hap', core := hcore }⟩

end NotAllOdd
end Bump
end Trop
end PeriodicDifference

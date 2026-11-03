/-
# `PeriodicDifference/EvenMin.lean` — `thm:nao-evenmin`, parity carriers at even minimum

Even `k`, palindromic `S`, `a = min S` even, `b` the least odd element.  If the class-`1`
parity carrier fails for one odd `σ₁`, the failure sits at an odd index
`i₁ ∈ (a, b]` with `(S₀ ∩ [1, k − 1 − i₁]) + i₁ ⊆ S₁` (`class1_fail`); that containment
empties `S₀ ∩ (i₁, i₁ + b)` (`gap`), and the gap hands the class-`0` carrier a read `1` at
every index for every even `σ₀` (`oneRead0`); the mirror supplies the reads `0`.
-/
import PeriodicDifference.EvenMinParity

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace EvenMin

open Parity

variable {k : ℕ} {S : Finset ℕ} {a b : ℕ}

/-- **The class-`1` failure.**  A missing read `1` of the class-`1` carrier sits at an odd
index `i ∈ (a, b]`, and gives the containment `(S₀ ∩ [1, k − 1 − i]) + i ⊆ S`. -/
theorem class1_fail (H : Setup k S a b) (hae : a % 2 = 0) {σ i : ℕ} (hσ : σ ∈ S)
    (hσo : σ % 2 = 1) (hi0 : 0 < i) (hik : i < k) (hno : ¬ OneRead k S σ 1 i) :
    i % 2 = 1 ∧ a < i ∧ i ≤ b ∧ ∀ s ∈ S, s % 2 = 0 → s + i < k → s + i ∈ S := by
  have hai : a < i := by
    by_contra h
    exact hno ((parityextreme H hσ (by omega) hσo hi0 (by omega)).1)
  obtain ⟨hib, hip⟩ := paritydichotomy H hσo hik hai hno
  refine ⟨by omega, hai, hib, fun s hs hse hsk => ?_⟩
  have := H.sub s hs
  by_cases hsσ : s + i = σ
  · rw [hsσ]; exact hσ
  · rcases lo_of_not_oneRead hno hs (by omega) (by omega) (by omega) with h | h
    · rwa [Nat.add_comm] at h
    · omega

/-- **The gap** `S₀ ∩ (i₁, i₁ + b) = ∅`. -/
theorem gap (H : Setup k S a b) {i₁ : ℕ} (h1o : i₁ % 2 = 1) (hbo : b % 2 = 1)
    (hcont : ∀ s ∈ S, s % 2 = 0 → s + i₁ < k → s + i₁ ∈ S)
    {s : ℕ} (hs : s ∈ S) (hse : s % 2 = 0) (h1 : i₁ < s) (h2 : s < i₁ + b) : False := by
  have hk2 := H.keven
  have hsk := H.sub s hs
  have ht := hcont (k - s) (H.pal s hs) (by omega) (by omega)
  have := H.le_kb ht (by omega)
  omega

/-- **The class-`0` reads `1`**, at every index and every even `σ₀ ∈ S`, given a class-`1`
failure index `i₁`. -/
theorem oneRead0 (H : Setup k S a b) (hae : a % 2 = 0) {i₁ : ℕ} (h1o : i₁ % 2 = 1)
    (hai₁ : a < i₁) (hi₁b : i₁ ≤ b) (hcont : ∀ s ∈ S, s % 2 = 0 → s + i₁ < k → s + i₁ ∈ S)
    {σ i : ℕ} (hσ : σ ∈ S) (hσe : σ % 2 = 0) (hi0 : 0 < i) (hik : i < k) :
    OneRead k S σ 0 i := by
  have hk2 := H.keven
  have hak := H.sub a H.ha
  have hbk := H.sub b H.hb
  have hbo : b % 2 = 1 := by have := H.bpar; omega
  have hab := H.a_lt_b
  have hbb := H.b_le
  have h2a := H.two_a
  have hapb := H.a_add_b
  have hσk := H.sub σ hσ
  rcases Nat.lt_trichotomy i a with hia | rfl | hai
  · rcases Nat.even_or_odd i with ⟨r, hr⟩ | ⟨r, hr⟩
    · -- even `i < a`: the tap `k − a`
      refine oneRead_lo (H.pal a H.ha) (by omega) (by omega) ?_ ?_ (by omega)
      · intro h; have := H.le_ka (h ▸ hσ); omega
      · intro h; have := H.le_ka h; omega
    · -- odd `i < a`: the tap `b` reaches into the gap
      refine oneRead_lo H.hb (by omega) (by omega) ?_ ?_ (by omega)
      · intro h; exact gap H h1o hbo hcont (h ▸ hσ) (by omega) (by omega) (by omega)
      · intro h; exact gap H h1o hbo hcont h (by omega) (by omega) (by omega)
  · -- the corner `i = a`
    by_contra hno
    have hclos : ∀ s ∈ S, s % 2 = 0 → s < k - i → i + s ∈ S := by
      intro s hs hse hsk
      have := H.sub s hs
      by_cases h : i + s = σ
      · rw [h]; exact hσ
      · rcases lo_of_not_oneRead hno hs (by omega) (by omega) h with h' | h'
        · exact h'
        · omega
    have key : ∀ d, ∀ s ∈ S, s % 2 = 0 → s + i₁ < k → k - s = d → False := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro s hs hse hsk hd
        have h1 := H.le_kb (hcont s hs hse hsk) (by omega)
        have hs' := hclos s hs hse (by omega)
        by_cases h2 : i + s + i₁ < k
        · exact ih (k - (i + s)) (by omega) _ hs' (by omega) h2 rfl
        · omega
    exact key _ i H.ha hae (by omega) rfl
  · by_contra hno
    obtain ⟨hib, hip⟩ := paritydichotomy H hσe hik hai hno
    -- the even index `i ∈ (a, b)`: the chain from `a` of step `i` stays in `[a, i₁]`
    have hcont0 : ∀ s ∈ S, s % 2 = 0 → s + i < k → s + i ∈ S := by
      intro s hs hse hsk
      have := H.sub s hs
      by_cases h : s + i = σ
      · rw [h]; exact hσ
      · rcases lo_of_not_oneRead hno hs (by omega) (by omega) (by omega) with h' | h'
        · rwa [Nat.add_comm] at h'
        · omega
    have chain : ∀ n, a + n * i ∈ S ∧ a + n * i ≤ i₁ := by
      intro n
      induction n with
      | zero => exact ⟨by simpa using H.ha, by omega⟩
      | succ n ih =>
        obtain ⟨h1, h2⟩ := ih
        have e : a + (n + 1) * i = a + n * i + i := by ring
        rw [e]
        have hin := hcont0 _ h1 (by
          have : (n * i) % 2 = 0 := by
            rw [Nat.mul_mod]; simp [show i % 2 = 0 by omega]
          omega) (by omega)
        refine ⟨hin, ?_⟩
        by_contra h3
        exact gap H h1o hbo hcont hin (by
          have : (n * i) % 2 = 0 := by
            rw [Nat.mul_mod]; simp [show i % 2 = 0 by omega]
          omega) (by omega) (by omega)
    have := (chain i₁).2
    have : i₁ ≤ i₁ * i := Nat.le_mul_of_pos_right _ (by omega)
    omega

/-- **`thm:nao-evenmin`.**  If the class-`1` parity carrier fails for one odd `σ₁ ∈ S`, the
class-`0` parity carrier is a σ-bump carrier for every even `σ₀ ∈ S`. -/
theorem evenmin (H : Setup k S a b) (hae : a % 2 = 0)
    (hfail : ∃ σ₁ ∈ S, σ₁ % 2 = 1 ∧ ¬ BumpSat k S σ₁ (parQ k S σ₁ 1)) :
    ∀ σ₀ ∈ S, σ₀ % 2 = 0 → BumpSat k S σ₀ (parQ k S σ₀ 0) := by
  obtain ⟨σ₁, hσ₁, hσ₁o, hnot⟩ := hfail
  have hk2 := H.keven
  have hσ₁k := H.sub σ₁ hσ₁
  obtain ⟨i, hi0, hik, hcl⟩ : ∃ i, 0 < i ∧ i < k ∧ ¬ Clause k S σ₁ (parQ k S σ₁ 1) i := by
    by_contra h
    push_neg at h
    exact hnot (bumpSat_parQ H.sub hσ₁ h)
  -- a missing read `1`, at `(i, σ₁)` or at the mirror `(k − i, k − σ₁)`
  obtain ⟨σ', i', hσ', hσ'o, hi'0, hi'k, hno⟩ : ∃ σ' i', σ' ∈ S ∧ σ' % 2 = 1 ∧ 0 < i' ∧
      i' < k ∧ ¬ OneRead k S σ' 1 i' := by
    by_cases hO : OneRead k S σ₁ 1 i
    · refine ⟨k - σ₁, k - i, H.pal σ₁ hσ₁, by omega, by omega, by omega, fun h => hcl ⟨hO, ?_⟩⟩
      exact zeroRead_of_mirror hk2 H.sub H.pal hσ₁ hi0 hik h
    · exact ⟨σ₁, i, hσ₁, hσ₁o, hi0, hik, hO⟩
  obtain ⟨h1o, hai₁, hi₁b, hcont⟩ := class1_fail H hae hσ' hσ'o hi'0 hi'k hno
  intro σ₀ hσ₀ hσ₀e
  have hσ₀k := H.sub σ₀ hσ₀
  refine bumpSat_parQ H.sub hσ₀ (fun j hj0 hjk => ⟨?_, ?_⟩)
  · exact oneRead0 H hae h1o hai₁ hi₁b hcont hσ₀ hσ₀e hj0 hjk
  · refine zeroRead_of_mirror hk2 H.sub H.pal hσ₀ hj0 hjk ?_
    exact oneRead0 H hae h1o hai₁ hi₁b hcont (H.pal σ₀ hσ₀) (by omega) (by omega) (by omega)

/-- `thm:nao-evenmin` in the paper's form: even `k`, `S ⊆ (0, k)` primitive and palindromic with
even minimum `a`.  If the class-`1` carrier fails for every odd `σ₁ ∈ S`, the class-`0`
carrier is valid for every even `σ₀ ∈ S`. -/
theorem evenmin_primitive (hk2 : k % 2 = 0) (hS : ∀ j ∈ S, 0 < j ∧ j < k)
    (hpal : ∀ j ∈ S, k - j ∈ S) (hprim : ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ k → d = 1)
    (ha : a ∈ S) (hamin : ∀ s ∈ S, a ≤ s) (hae : a % 2 = 0)
    (hfail : ∀ σ₁ ∈ S, σ₁ % 2 = 1 → ¬ BumpSat k S σ₁ (parQ k S σ₁ 1)) :
    ∀ σ₀ ∈ S, σ₀ % 2 = 0 → BumpSat k S σ₀ (parQ k S σ₀ 0) := by
  have hodd : ∃ s, s ∈ S ∧ s % 2 = 1 := by
    obtain ⟨s, hs, h⟩ := exists_odd_of_primitive hk2 hprim; exact ⟨s, hs, h⟩
  have hb := Nat.find_spec hodd
  have H : Setup k S a (Nat.find hodd) :=
    { keven := hk2, sub := hS, pal := hpal, ha := ha, amin := hamin, hb := hb.1
      bpar := by rw [hb.2, hae]; omega
      bmin := fun s hs hp => Nat.find_min' hodd ⟨hs, by rw [hp, hb.2]⟩ }
  exact evenmin H hae ⟨_, hb.1, hb.2, hfail _ hb.1 hb.2⟩

/-- **The parity carrier at even minimum.**  Every primitive palindromic support at even
order with even minimum carries a σ-bump on a parity carrier. -/
theorem evenmin_carrier (hk2 : k % 2 = 0) (hS : ∀ j ∈ S, 0 < j ∧ j < k)
    (hpal : ∀ j ∈ S, k - j ∈ S) (hprim : ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ k → d = 1)
    (ha : a ∈ S) (hamin : ∀ s ∈ S, a ≤ s) (hae : a % 2 = 0) :
    ∃ σ ∈ S, ∃ c, BumpSat k S σ (parQ k S σ c) := by
  by_cases h : ∀ σ₁ ∈ S, σ₁ % 2 = 1 → ¬ BumpSat k S σ₁ (parQ k S σ₁ 1)
  · exact ⟨a, ha, 0, evenmin_primitive hk2 hS hpal hprim ha hamin hae h a ha hae⟩
  · push_neg at h
    obtain ⟨σ, hσ, -, hB⟩ := h
    exact ⟨σ, hσ, 1, hB⟩

end EvenMin
end Bump
end Trop
end PeriodicDifference

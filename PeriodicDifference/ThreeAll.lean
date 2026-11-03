/-
# `PeriodicDifference/ThreeAll.lean` — `thm:allodd-threeall`: the half-arc carrier on `{a, h, k − a}`

`k = 2h`, `h` odd, `3 ≤ a < h` odd with `gcd(a, h) = 1`; `δ ∈ {2, 4}`,
`δ ≡ a + h (mod 4)`, `3δ < h`; `d ≡ a⁻¹(3h + δ) (mod 2k)`.  Then `halfQ k S a d 0` is a σ-bump
carrier with `σ = a` (`bumpSat_threeall`); `δ` and `d` are the paper's `β` and `ν`.  The
phases of the seven special indices are computed here (`Phases`); the case analysis is
`ThreeAllCore.core`; the reads of the taps are linearised by `read_lin`.
-/
import PeriodicDifference.ThreeAllCore

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace ThreeAll

open Finset HalfArc Shadow

/-- `x mod N` for `x < 2N`. -/
lemma mod2 {x N : ℕ} (hx : x < 2 * N) : (x < N ∧ x % N = x) ∨ (N ≤ x ∧ x % N = x - N) := by
  rcases Nat.lt_or_ge x N with h | h
  · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
  · exact Or.inr ⟨h, by rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]⟩

/-! ## The multiplier -/

/-- The multiplier `d = a⁻¹(3h + δ)`: `d ≡ 1 (mod 4)` and `da ≡ 3h + δ (mod 4h)`. -/
lemma exists_d {h a δ : ℕ} (hh : 1 ≤ h) (hho : h % 2 = 1) (hao : a % 2 = 1)
    (hcop : Nat.Coprime a h) (hδ4 : (3 * h + δ) % 4 = a % 4) (hδh : 3 * h + δ < 4 * h) :
    ∃ d, d % 4 = 1 ∧ d * a % (2 * (2 * h)) = 3 * h + δ := by
  have h4 : Nat.Coprime a 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hao))
  have hc : Nat.Coprime a (2 * (2 * h)) := by
    rw [show 2 * (2 * h) = 4 * h by ring]; exact Nat.Coprime.mul_right h4 hcop
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc (by omega)
  have hda : m * (3 * h + δ) * a % (2 * (2 * h)) = 3 * h + δ := by
    rw [show m * (3 * h + δ) * a = (a * m) * (3 * h + δ) by ring, Nat.mul_mod, hm, one_mul,
      Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  refine ⟨m * (3 * h + δ), ?_, hda⟩
  have h44 : m * (3 * h + δ) * a % 4 = a % 4 := by
    rw [← Nat.mod_mod_of_dvd _ (show 4 ∣ 2 * (2 * h) from ⟨h, by ring⟩), hda, hδ4]
  rw [Nat.mul_mod] at h44
  have := Nat.mod_lt (m * (3 * h + δ)) (show 0 < 4 by norm_num)
  have ha4 : a % 4 = 1 ∨ a % 4 = 3 := by omega
  interval_cases (m * (3 * h + δ) % 4) <;> rcases ha4 with h' | h' <;> rw [h'] at h44 <;>
    simp at h44

/-! ## The phases -/

section Phases

variable {h a d δ : ℕ}

lemma ph_h (hh : 1 ≤ h) (hd4 : d % 4 = 1) : ph (2 * h) d h = h := by
  unfold ph
  obtain ⟨q, rfl⟩ : ∃ q, d = 4 * q + 1 := ⟨d / 4, by omega⟩
  rw [show (4 * q + 1) * h = h + 2 * (2 * h) * q by ring, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by omega)]

lemma ph_add' (y z : ℕ) : ph (2 * h) d (y + z) = (ph (2 * h) d y + ph (2 * h) d z) % (2 * (2 * h)) :=
  phase_add y z

variable (hh : 3 * δ < h) (hah : a < h) (hδ : δ = 2 ∨ δ = 4) (hd4 : d % 4 = 1)
  (hda : ph (2 * h) d a = 3 * h + δ)
include hh hah hδ hd4 hda

omit hδ in
lemma ph_ka : ph (2 * h) d (2 * h - a) = 3 * h - δ := by
  have := phase_pair (d := d) (by omega) (show 0 < 2 * h by omega) (show a ≤ 2 * h by omega)
  omega

omit hah hδ in
lemma ph_ah : ph (2 * h) d (a + h) = δ := by
  rw [ph_add', hda, ph_h (by omega) hd4]
  rcases mod2 (x := 3 * h + δ + h) (N := 2 * (2 * h)) (by omega) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega

omit hah hd4 hδ in
lemma ph_2a : ph (2 * h) d (2 * a) = 2 * h + 2 * δ := by
  rw [two_mul a, ph_add', hda]
  rcases mod2 (x := 3 * h + δ + (3 * h + δ)) (N := 2 * (2 * h)) (by omega) with
    ⟨_, e⟩ | ⟨_, e⟩ <;> omega

omit hδ in
lemma ph_e : ph (2 * h) d (h - a) = 2 * h - δ := by
  have e1 := ph_add' (h := h) (d := d) (h - a) a
  rw [Nat.sub_add_cancel hah.le, ph_h (by omega) hd4, hda] at e1
  have hl : ph (2 * h) d (h - a) < 2 * (2 * h) := Nat.mod_lt _ (by omega)
  rcases mod2 (x := ph (2 * h) d (h - a) + (3 * h + δ)) (N := 2 * (2 * h)) (by omega) with
    ⟨_, e⟩ | ⟨_, e⟩ <;> omega

lemma ph_k2a : ph (2 * h) d (2 * h - 2 * a) = 4 * h - 2 * δ := by
  have e1 := ph_add' (h := h) (d := d) (2 * h - 2 * a) (2 * a)
  rw [Nat.sub_add_cancel (by omega), ph_2a hh hda] at e1
  have e2 : ph (2 * h) d (2 * h) = 2 * h := mul_k_mod (by omega) (by omega)
  have hl : ph (2 * h) d (2 * h - 2 * a) < 2 * (2 * h) := Nat.mod_lt _ (by omega)
  rcases mod2 (x := ph (2 * h) d (2 * h - 2 * a) + (2 * h + 2 * δ)) (N := 2 * (2 * h))
    (by omega) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega

end Phases

/-! ## The reads -/

section Reads

/-- The support `{a, h, 2h − a}`. -/
abbrev S3 (h a : ℕ) : Finset ℕ := {a, h, 2 * h - a}

variable {h a d : ℕ}

lemma mem_S3 {y : ℕ} : y ∈ S3 h a ↔ y = a ∨ y = h ∨ y = 2 * h - a := by
  simp [S3]

lemma mem_Q {y : ℕ} : y ∈ halfQ (2 * h) (S3 h a) a d 0 ↔
    y = a ∨ (y < 2 * h ∧ y ≠ 0 ∧ ¬ (y = a ∨ y = h ∨ y = 2 * h - a) ∧
      d * y % (2 * (2 * h)) < 2 * h) := by
  simp only [halfQ, mem_insert, mem_filter, mem_range, mem_singleton, ite_self, add_zero]

/-- **The read of a tap.**  An undeleted tap reads `1` at a wrapped pin, `0` at an
unwrapped pin, and the half-arc test of its phase at a free position. -/
lemma read_lin (hah : a < h) (hd : d % 2 = 1) {i j : ℕ} (hi0 : 0 < i) (hi : i < 2 * h)
    (hj : j < 2 * h) (hT : T h a (i + j)) :
    inP (2 * h) (halfQ (2 * h) (S3 h a) a d 0) (i + j) ↔
      V h a (i + j) (R (2 * h) (ph (2 * h) d i) (ph (2 * h) d j)) := by
  have hk : 0 < 2 * h := by omega
  unfold T at hT
  rcases Nat.lt_or_ge (i + j) (2 * h) with hl | hl
  · rw [inP_of_lt _ hl, mem_Q]
    by_cases hp : i + j = h ∨ i + j = 2 * h - a
    · unfold V; constructor
      · rintro (h1 | ⟨-, -, h2, -⟩) <;> omega
      · rintro (h1 | ⟨h1, h2, -⟩) <;> omega
    · rw [V_free (by omega) (by omega) (by omega) (by omega)]
      unfold ph; rw [← read_phase hk]
      constructor
      · rintro (h1 | ⟨-, -, -, h2⟩)
        · omega
        · exact h2
      · intro h2; exact Or.inr ⟨hl, by omega, by omega, h2⟩
  · obtain ⟨m, hm⟩ : ∃ m, i + j = 1 * (2 * h) + m := ⟨i + j - 2 * h, by omega⟩
    have hmk : m < 2 * h := by omega
    rw [hm, inP_qk_add_of_lt hk _ 1 hmk, wrap_iff, mem_Q, ← hm]
    by_cases hp : m = h ∨ m = 2 * h - a
    · unfold V; constructor
      · intro _; left; omega
      · intro _ h1; rcases h1 with h1 | ⟨-, -, h1, -⟩ <;> omega
    · rw [V_free (by omega) (by omega) (by omega) (by omega)]
      unfold ph; rw [← read_phase hk, hm, one_mul,
        phase_add_k hd hk, ← flip_half (Nat.mod_lt _ (by omega))]
      constructor
      · intro h1 h2; exact h1 (Or.inr ⟨hmk, by omega, by omega, h2⟩)
      · rintro h1 (h2 | ⟨-, -, -, h2⟩)
        · omega
        · exact h1 h2

end Reads

/-! ## `thm:allodd-threeall` -/

section Main

variable {h a d δ : ℕ}

/-- An undeleted tap avoids the two deletions of the clause. -/
lemma tap_ok {i j : ℕ} (hi0 : 0 < i) (hi : i < 2 * h) (hj : j < 2 * h) (hT : T h a (i + j)) :
    (i + j) % (2 * h) ≠ 0 ∧ (i + j) % (2 * h) ≠ a := by
  unfold T at hT
  rcases mod2 (x := i + j) (N := 2 * h) (by omega) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega

/-- **`thm:allodd-threeall`**, with `δ` and `d` given. -/
theorem bumpSat_of_d (hh : 3 * δ < h) (hho : h % 2 = 1) (hao : a % 2 = 1) (ha3 : 3 ≤ a)
    (hah : a < h) (hcop : Nat.Coprime a h) (hδ : δ = 2 ∨ δ = 4) (hd4 : d % 4 = 1)
    (hda : ph (2 * h) d a = 3 * h + δ) :
    BumpSat (2 * h) (S3 h a) a (halfQ (2 * h) (S3 h a) a d 0) := by
  have hd : d % 2 = 1 := by omega
  have h3a : h ≠ 3 * a := by
    intro e
    have := Nat.Coprime.eq_one_of_dvd hcop ⟨3, by omega⟩
    omega
  refine ⟨?_, by simp [S3], ?_, ?_⟩
  · intro j hj; rw [mem_S3] at hj; omega
  · ext y
    simp only [mem_inter, mem_insert, mem_Q, mem_singleton]
    constructor
    · rintro ⟨h1 | ⟨-, h2, h3, -⟩, h4⟩
      · exact h1
      · rcases h4 with h4 | h4 <;> tauto
    · rintro rfl; exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
  · intro i hi0 hik
    have hc : ph (2 * h) d i < 4 * h := by
      have := Nat.mod_lt (d * i) (show 0 < 2 * (2 * h) by omega); unfold ph; omega
    have K := core (c := ph (2 * h) d i) hh ha3 hah hao hho h3a hδ hi0 hik hc
      (fun e => by rw [e]; exact hda) (fun e => by rw [e]; exact ph_h (by omega) hd4)
      (fun e => by rw [e]; exact ph_ka hh hah hd4 hda)
      (fun e => by rw [e]; exact ph_ah hh hd4 hda)
      (fun e => by rw [e]; exact ph_2a hh hda)
      (fun e => by rw [e]; exact ph_e hh hah hd4 hda)
      (fun e => by rw [e]; exact ph_k2a hh hah hδ hd4 hda)
    have r1 : T h a (i + a) → (inP (2 * h) (halfQ (2 * h) (S3 h a) a d 0) (i + a) ↔
        V h a (i + a) (R (2 * h) (ph (2 * h) d i) (3 * h + δ))) := fun hT => by
      rw [read_lin hah hd hi0 hik (by omega) hT, hda]
    have r2 : T h a (i + h) → (inP (2 * h) (halfQ (2 * h) (S3 h a) a d 0) (i + h) ↔
        V h a (i + h) (R (2 * h) (ph (2 * h) d i) h)) := fun hT => by
      rw [read_lin hah hd hi0 hik (by omega) hT, ph_h (by omega) hd4]
    have r3 : T h a (i + (2 * h - a)) →
        (inP (2 * h) (halfQ (2 * h) (S3 h a) a d 0) (i + (2 * h - a)) ↔
        V h a (i + (2 * h - a)) (R (2 * h) (ph (2 * h) d i) (3 * h - δ))) := fun hT => by
      rw [read_lin hah hd hi0 hik (by omega) hT, ph_ka hh hah hd4 hda]
    have m1 : a ∈ S3 h a := mem_S3.mpr (Or.inl rfl)
    have m2 : h ∈ S3 h a := mem_S3.mpr (Or.inr (Or.inl rfl))
    have m3 : 2 * h - a ∈ S3 h a := mem_S3.mpr (Or.inr (Or.inr rfl))
    obtain ⟨K1, K2⟩ := K
    constructor
    · rcases K1 with ⟨hT, v⟩ | ⟨hT, v⟩ | ⟨hT, v⟩
      · exact ⟨a, m1, (tap_ok hi0 hik (by omega) hT).1, (tap_ok hi0 hik (by omega) hT).2, (r1 hT).mpr v⟩
      · exact ⟨h, m2, (tap_ok hi0 hik (by omega) hT).1, (tap_ok hi0 hik (by omega) hT).2, (r2 hT).mpr v⟩
      · exact ⟨_, m3, (tap_ok hi0 hik (by omega) hT).1, (tap_ok hi0 hik (by omega) hT).2,
          (r3 hT).mpr v⟩
    · rcases K2 with ⟨hT, v⟩ | ⟨hT, v⟩ | ⟨hT, v⟩
      · exact ⟨a, m1, (tap_ok hi0 hik (by omega) hT).1, (tap_ok hi0 hik (by omega) hT).2,
          fun p => v ((r1 hT).mp p)⟩
      · exact ⟨h, m2, (tap_ok hi0 hik (by omega) hT).1, (tap_ok hi0 hik (by omega) hT).2,
          fun p => v ((r2 hT).mp p)⟩
      · exact ⟨_, m3, (tap_ok hi0 hik (by omega) hT).1, (tap_ok hi0 hik (by omega) hT).2,
          fun p => v ((r3 hT).mp p)⟩

/-- **`thm:allodd-threeall`.**  For `k ≡ 2 (mod 4)` and `a` odd with `1 < a < k/2`,
`gcd(a, k/2) = 1`, and `k ≥ 14` if `a + k/2 ≡ 2 (mod 4)`, `k ≥ 26` otherwise (that is, `3δ < h`),
some multiplier `d` (namely `a⁻¹(3h + δ)`) makes the half-arc carrier `Q(d;0)` a σ-bump carrier
of `{a, k/2, k − a}` at `σ = a`. -/
theorem threeall (k a : ℕ) (hk4 : k % 4 = 2) (hk : 26 ≤ k ∨ (14 ≤ k ∧ (a + k / 2) % 4 = 2))
    (hao : a % 2 = 1) (ha1 : 1 < a) (hah : a < k / 2) (hcop : Nat.Coprime a (k / 2)) :
    ∃ d, BumpSat k {a, k / 2, k - a} a (halfQ k {a, k / 2, k - a} a d 0) := by
  obtain ⟨h, rfl⟩ : ∃ h, k = 2 * h := ⟨k / 2, by omega⟩
  have e : 2 * h / 2 = h := by omega
  rw [e] at hah hcop hk ⊢
  have hδ : (if (a + h) % 4 = 2 then 2 else 4) = 2 ∨ (if (a + h) % 4 = 2 then 2 else 4) = 4 := by
    split_ifs <;> simp
  obtain ⟨d, hd4, hda⟩ := exists_d (δ := if (a + h) % 4 = 2 then 2 else 4) (h := h) (by omega)
    (by omega) hao hcop (by split_ifs <;> omega) (by split_ifs <;> omega)
  exact ⟨d, bumpSat_of_d (by split_ifs <;> omega) (by omega) hao (by omega) hah hcop hδ hd4 hda⟩

end Main

end ThreeAll
end Bump
end Trop
end PeriodicDifference

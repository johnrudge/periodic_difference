/-
# `PeriodicDifference/SigmaBump.lean` — the σ-bump ray (`thm:sigmabump` / `def:bump`)

`PeriodicDifference/TropicalQpp.lean` proves Theorem Q″: an integer tangent orbit that is unbounded
along a periodic orbit of the min-plus map rules out global periodicity of the equation
for every choice of positive coefficients on the support.  There the periodic orbit,
the designated argmin word and the drift pair are *data* — a certificate, checked by
`decide`.  This file proves the same conclusion from a **criterion on residues**: the
σ-bump lemma of the paper (`thm:sigmabump`, in the clause form of `def:bump`).

## The objects

Order `k ≥ 2`, support `S ⊆ {1, …, k−1}`, a bit set `Q ⊆ [0, k)` coding the
anti-periodic set `P ⊆ ℤ/2k` by

  `n ∈ P  ⟺  (n/k even ↔ n mod k ∈ Q)`                                (`inP`)

and the constant-minimum carrier `E n = −1` if `n ∈ P`, `0` otherwise (`E`).  The
σ-bump is the closed form `eq:trop-bump` (`bump`): writing
`n = qk + i`,

  `d_{qk} = −q` (`q` even), `q + 1` (`q` odd);  `d_{qk+σ} = ±2` (sign `(−1)^q`);
  `d_{qk+i} = 0` otherwise.

`BumpSat k S σ Q` is the pair of clauses of `def:bump`:

  (B1) `Q ∩ ({0} ∪ S) = {σ}`;
  (B2) for every `i ∈ {1,…,k−1}` the map `j ↦ [i+j ∈ P]` is non-constant on
       `S ∖ {z(i), s(i)}`, where `i + z(i) ≡ 0` and `i + s(i) ≡ σ (mod k)` —
       i.e. there are `j, j' ∈ S` with `(i+j) mod k ∉ {0, σ}`, `(i+j') mod k ∉ {0, σ}`,
       `i + j ∈ P` and `i + j' ∉ P`.

## What is proved

* `E_add_k`, `isTrop_E` — `E` is an exact solution of the min-plus recursion for every
  slot list `J` whose nonzero slots are exactly `S`, with or without the constant slot
  `0`: the minimum is `−1 < 0`, so slot `0` never attains and **both θ are killed at
  once** (`mval_E`).
* `step` — the substitution of `thm:sigmabump`: at every `n` there is a tap `w ∈ S`
  attaining on `E`, minimising the bump among the attaining taps, and
  `d (n+k) + d n = d (n+w)`.  The margin needs only the two facts `0 ∉ Q`, `σ ∈ Q`
  from (B1): they say exactly that the negative entries of the bump sit **off** the
  carrier (`bump_nonneg_of_inP`), which is condition (ii) of `thm:sigmabump`.
* `bump_two_mul` — `d (2mk) = −2m`: the ray is unbounded.
* `not_tropPeriodic_of_ray` — any tangent ray along the carrier, given as a sequence
  `d` with a tap at every `n` that lies on `P`, minimises `d` among the taps on `P` and
  carries the tangent recursion, kills the support at both θ when `d` is not periodic.  The
  full support (`PeriodicDifference/FullSupport.lean`) is the other instance.
* `not_tropPeriodic_of_bumpSat` — the theorem: for every `J` with nonzero slots `S` and
  every `p ≥ 1`, `¬ TropPeriodic k J p`.  The proof is Theorem Q″'s two-scale argument with
  `pert_agree_tied`, the designated word being chosen from `step`.
* `not_globallyPeriodic_of_ray`, `not_globallyPeriodic_of_bumpSat` — the same for the
  equation, at every positive `co` on `J`, through `theoremP`
  (`GloballyPeriodic.tropPeriodic_of_supp`).

The dictionary with `theoremP` is the one of `PeriodicDifference/Bridge.lean`: the paper's order
`k` is Lean's `GloballyPeriodic k J co p` with slots `j < k`, i.e. `theoremP` at
`k − 1`.
-/

import PeriodicDifference.TropicalQpp
import PeriodicDifference.ModArith

namespace PeriodicDifference
namespace Trop
namespace Bump

/-! ## The carrier -/

/-- `n ∈ P`, for the anti-periodic `P ⊆ ℤ/2k` coded by `Q = P ∩ [0, k)`: for `n = qk + m`
with `m < k`, `n ∈ P ⟺ m ∈ Q` when `q` is even and `n ∈ P ⟺ m ∉ Q` when `q` is odd. -/
def inP (k : ℕ) (Q : Finset ℕ) (n : ℕ) : Prop := ((n / k) % 2 = 0 ↔ n % k ∈ Q)

instance (k : ℕ) (Q : Finset ℕ) : DecidablePred (inP k Q) :=
  fun n => inferInstanceAs (Decidable ((n / k) % 2 = 0 ↔ n % k ∈ Q))

/-- The constant-minimum carrier sequence: `−1` on `P`, `0` off it. -/
def E (k : ℕ) (Q : Finset ℕ) (n : ℕ) : ℤ := if inP k Q n then -1 else 0

/-- The σ-bump, `eq:trop-bump`. -/
def bump (k σ : ℕ) (n : ℕ) : ℤ :=
  if n % k = 0 then (if (n / k) % 2 = 0 then -((n / k : ℕ) : ℤ) else ((n / k : ℕ) : ℤ) + 1)
  else if n % k = σ then (if (n / k) % 2 = 0 then 2 else -2)
  else 0

/-- `d 0 = 0`: the ray starts at the origin. -/
lemma bump_zero (k σ : ℕ) : bump k σ 0 = 0 := by
  simp [bump]

/-- The hypotheses of `thm:sigmabump`, in the clause form of `def:bump`. -/
structure BumpSat (k : ℕ) (S : Finset ℕ) (σ : ℕ) (Q : Finset ℕ) : Prop where
  /-- `S ⊆ {1, …, k − 1}` -/
  S_sub : ∀ j ∈ S, 0 < j ∧ j < k
  /-- `σ ∈ S` -/
  σ_mem : σ ∈ S
  /-- (B1): `Q ∩ ({0} ∪ S) = {σ}` -/
  B1 : Q ∩ insert 0 S = {σ}
  /-- (B2): `j ↦ [i + j ∈ P]` is non-constant on `S ∖ {z(i), s(i)}`, for `0 < i < k` -/
  B2 : ∀ i, 0 < i → i < k →
    (∃ j ∈ S, (i + j) % k ≠ 0 ∧ (i + j) % k ≠ σ ∧ inP k Q (i + j)) ∧
    (∃ j ∈ S, (i + j) % k ≠ 0 ∧ (i + j) % k ≠ σ ∧ ¬ inP k Q (i + j))

/-! ## Consequences of (B1) -/

namespace BumpSat

variable {k : ℕ} {S : Finset ℕ} {σ : ℕ} {Q : Finset ℕ}

lemma σ_pos (h : BumpSat k S σ Q) : 0 < σ := (h.S_sub σ h.σ_mem).1

lemma σ_lt (h : BumpSat k S σ Q) : σ < k := (h.S_sub σ h.σ_mem).2

lemma two_le (h : BumpSat k S σ Q) : 2 ≤ k := by
  have := h.σ_pos; have := h.σ_lt; omega

lemma k_pos (h : BumpSat k S σ Q) : 0 < k := by have := h.two_le; omega

lemma mem_B1 (h : BumpSat k S σ Q) {j : ℕ} : j ∈ Q ∩ insert 0 S ↔ j = σ := by
  rw [h.B1, Finset.mem_singleton]

lemma σ_mem_Q (h : BumpSat k S σ Q) : σ ∈ Q :=
  (Finset.mem_inter.mp (h.mem_B1.mpr rfl)).1

lemma zero_not_mem_Q (h : BumpSat k S σ Q) : 0 ∉ Q := by
  intro h0
  have h1 : (0 : ℕ) ∈ Q ∩ insert 0 S :=
    Finset.mem_inter.mpr ⟨h0, Finset.mem_insert_self _ _⟩
  have h2 := h.mem_B1.mp h1
  have := h.σ_pos
  omega

lemma eq_σ_of_mem (h : BumpSat k S σ Q) {j : ℕ} (hj : j ∈ S) (hjQ : j ∈ Q) : j = σ :=
  h.mem_B1.mp (Finset.mem_inter.mpr ⟨hjQ, Finset.mem_insert_of_mem hj⟩)

/-- `S ∖ {σ}` is nonempty: (B2) at `i = 1` needs two taps of `S`. -/
lemma exists_ne_σ (h : BumpSat k S σ Q) : ∃ j ∈ S, j ≠ σ := by
  obtain ⟨⟨j, hj, -, -, hjP⟩, ⟨j', hj', -, -, hj'P⟩⟩ :=
    h.B2 1 Nat.one_pos (by have := h.two_le; omega)
  by_cases hjσ : j = σ
  · refine ⟨j', hj', fun hj'σ => hj'P ?_⟩
    rw [hj'σ, ← hjσ]; exact hjP
  · exact ⟨j, hj, hjσ⟩

end BumpSat

/-! ## Division arithmetic for `n = qk + m` -/

section Arith

variable {k : ℕ} (hk : 0 < k)
include hk

lemma div_qk_add (q m : ℕ) : (q * k + m) / k = q + m / k := by
  rw [Nat.mul_comm q k]; exact Nat.mul_add_div hk q m

omit hk in
lemma mod_qk_add (q m : ℕ) : (q * k + m) % k = m % k := Nat.mul_add_mod' q k m

lemma div_qk_add_of_lt {m : ℕ} (hm : m < k) (q : ℕ) : (q * k + m) / k = q := by
  rw [div_qk_add hk, Nat.div_eq_of_lt hm, Nat.add_zero]

omit hk in
lemma mod_qk_add_of_lt {m : ℕ} (hm : m < k) (q : ℕ) : (q * k + m) % k = m := by
  rw [mod_qk_add, Nat.mod_eq_of_lt hm]

/-! ### The carrier -/

variable (Q : Finset ℕ)

/-- Anti-periodicity: `n + k ∈ P ⟺ n ∉ P`. -/
lemma inP_add_k (n : ℕ) : inP k Q (n + k) ↔ ¬ inP k Q n := by
  unfold inP
  rw [Nat.add_div_right n hk, Nat.add_mod_right]
  by_cases hQ : n % k ∈ Q <;> simp only [hQ, iff_true, iff_false, not_not] <;> omega

/-- Shifting by `q` blocks flips membership `q` times. -/
lemma inP_qk_add (q m : ℕ) : inP k Q (q * k + m) ↔ (q % 2 = 0 ↔ inP k Q m) := by
  unfold inP
  rw [div_qk_add hk, mod_qk_add]
  by_cases hQ : m % k ∈ Q <;> simp only [hQ, iff_true, iff_false] <;> omega

omit hk in
lemma inP_of_lt {m : ℕ} (hm : m < k) : inP k Q m ↔ m ∈ Q := by
  unfold inP
  rw [Nat.div_eq_of_lt hm, Nat.mod_eq_of_lt hm]
  simp

lemma inP_qk_add_of_lt (q : ℕ) {m : ℕ} (hm : m < k) :
    inP k Q (q * k + m) ↔ (q % 2 = 0 ↔ m ∈ Q) := by
  rw [inP_qk_add hk, inP_of_lt Q hm]

/-- `E` is an exact solution: `E (n+k) + E n = −1`. -/
lemma E_add_k (n : ℕ) : E k Q (n + k) + E k Q n = -1 := by
  have h := inP_add_k hk Q n
  unfold E
  by_cases hn : inP k Q n
  · rw [if_pos hn, if_neg (fun h' => h.mp h' hn)]; norm_num
  · rw [if_neg hn, if_pos (h.mpr hn)]; norm_num

/-! ### The bump -/

lemma bump_qk_add {m : ℕ} (hm : m < k) (σ q : ℕ) : bump k σ (q * k + m) =
    if m = 0 then (if q % 2 = 0 then -(q : ℤ) else (q : ℤ) + 1)
    else if m = σ then (if q % 2 = 0 then 2 else -2) else 0 := by
  unfold bump
  rw [div_qk_add_of_lt hk hm, mod_qk_add_of_lt hm]

/-- `d (2mk) = −2m`: the ray is unbounded. -/
lemma bump_two_mul (σ p : ℕ) : bump k σ (2 * k * p) = -2 * (p : ℤ) := by
  have e : 2 * k * p = (2 * p) * k + 0 := by ring
  rw [e, bump_qk_add hk hk σ (2 * p), if_pos rfl, if_pos (Nat.mul_mod_right 2 p)]
  push_cast; ring

omit hk in
/-- Condition (ii) of `thm:sigmabump`: on the carrier the bump is nonnegative — the
negative entries `d_{2mk}` and `d_{(2m+1)k+σ}` sit off `P` because `0 ∉ Q`, `σ ∈ Q`. -/
lemma bump_nonneg_of_inP {σ : ℕ} (h0 : 0 ∉ Q) (hσ : σ ∈ Q) (n : ℕ) (hn : inP k Q n) :
    0 ≤ bump k σ n := by
  unfold inP at hn
  unfold bump
  by_cases h1 : n % k = 0
  · rw [if_pos h1]
    rw [h1] at hn
    by_cases h2 : n / k % 2 = 0
    · exact absurd (hn.mp h2) h0
    · rw [if_neg h2]; exact Int.le_add_one (Int.natCast_nonneg _)
  · rw [if_neg h1]
    by_cases h3 : n % k = σ
    · rw [if_pos h3]
      rw [h3] at hn
      rw [if_pos (hn.mpr hσ)]; norm_num
    · rw [if_neg h3]

/-- The left-hand side of the tangent recursion: `2` at `n = 2mk`, `0` elsewhere. -/
lemma bump_add_k (σ n : ℕ) : bump k σ (n + k) + bump k σ n =
    if n % k = 0 ∧ n / k % 2 = 0 then 2 else 0 := by
  obtain ⟨q, m, hm, rfl⟩ : ∃ q m, m < k ∧ n = q * k + m :=
    ⟨n / k, n % k, Nat.mod_lt _ hk, (Nat.div_add_mod' n k).symm⟩
  have e : q * k + m + k = (q + 1) * k + m := by ring
  rw [e, bump_qk_add hk hm, bump_qk_add hk hm, div_qk_add_of_lt hk hm, mod_qk_add_of_lt hm]
  split_ifs <;> omega

end Arith

/-! ## The substitution of `thm:sigmabump`

At `n = qk + i` a read `d (n + j)` is nonzero only for `j = z(i)` or `j = s(i)`; (B2)
supplies a tap outside these reading `0` and attaining on `E`, and
`bump_nonneg_of_inP` forbids a negative read at any attaining tap.  At `i = 0` the
recursion asks for `2` (`q` even) or `0` (`q` odd), which is (B1). -/

/-- **The tangent step.**  At every `n` some tap `w ∈ S` attains on `E`, minimises the
bump among the attaining taps, and carries the recursion `d (n+k) + d n = d (n+w)`. -/
theorem step {k : ℕ} {S : Finset ℕ} {σ : ℕ} {Q : Finset ℕ} (h : BumpSat k S σ Q) (n : ℕ) :
    ∃ w ∈ S, inP k Q (n + w) ∧
      (∀ j ∈ S, inP k Q (n + j) → bump k σ (n + w) ≤ bump k σ (n + j)) ∧
      bump k σ (n + k) + bump k σ n = bump k σ (n + w) := by
  have hk := h.k_pos
  obtain ⟨q, i, hi, rfl⟩ : ∃ q i, i < k ∧ n = q * k + i :=
    ⟨n / k, n % k, Nat.mod_lt _ hk, (Nat.div_add_mod' n k).symm⟩
  have hsum := bump_add_k hk σ (q * k + i)
  rw [div_qk_add_of_lt hk hi, mod_qk_add_of_lt hi] at hsum
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hq : q % 2 = 0
    · -- `q` even: the tap is `σ`, the only attaining one, and the recursion reads `2`
      refine ⟨σ, h.σ_mem, ?_, ?_, ?_⟩
      · rw [Nat.add_zero, inP_qk_add_of_lt hk Q q h.σ_lt]
        exact ⟨fun _ => h.σ_mem_Q, fun _ => hq⟩
      · intro j hj hjP
        rw [Nat.add_zero, inP_qk_add_of_lt hk Q q (h.S_sub j hj).2] at hjP
        have hjσ : j = σ := h.eq_σ_of_mem hj (hjP.mp hq)
        subst hjσ
        exact le_rfl
      · rw [hsum, if_pos ⟨rfl, hq⟩, Nat.add_zero, bump_qk_add hk h.σ_lt,
          if_neg (by have := h.σ_pos; omega), if_pos rfl, if_pos hq]
    · -- `q` odd: every tap but `σ` attains, all reads are `0`
      obtain ⟨j₀, hj₀, hj₀σ⟩ := h.exists_ne_σ
      have hj₀Q : j₀ ∉ Q := fun hQ => hj₀σ (h.eq_σ_of_mem hj₀ hQ)
      have hj₀0 : ¬ j₀ = 0 := by have := (h.S_sub j₀ hj₀).1; omega
      refine ⟨j₀, hj₀, ?_, ?_, ?_⟩
      · rw [Nat.add_zero, inP_qk_add_of_lt hk Q q (h.S_sub j₀ hj₀).2]
        exact ⟨fun h' => absurd h' hq, fun h' => absurd h' hj₀Q⟩
      · intro j hj hjP
        rw [Nat.add_zero, inP_qk_add_of_lt hk Q q (h.S_sub j hj).2] at hjP
        have hjQ : j ∉ Q := fun hQ => hq (hjP.mpr hQ)
        have hjσ : ¬ j = σ := fun e => hjQ (e ▸ h.σ_mem_Q)
        have hj0 : ¬ j = 0 := by have := (h.S_sub j hj).1; omega
        rw [Nat.add_zero, bump_qk_add hk (h.S_sub j hj).2, bump_qk_add hk (h.S_sub j₀ hj₀).2,
          if_neg hj0, if_neg hjσ, if_neg hj₀0, if_neg hj₀σ]
      · rw [hsum, if_neg (fun h' => hq h'.2), Nat.add_zero, bump_qk_add hk (h.S_sub j₀ hj₀).2,
          if_neg hj₀0, if_neg hj₀σ]
  · -- `i ≠ 0`: (B2) supplies a tap reading `0`; attaining taps read `≥ 0`
    obtain ⟨⟨j₁, hj₁, hj₁0, hj₁σ, hj₁P⟩, ⟨j₂, hj₂, hj₂0, hj₂σ, hj₂P⟩⟩ :=
      h.B2 i (Nat.pos_of_ne_zero hi0) hi
    have hread : ∀ j, (i + j) % k ≠ 0 → (i + j) % k ≠ σ → bump k σ (q * k + i + j) = 0 := by
      intro j h0 hσ
      have e : q * k + i + j = q * k + (i + j) := by ring
      rw [e]
      unfold bump
      rw [mod_qk_add, if_neg h0, if_neg hσ]
    have hsum0 : bump k σ (q * k + i + k) + bump k σ (q * k + i) = 0 := by
      rw [hsum, if_neg (fun h' => hi0 h'.1)]
    have hmarg : ∀ w, bump k σ (q * k + i + w) = 0 → ∀ j ∈ S, inP k Q (q * k + i + j) →
        bump k σ (q * k + i + w) ≤ bump k σ (q * k + i + j) := by
      intro w hw j _ hjP
      rw [hw]
      exact bump_nonneg_of_inP Q h.zero_not_mem_Q h.σ_mem_Q _ hjP
    by_cases hq : q % 2 = 0
    · refine ⟨j₁, hj₁, ?_, hmarg j₁ (hread j₁ hj₁0 hj₁σ), ?_⟩
      · have e : q * k + i + j₁ = q * k + (i + j₁) := by ring
        rw [e, inP_qk_add hk]
        exact ⟨fun _ => hj₁P, fun _ => hq⟩
      · rw [hsum0, hread j₁ hj₁0 hj₁σ]
    · refine ⟨j₂, hj₂, ?_, hmarg j₂ (hread j₂ hj₂0 hj₂σ), ?_⟩
      · have e : q * k + i + j₂ = q * k + (i + j₂) := by ring
        rw [e, inP_qk_add hk]
        exact ⟨fun h' => absurd h' hq, fun h' => absurd h' hj₂P⟩
      · rw [hsum0, hread j₂ hj₂0 hj₂σ]

/-- Covering: every window meets `P`. -/
lemma covering {k : ℕ} {S : Finset ℕ} {σ : ℕ} {Q : Finset ℕ} (h : BumpSat k S σ Q) (n : ℕ) :
    ∃ j ∈ S, inP k Q (n + j) := by
  obtain ⟨w, hw, hwP, -, -⟩ := step h n
  exact ⟨w, hw, hwP⟩

/-! ## The slot dictionary

`J` is any slot list whose nonzero slots are exactly `S`; slot `0`, the constant term,
may or may not be present.  Because the minimum of `E` over the window is `−1 < 0`, a
slot attains iff it is a tap `j ∈ S` with `n + j ∈ P`. -/

section Slots

variable {k : ℕ} (Q : Finset ℕ)

lemma slot_E_ge (n j : ℕ) : -1 ≤ slot (E k Q) n j := by
  unfold slot E
  split_ifs <;> norm_num

lemma slot_E_eq_iff (n j : ℕ) : slot (E k Q) n j = -1 ↔ (j ≠ 0 ∧ inP k Q (n + j)) := by
  unfold slot E
  by_cases hj : j = 0
  · simp [hj]
  · by_cases hP : inP k Q (n + j) <;> simp [hj, hP]

variable {S : Finset ℕ} {J : List ℕ} (hSJ : ∀ j ∈ S, j ∈ J) (hS : ∀ j ∈ S, 0 < j ∧ j < k)
include hSJ hS

/-- The minimum is `−1` at every step; in particular the constant slot never attains. -/
lemma mval_E (n : ℕ) (hcov : ∃ j ∈ S, inP k Q (n + j)) : mval J (E k Q) n = -1 := by
  obtain ⟨j₀, hj₀, hP⟩ := hcov
  have hJne : J ≠ [] := List.ne_nil_of_mem (hSJ j₀ hj₀)
  apply le_antisymm
  · have h := mval_le (e := E k Q) (n := n) (hSJ j₀ hj₀)
    rw [(slot_E_eq_iff Q n j₀).mpr ⟨(hS j₀ hj₀).1.ne', hP⟩] at h
    exact h
  · obtain ⟨j, -, hje⟩ := mval_attained hJne (E k Q) n
    rw [hje]; exact slot_E_ge Q n j

/-- **`E` is an exact integer solution of the min-plus recursion**, for both θ. -/
lemma isTrop_E (hk : 0 < k) (hcov : ∀ n, ∃ j ∈ S, inP k Q (n + j)) :
    IsTrop k J (E k Q) := by
  intro n
  rw [mval_E Q hSJ hS n (hcov n)]
  exact E_add_k hk Q n

variable (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S)
include hJS

/-- A word of attaining taps that minimise `d` among the attaining taps, in the form
`pert_agree_tied` wants. -/
lemma hwd_of_step {d : ℕ → ℤ} {wd : ℕ → ℕ}
    (hwd : ∀ n, wd n ∈ S ∧ inP k Q (n + wd n) ∧
      (∀ j ∈ S, inP k Q (n + j) → d (n + wd n) ≤ d (n + j))) (n : ℕ) :
    wd n ∈ J ∧ slot (E k Q) n (wd n) = mval J (E k Q) n ∧
      ∀ j ∈ J, slot (E k Q) n j = mval J (E k Q) n → slot d n (wd n) ≤ slot d n j := by
  obtain ⟨hwS, hwP, hmarg⟩ := hwd n
  have hw0 : wd n ≠ 0 := (hS _ hwS).1.ne'
  have hm : mval J (E k Q) n = -1 := mval_E Q hSJ hS n ⟨_, hwS, hwP⟩
  refine ⟨hSJ _ hwS, ?_, ?_⟩
  · rw [hm]; exact (slot_E_eq_iff Q n _).mpr ⟨hw0, hwP⟩
  · intro j hj hje
    rw [hm, slot_E_eq_iff] at hje
    obtain ⟨hj0, hjP⟩ := hje
    have hjS : j ∈ S := (hJS j hj).resolve_left hj0
    simp only [slot, if_neg hw0, if_neg hj0]
    exact hmarg j hjS hjP

end Slots

/-! ## The theorem -/

/-- **A tangent ray along a constant-minimum carrier kills the support, at both θ.**  Let
`d` be an integer sequence such that at every `n` some tap `w ∈ S` lies on the carrier `P`
coded by `Q`, minimises `d` among the taps on `P`, and carries `d (n+k) + d n = d (n+w)`.  If
`d` is not `p`-periodic then, for every slot list `J` whose nonzero slots are exactly `S`
(the constant slot `0` present or not), the min-plus map does not have `p`-th power the
identity.  This is `not_tropPeriodic_of_tangent` with `E` the carrier (`isTrop_E`) and the word
read off the hypothesis (`hwd_of_step`). -/
theorem not_tropPeriodic_of_ray {k : ℕ} {S : Finset ℕ} {Q : Finset ℕ} {d : ℕ → ℤ}
    (hk : 0 < k) (hS : ∀ j ∈ S, 0 < j ∧ j < k)
    (hstep : ∀ n, ∃ w ∈ S, inP k Q (n + w) ∧
      (∀ j ∈ S, inP k Q (n + j) → d (n + w) ≤ d (n + j)) ∧ d (n + k) + d n = d (n + w))
    {p : ℕ} (hnp : ∃ m n, d (n + m * p) ≠ d n)
    {J : List ℕ} (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S) (hSJ : ∀ j ∈ S, j ∈ J) :
    ¬ TropPeriodic k J p := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hJk : ∀ j ∈ J, j ≤ k' := by
    intro j hj
    rcases hJS j hj with rfl | hjS
    · exact Nat.zero_le _
    · have := (hS j hjS).2; omega
  choose wd hwd using hstep
  have hwd' := hwd_of_step Q hSJ hS hJS (d := d)
    fun n => ⟨(hwd n).1, (hwd n).2.1, (hwd n).2.2.1⟩
  refine not_tropPeriodic_of_tangent (List.ne_nil_of_mem (hSJ _ (hwd 0).1)) hJk
    (isTrop_E Q hSJ hS hk fun n => ⟨wd n, (hwd n).1, (hwd n).2.1⟩)
    (fun n => ⟨wd n, (hwd' n).1, (hwd' n).2.1, (hwd' n).2.2, ?_⟩) hnp
  have hw0 : wd n ≠ 0 := (hS _ (hwd n).1).1.ne'
  simp only [slot, if_neg hw0]
  exact (hwd n).2.2.2

/-- `not_tropPeriodic_of_ray` for the equation: by `thm:P`
(`GloballyPeriodic.tropPeriodic_of_supp`), no positive coefficient choice on `J` makes it
globally `p`-periodic. -/
theorem not_globallyPeriodic_of_ray {k : ℕ} {S : Finset ℕ} {Q : Finset ℕ} {d : ℕ → ℤ}
    (hk : 0 < k) (hS : ∀ j ∈ S, 0 < j ∧ j < k)
    (hstep : ∀ n, ∃ w ∈ S, inP k Q (n + w) ∧
      (∀ j ∈ S, inP k Q (n + j) → d (n + w) ≤ d (n + j)) ∧ d (n + k) + d n = d (n + w))
    {p : ℕ} (hnp : ∃ m n, d (n + m * p) ≠ d n)
    {J : List ℕ} (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S) (hSJ : ∀ j ∈ S, j ∈ J)
    {co : ℕ → ℝ} (hco : ∀ j ∈ J, 0 < co j) : ¬ GloballyPeriodic k J co p := by
  obtain ⟨w, hw, -⟩ := hstep 0
  exact fun hg => not_tropPeriodic_of_ray hk hS hstep hnp hJS hSJ
    (hg.tropPeriodic_of_supp hS ⟨w, hw⟩ hJS hSJ hco)

/-- **The σ-bump kills the support, for the min-plus map at both θ.**  If `BumpSat k S σ Q`
holds, then for every slot list `J` whose nonzero slots are exactly `S` (the constant slot `0`
present or not) and every `p ≥ 1`, the min-plus map does not have `p`-th power the identity.

The proof is Theorem Q″'s: `E` is an exact solution (`isTrop_E`); `step` chooses the
word; `pert_agree_tied` pins the min-plus solution started at `(2B+1)·E + d` to that
ray on `[0, 2kp + k)`; `p`-periodicity of both gives `d (2kp) = d 0 = 0`; but
`d (2kp) = −2p`. -/
theorem not_tropPeriodic_of_bumpSat {k : ℕ} {S : Finset ℕ} {σ : ℕ} {Q : Finset ℕ}
    (h : BumpSat k S σ Q) {J : List ℕ} (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S)
    (hSJ : ∀ j ∈ S, j ∈ J) {p : ℕ} (hp : 0 < p) : ¬ TropPeriodic k J p := by
  have hk := h.k_pos
  refine not_tropPeriodic_of_ray hk h.S_sub (step h) ⟨2 * k, 0, ?_⟩ hJS hSJ
  -- the ray drifts: `d (2kp) = −2p ≠ 0 = d 0`
  rw [zero_add, bump_two_mul hk, bump_zero]
  omega

/-- **The σ-bump kills the support, at both θ and for every positive coefficient
choice.**  If `BumpSat k S σ Q` holds, then for every slot list `J` whose nonzero slots
are exactly `S` (the constant slot `0` present or not), every `co` positive on `J` and
every `p ≥ 1`, the min-plus problem — hence, through `PeriodicDifference/Bridge.lean`, the
equation — is not globally `p`-periodic: `not_tropPeriodic_of_bumpSat` and `thm:P`. -/
theorem not_globallyPeriodic_of_bumpSat {k : ℕ} {S : Finset ℕ} {σ : ℕ} {Q : Finset ℕ}
    (h : BumpSat k S σ Q) {J : List ℕ} (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S)
    (hSJ : ∀ j ∈ S, j ∈ J) {co : ℕ → ℝ} (hco : ∀ j ∈ J, 0 < co j) {p : ℕ} (hp : 0 < p) :
    ¬ GloballyPeriodic k J co p := fun hg =>
  not_tropPeriodic_of_bumpSat h hJS hSJ hp
    (hg.tropPeriodic_of_supp h.S_sub ⟨σ, h.σ_mem⟩ hJS hSJ hco)

/-! ## Decidability of `BumpSat` -/

section Decide

variable {k : ℕ} {S : Finset ℕ} {σ : ℕ} {Q : Finset ℕ}

/-- `BumpSat` as a bounded statement: (B2) quantified over `Finset.range k`. -/
lemma bumpSat_iff :
    BumpSat k S σ Q ↔
      (∀ j ∈ S, 0 < j ∧ j < k) ∧ σ ∈ S ∧ Q ∩ insert 0 S = {σ} ∧
      ∀ i ∈ Finset.range k, 0 < i →
        (∃ j ∈ S, (i + j) % k ≠ 0 ∧ (i + j) % k ≠ σ ∧ inP k Q (i + j)) ∧
        (∃ j ∈ S, (i + j) % k ≠ 0 ∧ (i + j) % k ≠ σ ∧ ¬ inP k Q (i + j)) := by
  constructor
  · intro h
    refine ⟨h.S_sub, h.σ_mem, h.B1, fun i hi hi0 => h.B2 i hi0 (Finset.mem_range.mp hi)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, fun i hi0 hik => h4 i (Finset.mem_range.mpr hik) hi0⟩

instance : Decidable (BumpSat k S σ Q) := decidable_of_iff _ bumpSat_iff.symm

end Decide

/-! ## Reads across the block boundary -/

section Reads

variable {k : ℕ} {Q : Finset ℕ}

/-- A wrapped read: for `k ≤ n < 2k`, `n ∈ P ⟺ n − k ∉ Q`. -/
lemma inP_wrap (hk : 0 < k) {n : ℕ} (h1 : k ≤ n) (h2 : n < 2 * k) :
    inP k Q n ↔ n - k ∉ Q := by
  have hn : n = 1 * k + (n - k) := by omega
  rw [hn, inP_qk_add_of_lt hk Q 1 (by omega)]
  simp

/-- After a wrapped read `inP_qk_add_of_lt … 1`, the goal has the shape `(1 % 2 = 0 ↔ P)`. -/
lemma wrap_iff {P : Prop} : ((1 : ℕ) % 2 = 0 ↔ P) ↔ ¬ P :=
  ⟨fun h hp => by have := h.mpr hp; omega, fun hp => ⟨fun h => by omega, fun h => (hp h).elim⟩⟩

end Reads

end Bump
end Trop
end PeriodicDifference


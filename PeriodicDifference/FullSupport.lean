/-
# `PeriodicDifference/FullSupport.lean` — the full support is never globally periodic (`K ≥ 4`)

At order `K ≥ 4` with every slot `1, …, K − 1` present (slot `0` present or not), take the
constant-minimum carrier of `Q = {1}`, i.e. the anti-periodic set
`P = {1, K} ∪ [K + 2, 2K − 1] (mod 2K)` (`Bump.E K {1}`, `lem:fs-carrier`): its minimum is
always `−1`, so the constant slot never attains and both `θ` are killed at once.  Along it runs
the explicit tangent ray `ray` (`lem:fs-ray`): writing `n = (8m + r)K + c` with `r < 8`, `c < K`,

  `d_n = f(r, c) + m·u(r, c)`,  `u(r, c) = (−1)^{r+1}` on the inner columns `2 ≤ c ≤ K − 2`,
  `0` on the columns `0`, `1`, `K − 1`,

with `f` by columns (`0`, `1`, inner, `K − 1`) given by the rows `A`, `B`, `I`, `L` below.  It
drifts by `−1` every `8` rows on the inner column `2`, so it is not periodic, and
`Bump.not_tropPeriodic_of_ray` (`thm:tangent`) shows that no power of the min-plus map is the
identity (`not_tropPeriodic`), hence (`thm:P`) rules out global periodicity of the equation for
every positive coefficient choice (`thm:fullsupport`, `not_globallyPeriodic`).
-/
import PeriodicDifference.SigmaBump

namespace PeriodicDifference
namespace Trop
namespace FS

open Bump

/-- Column `0` of the ray, by row mod `8`. -/
def A (r : ℕ) : ℤ := [-1, 1, 0, 0, 1, 0, 0, 1].getI r
/-- Column `1`. -/
def B (r : ℕ) : ℤ := [0, 1, 0, 0, 1, -1, 1, 0].getI r
/-- The inner columns `2 ≤ c ≤ K − 2`, at `m = 0`. -/
def I (r : ℕ) : ℤ := [0, 1, -1, 1, 0, 0, 0, 1].getI r
/-- Column `K − 1`. -/
def L (r : ℕ) : ℤ := [0, 1, -1, 1, 0, 0, 1, 0].getI r

/-- The ray at row `8m + r`, column `c`. -/
def rv (K m r c : ℕ) : ℤ :=
  if c = 0 then A r else if c = 1 then B r else if c + 1 = K then L r
  else I r + if r % 2 = 0 then -(m : ℤ) else m

/-- The tangent ray of `lem:fs-ray`. -/
def ray (K n : ℕ) : ℤ := rv K (n / K / 8) (n / K % 8) (n % K)

variable {K : ℕ}

/-- The reading of a position `(8m + r)K + c` with `c < K`: the ray and the carrier. -/
lemma read (hK : 0 < K) {m r c : ℕ} (hr : r < 8) (hc : c < K) :
    ray K ((8 * m + r) * K + c) = rv K m r c ∧
      (inP K {1} ((8 * m + r) * K + c) ↔ (r % 2 = 0 ↔ c = 1)) := by
  have hq := div_qk_add_of_lt hK hc (8 * m + r)
  refine ⟨?_, ?_⟩
  · unfold ray
    rw [hq, mod_qk_add_of_lt hc]
    congr 1 <;> omega
  · rw [inP_qk_add_of_lt hK _ _ hc, Finset.mem_singleton,
      show (8 * m + r) % 2 = r % 2 by omega]

/-- Positions `j ≤ K` past `(8m + r)K + i` sit in the same row or the next one. -/
lemma shift {m r i j : ℕ} (hr : r < 8) (hi : i < K) (hj : j ≤ K) :
    ∃ m' r' c, r' < 8 ∧ c < K ∧ (8 * m + r) * K + i + j = (8 * m' + r') * K + c ∧
      ((i + j < K ∧ m' = m ∧ r' = r ∧ c = i + j) ∨
        (K ≤ i + j ∧ c = i + j - K ∧
          ((r < 7 ∧ m' = m ∧ r' = r + 1) ∨ (r = 7 ∧ m' = m + 1 ∧ r' = 0)))) := by
  rcases Nat.lt_or_ge (i + j) K with h | h
  · exact ⟨m, r, i + j, hr, h, by ring, Or.inl ⟨h, rfl, rfl, rfl⟩⟩
  · rcases Nat.lt_or_ge r 7 with h7 | h7
    · refine ⟨m, r + 1, i + j - K, by omega, by omega, ?_, Or.inr ⟨h, rfl, Or.inl ⟨h7, rfl, rfl⟩⟩⟩
      zify [h]; ring
    · refine ⟨m + 1, 0, i + j - K, by omega, by omega, ?_,
        Or.inr ⟨h, rfl, Or.inr ⟨by omega, rfl, rfl⟩⟩⟩
      have : r = 7 := by omega
      subst this; zify [h]; ring

/-- The designated tap at row `r`, column `i`. -/
def tap (K r i : ℕ) : ℕ :=
  if r % 2 = 0 then (if i = 0 then 1 else K - i)
  else if i + 1 = K then 2 else if r = 1 ∧ 2 ≤ i then K + 1 - i else K - 1 - i

/-- The designated tap, case by case. -/
lemma tap_cases {r i : ℕ} :
    (r % 2 = 0 ∧ i = 0 ∧ tap K r i = 1) ∨ (r % 2 = 0 ∧ i ≠ 0 ∧ tap K r i = K - i) ∨
      (r % 2 = 1 ∧ i + 1 = K ∧ tap K r i = 2) ∨
      (r = 1 ∧ i + 1 ≠ K ∧ 2 ≤ i ∧ tap K r i = K + 1 - i) ∨
      (r % 2 = 1 ∧ i + 1 ≠ K ∧ ¬ (r = 1 ∧ 2 ≤ i) ∧ tap K r i = K - 1 - i) := by
  unfold tap; split_ifs <;> omega

/-- Evaluate the rows and split the columns, pruning each branch by `omega`. -/
macro "rv_tac" : tactic => `(tactic| first
  | omega
  | (simp only [rv, A, B, I, L, List.getI_cons_succ, List.getI_cons_zero, Nat.reduceMod,
        Nat.reduceAdd, Nat.reduceEqDiff, eq_self_iff_true, ↓reduceIte, true_iff, iff_true,
        false_iff, iff_false, true_and, and_true, false_and, and_false, or_false, false_or] at *
     repeat' (first | omega | split)))

section Step

variable (hK : 4 ≤ K) {m r i : ℕ} (hr : r < 8) (hi : i < K)
include hK hi

lemma tap_le : 1 ≤ tap K r i ∧ tap K r i ≤ K - 1 := by unfold tap; split_ifs <;> omega

include hr

/-- The designated tap lies on the carrier. -/
lemma tap_inP : inP K {1} ((8 * m + r) * K + i + tap K r i) := by
  have hw := tap_le (r := r) hK hi
  obtain ⟨m₁, r₁, c₁, hr₁, hc₁, e₁, h₁⟩ := shift (m := m) hr hi (show tap K r i ≤ K by omega)
  rw [e₁, (read (by omega) hr₁ hc₁).2]
  have ht := tap_cases (K := K) (r := r) (i := i)
  clear e₁
  generalize tap K r i = t at *
  interval_cases r <;>
    rcases h₁ with ⟨_, rfl, rfl, rfl⟩ | ⟨_, rfl, ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩⟩ <;> rv_tac

/-- The designated tap minimises the ray among the taps on the carrier. -/
lemma tap_min {j : ℕ} (hj : 1 ≤ j ∧ j ≤ K - 1) (hjP : inP K {1} ((8 * m + r) * K + i + j)) :
    ray K ((8 * m + r) * K + i + tap K r i) ≤ ray K ((8 * m + r) * K + i + j) := by
  have hw := tap_le (r := r) hK hi
  obtain ⟨m₁, r₁, c₁, hr₁, hc₁, e₁, h₁⟩ := shift (m := m) hr hi (show tap K r i ≤ K by omega)
  obtain ⟨m₂, r₂, c₂, hr₂, hc₂, e₂, h₂⟩ := shift (m := m) hr hi (show j ≤ K by omega)
  rw [e₂, (read (by omega) hr₂ hc₂).2] at hjP
  rw [e₁, e₂, (read (by omega) hr₁ hc₁).1, (read (by omega) hr₂ hc₂).1]
  have ht := tap_cases (K := K) (r := r) (i := i)
  clear e₁ e₂
  generalize tap K r i = t at *
  interval_cases r <;>
    rcases h₁ with ⟨_, rfl, rfl, rfl⟩ | ⟨_, rfl, ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩⟩ <;>
    rcases h₂ with ⟨_, rfl, rfl, rfl⟩ | ⟨_, rfl, ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩⟩ <;> rv_tac

set_option maxHeartbeats 1000000 in
/-- The tangent recursion along the designated tap. -/
lemma tap_rec : ray K ((8 * m + r) * K + i + K) + ray K ((8 * m + r) * K + i)
    = ray K ((8 * m + r) * K + i + tap K r i) := by
  have hw := tap_le (r := r) hK hi
  obtain ⟨m₁, r₁, c₁, hr₁, hc₁, e₁, h₁⟩ := shift (m := m) hr hi (show tap K r i ≤ K by omega)
  obtain ⟨m₂, r₂, c₂, hr₂, hc₂, e₂, h₂⟩ := shift (m := m) hr hi le_rfl
  rw [e₁, e₂, (read (by omega) hr₁ hc₁).1, (read (by omega) hr₂ hc₂).1,
    (read (by omega) hr hi).1]
  have ht := tap_cases (K := K) (r := r) (i := i)
  clear e₁ e₂
  generalize tap K r i = t at *
  interval_cases r <;>
    rcases h₁ with ⟨_, rfl, rfl, rfl⟩ | ⟨_, rfl, ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩⟩ <;>
    rcases h₂ with ⟨_, rfl, rfl, rfl⟩ | ⟨_, rfl, ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩⟩ <;> rv_tac

end Step

/-- **`lem:fs-ray`**: the ray is a tangent orbit along the carrier. -/
theorem step (hK : 4 ≤ K) (n : ℕ) : ∃ w ∈ Finset.Icc 1 (K - 1), inP K {1} (n + w) ∧
    (∀ j ∈ Finset.Icc 1 (K - 1), inP K {1} (n + j) → ray K (n + w) ≤ ray K (n + j)) ∧
    ray K (n + K) + ray K n = ray K (n + w) := by
  obtain ⟨m, r, i, hr, hi, rfl⟩ : ∃ m r i, r < 8 ∧ i < K ∧ n = (8 * m + r) * K + i :=
    ⟨n / K / 8, n / K % 8, n % K, Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega), by
      conv_lhs => rw [← Nat.div_add_mod n K, ← Nat.div_add_mod (n / K) 8]
      ring⟩
  exact ⟨tap K r i, Finset.mem_Icc.mpr (tap_le hK hi), tap_inP hK hr hi,
    fun j hj hjP => tap_min hK hr hi (Finset.mem_Icc.mp hj) hjP, tap_rec hK hr hi⟩

/-- The ray drifts by `−1` every `8` rows on the inner column `2`. -/
lemma ray_drift (hK : 4 ≤ K) (p : ℕ) : ray K ((8 * p + 2) * K + 2) = -1 - p := by
  rw [(read (by omega) (by norm_num) (by omega)).1]
  simp only [rv, A, B, I, L, List.getI_cons_succ, List.getI_cons_zero]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  norm_num; ring

/-- **The min-plus map of the full support is not periodic** (`lem:fs-carrier`,
`lem:fs-ray`): at order `k' + 1 ≥ 4`, with every slot `1, …, k'` present (slot `0` optional),
no power `T^p`, `p ≥ 1`, is the identity. -/
theorem not_tropPeriodic {k' : ℕ} {J : List ℕ} (hk : 3 ≤ k')
    (hJk : ∀ j ∈ J, j ≤ k') (hJin : ∀ j, 1 ≤ j → j ≤ k' → j ∈ J)
    {p : ℕ} (hp : 0 < p) : ¬ TropPeriodic (k' + 1) J p := by
  refine not_tropPeriodic_of_ray (by omega)
    (fun j hj => by rw [Finset.mem_Icc] at hj; omega) (step (K := k' + 1) (by omega))
    ⟨8 * (k' + 1), (8 * 0 + 2) * (k' + 1) + 2, ?_⟩ (fun j hj => ?_)
    (fun j hj => hJin j (Finset.mem_Icc.mp hj).1 (by have := (Finset.mem_Icc.mp hj).2; omega))
  · rw [show (8 * 0 + 2) * (k' + 1) + 2 + 8 * (k' + 1) * p = (8 * p + 2) * (k' + 1) + 2 by ring,
      ray_drift (by omega), ray_drift (by omega)]
    omega
  · rw [Finset.mem_Icc]; have := hJk j hj; omega

/-- **The full support is not globally periodic** (`thm:fullsupport`) at order `k' + 1 ≥ 4`:
every slot `1, …, k'` present (slot `0` optional), positive coefficients, any period `p ≥ 1`. -/
theorem not_globallyPeriodic {k' : ℕ} {J : List ℕ} {co : ℕ → ℝ} (hk : 3 ≤ k')
    (hJk : ∀ j ∈ J, j ≤ k') (hJin : ∀ j, 1 ≤ j → j ≤ k' → j ∈ J) (hco : ∀ j ∈ J, 0 < co j)
    {p : ℕ} (hp : 0 < p) : ¬ GloballyPeriodic (k' + 1) J co p := fun hg =>
  not_tropPeriodic hk hJk hJin hp
    (hg.tropPeriodic (List.ne_nil_of_mem (hJin 1 le_rfl (by omega)))
      (fun j hj => Nat.lt_succ_of_le (hJk j hj)) hco)

end FS
end Trop
end PeriodicDifference

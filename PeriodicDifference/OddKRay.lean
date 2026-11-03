/-
# `PeriodicDifference/OddKRay.lean` — indicator rays of the second tangent (`lem:odd-ray`)

Coordinates of `eq:odd-coords`: at odd `k = 2c+1` a palindromic support is
`S = {2x, k − 2x : x ∈ X}` with `X ⊆ [1, c]`.  In the reduced recursion `VRec` the read sets
at time `t` are `R₊(t)`, the positions `t + x` in the translate `t + X`, and `R₋(t)`, the
positions `t + k − x` in the reflection `t − X` (`x ∈ X`), a read being deleted when its
position is `≡ 0 (mod k)` (`eq:odd-reads`).

A ray is a state `v t = f (t mod k) + ⌊t/k⌋·δ (t mod k)` with `f = 𝟙_A − e₀`, and `δ` with
`δ 0 = −1`, `δ ≥ 0` elsewhere and supported on `A ∪ {0}`.  Position `0` is never read
(the remark after `eq:odd-reads`), so each minimum is the blocking indicator `[reads ⊆ A]`
(provided the vanishing condition holds: every blocked read set contains a site where `δ`
vanishes), and the recursion becomes the residue condition
`δ r = [r reflection-blocked] − [r translate-blocked]` (`ray_kill_trop`, `ray_kill`; `δ` is the
paper's `Δ`, and `A` its `U`).  Since `v (k·p) = −1 − p`, the ray is not periodic and
`not_tropPeriodic_of_vrec` applies.
-/
import PeriodicDifference.OddKCarrier

namespace PeriodicDifference
namespace Trop
namespace OddK

open Bump

/-- `q ≡ 0 (mod k)` iff `2q + 1 ≡ 1 (mod 2k)`. -/
lemma mod_zero_iff {k : ℕ} (hk : 0 < k) (q : ℕ) : q % k = 0 ↔ (2 * q + 1) % (2 * k) = 1 := by
  have h1 := Nat.div_add_mod q k
  have h2 := Nat.mod_lt q hk
  have h3 : 2 * q + 1 = 2 * k * (q / k) + (2 * (q % k) + 1) := by
    calc 2 * q + 1 = 2 * (k * (q / k) + q % k) + 1 := by rw [h1]
      _ = _ := by ring
  rw [h3, Nat.mul_add_mod, Nat.mod_eq_of_lt (show 2 * (q % k) + 1 < 2 * k by omega)]
  omega

/-- The coordinates: `S = {2x, k − 2x : x ∈ X}`, `X ⊆ [1, c]`. -/
structure Coords (k : ℕ) (S X : Finset ℕ) : Prop where
  odd : k % 2 = 1
  X_bd : ∀ x ∈ X, 1 ≤ x ∧ 2 * x < k
  mem : ∀ j, j ∈ S ↔ ∃ x ∈ X, j = 2 * x ∨ j = k - 2 * x
  two : ∃ a ∈ X, ∃ b ∈ X, a ≠ b

/-- The ray. -/
def ray (k : ℕ) (A : Finset ℕ) (δ : ℕ → ℤ) (t : ℕ) : ℤ :=
  (if t % k = 0 then -1 else if t % k ∈ A then 1 else 0) + ((t / k : ℕ) : ℤ) * δ (t % k)

/-- The residue `r` is reflection-blocked: every undeleted read of `R₋` lies in `A`. -/
def Fb (k : ℕ) (X A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ x ∈ X, (r + k - x) % k ≠ 0 → (r + k - x) % k ∈ A

/-- The residue `r` is translate-blocked: every undeleted read of `R₊` lies in `A`. -/
def Bb (k : ℕ) (X A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ x ∈ X, (r + x) % k ≠ 0 → (r + x) % k ∈ A

instance (k : ℕ) (X A : Finset ℕ) (r : ℕ) : Decidable (Fb k X A r) := by
  unfold Fb; infer_instance
instance (k : ℕ) (X A : Finset ℕ) (r : ℕ) : Decidable (Bb k X A r) := by
  unfold Bb; infer_instance

/-! ## The minima are blocking indicators -/

lemma inf_ind {T : Finset ℕ} (hne : T.Nonempty) (g : ℕ → ℤ) (P : Prop) [Decidable P]
    (h0 : ∀ j ∈ T, 0 ≤ g j) (h1 : P → ∀ j ∈ T, 1 ≤ g j) (h1' : P → ∃ j ∈ T, g j = 1)
    (h0' : ¬ P → ∃ j ∈ T, g j = 0) : T.inf' hne g = if P then 1 else 0 := by
  split_ifs with hP
  · obtain ⟨j, hj, hg⟩ := h1' hP
    exact le_antisymm (hg ▸ Finset.inf'_le _ hj) (Finset.le_inf' _ _ (h1 hP))
  · obtain ⟨j, hj, hg⟩ := h0' hP
    exact le_antisymm (hg ▸ Finset.inf'_le _ hj) (Finset.le_inf' _ _ h0)

lemma fwd_res {k : ℕ} {x : ℕ} (hx : x ≤ k) (t : ℕ) : (t + k - x) % k = (t % k + k - x) % k := by
  have h := Nat.div_add_mod t k
  have e : t + k - x = (t % k + k - x) + k * (t / k) := by omega
  rw [e, Nat.add_mul_mod_self_left]

lemma bwd_res {k : ℕ} (x t : ℕ) : (t + x) % k = (t % k + x) % k := by
  have h := Nat.div_add_mod t k
  have e : t + x = (t % k + x) + k * (t / k) := by omega
  rw [e, Nat.add_mul_mod_self_left]

/-- The hypotheses on `(A, δ)`. -/
structure RayData (k : ℕ) (A : Finset ℕ) (δ : ℕ → ℤ) : Prop where
  δ0 : δ 0 = -1
  δpos : ∀ r, r ≠ 0 → 0 ≤ δ r
  δA : ∀ r, r ≠ 0 → δ r ≠ 0 → r ∈ A

section Values

variable {k : ℕ} {A : Finset ℕ} {δ : ℕ → ℤ} (D : RayData k A δ)
include D

lemma ray_nonneg {q : ℕ} (hq : q % k ≠ 0) : 0 ≤ ray k A δ q := by
  unfold ray; rw [if_neg hq]
  have := D.δpos _ hq
  have : (0 : ℤ) ≤ ((q / k : ℕ) : ℤ) := by positivity
  split_ifs <;> nlinarith

lemma ray_ge_one {q : ℕ} (hq : q % k ≠ 0) (hA : q % k ∈ A) : 1 ≤ ray k A δ q := by
  unfold ray; rw [if_neg hq, if_pos hA]
  have := D.δpos _ hq
  have : (0 : ℤ) ≤ ((q / k : ℕ) : ℤ) := by positivity
  nlinarith

lemma ray_eq_zero {q : ℕ} (hq : q % k ≠ 0) (hA : q % k ∉ A) : ray k A δ q = 0 := by
  have hδ : δ (q % k) = 0 := by
    by_contra h; exact hA (D.δA _ hq h)
  unfold ray; rw [if_neg hq, if_neg hA, hδ]; ring

omit D in
lemma ray_eq_one {q : ℕ} (hq : q % k ≠ 0) (hA : q % k ∈ A) (hδ : δ (q % k) = 0) :
    ray k A δ q = 1 := by
  unfold ray; rw [if_neg hq, if_pos hA, hδ]; ring

end Values

section Ray

variable {k : ℕ} {S X A : Finset ℕ} {δ : ℕ → ℤ}

lemma Coords.k_pos (H : Coords k S X) : 0 < k := by have := H.odd; omega

lemma Coords.S_sub (H : Coords k S X) : ∀ j ∈ S, 0 < j ∧ j < k := by
  intro j hj
  obtain ⟨x, hx, h⟩ := (H.mem j).mp hj
  have := H.X_bd x hx
  omega

lemma Coords.pal (H : Coords k S X) : ∀ j ∈ S, k - j ∈ S := by
  intro j hj
  obtain ⟨x, hx, h⟩ := (H.mem j).mp hj
  have := H.X_bd x hx
  refine (H.mem _).mpr ⟨x, hx, ?_⟩
  omega

lemma Coords.hodd (H : Coords k S X) : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a % 2 = 1 ∧ b % 2 = 1 := by
  obtain ⟨a, ha, b, hb, hab⟩ := H.two
  have h1 := H.X_bd a ha
  have h2 := H.X_bd b hb
  have hk := H.odd
  exact ⟨k - 2 * a, (H.mem _).mpr ⟨a, ha, Or.inr rfl⟩, k - 2 * b, (H.mem _).mpr ⟨b, hb, Or.inr rfl⟩,
    by omega, by omega, by omega⟩

/-- Attaining taps at the even time `2t+1+k` (the reads `R₋`): `j = k − 2x`, read `t + k − x`. -/
lemma att_fwd (H : Coords k S X) (t j : ℕ) :
    j ∈ Att k S (2 * t + 1 + k) ↔ ∃ x ∈ X, j = k - 2 * x ∧ (t + k - x) % k ≠ 0 := by
  have hk := H.odd
  have hk0 := H.k_pos
  unfold Att
  rw [Finset.mem_filter, H.mem]
  constructor
  · rintro ⟨⟨x, hx, hj⟩, h1, h2⟩
    have hb := H.X_bd x hx
    rcases hj with rfl | rfl
    · omega
    · refine ⟨x, hx, rfl, ?_⟩
      rw [Ne, mod_zero_iff hk0]
      have : 2 * (t + k - x) + 1 = 2 * t + 1 + k + (k - 2 * x) := by omega
      rw [this]; exact h2
  · rintro ⟨x, hx, rfl, h⟩
    have hb := H.X_bd x hx
    refine ⟨⟨x, hx, Or.inr rfl⟩, by omega, ?_⟩
    rw [Ne, mod_zero_iff hk0] at h
    have : 2 * (t + k - x) + 1 = 2 * t + 1 + k + (k - 2 * x) := by omega
    rw [this] at h; exact h

/-- Attaining taps at the odd time `2t+1` (the reads `R₊`): `j = 2x`, read `t + x`. -/
lemma att_bwd (H : Coords k S X) (t j : ℕ) :
    j ∈ Att k S (2 * t + 1) ↔ ∃ x ∈ X, j = 2 * x ∧ (t + x) % k ≠ 0 := by
  have hk := H.odd
  have hk0 := H.k_pos
  unfold Att
  rw [Finset.mem_filter, H.mem]
  constructor
  · rintro ⟨⟨x, hx, hj⟩, h1, h2⟩
    have hb := H.X_bd x hx
    rcases hj with rfl | rfl
    · refine ⟨x, hx, rfl, ?_⟩
      rw [Ne, mod_zero_iff hk0]
      have : 2 * (t + x) + 1 = 2 * t + 1 + 2 * x := by ring
      rw [this]; exact h2
    · omega
  · rintro ⟨x, hx, rfl, h⟩
    refine ⟨⟨x, hx, Or.inl rfl⟩, by omega, ?_⟩
    rw [Ne, mod_zero_iff hk0] at h
    have : 2 * (t + x) + 1 = 2 * t + 1 + 2 * x := by ring
    rw [this] at h; exact h

lemma rd_fwd (H : Coords k S X) (D : RayData k A δ) (t : ℕ)
    (hG : Fb k X A (t % k) → ∃ x ∈ X, (t % k + k - x) % k ≠ 0 ∧ δ ((t % k + k - x) % k) = 0) :
    rd k S (ray k A δ) (2 * t + 1 + k) = if Fb k X A (t % k) then 1 else 0 := by
  have hk := H.odd
  unfold rd
  rw [dif_pos (att_nonempty hk H.S_sub H.pal H.hodd _)]
  have hread : ∀ x ∈ X, (2 * t + 1 + k + (k - 2 * x)) / 2 = t + k - x := by
    intro x hx; have := H.X_bd x hx; omega
  apply inf_ind
  · intro j hj
    obtain ⟨x, hx, rfl, hr⟩ := (att_fwd H t j).mp hj
    rw [hread x hx]; exact ray_nonneg D hr
  · intro hF j hj
    obtain ⟨x, hx, rfl, hr⟩ := (att_fwd H t j).mp hj
    have hxk : x ≤ k := by have := H.X_bd x hx; omega
    rw [hread x hx]
    refine ray_ge_one D hr ?_
    rw [fwd_res hxk] at hr ⊢
    exact hF x hx hr
  · intro hF
    obtain ⟨x, hx, hr, hδ⟩ := hG hF
    have hxk : x ≤ k := by have := H.X_bd x hx; omega
    have hr' : (t + k - x) % k ≠ 0 := by rw [fwd_res hxk]; exact hr
    refine ⟨k - 2 * x, (att_fwd H t _).mpr ⟨x, hx, rfl, hr'⟩, ?_⟩
    rw [hread x hx]
    refine ray_eq_one hr' ?_ ?_ <;> rw [fwd_res hxk]
    · exact hF x hx hr
    · exact hδ
  · intro hF
    simp only [Fb, not_forall] at hF
    obtain ⟨x, hx, hr, hA⟩ := hF
    have hxk : x ≤ k := by have := H.X_bd x hx; omega
    have hr' : (t + k - x) % k ≠ 0 := by rw [fwd_res hxk]; exact hr
    refine ⟨k - 2 * x, (att_fwd H t _).mpr ⟨x, hx, rfl, hr'⟩, ?_⟩
    rw [hread x hx]
    refine ray_eq_zero D hr' ?_
    rw [fwd_res hxk]; exact hA

lemma rd_bwd (H : Coords k S X) (D : RayData k A δ) (t : ℕ)
    (hG : Bb k X A (t % k) → ∃ x ∈ X, (t % k + x) % k ≠ 0 ∧ δ ((t % k + x) % k) = 0) :
    rd k S (ray k A δ) (2 * t + 1) = if Bb k X A (t % k) then 1 else 0 := by
  have hk := H.odd
  unfold rd
  rw [dif_pos (att_nonempty hk H.S_sub H.pal H.hodd _)]
  have hread : ∀ x, (2 * t + 1 + 2 * x) / 2 = t + x := by intro x; omega
  apply inf_ind
  · intro j hj
    obtain ⟨x, hx, rfl, hr⟩ := (att_bwd H t j).mp hj
    rw [hread x]; exact ray_nonneg D hr
  · intro hF j hj
    obtain ⟨x, hx, rfl, hr⟩ := (att_bwd H t j).mp hj
    rw [hread x]
    refine ray_ge_one D hr ?_
    rw [bwd_res] at hr ⊢
    exact hF x hx hr
  · intro hF
    obtain ⟨x, hx, hr, hδ⟩ := hG hF
    have hr' : (t + x) % k ≠ 0 := by rw [bwd_res]; exact hr
    refine ⟨2 * x, (att_bwd H t _).mpr ⟨x, hx, rfl, hr'⟩, ?_⟩
    rw [hread x]
    refine ray_eq_one hr' ?_ ?_ <;> rw [bwd_res]
    · exact hF x hx hr
    · exact hδ
  · intro hF
    simp only [Bb, not_forall] at hF
    obtain ⟨x, hx, hr, hA⟩ := hF
    have hr' : (t + x) % k ≠ 0 := by rw [bwd_res]; exact hr
    refine ⟨2 * x, (att_bwd H t _).mpr ⟨x, hx, rfl, hr'⟩, ?_⟩
    rw [hread x]
    refine ray_eq_zero D hr' ?_
    rw [bwd_res]; exact hA

/-- **The indicator ray kills the support, for the min-plus map** (`lem:odd-ray`); `hGF`,
`hGB` are the vanishing condition. -/
theorem ray_kill_trop (H : Coords k S X) (D : RayData k A δ)
    (hcond : ∀ r < k, δ r = (if Fb k X A r then 1 else 0) - (if Bb k X A r then 1 else 0))
    (hGF : ∀ r < k, Fb k X A r → ∃ x ∈ X, (r + k - x) % k ≠ 0 ∧ δ ((r + k - x) % k) = 0)
    (hGB : ∀ r < k, Bb k X A r → ∃ x ∈ X, (r + x) % k ≠ 0 ∧ δ ((r + x) % k) = 0)
    {J : List ℕ} (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S) (hSJ : ∀ j ∈ S, j ∈ J)
    {p : ℕ} (hp : 0 < p) : ¬ TropPeriodic k J p := by
  have hk0 := H.k_pos
  refine not_tropPeriodic_of_vrec H.odd H.S_sub H.pal H.hodd hJS hSJ
    (v := ray k A δ) ?_ ⟨k, 0, ?_⟩
  · intro t
    have hr := Nat.mod_lt t hk0
    rw [rd_fwd H D t (hGF _ hr), rd_bwd H D t (hGB _ hr), add_sub_assoc, ← hcond _ hr]
    have e1 : (t + k) % k = t % k := Nat.add_mod_right t k
    have e2 : (t + k) / k = t / k + 1 := Nat.add_div_right t hk0
    unfold ray
    rw [e1, e2]
    push_cast; ring
  · unfold ray
    rw [zero_add, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hk0]
    simp [D.δ0]
    omega

/-- **The indicator ray kills the support** (`lem:odd-ray`); `hGF`, `hGB` are the vanishing
condition. -/
theorem ray_kill (H : Coords k S X) (D : RayData k A δ)
    (hcond : ∀ r < k, δ r = (if Fb k X A r then 1 else 0) - (if Bb k X A r then 1 else 0))
    (hGF : ∀ r < k, Fb k X A r → ∃ x ∈ X, (r + k - x) % k ≠ 0 ∧ δ ((r + k - x) % k) = 0)
    (hGB : ∀ r < k, Bb k X A r → ∃ x ∈ X, (r + x) % k ≠ 0 ∧ δ ((r + x) % k) = 0)
    {J : List ℕ} (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S) (hSJ : ∀ j ∈ S, j ∈ J)
    {co : ℕ → ℝ} (hco : ∀ j ∈ J, 0 < co j) {p : ℕ} (hp : 0 < p) :
    ¬ GloballyPeriodic k J co p := by
  obtain ⟨a, ha, -⟩ := H.hodd
  exact fun hg => ray_kill_trop H D hcond hGF hGB hJS hSJ hp
    (hg.tropPeriodic_of_supp H.S_sub ⟨a, ha⟩ hJS hSJ hco)

end Ray

end OddK
end Trop
end PeriodicDifference

/-
# `PeriodicDifference/OddKAprime.lean` — the non-progressions are killed (`thm:odd-nondil`)

At odd `k`, in the coordinates `S = {2x, k − 2x : x ∈ X}`, if `X` is not a dilated interval
(equivalently `Σ = I ∪ {c}` is not a progression ending at `c`) then one of three indicator
rays of `PeriodicDifference/OddKRay.lean` exists:

* (a) `X` symmetric about `j` (`SymX`): `A = X ∪ {j}`, `δ = −e₀ + e_j` (case (a) of the
  proof of `thm:odd-nondil`);
* (b) otherwise `W = X ∪ {0}` symmetric about `q` (`SymW`): `A = X`, `δ = −e₀ + e_q`;
* (c) otherwise: the mirror state, `A = X`, `δ = −e₀`.

The blocking conditions are the rigidity lemmas of `PeriodicDifference/OddKRigid.lean`.
-/
import PeriodicDifference.OddKRay
import PeriodicDifference.OddKRigid

namespace PeriodicDifference
namespace Trop
namespace OddK

section Aprime

variable {k : ℕ} {S X : Finset ℕ} (H : Coords k S X) (hnd : ¬ Dil X)
include H hnd

omit hnd in
lemma Coords.bd : Bd k X := H.X_bd

omit hnd in
lemma Coords.ne : X.Nonempty := by obtain ⟨a, ha, -⟩ := H.two; exact ⟨a, ha⟩

omit hnd in
lemma Coords.lt {x : ℕ} (hx : x ∈ X) : x < k := by have := H.X_bd x hx; omega

/-- No residue other than `0` is translate-blocked against `X ∪ {j}` (or `X`). -/
lemma not_bb {j : ℕ} (hsym : j = 0 ∨ SymX k X j) {r : ℕ} (hr0 : r ≠ 0) (hrk : r < k)
    (hB : Bb k X (insert j X) r) : False := by
  apply hnd
  rcases hsym with rfl | hsym
  · refine trigid H.odd H.bd H.ne (Nat.pos_of_ne_zero hr0) hrk ?_
    intro x hx
    by_cases h0 : (x + r) % k = 0
    · exact Or.inr h0
    · have := hB x hx (by rwa [add_comm])
      rw [add_comm] at this
      rcases Finset.mem_insert.mp this with h | h
      · exact Or.inr h
      · exact Or.inl h
  · refine symfail H.odd H.bd H.ne hsym (Nat.pos_of_ne_zero hr0) hrk ?_
    intro x hx
    by_cases h0 : (x + r) % k = 0
    · exact Or.inr (Or.inl h0)
    · have := hB x hx (by rwa [add_comm])
      rw [add_comm] at this
      rcases Finset.mem_insert.mp this with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h

omit hnd in
/-- The residue `0` is translate-blocked. -/
lemma bb_zero {A : Finset ℕ} (hXA : X ⊆ A) : Bb k X A 0 := by
  intro x hx _
  rw [zero_add, Nat.mod_eq_of_lt (H.lt hx)]
  exact hXA hx

omit hnd in
/-- A residue reflection-blocked against `X` is a symmetry of `X` or of `W` (`lem:odd-frigid`). -/
lemma fb_rigid {r : ℕ} (hrk : r < k) (hF : Fb k X X r) : SymX k X r ∨ SymW k X r := by
  by_cases h : ∀ x ∈ X, (r + k - x) % k ≠ 0
  · left; intro x hx; exact hF x hx (h x hx)
  · right
    push_neg at h
    obtain ⟨x₀, hx₀, h0⟩ := h
    have hx₀r : x₀ = r := by
      have hx₀k := H.lt hx₀
      rcases sub_cases hrk hx₀k.le with ⟨e, h'⟩ | ⟨e, h'⟩ <;> rw [e] at h0 <;> omega
    subst hx₀r
    refine ⟨hx₀, fun x hx hne => hF x hx ?_⟩
    have hxk := H.lt hx
    have hx₀k := H.lt hx₀
    rcases sub_cases hx₀k hxk.le with ⟨e, h'⟩ | ⟨e, h'⟩ <;> rw [e] <;> omega

omit hnd in
/-- The reads at `0` are `k − x`, outside `X`. -/
lemma read_zero {x : ℕ} (hx : x ∈ X) : (0 + k - x) % k = k - x ∧ k - x ∉ X ∧ k - x ≠ 0 := by
  have hb := H.X_bd x hx
  refine ⟨by rw [Nat.mod_eq_of_lt (show 0 + k - x < k by omega)]; omega, fun h => ?_, by omega⟩
  have := H.X_bd _ h
  omega

omit H hnd in
lemma bb_mono {A A' : Finset ℕ} (h : A ⊆ A') {r : ℕ} (hB : Bb k X A r) : Bb k X A' r :=
  fun x hx h0 => h (hB x hx h0)

omit hnd in
lemma exists_ne (j : ℕ) : ∃ x ∈ X, x ≠ j := by
  obtain ⟨a, ha, b, hb, hab⟩ := H.two
  by_cases h : a = j
  · exact ⟨b, hb, fun hbj => hab (h.trans hbj.symm)⟩
  · exact ⟨a, ha, h⟩

variable {J : List ℕ} (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S) (hSJ : ∀ j ∈ S, j ∈ J)
  {p : ℕ} (hp : 0 < p)
include hJS hSJ hp

/-- Case (a): `X` symmetric about `j` (case (a) of the proof of `thm:odd-nondil`). -/
theorem kill_symX_trop {j : ℕ} (hjk : j < k) (hsym : SymX k X j) : ¬ TropPeriodic k J p := by
  have hk := H.odd
  have hk0 : 0 < k := by omega
  have hj0 : j ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha, -⟩ := H.two
    exact (read_zero H ha).2.1 ((read_zero H ha).1 ▸ hsym a ha)
  have hjX : j ∉ X := by
    intro hj
    have := hsym j hj
    rw [show j + k - j = k by omega, Nat.mod_self] at this
    have := H.X_bd 0 this; omega
  set A := insert j X with hA
  set δ : ℕ → ℤ := fun r => (if r = j then 1 else 0) - (if r = 0 then 1 else 0) with hδ
  have D : RayData k A δ :=
    ⟨by simp [hδ, hj0.symm], fun r hr => by simp [hδ, hr]; split_ifs <;> norm_num,
      fun r hr h => by
        simp only [hδ, if_neg hr, sub_zero] at h
        split_ifs at h with h'
        · rw [h']; exact Finset.mem_insert_self _ _
        · exact absurd rfl h⟩
  have hF : ∀ r < k, Fb k X A r ↔ r = j := by
    intro r hr
    constructor
    · intro hFb
      by_contra hrj
      by_cases hr0 : r = 0
      · subst hr0
        obtain ⟨a, ha, b, hb, hab⟩ := H.two
        have ra := read_zero H ha
        have rb := read_zero H hb
        have h1 := hFb a ha (by rw [ra.1]; exact ra.2.2)
        have h2 := hFb b hb (by rw [rb.1]; exact rb.2.2)
        rw [ra.1, Finset.mem_insert] at h1
        rw [rb.1, Finset.mem_insert] at h2
        have := H.lt ha; have := H.lt hb
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · omega
        · exact rb.2.1 h2
        · exact ra.2.1 h1
        · exact ra.2.1 h1
      · apply hnd
        set ζ := (r + k - j) % k with hζ
        have cζ : (ζ : ZMod k) = r - j := cast_sub_mod (by omega)
        have hζ0 : 0 < ζ := by
          rcases Nat.eq_zero_or_pos ζ with h | h
          · exfalso; apply hrj
            refine eq_of_cast hr hjk ?_
            have : ((ζ : ℕ) : ZMod k) = ((0 : ℕ) : ZMod k) := by rw [h]
            rw [cζ] at this; push_cast at this; linear_combination this
          · exact h
        refine symfail hk H.bd H.ne hsym hζ0 (Nat.mod_lt _ hk0) ?_
        intro y hy
        have hx := hsym y hy
        set x := (j + k - y) % k with hxdef
        have cx : (x : ZMod k) = j - y := cast_sub_mod (by have := H.lt hy; omega)
        have e : (y + ζ) % k = (r + k - x) % k := by
          refine eq_of_cast (Nat.mod_lt _ hk0) (Nat.mod_lt _ hk0) ?_
          rw [cast_add_mod, cζ, cast_sub_mod (by have := H.lt hx; omega), cx]; ring
        rw [e]
        by_cases h0 : (r + k - x) % k = 0
        · exact Or.inr (Or.inl h0)
        · rcases Finset.mem_insert.mp (hFb x hx h0) with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inl h
    · rintro rfl x hx _
      exact Finset.mem_insert_of_mem (hsym x hx)
  have hB : ∀ r < k, Bb k X A r ↔ r = 0 := by
    intro r hr
    constructor
    · intro hBb; by_contra hr0; exact not_bb H hnd (Or.inr hsym) hr0 hr hBb
    · rintro rfl; exact bb_zero H (Finset.subset_insert _ _)
  refine ray_kill_trop H D ?_ ?_ ?_ hJS hSJ hp
  · intro r hr
    simp only [hF r hr, hB r hr, hδ]
  · intro r hr hFb
    rw [(hF r hr)] at hFb; subst hFb
    obtain ⟨a, ha, -⟩ := H.two
    have hy := hsym a ha
    have hb := H.X_bd _ hy
    refine ⟨a, ha, by omega, ?_⟩
    have hne : (r + k - a) % k ≠ r := fun h => hjX (h ▸ hy)
    simp [hδ, hne]; omega
  · intro r hr hBb
    rw [(hB r hr)] at hBb; subst hBb
    obtain ⟨a, ha, -⟩ := H.two
    have hb := H.X_bd a ha
    refine ⟨a, ha, ?_, ?_⟩
    · rw [zero_add, Nat.mod_eq_of_lt (H.lt ha)]; omega
    · rw [zero_add, Nat.mod_eq_of_lt (H.lt ha)]
      have : a ≠ j := fun h => hjX (h ▸ ha)
      simp [hδ, this]; omega

omit hJS hSJ hp in
/-- Only the residue `0` is translate-blocked against `X`. -/
lemma bb_X_iff {r : ℕ} (hr : r < k) : Bb k X X r ↔ r = 0 := by
  constructor
  · intro hBb; by_contra hr0
    exact not_bb H hnd (Or.inl rfl) hr0 hr (bb_mono (Finset.subset_insert _ _) hBb)
  · rintro rfl; exact bb_zero H subset_rfl

/-- Case (b): `W` symmetric about `q`, `X` symmetric about nothing. -/
theorem kill_symW_trop (hna : ¬ ∃ j < k, SymX k X j) {q : ℕ} (hqk : q < k) (hq : SymW k X q) :
    ¬ TropPeriodic k J p := by
  have hk := H.odd
  have hk0 : 0 < k := by omega
  have hq0 : q ≠ 0 := by have := H.X_bd q hq.1; omega
  set δ : ℕ → ℤ := fun r => (if r = q then 1 else 0) - (if r = 0 then 1 else 0) with hδ
  have D : RayData k X δ :=
    ⟨by simp [hδ, hq0.symm], fun r hr => by simp [hδ, hr]; split_ifs <;> norm_num,
      fun r hr h => by
        simp only [hδ, if_neg hr, sub_zero] at h
        split_ifs at h with h'
        · rw [h']; exact hq.1
        · exact absurd rfl h⟩
  have hF : ∀ r < k, Fb k X X r ↔ r = q := by
    intro r hr
    constructor
    · intro hFb
      rcases fb_rigid H hr hFb with h | h
      · exact absurd ⟨r, hr, h⟩ hna
      · by_contra hrq
        exact hnd (symW_unique hk H.bd H.ne h hq hrq)
    · intro hrq x hx h0
      rw [hrq] at h0 ⊢
      refine hq.2 x hx ?_
      rintro rfl
      rw [show x + k - x = k by omega, Nat.mod_self] at h0
      exact h0 rfl
  refine ray_kill_trop H D ?_ ?_ ?_ hJS hSJ hp
  · intro r hr
    simp only [hF r hr, bb_X_iff H hnd hr, hδ]
  · intro r hr hFb
    rw [hF r hr] at hFb; subst hFb
    obtain ⟨x, hx, hxr⟩ := exists_ne H r
    have hy := hq.2 x hx hxr
    have hb := H.X_bd _ hy
    refine ⟨x, hx, by omega, ?_⟩
    have hne : (r + k - x) % k ≠ r := by
      intro h
      have c := cast_sub_mod (k := k) (a := r) (b := x) (by have := H.lt hx; omega)
      rw [h] at c
      have : x = 0 := eq_of_cast (H.lt hx) hk0 (by push_cast; linear_combination c)
      have := H.X_bd x hx; omega
    simp [hδ, hne]; omega
  · intro r hr hBb
    rw [bb_X_iff H hnd hr] at hBb; subst hBb
    obtain ⟨x, hx, hxq⟩ := exists_ne H q
    have hb := H.X_bd x hx
    refine ⟨x, hx, ?_, ?_⟩
    · rw [zero_add, Nat.mod_eq_of_lt (H.lt hx)]; omega
    · rw [zero_add, Nat.mod_eq_of_lt (H.lt hx)]
      simp [hδ, hxq]; omega

/-- Case (c): neither `X` nor `W` symmetric — the mirror state. -/
theorem kill_mirror_trop (hna : ¬ ∃ j < k, SymX k X j) (hnb : ¬ ∃ q < k, SymW k X q) :
    ¬ TropPeriodic k J p := by
  have hk := H.odd
  set δ : ℕ → ℤ := fun r => -(if r = 0 then 1 else 0) with hδ
  have D : RayData k X δ :=
    ⟨by simp [hδ], fun r hr => by simp [hδ, hr], fun r hr h => by simp [hδ, hr] at h⟩
  have hF : ∀ r < k, ¬ Fb k X X r := by
    intro r hr hFb
    rcases fb_rigid H hr hFb with h | h
    · exact hna ⟨r, hr, h⟩
    · exact hnb ⟨r, hr, h⟩
  refine ray_kill_trop H D ?_ ?_ ?_ hJS hSJ hp
  · intro r hr
    simp only [if_neg (hF r hr), bb_X_iff H hnd hr, hδ]; ring
  · intro r hr hFb; exact absurd hFb (hF r hr)
  · intro r hr hBb
    rw [bb_X_iff H hnd hr] at hBb; subst hBb
    obtain ⟨x, hx, -⟩ := H.two
    have hb := H.X_bd x hx
    refine ⟨x, hx, ?_, ?_⟩
    · rw [zero_add, Nat.mod_eq_of_lt (H.lt hx)]; omega
    · rw [zero_add, Nat.mod_eq_of_lt (H.lt hx)]
      have : x ≠ 0 := by omega
      simp [hδ, this]

/-- **`thm:odd-nondil`, for the min-plus map.**  If `X` is not a dilated interval, then for
every slot list with nonzero slots `S`, at both θ, no power `T^p`, `p ≥ 1`, of the min-plus map
is the identity. -/
theorem aprime_trop : ¬ TropPeriodic k J p := by
  by_cases ha : ∃ j < k, SymX k X j
  · obtain ⟨j, hjk, hj⟩ := ha
    exact kill_symX_trop H hnd hJS hSJ hp hjk hj
  · by_cases hb : ∃ q < k, SymW k X q
    · obtain ⟨q, hqk, hq⟩ := hb
      exact kill_symW_trop H hnd hJS hSJ hp ha hqk hq
    · exact kill_mirror_trop H hnd hJS hSJ hp ha hb

end Aprime

/-! ### The equation: `thm:P` -/

section AprimeEqn

variable {k : ℕ} {S X : Finset ℕ} (H : Coords k S X) (hnd : ¬ Dil X)
  {J : List ℕ} (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S) (hSJ : ∀ j ∈ S, j ∈ J)
  {co : ℕ → ℝ} (hco : ∀ j ∈ J, 0 < co j) {p : ℕ} (hp : 0 < p)
include H hJS hSJ hco

lemma Coords.tropPeriodic (hg : GloballyPeriodic k J co p) : TropPeriodic k J p := by
  obtain ⟨a, ha, -⟩ := H.hodd
  exact hg.tropPeriodic_of_supp H.S_sub ⟨a, ha⟩ hJS hSJ hco

include hnd hp

/-- Case (a) for the equation (`kill_symX_trop`). -/
theorem kill_symX {j : ℕ} (hjk : j < k) (hsym : SymX k X j) : ¬ GloballyPeriodic k J co p :=
  fun hg => kill_symX_trop H hnd hJS hSJ hp hjk hsym (H.tropPeriodic hJS hSJ hco hg)

/-- Case (b) for the equation (`kill_symW_trop`). -/
theorem kill_symW (hna : ¬ ∃ j < k, SymX k X j) {q : ℕ} (hqk : q < k) (hq : SymW k X q) :
    ¬ GloballyPeriodic k J co p :=
  fun hg => kill_symW_trop H hnd hJS hSJ hp hna hqk hq (H.tropPeriodic hJS hSJ hco hg)

/-- Case (c) for the equation (`kill_mirror_trop`). -/
theorem kill_mirror (hna : ¬ ∃ j < k, SymX k X j) (hnb : ¬ ∃ q < k, SymW k X q) :
    ¬ GloballyPeriodic k J co p :=
  fun hg => kill_mirror_trop H hnd hJS hSJ hp hna hnb (H.tropPeriodic hJS hSJ hco hg)

/-- **`thm:odd-nondil`.**  If `X` is not a dilated interval, no slot list with nonzero slots `S`
is globally periodic, at any positive coefficients and both θ. -/
theorem aprime : ¬ GloballyPeriodic k J co p :=
  fun hg => aprime_trop H hnd hJS hSJ hp (H.tropPeriodic hJS hSJ hco hg)

end AprimeEqn

end OddK
end Trop
end PeriodicDifference

/-
# `PeriodicDifference/E3AllLift.lean` — the lift count of `lem:allodd-nofail`

For `k > 90`, an all-blocked support whose lower half is not the chain `a, 3a, 5a, …` has a root `x`
whose progression failure is the lift of a primitive failure `(m; a', x') ∈ PF` with `m = k/g`,
`a = g·a'`.  The orders `m` so obtained for the given `a` (`admL k a`) all divide `k`; primitivity
forces `k` to be their lcm (`ell k a = k`).  Every such order carries a failure with the ratio
`a'/m = a/k`, so `ell k a` divides the lcm of the orders of `PF` sharing one ratio (`classLcm`).
The ratios shared by two orders are `3/12 = 7/28`, `3/24 = 5/40` and `1/16 = 3/48`, so every
`classLcm` is at most `90` except `lcm(24, 40) = 120`, met only with `a = 15` (`classCheck`).
-/
import PeriodicDifference.E3AllDefs

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace E3All

/-- The failing orders `m ∣ k` whose primitive failures lift to first entry `a` at order `k`. -/
def admL (k a : ℕ) : List ℕ :=
  (PF.filter (fun t => k % t.1 == 0 && a == k / t.1 * t.2.1)).map (·.1)

/-- Their least common multiple. -/
def ell (k a : ℕ) : ℕ := (admL k a).foldr Nat.lcm 1

/-- The orders of `PF` carrying a failure with the same ratio `a'/m` as `t`. -/
def classOrders (t : ℕ × ℕ × ℕ) : List ℕ :=
  (PF.filter fun u => u.2.1 * t.1 == t.2.1 * u.1).map (·.1)

/-- Their least common multiple. -/
def classLcm (t : ℕ × ℕ × ℕ) : ℕ := (classOrders t).foldr Nat.lcm 1

/-- **The ratio classes of `PF`.**  Every class has lcm at most `90`, except the class
`{24, 40}` of ratio `1/8`, whose lift to order `120` has first entry `15`. -/
def classCheck : Bool :=
  PF.all fun t => 0 < t.1 && 0 < classLcm t &&
    (decide (classLcm t ≤ 90) || (classLcm t == 120 && 120 / t.1 * t.2.1 == 15))

theorem classCheck_true : classCheck = true := by decide +kernel

lemma dvd_foldr_lcm {l : List ℕ} {m : ℕ} (h : m ∈ l) : m ∣ l.foldr Nat.lcm 1 := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.dvd_lcm_left _ _
    · exact (ih h).trans (Nat.dvd_lcm_right _ _)

lemma foldr_lcm_dvd {l : List ℕ} {n : ℕ} (h : ∀ m ∈ l, m ∣ n) : l.foldr Nat.lcm 1 ∣ n := by
  induction l with
  | nil => exact one_dvd n
  | cons y ys ih =>
    exact Nat.lcm_dvd (h y (by simp)) (ih fun m hm => h m (by simp [hm]))

lemma mem_admL {k a : ℕ} {m : ℕ} (h : m ∈ admL k a) : k % m = 0 ∧ ∃ a', a = k / m * a' := by
  simp only [admL, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨t, ⟨-, h1, h2⟩, rfl⟩ := h
  exact ⟨h1, t.2.1, h2⟩

lemma ell_dvd_k {k a : ℕ} : ell k a ∣ k :=
  foldr_lcm_dvd fun _ hm => Nat.dvd_of_mod_eq_zero (mem_admL hm).1

/-- `ell k a` divides the lcm of the ratio class of any failure lifting to `a`. -/
lemma ell_dvd_class {k a : ℕ} {t : ℕ × ℕ × ℕ} (hk : 0 < k) (ht0 : 0 < t.1)
    (hkm : k % t.1 = 0) (ha : a = k / t.1 * t.2.1) : ell k a ∣ classLcm t := by
  refine foldr_lcm_dvd fun m hm => ?_
  simp only [admL, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨u, ⟨hu, hku, hau⟩, rfl⟩ := hm
  have hu0 : 0 < u.1 := by
    rcases Nat.eq_zero_or_pos u.1 with h | h
    · rw [h, Nat.mod_zero] at hku; omega
    · exact h
  obtain ⟨p, hp⟩ := Nat.dvd_of_mod_eq_zero hkm
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hku
  have e1 : k / t.1 = p := by rw [hp, Nat.mul_div_cancel_left _ ht0]
  have e2 : k / u.1 = q := by rw [hq, Nat.mul_div_cancel_left _ hu0]
  rw [e1] at ha; rw [e2] at hau
  have hr : u.2.1 * t.1 = t.2.1 * u.1 := by
    have h1 : k * u.2.1 * t.1 = k * (t.2.1 * u.1) := by
      calc k * u.2.1 * t.1 = (u.1 * q) * u.2.1 * t.1 := by rw [← hq]
        _ = u.1 * t.1 * a := by rw [hau]; ring
        _ = u.1 * t.1 * (p * t.2.1) := by rw [ha]
        _ = (t.1 * p) * (t.2.1 * u.1) := by ring
        _ = k * (t.2.1 * u.1) := by rw [← hp]
    rw [mul_assoc] at h1
    exact Nat.eq_of_mul_eq_mul_left hk h1
  apply dvd_foldr_lcm
  simp only [classOrders, List.mem_map, List.mem_filter, beq_iff_eq]
  exact ⟨u, ⟨hu, hr⟩, rfl⟩

/-- **The lift count.**  For `k > 90`, a first entry `a = (k/m)·a'` of a lifted primitive
failure has `ell k a = k` only at `k = 120`, `a = 15`. -/
lemma lift_count {k a : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ PF) (hk : 90 < k)
    (hkm : k % t.1 = 0) (ha : a = k / t.1 * t.2.1) (hell : ell k a = k) :
    k = 120 ∧ a = 15 := by
  have hc := List.all_eq_true.mp classCheck_true t ht
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨ht0, hpos⟩, hc⟩ := hc
  have hd := ell_dvd_class (by omega) ht0 hkm ha
  rw [hell] at hd
  have hle := Nat.le_of_dvd hpos hd
  rcases hc with hc | ⟨h120, h15⟩
  · omega
  · rw [h120] at hd hle
    have hk120 : k = 120 := by
      obtain ⟨r, hr⟩ := hd
      rcases r with _ | _ | r
      · omega
      · omega
      · nlinarith
    subst hk120
    exact ⟨rfl, by rw [ha, h15]⟩

end E3All
end Bump
end Trop
end PeriodicDifference

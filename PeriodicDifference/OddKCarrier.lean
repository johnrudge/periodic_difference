/-
# `PeriodicDifference/OddKCarrier.lean` — the odd-order carrier: alternating carrier plus bump wave

At odd `k` the paper's second tangent (`sec:odd-carrier`, `prop:odd-second`) linearises
the tangent system of the alternating carrier (`P` = the odd positions) along the bump
wave.  Both scales are combined here into one explicit exact integer solution, `car k = 3·(alternating) + (bump
wave)`:

* odd `n`: `−2` if `n ≡ 1 (mod 2k)` (the bump), `−3` otherwise;
* even `n`: `−1` if `n ≡ k + 1 (mod 2k)`, `0` otherwise.

Its attaining taps at time `n` are `Att n = {j ∈ S : n + j odd, n + j ≢ 1 (mod 2k)}`: the
alternating carrier's argmin with the bump's tap deleted.  A tangent orbit along `car` is
determined by its values at odd positions (`prop:odd-second`): writing `v t = d (2t+1)`, it is the
lift `lift k S v` of any `v` satisfying the reduced recursion `VRec` (the `v`-recursion with
the bump's taps deleted, i.e. the second-tangent system).  The theorem
`not_tropPeriodic_of_vrec` composes this with `thm:tangent`
(`Trop.not_tropPeriodic_of_tangent`, `PeriodicDifference/TropicalQpp.lean`), and
`not_globallyPeriodic_of_vrec` adds `thm:P`.
-/
import PeriodicDifference.SigmaBump

namespace PeriodicDifference
namespace Trop
namespace OddK

open Bump

/-- The combined carrier. -/
def car (k n : ℕ) : ℤ :=
  if n % 2 = 1 then (if n % (2 * k) = 1 then -2 else -3)
  else (if n % (2 * k) = k + 1 then -1 else 0)

/-- The attaining taps at time `n`. -/
def Att (k : ℕ) (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  S.filter (fun j => (n + j) % 2 = 1 ∧ (n + j) % (2 * k) ≠ 1)

/-- The minimum of `v` over the reads (halved positions) of the attaining taps. -/
def rd (k : ℕ) (S : Finset ℕ) (v : ℕ → ℤ) (n : ℕ) : ℤ :=
  if h : (Att k S n).Nonempty then (Att k S n).inf' h (fun j => v ((n + j) / 2)) else 0

/-- The lift of a `v`-orbit to a tangent orbit along `car`. -/
def lift (k : ℕ) (S : Finset ℕ) (v : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n % 2 = 1 then v (n / 2) else rd k S v n - v ((n + k) / 2)

/-- The reduced (second-tangent) recursion. -/
def VRec (k : ℕ) (S : Finset ℕ) (v : ℕ → ℤ) : Prop :=
  ∀ t, v (t + k) = v t + rd k S v (2 * t + 1 + k) - rd k S v (2 * t + 1)

/-! ## Residue arithmetic -/

lemma add_mod_two_k {k : ℕ} (hk : 0 < k) (n j : ℕ) (hj : j < 2 * k) :
    (n + j) % (2 * k) = if n % (2 * k) + j < 2 * k then n % (2 * k) + j
      else n % (2 * k) + j - 2 * k := by
  have h2k : 0 < 2 * k := by omega
  have hr := Nat.mod_lt n h2k
  rw [Nat.add_mod, Nat.mod_eq_of_lt hj]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## The lift -/

lemma lift_odd {k : ℕ} {S : Finset ℕ} {v : ℕ → ℤ} {m : ℕ} (hm : m % 2 = 1) : lift k S v m = v (m / 2) := by
  simp [lift, hm]

lemma lift_add_k {k : ℕ} {S : Finset ℕ} (hk : k % 2 = 1) {v : ℕ → ℤ} (hv : VRec k S v) (n : ℕ) :
    lift k S v (n + k) + lift k S v n = rd k S v n := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have h1 : (n + k) % 2 = 1 := by omega
    simp only [lift, h1, hn, if_true]
    simp
  · have h1 : (n + k) % 2 = 0 := by omega
    obtain ⟨t, rfl⟩ : ∃ t, n = 2 * t + 1 := ⟨n / 2, by omega⟩
    have hv' := hv t
    have e1 : (2 * t + 1 + k + k) / 2 = t + k := by omega
    have e2 : (2 * t + 1) / 2 = t := by omega
    simp only [lift, h1, hn, e1, e2]
    simp only [zero_ne_one, if_false, if_true]
    linarith

/-! ## The carrier is exact -/

section Carrier

variable {k : ℕ} {S : Finset ℕ}

lemma car_add_k (hk : k % 2 = 1) (hk3 : 3 ≤ k) (n : ℕ) : car k (n + k) + car k n = -3 := by
  have hk0 : 0 < k := by omega
  have h1 := add_mod_two_k hk0 n k (by omega)
  have p1 := (Bump.mod_parity (Nat.mul_mod_right 2 k) (n + k)).symm
  have p0 := (Bump.mod_parity (Nat.mul_mod_right 2 k) n).symm
  have hr := Nat.mod_lt n (show 0 < 2 * k by omega)
  unfold car
  split_ifs at h1 ⊢ <;> omega

lemma car_ge (k n : ℕ) : -3 ≤ car k n := by unfold car; split_ifs <;> norm_num

lemma car_eq_iff (k n : ℕ) : car k n = -3 ↔ (n % 2 = 1 ∧ n % (2 * k) ≠ 1) := by
  unfold car; split_ifs <;> constructor <;> intro h <;> first | omega | simp_all

variable (hk : k % 2 = 1) (hS : ∀ j ∈ S, 0 < j ∧ j < k) (hpal : ∀ j ∈ S, k - j ∈ S)
  (hodd : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a % 2 = 1 ∧ b % 2 = 1)
include hk hS hpal hodd

/-- Every time has an attaining tap. -/
lemma att_nonempty (n : ℕ) : (Att k S n).Nonempty := by
  obtain ⟨a, ha, b, hb, hab, hao, hbo⟩ := hodd
  have hk0 : 0 < k := by omega
  have hak := hS a ha
  have hbk := hS b hb
  have hr := Nat.mod_lt n (show 0 < 2 * k by omega)
  have p0 := (Bump.mod_parity (Nat.mul_mod_right 2 k) n).symm
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · -- even time: the odd taps `a`, `b`
    have ea := add_mod_two_k hk0 n a (by omega)
    have eb := add_mod_two_k hk0 n b (by omega)
    by_cases h : (n + a) % (2 * k) = 1
    · refine ⟨b, Finset.mem_filter.mpr ⟨hb, by omega, ?_⟩⟩
      split_ifs at ea eb <;> omega
    · exact ⟨a, Finset.mem_filter.mpr ⟨ha, by omega, h⟩⟩
  · -- odd time: the even taps `k − a`, `k − b`
    have ha' := hpal a ha
    have hb' := hpal b hb
    have ea := add_mod_two_k hk0 n (k - a) (by omega)
    have eb := add_mod_two_k hk0 n (k - b) (by omega)
    by_cases h : (n + (k - a)) % (2 * k) = 1
    · refine ⟨k - b, Finset.mem_filter.mpr ⟨hb', by omega, ?_⟩⟩
      split_ifs at ea eb <;> omega
    · exact ⟨k - a, Finset.mem_filter.mpr ⟨ha', by omega, h⟩⟩

variable {J : List ℕ} (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S) (hSJ : ∀ j ∈ S, j ∈ J)
include hSJ

lemma mval_car (n : ℕ) : mval J (car k) n = -3 := by
  obtain ⟨w, hw⟩ := att_nonempty hk hS hpal hodd n
  obtain ⟨hwS, hw1, hw2⟩ := Finset.mem_filter.mp hw
  have hwJ := hSJ w hwS
  apply le_antisymm
  · have h := mval_le (e := car k) (n := n) hwJ
    have hw0 : w ≠ 0 := (hS w hwS).1.ne'
    simp only [slot, if_neg hw0] at h
    rw [(car_eq_iff k _).mpr ⟨hw1, hw2⟩] at h
    exact h
  · obtain ⟨j, -, hje⟩ := mval_attained (List.ne_nil_of_mem hwJ) (car k) n
    rw [hje]; unfold slot; split_ifs
    · norm_num
    · exact car_ge k _

lemma isTrop_car : IsTrop k J (car k) := by
  intro n
  rw [mval_car hk hS hpal hodd hSJ n]
  obtain ⟨a, ha, b, hb, hab, hao, hbo⟩ := hodd
  have := hS a ha
  have := hS b hb
  exact car_add_k hk (by omega) n

include hJS in
lemma slot_car_iff (n j : ℕ) (hj : j ∈ J) :
    slot (car k) n j = mval J (car k) n ↔ j ∈ Att k S n := by
  rw [mval_car hk hS hpal hodd hSJ n]
  constructor
  · intro h
    by_cases hj0 : j = 0
    · simp [slot, hj0] at h
    · simp only [slot, if_neg hj0] at h
      have hjS := (hJS j hj).resolve_left hj0
      exact Finset.mem_filter.mpr ⟨hjS, (car_eq_iff k _).mp h⟩
  · intro h
    obtain ⟨hjS, h1, h2⟩ := Finset.mem_filter.mp h
    have hj0 : j ≠ 0 := (hS j hjS).1.ne'
    simp only [slot, if_neg hj0]
    exact (car_eq_iff k _).mpr ⟨h1, h2⟩

include hJS in
/-- **The lift is a tangent orbit along the carrier.** -/
lemma tanAlong_lift {v : ℕ → ℤ} (hv : VRec k S v) : TanAlong k J (car k) (lift k S v) := by
  intro n
  have hne := att_nonempty hk hS hpal hodd n
  obtain ⟨w, hw, hwmin⟩ := Finset.exists_min_image (Att k S n) (fun j => v ((n + j) / 2)) hne
  obtain ⟨hwS, hw1, -⟩ := Finset.mem_filter.mp hw
  have hw0 : w ≠ 0 := (hS w hwS).1.ne'
  have hrd : rd k S v n = v ((n + w) / 2) := by
    unfold rd
    rw [dif_pos hne]
    exact le_antisymm (Finset.inf'_le _ hw) (Finset.le_inf' _ _ hwmin)
  refine ⟨w, hSJ w hwS, (slot_car_iff hk hS hpal hodd hJS hSJ n w (hSJ w hwS)).mpr hw, ?_, ?_⟩
  · intro j hj hje
    have hjA := (slot_car_iff hk hS hpal hodd hJS hSJ n j hj).mp hje
    obtain ⟨hjS, hj1, -⟩ := Finset.mem_filter.mp hjA
    have hj0 : j ≠ 0 := (hS j hjS).1.ne'
    simp only [slot, if_neg hw0, if_neg hj0]
    rw [lift_odd hw1, lift_odd hj1]
    exact hwmin j hjA
  · simp only [slot, if_neg hw0]
    rw [lift_add_k hk hv n, lift_odd hw1, hrd]

end Carrier

/-- **The odd-order second-tangent kill, for the min-plus map.**  At odd `k`, with `S`
palindromic and at least two odd taps, a solution `v` of the reduced recursion that is not
`p`-periodic shows, for every slot list with nonzero slots `S` and both θ, that the min-plus map
does not have `p`-th power the identity. -/
theorem not_tropPeriodic_of_vrec {k : ℕ} {S : Finset ℕ} (hk : k % 2 = 1)
    (hS : ∀ j ∈ S, 0 < j ∧ j < k) (hpal : ∀ j ∈ S, k - j ∈ S)
    (hodd : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a % 2 = 1 ∧ b % 2 = 1)
    {J : List ℕ} (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S) (hSJ : ∀ j ∈ S, j ∈ J)
    {v : ℕ → ℤ} (hv : VRec k S v) {p : ℕ} (hnp : ∃ m t, v (t + m * p) ≠ v t) :
    ¬ TropPeriodic k J p := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have ⟨a, ha, _⟩ := hodd
  have hJne : J ≠ [] := List.ne_nil_of_mem (hSJ a ha)
  have hJk : ∀ j ∈ J, j ≤ k' := by
    intro j hj
    rcases hJS j hj with rfl | hjS
    · exact Nat.zero_le _
    · have := (hS j hjS).2; omega
  obtain ⟨m, t, hne⟩ := hnp
  refine not_tropPeriodic_of_tangent hJne hJk (isTrop_car hk hS hpal hodd hSJ)
    (tanAlong_lift hk hS hpal hodd hJS hSJ hv) ⟨2 * m, 2 * t + 1, ?_⟩
  have e0 : 2 * t + 1 + 2 * m * p = 2 * (t + m * p) + 1 := by ring
  rw [e0]
  have e1 : (2 * (t + m * p) + 1) % 2 = 1 := by omega
  have e2 : (2 * t + 1) % 2 = 1 := by omega
  rw [lift_odd e1, lift_odd e2]
  have e3 : (2 * (t + m * p) + 1) / 2 = t + m * p := by omega
  have e4 : (2 * t + 1) / 2 = t := by omega
  rw [e3, e4]; exact hne

/-- **The odd-order second-tangent kill.**  At odd `k`, with `S` palindromic and at least two
odd taps, a solution `v` of the reduced recursion that is not periodic kills every slot list
with nonzero slots `S`, at every positive coefficient choice and both θ
(`not_tropPeriodic_of_vrec` and `thm:P`). -/
theorem not_globallyPeriodic_of_vrec {k : ℕ} {S : Finset ℕ} (hk : k % 2 = 1)
    (hS : ∀ j ∈ S, 0 < j ∧ j < k) (hpal : ∀ j ∈ S, k - j ∈ S)
    (hodd : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a % 2 = 1 ∧ b % 2 = 1)
    {J : List ℕ} (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S) (hSJ : ∀ j ∈ S, j ∈ J)
    {co : ℕ → ℝ} (hco : ∀ j ∈ J, 0 < co j) {v : ℕ → ℤ} (hv : VRec k S v)
    {p : ℕ} (hnp : ∃ m t, v (t + m * p) ≠ v t) :
    ¬ GloballyPeriodic k J co p := by
  have ⟨a, ha, _⟩ := hodd
  exact fun hg => not_tropPeriodic_of_vrec hk hS hpal hodd hJS hSJ hv hnp
    (hg.tropPeriodic_of_supp hS ⟨a, ha⟩ hJS hSJ hco)

end OddK
end Trop
end PeriodicDifference

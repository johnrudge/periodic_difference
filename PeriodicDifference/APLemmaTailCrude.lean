/-
# `PeriodicDifference/APLemmaTailCrude.lean` — a Jacobsthal bound for at least nine prime factors

For `n` with `ω = ω(n) ≥ 9` (`lem:lemmaA-crude`), let `A` (the paper's `B`) be the product of its
primes `≤ ω` and `R` that of the `r` primes `> ω`.  A window of `r + 1` integers holds at most one
multiple of each prime `> ω ≥ r`, so `JacOK R (r + 1)` (`jacOK_of_count`), and
`JacOK (A R) (A (r + 1))` (`jacOK_mul`).  Then `R ≥ (ω+1)(ω+2)⋯(ω+r)` (`rearr_prod`),
`A ≤ primorial ω` (the paper's `ω#`), and `r ≥ ω − π(ω)` give `178 A (r+1)² ≤ 10 R` and
`1000 (r+1) < 102 R`
(`crude_num`: kernel check for `ω ≤ 63`, and `A ≤ 4^ω`, `π(ω) ≤ ω/2 + 1` beyond).
-/
import PeriodicDifference.APLemmaTailJac

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

def P63 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61]

theorem prime_le63 {p : ℕ} (hp : p.Prime) (h : p ≤ 63) : p ∈ P63 := by
  interval_cases p <;> simp_all [P63] <;> norm_num at hp

/-- The numeric core for `9 ≤ ω ≤ 63`. -/
theorem crude_small : (List.range' 9 55).all (fun w => (List.range (w+1)).all fun r =>
    !(decide (w ≤ r + (P63.filter (· ≤ w)).length)) ||
    (decide (178*(P63.filter (· ≤ w)).prod*(r+1)^2 ≤ 10*∏ i ∈ Finset.range r, (w+1+i)) &&
     decide (1000*(r+1) < 102*∏ i ∈ Finset.range r, (w+1+i)))) = true := by
  decide +kernel

/-- At most `w/2 + 1` primes are `≤ w`. -/
theorem card_primes_le (S : Finset ℕ) (w : ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ w) :
    S.card ≤ w/2 + 1 := by
  classical
  have h1 : S ⊆ insert 2 (S.filter (· ≠ 2)) := by
    intro x hx; by_cases h : x = 2
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hx, h⟩)
  have h2 : (S.filter (· ≠ 2)).card ≤ (Finset.Icc 1 (w/2)).card := by
    apply Finset.card_le_card_of_injOn (fun x => x / 2)
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      have hp := (hS x hx.1).1
      have hw := (hS x hx.1).2
      have h2 := hx.2
      have := hp.two_le
      simp only [Finset.coe_Icc, Set.mem_Icc]
      constructor
      · have : x ≠ 2 := h2; omega
      · exact Nat.div_le_div_right hw
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      have ox := (hS x hx.1).1.eq_one_or_self_of_dvd 2
      have oy := (hS y hy.1).1.eq_one_or_self_of_dvd 2
      have hx2 : x % 2 = 1 := by
        rcases Nat.even_or_odd x with h | h
        · exfalso; have := ox (even_iff_two_dvd.1 h); omega
        · exact Nat.odd_iff.1 h
      have hy2 : y % 2 = 1 := by
        rcases Nat.even_or_odd y with h | h
        · exfalso; have := oy (even_iff_two_dvd.1 h); omega
        · exact Nat.odd_iff.1 h
      simp only at hxy
      omega
  have h3 := Finset.card_le_card h1
  have h4 := Finset.card_insert_le 2 (S.filter (· ≠ 2))
  rw [Nat.card_Icc] at h2
  omega

theorem pow4_ge (r : ℕ) (hr : 8 ≤ r) : 2848*(r+1)^2 ≤ 10*4^r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    have : 4^(r+1) = 4*4^r := by ring
    rw [this]; nlinarith [ih]

/-- The numeric core. -/
theorem crude_num {w s r A : ℕ} (hw : 9 ≤ w) (hsr : w = s + r)
    (Ssm : Finset ℕ) (hSc : Ssm.card = s) (hSp : ∀ p ∈ Ssm, p.Prime ∧ p ≤ w)
    (hAe : ∏ p ∈ Ssm, p = A) :
    178*A*(r+1)^2 ≤ 10*∏ i ∈ Finset.range r, (w+1+i) ∧
      1000*(r+1) < 102*∏ i ∈ Finset.range r, (w+1+i) := by
  rcases Nat.lt_or_ge w 64 with hw64 | hw64
  · -- kernel check
    have hsub : Ssm ⊆ (P63.filter (· ≤ w)).toFinset := by
      intro p hp
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨prime_le63 (hSp p hp).1 (by have := (hSp p hp).2; omega), (hSp p hp).2⟩
    have hnd : (P63.filter (· ≤ w)).Nodup := (by decide : P63.Nodup).filter _
    have hsle : s ≤ (P63.filter (· ≤ w)).length := by
      rw [← hSc, ← List.toFinset_card_of_nodup hnd]; exact Finset.card_le_card hsub
    have hAle : A ≤ (P63.filter (· ≤ w)).prod := by
      have e := List.prod_toFinset (fun p => p) hnd
      simp only [List.map_id'] at e
      rw [← hAe, ← e]
      exact Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p hp _ => by
        simp only [List.mem_toFinset, List.mem_filter] at hp
        have : ∀ q ∈ P63, 1 ≤ q := by decide
        exact this p hp.1)
    have hc := crude_small
    simp only [List.all_eq_true, List.mem_range', List.mem_range, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc w ⟨w - 9, by omega, by omega⟩ r (by omega) with h | ⟨h1, h2⟩
    · exact absurd (by omega) h
    · refine ⟨le_trans ?_ h1, h2⟩
      have := Nat.mul_le_mul_right ((r+1)^2) (Nat.mul_le_mul_left 178 hAle)
      linarith
  · -- `A ≤ 4^w`, `s ≤ w/2 + 1`
    have hA4 : A ≤ 4^w := by
      have hdvd : A ∣ primorial w := by
        rw [← hAe]; unfold primorial
        apply Finset.prod_dvd_prod_of_subset
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by have := (hSp p hp).2; omega, (hSp p hp).1⟩
      exact (Nat.le_of_dvd (primorial_pos w) hdvd).trans (primorial_le_4_pow w)
    have hs := card_primes_le Ssm w hSp
    rw [hSc] at hs
    have hr : 31 ≤ r := by omega
    have hw2 : w ≤ 2*r + 2 := by omega
    have hP : 64^r ≤ ∏ i ∈ Finset.range r, (w+1+i) := by
      have := Finset.pow_card_le_prod (Finset.range r) (fun i => w+1+i) 64
        (fun i _ => by show 64 ≤ w + 1 + i; omega)
      simpa using this
    have h4 : 4^w ≤ 16*16^r := by
      calc 4^w ≤ 4^(2*r+2) := Nat.pow_le_pow_right (by norm_num) hw2
        _ = 16*16^r := by rw [pow_add, pow_mul]; ring
    have h64 : 64^r = 16^r*4^r := by rw [← mul_pow]; norm_num
    have hk := pow4_ge r (by omega)
    have h16 : 0 < 16^r := by positivity
    constructor
    · calc 178*A*(r+1)^2 ≤ 178*(16*16^r)*(r+1)^2 := by
            have := hA4.trans h4; gcongr
        _ = 16^r*(2848*(r+1)^2) := by ring
        _ ≤ 16^r*(10*4^r) := Nat.mul_le_mul_left _ hk
        _ = 10*64^r := by rw [h64]; ring
        _ ≤ 10*∏ i ∈ Finset.range r, (w+1+i) := Nat.mul_le_mul_left _ hP
    · have : 1000*(r+1) < 2848*(r+1)^2 := by nlinarith
      have h4r : 4^r ≤ 64^r := Nat.pow_le_pow_left (by norm_num) r
      nlinarith

/-- The crude bound for `ω(n) ≥ 9`. -/
theorem jac_crude {n : ℕ} (hn : 0 < n) (hω : 9 ≤ n.primeFactors.card) :
    ∃ A R r : ℕ, JacOK n (A*(r+1)) ∧ A * R ∣ n ∧ 178*A*(r+1)^2 ≤ 10*R ∧
      1000*(r+1) < 102*R ∧ 0 < A := by
  classical
  set w := n.primeFactors.card with hwdef
  set Ssm := n.primeFactors.filter (· ≤ w) with hSsm
  set T := n.primeFactors.filter (w < ·) with hT
  have hdisj : Disjoint Ssm T := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [hSsm, hT, Finset.mem_filter] at h1 h2; omega
  have hunion : Ssm ∪ T = n.primeFactors := by
    ext p; simp only [hSsm, hT, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h; by_cases hp : p ≤ w
      · exact Or.inl ⟨h, hp⟩
      · exact Or.inr ⟨h, by omega⟩
  have hcard : w = Ssm.card + T.card := by
    rw [hwdef, ← hunion, Finset.card_union_of_disjoint hdisj]
  have hSp : ∀ p ∈ Ssm, p.Prime ∧ p ≤ w := by
    intro p hp; simp only [hSsm, Finset.mem_filter, Nat.mem_primeFactors] at hp
    exact ⟨hp.1.1, hp.2⟩
  have hTp : ∀ p ∈ T, p.Prime ∧ w < p := by
    intro p hp; simp only [hT, Finset.mem_filter, Nat.mem_primeFactors] at hp
    exact ⟨hp.1.1, hp.2⟩
  set A := ∏ p ∈ Ssm, p with hA
  set R := ∏ p ∈ T, p with hR
  set r := T.card with hr
  have hApos : 0 < A := Finset.prod_pos fun p hp => (hSp p hp).1.pos
  have hRge : ∏ i ∈ Finset.range r, (w+1+i) ≤ R :=
    rearr_prod (P := fun y => w < y) (fun i => w+1+i) r (fun i _ => count_gt w i) T
      (fun x hx => (hTp x hx).2) le_rfl
  obtain ⟨h1, h2⟩ := crude_num (by omega) hcard Ssm rfl hSp rfl
  have hAR : A * R ∣ n := by
    rw [hA, hR, ← Finset.prod_union hdisj, hunion]; exact Nat.prod_primeFactors_dvd n
  refine ⟨A, R, r, ?_, hAR, h1.trans (Nat.mul_le_mul_left _ hRge),
    h2.trans_le (Nat.mul_le_mul_left _ hRge), hApos⟩
  -- the Jacobsthal bound
  have hcnt : CountOK 1 (r+1) (r+1) := by
    intro X
    rw [Finset.filter_true_of_mem (fun i _ => by simpa using isCoprime_one_right), Finset.card_range]
  have hRJ : JacOK R (r+1) := by
    refine jacOK_of_count hcnt T (fun p hp => (hTp p hp).1) ?_ ?_
    · have : ∀ p ∈ T, (r + 1 + p - 1)/p = 1 := by
        intro p hp
        have hp' := (hTp p hp).2
        have : r + 1 + p - 1 = r + p := by omega
        rw [this, Nat.add_div_right _ (by omega), Nat.div_eq_of_lt (by omega)]
      rw [Finset.sum_congr rfl this]; simp [hr]
    · intro ℓ hℓ hdvd; right
      obtain ⟨p, hp, hℓp⟩ := (Prime.dvd_finset_prod_iff hℓ.prime _).1 hdvd
      rwa [(Nat.prime_dvd_prime_iff_eq hℓ (hTp p hp).1).1 hℓp]
  have hcop : Nat.Coprime A R := by
    apply Nat.Coprime.prod_left; intro p hp
    apply Nat.Coprime.prod_right; intro q hq
    exact (Nat.coprime_primes (hSp p hp).1 (hTp q hq).1).2
      (by have := (hSp p hp).2; have := (hTp q hq).2; omega)
  refine jacOK_of_primes (jacOK_mul hRJ hApos hcop) ?_
  intro ℓ hℓ hdvd
  have hmem : ℓ ∈ Ssm ∪ T := by rw [hunion]; exact Nat.mem_primeFactors.2 ⟨hℓ, hdvd, hn.ne'⟩
  rcases Finset.mem_union.1 hmem with h | h
  · exact (Finset.dvd_prod_of_mem (fun p => p) h).trans (Dvd.intro _ rfl)
  · exact (Finset.dvd_prod_of_mem (fun p => p) h).trans (Dvd.intro_left _ rfl)

end APLemma
end Bump
end Trop
end PeriodicDifference

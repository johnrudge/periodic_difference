/-
# `PeriodicDifference/APLemmaTailJac.lean` — elementary Jacobsthal bounds

* `jacOK_of_primes` — `JacOK` depends only on the set of prime factors;
* `CountOK s m c` — every window of `m` consecutive integers has `≥ c` elements prime to `s`;
  decided by a sliding window over one period (`slideCheck`, `countOK_of_check`);
* `jacOK_of_count` — the union bound (Jacobsthal, "Kanold-P." of Costello–Watts): `c` elements
  prime to `s`, minus at most `⌈m/p⌉` multiples of each further prime `p`;
* `jacOK_mul` — the progression trick `j(f d) ≤ f j(d)` for `gcd(f, d) = 1`.
-/
import Mathlib
import PeriodicDifference.APLemmaJac

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

theorem isCoprime_of_primes {x : ℤ} {n m : ℕ} (h : IsCoprime x (n:ℤ))
    (hp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ n) : IsCoprime x (m:ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one] at h ⊢
  have h' : Nat.Coprime x.natAbs n := h
  show Nat.Coprime x.natAbs m
  apply Nat.coprime_of_dvd
  intro ℓ hℓ h1 h2
  exact Nat.Prime.not_dvd_one hℓ (h' ▸ Nat.dvd_gcd h1 (hp ℓ hℓ h2))

theorem jacOK_of_primes {n m J : ℕ} (h : JacOK n J)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ n) : JacOK m J := by
  intro X
  obtain ⟨i, hi, hc⟩ := h X
  exact ⟨i, hi, isCoprime_of_primes hc hp⟩

/-- Every window of `m` consecutive integers contains at least `c` elements prime to `s`. -/
def CountOK (s m c : ℕ) : Prop :=
  ∀ X : ℤ, c ≤ ((Finset.range m).filter (fun i : ℕ => IsCoprime (X + i) (s:ℤ))).card

/-- Multiples of `p` in a window of length `m`: at most `⌈m/p⌉`. -/
theorem card_multiples_le (X : ℤ) (m p : ℕ) (hp : 0 < p) :
    ((Finset.range m).filter (fun i : ℕ => (p:ℤ) ∣ X + i)).card ≤ (m + p - 1)/p := by
  classical
  calc ((Finset.range m).filter (fun i : ℕ => (p:ℤ) ∣ X + i)).card
      ≤ (Finset.range ((m + p - 1)/p)).card := by
        apply Finset.card_le_card_of_injOn (fun i => i / p)
        · intro i hi
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
          simp only [Finset.coe_range, Set.mem_Iio]
          have h1 : i / p ≤ (m - 1)/p := Nat.div_le_div_right (by omega)
          have h2 : (m - 1)/p < (m + p - 1)/p := by
            have : m + p - 1 = (m - 1) + p := by omega
            rw [this, Nat.add_div_right _ hp]; omega
          omega
        · intro i hi i' hi' heq
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hi'
          have hd : (p:ℤ) ∣ (i:ℤ) - i' := by
            have := dvd_sub hi.2 hi'.2; simpa using this
          have hmod : i % p = i' % p := by
            have := (Int.ModEq.symm ((Int.modEq_iff_dvd).2 hd))
            exact_mod_cast this
          simp only at heq
          rw [← Nat.div_add_mod i p, ← Nat.div_add_mod i' p, heq, hmod]
    _ = (m + p - 1)/p := Finset.card_range _

/-- The union bound. -/
theorem jacOK_of_count {n s m c : ℕ} (hc : CountOK s m c) (T : Finset ℕ)
    (hTp : ∀ p ∈ T, p.Prime) (hsum : ∑ p ∈ T, (m + p - 1)/p < c)
    (hcov : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ∣ s ∨ ℓ ∈ T) : JacOK n m := by
  classical
  intro X
  set C := (Finset.range m).filter (fun i : ℕ => IsCoprime (X + i) (s:ℤ))
  set B := T.biUnion (fun p => (Finset.range m).filter (fun i : ℕ => (p:ℤ) ∣ X + i))
  have hB : B.card < C.card := by
    calc B.card ≤ ∑ p ∈ T, ((Finset.range m).filter (fun i : ℕ => (p:ℤ) ∣ X + i)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ p ∈ T, (m + p - 1)/p :=
          Finset.sum_le_sum fun p hp => card_multiples_le X m p (hTp p hp).pos
      _ < c := hsum
      _ ≤ C.card := hc X
  obtain ⟨i, hiC, hiB⟩ := Finset.exists_mem_notMem_of_card_lt_card hB
  simp only [C, Finset.mem_filter, Finset.mem_range] at hiC
  refine ⟨i, hiC.1, ?_⟩
  have hs := hiC.2
  rw [Int.isCoprime_iff_gcd_eq_one] at hs ⊢
  show Nat.Coprime (X + i).natAbs n
  have hs' : Nat.Coprime (X + i).natAbs s := hs
  apply Nat.coprime_of_dvd
  intro ℓ hℓ h1 h2
  rcases hcov ℓ hℓ h2 with h | h
  · exact Nat.Prime.not_dvd_one hℓ (hs' ▸ Nat.dvd_gcd h1 h)
  · apply hiB
    simp only [B, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
    exact ⟨ℓ, h, hiC.1, Int.natCast_dvd.2 h1⟩

/-- The progression trick: `j(f d) ≤ f · j(d)` when `gcd(f, d) = 1`. -/
theorem jacOK_mul {f d J : ℕ} (hJ : JacOK d J) (hf : 0 < f) (hfd : Nat.Coprime f d) :
    JacOK (f*d) (f*J) := by
  intro X
  have hfd' : IsCoprime (f:ℤ) (d:ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]; exact hfd
  obtain ⟨z, w, hzw⟩ := hfd'
  set r : ℕ := ((1 - X) % f).toNat with hr
  have hfz : (0:ℤ) < f := by exact_mod_cast hf
  have hr' : (r:ℤ) = (1 - X) % f := Int.toNat_of_nonneg (Int.emod_nonneg _ hfz.ne')
  have hrf : r < f := by have := Int.emod_lt_of_pos (1 - X) hfz; omega
  obtain ⟨t, ht, hct⟩ := hJ (z*(X + r))
  refine ⟨r + f*t, ?_, ?_⟩
  · have : t + 1 ≤ J := ht
    nlinarith
  · push_cast
    have hmod : (f:ℤ) ∣ X + r - 1 := by
      rw [hr']; have := Int.emod_add_mul_ediv (1 - X) f
      exact ⟨-((1 - X) / f), by linarith⟩
    obtain ⟨u, hu⟩ := hmod
    apply IsCoprime.mul_right
    · -- `X + r + f t ≡ 1 (mod f)`
      refine ⟨1, -(u + t), ?_⟩
      linear_combination hu
    · -- `X + r + f t = f (z(X + r) + t) + d w (X + r)`
      have e : X + (r + f*t) = (z*(X + r) + t) * f + (w*(X + r)) * d := by
        linear_combination (-(X + r)) * hzw
      rw [e]
      exact (IsCoprime.mul_left hct ⟨z, w, hzw⟩).add_mul_right_left _

/-- Indicator of `gcd(y, s) = 1`. -/
def ind (s y : ℕ) : ℕ := if Nat.gcd y s = 1 then 1 else 0

/-- Number of `i < m` with `gcd(x + i, s) = 1`. -/
def cw (s : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m+1, x => ind s x + cw s m (x+1)

theorem cw_shift (s m x : ℕ) : cw s m (x+1) + ind s x = cw s m x + ind s (x+m) := by
  induction m generalizing x with
  | zero => simp [cw]
  | succ m ih =>
    simp only [cw]
    have := ih (x+1)
    rw [show x + 1 + m = x + (m + 1) by ring] at this
    omega

theorem cw_eq_card (s m x : ℕ) :
    cw s m x = ((Finset.range m).filter (fun i => Nat.gcd (x+i) s = 1)).card := by
  induction m generalizing x with
  | zero => simp [cw]
  | succ m ih =>
    rw [Finset.card_filter, Finset.sum_range_succ', ← Finset.card_filter, cw, ih (x+1)]
    simp only [ind, add_zero]
    have : ∀ i, x + 1 + i = x + (i + 1) := fun i => by ring
    simp only [this]; ring

/-- The sliding-window scan of one period. -/
def slide (s m c : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | fuel+1, x, cur => decide (c ≤ cur) && slide s m c fuel (x+1) (cur + ind s (x+m) - ind s x)

def slideCheck (s m c : ℕ) : Bool := decide (0 < s) && slide s m c s 0 (cw s m 0)

theorem slide_sound (s m c : ℕ) : ∀ fuel x, slide s m c fuel x (cw s m x) = true →
    ∀ y, x ≤ y → y < x + fuel → c ≤ cw s m y := by
  intro fuel
  induction fuel with
  | zero => intro x _ y h1 h2; omega
  | succ fuel ih =>
    intro x h y h1 h2
    simp only [slide, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact h.1
    · have e : cw s m x + ind s (x+m) - ind s x = cw s m (x+1) := by
        have := cw_shift s m x; omega
      rw [e] at h
      exact ih (x+1) h.2 y h1 (by omega)

theorem countOK_of_check {s m c : ℕ} (h : slideCheck s m c = true) : CountOK s m c := by
  simp only [slideCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hs, h⟩ := h
  intro X
  have hs' : (0:ℤ) < s := by exact_mod_cast hs
  set x := (X % s).toNat with hx
  have hxX : (x : ℤ) = X % s := Int.toNat_of_nonneg (Int.emod_nonneg _ hs'.ne')
  have hxs : x < s := by have := Int.emod_lt_of_pos X hs'; omega
  have := slide_sound s m c s 0 h x (by omega) (by omega)
  rw [cw_eq_card] at this
  refine this.trans (le_of_eq ?_)
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [Int.isCoprime_iff_gcd_eq_one, ← Int.gcd_emod, Int.add_emod, ← hxX]
  have : ((x:ℤ) + (i:ℤ) % s) % s = ((x + i : ℕ) : ℤ) % s := by
    push_cast; rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]
  rw [this, Int.gcd_emod, Int.gcd_natCast_natCast]

/-- The largest element of a set of `r + 1` elements of `P` is at least the `r`-th element
of `P` (0-indexed), recognised through `count P (q r) = r`. -/
theorem le_of_count {P : ℕ → Prop} [DecidablePred P] {q : ℕ → ℕ} {r x : ℕ}
    (hq : Nat.count P (q r) = r) (T : Finset ℕ) (hT : ∀ y ∈ T, P y ∧ y < x) (hx : P x)
    (hcard : T.card = r) : q r ≤ x := by
  by_contra hlt
  push_neg at hlt
  have h1 : (insert x T) ⊆ (Finset.range (x+1)).filter P := by
    intro y hy
    simp only [Finset.mem_insert] at hy
    simp only [Finset.mem_filter, Finset.mem_range]
    rcases hy with rfl | hy
    · exact ⟨by omega, hx⟩
    · exact ⟨by have := (hT y hy).2; omega, (hT y hy).1⟩
  have h2 := Finset.card_le_card h1
  rw [Finset.card_insert_of_notMem (fun h => by have := (hT x h).2; omega), hcard,
    ← Nat.count_eq_card_filter_range] at h2
  have h3 := Nat.count_monotone P (show x + 1 ≤ q r by omega)
  omega

theorem rearr_sum {P : ℕ → Prop} [DecidablePred P] (q : ℕ → ℕ) (L : ℕ)
    (hq : ∀ i < L, Nat.count P (q i) = i) (f : ℕ → ℕ)
    (hf : ∀ i < L, ∀ b, q i ≤ b → f b ≤ f (q i)) :
    ∀ T : Finset ℕ, (∀ x ∈ T, P x) → T.card ≤ L →
      ∑ x ∈ T, f x ≤ ∑ i ∈ Finset.range T.card, f (q i) := by
  intro T
  induction T using Finset.induction_on_max with
  | h0 => intros; simp
  | step x T hlt ih =>
    intro hP hL
    have hxT : x ∉ T := fun h => lt_irrefl _ (hlt x h)
    rw [Finset.sum_insert hxT, Finset.card_insert_of_notMem hxT, Finset.sum_range_succ]
    rw [Finset.card_insert_of_notMem hxT] at hL
    have hle := le_of_count (hq T.card (by omega)) T
      (fun y hy => ⟨hP y (Finset.mem_insert_of_mem hy), hlt y hy⟩)
      (hP x (Finset.mem_insert_self _ _)) rfl
    have := ih (fun y hy => hP y (Finset.mem_insert_of_mem hy)) (by omega)
    have := hf T.card (by omega) x hle
    omega

theorem rearr_prod {P : ℕ → Prop} [DecidablePred P] (q : ℕ → ℕ) (L : ℕ)
    (hq : ∀ i < L, Nat.count P (q i) = i) :
    ∀ T : Finset ℕ, (∀ x ∈ T, P x) → T.card ≤ L →
      ∏ i ∈ Finset.range T.card, q i ≤ ∏ x ∈ T, x := by
  intro T
  induction T using Finset.induction_on_max with
  | h0 => intros; simp
  | step x T hlt ih =>
    intro hP hL
    have hxT : x ∉ T := fun h => lt_irrefl _ (hlt x h)
    rw [Finset.prod_insert hxT, Finset.card_insert_of_notMem hxT, Finset.prod_range_succ]
    rw [Finset.card_insert_of_notMem hxT] at hL
    have hle := le_of_count (hq T.card (by omega)) T
      (fun y hy => ⟨hP y (Finset.mem_insert_of_mem hy), hlt y hy⟩)
      (hP x (Finset.mem_insert_self _ _)) rfl
    have := ih (fun y hy => hP y (Finset.mem_insert_of_mem hy)) (by omega)
    rw [mul_comm x]
    exact Nat.mul_le_mul this hle

/-- `count (b < ·) (b + 1 + i) = i`. -/
theorem count_gt (b i : ℕ) : Nat.count (fun y => b < y) (b + 1 + i) = i := by
  induction i with
  | zero =>
    rw [Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy; simp only [Finset.mem_range] at hy; omega
  | succ i ih =>
    rw [show b + 1 + (i+1) = (b + 1 + i) + 1 by ring, Nat.count_succ, ih]
    simp; omega

end APLemma
end Bump
end Trop
end PeriodicDifference

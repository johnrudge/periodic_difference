/-
# `PeriodicDifference/APLemmaTwoPrime.lean` — `prop:lemmaA-twoprime`: Lemma A when `k` has two odd primes

For even `k ≥ 92` with at most two odd prime factors (`TwoPrime k`), every admissible pair
`(a, e)` has a witness (`good_twoPrime`), by hand.  One of `a − e`, `a`, `a + e` is a unit
(`TwoPrime.unit3`), and scaling by its inverse gives one of three normal forms:

* `a` a unit: the pair `(1, D)`.  A unit `m < k` with `m·D` in the window
  `((2i+1)k + m, (2i+2)k − m)` is a witness (`good_of_win`).  For `4 ≤ D ≤ k/8` three
  consecutive odd integers lie in `(k/(D − 1), 2k/(D + 1))`, and one is a unit (`win_I3`); for
  `k/8 < D ≤ k/2` a chain of small multipliers, chosen by the small primes dividing `k`, works
  (`win_chain`, the table `tab:lemmaA-chains`); `D ↦ k − D` keeps the witness (`win_mirror`),
  and `m = 1` covers `k < D < 2k` (`goodM`).
* `a − e` a unit: the pair `(A, A − 1)` with `f = gcd(A, 2k) > 1`.  A unit `ν < k` with
  `νA ≡ f·c` and the right half for `ν(2A − 1)` is a witness (`good_vert`); `ν ≡ c·w⁻¹
  (mod 2k/f)`, `A = f·w`: three lifts (`f ≥ 15`), two lifts (`5 ≤ f ≤ 13`, a prime power), one
  lift (`f = 3`, `9 ∣ k`), or `c ∈ {1, k/3 − 3, k/3 − 5, k/3 − 11}` (`f = 3`, `3 ∥ k`) (`goodF`).
* `a + e` a unit: the pair `(A', 1 − A')`, which has the witnesses of `(A' + k, A' + k − 1)`
  (`good_shift`).
-/
import PeriodicDifference.APLemmaHand

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

/-! ## Units -/

lemma coprime_two_k {n k : ℕ} (hn : n % 2 = 1) (h : Nat.Coprime n k) : Nat.Coprime n (2*k) :=
  Nat.Coprime.mul_right (Nat.coprime_two_right.2 (Nat.odd_iff.2 hn)) h

lemma one_lt_gcd_of_not_coprime {n k : ℕ} (hn : n % 2 = 1) (h : ¬ Nat.Coprime n (2*k)) :
    1 < Nat.gcd n k := by
  have h1 : Nat.gcd n k ≠ 1 := fun e => h (coprime_two_k hn e)
  have h0 : Nat.gcd n k ≠ 0 := by
    intro e; rw [Nat.gcd_eq_zero_iff] at e; omega
  omega

/-- Of three odd numbers, no two sharing a factor with `k`, one is a unit. -/
lemma TwoPrime.unit3 {k n₁ n₂ n₃ : ℕ} (hP : TwoPrime k) (h1 : n₁ % 2 = 1) (h2 : n₂ % 2 = 1)
    (h3 : n₃ % 2 = 1) (c12 : Nat.gcd (Nat.gcd n₁ n₂) k = 1)
    (c13 : Nat.gcd (Nat.gcd n₁ n₃) k = 1) (c23 : Nat.gcd (Nat.gcd n₂ n₃) k = 1) :
    Nat.Coprime n₁ (2*k) ∨ Nat.Coprime n₂ (2*k) ∨ Nat.Coprime n₃ (2*k) := by
  by_contra h
  push_neg at h
  rcases hP n₁ n₂ n₃ h1 h2 h3 (one_lt_gcd_of_not_coprime h1 h.1)
    (one_lt_gcd_of_not_coprime h2 h.2.1) (one_lt_gcd_of_not_coprime h3 h.2.2) with c | c | c <;>
    omega

/-- Three distinct odd primes cannot all divide `k`. -/
lemma TwoPrime.no3 {k : ℕ} (hP : TwoPrime k) (p q r : ℕ)
    (ho : p % 2 = 1 ∧ q % 2 = 1 ∧ r % 2 = 1) (h1 : 1 < p ∧ 1 < q ∧ 1 < r)
    (hc : Nat.gcd p q = 1 ∧ Nat.gcd p r = 1 ∧ Nat.gcd q r = 1)
    (hp : p ∣ k) (hq : q ∣ k) (hr : r ∣ k) : False := by
  have := hP p q r ho.1 ho.2.1 ho.2.2 (by rw [Nat.gcd_eq_left hp]; exact h1.1)
    (by rw [Nat.gcd_eq_left hq]; exact h1.2.1) (by rw [Nat.gcd_eq_left hr]; exact h1.2.2)
  rw [hc.1, hc.2.1, hc.2.2, Nat.gcd_one_left] at this
  omega

/-- `gcd(x, x + y) = gcd(x, y)`. -/
lemma gcd_shift (x y : ℕ) : Nat.gcd x (x + y) = Nat.gcd x y := by
  rw [add_comm, Nat.gcd_add_self_right]

/-- An odd prime `p ∤ k` is a unit modulo `2k`. -/
lemma prime_unit {p k : ℕ} (hp : p.Prime) (hpo : p % 2 = 1) (hpk : ¬ p ∣ k) :
    Nat.Coprime p (2*k) :=
  coprime_two_k hpo ((Nat.Prime.coprime_iff_not_dvd hp).2 hpk)

lemma int_gcd_of_coprime {m k : ℕ} (h : Nat.Coprime m (2*k)) : Int.gcd (m:ℤ) (2*(k:ℤ)) = 1 := by
  have e : (2*(k:ℤ)) = ((2*k : ℕ) : ℤ) := by push_cast; ring
  rw [e, Int.gcd_natCast_natCast]; exact h

/-! ## Unit `a`: the pair `(1, D)` -/

/-- `m·D` lies in the upper half `(k + m, 2k − m)` of an odd block. -/
def Win (k : ℕ) (m D : ℤ) : Prop := ∃ i : ℤ, (2*i+1)*k + m < m*D ∧ m*D < (2*i+2)*k - m

/-- A unit `0 < m < k` with `m·D` in the window is a witness for `(1, D)`. -/
theorem good_of_win {k : ℕ} {m D : ℤ} (hm : Int.gcd m (2*k) = 1) (h0 : 0 < m) (hmk : m < k)
    (hw : Win k m D) : Good k 1 D := by
  obtain ⟨i, h1, h2⟩ := hw
  have hk : (0:ℤ) < 2*k := by omega
  set Y := m*D - 2*k*i with hY
  have hY1 : k + m < Y := by rw [hY]; linarith
  have hY2 : Y < 2*k - m := by rw [hY]; linarith
  have hmod : ∀ (z t : ℤ), 0 ≤ z → z < 2*k → (z + 2*k*t) % (2*k) = z := by
    intro z t hz1 hz2
    rw [Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt hz1 hz2
  refine ⟨m, hm, ?_, ?_⟩
  · have e1 : m*(1-D) = (m - Y + 2*k) + 2*k*(-i-1) := by rw [hY]; ring
    have e2 : m*1 = m + 2*k*0 := by ring
    rw [e1, e2, hmod _ _ (by linarith) (by linarith), hmod _ _ (by linarith) (by linarith)]
    constructor <;> intro _ <;> linarith
  · have e1 : m*(1+D) = (m + Y) + 2*k*i := by rw [hY]; ring
    have e2 : m*1 = m + 2*k*0 := by ring
    rw [e1, e2, hmod _ _ (by linarith) (by linarith), hmod _ _ (by linarith) (by linarith)]
    constructor
    · intro h; linarith
    · intro h; exact absurd hmk (by linarith)

/-- `D ↦ k − D` keeps the window, for odd `m`. -/
theorem win_mirror {k : ℕ} {m D : ℤ} (hm : m % 2 = 1) (hw : Win k m (k - D)) : Win k m D := by
  obtain ⟨i, h1, h2⟩ := hw
  obtain ⟨h, rfl⟩ : ∃ h, m = 2*h + 1 := ⟨m / 2, by omega⟩
  refine ⟨h - 1 - i, ?_, ?_⟩
  · have e : (2*(h-1-i)+1)*(k:ℤ) + (2*h+1) = (2*h+1)*k - ((2*i+2)*k - (2*h+1)) := by ring
    have e2 : (2*h+1)*D = (2*h+1)*k - (2*h+1)*(k - D) := by ring
    rw [e, e2]; linarith
  · have e : (2*(h-1-i)+2)*(k:ℤ) - (2*h+1) = (2*h+1)*k - ((2*i+1)*k + (2*h+1)) := by ring
    have e2 : (2*h+1)*D = (2*h+1)*k - (2*h+1)*(k - D) := by ring
    rw [e, e2]; linarith

/-- The key inequality for the long interval: `6(D² − 1) < k(D − 3)`. -/
lemma long_ineq {k D : ℕ} (hk : 92 ≤ k) (hD4 : 4 ≤ D) (hD8 : 8*D ≤ k) :
    6*(D*D) + 3*k < k*D + 6 := by
  rcases Nat.lt_or_ge D 12 with h | h
  · interval_cases D <;> omega
  · obtain ⟨E, rfl⟩ : ∃ E, D = E + 12 := ⟨D - 12, by omega⟩
    have h2 : 8*(E+12)*(E+9) ≤ k*(E+9) := Nat.mul_le_mul_right _ hD8
    nlinarith

lemma gcd_odd_two {n : ℕ} (hn : n % 2 = 1) : Nat.gcd n 2 = 1 :=
  Nat.coprime_two_right.2 (Nat.odd_iff.2 hn)

lemma gcd_odd_four {n : ℕ} (hn : n % 2 = 1) : Nat.gcd n 4 = 1 := by
  have := Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 (Nat.odd_iff.2 hn))
  simpa using this

/-- **Small `D`**: three consecutive odd integers in `(k/(D−1), 2k/(D+1))`, one of them a unit. -/
theorem win_I3 {k D : ℕ} (hk : 92 ≤ k) (hP : TwoPrime k) (hD4 : 4 ≤ D) (hD8 : 8*D ≤ k) :
    ∃ m : ℕ, m % 2 = 1 ∧ Nat.Coprime m (2*k) ∧ 0 < m ∧ m < k ∧ Win k m D := by
  set Q := k / (D - 1) with hQ
  have hQ1 : Q * (D-1) ≤ k := Nat.div_mul_le_self k (D-1)
  have hQ2 : k < (Q+1) * (D-1) := by
    have := Nat.lt_div_mul_add (a := k) (b := D - 1) (by omega)
    rw [← hQ] at this; nlinarith
  set m₀ := if (Q+1) % 2 = 1 then Q+1 else Q+2 with hm₀
  have hm₀o : m₀ % 2 = 1 := by rw [hm₀]; split_ifs <;> omega
  have hm₀1 : Q + 1 ≤ m₀ ∧ m₀ ≤ Q + 2 := by rw [hm₀]; split_ifs <;> omega
  have hL := long_ineq hk hD4 hD8
  -- `(m₀ + 4)(D + 1) < 2k`
  have hup : (m₀ + 4) * (D + 1) < 2*k := by
    have h1 : (m₀ + 4) * (D+1) ≤ (Q + 6) * (D+1) := Nat.mul_le_mul_right _ (by omega)
    have h2 : (Q + 6) * (D+1) * (D - 1) < 2*k*(D-1) := by
      have e1 : (Q + 6) * (D+1) * (D - 1) = Q*(D-1)*(D+1) + 6*((D+1)*(D-1)) := by ring
      have e2 : (D+1)*(D-1) = D*D - 1 := by
        obtain ⟨E, rfl⟩ : ∃ E, D = E + 1 := ⟨D - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring_nf; omega
      have e3 : 2*k*(D-1) = k*(D+1) + (k*D - 3*k) := by
        obtain ⟨E, rfl⟩ : ∃ E, D = E + 4 := ⟨D - 4, by omega⟩
        simp only [show E + 4 - 1 = E + 3 by omega]
        have : 3*k ≤ k*(E+4) := by nlinarith
        ring_nf; omega
      have h3 : Q*(D-1)*(D+1) ≤ k*(D+1) := Nat.mul_le_mul_right _ hQ1
      rw [e1, e2, e3]
      have : 4 ≤ D*D := by nlinarith
      omega
    have h4 : (Q + 6) * (D+1) < 2*k := Nat.lt_of_mul_lt_mul_right h2
    omega
  have hlow : k < m₀ * (D - 1) := lt_of_lt_of_le hQ2 (Nat.mul_le_mul_right _ hm₀1.1)
  have hwin : ∀ m, m₀ ≤ m → m ≤ m₀ + 4 → Win k m D := by
    intro m h1 h2
    refine ⟨0, ?_, ?_⟩
    · have : k < m * (D-1) := lt_of_lt_of_le hlow (Nat.mul_le_mul_right _ h1)
      have e : m * (D - 1) + m = m * D := by
        rw [← Nat.mul_succ]; congr 1; omega
      push_cast; zify [show 1 ≤ D by omega] at this e; linarith
    · have : m * (D+1) < 2*k := lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hup
      have e : m * (D + 1) = m * D + m := by ring
      push_cast; zify at this e; linarith
  have hsmall : m₀ + 4 < k := by
    have : (m₀ + 4) * 5 ≤ (m₀ + 4) * (D+1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have c12 : Nat.gcd (Nat.gcd m₀ (m₀ + 2)) k = 1 := by
    rw [gcd_shift, gcd_odd_two hm₀o, Nat.gcd_one_left]
  have c13 : Nat.gcd (Nat.gcd m₀ (m₀ + 4)) k = 1 := by
    rw [gcd_shift, gcd_odd_four hm₀o, Nat.gcd_one_left]
  have c23 : Nat.gcd (Nat.gcd (m₀ + 2) (m₀ + 4)) k = 1 := by
    rw [show m₀ + 4 = (m₀ + 2) + 2 by ring, gcd_shift, gcd_odd_two (by omega), Nat.gcd_one_left]
  rcases hP.unit3 hm₀o (by omega) (by omega) c12 c13 c23 with hu | hu | hu
  · exact ⟨m₀, hm₀o, hu, by omega, by omega, hwin m₀ le_rfl (by omega)⟩
  · exact ⟨m₀ + 2, by omega, hu, by omega, by omega, hwin _ (by omega) (by omega)⟩
  · exact ⟨m₀ + 4, by omega, hu, by omega, hsmall, hwin _ (by omega) le_rfl⟩

/-- `m·D` in the block `i` for a literal multiplier. -/
lemma win_lit {k D : ℕ} (m i : ℕ) (h1 : (2*i+1)*k + m < m*D) (h2 : m*D + m < (2*i+2)*k) :
    Win k m D :=
  ⟨i, by exact_mod_cast h1, by zify at h2; linarith⟩

/-- **Large `D`**, `k/8 < D ≤ k/2`: walk along the chain of `tab:lemmaA-chains` for the small
primes dividing `k`; a failure of the right inequality of one rule is the left inequality of the
next. -/
theorem win_chain {k D : ℕ} (hk : 92 ≤ k) (he : k % 2 = 0) (hP : TwoPrime k) (hD8 : k < 8*D)
    (hD2 : 2*D ≤ k) :
    ∃ m : ℕ, m % 2 = 1 ∧ Nat.Coprime m (2*k) ∧ 0 < m ∧ m < k ∧ Win k m D := by
  have no3 := hP.no3
  have U : ∀ {m : ℕ} (j p : ℕ), p.Prime → p % 2 = 1 → m = p^j → ¬ p ∣ k →
      Nat.Coprime m (2*k) := fun j p hp hpo hm hpk => hm ▸ Nat.Coprime.pow_left j
        (prime_unit hp hpo hpk)
  by_cases h3 : 3 ∣ k
  · by_cases h5 : 5 ∣ k
    · have n7 : ¬ 7 ∣ k := fun h => no3 3 5 7 (by norm_num) (by norm_num) (by norm_num) h3 h5 h
      have n11 : ¬ 11 ∣ k := fun h => no3 3 5 11 (by norm_num) (by norm_num) (by norm_num) h3 h5 h
      have n13 : ¬ 13 ∣ k := fun h => no3 3 5 13 (by norm_num) (by norm_num) (by norm_num) h3 h5 h
      have n19 : ¬ 19 ∣ k := fun h => no3 3 5 19 (by norm_num) (by norm_num) (by norm_num) h3 h5 h
      have n31 : ¬ 31 ∣ k := fun h => no3 3 5 31 (by norm_num) (by norm_num) (by norm_num) h3 h5 h
      have n43 : ¬ 43 ∣ k := fun h => no3 3 5 43 (by norm_num) (by norm_num) (by norm_num) h3 h5 h
      by_cases r0 : 11*D + 11 < 2*k
      · exact ⟨11, by norm_num, U 1 11 (by norm_num) (by norm_num) (by norm_num) n11, by norm_num, by omega, win_lit 11 0 (by omega) r0⟩
      by_cases r1 : 7*D + 7 < 2*k
      · exact ⟨7, by norm_num, U 1 7 (by norm_num) (by norm_num) (by norm_num) n7, by norm_num, by omega, win_lit 7 0 (by omega) r1⟩
      by_cases r2 : 19*D + 19 < 6*k
      · exact ⟨19, by norm_num, U 1 19 (by norm_num) (by norm_num) (by norm_num) n19, by norm_num, by omega, win_lit 19 2 (by omega) r2⟩
      by_cases r3 : 11*D + 11 < 4*k
      · exact ⟨11, by norm_num, U 1 11 (by norm_num) (by norm_num) (by norm_num) n11, by norm_num, by omega, win_lit 11 1 (by omega) r3⟩
      by_cases r4 : 49*D + 49 < 18*k
      · exact ⟨49, by norm_num, U 2 7 (by norm_num) (by norm_num) (by norm_num) n7, by norm_num, by omega, win_lit 49 8 (by omega) r4⟩
      by_cases r5 : 43*D + 43 < 16*k
      · exact ⟨43, by norm_num, U 1 43 (by norm_num) (by norm_num) (by norm_num) n43, by norm_num, by omega, win_lit 43 7 (by omega) r5⟩
      by_cases r6 : 31*D + 31 < 12*k
      · exact ⟨31, by norm_num, U 1 31 (by norm_num) (by norm_num) (by norm_num) n31, by norm_num, by omega, win_lit 31 5 (by omega) r6⟩
      by_cases r7 : 19*D + 19 < 8*k
      · exact ⟨19, by norm_num, U 1 19 (by norm_num) (by norm_num) (by norm_num) n19, by norm_num, by omega, win_lit 19 3 (by omega) r7⟩
      by_cases r8 : 13*D + 13 < 6*k
      · exact ⟨13, by norm_num, U 1 13 (by norm_num) (by norm_num) (by norm_num) n13, by norm_num, by omega, win_lit 13 2 (by omega) r8⟩
      exact ⟨7, by norm_num, U 1 7 (by norm_num) (by norm_num) (by norm_num) n7, by norm_num, by omega, win_lit 7 1 (by omega) (by omega)⟩
    have n5 := h5
    by_cases h7 : 7 ∣ k
    · have n11 : ¬ 11 ∣ k := fun h => no3 3 7 11 (by norm_num) (by norm_num) (by norm_num) h3 h7 h
      have n17 : ¬ 17 ∣ k := fun h => no3 3 7 17 (by norm_num) (by norm_num) (by norm_num) h3 h7 h
      have n19 : ¬ 19 ∣ k := fun h => no3 3 7 19 (by norm_num) (by norm_num) (by norm_num) h3 h7 h
      have n23 : ¬ 23 ∣ k := fun h => no3 3 7 23 (by norm_num) (by norm_num) (by norm_num) h3 h7 h
      by_cases r0 : 11*D + 11 < 2*k
      · exact ⟨11, by norm_num, U 1 11 (by norm_num) (by norm_num) (by norm_num) n11, by norm_num, by omega, win_lit 11 0 (by omega) r0⟩
      by_cases r1 : 19*D + 19 < 4*k
      · exact ⟨19, by norm_num, U 1 19 (by norm_num) (by norm_num) (by norm_num) n19, by norm_num, by omega, win_lit 19 1 (by omega) r1⟩
      by_cases r2 : 17*D + 17 < 4*k
      · exact ⟨17, by norm_num, U 1 17 (by norm_num) (by norm_num) (by norm_num) n17, by norm_num, by omega, win_lit 17 1 (by omega) r2⟩
      by_cases r3 : 5*D + 5 < 2*k
      · exact ⟨5, by norm_num, U 1 5 (by norm_num) (by norm_num) (by norm_num) n5, by norm_num, by omega, win_lit 5 0 (by omega) r3⟩
      by_cases r4 : 19*D + 19 < 8*k
      · exact ⟨19, by norm_num, U 1 19 (by norm_num) (by norm_num) (by norm_num) n19, by norm_num, by omega, win_lit 19 3 (by omega) r4⟩
      by_cases r5 : 23*D + 23 < 10*k
      · exact ⟨23, by norm_num, U 1 23 (by norm_num) (by norm_num) (by norm_num) n23, by norm_num, by omega, win_lit 23 4 (by omega) r5⟩
      by_cases r6 : 17*D + 17 < 8*k
      · exact ⟨17, by norm_num, U 1 17 (by norm_num) (by norm_num) (by norm_num) n17, by norm_num, by omega, win_lit 17 3 (by omega) r6⟩
      exact ⟨11, by norm_num, U 1 11 (by norm_num) (by norm_num) (by norm_num) n11, by norm_num, by omega, win_lit 11 2 (by omega) (by omega)⟩
    have n7 := h7
    by_cases h11 : 11 ∣ k
    · have n13 : ¬ 13 ∣ k := fun h => no3 3 11 13 (by norm_num) (by norm_num) (by norm_num) h3 h11 h
      by_cases r0 : 13*D + 13 < 2*k
      · exact ⟨13, by norm_num, U 1 13 (by norm_num) (by norm_num) (by norm_num) n13, by norm_num, by omega, win_lit 13 0 (by omega) r0⟩
      by_cases r1 : 25*D + 25 < 4*k
      · exact ⟨25, by norm_num, U 2 5 (by norm_num) (by norm_num) (by norm_num) n5, by norm_num, by omega, win_lit 25 1 (by omega) r1⟩
      by_cases r2 : 7*D + 7 < 2*k
      · exact ⟨7, by norm_num, U 1 7 (by norm_num) (by norm_num) (by norm_num) n7, by norm_num, by omega, win_lit 7 0 (by omega) r2⟩
      by_cases r3 : 5*D + 5 < 2*k
      · exact ⟨5, by norm_num, U 1 5 (by norm_num) (by norm_num) (by norm_num) n5, by norm_num, by omega, win_lit 5 0 (by omega) r3⟩
      by_cases r4 : 13*D + 13 < 6*k
      · exact ⟨13, by norm_num, U 1 13 (by norm_num) (by norm_num) (by norm_num) n13, by norm_num, by omega, win_lit 13 2 (by omega) r4⟩
      exact ⟨7, by norm_num, U 1 7 (by norm_num) (by norm_num) (by norm_num) n7, by norm_num, by omega, win_lit 7 1 (by omega) (by omega)⟩
    have n11 := h11
    by_cases h13 : 13 ∣ k
    · have n17 : ¬ 17 ∣ k := fun h => no3 3 13 17 (by norm_num) (by norm_num) (by norm_num) h3 h13 h
      have n19 : ¬ 19 ∣ k := fun h => no3 3 13 19 (by norm_num) (by norm_num) (by norm_num) h3 h13 h
      have n23 : ¬ 23 ∣ k := fun h => no3 3 13 23 (by norm_num) (by norm_num) (by norm_num) h3 h13 h
      by_cases r0 : 11*D + 11 < 2*k
      · exact ⟨11, by norm_num, U 1 11 (by norm_num) (by norm_num) (by norm_num) n11, by norm_num, by omega, win_lit 11 0 (by omega) r0⟩
      by_cases r1 : 19*D + 19 < 4*k
      · exact ⟨19, by norm_num, U 1 19 (by norm_num) (by norm_num) (by norm_num) n19, by norm_num, by omega, win_lit 19 1 (by omega) r1⟩
      by_cases r2 : 17*D + 17 < 4*k
      · exact ⟨17, by norm_num, U 1 17 (by norm_num) (by norm_num) (by norm_num) n17, by norm_num, by omega, win_lit 17 1 (by omega) r2⟩
      by_cases r3 : 5*D + 5 < 2*k
      · exact ⟨5, by norm_num, U 1 5 (by norm_num) (by norm_num) (by norm_num) n5, by norm_num, by omega, win_lit 5 0 (by omega) r3⟩
      by_cases r4 : 19*D + 19 < 8*k
      · exact ⟨19, by norm_num, U 1 19 (by norm_num) (by norm_num) (by norm_num) n19, by norm_num, by omega, win_lit 19 3 (by omega) r4⟩
      by_cases r5 : 23*D + 23 < 10*k
      · exact ⟨23, by norm_num, U 1 23 (by norm_num) (by norm_num) (by norm_num) n23, by norm_num, by omega, win_lit 23 4 (by omega) r5⟩
      by_cases r6 : 17*D + 17 < 8*k
      · exact ⟨17, by norm_num, U 1 17 (by norm_num) (by norm_num) (by norm_num) n17, by norm_num, by omega, win_lit 17 3 (by omega) r6⟩
      exact ⟨11, by norm_num, U 1 11 (by norm_num) (by norm_num) (by norm_num) n11, by norm_num, by omega, win_lit 11 2 (by omega) (by omega)⟩
    have n13 := h13
    by_cases h19 : 19 ∣ k
    · have n29 : ¬ 29 ∣ k := fun h => no3 3 19 29 (by norm_num) (by norm_num) (by norm_num) h3 h19 h
      by_cases r0 : 11*D + 11 < 2*k
      · exact ⟨11, by norm_num, U 1 11 (by norm_num) (by norm_num) (by norm_num) n11, by norm_num, by omega, win_lit 11 0 (by omega) r0⟩
      by_cases r1 : 7*D + 7 < 2*k
      · exact ⟨7, by norm_num, U 1 7 (by norm_num) (by norm_num) (by norm_num) n7, by norm_num, by omega, win_lit 7 0 (by omega) r1⟩
      by_cases r2 : 5*D + 5 < 2*k
      · exact ⟨5, by norm_num, U 1 5 (by norm_num) (by norm_num) (by norm_num) n5, by norm_num, by omega, win_lit 5 0 (by omega) r2⟩
      by_cases r3 : 29*D + 29 < 12*k
      · exact ⟨29, by norm_num, U 1 29 (by norm_num) (by norm_num) (by norm_num) n29, by norm_num, by omega, win_lit 29 5 (by omega) r3⟩
      by_cases r4 : 13*D + 13 < 6*k
      · exact ⟨13, by norm_num, U 1 13 (by norm_num) (by norm_num) (by norm_num) n13, by norm_num, by omega, win_lit 13 2 (by omega) r4⟩
      exact ⟨7, by norm_num, U 1 7 (by norm_num) (by norm_num) (by norm_num) n7, by norm_num, by omega, win_lit 7 1 (by omega) (by omega)⟩
    have n19 := h19
    by_cases r0 : 11*D + 11 < 2*k
    · exact ⟨11, by norm_num, U 1 11 (by norm_num) (by norm_num) (by norm_num) n11, by norm_num, by omega, win_lit 11 0 (by omega) r0⟩
    by_cases r1 : 7*D + 7 < 2*k
    · exact ⟨7, by norm_num, U 1 7 (by norm_num) (by norm_num) (by norm_num) n7, by norm_num, by omega, win_lit 7 0 (by omega) r1⟩
    by_cases r2 : 5*D + 5 < 2*k
    · exact ⟨5, by norm_num, U 1 5 (by norm_num) (by norm_num) (by norm_num) n5, by norm_num, by omega, win_lit 5 0 (by omega) r2⟩
    by_cases r3 : 19*D + 19 < 8*k
    · exact ⟨19, by norm_num, U 1 19 (by norm_num) (by norm_num) (by norm_num) n19, by norm_num, by omega, win_lit 19 3 (by omega) r3⟩
    by_cases r4 : 13*D + 13 < 6*k
    · exact ⟨13, by norm_num, U 1 13 (by norm_num) (by norm_num) (by norm_num) n13, by norm_num, by omega, win_lit 13 2 (by omega) r4⟩
    exact ⟨7, by norm_num, U 1 7 (by norm_num) (by norm_num) (by norm_num) n7, by norm_num, by omega, win_lit 7 1 (by omega) (by omega)⟩
  · have n3 := h3
    by_cases h5 : 5 ∣ k
    · by_cases h7 : 7 ∣ k
      · have n11 : ¬ 11 ∣ k := fun h => no3 5 7 11 (by norm_num) (by norm_num) (by norm_num) h5 h7 h
        have n13 : ¬ 13 ∣ k := fun h => no3 5 7 13 (by norm_num) (by norm_num) (by norm_num) h5 h7 h
        have n17 : ¬ 17 ∣ k := fun h => no3 5 7 17 (by norm_num) (by norm_num) (by norm_num) h5 h7 h
        have n23 : ¬ 23 ∣ k := fun h => no3 5 7 23 (by norm_num) (by norm_num) (by norm_num) h5 h7 h
        by_cases r0 : 9*D + 9 < 2*k
        · exact ⟨9, by norm_num, U 2 3 (by norm_num) (by norm_num) (by norm_num) n3, by norm_num, by omega, win_lit 9 0 (by omega) r0⟩
        by_cases r1 : 17*D + 17 < 4*k
        · exact ⟨17, by norm_num, U 1 17 (by norm_num) (by norm_num) (by norm_num) n17, by norm_num, by omega, win_lit 17 1 (by omega) r1⟩
        by_cases r2 : 23*D + 23 < 6*k
        · exact ⟨23, by norm_num, U 1 23 (by norm_num) (by norm_num) (by norm_num) n23, by norm_num, by omega, win_lit 23 2 (by omega) r2⟩
        by_cases r3 : 13*D + 13 < 4*k
        · exact ⟨13, by norm_num, U 1 13 (by norm_num) (by norm_num) (by norm_num) n13, by norm_num, by omega, win_lit 13 1 (by omega) r3⟩
        by_cases r4 : 11*D + 11 < 4*k
        · exact ⟨11, by norm_num, U 1 11 (by norm_num) (by norm_num) (by norm_num) n11, by norm_num, by omega, win_lit 11 1 (by omega) r4⟩
        exact ⟨3, by norm_num, U 1 3 (by norm_num) (by norm_num) (by norm_num) n3, by norm_num, by omega, win_lit 3 0 (by omega) (by omega)⟩
      have n7 := h7
      by_cases h11 : 11 ∣ k
      · have n7 : ¬ 7 ∣ k := fun h => no3 5 11 7 (by norm_num) (by norm_num) (by norm_num) h5 h11 h
        have n17 : ¬ 17 ∣ k := fun h => no3 5 11 17 (by norm_num) (by norm_num) (by norm_num) h5 h11 h
        have n19 : ¬ 19 ∣ k := fun h => no3 5 11 19 (by norm_num) (by norm_num) (by norm_num) h5 h11 h
        by_cases r0 : 9*D + 9 < 2*k
        · exact ⟨9, by norm_num, U 2 3 (by norm_num) (by norm_num) (by norm_num) n3, by norm_num, by omega, win_lit 9 0 (by omega) r0⟩
        by_cases r1 : 7*D + 7 < 2*k
        · exact ⟨7, by norm_num, U 1 7 (by norm_num) (by norm_num) (by norm_num) n7, by norm_num, by omega, win_lit 7 0 (by omega) r1⟩
        by_cases r2 : 19*D + 19 < 6*k
        · exact ⟨19, by norm_num, U 1 19 (by norm_num) (by norm_num) (by norm_num) n19, by norm_num, by omega, win_lit 19 2 (by omega) r2⟩
        by_cases r3 : 17*D + 17 < 6*k
        · exact ⟨17, by norm_num, U 1 17 (by norm_num) (by norm_num) (by norm_num) n17, by norm_num, by omega, win_lit 17 2 (by omega) r3⟩
        exact ⟨3, by norm_num, U 1 3 (by norm_num) (by norm_num) (by norm_num) n3, by norm_num, by omega, win_lit 3 0 (by omega) (by omega)⟩
      have n11 := h11
      by_cases r0 : 9*D + 9 < 2*k
      · exact ⟨9, by norm_num, U 2 3 (by norm_num) (by norm_num) (by norm_num) n3, by norm_num, by omega, win_lit 9 0 (by omega) r0⟩
      by_cases r1 : 7*D + 7 < 2*k
      · exact ⟨7, by norm_num, U 1 7 (by norm_num) (by norm_num) (by norm_num) n7, by norm_num, by omega, win_lit 7 0 (by omega) r1⟩
      by_cases r2 : 27*D + 27 < 8*k
      · exact ⟨27, by norm_num, U 3 3 (by norm_num) (by norm_num) (by norm_num) n3, by norm_num, by omega, win_lit 27 3 (by omega) r2⟩
      by_cases r3 : 11*D + 11 < 4*k
      · exact ⟨11, by norm_num, U 1 11 (by norm_num) (by norm_num) (by norm_num) n11, by norm_num, by omega, win_lit 11 1 (by omega) r3⟩
      exact ⟨3, by norm_num, U 1 3 (by norm_num) (by norm_num) (by norm_num) n3, by norm_num, by omega, win_lit 3 0 (by omega) (by omega)⟩
    have n5 := h5
    by_cases r0 : 9*D + 9 < 2*k
    · exact ⟨9, by norm_num, U 2 3 (by norm_num) (by norm_num) (by norm_num) n3, by norm_num, by omega, win_lit 9 0 (by omega) r0⟩
    by_cases r1 : 5*D + 5 < 2*k
    · exact ⟨5, by norm_num, U 1 5 (by norm_num) (by norm_num) (by norm_num) n5, by norm_num, by omega, win_lit 5 0 (by omega) r1⟩
    exact ⟨3, by norm_num, U 1 3 (by norm_num) (by norm_num) (by norm_num) n3, by norm_num, by omega, win_lit 3 0 (by omega) (by omega)⟩


/-- **The pair `(1, D)`** for every even residue `D` outside `{0, ±2, k, k ± 2}`. -/
theorem goodM {k : ℕ} (hk : 92 ≤ k) (he : k % 2 = 0) (hP : TwoPrime k)
    {D : ℕ} (hD : D < 2*k) (hDe : D % 2 = 0)
    (h0 : D ≠ 0) (h2 : D ≠ 2) (h3 : D ≠ k - 2) (h4 : D ≠ k) (h5 : D ≠ k + 2)
    (h6 : D ≠ 2*k - 2) : Good k 1 D := by
  have half : ∀ D' : ℕ, 4 ≤ D' → 2*D' ≤ k →
      ∃ m : ℕ, m % 2 = 1 ∧ Nat.Coprime m (2*k) ∧ 0 < m ∧ m < k ∧ Win k m D' := by
    intro D' h4' h2'
    by_cases hs : 8*D' ≤ k
    · exact win_I3 hk hP h4' hs
    · exact win_chain hk he hP (by omega) h2'
  rcases Nat.lt_or_ge k D with hkD | hkD
  · -- `k < D < 2k`: `m = 1`
    refine good_of_win (m := 1) (by simp) one_pos (by omega) ⟨0, ?_, ?_⟩ <;> push_cast <;> omega
  by_cases hD2 : 2*D ≤ k
  · obtain ⟨m, hmo, hmu, hm0, hmk, hw⟩ := half D (by omega) hD2
    exact good_of_win (int_gcd_of_coprime hmu) (by exact_mod_cast hm0) (by exact_mod_cast hmk) hw
  · obtain ⟨m, hmo, hmu, hm0, hmk, hw⟩ := half (k - D) (by omega) (by omega)
    refine good_of_win (int_gcd_of_coprime hmu) (by exact_mod_cast hm0) (by exact_mod_cast hmk)
      (win_mirror (by exact_mod_cast hmo) ?_)
    have e : ((k - D : ℕ) : ℤ) = (k:ℤ) - D := by push_cast [Nat.cast_sub (by omega : D ≤ k)]; ring
    rw [← e]; exact hw

/-! ## Non-unit `a`: the pair `(A, A − 1)` -/

/-- A unit `0 < ν < k` with `νA ≡ r ∈ [0, k)` and `2r − ν` in the upper half modulo `2k` is a
witness for `(A, A − 1)`: `H(ν) = H(νA) = 1 ≠ H(ν(2A − 1))`. -/
theorem good_vert {k : ℕ} {A ν r : ℤ} (hν : Int.gcd ν (2*k) = 1) (h0 : 0 < ν) (h1 : ν < k)
    (hr : (ν*A) % (2*k) = r) (hr0 : 0 ≤ r) (hrk : r < k)
    (h3 : (2*r - ν < 0 ∧ k ≤ 2*r - ν + 2*k) ∨ (k ≤ 2*r - ν ∧ 2*r - ν < 2*k)) :
    Good k A (A - 1) := by
  have hk : (0:ℤ) < 2*k := by omega
  have hq := Int.emod_add_mul_ediv (ν*A) (2*k)
  rw [hr] at hq
  refine ⟨ν, hν, ?_, ?_⟩
  · have e : ν*(A - (A-1)) = ν := by ring
    rw [e, hr, Int.emod_eq_of_lt h0.le (by omega)]
    constructor <;> intro _ <;> omega
  · have e : ν*(A + (A-1)) = (2*r - ν) + 2*k*(2*(ν*A/(2*k))) := by
      rw [show ν*(A + (A-1)) = 2*(ν*A) - ν by ring]; linarith
    rw [e, Int.add_mul_emod_self_left, hr]
    rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rw [show 2*r - ν = (2*r - ν + 2*k) + 2*k*(-1) by ring, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by omega) (by omega)]
      constructor
      · intro h; omega
      · intro h; exact absurd hrk (by omega)
    · rw [Int.emod_eq_of_lt (by omega) h4]
      constructor
      · intro h; omega
      · intro h; exact absurd hrk (by omega)

/-- `q − s` is prime to `2q` when `q` is even, `s` odd, and no odd prime of `s` divides `q`. -/
lemma cop_sub {q s : ℕ} (hs : s < q) (hqe : q % 2 = 0) (hso : s % 2 = 1)
    (h : ∀ r : ℕ, r.Prime → r ∣ s → ¬ r ∣ q) : Nat.Coprime (q - s) (2*q) := by
  apply Nat.coprime_of_dvd
  intro r hr h1 h2
  have hr2 : r ≠ 2 := by
    rintro rfl
    have := Nat.mod_eq_zero_of_dvd h1; omega
  have hrq : r ∣ q := (Nat.Coprime.dvd_mul_left
    ((Nat.coprime_primes hr Nat.prime_two).2 hr2)).1 h2
  have hrs : r ∣ s := by
    have := Nat.dvd_sub hrq h1
    rwa [Nat.sub_sub_self hs.le] at this
  exact h r hr hrs hrq

set_option maxHeartbeats 2000000 in
/-- **The pair `(A, A − 1)`** with `f = gcd(A, 2k) > 1`, `2f < k`. -/
theorem goodF {k : ℕ} (hk : 92 ≤ k) (he : k % 2 = 0) (hP : TwoPrime k) {A : ℕ}
    (hAo : A % 2 = 1) (hf1 : 1 < Nat.gcd A (2*k)) (hf2 : 2 * Nat.gcd A (2*k) < k) :
    Good k A ((A:ℤ) - 1) := by
  set f := Nat.gcd A (2*k) with hfdef
  have hfA : f ∣ A := Nat.gcd_dvd_left _ _
  have hf2k : f ∣ 2*k := Nat.gcd_dvd_right _ _
  have hfo : f % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one f with h | h
    · have := (Nat.dvd_of_mod_eq_zero h).trans hfA; omega
    · exact h
  have hfk : f ∣ k :=
    (Nat.Coprime.dvd_mul_left (Nat.coprime_two_right.2 (Nat.odd_iff.2 hfo))).1 hf2k
  obtain ⟨q, hq⟩ := hfk
  have hqe : q % 2 = 0 := by
    have hk2 : Even k := Nat.even_iff.2 he
    rw [hq, Nat.even_mul] at hk2
    rcases hk2 with h | h
    · exact absurd (Nat.even_iff.1 h) (by omega)
    · exact Nat.even_iff.1 h
  have hq4 : 4 ≤ q := by
    by_contra h
    have : q ≤ 2 := by omega
    have : f*q ≤ f*2 := Nat.mul_le_mul_left _ this
    omega
  set M := 2*q with hM
  have h2k : 2*k = f*M := by rw [hq, hM]; ring
  obtain ⟨w, hw⟩ := hfA
  have hf0 : 0 < f := by omega
  have hwM : Nat.Coprime w M := by
    have := Nat.coprime_div_gcd_div_gcd (m := A) (n := 2*k) (by omega)
    rw [← hfdef, hw, Nat.mul_div_cancel_left _ hf0, h2k, Nat.mul_div_cancel_left _ hf0] at this
    exact this
  clear_value f
  obtain ⟨ν₀, hν₀M, hν₀⟩ := Nat.exists_mul_mod_eq_one_of_coprime hwM (by omega)
  -- the multiplier condition
  have lift_mul : ∀ ν c : ℕ, ν % M = (c*ν₀) % M → (ν*A) % (2*k) = (f*c) % (2*k) := by
    intro ν c h
    have h1 : (ν*w) % M = c % M := by
      rw [Nat.mul_mod, h, ← Nat.mul_mod, show c*ν₀*w = c*(w*ν₀) by ring, Nat.mul_mod, hν₀,
        mul_one, Nat.mod_mod]
    rw [h2k, hw, show ν*(f*w) = f*(ν*w) by ring, Nat.mul_mod_mul_left, h1,
      ← Nat.mul_mod_mul_left]
  have copM : ∀ ν : ℕ, ν % M = ν₀ % M → Nat.Coprime ν M := by
    intro ν h
    have g1 : Nat.gcd ν₀ M = 1 := by
      have hd : Nat.gcd ν₀ M ∣ w*ν₀ % M :=
        (Nat.dvd_mod_iff (Nat.gcd_dvd_right _ _)).2 (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) w)
      rw [hν₀] at hd; exact Nat.dvd_one.1 hd
    unfold Nat.Coprime
    rw [Nat.gcd_comm, Nat.gcd_rec, h, ← Nat.gcd_rec, Nat.gcd_comm]; exact g1
  have oddM : ∀ ν : ℕ, Nat.Coprime ν M → ν % 2 = 1 := by
    intro ν h
    rcases Nat.mod_two_eq_zero_or_one ν with h0 | h0
    · have : 2 ∣ Nat.gcd ν M := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h0) ⟨q, rfl⟩
      rw [h] at this; omega
    · exact h0
  -- a lift of `ν₀` in `(L, L + M]`
  have lift : ∀ L : ℕ, ∃ ν, ν % M = ν₀ % M ∧ L < ν ∧ ν ≤ L + M := by
    intro L
    refine ⟨ν₀ + M*((L + M - ν₀)/M), by rw [Nat.add_mul_mod_self_left], ?_, ?_⟩
    · have := Nat.lt_div_mul_add (a := L + M - ν₀) (b := M) (by omega)
      have e : (L + M - ν₀)/M*M = M*((L + M - ν₀)/M) := by ring
      omega
    · have := Nat.div_mul_le_self (L + M - ν₀) M
      have e : (L + M - ν₀)/M*M = M*((L + M - ν₀)/M) := by ring
      omega
  -- the witness, from `ν` and `c`
  have fin : ∀ ν c : ℕ, Nat.Coprime ν (2*k) → 0 < ν → ν < k → ν % M = (c*ν₀) % M →
      f*c < k → ((2*(f*c) < ν ∧ ν ≤ k + 2*(f*c)) ∨ (ν + k ≤ 2*(f*c) ∧ 2*(f*c) < ν + 2*k)) →
      Good k A ((A:ℤ) - 1) := by
    intro ν c hu h0 hνk hνM hc hcond
    have hr := lift_mul ν c hνM
    rw [Nat.mod_eq_of_lt (by omega : f*c < 2*k)] at hr
    refine good_vert (ν := ν) (r := ((f*c : ℕ) : ℤ)) (int_gcd_of_coprime hu) (by exact_mod_cast h0)
      (by exact_mod_cast hνk) (by exact_mod_cast hr) (by positivity) (by exact_mod_cast hc) ?_
    push_cast
    rcases hcond with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; constructor <;> push_cast at h1 h2 ⊢ <;> omega
    · right; constructor <;> omega
  have hk0 : 0 < k := by omega
  have hc1 : ∀ ν', ν' % M = ν₀ % M → ν' % M = (1*ν₀) % M := by intro ν' h; rw [one_mul]; exact h
  -- a non-unit lift has a prime factor dividing `f`
  have nonunit : ∀ ν : ℕ, Nat.Coprime ν M → ν % 2 = 1 → ¬ Nat.Coprime ν (2*k) →
      ∃ r, r.Prime ∧ r ∣ ν ∧ r ∣ f := by
    intro ν hνM hνo hnu
    obtain ⟨r, hr, -, hrν, hrk⟩ := exists_prime_of_gcd hνo (one_lt_gcd_of_not_coprime hνo hnu)
    refine ⟨r, hr, hrν, ?_⟩
    rw [hq] at hrk
    rcases (Nat.Prime.dvd_mul hr).1 hrk with h | h
    · exact h
    · exfalso
      have : r ∣ Nat.gcd ν M := Nat.dvd_gcd hrν (h.trans ⟨2, by rw [hM]; ring⟩)
      rw [hνM] at this; exact hr.one_lt.ne' (Nat.dvd_one.1 this)
  by_cases hf15 : 15 ≤ f
  · -- three consecutive lifts in `(2f, k)`, one of them a unit
    have hroom : 2*f + 3*M ≤ k := by
      rw [hq, hM]; zify at hf15 hq4 ⊢; nlinarith [mul_nonneg (sub_nonneg.2 hf15) (sub_nonneg.2 hq4)]
    obtain ⟨ν, hν, hν1, hν2⟩ := lift (2*f)
    have hc0 := copM ν hν
    have hνo := oddM ν hc0
    have hM1 : (ν + M) % M = ν₀ % M := by rw [Nat.add_mod_right, hν]
    have hM2 : (ν + 2*M) % M = ν₀ % M := by rw [Nat.add_mul_mod_self_right, hν]
    have ho1 := oddM _ (copM _ hM1)
    have ho2 := oddM _ (copM _ hM2)
    have c12 : Nat.gcd (Nat.gcd ν (ν + M)) k = 1 := by
      rw [gcd_shift, hc0, Nat.gcd_one_left]
    have c13 : Nat.gcd (Nat.gcd ν (ν + 2*M)) k = 1 := by
      rw [gcd_shift, Nat.Coprime.mul_right (Nat.coprime_two_right.2 (Nat.odd_iff.2 hνo)) hc0,
        Nat.gcd_one_left]
    have c23 : Nat.gcd (Nat.gcd (ν + M) (ν + 2*M)) k = 1 := by
      rw [show ν + 2*M = (ν + M) + M by ring, gcd_shift, copM _ hM1, Nat.gcd_one_left]
    rcases hP.unit3 hνo ho1 ho2 c12 c13 c23 with hu | hu | hu
    · exact fin ν 1 hu (by omega) (by omega) (hc1 ν hν) (by omega) (Or.inl ⟨by omega, by omega⟩)
    · exact fin _ 1 hu (by omega) (by omega) (hc1 _ hM1) (by omega) (Or.inl ⟨by omega, by omega⟩)
    · exact fin _ 1 hu (by omega) (by omega) (hc1 _ hM2) (by omega) (Or.inl ⟨by omega, by omega⟩)
  by_cases hf5 : 5 ≤ f
  · -- `f ∈ {5, 7, 9, 11, 13}` is a prime power: two lifts in `(2f, k)`
    have hroom : 2*f + 2*M ≤ k := by
      rw [hq, hM]
      rcases (show f = 5 ∨ f = 7 ∨ 9 ≤ f by omega) with h | h | h
      · subst h; omega
      · subst h; omega
      · zify at h hq4 ⊢; nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hq4)]
    obtain ⟨ℓ, hℓf⟩ : ∃ ℓ, ∀ r, r.Prime → r ∣ f → r = ℓ := by
      have pp : ∀ p : ℕ, p.Prime → ∀ r : ℕ, r.Prime → r ∣ p → r = p :=
        fun p hp r hr hd => (Nat.prime_dvd_prime_iff_eq hr hp).1 hd
      rcases (show f = 5 ∨ f = 7 ∨ f = 9 ∨ f = 11 ∨ f = 13 by omega) with h | h | h | h | h <;>
        rw [h]
      · exact ⟨5, pp 5 (by norm_num)⟩
      · exact ⟨7, pp 7 (by norm_num)⟩
      · exact ⟨3, fun r hr hd => pp 3 (by norm_num) r hr
          (hr.dvd_of_dvd_pow (show r ∣ 3^2 by norm_num; exact hd))⟩
      · exact ⟨11, pp 11 (by norm_num)⟩
      · exact ⟨13, pp 13 (by norm_num)⟩
    obtain ⟨ν, hν, hν1, hν2⟩ := lift (2*f)
    have hc0 := copM ν hν
    have hνo := oddM ν hc0
    have hM1 : (ν + M) % M = ν₀ % M := by rw [Nat.add_mod_right, hν]
    have ho1 := oddM _ (copM _ hM1)
    by_cases hu : Nat.Coprime ν (2*k)
    · exact fin ν 1 hu (by omega) (by omega) (hc1 ν hν) (by omega) (Or.inl ⟨by omega, by omega⟩)
    by_cases hu' : Nat.Coprime (ν + M) (2*k)
    · exact fin _ 1 hu' (by omega) (by omega) (hc1 _ hM1) (by omega) (Or.inl ⟨by omega, by omega⟩)
    exfalso
    obtain ⟨r, hr, hrν, hrf⟩ := nonunit ν hc0 hνo hu
    obtain ⟨r', hr', hrν', hrf'⟩ := nonunit _ (copM _ hM1) ho1 hu'
    have e1 := hℓf r hr hrf
    have e2 := hℓf r' hr' hrf'
    rw [e1] at hrν hr
    rw [e2] at hrν'
    have hrM : ℓ ∣ M := by
      have := Nat.dvd_sub hrν' hrν
      rwa [Nat.add_sub_cancel_left] at this
    have : ℓ ∣ Nat.gcd ν M := Nat.dvd_gcd hrν hrM
    rw [hc0] at this; exact hr.one_lt.ne' (Nat.dvd_one.1 this)
  have hf3 : f = 3 := by omega
  subst hf3
  have hq32 : 32 ≤ q := by omega
  by_cases h3M : 3 ∣ M
  · -- one lift in `(6, k)`, prime to `3`
    obtain ⟨ν, hν, hν1, hν2⟩ := lift 6
    have hνo := oddM ν (copM ν hν)
    have hu : Nat.Coprime ν (2*k) := by
      rw [h2k]
      exact Nat.Coprime.mul_right ((copM ν hν).coprime_dvd_right h3M) (copM ν hν)
    exact fin ν 1 hu (by omega) (by omega) (by rw [one_mul]; exact hν) (by omega)
      (Or.inl ⟨by omega, by omega⟩)
  -- `3 ∥ k`: a number prime to `3` and to `M` is a unit
  have unit3' : ∀ n : ℕ, Nat.Coprime n M → ¬ 3 ∣ n → Nat.Coprime n (2*k) := by
    intro n hnM h3n
    rw [h2k]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h3n).symm hnM
  have h3q : ¬ 3 ∣ q := fun h => h3M (Dvd.dvd.mul_left h 2)
  have hν₀c := copM ν₀ rfl
  have hν₀o := oddM ν₀ hν₀c
  have hν₀1 : ν₀ % M = (1*ν₀) % M := by rw [one_mul]
  have hpk : (ν₀ + M) % M = ν₀ % M := Nat.add_mod_right _ _
  have h3k : 3 ∣ k := ⟨q, hq⟩
  have hqM : ∀ r, r ∣ q → r ∣ M := fun r h => h.trans ⟨2, by rw [hM]; ring⟩
  rcases (show ν₀ < 6 ∨ (6 < ν₀ ∧ ν₀ < q) ∨ q < ν₀ by omega) with hs | ⟨hs1, hs2⟩ | hs
  · -- `ν₀ ∈ {1, 3, 5}`: the lift `ν₀ + M`, or `c = q − 5`, or `c = q − 11` if `5 ∣ k`
    by_cases h3 : 3 ∣ ν₀ + M
    · have hν₀15 : ν₀ = 1 ∨ ν₀ = 5 := by omega
      by_cases h5k : 5 ∣ k
      · have h5q : 5 ∣ q := (Nat.Coprime.dvd_mul_left (by norm_num)).1 (hq ▸ h5k)
        have hν₀1' : ν₀ = 1 := by
          rcases hν₀15 with h | h
          · exact h
          · exfalso
            have : 5 ∣ Nat.gcd ν₀ M := Nat.dvd_gcd ⟨1, by omega⟩ (hqM 5 h5q)
            rw [hν₀c] at this; omega
        have n11 : ¬ 11 ∣ k := fun h => hP.no3 3 5 11 (by norm_num) (by norm_num) (by norm_num)
          h3k h5k h
        have hcop : Nat.Coprime (q - 11) M := cop_sub (by omega) hqe (by norm_num)
          (fun r hr hrs hrq => by
            have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 hrs
            subst this; exact n11 (hq ▸ Dvd.dvd.mul_left hrq 3))
        refine fin (q - 11) (q - 11) (unit3' _ hcop (by omega)) (by omega) (by omega) ?_ (by omega)
          (Or.inr ⟨by omega, by omega⟩)
        rw [hν₀1', mul_one]
      · have n5q : ∀ r : ℕ, r.Prime → r ∣ 5 → ¬ r ∣ q := fun r hr hrs hrq => by
          have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 hrs
          subst this; exact h5k (hq ▸ Dvd.dvd.mul_left hrq 3)
        rcases hν₀15 with h1 | h5
        · refine fin (q - 5) (q - 5) (unit3' _ (cop_sub (by omega) hqe (by norm_num) n5q)
            (by omega)) (by omega) (by omega) ?_ (by omega) (Or.inr ⟨by omega, by omega⟩)
          rw [h1, mul_one]
        · have hcop : Nat.Coprime (q - 25) M := cop_sub (by omega) hqe (by norm_num)
            (fun r hr hrs hrq => n5q r hr
              (hr.dvd_of_dvd_pow (show r ∣ 5^2 by norm_num; exact hrs)) hrq)
          have n3 : ¬ 3 ∣ q - 25 := by omega
          have hu := unit3' _ hcop n3
          have hc : 3*(q - 5) < k := by omega
          refine fin (q - 25) (q - 5) hu (by omega) (by omega) ?_ hc
            (Or.inr ⟨by omega, by omega⟩)
          rw [h5, show (q - 5)*5 = (q - 25) + M*2 by omega, Nat.add_mul_mod_self_left]
    · exact fin (ν₀ + M) 1 (unit3' _ (copM _ hpk) h3) (by omega) (by omega) (hc1 _ hpk)
        (by omega) (Or.inl ⟨by omega, by omega⟩)
  · -- `6 < ν₀ < q`: the lifts `ν₀` and `ν₀ + M`
    by_cases h3 : 3 ∣ ν₀
    · exact fin (ν₀ + M) 1 (unit3' _ (copM _ hpk) (by omega)) (by omega) (by omega) (hc1 _ hpk)
        (by omega) (Or.inl ⟨by omega, by omega⟩)
    · exact fin ν₀ 1 (unit3' _ hν₀c h3) (by omega) (by omega) hν₀1 (by omega)
        (Or.inl ⟨by omega, by omega⟩)
  · -- `q < ν₀`: `ν₀` itself, or `c = q − 3`
    by_cases h3 : 3 ∣ ν₀
    · set ν := ((q - 3)*ν₀) % M with hνdef
      have hνM : ν % M = ((q - 3)*ν₀) % M := Nat.mod_mod _ _
      have hcopν : Nat.Coprime ν M := by
        have hc3 : Nat.Coprime (q - 3) M := cop_sub (by omega) hqe (by norm_num)
          (fun r hr hrs hrq => by
            have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 hrs
            subst this; exact h3q hrq)
        have := Nat.Coprime.mul_left hc3 hν₀c
        unfold Nat.Coprime at this ⊢
        rw [hνdef, ← Nat.gcd_rec, Nat.gcd_comm]; exact this
      -- `ν = 5q − 3ν₀` or `7q − 3ν₀`
      have hdiv := Nat.div_add_mod ((q - 3)*ν₀) M
      rw [← hνdef] at hdiv
      have hνlt : ν < M := Nat.mod_lt _ (by omega)
      obtain ⟨s, hs'⟩ : ∃ s, ν₀ = 2*s + 1 := ⟨ν₀ / 2, by omega⟩
      set t := (q - 3)*ν₀ / M
      have key : 2*(q*t) + ν + 3*ν₀ = 2*(q*s) + q := by
        have e1 : (q - 3)*ν₀ + 3*ν₀ = q*ν₀ := by
          rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
        have e2 : q*ν₀ = 2*(q*s) + q := by rw [hs']; ring
        have e3 : M*t = 2*(q*t) := by rw [hM]; ring
        omega
      have hj : (q*s = q*t + 2*q) ∨ (q*s = q*t + 3*q) := by
        have hst1 : t + 2 ≤ s := by
          by_contra h
          have : q*s ≤ q*(t+1) := Nat.mul_le_mul_left _ (by omega)
          have e : q*(t+1) = q*t + q := by ring
          omega
        have hst2 : s ≤ t + 3 := by
          by_contra h
          have : q*(t+4) ≤ q*s := Nat.mul_le_mul_left _ (by omega)
          have e : q*(t+4) = q*t + 4*q := by ring
          omega
        rcases (show s = t + 2 ∨ s = t + 3 by omega) with h | h
        · left; rw [h]; ring
        · right; rw [h]; ring
      have hν3 : ¬ 3 ∣ ν := by omega
      exact fin ν (q - 3) (unit3' ν hcopν hν3) (by omega) (by omega) hνM (by omega)
        (Or.inr ⟨by omega, by omega⟩)
    · exact fin ν₀ 1 (unit3' _ hν₀c h3) (by omega) (by omega) hν₀1 (by omega)
        (Or.inl ⟨by omega, by omega⟩)

/-! ## The last term a unit -/

/-- Adding `k` flips the half, for odd `ν`. -/
lemma flip_k {k : ℕ} {ν x : ℤ} (hν : ν % 2 = 1) (hk : 0 < k) :
    (ν*(x + k)) % (2*k) < k ↔ ¬ (ν*x) % (2*k) < k := by
  obtain ⟨t, rfl⟩ : ∃ t, ν = 2*t + 1 := ⟨ν / 2, by omega⟩
  have hk2 : (0:ℤ) < 2*k := by omega
  have e : (2*t+1)*(x + k) = ((2*t+1)*x % (2*k) + k) + 2*k*(t + (2*t+1)*x / (2*k)) := by
    have := Int.emod_add_mul_ediv ((2*t+1)*x) (2*k)
    linear_combination (-1 : ℤ) * this
  rw [e, Int.add_mul_emod_self_left]
  have h0 := Int.emod_nonneg ((2*t+1)*x) hk2.ne'
  have h1 := Int.emod_lt_of_pos ((2*t+1)*x) hk2
  rcases lt_or_ge ((2*t+1)*x % (2*k)) k with h | h
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]; constructor <;> intro _ <;> omega
  · rw [show (2*t+1)*x % (2*k) + k = ((2*t+1)*x % (2*k) - k) + 2*k*1 by ring,
      Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    constructor <;> intro _ <;> omega

/-- The pair `(B, 1 − B)` (last term `1`) has the witnesses of `(B + k, B + k − 1)`. -/
theorem good_shift {k : ℕ} {B : ℤ} (hk : 0 < k) (h : Good k (B + k) (B + k - 1)) :
    Good k B (1 - B) := by
  obtain ⟨ν, hν, h1, h2⟩ := h
  have hνo : ν % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one ν with h0 | h0
    · exfalso
      have h2ν : (2:ℤ) ∣ ν := Int.dvd_of_emod_eq_zero h0
      have : (2:ℤ) ∣ ((Int.gcd ν (2*k) : ℕ) : ℤ) := Int.dvd_coe_gcd h2ν ⟨k, rfl⟩
      rw [hν] at this; norm_num at this
    · exact h0
  have hf := flip_k (k := k) (x := B) hνo hk
  refine ⟨ν, hν, ?_, ?_⟩
  · rw [show ν*(B - (1-B)) = ν*(B + k + (B + k - 1)) + 2*k*(-ν) by ring,
      Int.add_mul_emod_self_left, h2, hf, not_not]
  · rw [show ν*(B + (1-B)) = ν*(B + k - (B + k - 1)) by ring, h1, hf]

/-- `gcd(n + k, 2k) = gcd(n, 2k)` for odd `n` and even `k`. -/
lemma gcd_add_k {n k : ℕ} (hn : n % 2 = 1) (hk : k % 2 = 0) :
    Nat.gcd (n + k) (2*k) = Nat.gcd n (2*k) := by
  have odd2 : ∀ m, m % 2 = 1 → Nat.gcd m (2*k) = Nat.gcd m k := fun m hm => by
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul_left_cancel k
      (Nat.coprime_two_left.2 (Nat.odd_iff.2 hm)), Nat.gcd_comm]
  rw [odd2 _ (by omega), odd2 _ hn, Nat.gcd_add_self_left]

lemma mod_val {k x r t : ℕ} (h : x = r + 2*k*t) (hr : r < 2*k) : x % (2*k) = r := by
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

lemma int_modEq_of_nat {k x y : ℕ} (h : x % (2*k) = y % (2*k)) :
    (x:ℤ) ≡ (y:ℤ) [ZMOD 2*k] := by
  unfold Int.ModEq
  have := congrArg (fun n : ℕ => (n:ℤ)) h
  push_cast at this
  exact this

/-- The six excluded residues do not occur: `a·D ≡ e` with `(a, e)` admissible. -/
lemma exceptions {k a e D : ℕ} (hao : a % 2 = 1) (hae : (a*D) % (2*k) = e) (hlt : 2*(a+e) < k)
    (he0 : 0 < e) (hne : e ≠ 2*a) :
    D ≠ 0 ∧ D ≠ 2 ∧ D ≠ k - 2 ∧ D ≠ k ∧ D ≠ k + 2 ∧ D ≠ 2*k - 2 := by
  obtain ⟨s, rfl⟩ : ∃ s, a = 2*s + 1 := ⟨a / 2, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hD <;> rw [hD] at hae
  · simp at hae; omega
  · rw [Nat.mod_eq_of_lt (by omega)] at hae; omega
  · have e1 : (2*s+1)*(k-2) = (k - 2*(2*s+1)) + 2*k*s := by
      zify [show 2 ≤ k by omega, show 2*(2*s+1) ≤ k by omega]; ring
    rw [mod_val e1 (by omega)] at hae; omega
  · rw [mod_val (r := k) (t := s) (by ring) (by omega)] at hae; omega
  · rw [mod_val (r := k + 2*(2*s+1)) (t := s) (by ring) (by omega)] at hae; omega
  · have e1 : (2*s+1)*(2*k-2) = (2*k - 2*(2*s+1)) + 2*k*(2*s) := by
      zify [show 2 ≤ 2*k by omega, show 2*(2*s+1) ≤ 2*k by omega]; ring
    rw [mod_val e1 (by omega)] at hae; omega

/-- **`prop:lemmaA-twoprime`.**  At an even order `k ≥ 92` with at most two odd prime factors,
every admissible pair has a witness. -/
theorem good_twoPrime {k : ℕ} (hk : 92 ≤ k) (hP : TwoPrime k) {a e : ℤ} (h : Adm k a e) :
    Good k a e := by
  have he : k % 2 = 0 := by have := h.k_even; omega
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le h.a_pos.le
  obtain ⟨e, rfl⟩ := Int.eq_ofNat_of_zero_le h.e_pos.le
  have ha0 : 0 < a := by exact_mod_cast h.a_pos
  have he0 : 0 < e := by exact_mod_cast h.e_pos
  have hlt : 2*(a+e) < k := by have := h.lt_half; omega
  have hao : a % 2 = 1 := by have := h.a_odd; omega
  have hee : e % 2 = 0 := by have := h.e_even; omega
  have hne : e ≠ 2*a := by have := h.ne3; omega
  have hcop : Nat.gcd (Nat.gcd a e) (2*k) = 1 := by
    have := h.cop
    have e1 : (2*(k:ℤ)) = ((2*k:ℕ):ℤ) := by push_cast; ring
    rw [e1, Int.gcd_natCast_natCast, Int.gcd_natCast_natCast] at this
    exact this
  have hk1 : 1 < 2*k := by omega
  have inv_cop : ∀ v ε : ℕ, v * ε % (2*k) = 1 → Nat.Coprime ε (2*k) := by
    intro v ε hε
    have hd : Nat.gcd ε (2*k) ∣ v*ε % (2*k) :=
      (Nat.dvd_mod_iff (Nat.gcd_dvd_right _ _)).2 (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) v)
    rw [hε] at hd; exact Nat.dvd_one.1 hd
  have odd_of_cop : ∀ ε : ℕ, Nat.Coprime ε (2*k) → ε % 2 = 1 := by
    intro ε hεc
    rcases Nat.mod_two_eq_zero_or_one ε with h0 | h0
    · have : 2 ∣ Nat.gcd ε (2*k) := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h0) ⟨k, rfl⟩
      rw [hεc] at this; omega
    · exact h0
  -- one of `u = a − e`, `a`, `u' = a + e` is a unit
  set u := a + 2*k - e with hudef
  set u' := a + e with hu'def
  have huo : u % 2 = 1 := by omega
  have hu'o : u' % 2 = 1 := by omega
  have hcom : ∀ g, g ∣ a → g ∣ e → g ∣ k → g = 1 := fun g h1 h2 h3 =>
    Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd (Nat.dvd_gcd h1 h2) (Dvd.dvd.mul_left h3 2))
  have c12 : Nat.gcd (Nat.gcd u a) k = 1 := by
    set g := Nat.gcd (Nat.gcd u a) k
    have h1 : g ∣ u := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have h2 : g ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have h3 : g ∣ k := Nat.gcd_dvd_right _ _
    have h4 : g ∣ e := by
      have := Nat.dvd_sub (Nat.dvd_add h2 (Dvd.dvd.mul_left h3 2)) h1
      rwa [hudef, Nat.sub_sub_self (by omega)] at this
    exact hcom g h2 h4 h3
  have c13 : Nat.gcd (Nat.gcd u u') k = 1 := by
    set g := Nat.gcd (Nat.gcd u u') k
    have h1 : g ∣ u := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have h2 : g ∣ u' := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have h3 : g ∣ k := Nat.gcd_dvd_right _ _
    have hgo : Nat.Coprime g 2 := by
      rcases Nat.mod_two_eq_zero_or_one g with h0 | h0
      · have := (Nat.dvd_of_mod_eq_zero h0).trans h2; omega
      · exact Nat.coprime_two_right.2 (Nat.odd_iff.2 h0)
    have h4 : g ∣ 2*(a + k) := by
      have := Nat.dvd_add h1 h2
      rwa [show u + u' = 2*(a + k) by omega] at this
    have h5 : g ∣ a := (Nat.dvd_add_left h3).1 ((Nat.Coprime.dvd_mul_left hgo).1 h4)
    exact hcom g h5 ((Nat.dvd_add_right h5).1 h2) h3
  have c23 : Nat.gcd (Nat.gcd a u') k = 1 := by
    set g := Nat.gcd (Nat.gcd a u') k
    have h1 : g ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have h2 : g ∣ u' := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    exact hcom g h1 ((Nat.dvd_add_right h1).1 h2) (Nat.gcd_dvd_right _ _)
  by_cases hu : Nat.Coprime a (2*k)
  · -- `a` a unit: the pair `(1, D)`, `D = a⁻¹e`
    obtain ⟨ε, -, hε⟩ := Nat.exists_mul_mod_eq_one_of_coprime hu hk1
    have hεc := inv_cop a ε hε
    obtain ⟨D, hD⟩ : ∃ D, D = ε*e % (2*k) := ⟨_, rfl⟩
    have hDk : D < 2*k := hD ▸ Nat.mod_lt _ (by omega)
    have hDe : D % 2 = 0 := by
      rw [hD, Nat.mod_mod_of_dvd _ ⟨k, rfl⟩, Nat.mul_mod, hee, mul_zero, Nat.zero_mod]
    -- `a·D ≡ e`
    have hae : (a*D) % (2*k) = e := by
      rw [hD, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, hε, one_mul,
        Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
    obtain ⟨x0, x2, x3, x4, x5, x6⟩ := exceptions hao hae hlt he0 hne
    have hgood : Good k 1 D := goodM hk he hP hDk hDe x0 x2 x3 x4 x5 x6
    have hA : ((ε:ℤ)*a) ≡ 1 [ZMOD 2*k] := by
      have := int_modEq_of_nat (k := k) (x := ε*a) (y := 1)
        (by rw [mul_comm, hε, Nat.mod_eq_of_lt hk1])
      push_cast at this ⊢; exact this
    have hE : ((ε:ℤ)*e) ≡ (D:ℤ) [ZMOD 2*k] := by
      have := int_modEq_of_nat (k := k) (x := ε*e) (y := D) (by rw [hD, Nat.mod_mod])
      push_cast at this ⊢; exact this
    exact good_of_unit_mul (int_gcd_of_coprime hεc) (good_of_modEq hA hE (by exact_mod_cast hgood))
  have hf1 : 1 < Nat.gcd a (2*k) := by
    have h1 : Nat.gcd a (2*k) ≠ 1 := hu
    have h0 : Nat.gcd a (2*k) ≠ 0 := by intro h0; rw [Nat.gcd_eq_zero_iff] at h0; omega
    omega
  have hf2a : 2 * Nat.gcd a (2*k) < k := by
    have := Nat.le_of_dvd ha0 (Nat.gcd_dvd_left a (2*k)); omega
  by_cases huc : Nat.Coprime u (2*k)
  · -- the first term `u = a − e` a unit: the pair `(A, A − 1)`, `A = u⁻¹a`
    obtain ⟨ε, -, hε⟩ := Nat.exists_mul_mod_eq_one_of_coprime huc hk1
    have hεc := inv_cop u ε hε
    have hεo := odd_of_cop ε hεc
    set A := ε*a % (2*k) with hAdef
    have hAo : A % 2 = 1 := by
      rw [hAdef, Nat.mod_mod_of_dvd _ ⟨k, rfl⟩, Nat.mul_mod, hεo, hao]
    have hfA : Nat.gcd A (2*k) = Nat.gcd a (2*k) := by
      rw [hAdef, ← Nat.gcd_rec, Nat.gcd_comm, Nat.Coprime.gcd_mul_left_cancel a hεc]
    have hF := goodF hk he hP hAo (hfA ▸ hf1) (hfA ▸ hf2a)
    have hA : ((ε:ℤ)*a) ≡ (A:ℤ) [ZMOD 2*k] := by
      have := int_modEq_of_nat (k := k) (x := ε*a) (y := A) (by rw [hAdef, Nat.mod_mod])
      push_cast at this; exact this
    have hU : ((ε:ℤ)*u) ≡ 1 [ZMOD 2*k] := by
      have := int_modEq_of_nat (k := k) (x := ε*u) (y := 1)
        (by rw [mul_comm, hε, Nat.mod_eq_of_lt hk1])
      push_cast at this; exact this
    have hE : ((ε:ℤ)*e) ≡ (A:ℤ) - 1 [ZMOD 2*k] := by
      have e1 : ((ε:ℤ)*e) = ε*a + 2*k*ε - ε*u := by
        rw [hudef]; push_cast [Nat.cast_sub (show e ≤ a + 2*k by omega)]; ring
      have h0 : (2*(k:ℤ)*ε) ≡ 0 [ZMOD 2*k] := (Int.modEq_zero_iff_dvd).2 ⟨ε, rfl⟩
      rw [e1]
      have := (hA.add h0).sub hU
      simpa using this
    exact good_of_unit_mul (int_gcd_of_coprime hεc) (good_of_modEq hA hE hF)
  -- the last term `u' = a + e` a unit: the pair `(A', 1 − A')`, `A' = u'⁻¹a`
  have hu'c : Nat.Coprime u' (2*k) := by
    rcases hP.unit3 huo hao hu'o c12 c13 c23 with h' | h' | h'
    · exact absurd h' huc
    · exact absurd h' hu
    · exact h'
  obtain ⟨ε, -, hε⟩ := Nat.exists_mul_mod_eq_one_of_coprime hu'c hk1
  have hεc := inv_cop u' ε hε
  have hεo := odd_of_cop ε hεc
  set A' := ε*a % (2*k) with hA'def
  have hA'o : A' % 2 = 1 := by
    rw [hA'def, Nat.mod_mod_of_dvd _ ⟨k, rfl⟩, Nat.mul_mod, hεo, hao]
  have hfA : Nat.gcd (A' + k) (2*k) = Nat.gcd a (2*k) := by
    rw [gcd_add_k hA'o he, hA'def, ← Nat.gcd_rec, Nat.gcd_comm,
      Nat.Coprime.gcd_mul_left_cancel a hεc]
  have hF := goodF hk he hP (by omega) (hfA ▸ hf1) (hfA ▸ hf2a)
  have hS : Good k (A':ℤ) (1 - (A':ℤ)) := good_shift (by omega) (by push_cast at hF; exact hF)
  have hA : ((ε:ℤ)*a) ≡ (A':ℤ) [ZMOD 2*k] := by
    have := int_modEq_of_nat (k := k) (x := ε*a) (y := A') (by rw [hA'def, Nat.mod_mod])
    push_cast at this; exact this
  have hU : ((ε:ℤ)*u') ≡ 1 [ZMOD 2*k] := by
    have := int_modEq_of_nat (k := k) (x := ε*u') (y := 1)
      (by rw [mul_comm, hε, Nat.mod_eq_of_lt hk1])
    push_cast at this; exact this
  have hE : ((ε:ℤ)*e) ≡ 1 - (A':ℤ) [ZMOD 2*k] := by
    have e1 : ((ε:ℤ)*e) = ε*u' - ε*a := by rw [hu'def]; push_cast; ring
    rw [e1]; exact hU.sub hA
  exact good_of_unit_mul (int_gcd_of_coprime hεc) (good_of_modEq hA hE hS)

end APLemma
end Bump
end Trop
end PeriodicDifference

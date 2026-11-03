/-
# `PeriodicDifference/APLemmaHand.lean` — the orders of `prop:lemmaA-twoprime`, as a kernel test

`TwoPrime k`: of any three odd numbers each sharing a factor with `k`, two share a factor with
each other and `k`; for even `k` this says that `k` has at most two odd prime factors.
`twoPrimeB` is a Boolean test for it (`twoPrime_of_B`): at most two odd divisors `d ≥ 3` of `k`
have no smaller odd divisor `≥ 3` dividing them (these are the odd primes of `k`).
`handB k` marks the orders settled by `prop:lemmaA-twoprime` (`PeriodicDifference/APLemmaTwoPrime.lean`),
and `orderOK1` lets the per-order certificate (C3) skip them.
-/
import PeriodicDifference.APLemmaData

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

/-- At most two odd prime factors, in the form used by the proofs. -/
def TwoPrime (k : ℕ) : Prop :=
  ∀ n₁ n₂ n₃ : ℕ, n₁ % 2 = 1 → n₂ % 2 = 1 → n₃ % 2 = 1 →
    1 < Nat.gcd n₁ k → 1 < Nat.gcd n₂ k → 1 < Nat.gcd n₃ k →
    1 < Nat.gcd (Nat.gcd n₁ n₂) k ∨ 1 < Nat.gcd (Nat.gcd n₁ n₃) k ∨
      1 < Nat.gcd (Nat.gcd n₂ n₃) k

/-- The odd divisors `d ≥ 3` of `k`, in increasing order. -/
def oddDivs (k : ℕ) : List ℕ := (List.range' 3 k 2).filter (fun d => k % d == 0)

/-- The odd prime divisors of `k`: odd divisors with no smaller odd divisor `≥ 3` dividing them. -/
def oddPrimeDivs (k : ℕ) : List ℕ :=
  (oddDivs k).filter (fun d => (oddDivs k).all (fun e => !(decide (e < d) && d % e == 0)))

/-- At most two odd prime factors. -/
def twoPrimeB (k : ℕ) : Bool := decide ((oddPrimeDivs k).length ≤ 2)

/-- The orders settled by `prop:lemmaA-twoprime`. -/
def handB (k : ℕ) : Bool := twoPrimeB k

/-- The per-order certificate (C3), skipped at the orders of `prop:lemmaA-twoprime`. -/
def orderOK1 (JT : List (ℕ × ℕ)) (CT : List (ℕ × List CE)) (k : ℕ) : Bool :=
  handB k || orderOK JT CT k

lemma mem_oddDivs {k q : ℕ} (hk : 0 < k) (hq3 : 3 ≤ q) (hqo : q % 2 = 1) (hqk : q ∣ k) :
    q ∈ oddDivs k := by
  have hle := Nat.le_of_dvd hk hqk
  simp only [oddDivs, List.mem_filter, List.mem_range', beq_iff_eq]
  refine ⟨⟨(q - 3) / 2, by omega, by omega⟩, Nat.mod_eq_zero_of_dvd hqk⟩

lemma dvd_of_mem_oddDivs {k d : ℕ} (h : d ∈ oddDivs k) : d ∣ k ∧ 3 ≤ d := by
  simp only [oddDivs, List.mem_filter, List.mem_range', beq_iff_eq] at h
  obtain ⟨⟨i, -, rfl⟩, h⟩ := h
  exact ⟨Nat.dvd_of_mod_eq_zero h, by omega⟩

/-- An odd prime factor of `k` is in `oddPrimeDivs k`. -/
lemma mem_oddPrimeDivs {k q : ℕ} (hk : 0 < k) (hq : q.Prime) (hqo : q % 2 = 1) (hqk : q ∣ k) :
    q ∈ oddPrimeDivs k := by
  have h2 := hq.two_le
  unfold oddPrimeDivs
  refine List.mem_filter.2 ⟨mem_oddDivs hk (by omega) hqo hqk, List.all_eq_true.2 fun e he => ?_⟩
  have he3 := (dvd_of_mem_oddDivs he).2
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt,
    beq_eq_false_iff_ne, ne_eq]
  by_contra hc
  push_neg at hc
  obtain ⟨hlt, hmod⟩ := hc
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq e (Nat.dvd_of_mod_eq_zero hmod)) with h | h <;> omega

/-- An odd number sharing a factor with `k` has an odd prime factor of `k`. -/
lemma exists_prime_of_gcd {k n : ℕ} (hn : n % 2 = 1) (h : 1 < Nat.gcd n k) :
    ∃ q, q.Prime ∧ q % 2 = 1 ∧ q ∣ n ∧ q ∣ k := by
  set q := (Nat.gcd n k).minFac
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqn : q ∣ n := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
  have hqk : q ∣ k := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
  refine ⟨q, hq, ?_, hqn, hqk⟩
  rcases Nat.mod_two_eq_zero_or_one q with h0 | h0
  · have := (Nat.dvd_of_mod_eq_zero h0).trans hqn; omega
  · exact h0

lemma one_lt_of_common {k n m q : ℕ} (hk : 0 < k) (hq : q.Prime) (hn : q ∣ n) (hm : q ∣ m)
    (hqk : q ∣ k) : 1 < Nat.gcd (Nat.gcd n m) k := by
  have hd : q ∣ Nat.gcd (Nat.gcd n m) k := Nat.dvd_gcd (Nat.dvd_gcd hn hm) hqk
  have := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ hk) hd
  have := hq.two_le
  omega

/-- Soundness of `twoPrimeB`. -/
theorem twoPrime_of_B {k : ℕ} (hk : 0 < k) (h : twoPrimeB k = true) : TwoPrime k := by
  intro n₁ n₂ n₃ h1 h2 h3 g1 g2 g3
  obtain ⟨q₁, hq₁, ho₁, hd₁, hk₁⟩ := exists_prime_of_gcd h1 g1
  obtain ⟨q₂, hq₂, ho₂, hd₂, hk₂⟩ := exists_prime_of_gcd h2 g2
  obtain ⟨q₃, hq₃, ho₃, hd₃, hk₃⟩ := exists_prime_of_gcd h3 g3
  by_cases e12 : q₁ = q₂
  · subst e12; exact Or.inl (one_lt_of_common hk hq₁ hd₁ hd₂ hk₁)
  by_cases e13 : q₁ = q₃
  · subst e13; exact Or.inr (Or.inl (one_lt_of_common hk hq₁ hd₁ hd₃ hk₁))
  by_cases e23 : q₂ = q₃
  · subst e23; exact Or.inr (Or.inr (one_lt_of_common hk hq₂ hd₂ hd₃ hk₂))
  exfalso
  have hlen : (oddPrimeDivs k).length ≤ 2 := of_decide_eq_true h
  have hnd : (oddPrimeDivs k).Nodup :=
    ((List.nodup_range' (step := 2) (by norm_num)).filter _).filter _
  have hsub : ({q₁, q₂, q₃} : Finset ℕ) ⊆ (oddPrimeDivs k).toFinset := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [List.mem_toFinset]
    rcases hy with rfl | rfl | rfl
    · exact mem_oddPrimeDivs hk hq₁ ho₁ hk₁
    · exact mem_oddPrimeDivs hk hq₂ ho₂ hk₂
    · exact mem_oddPrimeDivs hk hq₃ ho₃ hk₃
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_insert_of_notMem (by simp [e12, e13]),
    Finset.card_pair e23] at hc
  omega

end APLemma
end Bump
end Trop
end PeriodicDifference

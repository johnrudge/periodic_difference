/-
# `PeriodicDifference/APLemmaTailPat.lean` — Jacobsthal bounds for at most eight prime factors

For `n` with `ω(n) ≤ 8` (`lem:lemmaA-pattern`), write `A` (the paper's `B`) for the product of its
primes `≤ 13` and `r` for the number of its primes `> 13`; `LP_i` is the paper's `ϖ_{i+1}`.  The
table `patT` (`APLemmaTailPatData.lean`) gives for every such pattern `(A, r)` a window length `m`
and a count `c` with `CountOK A m c` (kernel-checked, `pat_count*`) and `∑_{i<r} ⌈m/LP_i⌉ < c`; by
the rearrangement inequality (`rearr_sum`) the actual primes `> 13` of `n` hit at most that many
points of a window, so `JacOK n m` (`jacOK_of_count`), and `n ≥ A · ∏_{i<r} LP_i` (`rearr_prod`).
-/
import PeriodicDifference.APLemmaTailPatCount

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pat_cover : SPl.sublists.all (fun L => (List.range (9 - L.length)).all fun r =>
    patT.any fun e => e.1 == L.prod && e.2.1 == r &&
      patEntryOK e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

theorem prime_le13 {p : ℕ} (hp : p.Prime) (h : p ≤ 13) : p ∈ SPl := by
  interval_cases p <;> simp_all [SPl] <;> norm_num at hp

theorem count_LP : ∀ i < 8, Nat.count (fun y => y.Prime ∧ 13 < y) (LPl.getD i 0) = i := by
  decide

/-- Ceiling division is antitone in the divisor. -/
theorem ceil_div_anti {m q b : ℕ} (hq : 0 < q) (hqb : q ≤ b) :
    (m + b - 1)/b ≤ (m + q - 1)/q := by
  set t := (m + q - 1)/q
  have h1 : m + q - 1 < q * (t + 1) := by
    have := Nat.lt_mul_div_succ (m + q - 1) hq; simpa [t] using this
  have h2 : m ≤ q * t := by
    rcases Nat.eq_zero_or_pos m with h | h
    · omega
    · have : q * (t+1) = q*t + q := by ring
      omega
  have h3 : m ≤ b * t := h2.trans (Nat.mul_le_mul_right _ hqb)
  have hb : 0 < b := by omega
  rw [Nat.div_le_iff_le_mul_add_pred hb]
  omega

/-- The pattern bound. -/
theorem jac_pattern {n : ℕ} (hn : 0 < n) (hω : n.primeFactors.card ≤ 8) :
    ∃ A r m : ℕ, JacOK n m ∧ A ∣ n ∧ A * lpProd r ≤ n ∧ (2 ∣ n → A % 2 = 0) ∧
      (A % 2 != 0 || decide (178*m^2 ≤ 10*max (A*lpProd r) (A*(2730/A + 1)))) = true ∧
      (decide (m ≤ 8) || decide (1000*m < 102*(A*lpProd r))) = true := by
  classical
  set L := SPl.filter (· ∣ n) with hL
  set T := n.primeFactors.filter (13 < ·) with hT
  have hLsub : L ∈ SPl.sublists := List.mem_sublists.2 List.filter_sublist
  have hSPnd : SPl.Nodup := by decide
  have hLnd : L.Nodup := hSPnd.filter _
  have hSPp : ∀ p ∈ SPl, p.Prime ∧ p ≤ 13 := by decide
  have hLmem : ∀ p, p ∈ L ↔ p ∈ n.primeFactors ∧ p ≤ 13 := by
    intro p
    simp only [hL, List.mem_filter, decide_eq_true_eq, Nat.mem_primeFactors]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨(hSPp p h1).1, h2, hn.ne'⟩, (hSPp p h1).2⟩
    · rintro ⟨⟨h1, h2, -⟩, h3⟩; exact ⟨prime_le13 h1 h3, h2⟩
  have hsplit : n.primeFactors = L.toFinset ∪ T := by
    ext p
    simp only [Finset.mem_union, List.mem_toFinset, hLmem, hT, Finset.mem_filter]
    constructor
    · intro h; by_cases h13 : p ≤ 13
      · exact Or.inl ⟨h, h13⟩
      · exact Or.inr ⟨h, by omega⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  have hdisj : Disjoint L.toFinset T := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [List.mem_toFinset, hLmem] at h1
    simp only [hT, Finset.mem_filter] at h2
    omega
  have hcard : L.length + T.card = n.primeFactors.card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj, List.toFinset_card_of_nodup hLnd]
  have hprodL : L.prod = ∏ p ∈ L.toFinset, p := by
    have e := List.prod_toFinset (fun p => p) hLnd
    simp only [List.map_id'] at e
    exact e.symm
  have hrad : L.prod * ∏ p ∈ T, p ∣ n := by
    rw [hprodL, ← Finset.prod_union hdisj, ← hsplit]
    exact Nat.prod_primeFactors_dvd n
  -- the table entry
  have hc := pat_cover
  simp only [List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hc
  obtain ⟨e, he, ⟨⟨heA, her⟩, hok⟩⟩ := hc L hLsub T.card (by omega)
  have hcount := pat_count_all e he
  obtain ⟨A, r, m, c⟩ := e
  simp only at heA her hok hcount
  subst heA her
  simp only [patEntryOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hus, htail⟩, hg⟩ := hok
  have hTp : ∀ x ∈ T, x.Prime ∧ 13 < x := by
    intro x hx; simp only [hT, Finset.mem_filter, Nat.mem_primeFactors] at hx
    exact ⟨hx.1.1, hx.2⟩
  have hTcard : T.card ≤ 8 := by omega
  have hsum : ∑ p ∈ T, (m + p - 1)/p ≤ unionSum m T.card := by
    unfold unionSum
    refine rearr_sum (fun i => LPl.getD i 0) 8 count_LP (fun x => (m + x - 1)/x) ?_ T hTp hTcard
    intro i hi b hb
    have : 0 < LPl.getD i 0 := by interval_cases i <;> decide
    exact ceil_div_anti this hb
  have hprod : lpProd T.card ≤ ∏ p ∈ T, p := by
    unfold lpProd
    exact rearr_prod (fun i => LPl.getD i 0) 8 count_LP T hTp hTcard
  refine ⟨L.prod, T.card, m, ?_, ?_, ?_, ?_, htail, hg⟩
  · refine jacOK_of_count hcount T (fun p hp => (hTp p hp).1) (by omega) ?_
    intro ℓ hℓ hdvd
    by_cases h13 : ℓ ≤ 13
    · left; exact List.dvd_prod ((hLmem ℓ).2 ⟨Nat.mem_primeFactors.2 ⟨hℓ, hdvd, hn.ne'⟩, h13⟩)
    · right; simp only [hT, Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hℓ, hdvd, hn.ne'⟩, by omega⟩
  · exact (Dvd.intro _ rfl).trans hrad
  · exact (Nat.mul_le_mul_left _ hprod).trans (Nat.le_of_dvd hn hrad)
  · intro h2
    have : 2 ∈ L := (hLmem 2).2 ⟨Nat.mem_primeFactors.2 ⟨Nat.prime_two, h2, hn.ne'⟩, by norm_num⟩
    exact Nat.mod_eq_zero_of_dvd (List.dvd_prod this)

end APLemma
end Bump
end Trop
end PeriodicDifference

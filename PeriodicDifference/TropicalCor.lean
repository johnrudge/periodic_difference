/-
# `PeriodicDifference/TropicalCor.lean` — the min-plus map is not periodic (`cor:trop-nonperiodic`)

The proof of `thm:main` never uses the coefficients on the min-plus side, so it also proves a
statement about the min-plus recursion alone: for every palindromic `S ⊆ {1, …, k − 1}` with
`|S| ≥ 3` and either θ, no power `T^p`, `p ≥ 1`, of the min-plus map `T` (`def:trop-minplus`)
is the identity on integer windows (`trop_nonperiodic`).

* **Primitive `S`** (`prim_not_tropPeriodic`): the case walk of `Problem11.big_case`, with each
  mechanism in its min-plus form — the full support (`FS.not_tropPeriodic`), odd `k`
  (`OddK.not_tropPeriodic`), `(6, {1, 3, 5})` (`Cert6.not_tropPeriodic`) and the σ-bump at the
  other even orders (`Problem11.bump_even`, `Bump.not_tropPeriodic_of_bumpSat`).  Each is
  `thm:tangent`(i) (`not_tropPeriodic_of_tangent`) for an explicit integer solution and tangent
  orbit, none of which involves the coefficients.
* **Unfolding** (`tropPeriodic_unfold`): with `ℓ = gcd(S ∪ {k})`, an integer solution `z` for
  `(k/ℓ, S/ℓ, θ)` spreads to the solution `x n = z ⌊n/ℓ⌋` for `(k, S, θ)` (`isTrop_spread`),
  so `T^p = id` at `(k, S)` gives it at `(k/ℓ, S/ℓ)`.  The folded data are those of
  `PeriodicDifference/Problem11Fold.lean` (`gcdS`, `prim_fold`, `supp_fold`).
* **Windows** (`exists_window_of_not_tropPeriodic`): `TropPeriodic` speaks of solutions; a
  solution is determined by its first window (`isTrop_unique`), which turns the refutation into
  an integer window `w` with `T^p w ≠ w`.
-/
import PeriodicDifference.Problem11Prim
import PeriodicDifference.Problem11Fold

namespace PeriodicDifference
namespace Trop

open Problem11
open Bump.PerSupport (Pal Prim)

/-! ## Solutions and windows -/

/-- The min-plus value through a relabelling `g` of the slots: equal slot values give equal
minima. -/
lemma mval_map_congr {J : List ℕ} {g : ℕ → ℕ} {e e' : ℕ → ℤ} {n n' : ℕ}
    (h : ∀ j ∈ J, slot e n j = slot e' n' (g j)) : mval J e n = mval (J.map g) e' n' := by
  cases J with
  | nil => rfl
  | cons i js =>
    simp only [mval, List.map_cons, List.map_map]
    rw [h i (List.mem_cons_self ..)]
    congr 1
    exact List.map_congr_left fun j hj => h j (List.mem_cons_of_mem _ hj)

/-- A solution of the min-plus recursion is determined by its first window. -/
lemma isTrop_unique {k' : ℕ} {J : List ℕ} (hJk : ∀ j ∈ J, j ≤ k') {e e' : ℕ → ℤ}
    (he : IsTrop (k' + 1) J e) (he' : IsTrop (k' + 1) J e') (h0 : ∀ i ≤ k', e i = e' i) :
    ∀ n, e n = e' n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hnk : n ≤ k'
    · exact h0 n hnk
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + (k' + 1) := ⟨n - (k' + 1), by omega⟩
      have hm : mval J e m = mval J e' m := by
        have h := mval_map_congr (J := J) (g := id) (e := e) (e' := e') (n := m) (n' := m)
          fun j hj => by
            by_cases hj0 : j = 0
            · simp [slot, hj0]
            · simp only [slot, id, if_neg hj0]
              exact ih _ (by have := hJk j hj; omega)
        simpa using h
      have h1 := he m
      have h2 := he' m
      have h3 : e m = e' m := ih m (by omega)
      omega

/-- A shifted solution is a solution. -/
lemma IsTrop.shift {k : ℕ} {J : List ℕ} {e : ℕ → ℤ} (he : IsTrop k J e) (n : ℕ) :
    IsTrop k J (fun i => e (n + i)) := by
  intro m
  show e (n + (m + k)) + e (n + m) = _
  rw [← add_assoc, he (n + m)]
  have h := mval_map_congr (J := J) (g := id) (e := e) (e' := fun i => e (n + i))
    (n := n + m) (n' := m) fun j _ => by
      by_cases hj0 : j = 0
      · simp [slot, hj0]
      · simp only [slot, id, if_neg hj0, add_assoc]
  simpa using h

/-- If every integer window returns after `p` steps of the min-plus map, every integer
solution is `p`-periodic. -/
theorem tropPeriodic_of_winIter {k' : ℕ} {J : List ℕ} (hJk : ∀ j ∈ J, j ≤ k') {p : ℕ}
    (h : ∀ w : List ℤ, w.length = k' + 1 → winIter (shiftApp (fZ J)) w p = w) :
    TropPeriodic (k' + 1) J p := by
  intro e he n
  have hlen := window_length (fun i => e (n + i)) k'
  have hseq : ∀ i, seqOf (fZ J) (window (fun i => e (n + i)) k') i = e (n + i) :=
    isTrop_unique hJk (isTrop_seqOf hlen hJk) (he.shift n) fun i hi => seqOf_window _ hi
  have h1 := congrArg (fun l : List ℤ => l.getI 0) (h _ hlen)
  simp only at h1
  rw [getI_winIter hlen 0 (Nat.zero_le _) p, window_getI _ k' (Nat.zero_le _), hseq] at h1
  simpa using h1

/-- A refutation of `TropPeriodic` is an integer window that does not return after `p` steps:
`T^p w ≠ w`. -/
theorem exists_window_of_not_tropPeriodic {k' : ℕ} {J : List ℕ} (hJk : ∀ j ∈ J, j ≤ k')
    {p : ℕ} (h : ¬ TropPeriodic (k' + 1) J p) :
    ∃ w : List ℤ, w.length = k' + 1 ∧ winIter (shiftApp (fZ J)) w p ≠ w := by
  by_contra hc
  push_neg at hc
  exact h (tropPeriodic_of_winIter hJk hc)

/-! ## Unfolding (`lem:unfold`) -/

/-- The spread `x n = z ⌊n/d⌋` of a solution for `(K', J')` solves the recursion for
`(d K', d J')`. -/
lemma isTrop_spread {d K' : ℕ} (hd : 0 < d) {J' : List ℕ} {z : ℕ → ℤ}
    (hz : IsTrop K' J' z) : IsTrop (d * K') (J'.map (· * d)) (fun n => z (n / d)) := by
  intro n
  show z ((n + d * K') / d) + z (n / d) = _
  rw [Nat.add_mul_div_left _ _ hd, hz (n / d)]
  refine mval_map_congr fun j _ => ?_
  by_cases hj0 : j = 0
  · simp [slot, hj0]
  · have hjd : j * d ≠ 0 := Nat.mul_ne_zero hj0 hd.ne'
    simp only [slot, if_neg hj0, if_neg hjd]
    rw [Nat.add_mul_div_right _ _ hd]

lemma periodic_mul_int {x : ℕ → ℤ} {p : ℕ} (h : ∀ n, x (n + p) = x n) :
    ∀ m n, x (n + p * m) = x n := by
  intro m
  induction m with
  | zero => intro n; simp
  | succ m ih =>
    intro n
    rw [show n + p * (m + 1) = (n + p * m) + p by ring, h, ih]

/-- **Unfolding**: if `T^p = id` for `(d K', d J')` then `T^p = id` for `(K', J')`, since
`z (m + p) = x (dm + dp) = x (dm) = z m`. -/
theorem tropPeriodic_unfold {d K' : ℕ} (hd : 0 < d) {J' : List ℕ} {p : ℕ}
    (h : TropPeriodic (d * K') (J'.map (· * d)) p) : TropPeriodic K' J' p := by
  intro z hz m
  have hx := periodic_mul_int (h _ (isTrop_spread hd hz)) d (d * m)
  simp only at hx
  rwa [show d * m + p * d = (m + p) * d by ring, Nat.mul_div_cancel _ hd,
    Nat.mul_div_cancel_left _ hd] at hx

/-! ## The case walk -/

/-- **`cor:trop-nonperiodic`, primitive supports.**  For a slot list `J` below `K` with
palindromic primitive support `S = supp J`, `|S| ≥ 3`, no power `T^p`, `p ≥ 1`, of the min-plus
map is the identity.  The walk is that of `Problem11.big_case`. -/
theorem prim_not_tropPeriodic {K : ℕ} {J : List ℕ} (hlt : ∀ j ∈ J, j < K)
    (hpal : ∀ j ∈ J, j ≠ 0 → K - j ∈ J) (hprim : Prim K (supp J))
    (hcard : 3 ≤ (supp J).card) {p : ℕ} (hp : 0 < p) : ¬ TropPeriodic K J p := by
  have hsub : supp J ⊆ Finset.Icc 1 (K - 1) := by
    intro m hm
    rw [mem_supp] at hm
    have := hlt m hm.2
    simp only [Finset.mem_Icc]; omega
  have hpalS : Pal K (supp J) := by
    intro m hm
    rw [mem_supp] at hm ⊢
    have := hlt m hm.2
    exact ⟨by omega, hpal m hm.2 hm.1⟩
  by_cases hne : supp J = Finset.Icc 1 (K - 1)
  · have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    obtain ⟨k', rfl⟩ : ∃ k', K = k' + 1 := ⟨K - 1, by omega⟩
    refine FS.not_tropPeriodic (by omega) (fun j hj => ?_) (fun j hj1 hj2 => ?_) hp
    · have := hlt j hj; omega
    · have hm : j ∈ supp J := by rw [hne, Finset.mem_Icc]; omega
      exact (mem_supp.mp hm).2
  by_cases hodd : K % 2 = 1
  · exact OddK.not_tropPeriodic hodd hsub hpalS hprim hcard hne supp_JS supp_SJ hp
  by_cases h6 : K = 6 ∧ supp J = {1, 3, 5}
  · obtain ⟨rfl, hs⟩ := h6
    refine Cert6.not_tropPeriodic (decide (0 ∈ J)) (fun m => ?_) hp
    have : m ∈ supp J ↔ m ∈ ({1, 3, 5} : Finset ℕ) := by rw [hs]
    rw [mem_supp] at this
    rcases eq_or_ne m 0 with rfl | hm0
    · by_cases h0 : 0 ∈ J <;> simp [Cert6.cert, h0]
    · by_cases h0 : 0 ∈ J <;> simp_all [Cert6.cert]
  obtain ⟨σ, Q, hbs⟩ := bump_even (by omega) hsub hpalS hprim hcard hne h6
  exact Bump.not_tropPeriodic_of_bumpSat hbs supp_JS supp_SJ hp

/-- **`cor:trop-nonperiodic`, for a slot list.**  For a slot list `J` below `K` with
palindromic support `S = supp J`, `|S| ≥ 3` (primitive or not), no power `T^p`, `p ≥ 1`, of the
min-plus map is the identity: fold to the primitive support (`tropPeriodic_unfold`). -/
theorem not_tropPeriodic_of_pal {K : ℕ} {J : List ℕ} (hlt : ∀ j ∈ J, j < K)
    (hpal : ∀ j ∈ J, j ≠ 0 → K - j ∈ J) (hcard : 3 ≤ (supp J).card) {p : ℕ} (hp : 0 < p) :
    ¬ TropPeriodic K J p := by
  intro hper
  obtain ⟨s, hs⟩ : (supp J).Nonempty := Finset.card_pos.mp (by omega)
  have hK : 0 < K := by have := hlt s (mem_supp.mp hs).2; omega
  set d := gcdS K J with hd_def
  have hd : 0 < d := gcdS_pos hK
  have hdJ : ∀ j ∈ J, d ∣ j := gcdS_dvd
  have hdK : d ∣ K := gcdS_dvd_K K J
  have h' : TropPeriodic (K / d) (J.map (· / d)) p :=
    tropPeriodic_unfold hd (by rw [Nat.mul_div_cancel' hdK, map_div_mul hdJ]; exact hper)
  refine prim_not_tropPeriodic (fun j' hj' => ?_) (fun j' hj' h0 => ?_) (prim_fold hK) ?_ hp h'
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hj'
    exact Nat.div_lt_div_of_lt_of_dvd hdK (hlt j hj)
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hj'
    have hj0 : j ≠ 0 := fun h' => h0 (by simp [h'])
    refine List.mem_map.mpr ⟨K - j, hpal j hj hj0, ?_⟩
    rw [← sub_fold hdK (hdJ j hj), Nat.mul_div_cancel _ hd]
  · rw [supp_fold hd hdJ, Finset.card_image_of_injOn]
    · exact hcard
    · intro a ha b hb hab
      have ha' := Nat.div_mul_cancel (hdJ a (mem_supp.mp ha).2)
      have hb' := Nat.div_mul_cancel (hdJ b (mem_supp.mp hb).2)
      simp only at hab
      rw [← ha', ← hb', hab]

/-! ## The corollary -/

/-- The slot list of a support `S` and `θ`: the constant slot `0` when `θ = true`, then the
elements of `S`. -/
def slotList (S : Finset ℕ) (θ : Bool) : List ℕ := (if θ then [0] else []) ++ S.sort (· ≤ ·)

lemma mem_slotList {S : Finset ℕ} {θ : Bool} {j : ℕ} :
    j ∈ slotList S θ ↔ (θ = true ∧ j = 0) ∨ j ∈ S := by
  cases θ <;> simp [slotList, Finset.mem_sort]

/-- **`cor:trop-nonperiodic`** (the min-plus map is not periodic).  Let `S ⊆ {1, …, k − 1}` be
palindromic (`k − s ∈ S` for `s ∈ S`) with `|S| ≥ 3`, and let `θ` be either value.  Then no power
of the min-plus map `T` of `(k, S, θ)` (`def:trop-minplus`: the window map
`shiftApp (fZ (slotList S θ))` on windows of length `k`) is the identity: for every `p ≥ 1`
there is an integer window `w ∈ ℤ^k` with `T^p(w) ≠ w`.  No primitivity hypothesis. -/
theorem trop_nonperiodic {k : ℕ} {S : Finset ℕ} (hsub : S ⊆ Finset.Icc 1 (k - 1))
    (hpal : ∀ s ∈ S, k - s ∈ S) (hcard : 3 ≤ S.card) (θ : Bool) {p : ℕ} (hp : 1 ≤ p) :
    ∃ w : List ℤ, w.length = k ∧ winIter (shiftApp (fZ (slotList S θ))) w p ≠ w := by
  obtain ⟨s, hs⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hsb := Finset.mem_Icc.mp (hsub hs)
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hS0 : (0 : ℕ) ∉ S := fun h => by have := Finset.mem_Icc.mp (hsub h); omega
  have hsupp : supp (slotList S θ) = S := by
    ext m
    rw [mem_supp, mem_slotList]
    constructor
    · rintro ⟨hm0, (⟨-, rfl⟩ | hm)⟩
      · exact absurd rfl hm0
      · exact hm
    · intro hm
      exact ⟨fun h => hS0 (h ▸ hm), Or.inr hm⟩
  have hlt : ∀ j ∈ slotList S θ, j < k' + 1 := by
    intro j hj
    rcases mem_slotList.mp hj with ⟨-, rfl⟩ | hjS
    · omega
    · have := Finset.mem_Icc.mp (hsub hjS); omega
  refine exists_window_of_not_tropPeriodic (fun j hj => Nat.lt_succ_iff.mp (hlt j hj))
    (not_tropPeriodic_of_pal hlt (fun j hj hj0 => ?_) (by rw [hsupp]; exact hcard) hp)
  have hjS : j ∈ S := by
    rcases mem_slotList.mp hj with ⟨-, rfl⟩ | hjS
    · exact absurd rfl hj0
    · exact hjS
  exact mem_slotList.mpr (Or.inr (hpal j hjS))

end Trop
end PeriodicDifference

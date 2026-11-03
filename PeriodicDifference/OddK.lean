/-
# `PeriodicDifference/OddK.lean` — `thm:oddk`: Problem 11 at every odd order

At odd `k`, every primitive palindromic support `S ⊆ [1, k−1]` with `|S| ≥ 3` other than the
full support is killed, at every positive coefficient choice and both θ:

* write `S = {2x, k − 2x : x ∈ X}` with `X ⊆ [1, c]` (`coords`), so `|X| ≥ 2`;
* if `X` is not a dilated interval, `thm:odd-nondil` (`OddK.aprime`, second-tangent rays on the
  alternating carrier plus bump wave, `PeriodicDifference/OddKAprime.lean`);
* if `X = μ·{1,…,M}`, then `S = 2μ·T_M` (`eq:odd-prog`), `μ` is coprime to `k` by
  primitivity, `2M + 3 ≤ k` unless `S` is the full support, and `thm:odd-rowcarrier`
  (`OddK.prog_bumpSat`: interval carrier + block-preserving dilation) gives a σ-bump.

The full support is excluded here; it is `PeriodicDifference/FullSupport.lean`.  The kill is proved for the
min-plus map (`not_tropPeriodic`, used by `cor:trop-nonperiodic`); `oddk_trop` adds `thm:P`.
-/
import PeriodicDifference.OddKAprime
import PeriodicDifference.OddKProg
import PeriodicDifference.PerSupportDefs

namespace PeriodicDifference
namespace Trop
namespace OddK

open Bump

/-- The half-coordinates of a palindromic support at odd order. -/
def halfX (S : Finset ℕ) : Finset ℕ := (S.filter (fun s => s % 2 = 0)).image (· / 2)

lemma coords {k : ℕ} {S : Finset ℕ} (hk : k % 2 = 1) (hS : S ⊆ Finset.Icc 1 (k - 1))
    (hpal : PerSupport.Pal k S) (hcard : 3 ≤ S.card) : Coords k S (halfX S) := by
  have hb : ∀ s ∈ S, 1 ≤ s ∧ s ≤ k - 1 := fun s hs => Finset.mem_Icc.mp (hS hs)
  have hmemX : ∀ x, x ∈ halfX S ↔ 2 * x ∈ S := by
    intro x
    simp only [halfX, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨s, ⟨hs, he⟩, rfl⟩
      rwa [show 2 * (s / 2) = s by omega]
    · intro h; exact ⟨2 * x, ⟨h, by omega⟩, by omega⟩
  have hmem : ∀ j, j ∈ S ↔ ∃ x ∈ halfX S, j = 2 * x ∨ j = k - 2 * x := by
    intro j
    constructor
    · intro hj
      have := hb j hj
      rcases Nat.mod_two_eq_zero_or_one j with h | h
      · exact ⟨j / 2, (hmemX _).mpr (by rwa [show 2 * (j / 2) = j by omega]), Or.inl (by omega)⟩
      · refine ⟨(k - j) / 2, (hmemX _).mpr ?_, Or.inr (by omega)⟩
        rw [show 2 * ((k - j) / 2) = k - j by omega]; exact hpal j hj
    · rintro ⟨x, hx, rfl | rfl⟩
      · exact (hmemX x).mp hx
      · exact hpal _ ((hmemX x).mp hx)
  refine ⟨hk, ?_, hmem, ?_⟩
  · intro x hx
    have := hb _ ((hmemX x).mp hx)
    omega
  · have hsub : S ⊆ (halfX S).image (fun x => 2 * x) ∪ (halfX S).image (fun x => k - 2 * x) := by
      intro j hj
      obtain ⟨x, hx, h | h⟩ := (hmem j).mp hj
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx, h.symm⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, h.symm⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le ((halfX S).image (fun x => 2 * x))
      ((halfX S).image (fun x => k - 2 * x))
    have h3 := Finset.card_image_le (s := halfX S) (f := fun x => 2 * x)
    have h4 := Finset.card_image_le (s := halfX S) (f := fun x => k - 2 * x)
    have : 1 < (halfX S).card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp this
    exact ⟨a, ha, b, hb, hab⟩

/-- **`thm:oddk`, for the min-plus map**: at odd `k`, for every primitive palindromic
`S ⊆ [1, k − 1]` with `|S| ≥ 3` other than the full support, every slot list with nonzero slots
`S` (both θ) and every `p ≥ 1`, the `p`-th power of the min-plus map is not the identity. -/
theorem not_tropPeriodic {k : ℕ} (hk : k % 2 = 1) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 (k - 1))
    (hpal : PerSupport.Pal k S) (hprim : PerSupport.Prim k S) (hcard : 3 ≤ S.card)
    (hne : S ≠ Finset.Icc 1 (k - 1))
    {J : List ℕ} (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S) (hSJ : ∀ j ∈ S, j ∈ J)
    {p : ℕ} (hp : 0 < p) : ¬ TropPeriodic k J p := by
  have H := coords hk hS hpal hcard
  by_cases hD : Dil (halfX S)
  swap
  · exact aprime_trop H hD hJS hSJ hp
  obtain ⟨μ, M, hμ, hXM⟩ := hD
  -- `S = 2μ·T_M`
  have hSprog : S = progS k μ M := by
    ext j
    rw [H.mem j]
    simp only [progS, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨x, hx, h⟩
      obtain ⟨i, h1, h2, rfl⟩ := (hXM x).mp hx
      rcases h with rfl | rfl
      · exact Or.inl ⟨i, ⟨h1, h2⟩, by ring⟩
      · exact Or.inr ⟨i, ⟨h1, h2⟩, by rw [mul_assoc]⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact ⟨μ * i, (hXM _).mpr ⟨i, hi.1, hi.2, rfl⟩, Or.inl (by ring)⟩
      · exact ⟨μ * i, (hXM _).mpr ⟨i, hi.1, hi.2, rfl⟩, Or.inr (by rw [mul_assoc])⟩
  -- `M ≥ 2` and `2μM < k`
  have hM : 2 ≤ M := by
    obtain ⟨a, ha, b, hb, hab⟩ := H.two
    obtain ⟨i, hi1, hi2, rfl⟩ := (hXM a).mp ha
    obtain ⟨i', hi1', hi2', rfl⟩ := (hXM b).mp hb
    by_contra h
    exact hab (by rw [show i = 1 by omega, show i' = 1 by omega])
  have hbd : 2 * μ * M < k := by
    have := H.X_bd _ ((hXM (μ * M)).mpr ⟨M, by omega, le_rfl, rfl⟩)
    rw [← mul_assoc] at this; exact this.2
  -- primitivity makes `μ` a unit
  have hcop : Nat.Coprime μ k := by
    have hg : Nat.gcd μ k ∣ S.gcd id := by
      apply Finset.dvd_gcd
      intro s hs
      rw [hSprog] at hs
      simp only [progS, Finset.mem_union, Finset.mem_image] at hs
      have h1 : Nat.gcd μ k ∣ μ := Nat.gcd_dvd_left μ k
      have h2 : Nat.gcd μ k ∣ k := Nat.gcd_dvd_right μ k
      rcases hs with ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h1 2) i
      · exact Nat.dvd_sub h2 (Dvd.dvd.mul_right (Dvd.dvd.mul_left h1 2) i)
    have := Nat.dvd_gcd hg (Nat.gcd_dvd_right μ k)
    unfold PerSupport.Prim at hprim
    rw [hprim] at this
    exact Nat.eq_one_of_dvd_one this
  -- not the full support
  have h2 : 2 * M + 3 ≤ k := by
    rcases Nat.lt_or_ge μ 2 with h | h
    · have hμ1 : μ = 1 := by omega
      subst hμ1
      by_contra hc
      apply hne
      have hkM : k = 2 * M + 1 := by omega
      rw [hSprog]
      ext j
      simp only [progS, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> omega
      · intro hj
        rcases Nat.mod_two_eq_zero_or_one j with h | h
        · exact Or.inl ⟨j / 2, ⟨by omega, by omega⟩, by omega⟩
        · exact Or.inr ⟨(k - j) / 2, ⟨by omega, by omega⟩, by omega⟩
    · have : 4 * M ≤ 2 * μ * M := by nlinarith
      omega
  obtain ⟨σ, Q, hbs⟩ := prog_bumpSat hk hM h2 hbd hcop
  rw [← hSprog] at hbs
  exact not_tropPeriodic_of_bumpSat hbs hJS hSJ hp

/-- **`thm:oddk`, min-plus form** (`not_tropPeriodic` and `thm:P`). -/
theorem oddk_trop {k : ℕ} (hk : k % 2 = 1) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 (k - 1))
    (hpal : PerSupport.Pal k S) (hprim : PerSupport.Prim k S) (hcard : 3 ≤ S.card)
    (hne : S ≠ Finset.Icc 1 (k - 1))
    {J : List ℕ} (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S) (hSJ : ∀ j ∈ S, j ∈ J)
    {co : ℕ → ℝ} (hco : ∀ j ∈ J, 0 < co j) {p : ℕ} (hp : 0 < p) :
    ¬ GloballyPeriodic k J co p := fun hg =>
  not_tropPeriodic hk hS hpal hprim hcard hne hJS hSJ hp
    ((coords hk hS hpal hcard).tropPeriodic hJS hSJ hco hg)

end OddK
end Trop

end PeriodicDifference

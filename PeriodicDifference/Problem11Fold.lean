/-
# `PeriodicDifference/Problem11Fold.lean` — the primitive reduction, in the sequence form

With `d = gcd(S ∪ {K})` (the paper's `ℓ` in `lem:unfold`), an admissible equation at order `K`
is the `d`-fold unfolding of the admissible equation at order `K/d` with slots `J/d` and
coefficients `m ↦ co (m d)`; global periodicity passes down (`Trop.unfold_globallyPeriodic`),
the folded support is primitive, and a member below is a member above.
-/
import PeriodicDifference.Problem11Defs
import PeriodicDifference.Unfold

namespace PeriodicDifference
namespace Problem11

open Trop
open Trop.Bump.PerSupport (Pal Prim)

section Fold

variable {K d : ℕ} {J : List ℕ} {co : ℕ → ℝ}

/-- The folded coefficients. -/
def foldCo (d : ℕ) (co : ℕ → ℝ) : ℕ → ℝ := fun m => co (m * d)

lemma map_div_mul (hdJ : ∀ j ∈ J, d ∣ j) : (J.map (· / d)).map (· * d) = J := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id J]
  exact List.map_congr_left fun j hj => Nat.div_mul_cancel (hdJ j hj)

lemma fold_gp (hd : 0 < d) (hdK : d ∣ K) (hdJ : ∀ j ∈ J, d ∣ j) {p : ℕ}
    (hg : GloballyPeriodic K J co p) :
    GloballyPeriodic (K / d) (J.map (· / d)) (foldCo d co) p := by
  refine unfold_globallyPeriodic hd ?_
  rw [Nat.mul_div_cancel' hdK, map_div_mul hdJ]
  refine gp_congr (fun x n => ?_) (hg.mul d)
  rw [rhs, rhs]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  simp only [spreadCo, foldCo, Nat.div_mul_cancel (hdJ j hj)]

lemma div_eq_zero_iff_of_dvd (hd : 0 < d) {j : ℕ} (h : d ∣ j) : j / d = 0 ↔ j = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.mul_div_cancel_left _ hd]
  constructor
  · rintro rfl; simp
  · intro h0; rcases Nat.mul_eq_zero.mp h0 with h0 | h0 <;> omega

lemma sub_fold {j : ℕ} (hdK : d ∣ K) (hj : d ∣ j) : (K / d - j / d) * d = K - j := by
  rw [Nat.sub_mul, Nat.div_mul_cancel hdK, Nat.div_mul_cancel hj]

lemma fold_admissible (h : Admissible K J co) (hd : 0 < d) (hdK : d ∣ K)
    (hdJ : ∀ j ∈ J, d ∣ j) : Admissible (K / d) (J.map (· / d)) (foldCo d co) where
  K_pos := Nat.div_pos (Nat.le_of_dvd h.K_pos hdK) hd
  nodup := by
    refine h.nodup.map_on fun a ha b hb hab => ?_
    rw [← Nat.div_mul_cancel (hdJ a ha), ← Nat.div_mul_cancel (hdJ b hb)]
    exact congrArg (· * d) hab
  lt := by
    intro j' hj'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hj'
    exact Nat.div_lt_div_of_lt_of_dvd hdK (h.lt j hj)
  pos := by
    intro j' hj'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hj'
    simp only [foldCo, Nat.div_mul_cancel (hdJ j hj)]
    exact h.pos j hj
  pal := by
    intro j' hj' h0
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hj'
    have hj0 : j ≠ 0 := fun h' => h0 (by simp [h'])
    refine List.mem_map.mpr ⟨K - j, h.pal j hj hj0, ?_⟩
    rw [← sub_fold hdK (hdJ j hj), Nat.mul_div_cancel _ hd]
  copal := by
    intro j' hj' h0
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hj'
    have hj0 : j ≠ 0 := fun h' => h0 (by simp [h'])
    simp only [foldCo]
    rw [sub_fold hdK (hdJ j hj), Nat.div_mul_cancel (hdJ j hj)]
    exact h.copal j hj hj0

lemma supp_fold (hd : 0 < d) (hdJ : ∀ j ∈ J, d ∣ j) :
    supp (J.map (· / d)) = (supp J).image (· / d) := by
  ext m
  simp only [mem_supp, Finset.mem_image, List.mem_map]
  constructor
  · rintro ⟨hm, j, hj, rfl⟩
    exact ⟨j, ⟨fun h' => hm (by simp [h']), hj⟩, rfl⟩
  · rintro ⟨j, ⟨hj0, hj⟩, rfl⟩
    exact ⟨fun h' => hj0 ((div_eq_zero_iff_of_dvd hd (hdJ j hj)).mp h'), j, hj, rfl⟩

lemma supp_unfold (hd : 0 < d) (hdJ : ∀ j ∈ J, d ∣ j) :
    supp J = (supp (J.map (· / d))).image (· * d) := by
  rw [supp_fold hd hdJ, Finset.image_image]
  ext m
  simp only [Finset.mem_image, Function.comp_apply]
  constructor
  · intro hm
    exact ⟨m, hm, Nat.div_mul_cancel (hdJ m (mem_supp.mp hm).2)⟩
  · rintro ⟨j, hj, rfl⟩
    rw [Nat.div_mul_cancel (hdJ j (mem_supp.mp hj).2)]; exact hj

lemma zero_mem_fold : 0 ∈ J.map (· / d) ↔ 0 ∈ J ∨ (∃ j ∈ J, j / d = 0 ∧ j ≠ 0) := by
  constructor
  · intro h
    obtain ⟨j, hj, h0⟩ := List.mem_map.mp h
    by_cases hj0 : j = 0
    · exact Or.inl (hj0 ▸ hj)
    · exact Or.inr ⟨j, hj, h0, hj0⟩
  · rintro (h | ⟨j, hj, h0, _⟩)
    · exact List.mem_map.mpr ⟨0, h, by simp⟩
    · exact List.mem_map.mpr ⟨j, hj, h0⟩

lemma zero_mem_fold_iff (hd : 0 < d) (hdJ : ∀ j ∈ J, d ∣ j) :
    0 ∈ J.map (· / d) ↔ 0 ∈ J := by
  rw [zero_mem_fold]
  constructor
  · rintro (h | ⟨j, hj, h0, hj0⟩)
    · exact h
    · exact absurd ((div_eq_zero_iff_of_dvd hd (hdJ j hj)).mp h0) hj0
  · exact Or.inl

end Fold

/-! ## The gcd -/

/-- `d = gcd(S ∪ {K})`. -/
def gcdS (K : ℕ) (J : List ℕ) : ℕ := Nat.gcd ((supp J).gcd id) K

lemma gcdS_pos {K : ℕ} {J : List ℕ} (hK : 0 < K) : 0 < gcdS K J := Nat.gcd_pos_of_pos_right _ hK

lemma gcdS_dvd_K (K : ℕ) (J : List ℕ) : gcdS K J ∣ K := Nat.gcd_dvd_right _ _

lemma gcdS_dvd {K : ℕ} {J : List ℕ} : ∀ j ∈ J, gcdS K J ∣ j := by
  intro j hj
  by_cases h0 : j = 0
  · rw [h0]; exact dvd_zero _
  · exact (Nat.gcd_dvd_left _ _).trans (Finset.gcd_dvd (mem_supp.mpr ⟨h0, hj⟩))

lemma prim_fold {K : ℕ} {J : List ℕ} (hK : 0 < K) :
    Prim (K / gcdS K J) (supp (J.map (· / gcdS K J))) := by
  set d := gcdS K J with hd_def
  have hd : 0 < d := gcdS_pos hK
  have hdJ : ∀ j ∈ J, d ∣ j := gcdS_dvd
  have hdK : d ∣ K := gcdS_dvd_K K J
  unfold Prim
  set g := Nat.gcd ((supp (J.map (· / d))).gcd id) (K / d) with hg
  have hgK : d * g ∣ K := Nat.mul_dvd_of_dvd_div hdK (Nat.gcd_dvd_right _ _)
  have hgS : d * g ∣ (supp J).gcd id := by
    refine Finset.dvd_gcd fun s hs => ?_
    have hs' : s / d ∈ supp (J.map (· / d)) := by
      rw [supp_fold hd hdJ]; exact Finset.mem_image_of_mem _ hs
    exact Nat.mul_dvd_of_dvd_div (hdJ s (mem_supp.mp hs).2)
      ((Nat.gcd_dvd_left _ _).trans (Finset.gcd_dvd hs'))
  have h1 : d * g ∣ d * 1 := by rw [mul_one]; exact Nat.dvd_gcd hgS hgK
  exact Nat.dvd_one.mp ((Nat.mul_dvd_mul_iff_left hd).mp h1)


/-- **The primitive reduction.**  If every primitive admissible periodic equation is a member,
so is every admissible periodic equation. -/
theorem tropMember_of_prim {K : ℕ} {J : List ℕ} {co : ℕ → ℝ} {p : ℕ}
    (h : Admissible K J co) (hg : GloballyPeriodic K J co p)
    (hprim : ∀ (K' : ℕ) (J' : List ℕ) (co' : ℕ → ℝ), Admissible K' J' co' →
      Prim K' (supp J') → GloballyPeriodic K' J' co' p → TropMember K' J' co') :
    TropMember K J co := by
  set d := gcdS K J with hd_def
  have hd : 0 < d := gcdS_pos h.K_pos
  have hdJ : ∀ j ∈ J, d ∣ j := gcdS_dvd
  have hdK : d ∣ K := gcdS_dvd_K K J
  have hK : K = K / d * d := (Nat.div_mul_cancel hdK).symm
  have hsupp := supp_unfold hd hdJ
  have h0 := zero_mem_fold_iff hd hdJ
  rcases hprim (K / d) (J.map (· / d)) (foldCo d co) (fold_admissible h hd hdK hdJ)
    (prim_fold h.K_pos) (fold_gp hd hdK hdJ hg) with he | ⟨m, hm, hs, hc⟩ | ⟨m, hm, hs, hc⟩
  · left; rw [hsupp, he, Finset.image_empty]
  · right; left
    refine ⟨m * d, by rw [hK, hm]; ring, by rw [hsupp, hs, Finset.image_singleton], ?_⟩
    rcases hc with hc | hc
    · exact Or.inl (fun h' => hc (h0.mpr h'))
    · right; simpa [foldCo] using hc
  · right; right
    refine ⟨m * d, by rw [hK, hm]; ring, ?_, by simpa [foldCo] using hc⟩
    rw [hsupp, hs, Finset.image_insert, Finset.image_singleton, mul_assoc]

end Problem11
end PeriodicDifference

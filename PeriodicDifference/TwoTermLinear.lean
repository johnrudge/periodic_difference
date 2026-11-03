/-
# `PeriodicDifference/TwoTermLinear.lean` — linearisation of a two-term equation (`thm:spectral`, `|S| = 2`)

For admissible data with `supp J = {j, K − j}` the equation reads
`x_{n+K} xₙ = c₀ + c (x_{n+j} + x_{n+K−j})`.  At the interior equilibrium
`x* = c + √(c² + c₀)` put `ε = c / x* ∈ (0, 1/2]`.  If the equation is globally
`p`-periodic then so is every real solution of the linearisation
`y_{n+K} + yₙ = ε (y_{n+j} + y_{n+K−j})` (`linear_periodic`), and hence every complex root
of `χ_ε(z) = z^K + 1 − ε (z^j + z^{K−j})` is a `p`-th root of unity (`root_pow_eq_one`).

The proof is the sequence form of the rescaling argument of `FamilyA`: the orbit started
from `x* + δ y` has `(x^δ − x*)/δ → y` termwise as `δ → 0⁺`.
-/
import PeriodicDifference.Problem11Defs

namespace PeriodicDifference
namespace TwoTerm

open Trop Problem11 Filter Topology

variable {K : ℕ} {J : List ℕ} {co : ℕ → ℝ} {j : ℕ}

/-- The right-hand side of a two-term equation. -/
lemma rhs_two (h : Admissible K J co) (hs : supp J = {j, K - j}) (hj0 : 0 < j)
    (hjK : 2 * j < K) (x : ℕ → ℝ) (n : ℕ) :
    rhs J co x n = cJ J co 0 + co j * (x (n + j) + x (n + (K - j))) := by
  have hjJ : j ∈ J := (mem_supp.mp (hs ▸ (by simp : j ∈ ({j, K - j} : Finset ℕ)))).2
  have hKjJ : K - j ∈ J :=
    (mem_supp.mp (hs ▸ (by simp : K - j ∈ ({j, K - j} : Finset ℕ)))).2
  have hc : co (K - j) = co j := h.copal j hjJ (by omega)
  rw [rhs_eq_range h]
  have hsub : ({0, j, K - j} : Finset ℕ) ⊆ Finset.range K := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
      Finset.sum_singleton, if_pos rfl, if_neg (by omega), if_neg (by omega),
      cJ_of_mem hjJ, cJ_of_mem hKjJ, hc]
    ring
  · intro m hmK hm
    have hmJ : m ∉ J := by
      intro hmJ
      have hm0 : m ≠ 0 := by rintro rfl; simp at hm
      have := mem_supp.mpr ⟨hm0, hmJ⟩
      rw [hs] at this
      exact hm (by simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢; tauto)
    rw [cJ, if_neg hmJ, zero_mul]

/-! ## The equilibrium -/

/-- The interior equilibrium of `x² = c₀ + 2 c x`. -/
noncomputable def xs (c c0 : ℝ) : ℝ := c + Real.sqrt (c ^ 2 + c0)

lemma xs_pos {c c0 : ℝ} (hc : 0 < c) : 0 < xs c c0 := by
  unfold xs; positivity

lemma xs_sq {c c0 : ℝ} (hc0 : 0 ≤ c0) : xs c c0 ^ 2 = c0 + 2 * c * xs c c0 := by
  unfold xs
  have := Real.sq_sqrt (add_nonneg (sq_nonneg c) hc0)
  linear_combination this

lemma two_c_le_xs {c c0 : ℝ} (hc : 0 < c) (hc0 : 0 ≤ c0) : 2 * c ≤ xs c c0 := by
  unfold xs
  have h1 : Real.sqrt (c ^ 2) ≤ Real.sqrt (c ^ 2 + c0) := Real.sqrt_le_sqrt (by linarith)
  rw [Real.sqrt_sq hc.le] at h1
  linarith

/-! ## Linearisation -/

/-- **Linearisation.**  A globally periodic two-term equation has every real solution of
its linearisation at `x*` periodic, with `ε = c / x* ∈ (0, 1/2]`. -/
theorem linear_periodic (h : Admissible K J co) (hs : supp J = {j, K - j}) (hj0 : 0 < j)
    (hjK : 2 * j < K) {p : ℕ} (hg : GloballyPeriodic K J co p) :
    ∃ ε : ℝ, ε = co j / xs (co j) (cJ J co 0) ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧ ∀ y : ℕ → ℝ,
      (∀ n, y (n + K) + y n = ε * (y (n + j) + y (n + (K - j)))) → ∀ n, y (n + p) = y n := by
  have hjJ : j ∈ J := (mem_supp.mp (hs ▸ (by simp : j ∈ ({j, K - j} : Finset ℕ)))).2
  have hc : 0 < co j := h.pos j hjJ
  have hc0 : 0 ≤ cJ J co 0 := by
    by_cases h0 : (0 : ℕ) ∈ J
    · rw [cJ_of_mem h0]; exact (h.pos 0 h0).le
    · rw [cJ, if_neg h0]
  set c := co j with hcdef
  set c0 := cJ J co 0 with hc0def
  set X := xs c c0 with hXdef
  have hX : 0 < X := xs_pos hc
  have hX2 : X ^ 2 = c0 + 2 * c * X := xs_sq hc0
  have h2c : 2 * c ≤ X := two_c_le_xs hc hc0
  refine ⟨c / X, rfl, div_pos hc hX, ?_, ?_⟩
  · rw [div_le_iff₀ hX]; linarith
  intro y hy n
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  let w0 : ℝ → List ℝ := fun δ => List.ofFn fun i : Fin (k + 1) => X + δ * y i
  have hw : ∀ δ, (w0 δ).length = k + 1 := fun δ => by simp [w0]
  have hwget : ∀ δ i, i ≤ k → (w0 δ).getI i = X + δ * y i := by
    intro δ i hi
    rw [List.getI_eq_getElem _ (by rw [hw]; omega)]
    simp only [w0, List.getElem_ofFn]
  let Z : ℝ → ℕ → ℝ := fun δ => orbR J co (w0 δ)
  have hJne : J ≠ [] := List.ne_nil_of_mem hjJ
  have hJk : ∀ m ∈ J, m ≤ k := fun m hm => by have := h.lt m hm; omega
  have hsol : ∀ δ, (∀ i ≤ k, 0 < X + δ * y i) → (∀ m, 0 < Z δ m) ∧
      ∀ m, Z δ (m + (k + 1)) * Z δ m = c0 + c * (Z δ (m + j) + Z δ (m + (k + 1 - j))) := by
    intro δ hδ
    have hw0 : ∀ i ≤ k, 0 < (w0 δ).getI i := fun i hi => by rw [hwget δ i hi]; exact hδ i hi
    refine ⟨orbR_pos hJne h.pos (hw δ) hJk hw0, fun m => ?_⟩
    rw [orbR_rec hJne h.pos (hw δ) hJk hw0 m, rhs_two h hs hj0 hjK]
  let L : Filter ℝ := 𝓝[>] 0
  have hgood : ∀ᶠ δ in L, 0 < δ ∧ ∀ i ≤ k, 0 < X + δ * y i := by
    refine (eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0)).and ?_
    have hall : ∀ i ∈ Finset.range (k + 1), ∀ᶠ δ in L, 0 < X + δ * y i := by
      intro i _
      have ht : Tendsto (fun δ : ℝ => X + δ * y i) (𝓝 0) (𝓝 X) := by
        have := ((continuous_const.add (continuous_id.mul continuous_const)).tendsto
          (0 : ℝ) : Tendsto (fun δ : ℝ => X + δ * y i) (𝓝 0) (𝓝 (X + 0 * y i)))
        simpa using this
      exact nhdsWithin_le_nhds (ht.eventually (lt_mem_nhds hX))
    filter_upwards [(Filter.eventually_all_finset (Finset.range (k + 1))).mpr hall]
      with δ hδ i hi
    exact hδ i (Finset.mem_range.mpr (by omega))
  have hδL : Tendsto (fun δ : ℝ => δ) L (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hconv : ∀ m, Tendsto (fun δ => (Z δ m - X) / δ) L (𝓝 (y m)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases hm : m ≤ k
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [hgood] with δ hδ
        have : Z δ m = X + δ * y m := by
          show orbR J co (w0 δ) m = _
          rw [orbR_init (hw δ) hm, hwget δ m hm]
        have hδ0 := hδ.1.ne'
        rw [this]; field_simp; ring
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + (k + 1) := ⟨m - (k + 1), by omega⟩
        have ha := ih (m' + j) (by omega)
        have hb := ih (m' + (k + 1 - j)) (by omega)
        have hm' := ih m' (by omega)
        have hZm : Tendsto (fun δ => Z δ m') L (𝓝 X) := by
          have h1 : Tendsto (fun δ => X + δ * ((Z δ m' - X) / δ)) L (𝓝 (X + 0 * y m')) :=
            tendsto_const_nhds.add (hδL.mul hm')
          rw [zero_mul, add_zero] at h1
          refine h1.congr' ?_
          filter_upwards [hgood] with δ hδ
          have hδ0 := hδ.1.ne'
          field_simp; ring
        have hlim : Tendsto (fun δ => (c * ((Z δ (m' + j) - X) / δ +
            (Z δ (m' + (k + 1 - j)) - X) / δ) - X * ((Z δ m' - X) / δ)) / Z δ m') L
            (𝓝 ((c * (y (m' + j) + y (m' + (k + 1 - j))) - X * y m') / X)) :=
          ((tendsto_const_nhds.mul (ha.add hb)).sub (tendsto_const_nhds.mul hm')).div hZm
            hX.ne'
        have hval : (c * (y (m' + j) + y (m' + (k + 1 - j))) - X * y m') / X
            = y (m' + (k + 1)) := by
          have := hy m'
          field_simp
          rw [show c / X * (y (m' + j) + y (m' + (k + 1 - j))) =
            c * (y (m' + j) + y (m' + (k + 1 - j))) / X by ring] at this
          field_simp at this
          linarith
        rw [hval] at hlim
        refine hlim.congr' ?_
        filter_upwards [hgood] with δ hδ
        obtain ⟨hpos, hrec⟩ := hsol δ hδ.2
        have hZ := hrec m'
        have hZm0 := hpos m'
        have hδ0 := hδ.1.ne'
        rw [div_eq_div_iff hZm0.ne' hδ0]
        field_simp
        linear_combination hX2 - hZ
  have hper : ∀ᶠ δ in L, (Z δ (n + p) - X) / δ = (Z δ n - X) / δ := by
    filter_upwards [hgood] with δ hδ
    obtain ⟨hpos, hrec⟩ := hsol δ hδ.2
    rw [hg (Z δ) hpos (fun m => by rw [rhs_two h hs hj0 hjK]; exact hrec m) n]
  exact tendsto_nhds_unique ((hconv (n + p)).congr' hper) (hconv n)

/-! ## Complex roots -/

/-- `χ_ε(z) = z^K + 1 − ε (z^j + z^{K−j})`. -/
noncomputable def chi (K j : ℕ) (ε : ℝ) (z : ℂ) : ℂ := z ^ K + 1 - (ε : ℂ) * (z ^ j + z ^ (K - j))

/-- If every real solution of the linearisation is `p`-periodic, every complex root of
`χ_ε` is a `p`-th root of unity. -/
theorem root_pow_eq_one {K j p : ℕ} {ε : ℝ}
    (hlin : ∀ y : ℕ → ℝ,
      (∀ n, y (n + K) + y n = ε * (y (n + j) + y (n + (K - j)))) → ∀ n, y (n + p) = y n)
    {z : ℂ} (hz : chi K j ε z = 0) : z ^ p = 1 := by
  have hrec : ∀ n, z ^ (n + K) + z ^ n = (ε : ℂ) * (z ^ (n + j) + z ^ (n + (K - j))) := by
    intro n
    have : z ^ n * chi K j ε z = 0 := by rw [hz, mul_zero]
    unfold chi at this
    rw [pow_add, pow_add, pow_add]
    linear_combination this
  have hre := hlin (fun n => (z ^ n).re) (fun n => by
    have := congrArg Complex.re (hrec n)
    simpa using this) 0
  have him := hlin (fun n => (z ^ n).im) (fun n => by
    have := congrArg Complex.im (hrec n)
    simpa using this) 0
  simp only [zero_add, pow_zero] at hre him
  exact Complex.ext (by simpa using hre) (by simpa using him)

end TwoTerm
end PeriodicDifference

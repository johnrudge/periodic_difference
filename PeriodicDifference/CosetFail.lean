/-
# `PeriodicDifference/CosetFail.lean` — two complementary failures force a coset (`lem:allodd-cosetfail`)

The paper's `lem:allodd-cosetfail` (2026-10-29): let `k` be even, `X` (the paper's `Φ`) a set
of odd residues modulo `2k` with `X = k − X`, meeting both open half-circles `U = (0, k)` and
`V = (k, 2k)`, and let `ρ, ρ'` (the paper's `φ, φ'`) be even residues outside `{0, k}`.  If
`C_U(ρ)`: `(ρ + X) ∩ U ⊆ X` and `C_V(ρ')`: `(ρ' + X) ∩ V ⊆ X`, then `X` contains a coset
of a nontrivial subgroup of `ℤ/2k`.

The proof follows the paper's (G1)–(G4) and Steps 1–4 (staged below as (i)–(v)), with `P = X ∩ U`
and `M = (X ∩ V) − k` (the paper's `Y₊`, `Y₋`) as predicates on the odd numbers of `(0, k)`:

* `per_gcd` is the engine used twice: if `P` is `d`-periodic inside `(0, k)` and its
  residue set modulo `d` is closed under `+e`, then `P` is `gcd d e`-periodic.
* (G1)+(i) give `ρ`-periodicity and closure under `+ρ'` (`per_rho`, `shift_rho'`), so `P` is
  `g₁ = gcd ρ ρ'`-periodic;
* (ii)–(iv) give closure under `+2k` modulo `g₁` (`mem_M_of_sum`, `shift_2k`), so `P` is
  `g = gcd g₁ 2k`-periodic, and (v) reads off the coset `a₀ + gℤ ⊆ X`.

The symmetries `ρ ↦ −ρ` (`cU_reflect`, `cV_reflect`) and `X ↦ X + k` (the core lemma
is stated symmetrically in `(P, ρ)` and `(M, ρ')`, so the swap is an instantiation)
reduce the theorem to `0 < ρ ≤ ρ' < k`.
-/
import Mathlib
import PeriodicDifference.ModArith

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace CosetFail

open scoped Nat

/-! ## Arithmetic helpers -/

/-- The residue of `a` modulo `2k`, for `a < 4k`, written without `%`. -/
lemma mod_two_k_cases {k : ℕ} {a : ℕ} (ha : a < 4 * k) :
    (a < 2 * k ∧ a % (2 * k) = a) ∨ (2 * k ≤ a ∧ a % (2 * k) = a - 2 * k) := by
  rcases lt_or_ge a (2 * k) with h | h
  · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
  · refine Or.inr ⟨h, ?_⟩
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

/-- Iterating an upward step inside `(0, k)`. -/
lemma iter_up {Q : ℕ → Prop} {d k : ℕ} (h : ∀ m, Q m → m + d < k → Q (m + d)) :
    ∀ j m, Q m → m + j * d < k → Q (m + j * d) := by
  intro j
  induction j with
  | zero => intro m hm _; simpa using hm
  | succ j ih =>
    intro m hm hlt
    rw [Nat.succ_mul] at hlt ⊢
    rw [← add_assoc] at hlt ⊢
    exact h _ (ih m hm (by omega)) hlt

/-- Iterating a downward step inside `(0, k)`. -/
lemma iter_down {Q : ℕ → Prop} {d : ℕ} (h : ∀ m, Q m → d < m → Q (m - d)) :
    ∀ j m, Q m → j * d < m → Q (m - j * d) := by
  intro j
  induction j with
  | zero => intro m hm _; simpa using hm
  | succ j ih =>
    intro m hm hlt
    rw [Nat.succ_mul] at hlt ⊢
    have := h _ (ih m hm (by omega)) (by omega)
    rwa [Nat.sub_sub] at this

/-! ## The periodicity engine -/

/-- `Q` is `d`-periodic inside the odd numbers of `(0, k)`. -/
def Per (Q : ℕ → Prop) (d k : ℕ) : Prop :=
  ∀ p z, Q p → z < k → z % 2 = 1 → z ≡ p [MOD d] → Q z

/-- The residue set of `Q` modulo `d` is closed under `+e`. -/
def Shift (Q : ℕ → Prop) (d e : ℕ) : Prop :=
  ∀ a, Q a → ∃ a', Q a' ∧ a' ≡ a + e [MOD d]

lemma Shift.mul {Q : ℕ → Prop} {d e : ℕ} (h : Shift Q d e) : ∀ j, Shift Q d (j * e) := by
  intro j
  induction j with
  | zero => intro a ha; exact ⟨a, ha, by simp [Nat.ModEq]⟩
  | succ j ih =>
    intro a ha
    obtain ⟨b, hb, hab⟩ := ih a ha
    obtain ⟨c, hc, hbc⟩ := h b hb
    refine ⟨c, hc, hbc.trans ?_⟩
    rw [Nat.succ_mul, ← add_assoc]
    exact hab.add_right e

/-- Bezout, in the form needed: some multiple of `e` is `gcd d e` modulo `d`. -/
lemma exists_mul_modEq_gcd {d : ℕ} (hd : 0 < d) (e : ℕ) :
    ∃ y, y * e ≡ Nat.gcd d e [MOD d] := by
  rcases lt_or_ge (Nat.gcd e d) d with h | h
  · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd h
    refine ⟨m, ?_⟩
    rw [Nat.gcd_comm, Nat.ModEq, ← hm, mul_comm, Nat.mod_mod]
  · refine ⟨0, ?_⟩
    have : Nat.gcd d e = d := le_antisymm (Nat.gcd_le_left _ hd) (by rw [Nat.gcd_comm]; exact h)
    rw [this]; simp [Nat.ModEq]

/-- The engine: `d`-periodic and shift-closed by `e` modulo `d` gives `gcd d e`-periodic. -/
lemma per_gcd {Q : ℕ → Prop} {d e k : ℕ} (hd : 0 < d) (hper : Per Q d k) (hsh : Shift Q d e) :
    Per Q (Nat.gcd d e) k := by
  intro p z hp hz hodd hmod
  obtain ⟨y, hy⟩ := exists_mul_modEq_gcd hd e
  have hpd : p ≤ d * p := Nat.le_mul_of_pos_left p hd
  set g := Nat.gcd d e with hg
  have hgd : g ∣ d := Nat.gcd_dvd_left d e
  -- `w = z + d·p ≥ p` is `z` modulo `d` and `p` modulo `g`.
  have hw : z + d * p ≡ z [MOD d] := by
    unfold Nat.ModEq; exact Nat.add_mul_mod_self_left z d p
  have hwp : p ≡ z + d * p [MOD g] := hmod.symm.trans (hw.of_dvd hgd).symm
  obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' (by omega)).1 hwp
  obtain ⟨a', ha', hmod'⟩ := hsh.mul (j * y) p hp
  refine hper a' z ha' hz hodd ?_
  have h1 : j * y * e ≡ j * g [MOD d] := by
    rw [mul_assoc]; exact hy.mul_left j
  have h2 : a' ≡ p + j * g [MOD d] := hmod'.trans (h1.add_left p)
  have h3 : p + j * g = z + d * p := by rw [mul_comm j g, ← hj]; omega
  rw [h3] at h2
  exact (h2.trans hw).symm

/-! ## The core: `P = X ∩ U` and `M = (X ∩ V) − k` -/

/-- The data of the paper's (G1)–(G4), with the standing hypotheses on
`P = X ∩ U` and `M = (X ∩ V) − k` (odd, in `(0, k)`, symmetric under `z ↦ k − z`, nonempty).
It is symmetric under `(P, ρ) ↔ (M, ρ')`, which is the paper's `Φ ↦ Φ + k`. -/
structure Data (k ρ ρ' : ℕ) (P M : ℕ → Prop) : Prop where
  hk : k % 2 = 0
  hρ : ρ % 2 = 0
  hρ' : ρ' % 2 = 0
  hρ0 : 0 < ρ
  hρ'0 : 0 < ρ'
  hρk : ρ < k
  hρ'k : ρ' < k
  hP : ∀ z, P z → z < k ∧ z % 2 = 1
  hM : ∀ z, M z → z < k ∧ z % 2 = 1
  hPs : ∀ z, P z → P (k - z)
  hMs : ∀ z, M z → M (k - z)
  hPne : ∃ a, P a
  hMne : ∃ a, M a
  f1 : ∀ p, P p → p + ρ < k → P (p + ρ)
  f2 : ∀ m, M m → m < ρ → P (ρ - m)
  f4 : ∀ m, M m → m + ρ' < k → M (m + ρ')
  f5 : ∀ p, P p → p < ρ' → M (ρ' - p)

namespace Data

variable {k ρ ρ' : ℕ} {P M : ℕ → Prop}

/-- The swap `(P, ρ) ↔ (M, ρ')`. -/
lemma swap (h : Data k ρ ρ' P M) : Data k ρ' ρ M P where
  hk := h.hk
  hρ := h.hρ'
  hρ' := h.hρ
  hρ0 := h.hρ'0
  hρ'0 := h.hρ0
  hρk := h.hρ'k
  hρ'k := h.hρk
  hP := h.hM
  hM := h.hP
  hPs := h.hMs
  hMs := h.hPs
  hPne := h.hMne
  hMne := h.hPne
  f1 := h.f4
  f2 := h.f5
  f4 := h.f1
  f5 := h.f2

/-- (G1) downwards, by the symmetry of `P`. -/
lemma down (h : Data k ρ ρ' P M) : ∀ p, P p → ρ < p → P (p - ρ) := by
  intro p hp hlt
  have hpk := h.hP p hp
  have := h.hPs _ (h.f1 _ (h.hPs _ hp) (by omega))
  rwa [show k - (k - p + ρ) = p - ρ by omega] at this

/-- (G1): `P` is `ρ`-periodic inside `(0, k)`. -/
lemma per_rho (h : Data k ρ ρ' P M) : Per P ρ k := by
  intro p z hp hz hodd hmod
  have hz' := Nat.div_add_mod z ρ
  have hp' := Nat.div_add_mod p ρ
  have hr : z % ρ = p % ρ := hmod
  rcases Nat.lt_or_ge (z / ρ) (p / ρ) with hq | hq
  · obtain ⟨j, hj⟩ : ∃ j, p / ρ = z / ρ + j := ⟨p / ρ - z / ρ, by omega⟩
    rw [hj, mul_add, ← hr] at hp'
    have : z = p - j * ρ := by rw [mul_comm j ρ]; omega
    rw [this]; exact iter_down h.down j p hp (by rw [mul_comm j ρ]; omega)
  · obtain ⟨j, hj⟩ : ∃ j, z / ρ = p / ρ + j := ⟨z / ρ - p / ρ, by omega⟩
    rw [hj, hr, mul_add] at hz'
    have : z = p + j * ρ := by rw [mul_comm j ρ]; omega
    rw [this]; exact iter_up h.f1 j p hp (by omega)

/-- The paper's (i): from `a ∈ P` below `ρ'`, climb by `ρ` to just below `ρ'`, cross to `M`
by (G4), and return by (G2); the landing point is `a − ρ'` modulo `ρ`. -/
lemma step_i (h : Data k ρ ρ' P M) : ∀ n a, P a → a < ρ' → ρ' ≤ a + n * ρ →
    ∃ a', P a' ∧ a' + ρ' ≡ a [MOD ρ] := by
  intro n
  induction n with
  | zero => intro a _ h1 h2; omega
  | succ n ih =>
    intro a ha h1 h2
    have hak := h.hP a ha
    have hρ := h.hρ
    have hρ'k := h.hρ'k
    rw [add_mul, one_mul] at h2
    rcases lt_or_ge (a + ρ) ρ' with h3 | h3
    · obtain ⟨a', ha', hmod⟩ := ih (a + ρ) (h.f1 a ha (by omega)) h3 (by omega)
      exact ⟨a', ha', hmod.trans Nat.add_modEq_right⟩
    · have hm := h.f5 a ha h1
      have hmk := h.hM _ hm
      have hlt : ρ' - a < ρ := by omega
      refine ⟨ρ - (ρ' - a), h.f2 _ hm hlt, ?_⟩
      rw [show ρ - (ρ' - a) + ρ' = ρ + a by omega]
      exact Nat.add_modEq_left

/-- The residue set of `P` modulo `ρ` is closed under `−ρ'` (needs `ρ ≤ ρ'`). -/
lemma shift_rev (h : Data k ρ ρ' P M) (hle : ρ ≤ ρ') :
    ∀ a, P a → ∃ a', P a' ∧ a' + ρ' ≡ a [MOD ρ] := by
  intro a ha
  have hak := h.hP a ha
  have hρ0 := h.hρ0
  have hρ'k := h.hρ'k
  have hmod : a % ρ < ρ := Nat.mod_lt a hρ0
  have ha' : P (a % ρ) :=
    h.per_rho a (a % ρ) ha (by omega) (by rw [mod_parity h.hρ]; exact hak.2) (Nat.mod_modEq a ρ)
  obtain ⟨a', ha'', hm⟩ := h.step_i ρ' (a % ρ) ha' (by omega)
    (by have := Nat.le_mul_of_pos_right ρ' hρ0; omega)
  exact ⟨a', ha'', hm.trans (Nat.mod_modEq a ρ)⟩

/-- A backward shift of the residue set gives a forward one, by the symmetry `z ↦ k − z`. -/
lemma fwd_of_rev {Q : ℕ → Prop} {k d e : ℕ} (hQ : ∀ z, Q z → z < k) (hs : ∀ z, Q z → Q (k - z))
    (hrev : ∀ a, Q a → ∃ a', Q a' ∧ a' + e ≡ a [MOD d]) : Shift Q d e := by
  intro a ha
  obtain ⟨b, hb, hmod⟩ := hrev (k - a) (hs a ha)
  refine ⟨k - b, hs b hb, ?_⟩
  have hak := hQ a ha
  have hbk := hQ b hb
  have h1 : (k - b) + (b + e) ≡ (a + e) + (k - a) [MOD d] := by
    rw [show (k - b) + (b + e) = (a + e) + (k - a) by omega]
  have h2 : (a + e) + (b + e) ≡ (a + e) + (k - a) [MOD d] := hmod.add_left _
  exact Nat.ModEq.add_right_cancel' _ (h1.trans h2.symm)

/-- `P` is `gcd ρ ρ'`-periodic. -/
lemma per_g1 (h : Data k ρ ρ' P M) (hle : ρ ≤ ρ') : Per P (Nat.gcd ρ ρ') k :=
  per_gcd h.hρ0 h.per_rho
    (fwd_of_rev (fun z hz => (h.hP z hz).1) h.hPs (h.shift_rev hle))

lemma two_dvd_g1 (h : Data k ρ ρ' P M) : 2 ∣ Nat.gcd ρ ρ' :=
  Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h.hρ) (Nat.dvd_of_mod_eq_zero h.hρ')

lemma g1_pos (h : Data k ρ ρ' P M) : 0 < Nat.gcd ρ ρ' := Nat.gcd_pos_of_pos_left _ h.hρ0

lemma g1_le (h : Data k ρ ρ' P M) : Nat.gcd ρ ρ' ≤ ρ := Nat.gcd_le_left _ h.hρ0


/-- The paper's (ii): an odd `z ∈ (0, k)` with `z ≡ −a (mod gcd ρ ρ')` for some `a ∈ P` lies
in `M`: its residue `z₀` modulo `ρ'` has `ρ' − z₀ ∈ P`, so `z₀ ∈ M` by (G4), and `z ∈ M` by
(G3). -/
lemma mem_M_of_sum (h : Data k ρ ρ' P M) (hle : ρ ≤ ρ') :
    ∀ z, z < k → z % 2 = 1 → (∃ a, P a ∧ z + a ≡ 0 [MOD Nat.gcd ρ ρ']) → M z := by
  intro z hz hodd ⟨a, ha, hza⟩
  have hρ'0 := h.hρ'0
  have hρ'k := h.hρ'k
  have hρ' := h.hρ'
  have hz0 : z % ρ' < ρ' := Nat.mod_lt z hρ'0
  have hz0odd : z % ρ' % 2 = 1 := by rw [mod_parity hρ']; exact hodd
  have hdm := Nat.div_add_mod z ρ'
  have hdiv : Nat.gcd ρ ρ' ∣ (ρ' - z % ρ') + z := by
    have : (ρ' - z % ρ') + z = ρ' * (z / ρ' + 1) := by rw [mul_add]; omega
    rw [this]; exact Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _
  have hza' : a + z ≡ 0 [MOD Nat.gcd ρ ρ'] := by rwa [add_comm]
  have h1 : (ρ' - z % ρ') ≡ a [MOD Nat.gcd ρ ρ'] :=
    Nat.ModEq.add_right_cancel' z ((Nat.modEq_zero_iff_dvd.2 hdiv).trans hza'.symm)
  have hP1 : P (ρ' - z % ρ') := h.per_g1 hle a _ ha (by omega) (by omega) h1
  have hM0 : M (z % ρ') := by
    have := h.f5 _ hP1 (by omega)
    rwa [show ρ' - (ρ' - z % ρ') = z % ρ' by omega] at this
  have := iter_up h.f4 (z / ρ') (z % ρ') hM0 (by rw [Nat.mod_add_div' z ρ']; exact hz)
  rwa [Nat.mod_add_div' z ρ'] at this

/-- The paper's (iii)–(iv): the residue set of `P` modulo `gcd ρ ρ'` is closed under `+2k`. -/
lemma shift_2k (h : Data k ρ ρ' P M) (hle : ρ ≤ ρ') : Shift P (Nat.gcd ρ ρ') (2 * k) := by
  intro a ha
  set g₁ := Nat.gcd ρ ρ' with hg₁
  have hg₁2 : g₁ % 2 = 0 := Nat.mod_eq_zero_of_dvd h.two_dvd_g1
  have hg₁0 : 0 < g₁ := h.g1_pos
  have hg₁ρ : g₁ ≤ ρ := h.g1_le
  have hak := h.hP a ha
  have hk := h.hk
  have hρk := h.hρk
  set z := (k + a) % g₁ with hz
  have hzlt : z < g₁ := Nat.mod_lt _ hg₁0
  have hzodd : z % 2 = 1 := by rw [hz, mod_parity hg₁2]; omega
  have hzmod : z ≡ k + a [MOD g₁] := Nat.mod_modEq _ _
  have hM1 : M (k - z) := by
    refine h.mem_M_of_sum hle (k - z) (by omega) (by omega) ⟨a, ha, ?_⟩
    refine Nat.ModEq.add_right_cancel' z ?_
    rw [show k - z + a + z = k + a by omega, zero_add]
    exact hzmod.symm
  have hM2 : M z := by
    have := h.hMs _ hM1
    rwa [show k - (k - z) = z by omega] at this
  have hP1 : P (k - (ρ - z)) := h.hPs _ (h.f2 z hM2 (by omega))
  refine ⟨k - (ρ - z), hP1, ?_⟩
  have h1 : k - (ρ - z) + ρ ≡ k - (ρ - z) [MOD g₁] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_left _ _) Nat.add_modEq_right
  refine h1.symm.trans ?_
  rw [show k - (ρ - z) + ρ = k + z by omega, show a + 2 * k = k + (k + a) by ring]
  exact hzmod.add_left k

/-- The paper's (iv)–(v): `P` is `gcd (gcd ρ ρ') (2k)`-periodic. -/
lemma per_g (h : Data k ρ ρ' P M) (hle : ρ ≤ ρ') :
    Per P (Nat.gcd (Nat.gcd ρ ρ') (2 * k)) k :=
  per_gcd h.g1_pos (h.per_g1 hle) (h.shift_2k hle)

/-- The core of `lem:allodd-cosetfail`, for `ρ ≤ ρ'`: with `g = gcd (gcd ρ ρ') (2k)` and `a₀ ∈ P`,
every odd `z ∈ (0, k)` with `z ≡ a₀` is in `P`, and every one with `z + k ≡ a₀` is in `M`. -/
lemma core (h : Data k ρ ρ' P M) (hle : ρ ≤ ρ') :
    ∃ c g, g ∣ 2 * k ∧ 0 < g ∧ g < 2 * k ∧ g % 2 = 0 ∧ c % 2 = 1 ∧
      ∀ z, z < k → z % 2 = 1 → (z ≡ c [MOD g] → P z) ∧ (z + k ≡ c [MOD g] → M z) := by
  obtain ⟨a₀, ha₀⟩ := h.hPne
  set g₁ := Nat.gcd ρ ρ' with hg₁
  set g := Nat.gcd g₁ (2 * k) with hg
  have hg₁2 : g₁ % 2 = 0 := Nat.mod_eq_zero_of_dvd h.two_dvd_g1
  have hg₁0 : 0 < g₁ := h.g1_pos
  have hg₁ρ : g₁ ≤ ρ := h.g1_le
  have hgg₁ : g ∣ g₁ := Nat.gcd_dvd_left _ _
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hg₁0
  have hgle : g ≤ g₁ := Nat.gcd_le_left _ hg₁0
  have ha₀k := h.hP a₀ ha₀
  have hk := h.hk
  have hρk := h.hρk
  refine ⟨a₀, g, Nat.gcd_dvd_right _ _, hg0, by omega,
    Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hg₁2) (dvd_mul_right 2 k)),
    ha₀k.2, ?_⟩
  intro z hz hodd
  refine ⟨fun hzc => h.per_g hle a₀ z ha₀ hz hodd hzc, fun hzk => ?_⟩
  -- the point `z' ≡ −z (mod g₁)` in `(0, g₁)` lies in `P`, since `−z ≡ k − a₀ (mod g)`.
  have hzk' : z ≤ g₁ * k := by have := Nat.le_mul_of_pos_left k hg₁0; omega
  set z' := (g₁ * k - z) % g₁ with hz'
  have hz'lt : z' < g₁ := Nat.mod_lt _ hg₁0
  have hz'odd : z' % 2 = 1 := by
    rw [hz', mod_parity hg₁2]
    have : g₁ * k % 2 = 0 := Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero hg₁2) k)
    omega
  have hz'mod : z' ≡ g₁ * k - z [MOD g₁] := Nat.mod_modEq _ _
  have hdiv : g ∣ g₁ * k := Dvd.dvd.mul_right hgg₁ k
  have h1 : (g₁ * k - z) + (z + k) ≡ (k - a₀) + (z + k) [MOD g] := by
    have e1 : (g₁ * k - z) + (z + k) = g₁ * k + ((k - a₀) + a₀) := by omega
    have e2 : (k - a₀) + (z + k) = 0 + ((k - a₀) + (z + k)) := by omega
    rw [e1, e2]
    exact (Nat.modEq_zero_iff_dvd.2 hdiv).add (hzk.symm.add_left _)
  have hz'g : z' ≡ k - a₀ [MOD g] :=
    (hz'mod.of_dvd hgg₁).trans (Nat.ModEq.add_right_cancel' _ h1)
  have hPz' : P z' := h.per_g hle (k - a₀) z' (h.hPs a₀ ha₀) (by omega) hz'odd hz'g
  refine h.mem_M_of_sum hle z hz hodd ⟨z', hPz', ?_⟩
  refine (hz'mod.add_left z).trans ?_
  rw [show z + (g₁ * k - z) = g₁ * k by omega]
  exact Nat.modEq_zero_iff_dvd.2 (dvd_mul_right _ _)


end Data

/-! ## From `X ⊆ ℤ/2k` to the core and back -/

/-- `C_U(ρ)`: `(ρ + X) ∩ U ⊆ X`, with `U = (0, k)`. -/
def CU (k : ℕ) (X : Finset ℕ) (ρ : ℕ) : Prop :=
  ∀ x ∈ X, 0 < (ρ + x) % (2 * k) → (ρ + x) % (2 * k) < k → (ρ + x) % (2 * k) ∈ X

/-- `C_V(ρ')`: `(ρ' + X) ∩ V ⊆ X`, with `V = (k, 2k)`. -/
def CV (k : ℕ) (X : Finset ℕ) (ρ' : ℕ) : Prop :=
  ∀ x ∈ X, k < (ρ' + x) % (2 * k) → (ρ' + x) % (2 * k) < 2 * k → (ρ' + x) % (2 * k) ∈ X

/-- `P = X ∩ U`. -/
def PX (k : ℕ) (X : Finset ℕ) (z : ℕ) : Prop := z ∈ X ∧ z < k

/-- `M = (X ∩ V) − k`. -/
def MX (k : ℕ) (X : Finset ℕ) (z : ℕ) : Prop := z + k ∈ X ∧ z < k

section Main

variable {k : ℕ} {X : Finset ℕ} (hk : k % 2 = 0)
  (hX : ∀ x ∈ X, x < 2 * k ∧ x % 2 = 1)
  (hsym : ∀ x ∈ X, ∀ y, y < 2 * k → (x + y) % (2 * k) = k → y ∈ X)

include hX hsym in
/-- `X = k − X` on `U`. -/
lemma sym_lt {x : ℕ} (hx : x ∈ X) (hxk : x < k) : k - x ∈ X := by
  have := hX x hx
  exact hsym x hx (k - x) (by omega)
    (by rw [show x + (k - x) = k by omega]; exact Nat.mod_eq_of_lt (by omega))

include hX hsym in
/-- `X = k − X` on `V`. -/
lemma sym_gt {x : ℕ} (hx : x ∈ X) (hxk : k < x) : 3 * k - x ∈ X := by
  have := hX x hx
  refine hsym x hx (3 * k - x) (by omega) ?_
  rw [show x + (3 * k - x) = k + 1 * (2 * k) by omega, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (by omega)]

include hk hX hsym in
/-- `C_U(ρ)` is unchanged under `ρ ↦ −ρ` (reflect in `z ↦ k − z`). -/
lemma cU_reflect {ρ : ℕ} (hρ : ρ < 2 * k) (hCU : CU k X ρ) : CU k X (2 * k - ρ) := by
  intro x hx hu1 hu2
  have hxk := hX x hx
  have hc1 := mod_two_k_cases (k := k) (a := 2 * k - ρ + x) (by omega)
  -- `y = k − x` modulo `2k`
  obtain ⟨y, hy, hyk, hyx⟩ : ∃ y, y ∈ X ∧ y < 2 * k ∧ (x < k ∧ y = k - x ∨ k < x ∧ y = 3 * k - x) := by
    rcases Nat.lt_or_ge x k with h | h
    · exact ⟨k - x, sym_lt hX hsym hx h, by omega, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨3 * k - x, sym_gt hX hsym hx (by omega), by omega, Or.inr ⟨by omega, rfl⟩⟩
  have hc2 := mod_two_k_cases (k := k) (a := ρ + y) (by omega)
  have hv : (ρ + y) % (2 * k) = k - (2 * k - ρ + x) % (2 * k) := by omega
  have hvX := hCU y hy (by omega) (by omega)
  rw [hv] at hvX
  refine hsym _ hvX _ (by omega) ?_
  rw [show k - (2 * k - ρ + x) % (2 * k) + (2 * k - ρ + x) % (2 * k) = k by omega]
  exact Nat.mod_eq_of_lt (by omega)

include hk hX hsym in
/-- `C_V(ρ')` is unchanged under `ρ' ↦ −ρ'`. -/
lemma cV_reflect {ρ' : ℕ} (hρ' : ρ' < 2 * k) (hCV : CV k X ρ') : CV k X (2 * k - ρ') := by
  intro x hx hv1 hv2
  have hxk := hX x hx
  have hc1 := mod_two_k_cases (k := k) (a := 2 * k - ρ' + x) (by omega)
  obtain ⟨y, hy, hyk, hyx⟩ : ∃ y, y ∈ X ∧ y < 2 * k ∧ (x < k ∧ y = k - x ∨ k < x ∧ y = 3 * k - x) := by
    rcases Nat.lt_or_ge x k with h | h
    · exact ⟨k - x, sym_lt hX hsym hx h, by omega, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨3 * k - x, sym_gt hX hsym hx (by omega), by omega, Or.inr ⟨by omega, rfl⟩⟩
  have hc2 := mod_two_k_cases (k := k) (a := ρ' + y) (by omega)
  have hv : (ρ' + y) % (2 * k) = 3 * k - (2 * k - ρ' + x) % (2 * k) := by omega
  have hvX := hCV y hy (by omega) (by omega)
  rw [hv] at hvX
  refine hsym _ hvX _ (by omega) ?_
  rw [show 3 * k - (2 * k - ρ' + x) % (2 * k) + (2 * k - ρ' + x) % (2 * k) = k + 1 * (2 * k) by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

include hk hX hsym in
/-- The paper's (G1)–(G4) for `0 < ρ, ρ' < k`. -/
lemma data (hU : ∃ x ∈ X, x < k) (hV : ∃ x ∈ X, k < x)
    {ρ ρ' : ℕ} (hρ : ρ % 2 = 0) (hρ0 : 0 < ρ) (hρk : ρ < k)
    (hρ' : ρ' % 2 = 0) (hρ'0 : 0 < ρ') (hρ'k : ρ' < k)
    (hCU : CU k X ρ) (hCV : CV k X ρ') : Data k ρ ρ' (PX k X) (MX k X) where
  hk := hk
  hρ := hρ
  hρ' := hρ'
  hρ0 := hρ0
  hρ'0 := hρ'0
  hρk := hρk
  hρ'k := hρ'k
  hP := fun z hz => ⟨hz.2, (hX z hz.1).2⟩
  hM := fun z hz => ⟨hz.2, by have := (hX _ hz.1).2; omega⟩
  hPs := fun z hz => ⟨sym_lt hX hsym hz.1 hz.2, by have := hX z hz.1; omega⟩
  hMs := fun z hz => by
    obtain ⟨hz1, hz2⟩ := hz
    have hz3 := hX _ hz1
    have := sym_gt hX hsym hz1 (by omega)
    exact ⟨by rw [show k - z + k = 3 * k - (z + k) by omega]; exact this, by omega⟩
  hPne := by obtain ⟨x, hx, hxk⟩ := hU; exact ⟨x, hx, hxk⟩
  hMne := by
    obtain ⟨x, hx, hxk⟩ := hV
    exact ⟨x - k, by rw [show x - k + k = x by omega]; exact hx, by have := hX x hx; omega⟩
  f1 := fun p hp hlt => by
    have := hCU p hp.1
    rw [Nat.mod_eq_of_lt (by omega)] at this
    exact ⟨by rw [add_comm]; exact this (by omega) (by omega), hlt⟩
  f2 := fun m hm hlt => by
    have hm3 := hX _ hm.1
    have h1 := sym_gt hX hsym hm.1 (by omega)
    have h2 := hCU _ h1
    rw [show ρ + (3 * k - (m + k)) = (ρ - m) + 1 * (2 * k) by omega, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by omega)] at h2
    exact ⟨h2 (by omega) (by omega), by omega⟩
  f4 := fun m hm hlt => by
    have := hCV _ hm.1
    rw [Nat.mod_eq_of_lt (by omega)] at this
    exact ⟨by rw [show m + ρ' + k = ρ' + (m + k) by ring]; exact this (by omega) (by omega), hlt⟩
  f5 := fun p hp hlt => by
    have h1 := sym_lt hX hsym hp.1 hp.2
    have h2 := hCV _ h1
    have hp1 := hX p hp.1
    rw [Nat.mod_eq_of_lt (by omega)] at h2
    exact ⟨by rw [show ρ' - p + k = ρ' + (k - p) by omega]; exact h2 (by omega) (by omega), by omega⟩

/-- Swapping the roles of `P` and `M` in the conclusion of `Data.core`. -/
lemma swap_core {P M : ℕ → Prop} {k c g : ℕ} (hg : g ∣ 2 * k)
    (hz : ∀ z, z < k → z % 2 = 1 → (z ≡ c [MOD g] → M z) ∧ (z + k ≡ c [MOD g] → P z)) :
    ∀ z, z < k → z % 2 = 1 → (z ≡ c + k [MOD g] → P z) ∧ (z + k ≡ c + k [MOD g] → M z) := by
  intro z hzk hodd
  refine ⟨fun h => (hz z hzk hodd).2 ?_, fun h => (hz z hzk hodd).1 (Nat.ModEq.add_right_cancel' k h)⟩
  refine (h.add_right k).trans ?_
  rw [add_assoc, show k + k = 2 * k by ring]
  exact Nat.ModEq.of_dvd hg Nat.add_modEq_right

include hk in
/-- Reading the coset off the conclusion of `Data.core`. -/
lemma coset_of_core (hk0 : 0 < k) {c g : ℕ} (hg : g ∣ 2 * k) (hg2 : g % 2 = 0) (hc : c % 2 = 1)
    (hz : ∀ z, z < k → z % 2 = 1 → (z ≡ c [MOD g] → PX k X z) ∧ (z + k ≡ c [MOD g] → MX k X z)) :
    ∀ t, (c + t * g) % (2 * k) ∈ X := by
  intro t
  have hw : (c + t * g) % (2 * k) < 2 * k := Nat.mod_lt _ (by omega)
  have hodd : (c + t * g) % (2 * k) % 2 = 1 := by
    rw [mod_parity (by omega)]
    have : t * g % 2 = 0 := Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero hg2) t)
    omega
  have hmod : (c + t * g) % (2 * k) ≡ c [MOD g] := by
    refine ((Nat.mod_modEq _ _).of_dvd hg).trans ?_
    unfold Nat.ModEq; exact Nat.add_mul_mod_self_right c t g
  rcases Nat.lt_or_ge ((c + t * g) % (2 * k)) k with h | h
  · exact ((hz _ h hodd).1 hmod).1
  · have h' := (hz ((c + t * g) % (2 * k) - k) (by omega) (by omega)).2
      (by rw [show (c + t * g) % (2 * k) - k + k = (c + t * g) % (2 * k) by omega]; exact hmod)
    have h'' := h'.1
    rw [show (c + t * g) % (2 * k) - k + k = (c + t * g) % (2 * k) by omega] at h''
    exact h''

end Main


/-! ## The theorem -/

/-- **`lem:allodd-cosetfail`** (two complementary failures force a coset).  Let `k` be even and `X`
(the paper's `Φ`) a set of odd residues modulo `2k` (elements `< 2k`), symmetric under `x ↦ k − x`
(`hsym`: if `x ∈ X` and `x + y ≡ k (mod 2k)` then `y ∈ X`), meeting `U = (0, k)` and `V = (k, 2k)`.
Let `ρ, ρ'` (the paper's `φ, φ'`) be even residues outside `{0, k}`, and suppose `C_U(ρ)`:
`(ρ + X) ∩ U ⊆ X` and `C_V(ρ')`: `(ρ' + X) ∩ V ⊆ X`.  Then `X` contains a coset `c + gℤ/2kℤ` of a
nontrivial subgroup: `g ∣ 2k`, `0 < g < 2k`, and `c + t·g mod 2k ∈ X` for every `t`.  (In fact
`g = gcd (gcd ρ ρ') (2k)` and `c ∈ X`.) -/
theorem cosetfail {k : ℕ} {X : Finset ℕ} (hk : k % 2 = 0)
    (hX : ∀ x ∈ X, x < 2 * k ∧ x % 2 = 1)
    (hsym : ∀ x ∈ X, ∀ y, y < 2 * k → (x + y) % (2 * k) = k → y ∈ X)
    (hU : ∃ x ∈ X, x < k) (hV : ∃ x ∈ X, k < x)
    {ρ ρ' : ℕ} (hρ : ρ % 2 = 0) (hρ0 : 0 < ρ) (hρk : ρ ≠ k) (hρ2k : ρ < 2 * k)
    (hρ' : ρ' % 2 = 0) (hρ'0 : 0 < ρ') (hρ'k : ρ' ≠ k) (hρ'2k : ρ' < 2 * k)
    (hCU : ∀ x ∈ X, 0 < (ρ + x) % (2 * k) → (ρ + x) % (2 * k) < k → (ρ + x) % (2 * k) ∈ X)
    (hCV : ∀ x ∈ X, k < (ρ' + x) % (2 * k) → (ρ' + x) % (2 * k) < 2 * k →
      (ρ' + x) % (2 * k) ∈ X) :
    ∃ c g, g ∣ 2 * k ∧ 0 < g ∧ g < 2 * k ∧ ∀ t, (c + t * g) % (2 * k) ∈ X := by
  have hk0 : 0 < k := by obtain ⟨x, hx, hxk⟩ := hU; omega
  -- reflect `ρ` and `ρ'` into `(0, k)`
  obtain ⟨ρ₁, h1, h2, h3, hCU₁⟩ : ∃ ρ₁, ρ₁ % 2 = 0 ∧ 0 < ρ₁ ∧ ρ₁ < k ∧ CU k X ρ₁ := by
    rcases Nat.lt_or_ge ρ k with h | h
    · exact ⟨ρ, hρ, hρ0, h, hCU⟩
    · exact ⟨2 * k - ρ, by omega, by omega, by omega, cU_reflect hk hX hsym hρ2k hCU⟩
  obtain ⟨ρ'₁, h1', h2', h3', hCV₁⟩ : ∃ ρ'₁, ρ'₁ % 2 = 0 ∧ 0 < ρ'₁ ∧ ρ'₁ < k ∧ CV k X ρ'₁ := by
    rcases Nat.lt_or_ge ρ' k with h | h
    · exact ⟨ρ', hρ', hρ'0, h, hCV⟩
    · exact ⟨2 * k - ρ', by omega, by omega, by omega, cV_reflect hk hX hsym hρ'2k hCV⟩
  have hD := data hk hX hsym hU hV h1 h2 h3 h1' h2' h3' hCU₁ hCV₁
  rcases le_or_gt ρ₁ ρ'₁ with hle | hlt
  · obtain ⟨c, g, hg, hg0, hg2k, hg2, hc, hz⟩ := hD.core hle
    exact ⟨c, g, hg, hg0, hg2k, coset_of_core hk hk0 hg hg2 hc hz⟩
  · obtain ⟨c, g, hg, hg0, hg2k, hg2, hc, hz⟩ := hD.swap.core hlt.le
    exact ⟨c + k, g, hg, hg0, hg2k, coset_of_core hk hk0 hg hg2 (by omega) (swap_core hg hz)⟩


end CosetFail
end Bump
end Trop
end PeriodicDifference


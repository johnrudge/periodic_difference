/-
# `PeriodicDifference/APLemmaData.lean` — `thm:lemmaA`: the finite certificate and its soundness

The finite data of `prop:lemmaA-finite` is stored as flat `List ℕ` literals (integers zig-zag
encoded, `decZ`) — long `List ℤ` literals elaborate far too slowly — and parsed by the kernel:

* the chord table (C1), grouped by `g` (`CE`, `parseCE`), checked once by `ceCheck` and
  `complete`;
* the Jacobsthal values (C2), pairs `(n, J)` with `JacOK n J` (`jacCheck`).

There is no per-order data.  For `g ∣ 2k` the Jacobsthal value is looked up in (C2) at the
product `n` of the primes of `2k` not dividing `g` (`lookupJ`, recognised by `coprimePart`).
The per-order check (C3) is `orderOK`: either `J(2k)` satisfies `178 J² ≤ 10 k` and
`1699 J < 10 k`, so that the argument of `prop:lemmaA-tail` applies (`jacRoute`), or every
table entry passing Hermite's test passes the chord condition (i) of (C3) or has all its lattice
classes settled (ii), each class by an exclusion or by a witness `d < 100` found by search
(`clsOne`).  `cert_all` turns `perK` into `Cert k g p q` at every direction that can carry a
shortest vector.
-/
import PeriodicDifference.APLemmaCert
import PeriodicDifference.APLemmaChordCheck

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

/-- Zig-zag decoding `0, 1, 2, 3, 4, … ↦ 0, −1, 1, −2, 2, …`. -/
def decZ (n : ℕ) : ℤ := if n % 2 = 0 then ((n/2 : ℕ) : ℤ) else -(((n+1)/2 : ℕ) : ℤ)

/-- A chord-table entry of a fixed `g`: direction `(p,q)`, witness `(j, t, (m,n), a₀/b₀, a₁/b₁)`. -/
structure CE where
  p : ℤ
  q : ℤ
  j : ℤ
  t : ℕ
  m : ℤ
  n : ℤ
  a₀ : ℤ
  b₀ : ℤ
  a₁ : ℤ
  b₁ : ℤ

def parseCE : List ℕ → List CE
  | p::q::j::t::m::n::a₀::b₀::a₁::b₁::rest =>
      ⟨decZ p, decZ q, decZ j, t, decZ m, decZ n, decZ a₀, decZ b₀, decZ a₁, decZ b₁⟩ :: parseCE rest
  | _ => []

def parsePairs : List ℕ → List (ℕ × ℕ)
  | a::b::rest => (a, b) :: parsePairs rest
  | _ => []

def parseQuads : List ℕ → List (ℕ × ℕ × ℕ × ℕ)
  | a::b::c::d::rest => (a, b, c, d) :: parseQuads rest
  | _ => []

/-- Validity of one chord-table entry. -/
def ceCheck (g : ℕ) (e : CE) : Bool :=
  chordCheck g e.p e.q e.j e.t e.m e.n e.a₀ e.b₀ e.a₁ e.b₁ && Int.gcd e.j g == 1

theorem ceCheck_sound {g : ℕ} {e : CE} (h : ceCheck g e = true) :
    ChordOK g e.p e.q e.j e.t e.m e.n ((e.a₀:ℚ)/e.b₀) ((e.a₁:ℚ)/e.b₁) ∧ IsCoprime e.j (g:ℤ) := by
  simp only [ceCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨chordOK_of_check h.1, Int.isCoprime_iff_gcd_eq_one.2 h.2⟩

/-- Hermite's test `3 (g²|u|²)² ≤ 16 k²`. -/
def herm (k g : ℕ) (e : CE) : Bool := decide (3*((g:ℤ)^2*(e.p^2+e.q^2))^2 ≤ 16*(k:ℤ)^2)

/-- Condition (B): `2k σ > J g`, `σ = a₁/b₁ − a₀/b₀`. -/
def passB (k g J : ℕ) (e : CE) : Bool :=
  decide ((J:ℤ)*g*(e.b₀*e.b₁) < 2*k*(e.a₁*e.b₀ - e.a₀*e.b₁))

/-- `d` witnesses `Good k A E`. -/
def goodCheck (k : ℕ) (A E d : ℤ) : Bool :=
  Int.gcd d (2*k) == 1 &&
  (decide ((d*(A-E)) % (2*k) < k) == decide ((d*A) % (2*k) < k)) &&
  (decide ((d*(A+E)) % (2*k) < k) == !decide ((d*A) % (2*k) < k))

theorem goodCheck_sound {k : ℕ} {A E d : ℤ} (h : goodCheck k A E d = true) : Good k A E := by
  simp only [goodCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨d, h1, ?_, ?_⟩
  · simpa using h2
  · by_cases u : (d*(A+E)) % (2*k) < k <;> by_cases v : (d*A) % (2*k) < k <;> simp_all

/-- One class `(s,t)` of `(g, p, q)` at order `k`: an exclusion (some `0 < m < g` with
`2k ∣ m(pE − qA)`, or `gcd(A, E, 2k) > 1`) or a witness `d < 100`. -/
def clsOne (k g : ℕ) (p q : ℤ) (s t : ℕ) : Bool :=
  (List.range g).any (fun m => decide (0 < m) &&
    decide ((2*k:ℤ) ∣ (m*p)*(q + (2*k/g)*t) - (m*q)*(p + (2*k/g)*s))) ||
  Int.gcd (Int.gcd (p + (2*k/g)*s) (q + (2*k/g)*t)) (2*k) != 1 ||
  (List.range 100).any fun d => goodCheck k (p + (2*k/g)*s) (q + (2*k/g)*t) d

theorem clsOne_sound {k g : ℕ} {p q : ℤ} {s t : ℕ} (h : clsOne k g p q s t = true) :
    ClassOK k g p q s t := by
  simp only [clsOne, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  rcases h with (⟨m, hm, hm0, hdvd⟩ | h) | ⟨d, -, hd⟩
  · right; left
    refine ⟨m, by exact_mod_cast hm0, by exact_mod_cast hm, ?_⟩
    unfold Mem; exact hdvd
  · right; right; exact h
  · left; exact goodCheck_sound hd

/-- All `g²` classes of `(g, p, q)` at order `k`. -/
def clsAll (k g : ℕ) (p q : ℤ) : Bool :=
  (List.range g).all fun s => (List.range g).all fun t => clsOne k g p q s t

theorem clsAll_sound {k g : ℕ} {p q : ℤ} (h : clsAll k g p q = true) :
    ∀ s t : ℤ, 0 ≤ s → s < g → 0 ≤ t → t < g → ClassOK k g p q s t := by
  intro s t hs0 hs ht0 ht
  simp only [clsAll, List.all_eq_true, List.mem_range] at h
  have := clsOne_sound (h s.toNat (by omega) t.toNat (by omega))
  rwa [Int.toNat_of_nonneg hs0, Int.toNat_of_nonneg ht0] at this

/-- The part of `n` prime to `c`: `gcd(n, c)` is divided out while it exceeds `1`, at most
`f` times. -/
def coprimePart : ℕ → ℕ → ℕ → ℕ
  | 0, n, _ => n
  | f + 1, n, c => if Nat.gcd n c = 1 then n else coprimePart f (n / Nat.gcd n c) c

/-- If the part of `n` prime to `c` is `1`, every prime factor of `n` divides `c`. -/
theorem dvd_of_coprimePart : ∀ (f n c : ℕ), coprimePart f n c = 1 →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ∣ c
  | 0, n, c, h, ℓ, hℓ, hd => by
    simp only [coprimePart] at h
    subst h; exact absurd (Nat.le_of_dvd one_pos hd) (by have := hℓ.two_le; omega)
  | f + 1, n, c, h, ℓ, hℓ, hd => by
    simp only [coprimePart] at h
    split_ifs at h with h1
    · subst h; exact absurd (Nat.le_of_dvd one_pos hd) (by have := hℓ.two_le; omega)
    · by_cases hℓg : ℓ ∣ Nat.gcd n c
      · exact hℓg.trans (Nat.gcd_dvd_right _ _)
      · refine dvd_of_coprimePart f _ c h ℓ hℓ ?_
        rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_left n c)] at hd
        exact (hℓ.dvd_mul.mp hd).resolve_left hℓg

/-- The Jacobsthal value for `g` at order `k`: that of the entry `(n, J)` of `JT` with
`n ∣ 2k`, `gcd(n, g) = 1` and every prime of `2k` dividing `n g`. -/
def lookupJ (JT : List (ℕ × ℕ)) (k g : ℕ) : Option ℕ :=
  (JT.find? fun x => (2*k) % x.1 == 0 && Nat.gcd x.1 g == 1 &&
    coprimePart (2*k) (2*k) (x.1*g) == 1).map (·.2)

theorem jac_of_lookup {JT : List (ℕ × ℕ)} {k g J : ℕ}
    (hJT : ∀ x ∈ JT, JacOK x.1 x.2) (h : lookupJ JT k g = some J) :
    ∃ nn : ℕ, JacOK nn J ∧ nn ∣ 2*k ∧ Nat.Coprime nn g ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2*k → ℓ ∣ nn ∨ ℓ ∣ g) := by
  unfold lookupJ at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  have hmem := List.mem_of_find?_eq_some hx
  have hp := List.find?_some hx
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨hdvd, hgcd⟩, hcov⟩ := hp
  refine ⟨x.1, hJT x hmem, Nat.dvd_of_mod_eq_zero hdvd, hgcd, fun ℓ hℓ hℓk => ?_⟩
  exact (Nat.Prime.dvd_mul hℓ).1 (dvd_of_coprimePart _ _ _ hcov ℓ hℓ hℓk)

def entryOK (k g : ℕ) (o : Option ℕ) (e : CE) : Bool :=
  !herm k g e ||
  (match o with
   | some J => passB k g J e
   | none => false) ||
  clsAll k g e.p e.q

/-- The per-entry part of (C3) at order `k`. -/
def perK (JT : List (ℕ × ℕ)) (CT : List (ℕ × List CE)) (k : ℕ) : Bool :=
  CT.all fun ge => (2*k) % ge.1 != 0 || ge.2.all (entryOK k ge.1 (lookupJ JT k ge.1))

/-- The Jacobsthal route: `J(2k)` from `JT` satisfies `178 J² ≤ 10 k` and `1699 J < 10 k`. -/
def jacRoute (JT : List (ℕ × ℕ)) (k : ℕ) : Bool :=
  match lookupJ JT k 1 with
  | some J => decide (178*J^2 ≤ 10*k) && decide (1699*J < 10*k)
  | none => false

/-- The per-order certificate (C3). -/
def orderOK (JT : List (ℕ × ℕ)) (CT : List (ℕ × List CE)) (k : ℕ) : Bool :=
  jacRoute JT k || perK JT CT k

/-- Soundness of `perK`: every table entry passing Hermite's test at a `g ∣ 2k` is certified. -/
theorem cert_of_perK {JT : List (ℕ × ℕ)} {CT : List (ℕ × List CE)} {k : ℕ}
    (hJT : ∀ x ∈ JT, JacOK x.1 x.2) (hCT : ∀ ge ∈ CT, ∀ e ∈ ge.2, ceCheck ge.1 e = true)
    (h : perK JT CT k = true) :
    ∀ ge ∈ CT, ∀ e ∈ ge.2, (ge.1 : ℤ) ∣ 2*k →
      3*((ge.1:ℤ)^2*(e.p^2+e.q^2))^2 ≤ 16*(k:ℤ)^2 → Cert k ge.1 e.p e.q := by
  intro ge hge e he hdvd hH
  simp only [perK, List.all_eq_true] at h
  have h1 := h ge hge
  have hmod : (2*k) % ge.1 = 0 := Nat.mod_eq_zero_of_dvd (by exact_mod_cast hdvd)
  rw [hmod] at h1
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at h1
  have h2 := h1 e he
  have hH' : herm k ge.1 e = true := by simp only [herm, decide_eq_true_eq]; exact hH
  simp only [entryOK, hH', Bool.not_true, Bool.false_or, Bool.or_eq_true] at h2
  obtain ⟨hc, hj⟩ := ceCheck_sound (hCT ge hge e he)
  rcases h2 with h2 | h2
  · -- condition (B)
    split at h2
    · rename_i J hJ
      obtain ⟨nn, hJac, hnn, hng, hcov⟩ := jac_of_lookup hJT hJ
      left
      refine ⟨e.j, e.t, e.m, e.n, _, _, nn, J, hj, hc, hJac, by exact_mod_cast hnn,
        Int.isCoprime_iff_gcd_eq_one.2 (by rw [Int.gcd_natCast_natCast]; exact hng),
        fun ℓ hℓ hℓk => ?_, ?_⟩
      · rcases hcov ℓ hℓ (by exact_mod_cast hℓk) with h | h
        · left; exact_mod_cast h
        · right; exact_mod_cast h
      have hb₀ : 0 < e.b₀ := by
        simp only [ceCheck, chordCheck, Bool.and_eq_true, decide_eq_true_eq] at hCT
        exact (hCT ge hge e he).1.1.1.2
      have hb₁ : 0 < e.b₁ := by
        simp only [ceCheck, chordCheck, Bool.and_eq_true, decide_eq_true_eq] at hCT
        exact (hCT ge hge e he).1.1.2
      simp only [passB, decide_eq_true_eq] at h2
      have hb₀' : (0:ℚ) < e.b₀ := by exact_mod_cast hb₀
      have hb₁' : (0:ℚ) < e.b₁ := by exact_mod_cast hb₁
      have h3 : ((J:ℤ)*ge.1*(e.b₀*e.b₁) : ℚ) < (2*k*(e.a₁*e.b₀ - e.a₀*e.b₁) : ℤ) := by
        exact_mod_cast h2
      rw [div_sub_div _ _ hb₁'.ne' hb₀'.ne', mul_div_assoc', lt_div_iff₀ (by positivity)]
      push_cast at h3 ⊢
      linarith
    · exact absurd h2 (by simp)
  · -- the classes of a failing entry
    exact Or.inr (clsAll_sound h2)

/-- The admissible directions of a given `g` with `g²|u|² ≤ 6400`, in table order. -/
def dirOK (g : ℕ) (p q : ℤ) : Bool :=
  (decide (0 < p) || (p == 0 && decide (0 < q))) && Int.gcd p q == 1 && (g*q) % 2 == 0 &&
  decide ((g:ℤ)^2*(p^2+q^2) ≤ 6400) &&
  !((g == 1 && p == 1 && q == 0) || (g == 1 && p == 1 && q == 2) || (g == 2 && p == 0 && q == 1) ||
    (g == 2 && p == 1 && q == 0) || (g == 2 && p == 1 && q == 1) || (g == 2 && p == 1 && q == -1) ||
    (g == 2 && p == 1 && q == -2) || (g == 4 && p == 0 && q == 1))

def cands (g : ℕ) : List (ℤ × ℤ) :=
  ((List.range (80/g+1)).flatMap fun (p : ℕ) =>
    (List.range (2*(80/g)+1)).map fun (i : ℕ) => ((p:ℤ), (i:ℤ) - ((80/g : ℕ) : ℤ))).filter
    fun pq => dirOK g pq.1 pq.2

/-- The table lists exactly the admissible directions, for `g = 1, …, 80`. -/
def complete (CT : List (ℕ × List CE)) : Bool :=
  CT.map (·.1) == List.range' 1 80 && CT.all fun ge => ge.2.map (fun e => (e.p, e.q)) == cands ge.1

theorem mem_cands {g : ℕ} {p q : ℤ} (hg : 0 < g) (h : dirOK g p q = true) : (p, q) ∈ cands g := by
  unfold cands
  rw [List.mem_filter]
  refine ⟨?_, h⟩
  simp only [dirOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hn, -⟩, -⟩, hU⟩, -⟩ := h
  have hp0 : 0 ≤ p := by rcases hn with h0 | h0 <;> omega
  have hg' : (1:ℤ) ≤ g := by exact_mod_cast hg
  have hgp : (g:ℤ)*p ≤ 80 := by nlinarith
  have hgq : (g:ℤ)*|q| ≤ 80 := by
    have : (g:ℤ)^2*q^2 ≤ 6400 := by nlinarith
    have h2 : ((g:ℤ)*|q|)^2 ≤ 80^2 := by rw [mul_pow, sq_abs]; linarith
    nlinarith [abs_nonneg q]
  have hdiv : ((80/g : ℕ) : ℤ) = 80 / (g:ℤ) := by push_cast; rfl
  have hp80 : p ≤ ((80/g : ℕ) : ℤ) := by
    rw [hdiv, Int.le_ediv_iff_mul_le (by omega)]; linarith
  have hq80 : |q| ≤ ((80/g : ℕ) : ℤ) := by
    rw [hdiv, Int.le_ediv_iff_mul_le (by omega)]; linarith
  rw [List.mem_flatMap]
  refine ⟨p.toNat, ?_, ?_⟩
  · rw [List.mem_range]; omega
  · rw [List.mem_map]
    refine ⟨(q + ((80/g : ℕ) : ℤ)).toNat, ?_, ?_⟩
    · rw [List.mem_range]; rw [abs_le] at hq80; omega
    · rw [abs_le] at hq80; simp only [Prod.mk.injEq]; omega

/-- Every admissible direction with `g²|u|² ≤ 6400` is an entry of a complete table. -/
theorem exists_entry {CT : List (ℕ × List CE)} (hcomp : complete CT = true) {g p q : ℤ}
    (hg : 0 < g) (hn : 0 < p ∨ (p = 0 ∧ 0 < q)) (hpq : IsCoprime p q) (h2 : 2 ∣ g*q)
    (hX : g^2*(p^2+q^2) ≤ 6400) (hz : ¬ ZeroEntry g p q) :
    ∃ ge ∈ CT, ∃ e ∈ ge.2, (ge.1:ℤ) = g ∧ e.p = p ∧ e.q = q := by
  have hU : 1 ≤ p^2 + q^2 := by rcases hn with h0 | ⟨_, h0⟩ <;> nlinarith
  set G := g.toNat with hG
  have hGg : (G:ℤ) = g := Int.toNat_of_nonneg hg.le
  have hG80 : G ∈ List.range' 1 80 := by
    rw [List.mem_range']; have : g ≤ 80 := by nlinarith
    refine ⟨G - 1, by omega, by omega⟩
  have hdir : dirOK G p q = true := by
    have hzb : (!((G == 1 && p == 1 && q == 0) || (G == 1 && p == 1 && q == 2) ||
        (G == 2 && p == 0 && q == 1) || (G == 2 && p == 1 && q == 0) ||
        (G == 2 && p == 1 && q == 1) || (G == 2 && p == 1 && q == -1) ||
        (G == 2 && p == 1 && q == -2) || (G == 4 && p == 0 && q == 1))) = true := by
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      intro hb; apply hz
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hb
      rcases hb with (((((((h|h)|h)|h)|h)|h)|h)|h) <;> obtain ⟨⟨h1, h2⟩, h3⟩ := h <;>
        (unfold ZeroEntry; rw [← hGg, h1, h2, h3]; norm_num)
    unfold dirOK
    rw [hzb, Bool.and_true]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, hGg]
    refine ⟨⟨⟨?_, Int.isCoprime_iff_gcd_eq_one.1 hpq⟩, ?_⟩, hX⟩
    · rcases hn with h0 | ⟨h0, h1⟩
      · exact Or.inl h0
      · exact Or.inr ⟨h0, h1⟩
    · omega
  simp only [complete, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcomp
  obtain ⟨hmap, hall⟩ := hcomp
  rw [← hmap, List.mem_map] at hG80
  obtain ⟨ge, hge, hge1⟩ := hG80
  have hmem := mem_cands (show 0 < G by omega) hdir
  rw [← hge1, ← hall ge hge, List.mem_map] at hmem
  obtain ⟨e, he, hpq'⟩ := hmem
  simp only [Prod.mk.injEq] at hpq'
  exact ⟨ge, hge, e, he, by rw [hge1, hGg], hpq'.1, hpq'.2⟩

/-- **(C3)(i)–(ii) are sound**: at `k ≤ 2730`, `perK` certifies every direction that can carry
a shortest vector. -/
theorem cert_all {JT : List (ℕ × ℕ)} {CT : List (ℕ × List CE)} {k : ℕ}
    (hJT : ∀ x ∈ JT, JacOK x.1 x.2) (hCT : ∀ ge ∈ CT, ∀ e ∈ ge.2, ceCheck ge.1 e = true)
    (hcomp : complete CT = true) (hk : k ≤ 2730) (h : perK JT CT k = true) :
    ∀ g p q : ℤ, 0 < g → g ∣ 2*k → (0 < p ∨ (p = 0 ∧ 0 < q)) → IsCoprime p q →
      2 ∣ g*q → 3*(g^2*(p^2+q^2))^2 ≤ 16*k^2 → ¬ ZeroEntry g p q → Cert k g p q := by
  intro g p q hg hgk hn hpq h2 hH hz
  have hX : g^2*(p^2+q^2) ≤ 6400 := by
    have : (k:ℤ) ≤ 2730 := by exact_mod_cast hk
    have : 3*(g^2*(p^2+q^2))^2 ≤ 16*2730^2 := by nlinarith
    nlinarith [sq_nonneg (g^2*(p^2+q^2) - 6401)]
  obtain ⟨ge, hge, e, he, hg', hp', hq'⟩ := exists_entry hcomp hg hn hpq h2 hX hz
  have := cert_of_perK hJT hCT h ge hge e he
  rw [hp', hq', hg'] at this
  exact this hgk hH

end APLemma
end Bump
end Trop
end PeriodicDifference

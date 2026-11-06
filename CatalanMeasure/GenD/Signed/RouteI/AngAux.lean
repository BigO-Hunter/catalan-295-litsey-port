module

public import CatalanMeasure.GenD.Signed.RouteI.AngularCap
public import CatalanMeasure.GenD.Signed.RouteI.CapSourceData
public import CatalanMeasure.GenD.Signed.RouteI.KronSquare
public import CatalanMeasure.GenD.Signed.RouteI.MomentInputs
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section
set_option Elab.async false

/-!
# Route I `AngAux`: the auxiliary side of `AngRadiusCert`, for every species and radius index

Generalises the auxiliary part of `AngPilot` (positive species, radius index 1) to any sign and any
radius index, with no constant of the source hard-coded. `auxA_eq` writes the true coefficient as a
sum over `ns σ` geometric streams (`16` ratio streams, and for the negative species `16` reflection
streams, sharing the same class sums). The checks split in two: `AuxSharedOK` is radius free and
holds once per species, `AuxRadOK` holds per radius. `hA_bound`, `tail_bound` give the fields `hA`,
`hT` of `AngularCap.AngRadiusCert`, and `angRadius_of_data` assembles a certificate from a gas part.

No sorry, no native_decide, no new axioms.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.AngAux
open CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MomentInputs

noncomputable section

/-! ### exp enclosure -/
open Nat in

def expS (s : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => expS s n + s ^ n / (n.factorial : ℚ)

theorem expS_cast (s : ℚ) (N : ℕ) : (expS s N : ℝ) = ∑ i ∈ Finset.range N, (s : ℝ) ^ i / (i.factorial : ℝ) := by
  induction N with
  | zero => simp [expS]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; simp [expS]

def expLoQ (t : ℚ) (N : ℕ) : ℚ :=
  (1 / (expS (t / 8) N + (t / 8) ^ N * (N + 1) / ((N.factorial : ℚ) * N))) ^ 8
def expHiQ (t : ℚ) (N : ℕ) : ℚ := (1 / expS (t / 8) N) ^ 8

theorem expQ_enc (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 8) (N : ℕ) (hN : 0 < N) :
    (expLoQ t N : ℝ) ≤ Real.exp (-(t : ℝ)) ∧ Real.exp (-(t : ℝ)) ≤ (expHiQ t N : ℝ) := by
  set s : ℝ := (t : ℝ) / 8 with hs
  have hs0 : 0 ≤ s := by rw [hs]; have : (0:ℝ) ≤ t := by exact_mod_cast ht0
                         positivity
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one (by norm_num)]; exact_mod_cast ht1
  have hlo : ∑ i ∈ Finset.range N, s ^ i / (i.factorial : ℝ) ≤ Real.exp s := Real.sum_le_exp_of_nonneg hs0 N
  have hhi := Real.exp_bound' hs0 hs1 hN
  have hE0 : 0 < ∑ i ∈ Finset.range N, s ^ i / (i.factorial : ℝ) := by
    obtain ⟨n', rfl⟩ : ∃ n', N = n' + 1 := ⟨N - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have : 0 ≤ ∑ i ∈ Finset.range n', s ^ (i + 1) / ((i + 1).factorial : ℝ) :=
      Finset.sum_nonneg fun i _ => by positivity
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    linarith
  have hexp : Real.exp (-(t : ℝ)) = (Real.exp s)⁻¹ ^ 8 := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1; rw [hs]; push_cast; ring
  have e1 : (expLoQ t N : ℝ) = (1 / (∑ i ∈ Finset.range N, s ^ i / (i.factorial : ℝ) +
      s ^ N * (N + 1) / ((N.factorial : ℝ) * N))) ^ 8 := by
    unfold expLoQ; push_cast; rw [expS_cast]; simp [hs]
  have e2 : (expHiQ t N : ℝ) = (1 / ∑ i ∈ Finset.range N, s ^ i / (i.factorial : ℝ)) ^ 8 := by
    unfold expHiQ; push_cast; rw [expS_cast]; simp [hs]
  rw [e1, e2, hexp]
  have hexp_pos := Real.exp_pos s
  constructor
  · apply pow_le_pow_left₀ (by positivity)
    rw [← one_div]
    exact one_div_le_one_div_of_le hexp_pos hhi
  · apply pow_le_pow_left₀ (by positivity)
    rw [one_div]
    exact inv_anti₀ hE0 hlo



open AngularSource in
theorem group_sum' {α : Type*} (L : List α) (c : α → ℕ) (N : ℕ) (hc : ∀ a ∈ L, c a < N) (F : ℕ → ℝ) (h : α → ℝ) :
    (L.map fun a => F (c a) * h a).sum =
      ∑ r ∈ Finset.range N, F r * (L.map fun a => if c a = r then h a else 0).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ih' := ih (fun b hb => hc b (by simp [hb]))
    have hca := hc a (by simp)
    simp only [List.map_cons, List.sum_cons]
    rw [ih']
    have : ∀ r ∈ Finset.range N, F r * ((if c a = r then h a else 0) + (L.map fun a => if c a = r then h a else 0).sum) =
        F r * (if c a = r then h a else 0) + F r * (L.map fun a => if c a = r then h a else 0).sum := fun r _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    congr 1
    simp [Finset.sum_ite_eq', hca]

/-! ### Species parameters -/
open CapSourceData

/-- number of power streams of a species: `16` ratio streams, plus `16` reflection streams for the
negative species. -/
def ns (σ : Sign) : ℕ := if σ = Sign.neg then 32 else 16

/-- the gas population of a species. -/
def gasT (σ : Sign) : List Tr := if σ = Sign.neg then gasNegT else gasPosT

/-- the mass budget of a species: `tgt σ = tgtB σ - m_σ`. -/
def tgtB (σ : Sign) : ℚ := if σ = Sign.neg then 53 / 58 else 1

/-- the tail factor of a species. -/
def tailF (σ : Sign) : ℚ := if σ = Sign.neg then 2 else 1

theorem tgt_val {σ : Sign} {Tt Sg : ℤ} (hT : sumP row0 = Tt) (hS : sumP (gasT σ) = Sg) :
    tgt σ = ((tgtB σ - (Sg : ℚ) / (Tt : ℚ) : ℚ) : ℝ) := by
  subst hT hS
  cases σ
  · show 53 / 58 - massL (gasCells Sign.neg) = _
    rw [massNeg]
    simp [gasT, tgtB]
  · show 1 - massL (gasCells _) = _
    rw [massPos]
    simp [gasT, tgtB]

theorem aux_ok (σ : Sign) : ∀ t ∈ auxT σ, 0 ≤ t.2.2 ∧ t.1 < 16 := by
  cases σ
  · exact na_ok
  · exact pa_ok

theorem aux_tot (σ : Sign) : 0 < sumP (auxT σ) := by
  cases σ
  · exact na_tot
  · exact pa_tot

theorem auxJ_ok (σ : Sign) : ∀ t ∈ auxT σ, 0 ≤ t.2.1 ∧ t.2.1 < 186 := by
  -- kcost: 1671 triples in all, two Int comparisons each: below 0.1 s.
  cases σ
  · show ∀ t ∈ naT, _
    decide +kernel
  · show ∀ t ∈ paT, _
    decide +kernel

theorem mkAux_fields {g : ℝ} {M : ℤ} {t : Tr} (hg : 0 ≤ g) (hM : 0 ≤ M) (h0 : 0 ≤ t.2.2) :
    (mkAux g M t).rad = t.1.toNat ∧ (mkAux g M t).phase = Real.pi * (t.2.1 : ℝ) / 93 ∧
      (mkAux g M t).w = g * (t.2.2 : ℝ) / (M : ℝ) := by
  have hh : 0 ≤ t.2.2 ∧ 0 ≤ M ∧ 0 ≤ g := ⟨h0, hM, hg⟩
  unfold mkAux
  rw [dif_pos hh]
  exact ⟨rfl, rfl, rfl⟩

/-! ### The streams and the class sums -/

/-- the geometric ratio of stream `s` at radius `i`: `s < 16` the ratio stream
`q rad(max i s) / rad(min i s)`, `s = 16 + r` the reflection stream `q rad i rad r`. -/
def tauS (i s : ℕ) : ℝ :=
  if s < 16 then capSource.q * (capSource.rad (max i s) / capSource.rad (min i s))
  else capSource.q * (capSource.rad i * capSource.rad (s - 16))

def Gk (k : ℕ) : ℝ := (1 + capSource.strength * k + capSource.curvature * (k : ℝ) ^ 2) / k

/-- class sums of the weighted cosines. -/
def Sr (σ : Sign) (r k : ℕ) : ℝ :=
  ((auxT σ).map fun t => if t.1.toNat = r then (tgt σ * (t.2.2 : ℝ) / (sumP (auxT σ) : ℝ)) *
    Real.cos ((k : ℝ) * (Real.pi * (t.2.1 : ℝ) / 93)) else 0).sum

theorem sum_streams (σ : Sign) (i k : ℕ) (f : ℕ → ℝ) :
    ∑ r ∈ Finset.range 16, (tauS i r ^ k + (if σ = Sign.neg then tauS i (16 + r) ^ k else 0)) * f r =
      ∑ s ∈ Finset.range (ns σ), tauS i s ^ k * f (s % 16) := by
  cases σ
  · show _ = ∑ s ∈ Finset.range (16 + 16), _
    rw [Finset.sum_range_add, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_range.1 hr
    have e1 : r % 16 = r := Nat.mod_eq_of_lt hr'
    have e2 : (16 + r) % 16 = r := by omega
    rw [e1, e2, if_pos rfl]
    ring
  · show _ = ∑ s ∈ Finset.range 16, _
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_range.1 hr
    rw [Nat.mod_eq_of_lt hr', if_neg (by decide), add_zero]

/-- **(X1)** the auxiliary Chebyshev coefficient as a sum over the streams of the species. -/
theorem auxA_eq (σ : Sign) (i k : ℕ) (hk : 1 ≤ k) :
    AngularCap.auxA capSource σ i k =
      -Gk k * ∑ s ∈ Finset.range (ns σ), tauS i s ^ k * Sr σ (s % 16) k := by
  have hk0 : k ≠ 0 := by omega
  have hMaux : (0 : ℤ) ≤ sumP (auxT σ) := (aux_tot σ).le
  have hgt : 0 ≤ tgt σ := tgt_nonneg _
  unfold AngularCap.auxA AngularSource.auxCoefHat
  simp only [hk0, if_false]
  show ((auxCells σ).map fun e => e.w * AngularSource.auxFun capSource σ i k e).sum = _
  unfold auxCells
  rw [List.map_map]
  have hterm : ∀ t ∈ auxT σ, ((fun e => e.w * AngularSource.auxFun capSource σ i k e) ∘
        mkAux (tgt σ) (sumP (auxT σ))) t =
      (fun r => -Gk k * (tauS i r ^ k + (if σ = Sign.neg then tauS i (16 + r) ^ k else 0))) t.1.toNat *
        ((tgt σ * (t.2.2 : ℝ) / (sumP (auxT σ) : ℝ)) *
          Real.cos ((k : ℝ) * (Real.pi * (t.2.1 : ℝ) / 93))) := by
    intro t ht
    obtain ⟨hp, hr⟩ := aux_ok σ t ht
    obtain ⟨f1, f2, f3⟩ := mkAux_fields hgt hMaux hp
    have hr' : t.1.toNat < 16 := by omega
    simp only [Function.comp_apply, AngularSource.auxFun, f1, f2, f3]
    have e1 : tauS i t.1.toNat = capSource.q *
        (capSource.rad (max i t.1.toNat) / capSource.rad (min i t.1.toNat)) := by
      unfold tauS; rw [if_pos hr']
    have e2 : tauS i (16 + t.1.toNat) = capSource.q * (capSource.rad i * capSource.rad t.1.toNat) := by
      unfold tauS
      rw [if_neg (by omega)]
      congr 3
      omega
    rw [e1, e2]
    unfold Gk CapFields.CapSource.coef
    have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    by_cases hσ : σ = Sign.neg
    · simp only [if_pos hσ, mul_pow]
      field_simp
    · simp only [if_neg hσ, mul_pow, add_zero]
      field_simp
  rw [List.map_congr_left hterm]
  have hcl : ∀ t ∈ auxT σ, t.1.toNat < 16 := fun t ht => by
    have := (aux_ok σ t ht).2; omega
  rw [group_sum' (auxT σ) (fun t => t.1.toNat) 16 hcl
    (fun r => -Gk k * (tauS i r ^ k + (if σ = Sign.neg then tauS i (16 + r) ^ k else 0)))
    (fun t => (tgt σ * (t.2.2 : ℝ) / (sumP (auxT σ) : ℝ)) * Real.cos ((k : ℝ) * (Real.pi * (t.2.1 : ℝ) / 93)))]
  rw [← sum_streams σ i k (fun r => Sr σ r k), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  unfold Sr
  ring

/-! ### Enclosures of `q`, `tau_s`, `strength`, `curvature` -/

def sigq (k : ℕ) : ℚ := (sigN.getD (min k 15) 0 : ℚ) / 10 ^ 17

/-- the rational radial field. -/
def radq (k : ℕ) : ℚ := (radN.getD (min k 15) 0 : ℚ) / 10 ^ 17

theorem sigma_eq (k : ℕ) : capSource.sigma k = (sigq k : ℝ) := by
  show (sigN.getD (min k 15) 0 : ℝ) / 10 ^ 17 = _
  unfold sigq; push_cast; rfl

theorem radial_eq (k : ℕ) : capSource.radial k = (radq k : ℝ) := by
  show (radN.getD (min k 15) 0 : ℝ) / 10 ^ 17 = _
  unfold radq; push_cast; rfl

theorem rad_eq (k : ℕ) : capSource.rad k = Real.exp (-(sigq k : ℝ)) := by
  show Real.exp (-capSource.sigma k) = _
  rw [sigma_eq]

theorem q_eq : capSource.q = Real.exp (-((27 / 500 : ℚ) : ℝ)) := by
  show Real.exp (-capSource.eps / 2) = _
  have : capSource.eps = 27 / 250 := rfl
  rw [this]; congr 1; push_cast; ring

theorem sigN_bd : ∀ n < 16, 0 ≤ sigN.getD n 0 ∧ sigN.getD n 0 ≤ 395 * 10 ^ 15 := by
  -- kcost: 16 comparisons of 18-digit integers: negligible.
  decide +kernel

theorem sigq_bd (k : ℕ) : 0 ≤ sigq k ∧ sigq k ≤ 395 / 100 := by
  obtain ⟨h0, h1⟩ := sigN_bd (min k 15) (by omega)
  unfold sigq
  have h0' : (0 : ℚ) ≤ (sigN.getD (min k 15) 0 : ℚ) := by exact_mod_cast h0
  have h1' : (sigN.getD (min k 15) 0 : ℚ) ≤ 395 * 10 ^ 15 := by exact_mod_cast h1
  constructor
  · positivity
  · rw [div_le_iff₀ (by norm_num)]
    linarith

theorem sigq_mono {a b : ℕ} (h : a ≤ b) : sigq a ≤ sigq b := by
  have := sigma_mono_thm h
  rw [sigma_eq, sigma_eq] at this
  exact_mod_cast this

/-- exponent of `tau_s`. -/
def tq (i s : ℕ) : ℚ :=
  if s < 16 then 27 / 500 + (sigq (max i s) - sigq (min i s))
  else 27 / 500 + (sigq i + sigq (s - 16))

theorem tauS_eq (i s : ℕ) : tauS i s = Real.exp (-(tq i s : ℝ)) := by
  unfold tauS tq
  split_ifs
  · rw [q_eq, rad_eq, rad_eq, ← Real.exp_sub, ← Real.exp_add]
    congr 1
    push_cast; ring
  · rw [q_eq, rad_eq, rad_eq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast; ring

theorem tq_range (i s : ℕ) : 0 ≤ tq i s ∧ tq i s ≤ 8 := by
  unfold tq
  have a1 := sigq_bd i
  have a2 := sigq_bd (s - 16)
  have a3 := sigq_bd (max i s)
  have a4 := sigq_bd (min i s)
  have a5 : sigq (min i s) ≤ sigq (max i s) := sigq_mono min_le_max
  split_ifs <;> constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]

theorem tauS_enc (i s : ℕ) (N : ℕ) (hN : 0 < N) :
    (expLoQ (tq i s) N : ℝ) ≤ tauS i s ∧ tauS i s ≤ (expHiQ (tq i s) N : ℝ) := by
  rw [tauS_eq]
  exact expQ_enc (tq i s) (tq_range i s).1 (tq_range i s).2 N hN

theorem tauS_le_one (i s : ℕ) : 0 ≤ tauS i s ∧ tauS i s ≤ 1 := by
  rw [tauS_eq]
  refine ⟨(Real.exp_pos _).le, ?_⟩
  rw [Real.exp_le_one_iff]
  have : (0 : ℚ) ≤ tq i s := (tq_range i s).1
  have : (0 : ℝ) ≤ (tq i s : ℝ) := by exact_mod_cast this
  linarith

/-- a fixed-point power stream approximates `tau^k` -/
theorem pow_stream_err {τ lo hi : ℝ} {a P : ℕ} (hlo : lo ≤ τ) (hhi : τ ≤ hi) (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (ha : (a : ℝ) / 2 ^ P ≤ lo) (haP : a ≤ 2 ^ P) (k : ℕ) :
    |τ ^ k - (stream P a (2 ^ P) k : ℝ) / 2 ^ P| ≤ k * (hi - (a : ℝ) / 2 ^ P) + k / 2 ^ P := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hα0 : (0 : ℝ) ≤ (a : ℝ) / 2 ^ P := by positivity
  have hα1 : (a : ℝ) / 2 ^ P ≤ 1 := by rw [div_le_one hP]; exact_mod_cast haP
  have hu := stream_upper P a (2 ^ P) k
  have hl := stream_lower P a (2 ^ P) haP k
  have hs : ((2 ^ P : ℕ) : ℝ) / 2 ^ P = 1 := by push_cast; field_simp
  rw [hs, one_mul] at hu hl
  have hp := abs_pow_sub_pow_le_unit h0 h1 hα0 hα1 k
  have hd : |τ - (a : ℝ) / 2 ^ P| ≤ hi - (a : ℝ) / 2 ^ P := by
    rw [abs_of_nonneg (by linarith)]; linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : |τ ^ k - ((a : ℝ) / 2 ^ P) ^ k| ≤ k * (hi - (a : ℝ) / 2 ^ P) :=
    hp.trans (mul_le_mul_of_nonneg_left hd hk)
  rw [abs_le] at h2 ⊢
  constructor <;> nlinarith [h2.1, h2.2, hu, hl]

/-! ### `strength` and `curvature` as monotone functions of `q^2` -/

def Af (x : ℚ) : ℚ := 3 * (1 - x ^ 2) / (2 * (1 + 4 * x + x ^ 2))
def Bf (x : ℚ) : ℚ := (1 - x) ^ 2 / (2 * (1 + 4 * x + x ^ 2))
def AfR (x : ℝ) : ℝ := 3 * (1 - x ^ 2) / (2 * (1 + 4 * x + x ^ 2))
def BfR (x : ℝ) : ℝ := (1 - x) ^ 2 / (2 * (1 + 4 * x + x ^ 2))

theorem Af_cast (x : ℚ) : AfR (x : ℝ) = (Af x : ℝ) := by unfold AfR Af; push_cast; rfl
theorem Bf_cast (x : ℚ) : BfR (x : ℝ) = (Bf x : ℝ) := by unfold BfR Bf; push_cast; rfl

theorem q_lt_one' : capSource.q < 1 := by
  rw [q_eq, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by norm_num)

theorem q_pos' : 0 < capSource.q := Real.exp_pos _

theorem strength_eq : capSource.strength = AfR (capSource.q ^ 2) := by
  have h1 := q_lt_one'
  have h0 := q_pos'
  have hx : capSource.q ^ 2 < 1 := by nlinarith
  have hx0 : 0 < capSource.q ^ 2 := by positivity
  have hD : (0 : ℝ) < 1 - capSource.q ^ 2 := by linarith
  unfold CapFields.CapSource.strength CapFields.CapSource.normalizer AfR
  have hDx : (0 : ℝ) < 1 + 4 * capSource.q ^ 2 + (capSource.q ^ 2) ^ 2 := by positivity
  field_simp
  ring

theorem curvature_eq : capSource.curvature = BfR (capSource.q ^ 2) := by
  have h1 := q_lt_one'
  have h0 := q_pos'
  have hx : capSource.q ^ 2 < 1 := by nlinarith
  have hD : (0 : ℝ) < 1 - capSource.q ^ 2 := by linarith
  unfold CapFields.CapSource.curvature CapFields.CapSource.normalizer BfR
  have hDx : (0 : ℝ) < 1 + 4 * capSource.q ^ 2 + (capSource.q ^ 2) ^ 2 := by positivity
  field_simp

theorem AfR_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : AfR y ≤ AfR x := by
  unfold AfR
  have hDx : (0 : ℝ) < 2 * (1 + 4 * x + x ^ 2) := by positivity
  have hDy : (0 : ℝ) < 2 * (1 + 4 * y + y ^ 2) := by nlinarith
  rw [div_le_div_iff₀ hDy hDx]
  nlinarith [mul_nonneg (sub_nonneg.2 hxy) (by nlinarith : (0:ℝ) ≤ 4 + 2 * (x + y) + 4 * x * y)]

theorem BfR_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : BfR y ≤ BfR x := by
  unfold BfR
  have hDx : (0 : ℝ) < 2 * (1 + 4 * x + x ^ 2) := by positivity
  have hDy : (0 : ℝ) < 2 * (1 + 4 * y + y ^ 2) := by nlinarith
  rw [div_le_div_iff₀ hDy hDx]
  have h1 : (1 - y) ^ 2 ≤ (1 - x) ^ 2 := by nlinarith
  have h2 : 2 * (1 + 4 * x + x ^ 2) ≤ 2 * (1 + 4 * y + y ^ 2) := by nlinarith
  exact mul_le_mul h1 h2 hDx.le (by positivity)



/-! ### Taylor bound for cos -/
section cosT
open Complex

theorem cos_taylor_re (x : ℝ) : ∀ N : ℕ,
    (∑ m ∈ Finset.range (2 * N), ((x : ℂ) * I) ^ m / (m.factorial : ℂ)).re =
      ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Complex.add_re, Complex.add_re, ih, Finset.sum_range_succ]
    have e1 : ((x : ℂ) * I) ^ (2 * N) / ((2 * N).factorial : ℂ) =
        (((-1 : ℝ) ^ N * x ^ (2 * N) / ((2 * N).factorial : ℝ) : ℝ) : ℂ) := by
      rw [mul_pow, pow_mul I, Complex.I_sq]
      push_cast
      ring
    have e2 : (((x : ℂ) * I) ^ (2 * N + 1) / ((2 * N + 1).factorial : ℂ)).re = 0 := by
      have : ((x : ℂ) * I) ^ (2 * N + 1) / ((2 * N + 1).factorial : ℂ) =
          (((-1 : ℝ) ^ N * x ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) : ℝ) : ℂ) * I := by
        rw [mul_pow, pow_succ I, pow_succ (x : ℂ), pow_mul I, Complex.I_sq]
        push_cast
        ring
      rw [this]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [e2, e1, Complex.ofReal_re]
    ring

theorem cos_taylor (x : ℝ) (hx : |x| ≤ 1) (N : ℕ) (hN : 0 < N) :
    |Real.cos x - ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)| ≤
      |x| ^ (2 * N) * (((2 * N).succ : ℝ) / (((2 * N).factorial : ℝ) * ((2 * N : ℕ) : ℝ))) := by
  have hxc : ‖(x : ℂ) * I‖ ≤ 1 := by simpa using hx
  have hb := Complex.exp_bound hxc (n := 2 * N) (by omega)
  have hre : (Complex.exp ((x : ℂ) * I)).re = Real.cos x := Complex.exp_ofReal_mul_I_re x
  have h1 := Complex.abs_re_le_norm (Complex.exp ((x : ℂ) * I) -
    ∑ m ∈ Finset.range (2 * N), ((x : ℂ) * I) ^ m / (m.factorial : ℂ))
  rw [Complex.sub_re, hre, cos_taylor_re] at h1
  refine h1.trans ?_
  refine hb.trans (le_of_eq ?_)
  have hn : ‖(x : ℂ) * I‖ = |x| := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  rw [hn]
  push_cast
  ring


end cosT


/-! ### Cosine table `cos (pi l / 93)` -/

def cosS (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => cosS x n + (-1) ^ n * x ^ (2 * n) / ((2 * n).factorial : ℚ)

theorem cosS_cast (x : ℚ) (N : ℕ) :
    (cosS x N : ℝ) = ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  induction N with
  | zero => simp [cosS]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; simp [cosS]

/-- a rational lower bound of pi with `pi - piQ <= 10^-20`. -/
def piQ : ℚ := 314159265358979323846 / 10 ^ 20

theorem piQ_enc : (piQ : ℝ) ≤ Real.pi ∧ Real.pi ≤ piQ + 1 / 10 ^ 20 := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  unfold piQ
  push_cast
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- the cosine value used for `l <= 93`: two doublings of a 12-term Taylor value at `pi l / 372`. -/
def cosY (l : ℕ) : ℚ :=
  let P := cosS (piQ * l / 372) 12
  let v := 2 * P ^ 2 - 1
  2 * v ^ 2 - 1

/-- error propagation of `u -> 2 u^2 - 1`. -/
def dblE (e : ℚ) : ℚ := 2 * e * (2 + e)

def eCos1 : ℚ := 1 / (4 * 10 ^ 20) + 25 / (((24).factorial : ℚ) * 24)
def dY : ℚ := dblE (dblE eCos1)

theorem dbl_err {u û : ℝ} {e : ℝ} (hu : |u| ≤ 1) (he : 0 ≤ e) (h : |u - û| ≤ e) :
    |(2 * u ^ 2 - 1) - (2 * û ^ 2 - 1)| ≤ 2 * e * (2 + e) := by
  have e1 : (2 * u ^ 2 - 1) - (2 * û ^ 2 - 1) = 2 * (u - û) * (u + û) := by ring
  rw [e1, abs_mul, abs_mul]
  have h2 : |u + û| ≤ 2 + e := by
    have : |û| ≤ 1 + e := by
      have := abs_sub_abs_le_abs_sub û u
      rw [abs_sub_comm] at this
      linarith
    calc |u + û| ≤ |u| + |û| := abs_add_le _ _
      _ ≤ 2 + e := by linarith
  have h3 : |(2 : ℝ)| = 2 := by norm_num
  rw [h3]
  calc 2 * |u - û| * |u + û| ≤ 2 * e * (2 + e) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h (by norm_num)) h2 (abs_nonneg _) (by positivity)

theorem cosY_spec {l : ℕ} (hl : l ≤ 93) :
    |Real.cos (Real.pi * l / 93) - (cosY l : ℝ)| ≤ (dY : ℝ) := by
  obtain ⟨hp1, hp2⟩ := piQ_enc
  have hl' : (l : ℝ) ≤ 93 := by exact_mod_cast hl
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  set φ : ℝ := Real.pi * l / 372 with hφ
  set φh : ℝ := (piQ : ℝ) * l / 372 with hφh
  have hpiQ0 : (0 : ℝ) ≤ piQ := by
    have : (0 : ℚ) ≤ piQ := by unfold piQ; norm_num
    exact_mod_cast this
  have hφ1 : |φ| ≤ 1 := by
    rw [abs_le]; constructor
    · have : 0 ≤ φ := by rw [hφ]; positivity
      linarith
    · rw [hφ, div_le_one (by norm_num)]; nlinarith [Real.pi_pos]
  have hφh1 : |φh| ≤ 1 := by
    rw [abs_le]; constructor
    · have : 0 ≤ φh := by rw [hφh]; positivity
      linarith
    · rw [hφh, div_le_one (by norm_num)]; nlinarith [Real.pi_pos]
  have hdiff : |φ - φh| ≤ 1 / (4 * 10 ^ 20) := by
    have : φ - φh = (Real.pi - piQ) * l / 372 := by rw [hφ, hφh]; ring
    rw [this, abs_le]
    constructor
    · have : 0 ≤ (Real.pi - piQ) * l / 372 := by
        apply div_nonneg (mul_nonneg (by linarith) hl0) (by norm_num)
      have : (0 : ℝ) ≤ 1 / (4 * 10 ^ 20) := by norm_num
      linarith
    · have h1 : (Real.pi - piQ) * l ≤ 1 / 10 ^ 20 * 93 := by
        apply mul_le_mul (by linarith) hl' hl0 (by norm_num)
      calc (Real.pi - piQ) * l / 372 ≤ 1 / 10 ^ 20 * 93 / 372 := by
            apply div_le_div_of_nonneg_right h1 (by norm_num)
        _ = 1 / (4 * 10 ^ 20) := by norm_num
  have hcosd : |Real.cos φ - Real.cos φh| ≤ 1 / (4 * 10 ^ 20) :=
    (Real.abs_cos_sub_cos_le φ φh).trans hdiff
  have hT := cos_taylor φh hφh1 12 (by norm_num)
  have hrem : |φh| ^ (2 * 12) * (((2 * 12).succ : ℝ) / (((2 * 12).factorial : ℝ) * ((2 * 12 : ℕ) : ℝ))) ≤
      25 / (((24).factorial : ℝ) * 24) := by
    have : |φh| ^ (2 * 12) ≤ 1 := pow_le_one₀ (abs_nonneg _) hφh1
    have hpos : (0 : ℝ) ≤ ((2 * 12).succ : ℝ) / (((2 * 12).factorial : ℝ) * ((2 * 12 : ℕ) : ℝ)) := by positivity
    calc _ ≤ 1 * (((2 * 12).succ : ℝ) / (((2 * 12).factorial : ℝ) * ((2 * 12 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right this hpos
      _ = _ := by norm_num
  have hP : (cosS (piQ * l / 372) 12 : ℝ) = ∑ k ∈ Finset.range 12, (-1 : ℝ) ^ k * φh ^ (2 * k) / ((2 * k).factorial : ℝ) := by
    rw [cosS_cast]; push_cast; rw [hφh]
  have hT' : |Real.cos φh - (cosS (piQ * l / 372) 12 : ℝ)| ≤ 25 / (((24).factorial : ℝ) * 24) := by
    rw [hP]; exact hT.trans hrem
  have e1 : |Real.cos φ - (cosS (piQ * l / 372) 12 : ℝ)| ≤ (eCos1 : ℝ) := by
    have t := abs_add_le (Real.cos φ - Real.cos φh) (Real.cos φh - (cosS (piQ * l / 372) 12 : ℝ))
    have e : Real.cos φ - (cosS (piQ * l / 372) 12 : ℝ) =
        (Real.cos φ - Real.cos φh) + (Real.cos φh - (cosS (piQ * l / 372) 12 : ℝ)) := by ring
    rw [e]
    have : (eCos1 : ℝ) = 1 / (4 * 10 ^ 20) + 25 / (((24).factorial : ℝ) * 24) := by
      unfold eCos1; push_cast; ring
    rw [this]
    linarith
  have hcu : |Real.cos φ| ≤ 1 := Real.abs_cos_le_one φ
  have hc2 : Real.cos (2 * φ) = 2 * Real.cos φ ^ 2 - 1 := Real.cos_two_mul φ
  have hc4 : Real.cos (2 * (2 * φ)) = 2 * Real.cos (2 * φ) ^ 2 - 1 := Real.cos_two_mul (2 * φ)
  have hθ : Real.pi * l / 93 = 2 * (2 * φ) := by rw [hφ]; ring
  have e1' : (0 : ℝ) ≤ (eCos1 : ℝ) := by unfold eCos1; positivity
  have s1 := dbl_err hcu e1' e1
  have hv1 : |Real.cos (2 * φ)| ≤ 1 := Real.abs_cos_le_one _
  have e2' : (0 : ℝ) ≤ 2 * (eCos1 : ℝ) * (2 + eCos1) := by positivity
  rw [← hc2] at s1
  have s2 := dbl_err hv1 e2' s1
  rw [hθ, hc4]
  have hy : (cosY l : ℝ) = 2 * (2 * (cosS (piQ * l / 372) 12 : ℝ) ^ 2 - 1) ^ 2 - 1 := by
    unfold cosY; push_cast; ring
  have hd : (dY : ℝ) = 2 * (2 * (eCos1 : ℝ) * (2 + eCos1)) * (2 + 2 * (eCos1 : ℝ) * (2 + eCos1)) := by
    unfold dY dblE; push_cast; ring
  rw [hy, hd]
  exact s2


/-! ### The shared cosine table -/

def PY : ℕ := 100

def foldI (l : ℕ) : ℕ := if l ≤ 93 then l else 186 - l

def dC : ℚ := dY + 1 / 2 ^ PY

theorem cos_mod (m : ℕ) : Real.cos (Real.pi * m / 93) = Real.cos (Real.pi * ((m % 186 : ℕ) : ℝ) / 93) := by
  have h : (m : ℝ) = ((m % 186 : ℕ) : ℝ) + ((m / 186 : ℕ) : ℝ) * 186 := by
    have := Nat.mod_add_div m 186
    have h2 : ((m % 186 + 186 * (m / 186) : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast this
    push_cast at h2
    linarith
  have : Real.pi * m / 93 = Real.pi * ((m % 186 : ℕ) : ℝ) / 93 + ((m / 186 : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [h]; ring
  rw [this, Real.cos_add_nat_mul_two_pi]

theorem cos_fold {l : ℕ} (hl : l < 186) : Real.cos (Real.pi * l / 93) = Real.cos (Real.pi * (foldI l : ℕ) / 93) := by
  unfold foldI
  split_ifs with h
  · rfl
  · have : Real.pi * l / 93 = 2 * Real.pi - Real.pi * ((186 - l : ℕ) : ℝ) / 93 := by
      have : ((186 - l : ℕ) : ℝ) = 186 - l := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [this]; ring
    rw [this, Real.cos_two_pi_sub]

theorem Ycos_err (Y : List ℤ) (hY : ∀ l < 94, (Y.getD l 0 : ℚ) ≤ cosY l * 2 ^ PY ∧ cosY l * 2 ^ PY < Y.getD l 0 + 1)
    {l : ℕ} (hl : l < 186) :
    |Real.cos (Real.pi * l / 93) - ((Y.getD (foldI l) 0 : ℤ) : ℝ) / 2 ^ PY| ≤ (dC : ℝ) := by
  rw [cos_fold hl]
  have hf : foldI l ≤ 93 := by unfold foldI; split_ifs <;> omega
  have h1 := cosY_spec hf
  obtain ⟨a1, a2⟩ := hY (foldI l) (by omega)
  have hP : (0 : ℚ) < 2 ^ PY := by positivity
  have hP' : (0 : ℝ) < 2 ^ PY := by positivity
  have b1 : ((Y.getD (foldI l) 0 : ℤ) : ℚ) / 2 ^ PY ≤ cosY (foldI l) := by rw [div_le_iff₀ hP]; exact a1
  have b2 : cosY (foldI l) ≤ ((Y.getD (foldI l) 0 : ℤ) : ℚ) / 2 ^ PY + 1 / 2 ^ PY := by
    rw [← add_div, le_div_iff₀ hP]; linarith
  have c1 := (Rat.cast_le (K := ℝ)).2 b1
  have c2 := (Rat.cast_le (K := ℝ)).2 b2
  push_cast at c1 c2
  unfold dC
  push_cast
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]



/-! ### The class sums `S_r(k)` and their integer tables -/

theorem ite_sum_filter {α : Type*} (L : List α) (p : α → Prop) [DecidablePred p] (f : α → ℝ) :
    (L.map fun a => if p a then f a else 0).sum = ((L.filter fun a => decide (p a)).map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases h : p a
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

/-- entries `(jj, p)` of the radius class `r` of the auxiliary population. -/
def clsOf (σ : Sign) (r : ℕ) : List (ℕ × ℤ) :=
  ((auxT σ).filter fun t => decide (t.1.toNat = r)).map fun t => (t.2.1.toNat, t.2.2)

def PwC (Y : List ℤ) (cls : List (List (ℕ × ℤ))) (r jm : ℕ) : ℤ :=
  ((cls.getD r []).map fun x => x.2 * Y.getD (foldI ((jm * x.1) % 186)) 0).sum

def Pcls (cls : List (List (ℕ × ℤ))) (r : ℕ) : ℤ := ((cls.getD r []).map Prod.snd).sum

theorem Sr_eq_cls (σ : Sign) (r k : ℕ) :
    Sr σ r k = ((clsOf σ r).map fun x => (tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) *
      Real.cos ((k : ℝ) * (Real.pi * (x.1 : ℝ) / 93))).sum := by
  unfold Sr clsOf
  rw [ite_sum_filter (auxT σ) (fun t => t.1.toNat = r)]
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  obtain ⟨hj, _⟩ := auxJ_ok σ t (List.mem_of_mem_filter ht)
  simp only [Function.comp_apply]
  rw [show (((t.2.1.toNat : ℕ)) : ℝ) = (t.2.1 : ℝ) by exact_mod_cast Int.toNat_of_nonneg hj]

theorem cls_sum_err (σ : Sign) (Y : List ℤ) (hY : ∀ l < 94, (Y.getD l 0 : ℚ) ≤ cosY l * 2 ^ PY ∧ cosY l * 2 ^ PY < Y.getD l 0 + 1)
    (cls : List (List (ℕ × ℤ))) (r k : ℕ) (hcl : cls.getD r [] = clsOf σ r)
    (hjj : ∀ x ∈ clsOf σ r, x.1 < 186) (hp : ∀ x ∈ clsOf σ r, 0 ≤ x.2) :
    |Sr σ r k - (tgt σ / (sumP (auxT σ) : ℝ)) * (PwC Y cls r (k % 186) : ℝ) / 2 ^ PY| ≤
      (tgt σ / (sumP (auxT σ) : ℝ)) * (Pcls cls r : ℝ) * (dC : ℝ) ∧
    |Sr σ r k| ≤ (tgt σ / (sumP (auxT σ) : ℝ)) * (Pcls cls r : ℝ) := by
  have hg := tgt_nonneg σ
  have hM : (0 : ℝ) < (sumP (auxT σ) : ℝ) := by exact_mod_cast aux_tot σ
  have hP : (0 : ℝ) < 2 ^ PY := by positivity
  rw [Sr_eq_cls σ]
  unfold PwC Pcls
  rw [hcl]
  have hdC : (0 : ℝ) ≤ (dC : ℝ) := by
    have : (0 : ℚ) ≤ dC := by unfold dC dY dblE eCos1 PY; norm_num
    exact_mod_cast this
  -- both statements by induction on the class list
  have key : ∀ (L : List (ℕ × ℤ)), (∀ x ∈ L, x.1 < 186) → (∀ x ∈ L, 0 ≤ x.2) →
      |(L.map fun x => (tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) * Real.cos ((k : ℝ) * (Real.pi * (x.1 : ℝ) / 93))).sum
        - (tgt σ / (sumP (auxT σ) : ℝ)) * ((L.map fun x => x.2 * Y.getD (foldI (((k % 186) * x.1) % 186)) 0).sum : ℤ) / 2 ^ PY|
        ≤ (tgt σ / (sumP (auxT σ) : ℝ)) * ((L.map Prod.snd).sum : ℤ) * (dC : ℝ) ∧
      |(L.map fun x => (tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) * Real.cos ((k : ℝ) * (Real.pi * (x.1 : ℝ) / 93))).sum|
        ≤ (tgt σ / (sumP (auxT σ) : ℝ)) * ((L.map Prod.snd).sum : ℤ) := by
    intro L
    induction L with
    | nil => intro _ _; simp
    | cons x L ih =>
      intro h1 h2
      obtain ⟨ih1, ih2⟩ := ih (fun y hy => h1 y (by simp [hy])) (fun y hy => h2 y (by simp [hy]))
      have hx1 := h1 x (by simp)
      have hx2 := h2 x (by simp)
      have hxr : (0 : ℝ) ≤ (x.2 : ℝ) := by exact_mod_cast hx2
      have hw0 : 0 ≤ tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ) := div_nonneg (mul_nonneg hg hxr) hM.le
      have hcos : Real.cos ((k : ℝ) * (Real.pi * (x.1 : ℝ) / 93)) = Real.cos (Real.pi * ((k * x.1 : ℕ) : ℝ) / 93) := by
        congr 1; push_cast; ring
      have hmod : (k * x.1) % 186 = ((k % 186) * x.1) % 186 := by
        rw [Nat.mul_mod k x.1 186, Nat.mul_mod (k % 186) x.1 186, Nat.mod_mod]
      have he := Ycos_err Y hY (l := (k * x.1) % 186) (Nat.mod_lt _ (by norm_num))
      rw [← cos_mod, ← hcos] at he
      rw [hmod] at he
      simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul]
      constructor
      · set c := Real.cos ((k : ℝ) * (Real.pi * (x.1 : ℝ) / 93)) with hc
        set yv : ℝ := ((Y.getD (foldI (((k % 186) * x.1) % 186)) 0 : ℤ) : ℝ) / 2 ^ PY with hyv
        have e : (tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ) * c + (L.map fun x => (tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) * Real.cos ((k : ℝ) * (Real.pi * (x.1 : ℝ) / 93))).sum) -
            (tgt σ / (sumP (auxT σ) : ℝ)) * (x.2 * Y.getD (foldI (((k % 186) * x.1) % 186)) 0 +
              (L.map fun x => x.2 * Y.getD (foldI (((k % 186) * x.1) % 186)) 0).sum : ℤ) / 2 ^ PY =
            (tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) * (c - yv) +
            ((L.map fun x => (tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) * Real.cos ((k : ℝ) * (Real.pi * (x.1 : ℝ) / 93))).sum -
              (tgt σ / (sumP (auxT σ) : ℝ)) * ((L.map fun x => x.2 * Y.getD (foldI (((k % 186) * x.1) % 186)) 0).sum : ℤ) / 2 ^ PY) := by
          rw [hyv]; simp only [Int.cast_add, Int.cast_mul]; ring
        simp only [Int.cast_add, Int.cast_mul] at e
        rw [e]
        have t1 : |(tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) * (c - yv)| ≤ (tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) * (dC : ℝ) := by
          rw [abs_mul, abs_of_nonneg hw0]
          exact mul_le_mul_of_nonneg_left he hw0
        have t2 := abs_add_le ((tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) * (c - yv))
          ((L.map fun x => (tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) * Real.cos ((k : ℝ) * (Real.pi * (x.1 : ℝ) / 93))).sum -
              (tgt σ / (sumP (auxT σ) : ℝ)) * ((L.map fun x => x.2 * Y.getD (foldI (((k % 186) * x.1) % 186)) 0).sum : ℤ) / 2 ^ PY)
        have e3 : (tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) * (dC : ℝ) + (tgt σ / (sumP (auxT σ) : ℝ)) * ((L.map Prod.snd).sum : ℤ) * (dC : ℝ) =
            (tgt σ / (sumP (auxT σ) : ℝ)) * ((x.2 + (L.map Prod.snd).sum : ℤ) : ℝ) * (dC : ℝ) := by simp only [Int.cast_add]; ring
        simp only [Int.cast_add] at e3
        linarith
      · have hc1 := Real.abs_cos_le_one ((k : ℝ) * (Real.pi * (x.1 : ℝ) / 93))
        have t1 : |(tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) * Real.cos ((k : ℝ) * (Real.pi * (x.1 : ℝ) / 93))| ≤
            tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ) := by
          rw [abs_mul, abs_of_nonneg hw0]
          calc _ ≤ (tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) * 1 := mul_le_mul_of_nonneg_left hc1 hw0
            _ = _ := by ring
        have t2 := abs_add_le ((tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) * Real.cos ((k : ℝ) * (Real.pi * (x.1 : ℝ) / 93)))
          ((L.map fun x => (tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ)) * Real.cos ((k : ℝ) * (Real.pi * (x.1 : ℝ) / 93))).sum)
        have e3 : tgt σ * (x.2 : ℝ) / (sumP (auxT σ) : ℝ) + (tgt σ / (sumP (auxT σ) : ℝ)) * ((L.map Prod.snd).sum : ℤ) =
            (tgt σ / (sumP (auxT σ) : ℝ)) * ((x.2 : ℝ) + ((L.map Prod.snd).sum : ℤ)) := by ring
        linarith
  exact key _ hjj hp



/-! ### The error of one auxiliary coefficient (abstract) -/

theorem aux_j_err {n j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 384) {A B Ah Bh wA wB δ GM : ℝ}
    (hA : |A - Ah| ≤ wA) (hB : |B - Bh| ≤ wB) (hAh : 0 ≤ Ah) (hBh : 0 ≤ Bh)
    (hGM : 1 + Ah + 384 * Bh ≤ GM) (_hδ : 0 ≤ δ)
    {τJ T S Sh m eT : ℕ → ℝ}
    (hτ0 : ∀ r < n, 0 ≤ τJ r ∧ τJ r ≤ 1) (hT0 : ∀ r < n, 0 ≤ T r ∧ T r ≤ 1)
    (hτT : ∀ r < n, |τJ r - T r| ≤ eT r) (hS : ∀ r < n, |S r| ≤ m r)
    (hSS : ∀ r < n, |S r - Sh r| ≤ m r * δ) (hm0 : ∀ r < n, 0 ≤ m r) :
    |(-((1 + A * j + B * (j : ℝ) ^ 2) / j) * ∑ r ∈ Finset.range n, τJ r * S r) -
      (-((1 + Ah * j + Bh * (j : ℝ) ^ 2) / j) * ∑ r ∈ Finset.range n, T r * Sh r)| ≤
    (wA + 384 * wB) * (∑ r ∈ Finset.range n, m r) + GM * ∑ r ∈ Finset.range n, m r * (eT r + δ) := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hjr2 : (j : ℝ) ≤ 384 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  set G : ℝ := (1 + A * j + B * (j : ℝ) ^ 2) / j with hG
  set Gh : ℝ := (1 + Ah * j + Bh * (j : ℝ) ^ 2) / j with hGh
  set M : ℝ := ∑ r ∈ Finset.range n, τJ r * S r with hM
  set Mh : ℝ := ∑ r ∈ Finset.range n, T r * Sh r with hMh
  have hGd : G - Gh = (A - Ah) + (B - Bh) * j := by
    rw [hG, hGh]; field_simp; ring
  have hGdab : |G - Gh| ≤ wA + 384 * wB := by
    rw [hGd]
    have t1 := abs_add_le (A - Ah) ((B - Bh) * j)
    have t2 : |(B - Bh) * j| ≤ wB * 384 := by
      rw [abs_mul, abs_of_pos hj0]
      exact mul_le_mul hB hjr2 hj0.le ((abs_nonneg _).trans hB)
    linarith
  have hGhle : |Gh| ≤ GM := by
    have h1 : Gh = 1 / j + Ah + Bh * j := by rw [hGh]; field_simp
    have h2 : 1 / (j : ℝ) ≤ 1 := by rw [div_le_one hj0]; exact hjr
    have h3 : Bh * j ≤ Bh * 384 := mul_le_mul_of_nonneg_left hjr2 hBh
    have h4 : 0 ≤ Gh := by rw [h1]; positivity
    rw [abs_of_nonneg h4]; rw [h1]; linarith
  have hMle : |M| ≤ ∑ r ∈ Finset.range n, m r := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
    have hr' := Finset.mem_range.1 hr
    rw [abs_mul, abs_of_nonneg (hτ0 r hr').1]
    calc τJ r * |S r| ≤ 1 * m r := mul_le_mul (hτ0 r hr').2 (hS r hr') (abs_nonneg _) zero_le_one
      _ = m r := one_mul _
  have hMd : |M - Mh| ≤ ∑ r ∈ Finset.range n, m r * (eT r + δ) := by
    rw [hM, hMh, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
    have hr' := Finset.mem_range.1 hr
    have e : τJ r * S r - T r * Sh r = (τJ r - T r) * S r + T r * (S r - Sh r) := by ring
    rw [e]
    have a1 : |(τJ r - T r) * S r| ≤ eT r * m r := by
      rw [abs_mul]; exact mul_le_mul (hτT r hr') (hS r hr') (abs_nonneg _) ((abs_nonneg _).trans (hτT r hr'))
    have a2 : |T r * (S r - Sh r)| ≤ m r * δ := by
      rw [abs_mul, abs_of_nonneg (hT0 r hr').1]
      calc T r * |S r - Sh r| ≤ 1 * (m r * δ) := mul_le_mul (hT0 r hr').2 (hSS r hr') (abs_nonneg _) zero_le_one
        _ = m r * δ := one_mul _
    calc _ ≤ |(τJ r - T r) * S r| + |T r * (S r - Sh r)| := abs_add_le _ _
      _ ≤ eT r * m r + m r * δ := add_le_add a1 a2
      _ = m r * (eT r + δ) := by ring
  have e : (-G * M) - (-Gh * Mh) = -((G - Gh) * M + Gh * (M - Mh)) := by ring
  rw [e, abs_neg]
  have hsumm : 0 ≤ ∑ r ∈ Finset.range n, m r := Finset.sum_nonneg fun r hr => hm0 r (Finset.mem_range.1 hr)
  have hsume : 0 ≤ ∑ r ∈ Finset.range n, m r * (eT r + δ) :=
    (abs_nonneg _).trans hMd
  calc |(G - Gh) * M + Gh * (M - Mh)| ≤ |(G - Gh) * M| + |Gh * (M - Mh)| := abs_add_le _ _
    _ ≤ (wA + 384 * wB) * (∑ r ∈ Finset.range n, m r) + GM * ∑ r ∈ Finset.range n, m r * (eT r + δ) := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul hGdab hMle (abs_nonneg _) ((abs_nonneg _).trans hGdab)
      · rw [abs_mul]
        exact mul_le_mul hGhle hMd (abs_nonneg _) ((abs_nonneg _).trans hGhle)



/-! ### The auxiliary list: data, evaluator, specification -/

def Pa : ℕ := 100
def PA : ℕ := 100
def adN : ℕ := 2 ^ 64
def Pq : ℕ := 140

/-- the radius-free data of a species, shared by all sixteen radii. -/
structure AuxS where
  Mx : ℤ
  Tt : ℤ
  Sg : ℤ
  Y : List ℤ
  cls : List (List (ℕ × ℤ))
  pw : List (List ℤ)
  an : ℤ
  bn : ℤ
  qln : ℕ
  qhn : ℕ
  NQ : ℕ

/-- the data of one radius: the shared data with the stream ratios (`aL` lower, `bL` upper). -/
structure AuxD where
  sh : AuxS
  aL : List ℕ
  bL : List ℕ

def qlo (S : AuxS) : ℚ := (S.qln : ℚ) / 2 ^ Pq
def qhi (S : AuxS) : ℚ := (S.qhn : ℚ) / 2 ^ Pq

/-- the auxiliary mass `tgt σ`, as a rational. -/
def tgtQ (σ : Sign) (S : AuxS) : ℚ := tgtB σ - (S.Sg : ℚ) / (S.Tt : ℚ)

/-- `tgt σ / M_σ`, the weight of one integer unit. -/
def cQ (σ : Sign) (S : AuxS) : ℚ := tgtQ σ S / (S.Mx : ℚ)

/-- one step of the fixed-point power streams -/
def stepA (as ss : List ℕ) : List ℕ := List.zipWith (fun a s => s * a / 2 ^ Pa) as ss

/-- a row of class values, extended to the streams of the species (both families read the same
sixteen classes: entry `s` is class `s % 16`). -/
def rowExt (σ : Sign) (row : List ℤ) : List ℤ := if σ = Sign.neg then row ++ row else row

/-- integer inner product of the states with a row. -/
def dotZ : List ℕ → List ℤ → ℤ
  | a :: as, b :: bs => (a : ℤ) * b + dotZ as bs
  | _, _ => 0

/-- `sum_s ss_s * pw[j % 186][s % 16]` -/
def Xsum (σ : Sign) (S : AuxS) (j : ℕ) (ss : List ℕ) : ℤ :=
  dotZ ss (rowExt σ (S.pw.getD (j % 186) []))

/-- `-G^_j * M^_j`, with `M^_j = (tgt/M) * sum_s ss_s pw_(s % 16) / 2^(Pa+PY)` -/
def valAt (σ : Sign) (S : AuxS) (j : ℕ) (ss : List ℕ) : ℚ :=
  -((1 + ((S.an : ℚ) / 2 ^ PA) * j + ((S.bn : ℚ) / 2 ^ PA) * (j : ℚ) ^ 2) / j) *
    (cQ σ S * (Xsum σ S j ss : ℚ) / 2 ^ (Pa + PY))

def auxLoop (σ : Sign) (D : AuxD) : ℕ → ℕ → List ℕ → List ℤ
  | 0, _, _ => []
  | n + 1, j, ss => ⌊valAt σ D.sh j ss * adN⌋ :: auxLoop σ D n (j + 1) (stepA D.aL ss)

def statesAt (aL : List ℕ) (j : ℕ) : List ℕ := aL.map fun a => stream Pa a (2 ^ Pa) j

theorem stepA_statesAt (aL : List ℕ) (j : ℕ) : stepA aL (statesAt aL j) = statesAt aL (j + 1) := by
  unfold stepA statesAt
  induction aL with
  | nil => rfl
  | cons a aL ih => simp [List.zipWith_cons_cons, stream, ih]

theorem auxLoop_spec (σ : Sign) (D : AuxD) : ∀ (n j : ℕ),
    auxLoop σ D n j (statesAt D.aL j) =
      (List.range n).map fun i => ⌊valAt σ D.sh (j + i) (statesAt D.aL (j + i)) * adN⌋ := by
  intro n
  induction n with
  | zero => intro j; simp [auxLoop]
  | succ n ih =>
    intro j
    rw [auxLoop, stepA_statesAt, ih (j + 1), List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    rw [show j + (i + 1) = j + 1 + i by ring]

/-- constant term of the auxiliary Chebyshev coefficients, exact rational. -/
def A0Q (σ : Sign) (i : ℕ) (S : AuxS) : ℚ :=
  -cQ σ S * (((List.range 16).map fun r => (Pcls S.cls r : ℚ) * sigq (min i r)).sum) +
    (53 * sigq i - radq i / 2) / 58

def auxList (σ : Sign) (i : ℕ) (D : AuxD) : List ℤ :=
  ⌊A0Q σ i D.sh * adN⌋ :: auxLoop σ D 384 1 (statesAt D.aL 1)

theorem auxList_length (σ : Sign) (i : ℕ) (D : AuxD) : (auxList σ i D).length = 385 := by
  have : ∀ n j ss, (auxLoop σ D n j ss).length = n := by
    intro n
    induction n with
    | zero => intro j ss; rfl
    | succ n ih => intro j ss; simp [auxLoop, ih]
  simp [auxList, this]

theorem auxList_getD (σ : Sign) (i : ℕ) (D : AuxD) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 384) :
    (auxList σ i D).getD j 0 = ⌊valAt σ D.sh j (statesAt D.aL j) * adN⌋ := by
  unfold auxList
  rw [auxLoop_spec σ D 384 1]
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [List.getD_cons_succ]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  rw [show 1 + i = i + 1 by ring]

theorem dotZ_eq : ∀ (as : List ℕ) (bs : List ℤ), as.length ≤ bs.length →
    dotZ as bs = ∑ s ∈ Finset.range as.length, ((as.getD s 0 : ℕ) : ℤ) * bs.getD s 0 := by
  intro as
  induction as with
  | nil => intro bs _; cases bs <;> simp [dotZ]
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => simp at h
    | cons b bs =>
      have h' : as.length ≤ bs.length := by simpa using h
      rw [dotZ, ih bs h', List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      ring

theorem rowExt_length (σ : Sign) {row : List ℤ} (h : row.length = 16) :
    (rowExt σ row).length = ns σ := by
  unfold rowExt ns
  split_ifs
  · simp [h]
  · exact h

theorem rowExt_getD (σ : Sign) {row : List ℤ} (h : row.length = 16) {s : ℕ} (hs : s < ns σ) :
    (rowExt σ row).getD s 0 = row.getD (s % 16) 0 := by
  unfold rowExt
  unfold ns at hs
  split_ifs at hs ⊢ with hσ
  · by_cases h1 : s < 16
    · rw [Nat.mod_eq_of_lt h1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
    · rw [show s % 16 = s - 16 by omega, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), h]
  · rw [Nat.mod_eq_of_lt hs]

/-! ### The checks -/

/-- **shared (radius-free) checks of a species.** Every field is decidable; `pw_ok` is the heavy
one and can be split by `r` at the instance. -/
structure AuxSharedOK (σ : Sign) (S : AuxS) : Prop where
  sum_M : sumP (auxT σ) = S.Mx
  sum_T : sumP row0 = S.Tt
  sum_S : sumP (gasT σ) = S.Sg
  Y_ok : ∀ l < 94, (S.Y.getD l 0 : ℚ) ≤ cosY l * 2 ^ PY ∧ cosY l * 2 ^ PY < S.Y.getD l 0 + 1
  cls_ok : ∀ r < 16, S.cls.getD r [] = clsOf σ r
  pw_len : ∀ jm < 186, (S.pw.getD jm []).length = 16
  pw_ok : ∀ jm < 186, ∀ r < 16, (S.pw.getD jm []).getD r 0 = PwC S.Y S.cls r jm
  A_ok : (S.an : ℚ) / 2 ^ PA ≤ Af (qhi S ^ 2) ∧ Af (qlo S ^ 2) ≤ (S.an + 1) / 2 ^ PA
  B_ok : (S.bn : ℚ) / 2 ^ PA ≤ Bf (qhi S ^ 2) ∧ Bf (qlo S ^ 2) ≤ (S.bn + 1) / 2 ^ PA
  an_nn : 0 ≤ S.an
  bn_nn : 0 ≤ S.bn
  ql_nn : 0 ≤ qlo S
  qh_lt : qhi S < 1
  NQ_pos : 0 < S.NQ
  q_ok : qlo S ≤ expLoQ (27 / 500) S.NQ ∧ expHiQ (27 / 500) S.NQ ≤ qhi S

/-- **per-radius checks** with exponential series length `NE`. -/
structure AuxRadOK (σ : Sign) (NE i : ℕ) (D : AuxD) : Prop where
  NE_pos : 0 < NE
  len : D.aL.length = ns σ
  a_ok : ∀ s < ns σ, ((D.aL.getD s 0 : ℕ) : ℚ) ≤ expLoQ (tq i s) NE * 2 ^ Pa ∧ D.aL.getD s 0 ≤ 2 ^ Pa
  b_ok : ∀ s < ns σ, expHiQ (tq i s) NE ≤ ((D.bL.getD s 0 : ℕ) : ℚ) / 2 ^ Pa

/-- the per-radius checks as one Boolean, for `decide +kernel` at the instance. -/
def auxRadCheck (σ : Sign) (NE i : ℕ) (D : AuxD) : Bool :=
  decide (0 < NE) && decide (D.aL.length = ns σ) &&
    decide (∀ s < ns σ, ((D.aL.getD s 0 : ℕ) : ℚ) ≤ expLoQ (tq i s) NE * 2 ^ Pa ∧ D.aL.getD s 0 ≤ 2 ^ Pa) &&
    decide (∀ s < ns σ, expHiQ (tq i s) NE ≤ ((D.bL.getD s 0 : ℕ) : ℚ) / 2 ^ Pa)

theorem auxRadOK_of_check {σ : Sign} {NE i : ℕ} {D : AuxD} (h : auxRadCheck σ NE i D = true) :
    AuxRadOK σ NE i D := by
  unfold auxRadCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

/-! ### Error of the integer auxiliary list -/

def mq (σ : Sign) (S : AuxS) (s : ℕ) : ℚ := cQ σ S * (Pcls S.cls (s % 16) : ℚ)
def eTq (D : AuxD) (s : ℕ) : ℚ :=
  384 * (((D.bL.getD s 0 : ℕ) : ℚ) / 2 ^ Pa - ((D.aL.getD s 0 : ℕ) : ℚ) / 2 ^ Pa) + 384 / 2 ^ Pa
def GMq (S : AuxS) : ℚ := 1 + (S.an : ℚ) / 2 ^ PA + 384 * ((S.bn : ℚ) / 2 ^ PA)
def eJq (σ : Sign) (D : AuxD) : ℚ :=
  (1 / 2 ^ PA + 384 * (1 / 2 ^ PA)) * ((List.range (ns σ)).map (mq σ D.sh)).sum +
    GMq D.sh * ((List.range (ns σ)).map fun s => mq σ D.sh s * (eTq D s + dC)).sum

theorem sum_range_list_q (f : ℕ → ℚ) (n : ℕ) : (((List.range n).map f).sum : ℚ) = ∑ r ∈ Finset.range n, f r := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]; simp

theorem q_enc {σ : Sign} {S : AuxS} (h : AuxSharedOK σ S) :
    (qlo S : ℝ) ≤ capSource.q ∧ capSource.q ≤ (qhi S : ℝ) := by
  rw [q_eq]
  obtain ⟨e1, e2⟩ := expQ_enc (27 / 500) (by norm_num) (by norm_num) S.NQ h.NQ_pos
  have h1 := (Rat.cast_le (K := ℝ)).2 h.q_ok.1
  have h2 := (Rat.cast_le (K := ℝ)).2 h.q_ok.2
  exact ⟨h1.trans e1, e2.trans h2⟩

theorem AB_enc {σ : Sign} {S : AuxS} (h : AuxSharedOK σ S) :
    |capSource.strength - ((S.an : ℚ) / 2 ^ PA : ℚ)| ≤ (1 / 2 ^ PA : ℚ) ∧
    |capSource.curvature - ((S.bn : ℚ) / 2 ^ PA : ℚ)| ≤ (1 / 2 ^ PA : ℚ) := by
  obtain ⟨a1, a2⟩ := h.A_ok
  obtain ⟨b1, b2⟩ := h.B_ok
  have hqlo0 := h.ql_nn
  have hqhi1 := h.qh_lt.le
  obtain ⟨hq1, hq2⟩ := q_enc h
  have hql0 : (0 : ℝ) ≤ qlo S := by exact_mod_cast hqlo0
  have hqh1 : (qhi S : ℝ) ≤ 1 := by exact_mod_cast hqhi1
  have hq0 := q_pos'
  have hqq1 := q_lt_one'
  have hx1 : (qlo S : ℝ) ^ 2 ≤ capSource.q ^ 2 := by gcongr
  have hx2 : capSource.q ^ 2 ≤ (qhi S : ℝ) ^ 2 := by gcongr
  have hx3 : (qhi S : ℝ) ^ 2 ≤ 1 := by nlinarith
  have hx4 : capSource.q ^ 2 ≤ 1 := by nlinarith
  have hs := strength_eq
  have hc := curvature_eq
  have sA1 := AfR_anti (by positivity : (0 : ℝ) ≤ capSource.q ^ 2) hx2 hx3
  have sA2 := AfR_anti (by positivity : (0 : ℝ) ≤ (qlo S : ℝ) ^ 2) hx1 hx4
  have sB1 := BfR_anti (by positivity : (0 : ℝ) ≤ capSource.q ^ 2) hx2 hx3
  have sB2 := BfR_anti (by positivity : (0 : ℝ) ≤ (qlo S : ℝ) ^ 2) hx1 hx4
  have eA1 : AfR ((qhi S : ℝ) ^ 2) = (Af (qhi S ^ 2) : ℝ) := by
    have := Af_cast (qhi S ^ 2); push_cast at this; exact this
  have eA2 : AfR ((qlo S : ℝ) ^ 2) = (Af (qlo S ^ 2) : ℝ) := by
    have := Af_cast (qlo S ^ 2); push_cast at this; exact this
  have eB1 : BfR ((qhi S : ℝ) ^ 2) = (Bf (qhi S ^ 2) : ℝ) := by
    have := Bf_cast (qhi S ^ 2); push_cast at this; exact this
  have eB2 : BfR ((qlo S : ℝ) ^ 2) = (Bf (qlo S ^ 2) : ℝ) := by
    have := Bf_cast (qlo S ^ 2); push_cast at this; exact this
  have a1' := (Rat.cast_le (K := ℝ)).2 a1
  have a2' := (Rat.cast_le (K := ℝ)).2 a2
  have b1' := (Rat.cast_le (K := ℝ)).2 b1
  have b2' := (Rat.cast_le (K := ℝ)).2 b2
  push_cast at a1' a2' b1' b2' ⊢
  rw [hs, hc]
  rw [eA1] at sA1; rw [eA2] at sA2; rw [eB1] at sB1; rw [eB2] at sB2
  have ea : ((S.an : ℝ) + 1) / 2 ^ PA = (S.an : ℝ) / 2 ^ PA + 1 / 2 ^ PA := by ring
  have eb : ((S.bn : ℝ) + 1) / 2 ^ PA = (S.bn : ℝ) / 2 ^ PA + 1 / 2 ^ PA := by ring
  rw [ea] at a2'
  rw [eb] at b2'
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem statesAt_getD {aL : List ℕ} {s : ℕ} (hs : s < aL.length) (j : ℕ) :
    (statesAt aL j).getD s 0 = stream Pa (aL.getD s 0) (2 ^ Pa) j := by
  unfold statesAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hs]
  simp

theorem stream_le_one (a P : ℕ) (haP : a ≤ 2 ^ P) (k : ℕ) : (stream P a (2 ^ P) k : ℝ) / 2 ^ P ≤ 1 := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hu := stream_upper P a (2 ^ P) k
  have hs : ((2 ^ P : ℕ) : ℝ) / 2 ^ P = 1 := by push_cast; field_simp
  rw [hs, one_mul] at hu
  have hα0 : (0 : ℝ) ≤ (a : ℝ) / 2 ^ P := by positivity
  have hα1 : (a : ℝ) / 2 ^ P ≤ 1 := by rw [div_le_one hP]; exact_mod_cast haP
  exact hu.trans (pow_le_one₀ hα0 hα1)

theorem dC_nonneg : (0 : ℝ) ≤ (dC : ℝ) := by
  have : (0 : ℚ) ≤ dC := by unfold dC dY dblE eCos1 PY; norm_num
  exact_mod_cast this

theorem cls_j {σ : Sign} {r : ℕ} : ∀ x ∈ clsOf σ r, x.1 < 186 := by
  intro x hx
  unfold clsOf at hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  obtain ⟨h1, h2⟩ := auxJ_ok σ t (List.mem_of_mem_filter ht)
  simp only
  omega

theorem cls_p {σ : Sign} {r : ℕ} : ∀ x ∈ clsOf σ r, 0 ≤ x.2 := by
  intro x hx
  unfold clsOf at hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  exact (aux_ok σ t (List.mem_of_mem_filter ht)).1

theorem tgtQ_val {σ : Sign} {S : AuxS} (h : AuxSharedOK σ S) : tgt σ = (tgtQ σ S : ℝ) :=
  tgt_val h.sum_T h.sum_S

theorem cQ_val {σ : Sign} {S : AuxS} (h : AuxSharedOK σ S) :
    tgt σ / (sumP (auxT σ) : ℝ) = (cQ σ S : ℝ) := by
  rw [tgtQ_val h, h.sum_M]
  unfold cQ
  push_cast
  rfl

theorem cQ_nonneg {σ : Sign} {S : AuxS} (h : AuxSharedOK σ S) : (0 : ℝ) ≤ (cQ σ S : ℝ) := by
  rw [← cQ_val h]
  have hM : (0 : ℝ) < (sumP (auxT σ) : ℝ) := by exact_mod_cast aux_tot σ
  exact div_nonneg (tgt_nonneg σ) hM.le

theorem mq_nonneg {σ : Sign} {S : AuxS} (h : AuxSharedOK σ S) (s : ℕ) : (0 : ℝ) ≤ (mq σ S s : ℝ) := by
  have hr : s % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hp : 0 ≤ Pcls S.cls (s % 16) := by
    unfold Pcls
    rw [h.cls_ok _ hr]
    apply List.sum_nonneg
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact cls_p y hy
  have hp' : (0 : ℝ) ≤ (Pcls S.cls (s % 16) : ℝ) := by exact_mod_cast hp
  unfold mq
  push_cast
  exact mul_nonneg (cQ_nonneg h) hp'

theorem aux_coef_err (σ : Sign) (i NE : ℕ) (D : AuxD) (hS : AuxSharedOK σ D.sh) (hR : AuxRadOK σ NE i D)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 384) :
    |AngularCap.auxA capSource σ i j - (((auxList σ i D).getD j 0 : ℤ) : ℝ) / (adN : ℝ)| ≤
      (eJq σ D : ℝ) + 1 / (adN : ℝ) := by
  obtain ⟨hAe, hBe⟩ := AB_enc hS
  have hP2 : (0 : ℝ) < 2 ^ Pa := by positivity
  have hAh : (0 : ℝ) ≤ ((D.sh.an : ℚ) / 2 ^ PA : ℚ) := by
    have h0 : (0 : ℚ) ≤ (D.sh.an : ℚ) := by exact_mod_cast hS.an_nn
    have : (0 : ℚ) ≤ (D.sh.an : ℚ) / 2 ^ PA := by positivity
    exact_mod_cast this
  have hBh : (0 : ℝ) ≤ ((D.sh.bn : ℚ) / 2 ^ PA : ℚ) := by
    have h0 : (0 : ℚ) ≤ (D.sh.bn : ℚ) := by exact_mod_cast hS.bn_nn
    have : (0 : ℚ) ≤ (D.sh.bn : ℚ) / 2 ^ PA := by positivity
    exact_mod_cast this
  have hc := cQ_val hS
  -- the per-stream hypotheses
  have hper : ∀ s < ns σ,
      (0 ≤ tauS i s ^ j ∧ tauS i s ^ j ≤ 1) ∧
      (0 ≤ (stream Pa (D.aL.getD s 0) (2 ^ Pa) j : ℝ) / 2 ^ Pa ∧ (stream Pa (D.aL.getD s 0) (2 ^ Pa) j : ℝ) / 2 ^ Pa ≤ 1) ∧
      |tauS i s ^ j - (stream Pa (D.aL.getD s 0) (2 ^ Pa) j : ℝ) / 2 ^ Pa| ≤ (eTq D s : ℝ) ∧
      |Sr σ (s % 16) j| ≤ (mq σ D.sh s : ℝ) ∧
      |Sr σ (s % 16) j - (cQ σ D.sh : ℝ) * (((D.sh.pw.getD (j % 186) []).getD (s % 16) 0 : ℤ) : ℝ) / 2 ^ PY| ≤
        (mq σ D.sh s : ℝ) * (dC : ℝ) := by
    intro s hs
    have hr : s % 16 < 16 := Nat.mod_lt _ (by norm_num)
    obtain ⟨hτ0, hτ1⟩ := tauS_le_one i s
    obtain ⟨hlo, hhi0⟩ := tauS_enc i s NE hR.NE_pos
    obtain ⟨ha1, ha2⟩ := hR.a_ok s hs
    have hhi : tauS i s ≤ ((D.bL.getD s 0 : ℕ) : ℝ) / 2 ^ Pa := by
      have := (Rat.cast_le (K := ℝ)).2 (hR.b_ok s hs)
      push_cast at this
      exact hhi0.trans this
    have ha1' : ((D.aL.getD s 0 : ℕ) : ℝ) / 2 ^ Pa ≤ (expLoQ (tq i s) NE : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 ha1
      push_cast at this
      rw [div_le_iff₀ hP2]; exact this
    have hcs := cls_sum_err σ D.sh.Y hS.Y_ok D.sh.cls (s % 16) j (hS.cls_ok _ hr) cls_j cls_p
    rw [hc] at hcs
    refine ⟨⟨by positivity, pow_le_one₀ hτ0 hτ1⟩, ⟨by positivity, stream_le_one _ _ ha2 j⟩, ?_, ?_, ?_⟩
    · have hs := pow_stream_err hlo hhi hτ0 hτ1 ha1' ha2 j
      refine hs.trans ?_
      have hjr : (j : ℝ) ≤ 384 := by exact_mod_cast hj
      have hd : 0 ≤ ((D.bL.getD s 0 : ℕ) : ℝ) / 2 ^ Pa - ((D.aL.getD s 0 : ℕ) : ℝ) / 2 ^ Pa := by linarith
      unfold eTq
      push_cast
      have h1 : (j : ℝ) * (((D.bL.getD s 0 : ℕ) : ℝ) / 2 ^ Pa - ((D.aL.getD s 0 : ℕ) : ℝ) / 2 ^ Pa) ≤
          384 * (((D.bL.getD s 0 : ℕ) : ℝ) / 2 ^ Pa - ((D.aL.getD s 0 : ℕ) : ℝ) / 2 ^ Pa) :=
        mul_le_mul_of_nonneg_right hjr hd
      have h2 : (j : ℝ) / 2 ^ Pa ≤ 384 / 2 ^ Pa := div_le_div_of_nonneg_right hjr hP2.le
      linarith
    · have := hcs.2
      unfold mq
      push_cast
      exact this
    · have := hcs.1
      have hpwj : (D.sh.pw.getD (j % 186) []).getD (s % 16) 0 = PwC D.sh.Y D.sh.cls (s % 16) (j % 186) :=
        hS.pw_ok (j % 186) (Nat.mod_lt _ (by norm_num)) _ hr
      rw [hpwj]
      unfold mq
      push_cast
      exact this
  -- assemble
  have hrowlen : (D.sh.pw.getD (j % 186) []).length = 16 := hS.pw_len _ (Nat.mod_lt _ (by norm_num))
  have hstlen : (statesAt D.aL j).length = ns σ := by simp [statesAt, hR.len]
  have hX : ((Xsum σ D.sh j (statesAt D.aL j) : ℤ) : ℝ) =
      ∑ s ∈ Finset.range (ns σ), ((stream Pa (D.aL.getD s 0) (2 ^ Pa) j : ℝ) *
        (((D.sh.pw.getD (j % 186) []).getD (s % 16) 0 : ℤ) : ℝ)) := by
    unfold Xsum
    rw [dotZ_eq _ _ (by rw [hstlen, rowExt_length σ hrowlen]), hstlen]
    push_cast
    apply Finset.sum_congr rfl
    intro s hs
    have hs' := Finset.mem_range.1 hs
    rw [statesAt_getD (by rw [hR.len]; exact hs') j, rowExt_getD σ hrowlen hs']
  have hval : ((valAt σ D.sh j (statesAt D.aL j) : ℚ) : ℝ) =
      -((1 + (((D.sh.an : ℚ) / 2 ^ PA : ℚ) : ℝ) * j + (((D.sh.bn : ℚ) / 2 ^ PA : ℚ) : ℝ) * (j : ℝ) ^ 2) / j) *
        ∑ s ∈ Finset.range (ns σ), ((stream Pa (D.aL.getD s 0) (2 ^ Pa) j : ℝ) / 2 ^ Pa) *
          ((cQ σ D.sh : ℝ) * (((D.sh.pw.getD (j % 186) []).getD (s % 16) 0 : ℤ) : ℝ) / 2 ^ PY) := by
    unfold valAt
    push_cast
    rw [hX]
    congr 1
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_add]
    field_simp
  have key := aux_j_err (j := j) hj1 hj (A := capSource.strength) (B := capSource.curvature)
    (Ah := (((D.sh.an : ℚ) / 2 ^ PA : ℚ) : ℝ)) (Bh := (((D.sh.bn : ℚ) / 2 ^ PA : ℚ) : ℝ))
    (wA := ((1 / 2 ^ PA : ℚ) : ℝ)) (wB := ((1 / 2 ^ PA : ℚ) : ℝ)) (δ := (dC : ℝ)) (GM := (GMq D.sh : ℝ))
    hAe hBe hAh hBh (by unfold GMq; push_cast; exact le_refl _) dC_nonneg
    (n := ns σ)
    (τJ := fun s => tauS i s ^ j) (T := fun s => (stream Pa (D.aL.getD s 0) (2 ^ Pa) j : ℝ) / 2 ^ Pa)
    (S := fun s => Sr σ (s % 16) j)
    (Sh := fun s => (cQ σ D.sh : ℝ) * (((D.sh.pw.getD (j % 186) []).getD (s % 16) 0 : ℤ) : ℝ) / 2 ^ PY)
    (m := fun s => (mq σ D.sh s : ℝ)) (eT := fun s => (eTq D s : ℝ))
    (fun s hs => (hper s hs).1) (fun s hs => (hper s hs).2.1) (fun s hs => (hper s hs).2.2.1)
    (fun s hs => (hper s hs).2.2.2.1) (fun s hs => (hper s hs).2.2.2.2) (fun s _ => mq_nonneg hS s)
  have hA := auxA_eq σ i j hj1
  unfold Gk at hA
  rw [hA]
  have hfl := auxList_getD σ i D hj1 hj
  have hfl1 := Int.floor_le (valAt σ D.sh j (statesAt D.aL j) * adN)
  have hfl2 := Int.lt_floor_add_one (valAt σ D.sh j (statesAt D.aL j) * adN)
  rw [hfl]
  set fl : ℤ := ⌊valAt σ D.sh j (statesAt D.aL j) * adN⌋ with hfldef
  have hadN : (0 : ℝ) < adN := by unfold adN; positivity
  have c1 : (fl : ℝ) ≤ ((valAt σ D.sh j (statesAt D.aL j) : ℚ) : ℝ) * adN := by exact_mod_cast hfl1
  have c2 : ((valAt σ D.sh j (statesAt D.aL j) : ℚ) : ℝ) * adN < fl + 1 := by exact_mod_cast hfl2
  have d1 : |((valAt σ D.sh j (statesAt D.aL j) : ℚ) : ℝ) - (fl : ℝ) / adN| ≤ 1 / adN := by
    have e1 : (fl : ℝ) / adN ≤ ((valAt σ D.sh j (statesAt D.aL j) : ℚ) : ℝ) := by rw [div_le_iff₀ hadN]; exact c1
    have e2 : ((valAt σ D.sh j (statesAt D.aL j) : ℚ) : ℝ) ≤ (fl : ℝ) / adN + 1 / adN := by
      rw [← add_div, le_div_iff₀ hadN]; linarith
    rw [abs_le]; constructor <;> linarith
  rw [hval] at d1
  have hJ : (eJq σ D : ℝ) = (((1 / 2 ^ PA : ℚ) : ℝ) + 384 * ((1 / 2 ^ PA : ℚ) : ℝ)) * ∑ s ∈ Finset.range (ns σ), (mq σ D.sh s : ℝ) +
      (GMq D.sh : ℝ) * ∑ s ∈ Finset.range (ns σ), (mq σ D.sh s : ℝ) * ((eTq D s : ℝ) + dC) := by
    unfold eJq
    rw [sum_range_list_q (mq σ D.sh) (ns σ), sum_range_list_q (fun s => mq σ D.sh s * (eTq D s + dC)) (ns σ)]
    push_cast
    ring
  exact (abs_sub_le _ _ _).trans (add_le_add (key.trans (le_of_eq hJ.symm)) d1)

/-! ### Constant term, total l1 error, and the tail of the auxiliary part -/

theorem auxA_zero (σ : Sign) (i : ℕ) (S : AuxS) (hS : AuxSharedOK σ S) :
    AngularCap.auxA capSource σ i 0 = (A0Q σ i S : ℝ) := by
  have hgt : 0 ≤ tgt σ := tgt_nonneg _
  have hMaux : (0 : ℤ) ≤ sumP (auxT σ) := (aux_tot σ).le
  unfold AngularCap.auxA
  simp only [ite_true]
  unfold AngularSource.auxConst AngularSource.extTerm
  show ((auxCells σ).map fun e => e.w * (-capSource.sigma (min i e.rad))).sum + _ = _
  unfold auxCells
  rw [List.map_map]
  have hterm : ∀ t ∈ auxT σ, ((fun e => e.w * (-capSource.sigma (min i e.rad))) ∘
        mkAux (tgt σ) (sumP (auxT σ))) t =
      (fun r => -(sigq (min i r) : ℝ)) t.1.toNat * (tgt σ * (t.2.2 : ℝ) / (sumP (auxT σ) : ℝ)) := by
    intro t ht
    obtain ⟨hp, hr⟩ := aux_ok σ t ht
    obtain ⟨f1, f2, f3⟩ := mkAux_fields hgt hMaux hp
    simp only [Function.comp_apply, f1, f3]
    rw [sigma_eq]
    ring
  rw [List.map_congr_left hterm]
  have hcl' : ∀ t ∈ auxT σ, t.1.toNat < 16 := fun t ht => by
    have := (aux_ok σ t ht).2; omega
  rw [group_sum' (auxT σ) (fun t => t.1.toNat) 16 hcl' (fun r => -(sigq (min i r) : ℝ))
    (fun t => tgt σ * (t.2.2 : ℝ) / (sumP (auxT σ) : ℝ))]
  have hinner : ∀ r < 16, ((auxT σ).map fun t => if t.1.toNat = r then
        tgt σ * (t.2.2 : ℝ) / (sumP (auxT σ) : ℝ) else 0).sum =
      tgt σ / (sumP (auxT σ) : ℝ) * (Pcls S.cls r : ℝ) := by
    intro r hr
    rw [ite_sum_filter (auxT σ) (fun t => t.1.toNat = r)]
    unfold Pcls
    rw [hS.cls_ok r hr]
    unfold clsOf
    rw [List.map_map]
    generalize (auxT σ).filter (fun t => decide (t.1.toNat = r)) = L
    induction L with
    | nil => simp
    | cons t L ih => simp only [List.map_cons, List.sum_cons, Function.comp_apply, Int.cast_add] at ih ⊢; rw [ih]; ring
  have hsum : ∑ r ∈ Finset.range 16, -(sigq (min i r) : ℝ) *
        ((auxT σ).map fun t => if t.1.toNat = r then tgt σ * (t.2.2 : ℝ) / (sumP (auxT σ) : ℝ) else 0).sum =
      -(tgt σ / (sumP (auxT σ) : ℝ)) * ∑ r ∈ Finset.range 16, (Pcls S.cls r : ℝ) * (sigq (min i r) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hinner r (Finset.mem_range.1 hr)]
    ring
  rw [hsum, sigma_eq, radial_eq, cQ_val hS]
  unfold A0Q
  rw [sum_range_list_q (fun r => (Pcls S.cls r : ℚ) * sigq (min i r)) 16]
  push_cast
  ring

/-- the l1 error of the auxiliary list. -/
def eAq (σ : Sign) (D : AuxD) : ℚ := 1 / (adN : ℚ) + 384 * (eJq σ D + 1 / (adN : ℚ))

/-- **(X4)** the field `hA` of `AngRadiusCert`. -/
theorem hA_bound (σ : Sign) (i NE : ℕ) (D : AuxD) (hS : AuxSharedOK σ D.sh) (hR : AuxRadOK σ NE i D) :
    ∑ j ∈ Finset.range (384 + 1),
      |AngularCap.auxA capSource σ i j - (((auxList σ i D).getD j 0 : ℤ) : ℝ) / (adN : ℝ)| ≤ (eAq σ D : ℝ) := by
  have hadN : (0 : ℝ) < adN := by unfold adN; positivity
  rw [Finset.sum_range_succ']
  have h0 : |AngularCap.auxA capSource σ i 0 - (((auxList σ i D).getD 0 0 : ℤ) : ℝ) / (adN : ℝ)| ≤ 1 / (adN : ℝ) := by
    rw [auxA_zero σ i D.sh hS]
    have hg : (auxList σ i D).getD 0 0 = ⌊A0Q σ i D.sh * adN⌋ := rfl
    rw [hg]
    have hfl1 := Int.floor_le (A0Q σ i D.sh * adN)
    have hfl2 := Int.lt_floor_add_one (A0Q σ i D.sh * adN)
    set fl : ℤ := ⌊A0Q σ i D.sh * adN⌋
    have c1 : (fl : ℝ) ≤ (A0Q σ i D.sh : ℝ) * adN := by exact_mod_cast hfl1
    have c2 : (A0Q σ i D.sh : ℝ) * adN < fl + 1 := by exact_mod_cast hfl2
    have e1 : (fl : ℝ) / adN ≤ (A0Q σ i D.sh : ℝ) := by rw [div_le_iff₀ hadN]; exact c1
    have e2 : (A0Q σ i D.sh : ℝ) ≤ (fl : ℝ) / adN + 1 / adN := by
      rw [← add_div, le_div_iff₀ hadN]; linarith
    rw [abs_le]; constructor <;> linarith
  have hs : ∑ j ∈ Finset.range 384,
      |AngularCap.auxA capSource σ i (j + 1) - (((auxList σ i D).getD (j + 1) 0 : ℤ) : ℝ) / (adN : ℝ)| ≤
      384 * ((eJq σ D : ℝ) + 1 / (adN : ℝ)) := by
    have : ∀ j ∈ Finset.range 384,
        |AngularCap.auxA capSource σ i (j + 1) - (((auxList σ i D).getD (j + 1) 0 : ℤ) : ℝ) / (adN : ℝ)| ≤
        (eJq σ D : ℝ) + 1 / (adN : ℝ) := by
      intro j hj
      have := Finset.mem_range.1 hj
      exact aux_coef_err σ i NE D hS hR (by omega) (by omega)
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    simp
    ring
  unfold eAq
  push_cast
  linarith

/-- bound for the tail of the auxiliary series (with the species factor). -/
def tailQ (σ : Sign) (S : AuxS) : ℚ :=
  qhi S ^ 385 * ((1 / 385 + ((S.an : ℚ) + 1) / 2 ^ PA) * (1 / (1 - qhi S)) +
    ((S.bn : ℚ) + 1) / 2 ^ PA * (385 * (1 / (1 - qhi S)) + qhi S * (1 / (1 - qhi S)) ^ 2)) * tgtQ σ S * tailF σ

/-- **(X4)** the field `hT` of `AngRadiusCert`. -/
theorem tail_bound (σ : Sign) (S : AuxS) (h : AuxSharedOK σ S) :
    capSource.auxTail (Trunc.finite 384) σ ≤ (tailQ σ S : ℝ) := by
  obtain ⟨hAe, hBe⟩ := AB_enc h
  obtain ⟨hq1', hq2'⟩ := q_enc h
  have hqh1 : (qhi S : ℝ) < 1 := by exact_mod_cast h.qh_lt
  have hq0 := q_pos'
  have hqq1 := q_lt_one'
  have hAd := capSource_admissible
  have hA0 := AngularSource.strength_nonneg capSource hAd
  have hB0 := AngularSource.curvature_nonneg capSource hAd
  have hmass : capSource.auxMass σ = (tgtQ σ S : ℝ) := by rw [auxMass_eq, tgtQ_val h]
  have hA1 : capSource.strength ≤ ((S.an : ℝ) + 1) / 2 ^ PA := by
    have := (abs_le.1 hAe).2
    push_cast at this
    have e : ((S.an : ℝ) + 1) / 2 ^ PA = (S.an : ℝ) / 2 ^ PA + 1 / 2 ^ PA := by ring
    rw [e]; linarith
  have hB1 : capSource.curvature ≤ ((S.bn : ℝ) + 1) / 2 ^ PA := by
    have := (abs_le.1 hBe).2
    push_cast at this
    have e : ((S.bn : ℝ) + 1) / 2 ^ PA = (S.bn : ℝ) / 2 ^ PA + 1 / 2 ^ PA := by ring
    rw [e]; linarith
  have hqhi0 : (0 : ℝ) ≤ qhi S := by linarith
  have hu : 1 / (1 - capSource.q) ≤ 1 / (1 - (qhi S : ℝ)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hu0 : 0 ≤ 1 / (1 - capSource.q) := by
    have : 0 < 1 - capSource.q := by linarith
    positivity
  have htg : (0 : ℝ) ≤ (tgtQ σ S : ℝ) := by
    rw [← tgtQ_val h]; exact tgt_nonneg _
  have hF : (if σ = Sign.neg then (2 : ℝ) else 1) = (tailF σ : ℝ) := by
    unfold tailF
    split_ifs <;> simp
  have hF0 : (0 : ℝ) ≤ (tailF σ : ℝ) := by
    rw [← hF]; split_ifs <;> norm_num
  rw [AngularSource.auxTail_eq, hmass, hF]
  unfold AngularSource.tailUnit tailQ
  push_cast
  have e385 : (384 : ℝ) + 1 = 385 := by norm_num
  rw [e385]
  set u : ℝ := 1 / (1 - capSource.q) with hudef
  set uh : ℝ := 1 / (1 - (qhi S : ℝ)) with huhdef
  set Ah : ℝ := ((S.an : ℝ) + 1) / 2 ^ PA with hAhdef
  set Bh : ℝ := ((S.bn : ℝ) + 1) / 2 ^ PA with hBhdef
  have hP : capSource.q ^ 385 ≤ (qhi S : ℝ) ^ 385 := pow_le_pow_left₀ hq0.le hq2' 385
  have hP0 : 0 ≤ capSource.q ^ 385 := by positivity
  have hAhnn : 0 ≤ Ah := by
    have : (0 : ℝ) ≤ S.an := by exact_mod_cast h.an_nn
    rw [hAhdef]; positivity
  have h1 : (1 / 385 + capSource.strength) * u ≤ (1 / 385 + Ah) * uh := by
    apply mul_le_mul (by linarith) hu hu0 (by linarith)
  have hu2 : u ^ 2 ≤ uh ^ 2 := pow_le_pow_left₀ hu0 hu 2
  have h2 : capSource.q * u ^ 2 ≤ (qhi S : ℝ) * uh ^ 2 :=
    mul_le_mul hq2' hu2 (by positivity) hqhi0
  have h3 : capSource.curvature * (385 * u + capSource.q * u ^ 2) ≤ Bh * (385 * uh + (qhi S : ℝ) * uh ^ 2) := by
    apply mul_le_mul hB1 (by linarith) (by positivity) (by
      exact le_trans hB0 hB1)
  have hX : (1 / 385 + capSource.strength) * u + capSource.curvature * (385 * u + capSource.q * u ^ 2) ≤
      (1 / 385 + Ah) * uh + Bh * (385 * uh + (qhi S : ℝ) * uh ^ 2) := by linarith
  have hX0 : 0 ≤ (1 / 385 + capSource.strength) * u + capSource.curvature * (385 * u + capSource.q * u ^ 2) := by
    positivity
  apply mul_le_mul_of_nonneg_right _ hF0
  apply mul_le_mul_of_nonneg_right _ htg
  exact mul_le_mul hP hX hX0 (pow_nonneg hqhi0 _)

/-! ### The certificate -/

open CatalanMeasure.Signed.ChebSquare in
/-- **(X4)** assembly of a radius certificate on the real source from a gas part (the fields
`bins`, `hb`, `n`, `hn`, `gl`, `gd`, `hgd`, `hgl`, `hgl0`, `eG`, `hG`), the auxiliary checks and the
square data. -/
def angRadius_of_data (σ : Sign) (i NE : ℕ) (cap : ℚ)
    (bins : List (List YCell)) (hb : AngularSource.Binning (capSource.gas σ) bins)
    (n : ℕ) (hn : Odd n) (gl : List ℤ) (gd : ℕ) (hgd : 0 < gd)
    (hgl : gl.length ≤ n + 1) (hgl0 : gl ≠ []) (eG : ℚ)
    (hG : ∑ j ∈ Finset.range (n + 1),
      |AngularCap.gasA capSource σ i bins j - ((gl.getD j 0 : ℤ) : ℝ) / gd| ≤ (eG : ℝ))
    (D : AuxD) (hS : AuxSharedOK σ D.sh) (hR : AuxRadOK σ NE i D)
    (auxL qL sL rL : List ℤ) (haux : auxList σ i D = auxL)
    (εQ : ℚ) (hε : eG + eAq σ D + tailQ σ D.sh ≤ εQ)
    (hid : SquareIdentity (AngularCap.combineP (AngularCap.Nlist gl) auxL (gd * 2 ^ (gl.length - 1)) adN)
      qL sL rL ((gd * 2 ^ (gl.length - 1)) * adN) cap εQ)
    (hm : l1 rL.tail < rL.headD 0) :
    AngularCap.AngRadiusCert capSource σ i cap := by
  refine
    { bins := bins
      hb := hb
      n := n
      hn := hn
      gl := gl
      gd := gd
      hgd := hgd
      hgl := hgl
      hgl0 := hgl0
      aux := auxL
      ad := adN
      had := by unfold adN; positivity
      hax := ?_
      eG := eG
      eA := eAq σ D
      eT := tailQ σ D.sh
      ε := εQ
      hG := hG
      hA := ?_
      hT := tail_bound σ D.sh hS
      hε := hε
      q := qL
      s := sL
      r := rL
      hid := hid
      hm := hm }
  · rw [← haux, auxList_length]
  · rw [← haux]; exact hA_bound σ i NE D hS hR

open CatalanMeasure.Signed.ChebSquare in
/-- the assembly with the square identity in Kronecker-packed form. -/
def angRadius_of_kron (σ : Sign) (i NE : ℕ) (cap : ℚ)
    (bins : List (List YCell)) (hb : AngularSource.Binning (capSource.gas σ) bins)
    (n : ℕ) (hn : Odd n) (gl : List ℤ) (gd : ℕ) (hgd : 0 < gd)
    (hgl : gl.length ≤ n + 1) (hgl0 : gl ≠ []) (eG : ℚ)
    (hG : ∑ j ∈ Finset.range (n + 1),
      |AngularCap.gasA capSource σ i bins j - ((gl.getD j 0 : ℤ) : ℝ) / gd| ≤ (eG : ℝ))
    (D : AuxD) (hS : AuxSharedOK σ D.sh) (hR : AuxRadOK σ NE i D)
    (auxL pL qL sL rL : List ℤ) (haux : auxList σ i D = auxL)
    (εQ : ℚ) (hε : eG + eAq σ D + tailQ σ D.sh ≤ εQ)
    (hconv : AngularCap.combineP (AngularCap.Nlist gl) auxL (gd * 2 ^ (gl.length - 1)) adN = pL)
    (K : ℕ) (hk : KronSquare.KronSquare K pL qL sL rL ((gd * 2 ^ (gl.length - 1)) * adN) cap εQ)
    (hm : l1 rL.tail < rL.headD 0) :
    AngularCap.AngRadiusCert capSource σ i cap :=
  angRadius_of_data σ i NE cap bins hb n hn gl gd hgd hgl hgl0 eG hG D hS hR auxL qL sL rL haux εQ hε
    (by rw [hconv]; exact hk.squareIdentity) hm

end

end CatalanMeasure.GenD.Signed.RouteI.AngAux

#print axioms CatalanMeasure.GenD.Signed.RouteI.AngAux.auxA_eq
#print axioms CatalanMeasure.GenD.Signed.RouteI.AngAux.hA_bound
#print axioms CatalanMeasure.GenD.Signed.RouteI.AngAux.tail_bound
#print axioms CatalanMeasure.GenD.Signed.RouteI.AngAux.angRadius_of_data
#print axioms CatalanMeasure.GenD.Signed.RouteI.AngAux.angRadius_of_kron

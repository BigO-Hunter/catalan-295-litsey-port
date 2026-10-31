module

public import CatalanMeasure.GenD.Signed.Interp
public import CatalanMeasure.GenD.Signed.SpikeDischarge

/-!
# `spikeFix` from the endpoint trials (lane SE)

The field `spikeFix` of `SignedNearBounds` asks for `SpikeCompareFixed` for the interpolated trial
data `D i N α = SignedData.interp (DA i N) (DB i N) l c` (`Interp.lean`).  Here it is derived from
spike witnesses at the two endpoint trials that share one configuration (the split of the
positives into rest and spikes, the pole `ρ`, the count `m`).

* `SpikeEnv.interp`: the environment of the spike lemmas is stable under `interp`.
* `SpikePair`: two witnesses with the same configuration and separate `(c1, hP, hcost)` data.
* `SpikePair.toWitness`: a witness for `interp DA DB l c`, `l ∈ [0,1]`.  The condition `(P')` is
  affine in `b` (take `c1 = (1-l) c1A + l c1B`).  The cost condition is
  `Δ(D) := LHS - RHS ≤ 0`; the part of `Δ` that is not affine in the data is the convex
  `4 ν m e Σ|a|` and the quadratic `(2 c / s') Σ b_n² (1 - 1/n)` in `b` (note the cancellation of the
  indefinite pairing `ra` and of `numConst`/`denConst`), and `cs` is affine, so
  `Δ(interp) ≤ (1-l) Δ(DA) + l Δ(DB)`.  Hence the spike constant `cs` of the interpolated trial is
  the chord of the endpoint constants (each endpoint keeps its own constant, e.g. CSP = 11/10 at
  α = 1/16).
* `spikeFix_of_ends`: the field `spikeFix` itself.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Set MeasureTheory Filter Topology OAI.InternalCatalan
open CatalanMeasure.GenD.Signed (heineZ)
open CatalanMeasure.Signed.ReflectionEnergy

noncomputable section

/-! ### 1. The environment is stable under `interp` -/

theorem refTilt_linSeq (l : ℝ) (R R' : ℕ → ℝ) (m : ℕ) :
    refTilt (linSeq l R R') m = (1 - l) * refTilt R m + l * refTilt R' m := by
  unfold refTilt linSeq
  ring

def SpikeEnv.interp {DA DB : SignedData} {l c : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (rA : SignedRegular DA) (rB : SignedRegular DB)
    (EA : SpikeEnv DA) (EB : SpikeEnv DB) : SpikeEnv (SignedData.interp DA DB l c) where
  hν := EA.hν
  he := EA.he
  hsp := EA.hsp
  hθ := EA.hθ
  ha := summable_abs_linSeq hl0 hl1 EA.ha EB.ha
  hr := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((EA.hr.mul_left (1 - l)).add (EB.hr.mul_left l))
    show ((k + 1 : ℕ) : ℝ) * refTilt (linSeq l DA.R DB.R) (k + 1) ^ 2 ≤ _
    rw [refTilt_linSeq]
    have hk : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : 0 ≤ l * (1 - l) * (refTilt DA.R (k + 1) - refTilt DB.R (k + 1)) ^ 2 :=
      mul_nonneg (mul_nonneg hl0 (by linarith)) (sq_nonneg _)
    nlinarith [mul_nonneg hk h2]
  hra := by
    have hreg := SignedRegular.interp (c := c) hl0 hl1 hc rA rB
    obtain ⟨M, hM⟩ := abs_rt_le hreg.tau hreg.hR
    exact summable_mul_bdd hM (summable_abs_sh hreg.ha)
  Qref := fun x => (1 - l) * EA.Qref x + l * EB.Qref x
  hQ := by
    intro x hx
    have hB := EB.hQ x hx
    rw [hc.e] at hB
    have h := ((EA.hQ x hx).mul_left (1 - l)).add (hB.mul_left l)
    convert h using 1
    funext k
    show refTilt (linSeq l DA.R DB.R) (k + 1) * realEnergyTau DA.e ^ (k + 1) * _ = _
    rw [refTilt_linSeq]
    ring
  hℓ := by
    intro x hx
    have hx1 : |x| ≤ 1 := abs_le.mpr hx
    show (1 - l) * EA.Qref x + l * EB.Qref x - 2 * barrierTrialT (linSeq l DA.a DB.a) x ≤
      (1 - l) * DA.Sup + l * DB.Sup
    rw [barrierTrialT_linSeq EA.ha EB.ha l hx1]
    have h1 := mul_le_mul_of_nonneg_left (EA.hℓ x hx) (by linarith : 0 ≤ 1 - l)
    have h2 := mul_le_mul_of_nonneg_left (EB.hℓ x hx) hl0
    linarith
  hbK := by
    intro i hi
    have hi' : DA.K < i := hi
    have hB := EB.hbK i (by rw [hc.K]; exact hi')
    show (1 - l) * DA.b i + l * DB.b i = 0
    rw [EA.hbK i hi', hB]
    ring


/-! ### 2. The numerator and denominator differences are affine

The cost condition compares the spike family `ext` (extended by the phantom) with `z`; in the
difference of the two bounds the terms `numConst`, `denConst` (and with them the indefinite pairing
`ra`) cancel, and what remains is affine in `(a, R)` and in `b`. -/

/-- `ip (u - R) (u - R) - ip (u' - R) (u' - R)`. -/
def Ipd (u u' R : ℕ → ℝ) : ℝ :=
  ip (fun n => u n - R n) (fun n => u n - R n) - ip (fun n => u' n - R n) (fun n => u' n - R n)

theorem Ipd_eq {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {u u' R : ℕ → ℝ} (hu : IsGeom τ u)
    (hu' : IsGeom τ u') (hR : IsGeom τ R) :
    Ipd u u' R = ip u u - ip u' u' - 2 * ip (fun n => u n - u' n) R := by
  have h1 := hasSum_ip hτ (hu.sub hR) (hu.sub hR)
  have h2 := hasSum_ip hτ (hu'.sub hR) (hu'.sub hR)
  have h3 := ((hasSum_ip hτ hu hu).sub (hasSum_ip hτ hu' hu')).sub
    ((hasSum_ip hτ (hu.sub hu') hR).mul_left 2)
  have h4 := h1.sub h2
  have h5 : HasSum (fun n : ℕ => (u n - R n) * (u n - R n) / ((n : ℝ) + 1) -
      (u' n - R n) * (u' n - R n) / ((n : ℝ) + 1))
      (ip u u - ip u' u' - 2 * ip (fun n => u n - u' n) R) := by
    convert h3 using 1
    funext n
    ring
  exact h4.unique h5

theorem Ipd_linSeq {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {u u' R R' : ℕ → ℝ} (hu : IsGeom τ u)
    (hu' : IsGeom τ u') (hR : IsGeom τ R) (hR' : IsGeom τ R') (l : ℝ) :
    Ipd u u' (linSeq l R R') = (1 - l) * Ipd u u' R + l * Ipd u u' R' := by
  rw [Ipd_eq hτ hu hu' (isGeom_linSeq hR hR' l), Ipd_eq hτ hu hu' hR, Ipd_eq hτ hu hu' hR',
    ip_linSeq_right hτ (hu.sub hu') hR hR' l]
  ring

/-- The difference of the numerator bounds `numB` at two positive lists. -/
def numDiff (ν τ : ℝ) (a R : ℕ → ℝ) {k n n' : ℕ} (x : Fin k → ℝ) (g : Fin n → ℝ)
    (g' : Fin n' → ℝ) : ℝ :=
  (2 / ν) * ((∑ p, barrierTrialS a (-τ * g p)) - ∑ p, barrierTrialS a (-τ * g' p)) +
    (1 / 2) * Ipd (fun j => powSum τ ν x j - powSum τ ν g j)
      (fun j => powSum τ ν x j - powSum τ ν g' j) R

theorem numB_sub (D : SignedData) {k n n' : ℕ} (x : Fin k → ℝ) (g : Fin n → ℝ)
    (g' : Fin n' → ℝ) : D.numB x g - D.numB x g' = numDiff D.ν D.τ D.a D.R x g g' := by
  simp only [SignedData.numB, numDiff, Ipd]
  ring

theorem numDiff_linSeq {ν τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν) {a a' R R' : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (ha' : Summable fun k => |a' k|) (hR : IsGeom τ R)
    (hR' : IsGeom τ R') (l : ℝ) {k n n' : ℕ} (x : Fin k → ℝ) (g : Fin n → ℝ) (g' : Fin n' → ℝ)
    (hx : ∀ b, |x b| ≤ 1) (hg : ∀ p, |g p| ≤ 1) (hg' : ∀ p, |g' p| ≤ 1) :
    numDiff ν τ (linSeq l a a') (linSeq l R R') x g g' =
      (1 - l) * numDiff ν τ a R x g g' + l * numDiff ν τ a' R' x g g' := by
  have hS : ∀ {n : ℕ} (g : Fin n → ℝ), (∀ p, |g p| ≤ 1) →
      ∑ p, barrierTrialS (linSeq l a a') (-τ * g p) =
        (1 - l) * ∑ p, barrierTrialS a (-τ * g p) + l * ∑ p, barrierTrialS a' (-τ * g p) := by
    intro n g hg
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ =>
      barrierTrialS_linSeq ha ha' l (abs_neg_tau_mul_le hτ (hg p))
  have hu : IsGeom τ (fun j => powSum τ ν x j - powSum τ ν g j) :=
    (isGeom_powSum hτ.1 hν x hx).sub (isGeom_powSum hτ.1 hν g hg)
  have hu' : IsGeom τ (fun j => powSum τ ν x j - powSum τ ν g' j) :=
    (isGeom_powSum hτ.1 hν x hx).sub (isGeom_powSum hτ.1 hν g' hg')
  unfold numDiff
  rw [Ipd_linSeq hτ hu hu' hR hR' l, hS g hg, hS g' hg']
  ring

/-- The difference of the denominator bounds `spikeDenB` (the constants cancel). -/
theorem spikeDenB_sub (b : ℕ → ℝ) (s : ℕ) {q n n' : ℕ} (y : Fin q → ℝ) (g : Fin n → ℝ)
    (g' : Fin n' → ℝ) :
    spikeDenB b s y g - spikeDenB b s y g' =
      2 * (s : ℝ) * ((∑ p, barrierTrialS b (-(g p))) - ∑ p, barrierTrialS b (-(g' p))) := by
  unfold spikeDenB
  ring

theorem denDiff_linSeq {b b' : ℕ → ℝ} (hb : Summable fun k => |b k|)
    (hb' : Summable fun k => |b' k|) (l : ℝ) (s : ℕ) {n n' : ℕ} (g : Fin n → ℝ)
    (g' : Fin n' → ℝ) (hg : ∀ p, |g p| ≤ 1) (hg' : ∀ p, |g' p| ≤ 1) :
    2 * (s : ℝ) * ((∑ p, barrierTrialS (linSeq l b b') (-(g p))) -
        ∑ p, barrierTrialS (linSeq l b b') (-(g' p))) =
      (1 - l) * (2 * (s : ℝ) * ((∑ p, barrierTrialS b (-(g p))) - ∑ p, barrierTrialS b (-(g' p)))) +
      l * (2 * (s : ℝ) * ((∑ p, barrierTrialS b' (-(g p))) - ∑ p, barrierTrialS b' (-(g' p)))) := by
  have hS : ∀ {n : ℕ} (g : Fin n → ℝ), (∀ p, |g p| ≤ 1) →
      ∑ p, barrierTrialS (linSeq l b b') (-(g p)) =
        (1 - l) * ∑ p, barrierTrialS b (-(g p)) + l * ∑ p, barrierTrialS b' (-(g p)) := by
    intro n g hg
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ =>
      barrierTrialS_linSeq hb hb' l (by rw [abs_neg]; exact hg p)
  rw [hS g hg, hS g' hg']
  ring

/-! ### 3. The spike cost is convex in the data

`spikeCost` splits into the part that depends on the configuration only, the term
`4 ν m e Σ|a|` (convex in `a`), a part affine in `b`, and the quadratic form
`(2 (s'+m) m / s') Σ_n (1 - 1/n) b_n²` in `b` (convex, as `1 - 1/n ≥ 0`). -/

def costCfg (e : ℝ) (s' m : ℕ) (ρ r : ℝ) (k : ℕ) : ℝ :=
  2 * (m : ℝ) * k * Real.log (2 / (1 + realEnergyTau e ^ 2 * r)) +
  2 * (m : ℝ) ^ 2 * (Real.log (1 - realEnergyTau e ^ 2 * r ^ 2) - Real.log (1 - ρ ^ 2)) +
  (m : ℝ) * Real.log 2 + (2 * (m : ℝ) ^ 2 / s') * (ρ ^ 2 / (1 - ρ ^ 2))

def costA (ν e : ℝ) (m : ℕ) (a : ℕ → ℝ) : ℝ := 4 * ν * m * e * ∑' j : ℕ, |a j|

def costLin (b : ℕ → ℝ) (s' m : ℕ) (ρ : ℝ) {M : ℕ} (z : Fin M → ℝ) : ℝ :=
  2 * ((s' : ℝ) + m) * ∑ p, (barrierTrialS b (-(z p)) - barrierTrialS b (-ρ)) -
    (4 * ((s' : ℝ) + m) * m / s') * (∑' k : ℕ, b (k + 1) * poisSeq ρ (k + 1)) +
    (4 * ((s' : ℝ) + m) * m / s') * barrierTrialS b (-ρ)

def costQuad (b : ℕ → ℝ) (s' m : ℕ) : ℝ :=
  -((((s' : ℝ) + m) * m / s') * (∑' i : ℕ, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ))) +
    (2 * ((s' : ℝ) + m) * m / s') * (∑' k : ℕ, b (k + 1) ^ 2)

theorem spikeCost_split (ν e : ℝ) (a b : ℕ → ℝ) (s' m : ℕ) (ρ r : ℝ) (k : ℕ) {M : ℕ}
    (z : Fin M → ℝ) :
    spikeCost ν e a b s' m ρ r k z =
      costCfg e s' m ρ r k + costA ν e m a + costLin b s' m ρ z + costQuad b s' m := by
  unfold spikeCost costCfg costA costLin costQuad
  ring

theorem costA_le {ν e : ℝ} (hν : 0 ≤ ν) (he : 0 ≤ e) (m : ℕ) {a a' : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (ha' : Summable fun k => |a' k|) {l : ℝ} (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) :
    costA ν e m (linSeq l a a') ≤ (1 - l) * costA ν e m a + l * costA ν e m a' := by
  have h1 : ∑' j, |linSeq l a a' j| ≤ (1 - l) * ∑' j, |a j| + l * ∑' j, |a' j| := by
    have hs := (ha.mul_left (1 - l)).add (ha'.mul_left l)
    calc _ ≤ ∑' j, ((1 - l) * |a j| + l * |a' j|) :=
          (summable_abs_linSeq hl0 hl1 ha ha').tsum_le_tsum
            (fun j => abs_linSeq_le l hl0 hl1 a a' j) hs
      _ = _ := by
          rw [(ha.mul_left _).tsum_add (ha'.mul_left _), tsum_mul_left, tsum_mul_left]
  unfold costA
  have hc : 0 ≤ 4 * ν * m * e := by positivity
  have := mul_le_mul_of_nonneg_left h1 hc
  linarith

theorem barrierTrialS_linSeq_fin {b b' : ℕ → ℝ} {K : ℕ} (hb : ∀ i, K < i → b i = 0)
    (hb' : ∀ i, K < i → b' i = 0) (l x : ℝ) :
    barrierTrialS (linSeq l b b') x = (1 - l) * barrierTrialS b x + l * barrierTrialS b' x := by
  have hlin : ∀ i, K < i → linSeq l b b' i = 0 := fun i hi => by
    simp [linSeq, hb i hi, hb' i hi]
  rw [barrierTrialS_trunc hlin, barrierTrialS_trunc hb, barrierTrialS_trunc hb',
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [linSeq]; ring

theorem tsum_linSeq_fin {b b' : ℕ → ℝ} {K : ℕ} (hb : ∀ i, K < i → b i = 0)
    (hb' : ∀ i, K < i → b' i = 0) (l : ℝ) (c : ℕ → ℝ) :
    ∑' k : ℕ, linSeq l b b' (k + 1) * c k =
      (1 - l) * ∑' k : ℕ, b (k + 1) * c k + l * ∑' k : ℕ, b' (k + 1) * c k := by
  rw [tsum_eq_range (K := K) (f := fun k => linSeq l b b' (k + 1) * c k) (fun k hk => by
        simp [linSeq, hb (k + 1) (by omega), hb' (k + 1) (by omega)]),
    tsum_eq_range (K := K) (f := fun k => b (k + 1) * c k) (fun k hk => by
        simp [hb (k + 1) (by omega)]),
    tsum_eq_range (K := K) (f := fun k => b' (k + 1) * c k) (fun k hk => by
        simp [hb' (k + 1) (by omega)]),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [linSeq]; ring

theorem costLin_linSeq {b b' : ℕ → ℝ} {K : ℕ} (hb : ∀ i, K < i → b i = 0)
    (hb' : ∀ i, K < i → b' i = 0) (l : ℝ) (s' m : ℕ) (ρ : ℝ) {M : ℕ} (z : Fin M → ℝ) :
    costLin (linSeq l b b') s' m ρ z = (1 - l) * costLin b s' m ρ z + l * costLin b' s' m ρ z := by
  unfold costLin
  simp only [barrierTrialS_linSeq_fin hb hb' l]
  rw [tsum_linSeq_fin hb hb' l (fun k => poisSeq ρ (k + 1))]
  have hsum : ∑ p, (((1 - l) * barrierTrialS b (-(z p)) + l * barrierTrialS b' (-(z p))) -
      ((1 - l) * barrierTrialS b (-ρ) + l * barrierTrialS b' (-ρ))) =
      (1 - l) * ∑ p, (barrierTrialS b (-(z p)) - barrierTrialS b (-ρ)) +
        l * ∑ p, (barrierTrialS b' (-(z p)) - barrierTrialS b' (-ρ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsum]
  ring

theorem costQuad_fin {b : ℕ → ℝ} {K : ℕ} (hb : ∀ i, K < i → b i = 0) (s' m : ℕ) :
    costQuad b s' m = (2 * ((s' : ℝ) + m) * m / s') *
      ∑ i ∈ Finset.range K, (1 - 1 / ((i + 1 : ℕ) : ℝ)) * b (i + 1) ^ 2 := by
  unfold costQuad
  rw [tsum_eq_range (K := K) (f := fun i => 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ))
      (fun k hk => by simp [hb (k + 1) (by omega)]),
    tsum_eq_range (K := K) (f := fun k => b (k + 1) ^ 2)
      (fun k hk => by simp [hb (k + 1) (by omega)])]
  have : ∀ i ∈ Finset.range K, (1 - 1 / ((i + 1 : ℕ) : ℝ)) * b (i + 1) ^ 2 =
      b (i + 1) ^ 2 - (1 / 2) * (2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) := fun i _ => by
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem costQuad_le {b b' : ℕ → ℝ} {K : ℕ} (hb : ∀ i, K < i → b i = 0)
    (hb' : ∀ i, K < i → b' i = 0) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (s' m : ℕ) :
    costQuad (linSeq l b b') s' m ≤ (1 - l) * costQuad b s' m + l * costQuad b' s' m := by
  have hlin : ∀ i, K < i → linSeq l b b' i = 0 := fun i hi => by
    simp [linSeq, hb i hi, hb' i hi]
  rw [costQuad_fin hlin, costQuad_fin hb, costQuad_fin hb']
  set c : ℝ := 2 * ((s' : ℝ) + m) * m / s' with hcdef
  have hc : 0 ≤ c := by positivity
  have hsum : ∑ i ∈ Finset.range K, (1 - 1 / ((i + 1 : ℕ) : ℝ)) * linSeq l b b' (i + 1) ^ 2 ≤
      (1 - l) * ∑ i ∈ Finset.range K, (1 - 1 / ((i + 1 : ℕ) : ℝ)) * b (i + 1) ^ 2 +
        l * ∑ i ∈ Finset.range K, (1 - 1 / ((i + 1 : ℕ) : ℝ)) * b' (i + 1) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hw : 0 ≤ 1 - 1 / ((i + 1 : ℕ) : ℝ) := by
      have h1 : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 i
      have : 1 / ((i + 1 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]; exact h1
      linarith
    have h2 : 0 ≤ l * (1 - l) * (b (i + 1) - b' (i + 1)) ^ 2 :=
      mul_nonneg (mul_nonneg hl0 (by linarith)) (sq_nonneg _)
    simp only [linSeq]
    nlinarith [mul_nonneg hw h2]
  have := mul_le_mul_of_nonneg_left hsum hc
  linarith

theorem spikeCost_interp_le {ν e : ℝ} (hν : 0 ≤ ν) (he : 0 ≤ e) {a a' b b' : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (ha' : Summable fun k => |a' k|) {K : ℕ}
    (hb : ∀ i, K < i → b i = 0) (hb' : ∀ i, K < i → b' i = 0) {l : ℝ} (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) (s' m : ℕ) (ρ r : ℝ) (k : ℕ) {M : ℕ} (z : Fin M → ℝ) :
    spikeCost ν e (linSeq l a a') (linSeq l b b') s' m ρ r k z ≤
      (1 - l) * spikeCost ν e a b s' m ρ r k z + l * spikeCost ν e a' b' s' m ρ r k z := by
  rw [spikeCost_split, spikeCost_split, spikeCost_split, costLin_linSeq hb hb' l]
  have h1 := costA_le hν he m ha ha' hl0 hl1
  have h2 := costQuad_le hb hb' hl0 hl1 s' m
  linarith

/-! ### 4. The cost condition and (P') pass to `interp` -/

/-- The cost condition `hcost` of `SpikeWitness`, as a predicate of the trial. -/
def SpikeCostOK (D : SignedData) {k q' M : ℕ} (m : ℕ) (xn : Fin k → ℝ) (y : Fin q' → ℝ)
    (z : Fin M → ℝ) (zph ρ : ℝ) : Prop :=
  spikeNumB D.ν D.e D.a (refTilt D.R) D.Sup D.sp xn y (extFam z zph m) -
        spikeDenB D.b D.sp y (extFam z zph m) +
        spikeCost D.ν D.e D.a D.b (D.sp - m) m ρ (1 - D.θ) k (extFam z zph m) ≤
      spikeNumB D.ν D.e D.a (refTilt D.R) D.Sup D.sp xn y z - spikeDenB D.b D.sp y z +
        D.ν * ((M : ℝ) * D.cs)

/-- The condition (P') of `SpikeWitness`, as a predicate of the trial. -/
def SpikeChebOK (D : SignedData) (m : ℕ) (ρ c1 : ℝ) : Prop :=
  ∀ u ∈ Icc (-1 : ℝ) 1, ((D.sp - m : ℕ) : ℝ) * c1 ≤
    (D.sp : ℝ) * chebPs D.b u - m * chebPs (poisSeq ρ) u

/-- `LHS - RHS` of the cost condition, after the cancellation of the configuration-free terms. -/
def costGap (D : SignedData) {k q' M : ℕ} (m : ℕ) (xn : Fin k → ℝ) (y : Fin q' → ℝ)
    (z : Fin M → ℝ) (zph ρ : ℝ) : ℝ :=
  D.ν ^ 2 * numDiff D.ν D.τ D.a D.R xn (Fin.append y (extFam z zph m)) (Fin.append y z) -
    2 * (D.sp : ℝ) * ((∑ p, barrierTrialS D.b (-(extFam z zph m p))) -
      ∑ p, barrierTrialS D.b (-(z p))) +
    spikeCost D.ν D.e D.a D.b (D.sp - m) m ρ (1 - D.θ) k (extFam z zph m) -
    D.ν * ((M : ℝ) * D.cs)

theorem costOK_iff (D : SignedData) (hν : 0 < D.ν) {k q' M : ℕ} (m : ℕ) (xn : Fin k → ℝ)
    (y : Fin q' → ℝ) (z : Fin M → ℝ) (zph ρ : ℝ) :
    SpikeCostOK D m xn y z zph ρ ↔ costGap D m xn y z zph ρ ≤ 0 := by
  unfold SpikeCostOK costGap
  have e1 : spikeNumB D.ν D.e D.a (refTilt D.R) D.Sup D.sp xn y (extFam z zph m) -
      spikeNumB D.ν D.e D.a (refTilt D.R) D.Sup D.sp xn y z =
      D.ν ^ 2 * numDiff D.ν D.τ D.a D.R xn (Fin.append y (extFam z zph m)) (Fin.append y z) := by
    rw [spikeNumB_eq D hν, spikeNumB_eq D hν, ← mul_sub, numB_sub]
  have e2 := spikeDenB_sub D.b D.sp y (extFam z zph m) z
  constructor <;> intro h <;> linarith

theorem abs_extFam_le {M m : ℕ} {z : Fin M → ℝ} {zph : ℝ} (hz : ∀ i, |z i| ≤ 1)
    (hph : |zph| ≤ 1) (p : Fin (2 * m)) : |extFam z zph m p| ≤ 1 := by
  unfold extFam
  split_ifs with h
  · exact hz _
  · exact hph

theorem costGap_interp_le {DA DB : SignedData} {l c : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (rA : SignedRegular DA) (rB : SignedRegular DB) (hν : 0 < DA.ν)
    (hbA : ∀ i, DA.K < i → DA.b i = 0) (hbB : ∀ i, DA.K < i → DB.b i = 0)
    {k q' M : ℕ} (m : ℕ) (xn : Fin k → ℝ) (y : Fin q' → ℝ) (z : Fin M → ℝ) (zph ρ : ℝ)
    (hx : ∀ b, |xn b| ≤ 1) (hy : ∀ j, |y j| ≤ 1) (hz : ∀ i, |z i| ≤ 1) (hph : |zph| ≤ 1) :
    costGap (SignedData.interp DA DB l c) m xn y z zph ρ ≤
      (1 - l) * costGap DA m xn y z zph ρ + l * costGap DB m xn y z zph ρ := by
  have hτ := rA.tau
  have hext : ∀ p, |extFam z zph m p| ≤ 1 := abs_extFam_le hz hph
  have hge : ∀ p, |Fin.append y (extFam z zph m) p| ≤ 1 :=
    fin_append_forall y (extFam z zph m) (fun t => |t| ≤ 1) hy hext
  have hgz : ∀ p, |Fin.append y z p| ≤ 1 :=
    fin_append_forall y z (fun t => |t| ≤ 1) hy hz
  have hsA : Summable fun k => |DA.b k| :=
    summable_of_ne_finset_zero (s := Finset.range (DA.K + 1)) fun i hi =>
      by simp [hbA i (by simpa using hi)]
  have hsB : Summable fun k => |DB.b k| :=
    summable_of_ne_finset_zero (s := Finset.range (DA.K + 1)) fun i hi =>
      by simp [hbB i (by simpa using hi)]
  have hI : costGap (SignedData.interp DA DB l c) m xn y z zph ρ =
      DA.ν ^ 2 * numDiff DA.ν DA.τ (linSeq l DA.a DB.a) (linSeq l DA.R DB.R) xn
          (Fin.append y (extFam z zph m)) (Fin.append y z) -
        2 * (DA.sp : ℝ) * ((∑ p, barrierTrialS (linSeq l DA.b DB.b) (-(extFam z zph m p))) -
          ∑ p, barrierTrialS (linSeq l DA.b DB.b) (-(z p))) +
        spikeCost DA.ν DA.e (linSeq l DA.a DB.a) (linSeq l DA.b DB.b) (DA.sp - m) m ρ
          (1 - DA.θ) k (extFam z zph m) -
        DA.ν * ((M : ℝ) * ((1 - l) * DA.cs + l * DB.cs)) := rfl
  have hB : costGap DB m xn y z zph ρ =
      DA.ν ^ 2 * numDiff DA.ν DA.τ DB.a DB.R xn (Fin.append y (extFam z zph m))
          (Fin.append y z) -
        2 * (DA.sp : ℝ) * ((∑ p, barrierTrialS DB.b (-(extFam z zph m p))) -
          ∑ p, barrierTrialS DB.b (-(z p))) +
        spikeCost DA.ν DA.e DB.a DB.b (DA.sp - m) m ρ (1 - DA.θ) k (extFam z zph m) -
        DA.ν * ((M : ℝ) * DB.cs) := by
    unfold costGap
    rw [hc.ν, hc.τ, hc.e, hc.sp, hc.θ]
  rw [hI, hB]
  have h1 := numDiff_linSeq hτ hν rA.ha rB.ha rA.hR (rB.hRτ hc) l xn
    (Fin.append y (extFam z zph m)) (Fin.append y z) hx hge hgz
  have h2 := denDiff_linSeq hsA hsB l DA.sp (extFam z zph m) z hext hz
  have h3 := spikeCost_interp_le hν.le rA.he.1.le rA.ha rB.ha hbA
    (fun i hi => hbB i hi) hl0 hl1 (DA.sp - m) m ρ (1 - DA.θ) k (extFam z zph m)
  unfold costGap
  rw [h1, h2]
  nlinarith [h3]

theorem SpikeCostOK.interp {DA DB : SignedData} {l c : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (rA : SignedRegular DA) (rB : SignedRegular DB) (EA : SpikeEnv DA)
    (EB : SpikeEnv DB) {k q' M : ℕ} {m : ℕ} {xn : Fin k → ℝ} {y : Fin q' → ℝ} {z : Fin M → ℝ}
    {zph ρ : ℝ} (hx : ∀ b, |xn b| ≤ 1) (hy : ∀ j, |y j| ≤ 1) (hz : ∀ i, |z i| ≤ 1)
    (hph : |zph| ≤ 1) (hA : SpikeCostOK DA m xn y z zph ρ) (hB : SpikeCostOK DB m xn y z zph ρ) :
    SpikeCostOK (SignedData.interp DA DB l c) m xn y z zph ρ := by
  have hνB : 0 < DB.ν := by rw [hc.ν]; exact EA.hν
  rw [costOK_iff DA EA.hν] at hA
  rw [costOK_iff DB hνB] at hB
  rw [costOK_iff (SignedData.interp DA DB l c) EA.hν]
  have h := costGap_interp_le hl0 hl1 hc rA rB EA.hν EA.hbK
    (fun i hi => EB.hbK i (by rw [hc.K]; exact hi)) m xn y z zph ρ hx hy hz hph (c := c)
  have h1 := mul_le_mul_of_nonneg_left hA (by linarith : 0 ≤ 1 - l)
  have h2 := mul_le_mul_of_nonneg_left hB hl0
  linarith

theorem SpikeChebOK.interp {DA DB : SignedData} {l c : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (EA : SpikeEnv DA) (EB : SpikeEnv DB) {m : ℕ} {ρ c1A c1B : ℝ}
    (hA : SpikeChebOK DA m ρ c1A) (hB : SpikeChebOK DB m ρ c1B) :
    SpikeChebOK (SignedData.interp DA DB l c) m ρ ((1 - l) * c1A + l * c1B) := by
  intro u hu
  have hbB : ∀ i, DA.K < i → DB.b i = 0 := fun i hi => EB.hbK i (by rw [hc.K]; exact hi)
  have hcheb : chebPs (linSeq l DA.b DB.b) u = (1 - l) * chebPs DA.b u + l * chebPs DB.b u := by
    unfold chebPs
    rw [tsum_linSeq_fin EA.hbK hbB l
      (fun k => (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u)]
    ring
  have h1 := hA u hu
  have h2 := hB u hu
  rw [hc.sp] at h2
  have h1' := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 1 - l)
  have h2' := mul_le_mul_of_nonneg_left h2 hl0
  show (((DA.sp - m : ℕ) : ℝ)) * ((1 - l) * c1A + l * c1B) ≤
    (DA.sp : ℝ) * chebPs (linSeq l DA.b DB.b) u - m * chebPs (poisSeq ρ) u
  rw [hcheb]
  nlinarith [h1', h2']

/-! ### 5. Witness pairs and the class -/

/-- Two spike witnesses at the endpoint trials `DA`, `DB` with ONE configuration (the split of the
positives into rest and spikes, the count `m`, the phantom, the pole `ρ`).  The data that belong to
the trial are kept apart: `(P')` with its own `c1`, and the cost condition (which contains the
spike constant `cs` of the trial, so each endpoint keeps its own constant). -/
structure SpikePair (DA DB : SignedData) (c' : ℝ) {k q : ℕ} (xn : Fin k → ℝ) (gp : Fin q → ℝ) where
  q' : ℕ
  M : ℕ
  m : ℕ
  y : Fin q' → ℝ
  z : Fin M → ℝ
  zph : ℝ
  σ : Fin (q' + M) ≃ Fin q
  hσ : ∀ i, gp (σ i) = Fin.append y z i
  hM : M = 2 * m ∨ M + 1 = 2 * m
  hm : m < DA.sp
  hxcap : ∀ i, -(1 - c') ≤ xn i
  hy_not_spike : ∀ j, y j ≤ 1 - DA.θ
  hz_spike : ∀ i, 1 - DA.θ < z i
  hzph : 1 - DA.θ ≤ zph ∧ zph < 1
  ρ : ℝ
  c1A : ℝ
  c1B : ℝ
  hρ : |ρ| < 1
  hρd : ρ ≤ DA.τ ^ 2 * (1 - DA.θ)
  hc1A : 0 < c1A
  hc1B : 0 < c1B
  hPA : SpikeChebOK DA m ρ c1A
  hPB : SpikeChebOK DB m ρ c1B
  hcostA : SpikeCostOK DA m xn y z zph ρ
  hcostB : SpikeCostOK DB m xn y z zph ρ

/-- **The interpolated witness.**  A pair of endpoint witnesses gives a witness for every
`interp DA DB l c`, `l ∈ [0,1]`, with `c1 = (1-l) c1A + l c1B`. -/
def SpikePair.toWitness {DA DB : SignedData} {l c c' : ℝ} {k q : ℕ} {xn : Fin k → ℝ}
    {gp : Fin q → ℝ} (P : SpikePair DA DB c' xn gp) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (rA : SignedRegular DA) (rB : SignedRegular DB) (EA : SpikeEnv DA)
    (EB : SpikeEnv DB) (hx : ∀ b, |xn b| ≤ 1) (hy : ∀ j, |P.y j| ≤ 1) (hz : ∀ i, |P.z i| ≤ 1) :
    SpikeWitness (SignedData.interp DA DB l c) c' xn gp where
  q' := P.q'
  M := P.M
  m := P.m
  y := P.y
  z := P.z
  zph := P.zph
  σ := P.σ
  hσ := P.hσ
  hM := P.hM
  hm := P.hm
  hxcap := P.hxcap
  hy_not_spike := P.hy_not_spike
  hz_spike := P.hz_spike
  hzph := P.hzph
  ρ := P.ρ
  c1 := (1 - l) * P.c1A + l * P.c1B
  hρ := P.hρ
  hρd := P.hρd
  hc1 := by
    have hmin : min P.c1A P.c1B ≤ (1 - l) * P.c1A + l * P.c1B := by
      have h1 := mul_le_mul_of_nonneg_left (min_le_left P.c1A P.c1B) (by linarith : 0 ≤ 1 - l)
      have h2 := mul_le_mul_of_nonneg_left (min_le_right P.c1A P.c1B) hl0
      nlinarith
    exact lt_of_lt_of_le (lt_min P.hc1A P.hc1B) hmin
  hP := SpikeChebOK.interp hl0 hl1 hc EA EB P.hPA P.hPB
  hcost := SpikeCostOK.interp hl0 hl1 hc rA rB EA EB hx hy hz
    (abs_le.mpr ⟨by linarith [EA.hθ.2, P.hzph.1], P.hzph.2.le⟩) P.hcostA P.hcostB

/-- The class of the interpolated contract: the endpoint trials are regular and compatible, their
environments exist, and the configuration is a witness pair (with the quadrature cap `bcap`). -/
structure PairCls (DA DB : SignedData) (c' bcap : ℝ) {k q m1 m2 : ℕ} (xn : Fin k → ℝ)
    (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) where
  compat : InterpCompat DA DB
  rA : SignedRegular DA
  rB : SignedRegular DB
  EA : SpikeEnv DA
  EB : SpikeEnv DB
  P : SpikePair DA DB c' (Fin.append xn yn) (Fin.append gp yp)
  hbcap : DA.θ < bcap
  hyp : ∀ p, yp p ≤ 1 - bcap

/-- `SpikeCompareFixed` for the interpolated trial `interp DA DB l c`, `l ∈ [0,1]`, for every
configuration whose class gives a witness pair at the endpoints. -/
theorem spikeCompareFixed_interp (DA DB : SignedData) {l c c' : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc' : c' ∈ Ioc (0 : ℝ) 1) (hcθ : c' ≤ DA.θ) {k q m1 m2 : ℕ}
    {LR : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ}
    (hLR : ∀ xn gp yn yp, LR xn gp yn yp =
      logRatioZ DA.sp (Fin.append xn yn) (Fin.append gp yp))
    {Cls : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop}
    (hCls : ∀ xn gp yn yp, Cls xn gp yn yp → ∃ bcap, Nonempty (PairCls DA DB c' bcap xn gp yn yp)) :
    SpikeCompareFixed (SignedData.interp DA DB l c) c' Cls LR := by
  intro xn gp yn yp hxn hgp hyn hyp hcls
  obtain ⟨bcap, ⟨C⟩⟩ := hCls xn gp yn yp hcls
  have hxa : ∀ b, Fin.append xn yn b ∈ Ioo (-1 : ℝ) 0 :=
    fin_append_forall xn yn (fun t => t ∈ Ioo (-1 : ℝ) 0) hxn hyn
  have hga : ∀ p, Fin.append gp yp p ∈ Ioo (0 : ℝ) 1 :=
    fin_append_forall gp yp (fun t => t ∈ Ioo (0 : ℝ) 1) hgp hyp
  have hx : ∀ b, |Fin.append xn yn b| ≤ 1 := fun b =>
    abs_le.mpr ⟨(hxa b).1.le, by linarith [(hxa b).2]⟩
  have hy : ∀ j, |C.P.y j| ≤ 1 := fun j => by
    have := hga (C.P.σ (Fin.castAdd C.P.M j))
    rw [C.P.hσ, Fin.append_left] at this
    exact abs_le.mpr ⟨by linarith [this.1], this.2.le⟩
  have hz : ∀ i, |C.P.z i| ≤ 1 := fun i => by
    have := hga (C.P.σ (Fin.natAdd C.P.q' i))
    rw [C.P.hσ, Fin.append_right] at this
    exact abs_le.mpr ⟨by linarith [this.1], this.2.le⟩
  have W := C.P.toWitness (c := c) (l := l) hl0 hl1 C.compat C.rA C.rB C.EA C.EB hx hy hz
  have E := SpikeEnv.interp (c := c) hl0 hl1 C.compat C.rA C.rB C.EA C.EB
  have key := spikeCompareFixed_of_class (SignedData.interp DA DB l c) E (bcap := bcap) hc' hcθ
    (LR := LR) (fun xn gp yn yp => hLR xn gp yn yp) xn gp yn yp hxn hgp hyn hyp
    ⟨⟨W⟩, C.hbcap, C.hyp⟩
  exact key

/-- **`spikeFix` of `SignedNearBounds.ofEnds`.**  For every interval `i`, every `N` and every `α`,
the interpolated trial `interpFamily (αA i) (αB i) (DA i) (DB i) constant N α` satisfies
`SpikeCompareFixed` with the margin `cp i N α` and the class `Clsf`, provided the class implies a
witness pair at the endpoint trials `DA i N`, `DB i N` (same configuration, each endpoint with its
own spike constant `cs`). -/
theorem spikeFix_of_ends {I : ℕ} (αA αB : Fin I → ℝ) (DA DB : Fin I → ℕ → SignedData)
    (constant : ℕ → ℝ → ℝ) (cp : Fin I → ℕ → ℝ → ℝ) (cp_pos : ∀ i N α, 0 < cp i N α)
    (cp_le : ∀ i N α, cp i N α ≤ 1) (cp_theta : ∀ i N α, cp i N α ≤ (DA i N).θ)
    (Clsf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop)
    (LRf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ)
    (hLR : ∀ i N k q m1 m2 xn gp yn yp, LRf N k q m1 m2 xn gp yn yp =
      logRatioZ (DA i N).sp (Fin.append xn yn) (Fin.append gp yp))
    (hCls : ∀ i N α k q m1 m2 xn gp yn yp, Clsf N k q m1 m2 xn gp yn yp →
      ∃ bcap, Nonempty (PairCls (DA i N) (DB i N) (cp i N α) bcap xn gp yn yp)) :
    ∀ i N α k q m1 m2,
      SpikeCompareFixed (interpFamily (αA i) (αB i) (DA i) (DB i) constant N α) (cp i N α)
        (Clsf N k q m1 m2) (LRf N k q m1 m2) := by
  intro i N α k q m1 m2
  exact spikeCompareFixed_interp (DA i N) (DB i N) (interpL_nonneg (αA i) (αB i) α)
    (interpL_le_one (αA i) (αB i) α) ⟨cp_pos i N α, cp_le i N α⟩ (cp_theta i N α)
    (fun xn gp yn yp => hLR i N k q m1 m2 xn gp yn yp)
    (fun xn gp yn yp h => hCls i N α k q m1 m2 xn gp yn yp h)


end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.refTilt_linSeq
#print axioms CatalanMeasure.Signed.SpikeEnv.interp
#print axioms CatalanMeasure.Signed.Ipd_eq
#print axioms CatalanMeasure.Signed.Ipd_linSeq
#print axioms CatalanMeasure.Signed.numB_sub
#print axioms CatalanMeasure.Signed.numDiff_linSeq
#print axioms CatalanMeasure.Signed.spikeDenB_sub
#print axioms CatalanMeasure.Signed.denDiff_linSeq
#print axioms CatalanMeasure.Signed.spikeCost_split
#print axioms CatalanMeasure.Signed.costA_le
#print axioms CatalanMeasure.Signed.costLin_linSeq
#print axioms CatalanMeasure.Signed.costQuad_fin
#print axioms CatalanMeasure.Signed.costQuad_le
#print axioms CatalanMeasure.Signed.spikeCost_interp_le
#print axioms CatalanMeasure.Signed.costOK_iff
#print axioms CatalanMeasure.Signed.costGap_interp_le
#print axioms CatalanMeasure.Signed.SpikeCostOK.interp
#print axioms CatalanMeasure.Signed.SpikeChebOK.interp
#print axioms CatalanMeasure.Signed.SpikePair.toWitness
#print axioms CatalanMeasure.Signed.spikeCompareFixed_interp
#print axioms CatalanMeasure.Signed.spikeFix_of_ends

module

public import CatalanMeasure.GenD.Signed.MeasureOfDesign
public import CatalanMeasure.GenD.Signed.Gate
public import CatalanMeasure.GenD.Signed.DesignConst
public import CatalanMeasure.GenD.Signed.DecayOfData
public import CatalanMeasure.GenD.Uniform.Arithmetic.Exponents

@[expose] public section
set_option Elab.async false

/-! The D72 measure theorem from individually named, matching data hypotheses.
No D58 certificate, trial literal or decay cell is imported. -/

namespace CatalanMeasure.GenD.Signed
open CatalanMeasure.GenD Filter Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Analytic
open CatalanMeasure.Signed
noncomputable section

theorem dc72_normalizer_cut : dc72.toParameters.H 1 < 98 := by
  norm_num [dc72, Parameters.H, Parameters.C, Parameters.L,
    Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]

local notation "P72" => dc72.toParameters
local notation "τ72" => Data.Assembly.Generic.nodesτ dc72
local notation "G72" => Data.Assembly.Generic.gapPredicate dc72

/-- Measure 400 from the content, three sheet bounds, matched S1 weights,
payment budget and arithmetic nonvanishing for the same D72 determinant. -/
theorem catalan_irrationalityMeasure_400_of_data
    (lb : NullityLB P72) (target cost Psi0 eta price : ℝ)
    (hcontent : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.log ((canonicalNormalizer P72 dc72.admissible lb 98 dc72_normalizer_cut).D N) ≤
        (price + ε) * (N : ℝ) ^ 2)
    (hfirst : FreeFirstBound P72 target (72 * cost))
    (hnear : FreeNearBound P72 G72 (NodeSub τ72) target (72 * cost) (1 / 16))
    (hlarge : FreeLargeBound P72 G72 target (72 * cost) (1 / 16))
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ p m : ℕ, p + m = dc72.toParameters.n N →
      ∀ k : ℕ, k < dc72.toParameters.n N → ∀ a : Fin (66 * N),
      |(rowCommonFactor P72 N).eval (τ72 N a)| *
        |restrictedWeight P72 N k (τ72 N) a| *
        (CatalanMeasure.binomBeta p m k : ℝ) ≤
          108000 * (N : ℝ) * Real.exp (Psi0 * N))
    (hrho : 0 < 72 * cost + Psi0)
    (heta : 0 < eta) (heta2 : eta < 132)
    (hk : 2 * (27 / 50) * (72 * cost + Psi0) < 400)
    (hwin : 72 * cost + Psi0 <
      2 * ((27 / 50) * (72 * cost + Psi0) -
        (29 / 100000000) * (800 - (27 / 50) * (72 * cost + Psi0))))
    (hpay : 66 * (72 * cost + Psi0) +
      4 * 66 * (29 / 100000000) * 400 < eta * 400)
    (hgain : eta < 72 ^ 2 * (target - Real.log 2 / 2) - price)
    (hnv : ∃ N1 : ℕ, ∀ p : ℕ, N1 ≤ p → p.Prime →
      ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
        aeval ((a : ℝ) / b) (deltaPoly P72 p) ≠ 0) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(400 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  have hsmall := Data.Assembly.Generic.delta_small dc72 target cost Psi0 (1 / 16)
    (by simpa only [dc72_n0, Nat.cast_ofNat] using hfirst)
    (by simpa only [dc72_n0, Nat.cast_ofNat] using hnear)
    (by simpa only [dc72_n0, Nat.cast_ofNat] using hlarge) hweights
  exact Generic.catalan_irrationalityMeasure_of_design dc72
    { B := 400
      Z := canonicalNormalizer P72 dc72.admissible lb 98 dc72_normalizer_cut
      w := 27 / 50
      ρ := 72 * cost + Psi0
      η := eta
      κ := 400 / (72 * cost + Psi0)
      δ := 29 / 100000000
      pay := pay400_w2750 _ _ hrho heta heta2 hk hwin hpay
      gD := price
      D_growth := hcontent
      tΔ := 72 ^ 2 * (target - Real.log 2 / 2)
      delta_small := by simpa only [dc72_n0, Nat.cast_ofNat] using hsmall
      eta_le := hgain
      nonvanishing := hnv }

end
end CatalanMeasure.GenD.Signed

#print axioms CatalanMeasure.GenD.Signed.catalan_irrationalityMeasure_400_of_data
#print axioms CatalanMeasure.GenD.Signed.dc72_normalizer_cut

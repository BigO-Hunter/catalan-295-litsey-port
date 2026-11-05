module

public import CatalanMeasure.GenD.Signed.Theorem400
public import CatalanMeasure.GenD.Signed.Davis.S1Certificate
public import CatalanMeasure.GenD.Signed.Data.C3.Cert
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 10

/-! Scalar-only D72 instance, pinned to producer bytes. Hashes are provenance,
not a claim that numerical field/energy certificates have been proved in Lean.
The remaining hypotheses are the exact content and three sheet producers.
C14 refresh already includes old boundary eta + 1/1000000; do not add twice.
Trial eta stays 9/20. The frozen eta literal and chosen eta are now identical.
Content price is (1057/2) log2 + 19129/2 - archived full-area + snapshot loss.
Rebinding replaces the generated scalar literal block and source hash block together.
No Trial/Consts/DesignInstance or held compatibility module is imported. -/
-- SHA256 trials72/frozen-margin72.json: a52dcc638d9e6a934b1ef3a694096ed086b40449ec152b187e1608064435b5bf
-- SHA256 trials72/thresholds72.json: 67a92d1bb51c4091f4da71038742b567f0cb9d6d237ae0d094dda53db9e938fd
-- SHA256 trials72/side-config72.json: 6d592858ed57b0dab79bae0ec974b7e7110ac288bdd267746e28121b6e3e4701
-- SHA256 trials72/spike-costs72.json: 8e9ac7e44cf42bc5d4dfcbaf65a5c0fd5d127c55a9c822e9b23bad25ec2f2417
-- SHA256 content72/ledger72.json: 0a4710e1c09c78d58ae85f138afeae173134c7d41be9f4746a5c81e6876bd48e
-- SHA256 content72/gate-source-S.json: 0c4fd787bd8f78e591c0862c39421d8bfe4418979e161a0ae84f64ff65c20e3d
-- SHA256 content72/CONTENT72-LEAN.md: db0b0200d435de80fb68d4efcc2d92292f8a50985d3f703eeaa5060d1c8056d5
-- SHA256 trials72/trial72-0.json: ba95606714f61bd596ecc08aa344ed881077bfef96341520833648755c913716
-- SHA256 trials72/trial72-1.json: 169530579087d051e245d7283b88c65a4b3835c62bffb88300b0ffbc56fb2c77
-- SHA256 trials72/trial72-2.json: e8288ccfec96cdd36417e1c5673680bc153f7d72616a6ae1e9142bea3494c345
-- SHA256 trials72/gen_emit.py: fadbd5d602e4d368673422af640e5e740449db31302213ce4a0d07fd57775d0d
-- SHA256 trials72/frozen_margin72.py: 3eb7ca4426feb3300043d22a9bbf37114e26b0aad72edabc16372e779c0f89d3

namespace CatalanMeasure.GenD.Signed.Davis.ScalarInstance72
open Filter Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.Signed
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD.Uniform.Arithmetic
noncomputable section

local notation "P72" => dc72.toParameters

def cost72 : ℝ := 3604373 / 1000000
def psi72 : ℝ := 54377 / 500
def frozenEta72 : ℝ := 151911097 / 2500000
def eta72 : ℝ := 151911097 / 2500000
def baseTarget72 : ℝ := 1132420467 / 500000000
def gain72 : ℝ := 639543 / 50000
def contentLoss72 : ℝ := 11111874115390747 / 100000000000000000
def contentBeta72 : ℝ := 4291778436603084806023571908665446593632023 / 450344200156521455970900000000000000000
def snapshotS72 : ℝ := 4797358369884609253 / 100000000000000000
def window72 : ℝ := 27 / 50
def gateDelta72 : ℝ := 29 / 100000000
def csp72 : ℝ := 5 / 4
def trialEta72 : ℝ := 9 / 20
def Dtop72 : ℝ := 13 / 5000
def dsp72 : ℝ := 17 / 100
def theta72 : ℝ := 1 / 1000
def C1_72 : ℝ := 467829 / 1000000
def countCut72 : ℝ := 142 / 125
def target72 : ℝ := baseTarget72 + gain72 / 72 ^ 2
def price72 : ℝ := (1057 / 2 : ℝ) * Real.log 2 + contentBeta72
def rho72 : ℝ := 72 * cost72 + psi72
def countSlope72 : ℝ := 72 * (Dtop72 / dsp72 + C1_72 * theta72)
def G72 (x : ℝ) : Prop := x ≤ -(19501 / 100000 : ℝ) ∨ (98749 / 1000000 : ℝ) ≤ x

theorem window_eq : window72 = (27 / 50 : ℝ) := rfl

theorem hrho : 0 < 72 * cost72 + psi72 := by norm_num [cost72, psi72]
theorem heta : 0 < eta72 := by norm_num [eta72]
theorem heta2 : eta72 < 132 := by norm_num [eta72]
theorem hk : 2 * (27 / 50) * (72 * cost72 + psi72) < (400 : ℝ) := by
  norm_num [cost72, psi72]
theorem hwin : 72 * cost72 + psi72 <
    2 * ((27 / 50) * (72 * cost72 + psi72) -
      (29 / 100000000) * (800 - (27 / 50) * (72 * cost72 + psi72))) := by
  norm_num [cost72, psi72]
theorem hpay : 66 * (72 * cost72 + psi72) +
    4 * 66 * (29 / 100000000) * 400 < eta72 * 400 := by
  norm_num [cost72, psi72, eta72]

/-- The C14 payment repair retains strict gain even at the conservative rational S. -/
theorem hgain_snapshot : eta72 < snapshotS72 + gain72 := by
  norm_num [eta72, snapshotS72, gain72]

/-- Exact gain for the same content price, using Mathlib's certified log2 upper bound. -/
theorem hgain : eta72 < 72 ^ 2 * (target72 - Real.log 2 / 2) - price72 := by
  have hl := Real.log_two_lt_d9
  norm_num at hl
  norm_num [eta72, target72, baseTarget72, gain72, price72, contentBeta72]
  linarith only [hl]

theorem psi_margin : psi072 < psi72 := by
  exact psi072_strict

theorem csp_checks :
    (1299401 / 1048576 : ℝ) ≤ csp72 ∧
    (20708361 / 16777216 : ℝ) ≤ csp72 ∧
    (39389 / 32768 : ℝ) ≤ csp72 := by
  norm_num [csp72]

theorem trial_split : trialEta72 = (9 / 20 : ℝ) ∧
    1 - 2 * trialEta72 = (1 / 10 : ℝ) := by norm_num [trialEta72]

theorem count_slope_eq : countSlope72 = (2411577837 / 2125000000 : ℝ) := by
  norm_num [countSlope72, Dtop72, dsp72, C1_72, theta72]

theorem count_cut_constants :
    0 < Dtop72 ∧ 0 < dsp72 ∧ 0 ≤ theta72 ∧ 0 ≤ C1_72 ∧
    countSlope72 < countCut72 ∧ countCut72 < (57 / 50 : ℝ) := by
  norm_num [Dtop72, dsp72, theta72, C1_72, countSlope72, countCut72]

/-- Three units pay the +1 inside the ceiling, its rounding, and the outside +1. -/
theorem count_cut_room (N : ℕ) (hN : 2632 ≤ N) :
    countSlope72 * (N : ℝ) + 3 ≤ countCut72 * N := by
  have hNr : (2632 : ℝ) ≤ N := by exact_mod_cast hN
  rw [count_slope_eq]
  norm_num [countCut72]
  linarith only [hNr]

theorem count_cut (N : ℕ) (hN : 2632 ≤ N) :
    (⌈countSlope72 * (N : ℝ) + 1⌉₊ : ℝ) + 1 ≤ countCut72 * N := by
  have hs : 0 ≤ countSlope72 := by rw [count_slope_eq]; norm_num
  have hx : 0 ≤ countSlope72 * (N : ℝ) + 1 := by positivity
  have hc := Nat.ceil_lt_add_one hx
  have hr := count_cut_room N hN
  linarith only [hc, hr]

/-- One final scalar instance: all payment/gain hypotheses are discharged.
Only matching content and sheet certificates remain; geometry, S1 and C3 are built. -/
theorem catalan_irrationalityMeasure_400_of_producer_data
    (lb : NullityLB P72)
    (hcontent : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.log ((canonicalNormalizer P72 dc72.admissible lb 98 dc72_normalizer_cut).D N) ≤
        (price72 + ε) * (N : ℝ) ^ 2)
    (hfirst : FreeFirstBound P72 target72 (72 * cost72))
    (hnear : FreeNearBound P72 G72 (NodeSub tau72) target72 (72 * cost72) (1 / 16))
    (hlarge : FreeLargeBound P72 G72 target72 (72 * cost72) (1 / 16)) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(400 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  apply Generic.catalan_irrationalityMeasure_400_of_nodes tau72 G72
    tau72_injective tau72_mem tau72_ne_zero tau72_support lb
    target72 cost72 psi72 eta72 price72 hcontent hfirst hnear hlarge
    _ hrho heta heta2 hk hwin hpay hgain Data.C3.nonvanishing_dc72
  simpa only [Parameters.n, dc72_n0, psi72] using S1Certificate.hweights72

end
end CatalanMeasure.GenD.Signed.Davis.ScalarInstance72

#print axioms CatalanMeasure.GenD.Signed.Davis.ScalarInstance72.hrho
#print axioms CatalanMeasure.GenD.Signed.Davis.ScalarInstance72.hpay
#print axioms CatalanMeasure.GenD.Signed.Davis.ScalarInstance72.hgain_snapshot
#print axioms CatalanMeasure.GenD.Signed.Davis.ScalarInstance72.hgain
#print axioms CatalanMeasure.GenD.Signed.Davis.ScalarInstance72.psi_margin
#print axioms CatalanMeasure.GenD.Signed.Davis.ScalarInstance72.csp_checks
#print axioms CatalanMeasure.GenD.Signed.Davis.ScalarInstance72.count_cut
#print axioms CatalanMeasure.GenD.Signed.Davis.ScalarInstance72.catalan_irrationalityMeasure_400_of_producer_data

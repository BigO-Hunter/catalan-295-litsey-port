module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SheetBindings
public import CatalanMeasure.GenD.DesignInstance.PositiveControl.Near
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 100000
namespace CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceNear
open Set CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial
open ReferenceData
noncomputable section
/-! C23: avoid the reference-near cover by the existing one-variable theorem.
Data: chebengine/production72/standalone/manifest.json; exact p1 independently
recomputed from frozen positive72.json. All logarithm and derivative checks below
are kernel checked; an Arb interval is not used as a proof. -/
def p1 : ℚ := 38981821736761334053339/219902325555200000000000
def firstQ (d : SeqQ) : ℚ := d.f.getD 0 0 + tailValQ d.tail 1
theorem sequence_one (d : SeqQ) :
    tseq (fQ d.f) (d.tail.map TailQ.toC) 1 = ((firstQ d : ℚ) : ℝ) := by
  unfold tseq
  rw [if_neg (Nat.succ_ne_zero 0), fQ_succ, ← tailValQ_spec]
  unfold firstQ
  push_cast
  rfl
-- kcost: 0.1s estimated: 75 tails with <=12 rational operations each plus finite head.
theorem secondP1_data : firstQ secondPData = p1 := by decide +kernel
theorem secondP_one : secondP 1 = (p1 : ℝ) := by
  change tseq (fQ secondPData.f) (secondPData.tail.map TailQ.toC) 1 = _
  rw [sequence_one, secondP1_data]

def nearBoxTerms72 : List LogTerm :=
  [⟨-11/12,0,1+(963/1250)^2,0⟩,⟨59/72,0,1541/2000,0⟩]

def nearBoxOK72 : Bool :=
  match sumLogs nearBoxTerms72 with
  | some ve => decide (ve.1+ve.2-(38981821736761334053339/219902325555200000000000)*(963/1250) ≤ -(77/100:ℚ))
  | none => false

theorem near_box72 :
    -(11/12:ℝ)*Real.log (1+(963/1250:ℝ)^2)+
      (59/72)*Real.log (1541/2000:ℝ)-(38981821736761334053339/219902325555200000000000)*(963/1250) ≤ -(77/100:ℝ) := by
  -- kcost: 1s estimated: two weighted rational logarithms; about10000 arithmetic steps including range/octant search.
  have hc : nearBoxOK72=true := by decide +kernel
  unfold nearBoxOK72 at hc
  split at hc
  · rename_i ve he
    have hh := sumLogs_spec he
    have hv : (nearBoxTerms72.map LogTerm.val).sum =
        -(11/12:ℝ)*Real.log (1+(963/1250:ℝ)^2)+
          (59/72)*Real.log (1541/2000:ℝ) := by
      simp only [nearBoxTerms72,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      rw [realLogTerm (-11/12) (1+(963/1250)^2) (by norm_num),
        realLogTerm (59/72) (1541/2000) (by norm_num)]
      norm_num
    rw [hv] at hh
    have hq : ve.1+ve.2-(38981821736761334053339/219902325555200000000000:ℚ)*(963/1250) ≤ -(77/100:ℚ) := of_decide_eq_true hc
    have hr : ((ve.1+ve.2-(38981821736761334053339/219902325555200000000000:ℚ)*(963/1250):ℚ):ℝ) ≤ ((-(77/100):ℚ):ℝ) := by
      exact_mod_cast hq
    push_cast at hr
    norm_num at hr
    linarith only [(abs_le.mp hh).2,hr]
  · simp at hc

theorem near_bound {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    -(11/12:ℝ)*Real.log (1+y^2)+(59/72)*Real.log y-secondP 1*y ≤ -(77/100:ℝ) := by
  apply CatalanMeasure.GenD.Signed.near_residual_field_le
    (a := 11/12) (ell := 59/72) (p0 := (p1:ℝ))
    (l := 963/1250) (u := 1541/2000)
    (by norm_num) (by norm_num) (by norm_num [p1]) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [p1]) (by norm_num [p1])
    (by simpa only [p1, Rat.cast_div, Rat.cast_ofNat] using near_box72)
    (by rw [secondP_one]) hy hy1

/-- Exactly the near field required by SheetBindings.SecondDecayBounds. -/
theorem secondDecay_near : ∀ y ∈ Ioo (0 : ℝ) 1,
    -CatalanMeasure.GenD.Analytic.gRes dc72.toParameters * Real.log (1+y^2) +
      (((dc72.toParameters.n0:ℝ)-2*dc72.toParameters.g0-1)/dc72.toParameters.n0)*Real.log y -
      secondP 1*y ≤ -(77/100:ℝ) := by
  intro y hy
  convert near_bound hy.1 hy.2.le using 1 <;>
    norm_num [CatalanMeasure.GenD.Analytic.gRes, dc72]
end
end CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceNear
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceNear.secondP1_data
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceNear.secondP_one
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceNear.near_box72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceNear.near_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceNear.secondDecay_near

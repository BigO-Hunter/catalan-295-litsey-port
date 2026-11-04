module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Cover
public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSM2
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
open AssemblyBindings
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private abbrev T : ℚ := ((-2784600393893 : ℚ) / 549755813888)
private abbrev K : ℚ := ((630019883697 : ℚ) / 137438953472)
abbrev S : ℚ := ((-4333909755572637 : ℚ) / 9007199254740992)

private theorem offset : smK T2.trial ≤ (K : ℝ) := by
  have ep : encT T2.trial.p.tail = some (-374182068496652202, 281) :=
    KappaBasics.tP_checked
  have ea : encS T2.trial.a.tail = some (3225998431658358, 40) :=
    KappaBasics.sA2_checked
  have hp := encl_tConst T2.trial.p.tail
  have ha := encl_sConst T2.trial.a.tail
  rw [ep] at hp
  rw [ea] at ha
  change Encl (cTp T2.trial) (ivOf (some (-374182068496652202, 281))) at hp
  change Encl (cSa T2.trial) (ivOf (some (3225998431658358, 40))) at ha
  -- kcost: 0.01 s estimated. One scalar comparison reuses two checked pole sums.
  exact sm_le (η := T2.trial.η) (B := K) hp ha (by decide +kernel)

private theorem selfDistance (p : List ℚ) : l1Q p p ≤ 0 := by
  induction p with
  | nil => simp [l1Q]
  | cons a p ih => simpa [l1Q, qAbs] using ih

theorem eventual : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -(19501/100000:ℝ) →
      (T2.D N).fNegM (groupedMarkedField dc72.toParameters N) x ≤ (S : ℝ) + ε := by
  have key := boundSM2 T2.smFq rfl rfl (δ := 0) (selfDistance _) (T := (T : ℝ))
    (by simpa [Rat.cast_div, Rat.cast_neg] using CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Cover.named)
  intro ε hε
  filter_upwards [key ε hε] with N hN x hx hcut
  have h := hN x hx hcut
  have hS : ((T + K : ℚ) : ℝ) ≤ (S : ℝ) :=
    (Rat.cast_le (K := ℝ)).mpr (show T + K ≤ S from by decide +kernel)
  simp only [Rat.cast_add, Rat.cast_zero, add_zero] at hS h
  linarith [offset]
#print axioms eventual
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSM2

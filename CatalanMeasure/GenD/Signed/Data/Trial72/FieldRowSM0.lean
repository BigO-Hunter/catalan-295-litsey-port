module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Cover
public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSM0
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
open AssemblyBindings
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private abbrev T : ℚ := ((-349229889121 : ℚ) / 68719476736)
private abbrev K : ℚ := ((5053722114275 : ℚ) / 1099511627776)
abbrev S : ℚ := ((-4374168466726137 : ℚ) / 9007199254740992)

private theorem offset : smK T0.trial ≤ (K : ℝ) := by
  have ep : encT T0.trial.p.tail = some (-374182068496652202, 281) :=
    KappaBasics.tP_checked
  have ea : encS T0.trial.a.tail = some (2781564582940640, 40) :=
    KappaBasics.sA0_checked
  have hp := encl_tConst T0.trial.p.tail
  have ha := encl_sConst T0.trial.a.tail
  rw [ep] at hp
  rw [ea] at ha
  change Encl (cTp T0.trial) (ivOf (some (-374182068496652202, 281))) at hp
  change Encl (cSa T0.trial) (ivOf (some (2781564582940640, 40))) at ha
  -- kcost: 0.01 s estimated. One scalar comparison reuses two checked pole sums.
  exact sm_le (η := T0.trial.η) (B := K) hp ha (by decide +kernel)

private theorem selfDistance (p : List ℚ) : l1Q p p ≤ 0 := by
  induction p with
  | nil => simp [l1Q]
  | cons a p ih => simpa [l1Q, qAbs] using ih

theorem eventual : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -(19501/100000:ℝ) →
      (T0.D N).fNegM (groupedMarkedField dc72.toParameters N) x ≤ (S : ℝ) + ε := by
  have key := boundSM0 T0.smFq rfl rfl (δ := 0) (selfDistance _) (T := (T : ℝ))
    (by simpa [Rat.cast_div, Rat.cast_neg] using CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Cover.named)
  intro ε hε
  filter_upwards [key ε hε] with N hN x hx hcut
  have h := hN x hx hcut
  have hS : ((T + K : ℚ) : ℝ) ≤ (S : ℝ) :=
    (Rat.cast_le (K := ℝ)).mpr (show T + K ≤ S from by decide +kernel)
  simp only [Rat.cast_add, Rat.cast_zero, add_zero] at hS h
  linarith [offset]
#print axioms eventual
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSM0

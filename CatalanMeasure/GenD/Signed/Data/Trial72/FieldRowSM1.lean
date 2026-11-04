module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Cover
public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSM1
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
open AssemblyBindings
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private abbrev T : ℚ := ((-5570396054187 : ℚ) / 1099511627776)
private abbrev K : ℚ := ((5037236724349 : ℚ) / 1099511627776)
abbrev S : ℚ := ((-4367641230028111 : ℚ) / 9007199254740992)

private theorem offset : smK T1.trial ≤ (K : ℝ) := by
  have ep : encT T1.trial.p.tail = some (-374182068496652202, 281) :=
    KappaBasics.tP_checked
  have ea : encS T1.trial.a.tail = some (3321757840045031, 40) :=
    KappaBasics.sA1_checked
  have hp := encl_tConst T1.trial.p.tail
  have ha := encl_sConst T1.trial.a.tail
  rw [ep] at hp
  rw [ea] at ha
  change Encl (cTp T1.trial) (ivOf (some (-374182068496652202, 281))) at hp
  change Encl (cSa T1.trial) (ivOf (some (3321757840045031, 40))) at ha
  -- kcost: 0.01 s estimated. One scalar comparison reuses two checked pole sums.
  exact sm_le (η := T1.trial.η) (B := K) hp ha (by decide +kernel)

private theorem selfDistance (p : List ℚ) : l1Q p p ≤ 0 := by
  induction p with
  | nil => simp [l1Q]
  | cons a p ih => simpa [l1Q, qAbs] using ih

theorem eventual : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -(19501/100000:ℝ) →
      (T1.D N).fNegM (groupedMarkedField dc72.toParameters N) x ≤ (S : ℝ) + ε := by
  have key := boundSM1 T1.smFq rfl rfl (δ := 0) (selfDistance _) (T := (T : ℝ))
    (fun y hy => by
      have h := CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Cover.named y (by norm_num [Set.mem_Ioc] at hy ⊢; exact hy)
      norm_num [T] at h ⊢
      exact h)
  intro ε hε
  filter_upwards [key ε hε] with N hN x hx hcut
  have h := hN x hx hcut
  have hS : ((T + K : ℚ) : ℝ) ≤ (S : ℝ) :=
    (Rat.cast_le (K := ℝ)).mpr (show T + K ≤ S from by decide +kernel)
  simp only [Rat.cast_add, Rat.cast_zero, add_zero] at hS h
  linarith [offset]
#print axioms eventual
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSM1

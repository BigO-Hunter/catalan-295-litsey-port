module
public import CatalanMeasure.GenD.Signed.Data.Trial72.Rows72
public import CatalanMeasure.GenD.Signed.Data.Trial72.LinkData72
public import CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceAbs72
public import CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneEndpoints72
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkSupLim
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearEndpoint72
open Set Filter CatalanMeasure.GenD.Analytic OAI.InternalCatalan CatalanMeasure.Parametric
open CatalanMeasure.Signed CatalanMeasure.Signed.Consts
open CatalanMeasure.GenD.Signed.Data.Assembly
open AssemblyBindings Inputs72 ReferenceData Davis.ScalarInstance72 StandaloneBudgets
noncomputable section

def gapRegion : Set ℝ := {x | 0 < |x| ∧ |x| < 7/100}

structure Regions : Prop where
  gap : ∀ x ∈ gapRegion, rowFieldG (3/8) (1/9) (97/72) secondP secondV x ≤ secondMX-1/25
  sup : ∀ x ∈ Ioo (1-1/1000 : ℝ) 1,
    rowFieldG (3/8) (1/9) (97/72) secondP secondV x ≤ secondMX-17/100

private theorem gap_sub : gapRegion ⊆ Ico (-1 : ℝ) 0 ∪ Ioo 0 1 := by
  intro x hx
  have h := abs_lt.mp (hx.2.trans (by norm_num : (7/100 : ℝ) < 1))
  rcases lt_or_gt_of_ne (abs_pos.mp hx.1) with hn | hp
  · exact Or.inl ⟨h.1.le,hn⟩
  · exact Or.inr ⟨hp,h.2⟩

private theorem sup_sub : Ioo (1-1/1000 : ℝ) 1 ⊆ Ico (-1 : ℝ) 0 ∪ Ioo 0 1 := by
  intro x hx
  exact Or.inr ⟨by linarith [hx.1],hx.2⟩

private theorem gap_eventual (B : Regions) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, 0 < |x| → |x| < 7/100 →
      freeRowX dc72.toParameters N secondP secondV x ≤ secondMX+(13/100000)/4-1/25 := by
  have h := freeRowX_eventually_of_region dc72.admissible secondP_summable secondV_summable
    (by norm_num [dc72] : (3/8 : ℝ) = _) (by norm_num [dc72] : (1/9 : ℝ) = _)
    (by norm_num [dc72] : (97/72 : ℝ) = _) gap_sub B.gap
    (ε := (13/100000)/4) (by norm_num)
  filter_upwards [h] with N hN x hx hy
  exact (hN x ⟨hx,hy⟩).trans_eq (by ring)

private theorem sup_eventual (B : Regions) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (1-1/1000 : ℝ) 1,
      freeRowX dc72.toParameters N secondP secondV x ≤ secondMX+(13/100000)/4-17/100 := by
  have h := freeRowX_eventually_of_region dc72.admissible secondP_summable secondV_summable
    (by norm_num [dc72] : (3/8 : ℝ) = _) (by norm_num [dc72] : (1/9 : ℝ) = _)
    (by norm_num [dc72] : (97/72 : ℝ) = _) sup_sub B.sup
    (ε := (13/100000)/4) (by norm_num)
  filter_upwards [h] with N hN x hx
  exact (hN x hx).trans_eq (by ring)

/-- The exact consumer contract; producers may supply these finite-N
regional bounds directly or use the limit-field adapter above. -/
structure EventualRegions : Prop where
  gap : ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, 0 < |x| → |x| < 7/100 →
    freeRowX dc72.toParameters N secondP secondV x ≤ secondMX+(13/100000)/4-1/25
  sup : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (1-1/1000 : ℝ) 1,
    freeRowX dc72.toParameters N secondP secondV x ≤ secondMX+(13/100000)/4-17/100

theorem Regions.eventual (B : Regions) : EventualRegions :=
  ⟨gap_eventual B,sup_eventual B⟩

def data (B : EventualRegions) :=
  LinkData72.data I (MXRef := secondMX) (targetOld := baseTarget72) (costOld := cost72)
    (c2 := 72*cost72) rfl
    (by intro i α hα; fin_cases i
        · exact ⟨hα.1,hα.2.trans (by norm_num : (1/200 : ℝ) ≤ 1/16)⟩
        · exact ⟨(by norm_num : (0 : ℝ) ≤ 1/200).trans hα.1,hα.2⟩)
    (fun _ => rfl) (fun _ => rfl) Inputs72.excess_cap Inputs72.excess_top
    B.gap B.sup
    (by change (999/1000 : ℝ) ≤ 1-1/1000; norm_num)
    (by change (0 : ℝ) ≤ 999/1000; norm_num)
    (by change (0 : ℝ) ≤ 467829/1000000; norm_num)

theorem hnear (F : Rows72.FieldRows) (B : EventualRegions)
    (E0 : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T0.D N)))
    (E1 : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T1.D N)))
    (E2 : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T2.D N))) :
    FreeNearBound dc72.toParameters G72 (NodeSub Davis.tau72) target72 (72*cost72) (1/16) := by
  let R := Rows72.rows F E0 E1 E2
  have L := Generic.link_asym dc72 geometry72 I R (data B) StandaloneEndpoints72.reference
    rfl rfl rfl (by intros; assumption)
  exact AssemblyBindings.hnear I Inputs72.matches R StandaloneCertificates.reference
    CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneDecayBounds.reference
    (by norm_num) (by constructor <;> norm_num) ReferenceAbs72.hec L

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearEndpoint72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearEndpoint72.hnear

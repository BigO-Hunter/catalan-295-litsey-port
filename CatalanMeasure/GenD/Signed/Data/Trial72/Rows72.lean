module
public import CatalanMeasure.GenD.Signed.Data.Trial72.RowsBudget72
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeClassifier72
public import CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly0
public import CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly1
public import CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly2
public import CatalanMeasure.GenD.Signed.Data.Trial72.CurvAssembly01
public import CatalanMeasure.GenD.Signed.Data.Trial72.CurvAssembly12

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.Rows72
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm OAI.InternalCatalan
open CatalanMeasure.Parametric CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open CatalanMeasure.GenD.Signed.Data.Assembly
open CatalanMeasure.GenD.Signed.Data.Assembly.Generic
open Inputs72 AssemblyBindings RowsCaps72
noncomputable section

/-- External endpoint covers at the frozen physical thresholds. The constants,
interpolation, spike classification, and near budget are produced here. -/
structure FieldRows : Prop where

  hSnA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (-1 : ℝ) 0, (I.DA i N).fNeg x ≤ SnA i + ε

  hSpA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (I.DA i N).fPosS x ≤ SpA i + ε

  hSyA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (I.DA i N).fCol x ≤ SyA i + ε

  hnegA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (-1 : ℝ) 0,
      x ≤ -geometry72.gsN → (I.DA i N).fNegM (groupedMarkedField dc72.toParameters N) x ≤ (capE i).lamNA + ε

  hposA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DA i N).fPosMR (groupedMarkedField dc72.toParameters N) (remC (I.epsSplit i)) α x ≤ (capE i).lamPA α + ε

  hposTopA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DA i N).fPosMS (groupedMarkedField dc72.toParameters N) x ≤ (capE i).gPA α + ε

  hnearA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DA i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).lamSA α β + ε

  hnearTopA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DA i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).gSA α β + ε + (capE i).rSA α β * (-Real.log (1-x^2))

  hSnB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (-1 : ℝ) 0, (I.DB i N).fNeg x ≤ SnB i + ε

  hSpB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (I.DB i N).fPosS x ≤ SpB i + ε

  hSyB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (I.DB i N).fCol x ≤ SyB i + ε

  hnegB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (-1 : ℝ) 0,
      x ≤ -geometry72.gsN → (I.DB i N).fNegM (groupedMarkedField dc72.toParameters N) x ≤ (capE i).lamNB + ε

  hposB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DB i N).fPosMR (groupedMarkedField dc72.toParameters N) (remC (I.epsSplit i)) α x ≤ (capE i).lamPB α + ε

  hposTopB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DB i N).fPosMS (groupedMarkedField dc72.toParameters N) x ≤ (capE i).gPB α + ε

  hnearB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DB i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).lamSB α β + ε

  hnearTopB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DB i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).gSB α β + ε + (capE i).rSB α β * (-Real.log (1-x^2))


private theorem αtop {i : Fin 2} {α : ℝ} (h : α ∈ Icc (I.lo i) (I.hi i)) :
    α ≤ 1/16 := by
  fin_cases i
  · exact h.2.trans (by norm_num : (1/200 : ℝ) ≤ 1/16)
  · exact h.2

private theorem chord_box {a b s t α : ℝ} (hs : s ∈ Icc (-2 : ℝ) 2)
    (ht : t ∈ Icc (-2 : ℝ) 2) : chord a b s t α ∈ Icc (-2 : ℝ) 2 := by
  have h0 := interpL_nonneg a b α
  have h1 := sub_nonneg.mpr (interpL_le_one a b α)
  have hsl := mul_le_mul_of_nonneg_left hs.1 h1
  have hsu := mul_le_mul_of_nonneg_left hs.2 h1
  have htl := mul_le_mul_of_nonneg_left ht.1 h0
  have htu := mul_le_mul_of_nonneg_left ht.2 h0
  unfold chord
  constructor <;> nlinarith only [hsl,hsu,htl,htu]

private theorem capBox (i : Fin 2) (α β : ℝ) :
    (capE i).gPA α ∈ Icc (-2 : ℝ) 2 ∧ (capE i).lamPA α ∈ Icc (-2 : ℝ) 2 ∧
    (capE i).gPB α ∈ Icc (-2 : ℝ) 2 ∧ (capE i).lamPB α ∈ Icc (-2 : ℝ) 2 ∧
    (capE i).gSA α β ∈ Icc (-2 : ℝ) 2 ∧ (capE i).lamSA α β ∈ Icc (-2 : ℝ) 2 ∧
    (capE i).gSB α β ∈ Icc (-2 : ℝ) 2 ∧ (capE i).lamSB α β ∈ Icc (-2 : ℝ) 2 := by
  fin_cases i <;> simp only [capE,cap0,cap1,Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals first
    | apply chord_box <;> constructor <;> norm_num
    | constructor <;> norm_num

def rows (F : FieldRows)
    (E0 : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T0.D N)))
    (E1 : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T1.D N)))
    (E2 : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T2.D N))) :
    RowsAsym dc72 geometry72 I where
  SnA := SnA
  SnB := SnB
  SpA := SpA
  SpB := SpB
  SyA := SyA
  SyB := SyB

  hSnA := F.hSnA

  hSpA := F.hSpA

  hSyA := F.hSyA

  hSnB := F.hSnB

  hSpB := F.hSpB

  hSyB := F.hSyB

  cP := cP
  hcP := fun _ _ _ => le_rfl
  rA := rA
  rB := rB
  κc := κc
  hrA := by
    intro i ε hε
    fin_cases i
    · simpa only [dc72_n0] using RAssembly0.constant_bound ε hε
    · simpa only [dc72_n0] using RAssembly1.constant_bound ε hε
  hrB := by
    intro i ε hε
    fin_cases i
    · simpa only [dc72_n0] using RAssembly1.constant_bound ε hε
    · simpa only [dc72_n0] using RAssembly2.constant_bound ε hε
  hκ := by
    intro i ε hε
    fin_cases i
    · filter_upwards [CurvAssembly01.curvature_bound] with N hN
      exact (sub_le_self _ hε.le).trans hN
    · filter_upwards [CurvAssembly12.curvature_bound] with N hN
      exact (sub_le_self _ hε.le).trans hN
  Clsf := SpikeClassifier72.Clsf
  cp := SpikeClassifier72.cp
  cp_pos := by intro i N α; norm_num [SpikeClassifier72.cp]
  cp_le := by intro i N α; norm_num [SpikeClassifier72.cp]
  err_small := by
    intro i ε hε
    fin_cases i
    · filter_upwards [Generic.err_small dc72 AssemblyBindings.X0 hε] with N hN α _
      exact hN
    · filter_upwards [Generic.err_small dc72 AssemblyBindings.X1 hε] with N hN α _
      exact hN
  cp_theta := by intro i N α; fin_cases i <;> exact le_rfl
  hCls := SpikeClassifier72.hCls E0 E1 E2
  capE := capE
  hxc0 := by intro i; fin_cases i <;> norm_num [capE,cap0,cap1]
  hxc1 := by intro i; fin_cases i <;> norm_num [capE,cap0,cap1]
  hC1 := by intro i; fin_cases i <;> norm_num [capE,cap0,cap1]
  hrP := by intro i α hα; fin_cases i <;> norm_num [I,capE,cap0,cap1,remC]
  hrSA := by
    intro i α hα β hβ
    fin_cases i <;> simp [capE,cap0,cap1] <;> linarith [hβ.1]
  hrSB := by
    intro i α hα β hβ
    fin_cases i <;> simp [capE,cap0,cap1] <;> linarith [hβ.1]
  Bd := fun _ => 4
  Rbd := fun _ => 1
  hBdPA := by
    intro i α _
    have h := capBox i α 0
    linarith [h.1.2,h.2.1.1]
  hBdPB := by
    intro i α _
    have h := capBox i α 0
    linarith [h.2.2.1.2,h.2.2.2.1.1]
  hBdSA := by
    intro i α _ β _
    have h := capBox i α β
    linarith [h.2.2.2.2.1.2,h.2.2.2.2.2.1.1]
  hBdSB := by
    intro i α _ β _
    have h := capBox i α β
    linarith [h.2.2.2.2.2.2.1.2,h.2.2.2.2.2.2.2.1]
  hRP := by
    intro i α hα
    have ht := αtop hα
    fin_cases i <;> simp [capE,cap0,cap1] <;> linarith
  hRSA := by
    intro i α hα β hβ
    have ht := αtop hα
    fin_cases i <;> simp [capE,cap0,cap1] <;> linarith [hβ.2]
  hRSB := by
    intro i α hα β hβ
    have ht := αtop hα
    fin_cases i <;> simp [capE,cap0,cap1] <;> linarith [hβ.2]
  hgs := by intro i; fin_cases i <;> exact le_rfl
  hxc := by intro i; fin_cases i <;> exact le_rfl
  hC1le := by intro i; fin_cases i <;> exact le_rfl

  hnegA := F.hnegA

  hposA := F.hposA

  hposTopA := F.hposTopA

  hnearA := F.hnearA

  hnearTopA := F.hnearTopA

  hnegB := F.hnegB

  hposB := F.hposB

  hposTopB := F.hposTopB

  hnearB := F.hnearB

  hnearTopB := F.hnearTopB

  zb := RowsBudget72.zb
  hZB := RowsBudget72.hZB
  hbudLo := by
    intro i α hα
    exact RowsBudget72.budget i hα (show (1/4 : ℝ) ∈ Icc 0 (1/2) by constructor <;> norm_num)
  hbudHi := by
    intro i α hα
    exact RowsBudget72.budget i hα (show (1/2 : ℝ) ∈ Icc 0 (1/2) by constructor <;> norm_num)

end
end CatalanMeasure.GenD.Signed.Data.Trial72.Rows72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.Rows72.rows

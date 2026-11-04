module
public import CatalanMeasure.GenD.Signed.Data.Trial72.Rows72
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRows72
open Set Filter CatalanMeasure.Signed CatalanMeasure.GenD.Analytic
open Inputs72 AssemblyBindings RowsCaps72
noncomputable section

structure EndpointA (i : Fin 2) : Prop where
  hSn : {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (-1 : ℝ) 0, (I.DA i N).fNeg x ≤ SnA i + ε
  hSp : {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (I.DA i N).fPosS x ≤ SpA i + ε
  hSy : {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (I.DA i N).fCol x ≤ SyA i + ε
  hneg : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (-1 : ℝ) 0,
      x ≤ -geometry72.gsN → (I.DA i N).fNegM (groupedMarkedField dc72.toParameters N) x ≤ (capE i).lamNA + ε
  hpos : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DA i N).fPosMR (groupedMarkedField dc72.toParameters N) (remC (I.epsSplit i)) α x ≤ (capE i).lamPA α + ε
  hposTop : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DA i N).fPosMS (groupedMarkedField dc72.toParameters N) x ≤ (capE i).gPA α + ε
  hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DA i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).lamSA α β + ε
  hnearTop : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DA i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).gSA α β + ε + (capE i).rSA α β * (-Real.log (1-x^2))

structure EndpointB (i : Fin 2) : Prop where
  hSn : {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (-1 : ℝ) 0, (I.DB i N).fNeg x ≤ SnB i + ε
  hSp : {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (I.DB i N).fPosS x ≤ SpB i + ε
  hSy : {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (I.DB i N).fCol x ≤ SyB i + ε
  hneg : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (-1 : ℝ) 0,
      x ≤ -geometry72.gsN → (I.DB i N).fNegM (groupedMarkedField dc72.toParameters N) x ≤ (capE i).lamNB + ε
  hpos : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DB i N).fPosMR (groupedMarkedField dc72.toParameters N) (remC (I.epsSplit i)) α x ≤ (capE i).lamPB α + ε
  hposTop : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DB i N).fPosMS (groupedMarkedField dc72.toParameters N) x ≤ (capE i).gPB α + ε
  hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DB i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).lamSB α β + ε
  hnearTop : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DB i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).gSB α β + ε + (capE i).rSB α β * (-Real.log (1-x^2))

/-- Each middle-trial endpoint carries the caps of its own interval. -/
theorem ofEndpoints (a0 : EndpointA 0) (a1 : EndpointA 1)
    (b0 : EndpointB 0) (b1 : EndpointB 1) : Rows72.FieldRows where
  hSnA := by
    intro i
    fin_cases i
    · exact a0.hSn
    · exact a1.hSn
  hSpA := by
    intro i
    fin_cases i
    · exact a0.hSp
    · exact a1.hSp
  hSyA := by
    intro i
    fin_cases i
    · exact a0.hSy
    · exact a1.hSy
  hnegA := by
    intro i
    fin_cases i
    · exact a0.hneg
    · exact a1.hneg
  hposA := by
    intro i
    fin_cases i
    · exact a0.hpos
    · exact a1.hpos
  hposTopA := by
    intro i
    fin_cases i
    · exact a0.hposTop
    · exact a1.hposTop
  hnearA := by
    intro i
    fin_cases i
    · exact a0.hnear
    · exact a1.hnear
  hnearTopA := by
    intro i
    fin_cases i
    · exact a0.hnearTop
    · exact a1.hnearTop
  hSnB := by
    intro i
    fin_cases i
    · exact b0.hSn
    · exact b1.hSn
  hSpB := by
    intro i
    fin_cases i
    · exact b0.hSp
    · exact b1.hSp
  hSyB := by
    intro i
    fin_cases i
    · exact b0.hSy
    · exact b1.hSy
  hnegB := by
    intro i
    fin_cases i
    · exact b0.hneg
    · exact b1.hneg
  hposB := by
    intro i
    fin_cases i
    · exact b0.hpos
    · exact b1.hpos
  hposTopB := by
    intro i
    fin_cases i
    · exact b0.hposTop
    · exact b1.hposTop
  hnearB := by
    intro i
    fin_cases i
    · exact b0.hnear
    · exact b1.hnear
  hnearTopB := by
    intro i
    fin_cases i
    · exact b0.hnearTop
    · exact b1.hnearTop
end
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRows72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.FieldRows72.ofEndpoints

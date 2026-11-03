module
public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.LinkExcess72
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.Data.Trial72.Inputs72
open Set Filter CatalanMeasure.Signed
open CatalanMeasure.GenD.Signed.Data.Assembly
open CatalanMeasure.GenD.Signed.Data.Assembly.Generic
open AssemblyBindings Davis.ScalarInstance72
noncomputable section

private theorem compat01 (N : ℕ) : InterpCompat (T0.D N) (T1.D N) :=
  Core.famD_compat dc72 T0.params T1.params (by decide +kernel) (by rfl) N

private theorem compat12 (N : ℕ) : InterpCompat (T1.D N) (T2.D N) :=
  Core.famD_compat dc72 T1.params T2.params (by decide +kernel) (by rfl) N

def I : InputsAsym dc72 geometry72 where
  XA := XA
  XB := XB
  DA := DA
  DB := DB
  hDA := hDA
  hDB := hDB
  target := target72
  cost := cost72
  α1 := 1/16
  α1_nonneg := by norm_num
  lo := ![0,1/200]
  hi := ![1/200,1/16]
  αA := ![0,1/200]
  αB := ![1/200,1/16]
  κlo := fun _ => 1/4
  κhi := fun _ => 1/2
  epsSplit := ![1/10,1/10]
  epsSplit_pos := by intro i; fin_cases i <;> norm_num
  epsSplit_le := by intro i; fin_cases i <;> norm_num
  cover := by
    intro α h0 h1
    rcases le_total α (1/200 : ℝ) with h | h
    · exact ⟨0,h0,h⟩
    · exact ⟨1,h,h1⟩
  hlo0 := by intro i; fin_cases i <;> norm_num
  hhi1 := by intro i; fin_cases i <;> norm_num
  hends := by
    intro i
    fin_cases i
    · exact ⟨by norm_num, le_rfl, le_rfl, compat01, Eventually.of_forall T0.regularD,
        Eventually.of_forall T1.regularD⟩
    · exact ⟨by norm_num, le_rfl, le_rfl, compat12, Eventually.of_forall T1.regularD,
        Eventually.of_forall T2.regularD⟩
  massA := by
    intro i
    apply Eventually.of_forall
    intro N
    fin_cases i
    · simpa [DA,T0.alpha] using (T0.massD N).symm
    · simpa [DA,T1.alpha] using (T1.massD N).symm
  massB := by
    intro i
    apply Eventually.of_forall
    intro N
    fin_cases i
    · simpa [DB,T1.alpha] using (T1.massD N).symm
    · simpa [DB,T2.alpha] using (T2.massD N).symm
  etaA := by
    intro i N
    fin_cases i
    · simpa [DA] using T0.etaD N
    · simpa [DA] using T1.etaD N
  gs := geometry72.gsP
  xc := geometry72.xc
  C1 := geometry72.C1
  gs_eq := rfl
  xc_eq := rfl
  hC := rfl
  umin := geometry72.umin
  humin := fun _ => rfl

theorem matches : InputsMatch I := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem excess_cap (i : Fin 2) (α : ℝ) (_ : α ∈ Icc (I.lo i) (I.hi i)) :
    excess baseTarget72 cost72 I.target (72*cost72) (13/100000) (dc72.n0 : ℝ) α ≤ 13/5000 :=
  LinkExcess72.excess_bound α

theorem excess_top (α : ℝ) (_ : α ∈ Icc 0 I.α1) :
    excess baseTarget72 cost72 I.target (72*cost72) (13/100000) (dc72.n0 : ℝ) α ≤ 13/5000 :=
  LinkExcess72.excess_bound α

end
end CatalanMeasure.GenD.Signed.Data.Trial72.Inputs72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.Inputs72.I
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.Inputs72.matches

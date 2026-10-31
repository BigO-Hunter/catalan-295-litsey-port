module

public import CatalanMeasure.GenD.Signed.Data.Trial.T2Data

/-! Trial 2: the data checks of `TrialForm.Spec` (tails, η, positivity and density caps of the species) and the mass. -/

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Trial.T2
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
open CatalanMeasure.Cert (TailQ)

set_option maxRecDepth 1000000
set_option Elab.async false

theorem pcT0_ok : PieceOK pcT0.toPiece :=
  pieceOK_of pcT0 (qlist (raw_ints% [1, 256, 1, 128, 1, 64, 1, 32, 1, 16, 5, 64, 3, 32, 1, 8, 1, 4, 1, 2, 3, 4])) (by decide +kernel) (by decide +kernel)

theorem pcF0_ok : PieceOK pcF0.toPiece :=
  pieceOK_of pcF0 (qlist (raw_ints% [401, 20000, 3609, 160000, 401, 16000, 1203, 40000, 401, 10000, 1203, 20000, 2807, 40000, 401, 5000])) (by decide +kernel) (by decide +kernel)

theorem pcF1_ok : PieceOK pcF1.toPiece :=
  pieceOK_of pcF1 (qlist (raw_ints% [5307, 20000, 3703, 10000, 2901, 5000, 7901, 10000])) (by decide +kernel) (by decide +kernel)

def capsT : List (ℚ × List ℚ) := [(((49 : ℚ) / 32), qlist (raw_ints% [1, 4, 1, 2, 3, 4, 7, 8, 15, 16]))]

def capsF : List (ℚ × List ℚ) := [(((17 : ℚ) / 64), qlist (raw_ints% [])), (((169 : ℚ) / 64), qlist (raw_ints% [3703, 10000, 2901, 5000, 7901, 10000]))]

theorem capsT_ok : capsOK trial.qT capsT = true := by decide +kernel

theorem capsF_ok : capsOK trial.qF capsF = true := by decide +kernel

/-- The density cap `Cb` of the trial (`BD (μ b) Cb` for both species). -/
def Cb : ℚ := ((93 : ℚ) / 32)

theorem capsT_le : (capsT.map Prod.fst).sum ≤ Cb := by decide +kernel

theorem capsF_le : (capsF.map Prod.fst).sum ≤ Cb := by decide +kernel

theorem dataOK {C : ℝ} (hC : ((Cb : ℚ) : ℝ) ≤ C) : trial.DataOK C where
  hvT := by decide +kernel
  haT := by decide +kernel
  hpT := by decide +kernel
  hη0 := by decide +kernel
  hη1 := by decide +kernel
  hRt := rfl
  pT := List.forall_mem_cons.mpr ⟨pcT0_ok, List.forall_mem_nil _⟩
  pF := List.forall_mem_cons.mpr ⟨pcF0_ok, List.forall_mem_cons.mpr ⟨pcF1_ok, List.forall_mem_nil _⟩⟩
  bdT := BD_mono (polyMeas_BD _ _ capsT_ok).2 (le_trans (by exact_mod_cast capsT_le) hC)
  bdF := BD_mono (polyMeas_BD _ _ capsF_ok).2 (le_trans (by exact_mod_cast capsF_le) hC)

/-- **`TrialForm.Spec`** of the trial for a family member with the trial's data. -/
theorem spec (D : SignedData) (hτ : D.τ ∈ Set.Ioo (0 : ℝ) 1)
    (hv : D.v = tseq (fQ trial.v.f) (trial.v.tail.map TailQ.toC))
    (ha : D.a = tseq (fQ trial.a.f) (trial.a.tail.map TailQ.toC))
    (hp : D.p = tseq (fQ trial.p.f) (trial.p.tail.map TailQ.toC))
    (hη : D.η = trial.η) (hR : D.R = fun n => fQ trial.R.f (n + 1)) (hSup : D.Sup = trial.Sup)
    (ht : D.t = mneg D.μ D.τ)
    (hμT : D.μ true = polyMeas (trial.qT.map PieceQ.toPiece))
    (hμF : D.μ false = polyMeas (trial.qF.map PieceQ.toPiece))
    (hCb : ((Cb : ℚ) : ℝ) ≤ D.Cb) : trial.form.Spec D :=
  TrialQ.spec trial D hτ hv ha hp hη hR hSup ht hμT hμF (dataOK hCb)

/-- The phantom bound of the Λ tilt: `|Σ R_n y^(n+1)/(n+1)| ≤ BRq` for `|y| ≤ 1` (`RefTrial.hBR`, via `hBR_of`). -/
def BRq : ℚ := ((992647 : ℚ) / 1048576)

theorem br_le : brQ trial.R.f ≤ BRq := by decide +kernel

/-- The mass of the reference `μ = c_r`: `mass μ = 1 - α/2`. -/
theorem mass : (trial.qT.map PieceQ.massQ).sum + (trial.qF.map PieceQ.massQ).sum = 1 - alpha / 2 := by
  decide +kernel

#print axioms spec
#print axioms mass
#print axioms br_le

end CatalanMeasure.GenD.Signed.Data.Trial.T2

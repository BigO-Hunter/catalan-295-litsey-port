module

public import CatalanMeasure.GenD.Signed.Data.Cells.Core
public import CatalanMeasure.GenD.Signed.Data.Trial.T0Fields

@[expose] public section

/-! SP, alpha = 0 (trial 0): the end window `(0, 2^-20]` by the Laurent end checker `endL0UOK` (Core, section
LaurentEnd0).  The field is `T0.spFq` verbatim and the Laurent part is `dilTermsS T0.trial.qT T0.trial.qTn` (the `hid_sp` right-hand
side `dilTermsS qT qTn`, P - N), so `l0OK` (exact cancellation of the negative powers, `n = 27`) and `endL0UOK` are `decide +kernel` on the Trial
literals.  `T` is the demo threshold: the numerically found sup of `spFq + Ts` on (0, 1) plus 5e-7 (in `fieldTower + lfieldTower` units).
`TR` is the largest regular-part bound the window check accepts at `T`; `hreg` below is the Taylor-cell cover of the regular
part on `[0, 2^-20]` of the campaign, to be proved with threshold `TR`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

abbrev q0spE0Fq : FieldQ := CatalanMeasure.GenD.Signed.Data.Trial.T0.spFq
def q0spE0Ts : List LTerm :=
  CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qT
    CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qTn
def q0spE0Hi : ℚ := (1 : ℚ) / 2 ^ 20
def q0spE0U : ℚ := dy3 (14169) 0 39
def q0spE0TR : ℚ := dy3 (23880618029) 0 33
def q0spE0T : ℚ := dy3 (18698378698293) 0 40

/-- the negative powers of the dilated block cancel exactly on the window (one exact computation). -/
theorem q0spE0_laurent : l0OK q0spE0Ts q0spE0Hi 27 = true := by decide +kernel

/-- the window check (field part by `endOK`, Laurent part by `l0OK`, uniform bound `T`). -/
theorem q0spE0_check : endL0UOK q0spE0Fq q0spE0Ts q0spE0Hi 20 20 27 q0spE0U q0spE0TR q0spE0T = true := by
  decide +kernel

/-- **The SP window at 0** (given the cover `hreg` of the regular part): the field plus the dilated block is at
most `T` on `(0, 2^-20]`. -/
theorem q0spE0_sup
    (hreg : ∀ x ∈ Icc (((0 : ℚ) : ℝ)) (q0spE0Hi : ℝ),
      fieldTower (regQ q0spE0Fq 0) (poleF (regQ q0spE0Fq 0).poles) 0 x ≤ (q0spE0TR : ℝ)) :
    ∀ x ∈ Ioc (0 : ℝ) (q0spE0Hi : ℝ), fieldTower q0spE0Fq (poleF q0spE0Fq.poles) 0 x +
      lfieldTower q0spE0Ts 0 x ≤ (q0spE0T : ℝ) :=
  endL0U_sound q0spE0Fq q0spE0Ts q0spE0Hi 20 20 27 q0spE0U q0spE0TR q0spE0T q0spE0_check hreg

#print axioms q0spE0_sup

end CatalanMeasure.GenD.Signed.Data.Cells

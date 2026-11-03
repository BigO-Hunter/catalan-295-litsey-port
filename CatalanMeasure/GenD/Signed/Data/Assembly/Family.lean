module

public import CatalanMeasure.GenD.Signed.Glue410
public import CatalanMeasure.GenD.Signed.DesignConst
public import CatalanMeasure.GenD.Signed.Interp
public import CatalanMeasure.GenD.Signed.Data.Trial.Hid
public import CatalanMeasure.GenD.Signed.Data.Consts.PolyPos
public import CatalanMeasure.GenD.D58.OddProfile
public import CatalanMeasure.Parametric.PopulationPhysicalValue

@[expose] public section

/-!
# 410 assembly: the concrete trial family `famD X N : SignedData`

The trial data modules (`Data/Trial/T{t}Data`, `T{t}Spec`) and the spike/E1b/cell lanes state their
results about an ABSTRACT family member `D` ("`ν = 58 N`, `sp = 20 N`, `θ = 1/1024`, ..."); nothing
defined the family.  This module does, once, for any rational trial datum `X : FamPar`:

* `famD X N`: `ν = 58 N`, `e = dampE N` (`2^-30/(N+1)`), `sp = 20 N`, `g = 5 N`, `v, a, p` from the trial,
  `b = bSeq X.bs`, `K = X.bs.length`, `R = fQ R.f (· + 1)`, `μ = ⟨polyMeas qT/qF, polyMeas qTn/qFn⟩`,
  `t = mneg μ τ`, `cs = CSP / 58`, `kph = 14`, `θ = 1/1024`, `constant = 0` (only the difference
  `constTotal - constant` is used), `Rf, Cf` the problem's population fields of `Odd.design`.
* `famD_spec` (`TrialForm.Spec`), `famD_family` (`Family`), `famD_regular` (`SignedRegular`),
  `famD_compat` (`InterpCompat`), `famD_ends` (`IntervalEnds`).
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.Consts
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Cert OAI.InternalCatalan

noncomputable section

/-- The rational datum of one trial of the family. -/
structure FamPar where
  T : TrialQ
  /-- coefficients of the denominator trial `b` (`TrialB`) -/
  bs : List ℚ
  /-- the per-spike charge `CSP` (`D.cs = CSP / 58`) -/
  CSP : ℚ
  /-- the density cap of `T{t}Spec` -/
  Cb : ℚ

/-- The signed reference `P - N` of the trial as an `SRef`. -/
def famMu (X : FamPar) : SRef :=
  ⟨fun τ => cond τ (polyMeas (X.T.qT.map PieceQ.toPiece)) (polyMeas (X.T.qF.map PieceQ.toPiece)),
   fun τ => cond τ (polyMeas (X.T.qTn.map PieceQ.toPiece)) (polyMeas (X.T.qFn.map PieceQ.toPiece))⟩

/- The trial family member at scale `N`. -/

namespace Generic

variable (dc : DesignConst)

def famD (X : FamPar) (N : ℕ) : SignedData where
  ν := (dc.n0 : ℝ) * (N : ℝ)
  e := dampE N
  sp := dc.sp * N
  g := dc.g0 * N
  v := tseq (fQ X.T.v.f) (X.T.v.tail.map TailQ.toC)
  a := tseq (fQ X.T.a.f) (X.T.a.tail.map TailQ.toC)
  b := bSeq X.bs
  K := X.bs.length
  R := fun n => fQ X.T.R.f (n + 1)
  t := mneg (famMu X) (realEnergyTau (dampE N))
  μ := famMu X
  Cb := (X.Cb : ℝ)
  η := (X.T.η : ℝ)
  p := tseq (fQ X.T.p.f) (X.T.p.tail.map TailQ.toC)
  Sup := (X.T.Sup : ℝ)
  constant := 0
  Rf := CatalanMeasure.Parametric.populationPhysicalFreeField dc.toParameters N
  Cf := CatalanMeasure.Parametric.populationPhysicalColumnField dc.toParameters N (0 + 0)
  θ := (dc.thetaL : ℝ)
  cs := (X.CSP : ℝ) / dc.n0
  kph := 14

theorem famD_tau (X : FamPar) (N : ℕ) : (famD dc X N).τ = 1 - dampE N := rfl

theorem famD_tau_mem (X : FamPar) (N : ℕ) : (famD dc X N).τ ∈ Ioo (0 : ℝ) 1 :=
  realEnergyTau_bounds (dampE_mem N)

/-- `TrialForm.Spec` of the family member (`hok`: the data checks of `T{t}Spec.dataOK`). -/
theorem famD_spec (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (N : ℕ) :
    X.T.form.Spec (famD dc X N) :=
  TrialQ.spec X.T (famD dc X N) (famD_tau_mem dc X N) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hok _ le_rfl)

/-- `Family (famD dc X) F`. -/
theorem famD_family (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) :
    Family (famD dc X) X.T.form where
  spec := famD_spec dc X hok
  hτ := by
    show Tendsto (fun N : ℕ => 1 - dampE N) atTop (𝓝 1)
    exact dampE_tau_tendsto
  hν := by
    show Tendsto (fun N : ℕ => (dc.n0 : ℝ) * (N : ℝ)) atTop atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by exact_mod_cast dc.n0_pos)
  hℓ := by
    show Tendsto (fun N : ℕ => Real.log (1 / (1 - (1 - dampE N) ^ 2)) / ((dc.n0 : ℝ) * (N : ℝ))) atTop (𝓝 0)
    exact dampE_hℓ (by exact_mod_cast dc.n0_pos)
  hasum := Glue410.hasum_of_spec (famD_spec dc X hok 0)

/-- `SignedRegular` of every member (needs `0 ≤ Cb`). -/
theorem famD_regular (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (hCb : (0 : ℝ) ≤ X.Cb) (N : ℕ) : SignedRegular (famD dc X N) := by
  have h := famD_spec dc X hok N
  exact
    { he := dampE_mem N
      hv := Glue410.Spec_summable_v h
      ha := Glue410.Spec_summable_a h
      hR := h.hRg
      ht := TrialForm.isGeom_t h
      hμ := h.bd
      hC := hCb
      hp := Glue410.Spec_summable_p h
      hη0 := by rw [h.hη]; exact h.hηI.1 }

/-- Two trials of the family can be interpolated when their `b`-lengths and `η` agree. -/
theorem famD_compat (X Y : FamPar) (hK : X.bs.length = Y.bs.length) (hη : (X.T.η : ℝ) = Y.T.η)
    (N : ℕ) : InterpCompat (famD dc X N) (famD dc Y N) where
  ν := rfl
  e := rfl
  sp := rfl
  g := rfl
  K := hK.symm
  Rf := rfl
  Cf := rfl
  θ := rfl
  kph := rfl
  η := hη.symm

/-- `IntervalEnds` of the endpoint families of one α-interval. -/
theorem famD_ends (X Y : FamPar) (hokX : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (hokY : ∀ C : ℝ, (Y.Cb : ℝ) ≤ C → Y.T.DataOK C) (hCX : (0 : ℝ) ≤ X.Cb) (hCY : (0 : ℝ) ≤ Y.Cb)
    (hK : X.bs.length = Y.bs.length) (hη : (X.T.η : ℝ) = Y.T.η) {αA αB lo hi : ℝ}
    (hlt : αA < αB) (hlo : αA ≤ lo) (hhi : hi ≤ αB) :
    IntervalEnds αA αB lo hi (famD dc X) (famD dc Y) where
  lt := hlt
  lo_ge := hlo
  hi_le := hhi
  compat := famD_compat dc X Y hK hη
  regA := Eventually.of_forall (famD_regular dc X hokX hCX)
  regB := Eventually.of_forall (famD_regular dc Y hokY hCY)

end Generic

/- BEGIN EMITTED FAMILY INSTANCE: consts/family_instance_emit.py -/
def famD (X : FamPar) (N : ℕ) : SignedData where
  ν := 58 * (N : ℝ)
  e := dampE N
  sp := 20 * N
  g := 5 * N
  v := tseq (fQ X.T.v.f) (X.T.v.tail.map TailQ.toC)
  a := tseq (fQ X.T.a.f) (X.T.a.tail.map TailQ.toC)
  b := bSeq X.bs
  K := X.bs.length
  R := fun n => fQ X.T.R.f (n + 1)
  t := mneg (famMu X) (realEnergyTau (dampE N))
  μ := famMu X
  Cb := (X.Cb : ℝ)
  η := (X.T.η : ℝ)
  p := tseq (fQ X.T.p.f) (X.T.p.tail.map TailQ.toC)
  Sup := (X.T.Sup : ℝ)
  constant := 0
  Rf := CatalanMeasure.Parametric.populationPhysicalFreeField CatalanMeasure.GenD.D58.Odd.design N
  Cf := CatalanMeasure.Parametric.populationPhysicalColumnField CatalanMeasure.GenD.D58.Odd.design N (0 + 0)
  θ := 1 / 1024
  cs := (X.CSP : ℝ) / 58
  kph := 14

/- END EMITTED FAMILY INSTANCE -/

/-- The emitted concrete family is the D58 specialization of the generic family.
The explicit bridge preserves old real-division reduction behavior at theta. -/
theorem famD_eq_generic (X : FamPar) : famD X = Generic.famD dc58 X := by
  funext N
  unfold famD Generic.famD
  congr 1 <;> norm_num [dc58, D58.Odd.design]

theorem famD_tau (X : FamPar) (N : ℕ) : (famD X N).τ = 1 - dampE N := by
  revert X N
  simpa only [famD_eq_generic, dc58_n0, dc58_g0, dc58_sp,
    (show (dc58.thetaL : ℝ) = (1 / 1024 : ℝ) by norm_num [dc58]),
    Nat.cast_ofNat,
    (show ((58 : ℝ) - 5) / 58 = (53 / 58 : ℝ) by norm_num),
    (show ((58 : ℝ) - 2 * 5) / 58 = (24 / 29 : ℝ) by norm_num)] using (Generic.famD_tau dc58)

theorem famD_tau_mem (X : FamPar) (N : ℕ) : (famD X N).τ ∈ Ioo (0 : ℝ) 1 := by
  revert X N
  simpa only [famD_eq_generic, dc58_n0, dc58_g0, dc58_sp,
    (show (dc58.thetaL : ℝ) = (1 / 1024 : ℝ) by norm_num [dc58]),
    Nat.cast_ofNat,
    (show ((58 : ℝ) - 5) / 58 = (53 / 58 : ℝ) by norm_num),
    (show ((58 : ℝ) - 2 * 5) / 58 = (24 / 29 : ℝ) by norm_num)] using (Generic.famD_tau_mem dc58)

theorem famD_spec (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (N : ℕ) :
    X.T.form.Spec (famD X N) := by
  revert X hok N
  simpa only [famD_eq_generic, dc58_n0, dc58_g0, dc58_sp,
    (show (dc58.thetaL : ℝ) = (1 / 1024 : ℝ) by norm_num [dc58]),
    Nat.cast_ofNat,
    (show ((58 : ℝ) - 5) / 58 = (53 / 58 : ℝ) by norm_num),
    (show ((58 : ℝ) - 2 * 5) / 58 = (24 / 29 : ℝ) by norm_num)] using (Generic.famD_spec dc58)

theorem famD_family (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) :
    Family (famD X) X.T.form := by
  revert X hok
  simpa only [famD_eq_generic, dc58_n0, dc58_g0, dc58_sp,
    (show (dc58.thetaL : ℝ) = (1 / 1024 : ℝ) by norm_num [dc58]),
    Nat.cast_ofNat,
    (show ((58 : ℝ) - 5) / 58 = (53 / 58 : ℝ) by norm_num),
    (show ((58 : ℝ) - 2 * 5) / 58 = (24 / 29 : ℝ) by norm_num)] using (Generic.famD_family dc58)

theorem famD_regular (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (hCb : (0 : ℝ) ≤ X.Cb) (N : ℕ) : SignedRegular (famD X N) := by
  revert X hok hCb N
  simpa only [famD_eq_generic, dc58_n0, dc58_g0, dc58_sp,
    (show (dc58.thetaL : ℝ) = (1 / 1024 : ℝ) by norm_num [dc58]),
    Nat.cast_ofNat,
    (show ((58 : ℝ) - 5) / 58 = (53 / 58 : ℝ) by norm_num),
    (show ((58 : ℝ) - 2 * 5) / 58 = (24 / 29 : ℝ) by norm_num)] using (Generic.famD_regular dc58)

theorem famD_compat (X Y : FamPar) (hK : X.bs.length = Y.bs.length) (hη : (X.T.η : ℝ) = Y.T.η)
    (N : ℕ) : InterpCompat (famD X N) (famD Y N) := by
  revert X Y hK hη N
  simpa only [famD_eq_generic, dc58_n0, dc58_g0, dc58_sp,
    (show (dc58.thetaL : ℝ) = (1 / 1024 : ℝ) by norm_num [dc58]),
    Nat.cast_ofNat,
    (show ((58 : ℝ) - 5) / 58 = (53 / 58 : ℝ) by norm_num),
    (show ((58 : ℝ) - 2 * 5) / 58 = (24 / 29 : ℝ) by norm_num)] using (Generic.famD_compat dc58)

theorem famD_ends (X Y : FamPar) (hokX : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (hokY : ∀ C : ℝ, (Y.Cb : ℝ) ≤ C → Y.T.DataOK C) (hCX : (0 : ℝ) ≤ X.Cb) (hCY : (0 : ℝ) ≤ Y.Cb)
    (hK : X.bs.length = Y.bs.length) (hη : (X.T.η : ℝ) = Y.T.η) {αA αB lo hi : ℝ}
    (hlt : αA < αB) (hlo : αA ≤ lo) (hhi : hi ≤ αB) :
    IntervalEnds αA αB lo hi (famD X) (famD Y) := by
  revert X Y hokX hokY hCX hCY hK hη αA αB lo hi hlt hlo hhi
  simpa only [famD_eq_generic, dc58_n0, dc58_g0, dc58_sp,
    (show (dc58.thetaL : ℝ) = (1 / 1024 : ℝ) by norm_num [dc58]),
    Nat.cast_ofNat,
    (show ((58 : ℝ) - 5) / 58 = (53 / 58 : ℝ) by norm_num),
    (show ((58 : ℝ) - 2 * 5) / 58 = (24 / 29 : ℝ) by norm_num)] using (Generic.famD_ends dc58)


end

end CatalanMeasure.GenD.Signed.Data.Assembly

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.famD_tau
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.famD_tau_mem
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.famD_spec
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.famD_family
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.famD_regular
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.famD_compat
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.famD_ends
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.famD_tau
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.famD_tau_mem
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.famD_spec
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.famD_family
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.famD_regular
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.famD_compat
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.famD_ends

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.famD_eq_generic

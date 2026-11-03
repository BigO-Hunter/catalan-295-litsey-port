module

public import CatalanMeasure.GenD.Signed.Data.Assembly.Family
public import CatalanMeasure.GenD.Signed.Data.Assembly.Nodes
public import CatalanMeasure.GenD.Signed.Phase2Contract
public import CatalanMeasure.GenD.Signed.Data.Trial.T0Spec
public import CatalanMeasure.GenD.Signed.Data.Trial.T1Spec
public import CatalanMeasure.GenD.Signed.Data.Trial.T2Spec
public import CatalanMeasure.GenD.Signed.Data.Consts.TrialB0
public import CatalanMeasure.GenD.Signed.Data.Consts.TrialB1
public import CatalanMeasure.GenD.Signed.Data.Consts.TrialB2
public import CatalanMeasure.GenD.Signed.Data.Consts.Umin
public import CatalanMeasure.GenD.DesignInstance.PositiveBudget

@[expose] public section

/-!
# 410 assembly: `Phase2Data 2` from the structural data and the row ingredients

`phase2 R : Phase2Data 2` fills every structural field (scale `ncount = 58 N`, the two intervals
`[0, 1/200]`, `[1/200, 1/16]` with endpoint trials `(T0, T1)`, `(T1, T2)` as `famD`, `epsSplit = 1/10`,
`κ` windows, `umin`, the cap geometry `gs, xc, C1`, the problem fields) and takes the remaining rows as
a record `Rows410` whose field TYPES are exactly those of `Phase2Data` for these definitions.  The row
producers (lane C cells with `cover_eventually`, E1b instances, the spike class, the σ-cap constants,
the budget arithmetic) each deliver one field of `Rows410`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm OAI.InternalCatalan CatalanMeasure.Parametric CatalanMeasure.GenD.Analytic
open CatalanMeasure.GenD CatalanMeasure.GenD.D58
open CatalanMeasure.GenD.Signed.Data.Trial

noncomputable section

def X0 : FamPar := ⟨T0.trial, CatalanMeasure.Signed.Consts.bs0, 21 / 20, T0.Cb⟩
def X1 : FamPar := ⟨T1.trial, CatalanMeasure.Signed.Consts.bs1, 21 / 20, T1.Cb⟩
def X2 : FamPar := ⟨T2.trial, CatalanMeasure.Signed.Consts.bs2, 11 / 10, T2.Cb⟩

def DA410 : Fin 2 → ℕ → SignedData := ![famD X0, famD X1]
def DB410 : Fin 2 → ℕ → SignedData := ![famD X1, famD X2]
def lo410 : Fin 2 → ℝ := ![0, 1 / 200]
def hi410 : Fin 2 → ℝ := ![1 / 200, 1 / 16]
def αA410 : Fin 2 → ℝ := ![0, 1 / 200]
def αB410 : Fin 2 → ℝ := ![1 / 200, 1 / 16]
def κlo410 : Fin 2 → ℝ := ![3 / 10, 27 / 100]
def κhi410 : Fin 2 → ℝ := ![223 / 500, 4431 / 10000]

abbrev P410 : Parameters := CatalanMeasure.GenD.D58.Odd.design

namespace Generic

variable (dc : DesignConst)

theorem famD_mass (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (N : ℕ) {c : ℚ}
    (hc : ((X.T.qT.map PieceQ.massQ).sum + (X.T.qF.map PieceQ.massQ).sum) -
      ((X.T.qTn.map PieceQ.massQ).sum + (X.T.qFn.map PieceQ.massQ).sum) = c) :
    (famD dc X N).μ.mass = (c : ℝ) := by
  have h := hok _ le_rfl
  have hm : ∀ qs : List PieceQ, (∀ q ∈ qs, PieceOK q.toPiece) →
      (polyMeas (qs.map PieceQ.toPiece)).real univ = (((qs.map PieceQ.massQ).sum : ℚ) : ℝ) := by
    intro qs hqs
    have hq' : ∀ q ∈ qs.map PieceQ.toPiece, PieceOK q := by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact hqs r hr
    have := integral_const_polyMeas hq'
    rw [MeasureTheory.integral_const, smul_eq_mul, mul_one] at this
    rw [this, polyMass_cast]
  show SRef.mass (famMu X) = _
  unfold SRef.mass famMu
  simp only [Fintype.sum_bool, cond_true, cond_false]
  rw [hm _ h.pT, hm _ h.pF, hm _ h.pTn, hm _ h.pFn, ← hc]
  push_cast
  ring

end Generic

theorem famD_mass (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (N : ℕ) {c : ℚ}
    (hc : ((X.T.qT.map PieceQ.massQ).sum + (X.T.qF.map PieceQ.massQ).sum) -
      ((X.T.qTn.map PieceQ.massQ).sum + (X.T.qFn.map PieceQ.massQ).sum) = c) :
    (famD X N).μ.mass = (c : ℝ) := by
  simpa only [famD_eq_generic] using (Generic.famD_mass dc58 X hok N hc)


theorem mass0 (N : ℕ) : (famD X0 N).μ.mass = 1 - 0 / 2 := by
  rw [famD_mass X0 (fun C hC => T0.dataOK hC) N T0.mass]; norm_num [T0.alpha]
theorem mass1 (N : ℕ) : (famD X1 N).μ.mass = 1 - 1 / 200 / 2 := by
  rw [famD_mass X1 (fun C hC => T1.dataOK hC) N T1.mass]; norm_num [T1.alpha]
theorem mass2 (N : ℕ) : (famD X2 N).μ.mass = 1 - 1 / 16 / 2 := by
  rw [famD_mass X2 (fun C hC => T2.dataOK hC) N T2.mass]; norm_num [T2.alpha]

theorem ends410 (i : Fin 2) : IntervalEnds (αA410 i) (αB410 i) (lo410 i) (hi410 i) (DA410 i) (DB410 i) := by
  have hη : (X0.T.η : ℝ) = X1.T.η := by norm_num [X0, X1, T0.trial, T1.trial]
  have hη' : (X1.T.η : ℝ) = X2.T.η := by norm_num [X1, X2, T1.trial, T2.trial]
  -- kcost: 0.048 s estimated; two 120-element maps and two length traversals, about 480 reductions.
  have hK : X0.bs.length = X1.bs.length := by decide +kernel
  -- kcost: 0.048 s estimated; two 120-element maps and two length traversals, about 480 reductions.
  have hK' : X1.bs.length = X2.bs.length := by decide +kernel
  fin_cases i
  · exact famD_ends X0 X1 (fun C hC => T0.dataOK hC) (fun C hC => T1.dataOK hC)
      (by norm_num [X0, T0.Cb]) (by norm_num [X1, T1.Cb]) hK hη
      (show _ < _ by norm_num [αA410, αB410]) (le_of_eq (by simp [αA410, lo410])) (le_of_eq (by simp [hi410, αB410]))
  · exact famD_ends X1 X2 (fun C hC => T1.dataOK hC) (fun C hC => T2.dataOK hC)
      (by norm_num [X1, T1.Cb]) (by norm_num [X2, T2.Cb]) hK' hη'
      (show _ < _ by norm_num [αA410, αB410]) (le_of_eq (by simp [αA410, lo410])) (le_of_eq (by simp [hi410, αB410]))

/-- **The ingredient rows**: the fields of `Phase2Data 2` that are not structural, with the types
`Phase2Data` demands for the definitions above. -/
structure Rows410 where
  SnA : Fin 2 → ℝ
  SnB : Fin 2 → ℝ
  SpA : Fin 2 → ℝ
  SpB : Fin 2 → ℝ
  SyA : Fin 2 → ℝ
  SyB : Fin 2 → ℝ
  hSnA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, (DA410 i N).fNeg x ≤ SnA i + ε
  hSnB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, (DB410 i N).fNeg x ≤ SnB i + ε
  hSpA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, (DA410 i N).fPosS x ≤ SpA i + ε
  hSpB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, (DB410 i N).fPosS x ≤ SpB i + ε
  hSyA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1, (DA410 i N).fCol s ≤ SyA i + ε
  hSyB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1, (DB410 i N).fCol s ≤ SyB i + ε
  cP : Fin 2 → ℝ → ℝ
  hcP : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), Glue410.constantLim P410 α ≤ cP i α
  rA : Fin 2 → ℝ
  rB : Fin 2 → ℝ
  κc : Fin 2 → ℝ
  hrA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (DA410 i N).constTotal (58 * N) - (DA410 i N).constant ≤ rA i + ε
  hrB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (DB410 i N).constTotal (58 * N) - (DB410 i N).constant ≤ rB i + ε
  hκ : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, κc i - ε ≤ curvQ (DA410 i N) (DB410 i N) (58 * N)
  Clsf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop
  cp : Fin 2 → ℕ → ℝ → ℝ
  cp_pos : ∀ i N α, 0 < cp i N α
  cp_le : ∀ i N α, cp i N α ≤ 1
  err_small : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ((DA410 i N).withCount (58 * N)).errJ3 (cp i N α) (58 * N) ≤ ε
  cp_theta : ∀ i N α, cp i N α ≤ (DA410 i N).θ
  hCls : ∀ i, ∀ᶠ N : ℕ in atTop, ∀ α k q m1 m2 xn gp yn yp, Clsf N k q m1 m2 xn gp yn yp →
    (0 < (DA410 i N).sp ∧ (DA410 i N).sp + (DA410 i N).g ≤ q + m2) ∧
    Nonempty (PairCls ((DA410 i N).withCount (q + m2 - (DA410 i N).g))
      ((DB410 i N).withCount (q + m2 - (DA410 i N).g)) (cp i N α) xn gp yn yp)
  capE : Fin 2 → CapEnd
  hxc0 : ∀ i, 0 ≤ (capE i).xc
  hxc1 : ∀ i, (capE i).xc < 1
  hC1 : ∀ i, 0 < (capE i).C1
  hrP : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), remC (1 / 10) * α ≤ (capE i).rP α
  hrSA : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, 0 ≤ (capE i).rSA α β
  hrSB : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, 0 ≤ (capE i).rSB α β
  Bd : Fin 2 → ℝ
  Rbd : Fin 2 → ℝ
  hBdPA : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), (capE i).gPA α - (capE i).lamPA α ≤ Bd i
  hBdPB : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), (capE i).gPB α - (capE i).lamPB α ≤ Bd i
  hBdSA : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α,
    (capE i).gSA α β - (capE i).lamSA α β ≤ Bd i
  hBdSB : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α,
    (capE i).gSB α β - (capE i).lamSB α β ≤ Bd i
  hRP : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), (capE i).rP α ≤ Rbd i
  hRSA : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, (capE i).rSA α β ≤ Rbd i
  hRSB : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, (capE i).rSB α β ≤ Rbd i
  hgs : ∀ i, (capE i).gs ≤ 401 / 2500
  hxc : ∀ i, 999 / 1000 ≤ (capE i).xc
  hC1le : ∀ i, 9631 / 20000 ≤ (capE i).C1
  hnegA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -(capE i).gs →
      (DA410 i N).fNegM (groupedMarkedField P410 N) x ≤ (capE i).lamNA + ε
  hnegB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -(capE i).gs →
      (DB410 i N).fNegM (groupedMarkedField P410 N) x ≤ (capE i).lamNB + ε
  hposA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DA410 i N).fPosMR (groupedMarkedField P410 N) (remC (1 / 10)) α x ≤ (capE i).lamPA α + ε
  hposB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DB410 i N).fPosMR (groupedMarkedField P410 N) (remC (1 / 10)) α x ≤ (capE i).lamPB α + ε
  hposTopA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (DA410 i N).fPosMS (groupedMarkedField P410 N) x ≤ (capE i).gPA α + ε
  hposTopB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (DB410 i N).fPosMS (groupedMarkedField P410 N) x ≤ (capE i).gPB α + ε
  hnearA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DA410 i N).fNearMS (groupedNearField P410 N) α β x ≤ (capE i).lamSA α β + ε
  hnearB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DB410 i N).fNearMS (groupedNearField P410 N) α β x ≤ (capE i).lamSB α β + ε
  hnearTopA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (DA410 i N).fNearMS (groupedNearField P410 N) α β x ≤
        (capE i).gSA α β + ε + (capE i).rSA α β * (-Real.log (1 - x ^ 2))
  hnearTopB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (DB410 i N).fNearMS (groupedNearField P410 N) α β x ≤
        (capE i).gSB α β + ε + (capE i).rSB α β * (-Real.log (1 - x ^ 2))
  zb : Fin 2 → ℝ → ℝ
  hZB : ∀ (i : Fin 2) (c d e : ℝ), 0 ≤ c → 0 ≤ d → 0 ≤ e → lo410 i ≤ c + d + e →
    c + d + e ≤ hi410 i →
    zbCap ((capE i).toS (αA410 i) (αB410 i)) c d e ≤ zb i (c + d + e)
  hbudLo : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i),
    interpCInf (αA410 i) (αB410 i) (cP i α) (rA i) (rB i) (κc i) α +
      fixLog2 (1 / 10) α * Real.log 2 +
      κlo410 i * chord (αA410 i) (αB410 i) (SnA i) (SnB i) α +
      (1 - κlo410 i - α) * chord (αA410 i) (αB410 i) (SpA i) (SpB i) α +
      (1 - α) * chord (αA410 i) (αB410 i) (SyA i) (SyB i) α + zb i α ≤
        (-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α
  hbudHi : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i),
    interpCInf (αA410 i) (αB410 i) (cP i α) (rA i) (rB i) (κc i) α +
      fixLog2 (1 / 10) α * Real.log 2 +
      κhi410 i * chord (αA410 i) (αB410 i) (SnA i) (SnB i) α +
      (1 - κhi410 i - α) * chord (αA410 i) (αB410 i) (SpA i) (SpB i) α +
      (1 - α) * chord (αA410 i) (αB410 i) (SyA i) (SyB i) α + zb i α ≤
        (-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α


namespace Generic

/-- Actual endpoint/certificate choices for the same determinant design. -/
structure Inputs (dc : DesignConst) where
  XA : Fin 2 → FamPar
  XB : Fin 2 → FamPar
  DA : Fin 2 → ℕ → SignedData
  DB : Fin 2 → ℕ → SignedData
  hDA : ∀ i N, DA i N = famD dc (XA i) N
  hDB : ∀ i N, DB i N = famD dc (XB i) N
  target : ℝ
  cost : ℝ
  α1 : ℝ
  α1_nonneg : 0 ≤ α1
  lo : Fin 2 → ℝ
  hi : Fin 2 → ℝ
  αA : Fin 2 → ℝ
  αB : Fin 2 → ℝ
  κlo : Fin 2 → ℝ
  κhi : Fin 2 → ℝ
  epsSplit : Fin 2 → ℝ
  epsSplit_pos : ∀ i, 0 < epsSplit i
  epsSplit_le : ∀ i, epsSplit i ≤ 1
  cover : ∀ α : ℝ, 0 ≤ α → α ≤ α1 → ∃ i, lo i ≤ α ∧ α ≤ hi i
  hlo0 : ∀ i, 0 ≤ lo i
  hhi1 : ∀ i, hi i ≤ 1
  hends : ∀ i, IntervalEnds (αA i) (αB i) (lo i) (hi i) (DA i) (DB i)
  massA : ∀ i, ∀ᶠ N : ℕ in atTop, 1 - αA i / 2 = (DA i N).μ.mass
  massB : ∀ i, ∀ᶠ N : ℕ in atTop, 1 - αB i / 2 = (DB i N).μ.mass
  etaA : ∀ i N, (DA i N).η = (1 - epsSplit i) / 2
  gs : ℝ
  xc : ℝ
  C1 : ℝ
  gs_eq : gs = (dc.gstar : ℝ)
  xc_eq : xc = (dc.xc : ℝ)
  hC : (dc.d0 : ℝ) / ((dc.n0 : ℝ) *
    (2 * (dc.xc : ℝ) * Real.sqrt (1 - (dc.astar : ℝ) ^ 2))) ≤ C1
  umin : ℕ → ℝ
  humin : ∀ N, umin N = Generic.umin dc N

/-- The input geometry is the cap proved for these same design nodes. -/
theorem markedCap_inputs (dc : DesignConst) (I : Inputs dc)
    (N : ℕ) {m : ℕ} {y : Fin m → ℝ} (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1)
    (h : NodeSub (nodesτ dc) N m y) :
    MarkedCap I.gs I.xc I.C1 ((dc.n0 * N : ℕ) : ℝ) (I.umin N) y := by
  rw [I.gs_eq, I.xc_eq, I.humin]
  simpa only [Nat.cast_mul] using (markedCap_real dc I.C1 I.hC N hy h)

structure Rows (dc : DesignConst) (I : Inputs dc) where
  SnA : Fin 2 → ℝ
  SnB : Fin 2 → ℝ
  SpA : Fin 2 → ℝ
  SpB : Fin 2 → ℝ
  SyA : Fin 2 → ℝ
  SyB : Fin 2 → ℝ
  hSnA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, (I.DA i N).fNeg x ≤ SnA i + ε
  hSnB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, (I.DB i N).fNeg x ≤ SnB i + ε
  hSpA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, (I.DA i N).fPosS x ≤ SpA i + ε
  hSpB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, (I.DB i N).fPosS x ≤ SpB i + ε
  hSyA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1, (I.DA i N).fCol s ≤ SyA i + ε
  hSyB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1, (I.DB i N).fCol s ≤ SyB i + ε
  cP : Fin 2 → ℝ → ℝ
  hcP : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i), Glue410.constantLim dc.toParameters α ≤ cP i α
  rA : Fin 2 → ℝ
  rB : Fin 2 → ℝ
  κc : Fin 2 → ℝ
  hrA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (I.DA i N).constTotal (dc.n0 * N) - (I.DA i N).constant ≤ rA i + ε
  hrB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (I.DB i N).constTotal (dc.n0 * N) - (I.DB i N).constant ≤ rB i + ε
  hκ : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, κc i - ε ≤ curvQ (I.DA i N) (I.DB i N) (dc.n0 * N)
  Clsf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop
  cp : Fin 2 → ℕ → ℝ → ℝ
  cp_pos : ∀ i N α, 0 < cp i N α
  cp_le : ∀ i N α, cp i N α ≤ 1
  err_small : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (I.lo i) (I.hi i),
    ((I.DA i N).withCount (dc.n0 * N)).errJ3 (cp i N α) (dc.n0 * N) ≤ ε
  cp_theta : ∀ i N α, cp i N α ≤ (I.DA i N).θ
  hCls : ∀ i, ∀ᶠ N : ℕ in atTop, ∀ α k q m1 m2 xn gp yn yp, Clsf N k q m1 m2 xn gp yn yp →
    (0 < (I.DA i N).sp ∧ (I.DA i N).sp + (I.DA i N).g ≤ q + m2) ∧
    Nonempty (PairCls ((I.DA i N).withCount (q + m2 - (I.DA i N).g))
      ((I.DB i N).withCount (q + m2 - (I.DA i N).g)) (cp i N α) xn gp yn yp)
  capE : Fin 2 → CapEnd
  hxc0 : ∀ i, 0 ≤ (capE i).xc
  hxc1 : ∀ i, (capE i).xc < 1
  hC1 : ∀ i, 0 < (capE i).C1
  hrP : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i), remC (I.epsSplit i) * α ≤ (capE i).rP α
  hrSA : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, 0 ≤ (capE i).rSA α β
  hrSB : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, 0 ≤ (capE i).rSB α β
  Bd : Fin 2 → ℝ
  Rbd : Fin 2 → ℝ
  hBdPA : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i), (capE i).gPA α - (capE i).lamPA α ≤ Bd i
  hBdPB : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i), (capE i).gPB α - (capE i).lamPB α ≤ Bd i
  hBdSA : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α,
    (capE i).gSA α β - (capE i).lamSA α β ≤ Bd i
  hBdSB : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α,
    (capE i).gSB α β - (capE i).lamSB α β ≤ Bd i
  hRP : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i), (capE i).rP α ≤ Rbd i
  hRSA : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, (capE i).rSA α β ≤ Rbd i
  hRSB : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, (capE i).rSB α β ≤ Rbd i
  hgs : ∀ i, (capE i).gs ≤ I.gs
  hxc : ∀ i, I.xc ≤ (capE i).xc
  hC1le : ∀ i, I.C1 ≤ (capE i).C1
  hnegA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (I.lo i) (I.hi i),
    ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -(capE i).gs →
      (I.DA i N).fNegM (groupedMarkedField dc.toParameters N) x ≤ (capE i).lamNA + ε
  hnegB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (I.lo i) (I.hi i),
    ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -(capE i).gs →
      (I.DB i N).fNegM (groupedMarkedField dc.toParameters N) x ≤ (capE i).lamNB + ε
  hposA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (I.lo i) (I.hi i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (I.DA i N).fPosMR (groupedMarkedField dc.toParameters N) (remC (I.epsSplit i)) α x ≤ (capE i).lamPA α + ε
  hposB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (I.lo i) (I.hi i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (I.DB i N).fPosMR (groupedMarkedField dc.toParameters N) (remC (I.epsSplit i)) α x ≤ (capE i).lamPB α + ε
  hposTopA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (I.lo i) (I.hi i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (I.DA i N).fPosMS (groupedMarkedField dc.toParameters N) x ≤ (capE i).gPA α + ε
  hposTopB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (I.lo i) (I.hi i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (I.DB i N).fPosMS (groupedMarkedField dc.toParameters N) x ≤ (capE i).gPB α + ε
  hnearA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (I.lo i) (I.hi i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (I.DA i N).fNearMS (groupedNearField dc.toParameters N) α β x ≤ (capE i).lamSA α β + ε
  hnearB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (I.lo i) (I.hi i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (I.DB i N).fNearMS (groupedNearField dc.toParameters N) α β x ≤ (capE i).lamSB α β + ε
  hnearTopA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (I.lo i) (I.hi i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (I.DA i N).fNearMS (groupedNearField dc.toParameters N) α β x ≤
        (capE i).gSA α β + ε + (capE i).rSA α β * (-Real.log (1 - x ^ 2))
  hnearTopB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (I.lo i) (I.hi i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (I.DB i N).fNearMS (groupedNearField dc.toParameters N) α β x ≤
        (capE i).gSB α β + ε + (capE i).rSB α β * (-Real.log (1 - x ^ 2))
  zb : Fin 2 → ℝ → ℝ
  hZB : ∀ (i : Fin 2) (c d e : ℝ), 0 ≤ c → 0 ≤ d → 0 ≤ e → I.lo i ≤ c + d + e →
    c + d + e ≤ I.hi i →
    zbCap ((capE i).toS (I.αA i) (I.αB i)) c d e ≤ zb i (c + d + e)
  hbudLo : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i),
    interpCInf (I.αA i) (I.αB i) (cP i α) (rA i) (rB i) (κc i) α +
      fixLog2 (I.epsSplit i) α * Real.log 2 +
      I.κlo i * chord (I.αA i) (I.αB i) (SnA i) (SnB i) α +
      (1 - I.κlo i - α) * chord (I.αA i) (I.αB i) (SpA i) (SpB i) α +
      (1 - α) * chord (I.αA i) (I.αB i) (SyA i) (SyB i) α + zb i α ≤
        (-I.target + Real.log 2 / 2) + I.cost * α
  hbudHi : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i),
    interpCInf (I.αA i) (I.αB i) (cP i α) (rA i) (rB i) (κc i) α +
      fixLog2 (I.epsSplit i) α * Real.log 2 +
      I.κhi i * chord (I.αA i) (I.αB i) (SnA i) (SnB i) α +
      (1 - I.κhi i - α) * chord (I.αA i) (I.αB i) (SpA i) (SpB i) α +
      (1 - α) * chord (I.αA i) (I.αB i) (SyA i) (SyB i) α + zb i α ≤
        (-I.target + Real.log 2 / 2) + I.cost * α


end Generic


/-- The D58 structural choices and their same-design identifications. -/
def inputs410 : Generic.Inputs dc58 where
  XA := ![X0, X1]
  XB := ![X1, X2]
  DA := DA410
  DB := DB410
  hDA := fun i N => by fin_cases i <;> exact congrFun (famD_eq_generic _) N
  hDB := fun i N => by fin_cases i <;> exact congrFun (famD_eq_generic _) N
  target := K590.target0
  cost := K590.secondCost'
  α1 := 1 / 16
  α1_nonneg := by norm_num
  lo := lo410
  hi := hi410
  αA := αA410
  αB := αB410
  κlo := κlo410
  κhi := κhi410
  epsSplit := fun _ => 1 / 10
  epsSplit_pos := fun _ => by norm_num
  epsSplit_le := fun _ => by norm_num
  cover := fun α h0 h1 => by
    by_cases h : α ≤ 1 / 200
    · exact ⟨0, (show (0 : ℝ) ≤ α from h0), (show α ≤ 1 / 200 from h)⟩
    · push_neg at h
      exact ⟨1, (show (1 / 200 : ℝ) ≤ α from h.le), (show α ≤ 1 / 16 from h1)⟩
  hlo0 := fun i => by fin_cases i <;> norm_num [lo410]
  hhi1 := fun i => by fin_cases i <;> norm_num [hi410]
  hends := ends410
  massA := fun i => Eventually.of_forall fun N => by
    fin_cases i
    · show (1 : ℝ) - 0 / 2 = (famD X0 N).μ.mass; rw [mass0]
    · show (1 : ℝ) - 1 / 200 / 2 = (famD X1 N).μ.mass; rw [mass1]
  massB := fun i => Eventually.of_forall fun N => by
    fin_cases i
    · show (1 : ℝ) - 1 / 200 / 2 = (famD X1 N).μ.mass; rw [mass1]
    · show (1 : ℝ) - 1 / 16 / 2 = (famD X2 N).μ.mass; rw [mass2]
  etaA := fun i N => by
    fin_cases i <;> simp [DA410, famD, Generic.famD, X0, X1, T0.trial, T1.trial] <;> norm_num
  gs := 401 / 2500
  xc := 999 / 1000
  C1 := 9631 / 20000
  gs_eq := by norm_num [dc58]
  xc_eq := by norm_num [dc58]
  hC := by
    simpa only [dc58_d0, dc58_n0, Nat.cast_ofNat,
      (show (dc58.xc : ℝ) = (999 / 1000 : ℝ) by norm_num [dc58]),
      (show (dc58.astar : ℝ) = (2005000 / 6410801 : ℝ) by norm_num [DesignConst.astar, dc58])]
      using CatalanMeasure.Signed.Consts.C1_bound
  umin := umin410
  humin := fun N => by
    unfold umin410 Generic.umin
    rw [dc58_d0,
      (show (dc58.astar : ℝ) = (2005000 / 6410801 : ℝ) by norm_num [DesignConst.astar, dc58])]
    rw [show CatalanMeasure.GenD.Signed.Data.S1.aGap = (2005000 / 6410801 : ℝ) by
      norm_num [CatalanMeasure.GenD.Signed.Data.S1.aGap, CatalanMeasure.GenD.Signed.Data.S1.aQ]]
    push_cast
    congr 1
    ring

/-- The concrete ingredient rows viewed through their generic contract. -/
def Rows410.toGeneric (R : Rows410) : Generic.Rows dc58 inputs410 where
  SnA := R.SnA
  SnB := R.SnB
  SpA := R.SpA
  SpB := R.SpB
  SyA := R.SyA
  SyB := R.SyB
  hSnA := R.hSnA
  hSnB := R.hSnB
  hSpA := R.hSpA
  hSpB := R.hSpB
  hSyA := R.hSyA
  hSyB := R.hSyB
  cP := R.cP
  hcP := R.hcP
  rA := R.rA
  rB := R.rB
  κc := R.κc
  hrA := R.hrA
  hrB := R.hrB
  hκ := R.hκ
  Clsf := R.Clsf
  cp := R.cp
  cp_pos := R.cp_pos
  cp_le := R.cp_le
  err_small := R.err_small
  cp_theta := R.cp_theta
  hCls := R.hCls
  capE := R.capE
  hxc0 := R.hxc0
  hxc1 := R.hxc1
  hC1 := R.hC1
  hrP := R.hrP
  hrSA := R.hrSA
  hrSB := R.hrSB
  Bd := R.Bd
  Rbd := R.Rbd
  hBdPA := R.hBdPA
  hBdPB := R.hBdPB
  hBdSA := R.hBdSA
  hBdSB := R.hBdSB
  hRP := R.hRP
  hRSA := R.hRSA
  hRSB := R.hRSB
  hgs := R.hgs
  hxc := R.hxc
  hC1le := R.hC1le
  hnegA := R.hnegA
  hnegB := R.hnegB
  hposA := R.hposA
  hposB := R.hposB
  hposTopA := R.hposTopA
  hposTopB := R.hposTopB
  hnearA := R.hnearA
  hnearB := R.hnearB
  hnearTopA := R.hnearTopA
  hnearTopB := R.hnearTopB
  zb := R.zb
  hZB := R.hZB
  hbudLo := R.hbudLo
  hbudHi := R.hbudHi

end

end CatalanMeasure.GenD.Signed.Data.Assembly

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.inputs410
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Rows410.toGeneric

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.famD_mass
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.famD_mass
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.mass0
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.mass1
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.mass2
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.ends410
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.markedCap_inputs

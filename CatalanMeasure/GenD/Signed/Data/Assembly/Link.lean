module

public import CatalanMeasure.GenD.Signed.Data.Assembly.Phase2
public import CatalanMeasure.GenD.Signed.Data.Assembly.Decay
public import CatalanMeasure.CellCert.Scaled
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkMean
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkStatSigns
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkStatSlope
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkStatP
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkGrid
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkExcess
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkSupK590
public import CatalanMeasure.GenD.Signed.Data.Consts.SumAbs

@[expose] public section
set_option maxRecDepth 1000000

/-!
# 410 assembly: the `LinkCert` term (class-link data) of the near case

`link410 R D0 hp hv hM hCls : LinkCert (phase2 R) P410 .. D0 δ e target0 c2_410` with `δ = 13/100000`,
`e = 2^-30`, `Dcap = Dtop = 13/5000`, `θ0 = 1/1000`, `dsp = 18/125`, `a0 = 7/100`, `dgap = 1/25`,
`ts = 13/128`, the 24-point slope grid, `κ` windows `[3/10, 223/500]`, `[27/100, 4431/10000]`.
Every field is a theorem of `Data/Consts/{LinkSigns,LinkSlope,LinkStat*,LinkGrid,LinkMean,LinkExcess,LinkSupK590,SumAbs}`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter
open CatalanMeasure.Signed CatalanMeasure.Signed.Consts OAI.InternalCatalan CatalanMeasure.Parametric
open CatalanMeasure.GenD.D58.Cert590 (Pc P V)

open CatalanMeasure.GenD.D58 CatalanMeasure.GenD.Analytic CatalanMeasure.CellCert

noncomputable section

def eL : ℝ := 1 / 2 ^ 30

theorem eL_mem : eL ∈ Ioo (0 : ℝ) (1 / 8) := by unfold eL; constructor <;> norm_num

def gSL : ℕ → List ℚ
  | 0 => gS0
  | 1 => gS1
  | 2 => gS2
  | 3 => gS3
  | 4 => gS4
  | 5 => gS5
  | 6 => gS6
  | 7 => gS7
  | 8 => gS8
  | 9 => gS9
  | 10 => gS10
  | 11 => gS11
  | 12 => gS12
  | 13 => gS13
  | 14 => gS14
  | 15 => gS15
  | 16 => gS16
  | 17 => gS17
  | 18 => gS18
  | 19 => gS19
  | 20 => gS20
  | 21 => gS21
  | 22 => gS22
  | 23 => gS23
  | _ => []

def c0SL : ℕ → ℚ
  | 0 => c0S0
  | 1 => c0S1
  | 2 => c0S2
  | 3 => c0S3
  | 4 => c0S4
  | 5 => c0S5
  | 6 => c0S6
  | 7 => c0S7
  | 8 => c0S8
  | 9 => c0S9
  | 10 => c0S10
  | 11 => c0S11
  | 12 => c0S12
  | 13 => c0S13
  | 14 => c0S14
  | 15 => c0S15
  | 16 => c0S16
  | 17 => c0S17
  | 18 => c0S18
  | 19 => c0S19
  | 20 => c0S20
  | 21 => c0S21
  | 22 => c0S22
  | 23 => c0S23
  | _ => 0

def sSL : ℕ → ℚ
  | 0 => sS0
  | 1 => sS1
  | 2 => sS2
  | 3 => sS3
  | 4 => sS4
  | 5 => sS5
  | 6 => sS6
  | 7 => sS7
  | 8 => sS8
  | 9 => sS9
  | 10 => sS10
  | 11 => sS11
  | 12 => sS12
  | 13 => sS13
  | 14 => sS14
  | 15 => sS15
  | 16 => sS16
  | 17 => sS17
  | 18 => sS18
  | 19 => sS19
  | 20 => sS20
  | 21 => sS21
  | 22 => sS22
  | 23 => sS23
  | _ => 0

theorem slopeL {j : ℕ} (hj : j < 24) {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert eL (gSL j).length (gcertG eL (gSL j)) (c0SL j : ℝ) y + 3 / 16 ≤
      1 - slopeKernel (tgR j) y := by
  have e : tgR j = ((247 + 78 * j : ℕ) : ℝ) / 2 ^ 11 := tgR_eq j
  rw [e]
  interval_cases j
  · simpa [gSL, c0SL] using slope0 eL_mem hy
  · simpa [gSL, c0SL] using slope1 eL_mem hy
  · simpa [gSL, c0SL] using slope2 eL_mem hy
  · simpa [gSL, c0SL] using slope3 eL_mem hy
  · simpa [gSL, c0SL] using slope4 eL_mem hy
  · simpa [gSL, c0SL] using slope5 eL_mem hy
  · simpa [gSL, c0SL] using slope6 eL_mem hy
  · simpa [gSL, c0SL] using slope7 eL_mem hy
  · simpa [gSL, c0SL] using slope8 eL_mem hy
  · simpa [gSL, c0SL] using slope9 eL_mem hy
  · simpa [gSL, c0SL] using slope10 eL_mem hy
  · simpa [gSL, c0SL] using slope11 eL_mem hy
  · simpa [gSL, c0SL] using slope12 eL_mem hy
  · simpa [gSL, c0SL] using slope13 eL_mem hy
  · simpa [gSL, c0SL] using slope14 eL_mem hy
  · simpa [gSL, c0SL] using slope15 eL_mem hy
  · simpa [gSL, c0SL] using slope16 eL_mem hy
  · simpa [gSL, c0SL] using slope17 eL_mem hy
  · simpa [gSL, c0SL] using slope18 eL_mem hy
  · simpa [gSL, c0SL] using slope19 eL_mem hy
  · simpa [gSL, c0SL] using slope20 eL_mem hy
  · simpa [gSL, c0SL] using slope21 eL_mem hy
  · simpa [gSL, c0SL] using slope22 eL_mem hy
  · simpa [gSL, c0SL] using slope23 eL_mem hy

theorem margL {j : ℕ} (hj : j < 24) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 16)) :
    (5 / 29 + 1 / 20 : ℝ) ≤ (1 - α) * (c0SL j : ℝ) +
      ∑ k ∈ Finset.range (gSL j).length, gcertG eL (gSL j) k * trialSeqS Pc P (k + 1) - (sSL j : ℝ) := by
  interval_cases j
  · exact marg_S0 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S1 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S2 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S3 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S4 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S5 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S6 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S7 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S8 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S9 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S10 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S11 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S12 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S13 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S14 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S15 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S16 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S17 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S18 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S19 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S20 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S21 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S22 rfl (fun k => rfl) (fun k => rfl) hα
  · exact marg_S23 rfl (fun k => rfl) (fun k => rfl) hα

theorem statL {j : ℕ} (hj : j < 24) :
    certH (gSL j).length (gcertG eL (gSL j)) * (13 / 5000 : ℝ) ≤ (sSL j : ℝ) ^ 2 := by
  have key : ∀ {g : List ℚ} {s : ℚ}, Hq g (1 / 2 ^ 20) * (3 / 1000) ≤ s ^ 2 →
      certH g.length (gcertG eL g) * (13 / 5000 : ℝ) ≤ (s : ℝ) ^ 2 := by
    intro g s hs
    have := certH_mul_le_mono (e' := 1 / 2 ^ 30) (e := 1 / 2 ^ 20) (g := g) (s := s)
      (Dm := 3 / 1000) (D := 13 / 5000) (by norm_num) (by norm_num) hs (by norm_num) (by norm_num)
      (by norm_num)
    push_cast at this
    simpa [eL] using this
  interval_cases j
  · exact key slope0_stat
  · exact key slope1_stat
  · exact key slope2_stat
  · exact key slope3_stat
  · exact key slope4_stat
  · exact key slope5_stat
  · exact key slope6_stat
  · exact key slope7_stat
  · exact key slope8_stat
  · exact key slope9_stat
  · exact key slope10_stat
  · exact key slope11_stat
  · exact key slope12_stat
  · exact key slope13_stat
  · exact key slope14_stat
  · exact key slope15_stat
  · exact key slope16_stat
  · exact key slope17_stat
  · exact key slope18_stat
  · exact key slope19_stat
  · exact key slope20_stat
  · exact key slope21_stat
  · exact key slope22_stat
  · exact key slope23_stat

theorem sSL_nonneg {j : ℕ} (hj : j < 24) : (0 : ℝ) ≤ (sSL j : ℝ) := by
  interval_cases j <;> simp only [sSL] <;> (try unfold sS0) <;> norm_num [sS0, sS1, sS2, sS3, sS4, sS5, sS6,
    sS7, sS8, sS9, sS10, sS11, sS12, sS13, sS14, sS15, sS16, sS17, sS18, sS19, sS20, sS21, sS22, sS23]

/- The class-link data of the near case. -/
namespace Generic

open CatalanMeasure.GenD.Signed

/-- Actual certified link data: signed field tables, sign/mean/slope bounds and
finite-N gap/top estimates. Geometry/count identities are derived by `link`.
No certificate output is inferred from the design. -/
structure LinkData (dc : DesignConst) (I : Inputs dc)
    (pRef vRef : ℕ → ℝ) (MXRef targetOld costOld δ e c2 : ℝ) where
  Dcap : Fin 2 → ℝ
  hDcap : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i), excess targetOld costOld I.target c2 δ (dc.n0 : ℝ) α ≤ Dcap i
  Dtop : ℝ
  hDtop : ∀ α ∈ Icc (0 : ℝ) I.α1, excess targetOld costOld I.target c2 δ (dc.n0 : ℝ) α ≤ Dtop
  Cp : Fin 2 → PolyCert
  Cm : Fin 2 → PolyCert
  sP : Fin 2 → ℝ
  sM : Fin 2 → ℝ
  hsP0 : ∀ i, 0 ≤ sP i
  hsM0 : ∀ i, 0 ≤ sM i
  hsP : ∀ i, certH (Cp i).K (Cp i).G * Dcap i ≤ sP i ^ 2
  hsM : ∀ i, certH (Cm i).K (Cm i).G * Dcap i ≤ sM i ^ 2
  hCp_neg : ∀ i, ∀ y ∈ Icc (-1 : ℝ) 1, y < 0 → evalCert e (Cp i).K (Cp i).G (Cp i).c0 y ≤ 0
  hCp_pos : ∀ i, ∀ y ∈ Icc (-1 : ℝ) 1, 0 < y → evalCert e (Cp i).K (Cp i).G (Cp i).c0 y ≤ 1
  hCm_neg : ∀ i, ∀ y ∈ Icc (-1 : ℝ) 1, y < 0 → evalCert e (Cm i).K (Cm i).G (Cm i).c0 y ≤ 1
  hCm_pos : ∀ i, ∀ y ∈ Icc (-1 : ℝ) 1, 0 < y → evalCert e (Cm i).K (Cm i).G (Cm i).c0 y ≤ 0
  hκlo : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i),
    I.κlo i ≤ (1 - α) * (Cm i).c0 + certMean (Cm i).K (Cm i).G pRef - sM i
  hκhi : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i),
    (1 - α) - ((1 - α) * (Cp i).c0 + certMean (Cp i).K (Cp i).G pRef - sP i) ≤ I.κhi i
  hk0 : ∀ i, 0 < I.κlo i
  hq2g : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i),
    2 * (dc.g0 : ℝ) / dc.n0 < (1 - α) * (Cp i).c0 + certMean (Cp i).K (Cp i).G pRef - sP i
  hspq_floor : ((dc.sp : ℝ) + dc.g0) / dc.n0 ≤ (dc.hspq_qlo : ℝ)
  hqlo : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i), (dc.hspq_qlo : ℝ) ≤
    (1 - α) * (Cp i).c0 + certMean (Cp i).K (Cp i).G pRef - sP i
  a0 : ℝ
  ts : ℝ
  dgap : ℝ
  ηT : ℝ
  ha0 : 0 < a0
  hts : 0 < ts
  hdgap : 0 < dgap
  hηT : 0 < ηT
  hgap : ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, 0 < |x| → |x| < a0 →
    freeRowX dc.toParameters N pRef vRef x ≤ MXRef + δ / 4 - dgap
  hsmall : ∀ α ∈ Icc (0 : ℝ) I.α1,
    2 * (dc.g0 : ℝ) / dc.n0 + ηT < ((1 - α) - Dtop / dgap) * (a0 ^ 2 / (ts ^ 2 + a0 ^ 2))
  J : ℕ
  tg : Fin J → ℝ
  hmesh : ℝ
  htg : ∀ j, tg j ∈ Icc ts 1
  hcov : ∀ t ∈ Icc ts 1, ∃ j, |t - tg j| ≤ hmesh
  Ct : Fin J → PolyCert
  sT : Fin J → ℝ
  hsT0 : ∀ j, 0 ≤ sT j
  hsT : ∀ j, certH (Ct j).K (Ct j).G * Dtop ≤ sT j ^ 2
  hPt : ∀ j, ∀ y ∈ Icc (-1 : ℝ) 1, y ≠ 0 →
    evalCert e (Ct j).K (Ct j).G (Ct j).c0 y + hmesh / ts ≤ 1 - slopeKernel (tg j) y
  hmarg : ∀ j, ∀ α ∈ Icc (0 : ℝ) I.α1, 2 * (dc.g0 : ℝ) / dc.n0 + ηT ≤
    (1 - α) * (Ct j).c0 + certMean (Ct j).K (Ct j).G pRef - sT j
  θ0 : ℝ
  dsp : ℝ
  hθ0 : 0 ≤ θ0
  hdsp : 0 < dsp
  hθcut : (dc.thetaL : ℝ) ≤ θ0
  hxcθ : I.xc ≤ 1 - θ0
  hxcnn : 0 ≤ I.xc
  hC1nn : 0 ≤ I.C1
  hsup : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (1 - θ0) 1,
    freeRowX dc.toParameters N pRef vRef x ≤ MXRef + δ / 4 - dsp

/-- Assemble LinkCert after identifying the actual first/column witness fields. -/
def link (dc : DesignConst) (I : Inputs dc) (R : Rows dc I)
    {pRef vRef : ℕ → ℝ} {MXRef targetOld residual nearCap costOld δ e c2 : ℝ}
    {G : ℝ → Prop}
    (C : LinkData dc I pRef vRef MXRef targetOld costOld δ e c2)
    (D0 : SecondTrialBoundsEnd dc.toParameters 0 targetOld residual nearCap costOld G)
    (hp : D0.p = pRef) (hv : D0.v = vRef) (hMX : D0.MX = MXRef)
    (hCls : ∀ N k q m1 m2 xn gp yn yp,
      ClsfCanon (fun i N => (I.DA i N).θ) (fun i N => (I.DA i N).sp)
        (fun i N => (I.DA i N).g) (fun i N => (I.DA i N).ν)
        (fun N => ((dc.n0 * N : ℕ) : ℝ)) (fun N => ((dc.n0 * N : ℕ) : ℝ) + 1)
        (CatalanMeasure.Signed.Consts.Generic.mmaxOf dc (C.Dtop / C.dsp + I.C1 * C.θ0))
        N k q m1 m2 xn gp yn yp → R.Clsf N k q m1 m2 xn gp yn yp) :
    LinkCert (phase2 dc I R) dc.toParameters targetOld residual nearCap costOld G D0 δ e
      I.target c2 where
  Dcap := C.Dcap
  hDcap := C.hDcap
  Dtop := C.Dtop
  hDtop := C.hDtop
  Cp := C.Cp
  Cm := C.Cm
  sP := C.sP
  sM := C.sM
  hsP0 := C.hsP0
  hsM0 := C.hsM0
  hsP := C.hsP
  hsM := C.hsM
  hCp_neg := C.hCp_neg
  hCp_pos := C.hCp_pos
  hCm_neg := C.hCm_neg
  hCm_pos := C.hCm_pos
  hκlo := by simpa only [hp, phase2] using C.hκlo
  hκhi := by simpa only [hp, phase2] using C.hκhi
  hk0 := C.hk0
  hq2g := by simpa only [hp, phase2] using C.hq2g
  a0 := C.a0
  ts := C.ts
  dgap := C.dgap
  ηT := C.ηT
  ha0 := C.ha0
  hts := C.hts
  hdgap := C.hdgap
  hηT := C.hηT
  hgap := by simpa only [hp, hv, hMX] using C.hgap
  hsmall := C.hsmall
  J := C.J
  tg := C.tg
  hmesh := C.hmesh
  htg := C.htg
  hcov := C.hcov
  Ct := C.Ct
  sT := C.sT
  hsT0 := C.hsT0
  hsT := C.hsT
  hPt := C.hPt
  hmarg := by simpa only [hp, phase2] using C.hmarg
  θ0 := C.θ0
  dsp := C.dsp
  hθ0 := C.hθ0
  hdsp := C.hdsp
  hxcθ := C.hxcθ
  hxcnn := C.hxcnn
  hC1nn := C.hC1nn
  hsup := by simpa only [hp, hv, hMX] using C.hsup
  hθi := fun i N => by
    change (I.DA i N).θ ≤ C.θ0
    rw [I.hDA]
    exact C.hθcut
  Kn := fun N => ((dc.n0 * N : ℕ) : ℝ)
  Tn := fun N => ((dc.n0 * N : ℕ) : ℝ) + 1
  Mmax := CatalanMeasure.Signed.Consts.Generic.mmaxOf dc (C.Dtop / C.dsp + I.C1 * C.θ0)
  hKn := fun N => le_rfl
  hTn := fun N => le_rfl
  hMmax := fun N => by
    simpa only [Parameters.n, Nat.cast_mul, phase2] using
      CatalanMeasure.Signed.Consts.Generic.mmaxOf_ge dc (C.Dtop / C.dsp + I.C1 * C.θ0) N
  hgA := fun i N => by
    change (I.DA i N).g = dc.g0 * N
    rw [I.hDA]
    rfl
  hspA := fun i N hN => by
    change 0 < (I.DA i N).sp
    rw [I.hDA]
    change 0 < dc.sp * N
    exact Nat.mul_pos dc.sp_pos (by omega)
  hspq := fun i i0 N hN α hα => by
    let Q : ℝ := (1 - α) * (C.Cp i0).c0 + certMean (C.Cp i0).K (C.Cp i0).G pRef - C.sP i0
    have hn0 : (0 : ℝ) < dc.n0 := by exact_mod_cast dc.n0_pos
    have hratio : ((dc.sp : ℝ) + dc.g0) / dc.n0 ≤ Q := C.hspq_floor.trans (C.hqlo i0 α hα)
    have hsum : (dc.sp : ℝ) + dc.g0 ≤ Q * dc.n0 := (div_le_iff₀ hn0).1 hratio
    have hscaled := mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    change ((I.DA i N).sp : ℝ) + ((dc.g0 * N : ℕ) : ℝ) ≤
      ((1 - α) * (C.Cp i0).c0 + certMean (C.Cp i0).K (C.Cp i0).G D0.p - C.sP i0) *
        ((dc.n0 * N : ℕ) : ℝ)
    rw [hp, I.hDA]
    change ((dc.sp * N : ℕ) : ℝ) + ((dc.g0 * N : ℕ) : ℝ) ≤ Q * ((dc.n0 * N : ℕ) : ℝ)
    push_cast
    nlinarith only [hscaled]
  hClsf := hCls

/-- A checked scalar budget for the actual p/v sequences pays the damping error. -/
theorem hec_of_bounds {p v : ℕ → ℝ} {e δ Psum Vsum P1 : ℝ} (he0 : 0 ≤ e)
    (hp : (∑' j, |p j|) ≤ Psum) (hv : (∑' j, |v j|) ≤ Vsum) (hp1 : |p 1| ≤ P1)
    (hbudget : e * (4 * Psum + 4 * Vsum + P1 + 20) < δ / 2) :
    e * (4 * (∑' j, |p j|) + 4 * (∑' j, |v j|) + |p 1| + 20) < δ / 2 := by
  have hsum : 4 * (∑' j, |p j|) + 4 * (∑' j, |v j|) + |p 1| + 20 ≤
      4 * Psum + 4 * Vsum + P1 + 20 := by linarith only [hp, hv, hp1]
  exact (mul_le_mul_of_nonneg_left hsum he0).trans_lt hbudget

end Generic


/-- The D58 link certificate outputs; these are supplied data, not design identities. -/
def linkData410 : Generic.LinkData dc58 inputs410
    (trialSeqS Pc P) (trialSeqS CatalanMeasure.GenD.D58.Cert590.Vc CatalanMeasure.GenD.D58.Cert590.V)
    ((CatalanMeasure.GenD.D58.Cert590.MX : ℚ) : ℝ) K590.target K590.secondCost'
    (13 / 100000) eL c2_410 where
  Dcap := fun _ => 13 / 5000
  hDcap := fun i α _ => excess_le_dtop410 α (by norm_num [P410, D58.Odd.design])
    (by norm_num [c2_410, P410, D58.Odd.design])
    (by
      have htarget : inputs410.target = K590.target0 := rfl
      rw [htarget]
      have := K590.target0_sub
      nlinarith) le_rfl
  Dtop := 13 / 5000
  hDtop := fun α _ => excess_le_dtop410 α (by norm_num [P410, D58.Odd.design])
    (by norm_num [c2_410, P410, D58.Odd.design])
    (by
      have htarget : inputs410.target = K590.target0 := rfl
      rw [htarget]
      have := K590.target0_sub
      nlinarith) le_rfl
  Cp := fun _ => ⟨gCp.length, gcertG eL gCp, (c0Cp : ℝ)⟩
  Cm := fun _ => ⟨gCm.length, gcertG eL gCm, (c0Cm : ℝ)⟩
  sP := fun _ => (sCp : ℝ)
  sM := fun _ => (sCm : ℝ)
  hsP0 := fun _ => by norm_num [sCp]
  hsM0 := fun _ => by norm_num [sCm]
  hsP := fun _ => by
    have := certH_mul_le_mono (e' := 1 / 2 ^ 30) (e := 1 / 2 ^ 20) (g := gCp) (s := sCp)
      (Dm := 3 / 1000) (D := 13 / 5000) (by norm_num) (by norm_num) Cp_stat (by norm_num)
      (by norm_num) (by norm_num)
    push_cast at this
    simpa [eL] using this
  hsM := fun _ => by
    have := certH_mul_le_mono (e' := 1 / 2 ^ 30) (e := 1 / 2 ^ 20) (g := gCm) (s := sCm)
      (Dm := 3 / 1000) (D := 13 / 5000) (by norm_num) (by norm_num) Cm_stat (by norm_num)
      (by norm_num) (by norm_num)
    push_cast at this
    simpa [eL] using this
  hCp_neg := fun _ y hy h => Cp_neg eL_mem hy h
  hCp_pos := fun _ y hy h => Cp_pos eL_mem hy h
  hCm_neg := fun _ y hy h => Cm_neg eL_mem hy h
  hCm_pos := fun _ y hy h => Cm_pos eL_mem hy h
  hκlo := fun i α hα => by
    rw [certMean]
    fin_cases i
    · exact (kappaLo_I0 rfl (fun _ => rfl) (fun _ => rfl) hα)
    · exact (kappaLo_I1 rfl (fun _ => rfl) (fun _ => rfl) hα)
  hκhi := fun i α hα => by
    rw [certMean]
    fin_cases i
    · exact (kappaHi_I0 rfl (fun _ => rfl) (fun _ => rfl) hα)
    · exact (kappaHi_I1 rfl (fun _ => rfl) (fun _ => rfl) hα)
  hk0 := fun i => by fin_cases i <;> norm_num [inputs410, κlo410]
  hq2g := fun i α hα => by
    rw [certMean]
    have h5 : 2 * (dc58.g0 : ℝ) / dc58.n0 = 5 / 29 := by norm_num
    rw [h5]
    fin_cases i
    · have := q_ge_I0 (G := gcertG eL gCp) rfl (fun _ => rfl) (fun _ => rfl) hα; dsimp only; linarith
    · have := q_ge_I1 (G := gcertG eL gCp) rfl (fun _ => rfl) (fun _ => rfl) hα; dsimp only; linarith
  hspq_floor := by norm_num
  hqlo := fun i α hα => by
    have hq : (dc58.hspq_qlo : ℝ) = (25 / 58 : ℝ) := by norm_num
    rw [hq, certMean]
    fin_cases i
    · exact q_ge_I0 rfl (fun _ => rfl) (fun _ => rfl) hα
    · exact q_ge_I1 rfl (fun _ => rfl) (fun _ => rfl) hα
  a0 := 7 / 100
  ts := 13 / 128
  dgap := 1 / 25
  ηT := 1 / 20
  ha0 := by norm_num
  hts := by norm_num
  hdgap := by norm_num
  hηT := by norm_num
  hgap := by
    have := link_hgap_odd (δ := 13 / 100000) (by norm_num) rfl rfl rfl
    filter_upwards [this] with N hN x h0 h1 using hN x h0 h1
  hsmall := fun α hα => by
    have h5 : 2 * (dc58.g0 : ℝ) / dc58.n0 = 5 / 29 := by norm_num
    rw [h5]
    have : α ≤ 1 / 16 := hα.2
    norm_num
    nlinarith [hα.1]
  J := 24
  tg := fun j => tgR j
  hmesh := 39 / 2048
  htg := fun j => by
    have := tgR_mem j.2
    exact ⟨by norm_num at this ⊢; exact this.1, this.2⟩
  hcov := fun t ht => by
    obtain ⟨j, hj, h⟩ := tgR_cover ⟨by norm_num at ht ⊢; exact ht.1, ht.2⟩
    exact ⟨⟨j, hj⟩, h⟩
  Ct := fun j => ⟨(gSL j).length, gcertG eL (gSL j), (c0SL j : ℝ)⟩
  sT := fun j => (sSL j : ℝ)
  hsT0 := fun j => sSL_nonneg j.2
  hsT := fun j => statL j.2
  hPt := fun j y hy h0 => by
    have := slopeL j.2 hy
    have e : (39 / 2048 : ℝ) / (13 / 128) = 3 / 16 := by norm_num
    show evalCert eL (gSL j).length (gcertG eL (gSL j)) (c0SL j : ℝ) y + (39 / 2048) / (13 / 128) ≤ _
    rw [e]; exact this
  hmarg := fun j α hα => by
    have h5 : 2 * (dc58.g0 : ℝ) / dc58.n0 = 5 / 29 := by norm_num
    rw [h5, certMean]
    exact margL j.2 hα
  θ0 := 1 / 1000
  dsp := 18 / 125
  hθ0 := by norm_num
  hdsp := by norm_num
  hθcut := by norm_num
  hxcθ := by norm_num [inputs410]
  hxcnn := by norm_num [inputs410]
  hC1nn := by norm_num [inputs410]
  hsup := by
    have := link_hsup_odd (δ := 13 / 100000) (by norm_num) rfl rfl rfl
    filter_upwards [this] with N hN x hx using hN x hx


def link410 (R : Rows410) {residual nearCap : ℝ}
    (D0 : SecondTrialBoundsEnd P410 0 K590.target residual nearCap K590.secondCost' G410)
    (hp : D0.p = trialSeqS Pc P) (hM : D0.MX = ((CatalanMeasure.GenD.D58.Cert590.MX : ℚ) : ℝ))
    (hv : D0.v = trialSeqS CatalanMeasure.GenD.D58.Cert590.Vc CatalanMeasure.GenD.D58.Cert590.V)
    (hCls : ∀ N k q m1 m2 xn gp yn yp,
      ClsfCanon (fun i N => ((phase2 R).DA i N).θ) (fun i N => ((phase2 R).DA i N).sp)
        (fun i N => ((phase2 R).DA i N).g) (fun i N => ((phase2 R).DA i N).ν)
        (fun N => ((58 * N : ℕ) : ℝ)) (fun N => ((58 * N : ℕ) : ℝ) + 1) (mmaxOf s410) N k q m1 m2
        xn gp yn yp → (phase2 R).Clsf N k q m1 m2 xn gp yn yp) :
    LinkCert (phase2 R) P410 K590.target residual nearCap K590.secondCost' G410 D0
      (13 / 100000) eL K590.target0 c2_410 := by
  have hs : linkData410.Dtop / linkData410.dsp + inputs410.C1 * linkData410.θ0 = s410 := rfl
  have hCap : CatalanMeasure.Signed.Consts.Generic.mmaxOf dc58
      (linkData410.Dtop / linkData410.dsp + inputs410.C1 * linkData410.θ0) = mmaxOf s410 := by
    rw [hs]
    rfl
  apply Generic.link dc58 inputs410 (Rows410.toGeneric R) linkData410 D0 hp hv hM
  simpa only [phase2, Generic.phase2, Rows410.toGeneric, dc58_n0, hCap] using hCls

theorem hec410' {residual nearCap : ℝ}
    (D0 : SecondTrialBoundsEnd P410 0 K590.target residual nearCap K590.secondCost' G410)
    (hp : D0.p = trialSeqS Pc P) (hv : D0.v = trialSeqS CatalanMeasure.GenD.D58.Cert590.Vc CatalanMeasure.GenD.D58.Cert590.V) :
    eL * (4 * (∑' j, |D0.p j|) + 4 * (∑' j, |D0.v j|) + |D0.p 1| + 20) < (13 / 100000) / 2 :=
  hec_K590 (by positivity) le_rfl le_rfl hp hv

end

end CatalanMeasure.GenD.Signed.Data.Assembly

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.eL_mem
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.slopeL
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.margL
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.statL
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.sSL_nonneg
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.hec_of_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.hec410'

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.link

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.linkData410

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.link410

module

public import CatalanMeasure.GenD.Signed.Data.Assembly.Data
public import CatalanMeasure.GenD.DesignInstance.PositiveBudget

@[expose] public section

/-!
# 410 assembly: the `Phase2Data 2` term
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed OAI.InternalCatalan CatalanMeasure.Parametric CatalanMeasure.GenD.Analytic

open CatalanMeasure.GenD.D58
open CatalanMeasure.GenD.Signed.Data.S1 CatalanMeasure.GenD.Signed.Data.Trial

noncomputable section

namespace Generic

theorem hn_top (dc : DesignConst) : Tendsto (fun N : ℕ => ((dc.n0 * N : ℕ) : ℝ)) atTop atTop :=
  (CatalanMeasure.Signed.Consts.hn_top_lin (n0 := (dc.n0 : ℝ)) (by exact_mod_cast dc.n0_pos)).congr
    (fun N => by push_cast; rfl)

theorem hlogu (dc : DesignConst) (I : Inputs dc) :
    Tendsto (fun N : ℕ => -Real.log (I.umin N) / ((dc.n0 * N : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hd : 0 < dc.d0 := by
    have h := dc.admissible.2.2.2.2
    unfold DesignConst.d0
    omega
  have h := CatalanMeasure.Signed.Consts.hlogu_lin
    (s := Real.sqrt (1 - (dc.astar : ℝ) ^ 2)) (A := 2 * (dc.d0 : ℝ)) (B := 2) (n0 := (dc.n0 : ℝ))
    (Real.sqrt_pos.2 (one_sub_astar_sq_pos dc))
    (by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hd)
    (by norm_num) (by exact_mod_cast dc.n0_pos)
  refine h.congr (fun N => ?_)
  rw [I.humin]
  unfold umin
  push_cast
  rw [show 2 * (dc.d0 : ℝ) * (N : ℝ) + 2 =
    2 * ((dc.d0 : ℝ) * (N : ℝ) + 1) by ring]

def phase2 (dc : DesignConst) (I : Inputs dc) (R : Rows dc I) : Phase2Data 2 where
  ncount := fun N => dc.n0 * N
  ncount_pos := fun N hN => Nat.mul_pos dc.n0_pos hN
  B := -I.target + Real.log 2 / 2
  cost := I.cost
  α1 := I.α1
  α1_nonneg := I.α1_nonneg
  lo := I.lo
  hi := I.hi
  cover := I.cover
  Rf := fun N => populationPhysicalFreeField dc.toParameters N
  Cf := fun N => populationPhysicalColumnField dc.toParameters N (0 + 0)
  Rm := fun N => groupedMarkedField dc.toParameters N
  Rn := fun N => groupedNearField dc.toParameters N
  constant := fun N α => Glue410.constantClosed dc.toParameters N α
  αA := I.αA
  αB := I.αB
  DA := I.DA
  DB := I.DB
  hends := I.hends
  hν := fun i N => by rw [I.hDA]; simp only [famD, Nat.cast_mul]
  hRf := fun i N => by rw [I.hDA]; rfl
  hCf := fun i N => by rw [I.hDA]; rfl
  mA := I.massA
  mB := I.massB
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
  rA := R.rA
  rB := R.rB
  κc := R.κc
  hP := Glue410.hP_closed dc.admissible I.hlo0 I.hhi1 R.hcP
  hrA := R.hrA
  hrB := R.hrB
  hκ := R.hκ
  κlo := I.κlo
  κhi := I.κhi
  epsSplit := I.epsSplit
  epsSplit_pos := I.epsSplit_pos
  epsSplit_le := I.epsSplit_le
  etaA := I.etaA
  Clsf := R.Clsf
  LRf := fun N k q m1 m2 xn gp yn yp =>
    logRatioZ (q + m2 - dc.g0 * N) (Fin.append xn yn) (Fin.append gp yp)
  cp := R.cp
  cp_pos := R.cp_pos
  cp_le := R.cp_le
  err_small := R.err_small
  cp_theta := R.cp_theta
  hLR := fun i N k q m1 m2 xn gp yn yp => by rw [I.hDA]; rfl
  hCls := R.hCls
  capE := R.capE
  hxc0 := R.hxc0
  hxc1 := R.hxc1
  hC1 := R.hC1
  hlo0 := I.hlo0
  hhi1 := I.hhi1
  hrP := R.hrP
  hrSA := R.hrSA
  hrSB := R.hrSB
  umin := I.umin
  hum0 := fun N => by rw [I.humin]; exact umin_pos dc N
  hum1 := fun N => by rw [I.humin]; exact umin_le_one dc N
  Bd := R.Bd
  Rbd := R.Rbd
  hBdPA := R.hBdPA
  hBdPB := R.hBdPB
  hBdSA := R.hBdSA
  hBdSB := R.hBdSB
  hRP := R.hRP
  hRSA := R.hRSA
  hRSB := R.hRSB
  hn_top := hn_top dc
  hlogu := hlogu dc I
  gs := I.gs
  xc := I.xc
  C1 := I.C1
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

end Generic

theorem hn_top410 : Tendsto (fun N : ℕ => ((58 * N : ℕ) : ℝ)) atTop atTop :=
  Generic.hn_top dc58

theorem hlogu410 : Tendsto (fun N : ℕ => -Real.log (umin410 N) / ((58 * N : ℕ) : ℝ)) atTop (𝓝 0) :=
  Generic.hlogu dc58 inputs410

/-- **`Phase2Data 2` of the 410 chain** from the ingredient rows. -/
def phase2 (R : Rows410) : Phase2Data 2 :=
  Generic.phase2 dc58 inputs410 R.toGeneric


end

end CatalanMeasure.GenD.Signed.Data.Assembly

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.phase2
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.phase2

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.hn_top
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.hlogu
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.hn_top410
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.hlogu410

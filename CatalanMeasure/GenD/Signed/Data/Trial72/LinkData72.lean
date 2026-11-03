module

public import CatalanMeasure.GenD.Signed.Data.Assembly.Link
public import CatalanMeasure.GenD.Signed.Data.Trial72.LControl72
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkGrid

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CatalanMeasure.GenD.Signed.Data.Trial72.LinkData72
open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.Consts CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Assembly CatalanMeasure.GenD.Signed.Data.Assembly.Generic
noncomputable section

def cp : PolyCert := ⟨LRows00.Row0.g.length, gcertG (LRows00.Row0.e : ℝ) LRows00.Row0.g, (LRows00.Row0.c0 : ℝ)⟩
def cm : PolyCert := ⟨LRows00.Row1.g.length, gcertG (LRows00.Row1.e : ℝ) LRows00.Row1.g, (LRows00.Row1.c0 : ℝ)⟩
def ct (j : Fin 24) : PolyCert :=
  ([⟨LRows00.Row2.g.length, gcertG (LRows00.Row2.e : ℝ) LRows00.Row2.g, (LRows00.Row2.c0 : ℝ)⟩, ⟨LRows00.Row3.g.length, gcertG (LRows00.Row3.e : ℝ) LRows00.Row3.g, (LRows00.Row3.c0 : ℝ)⟩, ⟨LRows00.Row4.g.length, gcertG (LRows00.Row4.e : ℝ) LRows00.Row4.g, (LRows00.Row4.c0 : ℝ)⟩, ⟨LRows01.Row5.g.length, gcertG (LRows01.Row5.e : ℝ) LRows01.Row5.g, (LRows01.Row5.c0 : ℝ)⟩, ⟨LMeanPilot.g.length, gcertG (LMeanPilot.e : ℝ) LMeanPilot.g, (LMeanPilot.c0 : ℝ)⟩, ⟨LRows01.Row7.g.length, gcertG (LRows01.Row7.e : ℝ) LRows01.Row7.g, (LRows01.Row7.c0 : ℝ)⟩, ⟨LRows01.Row8.g.length, gcertG (LRows01.Row8.e : ℝ) LRows01.Row8.g, (LRows01.Row8.c0 : ℝ)⟩, ⟨LRows01.Row9.g.length, gcertG (LRows01.Row9.e : ℝ) LRows01.Row9.g, (LRows01.Row9.c0 : ℝ)⟩, ⟨LRows01.Row10.g.length, gcertG (LRows01.Row10.e : ℝ) LRows01.Row10.g, (LRows01.Row10.c0 : ℝ)⟩, ⟨LRows02.Row11.g.length, gcertG (LRows02.Row11.e : ℝ) LRows02.Row11.g, (LRows02.Row11.c0 : ℝ)⟩, ⟨LRows02.Row12.g.length, gcertG (LRows02.Row12.e : ℝ) LRows02.Row12.g, (LRows02.Row12.c0 : ℝ)⟩, ⟨LRows02.Row13.g.length, gcertG (LRows02.Row13.e : ℝ) LRows02.Row13.g, (LRows02.Row13.c0 : ℝ)⟩, ⟨LRows02.Row14.g.length, gcertG (LRows02.Row14.e : ℝ) LRows02.Row14.g, (LRows02.Row14.c0 : ℝ)⟩, ⟨LRows02.Row15.g.length, gcertG (LRows02.Row15.e : ℝ) LRows02.Row15.g, (LRows02.Row15.c0 : ℝ)⟩, ⟨LRows03.Row16.g.length, gcertG (LRows03.Row16.e : ℝ) LRows03.Row16.g, (LRows03.Row16.c0 : ℝ)⟩, ⟨LRows03.Row17.g.length, gcertG (LRows03.Row17.e : ℝ) LRows03.Row17.g, (LRows03.Row17.c0 : ℝ)⟩, ⟨LRows03.Row18.g.length, gcertG (LRows03.Row18.e : ℝ) LRows03.Row18.g, (LRows03.Row18.c0 : ℝ)⟩, ⟨LRows03.Row19.g.length, gcertG (LRows03.Row19.e : ℝ) LRows03.Row19.g, (LRows03.Row19.c0 : ℝ)⟩, ⟨LRows03.Row20.g.length, gcertG (LRows03.Row20.e : ℝ) LRows03.Row20.g, (LRows03.Row20.c0 : ℝ)⟩, ⟨LRows04.Row21.g.length, gcertG (LRows04.Row21.e : ℝ) LRows04.Row21.g, (LRows04.Row21.c0 : ℝ)⟩, ⟨LRows04.Row22.g.length, gcertG (LRows04.Row22.e : ℝ) LRows04.Row22.g, (LRows04.Row22.c0 : ℝ)⟩, ⟨LRows04.Row23.g.length, gcertG (LRows04.Row23.e : ℝ) LRows04.Row23.g, (LRows04.Row23.c0 : ℝ)⟩, ⟨LRows04.Row24.g.length, gcertG (LRows04.Row24.e : ℝ) LRows04.Row24.g, (LRows04.Row24.c0 : ℝ)⟩, ⟨LRows04.Row25.g.length, gcertG (LRows04.Row25.e : ℝ) LRows04.Row25.g, (LRows04.Row25.c0 : ℝ)⟩] : List PolyCert).get j
def st (j : Fin 24) : ℝ :=
  ([(LRows00.Row2.s : ℝ), (LRows00.Row3.s : ℝ), (LRows00.Row4.s : ℝ), (LRows01.Row5.s : ℝ), (LMeanPilot.s : ℝ), (LRows01.Row7.s : ℝ), (LRows01.Row8.s : ℝ), (LRows01.Row9.s : ℝ), (LRows01.Row10.s : ℝ), (LRows02.Row11.s : ℝ), (LRows02.Row12.s : ℝ), (LRows02.Row13.s : ℝ), (LRows02.Row14.s : ℝ), (LRows02.Row15.s : ℝ), (LRows03.Row16.s : ℝ), (LRows03.Row17.s : ℝ), (LRows03.Row18.s : ℝ), (LRows03.Row19.s : ℝ), (LRows03.Row20.s : ℝ), (LRows04.Row21.s : ℝ), (LRows04.Row22.s : ℝ), (LRows04.Row23.s : ℝ), (LRows04.Row24.s : ℝ), (LRows04.Row25.s : ℝ)] : List ℝ).get j

def data {H : NodeGeometryData dc72} (I : InputsAsym dc72 H) {MXRef targetOld costOld c2 : ℝ}
    (hα1 : I.α1 = 1/16)
    (hdom : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i), α ∈ Icc (0 : ℝ) (1/16))
    (hlo : ∀ i, I.κlo i = 1/4) (hhi : ∀ i, I.κhi i = 1/2)
    (hDcap : ∀ i, ∀ α ∈ Icc (I.lo i) (I.hi i),
      excess targetOld costOld I.target c2 (13/100000) (dc72.n0 : ℝ) α ≤ 13/5000)
    (hDtop : ∀ α ∈ Icc (0 : ℝ) I.α1,
      excess targetOld costOld I.target c2 (13/100000) (dc72.n0 : ℝ) α ≤ 13/5000)
    (hgap : ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, 0 < |x| → |x| < 7/100 →
      freeRowX dc72.toParameters N ReferenceData.secondP ReferenceData.secondV x ≤ MXRef + (13/100000)/4 - 1/25)
    (hsup : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (1-1/1000) 1,
      freeRowX dc72.toParameters N ReferenceData.secondP ReferenceData.secondV x ≤ MXRef + (13/100000)/4 - 17/100)
    (hxc : I.xc ≤ 1-1/1000) (hxc0 : 0 ≤ I.xc) (hC1 : 0 ≤ I.C1) :
    LinkDataAsym dc72 H I ReferenceData.secondP ReferenceData.secondV MXRef targetOld costOld
      (13/100000) (1/1073741824) c2 where
  Dcap := fun _ => 13/5000
  hDcap := hDcap
  Dtop := 13/5000
  hDtop := hDtop
  Cp := fun _ => cp
  Cm := fun _ => cm
  sP := fun _ => (LRows00.Row0.s : ℝ)
  sM := fun _ => (LRows00.Row1.s : ℝ)
  hsP0 := fun _ => by norm_num [LRows00.Row0.s]
  hsM0 := fun _ => by norm_num [LRows00.Row1.s]
  hsP := fun _ => LControl72.actualStatCp
  hsM := fun _ => LControl72.actualStatCm
  hCp_neg := fun _ _ hy hz => LControl72.actualCp_neg hy hz
  hCp_pos := fun _ _ hy hz => LControl72.actualCp_pos hy hz
  hCm_neg := fun _ _ hy hz => LControl72.actualCm_neg hy hz
  hCm_pos := fun _ _ hy hz => LControl72.actualCm_pos hy hz
  hκlo := by
    intro i α hα
    rw [hlo i]
    exact LControl72.actualMarginCm (hdom i α hα)
  hκhi := by
    intro i α hα
    rw [hhi i]
    exact LControl72.actualCpHalf (hdom i α hα).1
  hk0 := fun i => by rw [hlo i]; norm_num
  hq2g := by
    intro i α hα
    exact (show 2*(dc72.g0 : ℝ)/dc72.n0 < ((25/58 : ℚ) : ℝ) by norm_num [dc72]).trans_le
      (LControl72.actualMarginCp (hdom i α hα))
  hspq_floor := by norm_num [dc72]
  hqlo := by
    intro i α hα
    exact (show (dc72.hspq_qlo : ℝ) ≤ ((25/58 : ℚ) : ℝ) by norm_num [dc72]).trans
      (LControl72.actualMarginCp (hdom i α hα))
  a0 := 7/100
  ts := 13/128
  dgap := 1/25
  ηT := 1/20
  ha0 := by norm_num
  hts := by norm_num
  hdgap := by norm_num
  hηT := by norm_num
  hgap := hgap
  hsmall := by
    intro α hα
    have hh : α ≤ (1/16 : ℝ) := by simpa only [hα1] using hα.2
    have hm := mul_le_mul_of_nonneg_right (show (1-1/16 : ℝ) - (13/5000)/(1/25) ≤
      (1-α) - (13/5000)/(1/25) by linarith only [hh])
      (show 0 ≤ (7/100 : ℝ)^2 / ((13/128)^2 + (7/100)^2) by positivity)
    exact (show 2*(dc72.g0 : ℝ)/dc72.n0 + 1/20 < ((1-1/16 : ℝ) - (13/5000)/(1/25)) *
      ((7/100 : ℝ)^2 / ((13/128)^2 + (7/100)^2)) by norm_num [dc72]).trans_le hm
  J := 24
  tg := fun j => tgR j.val
  hmesh := 39/2048
  htg := fun j => tgR_mem j.isLt
  hcov := by
    intro t ht
    obtain ⟨j, hj, h⟩ := tgR_cover ht
    exact ⟨⟨j,hj⟩,h⟩
  Ct := ct
  sT := st
  hsT0 := by
    intro j
    fin_cases j
    · norm_num [st, LRows00.Row2.s]
    · norm_num [st, LRows00.Row3.s]
    · norm_num [st, LRows00.Row4.s]
    · norm_num [st, LRows01.Row5.s]
    · norm_num [st, LMeanPilot.s]
    · norm_num [st, LRows01.Row7.s]
    · norm_num [st, LRows01.Row8.s]
    · norm_num [st, LRows01.Row9.s]
    · norm_num [st, LRows01.Row10.s]
    · norm_num [st, LRows02.Row11.s]
    · norm_num [st, LRows02.Row12.s]
    · norm_num [st, LRows02.Row13.s]
    · norm_num [st, LRows02.Row14.s]
    · norm_num [st, LRows02.Row15.s]
    · norm_num [st, LRows03.Row16.s]
    · norm_num [st, LRows03.Row17.s]
    · norm_num [st, LRows03.Row18.s]
    · norm_num [st, LRows03.Row19.s]
    · norm_num [st, LRows03.Row20.s]
    · norm_num [st, LRows04.Row21.s]
    · norm_num [st, LRows04.Row22.s]
    · norm_num [st, LRows04.Row23.s]
    · norm_num [st, LRows04.Row24.s]
    · norm_num [st, LRows04.Row25.s]
  hsT := by
    intro j
    fin_cases j
    · exact LControl72.actualStatS0
    · exact LControl72.actualStatS1
    · exact LControl72.actualStatS2
    · exact LControl72.actualStatS3
    · exact LControl72.actualStatS4
    · exact LControl72.actualStatS5
    · exact LControl72.actualStatS6
    · exact LControl72.actualStatS7
    · exact LControl72.actualStatS8
    · exact LControl72.actualStatS9
    · exact LControl72.actualStatS10
    · exact LControl72.actualStatS11
    · exact LControl72.actualStatS12
    · exact LControl72.actualStatS13
    · exact LControl72.actualStatS14
    · exact LControl72.actualStatS15
    · exact LControl72.actualStatS16
    · exact LControl72.actualStatS17
    · exact LControl72.actualStatS18
    · exact LControl72.actualStatS19
    · exact LControl72.actualStatS20
    · exact LControl72.actualStatS21
    · exact LControl72.actualStatS22
    · exact LControl72.actualStatS23
  hPt := by
    intro j y hy _
    rw [tgR_eq]
    fin_cases j
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS0 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS1 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS2 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS3 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS4 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS5 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS6 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS7 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS8 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS9 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS10 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS11 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS12 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS13 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS14 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS15 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS16 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS17 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS18 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS19 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS20 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS21 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS22 hy
    · simpa only [show (39/2048 : ℝ)/(13/128) = 3/16 by norm_num] using LControl72.actualS23 hy
  hmarg := by
    intro j α hα
    have hα0 : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ) := by simpa [hα1] using hα
    have hE : 2*(dc72.g0 : ℝ)/dc72.n0 + 1/20 = ((13/60 : ℚ) : ℝ) := by norm_num [dc72]
    rw [hE]
    fin_cases j
    · exact LControl72.actualMarginS0 hα0
    · exact LControl72.actualMarginS1 hα0
    · exact LControl72.actualMarginS2 hα0
    · exact LControl72.actualMarginS3 hα0
    · exact LControl72.actualMarginS4 hα0
    · exact LControl72.actualMarginS5 hα0
    · exact LControl72.actualMarginS6 hα0
    · exact LControl72.actualMarginS7 hα0
    · exact LControl72.actualMarginS8 hα0
    · exact LControl72.actualMarginS9 hα0
    · exact LControl72.actualMarginS10 hα0
    · exact LControl72.actualMarginS11 hα0
    · exact LControl72.actualMarginS12 hα0
    · exact LControl72.actualMarginS13 hα0
    · exact LControl72.actualMarginS14 hα0
    · exact LControl72.actualMarginS15 hα0
    · exact LControl72.actualMarginS16 hα0
    · exact LControl72.actualMarginS17 hα0
    · exact LControl72.actualMarginS18 hα0
    · exact LControl72.actualMarginS19 hα0
    · exact LControl72.actualMarginS20 hα0
    · exact LControl72.actualMarginS21 hα0
    · exact LControl72.actualMarginS22 hα0
    · exact LControl72.actualMarginS23 hα0
  θ0 := 1/1000
  dsp := 17/100
  hθ0 := by norm_num
  hdsp := by norm_num
  hθcut := by norm_num [dc72]
  hxcθ := hxc
  hxcnn := hxc0
  hC1nn := hC1
  hsup := hsup

end
end CatalanMeasure.GenD.Signed.Data.Trial72.LinkData72

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LinkData72.data

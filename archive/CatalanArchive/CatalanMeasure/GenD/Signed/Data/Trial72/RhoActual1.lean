module
public import CatalanMeasure.GenD.Signed.Data.Trial72.RhoGlobal72
public import CatalanMeasure.GenD.Signed.Data.Trial72.RhoQAliases72
public import CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RhoActual1
open Set CatalanMeasure.Signed CatalanMeasure.Signed.Consts
open RhoGlobal72
noncomputable section

theorem row00 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 0 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A00.ap : ℝ)*(2+CostRootData.A00.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A00.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 0 0 : ℝ) = (639/2500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 0 0 = (639/2500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A00.rho_bounds.1
  simp only [CostRootData.A00.rhoLo, CostRootData.A00.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A00.ap : ℝ)*(2+CostRootData.A00.ap)) ≤ (CostRootData.A00.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (639/2500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A00.sqrtHi : ℝ) = u1_0 := by
    norm_num [sr1, CostRootData.A00.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_0]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_0 h2
  rw [actual1] at hb
  have ha : ap0 = (CostRootData.A00.ap : ℝ) := by
    norm_num [ap0, CostRootData.A00.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row01 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 1 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A01.ap : ℝ)*(2+CostRootData.A01.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A01.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 1 0 : ℝ) = (3337/12500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 1 0 = (3337/12500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A01.rho_bounds.1
  simp only [CostRootData.A01.rhoLo, CostRootData.A01.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A01.ap : ℝ)*(2+CostRootData.A01.ap)) ≤ (CostRootData.A01.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (3337/12500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A01.sqrtHi : ℝ) = u1_1 := by
    norm_num [sr1, CostRootData.A01.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_1]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_1 h2
  rw [actual1] at hb
  have ha : ap1 = (CostRootData.A01.ap : ℝ) := by
    norm_num [ap1, CostRootData.A01.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row02 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 2 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A02.ap : ℝ)*(2+CostRootData.A02.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A02.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 2 0 : ℝ) = (71/250 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 2 0 = (71/250 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A02.rho_bounds.1
  simp only [CostRootData.A02.rhoLo, CostRootData.A02.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A02.ap : ℝ)*(2+CostRootData.A02.ap)) ≤ (CostRootData.A02.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (71/250 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A02.sqrtHi : ℝ) = u1_2 := by
    norm_num [sr1, CostRootData.A02.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_2]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_2 h2
  rw [actual1] at hb
  have ha : ap2 = (CostRootData.A02.ap : ℝ) := by
    norm_num [ap2, CostRootData.A02.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row03 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 3 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A03.ap : ℝ)*(2+CostRootData.A03.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A03.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 3 0 : ℝ) = (3763/12500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 3 0 = (3763/12500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A03.rho_bounds.1
  simp only [CostRootData.A03.rhoLo, CostRootData.A03.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A03.ap : ℝ)*(2+CostRootData.A03.ap)) ≤ (CostRootData.A03.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (3763/12500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A03.sqrtHi : ℝ) = u1_3 := by
    norm_num [sr1, CostRootData.A03.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_3]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_3 h2
  rw [actual1] at hb
  have ha : ap3 = (CostRootData.A03.ap : ℝ) := by
    norm_num [ap3, CostRootData.A03.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row04 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 4 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A04.ap : ℝ)*(2+CostRootData.A04.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A04.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 4 0 : ℝ) = (4047/12500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 4 0 = (4047/12500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A04.rho_bounds.1
  simp only [CostRootData.A04.rhoLo, CostRootData.A04.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A04.ap : ℝ)*(2+CostRootData.A04.ap)) ≤ (CostRootData.A04.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (4047/12500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A04.sqrtHi : ℝ) = u1_4 := by
    norm_num [sr1, CostRootData.A04.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_4]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_4 h2
  rw [actual1] at hb
  have ha : ap4 = (CostRootData.A04.ap : ℝ) := by
    norm_num [ap4, CostRootData.A04.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row05 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 5 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A05.ap : ℝ)*(2+CostRootData.A05.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A05.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 5 0 : ℝ) = (213/625 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 5 0 = (213/625 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A05.rho_bounds.1
  simp only [CostRootData.A05.rhoLo, CostRootData.A05.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A05.ap : ℝ)*(2+CostRootData.A05.ap)) ≤ (CostRootData.A05.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (213/625 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A05.sqrtHi : ℝ) = u1_5 := by
    norm_num [sr1, CostRootData.A05.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_5]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_5 h2
  rw [actual1] at hb
  have ha : ap5 = (CostRootData.A05.ap : ℝ) := by
    norm_num [ap5, CostRootData.A05.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row06 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 6 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A06.ap : ℝ)*(2+CostRootData.A06.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A06.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 6 0 : ℝ) = (1136/3125 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 6 0 = (1136/3125 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A06.rho_bounds.1
  simp only [CostRootData.A06.rhoLo, CostRootData.A06.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A06.ap : ℝ)*(2+CostRootData.A06.ap)) ≤ (CostRootData.A06.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (1136/3125 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A06.sqrtHi : ℝ) = u1_6 := by
    norm_num [sr1, CostRootData.A06.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_6]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_6 h2
  rw [actual1] at hb
  have ha : ap6 = (CostRootData.A06.ap : ℝ) := by
    norm_num [ap6, CostRootData.A06.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row07 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 7 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A07.ap : ℝ)*(2+CostRootData.A07.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A07.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 7 0 : ℝ) = (1207/3125 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 7 0 = (1207/3125 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A07.rho_bounds.1
  simp only [CostRootData.A07.rhoLo, CostRootData.A07.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A07.ap : ℝ)*(2+CostRootData.A07.ap)) ≤ (CostRootData.A07.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (1207/3125 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A07.sqrtHi : ℝ) = u1_7 := by
    norm_num [sr1, CostRootData.A07.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_7]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_7 h2
  rw [actual1] at hb
  have ha : ap7 = (CostRootData.A07.ap : ℝ) := by
    norm_num [ap7, CostRootData.A07.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row08 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 8 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A08.ap : ℝ)*(2+CostRootData.A08.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A08.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 8 0 : ℝ) = (1278/3125 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 8 0 = (1278/3125 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A08.rho_bounds.1
  simp only [CostRootData.A08.rhoLo, CostRootData.A08.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A08.ap : ℝ)*(2+CostRootData.A08.ap)) ≤ (CostRootData.A08.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (1278/3125 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A08.sqrtHi : ℝ) = u1_8 := by
    norm_num [sr1, CostRootData.A08.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_8]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_8 h2
  rw [actual1] at hb
  have ha : ap8 = (CostRootData.A08.ap : ℝ) := by
    norm_num [ap8, CostRootData.A08.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row09 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 9 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A09.ap : ℝ)*(2+CostRootData.A09.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A09.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 9 0 : ℝ) = (1349/3125 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 9 0 = (1349/3125 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A09.rho_bounds.1
  simp only [CostRootData.A09.rhoLo, CostRootData.A09.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A09.ap : ℝ)*(2+CostRootData.A09.ap)) ≤ (CostRootData.A09.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (1349/3125 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A09.sqrtHi : ℝ) = u1_9 := by
    norm_num [sr1, CostRootData.A09.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_9]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_9 h2
  rw [actual1] at hb
  have ha : ap9 = (CostRootData.A09.ap : ℝ) := by
    norm_num [ap9, CostRootData.A09.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row10 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 10 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A10.ap : ℝ)*(2+CostRootData.A10.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A10.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 10 0 : ℝ) = (5751/12500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 10 0 = (5751/12500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A10.rho_bounds.1
  simp only [CostRootData.A10.rhoLo, CostRootData.A10.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A10.ap : ℝ)*(2+CostRootData.A10.ap)) ≤ (CostRootData.A10.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (5751/12500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A10.sqrtHi : ℝ) = u1_10 := by
    norm_num [sr1, CostRootData.A10.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_10]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_10 h2
  rw [actual1] at hb
  have ha : ap10 = (CostRootData.A10.ap : ℝ) := by
    norm_num [ap10, CostRootData.A10.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row11 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 11 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A11.ap : ℝ)*(2+CostRootData.A11.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A11.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 11 0 : ℝ) = (3053/6250 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 11 0 = (3053/6250 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A11.rho_bounds.1
  simp only [CostRootData.A11.rhoLo, CostRootData.A11.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A11.ap : ℝ)*(2+CostRootData.A11.ap)) ≤ (CostRootData.A11.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (3053/6250 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A11.sqrtHi : ℝ) = u1_11 := by
    norm_num [sr1, CostRootData.A11.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_11]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_11 h2
  rw [actual1] at hb
  have ha : ap11 = (CostRootData.A11.ap : ℝ) := by
    norm_num [ap11, CostRootData.A11.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row12 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 12 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A12.ap : ℝ)*(2+CostRootData.A12.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A12.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 12 0 : ℝ) = (6461/12500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 12 0 = (6461/12500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A12.rho_bounds.1
  simp only [CostRootData.A12.rhoLo, CostRootData.A12.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A12.ap : ℝ)*(2+CostRootData.A12.ap)) ≤ (CostRootData.A12.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (6461/12500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A12.sqrtHi : ℝ) = u1_12 := by
    norm_num [sr1, CostRootData.A12.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_12]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_12 h2
  rw [actual1] at hb
  have ha : ap12 = (CostRootData.A12.ap : ℝ) := by
    norm_num [ap12, CostRootData.A12.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row13 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 13 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A13.ap : ℝ)*(2+CostRootData.A13.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A13.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 13 0 : ℝ) = (6887/12500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 13 0 = (6887/12500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A13.rho_bounds.1
  simp only [CostRootData.A13.rhoLo, CostRootData.A13.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A13.ap : ℝ)*(2+CostRootData.A13.ap)) ≤ (CostRootData.A13.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (6887/12500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A13.sqrtHi : ℝ) = u1_13 := by
    norm_num [sr1, CostRootData.A13.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_13]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_13 h2
  rw [actual1] at hb
  have ha : ap13 = (CostRootData.A13.ap : ℝ) := by
    norm_num [ap13, CostRootData.A13.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row14 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 14 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A14.ap : ℝ)*(2+CostRootData.A14.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A14.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 14 0 : ℝ) = (7313/12500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 14 0 = (7313/12500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A14.rho_bounds.1
  simp only [CostRootData.A14.rhoLo, CostRootData.A14.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A14.ap : ℝ)*(2+CostRootData.A14.ap)) ≤ (CostRootData.A14.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (7313/12500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A14.sqrtHi : ℝ) = u1_14 := by
    norm_num [sr1, CostRootData.A14.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_14]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_14 h2
  rw [actual1] at hb
  have ha : ap14 = (CostRootData.A14.ap : ℝ) := by
    norm_num [ap14, CostRootData.A14.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row15 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 15 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A15.ap : ℝ)*(2+CostRootData.A15.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A15.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 15 0 : ℝ) = (7739/12500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 15 0 = (7739/12500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A15.rho_bounds.1
  simp only [CostRootData.A15.rhoLo, CostRootData.A15.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A15.ap : ℝ)*(2+CostRootData.A15.ap)) ≤ (CostRootData.A15.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (7739/12500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A15.sqrtHi : ℝ) = u1_15 := by
    norm_num [sr1, CostRootData.A15.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_15]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_15 h2
  rw [actual1] at hb
  have ha : ap15 = (CostRootData.A15.ap : ℝ) := by
    norm_num [ap15, CostRootData.A15.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row16 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 16 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A16.ap : ℝ)*(2+CostRootData.A16.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A16.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 16 0 : ℝ) = (1633/2500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 16 0 = (1633/2500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A16.rho_bounds.1
  simp only [CostRootData.A16.rhoLo, CostRootData.A16.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A16.ap : ℝ)*(2+CostRootData.A16.ap)) ≤ (CostRootData.A16.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (1633/2500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A16.sqrtHi : ℝ) = u1_16 := by
    norm_num [sr1, CostRootData.A16.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_16]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_16 h2
  rw [actual1] at hb
  have ha : ap16 = (CostRootData.A16.ap : ℝ) := by
    norm_num [ap16, CostRootData.A16.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row17 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 17 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A17.ap : ℝ)*(2+CostRootData.A17.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A17.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 17 0 : ℝ) = (8733/12500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 17 0 = (8733/12500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A17.rho_bounds.1
  simp only [CostRootData.A17.rhoLo, CostRootData.A17.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A17.ap : ℝ)*(2+CostRootData.A17.ap)) ≤ (CostRootData.A17.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (8733/12500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A17.sqrtHi : ℝ) = u1_17 := by
    norm_num [sr1, CostRootData.A17.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_17]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_17 h2
  rw [actual1] at hb
  have ha : ap17 = (CostRootData.A17.ap : ℝ) := by
    norm_num [ap17, CostRootData.A17.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row18 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 18 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A18.ap : ℝ)*(2+CostRootData.A18.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A18.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 18 0 : ℝ) = (923/1250 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 18 0 = (923/1250 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A18.rho_bounds.1
  simp only [CostRootData.A18.rhoLo, CostRootData.A18.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A18.ap : ℝ)*(2+CostRootData.A18.ap)) ≤ (CostRootData.A18.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (923/1250 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A18.sqrtHi : ℝ) = u1_18 := by
    norm_num [sr1, CostRootData.A18.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_18]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_18 h2
  rw [actual1] at hb
  have ha : ap18 = (CostRootData.A18.ap : ℝ) := by
    norm_num [ap18, CostRootData.A18.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row19 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 19 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A19.ap : ℝ)*(2+CostRootData.A19.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A19.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 19 0 : ℝ) = (4899/6250 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 19 0 = (4899/6250 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A19.rho_bounds.1
  simp only [CostRootData.A19.rhoLo, CostRootData.A19.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A19.ap : ℝ)*(2+CostRootData.A19.ap)) ≤ (CostRootData.A19.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (4899/6250 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A19.sqrtHi : ℝ) = u1_19 := by
    norm_num [sr1, CostRootData.A19.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_19]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_19 h2
  rw [actual1] at hb
  have ha : ap19 = (CostRootData.A19.ap : ℝ) := by
    norm_num [ap19, CostRootData.A19.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row20 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 20 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A20.ap : ℝ)*(2+CostRootData.A20.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A20.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 20 0 : ℝ) = (5183/6250 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 20 0 = (5183/6250 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A20.rho_bounds.1
  simp only [CostRootData.A20.rhoLo, CostRootData.A20.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A20.ap : ℝ)*(2+CostRootData.A20.ap)) ≤ (CostRootData.A20.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (5183/6250 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A20.sqrtHi : ℝ) = u1_20 := by
    norm_num [sr1, CostRootData.A20.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_20]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_20 h2
  rw [actual1] at hb
  have ha : ap20 = (CostRootData.A20.ap : ℝ) := by
    norm_num [ap20, CostRootData.A20.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row21 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 21 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A21.ap : ℝ)*(2+CostRootData.A21.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A21.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 21 0 : ℝ) = (2201/2500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 21 0 = (2201/2500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A21.rho_bounds.1
  simp only [CostRootData.A21.rhoLo, CostRootData.A21.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A21.ap : ℝ)*(2+CostRootData.A21.ap)) ≤ (CostRootData.A21.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (2201/2500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A21.sqrtHi : ℝ) = u1_21 := by
    norm_num [sr1, CostRootData.A21.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_21]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_21 h2
  rw [actual1] at hb
  have ha : ap21 = (CostRootData.A21.ap : ℝ) := by
    norm_num [ap21, CostRootData.A21.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row22 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 22 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A22.ap : ℝ)*(2+CostRootData.A22.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A22.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 22 0 : ℝ) = (2343/2500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 22 0 = (2343/2500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A22.rho_bounds.1
  simp only [CostRootData.A22.rhoLo, CostRootData.A22.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A22.ap : ℝ)*(2+CostRootData.A22.ap)) ≤ (CostRootData.A22.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (2343/2500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A22.sqrtHi : ℝ) = u1_22 := by
    norm_num [sr1, CostRootData.A22.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_22]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_22 h2
  rw [actual1] at hb
  have ha : ap22 = (CostRootData.A22.ap : ℝ) := by
    norm_num [ap22, CostRootData.A22.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row23 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 23 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A23.ap : ℝ)*(2+CostRootData.A23.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A23.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 23 0 : ℝ) = (497/500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 23 0 = (497/500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A23.rho_bounds.1
  simp only [CostRootData.A23.rhoLo, CostRootData.A23.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A23.ap : ℝ)*(2+CostRootData.A23.ap)) ≤ (CostRootData.A23.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (497/500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A23.sqrtHi : ℝ) = u1_23 := by
    norm_num [sr1, CostRootData.A23.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_23]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_23 h2
  rw [actual1] at hb
  have ha : ap23 = (CostRootData.A23.ap : ℝ) := by
    norm_num [ap23, CostRootData.A23.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row24 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 24 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A24.ap : ℝ)*(2+CostRootData.A24.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A24.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 24 0 : ℝ) = (2627/2500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 24 0 = (2627/2500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A24.rho_bounds.1
  simp only [CostRootData.A24.rhoLo, CostRootData.A24.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A24.ap : ℝ)*(2+CostRootData.A24.ap)) ≤ (CostRootData.A24.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (2627/2500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A24.sqrtHi : ℝ) = u1_24 := by
    norm_num [sr1, CostRootData.A24.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_24]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_24 h2
  rw [actual1] at hb
  have ha : ap24 = (CostRootData.A24.ap : ℝ) := by
    norm_num [ap24, CostRootData.A24.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row25 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 25 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A25.ap : ℝ)*(2+CostRootData.A25.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A25.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 25 0 : ℝ) = (13987/12500 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 25 0 = (13987/12500 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A25.rho_bounds.1
  simp only [CostRootData.A25.rhoLo, CostRootData.A25.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A25.ap : ℝ)*(2+CostRootData.A25.ap)) ≤ (CostRootData.A25.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (13987/12500 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A25.sqrtHi : ℝ) = u1_25 := by
    norm_num [sr1, CostRootData.A25.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_25]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_25 h2
  rw [actual1] at hb
  have ha : ap25 = (CostRootData.A25.ap : ℝ) := by
    norm_num [ap25, CostRootData.A25.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

theorem row26 {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD 26 0 : ℝ)) :
    q/(2*(17/20)*sr1) * Real.sqrt ((CostRootData.A26.ap : ℝ)*(2+CostRootData.A26.ap)) ≤
      chebPs (bSeq SpikeChebInteger1.bs) u * (1+(CostRootData.A26.ap : ℝ)+u) := by
  have he : (RhoQAliases72.qmax.getD 26 0 : ℝ) = (142/125 : ℝ) := by
    exact_mod_cast (show RhoQAliases72.qmax.getD 26 0 = (142/125 : ℚ) by decide +kernel)
  have hq' := hQ
  rw [he] at hq'
  have hs := CostRootData.A26.rho_bounds.1
  simp only [CostRootData.A26.rhoLo, CostRootData.A26.rho, Rat.cast_sub, Rat.cast_add, Rat.cast_one] at hs
  have hs' : Real.sqrt ((CostRootData.A26.ap : ℝ)*(2+CostRootData.A26.ap)) ≤ (CostRootData.A26.sqrtHi : ℝ) := by linarith only [hs]
  have hw := RhoQAliases72.weighted_alias hq hq' (Real.sqrt_nonneg _) hs' sr1_pos
  have hU : (142/125 : ℝ)/(2*(17/20)*sr1)*(CostRootData.A26.sqrtHi : ℝ) = u1_26 := by
    norm_num [sr1, CostRootData.A26.sqrtHi, CostHornerPilot.sqrtHi, qlist, u1_26]
  rw [hU] at hw
  have h2 : 2*u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := bound1_26 h2
  rw [actual1] at hb
  have ha : ap26 = (CostRootData.A26.ap : ℝ) := by
    norm_num [ap26, CostRootData.A26.ap, CostHornerPilot.ap, qlist]
  rw [ha, show 2*u/2 = u by ring] at hb
  exact hw.trans hb

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RhoActual1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoActual1.row00
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoActual1.row26

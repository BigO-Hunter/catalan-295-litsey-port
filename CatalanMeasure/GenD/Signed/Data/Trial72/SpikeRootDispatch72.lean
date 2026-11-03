module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeEndpoint72
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeDe0
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeDe1
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeDe2
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeRootDispatch72
open Set CatalanMeasure.Signed CatalanMeasure.Signed.Consts SpikeEndpoint72 RhoGlobal72
noncomputable section

def ap (a : Fin 27) : ℚ := [CostRootData.A00.ap, CostRootData.A01.ap, CostRootData.A02.ap, CostRootData.A03.ap, CostRootData.A04.ap, CostRootData.A05.ap, CostRootData.A06.ap, CostRootData.A07.ap, CostRootData.A08.ap, CostRootData.A09.ap, CostRootData.A10.ap, CostRootData.A11.ap, CostRootData.A12.ap, CostRootData.A13.ap, CostRootData.A14.ap, CostRootData.A15.ap, CostRootData.A16.ap, CostRootData.A17.ap, CostRootData.A18.ap, CostRootData.A19.ap, CostRootData.A20.ap, CostRootData.A21.ap, CostRootData.A22.ap, CostRootData.A23.ap, CostRootData.A24.ap, CostRootData.A25.ap, CostRootData.A26.ap].getD a.val 0

theorem ap_pos_q : ∀ a : Fin 27, 0 < ap a := by decide +kernel
theorem ap_pos (a : Fin 27) : (0 : ℝ) < (ap a : ℝ) := by exact_mod_cast ap_pos_q a

theorem rhoLo (a : Fin 27) : 0 ≤ rho (ap a) := by
  fin_cases a

  · exact (show (0 : ℝ) ≤ (CostRootData.A00.rhoLo : ℝ) by exact_mod_cast CostRootData.A00.rhoLo_nonneg).trans CostRootData.A00.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A01.rhoLo : ℝ) by exact_mod_cast CostRootData.A01.rhoLo_nonneg).trans CostRootData.A01.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A02.rhoLo : ℝ) by exact_mod_cast CostRootData.A02.rhoLo_nonneg).trans CostRootData.A02.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A03.rhoLo : ℝ) by exact_mod_cast CostRootData.A03.rhoLo_nonneg).trans CostRootData.A03.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A04.rhoLo : ℝ) by exact_mod_cast CostRootData.A04.rhoLo_nonneg).trans CostRootData.A04.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A05.rhoLo : ℝ) by exact_mod_cast CostRootData.A05.rhoLo_nonneg).trans CostRootData.A05.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A06.rhoLo : ℝ) by exact_mod_cast CostRootData.A06.rhoLo_nonneg).trans CostRootData.A06.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A07.rhoLo : ℝ) by exact_mod_cast CostRootData.A07.rhoLo_nonneg).trans CostRootData.A07.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A08.rhoLo : ℝ) by exact_mod_cast CostRootData.A08.rhoLo_nonneg).trans CostRootData.A08.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A09.rhoLo : ℝ) by exact_mod_cast CostRootData.A09.rhoLo_nonneg).trans CostRootData.A09.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A10.rhoLo : ℝ) by exact_mod_cast CostRootData.A10.rhoLo_nonneg).trans CostRootData.A10.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A11.rhoLo : ℝ) by exact_mod_cast CostRootData.A11.rhoLo_nonneg).trans CostRootData.A11.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A12.rhoLo : ℝ) by exact_mod_cast CostRootData.A12.rhoLo_nonneg).trans CostRootData.A12.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A13.rhoLo : ℝ) by exact_mod_cast CostRootData.A13.rhoLo_nonneg).trans CostRootData.A13.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A14.rhoLo : ℝ) by exact_mod_cast CostRootData.A14.rhoLo_nonneg).trans CostRootData.A14.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A15.rhoLo : ℝ) by exact_mod_cast CostRootData.A15.rhoLo_nonneg).trans CostRootData.A15.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A16.rhoLo : ℝ) by exact_mod_cast CostRootData.A16.rhoLo_nonneg).trans CostRootData.A16.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A17.rhoLo : ℝ) by exact_mod_cast CostRootData.A17.rhoLo_nonneg).trans CostRootData.A17.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A18.rhoLo : ℝ) by exact_mod_cast CostRootData.A18.rhoLo_nonneg).trans CostRootData.A18.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A19.rhoLo : ℝ) by exact_mod_cast CostRootData.A19.rhoLo_nonneg).trans CostRootData.A19.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A20.rhoLo : ℝ) by exact_mod_cast CostRootData.A20.rhoLo_nonneg).trans CostRootData.A20.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A21.rhoLo : ℝ) by exact_mod_cast CostRootData.A21.rhoLo_nonneg).trans CostRootData.A21.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A22.rhoLo : ℝ) by exact_mod_cast CostRootData.A22.rhoLo_nonneg).trans CostRootData.A22.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A23.rhoLo : ℝ) by exact_mod_cast CostRootData.A23.rhoLo_nonneg).trans CostRootData.A23.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A24.rhoLo : ℝ) by exact_mod_cast CostRootData.A24.rhoLo_nonneg).trans CostRootData.A24.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A25.rhoLo : ℝ) by exact_mod_cast CostRootData.A25.rhoLo_nonneg).trans CostRootData.A25.rho_bounds.1

  · exact (show (0 : ℝ) ≤ (CostRootData.A26.rhoLo : ℝ) by exact_mod_cast CostRootData.A26.rhoLo_nonneg).trans CostRootData.A26.rho_bounds.1

theorem rhoHi (a : Fin 27) : rho (ap a) ≤ (SpikeLinear72.rhoHi.getD a.val 0 : ℝ) := by
  fin_cases a

  · exact CostRootData.A00.rho_bounds.2

  · exact CostRootData.A01.rho_bounds.2

  · exact CostRootData.A02.rho_bounds.2

  · exact CostRootData.A03.rho_bounds.2

  · exact CostRootData.A04.rho_bounds.2

  · exact CostRootData.A05.rho_bounds.2

  · exact CostRootData.A06.rho_bounds.2

  · exact CostRootData.A07.rho_bounds.2

  · exact CostRootData.A08.rho_bounds.2

  · exact CostRootData.A09.rho_bounds.2

  · exact CostRootData.A10.rho_bounds.2

  · exact CostRootData.A11.rho_bounds.2

  · exact CostRootData.A12.rho_bounds.2

  · exact CostRootData.A13.rho_bounds.2

  · exact CostRootData.A14.rho_bounds.2

  · exact CostRootData.A15.rho_bounds.2

  · exact CostRootData.A16.rho_bounds.2

  · exact CostRootData.A17.rho_bounds.2

  · exact CostRootData.A18.rho_bounds.2

  · exact CostRootData.A19.rho_bounds.2

  · exact CostRootData.A20.rho_bounds.2

  · exact CostRootData.A21.rho_bounds.2

  · exact CostRootData.A22.rho_bounds.2

  · exact CostRootData.A23.rho_bounds.2

  · exact CostRootData.A24.rho_bounds.2

  · exact CostRootData.A25.rho_bounds.2

  · exact CostRootData.A26.rho_bounds.2


theorem root (a : Fin 27) : rho (ap a) ∈ Icc (0 : ℝ) (999001/1000000) :=
  ⟨rhoLo a,(rhoHi a).trans (by exact_mod_cast SpikeLinear72.root_bound a)⟩

def qlo (i : Fin 200) : ℝ := 71*(i.val : ℝ)/12500

theorem gain_nonpos (i : Fin 200) : (SpikeLinear72.sg i : ℝ) ≤ 0 := by
  unfold SpikeLinear72.sg
  split_ifs <;> norm_num

theorem gain (i : Fin 200) (a : Fin 27) (ha : a.val = RhoQAliases72.indices.getD i.val 0)
    (τ : ℝ) (hτ : τ ∈ Icc (1-1/1073741824 : ℝ) 1) :
    Real.log (1-τ^2*(1-1/1024)^2)-Real.log (1-(rho (ap a))^2) ≤ (SpikeLinear72.sg i : ℝ) := by
  unfold SpikeLinear72.sg
  split_ifs with h
  · have hr := SpikeLinear72.root_high i h
    rw [← ha] at hr
    have hh : rho (ap a) ≤ (499/500 : ℝ) := (rhoHi a).trans (by exact_mod_cast hr)
    simpa using SpikeLinear72.sg_high hτ ⟨rhoLo a,hh⟩
  · simpa using (SpikeLinear72.root_geometry hτ (root a)).2.2

theorem weighted (a : Fin 27) {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : 0 ≤ q)
    (hQ : q ≤ (RhoQAliases72.qmax.getD a.val 0 : ℝ)) :
    q/2*Real.sqrt ((ap a : ℝ)*(2+ap a)) ≤ (sr2*P2 (2*u)-SpikeWorstGlobal72.shift)*(1+ap a+u) := by
  fin_cases a

  · exact SpikeWorstGlobal72.bound00 hu hq hQ

  · exact SpikeWorstGlobal72.bound01 hu hq hQ

  · exact SpikeWorstGlobal72.bound02 hu hq hQ

  · exact SpikeWorstGlobal72.bound03 hu hq hQ

  · exact SpikeWorstGlobal72.bound04 hu hq hQ

  · exact SpikeWorstGlobal72.bound05 hu hq hQ

  · exact SpikeWorstGlobal72.bound06 hu hq hQ

  · exact SpikeWorstGlobal72.bound07 hu hq hQ

  · exact SpikeWorstGlobal72.bound08 hu hq hQ

  · exact SpikeWorstGlobal72.bound09 hu hq hQ

  · exact SpikeWorstGlobal72.bound10 hu hq hQ

  · exact SpikeWorstGlobal72.bound11 hu hq hQ

  · exact SpikeWorstGlobal72.bound12 hu hq hQ

  · exact SpikeWorstGlobal72.bound13 hu hq hQ

  · exact SpikeWorstGlobal72.bound14 hu hq hQ

  · exact SpikeWorstGlobal72.bound15 hu hq hQ

  · exact SpikeWorstGlobal72.bound16 hu hq hQ

  · exact SpikeWorstGlobal72.bound17 hu hq hQ

  · exact SpikeWorstGlobal72.bound18 hu hq hQ

  · exact SpikeWorstGlobal72.bound19 hu hq hQ

  · exact SpikeWorstGlobal72.bound20 hu hq hQ

  · exact SpikeWorstGlobal72.bound21 hu hq hQ

  · exact SpikeWorstGlobal72.bound22 hu hq hQ

  · exact SpikeWorstGlobal72.bound23 hu hq hQ

  · exact SpikeWorstGlobal72.bound24 hu hq hQ

  · exact SpikeWorstGlobal72.bound25 hu hq hQ

  · exact SpikeWorstGlobal72.bound26 hu hq hQ


def de0 (a : Fin 27) : ℝ := (max 0 (SpikeCostScalars0.deUpper.getD a.val 0) : ℚ)

theorem jump0 (a : Fin 27) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq SpikeDe0.bs) (-y)-barrierTrialS (bSeq SpikeDe0.bs) (-(rho (ap a)))) ≤ de0 a := by
  have h : (SpikeCostScalars0.deUpper.getD a.val 0 : ℝ) ≤ de0 a := by
    exact_mod_cast (le_max_right 0 (SpikeCostScalars0.deUpper.getD a.val 0))
  apply le_trans _ h
  fin_cases a

  · exact SpikeDe0.row00 hy

  · exact SpikeDe0.row01 hy

  · exact SpikeDe0.row02 hy

  · exact SpikeDe0.row03 hy

  · exact SpikeDe0.row04 hy

  · exact SpikeDe0.row05 hy

  · exact SpikeDe0.row06 hy

  · exact SpikeDe0.row07 hy

  · exact SpikeDe0.row08 hy

  · exact SpikeDe0.row09 hy

  · exact SpikeDe0.row10 hy

  · exact SpikeDe0.row11 hy

  · exact SpikeDe0.row12 hy

  · exact SpikeDe0.row13 hy

  · exact SpikeDe0.row14 hy

  · exact SpikeDe0.row15 hy

  · exact SpikeDe0.row16 hy

  · exact SpikeDe0.row17 hy

  · exact SpikeDe0.row18 hy

  · exact SpikeDe0.row19 hy

  · exact SpikeDe0.row20 hy

  · exact SpikeDe0.row21 hy

  · exact SpikeDe0.row22 hy

  · exact SpikeDe0.row23 hy

  · exact SpikeDe0.row24 hy

  · exact SpikeDe0.row25 hy

  · exact SpikeDe0.row26 hy


def de1 (a : Fin 27) : ℝ := (max 0 (SpikeCostScalars1.deUpper.getD a.val 0) : ℚ)

theorem jump1 (a : Fin 27) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq SpikeDe1.bs) (-y)-barrierTrialS (bSeq SpikeDe1.bs) (-(rho (ap a)))) ≤ de1 a := by
  have h : (SpikeCostScalars1.deUpper.getD a.val 0 : ℝ) ≤ de1 a := by
    exact_mod_cast (le_max_right 0 (SpikeCostScalars1.deUpper.getD a.val 0))
  apply le_trans _ h
  fin_cases a

  · exact SpikeDe1.row00 hy

  · exact SpikeDe1.row01 hy

  · exact SpikeDe1.row02 hy

  · exact SpikeDe1.row03 hy

  · exact SpikeDe1.row04 hy

  · exact SpikeDe1.row05 hy

  · exact SpikeDe1.row06 hy

  · exact SpikeDe1.row07 hy

  · exact SpikeDe1.row08 hy

  · exact SpikeDe1.row09 hy

  · exact SpikeDe1.row10 hy

  · exact SpikeDe1.row11 hy

  · exact SpikeDe1.row12 hy

  · exact SpikeDe1.row13 hy

  · exact SpikeDe1.row14 hy

  · exact SpikeDe1.row15 hy

  · exact SpikeDe1.row16 hy

  · exact SpikeDe1.row17 hy

  · exact SpikeDe1.row18 hy

  · exact SpikeDe1.row19 hy

  · exact SpikeDe1.row20 hy

  · exact SpikeDe1.row21 hy

  · exact SpikeDe1.row22 hy

  · exact SpikeDe1.row23 hy

  · exact SpikeDe1.row24 hy

  · exact SpikeDe1.row25 hy

  · exact SpikeDe1.row26 hy


def de2 (a : Fin 27) : ℝ := (max 0 (SpikeCostScalars2.deUpper.getD a.val 0) : ℚ)

theorem jump2 (a : Fin 27) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq SpikeDe2.bs) (-y)-barrierTrialS (bSeq SpikeDe2.bs) (-(rho (ap a)))) ≤ de2 a := by
  have h : (SpikeCostScalars2.deUpper.getD a.val 0 : ℝ) ≤ de2 a := by
    exact_mod_cast (le_max_right 0 (SpikeCostScalars2.deUpper.getD a.val 0))
  apply le_trans _ h
  fin_cases a

  · exact SpikeDe2.row00 hy

  · exact SpikeDe2.row01 hy

  · exact SpikeDe2.row02 hy

  · exact SpikeDe2.row03 hy

  · exact SpikeDe2.row04 hy

  · exact SpikeDe2.row05 hy

  · exact SpikeDe2.row06 hy

  · exact SpikeDe2.row07 hy

  · exact SpikeDe2.row08 hy

  · exact SpikeDe2.row09 hy

  · exact SpikeDe2.row10 hy

  · exact SpikeDe2.row11 hy

  · exact SpikeDe2.row12 hy

  · exact SpikeDe2.row13 hy

  · exact SpikeDe2.row14 hy

  · exact SpikeDe2.row15 hy

  · exact SpikeDe2.row16 hy

  · exact SpikeDe2.row17 hy

  · exact SpikeDe2.row18 hy

  · exact SpikeDe2.row19 hy

  · exact SpikeDe2.row20 hy

  · exact SpikeDe2.row21 hy

  · exact SpikeDe2.row22 hy

  · exact SpikeDe2.row23 hy

  · exact SpikeDe2.row24 hy

  · exact SpikeDe2.row25 hy

  · exact SpikeDe2.row26 hy

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeRootDispatch72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeRootDispatch72.weighted

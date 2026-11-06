module
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock00
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock01
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock02
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock03
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock04
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock05
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock06
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock07
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock08
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock09
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock10
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock11
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock12
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock13
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock14
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock15
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock16
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock17
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock18
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock19
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock20
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock21
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock22
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock23
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock24
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock25
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock26
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock27
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock28
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock29
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock30
public import CatalanMeasure.GenD.Signed.Davis.S1CompleteBlockStress
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock32
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock33
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock34
public import CatalanMeasure.GenD.Signed.Davis.S1CompleteBlockPilot
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock36
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock37
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock38
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock39
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock40
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock41
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock42
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock43
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock44
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock45
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock46
public import CatalanMeasure.GenD.Signed.Davis.S1CircleBlock47
public import CatalanMeasure.GenD.Analytic.ConjugateCircle
public import CatalanMeasure.GenD.Signed.Davis.Design72Weights
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 10
namespace CatalanMeasure.GenD.Signed.Davis.S1CircleData
open Set Polynomial CatalanMeasure.GenD.Analytic
open S1PolynomialBounds CatalanMeasure.Refinement.Trimmed130
noncomputable section
def positiveIntervals : List (ℚ × ℚ) := [(S1CircleBlock00.blo,S1CircleBlock00.bhi),(S1CircleBlock01.blo,S1CircleBlock01.bhi),(S1CircleBlock02.blo,S1CircleBlock02.bhi),(S1CircleBlock03.blo,S1CircleBlock03.bhi),(S1CircleBlock04.blo,S1CircleBlock04.bhi),(S1CircleBlock05.blo,S1CircleBlock05.bhi),(S1CircleBlock06.blo,S1CircleBlock06.bhi),(S1CircleBlock07.blo,S1CircleBlock07.bhi)]
theorem positiveCover : RationalIntervalCover.coversFrom 0 1 positiveIntervals=true := by
  -- kcost: 0.1 s estimated;8 complete blocks form a contiguous side chart.
  decide +kernel
theorem positiveChart (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    (66 : ℝ)/130*ellipseLog (complexP.eval (rationalCirclePoint (3/5) (1) u))+
      8*Real.log ‖(1 : ℂ)-rationalCirclePoint (3/5) (1) u‖ ≤
        (24330011831893/549755813888 : ℝ) := by
  obtain ⟨iv,hiv,huiv⟩ := RationalIntervalCover.coversFrom_spec positiveCover
    (by norm_num) u (by simpa using hu.1) (by simpa using hu.2)
  simp only [positiveIntervals,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hiv
  rcases hiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact S1CircleBlock00.complete_block u huiv
  · exact S1CircleBlock01.complete_block u huiv
  · exact S1CircleBlock02.complete_block u huiv
  · exact S1CircleBlock03.complete_block u huiv
  · exact S1CircleBlock04.complete_block u huiv
  · exact S1CircleBlock05.complete_block u huiv
  · exact S1CircleBlock06.complete_block u huiv
  · exact S1CircleBlock07.complete_block u huiv
def negativeIntervals : List (ℚ × ℚ) := [(S1CircleBlock08.blo,S1CircleBlock08.bhi),(S1CircleBlock09.blo,S1CircleBlock09.bhi),(S1CircleBlock10.blo,S1CircleBlock10.bhi),(S1CircleBlock11.blo,S1CircleBlock11.bhi),(S1CircleBlock12.blo,S1CircleBlock12.bhi),(S1CircleBlock13.blo,S1CircleBlock13.bhi),(S1CircleBlock14.blo,S1CircleBlock14.bhi),(S1CircleBlock15.blo,S1CircleBlock15.bhi),(S1CircleBlock16.blo,S1CircleBlock16.bhi),(S1CircleBlock17.blo,S1CircleBlock17.bhi),(S1CircleBlock18.blo,S1CircleBlock18.bhi),(S1CircleBlock19.blo,S1CircleBlock19.bhi),(S1CircleBlock20.blo,S1CircleBlock20.bhi),(S1CircleBlock21.blo,S1CircleBlock21.bhi),(S1CircleBlock22.blo,S1CircleBlock22.bhi),(S1CircleBlock23.blo,S1CircleBlock23.bhi),(S1CircleBlock24.blo,S1CircleBlock24.bhi),(S1CircleBlock25.blo,S1CircleBlock25.bhi),(S1CircleBlock26.blo,S1CircleBlock26.bhi),(S1CircleBlock27.blo,S1CircleBlock27.bhi),(S1CircleBlock28.blo,S1CircleBlock28.bhi),(S1CircleBlock29.blo,S1CircleBlock29.bhi),(S1CircleBlock30.blo,S1CircleBlock30.bhi),(S1CompleteBlockStress.blo,S1CompleteBlockStress.bhi),(S1CircleBlock32.blo,S1CircleBlock32.bhi),(S1CircleBlock33.blo,S1CircleBlock33.bhi),(S1CircleBlock34.blo,S1CircleBlock34.bhi),(S1CompleteBlockPilot.blo,S1CompleteBlockPilot.bhi),(S1CircleBlock36.blo,S1CircleBlock36.bhi),(S1CircleBlock37.blo,S1CircleBlock37.bhi),(S1CircleBlock38.blo,S1CircleBlock38.bhi),(S1CircleBlock39.blo,S1CircleBlock39.bhi),(S1CircleBlock40.blo,S1CircleBlock40.bhi),(S1CircleBlock41.blo,S1CircleBlock41.bhi),(S1CircleBlock42.blo,S1CircleBlock42.bhi),(S1CircleBlock43.blo,S1CircleBlock43.bhi),(S1CircleBlock44.blo,S1CircleBlock44.bhi),(S1CircleBlock45.blo,S1CircleBlock45.bhi),(S1CircleBlock46.blo,S1CircleBlock46.bhi),(S1CircleBlock47.blo,S1CircleBlock47.bhi)]
theorem negativeCover : RationalIntervalCover.coversFrom 0 1 negativeIntervals=true := by
  -- kcost: 0.1 s estimated;40 complete blocks form a contiguous side chart.
  decide +kernel
theorem negativeChart (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    (66 : ℝ)/130*ellipseLog (complexP.eval (rationalCirclePoint (3/5) (-1) u))+
      8*Real.log ‖(1 : ℂ)-rationalCirclePoint (3/5) (-1) u‖ ≤
        (24330011831893/549755813888 : ℝ) := by
  obtain ⟨iv,hiv,huiv⟩ := RationalIntervalCover.coversFrom_spec negativeCover
    (by norm_num) u (by simpa using hu.1) (by simpa using hu.2)
  simp only [negativeIntervals,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hiv
  rcases hiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact S1CircleBlock08.complete_block u huiv
  · exact S1CircleBlock09.complete_block u huiv
  · exact S1CircleBlock10.complete_block u huiv
  · exact S1CircleBlock11.complete_block u huiv
  · exact S1CircleBlock12.complete_block u huiv
  · exact S1CircleBlock13.complete_block u huiv
  · exact S1CircleBlock14.complete_block u huiv
  · exact S1CircleBlock15.complete_block u huiv
  · exact S1CircleBlock16.complete_block u huiv
  · exact S1CircleBlock17.complete_block u huiv
  · exact S1CircleBlock18.complete_block u huiv
  · exact S1CircleBlock19.complete_block u huiv
  · exact S1CircleBlock20.complete_block u huiv
  · exact S1CircleBlock21.complete_block u huiv
  · exact S1CircleBlock22.complete_block u huiv
  · exact S1CircleBlock23.complete_block u huiv
  · exact S1CircleBlock24.complete_block u huiv
  · exact S1CircleBlock25.complete_block u huiv
  · exact S1CircleBlock26.complete_block u huiv
  · exact S1CircleBlock27.complete_block u huiv
  · exact S1CircleBlock28.complete_block u huiv
  · exact S1CircleBlock29.complete_block u huiv
  · exact S1CircleBlock30.complete_block u huiv
  · exact S1CompleteBlockStress.complete_block u huiv
  · exact S1CircleBlock32.complete_block u huiv
  · exact S1CircleBlock33.complete_block u huiv
  · exact S1CircleBlock34.complete_block u huiv
  · exact S1CompleteBlockPilot.complete_block u huiv
  · exact S1CircleBlock36.complete_block u huiv
  · exact S1CircleBlock37.complete_block u huiv
  · exact S1CircleBlock38.complete_block u huiv
  · exact S1CircleBlock39.complete_block u huiv
  · exact S1CircleBlock40.complete_block u huiv
  · exact S1CircleBlock41.complete_block u huiv
  · exact S1CircleBlock42.complete_block u huiv
  · exact S1CircleBlock43.complete_block u huiv
  · exact S1CircleBlock44.complete_block u huiv
  · exact S1CircleBlock45.complete_block u huiv
  · exact S1CircleBlock46.complete_block u huiv
  · exact S1CircleBlock47.complete_block u huiv
theorem circle_weight (z : ℂ) (hz : ‖z‖=(3/5 : ℝ)) :
    (66 : ℝ)/130*ellipseLog (complexP.eval z)+8*Real.log ‖(1 : ℂ)-z‖ ≤
      (24330011831893/549755813888 : ℝ) := by
  change (66 : ℝ)/130*ellipseLog ((realP.map (algebraMap ℝ ℂ)).eval z)+
    8*Real.log ‖(1 : ℂ)-z‖ ≤ (24330011831893/549755813888 : ℝ)
  apply realPolynomial_circle_weight_of_charts realP (by norm_num) _ z hz
  intro side hs u hu
  change (66 : ℝ)/130*ellipseLog (complexP.eval (rationalCirclePoint (3/5) side u))+
    8*Real.log ‖(1 : ℂ)-rationalCirclePoint (3/5) side u‖ ≤ _
  rcases hs with rfl | rfl
  · exact positiveChart u hu
  · exact negativeChart u hu

theorem circleG : ∀ z : ℂ, ‖z‖=(3/5 : ℝ) →
    8*Real.log ‖(1 : ℂ)-z‖+66*green72 z ≤ circleCap72 := by
  intro z hz
  have hh := circle_weight z hz
  unfold green72 nodalGreen circleCap72
  change 8*Real.log ‖(1 : ℂ)-z‖+66*(ellipseLog (complexP.eval z)/(130 : ℝ)) ≤
    (24330011831893/549755813888 : ℝ)
  linarith

end
end CatalanMeasure.GenD.Signed.Davis.S1CircleData
#print axioms CatalanMeasure.GenD.Signed.Davis.S1CircleData.positiveChart
#print axioms CatalanMeasure.GenD.Signed.Davis.S1CircleData.negativeChart
#print axioms CatalanMeasure.GenD.Signed.Davis.S1CircleData.circleG

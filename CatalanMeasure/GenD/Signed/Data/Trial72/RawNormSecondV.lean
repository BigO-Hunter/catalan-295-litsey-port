module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog00
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog02
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog03
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog04
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog05
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog06
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog07
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog08
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog09
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog10
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog11
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog12
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog13
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog14
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog15
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog16
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog17
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog18
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog19
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog20
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog21
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog22
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog23
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog24
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog25
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog26
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog27
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog28
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog29
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog30
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog31
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog32
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog33
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog34
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog35
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog36
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog37
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVCross00
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVCross01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVCross02
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVCross03
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVCross04
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSquares

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondV
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem logs_ok : ∀ j < secondVLogUBs.length,
    logUpperWOK (((secondVTail.drop (1 * j)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms secondVTail))
      (secondVLogUBs.getD j 0) = true := by
  intro j hj
  change j < 75 at hj
  interval_cases j
  · exact RawNormSecondVLog00.row0
  · exact RawNormSecondVLog00.row1
  · exact RawNormSecondVLog01.row2
  · exact RawNormSecondVLog01.row3
  · exact RawNormSecondVLog02.row4
  · exact RawNormSecondVLog02.row5
  · exact RawNormSecondVLog03.row6
  · exact RawNormSecondVLog03.row7
  · exact RawNormSecondVLog04.row8
  · exact RawNormSecondVLog04.row9
  · exact RawNormSecondVLog05.row10
  · exact RawNormSecondVLog05.row11
  · exact RawNormSecondVLog06.row12
  · exact RawNormSecondVLog06.row13
  · exact RawNormSecondVLog07.row14
  · exact RawNormSecondVLog07.row15
  · exact RawNormSecondVLog08.row16
  · exact RawNormSecondVLog08.row17
  · exact RawNormSecondVLog09.row18
  · exact RawNormSecondVLog09.row19
  · exact RawNormSecondVLog10.row20
  · exact RawNormSecondVLog10.row21
  · exact RawNormSecondVLog11.row22
  · exact RawNormSecondVLog11.row23
  · exact RawNormSecondVLog12.row24
  · exact RawNormSecondVLog12.row25
  · exact RawNormSecondVLog13.row26
  · exact RawNormSecondVLog13.row27
  · exact RawNormSecondVLog14.row28
  · exact RawNormSecondVLog14.row29
  · exact RawNormSecondVLog15.row30
  · exact RawNormSecondVLog15.row31
  · exact RawNormSecondVLog16.row32
  · exact RawNormSecondVLog16.row33
  · exact RawNormSecondVLog17.row34
  · exact RawNormSecondVLog17.row35
  · exact RawNormSecondVLog18.row36
  · exact RawNormSecondVLog18.row37
  · exact RawNormSecondVLog19.row38
  · exact RawNormSecondVLog19.row39
  · exact RawNormSecondVLog20.row40
  · exact RawNormSecondVLog20.row41
  · exact RawNormSecondVLog21.row42
  · exact RawNormSecondVLog21.row43
  · exact RawNormSecondVLog22.row44
  · exact RawNormSecondVLog22.row45
  · exact RawNormSecondVLog23.row46
  · exact RawNormSecondVLog23.row47
  · exact RawNormSecondVLog24.row48
  · exact RawNormSecondVLog24.row49
  · exact RawNormSecondVLog25.row50
  · exact RawNormSecondVLog25.row51
  · exact RawNormSecondVLog26.row52
  · exact RawNormSecondVLog26.row53
  · exact RawNormSecondVLog27.row54
  · exact RawNormSecondVLog27.row55
  · exact RawNormSecondVLog28.row56
  · exact RawNormSecondVLog28.row57
  · exact RawNormSecondVLog29.row58
  · exact RawNormSecondVLog29.row59
  · exact RawNormSecondVLog30.row60
  · exact RawNormSecondVLog30.row61
  · exact RawNormSecondVLog31.row62
  · exact RawNormSecondVLog31.row63
  · exact RawNormSecondVLog32.row64
  · exact RawNormSecondVLog32.row65
  · exact RawNormSecondVLog33.row66
  · exact RawNormSecondVLog33.row67
  · exact RawNormSecondVLog34.row68
  · exact RawNormSecondVLog34.row69
  · exact RawNormSecondVLog35.row70
  · exact RawNormSecondVLog35.row71
  · exact RawNormSecondVLog36.row72
  · exact RawNormSecondVLog36.row73
  · exact RawNormSecondVLog37.row74

theorem cross_ok : ∀ j < secondVCrossUBs.length,
    (((secondVTail.drop (4 * j)).take 4).map (nCross NormData.secondVInt)).sum ≤ secondVCrossUBs.getD j 0 := by
  intro j hj
  change j < 19 at hj
  interval_cases j
  · exact RawNormSecondVCross00.cross0
  · exact RawNormSecondVCross00.cross1
  · exact RawNormSecondVCross00.cross2
  · exact RawNormSecondVCross00.cross3
  · exact RawNormSecondVCross01.cross4
  · exact RawNormSecondVCross01.cross5
  · exact RawNormSecondVCross01.cross6
  · exact RawNormSecondVCross01.cross7
  · exact RawNormSecondVCross02.cross8
  · exact RawNormSecondVCross02.cross9
  · exact RawNormSecondVCross02.cross10
  · exact RawNormSecondVCross02.cross11
  · exact RawNormSecondVCross03.cross12
  · exact RawNormSecondVCross03.cross13
  · exact RawNormSecondVCross03.cross14
  · exact RawNormSecondVCross03.cross15
  · exact RawNormSecondVCross04.cross16
  · exact RawNormSecondVCross04.cross17
  · exact RawNormSecondVCross04.cross18

theorem disk : tailsInDisk secondVTail = true := by
  unfold tailsInDisk
  apply List.all_eq_true.mpr
  intro t ht
  have hh := List.all_eq_true.mp ReferenceData.secondV_tail t ht
  simp only [Bool.and_eq_true] at hh
  exact hh.1.1

theorem raw_norm : barrierTrialNormSq (trialSeqS NormData.secondVInt secondVTail) ≤ (secondVNormUB : ℝ) :=
  normSq_le_of_shardsW disk 4 secondVCrossUBs secondVSqUB 1 secondVLogUBs
    RawNormSquares.secondV_sq (by decide +kernel) cross_ok (by decide +kernel) logs_ok (by decide +kernel)

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondV
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondV.raw_norm

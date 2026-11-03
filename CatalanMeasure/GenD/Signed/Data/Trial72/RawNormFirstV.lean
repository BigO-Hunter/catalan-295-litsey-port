module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog00
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog02
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog03
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog04
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog05
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog06
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog07
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog08
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog09
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog10
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog11
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog12
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog13
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog14
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog15
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog16
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog17
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog18
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog19
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog20
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog21
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog22
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog23
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog24
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog25
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog26
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog27
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog28
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog29
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog30
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog31
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog32
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog33
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog34
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog35
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog36
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog37
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVCross00
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVCross01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVCross02
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVCross03
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVCross04
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSquares

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstV
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem logs_ok : ∀ j < firstVLogUBs.length,
    logUpperWOK (((firstVTail.drop (1 * j)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstVTail))
      (firstVLogUBs.getD j 0) = true := by
  intro j hj
  change j < 75 at hj
  interval_cases j
  · exact RawNormFirstVLog00.row0
  · exact RawNormFirstVLog00.row1
  · exact RawNormFirstVLog01.row2
  · exact RawNormFirstVLog01.row3
  · exact RawNormFirstVLog02.row4
  · exact RawNormFirstVLog02.row5
  · exact RawNormFirstVLog03.row6
  · exact RawNormFirstVLog03.row7
  · exact RawNormFirstVLog04.row8
  · exact RawNormFirstVLog04.row9
  · exact RawNormFirstVLog05.row10
  · exact RawNormFirstVLog05.row11
  · exact RawNormFirstVLog06.row12
  · exact RawNormFirstVLog06.row13
  · exact RawNormFirstVLog07.row14
  · exact RawNormFirstVLog07.row15
  · exact RawNormFirstVLog08.row16
  · exact RawNormFirstVLog08.row17
  · exact RawNormFirstVLog09.row18
  · exact RawNormFirstVLog09.row19
  · exact RawNormFirstVLog10.row20
  · exact RawNormFirstVLog10.row21
  · exact RawNormFirstVLog11.row22
  · exact RawNormFirstVLog11.row23
  · exact RawNormFirstVLog12.row24
  · exact RawNormFirstVLog12.row25
  · exact RawNormFirstVLog13.row26
  · exact RawNormFirstVLog13.row27
  · exact RawNormFirstVLog14.row28
  · exact RawNormFirstVLog14.row29
  · exact RawNormFirstVLog15.row30
  · exact RawNormFirstVLog15.row31
  · exact RawNormFirstVLog16.row32
  · exact RawNormFirstVLog16.row33
  · exact RawNormFirstVLog17.row34
  · exact RawNormFirstVLog17.row35
  · exact RawNormFirstVLog18.row36
  · exact RawNormFirstVLog18.row37
  · exact RawNormFirstVLog19.row38
  · exact RawNormFirstVLog19.row39
  · exact RawNormFirstVLog20.row40
  · exact RawNormFirstVLog20.row41
  · exact RawNormFirstVLog21.row42
  · exact RawNormFirstVLog21.row43
  · exact RawNormFirstVLog22.row44
  · exact RawNormFirstVLog22.row45
  · exact RawNormFirstVLog23.row46
  · exact RawNormFirstVLog23.row47
  · exact RawNormFirstVLog24.row48
  · exact RawNormFirstVLog24.row49
  · exact RawNormFirstVLog25.row50
  · exact RawNormFirstVLog25.row51
  · exact RawNormFirstVLog26.row52
  · exact RawNormFirstVLog26.row53
  · exact RawNormFirstVLog27.row54
  · exact RawNormFirstVLog27.row55
  · exact RawNormFirstVLog28.row56
  · exact RawNormFirstVLog28.row57
  · exact RawNormFirstVLog29.row58
  · exact RawNormFirstVLog29.row59
  · exact RawNormFirstVLog30.row60
  · exact RawNormFirstVLog30.row61
  · exact RawNormFirstVLog31.row62
  · exact RawNormFirstVLog31.row63
  · exact RawNormFirstVLog32.row64
  · exact RawNormFirstVLog32.row65
  · exact RawNormFirstVLog33.row66
  · exact RawNormFirstVLog33.row67
  · exact RawNormFirstVLog34.row68
  · exact RawNormFirstVLog34.row69
  · exact RawNormFirstVLog35.row70
  · exact RawNormFirstVLog35.row71
  · exact RawNormFirstVLog36.row72
  · exact RawNormFirstVLog36.row73
  · exact RawNormFirstVLog37.row74

theorem cross_ok : ∀ j < firstVCrossUBs.length,
    (((firstVTail.drop (4 * j)).take 4).map (nCross NormData.firstVInt)).sum ≤ firstVCrossUBs.getD j 0 := by
  intro j hj
  change j < 19 at hj
  interval_cases j
  · exact RawNormFirstVCross00.cross0
  · exact RawNormFirstVCross00.cross1
  · exact RawNormFirstVCross00.cross2
  · exact RawNormFirstVCross00.cross3
  · exact RawNormFirstVCross01.cross4
  · exact RawNormFirstVCross01.cross5
  · exact RawNormFirstVCross01.cross6
  · exact RawNormFirstVCross01.cross7
  · exact RawNormFirstVCross02.cross8
  · exact RawNormFirstVCross02.cross9
  · exact RawNormFirstVCross02.cross10
  · exact RawNormFirstVCross02.cross11
  · exact RawNormFirstVCross03.cross12
  · exact RawNormFirstVCross03.cross13
  · exact RawNormFirstVCross03.cross14
  · exact RawNormFirstVCross03.cross15
  · exact RawNormFirstVCross04.cross16
  · exact RawNormFirstVCross04.cross17
  · exact RawNormFirstVCross04.cross18

theorem disk : tailsInDisk firstVTail = true := by
  unfold tailsInDisk
  apply List.all_eq_true.mpr
  intro t ht
  have hh := List.all_eq_true.mp ReferenceData.firstV_tail t ht
  simp only [Bool.and_eq_true] at hh
  exact hh.1.1

theorem raw_norm : barrierTrialNormSq (trialSeqS NormData.firstVInt firstVTail) ≤ (firstVNormUB : ℝ) :=
  normSq_le_of_shardsW disk 4 firstVCrossUBs firstVSqUB 1 firstVLogUBs
    RawNormSquares.firstV_sq (by decide +kernel) cross_ok (by decide +kernel) logs_ok (by decide +kernel)

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstV
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstV.raw_norm

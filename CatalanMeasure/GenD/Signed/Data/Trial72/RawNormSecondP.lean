module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog00
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog02
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog03
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog04
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog05
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog06
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog07
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog08
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog09
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog10
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog11
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog12
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog13
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog14
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog15
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog16
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog17
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog18
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog19
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog20
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog21
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog22
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog23
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog24
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog25
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog26
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog27
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog28
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog29
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog30
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog31
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog32
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog33
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog34
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog35
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog36
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog37
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross00
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross02
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross03
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross04
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSquares

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondP
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem logs_ok : ∀ j < secondPLogUBs.length,
    logUpperWOK (((secondPTail.drop (1 * j)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms secondPTail))
      (secondPLogUBs.getD j 0) = true := by
  intro j hj
  change j < 75 at hj
  interval_cases j
  · exact RawNormSecondPLog00.row0
  · exact RawNormSecondPLog00.row1
  · exact RawNormSecondPLog01.row2
  · exact RawNormSecondPLog01.row3
  · exact RawNormSecondPLog02.row4
  · exact RawNormSecondPLog02.row5
  · exact RawNormSecondPLog03.row6
  · exact RawNormSecondPLog03.row7
  · exact RawNormSecondPLog04.row8
  · exact RawNormSecondPLog04.row9
  · exact RawNormSecondPLog05.row10
  · exact RawNormSecondPLog05.row11
  · exact RawNormSecondPLog06.row12
  · exact RawNormSecondPLog06.row13
  · exact RawNormSecondPLog07.row14
  · exact RawNormSecondPLog07.row15
  · exact RawNormSecondPLog08.row16
  · exact RawNormSecondPLog08.row17
  · exact RawNormSecondPLog09.row18
  · exact RawNormSecondPLog09.row19
  · exact RawNormSecondPLog10.row20
  · exact RawNormSecondPLog10.row21
  · exact RawNormSecondPLog11.row22
  · exact RawNormSecondPLog11.row23
  · exact RawNormSecondPLog12.row24
  · exact RawNormSecondPLog12.row25
  · exact RawNormSecondPLog13.row26
  · exact RawNormSecondPLog13.row27
  · exact RawNormSecondPLog14.row28
  · exact RawNormSecondPLog14.row29
  · exact RawNormSecondPLog15.row30
  · exact RawNormSecondPLog15.row31
  · exact RawNormSecondPLog16.row32
  · exact RawNormSecondPLog16.row33
  · exact RawNormSecondPLog17.row34
  · exact RawNormSecondPLog17.row35
  · exact RawNormSecondPLog18.row36
  · exact RawNormSecondPLog18.row37
  · exact RawNormSecondPLog19.row38
  · exact RawNormSecondPLog19.row39
  · exact RawNormSecondPLog20.row40
  · exact RawNormSecondPLog20.row41
  · exact RawNormSecondPLog21.row42
  · exact RawNormSecondPLog21.row43
  · exact RawNormSecondPLog22.row44
  · exact RawNormSecondPLog22.row45
  · exact RawNormSecondPLog23.row46
  · exact RawNormSecondPLog23.row47
  · exact RawNormSecondPLog24.row48
  · exact RawNormSecondPLog24.row49
  · exact RawNormSecondPLog25.row50
  · exact RawNormSecondPLog25.row51
  · exact RawNormSecondPLog26.row52
  · exact RawNormSecondPLog26.row53
  · exact RawNormSecondPLog27.row54
  · exact RawNormSecondPLog27.row55
  · exact RawNormSecondPLog28.row56
  · exact RawNormSecondPLog28.row57
  · exact RawNormSecondPLog29.row58
  · exact RawNormSecondPLog29.row59
  · exact RawNormSecondPLog30.row60
  · exact RawNormSecondPLog30.row61
  · exact RawNormSecondPLog31.row62
  · exact RawNormSecondPLog31.row63
  · exact RawNormSecondPLog32.row64
  · exact RawNormSecondPLog32.row65
  · exact RawNormSecondPLog33.row66
  · exact RawNormSecondPLog33.row67
  · exact RawNormSecondPLog34.row68
  · exact RawNormSecondPLog34.row69
  · exact RawNormSecondPLog35.row70
  · exact RawNormSecondPLog35.row71
  · exact RawNormSecondPLog36.row72
  · exact RawNormSecondPLog36.row73
  · exact RawNormSecondPLog37.row74

theorem cross_ok : ∀ j < secondPCrossUBs.length,
    (((secondPTail.drop (4 * j)).take 4).map (nCross NormData.secondPInt)).sum ≤ secondPCrossUBs.getD j 0 := by
  intro j hj
  change j < 19 at hj
  interval_cases j
  · exact RawNormSecondPCross00.cross0
  · exact RawNormSecondPCross00.cross1
  · exact RawNormSecondPCross00.cross2
  · exact RawNormSecondPCross00.cross3
  · exact RawNormSecondPCross01.cross4
  · exact RawNormSecondPCross01.cross5
  · exact RawNormSecondPCross01.cross6
  · exact RawNormSecondPCross01.cross7
  · exact RawNormSecondPCross02.cross8
  · exact RawNormSecondPCross02.cross9
  · exact RawNormSecondPCross02.cross10
  · exact RawNormSecondPCross02.cross11
  · exact RawNormSecondPCross03.cross12
  · exact RawNormSecondPCross03.cross13
  · exact RawNormSecondPCross03.cross14
  · exact RawNormSecondPCross03.cross15
  · exact RawNormSecondPCross04.cross16
  · exact RawNormSecondPCross04.cross17
  · exact RawNormSecondPCross04.cross18

theorem disk : tailsInDisk secondPTail = true := by
  unfold tailsInDisk
  apply List.all_eq_true.mpr
  intro t ht
  have hh := List.all_eq_true.mp ReferenceData.secondP_tail t ht
  simp only [Bool.and_eq_true] at hh
  exact hh.1.1

theorem raw_norm : barrierTrialNormSq (trialSeqS NormData.secondPInt secondPTail) ≤ (secondPNormUB : ℝ) :=
  normSq_le_of_shardsW disk 4 secondPCrossUBs secondPSqUB 1 secondPLogUBs
    RawNormSquares.secondP_sq (by decide +kernel) cross_ok (by decide +kernel) logs_ok (by decide +kernel)

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondP
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondP.raw_norm

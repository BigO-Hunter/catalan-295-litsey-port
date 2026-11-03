module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog00
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog02
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog03
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog04
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog05
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog06
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog07
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog08
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog09
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog10
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog11
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog12
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog13
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog14
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog15
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog16
public import CatalanMeasure.GenD.Signed.Data.Trial72.NormLogFirstP2
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog18
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog19
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog20
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog21
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog22
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog23
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog24
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog25
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog26
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog27
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog28
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog29
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog30
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog31
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog32
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog33
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog34
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog35
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog36
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog37
public import CatalanMeasure.GenD.Signed.Data.Trial72.NormFinFirstP2
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPCross00
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPCross01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPCross02
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPCross03
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPCross04
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSquares

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstP
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem logs_ok : ∀ j < firstPLogUBs.length,
    logUpperWOK (((firstPTail.drop (1 * j)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstPTail))
      (firstPLogUBs.getD j 0) = true := by
  intro j hj
  change j < 75 at hj
  interval_cases j
  · exact RawNormFirstPLog00.row0
  · exact RawNormFirstPLog00.row1
  · exact RawNormFirstPLog01.row2
  · exact RawNormFirstPLog01.row3
  · exact RawNormFirstPLog02.row4
  · exact RawNormFirstPLog02.row5
  · exact RawNormFirstPLog03.row6
  · exact RawNormFirstPLog03.row7
  · exact RawNormFirstPLog04.row8
  · exact RawNormFirstPLog04.row9
  · exact RawNormFirstPLog05.row10
  · exact RawNormFirstPLog05.row11
  · exact RawNormFirstPLog06.row12
  · exact RawNormFirstPLog06.row13
  · exact RawNormFirstPLog07.row14
  · exact RawNormFirstPLog07.row15
  · exact RawNormFirstPLog08.row16
  · exact RawNormFirstPLog08.row17
  · exact RawNormFirstPLog09.row18
  · exact RawNormFirstPLog09.row19
  · exact RawNormFirstPLog10.row20
  · exact RawNormFirstPLog10.row21
  · exact RawNormFirstPLog11.row22
  · exact RawNormFirstPLog11.row23
  · exact RawNormFirstPLog12.row24
  · exact RawNormFirstPLog12.row25
  · exact RawNormFirstPLog13.row26
  · exact RawNormFirstPLog13.row27
  · exact RawNormFirstPLog14.row28
  · exact RawNormFirstPLog14.row29
  · exact RawNormFirstPLog15.row30
  · exact RawNormFirstPLog15.row31
  · exact RawNormFirstPLog16.row32
  · exact RawNormFirstPLog16.row33
  · exact NormLogFirstP2.nlFirstP34W
  · exact NormLogFirstP2.nlFirstP35W
  · exact RawNormFirstPLog18.row36
  · exact RawNormFirstPLog18.row37
  · exact RawNormFirstPLog19.row38
  · exact RawNormFirstPLog19.row39
  · exact RawNormFirstPLog20.row40
  · exact RawNormFirstPLog20.row41
  · exact RawNormFirstPLog21.row42
  · exact RawNormFirstPLog21.row43
  · exact RawNormFirstPLog22.row44
  · exact RawNormFirstPLog22.row45
  · exact RawNormFirstPLog23.row46
  · exact RawNormFirstPLog23.row47
  · exact RawNormFirstPLog24.row48
  · exact RawNormFirstPLog24.row49
  · exact RawNormFirstPLog25.row50
  · exact RawNormFirstPLog25.row51
  · exact RawNormFirstPLog26.row52
  · exact RawNormFirstPLog26.row53
  · exact RawNormFirstPLog27.row54
  · exact RawNormFirstPLog27.row55
  · exact RawNormFirstPLog28.row56
  · exact RawNormFirstPLog28.row57
  · exact RawNormFirstPLog29.row58
  · exact RawNormFirstPLog29.row59
  · exact RawNormFirstPLog30.row60
  · exact RawNormFirstPLog30.row61
  · exact RawNormFirstPLog31.row62
  · exact RawNormFirstPLog31.row63
  · exact RawNormFirstPLog32.row64
  · exact RawNormFirstPLog32.row65
  · exact RawNormFirstPLog33.row66
  · exact RawNormFirstPLog33.row67
  · exact RawNormFirstPLog34.row68
  · exact RawNormFirstPLog34.row69
  · exact RawNormFirstPLog35.row70
  · exact RawNormFirstPLog35.row71
  · exact RawNormFirstPLog36.row72
  · exact RawNormFirstPLog36.row73
  · exact RawNormFirstPLog37.row74

theorem cross_ok : ∀ j < firstPCrossUBs.length,
    (((firstPTail.drop (4 * j)).take 4).map (nCross NormData.firstPInt)).sum ≤ firstPCrossUBs.getD j 0 := by
  intro j hj
  change j < 19 at hj
  interval_cases j
  · exact RawNormFirstPCross00.cross0
  · exact RawNormFirstPCross00.cross1
  · exact RawNormFirstPCross00.cross2
  · exact RawNormFirstPCross00.cross3
  · exact RawNormFirstPCross01.cross4
  · exact RawNormFirstPCross01.cross5
  · exact RawNormFirstPCross01.cross6
  · exact RawNormFirstPCross01.cross7
  · exact RawNormFirstPCross02.cross8
  · exact RawNormFirstPCross02.cross9
  · exact RawNormFirstPCross02.cross10
  · exact RawNormFirstPCross02.cross11
  · exact RawNormFirstPCross03.cross12
  · exact RawNormFirstPCross03.cross13
  · exact NormFinFirstP2.nfFirstP14
  · exact RawNormFirstPCross03.cross15
  · exact RawNormFirstPCross03.cross16
  · exact RawNormFirstPCross04.cross17
  · exact RawNormFirstPCross04.cross18

theorem disk : tailsInDisk firstPTail = true := by
  unfold tailsInDisk
  apply List.all_eq_true.mpr
  intro t ht
  have hh := List.all_eq_true.mp ReferenceData.firstP_tail t ht
  simp only [Bool.and_eq_true] at hh
  exact hh.1.1

theorem raw_norm : barrierTrialNormSq (trialSeqS NormData.firstPInt firstPTail) ≤ (firstPNormUB : ℝ) :=
  normSq_le_of_shardsW disk 4 firstPCrossUBs firstPSqUB 1 firstPLogUBs
    RawNormSquares.firstP_sq (by decide +kernel) cross_ok (by decide +kernel) logs_ok (by decide +kernel)

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstP
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstP.raw_norm

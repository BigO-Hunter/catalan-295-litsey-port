module

public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionCore
public import CatalanMeasure.GenD.Signed.Data.Trial.Hid
public import CatalanMeasure.CellCert.RawInts

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionNodes
open CatalanMeasure.Signed CatalanMeasure.Refinement CatalanMeasure.CellCert
open CatalanMeasure.GenD.Signed.LogEval CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section

def E : ℚ := (qlist (raw_ints% [6613313319248080001, 2432902008176640000])).headD 0
theorem e_checked : expTaylorRat 1 21 = E := by decide +kernel
theorem e_nonneg : 0 ≤ E := by decide +kernel
theorem e_le : (E : ℝ) ≤ Real.exp 1 := by
  rw [← e_checked]
  simpa using expTaylorRat_le_exp (x := (1 : ℚ)) (by norm_num) 21

def arg0 : ℚ := (qlist (raw_ints% [0, 1])).headD 0
def exp0 : ℚ := (qlist (raw_ints% [1, 1])).headD 0
theorem arg0_nonneg : 0 ≤ arg0 := by decide +kernel
theorem exp0_nonneg : 0 ≤ exp0 := by decide +kernel
theorem exp0_checked : expTaylorRat arg0 21 = exp0 := by decide +kernel
theorem exp0_le : (exp0 : ℝ) ≤ Real.exp (arg0 : ℝ) := by
  rw [← exp0_checked]
  exact expTaylorRat_le_exp arg0_nonneg 21

def arg1 : ℚ := (qlist (raw_ints% [271741149, 715128832])).headD 0
def exp1 : ℚ := (qlist (raw_ints% [39031799870716513774453561071848991989819619321752876369450574744929752458915514160512232486515489957740591066117887451367193786099311441434682394205385279423145154739683825291224156020086113, 26692633069245507871231563990643977773645032155431011852813241108964657582935182290057641555966581353575863942300356612947976158076787542993991366196813985661409023390861435495164642590720000])).headD 0
theorem arg1_nonneg : 0 ≤ arg1 := by decide +kernel
theorem exp1_nonneg : 0 ≤ exp1 := by decide +kernel
theorem exp1_checked : expTaylorRat arg1 21 = exp1 := by decide +kernel
theorem exp1_le : (exp1 : ℝ) ≤ Real.exp (arg1 : ℝ) := by
  rw [← exp1_checked]
  exact expTaylorRat_le_exp arg1_nonneg 21

def arg2 : ℚ := (qlist (raw_ints% [1299087969369, 2621532274688])).headD 0
def exp2 : ℚ := (qlist (raw_ints% [13004050746140028750714231158641551789956534159277818212738400096211955256097059266557068076848569567194088912682845685720865245059993679000012453544468668720423400827236063938286440140392162287459810246154521121786865536473999524066277593717912233096791704020451, 7922569741583052676032258364333400461513227121750988487899110748752806234771863924134672098689201470495840898393235938046891983577151244318093995833731213060434683245549906495732565817213174107734861395595872066785577164274748549078763546866589993258545315840000])).headD 0
theorem arg2_nonneg : 0 ≤ arg2 := by decide +kernel
theorem exp2_nonneg : 0 ≤ exp2 := by decide +kernel
theorem exp2_checked : expTaylorRat arg2 21 = exp2 := by decide +kernel
theorem exp2_le : (exp2 : ℝ) ≤ Real.exp (arg2 : ℝ) := by
  rw [← exp2_checked]
  exact expTaylorRat_le_exp arg2_nonneg 21

def arg3 : ℚ := (qlist (raw_ints% [6386583935, 9965666304])).headD 0
def exp3 : ℚ := (qlist (raw_ints% [689751755062243868100845969532993959908296701562973156175778363936627113785465236967933259455091389669855199358484606548534212877220982789271286424119418028869353893003039991350980653659307837359371463742543825035409, 363388699653066612191669599054909081209662071886776000087365319324810018347944220079367241214158986123903349640738580588093197790315193324561199035352650029248311537715908847006057384380763717580440989128981924020224])).headD 0
theorem arg3_nonneg : 0 ≤ arg3 := by decide +kernel
theorem exp3_nonneg : 0 ≤ exp3 := by decide +kernel
theorem exp3_checked : expTaylorRat arg3 21 = exp3 := by decide +kernel
theorem exp3_le : (exp3 : ℝ) ≤ Real.exp (arg3 : ℝ) := by
  rw [← exp3_checked]
  exact expTaylorRat_le_exp arg3_nonneg 21

def arg4 : ℚ := (qlist (raw_ints% [1853973623727, 2831339749376])).headD 0
def exp4 : ℚ := (qlist (raw_ints% [71118000460584507199096403158528414894875141006265386553596475546404651397889596194430343858505477043759488777473708630913999669270111324468669056668536079271343512384538823973614944323925007103905178176083943945224084017225411030028296442365486858660097905345411, 36948908677685969629158327966352625121252084399741959036112026281689412266339739696919332626063491784407002468850730059189954196639732793708365770459711672166409777114650871459948755692530727204194800417287254006442772606368245531316472674281735486508462243840000])).headD 0
theorem arg4_nonneg : 0 ≤ arg4 := by decide +kernel
theorem exp4_nonneg : 0 ≤ exp4 := by decide +kernel
theorem exp4_checked : expTaylorRat arg4 21 = exp4 := by decide +kernel
theorem exp4_le : (exp4 : ℝ) ≤ Real.exp (arg4 : ℝ) := by
  rw [← exp4_checked]
  exact expTaylorRat_le_exp arg4_nonneg 21

def arg5 : ℚ := (qlist (raw_ints% [4308650217961, 6501909397504])).headD 0
def exp5 : ℚ := (qlist (raw_ints% [86047609148471770021670574360320373262322935601282363105566360856657914319445701192835199402881950675634676606855153072940297203540325718818299687054383072215495310325528616909142736411216721012991564832206244726362650254160390804453652185682644883490667373271657150806370721, 44355030805015892371453736980218822428673613183464408345720249919178567154237319505826183682039114387754270709192694066145987205838659878178054624029934659801854059965819504309362017254240603856148719032148254565621935872026400133341818974497121645954151584209792810352640000])).headD 0
theorem arg5_nonneg : 0 ≤ arg5 := by decide +kernel
theorem exp5_nonneg : 0 ≤ exp5 := by decide +kernel
theorem exp5_checked : expTaylorRat arg5 21 = exp5 := by decide +kernel
theorem exp5_le : (exp5 : ℝ) ≤ Real.exp (arg5 : ℝ) := by
  rw [← exp5_checked]
  exact expTaylorRat_le_exp arg5_nonneg 21

def theta : ℚ := 1 / 1000
def logValue : ℚ × ℚ := ((qlist (raw_ints% [-588679264591688758597680190076088685360026937213473052527942151531260938880917179996691919096783793697, 85220052074344922657159726438000431570373537897847303157330828786545207320395719927801781588978565120])).headD 0, (qlist (raw_ints% [2885621, 44601320255877785813839704857993007127855104])).headD 0)
theorem log_checked : logQ 7 theta = some logValue := by decide +kernel
def logLo : ℚ := (qlist (raw_ints% [-22045449779694152320724525438159445178254126681813074196818859242246310924726139517066864908998544430433323, 3191405730132143008587974595376678161878918620736483655938882207227331468941499315576248918725658285178880])).headD 0
def logHi : ℚ := (qlist (raw_ints% [-22045449779694152320724525438159445177841170861601630491418952023142070875576795430325366447512368149884583, 3191405730132143008587974595376678161878918620736483655938882207227331468941499315576248918725658285178880])).headD 0
theorem log_bounds : (logLo : ℝ) ≤ Real.log (1/1000) ∧ Real.log (1/1000) ≤ (logHi : ℝ) := by
  have h := (logQ_spec log_checked).2
  have hlo : logLo ≤ logValue.1 - logValue.2 := by decide +kernel
  have hhi : logValue.1 + logValue.2 ≤ logHi := by decide +kernel
  have hx : (theta : ℝ) = 1/1000 := by norm_num [theta]
  rw [hx] at h
  exact ⟨((Rat.cast_le (K := ℝ)).mpr hlo).trans h.ge_lower, h.le_upper.trans ((Rat.cast_le (K := ℝ)).mpr hhi)⟩

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionNodes
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionNodes.e_le
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionNodes.exp0_le
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionNodes.exp1_le
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionNodes.exp2_le
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionNodes.exp3_le
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionNodes.exp4_le
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionNodes.exp5_le
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionNodes.log_bounds

module

public import CatalanMeasure.GenD.Signed.Data.Trial72.CostHornerPilot

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert CatalanMeasure.Signed OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial72 CatalanMeasure.GenD.Signed.Data.Trial
noncomputable section
namespace A00
abbrev ap := CostHornerPilot.ap
abbrev sqrtLo := CostHornerPilot.sqrtLo
abbrev sqrtHi := CostHornerPilot.sqrtHi
abbrev rhoLo := CostHornerPilot.rhoLo
abbrev rhoHi := CostHornerPilot.rhoHi
abbrev rho := CostHornerPilot.rho
theorem rhoLo_nonneg : 0 ≤ rhoLo := CostHornerPilot.rhoLo_nonneg
theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := CostHornerPilot.rho_bounds
end A00
namespace A01
def ap : ℚ := (qlist (raw_ints% [1, 1776000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [160362657384020239247, 151115727451828646838272])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [1282901259072161913979, 1208925819614629174706176])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A01
namespace A02
def ap : ℚ := (qlist (raw_ints% [3, 4736000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [85045143360431897151, 75557863725914323419136])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [1360722293766910354419, 1208925819614629174706176])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A02
namespace A03
def ap : ℚ := (qlist (raw_ints% [27, 37888000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [180407996302639019005, 151115727451828646838272])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [1443263970421112152043, 1208925819614629174706176])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A03
namespace A04
def ap : ℚ := (qlist (raw_ints% [243, 303104000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [765406322440515639075, 604462909807314587353088])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [1530812644881031278153, 1208925819614629174706176])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A04
namespace A05
def ap : ℚ := (qlist (raw_ints% [2187, 2424832000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [1623672043560533012451, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [811836021780266506227, 604462909807314587353088])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A05
namespace A06
def ap : ℚ := (qlist (raw_ints% [19683, 19398656000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [1722164317176086380239, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [861082158588043190121, 604462909807314587353088])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A06
namespace A07
def ap : ℚ := (qlist (raw_ints% [177147, 155189248000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [1826631158407964794459, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [913315579203982397231, 604462909807314587353088])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A07
namespace A08
def ap : ℚ := (qlist (raw_ints% [1594323, 1241513984000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [1937434987366665856005, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [242179373420833232001, 151115727451828646838272])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A08
namespace A09
def ap : ℚ := (qlist (raw_ints% [14348907, 9932111872000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [1027480104489557137501, 604462909807314587353088])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [2054960208979114275005, 1208925819614629174706176])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A09
namespace A10
def ap : ℚ := (qlist (raw_ints% [129140163, 79456894976000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [2179614546659089522659, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [1089807273329544761331, 604462909807314587353088])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A10
namespace A11
def ap : ℚ := (qlist (raw_ints% [1162261467, 635655159808000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [2311830456891410646073, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [577957614222852661519, 302231454903657293676544])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A11
namespace A12
def ap : ℚ := (qlist (raw_ints% [10460353203, 5085241278464000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [2452066629640648246385, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [613016657410162061597, 302231454903657293676544])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A12
namespace A13
def ap : ℚ := (qlist (raw_ints% [94143178827, 40681930227712000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [1300404789896755104167, 604462909807314587353088])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [2600809579793510208337, 1208925819614629174706176])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A13
namespace A14
def ap : ℚ := (qlist (raw_ints% [847288609443, 325455441821696000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [2758575335160618317555, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [1379287667580309158779, 604462909807314587353088])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A14
namespace A15
def ap : ℚ := (qlist (raw_ints% [7625597484987, 2603643534573568000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [1462955613449639649467, 604462909807314587353088])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [2925911226899279298937, 1208925819614629174706176])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A15
namespace A16
def ap : ℚ := (qlist (raw_ints% [68630377364883, 20829148276588544000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [3103397788575249520909, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [193962361785953095057, 75557863725914323419136])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A16
namespace A17
def ap : ℚ := (qlist (raw_ints% [617673396283947, 166633186212708352000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [1645825385229833852233, 604462909807314587353088])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [3291650770459667704469, 1208925819614629174706176])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A17
namespace A18
def ap : ℚ := (qlist (raw_ints% [5559060566555523, 1333065489701666816000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [3491323276058636579691, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [1745661638029318289847, 604462909807314587353088])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A18
namespace A19
def ap : ℚ := (qlist (raw_ints% [50031545098999707, 10664523917613334528000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [1851554014149406341715, 604462909807314587353088])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [3703108028298812683433, 1208925819614629174706176])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A19
namespace A20
def ap : ℚ := (qlist (raw_ints% [450283905890997363, 85316191340906676224000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [3927739773244348028575, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [1963869886622174014289, 604462909807314587353088])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A20
namespace A21
def ap : ℚ := (qlist (raw_ints% [4052555153018976267, 682529530727253409792000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [4165997829700254455521, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [1041499457425063613881, 302231454903657293676544])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A21
namespace A22
def ap : ℚ := (qlist (raw_ints% [36472996377170786403, 5460236245818027278336000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [4418708793566476784139, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [2209354396783238392071, 604462909807314587353088])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A22
namespace A23
def ap : ℚ := (qlist (raw_ints% [328256967394537077627, 43681889966544218226688000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [4686749406347528136771, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [2343374703173764068387, 604462909807314587353088])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A23
namespace A24
def ap : ℚ := (qlist (raw_ints% [2954312706550833698643, 349455119732353745813504000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [2485524798898225626255, 604462909807314587353088])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [4971049597796451252513, 1208925819614629174706176])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A24
namespace A25
def ap : ℚ := (qlist (raw_ints% [26588814358957503287787, 2795640957858829966508032000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [5272595713281252585247, 1208925819614629174706176])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [2636297856640626292625, 604462909807314587353088])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A25
namespace A26
def ap : ℚ := (qlist (raw_ints% [239299329230617529590083, 22365127662870639732064256000])).headD 0
def sqrtLo : ℚ := (qlist (raw_ints% [2796216968554545291855, 604462909807314587353088])).headD 0
def sqrtHi : ℚ := (qlist (raw_ints% [5592433937109090583713, 1208925819614629174706176])).headD 0
def rhoLo : ℚ := 1+ap-sqrtHi
def rhoHi : ℚ := 1+ap-sqrtLo
def rho : ℝ := 1+(ap : ℝ)-Real.sqrt ((ap : ℝ)*(2+(ap : ℝ)))

theorem sqrt_checked : 0 ≤ ap ∧ 0 ≤ sqrtLo ∧ 0 ≤ sqrtHi ∧
    sqrtLo^2 ≤ ap*(2+ap) ∧ ap*(2+ap) ≤ sqrtHi^2 := by
  -- kcost: 0.003 s estimated;five comparisons plus rational squares/products.
  decide +kernel

theorem rhoLo_nonneg : 0 ≤ rhoLo := by
  -- kcost: 0.001 s estimated;one rational subtraction/sign comparison.
  decide +kernel

theorem rho_bounds : (rhoLo : ℝ) ≤ rho ∧ rho ≤ (rhoHi : ℝ) := by
  obtain ⟨ha,hl,hh,hlo,hhi⟩ := sqrt_checked
  have ha' : (0 : ℝ) ≤ (ap : ℝ) := by exact_mod_cast ha
  have hl' : (0 : ℝ) ≤ (sqrtLo : ℝ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (sqrtHi : ℝ) := by exact_mod_cast hh
  have hlo' : (sqrtLo : ℝ)^2 ≤ (ap : ℝ)*(2+(ap : ℝ)) := by exact_mod_cast hlo
  have hhi' : (ap : ℝ)*(2+(ap : ℝ)) ≤ (sqrtHi : ℝ)^2 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (ap : ℝ)*(2+(ap : ℝ)) := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((ap : ℝ)*(2+(ap : ℝ)))
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) := by
    nlinarith only [hlo',hsq,hl',hs0]
  have hshi : Real.sqrt ((ap : ℝ)*(2+(ap : ℝ))) ≤ (sqrtHi : ℝ) := by
    nlinarith only [hhi',hsq,hh',hs0]
  dsimp only [rhoLo,rhoHi,rho]
  push_cast
  constructor <;> linarith

end A26
end
end CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A00.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A01.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A02.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A03.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A04.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A05.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A06.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A07.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A08.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A09.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A10.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A11.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A12.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A13.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A14.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A15.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A16.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A17.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A18.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A19.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A20.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A21.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A22.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A23.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A24.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A25.rho_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData.A26.rho_bounds

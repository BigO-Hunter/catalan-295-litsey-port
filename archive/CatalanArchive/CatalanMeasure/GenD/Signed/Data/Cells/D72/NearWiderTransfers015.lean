module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache008
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers015
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers015
open D72.LogTransfer
def d2WiderTransfer120Lo : ℚ := (d2LitsNearWiderTransfers015.q2 (165758587) 1 (-28))
def d2WiderTransfer120Hi : ℚ := (d2LitsNearWiderTransfers015.q2 (1327746417) 1 (-31))
def d2WiderTransfer120Cap : ℚ := (d2LitsNearWiderTransfers015.q2 (4591115534748209726435) 1 (-78))
def d2WiderTransfer120C0 : ℚ := (d2LitsNearWiderTransfers015.q2 (1) 1 (-5))
def d2WiderTransfer120S0 : ℚ := (d2LitsNearWiderTransfers015.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer120Arithmetic : weightedUpper d2WiderTransfer120C0 d2Log132Lo d2Log132Hi ≤ d2WiderTransfer120Cap := by decide +kernel
theorem d2WiderTransfer120Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer120Lo:ℚ):ℝ) ((d2WiderTransfer120Hi:ℚ):ℝ), ((d2WiderTransfer120C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer120S0:ℚ):ℝ)| ≤ ((d2WiderTransfer120Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer120S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer120S0,d2WiderTransfer120Lo,d2WiderTransfer120Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer120C0 then |x-((d2WiderTransfer120S0:ℚ):ℝ)| ≤ ((d2Log132Q:ℚ):ℝ) else ((d2Log132Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer120S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer120S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer120S0,d2WiderTransfer120Lo,d2WiderTransfer120Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer120C0,d2Log132Q,d2WiderTransfer120S0,d2WiderTransfer120Lo,d2WiderTransfer120Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer120C0 d2WiderTransfer120S0 d2Log132Q d2Log132Lo d2Log132Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log132Bounds
  have har : (((weightedUpper d2WiderTransfer120C0 d2Log132Lo d2Log132Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer120Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer120Arithmetic
  linarith
#print axioms d2WiderTransfer120Arithmetic
#print axioms d2WiderTransfer120Bound
def d2WiderTransfer121Lo : ℚ := (d2LitsNearWiderTransfers015.q2 (165758587) 1 (-28))
def d2WiderTransfer121Hi : ℚ := (d2LitsNearWiderTransfers015.q2 (1327746417) 1 (-31))
def d2WiderTransfer121Cap : ℚ := (d2LitsNearWiderTransfers015.q2 (8682324865321086567395) 1 (-78))
def d2WiderTransfer121C0 : ℚ := (d2LitsNearWiderTransfers015.q2 (1) 11 (-5))
def d2WiderTransfer121S0 : ℚ := (d2LitsNearWiderTransfers015.q2 (-1) 1 (0))
def d2WiderTransfer121C1 : ℚ := (d2LitsNearWiderTransfers015.q2 (-5) 11 (-4))
def d2WiderTransfer121S1 : ℚ := (d2LitsNearWiderTransfers015.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer121Arithmetic : weightedUpper d2WiderTransfer121C0 d2Log132Lo d2Log132Hi + weightedUpper d2WiderTransfer121C1 d2Log42Lo d2Log42Hi ≤ d2WiderTransfer121Cap := by decide +kernel
theorem d2WiderTransfer121Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer121Lo:ℚ):ℝ) ((d2WiderTransfer121Hi:ℚ):ℝ), ((d2WiderTransfer121C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer121S0:ℚ):ℝ)| + ((d2WiderTransfer121C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer121S1:ℚ):ℝ)| ≤ ((d2WiderTransfer121Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer121S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer121S0,d2WiderTransfer121Lo,d2WiderTransfer121Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer121C0 then |x-((d2WiderTransfer121S0:ℚ):ℝ)| ≤ ((d2Log132Q:ℚ):ℝ) else ((d2Log132Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer121S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer121S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer121S0,d2WiderTransfer121Lo,d2WiderTransfer121Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer121C0,d2Log132Q,d2WiderTransfer121S0,d2WiderTransfer121Lo,d2WiderTransfer121Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer121C0 d2WiderTransfer121S0 d2Log132Q d2Log132Lo d2Log132Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log132Bounds
  have hn1 : x-((d2WiderTransfer121S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer121S1,d2WiderTransfer121Lo,d2WiderTransfer121Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer121C1 then |x-((d2WiderTransfer121S1:ℚ):ℝ)| ≤ ((d2Log42Q:ℚ):ℝ) else ((d2Log42Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer121S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer121S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer121S1,d2WiderTransfer121Lo,d2WiderTransfer121Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer121C1,d2Log42Q,d2WiderTransfer121S1,d2WiderTransfer121Lo,d2WiderTransfer121Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer121C1 d2WiderTransfer121S1 d2Log42Q d2Log42Lo d2Log42Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log42Bounds
  have har : (((weightedUpper d2WiderTransfer121C0 d2Log132Lo d2Log132Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer121C1 d2Log42Lo d2Log42Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer121Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer121Arithmetic
  linarith
#print axioms d2WiderTransfer121Arithmetic
#print axioms d2WiderTransfer121Bound
def d2WiderTransfer122Lo : ℚ := (d2LitsNearWiderTransfers015.q2 (1327746417) 1 (-31))
def d2WiderTransfer122Hi : ℚ := (d2LitsNearWiderTransfers015.q2 (664712069) 1 (-30))
def d2WiderTransfer122Cap : ℚ := (d2LitsNearWiderTransfers015.q2 (61347528822902331459) 1 (-75))
def d2WiderTransfer122C0 : ℚ := (d2LitsNearWiderTransfers015.q2 (1) 25 (-4))
def d2WiderTransfer122S0 : ℚ := (d2LitsNearWiderTransfers015.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer122Arithmetic : weightedUpper d2WiderTransfer122C0 d2Log133Lo d2Log133Hi ≤ d2WiderTransfer122Cap := by decide +kernel
theorem d2WiderTransfer122Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer122Lo:ℚ):ℝ) ((d2WiderTransfer122Hi:ℚ):ℝ), ((d2WiderTransfer122C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer122S0:ℚ):ℝ)| ≤ ((d2WiderTransfer122Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer122S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer122S0,d2WiderTransfer122Lo,d2WiderTransfer122Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer122C0 then |x-((d2WiderTransfer122S0:ℚ):ℝ)| ≤ ((d2Log133Q:ℚ):ℝ) else ((d2Log133Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer122S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer122S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer122S0,d2WiderTransfer122Lo,d2WiderTransfer122Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer122C0,d2Log133Q,d2WiderTransfer122S0,d2WiderTransfer122Lo,d2WiderTransfer122Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer122C0 d2WiderTransfer122S0 d2Log133Q d2Log133Lo d2Log133Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log133Bounds
  have har : (((weightedUpper d2WiderTransfer122C0 d2Log133Lo d2Log133Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer122Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer122Arithmetic
  linarith
#print axioms d2WiderTransfer122Arithmetic
#print axioms d2WiderTransfer122Bound
def d2WiderTransfer123Lo : ℚ := (d2LitsNearWiderTransfers015.q2 (1327746417) 1 (-31))
def d2WiderTransfer123Hi : ℚ := (d2LitsNearWiderTransfers015.q2 (664712069) 1 (-30))
def d2WiderTransfer123Cap : ℚ := (d2LitsNearWiderTransfers015.q2 (100419409092769060931) 1 (-75))
def d2WiderTransfer123C0 : ℚ := (d2LitsNearWiderTransfers015.q2 (1) 275 (-4))
def d2WiderTransfer123S0 : ℚ := (d2LitsNearWiderTransfers015.q2 (-1) 1 (0))
def d2WiderTransfer123C1 : ℚ := (d2LitsNearWiderTransfers015.q2 (-1) 55 (-3))
def d2WiderTransfer123S1 : ℚ := (d2LitsNearWiderTransfers015.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer123Arithmetic : weightedUpper d2WiderTransfer123C0 d2Log133Lo d2Log133Hi + weightedUpper d2WiderTransfer123C1 d2Log41Lo d2Log41Hi ≤ d2WiderTransfer123Cap := by decide +kernel
theorem d2WiderTransfer123Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer123Lo:ℚ):ℝ) ((d2WiderTransfer123Hi:ℚ):ℝ), ((d2WiderTransfer123C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer123S0:ℚ):ℝ)| + ((d2WiderTransfer123C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer123S1:ℚ):ℝ)| ≤ ((d2WiderTransfer123Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer123S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer123S0,d2WiderTransfer123Lo,d2WiderTransfer123Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer123C0 then |x-((d2WiderTransfer123S0:ℚ):ℝ)| ≤ ((d2Log133Q:ℚ):ℝ) else ((d2Log133Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer123S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer123S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer123S0,d2WiderTransfer123Lo,d2WiderTransfer123Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer123C0,d2Log133Q,d2WiderTransfer123S0,d2WiderTransfer123Lo,d2WiderTransfer123Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer123C0 d2WiderTransfer123S0 d2Log133Q d2Log133Lo d2Log133Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log133Bounds
  have hn1 : x-((d2WiderTransfer123S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer123S1,d2WiderTransfer123Lo,d2WiderTransfer123Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer123C1 then |x-((d2WiderTransfer123S1:ℚ):ℝ)| ≤ ((d2Log41Q:ℚ):ℝ) else ((d2Log41Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer123S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer123S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer123S1,d2WiderTransfer123Lo,d2WiderTransfer123Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer123C1,d2Log41Q,d2WiderTransfer123S1,d2WiderTransfer123Lo,d2WiderTransfer123Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer123C1 d2WiderTransfer123S1 d2Log41Q d2Log41Lo d2Log41Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log41Bounds
  have har : (((weightedUpper d2WiderTransfer123C0 d2Log133Lo d2Log133Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer123C1 d2Log41Lo d2Log41Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer123Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer123Arithmetic
  linarith
#print axioms d2WiderTransfer123Arithmetic
#print axioms d2WiderTransfer123Bound
def d2WiderTransfer124Lo : ℚ := (d2LitsNearWiderTransfers015.q2 (1327746417) 1 (-31))
def d2WiderTransfer124Hi : ℚ := (d2LitsNearWiderTransfers015.q2 (664712069) 1 (-30))
def d2WiderTransfer124Cap : ℚ := (d2LitsNearWiderTransfers015.q2 (576140099418486577219) 1 (-75))
def d2WiderTransfer124C0 : ℚ := (d2LitsNearWiderTransfers015.q2 (1) 1 (-5))
def d2WiderTransfer124S0 : ℚ := (d2LitsNearWiderTransfers015.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer124Arithmetic : weightedUpper d2WiderTransfer124C0 d2Log133Lo d2Log133Hi ≤ d2WiderTransfer124Cap := by decide +kernel
theorem d2WiderTransfer124Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer124Lo:ℚ):ℝ) ((d2WiderTransfer124Hi:ℚ):ℝ), ((d2WiderTransfer124C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer124S0:ℚ):ℝ)| ≤ ((d2WiderTransfer124Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer124S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer124S0,d2WiderTransfer124Lo,d2WiderTransfer124Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer124C0 then |x-((d2WiderTransfer124S0:ℚ):ℝ)| ≤ ((d2Log133Q:ℚ):ℝ) else ((d2Log133Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer124S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer124S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer124S0,d2WiderTransfer124Lo,d2WiderTransfer124Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer124C0,d2Log133Q,d2WiderTransfer124S0,d2WiderTransfer124Lo,d2WiderTransfer124Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer124C0 d2WiderTransfer124S0 d2Log133Q d2Log133Lo d2Log133Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log133Bounds
  have har : (((weightedUpper d2WiderTransfer124C0 d2Log133Lo d2Log133Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer124Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer124Arithmetic
  linarith
#print axioms d2WiderTransfer124Arithmetic
#print axioms d2WiderTransfer124Bound
def d2WiderTransfer125Lo : ℚ := (d2LitsNearWiderTransfers015.q2 (1327746417) 1 (-31))
def d2WiderTransfer125Hi : ℚ := (d2LitsNearWiderTransfers015.q2 (664712069) 1 (-30))
def d2WiderTransfer125Cap : ℚ := (d2LitsNearWiderTransfers015.q2 (1087541265740096182339) 1 (-75))
def d2WiderTransfer125C0 : ℚ := (d2LitsNearWiderTransfers015.q2 (1) 11 (-5))
def d2WiderTransfer125S0 : ℚ := (d2LitsNearWiderTransfers015.q2 (-1) 1 (0))
def d2WiderTransfer125C1 : ℚ := (d2LitsNearWiderTransfers015.q2 (-5) 11 (-4))
def d2WiderTransfer125S1 : ℚ := (d2LitsNearWiderTransfers015.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer125Arithmetic : weightedUpper d2WiderTransfer125C0 d2Log133Lo d2Log133Hi + weightedUpper d2WiderTransfer125C1 d2Log41Lo d2Log41Hi ≤ d2WiderTransfer125Cap := by decide +kernel
theorem d2WiderTransfer125Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer125Lo:ℚ):ℝ) ((d2WiderTransfer125Hi:ℚ):ℝ), ((d2WiderTransfer125C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer125S0:ℚ):ℝ)| + ((d2WiderTransfer125C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer125S1:ℚ):ℝ)| ≤ ((d2WiderTransfer125Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer125S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer125S0,d2WiderTransfer125Lo,d2WiderTransfer125Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer125C0 then |x-((d2WiderTransfer125S0:ℚ):ℝ)| ≤ ((d2Log133Q:ℚ):ℝ) else ((d2Log133Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer125S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer125S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer125S0,d2WiderTransfer125Lo,d2WiderTransfer125Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer125C0,d2Log133Q,d2WiderTransfer125S0,d2WiderTransfer125Lo,d2WiderTransfer125Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer125C0 d2WiderTransfer125S0 d2Log133Q d2Log133Lo d2Log133Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log133Bounds
  have hn1 : x-((d2WiderTransfer125S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer125S1,d2WiderTransfer125Lo,d2WiderTransfer125Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer125C1 then |x-((d2WiderTransfer125S1:ℚ):ℝ)| ≤ ((d2Log41Q:ℚ):ℝ) else ((d2Log41Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer125S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer125S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer125S1,d2WiderTransfer125Lo,d2WiderTransfer125Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer125C1,d2Log41Q,d2WiderTransfer125S1,d2WiderTransfer125Lo,d2WiderTransfer125Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer125C1 d2WiderTransfer125S1 d2Log41Q d2Log41Lo d2Log41Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log41Bounds
  have har : (((weightedUpper d2WiderTransfer125C0 d2Log133Lo d2Log133Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer125C1 d2Log41Lo d2Log41Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer125Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer125Arithmetic
  linarith
#print axioms d2WiderTransfer125Arithmetic
#print axioms d2WiderTransfer125Bound
def d2WiderTransfer126Lo : ℚ := (d2LitsNearWiderTransfers015.q2 (664712069) 1 (-30))
def d2WiderTransfer126Hi : ℚ := (d2LitsNearWiderTransfers015.q2 (1331101859) 1 (-31))
def d2WiderTransfer126Cap : ℚ := (d2LitsNearWiderTransfers015.q2 (7950334446886927103) 1 (-72))
def d2WiderTransfer126C0 : ℚ := (d2LitsNearWiderTransfers015.q2 (1) 25 (-4))
def d2WiderTransfer126S0 : ℚ := (d2LitsNearWiderTransfers015.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer126Arithmetic : weightedUpper d2WiderTransfer126C0 d2Log134Lo d2Log134Hi ≤ d2WiderTransfer126Cap := by decide +kernel
theorem d2WiderTransfer126Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer126Lo:ℚ):ℝ) ((d2WiderTransfer126Hi:ℚ):ℝ), ((d2WiderTransfer126C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer126S0:ℚ):ℝ)| ≤ ((d2WiderTransfer126Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer126S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer126S0,d2WiderTransfer126Lo,d2WiderTransfer126Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer126C0 then |x-((d2WiderTransfer126S0:ℚ):ℝ)| ≤ ((d2Log134Q:ℚ):ℝ) else ((d2Log134Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer126S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer126S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer126S0,d2WiderTransfer126Lo,d2WiderTransfer126Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer126C0,d2Log134Q,d2WiderTransfer126S0,d2WiderTransfer126Lo,d2WiderTransfer126Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer126C0 d2WiderTransfer126S0 d2Log134Q d2Log134Lo d2Log134Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log134Bounds
  have har : (((weightedUpper d2WiderTransfer126C0 d2Log134Lo d2Log134Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer126Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer126Arithmetic
  linarith
#print axioms d2WiderTransfer126Arithmetic
#print axioms d2WiderTransfer126Bound
def d2WiderTransfer127Lo : ℚ := (d2LitsNearWiderTransfers015.q2 (664712069) 1 (-30))
def d2WiderTransfer127Hi : ℚ := (d2LitsNearWiderTransfers015.q2 (1331101859) 1 (-31))
def d2WiderTransfer127Cap : ℚ := (d2LitsNearWiderTransfers015.q2 (12834319480620268287) 1 (-72))
def d2WiderTransfer127C0 : ℚ := (d2LitsNearWiderTransfers015.q2 (1) 275 (-4))
def d2WiderTransfer127S0 : ℚ := (d2LitsNearWiderTransfers015.q2 (-1) 1 (0))
def d2WiderTransfer127C1 : ℚ := (d2LitsNearWiderTransfers015.q2 (-1) 55 (-3))
def d2WiderTransfer127S1 : ℚ := (d2LitsNearWiderTransfers015.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer127Arithmetic : weightedUpper d2WiderTransfer127C0 d2Log134Lo d2Log134Hi + weightedUpper d2WiderTransfer127C1 d2Log40Lo d2Log40Hi ≤ d2WiderTransfer127Cap := by decide +kernel
theorem d2WiderTransfer127Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer127Lo:ℚ):ℝ) ((d2WiderTransfer127Hi:ℚ):ℝ), ((d2WiderTransfer127C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer127S0:ℚ):ℝ)| + ((d2WiderTransfer127C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer127S1:ℚ):ℝ)| ≤ ((d2WiderTransfer127Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer127S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer127S0,d2WiderTransfer127Lo,d2WiderTransfer127Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer127C0 then |x-((d2WiderTransfer127S0:ℚ):ℝ)| ≤ ((d2Log134Q:ℚ):ℝ) else ((d2Log134Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer127S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer127S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer127S0,d2WiderTransfer127Lo,d2WiderTransfer127Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer127C0,d2Log134Q,d2WiderTransfer127S0,d2WiderTransfer127Lo,d2WiderTransfer127Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer127C0 d2WiderTransfer127S0 d2Log134Q d2Log134Lo d2Log134Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log134Bounds
  have hn1 : x-((d2WiderTransfer127S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer127S1,d2WiderTransfer127Lo,d2WiderTransfer127Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer127C1 then |x-((d2WiderTransfer127S1:ℚ):ℝ)| ≤ ((d2Log40Q:ℚ):ℝ) else ((d2Log40Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer127S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer127S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer127S1,d2WiderTransfer127Lo,d2WiderTransfer127Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers015.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer127C1,d2Log40Q,d2WiderTransfer127S1,d2WiderTransfer127Lo,d2WiderTransfer127Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer127C1 d2WiderTransfer127S1 d2Log40Q d2Log40Lo d2Log40Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log40Bounds
  have har : (((weightedUpper d2WiderTransfer127C0 d2Log134Lo d2Log134Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer127C1 d2Log40Lo d2Log40Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer127Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer127Arithmetic
  linarith
#print axioms d2WiderTransfer127Arithmetic
#print axioms d2WiderTransfer127Bound
end CatalanMeasure.GenD.Signed.Data.Cells

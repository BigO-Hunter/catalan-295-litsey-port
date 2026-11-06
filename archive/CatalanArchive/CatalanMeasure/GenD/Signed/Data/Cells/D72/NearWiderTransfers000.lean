module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers000
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers000
open D72.LogTransfer
def d2WiderTransfer0Lo : ℚ := (d2LitsNearWiderTransfers000.q2 (98749) 15625 (-6))
def d2WiderTransfer0Hi : ℚ := (d2LitsNearWiderTransfers000.q2 (828367) 1 (-23))
def d2WiderTransfer0Cap : ℚ := (d2LitsNearWiderTransfers000.q2 (648894057) 1 (-39))
def d2WiderTransfer0C0 : ℚ := (d2LitsNearWiderTransfers000.q2 (1) 25 (-4))
def d2WiderTransfer0S0 : ℚ := (d2LitsNearWiderTransfers000.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer0Arithmetic : weightedUpper d2WiderTransfer0C0 d2Log88Lo d2Log88Hi ≤ d2WiderTransfer0Cap := by decide +kernel
theorem d2WiderTransfer0Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer0Lo:ℚ):ℝ) ((d2WiderTransfer0Hi:ℚ):ℝ), ((d2WiderTransfer0C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer0S0:ℚ):ℝ)| ≤ ((d2WiderTransfer0Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer0S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer0S0,d2WiderTransfer0Lo,d2WiderTransfer0Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer0C0 then |x-((d2WiderTransfer0S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer0S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer0S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer0S0,d2WiderTransfer0Lo,d2WiderTransfer0Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer0C0,d2Log88Q,d2WiderTransfer0S0,d2WiderTransfer0Lo,d2WiderTransfer0Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer0C0 d2WiderTransfer0S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have har : (((weightedUpper d2WiderTransfer0C0 d2Log88Lo d2Log88Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer0Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer0Arithmetic
  linarith
#print axioms d2WiderTransfer0Arithmetic
#print axioms d2WiderTransfer0Bound
def d2WiderTransfer1Lo : ℚ := (d2LitsNearWiderTransfers000.q2 (98749) 15625 (-6))
def d2WiderTransfer1Hi : ℚ := (d2LitsNearWiderTransfers000.q2 (828367) 1 (-23))
def d2WiderTransfer1Cap : ℚ := (d2LitsNearWiderTransfers000.q2 (2432512853) 1 (-40))
def d2WiderTransfer1C0 : ℚ := (d2LitsNearWiderTransfers000.q2 (1) 275 (-4))
def d2WiderTransfer1S0 : ℚ := (d2LitsNearWiderTransfers000.q2 (-1) 1 (0))
def d2WiderTransfer1C1 : ℚ := (d2LitsNearWiderTransfers000.q2 (-1) 55 (-3))
def d2WiderTransfer1S1 : ℚ := (d2LitsNearWiderTransfers000.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer1Arithmetic : weightedUpper d2WiderTransfer1C0 d2Log88Lo d2Log88Hi + weightedUpper d2WiderTransfer1C1 d2Log86Lo d2Log86Hi ≤ d2WiderTransfer1Cap := by decide +kernel
theorem d2WiderTransfer1Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer1Lo:ℚ):ℝ) ((d2WiderTransfer1Hi:ℚ):ℝ), ((d2WiderTransfer1C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer1S0:ℚ):ℝ)| + ((d2WiderTransfer1C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer1S1:ℚ):ℝ)| ≤ ((d2WiderTransfer1Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer1S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer1S0,d2WiderTransfer1Lo,d2WiderTransfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer1C0 then |x-((d2WiderTransfer1S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer1S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer1S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer1S0,d2WiderTransfer1Lo,d2WiderTransfer1Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer1C0,d2Log88Q,d2WiderTransfer1S0,d2WiderTransfer1Lo,d2WiderTransfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer1C0 d2WiderTransfer1S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have hn1 : x-((d2WiderTransfer1S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer1S1,d2WiderTransfer1Lo,d2WiderTransfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer1C1 then |x-((d2WiderTransfer1S1:ℚ):ℝ)| ≤ ((d2Log86Q:ℚ):ℝ) else ((d2Log86Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer1S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer1S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer1S1,d2WiderTransfer1Lo,d2WiderTransfer1Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer1C1,d2Log86Q,d2WiderTransfer1S1,d2WiderTransfer1Lo,d2WiderTransfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer1C1 d2WiderTransfer1S1 d2Log86Q d2Log86Lo d2Log86Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log86Bounds
  have har : (((weightedUpper d2WiderTransfer1C0 d2Log88Lo d2Log88Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer1C1 d2Log86Lo d2Log86Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer1Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer1Arithmetic
  linarith
#print axioms d2WiderTransfer1Arithmetic
#print axioms d2WiderTransfer1Bound
def d2WiderTransfer2Lo : ℚ := (d2LitsNearWiderTransfers000.q2 (828367) 1 (-23))
def d2WiderTransfer2Hi : ℚ := (d2LitsNearWiderTransfers000.q2 (8304657) 1 (-26))
def d2WiderTransfer2Cap : ℚ := (d2LitsNearWiderTransfers000.q2 (648894057) 1 (-39))
def d2WiderTransfer2C0 : ℚ := (d2LitsNearWiderTransfers000.q2 (1) 25 (-4))
def d2WiderTransfer2S0 : ℚ := (d2LitsNearWiderTransfers000.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer2Arithmetic : weightedUpper d2WiderTransfer2C0 d2Log95Lo d2Log95Hi ≤ d2WiderTransfer2Cap := by decide +kernel
theorem d2WiderTransfer2Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer2Lo:ℚ):ℝ) ((d2WiderTransfer2Hi:ℚ):ℝ), ((d2WiderTransfer2C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer2S0:ℚ):ℝ)| ≤ ((d2WiderTransfer2Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer2S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer2S0,d2WiderTransfer2Lo,d2WiderTransfer2Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer2C0 then |x-((d2WiderTransfer2S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer2S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer2S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer2S0,d2WiderTransfer2Lo,d2WiderTransfer2Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer2C0,d2Log95Q,d2WiderTransfer2S0,d2WiderTransfer2Lo,d2WiderTransfer2Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer2C0 d2WiderTransfer2S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have har : (((weightedUpper d2WiderTransfer2C0 d2Log95Lo d2Log95Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer2Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer2Arithmetic
  linarith
#print axioms d2WiderTransfer2Arithmetic
#print axioms d2WiderTransfer2Bound
def d2WiderTransfer3Lo : ℚ := (d2LitsNearWiderTransfers000.q2 (828367) 1 (-23))
def d2WiderTransfer3Hi : ℚ := (d2LitsNearWiderTransfers000.q2 (8304657) 1 (-26))
def d2WiderTransfer3Cap : ℚ := (d2LitsNearWiderTransfers000.q2 (2432512853) 1 (-40))
def d2WiderTransfer3C0 : ℚ := (d2LitsNearWiderTransfers000.q2 (1) 275 (-4))
def d2WiderTransfer3S0 : ℚ := (d2LitsNearWiderTransfers000.q2 (-1) 1 (0))
def d2WiderTransfer3C1 : ℚ := (d2LitsNearWiderTransfers000.q2 (-1) 55 (-3))
def d2WiderTransfer3S1 : ℚ := (d2LitsNearWiderTransfers000.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer3Arithmetic : weightedUpper d2WiderTransfer3C0 d2Log95Lo d2Log95Hi + weightedUpper d2WiderTransfer3C1 d2Log79Lo d2Log79Hi ≤ d2WiderTransfer3Cap := by decide +kernel
theorem d2WiderTransfer3Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer3Lo:ℚ):ℝ) ((d2WiderTransfer3Hi:ℚ):ℝ), ((d2WiderTransfer3C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer3S0:ℚ):ℝ)| + ((d2WiderTransfer3C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer3S1:ℚ):ℝ)| ≤ ((d2WiderTransfer3Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer3S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer3S0,d2WiderTransfer3Lo,d2WiderTransfer3Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer3C0 then |x-((d2WiderTransfer3S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer3S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer3S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer3S0,d2WiderTransfer3Lo,d2WiderTransfer3Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer3C0,d2Log95Q,d2WiderTransfer3S0,d2WiderTransfer3Lo,d2WiderTransfer3Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer3C0 d2WiderTransfer3S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have hn1 : x-((d2WiderTransfer3S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer3S1,d2WiderTransfer3Lo,d2WiderTransfer3Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer3C1 then |x-((d2WiderTransfer3S1:ℚ):ℝ)| ≤ ((d2Log79Q:ℚ):ℝ) else ((d2Log79Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer3S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer3S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer3S1,d2WiderTransfer3Lo,d2WiderTransfer3Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer3C1,d2Log79Q,d2WiderTransfer3S1,d2WiderTransfer3Lo,d2WiderTransfer3Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer3C1 d2WiderTransfer3S1 d2Log79Q d2Log79Lo d2Log79Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log79Bounds
  have har : (((weightedUpper d2WiderTransfer3C0 d2Log95Lo d2Log95Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer3C1 d2Log79Lo d2Log79Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer3Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer3Arithmetic
  linarith
#print axioms d2WiderTransfer3Arithmetic
#print axioms d2WiderTransfer3Bound
def d2WiderTransfer4Lo : ℚ := (d2LitsNearWiderTransfers000.q2 (8304657) 1 (-26))
def d2WiderTransfer4Hi : ℚ := (d2LitsNearWiderTransfers000.q2 (4991189) 1 (-25))
def d2WiderTransfer4Cap : ℚ := (d2LitsNearWiderTransfers000.q2 (648894057) 1 (-39))
def d2WiderTransfer4C0 : ℚ := (d2LitsNearWiderTransfers000.q2 (1) 25 (-4))
def d2WiderTransfer4S0 : ℚ := (d2LitsNearWiderTransfers000.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer4Arithmetic : weightedUpper d2WiderTransfer4C0 d2Log99Lo d2Log99Hi ≤ d2WiderTransfer4Cap := by decide +kernel
theorem d2WiderTransfer4Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer4Lo:ℚ):ℝ) ((d2WiderTransfer4Hi:ℚ):ℝ), ((d2WiderTransfer4C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer4S0:ℚ):ℝ)| ≤ ((d2WiderTransfer4Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer4S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer4S0,d2WiderTransfer4Lo,d2WiderTransfer4Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer4C0 then |x-((d2WiderTransfer4S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer4S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer4S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer4S0,d2WiderTransfer4Lo,d2WiderTransfer4Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer4C0,d2Log99Q,d2WiderTransfer4S0,d2WiderTransfer4Lo,d2WiderTransfer4Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer4C0 d2WiderTransfer4S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have har : (((weightedUpper d2WiderTransfer4C0 d2Log99Lo d2Log99Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer4Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer4Arithmetic
  linarith
#print axioms d2WiderTransfer4Arithmetic
#print axioms d2WiderTransfer4Bound
def d2WiderTransfer5Lo : ℚ := (d2LitsNearWiderTransfers000.q2 (8304657) 1 (-26))
def d2WiderTransfer5Hi : ℚ := (d2LitsNearWiderTransfers000.q2 (4991189) 1 (-25))
def d2WiderTransfer5Cap : ℚ := (d2LitsNearWiderTransfers000.q2 (2432512853) 1 (-40))
def d2WiderTransfer5C0 : ℚ := (d2LitsNearWiderTransfers000.q2 (1) 275 (-4))
def d2WiderTransfer5S0 : ℚ := (d2LitsNearWiderTransfers000.q2 (-1) 1 (0))
def d2WiderTransfer5C1 : ℚ := (d2LitsNearWiderTransfers000.q2 (-1) 55 (-3))
def d2WiderTransfer5S1 : ℚ := (d2LitsNearWiderTransfers000.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer5Arithmetic : weightedUpper d2WiderTransfer5C0 d2Log99Lo d2Log99Hi + weightedUpper d2WiderTransfer5C1 d2Log75Lo d2Log75Hi ≤ d2WiderTransfer5Cap := by decide +kernel
theorem d2WiderTransfer5Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer5Lo:ℚ):ℝ) ((d2WiderTransfer5Hi:ℚ):ℝ), ((d2WiderTransfer5C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer5S0:ℚ):ℝ)| + ((d2WiderTransfer5C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer5S1:ℚ):ℝ)| ≤ ((d2WiderTransfer5Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer5S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer5S0,d2WiderTransfer5Lo,d2WiderTransfer5Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer5C0 then |x-((d2WiderTransfer5S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer5S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer5S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer5S0,d2WiderTransfer5Lo,d2WiderTransfer5Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer5C0,d2Log99Q,d2WiderTransfer5S0,d2WiderTransfer5Lo,d2WiderTransfer5Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer5C0 d2WiderTransfer5S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have hn1 : x-((d2WiderTransfer5S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer5S1,d2WiderTransfer5Lo,d2WiderTransfer5Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer5C1 then |x-((d2WiderTransfer5S1:ℚ):ℝ)| ≤ ((d2Log75Q:ℚ):ℝ) else ((d2Log75Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer5S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer5S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer5S1,d2WiderTransfer5Lo,d2WiderTransfer5Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer5C1,d2Log75Q,d2WiderTransfer5S1,d2WiderTransfer5Lo,d2WiderTransfer5Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer5C1 d2WiderTransfer5S1 d2Log75Q d2Log75Lo d2Log75Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log75Bounds
  have har : (((weightedUpper d2WiderTransfer5C0 d2Log99Lo d2Log99Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer5C1 d2Log75Lo d2Log75Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer5Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer5Arithmetic
  linarith
#print axioms d2WiderTransfer5Arithmetic
#print axioms d2WiderTransfer5Bound
def d2WiderTransfer6Lo : ℚ := (d2LitsNearWiderTransfers000.q2 (4991189) 1 (-25))
def d2WiderTransfer6Hi : ℚ := (d2LitsNearWiderTransfers000.q2 (3334455) 1 (-24))
def d2WiderTransfer6Cap : ℚ := (d2LitsNearWiderTransfers000.q2 (648894057) 1 (-39))
def d2WiderTransfer6C0 : ℚ := (d2LitsNearWiderTransfers000.q2 (1) 25 (-4))
def d2WiderTransfer6S0 : ℚ := (d2LitsNearWiderTransfers000.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer6Arithmetic : weightedUpper d2WiderTransfer6C0 d2Log106Lo d2Log106Hi ≤ d2WiderTransfer6Cap := by decide +kernel
theorem d2WiderTransfer6Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer6Lo:ℚ):ℝ) ((d2WiderTransfer6Hi:ℚ):ℝ), ((d2WiderTransfer6C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer6S0:ℚ):ℝ)| ≤ ((d2WiderTransfer6Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer6S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer6S0,d2WiderTransfer6Lo,d2WiderTransfer6Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer6C0 then |x-((d2WiderTransfer6S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer6S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer6S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer6S0,d2WiderTransfer6Lo,d2WiderTransfer6Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer6C0,d2Log106Q,d2WiderTransfer6S0,d2WiderTransfer6Lo,d2WiderTransfer6Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer6C0 d2WiderTransfer6S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have har : (((weightedUpper d2WiderTransfer6C0 d2Log106Lo d2Log106Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer6Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer6Arithmetic
  linarith
#print axioms d2WiderTransfer6Arithmetic
#print axioms d2WiderTransfer6Bound
def d2WiderTransfer7Lo : ℚ := (d2LitsNearWiderTransfers000.q2 (4991189) 1 (-25))
def d2WiderTransfer7Hi : ℚ := (d2LitsNearWiderTransfers000.q2 (3334455) 1 (-24))
def d2WiderTransfer7Cap : ℚ := (d2LitsNearWiderTransfers000.q2 (2432512853) 1 (-40))
def d2WiderTransfer7C0 : ℚ := (d2LitsNearWiderTransfers000.q2 (1) 275 (-4))
def d2WiderTransfer7S0 : ℚ := (d2LitsNearWiderTransfers000.q2 (-1) 1 (0))
def d2WiderTransfer7C1 : ℚ := (d2LitsNearWiderTransfers000.q2 (-1) 55 (-3))
def d2WiderTransfer7S1 : ℚ := (d2LitsNearWiderTransfers000.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer7Arithmetic : weightedUpper d2WiderTransfer7C0 d2Log106Lo d2Log106Hi + weightedUpper d2WiderTransfer7C1 d2Log68Lo d2Log68Hi ≤ d2WiderTransfer7Cap := by decide +kernel
theorem d2WiderTransfer7Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer7Lo:ℚ):ℝ) ((d2WiderTransfer7Hi:ℚ):ℝ), ((d2WiderTransfer7C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer7S0:ℚ):ℝ)| + ((d2WiderTransfer7C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer7S1:ℚ):ℝ)| ≤ ((d2WiderTransfer7Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer7S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer7S0,d2WiderTransfer7Lo,d2WiderTransfer7Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer7C0 then |x-((d2WiderTransfer7S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer7S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer7S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer7S0,d2WiderTransfer7Lo,d2WiderTransfer7Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer7C0,d2Log106Q,d2WiderTransfer7S0,d2WiderTransfer7Lo,d2WiderTransfer7Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer7C0 d2WiderTransfer7S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have hn1 : x-((d2WiderTransfer7S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer7S1,d2WiderTransfer7Lo,d2WiderTransfer7Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer7C1 then |x-((d2WiderTransfer7S1:ℚ):ℝ)| ≤ ((d2Log68Q:ℚ):ℝ) else ((d2Log68Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer7S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer7S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer7S1,d2WiderTransfer7Lo,d2WiderTransfer7Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer7C1,d2Log68Q,d2WiderTransfer7S1,d2WiderTransfer7Lo,d2WiderTransfer7Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer7C1 d2WiderTransfer7S1 d2Log68Q d2Log68Lo d2Log68Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log68Bounds
  have har : (((weightedUpper d2WiderTransfer7C0 d2Log106Lo d2Log106Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer7C1 d2Log68Lo d2Log68Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer7Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer7Arithmetic
  linarith
#print axioms d2WiderTransfer7Arithmetic
#print axioms d2WiderTransfer7Bound
end CatalanMeasure.GenD.Signed.Data.Cells

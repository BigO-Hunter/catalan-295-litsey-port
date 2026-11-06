module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers025
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers025
open D72.LogTransfer
def d2WiderTransfer200Lo : ℚ := (d2LitsNearWiderTransfers025.q2 (343261221) 1 (-29))
def d2WiderTransfer200Hi : ℚ := (d2LitsNearWiderTransfers025.q2 (172469471) 1 (-28))
def d2WiderTransfer200Cap : ℚ := (d2LitsNearWiderTransfers025.q2 (20666709428918369581081) 1 (-80))
def d2WiderTransfer200C0 : ℚ := (d2LitsNearWiderTransfers025.q2 (1) 1 (-5))
def d2WiderTransfer200S0 : ℚ := (d2LitsNearWiderTransfers025.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer200Arithmetic : weightedUpper d2WiderTransfer200C0 d2Log160Lo d2Log160Hi ≤ d2WiderTransfer200Cap := by decide +kernel
theorem d2WiderTransfer200Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer200Lo:ℚ):ℝ) ((d2WiderTransfer200Hi:ℚ):ℝ), ((d2WiderTransfer200C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer200S0:ℚ):ℝ)| ≤ ((d2WiderTransfer200Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer200S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer200S0,d2WiderTransfer200Lo,d2WiderTransfer200Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer200C0 then |x-((d2WiderTransfer200S0:ℚ):ℝ)| ≤ ((d2Log160Q:ℚ):ℝ) else ((d2Log160Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer200S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer200S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer200S0,d2WiderTransfer200Lo,d2WiderTransfer200Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer200C0,d2Log160Q,d2WiderTransfer200S0,d2WiderTransfer200Lo,d2WiderTransfer200Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer200C0 d2WiderTransfer200S0 d2Log160Q d2Log160Lo d2Log160Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log160Bounds
  have har : (((weightedUpper d2WiderTransfer200C0 d2Log160Lo d2Log160Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer200Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer200Arithmetic
  linarith
#print axioms d2WiderTransfer200Arithmetic
#print axioms d2WiderTransfer200Bound
def d2WiderTransfer201Lo : ℚ := (d2LitsNearWiderTransfers025.q2 (343261221) 1 (-29))
def d2WiderTransfer201Hi : ℚ := (d2LitsNearWiderTransfers025.q2 (172469471) 1 (-28))
def d2WiderTransfer201Cap : ℚ := (d2LitsNearWiderTransfers025.q2 (37031546751209876944921) 1 (-80))
def d2WiderTransfer201C0 : ℚ := (d2LitsNearWiderTransfers025.q2 (1) 11 (-5))
def d2WiderTransfer201S0 : ℚ := (d2LitsNearWiderTransfers025.q2 (-1) 1 (0))
def d2WiderTransfer201C1 : ℚ := (d2LitsNearWiderTransfers025.q2 (-5) 11 (-4))
def d2WiderTransfer201S1 : ℚ := (d2LitsNearWiderTransfers025.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer201Arithmetic : weightedUpper d2WiderTransfer201C0 d2Log160Lo d2Log160Hi + weightedUpper d2WiderTransfer201C1 d2Log14Lo d2Log14Hi ≤ d2WiderTransfer201Cap := by decide +kernel
theorem d2WiderTransfer201Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer201Lo:ℚ):ℝ) ((d2WiderTransfer201Hi:ℚ):ℝ), ((d2WiderTransfer201C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer201S0:ℚ):ℝ)| + ((d2WiderTransfer201C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer201S1:ℚ):ℝ)| ≤ ((d2WiderTransfer201Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer201S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer201S0,d2WiderTransfer201Lo,d2WiderTransfer201Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer201C0 then |x-((d2WiderTransfer201S0:ℚ):ℝ)| ≤ ((d2Log160Q:ℚ):ℝ) else ((d2Log160Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer201S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer201S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer201S0,d2WiderTransfer201Lo,d2WiderTransfer201Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer201C0,d2Log160Q,d2WiderTransfer201S0,d2WiderTransfer201Lo,d2WiderTransfer201Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer201C0 d2WiderTransfer201S0 d2Log160Q d2Log160Lo d2Log160Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log160Bounds
  have hn1 : x-((d2WiderTransfer201S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer201S1,d2WiderTransfer201Lo,d2WiderTransfer201Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer201C1 then |x-((d2WiderTransfer201S1:ℚ):ℝ)| ≤ ((d2Log14Q:ℚ):ℝ) else ((d2Log14Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer201S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer201S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer201S1,d2WiderTransfer201Lo,d2WiderTransfer201Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer201C1,d2Log14Q,d2WiderTransfer201S1,d2WiderTransfer201Lo,d2WiderTransfer201Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer201C1 d2WiderTransfer201S1 d2Log14Q d2Log14Lo d2Log14Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log14Bounds
  have har : (((weightedUpper d2WiderTransfer201C0 d2Log160Lo d2Log160Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer201C1 d2Log14Lo d2Log14Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer201Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer201Arithmetic
  linarith
#print axioms d2WiderTransfer201Arithmetic
#print axioms d2WiderTransfer201Bound
def d2WiderTransfer202Lo : ℚ := (d2LitsNearWiderTransfers025.q2 (172469471) 1 (-28))
def d2WiderTransfer202Hi : ℚ := (d2LitsNearWiderTransfers025.q2 (21768399) 1 (-25))
def d2WiderTransfer202Cap : ℚ := (d2LitsNearWiderTransfers025.q2 (4812127375716014614645) 1 (-80))
def d2WiderTransfer202C0 : ℚ := (d2LitsNearWiderTransfers025.q2 (1) 25 (-4))
def d2WiderTransfer202S0 : ℚ := (d2LitsNearWiderTransfers025.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer202Arithmetic : weightedUpper d2WiderTransfer202C0 d2Log162Lo d2Log162Hi ≤ d2WiderTransfer202Cap := by decide +kernel
theorem d2WiderTransfer202Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer202Lo:ℚ):ℝ) ((d2WiderTransfer202Hi:ℚ):ℝ), ((d2WiderTransfer202C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer202S0:ℚ):ℝ)| ≤ ((d2WiderTransfer202Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer202S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer202S0,d2WiderTransfer202Lo,d2WiderTransfer202Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer202C0 then |x-((d2WiderTransfer202S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer202S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer202S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer202S0,d2WiderTransfer202Lo,d2WiderTransfer202Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer202C0,d2Log162Q,d2WiderTransfer202S0,d2WiderTransfer202Lo,d2WiderTransfer202Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer202C0 d2WiderTransfer202S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have har : (((weightedUpper d2WiderTransfer202C0 d2Log162Lo d2Log162Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer202Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer202Arithmetic
  linarith
#print axioms d2WiderTransfer202Arithmetic
#print axioms d2WiderTransfer202Bound
def d2WiderTransfer203Lo : ℚ := (d2LitsNearWiderTransfers025.q2 (172469471) 1 (-28))
def d2WiderTransfer203Hi : ℚ := (d2LitsNearWiderTransfers025.q2 (21768399) 1 (-25))
def d2WiderTransfer203Cap : ℚ := (d2LitsNearWiderTransfers025.q2 (6062427544351749957749) 1 (-80))
def d2WiderTransfer203C0 : ℚ := (d2LitsNearWiderTransfers025.q2 (1) 275 (-4))
def d2WiderTransfer203S0 : ℚ := (d2LitsNearWiderTransfers025.q2 (-1) 1 (0))
def d2WiderTransfer203C1 : ℚ := (d2LitsNearWiderTransfers025.q2 (-1) 55 (-3))
def d2WiderTransfer203S1 : ℚ := (d2LitsNearWiderTransfers025.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer203Arithmetic : weightedUpper d2WiderTransfer203C0 d2Log162Lo d2Log162Hi + weightedUpper d2WiderTransfer203C1 d2Log12Lo d2Log12Hi ≤ d2WiderTransfer203Cap := by decide +kernel
theorem d2WiderTransfer203Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer203Lo:ℚ):ℝ) ((d2WiderTransfer203Hi:ℚ):ℝ), ((d2WiderTransfer203C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer203S0:ℚ):ℝ)| + ((d2WiderTransfer203C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer203S1:ℚ):ℝ)| ≤ ((d2WiderTransfer203Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer203S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer203S0,d2WiderTransfer203Lo,d2WiderTransfer203Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer203C0 then |x-((d2WiderTransfer203S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer203S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer203S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer203S0,d2WiderTransfer203Lo,d2WiderTransfer203Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer203C0,d2Log162Q,d2WiderTransfer203S0,d2WiderTransfer203Lo,d2WiderTransfer203Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer203C0 d2WiderTransfer203S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have hn1 : x-((d2WiderTransfer203S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer203S1,d2WiderTransfer203Lo,d2WiderTransfer203Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer203C1 then |x-((d2WiderTransfer203S1:ℚ):ℝ)| ≤ ((d2Log12Q:ℚ):ℝ) else ((d2Log12Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer203S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer203S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer203S1,d2WiderTransfer203Lo,d2WiderTransfer203Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer203C1,d2Log12Q,d2WiderTransfer203S1,d2WiderTransfer203Lo,d2WiderTransfer203Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer203C1 d2WiderTransfer203S1 d2Log12Q d2Log12Lo d2Log12Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log12Bounds
  have har : (((weightedUpper d2WiderTransfer203C0 d2Log162Lo d2Log162Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer203C1 d2Log12Lo d2Log12Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer203Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer203Arithmetic
  linarith
#print axioms d2WiderTransfer203Arithmetic
#print axioms d2WiderTransfer203Bound
def d2WiderTransfer204Lo : ℚ := (d2LitsNearWiderTransfers025.q2 (172469471) 1 (-28))
def d2WiderTransfer204Hi : ℚ := (d2LitsNearWiderTransfers025.q2 (21768399) 1 (-25))
def d2WiderTransfer204Cap : ℚ := (d2LitsNearWiderTransfers025.q2 (21285489634774710478965) 1 (-80))
def d2WiderTransfer204C0 : ℚ := (d2LitsNearWiderTransfers025.q2 (1) 1 (-5))
def d2WiderTransfer204S0 : ℚ := (d2LitsNearWiderTransfers025.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer204Arithmetic : weightedUpper d2WiderTransfer204C0 d2Log162Lo d2Log162Hi ≤ d2WiderTransfer204Cap := by decide +kernel
theorem d2WiderTransfer204Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer204Lo:ℚ):ℝ) ((d2WiderTransfer204Hi:ℚ):ℝ), ((d2WiderTransfer204C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer204S0:ℚ):ℝ)| ≤ ((d2WiderTransfer204Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer204S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer204S0,d2WiderTransfer204Lo,d2WiderTransfer204Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer204C0 then |x-((d2WiderTransfer204S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer204S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer204S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer204S0,d2WiderTransfer204Lo,d2WiderTransfer204Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer204C0,d2Log162Q,d2WiderTransfer204S0,d2WiderTransfer204Lo,d2WiderTransfer204Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer204C0 d2WiderTransfer204S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have har : (((weightedUpper d2WiderTransfer204C0 d2Log162Lo d2Log162Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer204Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer204Arithmetic
  linarith
#print axioms d2WiderTransfer204Arithmetic
#print axioms d2WiderTransfer204Bound
def d2WiderTransfer205Lo : ℚ := (d2LitsNearWiderTransfers025.q2 (172469471) 1 (-28))
def d2WiderTransfer205Hi : ℚ := (d2LitsNearWiderTransfers025.q2 (21768399) 1 (-25))
def d2WiderTransfer205Cap : ℚ := (d2LitsNearWiderTransfers025.q2 (37650326957066217842805) 1 (-80))
def d2WiderTransfer205C0 : ℚ := (d2LitsNearWiderTransfers025.q2 (1) 11 (-5))
def d2WiderTransfer205S0 : ℚ := (d2LitsNearWiderTransfers025.q2 (-1) 1 (0))
def d2WiderTransfer205C1 : ℚ := (d2LitsNearWiderTransfers025.q2 (-5) 11 (-4))
def d2WiderTransfer205S1 : ℚ := (d2LitsNearWiderTransfers025.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer205Arithmetic : weightedUpper d2WiderTransfer205C0 d2Log162Lo d2Log162Hi + weightedUpper d2WiderTransfer205C1 d2Log12Lo d2Log12Hi ≤ d2WiderTransfer205Cap := by decide +kernel
theorem d2WiderTransfer205Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer205Lo:ℚ):ℝ) ((d2WiderTransfer205Hi:ℚ):ℝ), ((d2WiderTransfer205C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer205S0:ℚ):ℝ)| + ((d2WiderTransfer205C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer205S1:ℚ):ℝ)| ≤ ((d2WiderTransfer205Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer205S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer205S0,d2WiderTransfer205Lo,d2WiderTransfer205Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer205C0 then |x-((d2WiderTransfer205S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer205S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer205S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer205S0,d2WiderTransfer205Lo,d2WiderTransfer205Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer205C0,d2Log162Q,d2WiderTransfer205S0,d2WiderTransfer205Lo,d2WiderTransfer205Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer205C0 d2WiderTransfer205S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have hn1 : x-((d2WiderTransfer205S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer205S1,d2WiderTransfer205Lo,d2WiderTransfer205Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer205C1 then |x-((d2WiderTransfer205S1:ℚ):ℝ)| ≤ ((d2Log12Q:ℚ):ℝ) else ((d2Log12Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer205S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer205S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer205S1,d2WiderTransfer205Lo,d2WiderTransfer205Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer205C1,d2Log12Q,d2WiderTransfer205S1,d2WiderTransfer205Lo,d2WiderTransfer205Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer205C1 d2WiderTransfer205S1 d2Log12Q d2Log12Lo d2Log12Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log12Bounds
  have har : (((weightedUpper d2WiderTransfer205C0 d2Log162Lo d2Log162Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer205C1 d2Log12Lo d2Log12Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer205Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer205Arithmetic
  linarith
#print axioms d2WiderTransfer205Arithmetic
#print axioms d2WiderTransfer205Bound
def d2WiderTransfer206Lo : ℚ := (d2LitsNearWiderTransfers025.q2 (21768399) 1 (-25))
def d2WiderTransfer206Hi : ℚ := (d2LitsNearWiderTransfers025.q2 (88751317) 1 (-27))
def d2WiderTransfer206Cap : ℚ := (d2LitsNearWiderTransfers025.q2 (3041282164444953296725) 1 (-79))
def d2WiderTransfer206C0 : ℚ := (d2LitsNearWiderTransfers025.q2 (1) 25 (-4))
def d2WiderTransfer206S0 : ℚ := (d2LitsNearWiderTransfers025.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer206Arithmetic : weightedUpper d2WiderTransfer206C0 d2Log164Lo d2Log164Hi ≤ d2WiderTransfer206Cap := by decide +kernel
theorem d2WiderTransfer206Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer206Lo:ℚ):ℝ) ((d2WiderTransfer206Hi:ℚ):ℝ), ((d2WiderTransfer206C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer206S0:ℚ):ℝ)| ≤ ((d2WiderTransfer206Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer206S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer206S0,d2WiderTransfer206Lo,d2WiderTransfer206Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer206C0 then |x-((d2WiderTransfer206S0:ℚ):ℝ)| ≤ ((d2Log164Q:ℚ):ℝ) else ((d2Log164Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer206S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer206S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer206S0,d2WiderTransfer206Lo,d2WiderTransfer206Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer206C0,d2Log164Q,d2WiderTransfer206S0,d2WiderTransfer206Lo,d2WiderTransfer206Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer206C0 d2WiderTransfer206S0 d2Log164Q d2Log164Lo d2Log164Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log164Bounds
  have har : (((weightedUpper d2WiderTransfer206C0 d2Log164Lo d2Log164Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer206Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer206Arithmetic
  linarith
#print axioms d2WiderTransfer206Arithmetic
#print axioms d2WiderTransfer206Bound
def d2WiderTransfer207Lo : ℚ := (d2LitsNearWiderTransfers025.q2 (21768399) 1 (-25))
def d2WiderTransfer207Hi : ℚ := (d2LitsNearWiderTransfers025.q2 (88751317) 1 (-27))
def d2WiderTransfer207Cap : ℚ := (d2LitsNearWiderTransfers025.q2 (3666432248762820968277) 1 (-79))
def d2WiderTransfer207C0 : ℚ := (d2LitsNearWiderTransfers025.q2 (1) 275 (-4))
def d2WiderTransfer207S0 : ℚ := (d2LitsNearWiderTransfers025.q2 (-1) 1 (0))
def d2WiderTransfer207C1 : ℚ := (d2LitsNearWiderTransfers025.q2 (-1) 55 (-3))
def d2WiderTransfer207S1 : ℚ := (d2LitsNearWiderTransfers025.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer207Arithmetic : weightedUpper d2WiderTransfer207C0 d2Log164Lo d2Log164Hi + weightedUpper d2WiderTransfer207C1 d2Log10Lo d2Log10Hi ≤ d2WiderTransfer207Cap := by decide +kernel
theorem d2WiderTransfer207Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer207Lo:ℚ):ℝ) ((d2WiderTransfer207Hi:ℚ):ℝ), ((d2WiderTransfer207C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer207S0:ℚ):ℝ)| + ((d2WiderTransfer207C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer207S1:ℚ):ℝ)| ≤ ((d2WiderTransfer207Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer207S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer207S0,d2WiderTransfer207Lo,d2WiderTransfer207Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer207C0 then |x-((d2WiderTransfer207S0:ℚ):ℝ)| ≤ ((d2Log164Q:ℚ):ℝ) else ((d2Log164Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer207S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer207S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer207S0,d2WiderTransfer207Lo,d2WiderTransfer207Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer207C0,d2Log164Q,d2WiderTransfer207S0,d2WiderTransfer207Lo,d2WiderTransfer207Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer207C0 d2WiderTransfer207S0 d2Log164Q d2Log164Lo d2Log164Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log164Bounds
  have hn1 : x-((d2WiderTransfer207S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer207S1,d2WiderTransfer207Lo,d2WiderTransfer207Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer207C1 then |x-((d2WiderTransfer207S1:ℚ):ℝ)| ≤ ((d2Log10Q:ℚ):ℝ) else ((d2Log10Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer207S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer207S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer207S1,d2WiderTransfer207Lo,d2WiderTransfer207Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers025.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer207C1,d2Log10Q,d2WiderTransfer207S1,d2WiderTransfer207Lo,d2WiderTransfer207Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer207C1 d2WiderTransfer207S1 d2Log10Q d2Log10Lo d2Log10Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log10Bounds
  have har : (((weightedUpper d2WiderTransfer207C0 d2Log164Lo d2Log164Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer207C1 d2Log10Lo d2Log10Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer207Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer207Arithmetic
  linarith
#print axioms d2WiderTransfer207Arithmetic
#print axioms d2WiderTransfer207Bound
end CatalanMeasure.GenD.Signed.Data.Cells

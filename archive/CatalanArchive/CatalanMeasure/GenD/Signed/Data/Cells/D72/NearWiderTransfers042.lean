module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache009
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers042
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers042
open D72.LogTransfer
def d2WiderTransfer336Lo : ℚ := (d2LitsNearWiderTransfers042.q2 (339905779) 1 (-29))
def d2WiderTransfer336Hi : ℚ := (d2LitsNearWiderTransfers042.q2 (1361300837) 1 (-31))
def d2WiderTransfer336Cap : ℚ := (d2LitsNearWiderTransfers042.q2 (34713836624474160589873) 1 (-80))
def d2WiderTransfer336C0 : ℚ := (d2LitsNearWiderTransfers042.q2 (3) 275 (-5))
def d2WiderTransfer336S0 : ℚ := (d2LitsNearWiderTransfers042.q2 (-1) 1 (0))
def d2WiderTransfer336C1 : ℚ := (d2LitsNearWiderTransfers042.q2 (-5) 11 (-4))
def d2WiderTransfer336S1 : ℚ := (d2LitsNearWiderTransfers042.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer336Arithmetic : weightedUpper d2WiderTransfer336C0 d2Log152Lo d2Log152Hi + weightedUpper d2WiderTransfer336C1 d2Log22Lo d2Log22Hi ≤ d2WiderTransfer336Cap := by decide +kernel
theorem d2WiderTransfer336Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer336Lo:ℚ):ℝ) ((d2WiderTransfer336Hi:ℚ):ℝ), ((d2WiderTransfer336C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer336S0:ℚ):ℝ)| + ((d2WiderTransfer336C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer336S1:ℚ):ℝ)| ≤ ((d2WiderTransfer336Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer336S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer336S0,d2WiderTransfer336Lo,d2WiderTransfer336Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer336C0 then |x-((d2WiderTransfer336S0:ℚ):ℝ)| ≤ ((d2Log152Q:ℚ):ℝ) else ((d2Log152Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer336S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer336S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer336S0,d2WiderTransfer336Lo,d2WiderTransfer336Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer336C0,d2Log152Q,d2WiderTransfer336S0,d2WiderTransfer336Lo,d2WiderTransfer336Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer336C0 d2WiderTransfer336S0 d2Log152Q d2Log152Lo d2Log152Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log152Bounds
  have hn1 : x-((d2WiderTransfer336S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer336S1,d2WiderTransfer336Lo,d2WiderTransfer336Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer336C1 then |x-((d2WiderTransfer336S1:ℚ):ℝ)| ≤ ((d2Log22Q:ℚ):ℝ) else ((d2Log22Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer336S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer336S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer336S1,d2WiderTransfer336Lo,d2WiderTransfer336Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer336C1,d2Log22Q,d2WiderTransfer336S1,d2WiderTransfer336Lo,d2WiderTransfer336Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer336C1 d2WiderTransfer336S1 d2Log22Q d2Log22Lo d2Log22Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log22Bounds
  have har : (((weightedUpper d2WiderTransfer336C0 d2Log152Lo d2Log152Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer336C1 d2Log22Lo d2Log22Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer336Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer336Arithmetic
  linarith
#print axioms d2WiderTransfer336Arithmetic
#print axioms d2WiderTransfer336Bound
def d2WiderTransfer337Lo : ℚ := (d2LitsNearWiderTransfers042.q2 (1361300837) 1 (-31))
def d2WiderTransfer337Hi : ℚ := (d2LitsNearWiderTransfers042.q2 (681489279) 1 (-30))
def d2WiderTransfer337Cap : ℚ := (d2LitsNearWiderTransfers042.q2 (1302310057795335633989) 1 (-79))
def d2WiderTransfer337C0 : ℚ := (d2LitsNearWiderTransfers042.q2 (-1) 55 (-3))
def d2WiderTransfer337S0 : ℚ := (d2LitsNearWiderTransfers042.q2 (-1) 1 (0))
def d2WiderTransfer337C1 : ℚ := (d2LitsNearWiderTransfers042.q2 (-1) 55 (-3))
def d2WiderTransfer337S1 : ℚ := (d2LitsNearWiderTransfers042.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer337Arithmetic : weightedUpper d2WiderTransfer337C0 d2Log152Lo d2Log152Hi + weightedUpper d2WiderTransfer337C1 d2Log21Lo d2Log21Hi ≤ d2WiderTransfer337Cap := by decide +kernel
theorem d2WiderTransfer337Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer337Lo:ℚ):ℝ) ((d2WiderTransfer337Hi:ℚ):ℝ), ((d2WiderTransfer337C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer337S0:ℚ):ℝ)| + ((d2WiderTransfer337C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer337S1:ℚ):ℝ)| ≤ ((d2WiderTransfer337Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer337S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer337S0,d2WiderTransfer337Lo,d2WiderTransfer337Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer337C0 then |x-((d2WiderTransfer337S0:ℚ):ℝ)| ≤ ((d2Log152Q:ℚ):ℝ) else ((d2Log152Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer337S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer337S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer337S0,d2WiderTransfer337Lo,d2WiderTransfer337Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer337C0,d2Log152Q,d2WiderTransfer337S0,d2WiderTransfer337Lo,d2WiderTransfer337Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer337C0 d2WiderTransfer337S0 d2Log152Q d2Log152Lo d2Log152Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log152Bounds
  have hn1 : x-((d2WiderTransfer337S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer337S1,d2WiderTransfer337Lo,d2WiderTransfer337Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer337C1 then |x-((d2WiderTransfer337S1:ℚ):ℝ)| ≤ ((d2Log21Q:ℚ):ℝ) else ((d2Log21Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer337S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer337S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer337S1,d2WiderTransfer337Lo,d2WiderTransfer337Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer337C1,d2Log21Q,d2WiderTransfer337S1,d2WiderTransfer337Lo,d2WiderTransfer337Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer337C1 d2WiderTransfer337S1 d2Log21Q d2Log21Lo d2Log21Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log21Bounds
  have har : (((weightedUpper d2WiderTransfer337C0 d2Log152Lo d2Log152Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer337C1 d2Log21Lo d2Log21Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer337Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer337Arithmetic
  linarith
#print axioms d2WiderTransfer337Arithmetic
#print axioms d2WiderTransfer337Bound
def d2WiderTransfer338Lo : ℚ := (d2LitsNearWiderTransfers042.q2 (1361300837) 1 (-31))
def d2WiderTransfer338Hi : ℚ := (d2LitsNearWiderTransfers042.q2 (681489279) 1 (-30))
def d2WiderTransfer338Cap : ℚ := (d2LitsNearWiderTransfers042.q2 (8968207994758479100997) 1 (-79))
def d2WiderTransfer338C0 : ℚ := (d2LitsNearWiderTransfers042.q2 (23) 25 (-5))
def d2WiderTransfer338S0 : ℚ := (d2LitsNearWiderTransfers042.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer338Arithmetic : weightedUpper d2WiderTransfer338C0 d2Log153Lo d2Log153Hi ≤ d2WiderTransfer338Cap := by decide +kernel
theorem d2WiderTransfer338Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer338Lo:ℚ):ℝ) ((d2WiderTransfer338Hi:ℚ):ℝ), ((d2WiderTransfer338C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer338S0:ℚ):ℝ)| ≤ ((d2WiderTransfer338Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer338S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer338S0,d2WiderTransfer338Lo,d2WiderTransfer338Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer338C0 then |x-((d2WiderTransfer338S0:ℚ):ℝ)| ≤ ((d2Log153Q:ℚ):ℝ) else ((d2Log153Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer338S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer338S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer338S0,d2WiderTransfer338Lo,d2WiderTransfer338Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer338C0,d2Log153Q,d2WiderTransfer338S0,d2WiderTransfer338Lo,d2WiderTransfer338Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer338C0 d2WiderTransfer338S0 d2Log153Q d2Log153Lo d2Log153Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log153Bounds
  have har : (((weightedUpper d2WiderTransfer338C0 d2Log153Lo d2Log153Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer338Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer338Arithmetic
  linarith
#print axioms d2WiderTransfer338Arithmetic
#print axioms d2WiderTransfer338Bound
def d2WiderTransfer339Lo : ℚ := (d2LitsNearWiderTransfers042.q2 (1361300837) 1 (-31))
def d2WiderTransfer339Hi : ℚ := (d2LitsNearWiderTransfers042.q2 (681489279) 1 (-30))
def d2WiderTransfer339Cap : ℚ := (d2LitsNearWiderTransfers042.q2 (17393701690392114248773) 1 (-79))
def d2WiderTransfer339C0 : ℚ := (d2LitsNearWiderTransfers042.q2 (3) 275 (-5))
def d2WiderTransfer339S0 : ℚ := (d2LitsNearWiderTransfers042.q2 (-1) 1 (0))
def d2WiderTransfer339C1 : ℚ := (d2LitsNearWiderTransfers042.q2 (-5) 11 (-4))
def d2WiderTransfer339S1 : ℚ := (d2LitsNearWiderTransfers042.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer339Arithmetic : weightedUpper d2WiderTransfer339C0 d2Log153Lo d2Log153Hi + weightedUpper d2WiderTransfer339C1 d2Log21Lo d2Log21Hi ≤ d2WiderTransfer339Cap := by decide +kernel
theorem d2WiderTransfer339Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer339Lo:ℚ):ℝ) ((d2WiderTransfer339Hi:ℚ):ℝ), ((d2WiderTransfer339C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer339S0:ℚ):ℝ)| + ((d2WiderTransfer339C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer339S1:ℚ):ℝ)| ≤ ((d2WiderTransfer339Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer339S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer339S0,d2WiderTransfer339Lo,d2WiderTransfer339Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer339C0 then |x-((d2WiderTransfer339S0:ℚ):ℝ)| ≤ ((d2Log153Q:ℚ):ℝ) else ((d2Log153Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer339S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer339S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer339S0,d2WiderTransfer339Lo,d2WiderTransfer339Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer339C0,d2Log153Q,d2WiderTransfer339S0,d2WiderTransfer339Lo,d2WiderTransfer339Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer339C0 d2WiderTransfer339S0 d2Log153Q d2Log153Lo d2Log153Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log153Bounds
  have hn1 : x-((d2WiderTransfer339S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer339S1,d2WiderTransfer339Lo,d2WiderTransfer339Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer339C1 then |x-((d2WiderTransfer339S1:ℚ):ℝ)| ≤ ((d2Log21Q:ℚ):ℝ) else ((d2Log21Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer339S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer339S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer339S1,d2WiderTransfer339Lo,d2WiderTransfer339Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer339C1,d2Log21Q,d2WiderTransfer339S1,d2WiderTransfer339Lo,d2WiderTransfer339Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer339C1 d2WiderTransfer339S1 d2Log21Q d2Log21Lo d2Log21Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log21Bounds
  have har : (((weightedUpper d2WiderTransfer339C0 d2Log153Lo d2Log153Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer339C1 d2Log21Lo d2Log21Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer339Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer339Arithmetic
  linarith
#print axioms d2WiderTransfer339Arithmetic
#print axioms d2WiderTransfer339Bound
def d2WiderTransfer340Lo : ℚ := (d2LitsNearWiderTransfers042.q2 (681489279) 1 (-30))
def d2WiderTransfer340Hi : ℚ := (d2LitsNearWiderTransfers042.q2 (1364656279) 1 (-31))
def d2WiderTransfer340Cap : ℚ := (d2LitsNearWiderTransfers042.q2 (2678343852355371081821) 1 (-80))
def d2WiderTransfer340C0 : ℚ := (d2LitsNearWiderTransfers042.q2 (-1) 55 (-3))
def d2WiderTransfer340S0 : ℚ := (d2LitsNearWiderTransfers042.q2 (-1) 1 (0))
def d2WiderTransfer340C1 : ℚ := (d2LitsNearWiderTransfers042.q2 (-1) 55 (-3))
def d2WiderTransfer340S1 : ℚ := (d2LitsNearWiderTransfers042.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer340Arithmetic : weightedUpper d2WiderTransfer340C0 d2Log153Lo d2Log153Hi + weightedUpper d2WiderTransfer340C1 d2Log20Lo d2Log20Hi ≤ d2WiderTransfer340Cap := by decide +kernel
theorem d2WiderTransfer340Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer340Lo:ℚ):ℝ) ((d2WiderTransfer340Hi:ℚ):ℝ), ((d2WiderTransfer340C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer340S0:ℚ):ℝ)| + ((d2WiderTransfer340C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer340S1:ℚ):ℝ)| ≤ ((d2WiderTransfer340Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer340S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer340S0,d2WiderTransfer340Lo,d2WiderTransfer340Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer340C0 then |x-((d2WiderTransfer340S0:ℚ):ℝ)| ≤ ((d2Log153Q:ℚ):ℝ) else ((d2Log153Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer340S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer340S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer340S0,d2WiderTransfer340Lo,d2WiderTransfer340Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer340C0,d2Log153Q,d2WiderTransfer340S0,d2WiderTransfer340Lo,d2WiderTransfer340Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer340C0 d2WiderTransfer340S0 d2Log153Q d2Log153Lo d2Log153Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log153Bounds
  have hn1 : x-((d2WiderTransfer340S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer340S1,d2WiderTransfer340Lo,d2WiderTransfer340Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer340C1 then |x-((d2WiderTransfer340S1:ℚ):ℝ)| ≤ ((d2Log20Q:ℚ):ℝ) else ((d2Log20Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer340S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer340S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer340S1,d2WiderTransfer340Lo,d2WiderTransfer340Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer340C1,d2Log20Q,d2WiderTransfer340S1,d2WiderTransfer340Lo,d2WiderTransfer340Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer340C1 d2WiderTransfer340S1 d2Log20Q d2Log20Lo d2Log20Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log20Bounds
  have har : (((weightedUpper d2WiderTransfer340C0 d2Log153Lo d2Log153Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer340C1 d2Log20Lo d2Log20Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer340Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer340Arithmetic
  linarith
#print axioms d2WiderTransfer340Arithmetic
#print axioms d2WiderTransfer340Bound
def d2WiderTransfer341Lo : ℚ := (d2LitsNearWiderTransfers042.q2 (681489279) 1 (-30))
def d2WiderTransfer341Hi : ℚ := (d2LitsNearWiderTransfers042.q2 (1364656279) 1 (-31))
def d2WiderTransfer341Cap : ℚ := (d2LitsNearWiderTransfers042.q2 (18010139726281658015837) 1 (-80))
def d2WiderTransfer341C0 : ℚ := (d2LitsNearWiderTransfers042.q2 (23) 25 (-5))
def d2WiderTransfer341S0 : ℚ := (d2LitsNearWiderTransfers042.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer341Arithmetic : weightedUpper d2WiderTransfer341C0 d2Log154Lo d2Log154Hi ≤ d2WiderTransfer341Cap := by decide +kernel
theorem d2WiderTransfer341Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer341Lo:ℚ):ℝ) ((d2WiderTransfer341Hi:ℚ):ℝ), ((d2WiderTransfer341C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer341S0:ℚ):ℝ)| ≤ ((d2WiderTransfer341Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer341S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer341S0,d2WiderTransfer341Lo,d2WiderTransfer341Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer341C0 then |x-((d2WiderTransfer341S0:ℚ):ℝ)| ≤ ((d2Log154Q:ℚ):ℝ) else ((d2Log154Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer341S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer341S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer341S0,d2WiderTransfer341Lo,d2WiderTransfer341Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer341C0,d2Log154Q,d2WiderTransfer341S0,d2WiderTransfer341Lo,d2WiderTransfer341Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer341C0 d2WiderTransfer341S0 d2Log154Q d2Log154Lo d2Log154Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log154Bounds
  have har : (((weightedUpper d2WiderTransfer341C0 d2Log154Lo d2Log154Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer341Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer341Arithmetic
  linarith
#print axioms d2WiderTransfer341Arithmetic
#print axioms d2WiderTransfer341Bound
def d2WiderTransfer342Lo : ℚ := (d2LitsNearWiderTransfers042.q2 (681489279) 1 (-30))
def d2WiderTransfer342Hi : ℚ := (d2LitsNearWiderTransfers042.q2 (1364656279) 1 (-31))
def d2WiderTransfer342Cap : ℚ := (d2LitsNearWiderTransfers042.q2 (34861127117548928311389) 1 (-80))
def d2WiderTransfer342C0 : ℚ := (d2LitsNearWiderTransfers042.q2 (3) 275 (-5))
def d2WiderTransfer342S0 : ℚ := (d2LitsNearWiderTransfers042.q2 (-1) 1 (0))
def d2WiderTransfer342C1 : ℚ := (d2LitsNearWiderTransfers042.q2 (-5) 11 (-4))
def d2WiderTransfer342S1 : ℚ := (d2LitsNearWiderTransfers042.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer342Arithmetic : weightedUpper d2WiderTransfer342C0 d2Log154Lo d2Log154Hi + weightedUpper d2WiderTransfer342C1 d2Log20Lo d2Log20Hi ≤ d2WiderTransfer342Cap := by decide +kernel
theorem d2WiderTransfer342Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer342Lo:ℚ):ℝ) ((d2WiderTransfer342Hi:ℚ):ℝ), ((d2WiderTransfer342C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer342S0:ℚ):ℝ)| + ((d2WiderTransfer342C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer342S1:ℚ):ℝ)| ≤ ((d2WiderTransfer342Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer342S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer342S0,d2WiderTransfer342Lo,d2WiderTransfer342Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer342C0 then |x-((d2WiderTransfer342S0:ℚ):ℝ)| ≤ ((d2Log154Q:ℚ):ℝ) else ((d2Log154Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer342S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer342S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer342S0,d2WiderTransfer342Lo,d2WiderTransfer342Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer342C0,d2Log154Q,d2WiderTransfer342S0,d2WiderTransfer342Lo,d2WiderTransfer342Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer342C0 d2WiderTransfer342S0 d2Log154Q d2Log154Lo d2Log154Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log154Bounds
  have hn1 : x-((d2WiderTransfer342S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer342S1,d2WiderTransfer342Lo,d2WiderTransfer342Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer342C1 then |x-((d2WiderTransfer342S1:ℚ):ℝ)| ≤ ((d2Log20Q:ℚ):ℝ) else ((d2Log20Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer342S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer342S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer342S1,d2WiderTransfer342Lo,d2WiderTransfer342Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer342C1,d2Log20Q,d2WiderTransfer342S1,d2WiderTransfer342Lo,d2WiderTransfer342Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer342C1 d2WiderTransfer342S1 d2Log20Q d2Log20Lo d2Log20Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log20Bounds
  have har : (((weightedUpper d2WiderTransfer342C0 d2Log154Lo d2Log154Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer342C1 d2Log20Lo d2Log20Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer342Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer342Arithmetic
  linarith
#print axioms d2WiderTransfer342Arithmetic
#print axioms d2WiderTransfer342Bound
def d2WiderTransfer343Lo : ℚ := (d2LitsNearWiderTransfers042.q2 (1364656279) 1 (-31))
def d2WiderTransfer343Hi : ℚ := (d2LitsNearWiderTransfers042.q2 (85395875) 1 (-27))
def d2WiderTransfer343Cap : ℚ := (d2LitsNearWiderTransfers042.q2 (2752225243658253026133) 1 (-80))
def d2WiderTransfer343C0 : ℚ := (d2LitsNearWiderTransfers042.q2 (-1) 55 (-3))
def d2WiderTransfer343S0 : ℚ := (d2LitsNearWiderTransfers042.q2 (-1) 1 (0))
def d2WiderTransfer343C1 : ℚ := (d2LitsNearWiderTransfers042.q2 (-1) 55 (-3))
def d2WiderTransfer343S1 : ℚ := (d2LitsNearWiderTransfers042.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer343Arithmetic : weightedUpper d2WiderTransfer343C0 d2Log154Lo d2Log154Hi + weightedUpper d2WiderTransfer343C1 d2Log19Lo d2Log19Hi ≤ d2WiderTransfer343Cap := by decide +kernel
theorem d2WiderTransfer343Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer343Lo:ℚ):ℝ) ((d2WiderTransfer343Hi:ℚ):ℝ), ((d2WiderTransfer343C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer343S0:ℚ):ℝ)| + ((d2WiderTransfer343C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer343S1:ℚ):ℝ)| ≤ ((d2WiderTransfer343Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer343S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer343S0,d2WiderTransfer343Lo,d2WiderTransfer343Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer343C0 then |x-((d2WiderTransfer343S0:ℚ):ℝ)| ≤ ((d2Log154Q:ℚ):ℝ) else ((d2Log154Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer343S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer343S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer343S0,d2WiderTransfer343Lo,d2WiderTransfer343Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer343C0,d2Log154Q,d2WiderTransfer343S0,d2WiderTransfer343Lo,d2WiderTransfer343Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer343C0 d2WiderTransfer343S0 d2Log154Q d2Log154Lo d2Log154Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log154Bounds
  have hn1 : x-((d2WiderTransfer343S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer343S1,d2WiderTransfer343Lo,d2WiderTransfer343Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer343C1 then |x-((d2WiderTransfer343S1:ℚ):ℝ)| ≤ ((d2Log19Q:ℚ):ℝ) else ((d2Log19Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer343S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer343S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer343S1,d2WiderTransfer343Lo,d2WiderTransfer343Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers042.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer343C1,d2Log19Q,d2WiderTransfer343S1,d2WiderTransfer343Lo,d2WiderTransfer343Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer343C1 d2WiderTransfer343S1 d2Log19Q d2Log19Lo d2Log19Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log19Bounds
  have har : (((weightedUpper d2WiderTransfer343C0 d2Log154Lo d2Log154Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer343C1 d2Log19Lo d2Log19Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer343Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer343Arithmetic
  linarith
#print axioms d2WiderTransfer343Arithmetic
#print axioms d2WiderTransfer343Bound
end CatalanMeasure.GenD.Signed.Data.Cells

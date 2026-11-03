module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache008
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers029
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers029
open D72.LogTransfer
def d2Transfer232Lo : ℚ := (d2LitsNearTransfers029.q2 (326484011) 1 (-29))
def d2Transfer232Hi : ℚ := (d2LitsNearTransfers029.q2 (654645743) 1 (-30))
def d2Transfer232Cap : ℚ := (d2LitsNearTransfers029.q2 (2248032279655269564805) 1 (-77))
def d2Transfer232C0 : ℚ := (d2LitsNearTransfers029.q2 (1) 1 (-5))
def d2Transfer232S0 : ℚ := (d2LitsNearTransfers029.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer232Arithmetic : weightedUpper d2Transfer232C0 d2Log127Lo d2Log127Hi ≤ d2Transfer232Cap := by decide +kernel
theorem d2Transfer232Bound : ∀ x ∈ Set.Icc ((d2Transfer232Lo:ℚ):ℝ) ((d2Transfer232Hi:ℚ):ℝ), ((d2Transfer232C0:ℚ):ℝ)*Real.log |x-((d2Transfer232S0:ℚ):ℝ)| ≤ ((d2Transfer232Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer232S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer232S0,d2Transfer232Lo,d2Transfer232Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer232C0 then |x-((d2Transfer232S0:ℚ):ℝ)| ≤ ((d2Log127Q:ℚ):ℝ) else ((d2Log127Q:ℚ):ℝ) ≤ |x-((d2Transfer232S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer232S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer232S0,d2Transfer232Lo,d2Transfer232Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer232C0,d2Log127Q,d2Transfer232S0,d2Transfer232Lo,d2Transfer232Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer232C0 d2Transfer232S0 d2Log127Q d2Log127Lo d2Log127Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log127Bounds
  have har : (((weightedUpper d2Transfer232C0 d2Log127Lo d2Log127Hi:ℚ):ℝ)) ≤ ((d2Transfer232Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer232Arithmetic
  linarith
#print axioms d2Transfer232Arithmetic
#print axioms d2Transfer232Bound
def d2Transfer233Lo : ℚ := (d2LitsNearTransfers029.q2 (326484011) 1 (-29))
def d2Transfer233Hi : ℚ := (d2LitsNearTransfers029.q2 (654645743) 1 (-30))
def d2Transfer233Cap : ℚ := (d2LitsNearTransfers029.q2 (4293636944941707985285) 1 (-77))
def d2Transfer233C0 : ℚ := (d2LitsNearTransfers029.q2 (1) 11 (-5))
def d2Transfer233S0 : ℚ := (d2LitsNearTransfers029.q2 (-1) 1 (0))
def d2Transfer233C1 : ℚ := (d2LitsNearTransfers029.q2 (-5) 11 (-4))
def d2Transfer233S1 : ℚ := (d2LitsNearTransfers029.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer233Arithmetic : weightedUpper d2Transfer233C0 d2Log127Lo d2Log127Hi + weightedUpper d2Transfer233C1 d2Log47Lo d2Log47Hi ≤ d2Transfer233Cap := by decide +kernel
theorem d2Transfer233Bound : ∀ x ∈ Set.Icc ((d2Transfer233Lo:ℚ):ℝ) ((d2Transfer233Hi:ℚ):ℝ), ((d2Transfer233C0:ℚ):ℝ)*Real.log |x-((d2Transfer233S0:ℚ):ℝ)| + ((d2Transfer233C1:ℚ):ℝ)*Real.log |x-((d2Transfer233S1:ℚ):ℝ)| ≤ ((d2Transfer233Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer233S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer233S0,d2Transfer233Lo,d2Transfer233Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer233C0 then |x-((d2Transfer233S0:ℚ):ℝ)| ≤ ((d2Log127Q:ℚ):ℝ) else ((d2Log127Q:ℚ):ℝ) ≤ |x-((d2Transfer233S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer233S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer233S0,d2Transfer233Lo,d2Transfer233Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer233C0,d2Log127Q,d2Transfer233S0,d2Transfer233Lo,d2Transfer233Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer233C0 d2Transfer233S0 d2Log127Q d2Log127Lo d2Log127Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log127Bounds
  have hn1 : x-((d2Transfer233S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer233S1,d2Transfer233Lo,d2Transfer233Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer233C1 then |x-((d2Transfer233S1:ℚ):ℝ)| ≤ ((d2Log47Q:ℚ):ℝ) else ((d2Log47Q:ℚ):ℝ) ≤ |x-((d2Transfer233S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer233S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer233S1,d2Transfer233Lo,d2Transfer233Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer233C1,d2Log47Q,d2Transfer233S1,d2Transfer233Lo,d2Transfer233Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer233C1 d2Transfer233S1 d2Log47Q d2Log47Lo d2Log47Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log47Bounds
  have har : (((weightedUpper d2Transfer233C0 d2Log127Lo d2Log127Hi:ℚ):ℝ) + ((weightedUpper d2Transfer233C1 d2Log47Lo d2Log47Hi:ℚ):ℝ)) ≤ ((d2Transfer233Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer233Arithmetic
  linarith
#print axioms d2Transfer233Arithmetic
#print axioms d2Transfer233Bound
def d2Transfer234Lo : ℚ := (d2LitsNearTransfers029.q2 (654645743) 1 (-30))
def d2Transfer234Hi : ℚ := (d2LitsNearTransfers029.q2 (82040433) 1 (-27))
def d2Transfer234Cap : ℚ := (d2LitsNearTransfers029.q2 (773774829148068366265) 1 (-79))
def d2Transfer234C0 : ℚ := (d2LitsNearTransfers029.q2 (1) 25 (-4))
def d2Transfer234S0 : ℚ := (d2LitsNearTransfers029.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer234Arithmetic : weightedUpper d2Transfer234C0 d2Log128Lo d2Log128Hi ≤ d2Transfer234Cap := by decide +kernel
theorem d2Transfer234Bound : ∀ x ∈ Set.Icc ((d2Transfer234Lo:ℚ):ℝ) ((d2Transfer234Hi:ℚ):ℝ), ((d2Transfer234C0:ℚ):ℝ)*Real.log |x-((d2Transfer234S0:ℚ):ℝ)| ≤ ((d2Transfer234Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer234S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer234S0,d2Transfer234Lo,d2Transfer234Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer234C0 then |x-((d2Transfer234S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2Transfer234S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer234S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer234S0,d2Transfer234Lo,d2Transfer234Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer234C0,d2Log128Q,d2Transfer234S0,d2Transfer234Lo,d2Transfer234Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer234C0 d2Transfer234S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have har : (((weightedUpper d2Transfer234C0 d2Log128Lo d2Log128Hi:ℚ):ℝ)) ≤ ((d2Transfer234Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer234Arithmetic
  linarith
#print axioms d2Transfer234Arithmetic
#print axioms d2Transfer234Bound
def d2Transfer235Lo : ℚ := (d2LitsNearTransfers029.q2 (654645743) 1 (-30))
def d2Transfer235Hi : ℚ := (d2LitsNearTransfers029.q2 (82040433) 1 (-27))
def d2Transfer235Cap : ℚ := (d2LitsNearTransfers029.q2 (1398924913465936037817) 1 (-79))
def d2Transfer235C0 : ℚ := (d2LitsNearTransfers029.q2 (1) 275 (-4))
def d2Transfer235S0 : ℚ := (d2LitsNearTransfers029.q2 (-1) 1 (0))
def d2Transfer235C1 : ℚ := (d2LitsNearTransfers029.q2 (-1) 55 (-3))
def d2Transfer235S1 : ℚ := (d2LitsNearTransfers029.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer235Arithmetic : weightedUpper d2Transfer235C0 d2Log128Lo d2Log128Hi + weightedUpper d2Transfer235C1 d2Log46Lo d2Log46Hi ≤ d2Transfer235Cap := by decide +kernel
theorem d2Transfer235Bound : ∀ x ∈ Set.Icc ((d2Transfer235Lo:ℚ):ℝ) ((d2Transfer235Hi:ℚ):ℝ), ((d2Transfer235C0:ℚ):ℝ)*Real.log |x-((d2Transfer235S0:ℚ):ℝ)| + ((d2Transfer235C1:ℚ):ℝ)*Real.log |x-((d2Transfer235S1:ℚ):ℝ)| ≤ ((d2Transfer235Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer235S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer235S0,d2Transfer235Lo,d2Transfer235Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer235C0 then |x-((d2Transfer235S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2Transfer235S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer235S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer235S0,d2Transfer235Lo,d2Transfer235Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer235C0,d2Log128Q,d2Transfer235S0,d2Transfer235Lo,d2Transfer235Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer235C0 d2Transfer235S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have hn1 : x-((d2Transfer235S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer235S1,d2Transfer235Lo,d2Transfer235Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer235C1 then |x-((d2Transfer235S1:ℚ):ℝ)| ≤ ((d2Log46Q:ℚ):ℝ) else ((d2Log46Q:ℚ):ℝ) ≤ |x-((d2Transfer235S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer235S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer235S1,d2Transfer235Lo,d2Transfer235Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer235C1,d2Log46Q,d2Transfer235S1,d2Transfer235Lo,d2Transfer235Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer235C1 d2Transfer235S1 d2Log46Q d2Log46Lo d2Log46Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log46Bounds
  have har : (((weightedUpper d2Transfer235C0 d2Log128Lo d2Log128Hi:ℚ):ℝ) + ((weightedUpper d2Transfer235C1 d2Log46Lo d2Log46Hi:ℚ):ℝ)) ≤ ((d2Transfer235Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer235Arithmetic
  linarith
#print axioms d2Transfer235Arithmetic
#print axioms d2Transfer235Bound
def d2Transfer236Lo : ℚ := (d2LitsNearTransfers029.q2 (654645743) 1 (-30))
def d2Transfer236Hi : ℚ := (d2LitsNearTransfers029.q2 (82040433) 1 (-27))
def d2Transfer236Cap : ℚ := (d2LitsNearTransfers029.q2 (9010455958677416298425) 1 (-79))
def d2Transfer236C0 : ℚ := (d2LitsNearTransfers029.q2 (1) 1 (-5))
def d2Transfer236S0 : ℚ := (d2LitsNearTransfers029.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer236Arithmetic : weightedUpper d2Transfer236C0 d2Log128Lo d2Log128Hi ≤ d2Transfer236Cap := by decide +kernel
theorem d2Transfer236Bound : ∀ x ∈ Set.Icc ((d2Transfer236Lo:ℚ):ℝ) ((d2Transfer236Hi:ℚ):ℝ), ((d2Transfer236C0:ℚ):ℝ)*Real.log |x-((d2Transfer236S0:ℚ):ℝ)| ≤ ((d2Transfer236Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer236S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer236S0,d2Transfer236Lo,d2Transfer236Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer236C0 then |x-((d2Transfer236S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2Transfer236S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer236S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer236S0,d2Transfer236Lo,d2Transfer236Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer236C0,d2Log128Q,d2Transfer236S0,d2Transfer236Lo,d2Transfer236Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer236C0 d2Transfer236S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have har : (((weightedUpper d2Transfer236C0 d2Log128Lo d2Log128Hi:ℚ):ℝ)) ≤ ((d2Transfer236Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer236Arithmetic
  linarith
#print axioms d2Transfer236Arithmetic
#print axioms d2Transfer236Bound
def d2Transfer237Lo : ℚ := (d2LitsNearTransfers029.q2 (654645743) 1 (-30))
def d2Transfer237Hi : ℚ := (d2LitsNearTransfers029.q2 (82040433) 1 (-27))
def d2Transfer237Cap : ℚ := (d2LitsNearTransfers029.q2 (17192874619823169980345) 1 (-79))
def d2Transfer237C0 : ℚ := (d2LitsNearTransfers029.q2 (1) 11 (-5))
def d2Transfer237S0 : ℚ := (d2LitsNearTransfers029.q2 (-1) 1 (0))
def d2Transfer237C1 : ℚ := (d2LitsNearTransfers029.q2 (-5) 11 (-4))
def d2Transfer237S1 : ℚ := (d2LitsNearTransfers029.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer237Arithmetic : weightedUpper d2Transfer237C0 d2Log128Lo d2Log128Hi + weightedUpper d2Transfer237C1 d2Log46Lo d2Log46Hi ≤ d2Transfer237Cap := by decide +kernel
theorem d2Transfer237Bound : ∀ x ∈ Set.Icc ((d2Transfer237Lo:ℚ):ℝ) ((d2Transfer237Hi:ℚ):ℝ), ((d2Transfer237C0:ℚ):ℝ)*Real.log |x-((d2Transfer237S0:ℚ):ℝ)| + ((d2Transfer237C1:ℚ):ℝ)*Real.log |x-((d2Transfer237S1:ℚ):ℝ)| ≤ ((d2Transfer237Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer237S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer237S0,d2Transfer237Lo,d2Transfer237Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer237C0 then |x-((d2Transfer237S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2Transfer237S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer237S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer237S0,d2Transfer237Lo,d2Transfer237Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer237C0,d2Log128Q,d2Transfer237S0,d2Transfer237Lo,d2Transfer237Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer237C0 d2Transfer237S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have hn1 : x-((d2Transfer237S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer237S1,d2Transfer237Lo,d2Transfer237Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer237C1 then |x-((d2Transfer237S1:ℚ):ℝ)| ≤ ((d2Log46Q:ℚ):ℝ) else ((d2Log46Q:ℚ):ℝ) ≤ |x-((d2Transfer237S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer237S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer237S1,d2Transfer237Lo,d2Transfer237Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer237C1,d2Log46Q,d2Transfer237S1,d2Transfer237Lo,d2Transfer237Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer237C1 d2Transfer237S1 d2Log46Q d2Log46Lo d2Log46Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log46Bounds
  have har : (((weightedUpper d2Transfer237C0 d2Log128Lo d2Log128Hi:ℚ):ℝ) + ((weightedUpper d2Transfer237C1 d2Log46Lo d2Log46Hi:ℚ):ℝ)) ≤ ((d2Transfer237Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer237Arithmetic
  linarith
#print axioms d2Transfer237Arithmetic
#print axioms d2Transfer237Bound
def d2Transfer238Lo : ℚ := (d2LitsNearTransfers029.q2 (82040433) 1 (-27))
def d2Transfer238Hi : ℚ := (d2LitsNearTransfers029.q2 (329839453) 1 (-29))
def d2Transfer238Cap : ℚ := (d2LitsNearTransfers029.q2 (1620750504893547881849) 1 (-80))
def d2Transfer238C0 : ℚ := (d2LitsNearTransfers029.q2 (1) 25 (-4))
def d2Transfer238S0 : ℚ := (d2LitsNearTransfers029.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer238Arithmetic : weightedUpper d2Transfer238C0 d2Log129Lo d2Log129Hi ≤ d2Transfer238Cap := by decide +kernel
theorem d2Transfer238Bound : ∀ x ∈ Set.Icc ((d2Transfer238Lo:ℚ):ℝ) ((d2Transfer238Hi:ℚ):ℝ), ((d2Transfer238C0:ℚ):ℝ)*Real.log |x-((d2Transfer238S0:ℚ):ℝ)| ≤ ((d2Transfer238Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer238S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer238S0,d2Transfer238Lo,d2Transfer238Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer238C0 then |x-((d2Transfer238S0:ℚ):ℝ)| ≤ ((d2Log129Q:ℚ):ℝ) else ((d2Log129Q:ℚ):ℝ) ≤ |x-((d2Transfer238S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer238S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer238S0,d2Transfer238Lo,d2Transfer238Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer238C0,d2Log129Q,d2Transfer238S0,d2Transfer238Lo,d2Transfer238Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer238C0 d2Transfer238S0 d2Log129Q d2Log129Lo d2Log129Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log129Bounds
  have har : (((weightedUpper d2Transfer238C0 d2Log129Lo d2Log129Hi:ℚ):ℝ)) ≤ ((d2Transfer238Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer238Arithmetic
  linarith
#print axioms d2Transfer238Arithmetic
#print axioms d2Transfer238Bound
def d2Transfer239Lo : ℚ := (d2LitsNearTransfers029.q2 (82040433) 1 (-27))
def d2Transfer239Hi : ℚ := (d2LitsNearTransfers029.q2 (329839453) 1 (-29))
def d2Transfer239Cap : ℚ := (d2LitsNearTransfers029.q2 (2871050673529283224953) 1 (-80))
def d2Transfer239C0 : ℚ := (d2LitsNearTransfers029.q2 (1) 275 (-4))
def d2Transfer239S0 : ℚ := (d2LitsNearTransfers029.q2 (-1) 1 (0))
def d2Transfer239C1 : ℚ := (d2LitsNearTransfers029.q2 (-1) 55 (-3))
def d2Transfer239S1 : ℚ := (d2LitsNearTransfers029.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer239Arithmetic : weightedUpper d2Transfer239C0 d2Log129Lo d2Log129Hi + weightedUpper d2Transfer239C1 d2Log45Lo d2Log45Hi ≤ d2Transfer239Cap := by decide +kernel
theorem d2Transfer239Bound : ∀ x ∈ Set.Icc ((d2Transfer239Lo:ℚ):ℝ) ((d2Transfer239Hi:ℚ):ℝ), ((d2Transfer239C0:ℚ):ℝ)*Real.log |x-((d2Transfer239S0:ℚ):ℝ)| + ((d2Transfer239C1:ℚ):ℝ)*Real.log |x-((d2Transfer239S1:ℚ):ℝ)| ≤ ((d2Transfer239Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer239S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer239S0,d2Transfer239Lo,d2Transfer239Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer239C0 then |x-((d2Transfer239S0:ℚ):ℝ)| ≤ ((d2Log129Q:ℚ):ℝ) else ((d2Log129Q:ℚ):ℝ) ≤ |x-((d2Transfer239S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer239S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer239S0,d2Transfer239Lo,d2Transfer239Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer239C0,d2Log129Q,d2Transfer239S0,d2Transfer239Lo,d2Transfer239Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer239C0 d2Transfer239S0 d2Log129Q d2Log129Lo d2Log129Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log129Bounds
  have hn1 : x-((d2Transfer239S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer239S1,d2Transfer239Lo,d2Transfer239Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer239C1 then |x-((d2Transfer239S1:ℚ):ℝ)| ≤ ((d2Log45Q:ℚ):ℝ) else ((d2Log45Q:ℚ):ℝ) ≤ |x-((d2Transfer239S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer239S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer239S1,d2Transfer239Lo,d2Transfer239Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers029.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer239C1,d2Log45Q,d2Transfer239S1,d2Transfer239Lo,d2Transfer239Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer239C1 d2Transfer239S1 d2Log45Q d2Log45Lo d2Log45Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log45Bounds
  have har : (((weightedUpper d2Transfer239C0 d2Log129Lo d2Log129Hi:ℚ):ℝ) + ((weightedUpper d2Transfer239C1 d2Log45Lo d2Log45Hi:ℚ):ℝ)) ≤ ((d2Transfer239Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer239Arithmetic
  linarith
#print axioms d2Transfer239Arithmetic
#print axioms d2Transfer239Bound
end CatalanMeasure.GenD.Signed.Data.Cells

module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers002
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers002
open D72.LogTransfer
def d2Transfer16Lo : ℚ := (d2LitsNearTransfers002.q2 (18287035) 1 (-27))
def d2Transfer16Hi : ℚ := (d2LitsNearTransfers002.q2 (38251791) 1 (-28))
def d2Transfer16Cap : ℚ := (d2LitsNearTransfers002.q2 (648894057) 1 (-39))
def d2Transfer16C0 : ℚ := (d2LitsNearTransfers002.q2 (1) 25 (-4))
def d2Transfer16S0 : ℚ := (d2LitsNearTransfers002.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer16Arithmetic : weightedUpper d2Transfer16C0 d2Log98Lo d2Log98Hi ≤ d2Transfer16Cap := by decide +kernel
theorem d2Transfer16Bound : ∀ x ∈ Set.Icc ((d2Transfer16Lo:ℚ):ℝ) ((d2Transfer16Hi:ℚ):ℝ), ((d2Transfer16C0:ℚ):ℝ)*Real.log |x-((d2Transfer16S0:ℚ):ℝ)| ≤ ((d2Transfer16Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer16S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer16S0,d2Transfer16Lo,d2Transfer16Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer16C0 then |x-((d2Transfer16S0:ℚ):ℝ)| ≤ ((d2Log98Q:ℚ):ℝ) else ((d2Log98Q:ℚ):ℝ) ≤ |x-((d2Transfer16S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer16S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer16S0,d2Transfer16Lo,d2Transfer16Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer16C0,d2Log98Q,d2Transfer16S0,d2Transfer16Lo,d2Transfer16Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer16C0 d2Transfer16S0 d2Log98Q d2Log98Lo d2Log98Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log98Bounds
  have har : (((weightedUpper d2Transfer16C0 d2Log98Lo d2Log98Hi:ℚ):ℝ)) ≤ ((d2Transfer16Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer16Arithmetic
  linarith
#print axioms d2Transfer16Arithmetic
#print axioms d2Transfer16Bound
def d2Transfer17Lo : ℚ := (d2LitsNearTransfers002.q2 (18287035) 1 (-27))
def d2Transfer17Hi : ℚ := (d2LitsNearTransfers002.q2 (38251791) 1 (-28))
def d2Transfer17Cap : ℚ := (d2LitsNearTransfers002.q2 (2432512853) 1 (-40))
def d2Transfer17C0 : ℚ := (d2LitsNearTransfers002.q2 (1) 275 (-4))
def d2Transfer17S0 : ℚ := (d2LitsNearTransfers002.q2 (-1) 1 (0))
def d2Transfer17C1 : ℚ := (d2LitsNearTransfers002.q2 (-1) 55 (-3))
def d2Transfer17S1 : ℚ := (d2LitsNearTransfers002.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer17Arithmetic : weightedUpper d2Transfer17C0 d2Log98Lo d2Log98Hi + weightedUpper d2Transfer17C1 d2Log76Lo d2Log76Hi ≤ d2Transfer17Cap := by decide +kernel
theorem d2Transfer17Bound : ∀ x ∈ Set.Icc ((d2Transfer17Lo:ℚ):ℝ) ((d2Transfer17Hi:ℚ):ℝ), ((d2Transfer17C0:ℚ):ℝ)*Real.log |x-((d2Transfer17S0:ℚ):ℝ)| + ((d2Transfer17C1:ℚ):ℝ)*Real.log |x-((d2Transfer17S1:ℚ):ℝ)| ≤ ((d2Transfer17Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer17S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer17S0,d2Transfer17Lo,d2Transfer17Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer17C0 then |x-((d2Transfer17S0:ℚ):ℝ)| ≤ ((d2Log98Q:ℚ):ℝ) else ((d2Log98Q:ℚ):ℝ) ≤ |x-((d2Transfer17S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer17S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer17S0,d2Transfer17Lo,d2Transfer17Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer17C0,d2Log98Q,d2Transfer17S0,d2Transfer17Lo,d2Transfer17Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer17C0 d2Transfer17S0 d2Log98Q d2Log98Lo d2Log98Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log98Bounds
  have hn1 : x-((d2Transfer17S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer17S1,d2Transfer17Lo,d2Transfer17Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer17C1 then |x-((d2Transfer17S1:ℚ):ℝ)| ≤ ((d2Log76Q:ℚ):ℝ) else ((d2Log76Q:ℚ):ℝ) ≤ |x-((d2Transfer17S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer17S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer17S1,d2Transfer17Lo,d2Transfer17Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer17C1,d2Log76Q,d2Transfer17S1,d2Transfer17Lo,d2Transfer17Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer17C1 d2Transfer17S1 d2Log76Q d2Log76Lo d2Log76Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log76Bounds
  have har : (((weightedUpper d2Transfer17C0 d2Log98Lo d2Log98Hi:ℚ):ℝ) + ((weightedUpper d2Transfer17C1 d2Log76Lo d2Log76Hi:ℚ):ℝ)) ≤ ((d2Transfer17Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer17Arithmetic
  linarith
#print axioms d2Transfer17Arithmetic
#print axioms d2Transfer17Bound
def d2Transfer18Lo : ℚ := (d2LitsNearTransfers002.q2 (38251791) 1 (-28))
def d2Transfer18Hi : ℚ := (d2LitsNearTransfers002.q2 (4991189) 1 (-25))
def d2Transfer18Cap : ℚ := (d2LitsNearTransfers002.q2 (648894057) 1 (-39))
def d2Transfer18C0 : ℚ := (d2LitsNearTransfers002.q2 (1) 25 (-4))
def d2Transfer18S0 : ℚ := (d2LitsNearTransfers002.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer18Arithmetic : weightedUpper d2Transfer18C0 d2Log99Lo d2Log99Hi ≤ d2Transfer18Cap := by decide +kernel
theorem d2Transfer18Bound : ∀ x ∈ Set.Icc ((d2Transfer18Lo:ℚ):ℝ) ((d2Transfer18Hi:ℚ):ℝ), ((d2Transfer18C0:ℚ):ℝ)*Real.log |x-((d2Transfer18S0:ℚ):ℝ)| ≤ ((d2Transfer18Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer18S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer18S0,d2Transfer18Lo,d2Transfer18Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer18C0 then |x-((d2Transfer18S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2Transfer18S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer18S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer18S0,d2Transfer18Lo,d2Transfer18Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer18C0,d2Log99Q,d2Transfer18S0,d2Transfer18Lo,d2Transfer18Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer18C0 d2Transfer18S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have har : (((weightedUpper d2Transfer18C0 d2Log99Lo d2Log99Hi:ℚ):ℝ)) ≤ ((d2Transfer18Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer18Arithmetic
  linarith
#print axioms d2Transfer18Arithmetic
#print axioms d2Transfer18Bound
def d2Transfer19Lo : ℚ := (d2LitsNearTransfers002.q2 (38251791) 1 (-28))
def d2Transfer19Hi : ℚ := (d2LitsNearTransfers002.q2 (4991189) 1 (-25))
def d2Transfer19Cap : ℚ := (d2LitsNearTransfers002.q2 (2432512853) 1 (-40))
def d2Transfer19C0 : ℚ := (d2LitsNearTransfers002.q2 (1) 275 (-4))
def d2Transfer19S0 : ℚ := (d2LitsNearTransfers002.q2 (-1) 1 (0))
def d2Transfer19C1 : ℚ := (d2LitsNearTransfers002.q2 (-1) 55 (-3))
def d2Transfer19S1 : ℚ := (d2LitsNearTransfers002.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer19Arithmetic : weightedUpper d2Transfer19C0 d2Log99Lo d2Log99Hi + weightedUpper d2Transfer19C1 d2Log75Lo d2Log75Hi ≤ d2Transfer19Cap := by decide +kernel
theorem d2Transfer19Bound : ∀ x ∈ Set.Icc ((d2Transfer19Lo:ℚ):ℝ) ((d2Transfer19Hi:ℚ):ℝ), ((d2Transfer19C0:ℚ):ℝ)*Real.log |x-((d2Transfer19S0:ℚ):ℝ)| + ((d2Transfer19C1:ℚ):ℝ)*Real.log |x-((d2Transfer19S1:ℚ):ℝ)| ≤ ((d2Transfer19Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer19S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer19S0,d2Transfer19Lo,d2Transfer19Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer19C0 then |x-((d2Transfer19S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2Transfer19S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer19S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer19S0,d2Transfer19Lo,d2Transfer19Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer19C0,d2Log99Q,d2Transfer19S0,d2Transfer19Lo,d2Transfer19Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer19C0 d2Transfer19S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have hn1 : x-((d2Transfer19S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer19S1,d2Transfer19Lo,d2Transfer19Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer19C1 then |x-((d2Transfer19S1:ℚ):ℝ)| ≤ ((d2Log75Q:ℚ):ℝ) else ((d2Log75Q:ℚ):ℝ) ≤ |x-((d2Transfer19S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer19S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer19S1,d2Transfer19Lo,d2Transfer19Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer19C1,d2Log75Q,d2Transfer19S1,d2Transfer19Lo,d2Transfer19Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer19C1 d2Transfer19S1 d2Log75Q d2Log75Lo d2Log75Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log75Bounds
  have har : (((weightedUpper d2Transfer19C0 d2Log99Lo d2Log99Hi:ℚ):ℝ) + ((weightedUpper d2Transfer19C1 d2Log75Lo d2Log75Hi:ℚ):ℝ)) ≤ ((d2Transfer19Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer19Arithmetic
  linarith
#print axioms d2Transfer19Arithmetic
#print axioms d2Transfer19Bound
def d2Transfer20Lo : ℚ := (d2LitsNearTransfers002.q2 (4991189) 1 (-25))
def d2Transfer20Hi : ℚ := (d2LitsNearTransfers002.q2 (41607233) 1 (-28))
def d2Transfer20Cap : ℚ := (d2LitsNearTransfers002.q2 (648894057) 1 (-39))
def d2Transfer20C0 : ℚ := (d2LitsNearTransfers002.q2 (1) 25 (-4))
def d2Transfer20S0 : ℚ := (d2LitsNearTransfers002.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer20Arithmetic : weightedUpper d2Transfer20C0 d2Log100Lo d2Log100Hi ≤ d2Transfer20Cap := by decide +kernel
theorem d2Transfer20Bound : ∀ x ∈ Set.Icc ((d2Transfer20Lo:ℚ):ℝ) ((d2Transfer20Hi:ℚ):ℝ), ((d2Transfer20C0:ℚ):ℝ)*Real.log |x-((d2Transfer20S0:ℚ):ℝ)| ≤ ((d2Transfer20Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer20S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer20S0,d2Transfer20Lo,d2Transfer20Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer20C0 then |x-((d2Transfer20S0:ℚ):ℝ)| ≤ ((d2Log100Q:ℚ):ℝ) else ((d2Log100Q:ℚ):ℝ) ≤ |x-((d2Transfer20S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer20S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer20S0,d2Transfer20Lo,d2Transfer20Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer20C0,d2Log100Q,d2Transfer20S0,d2Transfer20Lo,d2Transfer20Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer20C0 d2Transfer20S0 d2Log100Q d2Log100Lo d2Log100Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log100Bounds
  have har : (((weightedUpper d2Transfer20C0 d2Log100Lo d2Log100Hi:ℚ):ℝ)) ≤ ((d2Transfer20Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer20Arithmetic
  linarith
#print axioms d2Transfer20Arithmetic
#print axioms d2Transfer20Bound
def d2Transfer21Lo : ℚ := (d2LitsNearTransfers002.q2 (4991189) 1 (-25))
def d2Transfer21Hi : ℚ := (d2LitsNearTransfers002.q2 (41607233) 1 (-28))
def d2Transfer21Cap : ℚ := (d2LitsNearTransfers002.q2 (2432512853) 1 (-40))
def d2Transfer21C0 : ℚ := (d2LitsNearTransfers002.q2 (1) 275 (-4))
def d2Transfer21S0 : ℚ := (d2LitsNearTransfers002.q2 (-1) 1 (0))
def d2Transfer21C1 : ℚ := (d2LitsNearTransfers002.q2 (-1) 55 (-3))
def d2Transfer21S1 : ℚ := (d2LitsNearTransfers002.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer21Arithmetic : weightedUpper d2Transfer21C0 d2Log100Lo d2Log100Hi + weightedUpper d2Transfer21C1 d2Log74Lo d2Log74Hi ≤ d2Transfer21Cap := by decide +kernel
theorem d2Transfer21Bound : ∀ x ∈ Set.Icc ((d2Transfer21Lo:ℚ):ℝ) ((d2Transfer21Hi:ℚ):ℝ), ((d2Transfer21C0:ℚ):ℝ)*Real.log |x-((d2Transfer21S0:ℚ):ℝ)| + ((d2Transfer21C1:ℚ):ℝ)*Real.log |x-((d2Transfer21S1:ℚ):ℝ)| ≤ ((d2Transfer21Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer21S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer21S0,d2Transfer21Lo,d2Transfer21Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer21C0 then |x-((d2Transfer21S0:ℚ):ℝ)| ≤ ((d2Log100Q:ℚ):ℝ) else ((d2Log100Q:ℚ):ℝ) ≤ |x-((d2Transfer21S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer21S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer21S0,d2Transfer21Lo,d2Transfer21Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer21C0,d2Log100Q,d2Transfer21S0,d2Transfer21Lo,d2Transfer21Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer21C0 d2Transfer21S0 d2Log100Q d2Log100Lo d2Log100Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log100Bounds
  have hn1 : x-((d2Transfer21S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer21S1,d2Transfer21Lo,d2Transfer21Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer21C1 then |x-((d2Transfer21S1:ℚ):ℝ)| ≤ ((d2Log74Q:ℚ):ℝ) else ((d2Log74Q:ℚ):ℝ) ≤ |x-((d2Transfer21S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer21S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer21S1,d2Transfer21Lo,d2Transfer21Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer21C1,d2Log74Q,d2Transfer21S1,d2Transfer21Lo,d2Transfer21Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer21C1 d2Transfer21S1 d2Log74Q d2Log74Lo d2Log74Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log74Bounds
  have har : (((weightedUpper d2Transfer21C0 d2Log100Lo d2Log100Hi:ℚ):ℝ) + ((weightedUpper d2Transfer21C1 d2Log74Lo d2Log74Hi:ℚ):ℝ)) ≤ ((d2Transfer21Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer21Arithmetic
  linarith
#print axioms d2Transfer21Arithmetic
#print axioms d2Transfer21Bound
def d2Transfer22Lo : ℚ := (d2LitsNearTransfers002.q2 (41607233) 1 (-28))
def d2Transfer22Hi : ℚ := (d2LitsNearTransfers002.q2 (21642477) 1 (-27))
def d2Transfer22Cap : ℚ := (d2LitsNearTransfers002.q2 (648894057) 1 (-39))
def d2Transfer22C0 : ℚ := (d2LitsNearTransfers002.q2 (1) 25 (-4))
def d2Transfer22S0 : ℚ := (d2LitsNearTransfers002.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer22Arithmetic : weightedUpper d2Transfer22C0 d2Log101Lo d2Log101Hi ≤ d2Transfer22Cap := by decide +kernel
theorem d2Transfer22Bound : ∀ x ∈ Set.Icc ((d2Transfer22Lo:ℚ):ℝ) ((d2Transfer22Hi:ℚ):ℝ), ((d2Transfer22C0:ℚ):ℝ)*Real.log |x-((d2Transfer22S0:ℚ):ℝ)| ≤ ((d2Transfer22Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer22S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer22S0,d2Transfer22Lo,d2Transfer22Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer22C0 then |x-((d2Transfer22S0:ℚ):ℝ)| ≤ ((d2Log101Q:ℚ):ℝ) else ((d2Log101Q:ℚ):ℝ) ≤ |x-((d2Transfer22S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer22S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer22S0,d2Transfer22Lo,d2Transfer22Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer22C0,d2Log101Q,d2Transfer22S0,d2Transfer22Lo,d2Transfer22Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer22C0 d2Transfer22S0 d2Log101Q d2Log101Lo d2Log101Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log101Bounds
  have har : (((weightedUpper d2Transfer22C0 d2Log101Lo d2Log101Hi:ℚ):ℝ)) ≤ ((d2Transfer22Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer22Arithmetic
  linarith
#print axioms d2Transfer22Arithmetic
#print axioms d2Transfer22Bound
def d2Transfer23Lo : ℚ := (d2LitsNearTransfers002.q2 (41607233) 1 (-28))
def d2Transfer23Hi : ℚ := (d2LitsNearTransfers002.q2 (21642477) 1 (-27))
def d2Transfer23Cap : ℚ := (d2LitsNearTransfers002.q2 (2432512853) 1 (-40))
def d2Transfer23C0 : ℚ := (d2LitsNearTransfers002.q2 (1) 275 (-4))
def d2Transfer23S0 : ℚ := (d2LitsNearTransfers002.q2 (-1) 1 (0))
def d2Transfer23C1 : ℚ := (d2LitsNearTransfers002.q2 (-1) 55 (-3))
def d2Transfer23S1 : ℚ := (d2LitsNearTransfers002.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer23Arithmetic : weightedUpper d2Transfer23C0 d2Log101Lo d2Log101Hi + weightedUpper d2Transfer23C1 d2Log73Lo d2Log73Hi ≤ d2Transfer23Cap := by decide +kernel
theorem d2Transfer23Bound : ∀ x ∈ Set.Icc ((d2Transfer23Lo:ℚ):ℝ) ((d2Transfer23Hi:ℚ):ℝ), ((d2Transfer23C0:ℚ):ℝ)*Real.log |x-((d2Transfer23S0:ℚ):ℝ)| + ((d2Transfer23C1:ℚ):ℝ)*Real.log |x-((d2Transfer23S1:ℚ):ℝ)| ≤ ((d2Transfer23Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer23S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer23S0,d2Transfer23Lo,d2Transfer23Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer23C0 then |x-((d2Transfer23S0:ℚ):ℝ)| ≤ ((d2Log101Q:ℚ):ℝ) else ((d2Log101Q:ℚ):ℝ) ≤ |x-((d2Transfer23S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer23S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer23S0,d2Transfer23Lo,d2Transfer23Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer23C0,d2Log101Q,d2Transfer23S0,d2Transfer23Lo,d2Transfer23Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer23C0 d2Transfer23S0 d2Log101Q d2Log101Lo d2Log101Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log101Bounds
  have hn1 : x-((d2Transfer23S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer23S1,d2Transfer23Lo,d2Transfer23Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer23C1 then |x-((d2Transfer23S1:ℚ):ℝ)| ≤ ((d2Log73Q:ℚ):ℝ) else ((d2Log73Q:ℚ):ℝ) ≤ |x-((d2Transfer23S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer23S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer23S1,d2Transfer23Lo,d2Transfer23Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers002.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer23C1,d2Log73Q,d2Transfer23S1,d2Transfer23Lo,d2Transfer23Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer23C1 d2Transfer23S1 d2Log73Q d2Log73Lo d2Log73Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log73Bounds
  have har : (((weightedUpper d2Transfer23C0 d2Log101Lo d2Log101Hi:ℚ):ℝ) + ((weightedUpper d2Transfer23C1 d2Log73Lo d2Log73Hi:ℚ):ℝ)) ≤ ((d2Transfer23Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer23Arithmetic
  linarith
#print axioms d2Transfer23Arithmetic
#print axioms d2Transfer23Bound
end CatalanMeasure.GenD.Signed.Data.Cells

module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers002
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers002
open D72.LogTransfer
def d2WiderTransfer16Lo : ℚ := (d2LitsNearWiderTransfers002.q2 (18412957) 1 (-25))
def d2WiderTransfer16Hi : ℚ := (d2LitsNearWiderTransfers002.q2 (38503635) 1 (-26))
def d2WiderTransfer16Cap : ℚ := (d2LitsNearWiderTransfers002.q2 (648894057) 1 (-39))
def d2WiderTransfer16C0 : ℚ := (d2LitsNearWiderTransfers002.q2 (1) 25 (-4))
def d2WiderTransfer16S0 : ℚ := (d2LitsNearWiderTransfers002.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer16Arithmetic : weightedUpper d2WiderTransfer16C0 d2Log122Lo d2Log122Hi ≤ d2WiderTransfer16Cap := by decide +kernel
theorem d2WiderTransfer16Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer16Lo:ℚ):ℝ) ((d2WiderTransfer16Hi:ℚ):ℝ), ((d2WiderTransfer16C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer16S0:ℚ):ℝ)| ≤ ((d2WiderTransfer16Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer16S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer16S0,d2WiderTransfer16Lo,d2WiderTransfer16Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer16C0 then |x-((d2WiderTransfer16S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer16S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer16S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer16S0,d2WiderTransfer16Lo,d2WiderTransfer16Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer16C0,d2Log122Q,d2WiderTransfer16S0,d2WiderTransfer16Lo,d2WiderTransfer16Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer16C0 d2WiderTransfer16S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have har : (((weightedUpper d2WiderTransfer16C0 d2Log122Lo d2Log122Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer16Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer16Arithmetic
  linarith
#print axioms d2WiderTransfer16Arithmetic
#print axioms d2WiderTransfer16Bound
def d2WiderTransfer17Lo : ℚ := (d2LitsNearWiderTransfers002.q2 (18412957) 1 (-25))
def d2WiderTransfer17Hi : ℚ := (d2LitsNearWiderTransfers002.q2 (38503635) 1 (-26))
def d2WiderTransfer17Cap : ℚ := (d2LitsNearWiderTransfers002.q2 (2432512853) 1 (-40))
def d2WiderTransfer17C0 : ℚ := (d2LitsNearWiderTransfers002.q2 (1) 275 (-4))
def d2WiderTransfer17S0 : ℚ := (d2LitsNearWiderTransfers002.q2 (-1) 1 (0))
def d2WiderTransfer17C1 : ℚ := (d2LitsNearWiderTransfers002.q2 (-1) 55 (-3))
def d2WiderTransfer17S1 : ℚ := (d2LitsNearWiderTransfers002.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer17Arithmetic : weightedUpper d2WiderTransfer17C0 d2Log122Lo d2Log122Hi + weightedUpper d2WiderTransfer17C1 d2Log52Lo d2Log52Hi ≤ d2WiderTransfer17Cap := by decide +kernel
theorem d2WiderTransfer17Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer17Lo:ℚ):ℝ) ((d2WiderTransfer17Hi:ℚ):ℝ), ((d2WiderTransfer17C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer17S0:ℚ):ℝ)| + ((d2WiderTransfer17C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer17S1:ℚ):ℝ)| ≤ ((d2WiderTransfer17Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer17S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer17S0,d2WiderTransfer17Lo,d2WiderTransfer17Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer17C0 then |x-((d2WiderTransfer17S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer17S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer17S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer17S0,d2WiderTransfer17Lo,d2WiderTransfer17Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer17C0,d2Log122Q,d2WiderTransfer17S0,d2WiderTransfer17Lo,d2WiderTransfer17Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer17C0 d2WiderTransfer17S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have hn1 : x-((d2WiderTransfer17S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer17S1,d2WiderTransfer17Lo,d2WiderTransfer17Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer17C1 then |x-((d2WiderTransfer17S1:ℚ):ℝ)| ≤ ((d2Log52Q:ℚ):ℝ) else ((d2Log52Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer17S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer17S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer17S1,d2WiderTransfer17Lo,d2WiderTransfer17Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer17C1,d2Log52Q,d2WiderTransfer17S1,d2WiderTransfer17Lo,d2WiderTransfer17Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer17C1 d2WiderTransfer17S1 d2Log52Q d2Log52Lo d2Log52Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log52Bounds
  have har : (((weightedUpper d2WiderTransfer17C0 d2Log122Lo d2Log122Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer17C1 d2Log52Lo d2Log52Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer17Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer17Arithmetic
  linarith
#print axioms d2WiderTransfer17Arithmetic
#print axioms d2WiderTransfer17Bound
def d2WiderTransfer18Lo : ℚ := (d2LitsNearWiderTransfers002.q2 (38503635) 1 (-26))
def d2WiderTransfer18Hi : ℚ := (d2LitsNearWiderTransfers002.q2 (78684991) 1 (-27))
def d2WiderTransfer18Cap : ℚ := (d2LitsNearWiderTransfers002.q2 (648894057) 1 (-39))
def d2WiderTransfer18C0 : ℚ := (d2LitsNearWiderTransfers002.q2 (1) 25 (-4))
def d2WiderTransfer18S0 : ℚ := (d2LitsNearWiderTransfers002.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer18Arithmetic : weightedUpper d2WiderTransfer18C0 d2Log123Lo d2Log123Hi ≤ d2WiderTransfer18Cap := by decide +kernel
theorem d2WiderTransfer18Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer18Lo:ℚ):ℝ) ((d2WiderTransfer18Hi:ℚ):ℝ), ((d2WiderTransfer18C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer18S0:ℚ):ℝ)| ≤ ((d2WiderTransfer18Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer18S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer18S0,d2WiderTransfer18Lo,d2WiderTransfer18Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer18C0 then |x-((d2WiderTransfer18S0:ℚ):ℝ)| ≤ ((d2Log123Q:ℚ):ℝ) else ((d2Log123Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer18S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer18S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer18S0,d2WiderTransfer18Lo,d2WiderTransfer18Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer18C0,d2Log123Q,d2WiderTransfer18S0,d2WiderTransfer18Lo,d2WiderTransfer18Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer18C0 d2WiderTransfer18S0 d2Log123Q d2Log123Lo d2Log123Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log123Bounds
  have har : (((weightedUpper d2WiderTransfer18C0 d2Log123Lo d2Log123Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer18Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer18Arithmetic
  linarith
#print axioms d2WiderTransfer18Arithmetic
#print axioms d2WiderTransfer18Bound
def d2WiderTransfer19Lo : ℚ := (d2LitsNearWiderTransfers002.q2 (38503635) 1 (-26))
def d2WiderTransfer19Hi : ℚ := (d2LitsNearWiderTransfers002.q2 (78684991) 1 (-27))
def d2WiderTransfer19Cap : ℚ := (d2LitsNearWiderTransfers002.q2 (2432512853) 1 (-40))
def d2WiderTransfer19C0 : ℚ := (d2LitsNearWiderTransfers002.q2 (1) 275 (-4))
def d2WiderTransfer19S0 : ℚ := (d2LitsNearWiderTransfers002.q2 (-1) 1 (0))
def d2WiderTransfer19C1 : ℚ := (d2LitsNearWiderTransfers002.q2 (-1) 55 (-3))
def d2WiderTransfer19S1 : ℚ := (d2LitsNearWiderTransfers002.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer19Arithmetic : weightedUpper d2WiderTransfer19C0 d2Log123Lo d2Log123Hi + weightedUpper d2WiderTransfer19C1 d2Log51Lo d2Log51Hi ≤ d2WiderTransfer19Cap := by decide +kernel
theorem d2WiderTransfer19Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer19Lo:ℚ):ℝ) ((d2WiderTransfer19Hi:ℚ):ℝ), ((d2WiderTransfer19C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer19S0:ℚ):ℝ)| + ((d2WiderTransfer19C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer19S1:ℚ):ℝ)| ≤ ((d2WiderTransfer19Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer19S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer19S0,d2WiderTransfer19Lo,d2WiderTransfer19Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer19C0 then |x-((d2WiderTransfer19S0:ℚ):ℝ)| ≤ ((d2Log123Q:ℚ):ℝ) else ((d2Log123Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer19S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer19S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer19S0,d2WiderTransfer19Lo,d2WiderTransfer19Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer19C0,d2Log123Q,d2WiderTransfer19S0,d2WiderTransfer19Lo,d2WiderTransfer19Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer19C0 d2WiderTransfer19S0 d2Log123Q d2Log123Lo d2Log123Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log123Bounds
  have hn1 : x-((d2WiderTransfer19S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer19S1,d2WiderTransfer19Lo,d2WiderTransfer19Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer19C1 then |x-((d2WiderTransfer19S1:ℚ):ℝ)| ≤ ((d2Log51Q:ℚ):ℝ) else ((d2Log51Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer19S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer19S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer19S1,d2WiderTransfer19Lo,d2WiderTransfer19Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer19C1,d2Log51Q,d2WiderTransfer19S1,d2WiderTransfer19Lo,d2WiderTransfer19Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer19C1 d2WiderTransfer19S1 d2Log51Q d2Log51Lo d2Log51Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log51Bounds
  have har : (((weightedUpper d2WiderTransfer19C0 d2Log123Lo d2Log123Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer19C1 d2Log51Lo d2Log51Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer19Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer19Arithmetic
  linarith
#print axioms d2WiderTransfer19Arithmetic
#print axioms d2WiderTransfer19Bound
def d2WiderTransfer20Lo : ℚ := (d2LitsNearWiderTransfers002.q2 (78684991) 1 (-27))
def d2WiderTransfer20Hi : ℚ := (d2LitsNearWiderTransfers002.q2 (10045339) 1 (-24))
def d2WiderTransfer20Cap : ℚ := (d2LitsNearWiderTransfers002.q2 (648894057) 1 (-39))
def d2WiderTransfer20C0 : ℚ := (d2LitsNearWiderTransfers002.q2 (1) 25 (-4))
def d2WiderTransfer20S0 : ℚ := (d2LitsNearWiderTransfers002.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer20Arithmetic : weightedUpper d2WiderTransfer20C0 d2Log124Lo d2Log124Hi ≤ d2WiderTransfer20Cap := by decide +kernel
theorem d2WiderTransfer20Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer20Lo:ℚ):ℝ) ((d2WiderTransfer20Hi:ℚ):ℝ), ((d2WiderTransfer20C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer20S0:ℚ):ℝ)| ≤ ((d2WiderTransfer20Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer20S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer20S0,d2WiderTransfer20Lo,d2WiderTransfer20Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer20C0 then |x-((d2WiderTransfer20S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer20S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer20S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer20S0,d2WiderTransfer20Lo,d2WiderTransfer20Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer20C0,d2Log124Q,d2WiderTransfer20S0,d2WiderTransfer20Lo,d2WiderTransfer20Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer20C0 d2WiderTransfer20S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have har : (((weightedUpper d2WiderTransfer20C0 d2Log124Lo d2Log124Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer20Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer20Arithmetic
  linarith
#print axioms d2WiderTransfer20Arithmetic
#print axioms d2WiderTransfer20Bound
def d2WiderTransfer21Lo : ℚ := (d2LitsNearWiderTransfers002.q2 (78684991) 1 (-27))
def d2WiderTransfer21Hi : ℚ := (d2LitsNearWiderTransfers002.q2 (10045339) 1 (-24))
def d2WiderTransfer21Cap : ℚ := (d2LitsNearWiderTransfers002.q2 (2432512853) 1 (-40))
def d2WiderTransfer21C0 : ℚ := (d2LitsNearWiderTransfers002.q2 (1) 275 (-4))
def d2WiderTransfer21S0 : ℚ := (d2LitsNearWiderTransfers002.q2 (-1) 1 (0))
def d2WiderTransfer21C1 : ℚ := (d2LitsNearWiderTransfers002.q2 (-1) 55 (-3))
def d2WiderTransfer21S1 : ℚ := (d2LitsNearWiderTransfers002.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer21Arithmetic : weightedUpper d2WiderTransfer21C0 d2Log124Lo d2Log124Hi + weightedUpper d2WiderTransfer21C1 d2Log50Lo d2Log50Hi ≤ d2WiderTransfer21Cap := by decide +kernel
theorem d2WiderTransfer21Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer21Lo:ℚ):ℝ) ((d2WiderTransfer21Hi:ℚ):ℝ), ((d2WiderTransfer21C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer21S0:ℚ):ℝ)| + ((d2WiderTransfer21C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer21S1:ℚ):ℝ)| ≤ ((d2WiderTransfer21Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer21S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer21S0,d2WiderTransfer21Lo,d2WiderTransfer21Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer21C0 then |x-((d2WiderTransfer21S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer21S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer21S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer21S0,d2WiderTransfer21Lo,d2WiderTransfer21Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer21C0,d2Log124Q,d2WiderTransfer21S0,d2WiderTransfer21Lo,d2WiderTransfer21Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer21C0 d2WiderTransfer21S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have hn1 : x-((d2WiderTransfer21S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer21S1,d2WiderTransfer21Lo,d2WiderTransfer21Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer21C1 then |x-((d2WiderTransfer21S1:ℚ):ℝ)| ≤ ((d2Log50Q:ℚ):ℝ) else ((d2Log50Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer21S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer21S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer21S1,d2WiderTransfer21Lo,d2WiderTransfer21Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer21C1,d2Log50Q,d2WiderTransfer21S1,d2WiderTransfer21Lo,d2WiderTransfer21Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer21C1 d2WiderTransfer21S1 d2Log50Q d2Log50Lo d2Log50Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log50Bounds
  have har : (((weightedUpper d2WiderTransfer21C0 d2Log124Lo d2Log124Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer21C1 d2Log50Lo d2Log50Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer21Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer21Arithmetic
  linarith
#print axioms d2WiderTransfer21Arithmetic
#print axioms d2WiderTransfer21Bound
def d2WiderTransfer22Lo : ℚ := (d2LitsNearWiderTransfers002.q2 (10045339) 1 (-24))
def d2WiderTransfer22Hi : ℚ := (d2LitsNearWiderTransfers002.q2 (162403145) 1 (-28))
def d2WiderTransfer22Cap : ℚ := (d2LitsNearWiderTransfers002.q2 (358616464823175574959) 1 (-78))
def d2WiderTransfer22C0 : ℚ := (d2LitsNearWiderTransfers002.q2 (1) 25 (-4))
def d2WiderTransfer22S0 : ℚ := (d2LitsNearWiderTransfers002.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer22Arithmetic : weightedUpper d2WiderTransfer22C0 d2Log125Lo d2Log125Hi ≤ d2WiderTransfer22Cap := by decide +kernel
theorem d2WiderTransfer22Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer22Lo:ℚ):ℝ) ((d2WiderTransfer22Hi:ℚ):ℝ), ((d2WiderTransfer22C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer22S0:ℚ):ℝ)| ≤ ((d2WiderTransfer22Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer22S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer22S0,d2WiderTransfer22Lo,d2WiderTransfer22Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer22C0 then |x-((d2WiderTransfer22S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer22S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer22S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer22S0,d2WiderTransfer22Lo,d2WiderTransfer22Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer22C0,d2Log125Q,d2WiderTransfer22S0,d2WiderTransfer22Lo,d2WiderTransfer22Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer22C0 d2WiderTransfer22S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have har : (((weightedUpper d2WiderTransfer22C0 d2Log125Lo d2Log125Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer22Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer22Arithmetic
  linarith
#print axioms d2WiderTransfer22Arithmetic
#print axioms d2WiderTransfer22Bound
def d2WiderTransfer23Lo : ℚ := (d2LitsNearWiderTransfers002.q2 (10045339) 1 (-24))
def d2WiderTransfer23Hi : ℚ := (d2LitsNearWiderTransfers002.q2 (162403145) 1 (-28))
def d2WiderTransfer23Cap : ℚ := (d2LitsNearWiderTransfers002.q2 (670527226037072262575) 1 (-78))
def d2WiderTransfer23C0 : ℚ := (d2LitsNearWiderTransfers002.q2 (1) 275 (-4))
def d2WiderTransfer23S0 : ℚ := (d2LitsNearWiderTransfers002.q2 (-1) 1 (0))
def d2WiderTransfer23C1 : ℚ := (d2LitsNearWiderTransfers002.q2 (-1) 55 (-3))
def d2WiderTransfer23S1 : ℚ := (d2LitsNearWiderTransfers002.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer23Arithmetic : weightedUpper d2WiderTransfer23C0 d2Log125Lo d2Log125Hi + weightedUpper d2WiderTransfer23C1 d2Log49Lo d2Log49Hi ≤ d2WiderTransfer23Cap := by decide +kernel
theorem d2WiderTransfer23Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer23Lo:ℚ):ℝ) ((d2WiderTransfer23Hi:ℚ):ℝ), ((d2WiderTransfer23C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer23S0:ℚ):ℝ)| + ((d2WiderTransfer23C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer23S1:ℚ):ℝ)| ≤ ((d2WiderTransfer23Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer23S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer23S0,d2WiderTransfer23Lo,d2WiderTransfer23Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer23C0 then |x-((d2WiderTransfer23S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer23S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer23S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer23S0,d2WiderTransfer23Lo,d2WiderTransfer23Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer23C0,d2Log125Q,d2WiderTransfer23S0,d2WiderTransfer23Lo,d2WiderTransfer23Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer23C0 d2WiderTransfer23S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have hn1 : x-((d2WiderTransfer23S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer23S1,d2WiderTransfer23Lo,d2WiderTransfer23Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer23C1 then |x-((d2WiderTransfer23S1:ℚ):ℝ)| ≤ ((d2Log49Q:ℚ):ℝ) else ((d2Log49Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer23S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer23S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer23S1,d2WiderTransfer23Lo,d2WiderTransfer23Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer23C1,d2Log49Q,d2WiderTransfer23S1,d2WiderTransfer23Lo,d2WiderTransfer23Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer23C1 d2WiderTransfer23S1 d2Log49Q d2Log49Lo d2Log49Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log49Bounds
  have har : (((weightedUpper d2WiderTransfer23C0 d2Log125Lo d2Log125Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer23C1 d2Log49Lo d2Log49Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer23Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer23Arithmetic
  linarith
#print axioms d2WiderTransfer23Arithmetic
#print axioms d2WiderTransfer23Bound
end CatalanMeasure.GenD.Signed.Data.Cells

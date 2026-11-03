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
namespace d2LitsNearWiderTransfers017
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers017
open D72.LogTransfer
def d2WiderTransfer136Lo : ℚ := (d2LitsNearWiderTransfers017.q2 (333194895) 1 (-29))
def d2WiderTransfer136Hi : ℚ := (d2LitsNearWiderTransfers017.q2 (1334457301) 1 (-31))
def d2WiderTransfer136Cap : ℚ := (d2LitsNearWiderTransfers017.q2 (145729770427450393901) 1 (-73))
def d2WiderTransfer136C0 : ℚ := (d2LitsNearWiderTransfers017.q2 (1) 1 (-5))
def d2WiderTransfer136S0 : ℚ := (d2LitsNearWiderTransfers017.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer136Arithmetic : weightedUpper d2WiderTransfer136C0 d2Log136Lo d2Log136Hi ≤ d2WiderTransfer136Cap := by decide +kernel
theorem d2WiderTransfer136Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer136Lo:ℚ):ℝ) ((d2WiderTransfer136Hi:ℚ):ℝ), ((d2WiderTransfer136C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer136S0:ℚ):ℝ)| ≤ ((d2WiderTransfer136Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer136S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer136S0,d2WiderTransfer136Lo,d2WiderTransfer136Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer136C0 then |x-((d2WiderTransfer136S0:ℚ):ℝ)| ≤ ((d2Log136Q:ℚ):ℝ) else ((d2Log136Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer136S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer136S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer136S0,d2WiderTransfer136Lo,d2WiderTransfer136Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer136C0,d2Log136Q,d2WiderTransfer136S0,d2WiderTransfer136Lo,d2WiderTransfer136Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer136C0 d2WiderTransfer136S0 d2Log136Q d2Log136Lo d2Log136Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log136Bounds
  have har : (((weightedUpper d2WiderTransfer136C0 d2Log136Lo d2Log136Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer136Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer136Arithmetic
  linarith
#print axioms d2WiderTransfer136Arithmetic
#print axioms d2WiderTransfer136Bound
def d2WiderTransfer137Lo : ℚ := (d2LitsNearWiderTransfers017.q2 (333194895) 1 (-29))
def d2WiderTransfer137Hi : ℚ := (d2LitsNearWiderTransfers017.q2 (1334457301) 1 (-31))
def d2WiderTransfer137Cap : ℚ := (d2LitsNearWiderTransfers017.q2 (273580062007852795181) 1 (-73))
def d2WiderTransfer137C0 : ℚ := (d2LitsNearWiderTransfers017.q2 (1) 11 (-5))
def d2WiderTransfer137S0 : ℚ := (d2LitsNearWiderTransfers017.q2 (-1) 1 (0))
def d2WiderTransfer137C1 : ℚ := (d2LitsNearWiderTransfers017.q2 (-5) 11 (-4))
def d2WiderTransfer137S1 : ℚ := (d2LitsNearWiderTransfers017.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer137Arithmetic : weightedUpper d2WiderTransfer137C0 d2Log136Lo d2Log136Hi + weightedUpper d2WiderTransfer137C1 d2Log38Lo d2Log38Hi ≤ d2WiderTransfer137Cap := by decide +kernel
theorem d2WiderTransfer137Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer137Lo:ℚ):ℝ) ((d2WiderTransfer137Hi:ℚ):ℝ), ((d2WiderTransfer137C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer137S0:ℚ):ℝ)| + ((d2WiderTransfer137C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer137S1:ℚ):ℝ)| ≤ ((d2WiderTransfer137Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer137S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer137S0,d2WiderTransfer137Lo,d2WiderTransfer137Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer137C0 then |x-((d2WiderTransfer137S0:ℚ):ℝ)| ≤ ((d2Log136Q:ℚ):ℝ) else ((d2Log136Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer137S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer137S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer137S0,d2WiderTransfer137Lo,d2WiderTransfer137Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer137C0,d2Log136Q,d2WiderTransfer137S0,d2WiderTransfer137Lo,d2WiderTransfer137Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer137C0 d2WiderTransfer137S0 d2Log136Q d2Log136Lo d2Log136Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log136Bounds
  have hn1 : x-((d2WiderTransfer137S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer137S1,d2WiderTransfer137Lo,d2WiderTransfer137Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer137C1 then |x-((d2WiderTransfer137S1:ℚ):ℝ)| ≤ ((d2Log38Q:ℚ):ℝ) else ((d2Log38Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer137S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer137S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer137S1,d2WiderTransfer137Lo,d2WiderTransfer137Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer137C1,d2Log38Q,d2WiderTransfer137S1,d2WiderTransfer137Lo,d2WiderTransfer137Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer137C1 d2WiderTransfer137S1 d2Log38Q d2Log38Lo d2Log38Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log38Bounds
  have har : (((weightedUpper d2WiderTransfer137C0 d2Log136Lo d2Log136Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer137C1 d2Log38Lo d2Log38Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer137Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer137Arithmetic
  linarith
#print axioms d2WiderTransfer137Arithmetic
#print axioms d2WiderTransfer137Bound
def d2WiderTransfer138Lo : ℚ := (d2LitsNearWiderTransfers017.q2 (1334457301) 1 (-31))
def d2WiderTransfer138Hi : ℚ := (d2LitsNearWiderTransfers017.q2 (668067511) 1 (-30))
def d2WiderTransfer138Cap : ℚ := (d2LitsNearWiderTransfers017.q2 (2252647598101690118919) 1 (-80))
def d2WiderTransfer138C0 : ℚ := (d2LitsNearWiderTransfers017.q2 (1) 25 (-4))
def d2WiderTransfer138S0 : ℚ := (d2LitsNearWiderTransfers017.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer138Arithmetic : weightedUpper d2WiderTransfer138C0 d2Log137Lo d2Log137Hi ≤ d2WiderTransfer138Cap := by decide +kernel
theorem d2WiderTransfer138Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer138Lo:ℚ):ℝ) ((d2WiderTransfer138Hi:ℚ):ℝ), ((d2WiderTransfer138C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer138S0:ℚ):ℝ)| ≤ ((d2WiderTransfer138Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer138S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer138S0,d2WiderTransfer138Lo,d2WiderTransfer138Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer138C0 then |x-((d2WiderTransfer138S0:ℚ):ℝ)| ≤ ((d2Log137Q:ℚ):ℝ) else ((d2Log137Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer138S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer138S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer138S0,d2WiderTransfer138Lo,d2WiderTransfer138Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer138C0,d2Log137Q,d2WiderTransfer138S0,d2WiderTransfer138Lo,d2WiderTransfer138Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer138C0 d2WiderTransfer138S0 d2Log137Q d2Log137Lo d2Log137Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log137Bounds
  have har : (((weightedUpper d2WiderTransfer138C0 d2Log137Lo d2Log137Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer138Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer138Arithmetic
  linarith
#print axioms d2WiderTransfer138Arithmetic
#print axioms d2WiderTransfer138Bound
def d2WiderTransfer139Lo : ℚ := (d2LitsNearWiderTransfers017.q2 (1334457301) 1 (-31))
def d2WiderTransfer139Hi : ℚ := (d2LitsNearWiderTransfers017.q2 (668067511) 1 (-30))
def d2WiderTransfer139Cap : ℚ := (d2LitsNearWiderTransfers017.q2 (3502947766737425462023) 1 (-80))
def d2WiderTransfer139C0 : ℚ := (d2LitsNearWiderTransfers017.q2 (1) 275 (-4))
def d2WiderTransfer139S0 : ℚ := (d2LitsNearWiderTransfers017.q2 (-1) 1 (0))
def d2WiderTransfer139C1 : ℚ := (d2LitsNearWiderTransfers017.q2 (-1) 55 (-3))
def d2WiderTransfer139S1 : ℚ := (d2LitsNearWiderTransfers017.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer139Arithmetic : weightedUpper d2WiderTransfer139C0 d2Log137Lo d2Log137Hi + weightedUpper d2WiderTransfer139C1 d2Log37Lo d2Log37Hi ≤ d2WiderTransfer139Cap := by decide +kernel
theorem d2WiderTransfer139Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer139Lo:ℚ):ℝ) ((d2WiderTransfer139Hi:ℚ):ℝ), ((d2WiderTransfer139C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer139S0:ℚ):ℝ)| + ((d2WiderTransfer139C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer139S1:ℚ):ℝ)| ≤ ((d2WiderTransfer139Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer139S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer139S0,d2WiderTransfer139Lo,d2WiderTransfer139Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer139C0 then |x-((d2WiderTransfer139S0:ℚ):ℝ)| ≤ ((d2Log137Q:ℚ):ℝ) else ((d2Log137Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer139S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer139S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer139S0,d2WiderTransfer139Lo,d2WiderTransfer139Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer139C0,d2Log137Q,d2WiderTransfer139S0,d2WiderTransfer139Lo,d2WiderTransfer139Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer139C0 d2WiderTransfer139S0 d2Log137Q d2Log137Lo d2Log137Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log137Bounds
  have hn1 : x-((d2WiderTransfer139S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer139S1,d2WiderTransfer139Lo,d2WiderTransfer139Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer139C1 then |x-((d2WiderTransfer139S1:ℚ):ℝ)| ≤ ((d2Log37Q:ℚ):ℝ) else ((d2Log37Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer139S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer139S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer139S1,d2WiderTransfer139Lo,d2WiderTransfer139Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer139C1,d2Log37Q,d2WiderTransfer139S1,d2WiderTransfer139Lo,d2WiderTransfer139Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer139C1 d2WiderTransfer139S1 d2Log37Q d2Log37Lo d2Log37Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log37Bounds
  have har : (((weightedUpper d2WiderTransfer139C0 d2Log137Lo d2Log137Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer139C1 d2Log37Lo d2Log37Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer139Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer139Arithmetic
  linarith
#print axioms d2WiderTransfer139Arithmetic
#print axioms d2WiderTransfer139Bound
def d2WiderTransfer140Lo : ℚ := (d2LitsNearWiderTransfers017.q2 (1334457301) 1 (-31))
def d2WiderTransfer140Hi : ℚ := (d2LitsNearWiderTransfers017.q2 (668067511) 1 (-30))
def d2WiderTransfer140Cap : ℚ := (d2LitsNearWiderTransfers017.q2 (18726009857160385983239) 1 (-80))
def d2WiderTransfer140C0 : ℚ := (d2LitsNearWiderTransfers017.q2 (1) 1 (-5))
def d2WiderTransfer140S0 : ℚ := (d2LitsNearWiderTransfers017.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer140Arithmetic : weightedUpper d2WiderTransfer140C0 d2Log137Lo d2Log137Hi ≤ d2WiderTransfer140Cap := by decide +kernel
theorem d2WiderTransfer140Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer140Lo:ℚ):ℝ) ((d2WiderTransfer140Hi:ℚ):ℝ), ((d2WiderTransfer140C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer140S0:ℚ):ℝ)| ≤ ((d2WiderTransfer140Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer140S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer140S0,d2WiderTransfer140Lo,d2WiderTransfer140Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer140C0 then |x-((d2WiderTransfer140S0:ℚ):ℝ)| ≤ ((d2Log137Q:ℚ):ℝ) else ((d2Log137Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer140S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer140S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer140S0,d2WiderTransfer140Lo,d2WiderTransfer140Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer140C0,d2Log137Q,d2WiderTransfer140S0,d2WiderTransfer140Lo,d2WiderTransfer140Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer140C0 d2WiderTransfer140S0 d2Log137Q d2Log137Lo d2Log137Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log137Bounds
  have har : (((weightedUpper d2WiderTransfer140C0 d2Log137Lo d2Log137Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer140Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer140Arithmetic
  linarith
#print axioms d2WiderTransfer140Arithmetic
#print axioms d2WiderTransfer140Bound
def d2WiderTransfer141Lo : ℚ := (d2LitsNearWiderTransfers017.q2 (1334457301) 1 (-31))
def d2WiderTransfer141Hi : ℚ := (d2LitsNearWiderTransfers017.q2 (668067511) 1 (-30))
def d2WiderTransfer141Cap : ℚ := (d2LitsNearWiderTransfers017.q2 (35090847179451893347079) 1 (-80))
def d2WiderTransfer141C0 : ℚ := (d2LitsNearWiderTransfers017.q2 (1) 11 (-5))
def d2WiderTransfer141S0 : ℚ := (d2LitsNearWiderTransfers017.q2 (-1) 1 (0))
def d2WiderTransfer141C1 : ℚ := (d2LitsNearWiderTransfers017.q2 (-5) 11 (-4))
def d2WiderTransfer141S1 : ℚ := (d2LitsNearWiderTransfers017.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer141Arithmetic : weightedUpper d2WiderTransfer141C0 d2Log137Lo d2Log137Hi + weightedUpper d2WiderTransfer141C1 d2Log37Lo d2Log37Hi ≤ d2WiderTransfer141Cap := by decide +kernel
theorem d2WiderTransfer141Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer141Lo:ℚ):ℝ) ((d2WiderTransfer141Hi:ℚ):ℝ), ((d2WiderTransfer141C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer141S0:ℚ):ℝ)| + ((d2WiderTransfer141C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer141S1:ℚ):ℝ)| ≤ ((d2WiderTransfer141Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer141S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer141S0,d2WiderTransfer141Lo,d2WiderTransfer141Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer141C0 then |x-((d2WiderTransfer141S0:ℚ):ℝ)| ≤ ((d2Log137Q:ℚ):ℝ) else ((d2Log137Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer141S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer141S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer141S0,d2WiderTransfer141Lo,d2WiderTransfer141Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer141C0,d2Log137Q,d2WiderTransfer141S0,d2WiderTransfer141Lo,d2WiderTransfer141Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer141C0 d2WiderTransfer141S0 d2Log137Q d2Log137Lo d2Log137Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log137Bounds
  have hn1 : x-((d2WiderTransfer141S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer141S1,d2WiderTransfer141Lo,d2WiderTransfer141Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer141C1 then |x-((d2WiderTransfer141S1:ℚ):ℝ)| ≤ ((d2Log37Q:ℚ):ℝ) else ((d2Log37Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer141S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer141S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer141S1,d2WiderTransfer141Lo,d2WiderTransfer141Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer141C1,d2Log37Q,d2WiderTransfer141S1,d2WiderTransfer141Lo,d2WiderTransfer141Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer141C1 d2WiderTransfer141S1 d2Log37Q d2Log37Lo d2Log37Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log37Bounds
  have har : (((weightedUpper d2WiderTransfer141C0 d2Log137Lo d2Log137Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer141C1 d2Log37Lo d2Log37Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer141Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer141Arithmetic
  linarith
#print axioms d2WiderTransfer141Arithmetic
#print axioms d2WiderTransfer141Bound
def d2WiderTransfer142Lo : ℚ := (d2LitsNearWiderTransfers017.q2 (668067511) 1 (-30))
def d2WiderTransfer142Hi : ℚ := (d2LitsNearWiderTransfers017.q2 (1337812743) 1 (-31))
def d2WiderTransfer142Cap : ℚ := (d2LitsNearWiderTransfers017.q2 (1162696448405478776057) 1 (-79))
def d2WiderTransfer142C0 : ℚ := (d2LitsNearWiderTransfers017.q2 (1) 25 (-4))
def d2WiderTransfer142S0 : ℚ := (d2LitsNearWiderTransfers017.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer142Arithmetic : weightedUpper d2WiderTransfer142C0 d2Log138Lo d2Log138Hi ≤ d2WiderTransfer142Cap := by decide +kernel
theorem d2WiderTransfer142Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer142Lo:ℚ):ℝ) ((d2WiderTransfer142Hi:ℚ):ℝ), ((d2WiderTransfer142C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer142S0:ℚ):ℝ)| ≤ ((d2WiderTransfer142Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer142S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer142S0,d2WiderTransfer142Lo,d2WiderTransfer142Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer142C0 then |x-((d2WiderTransfer142S0:ℚ):ℝ)| ≤ ((d2Log138Q:ℚ):ℝ) else ((d2Log138Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer142S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer142S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer142S0,d2WiderTransfer142Lo,d2WiderTransfer142Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer142C0,d2Log138Q,d2WiderTransfer142S0,d2WiderTransfer142Lo,d2WiderTransfer142Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer142C0 d2WiderTransfer142S0 d2Log138Q d2Log138Lo d2Log138Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log138Bounds
  have har : (((weightedUpper d2WiderTransfer142C0 d2Log138Lo d2Log138Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer142Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer142Arithmetic
  linarith
#print axioms d2WiderTransfer142Arithmetic
#print axioms d2WiderTransfer142Bound
def d2WiderTransfer143Lo : ℚ := (d2LitsNearWiderTransfers017.q2 (668067511) 1 (-30))
def d2WiderTransfer143Hi : ℚ := (d2LitsNearWiderTransfers017.q2 (1337812743) 1 (-31))
def d2WiderTransfer143Cap : ℚ := (d2LitsNearWiderTransfers017.q2 (1787846532723346447609) 1 (-79))
def d2WiderTransfer143C0 : ℚ := (d2LitsNearWiderTransfers017.q2 (1) 275 (-4))
def d2WiderTransfer143S0 : ℚ := (d2LitsNearWiderTransfers017.q2 (-1) 1 (0))
def d2WiderTransfer143C1 : ℚ := (d2LitsNearWiderTransfers017.q2 (-1) 55 (-3))
def d2WiderTransfer143S1 : ℚ := (d2LitsNearWiderTransfers017.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer143Arithmetic : weightedUpper d2WiderTransfer143C0 d2Log138Lo d2Log138Hi + weightedUpper d2WiderTransfer143C1 d2Log36Lo d2Log36Hi ≤ d2WiderTransfer143Cap := by decide +kernel
theorem d2WiderTransfer143Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer143Lo:ℚ):ℝ) ((d2WiderTransfer143Hi:ℚ):ℝ), ((d2WiderTransfer143C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer143S0:ℚ):ℝ)| + ((d2WiderTransfer143C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer143S1:ℚ):ℝ)| ≤ ((d2WiderTransfer143Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer143S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer143S0,d2WiderTransfer143Lo,d2WiderTransfer143Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer143C0 then |x-((d2WiderTransfer143S0:ℚ):ℝ)| ≤ ((d2Log138Q:ℚ):ℝ) else ((d2Log138Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer143S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer143S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer143S0,d2WiderTransfer143Lo,d2WiderTransfer143Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer143C0,d2Log138Q,d2WiderTransfer143S0,d2WiderTransfer143Lo,d2WiderTransfer143Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer143C0 d2WiderTransfer143S0 d2Log138Q d2Log138Lo d2Log138Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log138Bounds
  have hn1 : x-((d2WiderTransfer143S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer143S1,d2WiderTransfer143Lo,d2WiderTransfer143Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer143C1 then |x-((d2WiderTransfer143S1:ℚ):ℝ)| ≤ ((d2Log36Q:ℚ):ℝ) else ((d2Log36Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer143S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer143S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer143S1,d2WiderTransfer143Lo,d2WiderTransfer143Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers017.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer143C1,d2Log36Q,d2WiderTransfer143S1,d2WiderTransfer143Lo,d2WiderTransfer143Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer143C1 d2WiderTransfer143S1 d2Log36Q d2Log36Lo d2Log36Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log36Bounds
  have har : (((weightedUpper d2WiderTransfer143C0 d2Log138Lo d2Log138Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer143C1 d2Log36Lo d2Log36Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer143Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer143Arithmetic
  linarith
#print axioms d2WiderTransfer143Arithmetic
#print axioms d2WiderTransfer143Bound
end CatalanMeasure.GenD.Signed.Data.Cells

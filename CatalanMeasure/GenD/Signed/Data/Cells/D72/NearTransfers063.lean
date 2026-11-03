module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
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
namespace d2LitsNearTransfers063
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers063
open D72.LogTransfer
def d2Transfer504Lo : ℚ := (d2LitsNearTransfers063.q2 (165758587) 1 (-28))
def d2Transfer504Hi : ℚ := (d2LitsNearTransfers063.q2 (333194895) 1 (-29))
def d2Transfer504Cap : ℚ := (d2LitsNearTransfers063.q2 (33631870487695382623017) 1 (-80))
def d2Transfer504C0 : ℚ := (d2LitsNearTransfers063.q2 (3) 275 (-5))
def d2Transfer504S0 : ℚ := (d2LitsNearTransfers063.q2 (-1) 1 (0))
def d2Transfer504C1 : ℚ := (d2LitsNearTransfers063.q2 (-5) 11 (-4))
def d2Transfer504S1 : ℚ := (d2LitsNearTransfers063.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer504Arithmetic : weightedUpper d2Transfer504C0 d2Log135Lo d2Log135Hi + weightedUpper d2Transfer504C1 d2Log39Lo d2Log39Hi ≤ d2Transfer504Cap := by decide +kernel
theorem d2Transfer504Bound : ∀ x ∈ Set.Icc ((d2Transfer504Lo:ℚ):ℝ) ((d2Transfer504Hi:ℚ):ℝ), ((d2Transfer504C0:ℚ):ℝ)*Real.log |x-((d2Transfer504S0:ℚ):ℝ)| + ((d2Transfer504C1:ℚ):ℝ)*Real.log |x-((d2Transfer504S1:ℚ):ℝ)| ≤ ((d2Transfer504Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer504S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer504S0,d2Transfer504Lo,d2Transfer504Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer504C0 then |x-((d2Transfer504S0:ℚ):ℝ)| ≤ ((d2Log135Q:ℚ):ℝ) else ((d2Log135Q:ℚ):ℝ) ≤ |x-((d2Transfer504S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer504S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer504S0,d2Transfer504Lo,d2Transfer504Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer504C0,d2Log135Q,d2Transfer504S0,d2Transfer504Lo,d2Transfer504Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer504C0 d2Transfer504S0 d2Log135Q d2Log135Lo d2Log135Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log135Bounds
  have hn1 : x-((d2Transfer504S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer504S1,d2Transfer504Lo,d2Transfer504Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer504C1 then |x-((d2Transfer504S1:ℚ):ℝ)| ≤ ((d2Log39Q:ℚ):ℝ) else ((d2Log39Q:ℚ):ℝ) ≤ |x-((d2Transfer504S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer504S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer504S1,d2Transfer504Lo,d2Transfer504Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer504C1,d2Log39Q,d2Transfer504S1,d2Transfer504Lo,d2Transfer504Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer504C1 d2Transfer504S1 d2Log39Q d2Log39Lo d2Log39Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log39Bounds
  have har : (((weightedUpper d2Transfer504C0 d2Log135Lo d2Log135Hi:ℚ):ℝ) + ((weightedUpper d2Transfer504C1 d2Log39Lo d2Log39Hi:ℚ):ℝ)) ≤ ((d2Transfer504Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer504Arithmetic
  linarith
#print axioms d2Transfer504Arithmetic
#print axioms d2Transfer504Bound
def d2Transfer505Lo : ℚ := (d2LitsNearTransfers063.q2 (333194895) 1 (-29))
def d2Transfer505Hi : ℚ := (d2LitsNearTransfers063.q2 (668067511) 1 (-30))
def d2Transfer505Cap : ℚ := (d2LitsNearTransfers063.q2 (1482581134158159655265) 1 (-80))
def d2Transfer505C0 : ℚ := (d2LitsNearTransfers063.q2 (-1) 55 (-3))
def d2Transfer505S0 : ℚ := (d2LitsNearTransfers063.q2 (-1) 1 (0))
def d2Transfer505C1 : ℚ := (d2LitsNearTransfers063.q2 (-1) 55 (-3))
def d2Transfer505S1 : ℚ := (d2LitsNearTransfers063.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer505Arithmetic : weightedUpper d2Transfer505C0 d2Log135Lo d2Log135Hi + weightedUpper d2Transfer505C1 d2Log37Lo d2Log37Hi ≤ d2Transfer505Cap := by decide +kernel
theorem d2Transfer505Bound : ∀ x ∈ Set.Icc ((d2Transfer505Lo:ℚ):ℝ) ((d2Transfer505Hi:ℚ):ℝ), ((d2Transfer505C0:ℚ):ℝ)*Real.log |x-((d2Transfer505S0:ℚ):ℝ)| + ((d2Transfer505C1:ℚ):ℝ)*Real.log |x-((d2Transfer505S1:ℚ):ℝ)| ≤ ((d2Transfer505Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer505S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer505S0,d2Transfer505Lo,d2Transfer505Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer505C0 then |x-((d2Transfer505S0:ℚ):ℝ)| ≤ ((d2Log135Q:ℚ):ℝ) else ((d2Log135Q:ℚ):ℝ) ≤ |x-((d2Transfer505S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer505S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer505S0,d2Transfer505Lo,d2Transfer505Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer505C0,d2Log135Q,d2Transfer505S0,d2Transfer505Lo,d2Transfer505Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer505C0 d2Transfer505S0 d2Log135Q d2Log135Lo d2Log135Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log135Bounds
  have hn1 : x-((d2Transfer505S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer505S1,d2Transfer505Lo,d2Transfer505Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer505C1 then |x-((d2Transfer505S1:ℚ):ℝ)| ≤ ((d2Log37Q:ℚ):ℝ) else ((d2Log37Q:ℚ):ℝ) ≤ |x-((d2Transfer505S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer505S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer505S1,d2Transfer505Lo,d2Transfer505Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer505C1,d2Log37Q,d2Transfer505S1,d2Transfer505Lo,d2Transfer505Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer505C1 d2Transfer505S1 d2Log37Q d2Log37Lo d2Log37Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log37Bounds
  have har : (((weightedUpper d2Transfer505C0 d2Log135Lo d2Log135Hi:ℚ):ℝ) + ((weightedUpper d2Transfer505C1 d2Log37Lo d2Log37Hi:ℚ):ℝ)) ≤ ((d2Transfer505Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer505Arithmetic
  linarith
#print axioms d2Transfer505Arithmetic
#print axioms d2Transfer505Bound
def d2Transfer506Lo : ℚ := (d2LitsNearTransfers063.q2 (333194895) 1 (-29))
def d2Transfer506Hi : ℚ := (d2LitsNearTransfers063.q2 (668067511) 1 (-30))
def d2Transfer506Cap : ℚ := (d2LitsNearTransfers063.q2 (16814377008084446589281) 1 (-80))
def d2Transfer506C0 : ℚ := (d2LitsNearTransfers063.q2 (23) 25 (-5))
def d2Transfer506S0 : ℚ := (d2LitsNearTransfers063.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer506Arithmetic : weightedUpper d2Transfer506C0 d2Log137Lo d2Log137Hi ≤ d2Transfer506Cap := by decide +kernel
theorem d2Transfer506Bound : ∀ x ∈ Set.Icc ((d2Transfer506Lo:ℚ):ℝ) ((d2Transfer506Hi:ℚ):ℝ), ((d2Transfer506C0:ℚ):ℝ)*Real.log |x-((d2Transfer506S0:ℚ):ℝ)| ≤ ((d2Transfer506Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer506S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer506S0,d2Transfer506Lo,d2Transfer506Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer506C0 then |x-((d2Transfer506S0:ℚ):ℝ)| ≤ ((d2Log137Q:ℚ):ℝ) else ((d2Log137Q:ℚ):ℝ) ≤ |x-((d2Transfer506S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer506S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer506S0,d2Transfer506Lo,d2Transfer506Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer506C0,d2Log137Q,d2Transfer506S0,d2Transfer506Lo,d2Transfer506Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer506C0 d2Transfer506S0 d2Log137Q d2Log137Lo d2Log137Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log137Bounds
  have har : (((weightedUpper d2Transfer506C0 d2Log137Lo d2Log137Hi:ℚ):ℝ)) ≤ ((d2Transfer506Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer506Arithmetic
  linarith
#print axioms d2Transfer506Arithmetic
#print axioms d2Transfer506Bound
def d2Transfer507Lo : ℚ := (d2LitsNearTransfers063.q2 (333194895) 1 (-29))
def d2Transfer507Hi : ℚ := (d2LitsNearTransfers063.q2 (668067511) 1 (-30))
def d2Transfer507Cap : ℚ := (d2LitsNearTransfers063.q2 (33665364399351716884833) 1 (-80))
def d2Transfer507C0 : ℚ := (d2LitsNearTransfers063.q2 (3) 275 (-5))
def d2Transfer507S0 : ℚ := (d2LitsNearTransfers063.q2 (-1) 1 (0))
def d2Transfer507C1 : ℚ := (d2LitsNearTransfers063.q2 (-5) 11 (-4))
def d2Transfer507S1 : ℚ := (d2LitsNearTransfers063.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer507Arithmetic : weightedUpper d2Transfer507C0 d2Log137Lo d2Log137Hi + weightedUpper d2Transfer507C1 d2Log37Lo d2Log37Hi ≤ d2Transfer507Cap := by decide +kernel
theorem d2Transfer507Bound : ∀ x ∈ Set.Icc ((d2Transfer507Lo:ℚ):ℝ) ((d2Transfer507Hi:ℚ):ℝ), ((d2Transfer507C0:ℚ):ℝ)*Real.log |x-((d2Transfer507S0:ℚ):ℝ)| + ((d2Transfer507C1:ℚ):ℝ)*Real.log |x-((d2Transfer507S1:ℚ):ℝ)| ≤ ((d2Transfer507Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer507S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer507S0,d2Transfer507Lo,d2Transfer507Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer507C0 then |x-((d2Transfer507S0:ℚ):ℝ)| ≤ ((d2Log137Q:ℚ):ℝ) else ((d2Log137Q:ℚ):ℝ) ≤ |x-((d2Transfer507S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer507S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer507S0,d2Transfer507Lo,d2Transfer507Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer507C0,d2Log137Q,d2Transfer507S0,d2Transfer507Lo,d2Transfer507Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer507C0 d2Transfer507S0 d2Log137Q d2Log137Lo d2Log137Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log137Bounds
  have hn1 : x-((d2Transfer507S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer507S1,d2Transfer507Lo,d2Transfer507Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer507C1 then |x-((d2Transfer507S1:ℚ):ℝ)| ≤ ((d2Log37Q:ℚ):ℝ) else ((d2Log37Q:ℚ):ℝ) ≤ |x-((d2Transfer507S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer507S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer507S1,d2Transfer507Lo,d2Transfer507Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer507C1,d2Log37Q,d2Transfer507S1,d2Transfer507Lo,d2Transfer507Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer507C1 d2Transfer507S1 d2Log37Q d2Log37Lo d2Log37Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log37Bounds
  have har : (((weightedUpper d2Transfer507C0 d2Log137Lo d2Log137Hi:ℚ):ℝ) + ((weightedUpper d2Transfer507C1 d2Log37Lo d2Log37Hi:ℚ):ℝ)) ≤ ((d2Transfer507Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer507Arithmetic
  linarith
#print axioms d2Transfer507Arithmetic
#print axioms d2Transfer507Bound
def d2Transfer508Lo : ℚ := (d2LitsNearTransfers063.q2 (668067511) 1 (-30))
def d2Transfer508Hi : ℚ := (d2LitsNearTransfers063.q2 (41859077) 1 (-26))
def d2Transfer508Cap : ℚ := (d2LitsNearTransfers063.q2 (1588671728036449488905) 1 (-80))
def d2Transfer508C0 : ℚ := (d2LitsNearTransfers063.q2 (-1) 55 (-3))
def d2Transfer508S0 : ℚ := (d2LitsNearTransfers063.q2 (-1) 1 (0))
def d2Transfer508C1 : ℚ := (d2LitsNearTransfers063.q2 (-1) 55 (-3))
def d2Transfer508S1 : ℚ := (d2LitsNearTransfers063.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer508Arithmetic : weightedUpper d2Transfer508C0 d2Log137Lo d2Log137Hi + weightedUpper d2Transfer508C1 d2Log35Lo d2Log35Hi ≤ d2Transfer508Cap := by decide +kernel
theorem d2Transfer508Bound : ∀ x ∈ Set.Icc ((d2Transfer508Lo:ℚ):ℝ) ((d2Transfer508Hi:ℚ):ℝ), ((d2Transfer508C0:ℚ):ℝ)*Real.log |x-((d2Transfer508S0:ℚ):ℝ)| + ((d2Transfer508C1:ℚ):ℝ)*Real.log |x-((d2Transfer508S1:ℚ):ℝ)| ≤ ((d2Transfer508Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer508S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer508S0,d2Transfer508Lo,d2Transfer508Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer508C0 then |x-((d2Transfer508S0:ℚ):ℝ)| ≤ ((d2Log137Q:ℚ):ℝ) else ((d2Log137Q:ℚ):ℝ) ≤ |x-((d2Transfer508S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer508S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer508S0,d2Transfer508Lo,d2Transfer508Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer508C0,d2Log137Q,d2Transfer508S0,d2Transfer508Lo,d2Transfer508Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer508C0 d2Transfer508S0 d2Log137Q d2Log137Lo d2Log137Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log137Bounds
  have hn1 : x-((d2Transfer508S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer508S1,d2Transfer508Lo,d2Transfer508Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer508C1 then |x-((d2Transfer508S1:ℚ):ℝ)| ≤ ((d2Log35Q:ℚ):ℝ) else ((d2Log35Q:ℚ):ℝ) ≤ |x-((d2Transfer508S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer508S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer508S1,d2Transfer508Lo,d2Transfer508Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer508C1,d2Log35Q,d2Transfer508S1,d2Transfer508Lo,d2Transfer508Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer508C1 d2Transfer508S1 d2Log35Q d2Log35Lo d2Log35Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log35Bounds
  have har : (((weightedUpper d2Transfer508C0 d2Log137Lo d2Log137Hi:ℚ):ℝ) + ((weightedUpper d2Transfer508C1 d2Log35Lo d2Log35Hi:ℚ):ℝ)) ≤ ((d2Transfer508Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer508Arithmetic
  linarith
#print axioms d2Transfer508Arithmetic
#print axioms d2Transfer508Bound
def d2Transfer509Lo : ℚ := (d2LitsNearTransfers063.q2 (668067511) 1 (-30))
def d2Transfer509Hi : ℚ := (d2LitsNearTransfers063.q2 (41859077) 1 (-26))
def d2Transfer509Cap : ℚ := (d2LitsNearTransfers063.q2 (16920467601962736422921) 1 (-80))
def d2Transfer509C0 : ℚ := (d2LitsNearTransfers063.q2 (23) 25 (-5))
def d2Transfer509S0 : ℚ := (d2LitsNearTransfers063.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer509Arithmetic : weightedUpper d2Transfer509C0 d2Log139Lo d2Log139Hi ≤ d2Transfer509Cap := by decide +kernel
theorem d2Transfer509Bound : ∀ x ∈ Set.Icc ((d2Transfer509Lo:ℚ):ℝ) ((d2Transfer509Hi:ℚ):ℝ), ((d2Transfer509C0:ℚ):ℝ)*Real.log |x-((d2Transfer509S0:ℚ):ℝ)| ≤ ((d2Transfer509Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer509S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer509S0,d2Transfer509Lo,d2Transfer509Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer509C0 then |x-((d2Transfer509S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2Transfer509S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer509S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer509S0,d2Transfer509Lo,d2Transfer509Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer509C0,d2Log139Q,d2Transfer509S0,d2Transfer509Lo,d2Transfer509Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer509C0 d2Transfer509S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have har : (((weightedUpper d2Transfer509C0 d2Log139Lo d2Log139Hi:ℚ):ℝ)) ≤ ((d2Transfer509Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer509Arithmetic
  linarith
#print axioms d2Transfer509Arithmetic
#print axioms d2Transfer509Bound
def d2Transfer510Lo : ℚ := (d2LitsNearTransfers063.q2 (668067511) 1 (-30))
def d2Transfer510Hi : ℚ := (d2LitsNearTransfers063.q2 (41859077) 1 (-26))
def d2Transfer510Cap : ℚ := (d2LitsNearTransfers063.q2 (33771454993230006718473) 1 (-80))
def d2Transfer510C0 : ℚ := (d2LitsNearTransfers063.q2 (3) 275 (-5))
def d2Transfer510S0 : ℚ := (d2LitsNearTransfers063.q2 (-1) 1 (0))
def d2Transfer510C1 : ℚ := (d2LitsNearTransfers063.q2 (-5) 11 (-4))
def d2Transfer510S1 : ℚ := (d2LitsNearTransfers063.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer510Arithmetic : weightedUpper d2Transfer510C0 d2Log139Lo d2Log139Hi + weightedUpper d2Transfer510C1 d2Log35Lo d2Log35Hi ≤ d2Transfer510Cap := by decide +kernel
theorem d2Transfer510Bound : ∀ x ∈ Set.Icc ((d2Transfer510Lo:ℚ):ℝ) ((d2Transfer510Hi:ℚ):ℝ), ((d2Transfer510C0:ℚ):ℝ)*Real.log |x-((d2Transfer510S0:ℚ):ℝ)| + ((d2Transfer510C1:ℚ):ℝ)*Real.log |x-((d2Transfer510S1:ℚ):ℝ)| ≤ ((d2Transfer510Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer510S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer510S0,d2Transfer510Lo,d2Transfer510Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer510C0 then |x-((d2Transfer510S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2Transfer510S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer510S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer510S0,d2Transfer510Lo,d2Transfer510Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer510C0,d2Log139Q,d2Transfer510S0,d2Transfer510Lo,d2Transfer510Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer510C0 d2Transfer510S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have hn1 : x-((d2Transfer510S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer510S1,d2Transfer510Lo,d2Transfer510Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer510C1 then |x-((d2Transfer510S1:ℚ):ℝ)| ≤ ((d2Log35Q:ℚ):ℝ) else ((d2Log35Q:ℚ):ℝ) ≤ |x-((d2Transfer510S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer510S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer510S1,d2Transfer510Lo,d2Transfer510Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer510C1,d2Log35Q,d2Transfer510S1,d2Transfer510Lo,d2Transfer510Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer510C1 d2Transfer510S1 d2Log35Q d2Log35Lo d2Log35Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log35Bounds
  have har : (((weightedUpper d2Transfer510C0 d2Log139Lo d2Log139Hi:ℚ):ℝ) + ((weightedUpper d2Transfer510C1 d2Log35Lo d2Log35Hi:ℚ):ℝ)) ≤ ((d2Transfer510Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer510Arithmetic
  linarith
#print axioms d2Transfer510Arithmetic
#print axioms d2Transfer510Bound
def d2Transfer511Lo : ℚ := (d2LitsNearTransfers063.q2 (41859077) 1 (-26))
def d2Transfer511Hi : ℚ := (d2LitsNearTransfers063.q2 (671422953) 1 (-30))
def d2Transfer511Cap : ℚ := (d2LitsNearTransfers063.q2 (432997801055116030553) 1 (-78))
def d2Transfer511C0 : ℚ := (d2LitsNearTransfers063.q2 (-1) 55 (-3))
def d2Transfer511S0 : ℚ := (d2LitsNearTransfers063.q2 (-1) 1 (0))
def d2Transfer511C1 : ℚ := (d2LitsNearTransfers063.q2 (-1) 55 (-3))
def d2Transfer511S1 : ℚ := (d2LitsNearTransfers063.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer511Arithmetic : weightedUpper d2Transfer511C0 d2Log139Lo d2Log139Hi + weightedUpper d2Transfer511C1 d2Log33Lo d2Log33Hi ≤ d2Transfer511Cap := by decide +kernel
theorem d2Transfer511Bound : ∀ x ∈ Set.Icc ((d2Transfer511Lo:ℚ):ℝ) ((d2Transfer511Hi:ℚ):ℝ), ((d2Transfer511C0:ℚ):ℝ)*Real.log |x-((d2Transfer511S0:ℚ):ℝ)| + ((d2Transfer511C1:ℚ):ℝ)*Real.log |x-((d2Transfer511S1:ℚ):ℝ)| ≤ ((d2Transfer511Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer511S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer511S0,d2Transfer511Lo,d2Transfer511Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer511C0 then |x-((d2Transfer511S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2Transfer511S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer511S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer511S0,d2Transfer511Lo,d2Transfer511Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer511C0,d2Log139Q,d2Transfer511S0,d2Transfer511Lo,d2Transfer511Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer511C0 d2Transfer511S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have hn1 : x-((d2Transfer511S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer511S1,d2Transfer511Lo,d2Transfer511Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer511C1 then |x-((d2Transfer511S1:ℚ):ℝ)| ≤ ((d2Log33Q:ℚ):ℝ) else ((d2Log33Q:ℚ):ℝ) ≤ |x-((d2Transfer511S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer511S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer511S1,d2Transfer511Lo,d2Transfer511Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers063.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer511C1,d2Log33Q,d2Transfer511S1,d2Transfer511Lo,d2Transfer511Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer511C1 d2Transfer511S1 d2Log33Q d2Log33Lo d2Log33Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log33Bounds
  have har : (((weightedUpper d2Transfer511C0 d2Log139Lo d2Log139Hi:ℚ):ℝ) + ((weightedUpper d2Transfer511C1 d2Log33Lo d2Log33Hi:ℚ):ℝ)) ≤ ((d2Transfer511Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer511Arithmetic
  linarith
#print axioms d2Transfer511Arithmetic
#print axioms d2Transfer511Bound
end CatalanMeasure.GenD.Signed.Data.Cells

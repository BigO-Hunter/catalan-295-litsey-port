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
namespace d2LitsNearWiderTransfers016
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers016
open D72.LogTransfer
def d2WiderTransfer128Lo : ℚ := (d2LitsNearWiderTransfers016.q2 (664712069) 1 (-30))
def d2WiderTransfer128Hi : ℚ := (d2LitsNearWiderTransfers016.q2 (1331101859) 1 (-31))
def d2WiderTransfer128Cap : ℚ := (d2LitsNearWiderTransfers016.q2 (72299405771334957823) 1 (-72))
def d2WiderTransfer128C0 : ℚ := (d2LitsNearWiderTransfers016.q2 (1) 1 (-5))
def d2WiderTransfer128S0 : ℚ := (d2LitsNearWiderTransfers016.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer128Arithmetic : weightedUpper d2WiderTransfer128C0 d2Log134Lo d2Log134Hi ≤ d2WiderTransfer128Cap := by decide +kernel
theorem d2WiderTransfer128Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer128Lo:ℚ):ℝ) ((d2WiderTransfer128Hi:ℚ):ℝ), ((d2WiderTransfer128C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer128S0:ℚ):ℝ)| ≤ ((d2WiderTransfer128Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer128S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer128S0,d2WiderTransfer128Lo,d2WiderTransfer128Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer128C0 then |x-((d2WiderTransfer128S0:ℚ):ℝ)| ≤ ((d2Log134Q:ℚ):ℝ) else ((d2Log134Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer128S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer128S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer128S0,d2WiderTransfer128Lo,d2WiderTransfer128Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer128C0,d2Log134Q,d2WiderTransfer128S0,d2WiderTransfer128Lo,d2WiderTransfer128Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer128C0 d2WiderTransfer128S0 d2Log134Q d2Log134Lo d2Log134Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log134Bounds
  have har : (((weightedUpper d2WiderTransfer128C0 d2Log134Lo d2Log134Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer128Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer128Arithmetic
  linarith
#print axioms d2WiderTransfer128Arithmetic
#print axioms d2WiderTransfer128Bound
def d2WiderTransfer129Lo : ℚ := (d2LitsNearWiderTransfers016.q2 (664712069) 1 (-30))
def d2WiderTransfer129Hi : ℚ := (d2LitsNearWiderTransfers016.q2 (1331101859) 1 (-31))
def d2WiderTransfer129Cap : ℚ := (d2LitsNearWiderTransfers016.q2 (136224551561536158463) 1 (-72))
def d2WiderTransfer129C0 : ℚ := (d2LitsNearWiderTransfers016.q2 (1) 11 (-5))
def d2WiderTransfer129S0 : ℚ := (d2LitsNearWiderTransfers016.q2 (-1) 1 (0))
def d2WiderTransfer129C1 : ℚ := (d2LitsNearWiderTransfers016.q2 (-5) 11 (-4))
def d2WiderTransfer129S1 : ℚ := (d2LitsNearWiderTransfers016.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer129Arithmetic : weightedUpper d2WiderTransfer129C0 d2Log134Lo d2Log134Hi + weightedUpper d2WiderTransfer129C1 d2Log40Lo d2Log40Hi ≤ d2WiderTransfer129Cap := by decide +kernel
theorem d2WiderTransfer129Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer129Lo:ℚ):ℝ) ((d2WiderTransfer129Hi:ℚ):ℝ), ((d2WiderTransfer129C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer129S0:ℚ):ℝ)| + ((d2WiderTransfer129C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer129S1:ℚ):ℝ)| ≤ ((d2WiderTransfer129Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer129S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer129S0,d2WiderTransfer129Lo,d2WiderTransfer129Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer129C0 then |x-((d2WiderTransfer129S0:ℚ):ℝ)| ≤ ((d2Log134Q:ℚ):ℝ) else ((d2Log134Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer129S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer129S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer129S0,d2WiderTransfer129Lo,d2WiderTransfer129Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer129C0,d2Log134Q,d2WiderTransfer129S0,d2WiderTransfer129Lo,d2WiderTransfer129Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer129C0 d2WiderTransfer129S0 d2Log134Q d2Log134Lo d2Log134Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log134Bounds
  have hn1 : x-((d2WiderTransfer129S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer129S1,d2WiderTransfer129Lo,d2WiderTransfer129Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer129C1 then |x-((d2WiderTransfer129S1:ℚ):ℝ)| ≤ ((d2Log40Q:ℚ):ℝ) else ((d2Log40Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer129S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer129S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer129S1,d2WiderTransfer129Lo,d2WiderTransfer129Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer129C1,d2Log40Q,d2WiderTransfer129S1,d2WiderTransfer129Lo,d2WiderTransfer129Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer129C1 d2WiderTransfer129S1 d2Log40Q d2Log40Lo d2Log40Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log40Bounds
  have har : (((weightedUpper d2WiderTransfer129C0 d2Log134Lo d2Log134Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer129C1 d2Log40Lo d2Log40Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer129Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer129Arithmetic
  linarith
#print axioms d2WiderTransfer129Arithmetic
#print axioms d2WiderTransfer129Bound
def d2WiderTransfer130Lo : ℚ := (d2LitsNearWiderTransfers016.q2 (1331101859) 1 (-31))
def d2WiderTransfer130Hi : ℚ := (d2LitsNearWiderTransfers016.q2 (333194895) 1 (-29))
def d2WiderTransfer130Cap : ℚ := (d2LitsNearWiderTransfers016.q2 (2107594563250375816115) 1 (-80))
def d2WiderTransfer130C0 : ℚ := (d2LitsNearWiderTransfers016.q2 (1) 25 (-4))
def d2WiderTransfer130S0 : ℚ := (d2LitsNearWiderTransfers016.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer130Arithmetic : weightedUpper d2WiderTransfer130C0 d2Log135Lo d2Log135Hi ≤ d2WiderTransfer130Cap := by decide +kernel
theorem d2WiderTransfer130Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer130Lo:ℚ):ℝ) ((d2WiderTransfer130Hi:ℚ):ℝ), ((d2WiderTransfer130C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer130S0:ℚ):ℝ)| ≤ ((d2WiderTransfer130Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer130S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer130S0,d2WiderTransfer130Lo,d2WiderTransfer130Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer130C0 then |x-((d2WiderTransfer130S0:ℚ):ℝ)| ≤ ((d2Log135Q:ℚ):ℝ) else ((d2Log135Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer130S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer130S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer130S0,d2WiderTransfer130Lo,d2WiderTransfer130Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer130C0,d2Log135Q,d2WiderTransfer130S0,d2WiderTransfer130Lo,d2WiderTransfer130Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer130C0 d2WiderTransfer130S0 d2Log135Q d2Log135Lo d2Log135Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log135Bounds
  have har : (((weightedUpper d2WiderTransfer130C0 d2Log135Lo d2Log135Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer130Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer130Arithmetic
  linarith
#print axioms d2WiderTransfer130Arithmetic
#print axioms d2WiderTransfer130Bound
def d2WiderTransfer131Lo : ℚ := (d2LitsNearWiderTransfers016.q2 (1331101859) 1 (-31))
def d2WiderTransfer131Hi : ℚ := (d2LitsNearWiderTransfers016.q2 (333194895) 1 (-29))
def d2WiderTransfer131Cap : ℚ := (d2LitsNearWiderTransfers016.q2 (3357894731886111159219) 1 (-80))
def d2WiderTransfer131C0 : ℚ := (d2LitsNearWiderTransfers016.q2 (1) 275 (-4))
def d2WiderTransfer131S0 : ℚ := (d2LitsNearWiderTransfers016.q2 (-1) 1 (0))
def d2WiderTransfer131C1 : ℚ := (d2LitsNearWiderTransfers016.q2 (-1) 55 (-3))
def d2WiderTransfer131S1 : ℚ := (d2LitsNearWiderTransfers016.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer131Arithmetic : weightedUpper d2WiderTransfer131C0 d2Log135Lo d2Log135Hi + weightedUpper d2WiderTransfer131C1 d2Log39Lo d2Log39Hi ≤ d2WiderTransfer131Cap := by decide +kernel
theorem d2WiderTransfer131Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer131Lo:ℚ):ℝ) ((d2WiderTransfer131Hi:ℚ):ℝ), ((d2WiderTransfer131C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer131S0:ℚ):ℝ)| + ((d2WiderTransfer131C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer131S1:ℚ):ℝ)| ≤ ((d2WiderTransfer131Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer131S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer131S0,d2WiderTransfer131Lo,d2WiderTransfer131Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer131C0 then |x-((d2WiderTransfer131S0:ℚ):ℝ)| ≤ ((d2Log135Q:ℚ):ℝ) else ((d2Log135Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer131S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer131S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer131S0,d2WiderTransfer131Lo,d2WiderTransfer131Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer131C0,d2Log135Q,d2WiderTransfer131S0,d2WiderTransfer131Lo,d2WiderTransfer131Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer131C0 d2WiderTransfer131S0 d2Log135Q d2Log135Lo d2Log135Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log135Bounds
  have hn1 : x-((d2WiderTransfer131S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer131S1,d2WiderTransfer131Lo,d2WiderTransfer131Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer131C1 then |x-((d2WiderTransfer131S1:ℚ):ℝ)| ≤ ((d2Log39Q:ℚ):ℝ) else ((d2Log39Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer131S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer131S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer131S1,d2WiderTransfer131Lo,d2WiderTransfer131Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer131C1,d2Log39Q,d2WiderTransfer131S1,d2WiderTransfer131Lo,d2WiderTransfer131Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer131C1 d2WiderTransfer131S1 d2Log39Q d2Log39Lo d2Log39Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log39Bounds
  have har : (((weightedUpper d2WiderTransfer131C0 d2Log135Lo d2Log135Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer131C1 d2Log39Lo d2Log39Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer131Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer131Arithmetic
  linarith
#print axioms d2WiderTransfer131Arithmetic
#print axioms d2WiderTransfer131Bound
def d2WiderTransfer132Lo : ℚ := (d2LitsNearWiderTransfers016.q2 (1331101859) 1 (-31))
def d2WiderTransfer132Hi : ℚ := (d2LitsNearWiderTransfers016.q2 (333194895) 1 (-29))
def d2WiderTransfer132Cap : ℚ := (d2LitsNearWiderTransfers016.q2 (18580956822309071680435) 1 (-80))
def d2WiderTransfer132C0 : ℚ := (d2LitsNearWiderTransfers016.q2 (1) 1 (-5))
def d2WiderTransfer132S0 : ℚ := (d2LitsNearWiderTransfers016.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer132Arithmetic : weightedUpper d2WiderTransfer132C0 d2Log135Lo d2Log135Hi ≤ d2WiderTransfer132Cap := by decide +kernel
theorem d2WiderTransfer132Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer132Lo:ℚ):ℝ) ((d2WiderTransfer132Hi:ℚ):ℝ), ((d2WiderTransfer132C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer132S0:ℚ):ℝ)| ≤ ((d2WiderTransfer132Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer132S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer132S0,d2WiderTransfer132Lo,d2WiderTransfer132Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer132C0 then |x-((d2WiderTransfer132S0:ℚ):ℝ)| ≤ ((d2Log135Q:ℚ):ℝ) else ((d2Log135Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer132S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer132S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer132S0,d2WiderTransfer132Lo,d2WiderTransfer132Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer132C0,d2Log135Q,d2WiderTransfer132S0,d2WiderTransfer132Lo,d2WiderTransfer132Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer132C0 d2WiderTransfer132S0 d2Log135Q d2Log135Lo d2Log135Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log135Bounds
  have har : (((weightedUpper d2WiderTransfer132C0 d2Log135Lo d2Log135Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer132Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer132Arithmetic
  linarith
#print axioms d2WiderTransfer132Arithmetic
#print axioms d2WiderTransfer132Bound
def d2WiderTransfer133Lo : ℚ := (d2LitsNearWiderTransfers016.q2 (1331101859) 1 (-31))
def d2WiderTransfer133Hi : ℚ := (d2LitsNearWiderTransfers016.q2 (333194895) 1 (-29))
def d2WiderTransfer133Cap : ℚ := (d2LitsNearWiderTransfers016.q2 (34945794144600579044275) 1 (-80))
def d2WiderTransfer133C0 : ℚ := (d2LitsNearWiderTransfers016.q2 (1) 11 (-5))
def d2WiderTransfer133S0 : ℚ := (d2LitsNearWiderTransfers016.q2 (-1) 1 (0))
def d2WiderTransfer133C1 : ℚ := (d2LitsNearWiderTransfers016.q2 (-5) 11 (-4))
def d2WiderTransfer133S1 : ℚ := (d2LitsNearWiderTransfers016.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer133Arithmetic : weightedUpper d2WiderTransfer133C0 d2Log135Lo d2Log135Hi + weightedUpper d2WiderTransfer133C1 d2Log39Lo d2Log39Hi ≤ d2WiderTransfer133Cap := by decide +kernel
theorem d2WiderTransfer133Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer133Lo:ℚ):ℝ) ((d2WiderTransfer133Hi:ℚ):ℝ), ((d2WiderTransfer133C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer133S0:ℚ):ℝ)| + ((d2WiderTransfer133C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer133S1:ℚ):ℝ)| ≤ ((d2WiderTransfer133Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer133S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer133S0,d2WiderTransfer133Lo,d2WiderTransfer133Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer133C0 then |x-((d2WiderTransfer133S0:ℚ):ℝ)| ≤ ((d2Log135Q:ℚ):ℝ) else ((d2Log135Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer133S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer133S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer133S0,d2WiderTransfer133Lo,d2WiderTransfer133Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer133C0,d2Log135Q,d2WiderTransfer133S0,d2WiderTransfer133Lo,d2WiderTransfer133Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer133C0 d2WiderTransfer133S0 d2Log135Q d2Log135Lo d2Log135Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log135Bounds
  have hn1 : x-((d2WiderTransfer133S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer133S1,d2WiderTransfer133Lo,d2WiderTransfer133Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer133C1 then |x-((d2WiderTransfer133S1:ℚ):ℝ)| ≤ ((d2Log39Q:ℚ):ℝ) else ((d2Log39Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer133S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer133S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer133S1,d2WiderTransfer133Lo,d2WiderTransfer133Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer133C1,d2Log39Q,d2WiderTransfer133S1,d2WiderTransfer133Lo,d2WiderTransfer133Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer133C1 d2WiderTransfer133S1 d2Log39Q d2Log39Lo d2Log39Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log39Bounds
  have har : (((weightedUpper d2WiderTransfer133C0 d2Log135Lo d2Log135Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer133C1 d2Log39Lo d2Log39Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer133Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer133Arithmetic
  linarith
#print axioms d2WiderTransfer133Arithmetic
#print axioms d2WiderTransfer133Bound
def d2WiderTransfer134Lo : ℚ := (d2LitsNearWiderTransfers016.q2 (333194895) 1 (-29))
def d2WiderTransfer134Hi : ℚ := (d2LitsNearWiderTransfers016.q2 (1334457301) 1 (-31))
def d2WiderTransfer134Cap : ℚ := (d2LitsNearWiderTransfers016.q2 (17031627778554332461) 1 (-73))
def d2WiderTransfer134C0 : ℚ := (d2LitsNearWiderTransfers016.q2 (1) 25 (-4))
def d2WiderTransfer134S0 : ℚ := (d2LitsNearWiderTransfers016.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer134Arithmetic : weightedUpper d2WiderTransfer134C0 d2Log136Lo d2Log136Hi ≤ d2WiderTransfer134Cap := by decide +kernel
theorem d2WiderTransfer134Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer134Lo:ℚ):ℝ) ((d2WiderTransfer134Hi:ℚ):ℝ), ((d2WiderTransfer134C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer134S0:ℚ):ℝ)| ≤ ((d2WiderTransfer134Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer134S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer134S0,d2WiderTransfer134Lo,d2WiderTransfer134Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer134C0 then |x-((d2WiderTransfer134S0:ℚ):ℝ)| ≤ ((d2Log136Q:ℚ):ℝ) else ((d2Log136Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer134S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer134S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer134S0,d2WiderTransfer134Lo,d2WiderTransfer134Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer134C0,d2Log136Q,d2WiderTransfer134S0,d2WiderTransfer134Lo,d2WiderTransfer134Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer134C0 d2WiderTransfer134S0 d2Log136Q d2Log136Lo d2Log136Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log136Bounds
  have har : (((weightedUpper d2WiderTransfer134C0 d2Log136Lo d2Log136Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer134Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer134Arithmetic
  linarith
#print axioms d2WiderTransfer134Arithmetic
#print axioms d2WiderTransfer134Bound
def d2WiderTransfer135Lo : ℚ := (d2LitsNearWiderTransfers016.q2 (333194895) 1 (-29))
def d2WiderTransfer135Hi : ℚ := (d2LitsNearWiderTransfers016.q2 (1334457301) 1 (-31))
def d2WiderTransfer135Cap : ℚ := (d2LitsNearWiderTransfers016.q2 (26799597846021014829) 1 (-73))
def d2WiderTransfer135C0 : ℚ := (d2LitsNearWiderTransfers016.q2 (1) 275 (-4))
def d2WiderTransfer135S0 : ℚ := (d2LitsNearWiderTransfers016.q2 (-1) 1 (0))
def d2WiderTransfer135C1 : ℚ := (d2LitsNearWiderTransfers016.q2 (-1) 55 (-3))
def d2WiderTransfer135S1 : ℚ := (d2LitsNearWiderTransfers016.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer135Arithmetic : weightedUpper d2WiderTransfer135C0 d2Log136Lo d2Log136Hi + weightedUpper d2WiderTransfer135C1 d2Log38Lo d2Log38Hi ≤ d2WiderTransfer135Cap := by decide +kernel
theorem d2WiderTransfer135Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer135Lo:ℚ):ℝ) ((d2WiderTransfer135Hi:ℚ):ℝ), ((d2WiderTransfer135C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer135S0:ℚ):ℝ)| + ((d2WiderTransfer135C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer135S1:ℚ):ℝ)| ≤ ((d2WiderTransfer135Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer135S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer135S0,d2WiderTransfer135Lo,d2WiderTransfer135Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer135C0 then |x-((d2WiderTransfer135S0:ℚ):ℝ)| ≤ ((d2Log136Q:ℚ):ℝ) else ((d2Log136Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer135S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer135S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer135S0,d2WiderTransfer135Lo,d2WiderTransfer135Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer135C0,d2Log136Q,d2WiderTransfer135S0,d2WiderTransfer135Lo,d2WiderTransfer135Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer135C0 d2WiderTransfer135S0 d2Log136Q d2Log136Lo d2Log136Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log136Bounds
  have hn1 : x-((d2WiderTransfer135S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer135S1,d2WiderTransfer135Lo,d2WiderTransfer135Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer135C1 then |x-((d2WiderTransfer135S1:ℚ):ℝ)| ≤ ((d2Log38Q:ℚ):ℝ) else ((d2Log38Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer135S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer135S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer135S1,d2WiderTransfer135Lo,d2WiderTransfer135Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers016.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer135C1,d2Log38Q,d2WiderTransfer135S1,d2WiderTransfer135Lo,d2WiderTransfer135Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer135C1 d2WiderTransfer135S1 d2Log38Q d2Log38Lo d2Log38Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log38Bounds
  have har : (((weightedUpper d2WiderTransfer135C0 d2Log136Lo d2Log136Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer135C1 d2Log38Lo d2Log38Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer135Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer135Arithmetic
  linarith
#print axioms d2WiderTransfer135Arithmetic
#print axioms d2WiderTransfer135Bound
end CatalanMeasure.GenD.Signed.Data.Cells

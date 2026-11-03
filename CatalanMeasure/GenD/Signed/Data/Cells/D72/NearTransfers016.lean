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
namespace d2LitsNearTransfers016
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers016
open D72.LogTransfer
def d2Transfer128Lo : ℚ := (d2LitsNearTransfers016.q2 (38251791) 1 (-28))
def d2Transfer128Hi : ℚ := (d2LitsNearTransfers016.q2 (4991189) 1 (-25))
def d2Transfer128Cap : ℚ := (d2LitsNearTransfers016.q2 (16281318465) 1 (-40))
def d2Transfer128C0 : ℚ := (d2LitsNearTransfers016.q2 (1) 1 (-5))
def d2Transfer128S0 : ℚ := (d2LitsNearTransfers016.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer128Arithmetic : weightedUpper d2Transfer128C0 d2Log99Lo d2Log99Hi ≤ d2Transfer128Cap := by decide +kernel
theorem d2Transfer128Bound : ∀ x ∈ Set.Icc ((d2Transfer128Lo:ℚ):ℝ) ((d2Transfer128Hi:ℚ):ℝ), ((d2Transfer128C0:ℚ):ℝ)*Real.log |x-((d2Transfer128S0:ℚ):ℝ)| ≤ ((d2Transfer128Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer128S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer128S0,d2Transfer128Lo,d2Transfer128Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer128C0 then |x-((d2Transfer128S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2Transfer128S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer128S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer128S0,d2Transfer128Lo,d2Transfer128Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer128C0,d2Log99Q,d2Transfer128S0,d2Transfer128Lo,d2Transfer128Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer128C0 d2Transfer128S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have har : (((weightedUpper d2Transfer128C0 d2Log99Lo d2Log99Hi:ℚ):ℝ)) ≤ ((d2Transfer128Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer128Arithmetic
  linarith
#print axioms d2Transfer128Arithmetic
#print axioms d2Transfer128Bound
def d2Transfer129Lo : ℚ := (d2LitsNearTransfers016.q2 (38251791) 1 (-28))
def d2Transfer129Hi : ℚ := (d2LitsNearTransfers016.q2 (4991189) 1 (-25))
def d2Transfer129Cap : ℚ := (d2LitsNearTransfers016.q2 (31165051305) 1 (-40))
def d2Transfer129C0 : ℚ := (d2LitsNearTransfers016.q2 (1) 11 (-5))
def d2Transfer129S0 : ℚ := (d2LitsNearTransfers016.q2 (-1) 1 (0))
def d2Transfer129C1 : ℚ := (d2LitsNearTransfers016.q2 (-5) 11 (-4))
def d2Transfer129S1 : ℚ := (d2LitsNearTransfers016.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer129Arithmetic : weightedUpper d2Transfer129C0 d2Log99Lo d2Log99Hi + weightedUpper d2Transfer129C1 d2Log75Lo d2Log75Hi ≤ d2Transfer129Cap := by decide +kernel
theorem d2Transfer129Bound : ∀ x ∈ Set.Icc ((d2Transfer129Lo:ℚ):ℝ) ((d2Transfer129Hi:ℚ):ℝ), ((d2Transfer129C0:ℚ):ℝ)*Real.log |x-((d2Transfer129S0:ℚ):ℝ)| + ((d2Transfer129C1:ℚ):ℝ)*Real.log |x-((d2Transfer129S1:ℚ):ℝ)| ≤ ((d2Transfer129Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer129S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer129S0,d2Transfer129Lo,d2Transfer129Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer129C0 then |x-((d2Transfer129S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2Transfer129S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer129S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer129S0,d2Transfer129Lo,d2Transfer129Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer129C0,d2Log99Q,d2Transfer129S0,d2Transfer129Lo,d2Transfer129Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer129C0 d2Transfer129S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have hn1 : x-((d2Transfer129S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer129S1,d2Transfer129Lo,d2Transfer129Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer129C1 then |x-((d2Transfer129S1:ℚ):ℝ)| ≤ ((d2Log75Q:ℚ):ℝ) else ((d2Log75Q:ℚ):ℝ) ≤ |x-((d2Transfer129S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer129S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer129S1,d2Transfer129Lo,d2Transfer129Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer129C1,d2Log75Q,d2Transfer129S1,d2Transfer129Lo,d2Transfer129Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer129C1 d2Transfer129S1 d2Log75Q d2Log75Lo d2Log75Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log75Bounds
  have har : (((weightedUpper d2Transfer129C0 d2Log99Lo d2Log99Hi:ℚ):ℝ) + ((weightedUpper d2Transfer129C1 d2Log75Lo d2Log75Hi:ℚ):ℝ)) ≤ ((d2Transfer129Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer129Arithmetic
  linarith
#print axioms d2Transfer129Arithmetic
#print axioms d2Transfer129Bound
def d2Transfer130Lo : ℚ := (d2LitsNearTransfers016.q2 (4991189) 1 (-25))
def d2Transfer130Hi : ℚ := (d2LitsNearTransfers016.q2 (41607233) 1 (-28))
def d2Transfer130Cap : ℚ := (d2LitsNearTransfers016.q2 (649441385) 1 (-39))
def d2Transfer130C0 : ℚ := (d2LitsNearTransfers016.q2 (1) 25 (-4))
def d2Transfer130S0 : ℚ := (d2LitsNearTransfers016.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer130Arithmetic : weightedUpper d2Transfer130C0 d2Log100Lo d2Log100Hi ≤ d2Transfer130Cap := by decide +kernel
theorem d2Transfer130Bound : ∀ x ∈ Set.Icc ((d2Transfer130Lo:ℚ):ℝ) ((d2Transfer130Hi:ℚ):ℝ), ((d2Transfer130C0:ℚ):ℝ)*Real.log |x-((d2Transfer130S0:ℚ):ℝ)| ≤ ((d2Transfer130Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer130S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer130S0,d2Transfer130Lo,d2Transfer130Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer130C0 then |x-((d2Transfer130S0:ℚ):ℝ)| ≤ ((d2Log100Q:ℚ):ℝ) else ((d2Log100Q:ℚ):ℝ) ≤ |x-((d2Transfer130S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer130S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer130S0,d2Transfer130Lo,d2Transfer130Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer130C0,d2Log100Q,d2Transfer130S0,d2Transfer130Lo,d2Transfer130Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer130C0 d2Transfer130S0 d2Log100Q d2Log100Lo d2Log100Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log100Bounds
  have har : (((weightedUpper d2Transfer130C0 d2Log100Lo d2Log100Hi:ℚ):ℝ)) ≤ ((d2Transfer130Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer130Arithmetic
  linarith
#print axioms d2Transfer130Arithmetic
#print axioms d2Transfer130Bound
def d2Transfer131Lo : ℚ := (d2LitsNearTransfers016.q2 (4991189) 1 (-25))
def d2Transfer131Hi : ℚ := (d2LitsNearTransfers016.q2 (41607233) 1 (-28))
def d2Transfer131Cap : ℚ := (d2LitsNearTransfers016.q2 (2436024149) 1 (-40))
def d2Transfer131C0 : ℚ := (d2LitsNearTransfers016.q2 (1) 275 (-4))
def d2Transfer131S0 : ℚ := (d2LitsNearTransfers016.q2 (-1) 1 (0))
def d2Transfer131C1 : ℚ := (d2LitsNearTransfers016.q2 (-1) 55 (-3))
def d2Transfer131S1 : ℚ := (d2LitsNearTransfers016.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer131Arithmetic : weightedUpper d2Transfer131C0 d2Log100Lo d2Log100Hi + weightedUpper d2Transfer131C1 d2Log74Lo d2Log74Hi ≤ d2Transfer131Cap := by decide +kernel
theorem d2Transfer131Bound : ∀ x ∈ Set.Icc ((d2Transfer131Lo:ℚ):ℝ) ((d2Transfer131Hi:ℚ):ℝ), ((d2Transfer131C0:ℚ):ℝ)*Real.log |x-((d2Transfer131S0:ℚ):ℝ)| + ((d2Transfer131C1:ℚ):ℝ)*Real.log |x-((d2Transfer131S1:ℚ):ℝ)| ≤ ((d2Transfer131Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer131S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer131S0,d2Transfer131Lo,d2Transfer131Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer131C0 then |x-((d2Transfer131S0:ℚ):ℝ)| ≤ ((d2Log100Q:ℚ):ℝ) else ((d2Log100Q:ℚ):ℝ) ≤ |x-((d2Transfer131S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer131S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer131S0,d2Transfer131Lo,d2Transfer131Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer131C0,d2Log100Q,d2Transfer131S0,d2Transfer131Lo,d2Transfer131Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer131C0 d2Transfer131S0 d2Log100Q d2Log100Lo d2Log100Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log100Bounds
  have hn1 : x-((d2Transfer131S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer131S1,d2Transfer131Lo,d2Transfer131Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer131C1 then |x-((d2Transfer131S1:ℚ):ℝ)| ≤ ((d2Log74Q:ℚ):ℝ) else ((d2Log74Q:ℚ):ℝ) ≤ |x-((d2Transfer131S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer131S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer131S1,d2Transfer131Lo,d2Transfer131Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer131C1,d2Log74Q,d2Transfer131S1,d2Transfer131Lo,d2Transfer131Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer131C1 d2Transfer131S1 d2Log74Q d2Log74Lo d2Log74Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log74Bounds
  have har : (((weightedUpper d2Transfer131C0 d2Log100Lo d2Log100Hi:ℚ):ℝ) + ((weightedUpper d2Transfer131C1 d2Log74Lo d2Log74Hi:ℚ):ℝ)) ≤ ((d2Transfer131Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer131Arithmetic
  linarith
#print axioms d2Transfer131Arithmetic
#print axioms d2Transfer131Bound
def d2Transfer132Lo : ℚ := (d2LitsNearTransfers016.q2 (4991189) 1 (-25))
def d2Transfer132Hi : ℚ := (d2LitsNearTransfers016.q2 (41607233) 1 (-28))
def d2Transfer132Cap : ℚ := (d2LitsNearTransfers016.q2 (16281318465) 1 (-40))
def d2Transfer132C0 : ℚ := (d2LitsNearTransfers016.q2 (1) 1 (-5))
def d2Transfer132S0 : ℚ := (d2LitsNearTransfers016.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer132Arithmetic : weightedUpper d2Transfer132C0 d2Log100Lo d2Log100Hi ≤ d2Transfer132Cap := by decide +kernel
theorem d2Transfer132Bound : ∀ x ∈ Set.Icc ((d2Transfer132Lo:ℚ):ℝ) ((d2Transfer132Hi:ℚ):ℝ), ((d2Transfer132C0:ℚ):ℝ)*Real.log |x-((d2Transfer132S0:ℚ):ℝ)| ≤ ((d2Transfer132Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer132S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer132S0,d2Transfer132Lo,d2Transfer132Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer132C0 then |x-((d2Transfer132S0:ℚ):ℝ)| ≤ ((d2Log100Q:ℚ):ℝ) else ((d2Log100Q:ℚ):ℝ) ≤ |x-((d2Transfer132S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer132S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer132S0,d2Transfer132Lo,d2Transfer132Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer132C0,d2Log100Q,d2Transfer132S0,d2Transfer132Lo,d2Transfer132Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer132C0 d2Transfer132S0 d2Log100Q d2Log100Lo d2Log100Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log100Bounds
  have har : (((weightedUpper d2Transfer132C0 d2Log100Lo d2Log100Hi:ℚ):ℝ)) ≤ ((d2Transfer132Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer132Arithmetic
  linarith
#print axioms d2Transfer132Arithmetic
#print axioms d2Transfer132Bound
def d2Transfer133Lo : ℚ := (d2LitsNearTransfers016.q2 (4991189) 1 (-25))
def d2Transfer133Hi : ℚ := (d2LitsNearTransfers016.q2 (41607233) 1 (-28))
def d2Transfer133Cap : ℚ := (d2LitsNearTransfers016.q2 (31165051305) 1 (-40))
def d2Transfer133C0 : ℚ := (d2LitsNearTransfers016.q2 (1) 11 (-5))
def d2Transfer133S0 : ℚ := (d2LitsNearTransfers016.q2 (-1) 1 (0))
def d2Transfer133C1 : ℚ := (d2LitsNearTransfers016.q2 (-5) 11 (-4))
def d2Transfer133S1 : ℚ := (d2LitsNearTransfers016.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer133Arithmetic : weightedUpper d2Transfer133C0 d2Log100Lo d2Log100Hi + weightedUpper d2Transfer133C1 d2Log74Lo d2Log74Hi ≤ d2Transfer133Cap := by decide +kernel
theorem d2Transfer133Bound : ∀ x ∈ Set.Icc ((d2Transfer133Lo:ℚ):ℝ) ((d2Transfer133Hi:ℚ):ℝ), ((d2Transfer133C0:ℚ):ℝ)*Real.log |x-((d2Transfer133S0:ℚ):ℝ)| + ((d2Transfer133C1:ℚ):ℝ)*Real.log |x-((d2Transfer133S1:ℚ):ℝ)| ≤ ((d2Transfer133Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer133S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer133S0,d2Transfer133Lo,d2Transfer133Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer133C0 then |x-((d2Transfer133S0:ℚ):ℝ)| ≤ ((d2Log100Q:ℚ):ℝ) else ((d2Log100Q:ℚ):ℝ) ≤ |x-((d2Transfer133S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer133S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer133S0,d2Transfer133Lo,d2Transfer133Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer133C0,d2Log100Q,d2Transfer133S0,d2Transfer133Lo,d2Transfer133Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer133C0 d2Transfer133S0 d2Log100Q d2Log100Lo d2Log100Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log100Bounds
  have hn1 : x-((d2Transfer133S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer133S1,d2Transfer133Lo,d2Transfer133Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer133C1 then |x-((d2Transfer133S1:ℚ):ℝ)| ≤ ((d2Log74Q:ℚ):ℝ) else ((d2Log74Q:ℚ):ℝ) ≤ |x-((d2Transfer133S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer133S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer133S1,d2Transfer133Lo,d2Transfer133Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer133C1,d2Log74Q,d2Transfer133S1,d2Transfer133Lo,d2Transfer133Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer133C1 d2Transfer133S1 d2Log74Q d2Log74Lo d2Log74Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log74Bounds
  have har : (((weightedUpper d2Transfer133C0 d2Log100Lo d2Log100Hi:ℚ):ℝ) + ((weightedUpper d2Transfer133C1 d2Log74Lo d2Log74Hi:ℚ):ℝ)) ≤ ((d2Transfer133Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer133Arithmetic
  linarith
#print axioms d2Transfer133Arithmetic
#print axioms d2Transfer133Bound
def d2Transfer134Lo : ℚ := (d2LitsNearTransfers016.q2 (41607233) 1 (-28))
def d2Transfer134Hi : ℚ := (d2LitsNearTransfers016.q2 (21642477) 1 (-27))
def d2Transfer134Cap : ℚ := (d2LitsNearTransfers016.q2 (649441385) 1 (-39))
def d2Transfer134C0 : ℚ := (d2LitsNearTransfers016.q2 (1) 25 (-4))
def d2Transfer134S0 : ℚ := (d2LitsNearTransfers016.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer134Arithmetic : weightedUpper d2Transfer134C0 d2Log101Lo d2Log101Hi ≤ d2Transfer134Cap := by decide +kernel
theorem d2Transfer134Bound : ∀ x ∈ Set.Icc ((d2Transfer134Lo:ℚ):ℝ) ((d2Transfer134Hi:ℚ):ℝ), ((d2Transfer134C0:ℚ):ℝ)*Real.log |x-((d2Transfer134S0:ℚ):ℝ)| ≤ ((d2Transfer134Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer134S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer134S0,d2Transfer134Lo,d2Transfer134Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer134C0 then |x-((d2Transfer134S0:ℚ):ℝ)| ≤ ((d2Log101Q:ℚ):ℝ) else ((d2Log101Q:ℚ):ℝ) ≤ |x-((d2Transfer134S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer134S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer134S0,d2Transfer134Lo,d2Transfer134Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer134C0,d2Log101Q,d2Transfer134S0,d2Transfer134Lo,d2Transfer134Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer134C0 d2Transfer134S0 d2Log101Q d2Log101Lo d2Log101Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log101Bounds
  have har : (((weightedUpper d2Transfer134C0 d2Log101Lo d2Log101Hi:ℚ):ℝ)) ≤ ((d2Transfer134Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer134Arithmetic
  linarith
#print axioms d2Transfer134Arithmetic
#print axioms d2Transfer134Bound
def d2Transfer135Lo : ℚ := (d2LitsNearTransfers016.q2 (41607233) 1 (-28))
def d2Transfer135Hi : ℚ := (d2LitsNearTransfers016.q2 (21642477) 1 (-27))
def d2Transfer135Cap : ℚ := (d2LitsNearTransfers016.q2 (2436024149) 1 (-40))
def d2Transfer135C0 : ℚ := (d2LitsNearTransfers016.q2 (1) 275 (-4))
def d2Transfer135S0 : ℚ := (d2LitsNearTransfers016.q2 (-1) 1 (0))
def d2Transfer135C1 : ℚ := (d2LitsNearTransfers016.q2 (-1) 55 (-3))
def d2Transfer135S1 : ℚ := (d2LitsNearTransfers016.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer135Arithmetic : weightedUpper d2Transfer135C0 d2Log101Lo d2Log101Hi + weightedUpper d2Transfer135C1 d2Log73Lo d2Log73Hi ≤ d2Transfer135Cap := by decide +kernel
theorem d2Transfer135Bound : ∀ x ∈ Set.Icc ((d2Transfer135Lo:ℚ):ℝ) ((d2Transfer135Hi:ℚ):ℝ), ((d2Transfer135C0:ℚ):ℝ)*Real.log |x-((d2Transfer135S0:ℚ):ℝ)| + ((d2Transfer135C1:ℚ):ℝ)*Real.log |x-((d2Transfer135S1:ℚ):ℝ)| ≤ ((d2Transfer135Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer135S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer135S0,d2Transfer135Lo,d2Transfer135Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer135C0 then |x-((d2Transfer135S0:ℚ):ℝ)| ≤ ((d2Log101Q:ℚ):ℝ) else ((d2Log101Q:ℚ):ℝ) ≤ |x-((d2Transfer135S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer135S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer135S0,d2Transfer135Lo,d2Transfer135Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer135C0,d2Log101Q,d2Transfer135S0,d2Transfer135Lo,d2Transfer135Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer135C0 d2Transfer135S0 d2Log101Q d2Log101Lo d2Log101Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log101Bounds
  have hn1 : x-((d2Transfer135S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer135S1,d2Transfer135Lo,d2Transfer135Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer135C1 then |x-((d2Transfer135S1:ℚ):ℝ)| ≤ ((d2Log73Q:ℚ):ℝ) else ((d2Log73Q:ℚ):ℝ) ≤ |x-((d2Transfer135S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer135S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer135S1,d2Transfer135Lo,d2Transfer135Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers016.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer135C1,d2Log73Q,d2Transfer135S1,d2Transfer135Lo,d2Transfer135Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer135C1 d2Transfer135S1 d2Log73Q d2Log73Lo d2Log73Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log73Bounds
  have har : (((weightedUpper d2Transfer135C0 d2Log101Lo d2Log101Hi:ℚ):ℝ) + ((weightedUpper d2Transfer135C1 d2Log73Lo d2Log73Hi:ℚ):ℝ)) ≤ ((d2Transfer135Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer135Arithmetic
  linarith
#print axioms d2Transfer135Arithmetic
#print axioms d2Transfer135Bound
end CatalanMeasure.GenD.Signed.Data.Cells

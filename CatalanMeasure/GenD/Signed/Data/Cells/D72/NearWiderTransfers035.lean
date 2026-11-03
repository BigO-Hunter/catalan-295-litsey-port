module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
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
namespace d2LitsNearWiderTransfers035
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers035
open D72.LogTransfer
def d2WiderTransfer280Lo : ℚ := (d2LitsNearWiderTransfers035.q2 (10045339) 1 (-24))
def d2WiderTransfer280Hi : ℚ := (d2LitsNearWiderTransfers035.q2 (162403145) 1 (-28))
def d2WiderTransfer280Cap : ℚ := (d2LitsNearWiderTransfers035.q2 (1169469059) 1 (-40))
def d2WiderTransfer280C0 : ℚ := (d2LitsNearWiderTransfers035.q2 (-1) 55 (-3))
def d2WiderTransfer280S0 : ℚ := (d2LitsNearWiderTransfers035.q2 (-1) 1 (0))
def d2WiderTransfer280C1 : ℚ := (d2LitsNearWiderTransfers035.q2 (-1) 55 (-3))
def d2WiderTransfer280S1 : ℚ := (d2LitsNearWiderTransfers035.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer280Arithmetic : weightedUpper d2WiderTransfer280C0 d2Log124Lo d2Log124Hi + weightedUpper d2WiderTransfer280C1 d2Log49Lo d2Log49Hi ≤ d2WiderTransfer280Cap := by decide +kernel
theorem d2WiderTransfer280Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer280Lo:ℚ):ℝ) ((d2WiderTransfer280Hi:ℚ):ℝ), ((d2WiderTransfer280C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer280S0:ℚ):ℝ)| + ((d2WiderTransfer280C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer280S1:ℚ):ℝ)| ≤ ((d2WiderTransfer280Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer280S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer280S0,d2WiderTransfer280Lo,d2WiderTransfer280Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer280C0 then |x-((d2WiderTransfer280S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer280S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer280S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer280S0,d2WiderTransfer280Lo,d2WiderTransfer280Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer280C0,d2Log124Q,d2WiderTransfer280S0,d2WiderTransfer280Lo,d2WiderTransfer280Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer280C0 d2WiderTransfer280S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have hn1 : x-((d2WiderTransfer280S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer280S1,d2WiderTransfer280Lo,d2WiderTransfer280Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer280C1 then |x-((d2WiderTransfer280S1:ℚ):ℝ)| ≤ ((d2Log49Q:ℚ):ℝ) else ((d2Log49Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer280S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer280S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer280S1,d2WiderTransfer280Lo,d2WiderTransfer280Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer280C1,d2Log49Q,d2WiderTransfer280S1,d2WiderTransfer280Lo,d2WiderTransfer280Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer280C1 d2WiderTransfer280S1 d2Log49Q d2Log49Lo d2Log49Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log49Bounds
  have har : (((weightedUpper d2WiderTransfer280C0 d2Log124Lo d2Log124Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer280C1 d2Log49Lo d2Log49Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer280Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer280Arithmetic
  linarith
#print axioms d2WiderTransfer280Arithmetic
#print axioms d2WiderTransfer280Bound
def d2WiderTransfer281Lo : ℚ := (d2LitsNearWiderTransfers035.q2 (10045339) 1 (-24))
def d2WiderTransfer281Hi : ℚ := (d2LitsNearWiderTransfers035.q2 (162403145) 1 (-28))
def d2WiderTransfer281Cap : ℚ := (d2LitsNearWiderTransfers035.q2 (15113656175) 1 (-40))
def d2WiderTransfer281C0 : ℚ := (d2LitsNearWiderTransfers035.q2 (23) 25 (-5))
def d2WiderTransfer281S0 : ℚ := (d2LitsNearWiderTransfers035.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer281Arithmetic : weightedUpper d2WiderTransfer281C0 d2Log125Lo d2Log125Hi ≤ d2WiderTransfer281Cap := by decide +kernel
theorem d2WiderTransfer281Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer281Lo:ℚ):ℝ) ((d2WiderTransfer281Hi:ℚ):ℝ), ((d2WiderTransfer281C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer281S0:ℚ):ℝ)| ≤ ((d2WiderTransfer281Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer281S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer281S0,d2WiderTransfer281Lo,d2WiderTransfer281Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer281C0 then |x-((d2WiderTransfer281S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer281S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer281S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer281S0,d2WiderTransfer281Lo,d2WiderTransfer281Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer281C0,d2Log125Q,d2WiderTransfer281S0,d2WiderTransfer281Lo,d2WiderTransfer281Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer281C0 d2WiderTransfer281S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have har : (((weightedUpper d2WiderTransfer281C0 d2Log125Lo d2Log125Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer281Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer281Arithmetic
  linarith
#print axioms d2WiderTransfer281Arithmetic
#print axioms d2WiderTransfer281Bound
def d2WiderTransfer282Lo : ℚ := (d2LitsNearWiderTransfers035.q2 (10045339) 1 (-24))
def d2WiderTransfer282Hi : ℚ := (d2LitsNearWiderTransfers035.q2 (162403145) 1 (-28))
def d2WiderTransfer282Cap : ℚ := (d2LitsNearWiderTransfers035.q2 (30439539927) 1 (-40))
def d2WiderTransfer282C0 : ℚ := (d2LitsNearWiderTransfers035.q2 (3) 275 (-5))
def d2WiderTransfer282S0 : ℚ := (d2LitsNearWiderTransfers035.q2 (-1) 1 (0))
def d2WiderTransfer282C1 : ℚ := (d2LitsNearWiderTransfers035.q2 (-5) 11 (-4))
def d2WiderTransfer282S1 : ℚ := (d2LitsNearWiderTransfers035.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer282Arithmetic : weightedUpper d2WiderTransfer282C0 d2Log125Lo d2Log125Hi + weightedUpper d2WiderTransfer282C1 d2Log49Lo d2Log49Hi ≤ d2WiderTransfer282Cap := by decide +kernel
theorem d2WiderTransfer282Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer282Lo:ℚ):ℝ) ((d2WiderTransfer282Hi:ℚ):ℝ), ((d2WiderTransfer282C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer282S0:ℚ):ℝ)| + ((d2WiderTransfer282C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer282S1:ℚ):ℝ)| ≤ ((d2WiderTransfer282Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer282S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer282S0,d2WiderTransfer282Lo,d2WiderTransfer282Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer282C0 then |x-((d2WiderTransfer282S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer282S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer282S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer282S0,d2WiderTransfer282Lo,d2WiderTransfer282Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer282C0,d2Log125Q,d2WiderTransfer282S0,d2WiderTransfer282Lo,d2WiderTransfer282Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer282C0 d2WiderTransfer282S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have hn1 : x-((d2WiderTransfer282S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer282S1,d2WiderTransfer282Lo,d2WiderTransfer282Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer282C1 then |x-((d2WiderTransfer282S1:ℚ):ℝ)| ≤ ((d2Log49Q:ℚ):ℝ) else ((d2Log49Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer282S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer282S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer282S1,d2WiderTransfer282Lo,d2WiderTransfer282Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer282C1,d2Log49Q,d2WiderTransfer282S1,d2WiderTransfer282Lo,d2WiderTransfer282Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer282C1 d2WiderTransfer282S1 d2Log49Q d2Log49Lo d2Log49Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log49Bounds
  have har : (((weightedUpper d2WiderTransfer282C0 d2Log125Lo d2Log125Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer282C1 d2Log49Lo d2Log49Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer282Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer282Arithmetic
  linarith
#print axioms d2WiderTransfer282Arithmetic
#print axioms d2WiderTransfer282Bound
def d2WiderTransfer283Lo : ℚ := (d2LitsNearWiderTransfers035.q2 (162403145) 1 (-28))
def d2WiderTransfer283Hi : ℚ := (d2LitsNearWiderTransfers035.q2 (82040433) 1 (-27))
def d2WiderTransfer283Cap : ℚ := (d2LitsNearWiderTransfers035.q2 (324000933795269575833) 1 (-78))
def d2WiderTransfer283C0 : ℚ := (d2LitsNearWiderTransfers035.q2 (-1) 55 (-3))
def d2WiderTransfer283S0 : ℚ := (d2LitsNearWiderTransfers035.q2 (-1) 1 (0))
def d2WiderTransfer283C1 : ℚ := (d2LitsNearWiderTransfers035.q2 (-1) 55 (-3))
def d2WiderTransfer283S1 : ℚ := (d2LitsNearWiderTransfers035.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer283Arithmetic : weightedUpper d2WiderTransfer283C0 d2Log125Lo d2Log125Hi + weightedUpper d2WiderTransfer283C1 d2Log46Lo d2Log46Hi ≤ d2WiderTransfer283Cap := by decide +kernel
theorem d2WiderTransfer283Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer283Lo:ℚ):ℝ) ((d2WiderTransfer283Hi:ℚ):ℝ), ((d2WiderTransfer283C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer283S0:ℚ):ℝ)| + ((d2WiderTransfer283C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer283S1:ℚ):ℝ)| ≤ ((d2WiderTransfer283Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer283S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer283S0,d2WiderTransfer283Lo,d2WiderTransfer283Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer283C0 then |x-((d2WiderTransfer283S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer283S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer283S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer283S0,d2WiderTransfer283Lo,d2WiderTransfer283Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer283C0,d2Log125Q,d2WiderTransfer283S0,d2WiderTransfer283Lo,d2WiderTransfer283Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer283C0 d2WiderTransfer283S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have hn1 : x-((d2WiderTransfer283S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer283S1,d2WiderTransfer283Lo,d2WiderTransfer283Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer283C1 then |x-((d2WiderTransfer283S1:ℚ):ℝ)| ≤ ((d2Log46Q:ℚ):ℝ) else ((d2Log46Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer283S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer283S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer283S1,d2WiderTransfer283Lo,d2WiderTransfer283Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer283C1,d2Log46Q,d2WiderTransfer283S1,d2WiderTransfer283Lo,d2WiderTransfer283Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer283C1 d2WiderTransfer283S1 d2Log46Q d2Log46Lo d2Log46Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log46Bounds
  have har : (((weightedUpper d2WiderTransfer283C0 d2Log125Lo d2Log125Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer283C1 d2Log46Lo d2Log46Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer283Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer283Arithmetic
  linarith
#print axioms d2WiderTransfer283Arithmetic
#print axioms d2WiderTransfer283Bound
def d2WiderTransfer284Lo : ℚ := (d2LitsNearWiderTransfers035.q2 (162403145) 1 (-28))
def d2WiderTransfer284Hi : ℚ := (d2LitsNearWiderTransfers035.q2 (82040433) 1 (-27))
def d2WiderTransfer284Cap : ℚ := (d2LitsNearWiderTransfers035.q2 (4156949902276841309337) 1 (-78))
def d2WiderTransfer284C0 : ℚ := (d2LitsNearWiderTransfers035.q2 (23) 25 (-5))
def d2WiderTransfer284S0 : ℚ := (d2LitsNearWiderTransfers035.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer284Arithmetic : weightedUpper d2WiderTransfer284C0 d2Log128Lo d2Log128Hi ≤ d2WiderTransfer284Cap := by decide +kernel
theorem d2WiderTransfer284Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer284Lo:ℚ):ℝ) ((d2WiderTransfer284Hi:ℚ):ℝ), ((d2WiderTransfer284C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer284S0:ℚ):ℝ)| ≤ ((d2WiderTransfer284Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer284S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer284S0,d2WiderTransfer284Lo,d2WiderTransfer284Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer284C0 then |x-((d2WiderTransfer284S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer284S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer284S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer284S0,d2WiderTransfer284Lo,d2WiderTransfer284Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer284C0,d2Log128Q,d2WiderTransfer284S0,d2WiderTransfer284Lo,d2WiderTransfer284Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer284C0 d2WiderTransfer284S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have har : (((weightedUpper d2WiderTransfer284C0 d2Log128Lo d2Log128Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer284Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer284Arithmetic
  linarith
#print axioms d2WiderTransfer284Arithmetic
#print axioms d2WiderTransfer284Bound
def d2WiderTransfer285Lo : ℚ := (d2LitsNearWiderTransfers035.q2 (162403145) 1 (-28))
def d2WiderTransfer285Hi : ℚ := (d2LitsNearWiderTransfers035.q2 (82040433) 1 (-27))
def d2WiderTransfer285Cap : ℚ := (d2LitsNearWiderTransfers035.q2 (8369696750093658883225) 1 (-78))
def d2WiderTransfer285C0 : ℚ := (d2LitsNearWiderTransfers035.q2 (3) 275 (-5))
def d2WiderTransfer285S0 : ℚ := (d2LitsNearWiderTransfers035.q2 (-1) 1 (0))
def d2WiderTransfer285C1 : ℚ := (d2LitsNearWiderTransfers035.q2 (-5) 11 (-4))
def d2WiderTransfer285S1 : ℚ := (d2LitsNearWiderTransfers035.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer285Arithmetic : weightedUpper d2WiderTransfer285C0 d2Log128Lo d2Log128Hi + weightedUpper d2WiderTransfer285C1 d2Log46Lo d2Log46Hi ≤ d2WiderTransfer285Cap := by decide +kernel
theorem d2WiderTransfer285Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer285Lo:ℚ):ℝ) ((d2WiderTransfer285Hi:ℚ):ℝ), ((d2WiderTransfer285C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer285S0:ℚ):ℝ)| + ((d2WiderTransfer285C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer285S1:ℚ):ℝ)| ≤ ((d2WiderTransfer285Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer285S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer285S0,d2WiderTransfer285Lo,d2WiderTransfer285Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer285C0 then |x-((d2WiderTransfer285S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer285S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer285S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer285S0,d2WiderTransfer285Lo,d2WiderTransfer285Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer285C0,d2Log128Q,d2WiderTransfer285S0,d2WiderTransfer285Lo,d2WiderTransfer285Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer285C0 d2WiderTransfer285S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have hn1 : x-((d2WiderTransfer285S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer285S1,d2WiderTransfer285Lo,d2WiderTransfer285Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer285C1 then |x-((d2WiderTransfer285S1:ℚ):ℝ)| ≤ ((d2Log46Q:ℚ):ℝ) else ((d2Log46Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer285S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer285S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer285S1,d2WiderTransfer285Lo,d2WiderTransfer285Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer285C1,d2Log46Q,d2WiderTransfer285S1,d2WiderTransfer285Lo,d2WiderTransfer285Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer285C1 d2WiderTransfer285S1 d2Log46Q d2Log46Lo d2Log46Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log46Bounds
  have har : (((weightedUpper d2WiderTransfer285C0 d2Log128Lo d2Log128Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer285C1 d2Log46Lo d2Log46Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer285Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer285Arithmetic
  linarith
#print axioms d2WiderTransfer285Arithmetic
#print axioms d2WiderTransfer285Bound
def d2WiderTransfer286Lo : ℚ := (d2LitsNearWiderTransfers035.q2 (82040433) 1 (-27))
def d2WiderTransfer286Hi : ℚ := (d2LitsNearWiderTransfers035.q2 (329839453) 1 (-29))
def d2WiderTransfer286Cap : ℚ := (d2LitsNearWiderTransfers035.q2 (328696967227444328115) 1 (-78))
def d2WiderTransfer286C0 : ℚ := (d2LitsNearWiderTransfers035.q2 (-1) 55 (-3))
def d2WiderTransfer286S0 : ℚ := (d2LitsNearWiderTransfers035.q2 (-1) 1 (0))
def d2WiderTransfer286C1 : ℚ := (d2LitsNearWiderTransfers035.q2 (-1) 55 (-3))
def d2WiderTransfer286S1 : ℚ := (d2LitsNearWiderTransfers035.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer286Arithmetic : weightedUpper d2WiderTransfer286C0 d2Log128Lo d2Log128Hi + weightedUpper d2WiderTransfer286C1 d2Log45Lo d2Log45Hi ≤ d2WiderTransfer286Cap := by decide +kernel
theorem d2WiderTransfer286Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer286Lo:ℚ):ℝ) ((d2WiderTransfer286Hi:ℚ):ℝ), ((d2WiderTransfer286C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer286S0:ℚ):ℝ)| + ((d2WiderTransfer286C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer286S1:ℚ):ℝ)| ≤ ((d2WiderTransfer286Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer286S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer286S0,d2WiderTransfer286Lo,d2WiderTransfer286Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer286C0 then |x-((d2WiderTransfer286S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer286S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer286S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer286S0,d2WiderTransfer286Lo,d2WiderTransfer286Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer286C0,d2Log128Q,d2WiderTransfer286S0,d2WiderTransfer286Lo,d2WiderTransfer286Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer286C0 d2WiderTransfer286S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have hn1 : x-((d2WiderTransfer286S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer286S1,d2WiderTransfer286Lo,d2WiderTransfer286Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer286C1 then |x-((d2WiderTransfer286S1:ℚ):ℝ)| ≤ ((d2Log45Q:ℚ):ℝ) else ((d2Log45Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer286S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer286S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer286S1,d2WiderTransfer286Lo,d2WiderTransfer286Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer286C1,d2Log45Q,d2WiderTransfer286S1,d2WiderTransfer286Lo,d2WiderTransfer286Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer286C1 d2WiderTransfer286S1 d2Log45Q d2Log45Lo d2Log45Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log45Bounds
  have har : (((weightedUpper d2WiderTransfer286C0 d2Log128Lo d2Log128Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer286C1 d2Log45Lo d2Log45Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer286Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer286Arithmetic
  linarith
#print axioms d2WiderTransfer286Arithmetic
#print axioms d2WiderTransfer286Bound
def d2WiderTransfer287Lo : ℚ := (d2LitsNearWiderTransfers035.q2 (82040433) 1 (-27))
def d2WiderTransfer287Hi : ℚ := (d2LitsNearWiderTransfers035.q2 (329839453) 1 (-29))
def d2WiderTransfer287Cap : ℚ := (d2LitsNearWiderTransfers035.q2 (4161645935709016061619) 1 (-78))
def d2WiderTransfer287C0 : ℚ := (d2LitsNearWiderTransfers035.q2 (23) 25 (-5))
def d2WiderTransfer287S0 : ℚ := (d2LitsNearWiderTransfers035.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer287Arithmetic : weightedUpper d2WiderTransfer287C0 d2Log129Lo d2Log129Hi ≤ d2WiderTransfer287Cap := by decide +kernel
theorem d2WiderTransfer287Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer287Lo:ℚ):ℝ) ((d2WiderTransfer287Hi:ℚ):ℝ), ((d2WiderTransfer287C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer287S0:ℚ):ℝ)| ≤ ((d2WiderTransfer287Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer287S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer287S0,d2WiderTransfer287Lo,d2WiderTransfer287Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer287C0 then |x-((d2WiderTransfer287S0:ℚ):ℝ)| ≤ ((d2Log129Q:ℚ):ℝ) else ((d2Log129Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer287S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer287S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer287S0,d2WiderTransfer287Lo,d2WiderTransfer287Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer287C0,d2Log129Q,d2WiderTransfer287S0,d2WiderTransfer287Lo,d2WiderTransfer287Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer287C0 d2WiderTransfer287S0 d2Log129Q d2Log129Lo d2Log129Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log129Bounds
  have har : (((weightedUpper d2WiderTransfer287C0 d2Log129Lo d2Log129Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer287Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer287Arithmetic
  linarith
#print axioms d2WiderTransfer287Arithmetic
#print axioms d2WiderTransfer287Bound
end CatalanMeasure.GenD.Signed.Data.Cells

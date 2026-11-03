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
namespace d2LitsNearTransfers035
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers035
open D72.LogTransfer
def d2Transfer280Lo : ℚ := (d2LitsNearTransfers035.q2 (1337812743) 1 (-31))
def d2Transfer280Hi : ℚ := (d2LitsNearTransfers035.q2 (41859077) 1 (-26))
def d2Transfer280Cap : ℚ := (d2LitsNearTransfers035.q2 (1179477945051769181583) 1 (-76))
def d2Transfer280C0 : ℚ := (d2LitsNearTransfers035.q2 (1) 1 (-5))
def d2Transfer280S0 : ℚ := (d2LitsNearTransfers035.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer280Arithmetic : weightedUpper d2Transfer280C0 d2Log139Lo d2Log139Hi ≤ d2Transfer280Cap := by decide +kernel
theorem d2Transfer280Bound : ∀ x ∈ Set.Icc ((d2Transfer280Lo:ℚ):ℝ) ((d2Transfer280Hi:ℚ):ℝ), ((d2Transfer280C0:ℚ):ℝ)*Real.log |x-((d2Transfer280S0:ℚ):ℝ)| ≤ ((d2Transfer280Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer280S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer280S0,d2Transfer280Lo,d2Transfer280Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer280C0 then |x-((d2Transfer280S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2Transfer280S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer280S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer280S0,d2Transfer280Lo,d2Transfer280Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer280C0,d2Log139Q,d2Transfer280S0,d2Transfer280Lo,d2Transfer280Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer280C0 d2Transfer280S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have har : (((weightedUpper d2Transfer280C0 d2Log139Lo d2Log139Hi:ℚ):ℝ)) ≤ ((d2Transfer280Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer280Arithmetic
  linarith
#print axioms d2Transfer280Arithmetic
#print axioms d2Transfer280Bound
def d2Transfer281Lo : ℚ := (d2LitsNearTransfers035.q2 (1337812743) 1 (-31))
def d2Transfer281Hi : ℚ := (d2LitsNearTransfers035.q2 (41859077) 1 (-26))
def d2Transfer281Cap : ℚ := (d2LitsNearTransfers035.q2 (2202280277694988391823) 1 (-76))
def d2Transfer281C0 : ℚ := (d2LitsNearTransfers035.q2 (1) 11 (-5))
def d2Transfer281S0 : ℚ := (d2LitsNearTransfers035.q2 (-1) 1 (0))
def d2Transfer281C1 : ℚ := (d2LitsNearTransfers035.q2 (-5) 11 (-4))
def d2Transfer281S1 : ℚ := (d2LitsNearTransfers035.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer281Arithmetic : weightedUpper d2Transfer281C0 d2Log139Lo d2Log139Hi + weightedUpper d2Transfer281C1 d2Log35Lo d2Log35Hi ≤ d2Transfer281Cap := by decide +kernel
theorem d2Transfer281Bound : ∀ x ∈ Set.Icc ((d2Transfer281Lo:ℚ):ℝ) ((d2Transfer281Hi:ℚ):ℝ), ((d2Transfer281C0:ℚ):ℝ)*Real.log |x-((d2Transfer281S0:ℚ):ℝ)| + ((d2Transfer281C1:ℚ):ℝ)*Real.log |x-((d2Transfer281S1:ℚ):ℝ)| ≤ ((d2Transfer281Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer281S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer281S0,d2Transfer281Lo,d2Transfer281Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer281C0 then |x-((d2Transfer281S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2Transfer281S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer281S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer281S0,d2Transfer281Lo,d2Transfer281Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer281C0,d2Log139Q,d2Transfer281S0,d2Transfer281Lo,d2Transfer281Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer281C0 d2Transfer281S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have hn1 : x-((d2Transfer281S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer281S1,d2Transfer281Lo,d2Transfer281Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer281C1 then |x-((d2Transfer281S1:ℚ):ℝ)| ≤ ((d2Log35Q:ℚ):ℝ) else ((d2Log35Q:ℚ):ℝ) ≤ |x-((d2Transfer281S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer281S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer281S1,d2Transfer281Lo,d2Transfer281Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer281C1,d2Log35Q,d2Transfer281S1,d2Transfer281Lo,d2Transfer281Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer281C1 d2Transfer281S1 d2Log35Q d2Log35Lo d2Log35Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log35Bounds
  have har : (((weightedUpper d2Transfer281C0 d2Log139Lo d2Log139Hi:ℚ):ℝ) + ((weightedUpper d2Transfer281C1 d2Log35Lo d2Log35Hi:ℚ):ℝ)) ≤ ((d2Transfer281Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer281Arithmetic
  linarith
#print axioms d2Transfer281Arithmetic
#print axioms d2Transfer281Bound
def d2Transfer282Lo : ℚ := (d2LitsNearTransfers035.q2 (41859077) 1 (-26))
def d2Transfer282Hi : ℚ := (d2LitsNearTransfers035.q2 (1341168185) 1 (-31))
def d2Transfer282Cap : ℚ := (d2LitsNearTransfers035.q2 (2471324106762310774949) 1 (-80))
def d2Transfer282C0 : ℚ := (d2LitsNearTransfers035.q2 (1) 25 (-4))
def d2Transfer282S0 : ℚ := (d2LitsNearTransfers035.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer282Arithmetic : weightedUpper d2Transfer282C0 d2Log140Lo d2Log140Hi ≤ d2Transfer282Cap := by decide +kernel
theorem d2Transfer282Bound : ∀ x ∈ Set.Icc ((d2Transfer282Lo:ℚ):ℝ) ((d2Transfer282Hi:ℚ):ℝ), ((d2Transfer282C0:ℚ):ℝ)*Real.log |x-((d2Transfer282S0:ℚ):ℝ)| ≤ ((d2Transfer282Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer282S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer282S0,d2Transfer282Lo,d2Transfer282Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer282C0 then |x-((d2Transfer282S0:ℚ):ℝ)| ≤ ((d2Log140Q:ℚ):ℝ) else ((d2Log140Q:ℚ):ℝ) ≤ |x-((d2Transfer282S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer282S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer282S0,d2Transfer282Lo,d2Transfer282Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer282C0,d2Log140Q,d2Transfer282S0,d2Transfer282Lo,d2Transfer282Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer282C0 d2Transfer282S0 d2Log140Q d2Log140Lo d2Log140Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log140Bounds
  have har : (((weightedUpper d2Transfer282C0 d2Log140Lo d2Log140Hi:ℚ):ℝ)) ≤ ((d2Transfer282Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer282Arithmetic
  linarith
#print axioms d2Transfer282Arithmetic
#print axioms d2Transfer282Bound
def d2Transfer283Lo : ℚ := (d2LitsNearTransfers035.q2 (41859077) 1 (-26))
def d2Transfer283Hi : ℚ := (d2LitsNearTransfers035.q2 (1341168185) 1 (-31))
def d2Transfer283Cap : ℚ := (d2LitsNearTransfers035.q2 (3721624275398046118053) 1 (-80))
def d2Transfer283C0 : ℚ := (d2LitsNearTransfers035.q2 (1) 275 (-4))
def d2Transfer283S0 : ℚ := (d2LitsNearTransfers035.q2 (-1) 1 (0))
def d2Transfer283C1 : ℚ := (d2LitsNearTransfers035.q2 (-1) 55 (-3))
def d2Transfer283S1 : ℚ := (d2LitsNearTransfers035.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer283Arithmetic : weightedUpper d2Transfer283C0 d2Log140Lo d2Log140Hi + weightedUpper d2Transfer283C1 d2Log34Lo d2Log34Hi ≤ d2Transfer283Cap := by decide +kernel
theorem d2Transfer283Bound : ∀ x ∈ Set.Icc ((d2Transfer283Lo:ℚ):ℝ) ((d2Transfer283Hi:ℚ):ℝ), ((d2Transfer283C0:ℚ):ℝ)*Real.log |x-((d2Transfer283S0:ℚ):ℝ)| + ((d2Transfer283C1:ℚ):ℝ)*Real.log |x-((d2Transfer283S1:ℚ):ℝ)| ≤ ((d2Transfer283Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer283S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer283S0,d2Transfer283Lo,d2Transfer283Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer283C0 then |x-((d2Transfer283S0:ℚ):ℝ)| ≤ ((d2Log140Q:ℚ):ℝ) else ((d2Log140Q:ℚ):ℝ) ≤ |x-((d2Transfer283S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer283S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer283S0,d2Transfer283Lo,d2Transfer283Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer283C0,d2Log140Q,d2Transfer283S0,d2Transfer283Lo,d2Transfer283Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer283C0 d2Transfer283S0 d2Log140Q d2Log140Lo d2Log140Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log140Bounds
  have hn1 : x-((d2Transfer283S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer283S1,d2Transfer283Lo,d2Transfer283Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer283C1 then |x-((d2Transfer283S1:ℚ):ℝ)| ≤ ((d2Log34Q:ℚ):ℝ) else ((d2Log34Q:ℚ):ℝ) ≤ |x-((d2Transfer283S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer283S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer283S1,d2Transfer283Lo,d2Transfer283Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer283C1,d2Log34Q,d2Transfer283S1,d2Transfer283Lo,d2Transfer283Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer283C1 d2Transfer283S1 d2Log34Q d2Log34Lo d2Log34Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log34Bounds
  have har : (((weightedUpper d2Transfer283C0 d2Log140Lo d2Log140Hi:ℚ):ℝ) + ((weightedUpper d2Transfer283C1 d2Log34Lo d2Log34Hi:ℚ):ℝ)) ≤ ((d2Transfer283Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer283Arithmetic
  linarith
#print axioms d2Transfer283Arithmetic
#print axioms d2Transfer283Bound
def d2Transfer284Lo : ℚ := (d2LitsNearTransfers035.q2 (41859077) 1 (-26))
def d2Transfer284Hi : ℚ := (d2LitsNearTransfers035.q2 (1341168185) 1 (-31))
def d2Transfer284Cap : ℚ := (d2LitsNearTransfers035.q2 (18944686365821006639269) 1 (-80))
def d2Transfer284C0 : ℚ := (d2LitsNearTransfers035.q2 (1) 1 (-5))
def d2Transfer284S0 : ℚ := (d2LitsNearTransfers035.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer284Arithmetic : weightedUpper d2Transfer284C0 d2Log140Lo d2Log140Hi ≤ d2Transfer284Cap := by decide +kernel
theorem d2Transfer284Bound : ∀ x ∈ Set.Icc ((d2Transfer284Lo:ℚ):ℝ) ((d2Transfer284Hi:ℚ):ℝ), ((d2Transfer284C0:ℚ):ℝ)*Real.log |x-((d2Transfer284S0:ℚ):ℝ)| ≤ ((d2Transfer284Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer284S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer284S0,d2Transfer284Lo,d2Transfer284Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer284C0 then |x-((d2Transfer284S0:ℚ):ℝ)| ≤ ((d2Log140Q:ℚ):ℝ) else ((d2Log140Q:ℚ):ℝ) ≤ |x-((d2Transfer284S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer284S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer284S0,d2Transfer284Lo,d2Transfer284Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer284C0,d2Log140Q,d2Transfer284S0,d2Transfer284Lo,d2Transfer284Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer284C0 d2Transfer284S0 d2Log140Q d2Log140Lo d2Log140Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log140Bounds
  have har : (((weightedUpper d2Transfer284C0 d2Log140Lo d2Log140Hi:ℚ):ℝ)) ≤ ((d2Transfer284Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer284Arithmetic
  linarith
#print axioms d2Transfer284Arithmetic
#print axioms d2Transfer284Bound
def d2Transfer285Lo : ℚ := (d2LitsNearTransfers035.q2 (41859077) 1 (-26))
def d2Transfer285Hi : ℚ := (d2LitsNearTransfers035.q2 (1341168185) 1 (-31))
def d2Transfer285Cap : ℚ := (d2LitsNearTransfers035.q2 (35309523688112514003109) 1 (-80))
def d2Transfer285C0 : ℚ := (d2LitsNearTransfers035.q2 (1) 11 (-5))
def d2Transfer285S0 : ℚ := (d2LitsNearTransfers035.q2 (-1) 1 (0))
def d2Transfer285C1 : ℚ := (d2LitsNearTransfers035.q2 (-5) 11 (-4))
def d2Transfer285S1 : ℚ := (d2LitsNearTransfers035.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer285Arithmetic : weightedUpper d2Transfer285C0 d2Log140Lo d2Log140Hi + weightedUpper d2Transfer285C1 d2Log34Lo d2Log34Hi ≤ d2Transfer285Cap := by decide +kernel
theorem d2Transfer285Bound : ∀ x ∈ Set.Icc ((d2Transfer285Lo:ℚ):ℝ) ((d2Transfer285Hi:ℚ):ℝ), ((d2Transfer285C0:ℚ):ℝ)*Real.log |x-((d2Transfer285S0:ℚ):ℝ)| + ((d2Transfer285C1:ℚ):ℝ)*Real.log |x-((d2Transfer285S1:ℚ):ℝ)| ≤ ((d2Transfer285Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer285S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer285S0,d2Transfer285Lo,d2Transfer285Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer285C0 then |x-((d2Transfer285S0:ℚ):ℝ)| ≤ ((d2Log140Q:ℚ):ℝ) else ((d2Log140Q:ℚ):ℝ) ≤ |x-((d2Transfer285S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer285S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer285S0,d2Transfer285Lo,d2Transfer285Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer285C0,d2Log140Q,d2Transfer285S0,d2Transfer285Lo,d2Transfer285Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer285C0 d2Transfer285S0 d2Log140Q d2Log140Lo d2Log140Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log140Bounds
  have hn1 : x-((d2Transfer285S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer285S1,d2Transfer285Lo,d2Transfer285Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer285C1 then |x-((d2Transfer285S1:ℚ):ℝ)| ≤ ((d2Log34Q:ℚ):ℝ) else ((d2Log34Q:ℚ):ℝ) ≤ |x-((d2Transfer285S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer285S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer285S1,d2Transfer285Lo,d2Transfer285Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer285C1,d2Log34Q,d2Transfer285S1,d2Transfer285Lo,d2Transfer285Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer285C1 d2Transfer285S1 d2Log34Q d2Log34Lo d2Log34Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log34Bounds
  have har : (((weightedUpper d2Transfer285C0 d2Log140Lo d2Log140Hi:ℚ):ℝ) + ((weightedUpper d2Transfer285C1 d2Log34Lo d2Log34Hi:ℚ):ℝ)) ≤ ((d2Transfer285Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer285Arithmetic
  linarith
#print axioms d2Transfer285Arithmetic
#print axioms d2Transfer285Bound
def d2Transfer286Lo : ℚ := (d2LitsNearTransfers035.q2 (1341168185) 1 (-31))
def d2Transfer286Hi : ℚ := (d2LitsNearTransfers035.q2 (671422953) 1 (-30))
def d2Transfer286Cap : ℚ := (d2LitsNearTransfers035.q2 (318063906175397004093) 1 (-77))
def d2Transfer286C0 : ℚ := (d2LitsNearTransfers035.q2 (1) 25 (-4))
def d2Transfer286S0 : ℚ := (d2LitsNearTransfers035.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer286Arithmetic : weightedUpper d2Transfer286C0 d2Log141Lo d2Log141Hi ≤ d2Transfer286Cap := by decide +kernel
theorem d2Transfer286Bound : ∀ x ∈ Set.Icc ((d2Transfer286Lo:ℚ):ℝ) ((d2Transfer286Hi:ℚ):ℝ), ((d2Transfer286C0:ℚ):ℝ)*Real.log |x-((d2Transfer286S0:ℚ):ℝ)| ≤ ((d2Transfer286Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer286S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer286S0,d2Transfer286Lo,d2Transfer286Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer286C0 then |x-((d2Transfer286S0:ℚ):ℝ)| ≤ ((d2Log141Q:ℚ):ℝ) else ((d2Log141Q:ℚ):ℝ) ≤ |x-((d2Transfer286S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer286S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer286S0,d2Transfer286Lo,d2Transfer286Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer286C0,d2Log141Q,d2Transfer286S0,d2Transfer286Lo,d2Transfer286Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer286C0 d2Transfer286S0 d2Log141Q d2Log141Lo d2Log141Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log141Bounds
  have har : (((weightedUpper d2Transfer286C0 d2Log141Lo d2Log141Hi:ℚ):ℝ)) ≤ ((d2Transfer286Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer286Arithmetic
  linarith
#print axioms d2Transfer286Arithmetic
#print axioms d2Transfer286Bound
def d2Transfer287Lo : ℚ := (d2LitsNearTransfers035.q2 (1341168185) 1 (-31))
def d2Transfer287Hi : ℚ := (d2LitsNearTransfers035.q2 (671422953) 1 (-30))
def d2Transfer287Cap : ℚ := (d2LitsNearTransfers035.q2 (474351427254863921981) 1 (-77))
def d2Transfer287C0 : ℚ := (d2LitsNearTransfers035.q2 (1) 275 (-4))
def d2Transfer287S0 : ℚ := (d2LitsNearTransfers035.q2 (-1) 1 (0))
def d2Transfer287C1 : ℚ := (d2LitsNearTransfers035.q2 (-1) 55 (-3))
def d2Transfer287S1 : ℚ := (d2LitsNearTransfers035.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer287Arithmetic : weightedUpper d2Transfer287C0 d2Log141Lo d2Log141Hi + weightedUpper d2Transfer287C1 d2Log33Lo d2Log33Hi ≤ d2Transfer287Cap := by decide +kernel
theorem d2Transfer287Bound : ∀ x ∈ Set.Icc ((d2Transfer287Lo:ℚ):ℝ) ((d2Transfer287Hi:ℚ):ℝ), ((d2Transfer287C0:ℚ):ℝ)*Real.log |x-((d2Transfer287S0:ℚ):ℝ)| + ((d2Transfer287C1:ℚ):ℝ)*Real.log |x-((d2Transfer287S1:ℚ):ℝ)| ≤ ((d2Transfer287Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer287S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer287S0,d2Transfer287Lo,d2Transfer287Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer287C0 then |x-((d2Transfer287S0:ℚ):ℝ)| ≤ ((d2Log141Q:ℚ):ℝ) else ((d2Log141Q:ℚ):ℝ) ≤ |x-((d2Transfer287S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer287S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer287S0,d2Transfer287Lo,d2Transfer287Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer287C0,d2Log141Q,d2Transfer287S0,d2Transfer287Lo,d2Transfer287Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer287C0 d2Transfer287S0 d2Log141Q d2Log141Lo d2Log141Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log141Bounds
  have hn1 : x-((d2Transfer287S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer287S1,d2Transfer287Lo,d2Transfer287Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer287C1 then |x-((d2Transfer287S1:ℚ):ℝ)| ≤ ((d2Log33Q:ℚ):ℝ) else ((d2Log33Q:ℚ):ℝ) ≤ |x-((d2Transfer287S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer287S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer287S1,d2Transfer287Lo,d2Transfer287Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers035.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer287C1,d2Log33Q,d2Transfer287S1,d2Transfer287Lo,d2Transfer287Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer287C1 d2Transfer287S1 d2Log33Q d2Log33Lo d2Log33Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log33Bounds
  have har : (((weightedUpper d2Transfer287C0 d2Log141Lo d2Log141Hi:ℚ):ℝ) + ((weightedUpper d2Transfer287C1 d2Log33Lo d2Log33Hi:ℚ):ℝ)) ≤ ((d2Transfer287Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer287Arithmetic
  linarith
#print axioms d2Transfer287Arithmetic
#print axioms d2Transfer287Bound
end CatalanMeasure.GenD.Signed.Data.Cells

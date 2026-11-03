module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers024
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers024
open D72.LogTransfer
def d2WiderTransfer192Lo : ℚ := (d2LitsNearWiderTransfers024.q2 (339905779) 1 (-29))
def d2WiderTransfer192Hi : ℚ := (d2LitsNearWiderTransfers024.q2 (85395875) 1 (-27))
def d2WiderTransfer192Cap : ℚ := (d2LitsNearWiderTransfers024.q2 (20058378016890016489705) 1 (-80))
def d2WiderTransfer192C0 : ℚ := (d2LitsNearWiderTransfers024.q2 (1) 1 (-5))
def d2WiderTransfer192S0 : ℚ := (d2LitsNearWiderTransfers024.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer192Arithmetic : weightedUpper d2WiderTransfer192C0 d2Log155Lo d2Log155Hi ≤ d2WiderTransfer192Cap := by decide +kernel
theorem d2WiderTransfer192Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer192Lo:ℚ):ℝ) ((d2WiderTransfer192Hi:ℚ):ℝ), ((d2WiderTransfer192C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer192S0:ℚ):ℝ)| ≤ ((d2WiderTransfer192Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer192S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer192S0,d2WiderTransfer192Lo,d2WiderTransfer192Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer192C0 then |x-((d2WiderTransfer192S0:ℚ):ℝ)| ≤ ((d2Log155Q:ℚ):ℝ) else ((d2Log155Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer192S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer192S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer192S0,d2WiderTransfer192Lo,d2WiderTransfer192Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer192C0,d2Log155Q,d2WiderTransfer192S0,d2WiderTransfer192Lo,d2WiderTransfer192Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer192C0 d2WiderTransfer192S0 d2Log155Q d2Log155Lo d2Log155Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log155Bounds
  have har : (((weightedUpper d2WiderTransfer192C0 d2Log155Lo d2Log155Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer192Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer192Arithmetic
  linarith
#print axioms d2WiderTransfer192Arithmetic
#print axioms d2WiderTransfer192Bound
def d2WiderTransfer193Lo : ℚ := (d2LitsNearWiderTransfers024.q2 (339905779) 1 (-29))
def d2WiderTransfer193Hi : ℚ := (d2LitsNearWiderTransfers024.q2 (85395875) 1 (-27))
def d2WiderTransfer193Cap : ℚ := (d2LitsNearWiderTransfers024.q2 (36423215339181523853545) 1 (-80))
def d2WiderTransfer193C0 : ℚ := (d2LitsNearWiderTransfers024.q2 (1) 11 (-5))
def d2WiderTransfer193S0 : ℚ := (d2LitsNearWiderTransfers024.q2 (-1) 1 (0))
def d2WiderTransfer193C1 : ℚ := (d2LitsNearWiderTransfers024.q2 (-5) 11 (-4))
def d2WiderTransfer193S1 : ℚ := (d2LitsNearWiderTransfers024.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer193Arithmetic : weightedUpper d2WiderTransfer193C0 d2Log155Lo d2Log155Hi + weightedUpper d2WiderTransfer193C1 d2Log19Lo d2Log19Hi ≤ d2WiderTransfer193Cap := by decide +kernel
theorem d2WiderTransfer193Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer193Lo:ℚ):ℝ) ((d2WiderTransfer193Hi:ℚ):ℝ), ((d2WiderTransfer193C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer193S0:ℚ):ℝ)| + ((d2WiderTransfer193C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer193S1:ℚ):ℝ)| ≤ ((d2WiderTransfer193Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer193S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer193S0,d2WiderTransfer193Lo,d2WiderTransfer193Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer193C0 then |x-((d2WiderTransfer193S0:ℚ):ℝ)| ≤ ((d2Log155Q:ℚ):ℝ) else ((d2Log155Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer193S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer193S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer193S0,d2WiderTransfer193Lo,d2WiderTransfer193Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer193C0,d2Log155Q,d2WiderTransfer193S0,d2WiderTransfer193Lo,d2WiderTransfer193Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer193C0 d2WiderTransfer193S0 d2Log155Q d2Log155Lo d2Log155Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log155Bounds
  have hn1 : x-((d2WiderTransfer193S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer193S1,d2WiderTransfer193Lo,d2WiderTransfer193Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer193C1 then |x-((d2WiderTransfer193S1:ℚ):ℝ)| ≤ ((d2Log19Q:ℚ):ℝ) else ((d2Log19Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer193S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer193S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer193S1,d2WiderTransfer193Lo,d2WiderTransfer193Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer193C1,d2Log19Q,d2WiderTransfer193S1,d2WiderTransfer193Lo,d2WiderTransfer193Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer193C1 d2WiderTransfer193S1 d2Log19Q d2Log19Lo d2Log19Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log19Bounds
  have har : (((weightedUpper d2WiderTransfer193C0 d2Log155Lo d2Log155Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer193C1 d2Log19Lo d2Log19Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer193Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer193Arithmetic
  linarith
#print axioms d2WiderTransfer193Arithmetic
#print axioms d2WiderTransfer193Bound
def d2WiderTransfer194Lo : ℚ := (d2LitsNearWiderTransfers024.q2 (85395875) 1 (-27))
def d2WiderTransfer194Hi : ℚ := (d2LitsNearWiderTransfers024.q2 (343261221) 1 (-29))
def d2WiderTransfer194Cap : ℚ := (d2LitsNearWiderTransfers024.q2 (3887898182126945858551) 1 (-80))
def d2WiderTransfer194C0 : ℚ := (d2LitsNearWiderTransfers024.q2 (1) 25 (-4))
def d2WiderTransfer194S0 : ℚ := (d2LitsNearWiderTransfers024.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer194Arithmetic : weightedUpper d2WiderTransfer194C0 d2Log158Lo d2Log158Hi ≤ d2WiderTransfer194Cap := by decide +kernel
theorem d2WiderTransfer194Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer194Lo:ℚ):ℝ) ((d2WiderTransfer194Hi:ℚ):ℝ), ((d2WiderTransfer194C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer194S0:ℚ):ℝ)| ≤ ((d2WiderTransfer194Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer194S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer194S0,d2WiderTransfer194Lo,d2WiderTransfer194Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer194C0 then |x-((d2WiderTransfer194S0:ℚ):ℝ)| ≤ ((d2Log158Q:ℚ):ℝ) else ((d2Log158Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer194S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer194S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer194S0,d2WiderTransfer194Lo,d2WiderTransfer194Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer194C0,d2Log158Q,d2WiderTransfer194S0,d2WiderTransfer194Lo,d2WiderTransfer194Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer194C0 d2WiderTransfer194S0 d2Log158Q d2Log158Lo d2Log158Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log158Bounds
  have har : (((weightedUpper d2WiderTransfer194C0 d2Log158Lo d2Log158Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer194Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer194Arithmetic
  linarith
#print axioms d2WiderTransfer194Arithmetic
#print axioms d2WiderTransfer194Bound
def d2WiderTransfer195Lo : ℚ := (d2LitsNearWiderTransfers024.q2 (85395875) 1 (-27))
def d2WiderTransfer195Hi : ℚ := (d2LitsNearWiderTransfers024.q2 (343261221) 1 (-29))
def d2WiderTransfer195Cap : ℚ := (d2LitsNearWiderTransfers024.q2 (5138198350762681201655) 1 (-80))
def d2WiderTransfer195C0 : ℚ := (d2LitsNearWiderTransfers024.q2 (1) 275 (-4))
def d2WiderTransfer195S0 : ℚ := (d2LitsNearWiderTransfers024.q2 (-1) 1 (0))
def d2WiderTransfer195C1 : ℚ := (d2LitsNearWiderTransfers024.q2 (-1) 55 (-3))
def d2WiderTransfer195S1 : ℚ := (d2LitsNearWiderTransfers024.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer195Arithmetic : weightedUpper d2WiderTransfer195C0 d2Log158Lo d2Log158Hi + weightedUpper d2WiderTransfer195C1 d2Log16Lo d2Log16Hi ≤ d2WiderTransfer195Cap := by decide +kernel
theorem d2WiderTransfer195Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer195Lo:ℚ):ℝ) ((d2WiderTransfer195Hi:ℚ):ℝ), ((d2WiderTransfer195C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer195S0:ℚ):ℝ)| + ((d2WiderTransfer195C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer195S1:ℚ):ℝ)| ≤ ((d2WiderTransfer195Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer195S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer195S0,d2WiderTransfer195Lo,d2WiderTransfer195Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer195C0 then |x-((d2WiderTransfer195S0:ℚ):ℝ)| ≤ ((d2Log158Q:ℚ):ℝ) else ((d2Log158Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer195S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer195S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer195S0,d2WiderTransfer195Lo,d2WiderTransfer195Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer195C0,d2Log158Q,d2WiderTransfer195S0,d2WiderTransfer195Lo,d2WiderTransfer195Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer195C0 d2WiderTransfer195S0 d2Log158Q d2Log158Lo d2Log158Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log158Bounds
  have hn1 : x-((d2WiderTransfer195S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer195S1,d2WiderTransfer195Lo,d2WiderTransfer195Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer195C1 then |x-((d2WiderTransfer195S1:ℚ):ℝ)| ≤ ((d2Log16Q:ℚ):ℝ) else ((d2Log16Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer195S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer195S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer195S1,d2WiderTransfer195Lo,d2WiderTransfer195Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer195C1,d2Log16Q,d2WiderTransfer195S1,d2WiderTransfer195Lo,d2WiderTransfer195Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer195C1 d2WiderTransfer195S1 d2Log16Q d2Log16Lo d2Log16Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log16Bounds
  have har : (((weightedUpper d2WiderTransfer195C0 d2Log158Lo d2Log158Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer195C1 d2Log16Lo d2Log16Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer195Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer195Arithmetic
  linarith
#print axioms d2WiderTransfer195Arithmetic
#print axioms d2WiderTransfer195Bound
def d2WiderTransfer196Lo : ℚ := (d2LitsNearWiderTransfers024.q2 (85395875) 1 (-27))
def d2WiderTransfer196Hi : ℚ := (d2LitsNearWiderTransfers024.q2 (343261221) 1 (-29))
def d2WiderTransfer196Cap : ℚ := (d2LitsNearWiderTransfers024.q2 (20361260441185641722871) 1 (-80))
def d2WiderTransfer196C0 : ℚ := (d2LitsNearWiderTransfers024.q2 (1) 1 (-5))
def d2WiderTransfer196S0 : ℚ := (d2LitsNearWiderTransfers024.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer196Arithmetic : weightedUpper d2WiderTransfer196C0 d2Log158Lo d2Log158Hi ≤ d2WiderTransfer196Cap := by decide +kernel
theorem d2WiderTransfer196Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer196Lo:ℚ):ℝ) ((d2WiderTransfer196Hi:ℚ):ℝ), ((d2WiderTransfer196C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer196S0:ℚ):ℝ)| ≤ ((d2WiderTransfer196Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer196S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer196S0,d2WiderTransfer196Lo,d2WiderTransfer196Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer196C0 then |x-((d2WiderTransfer196S0:ℚ):ℝ)| ≤ ((d2Log158Q:ℚ):ℝ) else ((d2Log158Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer196S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer196S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer196S0,d2WiderTransfer196Lo,d2WiderTransfer196Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer196C0,d2Log158Q,d2WiderTransfer196S0,d2WiderTransfer196Lo,d2WiderTransfer196Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer196C0 d2WiderTransfer196S0 d2Log158Q d2Log158Lo d2Log158Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log158Bounds
  have har : (((weightedUpper d2WiderTransfer196C0 d2Log158Lo d2Log158Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer196Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer196Arithmetic
  linarith
#print axioms d2WiderTransfer196Arithmetic
#print axioms d2WiderTransfer196Bound
def d2WiderTransfer197Lo : ℚ := (d2LitsNearWiderTransfers024.q2 (85395875) 1 (-27))
def d2WiderTransfer197Hi : ℚ := (d2LitsNearWiderTransfers024.q2 (343261221) 1 (-29))
def d2WiderTransfer197Cap : ℚ := (d2LitsNearWiderTransfers024.q2 (36726097763477149086711) 1 (-80))
def d2WiderTransfer197C0 : ℚ := (d2LitsNearWiderTransfers024.q2 (1) 11 (-5))
def d2WiderTransfer197S0 : ℚ := (d2LitsNearWiderTransfers024.q2 (-1) 1 (0))
def d2WiderTransfer197C1 : ℚ := (d2LitsNearWiderTransfers024.q2 (-5) 11 (-4))
def d2WiderTransfer197S1 : ℚ := (d2LitsNearWiderTransfers024.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer197Arithmetic : weightedUpper d2WiderTransfer197C0 d2Log158Lo d2Log158Hi + weightedUpper d2WiderTransfer197C1 d2Log16Lo d2Log16Hi ≤ d2WiderTransfer197Cap := by decide +kernel
theorem d2WiderTransfer197Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer197Lo:ℚ):ℝ) ((d2WiderTransfer197Hi:ℚ):ℝ), ((d2WiderTransfer197C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer197S0:ℚ):ℝ)| + ((d2WiderTransfer197C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer197S1:ℚ):ℝ)| ≤ ((d2WiderTransfer197Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer197S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer197S0,d2WiderTransfer197Lo,d2WiderTransfer197Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer197C0 then |x-((d2WiderTransfer197S0:ℚ):ℝ)| ≤ ((d2Log158Q:ℚ):ℝ) else ((d2Log158Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer197S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer197S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer197S0,d2WiderTransfer197Lo,d2WiderTransfer197Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer197C0,d2Log158Q,d2WiderTransfer197S0,d2WiderTransfer197Lo,d2WiderTransfer197Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer197C0 d2WiderTransfer197S0 d2Log158Q d2Log158Lo d2Log158Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log158Bounds
  have hn1 : x-((d2WiderTransfer197S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer197S1,d2WiderTransfer197Lo,d2WiderTransfer197Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer197C1 then |x-((d2WiderTransfer197S1:ℚ):ℝ)| ≤ ((d2Log16Q:ℚ):ℝ) else ((d2Log16Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer197S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer197S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer197S1,d2WiderTransfer197Lo,d2WiderTransfer197Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer197C1,d2Log16Q,d2WiderTransfer197S1,d2WiderTransfer197Lo,d2WiderTransfer197Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer197C1 d2WiderTransfer197S1 d2Log16Q d2Log16Lo d2Log16Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log16Bounds
  have har : (((weightedUpper d2WiderTransfer197C0 d2Log158Lo d2Log158Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer197C1 d2Log16Lo d2Log16Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer197Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer197Arithmetic
  linarith
#print axioms d2WiderTransfer197Arithmetic
#print axioms d2WiderTransfer197Bound
def d2WiderTransfer198Lo : ℚ := (d2LitsNearWiderTransfers024.q2 (343261221) 1 (-29))
def d2WiderTransfer198Hi : ℚ := (d2LitsNearWiderTransfers024.q2 (172469471) 1 (-28))
def d2WiderTransfer198Cap : ℚ := (d2LitsNearWiderTransfers024.q2 (4193347169859673716761) 1 (-80))
def d2WiderTransfer198C0 : ℚ := (d2LitsNearWiderTransfers024.q2 (1) 25 (-4))
def d2WiderTransfer198S0 : ℚ := (d2LitsNearWiderTransfers024.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer198Arithmetic : weightedUpper d2WiderTransfer198C0 d2Log160Lo d2Log160Hi ≤ d2WiderTransfer198Cap := by decide +kernel
theorem d2WiderTransfer198Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer198Lo:ℚ):ℝ) ((d2WiderTransfer198Hi:ℚ):ℝ), ((d2WiderTransfer198C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer198S0:ℚ):ℝ)| ≤ ((d2WiderTransfer198Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer198S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer198S0,d2WiderTransfer198Lo,d2WiderTransfer198Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer198C0 then |x-((d2WiderTransfer198S0:ℚ):ℝ)| ≤ ((d2Log160Q:ℚ):ℝ) else ((d2Log160Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer198S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer198S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer198S0,d2WiderTransfer198Lo,d2WiderTransfer198Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer198C0,d2Log160Q,d2WiderTransfer198S0,d2WiderTransfer198Lo,d2WiderTransfer198Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer198C0 d2WiderTransfer198S0 d2Log160Q d2Log160Lo d2Log160Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log160Bounds
  have har : (((weightedUpper d2WiderTransfer198C0 d2Log160Lo d2Log160Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer198Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer198Arithmetic
  linarith
#print axioms d2WiderTransfer198Arithmetic
#print axioms d2WiderTransfer198Bound
def d2WiderTransfer199Lo : ℚ := (d2LitsNearWiderTransfers024.q2 (343261221) 1 (-29))
def d2WiderTransfer199Hi : ℚ := (d2LitsNearWiderTransfers024.q2 (172469471) 1 (-28))
def d2WiderTransfer199Cap : ℚ := (d2LitsNearWiderTransfers024.q2 (5443647338495409059865) 1 (-80))
def d2WiderTransfer199C0 : ℚ := (d2LitsNearWiderTransfers024.q2 (1) 275 (-4))
def d2WiderTransfer199S0 : ℚ := (d2LitsNearWiderTransfers024.q2 (-1) 1 (0))
def d2WiderTransfer199C1 : ℚ := (d2LitsNearWiderTransfers024.q2 (-1) 55 (-3))
def d2WiderTransfer199S1 : ℚ := (d2LitsNearWiderTransfers024.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer199Arithmetic : weightedUpper d2WiderTransfer199C0 d2Log160Lo d2Log160Hi + weightedUpper d2WiderTransfer199C1 d2Log14Lo d2Log14Hi ≤ d2WiderTransfer199Cap := by decide +kernel
theorem d2WiderTransfer199Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer199Lo:ℚ):ℝ) ((d2WiderTransfer199Hi:ℚ):ℝ), ((d2WiderTransfer199C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer199S0:ℚ):ℝ)| + ((d2WiderTransfer199C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer199S1:ℚ):ℝ)| ≤ ((d2WiderTransfer199Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer199S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer199S0,d2WiderTransfer199Lo,d2WiderTransfer199Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer199C0 then |x-((d2WiderTransfer199S0:ℚ):ℝ)| ≤ ((d2Log160Q:ℚ):ℝ) else ((d2Log160Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer199S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer199S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer199S0,d2WiderTransfer199Lo,d2WiderTransfer199Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer199C0,d2Log160Q,d2WiderTransfer199S0,d2WiderTransfer199Lo,d2WiderTransfer199Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer199C0 d2WiderTransfer199S0 d2Log160Q d2Log160Lo d2Log160Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log160Bounds
  have hn1 : x-((d2WiderTransfer199S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer199S1,d2WiderTransfer199Lo,d2WiderTransfer199Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer199C1 then |x-((d2WiderTransfer199S1:ℚ):ℝ)| ≤ ((d2Log14Q:ℚ):ℝ) else ((d2Log14Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer199S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer199S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer199S1,d2WiderTransfer199Lo,d2WiderTransfer199Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers024.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer199C1,d2Log14Q,d2WiderTransfer199S1,d2WiderTransfer199Lo,d2WiderTransfer199Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer199C1 d2WiderTransfer199S1 d2Log14Q d2Log14Lo d2Log14Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log14Bounds
  have har : (((weightedUpper d2WiderTransfer199C0 d2Log160Lo d2Log160Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer199C1 d2Log14Lo d2Log14Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer199Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer199Arithmetic
  linarith
#print axioms d2WiderTransfer199Arithmetic
#print axioms d2WiderTransfer199Bound
end CatalanMeasure.GenD.Signed.Data.Cells

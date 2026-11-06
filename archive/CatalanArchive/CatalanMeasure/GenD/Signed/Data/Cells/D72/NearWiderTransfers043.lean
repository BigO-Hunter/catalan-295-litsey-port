module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache009
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers043
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers043
open D72.LogTransfer
def d2WiderTransfer344Lo : ℚ := (d2LitsNearWiderTransfers043.q2 (1364656279) 1 (-31))
def d2WiderTransfer344Hi : ℚ := (d2LitsNearWiderTransfers043.q2 (85395875) 1 (-27))
def d2WiderTransfer344Cap : ℚ := (d2LitsNearWiderTransfers043.q2 (18084021117584539960149) 1 (-80))
def d2WiderTransfer344C0 : ℚ := (d2LitsNearWiderTransfers043.q2 (23) 25 (-5))
def d2WiderTransfer344S0 : ℚ := (d2LitsNearWiderTransfers043.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer344Arithmetic : weightedUpper d2WiderTransfer344C0 d2Log155Lo d2Log155Hi ≤ d2WiderTransfer344Cap := by decide +kernel
theorem d2WiderTransfer344Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer344Lo:ℚ):ℝ) ((d2WiderTransfer344Hi:ℚ):ℝ), ((d2WiderTransfer344C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer344S0:ℚ):ℝ)| ≤ ((d2WiderTransfer344Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer344S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer344S0,d2WiderTransfer344Lo,d2WiderTransfer344Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer344C0 then |x-((d2WiderTransfer344S0:ℚ):ℝ)| ≤ ((d2Log155Q:ℚ):ℝ) else ((d2Log155Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer344S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer344S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer344S0,d2WiderTransfer344Lo,d2WiderTransfer344Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer344C0,d2Log155Q,d2WiderTransfer344S0,d2WiderTransfer344Lo,d2WiderTransfer344Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer344C0 d2WiderTransfer344S0 d2Log155Q d2Log155Lo d2Log155Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log155Bounds
  have har : (((weightedUpper d2WiderTransfer344C0 d2Log155Lo d2Log155Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer344Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer344Arithmetic
  linarith
#print axioms d2WiderTransfer344Arithmetic
#print axioms d2WiderTransfer344Bound
def d2WiderTransfer345Lo : ℚ := (d2LitsNearWiderTransfers043.q2 (1364656279) 1 (-31))
def d2WiderTransfer345Hi : ℚ := (d2LitsNearWiderTransfers043.q2 (85395875) 1 (-27))
def d2WiderTransfer345Cap : ℚ := (d2LitsNearWiderTransfers043.q2 (34935008508851810255701) 1 (-80))
def d2WiderTransfer345C0 : ℚ := (d2LitsNearWiderTransfers043.q2 (3) 275 (-5))
def d2WiderTransfer345S0 : ℚ := (d2LitsNearWiderTransfers043.q2 (-1) 1 (0))
def d2WiderTransfer345C1 : ℚ := (d2LitsNearWiderTransfers043.q2 (-5) 11 (-4))
def d2WiderTransfer345S1 : ℚ := (d2LitsNearWiderTransfers043.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer345Arithmetic : weightedUpper d2WiderTransfer345C0 d2Log155Lo d2Log155Hi + weightedUpper d2WiderTransfer345C1 d2Log19Lo d2Log19Hi ≤ d2WiderTransfer345Cap := by decide +kernel
theorem d2WiderTransfer345Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer345Lo:ℚ):ℝ) ((d2WiderTransfer345Hi:ℚ):ℝ), ((d2WiderTransfer345C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer345S0:ℚ):ℝ)| + ((d2WiderTransfer345C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer345S1:ℚ):ℝ)| ≤ ((d2WiderTransfer345Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer345S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer345S0,d2WiderTransfer345Lo,d2WiderTransfer345Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer345C0 then |x-((d2WiderTransfer345S0:ℚ):ℝ)| ≤ ((d2Log155Q:ℚ):ℝ) else ((d2Log155Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer345S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer345S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer345S0,d2WiderTransfer345Lo,d2WiderTransfer345Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer345C0,d2Log155Q,d2WiderTransfer345S0,d2WiderTransfer345Lo,d2WiderTransfer345Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer345C0 d2WiderTransfer345S0 d2Log155Q d2Log155Lo d2Log155Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log155Bounds
  have hn1 : x-((d2WiderTransfer345S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer345S1,d2WiderTransfer345Lo,d2WiderTransfer345Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer345C1 then |x-((d2WiderTransfer345S1:ℚ):ℝ)| ≤ ((d2Log19Q:ℚ):ℝ) else ((d2Log19Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer345S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer345S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer345S1,d2WiderTransfer345Lo,d2WiderTransfer345Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer345C1,d2Log19Q,d2WiderTransfer345S1,d2WiderTransfer345Lo,d2WiderTransfer345Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer345C1 d2WiderTransfer345S1 d2Log19Q d2Log19Lo d2Log19Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log19Bounds
  have har : (((weightedUpper d2WiderTransfer345C0 d2Log155Lo d2Log155Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer345C1 d2Log19Lo d2Log19Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer345Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer345Arithmetic
  linarith
#print axioms d2WiderTransfer345Arithmetic
#print axioms d2WiderTransfer345Bound
def d2WiderTransfer346Lo : ℚ := (d2LitsNearWiderTransfers043.q2 (85395875) 1 (-27))
def d2WiderTransfer346Hi : ℚ := (d2LitsNearWiderTransfers043.q2 (1368011721) 1 (-31))
def d2WiderTransfer346Cap : ℚ := (d2LitsNearWiderTransfers043.q2 (2826264967930141037325) 1 (-80))
def d2WiderTransfer346C0 : ℚ := (d2LitsNearWiderTransfers043.q2 (-1) 55 (-3))
def d2WiderTransfer346S0 : ℚ := (d2LitsNearWiderTransfers043.q2 (-1) 1 (0))
def d2WiderTransfer346C1 : ℚ := (d2LitsNearWiderTransfers043.q2 (-1) 55 (-3))
def d2WiderTransfer346S1 : ℚ := (d2LitsNearWiderTransfers043.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer346Arithmetic : weightedUpper d2WiderTransfer346C0 d2Log155Lo d2Log155Hi + weightedUpper d2WiderTransfer346C1 d2Log18Lo d2Log18Hi ≤ d2WiderTransfer346Cap := by decide +kernel
theorem d2WiderTransfer346Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer346Lo:ℚ):ℝ) ((d2WiderTransfer346Hi:ℚ):ℝ), ((d2WiderTransfer346C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer346S0:ℚ):ℝ)| + ((d2WiderTransfer346C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer346S1:ℚ):ℝ)| ≤ ((d2WiderTransfer346Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer346S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer346S0,d2WiderTransfer346Lo,d2WiderTransfer346Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer346C0 then |x-((d2WiderTransfer346S0:ℚ):ℝ)| ≤ ((d2Log155Q:ℚ):ℝ) else ((d2Log155Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer346S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer346S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer346S0,d2WiderTransfer346Lo,d2WiderTransfer346Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer346C0,d2Log155Q,d2WiderTransfer346S0,d2WiderTransfer346Lo,d2WiderTransfer346Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer346C0 d2WiderTransfer346S0 d2Log155Q d2Log155Lo d2Log155Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log155Bounds
  have hn1 : x-((d2WiderTransfer346S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer346S1,d2WiderTransfer346Lo,d2WiderTransfer346Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer346C1 then |x-((d2WiderTransfer346S1:ℚ):ℝ)| ≤ ((d2Log18Q:ℚ):ℝ) else ((d2Log18Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer346S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer346S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer346S1,d2WiderTransfer346Lo,d2WiderTransfer346Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer346C1,d2Log18Q,d2WiderTransfer346S1,d2WiderTransfer346Lo,d2WiderTransfer346Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer346C1 d2WiderTransfer346S1 d2Log18Q d2Log18Lo d2Log18Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log18Bounds
  have har : (((weightedUpper d2WiderTransfer346C0 d2Log155Lo d2Log155Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer346C1 d2Log18Lo d2Log18Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer346Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer346Arithmetic
  linarith
#print axioms d2WiderTransfer346Arithmetic
#print axioms d2WiderTransfer346Bound
def d2WiderTransfer347Lo : ℚ := (d2LitsNearWiderTransfers043.q2 (85395875) 1 (-27))
def d2WiderTransfer347Hi : ℚ := (d2LitsNearWiderTransfers043.q2 (1368011721) 1 (-31))
def d2WiderTransfer347Cap : ℚ := (d2LitsNearWiderTransfers043.q2 (18158060841856427971341) 1 (-80))
def d2WiderTransfer347C0 : ℚ := (d2LitsNearWiderTransfers043.q2 (23) 25 (-5))
def d2WiderTransfer347S0 : ℚ := (d2LitsNearWiderTransfers043.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer347Arithmetic : weightedUpper d2WiderTransfer347C0 d2Log156Lo d2Log156Hi ≤ d2WiderTransfer347Cap := by decide +kernel
theorem d2WiderTransfer347Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer347Lo:ℚ):ℝ) ((d2WiderTransfer347Hi:ℚ):ℝ), ((d2WiderTransfer347C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer347S0:ℚ):ℝ)| ≤ ((d2WiderTransfer347Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer347S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer347S0,d2WiderTransfer347Lo,d2WiderTransfer347Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer347C0 then |x-((d2WiderTransfer347S0:ℚ):ℝ)| ≤ ((d2Log156Q:ℚ):ℝ) else ((d2Log156Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer347S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer347S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer347S0,d2WiderTransfer347Lo,d2WiderTransfer347Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer347C0,d2Log156Q,d2WiderTransfer347S0,d2WiderTransfer347Lo,d2WiderTransfer347Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer347C0 d2WiderTransfer347S0 d2Log156Q d2Log156Lo d2Log156Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log156Bounds
  have har : (((weightedUpper d2WiderTransfer347C0 d2Log156Lo d2Log156Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer347Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer347Arithmetic
  linarith
#print axioms d2WiderTransfer347Arithmetic
#print axioms d2WiderTransfer347Bound
def d2WiderTransfer348Lo : ℚ := (d2LitsNearWiderTransfers043.q2 (85395875) 1 (-27))
def d2WiderTransfer348Hi : ℚ := (d2LitsNearWiderTransfers043.q2 (1368011721) 1 (-31))
def d2WiderTransfer348Cap : ℚ := (d2LitsNearWiderTransfers043.q2 (35009048233123698266893) 1 (-80))
def d2WiderTransfer348C0 : ℚ := (d2LitsNearWiderTransfers043.q2 (3) 275 (-5))
def d2WiderTransfer348S0 : ℚ := (d2LitsNearWiderTransfers043.q2 (-1) 1 (0))
def d2WiderTransfer348C1 : ℚ := (d2LitsNearWiderTransfers043.q2 (-5) 11 (-4))
def d2WiderTransfer348S1 : ℚ := (d2LitsNearWiderTransfers043.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer348Arithmetic : weightedUpper d2WiderTransfer348C0 d2Log156Lo d2Log156Hi + weightedUpper d2WiderTransfer348C1 d2Log18Lo d2Log18Hi ≤ d2WiderTransfer348Cap := by decide +kernel
theorem d2WiderTransfer348Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer348Lo:ℚ):ℝ) ((d2WiderTransfer348Hi:ℚ):ℝ), ((d2WiderTransfer348C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer348S0:ℚ):ℝ)| + ((d2WiderTransfer348C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer348S1:ℚ):ℝ)| ≤ ((d2WiderTransfer348Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer348S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer348S0,d2WiderTransfer348Lo,d2WiderTransfer348Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer348C0 then |x-((d2WiderTransfer348S0:ℚ):ℝ)| ≤ ((d2Log156Q:ℚ):ℝ) else ((d2Log156Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer348S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer348S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer348S0,d2WiderTransfer348Lo,d2WiderTransfer348Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer348C0,d2Log156Q,d2WiderTransfer348S0,d2WiderTransfer348Lo,d2WiderTransfer348Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer348C0 d2WiderTransfer348S0 d2Log156Q d2Log156Lo d2Log156Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log156Bounds
  have hn1 : x-((d2WiderTransfer348S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer348S1,d2WiderTransfer348Lo,d2WiderTransfer348Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer348C1 then |x-((d2WiderTransfer348S1:ℚ):ℝ)| ≤ ((d2Log18Q:ℚ):ℝ) else ((d2Log18Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer348S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer348S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer348S1,d2WiderTransfer348Lo,d2WiderTransfer348Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer348C1,d2Log18Q,d2WiderTransfer348S1,d2WiderTransfer348Lo,d2WiderTransfer348Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer348C1 d2WiderTransfer348S1 d2Log18Q d2Log18Lo d2Log18Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log18Bounds
  have har : (((weightedUpper d2WiderTransfer348C0 d2Log156Lo d2Log156Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer348C1 d2Log18Lo d2Log18Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer348Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer348Arithmetic
  linarith
#print axioms d2WiderTransfer348Arithmetic
#print axioms d2WiderTransfer348Bound
def d2WiderTransfer349Lo : ℚ := (d2LitsNearWiderTransfers043.q2 (1368011721) 1 (-31))
def d2WiderTransfer349Hi : ℚ := (d2LitsNearWiderTransfers043.q2 (684844721) 1 (-30))
def d2WiderTransfer349Cap : ℚ := (d2LitsNearWiderTransfers043.q2 (1450231853993301240833) 1 (-79))
def d2WiderTransfer349C0 : ℚ := (d2LitsNearWiderTransfers043.q2 (-1) 55 (-3))
def d2WiderTransfer349S0 : ℚ := (d2LitsNearWiderTransfers043.q2 (-1) 1 (0))
def d2WiderTransfer349C1 : ℚ := (d2LitsNearWiderTransfers043.q2 (-1) 55 (-3))
def d2WiderTransfer349S1 : ℚ := (d2LitsNearWiderTransfers043.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer349Arithmetic : weightedUpper d2WiderTransfer349C0 d2Log156Lo d2Log156Hi + weightedUpper d2WiderTransfer349C1 d2Log17Lo d2Log17Hi ≤ d2WiderTransfer349Cap := by decide +kernel
theorem d2WiderTransfer349Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer349Lo:ℚ):ℝ) ((d2WiderTransfer349Hi:ℚ):ℝ), ((d2WiderTransfer349C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer349S0:ℚ):ℝ)| + ((d2WiderTransfer349C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer349S1:ℚ):ℝ)| ≤ ((d2WiderTransfer349Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer349S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer349S0,d2WiderTransfer349Lo,d2WiderTransfer349Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer349C0 then |x-((d2WiderTransfer349S0:ℚ):ℝ)| ≤ ((d2Log156Q:ℚ):ℝ) else ((d2Log156Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer349S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer349S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer349S0,d2WiderTransfer349Lo,d2WiderTransfer349Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer349C0,d2Log156Q,d2WiderTransfer349S0,d2WiderTransfer349Lo,d2WiderTransfer349Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer349C0 d2WiderTransfer349S0 d2Log156Q d2Log156Lo d2Log156Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log156Bounds
  have hn1 : x-((d2WiderTransfer349S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer349S1,d2WiderTransfer349Lo,d2WiderTransfer349Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer349C1 then |x-((d2WiderTransfer349S1:ℚ):ℝ)| ≤ ((d2Log17Q:ℚ):ℝ) else ((d2Log17Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer349S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer349S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer349S1,d2WiderTransfer349Lo,d2WiderTransfer349Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer349C1,d2Log17Q,d2WiderTransfer349S1,d2WiderTransfer349Lo,d2WiderTransfer349Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer349C1 d2WiderTransfer349S1 d2Log17Q d2Log17Lo d2Log17Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log17Bounds
  have har : (((weightedUpper d2WiderTransfer349C0 d2Log156Lo d2Log156Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer349C1 d2Log17Lo d2Log17Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer349Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer349Arithmetic
  linarith
#print axioms d2WiderTransfer349Arithmetic
#print axioms d2WiderTransfer349Bound
def d2WiderTransfer350Lo : ℚ := (d2LitsNearWiderTransfers043.q2 (1368011721) 1 (-31))
def d2WiderTransfer350Hi : ℚ := (d2LitsNearWiderTransfers043.q2 (684844721) 1 (-30))
def d2WiderTransfer350Cap : ℚ := (d2LitsNearWiderTransfers043.q2 (9116129790956444707841) 1 (-79))
def d2WiderTransfer350C0 : ℚ := (d2LitsNearWiderTransfers043.q2 (23) 25 (-5))
def d2WiderTransfer350S0 : ℚ := (d2LitsNearWiderTransfers043.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer350Arithmetic : weightedUpper d2WiderTransfer350C0 d2Log157Lo d2Log157Hi ≤ d2WiderTransfer350Cap := by decide +kernel
theorem d2WiderTransfer350Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer350Lo:ℚ):ℝ) ((d2WiderTransfer350Hi:ℚ):ℝ), ((d2WiderTransfer350C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer350S0:ℚ):ℝ)| ≤ ((d2WiderTransfer350Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer350S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer350S0,d2WiderTransfer350Lo,d2WiderTransfer350Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer350C0 then |x-((d2WiderTransfer350S0:ℚ):ℝ)| ≤ ((d2Log157Q:ℚ):ℝ) else ((d2Log157Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer350S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer350S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer350S0,d2WiderTransfer350Lo,d2WiderTransfer350Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer350C0,d2Log157Q,d2WiderTransfer350S0,d2WiderTransfer350Lo,d2WiderTransfer350Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer350C0 d2WiderTransfer350S0 d2Log157Q d2Log157Lo d2Log157Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log157Bounds
  have har : (((weightedUpper d2WiderTransfer350C0 d2Log157Lo d2Log157Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer350Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer350Arithmetic
  linarith
#print axioms d2WiderTransfer350Arithmetic
#print axioms d2WiderTransfer350Bound
def d2WiderTransfer351Lo : ℚ := (d2LitsNearWiderTransfers043.q2 (1368011721) 1 (-31))
def d2WiderTransfer351Hi : ℚ := (d2LitsNearWiderTransfers043.q2 (684844721) 1 (-30))
def d2WiderTransfer351Cap : ℚ := (d2LitsNearWiderTransfers043.q2 (17541623486590079855617) 1 (-79))
def d2WiderTransfer351C0 : ℚ := (d2LitsNearWiderTransfers043.q2 (3) 275 (-5))
def d2WiderTransfer351S0 : ℚ := (d2LitsNearWiderTransfers043.q2 (-1) 1 (0))
def d2WiderTransfer351C1 : ℚ := (d2LitsNearWiderTransfers043.q2 (-5) 11 (-4))
def d2WiderTransfer351S1 : ℚ := (d2LitsNearWiderTransfers043.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer351Arithmetic : weightedUpper d2WiderTransfer351C0 d2Log157Lo d2Log157Hi + weightedUpper d2WiderTransfer351C1 d2Log17Lo d2Log17Hi ≤ d2WiderTransfer351Cap := by decide +kernel
theorem d2WiderTransfer351Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer351Lo:ℚ):ℝ) ((d2WiderTransfer351Hi:ℚ):ℝ), ((d2WiderTransfer351C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer351S0:ℚ):ℝ)| + ((d2WiderTransfer351C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer351S1:ℚ):ℝ)| ≤ ((d2WiderTransfer351Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer351S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer351S0,d2WiderTransfer351Lo,d2WiderTransfer351Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer351C0 then |x-((d2WiderTransfer351S0:ℚ):ℝ)| ≤ ((d2Log157Q:ℚ):ℝ) else ((d2Log157Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer351S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer351S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer351S0,d2WiderTransfer351Lo,d2WiderTransfer351Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer351C0,d2Log157Q,d2WiderTransfer351S0,d2WiderTransfer351Lo,d2WiderTransfer351Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer351C0 d2WiderTransfer351S0 d2Log157Q d2Log157Lo d2Log157Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log157Bounds
  have hn1 : x-((d2WiderTransfer351S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer351S1,d2WiderTransfer351Lo,d2WiderTransfer351Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer351C1 then |x-((d2WiderTransfer351S1:ℚ):ℝ)| ≤ ((d2Log17Q:ℚ):ℝ) else ((d2Log17Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer351S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer351S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer351S1,d2WiderTransfer351Lo,d2WiderTransfer351Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers043.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer351C1,d2Log17Q,d2WiderTransfer351S1,d2WiderTransfer351Lo,d2WiderTransfer351Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer351C1 d2WiderTransfer351S1 d2Log17Q d2Log17Lo d2Log17Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log17Bounds
  have har : (((weightedUpper d2WiderTransfer351C0 d2Log157Lo d2Log157Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer351C1 d2Log17Lo d2Log17Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer351Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer351Arithmetic
  linarith
#print axioms d2WiderTransfer351Arithmetic
#print axioms d2WiderTransfer351Bound
end CatalanMeasure.GenD.Signed.Data.Cells

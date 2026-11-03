module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers021
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers021
open D72.LogTransfer
def d2Transfer168Lo : ℚ := (d2LitsNearTransfers021.q2 (31708803) 1 (-27))
def d2Transfer168Hi : ℚ := (d2LitsNearTransfers021.q2 (8346631) 1 (-25))
def d2Transfer168Cap : ℚ := (d2LitsNearTransfers021.q2 (16281318465) 1 (-40))
def d2Transfer168C0 : ℚ := (d2LitsNearTransfers021.q2 (1) 1 (-5))
def d2Transfer168S0 : ℚ := (d2LitsNearTransfers021.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer168Arithmetic : weightedUpper d2Transfer168C0 d2Log110Lo d2Log110Hi ≤ d2Transfer168Cap := by decide +kernel
theorem d2Transfer168Bound : ∀ x ∈ Set.Icc ((d2Transfer168Lo:ℚ):ℝ) ((d2Transfer168Hi:ℚ):ℝ), ((d2Transfer168C0:ℚ):ℝ)*Real.log |x-((d2Transfer168S0:ℚ):ℝ)| ≤ ((d2Transfer168Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer168S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer168S0,d2Transfer168Lo,d2Transfer168Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer168C0 then |x-((d2Transfer168S0:ℚ):ℝ)| ≤ ((d2Log110Q:ℚ):ℝ) else ((d2Log110Q:ℚ):ℝ) ≤ |x-((d2Transfer168S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer168S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer168S0,d2Transfer168Lo,d2Transfer168Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer168C0,d2Log110Q,d2Transfer168S0,d2Transfer168Lo,d2Transfer168Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer168C0 d2Transfer168S0 d2Log110Q d2Log110Lo d2Log110Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log110Bounds
  have har : (((weightedUpper d2Transfer168C0 d2Log110Lo d2Log110Hi:ℚ):ℝ)) ≤ ((d2Transfer168Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer168Arithmetic
  linarith
#print axioms d2Transfer168Arithmetic
#print axioms d2Transfer168Bound
def d2Transfer169Lo : ℚ := (d2LitsNearTransfers021.q2 (31708803) 1 (-27))
def d2Transfer169Hi : ℚ := (d2LitsNearTransfers021.q2 (8346631) 1 (-25))
def d2Transfer169Cap : ℚ := (d2LitsNearTransfers021.q2 (31165051305) 1 (-40))
def d2Transfer169C0 : ℚ := (d2LitsNearTransfers021.q2 (1) 11 (-5))
def d2Transfer169S0 : ℚ := (d2LitsNearTransfers021.q2 (-1) 1 (0))
def d2Transfer169C1 : ℚ := (d2LitsNearTransfers021.q2 (-5) 11 (-4))
def d2Transfer169S1 : ℚ := (d2LitsNearTransfers021.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer169Arithmetic : weightedUpper d2Transfer169C0 d2Log110Lo d2Log110Hi + weightedUpper d2Transfer169C1 d2Log64Lo d2Log64Hi ≤ d2Transfer169Cap := by decide +kernel
theorem d2Transfer169Bound : ∀ x ∈ Set.Icc ((d2Transfer169Lo:ℚ):ℝ) ((d2Transfer169Hi:ℚ):ℝ), ((d2Transfer169C0:ℚ):ℝ)*Real.log |x-((d2Transfer169S0:ℚ):ℝ)| + ((d2Transfer169C1:ℚ):ℝ)*Real.log |x-((d2Transfer169S1:ℚ):ℝ)| ≤ ((d2Transfer169Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer169S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer169S0,d2Transfer169Lo,d2Transfer169Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer169C0 then |x-((d2Transfer169S0:ℚ):ℝ)| ≤ ((d2Log110Q:ℚ):ℝ) else ((d2Log110Q:ℚ):ℝ) ≤ |x-((d2Transfer169S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer169S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer169S0,d2Transfer169Lo,d2Transfer169Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer169C0,d2Log110Q,d2Transfer169S0,d2Transfer169Lo,d2Transfer169Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer169C0 d2Transfer169S0 d2Log110Q d2Log110Lo d2Log110Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log110Bounds
  have hn1 : x-((d2Transfer169S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer169S1,d2Transfer169Lo,d2Transfer169Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer169C1 then |x-((d2Transfer169S1:ℚ):ℝ)| ≤ ((d2Log64Q:ℚ):ℝ) else ((d2Log64Q:ℚ):ℝ) ≤ |x-((d2Transfer169S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer169S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer169S1,d2Transfer169Lo,d2Transfer169Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer169C1,d2Log64Q,d2Transfer169S1,d2Transfer169Lo,d2Transfer169Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer169C1 d2Transfer169S1 d2Log64Q d2Log64Lo d2Log64Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log64Bounds
  have har : (((weightedUpper d2Transfer169C0 d2Log110Lo d2Log110Hi:ℚ):ℝ) + ((weightedUpper d2Transfer169C1 d2Log64Lo d2Log64Hi:ℚ):ℝ)) ≤ ((d2Transfer169Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer169Arithmetic
  linarith
#print axioms d2Transfer169Arithmetic
#print axioms d2Transfer169Bound
def d2Transfer170Lo : ℚ := (d2LitsNearTransfers021.q2 (8346631) 1 (-25))
def d2Transfer170Hi : ℚ := (d2LitsNearTransfers021.q2 (35064245) 1 (-27))
def d2Transfer170Cap : ℚ := (d2LitsNearTransfers021.q2 (649441385) 1 (-39))
def d2Transfer170C0 : ℚ := (d2LitsNearTransfers021.q2 (1) 25 (-4))
def d2Transfer170S0 : ℚ := (d2LitsNearTransfers021.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer170Arithmetic : weightedUpper d2Transfer170C0 d2Log111Lo d2Log111Hi ≤ d2Transfer170Cap := by decide +kernel
theorem d2Transfer170Bound : ∀ x ∈ Set.Icc ((d2Transfer170Lo:ℚ):ℝ) ((d2Transfer170Hi:ℚ):ℝ), ((d2Transfer170C0:ℚ):ℝ)*Real.log |x-((d2Transfer170S0:ℚ):ℝ)| ≤ ((d2Transfer170Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer170S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer170S0,d2Transfer170Lo,d2Transfer170Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer170C0 then |x-((d2Transfer170S0:ℚ):ℝ)| ≤ ((d2Log111Q:ℚ):ℝ) else ((d2Log111Q:ℚ):ℝ) ≤ |x-((d2Transfer170S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer170S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer170S0,d2Transfer170Lo,d2Transfer170Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer170C0,d2Log111Q,d2Transfer170S0,d2Transfer170Lo,d2Transfer170Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer170C0 d2Transfer170S0 d2Log111Q d2Log111Lo d2Log111Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log111Bounds
  have har : (((weightedUpper d2Transfer170C0 d2Log111Lo d2Log111Hi:ℚ):ℝ)) ≤ ((d2Transfer170Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer170Arithmetic
  linarith
#print axioms d2Transfer170Arithmetic
#print axioms d2Transfer170Bound
def d2Transfer171Lo : ℚ := (d2LitsNearTransfers021.q2 (8346631) 1 (-25))
def d2Transfer171Hi : ℚ := (d2LitsNearTransfers021.q2 (35064245) 1 (-27))
def d2Transfer171Cap : ℚ := (d2LitsNearTransfers021.q2 (2436024149) 1 (-40))
def d2Transfer171C0 : ℚ := (d2LitsNearTransfers021.q2 (1) 275 (-4))
def d2Transfer171S0 : ℚ := (d2LitsNearTransfers021.q2 (-1) 1 (0))
def d2Transfer171C1 : ℚ := (d2LitsNearTransfers021.q2 (-1) 55 (-3))
def d2Transfer171S1 : ℚ := (d2LitsNearTransfers021.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer171Arithmetic : weightedUpper d2Transfer171C0 d2Log111Lo d2Log111Hi + weightedUpper d2Transfer171C1 d2Log63Lo d2Log63Hi ≤ d2Transfer171Cap := by decide +kernel
theorem d2Transfer171Bound : ∀ x ∈ Set.Icc ((d2Transfer171Lo:ℚ):ℝ) ((d2Transfer171Hi:ℚ):ℝ), ((d2Transfer171C0:ℚ):ℝ)*Real.log |x-((d2Transfer171S0:ℚ):ℝ)| + ((d2Transfer171C1:ℚ):ℝ)*Real.log |x-((d2Transfer171S1:ℚ):ℝ)| ≤ ((d2Transfer171Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer171S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer171S0,d2Transfer171Lo,d2Transfer171Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer171C0 then |x-((d2Transfer171S0:ℚ):ℝ)| ≤ ((d2Log111Q:ℚ):ℝ) else ((d2Log111Q:ℚ):ℝ) ≤ |x-((d2Transfer171S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer171S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer171S0,d2Transfer171Lo,d2Transfer171Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer171C0,d2Log111Q,d2Transfer171S0,d2Transfer171Lo,d2Transfer171Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer171C0 d2Transfer171S0 d2Log111Q d2Log111Lo d2Log111Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log111Bounds
  have hn1 : x-((d2Transfer171S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer171S1,d2Transfer171Lo,d2Transfer171Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer171C1 then |x-((d2Transfer171S1:ℚ):ℝ)| ≤ ((d2Log63Q:ℚ):ℝ) else ((d2Log63Q:ℚ):ℝ) ≤ |x-((d2Transfer171S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer171S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer171S1,d2Transfer171Lo,d2Transfer171Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer171C1,d2Log63Q,d2Transfer171S1,d2Transfer171Lo,d2Transfer171Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer171C1 d2Transfer171S1 d2Log63Q d2Log63Lo d2Log63Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log63Bounds
  have har : (((weightedUpper d2Transfer171C0 d2Log111Lo d2Log111Hi:ℚ):ℝ) + ((weightedUpper d2Transfer171C1 d2Log63Lo d2Log63Hi:ℚ):ℝ)) ≤ ((d2Transfer171Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer171Arithmetic
  linarith
#print axioms d2Transfer171Arithmetic
#print axioms d2Transfer171Bound
def d2Transfer172Lo : ℚ := (d2LitsNearTransfers021.q2 (8346631) 1 (-25))
def d2Transfer172Hi : ℚ := (d2LitsNearTransfers021.q2 (35064245) 1 (-27))
def d2Transfer172Cap : ℚ := (d2LitsNearTransfers021.q2 (16281318465) 1 (-40))
def d2Transfer172C0 : ℚ := (d2LitsNearTransfers021.q2 (1) 1 (-5))
def d2Transfer172S0 : ℚ := (d2LitsNearTransfers021.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer172Arithmetic : weightedUpper d2Transfer172C0 d2Log111Lo d2Log111Hi ≤ d2Transfer172Cap := by decide +kernel
theorem d2Transfer172Bound : ∀ x ∈ Set.Icc ((d2Transfer172Lo:ℚ):ℝ) ((d2Transfer172Hi:ℚ):ℝ), ((d2Transfer172C0:ℚ):ℝ)*Real.log |x-((d2Transfer172S0:ℚ):ℝ)| ≤ ((d2Transfer172Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer172S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer172S0,d2Transfer172Lo,d2Transfer172Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer172C0 then |x-((d2Transfer172S0:ℚ):ℝ)| ≤ ((d2Log111Q:ℚ):ℝ) else ((d2Log111Q:ℚ):ℝ) ≤ |x-((d2Transfer172S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer172S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer172S0,d2Transfer172Lo,d2Transfer172Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer172C0,d2Log111Q,d2Transfer172S0,d2Transfer172Lo,d2Transfer172Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer172C0 d2Transfer172S0 d2Log111Q d2Log111Lo d2Log111Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log111Bounds
  have har : (((weightedUpper d2Transfer172C0 d2Log111Lo d2Log111Hi:ℚ):ℝ)) ≤ ((d2Transfer172Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer172Arithmetic
  linarith
#print axioms d2Transfer172Arithmetic
#print axioms d2Transfer172Bound
def d2Transfer173Lo : ℚ := (d2LitsNearTransfers021.q2 (8346631) 1 (-25))
def d2Transfer173Hi : ℚ := (d2LitsNearTransfers021.q2 (35064245) 1 (-27))
def d2Transfer173Cap : ℚ := (d2LitsNearTransfers021.q2 (31165051305) 1 (-40))
def d2Transfer173C0 : ℚ := (d2LitsNearTransfers021.q2 (1) 11 (-5))
def d2Transfer173S0 : ℚ := (d2LitsNearTransfers021.q2 (-1) 1 (0))
def d2Transfer173C1 : ℚ := (d2LitsNearTransfers021.q2 (-5) 11 (-4))
def d2Transfer173S1 : ℚ := (d2LitsNearTransfers021.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer173Arithmetic : weightedUpper d2Transfer173C0 d2Log111Lo d2Log111Hi + weightedUpper d2Transfer173C1 d2Log63Lo d2Log63Hi ≤ d2Transfer173Cap := by decide +kernel
theorem d2Transfer173Bound : ∀ x ∈ Set.Icc ((d2Transfer173Lo:ℚ):ℝ) ((d2Transfer173Hi:ℚ):ℝ), ((d2Transfer173C0:ℚ):ℝ)*Real.log |x-((d2Transfer173S0:ℚ):ℝ)| + ((d2Transfer173C1:ℚ):ℝ)*Real.log |x-((d2Transfer173S1:ℚ):ℝ)| ≤ ((d2Transfer173Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer173S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer173S0,d2Transfer173Lo,d2Transfer173Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer173C0 then |x-((d2Transfer173S0:ℚ):ℝ)| ≤ ((d2Log111Q:ℚ):ℝ) else ((d2Log111Q:ℚ):ℝ) ≤ |x-((d2Transfer173S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer173S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer173S0,d2Transfer173Lo,d2Transfer173Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer173C0,d2Log111Q,d2Transfer173S0,d2Transfer173Lo,d2Transfer173Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer173C0 d2Transfer173S0 d2Log111Q d2Log111Lo d2Log111Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log111Bounds
  have hn1 : x-((d2Transfer173S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer173S1,d2Transfer173Lo,d2Transfer173Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer173C1 then |x-((d2Transfer173S1:ℚ):ℝ)| ≤ ((d2Log63Q:ℚ):ℝ) else ((d2Log63Q:ℚ):ℝ) ≤ |x-((d2Transfer173S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer173S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer173S1,d2Transfer173Lo,d2Transfer173Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer173C1,d2Log63Q,d2Transfer173S1,d2Transfer173Lo,d2Transfer173Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer173C1 d2Transfer173S1 d2Log63Q d2Log63Lo d2Log63Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log63Bounds
  have har : (((weightedUpper d2Transfer173C0 d2Log111Lo d2Log111Hi:ℚ):ℝ) + ((weightedUpper d2Transfer173C1 d2Log63Lo d2Log63Hi:ℚ):ℝ)) ≤ ((d2Transfer173Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer173Arithmetic
  linarith
#print axioms d2Transfer173Arithmetic
#print axioms d2Transfer173Bound
def d2Transfer174Lo : ℚ := (d2LitsNearTransfers021.q2 (35064245) 1 (-27))
def d2Transfer174Hi : ℚ := (d2LitsNearTransfers021.q2 (18370983) 1 (-26))
def d2Transfer174Cap : ℚ := (d2LitsNearTransfers021.q2 (649441385) 1 (-39))
def d2Transfer174C0 : ℚ := (d2LitsNearTransfers021.q2 (1) 25 (-4))
def d2Transfer174S0 : ℚ := (d2LitsNearTransfers021.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer174Arithmetic : weightedUpper d2Transfer174C0 d2Log112Lo d2Log112Hi ≤ d2Transfer174Cap := by decide +kernel
theorem d2Transfer174Bound : ∀ x ∈ Set.Icc ((d2Transfer174Lo:ℚ):ℝ) ((d2Transfer174Hi:ℚ):ℝ), ((d2Transfer174C0:ℚ):ℝ)*Real.log |x-((d2Transfer174S0:ℚ):ℝ)| ≤ ((d2Transfer174Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer174S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer174S0,d2Transfer174Lo,d2Transfer174Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer174C0 then |x-((d2Transfer174S0:ℚ):ℝ)| ≤ ((d2Log112Q:ℚ):ℝ) else ((d2Log112Q:ℚ):ℝ) ≤ |x-((d2Transfer174S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer174S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer174S0,d2Transfer174Lo,d2Transfer174Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer174C0,d2Log112Q,d2Transfer174S0,d2Transfer174Lo,d2Transfer174Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer174C0 d2Transfer174S0 d2Log112Q d2Log112Lo d2Log112Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log112Bounds
  have har : (((weightedUpper d2Transfer174C0 d2Log112Lo d2Log112Hi:ℚ):ℝ)) ≤ ((d2Transfer174Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer174Arithmetic
  linarith
#print axioms d2Transfer174Arithmetic
#print axioms d2Transfer174Bound
def d2Transfer175Lo : ℚ := (d2LitsNearTransfers021.q2 (35064245) 1 (-27))
def d2Transfer175Hi : ℚ := (d2LitsNearTransfers021.q2 (18370983) 1 (-26))
def d2Transfer175Cap : ℚ := (d2LitsNearTransfers021.q2 (2436024149) 1 (-40))
def d2Transfer175C0 : ℚ := (d2LitsNearTransfers021.q2 (1) 275 (-4))
def d2Transfer175S0 : ℚ := (d2LitsNearTransfers021.q2 (-1) 1 (0))
def d2Transfer175C1 : ℚ := (d2LitsNearTransfers021.q2 (-1) 55 (-3))
def d2Transfer175S1 : ℚ := (d2LitsNearTransfers021.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer175Arithmetic : weightedUpper d2Transfer175C0 d2Log112Lo d2Log112Hi + weightedUpper d2Transfer175C1 d2Log62Lo d2Log62Hi ≤ d2Transfer175Cap := by decide +kernel
theorem d2Transfer175Bound : ∀ x ∈ Set.Icc ((d2Transfer175Lo:ℚ):ℝ) ((d2Transfer175Hi:ℚ):ℝ), ((d2Transfer175C0:ℚ):ℝ)*Real.log |x-((d2Transfer175S0:ℚ):ℝ)| + ((d2Transfer175C1:ℚ):ℝ)*Real.log |x-((d2Transfer175S1:ℚ):ℝ)| ≤ ((d2Transfer175Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer175S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer175S0,d2Transfer175Lo,d2Transfer175Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer175C0 then |x-((d2Transfer175S0:ℚ):ℝ)| ≤ ((d2Log112Q:ℚ):ℝ) else ((d2Log112Q:ℚ):ℝ) ≤ |x-((d2Transfer175S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer175S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer175S0,d2Transfer175Lo,d2Transfer175Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer175C0,d2Log112Q,d2Transfer175S0,d2Transfer175Lo,d2Transfer175Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer175C0 d2Transfer175S0 d2Log112Q d2Log112Lo d2Log112Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log112Bounds
  have hn1 : x-((d2Transfer175S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer175S1,d2Transfer175Lo,d2Transfer175Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer175C1 then |x-((d2Transfer175S1:ℚ):ℝ)| ≤ ((d2Log62Q:ℚ):ℝ) else ((d2Log62Q:ℚ):ℝ) ≤ |x-((d2Transfer175S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer175S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer175S1,d2Transfer175Lo,d2Transfer175Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers021.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer175C1,d2Log62Q,d2Transfer175S1,d2Transfer175Lo,d2Transfer175Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer175C1 d2Transfer175S1 d2Log62Q d2Log62Lo d2Log62Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log62Bounds
  have har : (((weightedUpper d2Transfer175C0 d2Log112Lo d2Log112Hi:ℚ):ℝ) + ((weightedUpper d2Transfer175C1 d2Log62Lo d2Log62Hi:ℚ):ℝ)) ≤ ((d2Transfer175Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer175Arithmetic
  linarith
#print axioms d2Transfer175Arithmetic
#print axioms d2Transfer175Bound
end CatalanMeasure.GenD.Signed.Data.Cells

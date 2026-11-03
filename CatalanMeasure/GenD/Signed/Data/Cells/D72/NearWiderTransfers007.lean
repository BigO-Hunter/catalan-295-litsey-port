module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
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
namespace d2LitsNearWiderTransfers007
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers007
open D72.LogTransfer
def d2WiderTransfer56Lo : ℚ := (d2LitsNearWiderTransfers007.q2 (8304657) 1 (-26))
def d2WiderTransfer56Hi : ℚ := (d2LitsNearWiderTransfers007.q2 (4991189) 1 (-25))
def d2WiderTransfer56Cap : ℚ := (d2LitsNearWiderTransfers007.q2 (16281318465) 1 (-40))
def d2WiderTransfer56C0 : ℚ := (d2LitsNearWiderTransfers007.q2 (1) 1 (-5))
def d2WiderTransfer56S0 : ℚ := (d2LitsNearWiderTransfers007.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer56Arithmetic : weightedUpper d2WiderTransfer56C0 d2Log99Lo d2Log99Hi ≤ d2WiderTransfer56Cap := by decide +kernel
theorem d2WiderTransfer56Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer56Lo:ℚ):ℝ) ((d2WiderTransfer56Hi:ℚ):ℝ), ((d2WiderTransfer56C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer56S0:ℚ):ℝ)| ≤ ((d2WiderTransfer56Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer56S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer56S0,d2WiderTransfer56Lo,d2WiderTransfer56Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer56C0 then |x-((d2WiderTransfer56S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer56S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer56S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer56S0,d2WiderTransfer56Lo,d2WiderTransfer56Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer56C0,d2Log99Q,d2WiderTransfer56S0,d2WiderTransfer56Lo,d2WiderTransfer56Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer56C0 d2WiderTransfer56S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have har : (((weightedUpper d2WiderTransfer56C0 d2Log99Lo d2Log99Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer56Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer56Arithmetic
  linarith
#print axioms d2WiderTransfer56Arithmetic
#print axioms d2WiderTransfer56Bound
def d2WiderTransfer57Lo : ℚ := (d2LitsNearWiderTransfers007.q2 (8304657) 1 (-26))
def d2WiderTransfer57Hi : ℚ := (d2LitsNearWiderTransfers007.q2 (4991189) 1 (-25))
def d2WiderTransfer57Cap : ℚ := (d2LitsNearWiderTransfers007.q2 (31165051305) 1 (-40))
def d2WiderTransfer57C0 : ℚ := (d2LitsNearWiderTransfers007.q2 (1) 11 (-5))
def d2WiderTransfer57S0 : ℚ := (d2LitsNearWiderTransfers007.q2 (-1) 1 (0))
def d2WiderTransfer57C1 : ℚ := (d2LitsNearWiderTransfers007.q2 (-5) 11 (-4))
def d2WiderTransfer57S1 : ℚ := (d2LitsNearWiderTransfers007.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer57Arithmetic : weightedUpper d2WiderTransfer57C0 d2Log99Lo d2Log99Hi + weightedUpper d2WiderTransfer57C1 d2Log75Lo d2Log75Hi ≤ d2WiderTransfer57Cap := by decide +kernel
theorem d2WiderTransfer57Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer57Lo:ℚ):ℝ) ((d2WiderTransfer57Hi:ℚ):ℝ), ((d2WiderTransfer57C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer57S0:ℚ):ℝ)| + ((d2WiderTransfer57C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer57S1:ℚ):ℝ)| ≤ ((d2WiderTransfer57Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer57S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer57S0,d2WiderTransfer57Lo,d2WiderTransfer57Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer57C0 then |x-((d2WiderTransfer57S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer57S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer57S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer57S0,d2WiderTransfer57Lo,d2WiderTransfer57Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer57C0,d2Log99Q,d2WiderTransfer57S0,d2WiderTransfer57Lo,d2WiderTransfer57Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer57C0 d2WiderTransfer57S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have hn1 : x-((d2WiderTransfer57S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer57S1,d2WiderTransfer57Lo,d2WiderTransfer57Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer57C1 then |x-((d2WiderTransfer57S1:ℚ):ℝ)| ≤ ((d2Log75Q:ℚ):ℝ) else ((d2Log75Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer57S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer57S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer57S1,d2WiderTransfer57Lo,d2WiderTransfer57Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer57C1,d2Log75Q,d2WiderTransfer57S1,d2WiderTransfer57Lo,d2WiderTransfer57Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer57C1 d2WiderTransfer57S1 d2Log75Q d2Log75Lo d2Log75Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log75Bounds
  have har : (((weightedUpper d2WiderTransfer57C0 d2Log99Lo d2Log99Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer57C1 d2Log75Lo d2Log75Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer57Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer57Arithmetic
  linarith
#print axioms d2WiderTransfer57Arithmetic
#print axioms d2WiderTransfer57Bound
def d2WiderTransfer58Lo : ℚ := (d2LitsNearWiderTransfers007.q2 (4991189) 1 (-25))
def d2WiderTransfer58Hi : ℚ := (d2LitsNearWiderTransfers007.q2 (3334455) 1 (-24))
def d2WiderTransfer58Cap : ℚ := (d2LitsNearWiderTransfers007.q2 (649441385) 1 (-39))
def d2WiderTransfer58C0 : ℚ := (d2LitsNearWiderTransfers007.q2 (1) 25 (-4))
def d2WiderTransfer58S0 : ℚ := (d2LitsNearWiderTransfers007.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer58Arithmetic : weightedUpper d2WiderTransfer58C0 d2Log106Lo d2Log106Hi ≤ d2WiderTransfer58Cap := by decide +kernel
theorem d2WiderTransfer58Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer58Lo:ℚ):ℝ) ((d2WiderTransfer58Hi:ℚ):ℝ), ((d2WiderTransfer58C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer58S0:ℚ):ℝ)| ≤ ((d2WiderTransfer58Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer58S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer58S0,d2WiderTransfer58Lo,d2WiderTransfer58Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer58C0 then |x-((d2WiderTransfer58S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer58S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer58S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer58S0,d2WiderTransfer58Lo,d2WiderTransfer58Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer58C0,d2Log106Q,d2WiderTransfer58S0,d2WiderTransfer58Lo,d2WiderTransfer58Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer58C0 d2WiderTransfer58S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have har : (((weightedUpper d2WiderTransfer58C0 d2Log106Lo d2Log106Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer58Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer58Arithmetic
  linarith
#print axioms d2WiderTransfer58Arithmetic
#print axioms d2WiderTransfer58Bound
def d2WiderTransfer59Lo : ℚ := (d2LitsNearWiderTransfers007.q2 (4991189) 1 (-25))
def d2WiderTransfer59Hi : ℚ := (d2LitsNearWiderTransfers007.q2 (3334455) 1 (-24))
def d2WiderTransfer59Cap : ℚ := (d2LitsNearWiderTransfers007.q2 (2436024149) 1 (-40))
def d2WiderTransfer59C0 : ℚ := (d2LitsNearWiderTransfers007.q2 (1) 275 (-4))
def d2WiderTransfer59S0 : ℚ := (d2LitsNearWiderTransfers007.q2 (-1) 1 (0))
def d2WiderTransfer59C1 : ℚ := (d2LitsNearWiderTransfers007.q2 (-1) 55 (-3))
def d2WiderTransfer59S1 : ℚ := (d2LitsNearWiderTransfers007.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer59Arithmetic : weightedUpper d2WiderTransfer59C0 d2Log106Lo d2Log106Hi + weightedUpper d2WiderTransfer59C1 d2Log68Lo d2Log68Hi ≤ d2WiderTransfer59Cap := by decide +kernel
theorem d2WiderTransfer59Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer59Lo:ℚ):ℝ) ((d2WiderTransfer59Hi:ℚ):ℝ), ((d2WiderTransfer59C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer59S0:ℚ):ℝ)| + ((d2WiderTransfer59C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer59S1:ℚ):ℝ)| ≤ ((d2WiderTransfer59Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer59S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer59S0,d2WiderTransfer59Lo,d2WiderTransfer59Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer59C0 then |x-((d2WiderTransfer59S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer59S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer59S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer59S0,d2WiderTransfer59Lo,d2WiderTransfer59Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer59C0,d2Log106Q,d2WiderTransfer59S0,d2WiderTransfer59Lo,d2WiderTransfer59Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer59C0 d2WiderTransfer59S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have hn1 : x-((d2WiderTransfer59S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer59S1,d2WiderTransfer59Lo,d2WiderTransfer59Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer59C1 then |x-((d2WiderTransfer59S1:ℚ):ℝ)| ≤ ((d2Log68Q:ℚ):ℝ) else ((d2Log68Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer59S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer59S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer59S1,d2WiderTransfer59Lo,d2WiderTransfer59Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer59C1,d2Log68Q,d2WiderTransfer59S1,d2WiderTransfer59Lo,d2WiderTransfer59Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer59C1 d2WiderTransfer59S1 d2Log68Q d2Log68Lo d2Log68Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log68Bounds
  have har : (((weightedUpper d2WiderTransfer59C0 d2Log106Lo d2Log106Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer59C1 d2Log68Lo d2Log68Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer59Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer59Arithmetic
  linarith
#print axioms d2WiderTransfer59Arithmetic
#print axioms d2WiderTransfer59Bound
def d2WiderTransfer60Lo : ℚ := (d2LitsNearWiderTransfers007.q2 (4991189) 1 (-25))
def d2WiderTransfer60Hi : ℚ := (d2LitsNearWiderTransfers007.q2 (3334455) 1 (-24))
def d2WiderTransfer60Cap : ℚ := (d2LitsNearWiderTransfers007.q2 (16281318465) 1 (-40))
def d2WiderTransfer60C0 : ℚ := (d2LitsNearWiderTransfers007.q2 (1) 1 (-5))
def d2WiderTransfer60S0 : ℚ := (d2LitsNearWiderTransfers007.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer60Arithmetic : weightedUpper d2WiderTransfer60C0 d2Log106Lo d2Log106Hi ≤ d2WiderTransfer60Cap := by decide +kernel
theorem d2WiderTransfer60Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer60Lo:ℚ):ℝ) ((d2WiderTransfer60Hi:ℚ):ℝ), ((d2WiderTransfer60C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer60S0:ℚ):ℝ)| ≤ ((d2WiderTransfer60Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer60S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer60S0,d2WiderTransfer60Lo,d2WiderTransfer60Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer60C0 then |x-((d2WiderTransfer60S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer60S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer60S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer60S0,d2WiderTransfer60Lo,d2WiderTransfer60Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer60C0,d2Log106Q,d2WiderTransfer60S0,d2WiderTransfer60Lo,d2WiderTransfer60Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer60C0 d2WiderTransfer60S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have har : (((weightedUpper d2WiderTransfer60C0 d2Log106Lo d2Log106Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer60Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer60Arithmetic
  linarith
#print axioms d2WiderTransfer60Arithmetic
#print axioms d2WiderTransfer60Bound
def d2WiderTransfer61Lo : ℚ := (d2LitsNearWiderTransfers007.q2 (4991189) 1 (-25))
def d2WiderTransfer61Hi : ℚ := (d2LitsNearWiderTransfers007.q2 (3334455) 1 (-24))
def d2WiderTransfer61Cap : ℚ := (d2LitsNearWiderTransfers007.q2 (31165051305) 1 (-40))
def d2WiderTransfer61C0 : ℚ := (d2LitsNearWiderTransfers007.q2 (1) 11 (-5))
def d2WiderTransfer61S0 : ℚ := (d2LitsNearWiderTransfers007.q2 (-1) 1 (0))
def d2WiderTransfer61C1 : ℚ := (d2LitsNearWiderTransfers007.q2 (-5) 11 (-4))
def d2WiderTransfer61S1 : ℚ := (d2LitsNearWiderTransfers007.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer61Arithmetic : weightedUpper d2WiderTransfer61C0 d2Log106Lo d2Log106Hi + weightedUpper d2WiderTransfer61C1 d2Log68Lo d2Log68Hi ≤ d2WiderTransfer61Cap := by decide +kernel
theorem d2WiderTransfer61Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer61Lo:ℚ):ℝ) ((d2WiderTransfer61Hi:ℚ):ℝ), ((d2WiderTransfer61C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer61S0:ℚ):ℝ)| + ((d2WiderTransfer61C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer61S1:ℚ):ℝ)| ≤ ((d2WiderTransfer61Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer61S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer61S0,d2WiderTransfer61Lo,d2WiderTransfer61Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer61C0 then |x-((d2WiderTransfer61S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer61S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer61S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer61S0,d2WiderTransfer61Lo,d2WiderTransfer61Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer61C0,d2Log106Q,d2WiderTransfer61S0,d2WiderTransfer61Lo,d2WiderTransfer61Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer61C0 d2WiderTransfer61S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have hn1 : x-((d2WiderTransfer61S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer61S1,d2WiderTransfer61Lo,d2WiderTransfer61Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer61C1 then |x-((d2WiderTransfer61S1:ℚ):ℝ)| ≤ ((d2Log68Q:ℚ):ℝ) else ((d2Log68Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer61S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer61S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer61S1,d2WiderTransfer61Lo,d2WiderTransfer61Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer61C1,d2Log68Q,d2WiderTransfer61S1,d2WiderTransfer61Lo,d2WiderTransfer61Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer61C1 d2WiderTransfer61S1 d2Log68Q d2Log68Lo d2Log68Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log68Bounds
  have har : (((weightedUpper d2WiderTransfer61C0 d2Log106Lo d2Log106Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer61C1 d2Log68Lo d2Log68Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer61Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer61Arithmetic
  linarith
#print axioms d2WiderTransfer61Arithmetic
#print axioms d2WiderTransfer61Bound
def d2WiderTransfer62Lo : ℚ := (d2LitsNearWiderTransfers007.q2 (3334455) 1 (-24))
def d2WiderTransfer62Hi : ℚ := (d2LitsNearWiderTransfers007.q2 (313261) 1 (-20))
def d2WiderTransfer62Cap : ℚ := (d2LitsNearWiderTransfers007.q2 (649441385) 1 (-39))
def d2WiderTransfer62C0 : ℚ := (d2LitsNearWiderTransfers007.q2 (1) 25 (-4))
def d2WiderTransfer62S0 : ℚ := (d2LitsNearWiderTransfers007.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer62Arithmetic : weightedUpper d2WiderTransfer62C0 d2Log113Lo d2Log113Hi ≤ d2WiderTransfer62Cap := by decide +kernel
theorem d2WiderTransfer62Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer62Lo:ℚ):ℝ) ((d2WiderTransfer62Hi:ℚ):ℝ), ((d2WiderTransfer62C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer62S0:ℚ):ℝ)| ≤ ((d2WiderTransfer62Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer62S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer62S0,d2WiderTransfer62Lo,d2WiderTransfer62Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer62C0 then |x-((d2WiderTransfer62S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer62S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer62S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer62S0,d2WiderTransfer62Lo,d2WiderTransfer62Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer62C0,d2Log113Q,d2WiderTransfer62S0,d2WiderTransfer62Lo,d2WiderTransfer62Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer62C0 d2WiderTransfer62S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have har : (((weightedUpper d2WiderTransfer62C0 d2Log113Lo d2Log113Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer62Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer62Arithmetic
  linarith
#print axioms d2WiderTransfer62Arithmetic
#print axioms d2WiderTransfer62Bound
def d2WiderTransfer63Lo : ℚ := (d2LitsNearWiderTransfers007.q2 (3334455) 1 (-24))
def d2WiderTransfer63Hi : ℚ := (d2LitsNearWiderTransfers007.q2 (313261) 1 (-20))
def d2WiderTransfer63Cap : ℚ := (d2LitsNearWiderTransfers007.q2 (2436024149) 1 (-40))
def d2WiderTransfer63C0 : ℚ := (d2LitsNearWiderTransfers007.q2 (1) 275 (-4))
def d2WiderTransfer63S0 : ℚ := (d2LitsNearWiderTransfers007.q2 (-1) 1 (0))
def d2WiderTransfer63C1 : ℚ := (d2LitsNearWiderTransfers007.q2 (-1) 55 (-3))
def d2WiderTransfer63S1 : ℚ := (d2LitsNearWiderTransfers007.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer63Arithmetic : weightedUpper d2WiderTransfer63C0 d2Log113Lo d2Log113Hi + weightedUpper d2WiderTransfer63C1 d2Log61Lo d2Log61Hi ≤ d2WiderTransfer63Cap := by decide +kernel
theorem d2WiderTransfer63Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer63Lo:ℚ):ℝ) ((d2WiderTransfer63Hi:ℚ):ℝ), ((d2WiderTransfer63C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer63S0:ℚ):ℝ)| + ((d2WiderTransfer63C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer63S1:ℚ):ℝ)| ≤ ((d2WiderTransfer63Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer63S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer63S0,d2WiderTransfer63Lo,d2WiderTransfer63Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer63C0 then |x-((d2WiderTransfer63S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer63S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer63S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer63S0,d2WiderTransfer63Lo,d2WiderTransfer63Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer63C0,d2Log113Q,d2WiderTransfer63S0,d2WiderTransfer63Lo,d2WiderTransfer63Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer63C0 d2WiderTransfer63S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have hn1 : x-((d2WiderTransfer63S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer63S1,d2WiderTransfer63Lo,d2WiderTransfer63Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer63C1 then |x-((d2WiderTransfer63S1:ℚ):ℝ)| ≤ ((d2Log61Q:ℚ):ℝ) else ((d2Log61Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer63S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer63S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer63S1,d2WiderTransfer63Lo,d2WiderTransfer63Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer63C1,d2Log61Q,d2WiderTransfer63S1,d2WiderTransfer63Lo,d2WiderTransfer63Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer63C1 d2WiderTransfer63S1 d2Log61Q d2Log61Lo d2Log61Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log61Bounds
  have har : (((weightedUpper d2WiderTransfer63C0 d2Log113Lo d2Log113Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer63C1 d2Log61Lo d2Log61Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer63Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer63Arithmetic
  linarith
#print axioms d2WiderTransfer63Arithmetic
#print axioms d2WiderTransfer63Bound
end CatalanMeasure.GenD.Signed.Data.Cells

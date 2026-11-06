module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers011
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers011
open D72.LogTransfer
def d2WiderTransfer88Lo : ℚ := (d2LitsNearWiderTransfers011.q2 (78684991) 1 (-27))
def d2WiderTransfer88Hi : ℚ := (d2LitsNearWiderTransfers011.q2 (10045339) 1 (-24))
def d2WiderTransfer88Cap : ℚ := (d2LitsNearWiderTransfers011.q2 (16281318465) 1 (-40))
def d2WiderTransfer88C0 : ℚ := (d2LitsNearWiderTransfers011.q2 (1) 1 (-5))
def d2WiderTransfer88S0 : ℚ := (d2LitsNearWiderTransfers011.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer88Arithmetic : weightedUpper d2WiderTransfer88C0 d2Log124Lo d2Log124Hi ≤ d2WiderTransfer88Cap := by decide +kernel
theorem d2WiderTransfer88Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer88Lo:ℚ):ℝ) ((d2WiderTransfer88Hi:ℚ):ℝ), ((d2WiderTransfer88C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer88S0:ℚ):ℝ)| ≤ ((d2WiderTransfer88Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer88S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer88S0,d2WiderTransfer88Lo,d2WiderTransfer88Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer88C0 then |x-((d2WiderTransfer88S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer88S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer88S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer88S0,d2WiderTransfer88Lo,d2WiderTransfer88Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer88C0,d2Log124Q,d2WiderTransfer88S0,d2WiderTransfer88Lo,d2WiderTransfer88Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer88C0 d2WiderTransfer88S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have har : (((weightedUpper d2WiderTransfer88C0 d2Log124Lo d2Log124Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer88Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer88Arithmetic
  linarith
#print axioms d2WiderTransfer88Arithmetic
#print axioms d2WiderTransfer88Bound
def d2WiderTransfer89Lo : ℚ := (d2LitsNearWiderTransfers011.q2 (78684991) 1 (-27))
def d2WiderTransfer89Hi : ℚ := (d2LitsNearWiderTransfers011.q2 (10045339) 1 (-24))
def d2WiderTransfer89Cap : ℚ := (d2LitsNearWiderTransfers011.q2 (31165051305) 1 (-40))
def d2WiderTransfer89C0 : ℚ := (d2LitsNearWiderTransfers011.q2 (1) 11 (-5))
def d2WiderTransfer89S0 : ℚ := (d2LitsNearWiderTransfers011.q2 (-1) 1 (0))
def d2WiderTransfer89C1 : ℚ := (d2LitsNearWiderTransfers011.q2 (-5) 11 (-4))
def d2WiderTransfer89S1 : ℚ := (d2LitsNearWiderTransfers011.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer89Arithmetic : weightedUpper d2WiderTransfer89C0 d2Log124Lo d2Log124Hi + weightedUpper d2WiderTransfer89C1 d2Log50Lo d2Log50Hi ≤ d2WiderTransfer89Cap := by decide +kernel
theorem d2WiderTransfer89Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer89Lo:ℚ):ℝ) ((d2WiderTransfer89Hi:ℚ):ℝ), ((d2WiderTransfer89C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer89S0:ℚ):ℝ)| + ((d2WiderTransfer89C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer89S1:ℚ):ℝ)| ≤ ((d2WiderTransfer89Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer89S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer89S0,d2WiderTransfer89Lo,d2WiderTransfer89Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer89C0 then |x-((d2WiderTransfer89S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer89S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer89S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer89S0,d2WiderTransfer89Lo,d2WiderTransfer89Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer89C0,d2Log124Q,d2WiderTransfer89S0,d2WiderTransfer89Lo,d2WiderTransfer89Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer89C0 d2WiderTransfer89S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have hn1 : x-((d2WiderTransfer89S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer89S1,d2WiderTransfer89Lo,d2WiderTransfer89Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer89C1 then |x-((d2WiderTransfer89S1:ℚ):ℝ)| ≤ ((d2Log50Q:ℚ):ℝ) else ((d2Log50Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer89S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer89S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer89S1,d2WiderTransfer89Lo,d2WiderTransfer89Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer89C1,d2Log50Q,d2WiderTransfer89S1,d2WiderTransfer89Lo,d2WiderTransfer89Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer89C1 d2WiderTransfer89S1 d2Log50Q d2Log50Lo d2Log50Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log50Bounds
  have har : (((weightedUpper d2WiderTransfer89C0 d2Log124Lo d2Log124Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer89C1 d2Log50Lo d2Log50Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer89Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer89Arithmetic
  linarith
#print axioms d2WiderTransfer89Arithmetic
#print axioms d2WiderTransfer89Bound
def d2WiderTransfer90Lo : ℚ := (d2LitsNearWiderTransfers011.q2 (10045339) 1 (-24))
def d2WiderTransfer90Hi : ℚ := (d2LitsNearWiderTransfers011.q2 (162403145) 1 (-28))
def d2WiderTransfer90Cap : ℚ := (d2LitsNearWiderTransfers011.q2 (357952183878138426799) 1 (-78))
def d2WiderTransfer90C0 : ℚ := (d2LitsNearWiderTransfers011.q2 (1) 25 (-4))
def d2WiderTransfer90S0 : ℚ := (d2LitsNearWiderTransfers011.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer90Arithmetic : weightedUpper d2WiderTransfer90C0 d2Log125Lo d2Log125Hi ≤ d2WiderTransfer90Cap := by decide +kernel
theorem d2WiderTransfer90Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer90Lo:ℚ):ℝ) ((d2WiderTransfer90Hi:ℚ):ℝ), ((d2WiderTransfer90C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer90S0:ℚ):ℝ)| ≤ ((d2WiderTransfer90Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer90S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer90S0,d2WiderTransfer90Lo,d2WiderTransfer90Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer90C0 then |x-((d2WiderTransfer90S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer90S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer90S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer90S0,d2WiderTransfer90Lo,d2WiderTransfer90Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer90C0,d2Log125Q,d2WiderTransfer90S0,d2WiderTransfer90Lo,d2WiderTransfer90Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer90C0 d2WiderTransfer90S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have har : (((weightedUpper d2WiderTransfer90C0 d2Log125Lo d2Log125Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer90Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer90Arithmetic
  linarith
#print axioms d2WiderTransfer90Arithmetic
#print axioms d2WiderTransfer90Bound
def d2WiderTransfer91Lo : ℚ := (d2LitsNearWiderTransfers011.q2 (10045339) 1 (-24))
def d2WiderTransfer91Hi : ℚ := (d2LitsNearWiderTransfers011.q2 (162403145) 1 (-28))
def d2WiderTransfer91Cap : ℚ := (d2LitsNearWiderTransfers011.q2 (670527226037072262575) 1 (-78))
def d2WiderTransfer91C0 : ℚ := (d2LitsNearWiderTransfers011.q2 (1) 275 (-4))
def d2WiderTransfer91S0 : ℚ := (d2LitsNearWiderTransfers011.q2 (-1) 1 (0))
def d2WiderTransfer91C1 : ℚ := (d2LitsNearWiderTransfers011.q2 (-1) 55 (-3))
def d2WiderTransfer91S1 : ℚ := (d2LitsNearWiderTransfers011.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer91Arithmetic : weightedUpper d2WiderTransfer91C0 d2Log125Lo d2Log125Hi + weightedUpper d2WiderTransfer91C1 d2Log49Lo d2Log49Hi ≤ d2WiderTransfer91Cap := by decide +kernel
theorem d2WiderTransfer91Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer91Lo:ℚ):ℝ) ((d2WiderTransfer91Hi:ℚ):ℝ), ((d2WiderTransfer91C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer91S0:ℚ):ℝ)| + ((d2WiderTransfer91C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer91S1:ℚ):ℝ)| ≤ ((d2WiderTransfer91Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer91S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer91S0,d2WiderTransfer91Lo,d2WiderTransfer91Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer91C0 then |x-((d2WiderTransfer91S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer91S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer91S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer91S0,d2WiderTransfer91Lo,d2WiderTransfer91Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer91C0,d2Log125Q,d2WiderTransfer91S0,d2WiderTransfer91Lo,d2WiderTransfer91Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer91C0 d2WiderTransfer91S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have hn1 : x-((d2WiderTransfer91S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer91S1,d2WiderTransfer91Lo,d2WiderTransfer91Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer91C1 then |x-((d2WiderTransfer91S1:ℚ):ℝ)| ≤ ((d2Log49Q:ℚ):ℝ) else ((d2Log49Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer91S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer91S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer91S1,d2WiderTransfer91Lo,d2WiderTransfer91Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer91C1,d2Log49Q,d2WiderTransfer91S1,d2WiderTransfer91Lo,d2WiderTransfer91Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer91C1 d2WiderTransfer91S1 d2Log49Q d2Log49Lo d2Log49Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log49Bounds
  have har : (((weightedUpper d2WiderTransfer91C0 d2Log125Lo d2Log125Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer91C1 d2Log49Lo d2Log49Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer91Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer91Arithmetic
  linarith
#print axioms d2WiderTransfer91Arithmetic
#print axioms d2WiderTransfer91Bound
def d2WiderTransfer92Lo : ℚ := (d2LitsNearWiderTransfers011.q2 (10045339) 1 (-24))
def d2WiderTransfer92Hi : ℚ := (d2LitsNearWiderTransfers011.q2 (162403145) 1 (-28))
def d2WiderTransfer92Cap : ℚ := (d2LitsNearWiderTransfers011.q2 (4476292748642812392879) 1 (-78))
def d2WiderTransfer92C0 : ℚ := (d2LitsNearWiderTransfers011.q2 (1) 1 (-5))
def d2WiderTransfer92S0 : ℚ := (d2LitsNearWiderTransfers011.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer92Arithmetic : weightedUpper d2WiderTransfer92C0 d2Log125Lo d2Log125Hi ≤ d2WiderTransfer92Cap := by decide +kernel
theorem d2WiderTransfer92Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer92Lo:ℚ):ℝ) ((d2WiderTransfer92Hi:ℚ):ℝ), ((d2WiderTransfer92C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer92S0:ℚ):ℝ)| ≤ ((d2WiderTransfer92Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer92S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer92S0,d2WiderTransfer92Lo,d2WiderTransfer92Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer92C0 then |x-((d2WiderTransfer92S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer92S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer92S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer92S0,d2WiderTransfer92Lo,d2WiderTransfer92Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer92C0,d2Log125Q,d2WiderTransfer92S0,d2WiderTransfer92Lo,d2WiderTransfer92Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer92C0 d2WiderTransfer92S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have har : (((weightedUpper d2WiderTransfer92C0 d2Log125Lo d2Log125Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer92Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer92Arithmetic
  linarith
#print axioms d2WiderTransfer92Arithmetic
#print axioms d2WiderTransfer92Bound
def d2WiderTransfer93Lo : ℚ := (d2LitsNearWiderTransfers011.q2 (10045339) 1 (-24))
def d2WiderTransfer93Hi : ℚ := (d2LitsNearWiderTransfers011.q2 (162403145) 1 (-28))
def d2WiderTransfer93Cap : ℚ := (d2LitsNearWiderTransfers011.q2 (8567502079215689233839) 1 (-78))
def d2WiderTransfer93C0 : ℚ := (d2LitsNearWiderTransfers011.q2 (1) 11 (-5))
def d2WiderTransfer93S0 : ℚ := (d2LitsNearWiderTransfers011.q2 (-1) 1 (0))
def d2WiderTransfer93C1 : ℚ := (d2LitsNearWiderTransfers011.q2 (-5) 11 (-4))
def d2WiderTransfer93S1 : ℚ := (d2LitsNearWiderTransfers011.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer93Arithmetic : weightedUpper d2WiderTransfer93C0 d2Log125Lo d2Log125Hi + weightedUpper d2WiderTransfer93C1 d2Log49Lo d2Log49Hi ≤ d2WiderTransfer93Cap := by decide +kernel
theorem d2WiderTransfer93Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer93Lo:ℚ):ℝ) ((d2WiderTransfer93Hi:ℚ):ℝ), ((d2WiderTransfer93C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer93S0:ℚ):ℝ)| + ((d2WiderTransfer93C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer93S1:ℚ):ℝ)| ≤ ((d2WiderTransfer93Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer93S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer93S0,d2WiderTransfer93Lo,d2WiderTransfer93Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer93C0 then |x-((d2WiderTransfer93S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer93S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer93S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer93S0,d2WiderTransfer93Lo,d2WiderTransfer93Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer93C0,d2Log125Q,d2WiderTransfer93S0,d2WiderTransfer93Lo,d2WiderTransfer93Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer93C0 d2WiderTransfer93S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have hn1 : x-((d2WiderTransfer93S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer93S1,d2WiderTransfer93Lo,d2WiderTransfer93Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer93C1 then |x-((d2WiderTransfer93S1:ℚ):ℝ)| ≤ ((d2Log49Q:ℚ):ℝ) else ((d2Log49Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer93S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer93S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer93S1,d2WiderTransfer93Lo,d2WiderTransfer93Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer93C1,d2Log49Q,d2WiderTransfer93S1,d2WiderTransfer93Lo,d2WiderTransfer93Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer93C1 d2WiderTransfer93S1 d2Log49Q d2Log49Lo d2Log49Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log49Bounds
  have har : (((weightedUpper d2WiderTransfer93C0 d2Log125Lo d2Log125Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer93C1 d2Log49Lo d2Log49Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer93Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer93Arithmetic
  linarith
#print axioms d2WiderTransfer93Arithmetic
#print axioms d2WiderTransfer93Bound
def d2WiderTransfer94Lo : ℚ := (d2LitsNearWiderTransfers011.q2 (162403145) 1 (-28))
def d2WiderTransfer94Hi : ℚ := (d2LitsNearWiderTransfers011.q2 (326484011) 1 (-29))
def d2WiderTransfer94Cap : ℚ := (d2LitsNearWiderTransfers011.q2 (1474206701587581144801) 1 (-80))
def d2WiderTransfer94C0 : ℚ := (d2LitsNearWiderTransfers011.q2 (1) 25 (-4))
def d2WiderTransfer94S0 : ℚ := (d2LitsNearWiderTransfers011.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer94Arithmetic : weightedUpper d2WiderTransfer94C0 d2Log126Lo d2Log126Hi ≤ d2WiderTransfer94Cap := by decide +kernel
theorem d2WiderTransfer94Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer94Lo:ℚ):ℝ) ((d2WiderTransfer94Hi:ℚ):ℝ), ((d2WiderTransfer94C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer94S0:ℚ):ℝ)| ≤ ((d2WiderTransfer94Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer94S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer94S0,d2WiderTransfer94Lo,d2WiderTransfer94Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer94C0 then |x-((d2WiderTransfer94S0:ℚ):ℝ)| ≤ ((d2Log126Q:ℚ):ℝ) else ((d2Log126Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer94S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer94S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer94S0,d2WiderTransfer94Lo,d2WiderTransfer94Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer94C0,d2Log126Q,d2WiderTransfer94S0,d2WiderTransfer94Lo,d2WiderTransfer94Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer94C0 d2WiderTransfer94S0 d2Log126Q d2Log126Lo d2Log126Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log126Bounds
  have har : (((weightedUpper d2WiderTransfer94C0 d2Log126Lo d2Log126Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer94Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer94Arithmetic
  linarith
#print axioms d2WiderTransfer94Arithmetic
#print axioms d2WiderTransfer94Bound
def d2WiderTransfer95Lo : ℚ := (d2LitsNearWiderTransfers011.q2 (162403145) 1 (-28))
def d2WiderTransfer95Hi : ℚ := (d2LitsNearWiderTransfers011.q2 (326484011) 1 (-29))
def d2WiderTransfer95Cap : ℚ := (d2LitsNearWiderTransfers011.q2 (2724506870223316487905) 1 (-80))
def d2WiderTransfer95C0 : ℚ := (d2LitsNearWiderTransfers011.q2 (1) 275 (-4))
def d2WiderTransfer95S0 : ℚ := (d2LitsNearWiderTransfers011.q2 (-1) 1 (0))
def d2WiderTransfer95C1 : ℚ := (d2LitsNearWiderTransfers011.q2 (-1) 55 (-3))
def d2WiderTransfer95S1 : ℚ := (d2LitsNearWiderTransfers011.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer95Arithmetic : weightedUpper d2WiderTransfer95C0 d2Log126Lo d2Log126Hi + weightedUpper d2WiderTransfer95C1 d2Log48Lo d2Log48Hi ≤ d2WiderTransfer95Cap := by decide +kernel
theorem d2WiderTransfer95Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer95Lo:ℚ):ℝ) ((d2WiderTransfer95Hi:ℚ):ℝ), ((d2WiderTransfer95C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer95S0:ℚ):ℝ)| + ((d2WiderTransfer95C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer95S1:ℚ):ℝ)| ≤ ((d2WiderTransfer95Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer95S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer95S0,d2WiderTransfer95Lo,d2WiderTransfer95Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer95C0 then |x-((d2WiderTransfer95S0:ℚ):ℝ)| ≤ ((d2Log126Q:ℚ):ℝ) else ((d2Log126Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer95S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer95S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer95S0,d2WiderTransfer95Lo,d2WiderTransfer95Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer95C0,d2Log126Q,d2WiderTransfer95S0,d2WiderTransfer95Lo,d2WiderTransfer95Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer95C0 d2WiderTransfer95S0 d2Log126Q d2Log126Lo d2Log126Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log126Bounds
  have hn1 : x-((d2WiderTransfer95S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer95S1,d2WiderTransfer95Lo,d2WiderTransfer95Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer95C1 then |x-((d2WiderTransfer95S1:ℚ):ℝ)| ≤ ((d2Log48Q:ℚ):ℝ) else ((d2Log48Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer95S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer95S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer95S1,d2WiderTransfer95Lo,d2WiderTransfer95Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers011.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer95C1,d2Log48Q,d2WiderTransfer95S1,d2WiderTransfer95Lo,d2WiderTransfer95Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer95C1 d2WiderTransfer95S1 d2Log48Q d2Log48Lo d2Log48Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log48Bounds
  have har : (((weightedUpper d2WiderTransfer95C0 d2Log126Lo d2Log126Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer95C1 d2Log48Lo d2Log48Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer95Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer95Arithmetic
  linarith
#print axioms d2WiderTransfer95Arithmetic
#print axioms d2WiderTransfer95Bound
end CatalanMeasure.GenD.Signed.Data.Cells

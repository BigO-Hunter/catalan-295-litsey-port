module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
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
namespace d2LitsNearTransfers068
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers068
open D72.LogTransfer
def d2Transfer544Lo : ℚ := (d2LitsNearTransfers068.q2 (339905779) 1 (-29))
def d2Transfer544Hi : ℚ := (d2LitsNearTransfers068.q2 (1361300837) 1 (-31))
def d2Transfer544Cap : ℚ := (d2LitsNearTransfers068.q2 (2531053359280603360305) 1 (-80))
def d2Transfer544C0 : ℚ := (d2LitsNearTransfers068.q2 (-1) 55 (-3))
def d2Transfer544S0 : ℚ := (d2LitsNearTransfers068.q2 (-1) 1 (0))
def d2Transfer544C1 : ℚ := (d2LitsNearTransfers068.q2 (-1) 55 (-3))
def d2Transfer544S1 : ℚ := (d2LitsNearTransfers068.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer544Arithmetic : weightedUpper d2Transfer544C0 d2Log151Lo d2Log151Hi + weightedUpper d2Transfer544C1 d2Log22Lo d2Log22Hi ≤ d2Transfer544Cap := by decide +kernel
theorem d2Transfer544Bound : ∀ x ∈ Set.Icc ((d2Transfer544Lo:ℚ):ℝ) ((d2Transfer544Hi:ℚ):ℝ), ((d2Transfer544C0:ℚ):ℝ)*Real.log |x-((d2Transfer544S0:ℚ):ℝ)| + ((d2Transfer544C1:ℚ):ℝ)*Real.log |x-((d2Transfer544S1:ℚ):ℝ)| ≤ ((d2Transfer544Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer544S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer544S0,d2Transfer544Lo,d2Transfer544Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer544C0 then |x-((d2Transfer544S0:ℚ):ℝ)| ≤ ((d2Log151Q:ℚ):ℝ) else ((d2Log151Q:ℚ):ℝ) ≤ |x-((d2Transfer544S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer544S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer544S0,d2Transfer544Lo,d2Transfer544Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer544C0,d2Log151Q,d2Transfer544S0,d2Transfer544Lo,d2Transfer544Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer544C0 d2Transfer544S0 d2Log151Q d2Log151Lo d2Log151Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log151Bounds
  have hn1 : x-((d2Transfer544S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer544S1,d2Transfer544Lo,d2Transfer544Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer544C1 then |x-((d2Transfer544S1:ℚ):ℝ)| ≤ ((d2Log22Q:ℚ):ℝ) else ((d2Log22Q:ℚ):ℝ) ≤ |x-((d2Transfer544S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer544S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer544S1,d2Transfer544Lo,d2Transfer544Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer544C1,d2Log22Q,d2Transfer544S1,d2Transfer544Lo,d2Transfer544Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer544C1 d2Transfer544S1 d2Log22Q d2Log22Lo d2Log22Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log22Bounds
  have har : (((weightedUpper d2Transfer544C0 d2Log151Lo d2Log151Hi:ℚ):ℝ) + ((weightedUpper d2Transfer544C1 d2Log22Lo d2Log22Hi:ℚ):ℝ)) ≤ ((d2Transfer544Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer544Arithmetic
  linarith
#print axioms d2Transfer544Arithmetic
#print axioms d2Transfer544Bound
def d2Transfer545Lo : ℚ := (d2LitsNearTransfers068.q2 (339905779) 1 (-29))
def d2Transfer545Hi : ℚ := (d2LitsNearTransfers068.q2 (1361300837) 1 (-31))
def d2Transfer545Cap : ℚ := (d2LitsNearTransfers068.q2 (17862849233206890294321) 1 (-80))
def d2Transfer545C0 : ℚ := (d2LitsNearTransfers068.q2 (23) 25 (-5))
def d2Transfer545S0 : ℚ := (d2LitsNearTransfers068.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer545Arithmetic : weightedUpper d2Transfer545C0 d2Log152Lo d2Log152Hi ≤ d2Transfer545Cap := by decide +kernel
theorem d2Transfer545Bound : ∀ x ∈ Set.Icc ((d2Transfer545Lo:ℚ):ℝ) ((d2Transfer545Hi:ℚ):ℝ), ((d2Transfer545C0:ℚ):ℝ)*Real.log |x-((d2Transfer545S0:ℚ):ℝ)| ≤ ((d2Transfer545Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer545S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer545S0,d2Transfer545Lo,d2Transfer545Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer545C0 then |x-((d2Transfer545S0:ℚ):ℝ)| ≤ ((d2Log152Q:ℚ):ℝ) else ((d2Log152Q:ℚ):ℝ) ≤ |x-((d2Transfer545S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer545S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer545S0,d2Transfer545Lo,d2Transfer545Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer545C0,d2Log152Q,d2Transfer545S0,d2Transfer545Lo,d2Transfer545Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer545C0 d2Transfer545S0 d2Log152Q d2Log152Lo d2Log152Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log152Bounds
  have har : (((weightedUpper d2Transfer545C0 d2Log152Lo d2Log152Hi:ℚ):ℝ)) ≤ ((d2Transfer545Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer545Arithmetic
  linarith
#print axioms d2Transfer545Arithmetic
#print axioms d2Transfer545Bound
def d2Transfer546Lo : ℚ := (d2LitsNearTransfers068.q2 (339905779) 1 (-29))
def d2Transfer546Hi : ℚ := (d2LitsNearTransfers068.q2 (1361300837) 1 (-31))
def d2Transfer546Cap : ℚ := (d2LitsNearTransfers068.q2 (34713836624474160589873) 1 (-80))
def d2Transfer546C0 : ℚ := (d2LitsNearTransfers068.q2 (3) 275 (-5))
def d2Transfer546S0 : ℚ := (d2LitsNearTransfers068.q2 (-1) 1 (0))
def d2Transfer546C1 : ℚ := (d2LitsNearTransfers068.q2 (-5) 11 (-4))
def d2Transfer546S1 : ℚ := (d2LitsNearTransfers068.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer546Arithmetic : weightedUpper d2Transfer546C0 d2Log152Lo d2Log152Hi + weightedUpper d2Transfer546C1 d2Log22Lo d2Log22Hi ≤ d2Transfer546Cap := by decide +kernel
theorem d2Transfer546Bound : ∀ x ∈ Set.Icc ((d2Transfer546Lo:ℚ):ℝ) ((d2Transfer546Hi:ℚ):ℝ), ((d2Transfer546C0:ℚ):ℝ)*Real.log |x-((d2Transfer546S0:ℚ):ℝ)| + ((d2Transfer546C1:ℚ):ℝ)*Real.log |x-((d2Transfer546S1:ℚ):ℝ)| ≤ ((d2Transfer546Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer546S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer546S0,d2Transfer546Lo,d2Transfer546Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer546C0 then |x-((d2Transfer546S0:ℚ):ℝ)| ≤ ((d2Log152Q:ℚ):ℝ) else ((d2Log152Q:ℚ):ℝ) ≤ |x-((d2Transfer546S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer546S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer546S0,d2Transfer546Lo,d2Transfer546Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer546C0,d2Log152Q,d2Transfer546S0,d2Transfer546Lo,d2Transfer546Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer546C0 d2Transfer546S0 d2Log152Q d2Log152Lo d2Log152Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log152Bounds
  have hn1 : x-((d2Transfer546S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer546S1,d2Transfer546Lo,d2Transfer546Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer546C1 then |x-((d2Transfer546S1:ℚ):ℝ)| ≤ ((d2Log22Q:ℚ):ℝ) else ((d2Log22Q:ℚ):ℝ) ≤ |x-((d2Transfer546S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer546S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer546S1,d2Transfer546Lo,d2Transfer546Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer546C1,d2Log22Q,d2Transfer546S1,d2Transfer546Lo,d2Transfer546Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer546C1 d2Transfer546S1 d2Log22Q d2Log22Lo d2Log22Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log22Bounds
  have har : (((weightedUpper d2Transfer546C0 d2Log152Lo d2Log152Hi:ℚ):ℝ) + ((weightedUpper d2Transfer546C1 d2Log22Lo d2Log22Hi:ℚ):ℝ)) ≤ ((d2Transfer546Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer546Arithmetic
  linarith
#print axioms d2Transfer546Arithmetic
#print axioms d2Transfer546Bound
def d2Transfer547Lo : ℚ := (d2LitsNearTransfers068.q2 (1361300837) 1 (-31))
def d2Transfer547Hi : ℚ := (d2LitsNearTransfers068.q2 (681489279) 1 (-30))
def d2Transfer547Cap : ℚ := (d2LitsNearTransfers068.q2 (1302310057795335633989) 1 (-79))
def d2Transfer547C0 : ℚ := (d2LitsNearTransfers068.q2 (-1) 55 (-3))
def d2Transfer547S0 : ℚ := (d2LitsNearTransfers068.q2 (-1) 1 (0))
def d2Transfer547C1 : ℚ := (d2LitsNearTransfers068.q2 (-1) 55 (-3))
def d2Transfer547S1 : ℚ := (d2LitsNearTransfers068.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer547Arithmetic : weightedUpper d2Transfer547C0 d2Log152Lo d2Log152Hi + weightedUpper d2Transfer547C1 d2Log21Lo d2Log21Hi ≤ d2Transfer547Cap := by decide +kernel
theorem d2Transfer547Bound : ∀ x ∈ Set.Icc ((d2Transfer547Lo:ℚ):ℝ) ((d2Transfer547Hi:ℚ):ℝ), ((d2Transfer547C0:ℚ):ℝ)*Real.log |x-((d2Transfer547S0:ℚ):ℝ)| + ((d2Transfer547C1:ℚ):ℝ)*Real.log |x-((d2Transfer547S1:ℚ):ℝ)| ≤ ((d2Transfer547Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer547S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer547S0,d2Transfer547Lo,d2Transfer547Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer547C0 then |x-((d2Transfer547S0:ℚ):ℝ)| ≤ ((d2Log152Q:ℚ):ℝ) else ((d2Log152Q:ℚ):ℝ) ≤ |x-((d2Transfer547S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer547S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer547S0,d2Transfer547Lo,d2Transfer547Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer547C0,d2Log152Q,d2Transfer547S0,d2Transfer547Lo,d2Transfer547Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer547C0 d2Transfer547S0 d2Log152Q d2Log152Lo d2Log152Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log152Bounds
  have hn1 : x-((d2Transfer547S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer547S1,d2Transfer547Lo,d2Transfer547Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer547C1 then |x-((d2Transfer547S1:ℚ):ℝ)| ≤ ((d2Log21Q:ℚ):ℝ) else ((d2Log21Q:ℚ):ℝ) ≤ |x-((d2Transfer547S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer547S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer547S1,d2Transfer547Lo,d2Transfer547Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer547C1,d2Log21Q,d2Transfer547S1,d2Transfer547Lo,d2Transfer547Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer547C1 d2Transfer547S1 d2Log21Q d2Log21Lo d2Log21Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log21Bounds
  have har : (((weightedUpper d2Transfer547C0 d2Log152Lo d2Log152Hi:ℚ):ℝ) + ((weightedUpper d2Transfer547C1 d2Log21Lo d2Log21Hi:ℚ):ℝ)) ≤ ((d2Transfer547Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer547Arithmetic
  linarith
#print axioms d2Transfer547Arithmetic
#print axioms d2Transfer547Bound
def d2Transfer548Lo : ℚ := (d2LitsNearTransfers068.q2 (1361300837) 1 (-31))
def d2Transfer548Hi : ℚ := (d2LitsNearTransfers068.q2 (681489279) 1 (-30))
def d2Transfer548Cap : ℚ := (d2LitsNearTransfers068.q2 (8968207994758479100997) 1 (-79))
def d2Transfer548C0 : ℚ := (d2LitsNearTransfers068.q2 (23) 25 (-5))
def d2Transfer548S0 : ℚ := (d2LitsNearTransfers068.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer548Arithmetic : weightedUpper d2Transfer548C0 d2Log153Lo d2Log153Hi ≤ d2Transfer548Cap := by decide +kernel
theorem d2Transfer548Bound : ∀ x ∈ Set.Icc ((d2Transfer548Lo:ℚ):ℝ) ((d2Transfer548Hi:ℚ):ℝ), ((d2Transfer548C0:ℚ):ℝ)*Real.log |x-((d2Transfer548S0:ℚ):ℝ)| ≤ ((d2Transfer548Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer548S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer548S0,d2Transfer548Lo,d2Transfer548Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer548C0 then |x-((d2Transfer548S0:ℚ):ℝ)| ≤ ((d2Log153Q:ℚ):ℝ) else ((d2Log153Q:ℚ):ℝ) ≤ |x-((d2Transfer548S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer548S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer548S0,d2Transfer548Lo,d2Transfer548Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer548C0,d2Log153Q,d2Transfer548S0,d2Transfer548Lo,d2Transfer548Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer548C0 d2Transfer548S0 d2Log153Q d2Log153Lo d2Log153Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log153Bounds
  have har : (((weightedUpper d2Transfer548C0 d2Log153Lo d2Log153Hi:ℚ):ℝ)) ≤ ((d2Transfer548Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer548Arithmetic
  linarith
#print axioms d2Transfer548Arithmetic
#print axioms d2Transfer548Bound
def d2Transfer549Lo : ℚ := (d2LitsNearTransfers068.q2 (1361300837) 1 (-31))
def d2Transfer549Hi : ℚ := (d2LitsNearTransfers068.q2 (681489279) 1 (-30))
def d2Transfer549Cap : ℚ := (d2LitsNearTransfers068.q2 (17393701690392114248773) 1 (-79))
def d2Transfer549C0 : ℚ := (d2LitsNearTransfers068.q2 (3) 275 (-5))
def d2Transfer549S0 : ℚ := (d2LitsNearTransfers068.q2 (-1) 1 (0))
def d2Transfer549C1 : ℚ := (d2LitsNearTransfers068.q2 (-5) 11 (-4))
def d2Transfer549S1 : ℚ := (d2LitsNearTransfers068.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer549Arithmetic : weightedUpper d2Transfer549C0 d2Log153Lo d2Log153Hi + weightedUpper d2Transfer549C1 d2Log21Lo d2Log21Hi ≤ d2Transfer549Cap := by decide +kernel
theorem d2Transfer549Bound : ∀ x ∈ Set.Icc ((d2Transfer549Lo:ℚ):ℝ) ((d2Transfer549Hi:ℚ):ℝ), ((d2Transfer549C0:ℚ):ℝ)*Real.log |x-((d2Transfer549S0:ℚ):ℝ)| + ((d2Transfer549C1:ℚ):ℝ)*Real.log |x-((d2Transfer549S1:ℚ):ℝ)| ≤ ((d2Transfer549Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer549S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer549S0,d2Transfer549Lo,d2Transfer549Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer549C0 then |x-((d2Transfer549S0:ℚ):ℝ)| ≤ ((d2Log153Q:ℚ):ℝ) else ((d2Log153Q:ℚ):ℝ) ≤ |x-((d2Transfer549S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer549S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer549S0,d2Transfer549Lo,d2Transfer549Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer549C0,d2Log153Q,d2Transfer549S0,d2Transfer549Lo,d2Transfer549Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer549C0 d2Transfer549S0 d2Log153Q d2Log153Lo d2Log153Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log153Bounds
  have hn1 : x-((d2Transfer549S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer549S1,d2Transfer549Lo,d2Transfer549Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer549C1 then |x-((d2Transfer549S1:ℚ):ℝ)| ≤ ((d2Log21Q:ℚ):ℝ) else ((d2Log21Q:ℚ):ℝ) ≤ |x-((d2Transfer549S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer549S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer549S1,d2Transfer549Lo,d2Transfer549Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer549C1,d2Log21Q,d2Transfer549S1,d2Transfer549Lo,d2Transfer549Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer549C1 d2Transfer549S1 d2Log21Q d2Log21Lo d2Log21Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log21Bounds
  have har : (((weightedUpper d2Transfer549C0 d2Log153Lo d2Log153Hi:ℚ):ℝ) + ((weightedUpper d2Transfer549C1 d2Log21Lo d2Log21Hi:ℚ):ℝ)) ≤ ((d2Transfer549Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer549Arithmetic
  linarith
#print axioms d2Transfer549Arithmetic
#print axioms d2Transfer549Bound
def d2Transfer550Lo : ℚ := (d2LitsNearTransfers068.q2 (681489279) 1 (-30))
def d2Transfer550Hi : ℚ := (d2LitsNearTransfers068.q2 (1364656279) 1 (-31))
def d2Transfer550Cap : ℚ := (d2LitsNearTransfers068.q2 (2678343852355371081821) 1 (-80))
def d2Transfer550C0 : ℚ := (d2LitsNearTransfers068.q2 (-1) 55 (-3))
def d2Transfer550S0 : ℚ := (d2LitsNearTransfers068.q2 (-1) 1 (0))
def d2Transfer550C1 : ℚ := (d2LitsNearTransfers068.q2 (-1) 55 (-3))
def d2Transfer550S1 : ℚ := (d2LitsNearTransfers068.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer550Arithmetic : weightedUpper d2Transfer550C0 d2Log153Lo d2Log153Hi + weightedUpper d2Transfer550C1 d2Log20Lo d2Log20Hi ≤ d2Transfer550Cap := by decide +kernel
theorem d2Transfer550Bound : ∀ x ∈ Set.Icc ((d2Transfer550Lo:ℚ):ℝ) ((d2Transfer550Hi:ℚ):ℝ), ((d2Transfer550C0:ℚ):ℝ)*Real.log |x-((d2Transfer550S0:ℚ):ℝ)| + ((d2Transfer550C1:ℚ):ℝ)*Real.log |x-((d2Transfer550S1:ℚ):ℝ)| ≤ ((d2Transfer550Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer550S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer550S0,d2Transfer550Lo,d2Transfer550Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer550C0 then |x-((d2Transfer550S0:ℚ):ℝ)| ≤ ((d2Log153Q:ℚ):ℝ) else ((d2Log153Q:ℚ):ℝ) ≤ |x-((d2Transfer550S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer550S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer550S0,d2Transfer550Lo,d2Transfer550Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer550C0,d2Log153Q,d2Transfer550S0,d2Transfer550Lo,d2Transfer550Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer550C0 d2Transfer550S0 d2Log153Q d2Log153Lo d2Log153Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log153Bounds
  have hn1 : x-((d2Transfer550S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer550S1,d2Transfer550Lo,d2Transfer550Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer550C1 then |x-((d2Transfer550S1:ℚ):ℝ)| ≤ ((d2Log20Q:ℚ):ℝ) else ((d2Log20Q:ℚ):ℝ) ≤ |x-((d2Transfer550S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer550S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer550S1,d2Transfer550Lo,d2Transfer550Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer550C1,d2Log20Q,d2Transfer550S1,d2Transfer550Lo,d2Transfer550Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer550C1 d2Transfer550S1 d2Log20Q d2Log20Lo d2Log20Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log20Bounds
  have har : (((weightedUpper d2Transfer550C0 d2Log153Lo d2Log153Hi:ℚ):ℝ) + ((weightedUpper d2Transfer550C1 d2Log20Lo d2Log20Hi:ℚ):ℝ)) ≤ ((d2Transfer550Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer550Arithmetic
  linarith
#print axioms d2Transfer550Arithmetic
#print axioms d2Transfer550Bound
def d2Transfer551Lo : ℚ := (d2LitsNearTransfers068.q2 (681489279) 1 (-30))
def d2Transfer551Hi : ℚ := (d2LitsNearTransfers068.q2 (1364656279) 1 (-31))
def d2Transfer551Cap : ℚ := (d2LitsNearTransfers068.q2 (18010139726281658015837) 1 (-80))
def d2Transfer551C0 : ℚ := (d2LitsNearTransfers068.q2 (23) 25 (-5))
def d2Transfer551S0 : ℚ := (d2LitsNearTransfers068.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer551Arithmetic : weightedUpper d2Transfer551C0 d2Log154Lo d2Log154Hi ≤ d2Transfer551Cap := by decide +kernel
theorem d2Transfer551Bound : ∀ x ∈ Set.Icc ((d2Transfer551Lo:ℚ):ℝ) ((d2Transfer551Hi:ℚ):ℝ), ((d2Transfer551C0:ℚ):ℝ)*Real.log |x-((d2Transfer551S0:ℚ):ℝ)| ≤ ((d2Transfer551Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer551S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer551S0,d2Transfer551Lo,d2Transfer551Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer551C0 then |x-((d2Transfer551S0:ℚ):ℝ)| ≤ ((d2Log154Q:ℚ):ℝ) else ((d2Log154Q:ℚ):ℝ) ≤ |x-((d2Transfer551S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer551S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer551S0,d2Transfer551Lo,d2Transfer551Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers068.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer551C0,d2Log154Q,d2Transfer551S0,d2Transfer551Lo,d2Transfer551Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer551C0 d2Transfer551S0 d2Log154Q d2Log154Lo d2Log154Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log154Bounds
  have har : (((weightedUpper d2Transfer551C0 d2Log154Lo d2Log154Hi:ℚ):ℝ)) ≤ ((d2Transfer551Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer551Arithmetic
  linarith
#print axioms d2Transfer551Arithmetic
#print axioms d2Transfer551Bound
end CatalanMeasure.GenD.Signed.Data.Cells

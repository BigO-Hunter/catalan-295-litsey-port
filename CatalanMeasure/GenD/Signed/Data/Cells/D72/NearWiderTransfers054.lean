module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache011
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers054
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers054
open D72.LogTransfer
def d2WiderTransfer432Lo : ℚ := (d2LitsNearWiderTransfers054.q2 (16760439) 1 (-24))
def d2WiderTransfer432Hi : ℚ := (d2LitsNearWiderTransfers054.q2 (1023) 1 (-10))
def d2WiderTransfer432Cap : ℚ := (d2LitsNearWiderTransfers054.q2 (1046920113723876731577) 1 (-79))
def d2WiderTransfer432C0 : ℚ := (d2LitsNearWiderTransfers054.q2 (1) 25 (-4))
def d2WiderTransfer432S0 : ℚ := (d2LitsNearWiderTransfers054.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer432Arithmetic : weightedUpper d2WiderTransfer432C0 d2Log176Lo d2Log176Hi ≤ d2WiderTransfer432Cap := by decide +kernel
theorem d2WiderTransfer432Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer432Lo:ℚ):ℝ) ((d2WiderTransfer432Hi:ℚ):ℝ), ((d2WiderTransfer432C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer432S0:ℚ):ℝ)| ≤ ((d2WiderTransfer432Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer432S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer432S0,d2WiderTransfer432Lo,d2WiderTransfer432Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer432C0 then |x-((d2WiderTransfer432S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer432S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer432S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer432S0,d2WiderTransfer432Lo,d2WiderTransfer432Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer432C0,d2Log176Q,d2WiderTransfer432S0,d2WiderTransfer432Lo,d2WiderTransfer432Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer432C0 d2WiderTransfer432S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2WiderTransfer432C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer432Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer432Arithmetic
  linarith
#print axioms d2WiderTransfer432Arithmetic
#print axioms d2WiderTransfer432Bound
def d2WiderTransfer433Lo : ℚ := (d2LitsNearWiderTransfers054.q2 (16760439) 1 (-24))
def d2WiderTransfer433Hi : ℚ := (d2LitsNearWiderTransfers054.q2 (1023) 1 (-10))
def d2WiderTransfer433Cap : ℚ := (d2LitsNearWiderTransfers054.q2 (13083954428117574642361) 1 (-79))
def d2WiderTransfer433C0 : ℚ := (d2LitsNearWiderTransfers054.q2 (1) 1 (-5))
def d2WiderTransfer433S0 : ℚ := (d2LitsNearWiderTransfers054.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer433Arithmetic : weightedUpper d2WiderTransfer433C0 d2Log176Lo d2Log176Hi ≤ d2WiderTransfer433Cap := by decide +kernel
theorem d2WiderTransfer433Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer433Lo:ℚ):ℝ) ((d2WiderTransfer433Hi:ℚ):ℝ), ((d2WiderTransfer433C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer433S0:ℚ):ℝ)| ≤ ((d2WiderTransfer433Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer433S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer433S0,d2WiderTransfer433Lo,d2WiderTransfer433Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer433C0 then |x-((d2WiderTransfer433S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer433S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer433S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer433S0,d2WiderTransfer433Lo,d2WiderTransfer433Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer433C0,d2Log176Q,d2WiderTransfer433S0,d2WiderTransfer433Lo,d2WiderTransfer433Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer433C0 d2WiderTransfer433S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2WiderTransfer433C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer433Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer433Arithmetic
  linarith
#print axioms d2WiderTransfer433Arithmetic
#print axioms d2WiderTransfer433Bound
def d2WiderTransfer434Lo : ℚ := (d2LitsNearWiderTransfers054.q2 (16760439) 1 (-24))
def d2WiderTransfer434Hi : ℚ := (d2LitsNearWiderTransfers054.q2 (1023) 1 (-10))
def d2WiderTransfer434Cap : ℚ := (d2LitsNearWiderTransfers054.q2 (13083954626029667642041) 1 (-79))
def d2WiderTransfer434C0 : ℚ := (d2LitsNearWiderTransfers054.q2 (1) 1 (-5))
def d2WiderTransfer434S0 : ℚ := (d2LitsNearWiderTransfers054.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer434Arithmetic : weightedUpper d2WiderTransfer434C0 d2Log176Lo d2Log176Hi ≤ d2WiderTransfer434Cap := by decide +kernel
theorem d2WiderTransfer434Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer434Lo:ℚ):ℝ) ((d2WiderTransfer434Hi:ℚ):ℝ), ((d2WiderTransfer434C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer434S0:ℚ):ℝ)| ≤ ((d2WiderTransfer434Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer434S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer434S0,d2WiderTransfer434Lo,d2WiderTransfer434Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer434C0 then |x-((d2WiderTransfer434S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer434S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer434S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer434S0,d2WiderTransfer434Lo,d2WiderTransfer434Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer434C0,d2Log176Q,d2WiderTransfer434S0,d2WiderTransfer434Lo,d2WiderTransfer434Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer434C0 d2WiderTransfer434S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2WiderTransfer434C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer434Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer434Arithmetic
  linarith
#print axioms d2WiderTransfer434Arithmetic
#print axioms d2WiderTransfer434Bound
def d2WiderTransfer435Lo : ℚ := (d2LitsNearWiderTransfers054.q2 (1023) 1 (-10))
def d2WiderTransfer435Hi : ℚ := (d2LitsNearWiderTransfers054.q2 (2047) 1 (-11))
def d2WiderTransfer435Cap : ℚ := (d2LitsNearWiderTransfers054.q2 (1051533698690763017477) 1 (-79))
def d2WiderTransfer435C0 : ℚ := (d2LitsNearWiderTransfers054.q2 (1) 25 (-4))
def d2WiderTransfer435S0 : ℚ := (d2LitsNearWiderTransfers054.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer435Arithmetic : weightedUpper d2WiderTransfer435C0 d2Log177Lo d2Log177Hi ≤ d2WiderTransfer435Cap := by decide +kernel
theorem d2WiderTransfer435Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer435Lo:ℚ):ℝ) ((d2WiderTransfer435Hi:ℚ):ℝ), ((d2WiderTransfer435C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer435S0:ℚ):ℝ)| ≤ ((d2WiderTransfer435Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer435S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer435S0,d2WiderTransfer435Lo,d2WiderTransfer435Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer435C0 then |x-((d2WiderTransfer435S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer435S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer435S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer435S0,d2WiderTransfer435Lo,d2WiderTransfer435Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer435C0,d2Log177Q,d2WiderTransfer435S0,d2WiderTransfer435Lo,d2WiderTransfer435Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer435C0 d2WiderTransfer435S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2WiderTransfer435C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer435Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer435Arithmetic
  linarith
#print axioms d2WiderTransfer435Arithmetic
#print axioms d2WiderTransfer435Bound
def d2WiderTransfer436Lo : ℚ := (d2LitsNearWiderTransfers054.q2 (1023) 1 (-10))
def d2WiderTransfer436Hi : ℚ := (d2LitsNearWiderTransfers054.q2 (2047) 1 (-11))
def d2WiderTransfer436Cap : ℚ := (d2LitsNearWiderTransfers054.q2 (1051533489233797926149) 1 (-79))
def d2WiderTransfer436C0 : ℚ := (d2LitsNearWiderTransfers054.q2 (1) 25 (-4))
def d2WiderTransfer436S0 : ℚ := (d2LitsNearWiderTransfers054.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer436Arithmetic : weightedUpper d2WiderTransfer436C0 d2Log177Lo d2Log177Hi ≤ d2WiderTransfer436Cap := by decide +kernel
theorem d2WiderTransfer436Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer436Lo:ℚ):ℝ) ((d2WiderTransfer436Hi:ℚ):ℝ), ((d2WiderTransfer436C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer436S0:ℚ):ℝ)| ≤ ((d2WiderTransfer436Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer436S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer436S0,d2WiderTransfer436Lo,d2WiderTransfer436Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer436C0 then |x-((d2WiderTransfer436S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer436S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer436S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer436S0,d2WiderTransfer436Lo,d2WiderTransfer436Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer436C0,d2Log177Q,d2WiderTransfer436S0,d2WiderTransfer436Lo,d2WiderTransfer436Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer436C0 d2WiderTransfer436S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2WiderTransfer436C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer436Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer436Arithmetic
  linarith
#print axioms d2WiderTransfer436Arithmetic
#print axioms d2WiderTransfer436Bound
def d2WiderTransfer437Lo : ℚ := (d2LitsNearWiderTransfers054.q2 (1023) 1 (-10))
def d2WiderTransfer437Hi : ℚ := (d2LitsNearWiderTransfers054.q2 (2047) 1 (-11))
def d2WiderTransfer437Cap : ℚ := (d2LitsNearWiderTransfers054.q2 (13088567803627495836933) 1 (-79))
def d2WiderTransfer437C0 : ℚ := (d2LitsNearWiderTransfers054.q2 (1) 1 (-5))
def d2WiderTransfer437S0 : ℚ := (d2LitsNearWiderTransfers054.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer437Arithmetic : weightedUpper d2WiderTransfer437C0 d2Log177Lo d2Log177Hi ≤ d2WiderTransfer437Cap := by decide +kernel
theorem d2WiderTransfer437Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer437Lo:ℚ):ℝ) ((d2WiderTransfer437Hi:ℚ):ℝ), ((d2WiderTransfer437C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer437S0:ℚ):ℝ)| ≤ ((d2WiderTransfer437Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer437S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer437S0,d2WiderTransfer437Lo,d2WiderTransfer437Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer437C0 then |x-((d2WiderTransfer437S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer437S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer437S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer437S0,d2WiderTransfer437Lo,d2WiderTransfer437Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer437C0,d2Log177Q,d2WiderTransfer437S0,d2WiderTransfer437Lo,d2WiderTransfer437Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer437C0 d2WiderTransfer437S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2WiderTransfer437C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer437Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer437Arithmetic
  linarith
#print axioms d2WiderTransfer437Arithmetic
#print axioms d2WiderTransfer437Bound
def d2WiderTransfer438Lo : ℚ := (d2LitsNearWiderTransfers054.q2 (1023) 1 (-10))
def d2WiderTransfer438Hi : ℚ := (d2LitsNearWiderTransfers054.q2 (2047) 1 (-11))
def d2WiderTransfer438Cap : ℚ := (d2LitsNearWiderTransfers054.q2 (13088568001539588836613) 1 (-79))
def d2WiderTransfer438C0 : ℚ := (d2LitsNearWiderTransfers054.q2 (1) 1 (-5))
def d2WiderTransfer438S0 : ℚ := (d2LitsNearWiderTransfers054.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer438Arithmetic : weightedUpper d2WiderTransfer438C0 d2Log177Lo d2Log177Hi ≤ d2WiderTransfer438Cap := by decide +kernel
theorem d2WiderTransfer438Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer438Lo:ℚ):ℝ) ((d2WiderTransfer438Hi:ℚ):ℝ), ((d2WiderTransfer438C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer438S0:ℚ):ℝ)| ≤ ((d2WiderTransfer438Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer438S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer438S0,d2WiderTransfer438Lo,d2WiderTransfer438Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer438C0 then |x-((d2WiderTransfer438S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer438S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer438S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer438S0,d2WiderTransfer438Lo,d2WiderTransfer438Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer438C0,d2Log177Q,d2WiderTransfer438S0,d2WiderTransfer438Lo,d2WiderTransfer438Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer438C0 d2WiderTransfer438S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2WiderTransfer438C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer438Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer438Arithmetic
  linarith
#print axioms d2WiderTransfer438Arithmetic
#print axioms d2WiderTransfer438Bound
def d2WiderTransfer439Lo : ℚ := (d2LitsNearWiderTransfers054.q2 (2047) 1 (-11))
def d2WiderTransfer439Hi : ℚ := (d2LitsNearWiderTransfers054.q2 (4095) 1 (-12))
def d2WiderTransfer439Cap : ℚ := (d2LitsNearWiderTransfers054.q2 (2107679927985260464173) 1 (-80))
def d2WiderTransfer439C0 : ℚ := (d2LitsNearWiderTransfers054.q2 (1) 25 (-4))
def d2WiderTransfer439S0 : ℚ := (d2LitsNearWiderTransfers054.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer439Arithmetic : weightedUpper d2WiderTransfer439C0 d2Log178Lo d2Log178Hi ≤ d2WiderTransfer439Cap := by decide +kernel
theorem d2WiderTransfer439Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer439Lo:ℚ):ℝ) ((d2WiderTransfer439Hi:ℚ):ℝ), ((d2WiderTransfer439C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer439S0:ℚ):ℝ)| ≤ ((d2WiderTransfer439Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer439S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer439S0,d2WiderTransfer439Lo,d2WiderTransfer439Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer439C0 then |x-((d2WiderTransfer439S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer439S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer439S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer439S0,d2WiderTransfer439Lo,d2WiderTransfer439Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers054.q2, d2LitsNearLogCache011.q2, d2WiderTransfer439C0,d2Log178Q,d2WiderTransfer439S0,d2WiderTransfer439Lo,d2WiderTransfer439Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer439C0 d2WiderTransfer439S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2WiderTransfer439C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer439Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer439Arithmetic
  linarith
#print axioms d2WiderTransfer439Arithmetic
#print axioms d2WiderTransfer439Bound
end CatalanMeasure.GenD.Signed.Data.Cells

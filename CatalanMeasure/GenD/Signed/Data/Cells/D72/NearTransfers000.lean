module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache005
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers000
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers000
open D72.LogTransfer
def d2Transfer0Lo : ℚ := (d2LitsNearTransfers000.q2 (98749) 15625 (-6))
def d2Transfer0Hi : ℚ := (d2LitsNearTransfers000.q2 (828367) 1 (-23))
def d2Transfer0Cap : ℚ := (d2LitsNearTransfers000.q2 (648894057) 1 (-39))
def d2Transfer0C0 : ℚ := (d2LitsNearTransfers000.q2 (1) 25 (-4))
def d2Transfer0S0 : ℚ := (d2LitsNearTransfers000.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer0Arithmetic : weightedUpper d2Transfer0C0 d2Log88Lo d2Log88Hi ≤ d2Transfer0Cap := by decide +kernel
theorem d2Transfer0Bound : ∀ x ∈ Set.Icc ((d2Transfer0Lo:ℚ):ℝ) ((d2Transfer0Hi:ℚ):ℝ), ((d2Transfer0C0:ℚ):ℝ)*Real.log |x-((d2Transfer0S0:ℚ):ℝ)| ≤ ((d2Transfer0Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer0S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer0S0,d2Transfer0Lo,d2Transfer0Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer0C0 then |x-((d2Transfer0S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2Transfer0S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer0S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer0S0,d2Transfer0Lo,d2Transfer0Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer0C0,d2Log88Q,d2Transfer0S0,d2Transfer0Lo,d2Transfer0Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer0C0 d2Transfer0S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have har : (((weightedUpper d2Transfer0C0 d2Log88Lo d2Log88Hi:ℚ):ℝ)) ≤ ((d2Transfer0Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer0Arithmetic
  linarith
#print axioms d2Transfer0Arithmetic
#print axioms d2Transfer0Bound
def d2Transfer1Lo : ℚ := (d2LitsNearTransfers000.q2 (98749) 15625 (-6))
def d2Transfer1Hi : ℚ := (d2LitsNearTransfers000.q2 (828367) 1 (-23))
def d2Transfer1Cap : ℚ := (d2LitsNearTransfers000.q2 (2432512853) 1 (-40))
def d2Transfer1C0 : ℚ := (d2LitsNearTransfers000.q2 (1) 275 (-4))
def d2Transfer1S0 : ℚ := (d2LitsNearTransfers000.q2 (-1) 1 (0))
def d2Transfer1C1 : ℚ := (d2LitsNearTransfers000.q2 (-1) 55 (-3))
def d2Transfer1S1 : ℚ := (d2LitsNearTransfers000.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer1Arithmetic : weightedUpper d2Transfer1C0 d2Log88Lo d2Log88Hi + weightedUpper d2Transfer1C1 d2Log86Lo d2Log86Hi ≤ d2Transfer1Cap := by decide +kernel
theorem d2Transfer1Bound : ∀ x ∈ Set.Icc ((d2Transfer1Lo:ℚ):ℝ) ((d2Transfer1Hi:ℚ):ℝ), ((d2Transfer1C0:ℚ):ℝ)*Real.log |x-((d2Transfer1S0:ℚ):ℝ)| + ((d2Transfer1C1:ℚ):ℝ)*Real.log |x-((d2Transfer1S1:ℚ):ℝ)| ≤ ((d2Transfer1Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer1S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer1S0,d2Transfer1Lo,d2Transfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer1C0 then |x-((d2Transfer1S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2Transfer1S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer1S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer1S0,d2Transfer1Lo,d2Transfer1Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer1C0,d2Log88Q,d2Transfer1S0,d2Transfer1Lo,d2Transfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer1C0 d2Transfer1S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have hn1 : x-((d2Transfer1S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer1S1,d2Transfer1Lo,d2Transfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer1C1 then |x-((d2Transfer1S1:ℚ):ℝ)| ≤ ((d2Log86Q:ℚ):ℝ) else ((d2Log86Q:ℚ):ℝ) ≤ |x-((d2Transfer1S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer1S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer1S1,d2Transfer1Lo,d2Transfer1Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer1C1,d2Log86Q,d2Transfer1S1,d2Transfer1Lo,d2Transfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer1C1 d2Transfer1S1 d2Log86Q d2Log86Lo d2Log86Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log86Bounds
  have har : (((weightedUpper d2Transfer1C0 d2Log88Lo d2Log88Hi:ℚ):ℝ) + ((weightedUpper d2Transfer1C1 d2Log86Lo d2Log86Hi:ℚ):ℝ)) ≤ ((d2Transfer1Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer1Arithmetic
  linarith
#print axioms d2Transfer1Arithmetic
#print axioms d2Transfer1Bound
def d2Transfer2Lo : ℚ := (d2LitsNearTransfers000.q2 (828367) 1 (-23))
def d2Transfer2Hi : ℚ := (d2LitsNearTransfers000.q2 (54693209) 1 (-29))
def d2Transfer2Cap : ℚ := (d2LitsNearTransfers000.q2 (648894057) 1 (-39))
def d2Transfer2C0 : ℚ := (d2LitsNearTransfers000.q2 (1) 25 (-4))
def d2Transfer2S0 : ℚ := (d2LitsNearTransfers000.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer2Arithmetic : weightedUpper d2Transfer2C0 d2Log89Lo d2Log89Hi ≤ d2Transfer2Cap := by decide +kernel
theorem d2Transfer2Bound : ∀ x ∈ Set.Icc ((d2Transfer2Lo:ℚ):ℝ) ((d2Transfer2Hi:ℚ):ℝ), ((d2Transfer2C0:ℚ):ℝ)*Real.log |x-((d2Transfer2S0:ℚ):ℝ)| ≤ ((d2Transfer2Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer2S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer2S0,d2Transfer2Lo,d2Transfer2Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer2C0 then |x-((d2Transfer2S0:ℚ):ℝ)| ≤ ((d2Log89Q:ℚ):ℝ) else ((d2Log89Q:ℚ):ℝ) ≤ |x-((d2Transfer2S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer2S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer2S0,d2Transfer2Lo,d2Transfer2Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer2C0,d2Log89Q,d2Transfer2S0,d2Transfer2Lo,d2Transfer2Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer2C0 d2Transfer2S0 d2Log89Q d2Log89Lo d2Log89Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log89Bounds
  have har : (((weightedUpper d2Transfer2C0 d2Log89Lo d2Log89Hi:ℚ):ℝ)) ≤ ((d2Transfer2Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer2Arithmetic
  linarith
#print axioms d2Transfer2Arithmetic
#print axioms d2Transfer2Bound
def d2Transfer3Lo : ℚ := (d2LitsNearTransfers000.q2 (828367) 1 (-23))
def d2Transfer3Hi : ℚ := (d2LitsNearTransfers000.q2 (54693209) 1 (-29))
def d2Transfer3Cap : ℚ := (d2LitsNearTransfers000.q2 (2432512853) 1 (-40))
def d2Transfer3C0 : ℚ := (d2LitsNearTransfers000.q2 (1) 275 (-4))
def d2Transfer3S0 : ℚ := (d2LitsNearTransfers000.q2 (-1) 1 (0))
def d2Transfer3C1 : ℚ := (d2LitsNearTransfers000.q2 (-1) 55 (-3))
def d2Transfer3S1 : ℚ := (d2LitsNearTransfers000.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer3Arithmetic : weightedUpper d2Transfer3C0 d2Log89Lo d2Log89Hi + weightedUpper d2Transfer3C1 d2Log85Lo d2Log85Hi ≤ d2Transfer3Cap := by decide +kernel
theorem d2Transfer3Bound : ∀ x ∈ Set.Icc ((d2Transfer3Lo:ℚ):ℝ) ((d2Transfer3Hi:ℚ):ℝ), ((d2Transfer3C0:ℚ):ℝ)*Real.log |x-((d2Transfer3S0:ℚ):ℝ)| + ((d2Transfer3C1:ℚ):ℝ)*Real.log |x-((d2Transfer3S1:ℚ):ℝ)| ≤ ((d2Transfer3Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer3S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer3S0,d2Transfer3Lo,d2Transfer3Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer3C0 then |x-((d2Transfer3S0:ℚ):ℝ)| ≤ ((d2Log89Q:ℚ):ℝ) else ((d2Log89Q:ℚ):ℝ) ≤ |x-((d2Transfer3S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer3S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer3S0,d2Transfer3Lo,d2Transfer3Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer3C0,d2Log89Q,d2Transfer3S0,d2Transfer3Lo,d2Transfer3Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer3C0 d2Transfer3S0 d2Log89Q d2Log89Lo d2Log89Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log89Bounds
  have hn1 : x-((d2Transfer3S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer3S1,d2Transfer3Lo,d2Transfer3Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer3C1 then |x-((d2Transfer3S1:ℚ):ℝ)| ≤ ((d2Log85Q:ℚ):ℝ) else ((d2Log85Q:ℚ):ℝ) ≤ |x-((d2Transfer3S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer3S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer3S1,d2Transfer3Lo,d2Transfer3Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer3C1,d2Log85Q,d2Transfer3S1,d2Transfer3Lo,d2Transfer3Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer3C1 d2Transfer3S1 d2Log85Q d2Log85Lo d2Log85Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log85Bounds
  have har : (((weightedUpper d2Transfer3C0 d2Log89Lo d2Log89Hi:ℚ):ℝ) + ((weightedUpper d2Transfer3C1 d2Log85Lo d2Log85Hi:ℚ):ℝ)) ≤ ((d2Transfer3Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer3Arithmetic
  linarith
#print axioms d2Transfer3Arithmetic
#print axioms d2Transfer3Bound
def d2Transfer4Lo : ℚ := (d2LitsNearTransfers000.q2 (54693209) 1 (-29))
def d2Transfer4Hi : ℚ := (d2LitsNearTransfers000.q2 (28185465) 1 (-28))
def d2Transfer4Cap : ℚ := (d2LitsNearTransfers000.q2 (648894057) 1 (-39))
def d2Transfer4C0 : ℚ := (d2LitsNearTransfers000.q2 (1) 25 (-4))
def d2Transfer4S0 : ℚ := (d2LitsNearTransfers000.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer4Arithmetic : weightedUpper d2Transfer4C0 d2Log90Lo d2Log90Hi ≤ d2Transfer4Cap := by decide +kernel
theorem d2Transfer4Bound : ∀ x ∈ Set.Icc ((d2Transfer4Lo:ℚ):ℝ) ((d2Transfer4Hi:ℚ):ℝ), ((d2Transfer4C0:ℚ):ℝ)*Real.log |x-((d2Transfer4S0:ℚ):ℝ)| ≤ ((d2Transfer4Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer4S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer4S0,d2Transfer4Lo,d2Transfer4Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer4C0 then |x-((d2Transfer4S0:ℚ):ℝ)| ≤ ((d2Log90Q:ℚ):ℝ) else ((d2Log90Q:ℚ):ℝ) ≤ |x-((d2Transfer4S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer4S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer4S0,d2Transfer4Lo,d2Transfer4Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer4C0,d2Log90Q,d2Transfer4S0,d2Transfer4Lo,d2Transfer4Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer4C0 d2Transfer4S0 d2Log90Q d2Log90Lo d2Log90Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log90Bounds
  have har : (((weightedUpper d2Transfer4C0 d2Log90Lo d2Log90Hi:ℚ):ℝ)) ≤ ((d2Transfer4Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer4Arithmetic
  linarith
#print axioms d2Transfer4Arithmetic
#print axioms d2Transfer4Bound
def d2Transfer5Lo : ℚ := (d2LitsNearTransfers000.q2 (54693209) 1 (-29))
def d2Transfer5Hi : ℚ := (d2LitsNearTransfers000.q2 (28185465) 1 (-28))
def d2Transfer5Cap : ℚ := (d2LitsNearTransfers000.q2 (2432512853) 1 (-40))
def d2Transfer5C0 : ℚ := (d2LitsNearTransfers000.q2 (1) 275 (-4))
def d2Transfer5S0 : ℚ := (d2LitsNearTransfers000.q2 (-1) 1 (0))
def d2Transfer5C1 : ℚ := (d2LitsNearTransfers000.q2 (-1) 55 (-3))
def d2Transfer5S1 : ℚ := (d2LitsNearTransfers000.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer5Arithmetic : weightedUpper d2Transfer5C0 d2Log90Lo d2Log90Hi + weightedUpper d2Transfer5C1 d2Log84Lo d2Log84Hi ≤ d2Transfer5Cap := by decide +kernel
theorem d2Transfer5Bound : ∀ x ∈ Set.Icc ((d2Transfer5Lo:ℚ):ℝ) ((d2Transfer5Hi:ℚ):ℝ), ((d2Transfer5C0:ℚ):ℝ)*Real.log |x-((d2Transfer5S0:ℚ):ℝ)| + ((d2Transfer5C1:ℚ):ℝ)*Real.log |x-((d2Transfer5S1:ℚ):ℝ)| ≤ ((d2Transfer5Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer5S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer5S0,d2Transfer5Lo,d2Transfer5Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer5C0 then |x-((d2Transfer5S0:ℚ):ℝ)| ≤ ((d2Log90Q:ℚ):ℝ) else ((d2Log90Q:ℚ):ℝ) ≤ |x-((d2Transfer5S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer5S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer5S0,d2Transfer5Lo,d2Transfer5Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer5C0,d2Log90Q,d2Transfer5S0,d2Transfer5Lo,d2Transfer5Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer5C0 d2Transfer5S0 d2Log90Q d2Log90Lo d2Log90Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log90Bounds
  have hn1 : x-((d2Transfer5S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer5S1,d2Transfer5Lo,d2Transfer5Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer5C1 then |x-((d2Transfer5S1:ℚ):ℝ)| ≤ ((d2Log84Q:ℚ):ℝ) else ((d2Log84Q:ℚ):ℝ) ≤ |x-((d2Transfer5S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer5S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer5S1,d2Transfer5Lo,d2Transfer5Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer5C1,d2Log84Q,d2Transfer5S1,d2Transfer5Lo,d2Transfer5Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer5C1 d2Transfer5S1 d2Log84Q d2Log84Lo d2Log84Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log84Bounds
  have har : (((weightedUpper d2Transfer5C0 d2Log90Lo d2Log90Hi:ℚ):ℝ) + ((weightedUpper d2Transfer5C1 d2Log84Lo d2Log84Hi:ℚ):ℝ)) ≤ ((d2Transfer5Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer5Arithmetic
  linarith
#print axioms d2Transfer5Arithmetic
#print axioms d2Transfer5Bound
def d2Transfer6Lo : ℚ := (d2LitsNearTransfers000.q2 (28185465) 1 (-28))
def d2Transfer6Hi : ℚ := (d2LitsNearTransfers000.q2 (14931593) 1 (-27))
def d2Transfer6Cap : ℚ := (d2LitsNearTransfers000.q2 (648894057) 1 (-39))
def d2Transfer6C0 : ℚ := (d2LitsNearTransfers000.q2 (1) 25 (-4))
def d2Transfer6S0 : ℚ := (d2LitsNearTransfers000.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer6Arithmetic : weightedUpper d2Transfer6C0 d2Log92Lo d2Log92Hi ≤ d2Transfer6Cap := by decide +kernel
theorem d2Transfer6Bound : ∀ x ∈ Set.Icc ((d2Transfer6Lo:ℚ):ℝ) ((d2Transfer6Hi:ℚ):ℝ), ((d2Transfer6C0:ℚ):ℝ)*Real.log |x-((d2Transfer6S0:ℚ):ℝ)| ≤ ((d2Transfer6Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer6S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer6S0,d2Transfer6Lo,d2Transfer6Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer6C0 then |x-((d2Transfer6S0:ℚ):ℝ)| ≤ ((d2Log92Q:ℚ):ℝ) else ((d2Log92Q:ℚ):ℝ) ≤ |x-((d2Transfer6S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer6S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer6S0,d2Transfer6Lo,d2Transfer6Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer6C0,d2Log92Q,d2Transfer6S0,d2Transfer6Lo,d2Transfer6Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer6C0 d2Transfer6S0 d2Log92Q d2Log92Lo d2Log92Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log92Bounds
  have har : (((weightedUpper d2Transfer6C0 d2Log92Lo d2Log92Hi:ℚ):ℝ)) ≤ ((d2Transfer6Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer6Arithmetic
  linarith
#print axioms d2Transfer6Arithmetic
#print axioms d2Transfer6Bound
def d2Transfer7Lo : ℚ := (d2LitsNearTransfers000.q2 (28185465) 1 (-28))
def d2Transfer7Hi : ℚ := (d2LitsNearTransfers000.q2 (14931593) 1 (-27))
def d2Transfer7Cap : ℚ := (d2LitsNearTransfers000.q2 (2432512853) 1 (-40))
def d2Transfer7C0 : ℚ := (d2LitsNearTransfers000.q2 (1) 275 (-4))
def d2Transfer7S0 : ℚ := (d2LitsNearTransfers000.q2 (-1) 1 (0))
def d2Transfer7C1 : ℚ := (d2LitsNearTransfers000.q2 (-1) 55 (-3))
def d2Transfer7S1 : ℚ := (d2LitsNearTransfers000.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer7Arithmetic : weightedUpper d2Transfer7C0 d2Log92Lo d2Log92Hi + weightedUpper d2Transfer7C1 d2Log82Lo d2Log82Hi ≤ d2Transfer7Cap := by decide +kernel
theorem d2Transfer7Bound : ∀ x ∈ Set.Icc ((d2Transfer7Lo:ℚ):ℝ) ((d2Transfer7Hi:ℚ):ℝ), ((d2Transfer7C0:ℚ):ℝ)*Real.log |x-((d2Transfer7S0:ℚ):ℝ)| + ((d2Transfer7C1:ℚ):ℝ)*Real.log |x-((d2Transfer7S1:ℚ):ℝ)| ≤ ((d2Transfer7Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer7S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer7S0,d2Transfer7Lo,d2Transfer7Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer7C0 then |x-((d2Transfer7S0:ℚ):ℝ)| ≤ ((d2Log92Q:ℚ):ℝ) else ((d2Log92Q:ℚ):ℝ) ≤ |x-((d2Transfer7S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer7S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer7S0,d2Transfer7Lo,d2Transfer7Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer7C0,d2Log92Q,d2Transfer7S0,d2Transfer7Lo,d2Transfer7Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer7C0 d2Transfer7S0 d2Log92Q d2Log92Lo d2Log92Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log92Bounds
  have hn1 : x-((d2Transfer7S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer7S1,d2Transfer7Lo,d2Transfer7Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer7C1 then |x-((d2Transfer7S1:ℚ):ℝ)| ≤ ((d2Log82Q:ℚ):ℝ) else ((d2Log82Q:ℚ):ℝ) ≤ |x-((d2Transfer7S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer7S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer7S1,d2Transfer7Lo,d2Transfer7Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer7C1,d2Log82Q,d2Transfer7S1,d2Transfer7Lo,d2Transfer7Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer7C1 d2Transfer7S1 d2Log82Q d2Log82Lo d2Log82Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log82Bounds
  have har : (((weightedUpper d2Transfer7C0 d2Log92Lo d2Log92Hi:ℚ):ℝ) + ((weightedUpper d2Transfer7C1 d2Log82Lo d2Log82Hi:ℚ):ℝ)) ≤ ((d2Transfer7Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer7Arithmetic
  linarith
#print axioms d2Transfer7Arithmetic
#print axioms d2Transfer7Bound
end CatalanMeasure.GenD.Signed.Data.Cells

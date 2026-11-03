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
namespace d2LitsNearTransfers012
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers012
open D72.LogTransfer
def d2Transfer96Lo : ℚ := (d2LitsNearTransfers012.q2 (54693209) 1 (-29))
def d2Transfer96Hi : ℚ := (d2LitsNearTransfers012.q2 (28185465) 1 (-28))
def d2Transfer96Cap : ℚ := (d2LitsNearTransfers012.q2 (16281318465) 1 (-40))
def d2Transfer96C0 : ℚ := (d2LitsNearTransfers012.q2 (1) 1 (-5))
def d2Transfer96S0 : ℚ := (d2LitsNearTransfers012.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer96Arithmetic : weightedUpper d2Transfer96C0 d2Log90Lo d2Log90Hi ≤ d2Transfer96Cap := by decide +kernel
theorem d2Transfer96Bound : ∀ x ∈ Set.Icc ((d2Transfer96Lo:ℚ):ℝ) ((d2Transfer96Hi:ℚ):ℝ), ((d2Transfer96C0:ℚ):ℝ)*Real.log |x-((d2Transfer96S0:ℚ):ℝ)| ≤ ((d2Transfer96Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer96S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer96S0,d2Transfer96Lo,d2Transfer96Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer96C0 then |x-((d2Transfer96S0:ℚ):ℝ)| ≤ ((d2Log90Q:ℚ):ℝ) else ((d2Log90Q:ℚ):ℝ) ≤ |x-((d2Transfer96S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer96S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer96S0,d2Transfer96Lo,d2Transfer96Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer96C0,d2Log90Q,d2Transfer96S0,d2Transfer96Lo,d2Transfer96Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer96C0 d2Transfer96S0 d2Log90Q d2Log90Lo d2Log90Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log90Bounds
  have har : (((weightedUpper d2Transfer96C0 d2Log90Lo d2Log90Hi:ℚ):ℝ)) ≤ ((d2Transfer96Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer96Arithmetic
  linarith
#print axioms d2Transfer96Arithmetic
#print axioms d2Transfer96Bound
def d2Transfer97Lo : ℚ := (d2LitsNearTransfers012.q2 (54693209) 1 (-29))
def d2Transfer97Hi : ℚ := (d2LitsNearTransfers012.q2 (28185465) 1 (-28))
def d2Transfer97Cap : ℚ := (d2LitsNearTransfers012.q2 (31165051305) 1 (-40))
def d2Transfer97C0 : ℚ := (d2LitsNearTransfers012.q2 (1) 11 (-5))
def d2Transfer97S0 : ℚ := (d2LitsNearTransfers012.q2 (-1) 1 (0))
def d2Transfer97C1 : ℚ := (d2LitsNearTransfers012.q2 (-5) 11 (-4))
def d2Transfer97S1 : ℚ := (d2LitsNearTransfers012.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer97Arithmetic : weightedUpper d2Transfer97C0 d2Log90Lo d2Log90Hi + weightedUpper d2Transfer97C1 d2Log84Lo d2Log84Hi ≤ d2Transfer97Cap := by decide +kernel
theorem d2Transfer97Bound : ∀ x ∈ Set.Icc ((d2Transfer97Lo:ℚ):ℝ) ((d2Transfer97Hi:ℚ):ℝ), ((d2Transfer97C0:ℚ):ℝ)*Real.log |x-((d2Transfer97S0:ℚ):ℝ)| + ((d2Transfer97C1:ℚ):ℝ)*Real.log |x-((d2Transfer97S1:ℚ):ℝ)| ≤ ((d2Transfer97Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer97S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer97S0,d2Transfer97Lo,d2Transfer97Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer97C0 then |x-((d2Transfer97S0:ℚ):ℝ)| ≤ ((d2Log90Q:ℚ):ℝ) else ((d2Log90Q:ℚ):ℝ) ≤ |x-((d2Transfer97S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer97S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer97S0,d2Transfer97Lo,d2Transfer97Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer97C0,d2Log90Q,d2Transfer97S0,d2Transfer97Lo,d2Transfer97Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer97C0 d2Transfer97S0 d2Log90Q d2Log90Lo d2Log90Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log90Bounds
  have hn1 : x-((d2Transfer97S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer97S1,d2Transfer97Lo,d2Transfer97Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer97C1 then |x-((d2Transfer97S1:ℚ):ℝ)| ≤ ((d2Log84Q:ℚ):ℝ) else ((d2Log84Q:ℚ):ℝ) ≤ |x-((d2Transfer97S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer97S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer97S1,d2Transfer97Lo,d2Transfer97Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer97C1,d2Log84Q,d2Transfer97S1,d2Transfer97Lo,d2Transfer97Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer97C1 d2Transfer97S1 d2Log84Q d2Log84Lo d2Log84Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log84Bounds
  have har : (((weightedUpper d2Transfer97C0 d2Log90Lo d2Log90Hi:ℚ):ℝ) + ((weightedUpper d2Transfer97C1 d2Log84Lo d2Log84Hi:ℚ):ℝ)) ≤ ((d2Transfer97Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer97Arithmetic
  linarith
#print axioms d2Transfer97Arithmetic
#print axioms d2Transfer97Bound
def d2Transfer98Lo : ℚ := (d2LitsNearTransfers012.q2 (28185465) 1 (-28))
def d2Transfer98Hi : ℚ := (d2LitsNearTransfers012.q2 (58048651) 1 (-29))
def d2Transfer98Cap : ℚ := (d2LitsNearTransfers012.q2 (649441385) 1 (-39))
def d2Transfer98C0 : ℚ := (d2LitsNearTransfers012.q2 (1) 25 (-4))
def d2Transfer98S0 : ℚ := (d2LitsNearTransfers012.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer98Arithmetic : weightedUpper d2Transfer98C0 d2Log91Lo d2Log91Hi ≤ d2Transfer98Cap := by decide +kernel
theorem d2Transfer98Bound : ∀ x ∈ Set.Icc ((d2Transfer98Lo:ℚ):ℝ) ((d2Transfer98Hi:ℚ):ℝ), ((d2Transfer98C0:ℚ):ℝ)*Real.log |x-((d2Transfer98S0:ℚ):ℝ)| ≤ ((d2Transfer98Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer98S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer98S0,d2Transfer98Lo,d2Transfer98Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer98C0 then |x-((d2Transfer98S0:ℚ):ℝ)| ≤ ((d2Log91Q:ℚ):ℝ) else ((d2Log91Q:ℚ):ℝ) ≤ |x-((d2Transfer98S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer98S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer98S0,d2Transfer98Lo,d2Transfer98Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer98C0,d2Log91Q,d2Transfer98S0,d2Transfer98Lo,d2Transfer98Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer98C0 d2Transfer98S0 d2Log91Q d2Log91Lo d2Log91Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log91Bounds
  have har : (((weightedUpper d2Transfer98C0 d2Log91Lo d2Log91Hi:ℚ):ℝ)) ≤ ((d2Transfer98Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer98Arithmetic
  linarith
#print axioms d2Transfer98Arithmetic
#print axioms d2Transfer98Bound
def d2Transfer99Lo : ℚ := (d2LitsNearTransfers012.q2 (28185465) 1 (-28))
def d2Transfer99Hi : ℚ := (d2LitsNearTransfers012.q2 (58048651) 1 (-29))
def d2Transfer99Cap : ℚ := (d2LitsNearTransfers012.q2 (2436024149) 1 (-40))
def d2Transfer99C0 : ℚ := (d2LitsNearTransfers012.q2 (1) 275 (-4))
def d2Transfer99S0 : ℚ := (d2LitsNearTransfers012.q2 (-1) 1 (0))
def d2Transfer99C1 : ℚ := (d2LitsNearTransfers012.q2 (-1) 55 (-3))
def d2Transfer99S1 : ℚ := (d2LitsNearTransfers012.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer99Arithmetic : weightedUpper d2Transfer99C0 d2Log91Lo d2Log91Hi + weightedUpper d2Transfer99C1 d2Log83Lo d2Log83Hi ≤ d2Transfer99Cap := by decide +kernel
theorem d2Transfer99Bound : ∀ x ∈ Set.Icc ((d2Transfer99Lo:ℚ):ℝ) ((d2Transfer99Hi:ℚ):ℝ), ((d2Transfer99C0:ℚ):ℝ)*Real.log |x-((d2Transfer99S0:ℚ):ℝ)| + ((d2Transfer99C1:ℚ):ℝ)*Real.log |x-((d2Transfer99S1:ℚ):ℝ)| ≤ ((d2Transfer99Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer99S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer99S0,d2Transfer99Lo,d2Transfer99Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer99C0 then |x-((d2Transfer99S0:ℚ):ℝ)| ≤ ((d2Log91Q:ℚ):ℝ) else ((d2Log91Q:ℚ):ℝ) ≤ |x-((d2Transfer99S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer99S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer99S0,d2Transfer99Lo,d2Transfer99Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer99C0,d2Log91Q,d2Transfer99S0,d2Transfer99Lo,d2Transfer99Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer99C0 d2Transfer99S0 d2Log91Q d2Log91Lo d2Log91Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log91Bounds
  have hn1 : x-((d2Transfer99S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer99S1,d2Transfer99Lo,d2Transfer99Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer99C1 then |x-((d2Transfer99S1:ℚ):ℝ)| ≤ ((d2Log83Q:ℚ):ℝ) else ((d2Log83Q:ℚ):ℝ) ≤ |x-((d2Transfer99S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer99S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer99S1,d2Transfer99Lo,d2Transfer99Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer99C1,d2Log83Q,d2Transfer99S1,d2Transfer99Lo,d2Transfer99Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer99C1 d2Transfer99S1 d2Log83Q d2Log83Lo d2Log83Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log83Bounds
  have har : (((weightedUpper d2Transfer99C0 d2Log91Lo d2Log91Hi:ℚ):ℝ) + ((weightedUpper d2Transfer99C1 d2Log83Lo d2Log83Hi:ℚ):ℝ)) ≤ ((d2Transfer99Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer99Arithmetic
  linarith
#print axioms d2Transfer99Arithmetic
#print axioms d2Transfer99Bound
def d2Transfer100Lo : ℚ := (d2LitsNearTransfers012.q2 (28185465) 1 (-28))
def d2Transfer100Hi : ℚ := (d2LitsNearTransfers012.q2 (58048651) 1 (-29))
def d2Transfer100Cap : ℚ := (d2LitsNearTransfers012.q2 (16281318465) 1 (-40))
def d2Transfer100C0 : ℚ := (d2LitsNearTransfers012.q2 (1) 1 (-5))
def d2Transfer100S0 : ℚ := (d2LitsNearTransfers012.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer100Arithmetic : weightedUpper d2Transfer100C0 d2Log91Lo d2Log91Hi ≤ d2Transfer100Cap := by decide +kernel
theorem d2Transfer100Bound : ∀ x ∈ Set.Icc ((d2Transfer100Lo:ℚ):ℝ) ((d2Transfer100Hi:ℚ):ℝ), ((d2Transfer100C0:ℚ):ℝ)*Real.log |x-((d2Transfer100S0:ℚ):ℝ)| ≤ ((d2Transfer100Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer100S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer100S0,d2Transfer100Lo,d2Transfer100Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer100C0 then |x-((d2Transfer100S0:ℚ):ℝ)| ≤ ((d2Log91Q:ℚ):ℝ) else ((d2Log91Q:ℚ):ℝ) ≤ |x-((d2Transfer100S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer100S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer100S0,d2Transfer100Lo,d2Transfer100Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer100C0,d2Log91Q,d2Transfer100S0,d2Transfer100Lo,d2Transfer100Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer100C0 d2Transfer100S0 d2Log91Q d2Log91Lo d2Log91Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log91Bounds
  have har : (((weightedUpper d2Transfer100C0 d2Log91Lo d2Log91Hi:ℚ):ℝ)) ≤ ((d2Transfer100Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer100Arithmetic
  linarith
#print axioms d2Transfer100Arithmetic
#print axioms d2Transfer100Bound
def d2Transfer101Lo : ℚ := (d2LitsNearTransfers012.q2 (28185465) 1 (-28))
def d2Transfer101Hi : ℚ := (d2LitsNearTransfers012.q2 (58048651) 1 (-29))
def d2Transfer101Cap : ℚ := (d2LitsNearTransfers012.q2 (31165051305) 1 (-40))
def d2Transfer101C0 : ℚ := (d2LitsNearTransfers012.q2 (1) 11 (-5))
def d2Transfer101S0 : ℚ := (d2LitsNearTransfers012.q2 (-1) 1 (0))
def d2Transfer101C1 : ℚ := (d2LitsNearTransfers012.q2 (-5) 11 (-4))
def d2Transfer101S1 : ℚ := (d2LitsNearTransfers012.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer101Arithmetic : weightedUpper d2Transfer101C0 d2Log91Lo d2Log91Hi + weightedUpper d2Transfer101C1 d2Log83Lo d2Log83Hi ≤ d2Transfer101Cap := by decide +kernel
theorem d2Transfer101Bound : ∀ x ∈ Set.Icc ((d2Transfer101Lo:ℚ):ℝ) ((d2Transfer101Hi:ℚ):ℝ), ((d2Transfer101C0:ℚ):ℝ)*Real.log |x-((d2Transfer101S0:ℚ):ℝ)| + ((d2Transfer101C1:ℚ):ℝ)*Real.log |x-((d2Transfer101S1:ℚ):ℝ)| ≤ ((d2Transfer101Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer101S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer101S0,d2Transfer101Lo,d2Transfer101Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer101C0 then |x-((d2Transfer101S0:ℚ):ℝ)| ≤ ((d2Log91Q:ℚ):ℝ) else ((d2Log91Q:ℚ):ℝ) ≤ |x-((d2Transfer101S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer101S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer101S0,d2Transfer101Lo,d2Transfer101Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer101C0,d2Log91Q,d2Transfer101S0,d2Transfer101Lo,d2Transfer101Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer101C0 d2Transfer101S0 d2Log91Q d2Log91Lo d2Log91Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log91Bounds
  have hn1 : x-((d2Transfer101S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer101S1,d2Transfer101Lo,d2Transfer101Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer101C1 then |x-((d2Transfer101S1:ℚ):ℝ)| ≤ ((d2Log83Q:ℚ):ℝ) else ((d2Log83Q:ℚ):ℝ) ≤ |x-((d2Transfer101S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer101S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer101S1,d2Transfer101Lo,d2Transfer101Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer101C1,d2Log83Q,d2Transfer101S1,d2Transfer101Lo,d2Transfer101Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer101C1 d2Transfer101S1 d2Log83Q d2Log83Lo d2Log83Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log83Bounds
  have har : (((weightedUpper d2Transfer101C0 d2Log91Lo d2Log91Hi:ℚ):ℝ) + ((weightedUpper d2Transfer101C1 d2Log83Lo d2Log83Hi:ℚ):ℝ)) ≤ ((d2Transfer101Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer101Arithmetic
  linarith
#print axioms d2Transfer101Arithmetic
#print axioms d2Transfer101Bound
def d2Transfer102Lo : ℚ := (d2LitsNearTransfers012.q2 (58048651) 1 (-29))
def d2Transfer102Hi : ℚ := (d2LitsNearTransfers012.q2 (14931593) 1 (-27))
def d2Transfer102Cap : ℚ := (d2LitsNearTransfers012.q2 (649441385) 1 (-39))
def d2Transfer102C0 : ℚ := (d2LitsNearTransfers012.q2 (1) 25 (-4))
def d2Transfer102S0 : ℚ := (d2LitsNearTransfers012.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer102Arithmetic : weightedUpper d2Transfer102C0 d2Log92Lo d2Log92Hi ≤ d2Transfer102Cap := by decide +kernel
theorem d2Transfer102Bound : ∀ x ∈ Set.Icc ((d2Transfer102Lo:ℚ):ℝ) ((d2Transfer102Hi:ℚ):ℝ), ((d2Transfer102C0:ℚ):ℝ)*Real.log |x-((d2Transfer102S0:ℚ):ℝ)| ≤ ((d2Transfer102Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer102S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer102S0,d2Transfer102Lo,d2Transfer102Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer102C0 then |x-((d2Transfer102S0:ℚ):ℝ)| ≤ ((d2Log92Q:ℚ):ℝ) else ((d2Log92Q:ℚ):ℝ) ≤ |x-((d2Transfer102S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer102S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer102S0,d2Transfer102Lo,d2Transfer102Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer102C0,d2Log92Q,d2Transfer102S0,d2Transfer102Lo,d2Transfer102Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer102C0 d2Transfer102S0 d2Log92Q d2Log92Lo d2Log92Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log92Bounds
  have har : (((weightedUpper d2Transfer102C0 d2Log92Lo d2Log92Hi:ℚ):ℝ)) ≤ ((d2Transfer102Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer102Arithmetic
  linarith
#print axioms d2Transfer102Arithmetic
#print axioms d2Transfer102Bound
def d2Transfer103Lo : ℚ := (d2LitsNearTransfers012.q2 (58048651) 1 (-29))
def d2Transfer103Hi : ℚ := (d2LitsNearTransfers012.q2 (14931593) 1 (-27))
def d2Transfer103Cap : ℚ := (d2LitsNearTransfers012.q2 (2436024149) 1 (-40))
def d2Transfer103C0 : ℚ := (d2LitsNearTransfers012.q2 (1) 275 (-4))
def d2Transfer103S0 : ℚ := (d2LitsNearTransfers012.q2 (-1) 1 (0))
def d2Transfer103C1 : ℚ := (d2LitsNearTransfers012.q2 (-1) 55 (-3))
def d2Transfer103S1 : ℚ := (d2LitsNearTransfers012.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer103Arithmetic : weightedUpper d2Transfer103C0 d2Log92Lo d2Log92Hi + weightedUpper d2Transfer103C1 d2Log82Lo d2Log82Hi ≤ d2Transfer103Cap := by decide +kernel
theorem d2Transfer103Bound : ∀ x ∈ Set.Icc ((d2Transfer103Lo:ℚ):ℝ) ((d2Transfer103Hi:ℚ):ℝ), ((d2Transfer103C0:ℚ):ℝ)*Real.log |x-((d2Transfer103S0:ℚ):ℝ)| + ((d2Transfer103C1:ℚ):ℝ)*Real.log |x-((d2Transfer103S1:ℚ):ℝ)| ≤ ((d2Transfer103Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer103S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer103S0,d2Transfer103Lo,d2Transfer103Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer103C0 then |x-((d2Transfer103S0:ℚ):ℝ)| ≤ ((d2Log92Q:ℚ):ℝ) else ((d2Log92Q:ℚ):ℝ) ≤ |x-((d2Transfer103S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer103S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer103S0,d2Transfer103Lo,d2Transfer103Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer103C0,d2Log92Q,d2Transfer103S0,d2Transfer103Lo,d2Transfer103Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer103C0 d2Transfer103S0 d2Log92Q d2Log92Lo d2Log92Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log92Bounds
  have hn1 : x-((d2Transfer103S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer103S1,d2Transfer103Lo,d2Transfer103Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer103C1 then |x-((d2Transfer103S1:ℚ):ℝ)| ≤ ((d2Log82Q:ℚ):ℝ) else ((d2Log82Q:ℚ):ℝ) ≤ |x-((d2Transfer103S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer103S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer103S1,d2Transfer103Lo,d2Transfer103Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers012.q2, d2LitsNearLogCache005.q2, d2Transfer103C1,d2Log82Q,d2Transfer103S1,d2Transfer103Lo,d2Transfer103Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer103C1 d2Transfer103S1 d2Log82Q d2Log82Lo d2Log82Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log82Bounds
  have har : (((weightedUpper d2Transfer103C0 d2Log92Lo d2Log92Hi:ℚ):ℝ) + ((weightedUpper d2Transfer103C1 d2Log82Lo d2Log82Hi:ℚ):ℝ)) ≤ ((d2Transfer103Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer103Arithmetic
  linarith
#print axioms d2Transfer103Arithmetic
#print axioms d2Transfer103Bound
end CatalanMeasure.GenD.Signed.Data.Cells

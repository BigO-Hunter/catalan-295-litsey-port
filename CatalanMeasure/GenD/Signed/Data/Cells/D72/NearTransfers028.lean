module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache002
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
namespace d2LitsNearTransfers028
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers028
open D72.LogTransfer
def d2Transfer224Lo : ℚ := (d2LitsNearTransfers028.q2 (10045339) 1 (-24))
def d2Transfer224Hi : ℚ := (d2LitsNearTransfers028.q2 (162403145) 1 (-28))
def d2Transfer224Cap : ℚ := (d2LitsNearTransfers028.q2 (4476292748642812392879) 1 (-78))
def d2Transfer224C0 : ℚ := (d2LitsNearTransfers028.q2 (1) 1 (-5))
def d2Transfer224S0 : ℚ := (d2LitsNearTransfers028.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer224Arithmetic : weightedUpper d2Transfer224C0 d2Log125Lo d2Log125Hi ≤ d2Transfer224Cap := by decide +kernel
theorem d2Transfer224Bound : ∀ x ∈ Set.Icc ((d2Transfer224Lo:ℚ):ℝ) ((d2Transfer224Hi:ℚ):ℝ), ((d2Transfer224C0:ℚ):ℝ)*Real.log |x-((d2Transfer224S0:ℚ):ℝ)| ≤ ((d2Transfer224Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer224S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer224S0,d2Transfer224Lo,d2Transfer224Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer224C0 then |x-((d2Transfer224S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2Transfer224S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer224S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer224S0,d2Transfer224Lo,d2Transfer224Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer224C0,d2Log125Q,d2Transfer224S0,d2Transfer224Lo,d2Transfer224Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer224C0 d2Transfer224S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have har : (((weightedUpper d2Transfer224C0 d2Log125Lo d2Log125Hi:ℚ):ℝ)) ≤ ((d2Transfer224Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer224Arithmetic
  linarith
#print axioms d2Transfer224Arithmetic
#print axioms d2Transfer224Bound
def d2Transfer225Lo : ℚ := (d2LitsNearTransfers028.q2 (10045339) 1 (-24))
def d2Transfer225Hi : ℚ := (d2LitsNearTransfers028.q2 (162403145) 1 (-28))
def d2Transfer225Cap : ℚ := (d2LitsNearTransfers028.q2 (8567502079215689233839) 1 (-78))
def d2Transfer225C0 : ℚ := (d2LitsNearTransfers028.q2 (1) 11 (-5))
def d2Transfer225S0 : ℚ := (d2LitsNearTransfers028.q2 (-1) 1 (0))
def d2Transfer225C1 : ℚ := (d2LitsNearTransfers028.q2 (-5) 11 (-4))
def d2Transfer225S1 : ℚ := (d2LitsNearTransfers028.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer225Arithmetic : weightedUpper d2Transfer225C0 d2Log125Lo d2Log125Hi + weightedUpper d2Transfer225C1 d2Log49Lo d2Log49Hi ≤ d2Transfer225Cap := by decide +kernel
theorem d2Transfer225Bound : ∀ x ∈ Set.Icc ((d2Transfer225Lo:ℚ):ℝ) ((d2Transfer225Hi:ℚ):ℝ), ((d2Transfer225C0:ℚ):ℝ)*Real.log |x-((d2Transfer225S0:ℚ):ℝ)| + ((d2Transfer225C1:ℚ):ℝ)*Real.log |x-((d2Transfer225S1:ℚ):ℝ)| ≤ ((d2Transfer225Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer225S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer225S0,d2Transfer225Lo,d2Transfer225Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer225C0 then |x-((d2Transfer225S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2Transfer225S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer225S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer225S0,d2Transfer225Lo,d2Transfer225Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer225C0,d2Log125Q,d2Transfer225S0,d2Transfer225Lo,d2Transfer225Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer225C0 d2Transfer225S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have hn1 : x-((d2Transfer225S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer225S1,d2Transfer225Lo,d2Transfer225Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer225C1 then |x-((d2Transfer225S1:ℚ):ℝ)| ≤ ((d2Log49Q:ℚ):ℝ) else ((d2Log49Q:ℚ):ℝ) ≤ |x-((d2Transfer225S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer225S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer225S1,d2Transfer225Lo,d2Transfer225Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer225C1,d2Log49Q,d2Transfer225S1,d2Transfer225Lo,d2Transfer225Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer225C1 d2Transfer225S1 d2Log49Q d2Log49Lo d2Log49Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log49Bounds
  have har : (((weightedUpper d2Transfer225C0 d2Log125Lo d2Log125Hi:ℚ):ℝ) + ((weightedUpper d2Transfer225C1 d2Log49Lo d2Log49Hi:ℚ):ℝ)) ≤ ((d2Transfer225Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer225Arithmetic
  linarith
#print axioms d2Transfer225Arithmetic
#print axioms d2Transfer225Bound
def d2Transfer226Lo : ℚ := (d2LitsNearTransfers028.q2 (162403145) 1 (-28))
def d2Transfer226Hi : ℚ := (d2LitsNearTransfers028.q2 (326484011) 1 (-29))
def d2Transfer226Cap : ℚ := (d2LitsNearTransfers028.q2 (1474206701587581144801) 1 (-80))
def d2Transfer226C0 : ℚ := (d2LitsNearTransfers028.q2 (1) 25 (-4))
def d2Transfer226S0 : ℚ := (d2LitsNearTransfers028.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer226Arithmetic : weightedUpper d2Transfer226C0 d2Log126Lo d2Log126Hi ≤ d2Transfer226Cap := by decide +kernel
theorem d2Transfer226Bound : ∀ x ∈ Set.Icc ((d2Transfer226Lo:ℚ):ℝ) ((d2Transfer226Hi:ℚ):ℝ), ((d2Transfer226C0:ℚ):ℝ)*Real.log |x-((d2Transfer226S0:ℚ):ℝ)| ≤ ((d2Transfer226Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer226S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer226S0,d2Transfer226Lo,d2Transfer226Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer226C0 then |x-((d2Transfer226S0:ℚ):ℝ)| ≤ ((d2Log126Q:ℚ):ℝ) else ((d2Log126Q:ℚ):ℝ) ≤ |x-((d2Transfer226S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer226S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer226S0,d2Transfer226Lo,d2Transfer226Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer226C0,d2Log126Q,d2Transfer226S0,d2Transfer226Lo,d2Transfer226Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer226C0 d2Transfer226S0 d2Log126Q d2Log126Lo d2Log126Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log126Bounds
  have har : (((weightedUpper d2Transfer226C0 d2Log126Lo d2Log126Hi:ℚ):ℝ)) ≤ ((d2Transfer226Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer226Arithmetic
  linarith
#print axioms d2Transfer226Arithmetic
#print axioms d2Transfer226Bound
def d2Transfer227Lo : ℚ := (d2LitsNearTransfers028.q2 (162403145) 1 (-28))
def d2Transfer227Hi : ℚ := (d2LitsNearTransfers028.q2 (326484011) 1 (-29))
def d2Transfer227Cap : ℚ := (d2LitsNearTransfers028.q2 (2724506870223316487905) 1 (-80))
def d2Transfer227C0 : ℚ := (d2LitsNearTransfers028.q2 (1) 275 (-4))
def d2Transfer227S0 : ℚ := (d2LitsNearTransfers028.q2 (-1) 1 (0))
def d2Transfer227C1 : ℚ := (d2LitsNearTransfers028.q2 (-1) 55 (-3))
def d2Transfer227S1 : ℚ := (d2LitsNearTransfers028.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer227Arithmetic : weightedUpper d2Transfer227C0 d2Log126Lo d2Log126Hi + weightedUpper d2Transfer227C1 d2Log48Lo d2Log48Hi ≤ d2Transfer227Cap := by decide +kernel
theorem d2Transfer227Bound : ∀ x ∈ Set.Icc ((d2Transfer227Lo:ℚ):ℝ) ((d2Transfer227Hi:ℚ):ℝ), ((d2Transfer227C0:ℚ):ℝ)*Real.log |x-((d2Transfer227S0:ℚ):ℝ)| + ((d2Transfer227C1:ℚ):ℝ)*Real.log |x-((d2Transfer227S1:ℚ):ℝ)| ≤ ((d2Transfer227Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer227S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer227S0,d2Transfer227Lo,d2Transfer227Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer227C0 then |x-((d2Transfer227S0:ℚ):ℝ)| ≤ ((d2Log126Q:ℚ):ℝ) else ((d2Log126Q:ℚ):ℝ) ≤ |x-((d2Transfer227S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer227S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer227S0,d2Transfer227Lo,d2Transfer227Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer227C0,d2Log126Q,d2Transfer227S0,d2Transfer227Lo,d2Transfer227Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer227C0 d2Transfer227S0 d2Log126Q d2Log126Lo d2Log126Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log126Bounds
  have hn1 : x-((d2Transfer227S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer227S1,d2Transfer227Lo,d2Transfer227Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer227C1 then |x-((d2Transfer227S1:ℚ):ℝ)| ≤ ((d2Log48Q:ℚ):ℝ) else ((d2Log48Q:ℚ):ℝ) ≤ |x-((d2Transfer227S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer227S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer227S1,d2Transfer227Lo,d2Transfer227Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer227C1,d2Log48Q,d2Transfer227S1,d2Transfer227Lo,d2Transfer227Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer227C1 d2Transfer227S1 d2Log48Q d2Log48Lo d2Log48Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log48Bounds
  have har : (((weightedUpper d2Transfer227C0 d2Log126Lo d2Log126Hi:ℚ):ℝ) + ((weightedUpper d2Transfer227C1 d2Log48Lo d2Log48Hi:ℚ):ℝ)) ≤ ((d2Transfer227Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer227Arithmetic
  linarith
#print axioms d2Transfer227Arithmetic
#print axioms d2Transfer227Bound
def d2Transfer228Lo : ℚ := (d2LitsNearTransfers028.q2 (162403145) 1 (-28))
def d2Transfer228Hi : ℚ := (d2LitsNearTransfers028.q2 (326484011) 1 (-29))
def d2Transfer228Cap : ℚ := (d2LitsNearTransfers028.q2 (17947568960646277009121) 1 (-80))
def d2Transfer228C0 : ℚ := (d2LitsNearTransfers028.q2 (1) 1 (-5))
def d2Transfer228S0 : ℚ := (d2LitsNearTransfers028.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer228Arithmetic : weightedUpper d2Transfer228C0 d2Log126Lo d2Log126Hi ≤ d2Transfer228Cap := by decide +kernel
theorem d2Transfer228Bound : ∀ x ∈ Set.Icc ((d2Transfer228Lo:ℚ):ℝ) ((d2Transfer228Hi:ℚ):ℝ), ((d2Transfer228C0:ℚ):ℝ)*Real.log |x-((d2Transfer228S0:ℚ):ℝ)| ≤ ((d2Transfer228Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer228S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer228S0,d2Transfer228Lo,d2Transfer228Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer228C0 then |x-((d2Transfer228S0:ℚ):ℝ)| ≤ ((d2Log126Q:ℚ):ℝ) else ((d2Log126Q:ℚ):ℝ) ≤ |x-((d2Transfer228S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer228S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer228S0,d2Transfer228Lo,d2Transfer228Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer228C0,d2Log126Q,d2Transfer228S0,d2Transfer228Lo,d2Transfer228Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer228C0 d2Transfer228S0 d2Log126Q d2Log126Lo d2Log126Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log126Bounds
  have har : (((weightedUpper d2Transfer228C0 d2Log126Lo d2Log126Hi:ℚ):ℝ)) ≤ ((d2Transfer228Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer228Arithmetic
  linarith
#print axioms d2Transfer228Arithmetic
#print axioms d2Transfer228Bound
def d2Transfer229Lo : ℚ := (d2LitsNearTransfers028.q2 (162403145) 1 (-28))
def d2Transfer229Hi : ℚ := (d2LitsNearTransfers028.q2 (326484011) 1 (-29))
def d2Transfer229Cap : ℚ := (d2LitsNearTransfers028.q2 (34312406282937784372961) 1 (-80))
def d2Transfer229C0 : ℚ := (d2LitsNearTransfers028.q2 (1) 11 (-5))
def d2Transfer229S0 : ℚ := (d2LitsNearTransfers028.q2 (-1) 1 (0))
def d2Transfer229C1 : ℚ := (d2LitsNearTransfers028.q2 (-5) 11 (-4))
def d2Transfer229S1 : ℚ := (d2LitsNearTransfers028.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer229Arithmetic : weightedUpper d2Transfer229C0 d2Log126Lo d2Log126Hi + weightedUpper d2Transfer229C1 d2Log48Lo d2Log48Hi ≤ d2Transfer229Cap := by decide +kernel
theorem d2Transfer229Bound : ∀ x ∈ Set.Icc ((d2Transfer229Lo:ℚ):ℝ) ((d2Transfer229Hi:ℚ):ℝ), ((d2Transfer229C0:ℚ):ℝ)*Real.log |x-((d2Transfer229S0:ℚ):ℝ)| + ((d2Transfer229C1:ℚ):ℝ)*Real.log |x-((d2Transfer229S1:ℚ):ℝ)| ≤ ((d2Transfer229Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer229S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer229S0,d2Transfer229Lo,d2Transfer229Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer229C0 then |x-((d2Transfer229S0:ℚ):ℝ)| ≤ ((d2Log126Q:ℚ):ℝ) else ((d2Log126Q:ℚ):ℝ) ≤ |x-((d2Transfer229S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer229S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer229S0,d2Transfer229Lo,d2Transfer229Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer229C0,d2Log126Q,d2Transfer229S0,d2Transfer229Lo,d2Transfer229Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer229C0 d2Transfer229S0 d2Log126Q d2Log126Lo d2Log126Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log126Bounds
  have hn1 : x-((d2Transfer229S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer229S1,d2Transfer229Lo,d2Transfer229Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer229C1 then |x-((d2Transfer229S1:ℚ):ℝ)| ≤ ((d2Log48Q:ℚ):ℝ) else ((d2Log48Q:ℚ):ℝ) ≤ |x-((d2Transfer229S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer229S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer229S1,d2Transfer229Lo,d2Transfer229Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer229C1,d2Log48Q,d2Transfer229S1,d2Transfer229Lo,d2Transfer229Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer229C1 d2Transfer229S1 d2Log48Q d2Log48Lo d2Log48Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log48Bounds
  have har : (((weightedUpper d2Transfer229C0 d2Log126Lo d2Log126Hi:ℚ):ℝ) + ((weightedUpper d2Transfer229C1 d2Log48Lo d2Log48Hi:ℚ):ℝ)) ≤ ((d2Transfer229Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer229Arithmetic
  linarith
#print axioms d2Transfer229Arithmetic
#print axioms d2Transfer229Bound
def d2Transfer230Lo : ℚ := (d2LitsNearTransfers028.q2 (326484011) 1 (-29))
def d2Transfer230Hi : ℚ := (d2LitsNearTransfers028.q2 (654645743) 1 (-30))
def d2Transfer230Cap : ℚ := (d2LitsNearTransfers028.q2 (188861997272932581765) 1 (-77))
def d2Transfer230C0 : ℚ := (d2LitsNearTransfers028.q2 (1) 25 (-4))
def d2Transfer230S0 : ℚ := (d2LitsNearTransfers028.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer230Arithmetic : weightedUpper d2Transfer230C0 d2Log127Lo d2Log127Hi ≤ d2Transfer230Cap := by decide +kernel
theorem d2Transfer230Bound : ∀ x ∈ Set.Icc ((d2Transfer230Lo:ℚ):ℝ) ((d2Transfer230Hi:ℚ):ℝ), ((d2Transfer230C0:ℚ):ℝ)*Real.log |x-((d2Transfer230S0:ℚ):ℝ)| ≤ ((d2Transfer230Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer230S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer230S0,d2Transfer230Lo,d2Transfer230Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer230C0 then |x-((d2Transfer230S0:ℚ):ℝ)| ≤ ((d2Log127Q:ℚ):ℝ) else ((d2Log127Q:ℚ):ℝ) ≤ |x-((d2Transfer230S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer230S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer230S0,d2Transfer230Lo,d2Transfer230Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer230C0,d2Log127Q,d2Transfer230S0,d2Transfer230Lo,d2Transfer230Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer230C0 d2Transfer230S0 d2Log127Q d2Log127Lo d2Log127Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log127Bounds
  have har : (((weightedUpper d2Transfer230C0 d2Log127Lo d2Log127Hi:ℚ):ℝ)) ≤ ((d2Transfer230Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer230Arithmetic
  linarith
#print axioms d2Transfer230Arithmetic
#print axioms d2Transfer230Bound
def d2Transfer231Lo : ℚ := (d2LitsNearTransfers028.q2 (326484011) 1 (-29))
def d2Transfer231Hi : ℚ := (d2LitsNearTransfers028.q2 (654645743) 1 (-30))
def d2Transfer231Cap : ℚ := (d2LitsNearTransfers028.q2 (345149518352399499653) 1 (-77))
def d2Transfer231C0 : ℚ := (d2LitsNearTransfers028.q2 (1) 275 (-4))
def d2Transfer231S0 : ℚ := (d2LitsNearTransfers028.q2 (-1) 1 (0))
def d2Transfer231C1 : ℚ := (d2LitsNearTransfers028.q2 (-1) 55 (-3))
def d2Transfer231S1 : ℚ := (d2LitsNearTransfers028.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer231Arithmetic : weightedUpper d2Transfer231C0 d2Log127Lo d2Log127Hi + weightedUpper d2Transfer231C1 d2Log47Lo d2Log47Hi ≤ d2Transfer231Cap := by decide +kernel
theorem d2Transfer231Bound : ∀ x ∈ Set.Icc ((d2Transfer231Lo:ℚ):ℝ) ((d2Transfer231Hi:ℚ):ℝ), ((d2Transfer231C0:ℚ):ℝ)*Real.log |x-((d2Transfer231S0:ℚ):ℝ)| + ((d2Transfer231C1:ℚ):ℝ)*Real.log |x-((d2Transfer231S1:ℚ):ℝ)| ≤ ((d2Transfer231Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer231S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer231S0,d2Transfer231Lo,d2Transfer231Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer231C0 then |x-((d2Transfer231S0:ℚ):ℝ)| ≤ ((d2Log127Q:ℚ):ℝ) else ((d2Log127Q:ℚ):ℝ) ≤ |x-((d2Transfer231S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer231S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer231S0,d2Transfer231Lo,d2Transfer231Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer231C0,d2Log127Q,d2Transfer231S0,d2Transfer231Lo,d2Transfer231Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer231C0 d2Transfer231S0 d2Log127Q d2Log127Lo d2Log127Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log127Bounds
  have hn1 : x-((d2Transfer231S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer231S1,d2Transfer231Lo,d2Transfer231Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer231C1 then |x-((d2Transfer231S1:ℚ):ℝ)| ≤ ((d2Log47Q:ℚ):ℝ) else ((d2Log47Q:ℚ):ℝ) ≤ |x-((d2Transfer231S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer231S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer231S1,d2Transfer231Lo,d2Transfer231Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers028.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer231C1,d2Log47Q,d2Transfer231S1,d2Transfer231Lo,d2Transfer231Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer231C1 d2Transfer231S1 d2Log47Q d2Log47Lo d2Log47Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log47Bounds
  have har : (((weightedUpper d2Transfer231C0 d2Log127Lo d2Log127Hi:ℚ):ℝ) + ((weightedUpper d2Transfer231C1 d2Log47Lo d2Log47Hi:ℚ):ℝ)) ≤ ((d2Transfer231Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer231Arithmetic
  linarith
#print axioms d2Transfer231Arithmetic
#print axioms d2Transfer231Bound
end CatalanMeasure.GenD.Signed.Data.Cells

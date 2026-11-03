module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers042
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers042
open D72.LogTransfer
def d2Transfer336Lo : ℚ := (d2LitsNearTransfers042.q2 (172469471) 1 (-28))
def d2Transfer336Hi : ℚ := (d2LitsNearTransfers042.q2 (21768399) 1 (-25))
def d2Transfer336Cap : ℚ := (d2LitsNearTransfers042.q2 (21285489634774710478965) 1 (-80))
def d2Transfer336C0 : ℚ := (d2LitsNearTransfers042.q2 (1) 1 (-5))
def d2Transfer336S0 : ℚ := (d2LitsNearTransfers042.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer336Arithmetic : weightedUpper d2Transfer336C0 d2Log162Lo d2Log162Hi ≤ d2Transfer336Cap := by decide +kernel
theorem d2Transfer336Bound : ∀ x ∈ Set.Icc ((d2Transfer336Lo:ℚ):ℝ) ((d2Transfer336Hi:ℚ):ℝ), ((d2Transfer336C0:ℚ):ℝ)*Real.log |x-((d2Transfer336S0:ℚ):ℝ)| ≤ ((d2Transfer336Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer336S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer336S0,d2Transfer336Lo,d2Transfer336Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer336C0 then |x-((d2Transfer336S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2Transfer336S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer336S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer336S0,d2Transfer336Lo,d2Transfer336Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer336C0,d2Log162Q,d2Transfer336S0,d2Transfer336Lo,d2Transfer336Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer336C0 d2Transfer336S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have har : (((weightedUpper d2Transfer336C0 d2Log162Lo d2Log162Hi:ℚ):ℝ)) ≤ ((d2Transfer336Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer336Arithmetic
  linarith
#print axioms d2Transfer336Arithmetic
#print axioms d2Transfer336Bound
def d2Transfer337Lo : ℚ := (d2LitsNearTransfers042.q2 (172469471) 1 (-28))
def d2Transfer337Hi : ℚ := (d2LitsNearTransfers042.q2 (21768399) 1 (-25))
def d2Transfer337Cap : ℚ := (d2LitsNearTransfers042.q2 (37650326957066217842805) 1 (-80))
def d2Transfer337C0 : ℚ := (d2LitsNearTransfers042.q2 (1) 11 (-5))
def d2Transfer337S0 : ℚ := (d2LitsNearTransfers042.q2 (-1) 1 (0))
def d2Transfer337C1 : ℚ := (d2LitsNearTransfers042.q2 (-5) 11 (-4))
def d2Transfer337S1 : ℚ := (d2LitsNearTransfers042.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer337Arithmetic : weightedUpper d2Transfer337C0 d2Log162Lo d2Log162Hi + weightedUpper d2Transfer337C1 d2Log12Lo d2Log12Hi ≤ d2Transfer337Cap := by decide +kernel
theorem d2Transfer337Bound : ∀ x ∈ Set.Icc ((d2Transfer337Lo:ℚ):ℝ) ((d2Transfer337Hi:ℚ):ℝ), ((d2Transfer337C0:ℚ):ℝ)*Real.log |x-((d2Transfer337S0:ℚ):ℝ)| + ((d2Transfer337C1:ℚ):ℝ)*Real.log |x-((d2Transfer337S1:ℚ):ℝ)| ≤ ((d2Transfer337Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer337S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer337S0,d2Transfer337Lo,d2Transfer337Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer337C0 then |x-((d2Transfer337S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2Transfer337S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer337S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer337S0,d2Transfer337Lo,d2Transfer337Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer337C0,d2Log162Q,d2Transfer337S0,d2Transfer337Lo,d2Transfer337Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer337C0 d2Transfer337S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have hn1 : x-((d2Transfer337S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer337S1,d2Transfer337Lo,d2Transfer337Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer337C1 then |x-((d2Transfer337S1:ℚ):ℝ)| ≤ ((d2Log12Q:ℚ):ℝ) else ((d2Log12Q:ℚ):ℝ) ≤ |x-((d2Transfer337S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer337S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer337S1,d2Transfer337Lo,d2Transfer337Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer337C1,d2Log12Q,d2Transfer337S1,d2Transfer337Lo,d2Transfer337Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer337C1 d2Transfer337S1 d2Log12Q d2Log12Lo d2Log12Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log12Bounds
  have har : (((weightedUpper d2Transfer337C0 d2Log162Lo d2Log162Hi:ℚ):ℝ) + ((weightedUpper d2Transfer337C1 d2Log12Lo d2Log12Hi:ℚ):ℝ)) ≤ ((d2Transfer337Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer337Arithmetic
  linarith
#print axioms d2Transfer337Arithmetic
#print axioms d2Transfer337Bound
def d2Transfer338Lo : ℚ := (d2LitsNearTransfers042.q2 (21768399) 1 (-25))
def d2Transfer338Hi : ℚ := (d2LitsNearTransfers042.q2 (88751317) 1 (-27))
def d2Transfer338Cap : ℚ := (d2LitsNearTransfers042.q2 (3041282164444953296725) 1 (-79))
def d2Transfer338C0 : ℚ := (d2LitsNearTransfers042.q2 (1) 25 (-4))
def d2Transfer338S0 : ℚ := (d2LitsNearTransfers042.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer338Arithmetic : weightedUpper d2Transfer338C0 d2Log164Lo d2Log164Hi ≤ d2Transfer338Cap := by decide +kernel
theorem d2Transfer338Bound : ∀ x ∈ Set.Icc ((d2Transfer338Lo:ℚ):ℝ) ((d2Transfer338Hi:ℚ):ℝ), ((d2Transfer338C0:ℚ):ℝ)*Real.log |x-((d2Transfer338S0:ℚ):ℝ)| ≤ ((d2Transfer338Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer338S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer338S0,d2Transfer338Lo,d2Transfer338Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer338C0 then |x-((d2Transfer338S0:ℚ):ℝ)| ≤ ((d2Log164Q:ℚ):ℝ) else ((d2Log164Q:ℚ):ℝ) ≤ |x-((d2Transfer338S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer338S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer338S0,d2Transfer338Lo,d2Transfer338Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer338C0,d2Log164Q,d2Transfer338S0,d2Transfer338Lo,d2Transfer338Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer338C0 d2Transfer338S0 d2Log164Q d2Log164Lo d2Log164Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log164Bounds
  have har : (((weightedUpper d2Transfer338C0 d2Log164Lo d2Log164Hi:ℚ):ℝ)) ≤ ((d2Transfer338Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer338Arithmetic
  linarith
#print axioms d2Transfer338Arithmetic
#print axioms d2Transfer338Bound
def d2Transfer339Lo : ℚ := (d2LitsNearTransfers042.q2 (21768399) 1 (-25))
def d2Transfer339Hi : ℚ := (d2LitsNearTransfers042.q2 (88751317) 1 (-27))
def d2Transfer339Cap : ℚ := (d2LitsNearTransfers042.q2 (3666432248762820968277) 1 (-79))
def d2Transfer339C0 : ℚ := (d2LitsNearTransfers042.q2 (1) 275 (-4))
def d2Transfer339S0 : ℚ := (d2LitsNearTransfers042.q2 (-1) 1 (0))
def d2Transfer339C1 : ℚ := (d2LitsNearTransfers042.q2 (-1) 55 (-3))
def d2Transfer339S1 : ℚ := (d2LitsNearTransfers042.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer339Arithmetic : weightedUpper d2Transfer339C0 d2Log164Lo d2Log164Hi + weightedUpper d2Transfer339C1 d2Log10Lo d2Log10Hi ≤ d2Transfer339Cap := by decide +kernel
theorem d2Transfer339Bound : ∀ x ∈ Set.Icc ((d2Transfer339Lo:ℚ):ℝ) ((d2Transfer339Hi:ℚ):ℝ), ((d2Transfer339C0:ℚ):ℝ)*Real.log |x-((d2Transfer339S0:ℚ):ℝ)| + ((d2Transfer339C1:ℚ):ℝ)*Real.log |x-((d2Transfer339S1:ℚ):ℝ)| ≤ ((d2Transfer339Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer339S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer339S0,d2Transfer339Lo,d2Transfer339Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer339C0 then |x-((d2Transfer339S0:ℚ):ℝ)| ≤ ((d2Log164Q:ℚ):ℝ) else ((d2Log164Q:ℚ):ℝ) ≤ |x-((d2Transfer339S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer339S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer339S0,d2Transfer339Lo,d2Transfer339Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer339C0,d2Log164Q,d2Transfer339S0,d2Transfer339Lo,d2Transfer339Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer339C0 d2Transfer339S0 d2Log164Q d2Log164Lo d2Log164Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log164Bounds
  have hn1 : x-((d2Transfer339S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer339S1,d2Transfer339Lo,d2Transfer339Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer339C1 then |x-((d2Transfer339S1:ℚ):ℝ)| ≤ ((d2Log10Q:ℚ):ℝ) else ((d2Log10Q:ℚ):ℝ) ≤ |x-((d2Transfer339S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer339S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer339S1,d2Transfer339Lo,d2Transfer339Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer339C1,d2Log10Q,d2Transfer339S1,d2Transfer339Lo,d2Transfer339Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer339C1 d2Transfer339S1 d2Log10Q d2Log10Lo d2Log10Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log10Bounds
  have har : (((weightedUpper d2Transfer339C0 d2Log164Lo d2Log164Hi:ℚ):ℝ) + ((weightedUpper d2Transfer339C1 d2Log10Lo d2Log10Hi:ℚ):ℝ)) ≤ ((d2Transfer339Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer339Arithmetic
  linarith
#print axioms d2Transfer339Arithmetic
#print axioms d2Transfer339Bound
def d2Transfer340Lo : ℚ := (d2LitsNearTransfers042.q2 (21768399) 1 (-25))
def d2Transfer340Hi : ℚ := (d2LitsNearTransfers042.q2 (88751317) 1 (-27))
def d2Transfer340Cap : ℚ := (d2LitsNearTransfers042.q2 (11277963293974301228885) 1 (-79))
def d2Transfer340C0 : ℚ := (d2LitsNearTransfers042.q2 (1) 1 (-5))
def d2Transfer340S0 : ℚ := (d2LitsNearTransfers042.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer340Arithmetic : weightedUpper d2Transfer340C0 d2Log164Lo d2Log164Hi ≤ d2Transfer340Cap := by decide +kernel
theorem d2Transfer340Bound : ∀ x ∈ Set.Icc ((d2Transfer340Lo:ℚ):ℝ) ((d2Transfer340Hi:ℚ):ℝ), ((d2Transfer340C0:ℚ):ℝ)*Real.log |x-((d2Transfer340S0:ℚ):ℝ)| ≤ ((d2Transfer340Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer340S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer340S0,d2Transfer340Lo,d2Transfer340Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer340C0 then |x-((d2Transfer340S0:ℚ):ℝ)| ≤ ((d2Log164Q:ℚ):ℝ) else ((d2Log164Q:ℚ):ℝ) ≤ |x-((d2Transfer340S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer340S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer340S0,d2Transfer340Lo,d2Transfer340Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer340C0,d2Log164Q,d2Transfer340S0,d2Transfer340Lo,d2Transfer340Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer340C0 d2Transfer340S0 d2Log164Q d2Log164Lo d2Log164Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log164Bounds
  have har : (((weightedUpper d2Transfer340C0 d2Log164Lo d2Log164Hi:ℚ):ℝ)) ≤ ((d2Transfer340Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer340Arithmetic
  linarith
#print axioms d2Transfer340Arithmetic
#print axioms d2Transfer340Bound
def d2Transfer341Lo : ℚ := (d2LitsNearTransfers042.q2 (21768399) 1 (-25))
def d2Transfer341Hi : ℚ := (d2LitsNearTransfers042.q2 (88751317) 1 (-27))
def d2Transfer341Cap : ℚ := (d2LitsNearTransfers042.q2 (19460381955120054910805) 1 (-79))
def d2Transfer341C0 : ℚ := (d2LitsNearTransfers042.q2 (1) 11 (-5))
def d2Transfer341S0 : ℚ := (d2LitsNearTransfers042.q2 (-1) 1 (0))
def d2Transfer341C1 : ℚ := (d2LitsNearTransfers042.q2 (-5) 11 (-4))
def d2Transfer341S1 : ℚ := (d2LitsNearTransfers042.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer341Arithmetic : weightedUpper d2Transfer341C0 d2Log164Lo d2Log164Hi + weightedUpper d2Transfer341C1 d2Log10Lo d2Log10Hi ≤ d2Transfer341Cap := by decide +kernel
theorem d2Transfer341Bound : ∀ x ∈ Set.Icc ((d2Transfer341Lo:ℚ):ℝ) ((d2Transfer341Hi:ℚ):ℝ), ((d2Transfer341C0:ℚ):ℝ)*Real.log |x-((d2Transfer341S0:ℚ):ℝ)| + ((d2Transfer341C1:ℚ):ℝ)*Real.log |x-((d2Transfer341S1:ℚ):ℝ)| ≤ ((d2Transfer341Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer341S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer341S0,d2Transfer341Lo,d2Transfer341Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer341C0 then |x-((d2Transfer341S0:ℚ):ℝ)| ≤ ((d2Log164Q:ℚ):ℝ) else ((d2Log164Q:ℚ):ℝ) ≤ |x-((d2Transfer341S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer341S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer341S0,d2Transfer341Lo,d2Transfer341Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer341C0,d2Log164Q,d2Transfer341S0,d2Transfer341Lo,d2Transfer341Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer341C0 d2Transfer341S0 d2Log164Q d2Log164Lo d2Log164Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log164Bounds
  have hn1 : x-((d2Transfer341S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer341S1,d2Transfer341Lo,d2Transfer341Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer341C1 then |x-((d2Transfer341S1:ℚ):ℝ)| ≤ ((d2Log10Q:ℚ):ℝ) else ((d2Log10Q:ℚ):ℝ) ≤ |x-((d2Transfer341S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer341S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer341S1,d2Transfer341Lo,d2Transfer341Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer341C1,d2Log10Q,d2Transfer341S1,d2Transfer341Lo,d2Transfer341Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer341C1 d2Transfer341S1 d2Log10Q d2Log10Lo d2Log10Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log10Bounds
  have har : (((weightedUpper d2Transfer341C0 d2Log164Lo d2Log164Hi:ℚ):ℝ) + ((weightedUpper d2Transfer341C1 d2Log10Lo d2Log10Hi:ℚ):ℝ)) ≤ ((d2Transfer341Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer341Arithmetic
  linarith
#print axioms d2Transfer341Arithmetic
#print axioms d2Transfer341Bound
def d2Transfer342Lo : ℚ := (d2LitsNearTransfers042.q2 (88751317) 1 (-27))
def d2Transfer342Hi : ℚ := (d2LitsNearTransfers042.q2 (45214519) 1 (-26))
def d2Transfer342Cap : ℚ := (d2LitsNearTransfers042.q2 (1849900766862984443043) 1 (-78))
def d2Transfer342C0 : ℚ := (d2LitsNearTransfers042.q2 (1) 25 (-4))
def d2Transfer342S0 : ℚ := (d2LitsNearTransfers042.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer342Arithmetic : weightedUpper d2Transfer342C0 d2Log165Lo d2Log165Hi ≤ d2Transfer342Cap := by decide +kernel
theorem d2Transfer342Bound : ∀ x ∈ Set.Icc ((d2Transfer342Lo:ℚ):ℝ) ((d2Transfer342Hi:ℚ):ℝ), ((d2Transfer342C0:ℚ):ℝ)*Real.log |x-((d2Transfer342S0:ℚ):ℝ)| ≤ ((d2Transfer342Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer342S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer342S0,d2Transfer342Lo,d2Transfer342Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer342C0 then |x-((d2Transfer342S0:ℚ):ℝ)| ≤ ((d2Log165Q:ℚ):ℝ) else ((d2Log165Q:ℚ):ℝ) ≤ |x-((d2Transfer342S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer342S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer342S0,d2Transfer342Lo,d2Transfer342Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer342C0,d2Log165Q,d2Transfer342S0,d2Transfer342Lo,d2Transfer342Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer342C0 d2Transfer342S0 d2Log165Q d2Log165Lo d2Log165Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log165Bounds
  have har : (((weightedUpper d2Transfer342C0 d2Log165Lo d2Log165Hi:ℚ):ℝ)) ≤ ((d2Transfer342Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer342Arithmetic
  linarith
#print axioms d2Transfer342Arithmetic
#print axioms d2Transfer342Bound
def d2Transfer343Lo : ℚ := (d2LitsNearTransfers042.q2 (88751317) 1 (-27))
def d2Transfer343Hi : ℚ := (d2LitsNearTransfers042.q2 (45214519) 1 (-26))
def d2Transfer343Cap : ℚ := (d2LitsNearTransfers042.q2 (2162475809021918278819) 1 (-78))
def d2Transfer343C0 : ℚ := (d2LitsNearTransfers042.q2 (1) 275 (-4))
def d2Transfer343S0 : ℚ := (d2LitsNearTransfers042.q2 (-1) 1 (0))
def d2Transfer343C1 : ℚ := (d2LitsNearTransfers042.q2 (-1) 55 (-3))
def d2Transfer343S1 : ℚ := (d2LitsNearTransfers042.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer343Arithmetic : weightedUpper d2Transfer343C0 d2Log165Lo d2Log165Hi + weightedUpper d2Transfer343C1 d2Log9Lo d2Log9Hi ≤ d2Transfer343Cap := by decide +kernel
theorem d2Transfer343Bound : ∀ x ∈ Set.Icc ((d2Transfer343Lo:ℚ):ℝ) ((d2Transfer343Hi:ℚ):ℝ), ((d2Transfer343C0:ℚ):ℝ)*Real.log |x-((d2Transfer343S0:ℚ):ℝ)| + ((d2Transfer343C1:ℚ):ℝ)*Real.log |x-((d2Transfer343S1:ℚ):ℝ)| ≤ ((d2Transfer343Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer343S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer343S0,d2Transfer343Lo,d2Transfer343Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer343C0 then |x-((d2Transfer343S0:ℚ):ℝ)| ≤ ((d2Log165Q:ℚ):ℝ) else ((d2Log165Q:ℚ):ℝ) ≤ |x-((d2Transfer343S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer343S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer343S0,d2Transfer343Lo,d2Transfer343Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer343C0,d2Log165Q,d2Transfer343S0,d2Transfer343Lo,d2Transfer343Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer343C0 d2Transfer343S0 d2Log165Q d2Log165Lo d2Log165Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log165Bounds
  have hn1 : x-((d2Transfer343S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer343S1,d2Transfer343Lo,d2Transfer343Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer343C1 then |x-((d2Transfer343S1:ℚ):ℝ)| ≤ ((d2Log9Q:ℚ):ℝ) else ((d2Log9Q:ℚ):ℝ) ≤ |x-((d2Transfer343S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer343S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer343S1,d2Transfer343Lo,d2Transfer343Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers042.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer343C1,d2Log9Q,d2Transfer343S1,d2Transfer343Lo,d2Transfer343Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer343C1 d2Transfer343S1 d2Log9Q d2Log9Lo d2Log9Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log9Bounds
  have har : (((weightedUpper d2Transfer343C0 d2Log165Lo d2Log165Hi:ℚ):ℝ) + ((weightedUpper d2Transfer343C1 d2Log9Lo d2Log9Hi:ℚ):ℝ)) ≤ ((d2Transfer343Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer343Arithmetic
  linarith
#print axioms d2Transfer343Arithmetic
#print axioms d2Transfer343Bound
end CatalanMeasure.GenD.Signed.Data.Cells

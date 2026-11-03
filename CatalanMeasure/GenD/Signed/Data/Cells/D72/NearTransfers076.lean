module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache011
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers076
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers076
open D72.LogTransfer
def d2Transfer608Lo : ℚ := (d2LitsNearTransfers076.q2 (16756223) 1 (-24))
def d2Transfer608Hi : ℚ := (d2LitsNearTransfers076.q2 (8380219) 1 (-23))
def d2Transfer608Cap : ℚ := (d2LitsNearTransfers076.q2 (55169039566099252876817) 1 (-78))
def d2Transfer608C0 : ℚ := (d2LitsNearTransfers076.q2 (23) 25 (-5))
def d2Transfer608S0 : ℚ := (d2LitsNearTransfers076.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer608Arithmetic : weightedUpper d2Transfer608C0 d2Log173Lo d2Log173Hi ≤ d2Transfer608Cap := by decide +kernel
theorem d2Transfer608Bound : ∀ x ∈ Set.Icc ((d2Transfer608Lo:ℚ):ℝ) ((d2Transfer608Hi:ℚ):ℝ), ((d2Transfer608C0:ℚ):ℝ)*Real.log |x-((d2Transfer608S0:ℚ):ℝ)| ≤ ((d2Transfer608Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer608S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer608S0,d2Transfer608Lo,d2Transfer608Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer608C0 then |x-((d2Transfer608S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2Transfer608S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer608S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer608S0,d2Transfer608Lo,d2Transfer608Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer608C0,d2Log173Q,d2Transfer608S0,d2Transfer608Lo,d2Transfer608Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer608C0 d2Transfer608S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have har : (((weightedUpper d2Transfer608C0 d2Log173Lo d2Log173Hi:ℚ):ℝ)) ≤ ((d2Transfer608Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer608Arithmetic
  linarith
#print axioms d2Transfer608Arithmetic
#print axioms d2Transfer608Bound
def d2Transfer609Lo : ℚ := (d2LitsNearTransfers076.q2 (16756223) 1 (-24))
def d2Transfer609Hi : ℚ := (d2LitsNearTransfers076.q2 (8380219) 1 (-23))
def d2Transfer609Cap : ℚ := (d2LitsNearTransfers076.q2 (59381786413916070450705) 1 (-78))
def d2Transfer609C0 : ℚ := (d2LitsNearTransfers076.q2 (3) 275 (-5))
def d2Transfer609S0 : ℚ := (d2LitsNearTransfers076.q2 (-1) 1 (0))
def d2Transfer609C1 : ℚ := (d2LitsNearTransfers076.q2 (-5) 11 (-4))
def d2Transfer609S1 : ℚ := (d2LitsNearTransfers076.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer609Arithmetic : weightedUpper d2Transfer609C0 d2Log173Lo d2Log173Hi + weightedUpper d2Transfer609C1 d2Log1Lo d2Log1Hi ≤ d2Transfer609Cap := by decide +kernel
theorem d2Transfer609Bound : ∀ x ∈ Set.Icc ((d2Transfer609Lo:ℚ):ℝ) ((d2Transfer609Hi:ℚ):ℝ), ((d2Transfer609C0:ℚ):ℝ)*Real.log |x-((d2Transfer609S0:ℚ):ℝ)| + ((d2Transfer609C1:ℚ):ℝ)*Real.log |x-((d2Transfer609S1:ℚ):ℝ)| ≤ ((d2Transfer609Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer609S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer609S0,d2Transfer609Lo,d2Transfer609Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer609C0 then |x-((d2Transfer609S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2Transfer609S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer609S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer609S0,d2Transfer609Lo,d2Transfer609Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer609C0,d2Log173Q,d2Transfer609S0,d2Transfer609Lo,d2Transfer609Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer609C0 d2Transfer609S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have hn1 : x-((d2Transfer609S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer609S1,d2Transfer609Lo,d2Transfer609Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer609C1 then |x-((d2Transfer609S1:ℚ):ℝ)| ≤ ((d2Log1Q:ℚ):ℝ) else ((d2Log1Q:ℚ):ℝ) ≤ |x-((d2Transfer609S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer609S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer609S1,d2Transfer609Lo,d2Transfer609Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer609C1,d2Log1Q,d2Transfer609S1,d2Transfer609Lo,d2Transfer609Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer609C1 d2Transfer609S1 d2Log1Q d2Log1Lo d2Log1Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log1Bounds
  have har : (((weightedUpper d2Transfer609C0 d2Log173Lo d2Log173Hi:ℚ):ℝ) + ((weightedUpper d2Transfer609C1 d2Log1Lo d2Log1Hi:ℚ):ℝ)) ≤ ((d2Transfer609Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer609Arithmetic
  linarith
#print axioms d2Transfer609Arithmetic
#print axioms d2Transfer609Bound
def d2Transfer610Lo : ℚ := (d2LitsNearTransfers076.q2 (8380219) 1 (-23))
def d2Transfer610Hi : ℚ := (d2LitsNearTransfers076.q2 (999) 125 (-3))
def d2Transfer610Cap : ℚ := (d2LitsNearTransfers076.q2 (102672983640873595763659) 1 (-79))
def d2Transfer610C0 : ℚ := (d2LitsNearTransfers076.q2 (-1) 55 (-3))
def d2Transfer610S0 : ℚ := (d2LitsNearTransfers076.q2 (-1) 1 (0))
def d2Transfer610C1 : ℚ := (d2LitsNearTransfers076.q2 (-1) 55 (-3))
def d2Transfer610S1 : ℚ := (d2LitsNearTransfers076.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer610Arithmetic : weightedUpper d2Transfer610C0 d2Log173Lo d2Log173Hi + weightedUpper d2Transfer610C1 d2Log0Lo d2Log0Hi ≤ d2Transfer610Cap := by decide +kernel
theorem d2Transfer610Bound : ∀ x ∈ Set.Icc ((d2Transfer610Lo:ℚ):ℝ) ((d2Transfer610Hi:ℚ):ℝ), ((d2Transfer610C0:ℚ):ℝ)*Real.log |x-((d2Transfer610S0:ℚ):ℝ)| + ((d2Transfer610C1:ℚ):ℝ)*Real.log |x-((d2Transfer610S1:ℚ):ℝ)| ≤ ((d2Transfer610Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer610S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer610S0,d2Transfer610Lo,d2Transfer610Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer610C0 then |x-((d2Transfer610S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2Transfer610S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer610S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer610S0,d2Transfer610Lo,d2Transfer610Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer610C0,d2Log173Q,d2Transfer610S0,d2Transfer610Lo,d2Transfer610Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer610C0 d2Transfer610S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have hn1 : x-((d2Transfer610S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer610S1,d2Transfer610Lo,d2Transfer610Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer610C1 then |x-((d2Transfer610S1:ℚ):ℝ)| ≤ ((d2Log0Q:ℚ):ℝ) else ((d2Log0Q:ℚ):ℝ) ≤ |x-((d2Transfer610S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer610S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer610S1,d2Transfer610Lo,d2Transfer610Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer610C1,d2Log0Q,d2Transfer610S1,d2Transfer610Lo,d2Transfer610Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer610C1 d2Transfer610S1 d2Log0Q d2Log0Lo d2Log0Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log0Bounds
  have har : (((weightedUpper d2Transfer610C0 d2Log173Lo d2Log173Hi:ℚ):ℝ) + ((weightedUpper d2Transfer610C1 d2Log0Lo d2Log0Hi:ℚ):ℝ)) ≤ ((d2Transfer610Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer610Arithmetic
  linarith
#print axioms d2Transfer610Arithmetic
#print axioms d2Transfer610Bound
def d2Transfer611Lo : ℚ := (d2LitsNearTransfers076.q2 (8380219) 1 (-23))
def d2Transfer611Hi : ℚ := (d2LitsNearTransfers076.q2 (999) 125 (-3))
def d2Transfer611Cap : ℚ := (d2LitsNearTransfers076.q2 (110338881577836739230667) 1 (-79))
def d2Transfer611C0 : ℚ := (d2LitsNearTransfers076.q2 (23) 25 (-5))
def d2Transfer611S0 : ℚ := (d2LitsNearTransfers076.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer611Arithmetic : weightedUpper d2Transfer611C0 d2Log174Lo d2Log174Hi ≤ d2Transfer611Cap := by decide +kernel
theorem d2Transfer611Bound : ∀ x ∈ Set.Icc ((d2Transfer611Lo:ℚ):ℝ) ((d2Transfer611Hi:ℚ):ℝ), ((d2Transfer611C0:ℚ):ℝ)*Real.log |x-((d2Transfer611S0:ℚ):ℝ)| ≤ ((d2Transfer611Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer611S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer611S0,d2Transfer611Lo,d2Transfer611Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer611C0 then |x-((d2Transfer611S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2Transfer611S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer611S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer611S0,d2Transfer611Lo,d2Transfer611Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer611C0,d2Log174Q,d2Transfer611S0,d2Transfer611Lo,d2Transfer611Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer611C0 d2Transfer611S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have har : (((weightedUpper d2Transfer611C0 d2Log174Lo d2Log174Hi:ℚ):ℝ)) ≤ ((d2Transfer611Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer611Arithmetic
  linarith
#print axioms d2Transfer611Arithmetic
#print axioms d2Transfer611Bound
def d2Transfer612Lo : ℚ := (d2LitsNearTransfers076.q2 (8380219) 1 (-23))
def d2Transfer612Hi : ℚ := (d2LitsNearTransfers076.q2 (999) 125 (-3))
def d2Transfer612Cap : ℚ := (d2LitsNearTransfers076.q2 (118764375273470374378443) 1 (-79))
def d2Transfer612C0 : ℚ := (d2LitsNearTransfers076.q2 (3) 275 (-5))
def d2Transfer612S0 : ℚ := (d2LitsNearTransfers076.q2 (-1) 1 (0))
def d2Transfer612C1 : ℚ := (d2LitsNearTransfers076.q2 (-5) 11 (-4))
def d2Transfer612S1 : ℚ := (d2LitsNearTransfers076.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer612Arithmetic : weightedUpper d2Transfer612C0 d2Log174Lo d2Log174Hi + weightedUpper d2Transfer612C1 d2Log0Lo d2Log0Hi ≤ d2Transfer612Cap := by decide +kernel
theorem d2Transfer612Bound : ∀ x ∈ Set.Icc ((d2Transfer612Lo:ℚ):ℝ) ((d2Transfer612Hi:ℚ):ℝ), ((d2Transfer612C0:ℚ):ℝ)*Real.log |x-((d2Transfer612S0:ℚ):ℝ)| + ((d2Transfer612C1:ℚ):ℝ)*Real.log |x-((d2Transfer612S1:ℚ):ℝ)| ≤ ((d2Transfer612Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer612S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer612S0,d2Transfer612Lo,d2Transfer612Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer612C0 then |x-((d2Transfer612S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2Transfer612S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer612S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer612S0,d2Transfer612Lo,d2Transfer612Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer612C0,d2Log174Q,d2Transfer612S0,d2Transfer612Lo,d2Transfer612Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer612C0 d2Transfer612S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have hn1 : x-((d2Transfer612S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer612S1,d2Transfer612Lo,d2Transfer612Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer612C1 then |x-((d2Transfer612S1:ℚ):ℝ)| ≤ ((d2Log0Q:ℚ):ℝ) else ((d2Log0Q:ℚ):ℝ) ≤ |x-((d2Transfer612S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer612S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer612S1,d2Transfer612Lo,d2Transfer612Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer612C1,d2Log0Q,d2Transfer612S1,d2Transfer612Lo,d2Transfer612Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer612C1 d2Transfer612S1 d2Log0Q d2Log0Lo d2Log0Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log0Bounds
  have har : (((weightedUpper d2Transfer612C0 d2Log174Lo d2Log174Hi:ℚ):ℝ) + ((weightedUpper d2Transfer612C1 d2Log0Lo d2Log0Hi:ℚ):ℝ)) ≤ ((d2Transfer612Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer612Arithmetic
  linarith
#print axioms d2Transfer612Arithmetic
#print axioms d2Transfer612Bound
def d2Transfer613Lo : ℚ := (d2LitsNearTransfers076.q2 (999) 125 (-3))
def d2Transfer613Hi : ℚ := (d2LitsNearTransfers076.q2 (16760439) 1 (-24))
def d2Transfer613Cap : ℚ := (d2LitsNearTransfers076.q2 (2093397711619402323551) 1 (-80))
def d2Transfer613C0 : ℚ := (d2LitsNearTransfers076.q2 (1) 25 (-4))
def d2Transfer613S0 : ℚ := (d2LitsNearTransfers076.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer613Arithmetic : weightedUpper d2Transfer613C0 d2Log175Lo d2Log175Hi ≤ d2Transfer613Cap := by decide +kernel
theorem d2Transfer613Bound : ∀ x ∈ Set.Icc ((d2Transfer613Lo:ℚ):ℝ) ((d2Transfer613Hi:ℚ):ℝ), ((d2Transfer613C0:ℚ):ℝ)*Real.log |x-((d2Transfer613S0:ℚ):ℝ)| ≤ ((d2Transfer613Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer613S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer613S0,d2Transfer613Lo,d2Transfer613Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer613C0 then |x-((d2Transfer613S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2Transfer613S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer613S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer613S0,d2Transfer613Lo,d2Transfer613Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer613C0,d2Log175Q,d2Transfer613S0,d2Transfer613Lo,d2Transfer613Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer613C0 d2Transfer613S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2Transfer613C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2Transfer613Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer613Arithmetic
  linarith
#print axioms d2Transfer613Arithmetic
#print axioms d2Transfer613Bound
def d2Transfer614Lo : ℚ := (d2LitsNearTransfers076.q2 (999) 125 (-3))
def d2Transfer614Hi : ℚ := (d2LitsNearTransfers076.q2 (16760439) 1 (-24))
def d2Transfer614Cap : ℚ := (d2LitsNearTransfers076.q2 (2093397292705472140895) 1 (-80))
def d2Transfer614C0 : ℚ := (d2LitsNearTransfers076.q2 (1) 25 (-4))
def d2Transfer614S0 : ℚ := (d2LitsNearTransfers076.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer614Arithmetic : weightedUpper d2Transfer614C0 d2Log175Lo d2Log175Hi ≤ d2Transfer614Cap := by decide +kernel
theorem d2Transfer614Bound : ∀ x ∈ Set.Icc ((d2Transfer614Lo:ℚ):ℝ) ((d2Transfer614Hi:ℚ):ℝ), ((d2Transfer614C0:ℚ):ℝ)*Real.log |x-((d2Transfer614S0:ℚ):ℝ)| ≤ ((d2Transfer614Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer614S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer614S0,d2Transfer614Lo,d2Transfer614Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer614C0 then |x-((d2Transfer614S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2Transfer614S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer614S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer614S0,d2Transfer614Lo,d2Transfer614Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer614C0,d2Log175Q,d2Transfer614S0,d2Transfer614Lo,d2Transfer614Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer614C0 d2Transfer614S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2Transfer614C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2Transfer614Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer614Arithmetic
  linarith
#print axioms d2Transfer614Arithmetic
#print axioms d2Transfer614Bound
def d2Transfer615Lo : ℚ := (d2LitsNearTransfers076.q2 (16760439) 1 (-24))
def d2Transfer615Hi : ℚ := (d2LitsNearTransfers076.q2 (1023) 1 (-10))
def d2Transfer615Cap : ℚ := (d2LitsNearTransfers076.q2 (1046716563706371062717) 1 (-79))
def d2Transfer615C0 : ℚ := (d2LitsNearTransfers076.q2 (1) 25 (-4))
def d2Transfer615S0 : ℚ := (d2LitsNearTransfers076.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer615Arithmetic : weightedUpper d2Transfer615C0 d2Log176Lo d2Log176Hi ≤ d2Transfer615Cap := by decide +kernel
theorem d2Transfer615Bound : ∀ x ∈ Set.Icc ((d2Transfer615Lo:ℚ):ℝ) ((d2Transfer615Hi:ℚ):ℝ), ((d2Transfer615C0:ℚ):ℝ)*Real.log |x-((d2Transfer615S0:ℚ):ℝ)| ≤ ((d2Transfer615Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer615S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer615S0,d2Transfer615Lo,d2Transfer615Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer615C0 then |x-((d2Transfer615S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2Transfer615S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer615S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer615S0,d2Transfer615Lo,d2Transfer615Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers076.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer615C0,d2Log176Q,d2Transfer615S0,d2Transfer615Lo,d2Transfer615Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer615C0 d2Transfer615S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2Transfer615C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2Transfer615Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer615Arithmetic
  linarith
#print axioms d2Transfer615Arithmetic
#print axioms d2Transfer615Bound
end CatalanMeasure.GenD.Signed.Data.Cells

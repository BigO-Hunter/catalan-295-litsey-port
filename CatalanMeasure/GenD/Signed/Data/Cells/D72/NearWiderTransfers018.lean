module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache008
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers018
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers018
open D72.LogTransfer
def d2WiderTransfer144Lo : ℚ := (d2LitsNearWiderTransfers018.q2 (668067511) 1 (-30))
def d2WiderTransfer144Hi : ℚ := (d2LitsNearWiderTransfers018.q2 (1337812743) 1 (-31))
def d2WiderTransfer144Cap : ℚ := (d2LitsNearWiderTransfers018.q2 (9399377577934826708217) 1 (-79))
def d2WiderTransfer144C0 : ℚ := (d2LitsNearWiderTransfers018.q2 (1) 1 (-5))
def d2WiderTransfer144S0 : ℚ := (d2LitsNearWiderTransfers018.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer144Arithmetic : weightedUpper d2WiderTransfer144C0 d2Log138Lo d2Log138Hi ≤ d2WiderTransfer144Cap := by decide +kernel
theorem d2WiderTransfer144Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer144Lo:ℚ):ℝ) ((d2WiderTransfer144Hi:ℚ):ℝ), ((d2WiderTransfer144C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer144S0:ℚ):ℝ)| ≤ ((d2WiderTransfer144Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer144S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer144S0,d2WiderTransfer144Lo,d2WiderTransfer144Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer144C0 then |x-((d2WiderTransfer144S0:ℚ):ℝ)| ≤ ((d2Log138Q:ℚ):ℝ) else ((d2Log138Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer144S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer144S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer144S0,d2WiderTransfer144Lo,d2WiderTransfer144Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer144C0,d2Log138Q,d2WiderTransfer144S0,d2WiderTransfer144Lo,d2WiderTransfer144Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer144C0 d2WiderTransfer144S0 d2Log138Q d2Log138Lo d2Log138Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log138Bounds
  have har : (((weightedUpper d2WiderTransfer144C0 d2Log138Lo d2Log138Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer144Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer144Arithmetic
  linarith
#print axioms d2WiderTransfer144Arithmetic
#print axioms d2WiderTransfer144Bound
def d2WiderTransfer145Lo : ℚ := (d2LitsNearWiderTransfers018.q2 (668067511) 1 (-30))
def d2WiderTransfer145Hi : ℚ := (d2LitsNearWiderTransfers018.q2 (1337812743) 1 (-31))
def d2WiderTransfer145Cap : ℚ := (d2LitsNearWiderTransfers018.q2 (17581796239080580390137) 1 (-79))
def d2WiderTransfer145C0 : ℚ := (d2LitsNearWiderTransfers018.q2 (1) 11 (-5))
def d2WiderTransfer145S0 : ℚ := (d2LitsNearWiderTransfers018.q2 (-1) 1 (0))
def d2WiderTransfer145C1 : ℚ := (d2LitsNearWiderTransfers018.q2 (-5) 11 (-4))
def d2WiderTransfer145S1 : ℚ := (d2LitsNearWiderTransfers018.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer145Arithmetic : weightedUpper d2WiderTransfer145C0 d2Log138Lo d2Log138Hi + weightedUpper d2WiderTransfer145C1 d2Log36Lo d2Log36Hi ≤ d2WiderTransfer145Cap := by decide +kernel
theorem d2WiderTransfer145Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer145Lo:ℚ):ℝ) ((d2WiderTransfer145Hi:ℚ):ℝ), ((d2WiderTransfer145C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer145S0:ℚ):ℝ)| + ((d2WiderTransfer145C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer145S1:ℚ):ℝ)| ≤ ((d2WiderTransfer145Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer145S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer145S0,d2WiderTransfer145Lo,d2WiderTransfer145Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer145C0 then |x-((d2WiderTransfer145S0:ℚ):ℝ)| ≤ ((d2Log138Q:ℚ):ℝ) else ((d2Log138Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer145S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer145S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer145S0,d2WiderTransfer145Lo,d2WiderTransfer145Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer145C0,d2Log138Q,d2WiderTransfer145S0,d2WiderTransfer145Lo,d2WiderTransfer145Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer145C0 d2WiderTransfer145S0 d2Log138Q d2Log138Lo d2Log138Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log138Bounds
  have hn1 : x-((d2WiderTransfer145S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer145S1,d2WiderTransfer145Lo,d2WiderTransfer145Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer145C1 then |x-((d2WiderTransfer145S1:ℚ):ℝ)| ≤ ((d2Log36Q:ℚ):ℝ) else ((d2Log36Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer145S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer145S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer145S1,d2WiderTransfer145Lo,d2WiderTransfer145Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer145C1,d2Log36Q,d2WiderTransfer145S1,d2WiderTransfer145Lo,d2WiderTransfer145Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer145C1 d2WiderTransfer145S1 d2Log36Q d2Log36Lo d2Log36Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log36Bounds
  have har : (((weightedUpper d2WiderTransfer145C0 d2Log138Lo d2Log138Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer145C1 d2Log36Lo d2Log36Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer145Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer145Arithmetic
  linarith
#print axioms d2WiderTransfer145Arithmetic
#print axioms d2WiderTransfer145Bound
def d2WiderTransfer146Lo : ℚ := (d2LitsNearWiderTransfers018.q2 (1337812743) 1 (-31))
def d2WiderTransfer146Hi : ℚ := (d2LitsNearWiderTransfers018.q2 (41859077) 1 (-26))
def d2WiderTransfer146Cap : ℚ := (d2LitsNearWiderTransfers018.q2 (149892803860600690063) 1 (-76))
def d2WiderTransfer146C0 : ℚ := (d2LitsNearWiderTransfers018.q2 (1) 25 (-4))
def d2WiderTransfer146S0 : ℚ := (d2LitsNearWiderTransfers018.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer146Arithmetic : weightedUpper d2WiderTransfer146C0 d2Log139Lo d2Log139Hi ≤ d2WiderTransfer146Cap := by decide +kernel
theorem d2WiderTransfer146Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer146Lo:ℚ):ℝ) ((d2WiderTransfer146Hi:ℚ):ℝ), ((d2WiderTransfer146C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer146S0:ℚ):ℝ)| ≤ ((d2WiderTransfer146Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer146S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer146S0,d2WiderTransfer146Lo,d2WiderTransfer146Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer146C0 then |x-((d2WiderTransfer146S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer146S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer146S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer146S0,d2WiderTransfer146Lo,d2WiderTransfer146Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer146C0,d2Log139Q,d2WiderTransfer146S0,d2WiderTransfer146Lo,d2WiderTransfer146Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer146C0 d2WiderTransfer146S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have har : (((weightedUpper d2WiderTransfer146C0 d2Log139Lo d2Log139Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer146Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer146Arithmetic
  linarith
#print axioms d2WiderTransfer146Arithmetic
#print axioms d2WiderTransfer146Bound
def d2WiderTransfer147Lo : ℚ := (d2LitsNearWiderTransfers018.q2 (1337812743) 1 (-31))
def d2WiderTransfer147Hi : ℚ := (d2LitsNearWiderTransfers018.q2 (41859077) 1 (-26))
def d2WiderTransfer147Cap : ℚ := (d2LitsNearWiderTransfers018.q2 (228036564400334149007) 1 (-76))
def d2WiderTransfer147C0 : ℚ := (d2LitsNearWiderTransfers018.q2 (1) 275 (-4))
def d2WiderTransfer147S0 : ℚ := (d2LitsNearWiderTransfers018.q2 (-1) 1 (0))
def d2WiderTransfer147C1 : ℚ := (d2LitsNearWiderTransfers018.q2 (-1) 55 (-3))
def d2WiderTransfer147S1 : ℚ := (d2LitsNearWiderTransfers018.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer147Arithmetic : weightedUpper d2WiderTransfer147C0 d2Log139Lo d2Log139Hi + weightedUpper d2WiderTransfer147C1 d2Log35Lo d2Log35Hi ≤ d2WiderTransfer147Cap := by decide +kernel
theorem d2WiderTransfer147Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer147Lo:ℚ):ℝ) ((d2WiderTransfer147Hi:ℚ):ℝ), ((d2WiderTransfer147C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer147S0:ℚ):ℝ)| + ((d2WiderTransfer147C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer147S1:ℚ):ℝ)| ≤ ((d2WiderTransfer147Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer147S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer147S0,d2WiderTransfer147Lo,d2WiderTransfer147Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer147C0 then |x-((d2WiderTransfer147S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer147S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer147S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer147S0,d2WiderTransfer147Lo,d2WiderTransfer147Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer147C0,d2Log139Q,d2WiderTransfer147S0,d2WiderTransfer147Lo,d2WiderTransfer147Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer147C0 d2WiderTransfer147S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have hn1 : x-((d2WiderTransfer147S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer147S1,d2WiderTransfer147Lo,d2WiderTransfer147Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer147C1 then |x-((d2WiderTransfer147S1:ℚ):ℝ)| ≤ ((d2Log35Q:ℚ):ℝ) else ((d2Log35Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer147S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer147S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer147S1,d2WiderTransfer147Lo,d2WiderTransfer147Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer147C1,d2Log35Q,d2WiderTransfer147S1,d2WiderTransfer147Lo,d2WiderTransfer147Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer147C1 d2WiderTransfer147S1 d2Log35Q d2Log35Lo d2Log35Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log35Bounds
  have har : (((weightedUpper d2WiderTransfer147C0 d2Log139Lo d2Log139Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer147C1 d2Log35Lo d2Log35Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer147Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer147Arithmetic
  linarith
#print axioms d2WiderTransfer147Arithmetic
#print axioms d2WiderTransfer147Bound
def d2WiderTransfer148Lo : ℚ := (d2LitsNearWiderTransfers018.q2 (1337812743) 1 (-31))
def d2WiderTransfer148Hi : ℚ := (d2LitsNearWiderTransfers018.q2 (41859077) 1 (-26))
def d2WiderTransfer148Cap : ℚ := (d2LitsNearWiderTransfers018.q2 (1179477945051769181583) 1 (-76))
def d2WiderTransfer148C0 : ℚ := (d2LitsNearWiderTransfers018.q2 (1) 1 (-5))
def d2WiderTransfer148S0 : ℚ := (d2LitsNearWiderTransfers018.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer148Arithmetic : weightedUpper d2WiderTransfer148C0 d2Log139Lo d2Log139Hi ≤ d2WiderTransfer148Cap := by decide +kernel
theorem d2WiderTransfer148Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer148Lo:ℚ):ℝ) ((d2WiderTransfer148Hi:ℚ):ℝ), ((d2WiderTransfer148C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer148S0:ℚ):ℝ)| ≤ ((d2WiderTransfer148Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer148S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer148S0,d2WiderTransfer148Lo,d2WiderTransfer148Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer148C0 then |x-((d2WiderTransfer148S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer148S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer148S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer148S0,d2WiderTransfer148Lo,d2WiderTransfer148Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer148C0,d2Log139Q,d2WiderTransfer148S0,d2WiderTransfer148Lo,d2WiderTransfer148Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer148C0 d2WiderTransfer148S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have har : (((weightedUpper d2WiderTransfer148C0 d2Log139Lo d2Log139Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer148Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer148Arithmetic
  linarith
#print axioms d2WiderTransfer148Arithmetic
#print axioms d2WiderTransfer148Bound
def d2WiderTransfer149Lo : ℚ := (d2LitsNearWiderTransfers018.q2 (1337812743) 1 (-31))
def d2WiderTransfer149Hi : ℚ := (d2LitsNearWiderTransfers018.q2 (41859077) 1 (-26))
def d2WiderTransfer149Cap : ℚ := (d2LitsNearWiderTransfers018.q2 (2202280277694988391823) 1 (-76))
def d2WiderTransfer149C0 : ℚ := (d2LitsNearWiderTransfers018.q2 (1) 11 (-5))
def d2WiderTransfer149S0 : ℚ := (d2LitsNearWiderTransfers018.q2 (-1) 1 (0))
def d2WiderTransfer149C1 : ℚ := (d2LitsNearWiderTransfers018.q2 (-5) 11 (-4))
def d2WiderTransfer149S1 : ℚ := (d2LitsNearWiderTransfers018.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer149Arithmetic : weightedUpper d2WiderTransfer149C0 d2Log139Lo d2Log139Hi + weightedUpper d2WiderTransfer149C1 d2Log35Lo d2Log35Hi ≤ d2WiderTransfer149Cap := by decide +kernel
theorem d2WiderTransfer149Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer149Lo:ℚ):ℝ) ((d2WiderTransfer149Hi:ℚ):ℝ), ((d2WiderTransfer149C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer149S0:ℚ):ℝ)| + ((d2WiderTransfer149C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer149S1:ℚ):ℝ)| ≤ ((d2WiderTransfer149Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer149S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer149S0,d2WiderTransfer149Lo,d2WiderTransfer149Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer149C0 then |x-((d2WiderTransfer149S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer149S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer149S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer149S0,d2WiderTransfer149Lo,d2WiderTransfer149Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer149C0,d2Log139Q,d2WiderTransfer149S0,d2WiderTransfer149Lo,d2WiderTransfer149Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer149C0 d2WiderTransfer149S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have hn1 : x-((d2WiderTransfer149S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer149S1,d2WiderTransfer149Lo,d2WiderTransfer149Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer149C1 then |x-((d2WiderTransfer149S1:ℚ):ℝ)| ≤ ((d2Log35Q:ℚ):ℝ) else ((d2Log35Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer149S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer149S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer149S1,d2WiderTransfer149Lo,d2WiderTransfer149Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer149C1,d2Log35Q,d2WiderTransfer149S1,d2WiderTransfer149Lo,d2WiderTransfer149Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer149C1 d2WiderTransfer149S1 d2Log35Q d2Log35Lo d2Log35Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log35Bounds
  have har : (((weightedUpper d2WiderTransfer149C0 d2Log139Lo d2Log139Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer149C1 d2Log35Lo d2Log35Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer149Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer149Arithmetic
  linarith
#print axioms d2WiderTransfer149Arithmetic
#print axioms d2WiderTransfer149Bound
def d2WiderTransfer150Lo : ℚ := (d2LitsNearWiderTransfers018.q2 (41859077) 1 (-26))
def d2WiderTransfer150Hi : ℚ := (d2LitsNearWiderTransfers018.q2 (1341168185) 1 (-31))
def d2WiderTransfer150Cap : ℚ := (d2LitsNearWiderTransfers018.q2 (2471324106762310774949) 1 (-80))
def d2WiderTransfer150C0 : ℚ := (d2LitsNearWiderTransfers018.q2 (1) 25 (-4))
def d2WiderTransfer150S0 : ℚ := (d2LitsNearWiderTransfers018.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer150Arithmetic : weightedUpper d2WiderTransfer150C0 d2Log140Lo d2Log140Hi ≤ d2WiderTransfer150Cap := by decide +kernel
theorem d2WiderTransfer150Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer150Lo:ℚ):ℝ) ((d2WiderTransfer150Hi:ℚ):ℝ), ((d2WiderTransfer150C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer150S0:ℚ):ℝ)| ≤ ((d2WiderTransfer150Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer150S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer150S0,d2WiderTransfer150Lo,d2WiderTransfer150Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer150C0 then |x-((d2WiderTransfer150S0:ℚ):ℝ)| ≤ ((d2Log140Q:ℚ):ℝ) else ((d2Log140Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer150S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer150S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer150S0,d2WiderTransfer150Lo,d2WiderTransfer150Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer150C0,d2Log140Q,d2WiderTransfer150S0,d2WiderTransfer150Lo,d2WiderTransfer150Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer150C0 d2WiderTransfer150S0 d2Log140Q d2Log140Lo d2Log140Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log140Bounds
  have har : (((weightedUpper d2WiderTransfer150C0 d2Log140Lo d2Log140Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer150Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer150Arithmetic
  linarith
#print axioms d2WiderTransfer150Arithmetic
#print axioms d2WiderTransfer150Bound
def d2WiderTransfer151Lo : ℚ := (d2LitsNearWiderTransfers018.q2 (41859077) 1 (-26))
def d2WiderTransfer151Hi : ℚ := (d2LitsNearWiderTransfers018.q2 (1341168185) 1 (-31))
def d2WiderTransfer151Cap : ℚ := (d2LitsNearWiderTransfers018.q2 (3721624275398046118053) 1 (-80))
def d2WiderTransfer151C0 : ℚ := (d2LitsNearWiderTransfers018.q2 (1) 275 (-4))
def d2WiderTransfer151S0 : ℚ := (d2LitsNearWiderTransfers018.q2 (-1) 1 (0))
def d2WiderTransfer151C1 : ℚ := (d2LitsNearWiderTransfers018.q2 (-1) 55 (-3))
def d2WiderTransfer151S1 : ℚ := (d2LitsNearWiderTransfers018.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer151Arithmetic : weightedUpper d2WiderTransfer151C0 d2Log140Lo d2Log140Hi + weightedUpper d2WiderTransfer151C1 d2Log34Lo d2Log34Hi ≤ d2WiderTransfer151Cap := by decide +kernel
theorem d2WiderTransfer151Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer151Lo:ℚ):ℝ) ((d2WiderTransfer151Hi:ℚ):ℝ), ((d2WiderTransfer151C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer151S0:ℚ):ℝ)| + ((d2WiderTransfer151C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer151S1:ℚ):ℝ)| ≤ ((d2WiderTransfer151Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer151S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer151S0,d2WiderTransfer151Lo,d2WiderTransfer151Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer151C0 then |x-((d2WiderTransfer151S0:ℚ):ℝ)| ≤ ((d2Log140Q:ℚ):ℝ) else ((d2Log140Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer151S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer151S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer151S0,d2WiderTransfer151Lo,d2WiderTransfer151Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer151C0,d2Log140Q,d2WiderTransfer151S0,d2WiderTransfer151Lo,d2WiderTransfer151Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer151C0 d2WiderTransfer151S0 d2Log140Q d2Log140Lo d2Log140Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log140Bounds
  have hn1 : x-((d2WiderTransfer151S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer151S1,d2WiderTransfer151Lo,d2WiderTransfer151Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer151C1 then |x-((d2WiderTransfer151S1:ℚ):ℝ)| ≤ ((d2Log34Q:ℚ):ℝ) else ((d2Log34Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer151S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer151S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer151S1,d2WiderTransfer151Lo,d2WiderTransfer151Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers018.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer151C1,d2Log34Q,d2WiderTransfer151S1,d2WiderTransfer151Lo,d2WiderTransfer151Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer151C1 d2WiderTransfer151S1 d2Log34Q d2Log34Lo d2Log34Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log34Bounds
  have har : (((weightedUpper d2WiderTransfer151C0 d2Log140Lo d2Log140Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer151C1 d2Log34Lo d2Log34Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer151Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer151Arithmetic
  linarith
#print axioms d2WiderTransfer151Arithmetic
#print axioms d2WiderTransfer151Bound
end CatalanMeasure.GenD.Signed.Data.Cells

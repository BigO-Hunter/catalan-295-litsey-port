module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers018
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers018
open D72.LogTransfer
def d2Transfer144Lo : ℚ := (d2LitsNearTransfers018.q2 (44962675) 1 (-28))
def d2Transfer144Hi : ℚ := (d2LitsNearTransfers018.q2 (11660099) 1 (-26))
def d2Transfer144Cap : ℚ := (d2LitsNearTransfers018.q2 (16281318465) 1 (-40))
def d2Transfer144C0 : ℚ := (d2LitsNearTransfers018.q2 (1) 1 (-5))
def d2Transfer144S0 : ℚ := (d2LitsNearTransfers018.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer144Arithmetic : weightedUpper d2Transfer144C0 d2Log103Lo d2Log103Hi ≤ d2Transfer144Cap := by decide +kernel
theorem d2Transfer144Bound : ∀ x ∈ Set.Icc ((d2Transfer144Lo:ℚ):ℝ) ((d2Transfer144Hi:ℚ):ℝ), ((d2Transfer144C0:ℚ):ℝ)*Real.log |x-((d2Transfer144S0:ℚ):ℝ)| ≤ ((d2Transfer144Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer144S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer144S0,d2Transfer144Lo,d2Transfer144Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer144C0 then |x-((d2Transfer144S0:ℚ):ℝ)| ≤ ((d2Log103Q:ℚ):ℝ) else ((d2Log103Q:ℚ):ℝ) ≤ |x-((d2Transfer144S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer144S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer144S0,d2Transfer144Lo,d2Transfer144Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer144C0,d2Log103Q,d2Transfer144S0,d2Transfer144Lo,d2Transfer144Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer144C0 d2Transfer144S0 d2Log103Q d2Log103Lo d2Log103Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log103Bounds
  have har : (((weightedUpper d2Transfer144C0 d2Log103Lo d2Log103Hi:ℚ):ℝ)) ≤ ((d2Transfer144Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer144Arithmetic
  linarith
#print axioms d2Transfer144Arithmetic
#print axioms d2Transfer144Bound
def d2Transfer145Lo : ℚ := (d2LitsNearTransfers018.q2 (44962675) 1 (-28))
def d2Transfer145Hi : ℚ := (d2LitsNearTransfers018.q2 (11660099) 1 (-26))
def d2Transfer145Cap : ℚ := (d2LitsNearTransfers018.q2 (31165051305) 1 (-40))
def d2Transfer145C0 : ℚ := (d2LitsNearTransfers018.q2 (1) 11 (-5))
def d2Transfer145S0 : ℚ := (d2LitsNearTransfers018.q2 (-1) 1 (0))
def d2Transfer145C1 : ℚ := (d2LitsNearTransfers018.q2 (-5) 11 (-4))
def d2Transfer145S1 : ℚ := (d2LitsNearTransfers018.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer145Arithmetic : weightedUpper d2Transfer145C0 d2Log103Lo d2Log103Hi + weightedUpper d2Transfer145C1 d2Log71Lo d2Log71Hi ≤ d2Transfer145Cap := by decide +kernel
theorem d2Transfer145Bound : ∀ x ∈ Set.Icc ((d2Transfer145Lo:ℚ):ℝ) ((d2Transfer145Hi:ℚ):ℝ), ((d2Transfer145C0:ℚ):ℝ)*Real.log |x-((d2Transfer145S0:ℚ):ℝ)| + ((d2Transfer145C1:ℚ):ℝ)*Real.log |x-((d2Transfer145S1:ℚ):ℝ)| ≤ ((d2Transfer145Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer145S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer145S0,d2Transfer145Lo,d2Transfer145Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer145C0 then |x-((d2Transfer145S0:ℚ):ℝ)| ≤ ((d2Log103Q:ℚ):ℝ) else ((d2Log103Q:ℚ):ℝ) ≤ |x-((d2Transfer145S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer145S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer145S0,d2Transfer145Lo,d2Transfer145Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer145C0,d2Log103Q,d2Transfer145S0,d2Transfer145Lo,d2Transfer145Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer145C0 d2Transfer145S0 d2Log103Q d2Log103Lo d2Log103Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log103Bounds
  have hn1 : x-((d2Transfer145S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer145S1,d2Transfer145Lo,d2Transfer145Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer145C1 then |x-((d2Transfer145S1:ℚ):ℝ)| ≤ ((d2Log71Q:ℚ):ℝ) else ((d2Log71Q:ℚ):ℝ) ≤ |x-((d2Transfer145S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer145S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer145S1,d2Transfer145Lo,d2Transfer145Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer145C1,d2Log71Q,d2Transfer145S1,d2Transfer145Lo,d2Transfer145Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer145C1 d2Transfer145S1 d2Log71Q d2Log71Lo d2Log71Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log71Bounds
  have har : (((weightedUpper d2Transfer145C0 d2Log103Lo d2Log103Hi:ℚ):ℝ) + ((weightedUpper d2Transfer145C1 d2Log71Lo d2Log71Hi:ℚ):ℝ)) ≤ ((d2Transfer145Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer145Arithmetic
  linarith
#print axioms d2Transfer145Arithmetic
#print axioms d2Transfer145Bound
def d2Transfer146Lo : ℚ := (d2LitsNearTransfers018.q2 (11660099) 1 (-26))
def d2Transfer146Hi : ℚ := (d2LitsNearTransfers018.q2 (24997919) 1 (-27))
def d2Transfer146Cap : ℚ := (d2LitsNearTransfers018.q2 (649441385) 1 (-39))
def d2Transfer146C0 : ℚ := (d2LitsNearTransfers018.q2 (1) 25 (-4))
def d2Transfer146S0 : ℚ := (d2LitsNearTransfers018.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer146Arithmetic : weightedUpper d2Transfer146C0 d2Log105Lo d2Log105Hi ≤ d2Transfer146Cap := by decide +kernel
theorem d2Transfer146Bound : ∀ x ∈ Set.Icc ((d2Transfer146Lo:ℚ):ℝ) ((d2Transfer146Hi:ℚ):ℝ), ((d2Transfer146C0:ℚ):ℝ)*Real.log |x-((d2Transfer146S0:ℚ):ℝ)| ≤ ((d2Transfer146Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer146S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer146S0,d2Transfer146Lo,d2Transfer146Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer146C0 then |x-((d2Transfer146S0:ℚ):ℝ)| ≤ ((d2Log105Q:ℚ):ℝ) else ((d2Log105Q:ℚ):ℝ) ≤ |x-((d2Transfer146S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer146S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer146S0,d2Transfer146Lo,d2Transfer146Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer146C0,d2Log105Q,d2Transfer146S0,d2Transfer146Lo,d2Transfer146Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer146C0 d2Transfer146S0 d2Log105Q d2Log105Lo d2Log105Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log105Bounds
  have har : (((weightedUpper d2Transfer146C0 d2Log105Lo d2Log105Hi:ℚ):ℝ)) ≤ ((d2Transfer146Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer146Arithmetic
  linarith
#print axioms d2Transfer146Arithmetic
#print axioms d2Transfer146Bound
def d2Transfer147Lo : ℚ := (d2LitsNearTransfers018.q2 (11660099) 1 (-26))
def d2Transfer147Hi : ℚ := (d2LitsNearTransfers018.q2 (24997919) 1 (-27))
def d2Transfer147Cap : ℚ := (d2LitsNearTransfers018.q2 (2436024149) 1 (-40))
def d2Transfer147C0 : ℚ := (d2LitsNearTransfers018.q2 (1) 275 (-4))
def d2Transfer147S0 : ℚ := (d2LitsNearTransfers018.q2 (-1) 1 (0))
def d2Transfer147C1 : ℚ := (d2LitsNearTransfers018.q2 (-1) 55 (-3))
def d2Transfer147S1 : ℚ := (d2LitsNearTransfers018.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer147Arithmetic : weightedUpper d2Transfer147C0 d2Log105Lo d2Log105Hi + weightedUpper d2Transfer147C1 d2Log69Lo d2Log69Hi ≤ d2Transfer147Cap := by decide +kernel
theorem d2Transfer147Bound : ∀ x ∈ Set.Icc ((d2Transfer147Lo:ℚ):ℝ) ((d2Transfer147Hi:ℚ):ℝ), ((d2Transfer147C0:ℚ):ℝ)*Real.log |x-((d2Transfer147S0:ℚ):ℝ)| + ((d2Transfer147C1:ℚ):ℝ)*Real.log |x-((d2Transfer147S1:ℚ):ℝ)| ≤ ((d2Transfer147Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer147S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer147S0,d2Transfer147Lo,d2Transfer147Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer147C0 then |x-((d2Transfer147S0:ℚ):ℝ)| ≤ ((d2Log105Q:ℚ):ℝ) else ((d2Log105Q:ℚ):ℝ) ≤ |x-((d2Transfer147S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer147S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer147S0,d2Transfer147Lo,d2Transfer147Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer147C0,d2Log105Q,d2Transfer147S0,d2Transfer147Lo,d2Transfer147Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer147C0 d2Transfer147S0 d2Log105Q d2Log105Lo d2Log105Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log105Bounds
  have hn1 : x-((d2Transfer147S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer147S1,d2Transfer147Lo,d2Transfer147Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer147C1 then |x-((d2Transfer147S1:ℚ):ℝ)| ≤ ((d2Log69Q:ℚ):ℝ) else ((d2Log69Q:ℚ):ℝ) ≤ |x-((d2Transfer147S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer147S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer147S1,d2Transfer147Lo,d2Transfer147Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer147C1,d2Log69Q,d2Transfer147S1,d2Transfer147Lo,d2Transfer147Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer147C1 d2Transfer147S1 d2Log69Q d2Log69Lo d2Log69Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log69Bounds
  have har : (((weightedUpper d2Transfer147C0 d2Log105Lo d2Log105Hi:ℚ):ℝ) + ((weightedUpper d2Transfer147C1 d2Log69Lo d2Log69Hi:ℚ):ℝ)) ≤ ((d2Transfer147Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer147Arithmetic
  linarith
#print axioms d2Transfer147Arithmetic
#print axioms d2Transfer147Bound
def d2Transfer148Lo : ℚ := (d2LitsNearTransfers018.q2 (11660099) 1 (-26))
def d2Transfer148Hi : ℚ := (d2LitsNearTransfers018.q2 (24997919) 1 (-27))
def d2Transfer148Cap : ℚ := (d2LitsNearTransfers018.q2 (16281318465) 1 (-40))
def d2Transfer148C0 : ℚ := (d2LitsNearTransfers018.q2 (1) 1 (-5))
def d2Transfer148S0 : ℚ := (d2LitsNearTransfers018.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer148Arithmetic : weightedUpper d2Transfer148C0 d2Log105Lo d2Log105Hi ≤ d2Transfer148Cap := by decide +kernel
theorem d2Transfer148Bound : ∀ x ∈ Set.Icc ((d2Transfer148Lo:ℚ):ℝ) ((d2Transfer148Hi:ℚ):ℝ), ((d2Transfer148C0:ℚ):ℝ)*Real.log |x-((d2Transfer148S0:ℚ):ℝ)| ≤ ((d2Transfer148Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer148S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer148S0,d2Transfer148Lo,d2Transfer148Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer148C0 then |x-((d2Transfer148S0:ℚ):ℝ)| ≤ ((d2Log105Q:ℚ):ℝ) else ((d2Log105Q:ℚ):ℝ) ≤ |x-((d2Transfer148S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer148S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer148S0,d2Transfer148Lo,d2Transfer148Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer148C0,d2Log105Q,d2Transfer148S0,d2Transfer148Lo,d2Transfer148Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer148C0 d2Transfer148S0 d2Log105Q d2Log105Lo d2Log105Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log105Bounds
  have har : (((weightedUpper d2Transfer148C0 d2Log105Lo d2Log105Hi:ℚ):ℝ)) ≤ ((d2Transfer148Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer148Arithmetic
  linarith
#print axioms d2Transfer148Arithmetic
#print axioms d2Transfer148Bound
def d2Transfer149Lo : ℚ := (d2LitsNearTransfers018.q2 (11660099) 1 (-26))
def d2Transfer149Hi : ℚ := (d2LitsNearTransfers018.q2 (24997919) 1 (-27))
def d2Transfer149Cap : ℚ := (d2LitsNearTransfers018.q2 (31165051305) 1 (-40))
def d2Transfer149C0 : ℚ := (d2LitsNearTransfers018.q2 (1) 11 (-5))
def d2Transfer149S0 : ℚ := (d2LitsNearTransfers018.q2 (-1) 1 (0))
def d2Transfer149C1 : ℚ := (d2LitsNearTransfers018.q2 (-5) 11 (-4))
def d2Transfer149S1 : ℚ := (d2LitsNearTransfers018.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer149Arithmetic : weightedUpper d2Transfer149C0 d2Log105Lo d2Log105Hi + weightedUpper d2Transfer149C1 d2Log69Lo d2Log69Hi ≤ d2Transfer149Cap := by decide +kernel
theorem d2Transfer149Bound : ∀ x ∈ Set.Icc ((d2Transfer149Lo:ℚ):ℝ) ((d2Transfer149Hi:ℚ):ℝ), ((d2Transfer149C0:ℚ):ℝ)*Real.log |x-((d2Transfer149S0:ℚ):ℝ)| + ((d2Transfer149C1:ℚ):ℝ)*Real.log |x-((d2Transfer149S1:ℚ):ℝ)| ≤ ((d2Transfer149Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer149S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer149S0,d2Transfer149Lo,d2Transfer149Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer149C0 then |x-((d2Transfer149S0:ℚ):ℝ)| ≤ ((d2Log105Q:ℚ):ℝ) else ((d2Log105Q:ℚ):ℝ) ≤ |x-((d2Transfer149S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer149S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer149S0,d2Transfer149Lo,d2Transfer149Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer149C0,d2Log105Q,d2Transfer149S0,d2Transfer149Lo,d2Transfer149Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer149C0 d2Transfer149S0 d2Log105Q d2Log105Lo d2Log105Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log105Bounds
  have hn1 : x-((d2Transfer149S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer149S1,d2Transfer149Lo,d2Transfer149Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer149C1 then |x-((d2Transfer149S1:ℚ):ℝ)| ≤ ((d2Log69Q:ℚ):ℝ) else ((d2Log69Q:ℚ):ℝ) ≤ |x-((d2Transfer149S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer149S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer149S1,d2Transfer149Lo,d2Transfer149Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer149C1,d2Log69Q,d2Transfer149S1,d2Transfer149Lo,d2Transfer149Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer149C1 d2Transfer149S1 d2Log69Q d2Log69Lo d2Log69Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log69Bounds
  have har : (((weightedUpper d2Transfer149C0 d2Log105Lo d2Log105Hi:ℚ):ℝ) + ((weightedUpper d2Transfer149C1 d2Log69Lo d2Log69Hi:ℚ):ℝ)) ≤ ((d2Transfer149Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer149Arithmetic
  linarith
#print axioms d2Transfer149Arithmetic
#print axioms d2Transfer149Bound
def d2Transfer150Lo : ℚ := (d2LitsNearTransfers018.q2 (24997919) 1 (-27))
def d2Transfer150Hi : ℚ := (d2LitsNearTransfers018.q2 (3334455) 1 (-24))
def d2Transfer150Cap : ℚ := (d2LitsNearTransfers018.q2 (649441385) 1 (-39))
def d2Transfer150C0 : ℚ := (d2LitsNearTransfers018.q2 (1) 25 (-4))
def d2Transfer150S0 : ℚ := (d2LitsNearTransfers018.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer150Arithmetic : weightedUpper d2Transfer150C0 d2Log106Lo d2Log106Hi ≤ d2Transfer150Cap := by decide +kernel
theorem d2Transfer150Bound : ∀ x ∈ Set.Icc ((d2Transfer150Lo:ℚ):ℝ) ((d2Transfer150Hi:ℚ):ℝ), ((d2Transfer150C0:ℚ):ℝ)*Real.log |x-((d2Transfer150S0:ℚ):ℝ)| ≤ ((d2Transfer150Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer150S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer150S0,d2Transfer150Lo,d2Transfer150Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer150C0 then |x-((d2Transfer150S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2Transfer150S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer150S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer150S0,d2Transfer150Lo,d2Transfer150Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer150C0,d2Log106Q,d2Transfer150S0,d2Transfer150Lo,d2Transfer150Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer150C0 d2Transfer150S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have har : (((weightedUpper d2Transfer150C0 d2Log106Lo d2Log106Hi:ℚ):ℝ)) ≤ ((d2Transfer150Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer150Arithmetic
  linarith
#print axioms d2Transfer150Arithmetic
#print axioms d2Transfer150Bound
def d2Transfer151Lo : ℚ := (d2LitsNearTransfers018.q2 (24997919) 1 (-27))
def d2Transfer151Hi : ℚ := (d2LitsNearTransfers018.q2 (3334455) 1 (-24))
def d2Transfer151Cap : ℚ := (d2LitsNearTransfers018.q2 (2436024149) 1 (-40))
def d2Transfer151C0 : ℚ := (d2LitsNearTransfers018.q2 (1) 275 (-4))
def d2Transfer151S0 : ℚ := (d2LitsNearTransfers018.q2 (-1) 1 (0))
def d2Transfer151C1 : ℚ := (d2LitsNearTransfers018.q2 (-1) 55 (-3))
def d2Transfer151S1 : ℚ := (d2LitsNearTransfers018.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer151Arithmetic : weightedUpper d2Transfer151C0 d2Log106Lo d2Log106Hi + weightedUpper d2Transfer151C1 d2Log68Lo d2Log68Hi ≤ d2Transfer151Cap := by decide +kernel
theorem d2Transfer151Bound : ∀ x ∈ Set.Icc ((d2Transfer151Lo:ℚ):ℝ) ((d2Transfer151Hi:ℚ):ℝ), ((d2Transfer151C0:ℚ):ℝ)*Real.log |x-((d2Transfer151S0:ℚ):ℝ)| + ((d2Transfer151C1:ℚ):ℝ)*Real.log |x-((d2Transfer151S1:ℚ):ℝ)| ≤ ((d2Transfer151Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer151S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer151S0,d2Transfer151Lo,d2Transfer151Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer151C0 then |x-((d2Transfer151S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2Transfer151S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer151S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer151S0,d2Transfer151Lo,d2Transfer151Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer151C0,d2Log106Q,d2Transfer151S0,d2Transfer151Lo,d2Transfer151Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer151C0 d2Transfer151S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have hn1 : x-((d2Transfer151S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer151S1,d2Transfer151Lo,d2Transfer151Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer151C1 then |x-((d2Transfer151S1:ℚ):ℝ)| ≤ ((d2Log68Q:ℚ):ℝ) else ((d2Log68Q:ℚ):ℝ) ≤ |x-((d2Transfer151S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer151S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer151S1,d2Transfer151Lo,d2Transfer151Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers018.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer151C1,d2Log68Q,d2Transfer151S1,d2Transfer151Lo,d2Transfer151Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer151C1 d2Transfer151S1 d2Log68Q d2Log68Lo d2Log68Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log68Bounds
  have har : (((weightedUpper d2Transfer151C0 d2Log106Lo d2Log106Hi:ℚ):ℝ) + ((weightedUpper d2Transfer151C1 d2Log68Lo d2Log68Hi:ℚ):ℝ)) ≤ ((d2Transfer151Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer151Arithmetic
  linarith
#print axioms d2Transfer151Arithmetic
#print axioms d2Transfer151Bound
end CatalanMeasure.GenD.Signed.Data.Cells

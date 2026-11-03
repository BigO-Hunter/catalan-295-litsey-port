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
namespace d2LitsNearTransfers017
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers017
open D72.LogTransfer
def d2Transfer136Lo : ℚ := (d2LitsNearTransfers017.q2 (41607233) 1 (-28))
def d2Transfer136Hi : ℚ := (d2LitsNearTransfers017.q2 (21642477) 1 (-27))
def d2Transfer136Cap : ℚ := (d2LitsNearTransfers017.q2 (16281318465) 1 (-40))
def d2Transfer136C0 : ℚ := (d2LitsNearTransfers017.q2 (1) 1 (-5))
def d2Transfer136S0 : ℚ := (d2LitsNearTransfers017.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer136Arithmetic : weightedUpper d2Transfer136C0 d2Log101Lo d2Log101Hi ≤ d2Transfer136Cap := by decide +kernel
theorem d2Transfer136Bound : ∀ x ∈ Set.Icc ((d2Transfer136Lo:ℚ):ℝ) ((d2Transfer136Hi:ℚ):ℝ), ((d2Transfer136C0:ℚ):ℝ)*Real.log |x-((d2Transfer136S0:ℚ):ℝ)| ≤ ((d2Transfer136Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer136S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer136S0,d2Transfer136Lo,d2Transfer136Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer136C0 then |x-((d2Transfer136S0:ℚ):ℝ)| ≤ ((d2Log101Q:ℚ):ℝ) else ((d2Log101Q:ℚ):ℝ) ≤ |x-((d2Transfer136S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer136S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer136S0,d2Transfer136Lo,d2Transfer136Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer136C0,d2Log101Q,d2Transfer136S0,d2Transfer136Lo,d2Transfer136Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer136C0 d2Transfer136S0 d2Log101Q d2Log101Lo d2Log101Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log101Bounds
  have har : (((weightedUpper d2Transfer136C0 d2Log101Lo d2Log101Hi:ℚ):ℝ)) ≤ ((d2Transfer136Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer136Arithmetic
  linarith
#print axioms d2Transfer136Arithmetic
#print axioms d2Transfer136Bound
def d2Transfer137Lo : ℚ := (d2LitsNearTransfers017.q2 (41607233) 1 (-28))
def d2Transfer137Hi : ℚ := (d2LitsNearTransfers017.q2 (21642477) 1 (-27))
def d2Transfer137Cap : ℚ := (d2LitsNearTransfers017.q2 (31165051305) 1 (-40))
def d2Transfer137C0 : ℚ := (d2LitsNearTransfers017.q2 (1) 11 (-5))
def d2Transfer137S0 : ℚ := (d2LitsNearTransfers017.q2 (-1) 1 (0))
def d2Transfer137C1 : ℚ := (d2LitsNearTransfers017.q2 (-5) 11 (-4))
def d2Transfer137S1 : ℚ := (d2LitsNearTransfers017.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer137Arithmetic : weightedUpper d2Transfer137C0 d2Log101Lo d2Log101Hi + weightedUpper d2Transfer137C1 d2Log73Lo d2Log73Hi ≤ d2Transfer137Cap := by decide +kernel
theorem d2Transfer137Bound : ∀ x ∈ Set.Icc ((d2Transfer137Lo:ℚ):ℝ) ((d2Transfer137Hi:ℚ):ℝ), ((d2Transfer137C0:ℚ):ℝ)*Real.log |x-((d2Transfer137S0:ℚ):ℝ)| + ((d2Transfer137C1:ℚ):ℝ)*Real.log |x-((d2Transfer137S1:ℚ):ℝ)| ≤ ((d2Transfer137Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer137S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer137S0,d2Transfer137Lo,d2Transfer137Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer137C0 then |x-((d2Transfer137S0:ℚ):ℝ)| ≤ ((d2Log101Q:ℚ):ℝ) else ((d2Log101Q:ℚ):ℝ) ≤ |x-((d2Transfer137S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer137S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer137S0,d2Transfer137Lo,d2Transfer137Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer137C0,d2Log101Q,d2Transfer137S0,d2Transfer137Lo,d2Transfer137Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer137C0 d2Transfer137S0 d2Log101Q d2Log101Lo d2Log101Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log101Bounds
  have hn1 : x-((d2Transfer137S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer137S1,d2Transfer137Lo,d2Transfer137Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer137C1 then |x-((d2Transfer137S1:ℚ):ℝ)| ≤ ((d2Log73Q:ℚ):ℝ) else ((d2Log73Q:ℚ):ℝ) ≤ |x-((d2Transfer137S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer137S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer137S1,d2Transfer137Lo,d2Transfer137Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer137C1,d2Log73Q,d2Transfer137S1,d2Transfer137Lo,d2Transfer137Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer137C1 d2Transfer137S1 d2Log73Q d2Log73Lo d2Log73Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log73Bounds
  have har : (((weightedUpper d2Transfer137C0 d2Log101Lo d2Log101Hi:ℚ):ℝ) + ((weightedUpper d2Transfer137C1 d2Log73Lo d2Log73Hi:ℚ):ℝ)) ≤ ((d2Transfer137Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer137Arithmetic
  linarith
#print axioms d2Transfer137Arithmetic
#print axioms d2Transfer137Bound
def d2Transfer138Lo : ℚ := (d2LitsNearTransfers017.q2 (21642477) 1 (-27))
def d2Transfer138Hi : ℚ := (d2LitsNearTransfers017.q2 (44962675) 1 (-28))
def d2Transfer138Cap : ℚ := (d2LitsNearTransfers017.q2 (649441385) 1 (-39))
def d2Transfer138C0 : ℚ := (d2LitsNearTransfers017.q2 (1) 25 (-4))
def d2Transfer138S0 : ℚ := (d2LitsNearTransfers017.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer138Arithmetic : weightedUpper d2Transfer138C0 d2Log102Lo d2Log102Hi ≤ d2Transfer138Cap := by decide +kernel
theorem d2Transfer138Bound : ∀ x ∈ Set.Icc ((d2Transfer138Lo:ℚ):ℝ) ((d2Transfer138Hi:ℚ):ℝ), ((d2Transfer138C0:ℚ):ℝ)*Real.log |x-((d2Transfer138S0:ℚ):ℝ)| ≤ ((d2Transfer138Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer138S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer138S0,d2Transfer138Lo,d2Transfer138Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer138C0 then |x-((d2Transfer138S0:ℚ):ℝ)| ≤ ((d2Log102Q:ℚ):ℝ) else ((d2Log102Q:ℚ):ℝ) ≤ |x-((d2Transfer138S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer138S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer138S0,d2Transfer138Lo,d2Transfer138Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer138C0,d2Log102Q,d2Transfer138S0,d2Transfer138Lo,d2Transfer138Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer138C0 d2Transfer138S0 d2Log102Q d2Log102Lo d2Log102Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log102Bounds
  have har : (((weightedUpper d2Transfer138C0 d2Log102Lo d2Log102Hi:ℚ):ℝ)) ≤ ((d2Transfer138Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer138Arithmetic
  linarith
#print axioms d2Transfer138Arithmetic
#print axioms d2Transfer138Bound
def d2Transfer139Lo : ℚ := (d2LitsNearTransfers017.q2 (21642477) 1 (-27))
def d2Transfer139Hi : ℚ := (d2LitsNearTransfers017.q2 (44962675) 1 (-28))
def d2Transfer139Cap : ℚ := (d2LitsNearTransfers017.q2 (2436024149) 1 (-40))
def d2Transfer139C0 : ℚ := (d2LitsNearTransfers017.q2 (1) 275 (-4))
def d2Transfer139S0 : ℚ := (d2LitsNearTransfers017.q2 (-1) 1 (0))
def d2Transfer139C1 : ℚ := (d2LitsNearTransfers017.q2 (-1) 55 (-3))
def d2Transfer139S1 : ℚ := (d2LitsNearTransfers017.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer139Arithmetic : weightedUpper d2Transfer139C0 d2Log102Lo d2Log102Hi + weightedUpper d2Transfer139C1 d2Log72Lo d2Log72Hi ≤ d2Transfer139Cap := by decide +kernel
theorem d2Transfer139Bound : ∀ x ∈ Set.Icc ((d2Transfer139Lo:ℚ):ℝ) ((d2Transfer139Hi:ℚ):ℝ), ((d2Transfer139C0:ℚ):ℝ)*Real.log |x-((d2Transfer139S0:ℚ):ℝ)| + ((d2Transfer139C1:ℚ):ℝ)*Real.log |x-((d2Transfer139S1:ℚ):ℝ)| ≤ ((d2Transfer139Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer139S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer139S0,d2Transfer139Lo,d2Transfer139Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer139C0 then |x-((d2Transfer139S0:ℚ):ℝ)| ≤ ((d2Log102Q:ℚ):ℝ) else ((d2Log102Q:ℚ):ℝ) ≤ |x-((d2Transfer139S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer139S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer139S0,d2Transfer139Lo,d2Transfer139Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer139C0,d2Log102Q,d2Transfer139S0,d2Transfer139Lo,d2Transfer139Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer139C0 d2Transfer139S0 d2Log102Q d2Log102Lo d2Log102Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log102Bounds
  have hn1 : x-((d2Transfer139S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer139S1,d2Transfer139Lo,d2Transfer139Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer139C1 then |x-((d2Transfer139S1:ℚ):ℝ)| ≤ ((d2Log72Q:ℚ):ℝ) else ((d2Log72Q:ℚ):ℝ) ≤ |x-((d2Transfer139S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer139S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer139S1,d2Transfer139Lo,d2Transfer139Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer139C1,d2Log72Q,d2Transfer139S1,d2Transfer139Lo,d2Transfer139Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer139C1 d2Transfer139S1 d2Log72Q d2Log72Lo d2Log72Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log72Bounds
  have har : (((weightedUpper d2Transfer139C0 d2Log102Lo d2Log102Hi:ℚ):ℝ) + ((weightedUpper d2Transfer139C1 d2Log72Lo d2Log72Hi:ℚ):ℝ)) ≤ ((d2Transfer139Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer139Arithmetic
  linarith
#print axioms d2Transfer139Arithmetic
#print axioms d2Transfer139Bound
def d2Transfer140Lo : ℚ := (d2LitsNearTransfers017.q2 (21642477) 1 (-27))
def d2Transfer140Hi : ℚ := (d2LitsNearTransfers017.q2 (44962675) 1 (-28))
def d2Transfer140Cap : ℚ := (d2LitsNearTransfers017.q2 (16281318465) 1 (-40))
def d2Transfer140C0 : ℚ := (d2LitsNearTransfers017.q2 (1) 1 (-5))
def d2Transfer140S0 : ℚ := (d2LitsNearTransfers017.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer140Arithmetic : weightedUpper d2Transfer140C0 d2Log102Lo d2Log102Hi ≤ d2Transfer140Cap := by decide +kernel
theorem d2Transfer140Bound : ∀ x ∈ Set.Icc ((d2Transfer140Lo:ℚ):ℝ) ((d2Transfer140Hi:ℚ):ℝ), ((d2Transfer140C0:ℚ):ℝ)*Real.log |x-((d2Transfer140S0:ℚ):ℝ)| ≤ ((d2Transfer140Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer140S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer140S0,d2Transfer140Lo,d2Transfer140Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer140C0 then |x-((d2Transfer140S0:ℚ):ℝ)| ≤ ((d2Log102Q:ℚ):ℝ) else ((d2Log102Q:ℚ):ℝ) ≤ |x-((d2Transfer140S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer140S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer140S0,d2Transfer140Lo,d2Transfer140Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer140C0,d2Log102Q,d2Transfer140S0,d2Transfer140Lo,d2Transfer140Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer140C0 d2Transfer140S0 d2Log102Q d2Log102Lo d2Log102Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log102Bounds
  have har : (((weightedUpper d2Transfer140C0 d2Log102Lo d2Log102Hi:ℚ):ℝ)) ≤ ((d2Transfer140Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer140Arithmetic
  linarith
#print axioms d2Transfer140Arithmetic
#print axioms d2Transfer140Bound
def d2Transfer141Lo : ℚ := (d2LitsNearTransfers017.q2 (21642477) 1 (-27))
def d2Transfer141Hi : ℚ := (d2LitsNearTransfers017.q2 (44962675) 1 (-28))
def d2Transfer141Cap : ℚ := (d2LitsNearTransfers017.q2 (31165051305) 1 (-40))
def d2Transfer141C0 : ℚ := (d2LitsNearTransfers017.q2 (1) 11 (-5))
def d2Transfer141S0 : ℚ := (d2LitsNearTransfers017.q2 (-1) 1 (0))
def d2Transfer141C1 : ℚ := (d2LitsNearTransfers017.q2 (-5) 11 (-4))
def d2Transfer141S1 : ℚ := (d2LitsNearTransfers017.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer141Arithmetic : weightedUpper d2Transfer141C0 d2Log102Lo d2Log102Hi + weightedUpper d2Transfer141C1 d2Log72Lo d2Log72Hi ≤ d2Transfer141Cap := by decide +kernel
theorem d2Transfer141Bound : ∀ x ∈ Set.Icc ((d2Transfer141Lo:ℚ):ℝ) ((d2Transfer141Hi:ℚ):ℝ), ((d2Transfer141C0:ℚ):ℝ)*Real.log |x-((d2Transfer141S0:ℚ):ℝ)| + ((d2Transfer141C1:ℚ):ℝ)*Real.log |x-((d2Transfer141S1:ℚ):ℝ)| ≤ ((d2Transfer141Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer141S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer141S0,d2Transfer141Lo,d2Transfer141Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer141C0 then |x-((d2Transfer141S0:ℚ):ℝ)| ≤ ((d2Log102Q:ℚ):ℝ) else ((d2Log102Q:ℚ):ℝ) ≤ |x-((d2Transfer141S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer141S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer141S0,d2Transfer141Lo,d2Transfer141Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer141C0,d2Log102Q,d2Transfer141S0,d2Transfer141Lo,d2Transfer141Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer141C0 d2Transfer141S0 d2Log102Q d2Log102Lo d2Log102Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log102Bounds
  have hn1 : x-((d2Transfer141S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer141S1,d2Transfer141Lo,d2Transfer141Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer141C1 then |x-((d2Transfer141S1:ℚ):ℝ)| ≤ ((d2Log72Q:ℚ):ℝ) else ((d2Log72Q:ℚ):ℝ) ≤ |x-((d2Transfer141S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer141S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer141S1,d2Transfer141Lo,d2Transfer141Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer141C1,d2Log72Q,d2Transfer141S1,d2Transfer141Lo,d2Transfer141Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer141C1 d2Transfer141S1 d2Log72Q d2Log72Lo d2Log72Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log72Bounds
  have har : (((weightedUpper d2Transfer141C0 d2Log102Lo d2Log102Hi:ℚ):ℝ) + ((weightedUpper d2Transfer141C1 d2Log72Lo d2Log72Hi:ℚ):ℝ)) ≤ ((d2Transfer141Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer141Arithmetic
  linarith
#print axioms d2Transfer141Arithmetic
#print axioms d2Transfer141Bound
def d2Transfer142Lo : ℚ := (d2LitsNearTransfers017.q2 (44962675) 1 (-28))
def d2Transfer142Hi : ℚ := (d2LitsNearTransfers017.q2 (11660099) 1 (-26))
def d2Transfer142Cap : ℚ := (d2LitsNearTransfers017.q2 (649441385) 1 (-39))
def d2Transfer142C0 : ℚ := (d2LitsNearTransfers017.q2 (1) 25 (-4))
def d2Transfer142S0 : ℚ := (d2LitsNearTransfers017.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer142Arithmetic : weightedUpper d2Transfer142C0 d2Log103Lo d2Log103Hi ≤ d2Transfer142Cap := by decide +kernel
theorem d2Transfer142Bound : ∀ x ∈ Set.Icc ((d2Transfer142Lo:ℚ):ℝ) ((d2Transfer142Hi:ℚ):ℝ), ((d2Transfer142C0:ℚ):ℝ)*Real.log |x-((d2Transfer142S0:ℚ):ℝ)| ≤ ((d2Transfer142Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer142S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer142S0,d2Transfer142Lo,d2Transfer142Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer142C0 then |x-((d2Transfer142S0:ℚ):ℝ)| ≤ ((d2Log103Q:ℚ):ℝ) else ((d2Log103Q:ℚ):ℝ) ≤ |x-((d2Transfer142S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer142S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer142S0,d2Transfer142Lo,d2Transfer142Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer142C0,d2Log103Q,d2Transfer142S0,d2Transfer142Lo,d2Transfer142Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer142C0 d2Transfer142S0 d2Log103Q d2Log103Lo d2Log103Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log103Bounds
  have har : (((weightedUpper d2Transfer142C0 d2Log103Lo d2Log103Hi:ℚ):ℝ)) ≤ ((d2Transfer142Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer142Arithmetic
  linarith
#print axioms d2Transfer142Arithmetic
#print axioms d2Transfer142Bound
def d2Transfer143Lo : ℚ := (d2LitsNearTransfers017.q2 (44962675) 1 (-28))
def d2Transfer143Hi : ℚ := (d2LitsNearTransfers017.q2 (11660099) 1 (-26))
def d2Transfer143Cap : ℚ := (d2LitsNearTransfers017.q2 (2436024149) 1 (-40))
def d2Transfer143C0 : ℚ := (d2LitsNearTransfers017.q2 (1) 275 (-4))
def d2Transfer143S0 : ℚ := (d2LitsNearTransfers017.q2 (-1) 1 (0))
def d2Transfer143C1 : ℚ := (d2LitsNearTransfers017.q2 (-1) 55 (-3))
def d2Transfer143S1 : ℚ := (d2LitsNearTransfers017.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer143Arithmetic : weightedUpper d2Transfer143C0 d2Log103Lo d2Log103Hi + weightedUpper d2Transfer143C1 d2Log71Lo d2Log71Hi ≤ d2Transfer143Cap := by decide +kernel
theorem d2Transfer143Bound : ∀ x ∈ Set.Icc ((d2Transfer143Lo:ℚ):ℝ) ((d2Transfer143Hi:ℚ):ℝ), ((d2Transfer143C0:ℚ):ℝ)*Real.log |x-((d2Transfer143S0:ℚ):ℝ)| + ((d2Transfer143C1:ℚ):ℝ)*Real.log |x-((d2Transfer143S1:ℚ):ℝ)| ≤ ((d2Transfer143Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer143S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer143S0,d2Transfer143Lo,d2Transfer143Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer143C0 then |x-((d2Transfer143S0:ℚ):ℝ)| ≤ ((d2Log103Q:ℚ):ℝ) else ((d2Log103Q:ℚ):ℝ) ≤ |x-((d2Transfer143S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer143S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer143S0,d2Transfer143Lo,d2Transfer143Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer143C0,d2Log103Q,d2Transfer143S0,d2Transfer143Lo,d2Transfer143Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer143C0 d2Transfer143S0 d2Log103Q d2Log103Lo d2Log103Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log103Bounds
  have hn1 : x-((d2Transfer143S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer143S1,d2Transfer143Lo,d2Transfer143Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer143C1 then |x-((d2Transfer143S1:ℚ):ℝ)| ≤ ((d2Log71Q:ℚ):ℝ) else ((d2Log71Q:ℚ):ℝ) ≤ |x-((d2Transfer143S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer143S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer143S1,d2Transfer143Lo,d2Transfer143Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers017.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer143C1,d2Log71Q,d2Transfer143S1,d2Transfer143Lo,d2Transfer143Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer143C1 d2Transfer143S1 d2Log71Q d2Log71Lo d2Log71Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log71Bounds
  have har : (((weightedUpper d2Transfer143C0 d2Log103Lo d2Log103Hi:ℚ):ℝ) + ((weightedUpper d2Transfer143C1 d2Log71Lo d2Log71Hi:ℚ):ℝ)) ≤ ((d2Transfer143Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer143Arithmetic
  linarith
#print axioms d2Transfer143Arithmetic
#print axioms d2Transfer143Bound
end CatalanMeasure.GenD.Signed.Data.Cells

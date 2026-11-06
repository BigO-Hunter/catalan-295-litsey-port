module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers006
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers006
open D72.LogTransfer
def d2WiderTransfer48Lo : ℚ := (d2LitsNearWiderTransfers006.q2 (98749) 15625 (-6))
def d2WiderTransfer48Hi : ℚ := (d2LitsNearWiderTransfers006.q2 (828367) 1 (-23))
def d2WiderTransfer48Cap : ℚ := (d2LitsNearWiderTransfers006.q2 (16281318465) 1 (-40))
def d2WiderTransfer48C0 : ℚ := (d2LitsNearWiderTransfers006.q2 (1) 1 (-5))
def d2WiderTransfer48S0 : ℚ := (d2LitsNearWiderTransfers006.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer48Arithmetic : weightedUpper d2WiderTransfer48C0 d2Log88Lo d2Log88Hi ≤ d2WiderTransfer48Cap := by decide +kernel
theorem d2WiderTransfer48Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer48Lo:ℚ):ℝ) ((d2WiderTransfer48Hi:ℚ):ℝ), ((d2WiderTransfer48C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer48S0:ℚ):ℝ)| ≤ ((d2WiderTransfer48Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer48S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer48S0,d2WiderTransfer48Lo,d2WiderTransfer48Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer48C0 then |x-((d2WiderTransfer48S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer48S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer48S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer48S0,d2WiderTransfer48Lo,d2WiderTransfer48Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer48C0,d2Log88Q,d2WiderTransfer48S0,d2WiderTransfer48Lo,d2WiderTransfer48Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer48C0 d2WiderTransfer48S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have har : (((weightedUpper d2WiderTransfer48C0 d2Log88Lo d2Log88Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer48Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer48Arithmetic
  linarith
#print axioms d2WiderTransfer48Arithmetic
#print axioms d2WiderTransfer48Bound
def d2WiderTransfer49Lo : ℚ := (d2LitsNearWiderTransfers006.q2 (98749) 15625 (-6))
def d2WiderTransfer49Hi : ℚ := (d2LitsNearWiderTransfers006.q2 (828367) 1 (-23))
def d2WiderTransfer49Cap : ℚ := (d2LitsNearWiderTransfers006.q2 (31165051305) 1 (-40))
def d2WiderTransfer49C0 : ℚ := (d2LitsNearWiderTransfers006.q2 (1) 11 (-5))
def d2WiderTransfer49S0 : ℚ := (d2LitsNearWiderTransfers006.q2 (-1) 1 (0))
def d2WiderTransfer49C1 : ℚ := (d2LitsNearWiderTransfers006.q2 (-5) 11 (-4))
def d2WiderTransfer49S1 : ℚ := (d2LitsNearWiderTransfers006.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer49Arithmetic : weightedUpper d2WiderTransfer49C0 d2Log88Lo d2Log88Hi + weightedUpper d2WiderTransfer49C1 d2Log86Lo d2Log86Hi ≤ d2WiderTransfer49Cap := by decide +kernel
theorem d2WiderTransfer49Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer49Lo:ℚ):ℝ) ((d2WiderTransfer49Hi:ℚ):ℝ), ((d2WiderTransfer49C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer49S0:ℚ):ℝ)| + ((d2WiderTransfer49C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer49S1:ℚ):ℝ)| ≤ ((d2WiderTransfer49Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer49S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer49S0,d2WiderTransfer49Lo,d2WiderTransfer49Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer49C0 then |x-((d2WiderTransfer49S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer49S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer49S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer49S0,d2WiderTransfer49Lo,d2WiderTransfer49Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer49C0,d2Log88Q,d2WiderTransfer49S0,d2WiderTransfer49Lo,d2WiderTransfer49Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer49C0 d2WiderTransfer49S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have hn1 : x-((d2WiderTransfer49S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer49S1,d2WiderTransfer49Lo,d2WiderTransfer49Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer49C1 then |x-((d2WiderTransfer49S1:ℚ):ℝ)| ≤ ((d2Log86Q:ℚ):ℝ) else ((d2Log86Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer49S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer49S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer49S1,d2WiderTransfer49Lo,d2WiderTransfer49Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer49C1,d2Log86Q,d2WiderTransfer49S1,d2WiderTransfer49Lo,d2WiderTransfer49Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer49C1 d2WiderTransfer49S1 d2Log86Q d2Log86Lo d2Log86Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log86Bounds
  have har : (((weightedUpper d2WiderTransfer49C0 d2Log88Lo d2Log88Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer49C1 d2Log86Lo d2Log86Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer49Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer49Arithmetic
  linarith
#print axioms d2WiderTransfer49Arithmetic
#print axioms d2WiderTransfer49Bound
def d2WiderTransfer50Lo : ℚ := (d2LitsNearWiderTransfers006.q2 (828367) 1 (-23))
def d2WiderTransfer50Hi : ℚ := (d2LitsNearWiderTransfers006.q2 (8304657) 1 (-26))
def d2WiderTransfer50Cap : ℚ := (d2LitsNearWiderTransfers006.q2 (649441385) 1 (-39))
def d2WiderTransfer50C0 : ℚ := (d2LitsNearWiderTransfers006.q2 (1) 25 (-4))
def d2WiderTransfer50S0 : ℚ := (d2LitsNearWiderTransfers006.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer50Arithmetic : weightedUpper d2WiderTransfer50C0 d2Log95Lo d2Log95Hi ≤ d2WiderTransfer50Cap := by decide +kernel
theorem d2WiderTransfer50Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer50Lo:ℚ):ℝ) ((d2WiderTransfer50Hi:ℚ):ℝ), ((d2WiderTransfer50C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer50S0:ℚ):ℝ)| ≤ ((d2WiderTransfer50Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer50S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer50S0,d2WiderTransfer50Lo,d2WiderTransfer50Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer50C0 then |x-((d2WiderTransfer50S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer50S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer50S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer50S0,d2WiderTransfer50Lo,d2WiderTransfer50Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer50C0,d2Log95Q,d2WiderTransfer50S0,d2WiderTransfer50Lo,d2WiderTransfer50Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer50C0 d2WiderTransfer50S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have har : (((weightedUpper d2WiderTransfer50C0 d2Log95Lo d2Log95Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer50Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer50Arithmetic
  linarith
#print axioms d2WiderTransfer50Arithmetic
#print axioms d2WiderTransfer50Bound
def d2WiderTransfer51Lo : ℚ := (d2LitsNearWiderTransfers006.q2 (828367) 1 (-23))
def d2WiderTransfer51Hi : ℚ := (d2LitsNearWiderTransfers006.q2 (8304657) 1 (-26))
def d2WiderTransfer51Cap : ℚ := (d2LitsNearWiderTransfers006.q2 (2436024149) 1 (-40))
def d2WiderTransfer51C0 : ℚ := (d2LitsNearWiderTransfers006.q2 (1) 275 (-4))
def d2WiderTransfer51S0 : ℚ := (d2LitsNearWiderTransfers006.q2 (-1) 1 (0))
def d2WiderTransfer51C1 : ℚ := (d2LitsNearWiderTransfers006.q2 (-1) 55 (-3))
def d2WiderTransfer51S1 : ℚ := (d2LitsNearWiderTransfers006.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer51Arithmetic : weightedUpper d2WiderTransfer51C0 d2Log95Lo d2Log95Hi + weightedUpper d2WiderTransfer51C1 d2Log79Lo d2Log79Hi ≤ d2WiderTransfer51Cap := by decide +kernel
theorem d2WiderTransfer51Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer51Lo:ℚ):ℝ) ((d2WiderTransfer51Hi:ℚ):ℝ), ((d2WiderTransfer51C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer51S0:ℚ):ℝ)| + ((d2WiderTransfer51C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer51S1:ℚ):ℝ)| ≤ ((d2WiderTransfer51Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer51S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer51S0,d2WiderTransfer51Lo,d2WiderTransfer51Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer51C0 then |x-((d2WiderTransfer51S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer51S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer51S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer51S0,d2WiderTransfer51Lo,d2WiderTransfer51Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer51C0,d2Log95Q,d2WiderTransfer51S0,d2WiderTransfer51Lo,d2WiderTransfer51Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer51C0 d2WiderTransfer51S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have hn1 : x-((d2WiderTransfer51S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer51S1,d2WiderTransfer51Lo,d2WiderTransfer51Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer51C1 then |x-((d2WiderTransfer51S1:ℚ):ℝ)| ≤ ((d2Log79Q:ℚ):ℝ) else ((d2Log79Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer51S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer51S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer51S1,d2WiderTransfer51Lo,d2WiderTransfer51Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer51C1,d2Log79Q,d2WiderTransfer51S1,d2WiderTransfer51Lo,d2WiderTransfer51Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer51C1 d2WiderTransfer51S1 d2Log79Q d2Log79Lo d2Log79Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log79Bounds
  have har : (((weightedUpper d2WiderTransfer51C0 d2Log95Lo d2Log95Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer51C1 d2Log79Lo d2Log79Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer51Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer51Arithmetic
  linarith
#print axioms d2WiderTransfer51Arithmetic
#print axioms d2WiderTransfer51Bound
def d2WiderTransfer52Lo : ℚ := (d2LitsNearWiderTransfers006.q2 (828367) 1 (-23))
def d2WiderTransfer52Hi : ℚ := (d2LitsNearWiderTransfers006.q2 (8304657) 1 (-26))
def d2WiderTransfer52Cap : ℚ := (d2LitsNearWiderTransfers006.q2 (16281318465) 1 (-40))
def d2WiderTransfer52C0 : ℚ := (d2LitsNearWiderTransfers006.q2 (1) 1 (-5))
def d2WiderTransfer52S0 : ℚ := (d2LitsNearWiderTransfers006.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer52Arithmetic : weightedUpper d2WiderTransfer52C0 d2Log95Lo d2Log95Hi ≤ d2WiderTransfer52Cap := by decide +kernel
theorem d2WiderTransfer52Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer52Lo:ℚ):ℝ) ((d2WiderTransfer52Hi:ℚ):ℝ), ((d2WiderTransfer52C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer52S0:ℚ):ℝ)| ≤ ((d2WiderTransfer52Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer52S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer52S0,d2WiderTransfer52Lo,d2WiderTransfer52Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer52C0 then |x-((d2WiderTransfer52S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer52S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer52S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer52S0,d2WiderTransfer52Lo,d2WiderTransfer52Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer52C0,d2Log95Q,d2WiderTransfer52S0,d2WiderTransfer52Lo,d2WiderTransfer52Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer52C0 d2WiderTransfer52S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have har : (((weightedUpper d2WiderTransfer52C0 d2Log95Lo d2Log95Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer52Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer52Arithmetic
  linarith
#print axioms d2WiderTransfer52Arithmetic
#print axioms d2WiderTransfer52Bound
def d2WiderTransfer53Lo : ℚ := (d2LitsNearWiderTransfers006.q2 (828367) 1 (-23))
def d2WiderTransfer53Hi : ℚ := (d2LitsNearWiderTransfers006.q2 (8304657) 1 (-26))
def d2WiderTransfer53Cap : ℚ := (d2LitsNearWiderTransfers006.q2 (31165051305) 1 (-40))
def d2WiderTransfer53C0 : ℚ := (d2LitsNearWiderTransfers006.q2 (1) 11 (-5))
def d2WiderTransfer53S0 : ℚ := (d2LitsNearWiderTransfers006.q2 (-1) 1 (0))
def d2WiderTransfer53C1 : ℚ := (d2LitsNearWiderTransfers006.q2 (-5) 11 (-4))
def d2WiderTransfer53S1 : ℚ := (d2LitsNearWiderTransfers006.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer53Arithmetic : weightedUpper d2WiderTransfer53C0 d2Log95Lo d2Log95Hi + weightedUpper d2WiderTransfer53C1 d2Log79Lo d2Log79Hi ≤ d2WiderTransfer53Cap := by decide +kernel
theorem d2WiderTransfer53Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer53Lo:ℚ):ℝ) ((d2WiderTransfer53Hi:ℚ):ℝ), ((d2WiderTransfer53C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer53S0:ℚ):ℝ)| + ((d2WiderTransfer53C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer53S1:ℚ):ℝ)| ≤ ((d2WiderTransfer53Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer53S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer53S0,d2WiderTransfer53Lo,d2WiderTransfer53Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer53C0 then |x-((d2WiderTransfer53S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer53S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer53S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer53S0,d2WiderTransfer53Lo,d2WiderTransfer53Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer53C0,d2Log95Q,d2WiderTransfer53S0,d2WiderTransfer53Lo,d2WiderTransfer53Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer53C0 d2WiderTransfer53S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have hn1 : x-((d2WiderTransfer53S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer53S1,d2WiderTransfer53Lo,d2WiderTransfer53Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer53C1 then |x-((d2WiderTransfer53S1:ℚ):ℝ)| ≤ ((d2Log79Q:ℚ):ℝ) else ((d2Log79Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer53S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer53S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer53S1,d2WiderTransfer53Lo,d2WiderTransfer53Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer53C1,d2Log79Q,d2WiderTransfer53S1,d2WiderTransfer53Lo,d2WiderTransfer53Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer53C1 d2WiderTransfer53S1 d2Log79Q d2Log79Lo d2Log79Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log79Bounds
  have har : (((weightedUpper d2WiderTransfer53C0 d2Log95Lo d2Log95Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer53C1 d2Log79Lo d2Log79Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer53Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer53Arithmetic
  linarith
#print axioms d2WiderTransfer53Arithmetic
#print axioms d2WiderTransfer53Bound
def d2WiderTransfer54Lo : ℚ := (d2LitsNearWiderTransfers006.q2 (8304657) 1 (-26))
def d2WiderTransfer54Hi : ℚ := (d2LitsNearWiderTransfers006.q2 (4991189) 1 (-25))
def d2WiderTransfer54Cap : ℚ := (d2LitsNearWiderTransfers006.q2 (649441385) 1 (-39))
def d2WiderTransfer54C0 : ℚ := (d2LitsNearWiderTransfers006.q2 (1) 25 (-4))
def d2WiderTransfer54S0 : ℚ := (d2LitsNearWiderTransfers006.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer54Arithmetic : weightedUpper d2WiderTransfer54C0 d2Log99Lo d2Log99Hi ≤ d2WiderTransfer54Cap := by decide +kernel
theorem d2WiderTransfer54Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer54Lo:ℚ):ℝ) ((d2WiderTransfer54Hi:ℚ):ℝ), ((d2WiderTransfer54C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer54S0:ℚ):ℝ)| ≤ ((d2WiderTransfer54Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer54S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer54S0,d2WiderTransfer54Lo,d2WiderTransfer54Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer54C0 then |x-((d2WiderTransfer54S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer54S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer54S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer54S0,d2WiderTransfer54Lo,d2WiderTransfer54Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer54C0,d2Log99Q,d2WiderTransfer54S0,d2WiderTransfer54Lo,d2WiderTransfer54Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer54C0 d2WiderTransfer54S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have har : (((weightedUpper d2WiderTransfer54C0 d2Log99Lo d2Log99Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer54Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer54Arithmetic
  linarith
#print axioms d2WiderTransfer54Arithmetic
#print axioms d2WiderTransfer54Bound
def d2WiderTransfer55Lo : ℚ := (d2LitsNearWiderTransfers006.q2 (8304657) 1 (-26))
def d2WiderTransfer55Hi : ℚ := (d2LitsNearWiderTransfers006.q2 (4991189) 1 (-25))
def d2WiderTransfer55Cap : ℚ := (d2LitsNearWiderTransfers006.q2 (2436024149) 1 (-40))
def d2WiderTransfer55C0 : ℚ := (d2LitsNearWiderTransfers006.q2 (1) 275 (-4))
def d2WiderTransfer55S0 : ℚ := (d2LitsNearWiderTransfers006.q2 (-1) 1 (0))
def d2WiderTransfer55C1 : ℚ := (d2LitsNearWiderTransfers006.q2 (-1) 55 (-3))
def d2WiderTransfer55S1 : ℚ := (d2LitsNearWiderTransfers006.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer55Arithmetic : weightedUpper d2WiderTransfer55C0 d2Log99Lo d2Log99Hi + weightedUpper d2WiderTransfer55C1 d2Log75Lo d2Log75Hi ≤ d2WiderTransfer55Cap := by decide +kernel
theorem d2WiderTransfer55Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer55Lo:ℚ):ℝ) ((d2WiderTransfer55Hi:ℚ):ℝ), ((d2WiderTransfer55C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer55S0:ℚ):ℝ)| + ((d2WiderTransfer55C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer55S1:ℚ):ℝ)| ≤ ((d2WiderTransfer55Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer55S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer55S0,d2WiderTransfer55Lo,d2WiderTransfer55Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer55C0 then |x-((d2WiderTransfer55S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer55S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer55S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer55S0,d2WiderTransfer55Lo,d2WiderTransfer55Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer55C0,d2Log99Q,d2WiderTransfer55S0,d2WiderTransfer55Lo,d2WiderTransfer55Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer55C0 d2WiderTransfer55S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have hn1 : x-((d2WiderTransfer55S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer55S1,d2WiderTransfer55Lo,d2WiderTransfer55Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer55C1 then |x-((d2WiderTransfer55S1:ℚ):ℝ)| ≤ ((d2Log75Q:ℚ):ℝ) else ((d2Log75Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer55S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer55S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer55S1,d2WiderTransfer55Lo,d2WiderTransfer55Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers006.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2WiderTransfer55C1,d2Log75Q,d2WiderTransfer55S1,d2WiderTransfer55Lo,d2WiderTransfer55Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer55C1 d2WiderTransfer55S1 d2Log75Q d2Log75Lo d2Log75Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log75Bounds
  have har : (((weightedUpper d2WiderTransfer55C0 d2Log99Lo d2Log99Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer55C1 d2Log75Lo d2Log75Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer55Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer55Arithmetic
  linarith
#print axioms d2WiderTransfer55Arithmetic
#print axioms d2WiderTransfer55Bound
end CatalanMeasure.GenD.Signed.Data.Cells

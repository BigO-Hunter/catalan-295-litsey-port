module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
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
namespace d2LitsNearTransfers052
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers052
open D72.LogTransfer
def d2Transfer416Lo : ℚ := (d2LitsNearTransfers052.q2 (38251791) 1 (-28))
def d2Transfer416Hi : ℚ := (d2LitsNearTransfers052.q2 (4991189) 1 (-25))
def d2Transfer416Cap : ℚ := (d2LitsNearTransfers052.q2 (15113656175) 1 (-40))
def d2Transfer416C0 : ℚ := (d2LitsNearTransfers052.q2 (23) 25 (-5))
def d2Transfer416S0 : ℚ := (d2LitsNearTransfers052.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer416Arithmetic : weightedUpper d2Transfer416C0 d2Log99Lo d2Log99Hi ≤ d2Transfer416Cap := by decide +kernel
theorem d2Transfer416Bound : ∀ x ∈ Set.Icc ((d2Transfer416Lo:ℚ):ℝ) ((d2Transfer416Hi:ℚ):ℝ), ((d2Transfer416C0:ℚ):ℝ)*Real.log |x-((d2Transfer416S0:ℚ):ℝ)| ≤ ((d2Transfer416Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer416S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer416S0,d2Transfer416Lo,d2Transfer416Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer416C0 then |x-((d2Transfer416S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2Transfer416S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer416S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer416S0,d2Transfer416Lo,d2Transfer416Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer416C0,d2Log99Q,d2Transfer416S0,d2Transfer416Lo,d2Transfer416Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer416C0 d2Transfer416S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have har : (((weightedUpper d2Transfer416C0 d2Log99Lo d2Log99Hi:ℚ):ℝ)) ≤ ((d2Transfer416Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer416Arithmetic
  linarith
#print axioms d2Transfer416Arithmetic
#print axioms d2Transfer416Bound
def d2Transfer417Lo : ℚ := (d2LitsNearTransfers052.q2 (38251791) 1 (-28))
def d2Transfer417Hi : ℚ := (d2LitsNearTransfers052.q2 (4991189) 1 (-25))
def d2Transfer417Cap : ℚ := (d2LitsNearTransfers052.q2 (30439539927) 1 (-40))
def d2Transfer417C0 : ℚ := (d2LitsNearTransfers052.q2 (3) 275 (-5))
def d2Transfer417S0 : ℚ := (d2LitsNearTransfers052.q2 (-1) 1 (0))
def d2Transfer417C1 : ℚ := (d2LitsNearTransfers052.q2 (-5) 11 (-4))
def d2Transfer417S1 : ℚ := (d2LitsNearTransfers052.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer417Arithmetic : weightedUpper d2Transfer417C0 d2Log99Lo d2Log99Hi + weightedUpper d2Transfer417C1 d2Log75Lo d2Log75Hi ≤ d2Transfer417Cap := by decide +kernel
theorem d2Transfer417Bound : ∀ x ∈ Set.Icc ((d2Transfer417Lo:ℚ):ℝ) ((d2Transfer417Hi:ℚ):ℝ), ((d2Transfer417C0:ℚ):ℝ)*Real.log |x-((d2Transfer417S0:ℚ):ℝ)| + ((d2Transfer417C1:ℚ):ℝ)*Real.log |x-((d2Transfer417S1:ℚ):ℝ)| ≤ ((d2Transfer417Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer417S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer417S0,d2Transfer417Lo,d2Transfer417Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer417C0 then |x-((d2Transfer417S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2Transfer417S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer417S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer417S0,d2Transfer417Lo,d2Transfer417Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer417C0,d2Log99Q,d2Transfer417S0,d2Transfer417Lo,d2Transfer417Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer417C0 d2Transfer417S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have hn1 : x-((d2Transfer417S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer417S1,d2Transfer417Lo,d2Transfer417Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer417C1 then |x-((d2Transfer417S1:ℚ):ℝ)| ≤ ((d2Log75Q:ℚ):ℝ) else ((d2Log75Q:ℚ):ℝ) ≤ |x-((d2Transfer417S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer417S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer417S1,d2Transfer417Lo,d2Transfer417Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer417C1,d2Log75Q,d2Transfer417S1,d2Transfer417Lo,d2Transfer417Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer417C1 d2Transfer417S1 d2Log75Q d2Log75Lo d2Log75Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log75Bounds
  have har : (((weightedUpper d2Transfer417C0 d2Log99Lo d2Log99Hi:ℚ):ℝ) + ((weightedUpper d2Transfer417C1 d2Log75Lo d2Log75Hi:ℚ):ℝ)) ≤ ((d2Transfer417Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer417Arithmetic
  linarith
#print axioms d2Transfer417Arithmetic
#print axioms d2Transfer417Bound
def d2Transfer418Lo : ℚ := (d2LitsNearTransfers052.q2 (4991189) 1 (-25))
def d2Transfer418Hi : ℚ := (d2LitsNearTransfers052.q2 (41607233) 1 (-28))
def d2Transfer418Cap : ℚ := (d2LitsNearTransfers052.q2 (1169469059) 1 (-40))
def d2Transfer418C0 : ℚ := (d2LitsNearTransfers052.q2 (-1) 55 (-3))
def d2Transfer418S0 : ℚ := (d2LitsNearTransfers052.q2 (-1) 1 (0))
def d2Transfer418C1 : ℚ := (d2LitsNearTransfers052.q2 (-1) 55 (-3))
def d2Transfer418S1 : ℚ := (d2LitsNearTransfers052.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer418Arithmetic : weightedUpper d2Transfer418C0 d2Log99Lo d2Log99Hi + weightedUpper d2Transfer418C1 d2Log74Lo d2Log74Hi ≤ d2Transfer418Cap := by decide +kernel
theorem d2Transfer418Bound : ∀ x ∈ Set.Icc ((d2Transfer418Lo:ℚ):ℝ) ((d2Transfer418Hi:ℚ):ℝ), ((d2Transfer418C0:ℚ):ℝ)*Real.log |x-((d2Transfer418S0:ℚ):ℝ)| + ((d2Transfer418C1:ℚ):ℝ)*Real.log |x-((d2Transfer418S1:ℚ):ℝ)| ≤ ((d2Transfer418Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer418S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer418S0,d2Transfer418Lo,d2Transfer418Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer418C0 then |x-((d2Transfer418S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2Transfer418S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer418S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer418S0,d2Transfer418Lo,d2Transfer418Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer418C0,d2Log99Q,d2Transfer418S0,d2Transfer418Lo,d2Transfer418Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer418C0 d2Transfer418S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have hn1 : x-((d2Transfer418S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer418S1,d2Transfer418Lo,d2Transfer418Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer418C1 then |x-((d2Transfer418S1:ℚ):ℝ)| ≤ ((d2Log74Q:ℚ):ℝ) else ((d2Log74Q:ℚ):ℝ) ≤ |x-((d2Transfer418S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer418S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer418S1,d2Transfer418Lo,d2Transfer418Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer418C1,d2Log74Q,d2Transfer418S1,d2Transfer418Lo,d2Transfer418Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer418C1 d2Transfer418S1 d2Log74Q d2Log74Lo d2Log74Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log74Bounds
  have har : (((weightedUpper d2Transfer418C0 d2Log99Lo d2Log99Hi:ℚ):ℝ) + ((weightedUpper d2Transfer418C1 d2Log74Lo d2Log74Hi:ℚ):ℝ)) ≤ ((d2Transfer418Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer418Arithmetic
  linarith
#print axioms d2Transfer418Arithmetic
#print axioms d2Transfer418Bound
def d2Transfer419Lo : ℚ := (d2LitsNearTransfers052.q2 (4991189) 1 (-25))
def d2Transfer419Hi : ℚ := (d2LitsNearTransfers052.q2 (41607233) 1 (-28))
def d2Transfer419Cap : ℚ := (d2LitsNearTransfers052.q2 (15113656175) 1 (-40))
def d2Transfer419C0 : ℚ := (d2LitsNearTransfers052.q2 (23) 25 (-5))
def d2Transfer419S0 : ℚ := (d2LitsNearTransfers052.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer419Arithmetic : weightedUpper d2Transfer419C0 d2Log100Lo d2Log100Hi ≤ d2Transfer419Cap := by decide +kernel
theorem d2Transfer419Bound : ∀ x ∈ Set.Icc ((d2Transfer419Lo:ℚ):ℝ) ((d2Transfer419Hi:ℚ):ℝ), ((d2Transfer419C0:ℚ):ℝ)*Real.log |x-((d2Transfer419S0:ℚ):ℝ)| ≤ ((d2Transfer419Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer419S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer419S0,d2Transfer419Lo,d2Transfer419Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer419C0 then |x-((d2Transfer419S0:ℚ):ℝ)| ≤ ((d2Log100Q:ℚ):ℝ) else ((d2Log100Q:ℚ):ℝ) ≤ |x-((d2Transfer419S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer419S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer419S0,d2Transfer419Lo,d2Transfer419Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer419C0,d2Log100Q,d2Transfer419S0,d2Transfer419Lo,d2Transfer419Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer419C0 d2Transfer419S0 d2Log100Q d2Log100Lo d2Log100Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log100Bounds
  have har : (((weightedUpper d2Transfer419C0 d2Log100Lo d2Log100Hi:ℚ):ℝ)) ≤ ((d2Transfer419Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer419Arithmetic
  linarith
#print axioms d2Transfer419Arithmetic
#print axioms d2Transfer419Bound
def d2Transfer420Lo : ℚ := (d2LitsNearTransfers052.q2 (4991189) 1 (-25))
def d2Transfer420Hi : ℚ := (d2LitsNearTransfers052.q2 (41607233) 1 (-28))
def d2Transfer420Cap : ℚ := (d2LitsNearTransfers052.q2 (30439539927) 1 (-40))
def d2Transfer420C0 : ℚ := (d2LitsNearTransfers052.q2 (3) 275 (-5))
def d2Transfer420S0 : ℚ := (d2LitsNearTransfers052.q2 (-1) 1 (0))
def d2Transfer420C1 : ℚ := (d2LitsNearTransfers052.q2 (-5) 11 (-4))
def d2Transfer420S1 : ℚ := (d2LitsNearTransfers052.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer420Arithmetic : weightedUpper d2Transfer420C0 d2Log100Lo d2Log100Hi + weightedUpper d2Transfer420C1 d2Log74Lo d2Log74Hi ≤ d2Transfer420Cap := by decide +kernel
theorem d2Transfer420Bound : ∀ x ∈ Set.Icc ((d2Transfer420Lo:ℚ):ℝ) ((d2Transfer420Hi:ℚ):ℝ), ((d2Transfer420C0:ℚ):ℝ)*Real.log |x-((d2Transfer420S0:ℚ):ℝ)| + ((d2Transfer420C1:ℚ):ℝ)*Real.log |x-((d2Transfer420S1:ℚ):ℝ)| ≤ ((d2Transfer420Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer420S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer420S0,d2Transfer420Lo,d2Transfer420Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer420C0 then |x-((d2Transfer420S0:ℚ):ℝ)| ≤ ((d2Log100Q:ℚ):ℝ) else ((d2Log100Q:ℚ):ℝ) ≤ |x-((d2Transfer420S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer420S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer420S0,d2Transfer420Lo,d2Transfer420Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer420C0,d2Log100Q,d2Transfer420S0,d2Transfer420Lo,d2Transfer420Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer420C0 d2Transfer420S0 d2Log100Q d2Log100Lo d2Log100Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log100Bounds
  have hn1 : x-((d2Transfer420S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer420S1,d2Transfer420Lo,d2Transfer420Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer420C1 then |x-((d2Transfer420S1:ℚ):ℝ)| ≤ ((d2Log74Q:ℚ):ℝ) else ((d2Log74Q:ℚ):ℝ) ≤ |x-((d2Transfer420S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer420S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer420S1,d2Transfer420Lo,d2Transfer420Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer420C1,d2Log74Q,d2Transfer420S1,d2Transfer420Lo,d2Transfer420Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer420C1 d2Transfer420S1 d2Log74Q d2Log74Lo d2Log74Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log74Bounds
  have har : (((weightedUpper d2Transfer420C0 d2Log100Lo d2Log100Hi:ℚ):ℝ) + ((weightedUpper d2Transfer420C1 d2Log74Lo d2Log74Hi:ℚ):ℝ)) ≤ ((d2Transfer420Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer420Arithmetic
  linarith
#print axioms d2Transfer420Arithmetic
#print axioms d2Transfer420Bound
def d2Transfer421Lo : ℚ := (d2LitsNearTransfers052.q2 (41607233) 1 (-28))
def d2Transfer421Hi : ℚ := (d2LitsNearTransfers052.q2 (21642477) 1 (-27))
def d2Transfer421Cap : ℚ := (d2LitsNearTransfers052.q2 (1169469059) 1 (-40))
def d2Transfer421C0 : ℚ := (d2LitsNearTransfers052.q2 (-1) 55 (-3))
def d2Transfer421S0 : ℚ := (d2LitsNearTransfers052.q2 (-1) 1 (0))
def d2Transfer421C1 : ℚ := (d2LitsNearTransfers052.q2 (-1) 55 (-3))
def d2Transfer421S1 : ℚ := (d2LitsNearTransfers052.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer421Arithmetic : weightedUpper d2Transfer421C0 d2Log100Lo d2Log100Hi + weightedUpper d2Transfer421C1 d2Log73Lo d2Log73Hi ≤ d2Transfer421Cap := by decide +kernel
theorem d2Transfer421Bound : ∀ x ∈ Set.Icc ((d2Transfer421Lo:ℚ):ℝ) ((d2Transfer421Hi:ℚ):ℝ), ((d2Transfer421C0:ℚ):ℝ)*Real.log |x-((d2Transfer421S0:ℚ):ℝ)| + ((d2Transfer421C1:ℚ):ℝ)*Real.log |x-((d2Transfer421S1:ℚ):ℝ)| ≤ ((d2Transfer421Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer421S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer421S0,d2Transfer421Lo,d2Transfer421Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer421C0 then |x-((d2Transfer421S0:ℚ):ℝ)| ≤ ((d2Log100Q:ℚ):ℝ) else ((d2Log100Q:ℚ):ℝ) ≤ |x-((d2Transfer421S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer421S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer421S0,d2Transfer421Lo,d2Transfer421Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer421C0,d2Log100Q,d2Transfer421S0,d2Transfer421Lo,d2Transfer421Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer421C0 d2Transfer421S0 d2Log100Q d2Log100Lo d2Log100Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log100Bounds
  have hn1 : x-((d2Transfer421S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer421S1,d2Transfer421Lo,d2Transfer421Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer421C1 then |x-((d2Transfer421S1:ℚ):ℝ)| ≤ ((d2Log73Q:ℚ):ℝ) else ((d2Log73Q:ℚ):ℝ) ≤ |x-((d2Transfer421S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer421S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer421S1,d2Transfer421Lo,d2Transfer421Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer421C1,d2Log73Q,d2Transfer421S1,d2Transfer421Lo,d2Transfer421Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer421C1 d2Transfer421S1 d2Log73Q d2Log73Lo d2Log73Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log73Bounds
  have har : (((weightedUpper d2Transfer421C0 d2Log100Lo d2Log100Hi:ℚ):ℝ) + ((weightedUpper d2Transfer421C1 d2Log73Lo d2Log73Hi:ℚ):ℝ)) ≤ ((d2Transfer421Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer421Arithmetic
  linarith
#print axioms d2Transfer421Arithmetic
#print axioms d2Transfer421Bound
def d2Transfer422Lo : ℚ := (d2LitsNearTransfers052.q2 (41607233) 1 (-28))
def d2Transfer422Hi : ℚ := (d2LitsNearTransfers052.q2 (21642477) 1 (-27))
def d2Transfer422Cap : ℚ := (d2LitsNearTransfers052.q2 (15113656175) 1 (-40))
def d2Transfer422C0 : ℚ := (d2LitsNearTransfers052.q2 (23) 25 (-5))
def d2Transfer422S0 : ℚ := (d2LitsNearTransfers052.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer422Arithmetic : weightedUpper d2Transfer422C0 d2Log101Lo d2Log101Hi ≤ d2Transfer422Cap := by decide +kernel
theorem d2Transfer422Bound : ∀ x ∈ Set.Icc ((d2Transfer422Lo:ℚ):ℝ) ((d2Transfer422Hi:ℚ):ℝ), ((d2Transfer422C0:ℚ):ℝ)*Real.log |x-((d2Transfer422S0:ℚ):ℝ)| ≤ ((d2Transfer422Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer422S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer422S0,d2Transfer422Lo,d2Transfer422Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer422C0 then |x-((d2Transfer422S0:ℚ):ℝ)| ≤ ((d2Log101Q:ℚ):ℝ) else ((d2Log101Q:ℚ):ℝ) ≤ |x-((d2Transfer422S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer422S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer422S0,d2Transfer422Lo,d2Transfer422Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer422C0,d2Log101Q,d2Transfer422S0,d2Transfer422Lo,d2Transfer422Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer422C0 d2Transfer422S0 d2Log101Q d2Log101Lo d2Log101Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log101Bounds
  have har : (((weightedUpper d2Transfer422C0 d2Log101Lo d2Log101Hi:ℚ):ℝ)) ≤ ((d2Transfer422Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer422Arithmetic
  linarith
#print axioms d2Transfer422Arithmetic
#print axioms d2Transfer422Bound
def d2Transfer423Lo : ℚ := (d2LitsNearTransfers052.q2 (41607233) 1 (-28))
def d2Transfer423Hi : ℚ := (d2LitsNearTransfers052.q2 (21642477) 1 (-27))
def d2Transfer423Cap : ℚ := (d2LitsNearTransfers052.q2 (30439539927) 1 (-40))
def d2Transfer423C0 : ℚ := (d2LitsNearTransfers052.q2 (3) 275 (-5))
def d2Transfer423S0 : ℚ := (d2LitsNearTransfers052.q2 (-1) 1 (0))
def d2Transfer423C1 : ℚ := (d2LitsNearTransfers052.q2 (-5) 11 (-4))
def d2Transfer423S1 : ℚ := (d2LitsNearTransfers052.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer423Arithmetic : weightedUpper d2Transfer423C0 d2Log101Lo d2Log101Hi + weightedUpper d2Transfer423C1 d2Log73Lo d2Log73Hi ≤ d2Transfer423Cap := by decide +kernel
theorem d2Transfer423Bound : ∀ x ∈ Set.Icc ((d2Transfer423Lo:ℚ):ℝ) ((d2Transfer423Hi:ℚ):ℝ), ((d2Transfer423C0:ℚ):ℝ)*Real.log |x-((d2Transfer423S0:ℚ):ℝ)| + ((d2Transfer423C1:ℚ):ℝ)*Real.log |x-((d2Transfer423S1:ℚ):ℝ)| ≤ ((d2Transfer423Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer423S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer423S0,d2Transfer423Lo,d2Transfer423Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer423C0 then |x-((d2Transfer423S0:ℚ):ℝ)| ≤ ((d2Log101Q:ℚ):ℝ) else ((d2Log101Q:ℚ):ℝ) ≤ |x-((d2Transfer423S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer423S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer423S0,d2Transfer423Lo,d2Transfer423Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer423C0,d2Log101Q,d2Transfer423S0,d2Transfer423Lo,d2Transfer423Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer423C0 d2Transfer423S0 d2Log101Q d2Log101Lo d2Log101Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log101Bounds
  have hn1 : x-((d2Transfer423S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer423S1,d2Transfer423Lo,d2Transfer423Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer423C1 then |x-((d2Transfer423S1:ℚ):ℝ)| ≤ ((d2Log73Q:ℚ):ℝ) else ((d2Log73Q:ℚ):ℝ) ≤ |x-((d2Transfer423S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer423S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer423S1,d2Transfer423Lo,d2Transfer423Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers052.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer423C1,d2Log73Q,d2Transfer423S1,d2Transfer423Lo,d2Transfer423Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer423C1 d2Transfer423S1 d2Log73Q d2Log73Lo d2Log73Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log73Bounds
  have har : (((weightedUpper d2Transfer423C0 d2Log101Lo d2Log101Hi:ℚ):ℝ) + ((weightedUpper d2Transfer423C1 d2Log73Lo d2Log73Hi:ℚ):ℝ)) ≤ ((d2Transfer423Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer423Arithmetic
  linarith
#print axioms d2Transfer423Arithmetic
#print axioms d2Transfer423Bound
end CatalanMeasure.GenD.Signed.Data.Cells

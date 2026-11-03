module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache009
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers069
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers069
open D72.LogTransfer
def d2Transfer552Lo : ℚ := (d2LitsNearTransfers069.q2 (681489279) 1 (-30))
def d2Transfer552Hi : ℚ := (d2LitsNearTransfers069.q2 (1364656279) 1 (-31))
def d2Transfer552Cap : ℚ := (d2LitsNearTransfers069.q2 (34861127117548928311389) 1 (-80))
def d2Transfer552C0 : ℚ := (d2LitsNearTransfers069.q2 (3) 275 (-5))
def d2Transfer552S0 : ℚ := (d2LitsNearTransfers069.q2 (-1) 1 (0))
def d2Transfer552C1 : ℚ := (d2LitsNearTransfers069.q2 (-5) 11 (-4))
def d2Transfer552S1 : ℚ := (d2LitsNearTransfers069.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer552Arithmetic : weightedUpper d2Transfer552C0 d2Log154Lo d2Log154Hi + weightedUpper d2Transfer552C1 d2Log20Lo d2Log20Hi ≤ d2Transfer552Cap := by decide +kernel
theorem d2Transfer552Bound : ∀ x ∈ Set.Icc ((d2Transfer552Lo:ℚ):ℝ) ((d2Transfer552Hi:ℚ):ℝ), ((d2Transfer552C0:ℚ):ℝ)*Real.log |x-((d2Transfer552S0:ℚ):ℝ)| + ((d2Transfer552C1:ℚ):ℝ)*Real.log |x-((d2Transfer552S1:ℚ):ℝ)| ≤ ((d2Transfer552Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer552S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer552S0,d2Transfer552Lo,d2Transfer552Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer552C0 then |x-((d2Transfer552S0:ℚ):ℝ)| ≤ ((d2Log154Q:ℚ):ℝ) else ((d2Log154Q:ℚ):ℝ) ≤ |x-((d2Transfer552S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer552S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer552S0,d2Transfer552Lo,d2Transfer552Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer552C0,d2Log154Q,d2Transfer552S0,d2Transfer552Lo,d2Transfer552Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer552C0 d2Transfer552S0 d2Log154Q d2Log154Lo d2Log154Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log154Bounds
  have hn1 : x-((d2Transfer552S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer552S1,d2Transfer552Lo,d2Transfer552Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer552C1 then |x-((d2Transfer552S1:ℚ):ℝ)| ≤ ((d2Log20Q:ℚ):ℝ) else ((d2Log20Q:ℚ):ℝ) ≤ |x-((d2Transfer552S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer552S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer552S1,d2Transfer552Lo,d2Transfer552Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer552C1,d2Log20Q,d2Transfer552S1,d2Transfer552Lo,d2Transfer552Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer552C1 d2Transfer552S1 d2Log20Q d2Log20Lo d2Log20Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log20Bounds
  have har : (((weightedUpper d2Transfer552C0 d2Log154Lo d2Log154Hi:ℚ):ℝ) + ((weightedUpper d2Transfer552C1 d2Log20Lo d2Log20Hi:ℚ):ℝ)) ≤ ((d2Transfer552Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer552Arithmetic
  linarith
#print axioms d2Transfer552Arithmetic
#print axioms d2Transfer552Bound
def d2Transfer553Lo : ℚ := (d2LitsNearTransfers069.q2 (1364656279) 1 (-31))
def d2Transfer553Hi : ℚ := (d2LitsNearTransfers069.q2 (85395875) 1 (-27))
def d2Transfer553Cap : ℚ := (d2LitsNearTransfers069.q2 (2752225243658253026133) 1 (-80))
def d2Transfer553C0 : ℚ := (d2LitsNearTransfers069.q2 (-1) 55 (-3))
def d2Transfer553S0 : ℚ := (d2LitsNearTransfers069.q2 (-1) 1 (0))
def d2Transfer553C1 : ℚ := (d2LitsNearTransfers069.q2 (-1) 55 (-3))
def d2Transfer553S1 : ℚ := (d2LitsNearTransfers069.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer553Arithmetic : weightedUpper d2Transfer553C0 d2Log154Lo d2Log154Hi + weightedUpper d2Transfer553C1 d2Log19Lo d2Log19Hi ≤ d2Transfer553Cap := by decide +kernel
theorem d2Transfer553Bound : ∀ x ∈ Set.Icc ((d2Transfer553Lo:ℚ):ℝ) ((d2Transfer553Hi:ℚ):ℝ), ((d2Transfer553C0:ℚ):ℝ)*Real.log |x-((d2Transfer553S0:ℚ):ℝ)| + ((d2Transfer553C1:ℚ):ℝ)*Real.log |x-((d2Transfer553S1:ℚ):ℝ)| ≤ ((d2Transfer553Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer553S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer553S0,d2Transfer553Lo,d2Transfer553Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer553C0 then |x-((d2Transfer553S0:ℚ):ℝ)| ≤ ((d2Log154Q:ℚ):ℝ) else ((d2Log154Q:ℚ):ℝ) ≤ |x-((d2Transfer553S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer553S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer553S0,d2Transfer553Lo,d2Transfer553Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer553C0,d2Log154Q,d2Transfer553S0,d2Transfer553Lo,d2Transfer553Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer553C0 d2Transfer553S0 d2Log154Q d2Log154Lo d2Log154Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log154Bounds
  have hn1 : x-((d2Transfer553S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer553S1,d2Transfer553Lo,d2Transfer553Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer553C1 then |x-((d2Transfer553S1:ℚ):ℝ)| ≤ ((d2Log19Q:ℚ):ℝ) else ((d2Log19Q:ℚ):ℝ) ≤ |x-((d2Transfer553S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer553S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer553S1,d2Transfer553Lo,d2Transfer553Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer553C1,d2Log19Q,d2Transfer553S1,d2Transfer553Lo,d2Transfer553Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer553C1 d2Transfer553S1 d2Log19Q d2Log19Lo d2Log19Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log19Bounds
  have har : (((weightedUpper d2Transfer553C0 d2Log154Lo d2Log154Hi:ℚ):ℝ) + ((weightedUpper d2Transfer553C1 d2Log19Lo d2Log19Hi:ℚ):ℝ)) ≤ ((d2Transfer553Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer553Arithmetic
  linarith
#print axioms d2Transfer553Arithmetic
#print axioms d2Transfer553Bound
def d2Transfer554Lo : ℚ := (d2LitsNearTransfers069.q2 (1364656279) 1 (-31))
def d2Transfer554Hi : ℚ := (d2LitsNearTransfers069.q2 (85395875) 1 (-27))
def d2Transfer554Cap : ℚ := (d2LitsNearTransfers069.q2 (18084021117584539960149) 1 (-80))
def d2Transfer554C0 : ℚ := (d2LitsNearTransfers069.q2 (23) 25 (-5))
def d2Transfer554S0 : ℚ := (d2LitsNearTransfers069.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer554Arithmetic : weightedUpper d2Transfer554C0 d2Log155Lo d2Log155Hi ≤ d2Transfer554Cap := by decide +kernel
theorem d2Transfer554Bound : ∀ x ∈ Set.Icc ((d2Transfer554Lo:ℚ):ℝ) ((d2Transfer554Hi:ℚ):ℝ), ((d2Transfer554C0:ℚ):ℝ)*Real.log |x-((d2Transfer554S0:ℚ):ℝ)| ≤ ((d2Transfer554Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer554S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer554S0,d2Transfer554Lo,d2Transfer554Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer554C0 then |x-((d2Transfer554S0:ℚ):ℝ)| ≤ ((d2Log155Q:ℚ):ℝ) else ((d2Log155Q:ℚ):ℝ) ≤ |x-((d2Transfer554S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer554S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer554S0,d2Transfer554Lo,d2Transfer554Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer554C0,d2Log155Q,d2Transfer554S0,d2Transfer554Lo,d2Transfer554Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer554C0 d2Transfer554S0 d2Log155Q d2Log155Lo d2Log155Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log155Bounds
  have har : (((weightedUpper d2Transfer554C0 d2Log155Lo d2Log155Hi:ℚ):ℝ)) ≤ ((d2Transfer554Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer554Arithmetic
  linarith
#print axioms d2Transfer554Arithmetic
#print axioms d2Transfer554Bound
def d2Transfer555Lo : ℚ := (d2LitsNearTransfers069.q2 (1364656279) 1 (-31))
def d2Transfer555Hi : ℚ := (d2LitsNearTransfers069.q2 (85395875) 1 (-27))
def d2Transfer555Cap : ℚ := (d2LitsNearTransfers069.q2 (34935008508851810255701) 1 (-80))
def d2Transfer555C0 : ℚ := (d2LitsNearTransfers069.q2 (3) 275 (-5))
def d2Transfer555S0 : ℚ := (d2LitsNearTransfers069.q2 (-1) 1 (0))
def d2Transfer555C1 : ℚ := (d2LitsNearTransfers069.q2 (-5) 11 (-4))
def d2Transfer555S1 : ℚ := (d2LitsNearTransfers069.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer555Arithmetic : weightedUpper d2Transfer555C0 d2Log155Lo d2Log155Hi + weightedUpper d2Transfer555C1 d2Log19Lo d2Log19Hi ≤ d2Transfer555Cap := by decide +kernel
theorem d2Transfer555Bound : ∀ x ∈ Set.Icc ((d2Transfer555Lo:ℚ):ℝ) ((d2Transfer555Hi:ℚ):ℝ), ((d2Transfer555C0:ℚ):ℝ)*Real.log |x-((d2Transfer555S0:ℚ):ℝ)| + ((d2Transfer555C1:ℚ):ℝ)*Real.log |x-((d2Transfer555S1:ℚ):ℝ)| ≤ ((d2Transfer555Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer555S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer555S0,d2Transfer555Lo,d2Transfer555Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer555C0 then |x-((d2Transfer555S0:ℚ):ℝ)| ≤ ((d2Log155Q:ℚ):ℝ) else ((d2Log155Q:ℚ):ℝ) ≤ |x-((d2Transfer555S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer555S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer555S0,d2Transfer555Lo,d2Transfer555Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer555C0,d2Log155Q,d2Transfer555S0,d2Transfer555Lo,d2Transfer555Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer555C0 d2Transfer555S0 d2Log155Q d2Log155Lo d2Log155Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log155Bounds
  have hn1 : x-((d2Transfer555S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer555S1,d2Transfer555Lo,d2Transfer555Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer555C1 then |x-((d2Transfer555S1:ℚ):ℝ)| ≤ ((d2Log19Q:ℚ):ℝ) else ((d2Log19Q:ℚ):ℝ) ≤ |x-((d2Transfer555S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer555S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer555S1,d2Transfer555Lo,d2Transfer555Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer555C1,d2Log19Q,d2Transfer555S1,d2Transfer555Lo,d2Transfer555Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer555C1 d2Transfer555S1 d2Log19Q d2Log19Lo d2Log19Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log19Bounds
  have har : (((weightedUpper d2Transfer555C0 d2Log155Lo d2Log155Hi:ℚ):ℝ) + ((weightedUpper d2Transfer555C1 d2Log19Lo d2Log19Hi:ℚ):ℝ)) ≤ ((d2Transfer555Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer555Arithmetic
  linarith
#print axioms d2Transfer555Arithmetic
#print axioms d2Transfer555Bound
def d2Transfer556Lo : ℚ := (d2LitsNearTransfers069.q2 (85395875) 1 (-27))
def d2Transfer556Hi : ℚ := (d2LitsNearTransfers069.q2 (1368011721) 1 (-31))
def d2Transfer556Cap : ℚ := (d2LitsNearTransfers069.q2 (2826264967930141037325) 1 (-80))
def d2Transfer556C0 : ℚ := (d2LitsNearTransfers069.q2 (-1) 55 (-3))
def d2Transfer556S0 : ℚ := (d2LitsNearTransfers069.q2 (-1) 1 (0))
def d2Transfer556C1 : ℚ := (d2LitsNearTransfers069.q2 (-1) 55 (-3))
def d2Transfer556S1 : ℚ := (d2LitsNearTransfers069.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer556Arithmetic : weightedUpper d2Transfer556C0 d2Log155Lo d2Log155Hi + weightedUpper d2Transfer556C1 d2Log18Lo d2Log18Hi ≤ d2Transfer556Cap := by decide +kernel
theorem d2Transfer556Bound : ∀ x ∈ Set.Icc ((d2Transfer556Lo:ℚ):ℝ) ((d2Transfer556Hi:ℚ):ℝ), ((d2Transfer556C0:ℚ):ℝ)*Real.log |x-((d2Transfer556S0:ℚ):ℝ)| + ((d2Transfer556C1:ℚ):ℝ)*Real.log |x-((d2Transfer556S1:ℚ):ℝ)| ≤ ((d2Transfer556Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer556S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer556S0,d2Transfer556Lo,d2Transfer556Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer556C0 then |x-((d2Transfer556S0:ℚ):ℝ)| ≤ ((d2Log155Q:ℚ):ℝ) else ((d2Log155Q:ℚ):ℝ) ≤ |x-((d2Transfer556S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer556S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer556S0,d2Transfer556Lo,d2Transfer556Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer556C0,d2Log155Q,d2Transfer556S0,d2Transfer556Lo,d2Transfer556Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer556C0 d2Transfer556S0 d2Log155Q d2Log155Lo d2Log155Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log155Bounds
  have hn1 : x-((d2Transfer556S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer556S1,d2Transfer556Lo,d2Transfer556Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer556C1 then |x-((d2Transfer556S1:ℚ):ℝ)| ≤ ((d2Log18Q:ℚ):ℝ) else ((d2Log18Q:ℚ):ℝ) ≤ |x-((d2Transfer556S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer556S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer556S1,d2Transfer556Lo,d2Transfer556Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer556C1,d2Log18Q,d2Transfer556S1,d2Transfer556Lo,d2Transfer556Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer556C1 d2Transfer556S1 d2Log18Q d2Log18Lo d2Log18Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log18Bounds
  have har : (((weightedUpper d2Transfer556C0 d2Log155Lo d2Log155Hi:ℚ):ℝ) + ((weightedUpper d2Transfer556C1 d2Log18Lo d2Log18Hi:ℚ):ℝ)) ≤ ((d2Transfer556Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer556Arithmetic
  linarith
#print axioms d2Transfer556Arithmetic
#print axioms d2Transfer556Bound
def d2Transfer557Lo : ℚ := (d2LitsNearTransfers069.q2 (85395875) 1 (-27))
def d2Transfer557Hi : ℚ := (d2LitsNearTransfers069.q2 (1368011721) 1 (-31))
def d2Transfer557Cap : ℚ := (d2LitsNearTransfers069.q2 (18158060841856427971341) 1 (-80))
def d2Transfer557C0 : ℚ := (d2LitsNearTransfers069.q2 (23) 25 (-5))
def d2Transfer557S0 : ℚ := (d2LitsNearTransfers069.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer557Arithmetic : weightedUpper d2Transfer557C0 d2Log156Lo d2Log156Hi ≤ d2Transfer557Cap := by decide +kernel
theorem d2Transfer557Bound : ∀ x ∈ Set.Icc ((d2Transfer557Lo:ℚ):ℝ) ((d2Transfer557Hi:ℚ):ℝ), ((d2Transfer557C0:ℚ):ℝ)*Real.log |x-((d2Transfer557S0:ℚ):ℝ)| ≤ ((d2Transfer557Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer557S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer557S0,d2Transfer557Lo,d2Transfer557Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer557C0 then |x-((d2Transfer557S0:ℚ):ℝ)| ≤ ((d2Log156Q:ℚ):ℝ) else ((d2Log156Q:ℚ):ℝ) ≤ |x-((d2Transfer557S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer557S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer557S0,d2Transfer557Lo,d2Transfer557Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer557C0,d2Log156Q,d2Transfer557S0,d2Transfer557Lo,d2Transfer557Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer557C0 d2Transfer557S0 d2Log156Q d2Log156Lo d2Log156Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log156Bounds
  have har : (((weightedUpper d2Transfer557C0 d2Log156Lo d2Log156Hi:ℚ):ℝ)) ≤ ((d2Transfer557Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer557Arithmetic
  linarith
#print axioms d2Transfer557Arithmetic
#print axioms d2Transfer557Bound
def d2Transfer558Lo : ℚ := (d2LitsNearTransfers069.q2 (85395875) 1 (-27))
def d2Transfer558Hi : ℚ := (d2LitsNearTransfers069.q2 (1368011721) 1 (-31))
def d2Transfer558Cap : ℚ := (d2LitsNearTransfers069.q2 (35009048233123698266893) 1 (-80))
def d2Transfer558C0 : ℚ := (d2LitsNearTransfers069.q2 (3) 275 (-5))
def d2Transfer558S0 : ℚ := (d2LitsNearTransfers069.q2 (-1) 1 (0))
def d2Transfer558C1 : ℚ := (d2LitsNearTransfers069.q2 (-5) 11 (-4))
def d2Transfer558S1 : ℚ := (d2LitsNearTransfers069.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer558Arithmetic : weightedUpper d2Transfer558C0 d2Log156Lo d2Log156Hi + weightedUpper d2Transfer558C1 d2Log18Lo d2Log18Hi ≤ d2Transfer558Cap := by decide +kernel
theorem d2Transfer558Bound : ∀ x ∈ Set.Icc ((d2Transfer558Lo:ℚ):ℝ) ((d2Transfer558Hi:ℚ):ℝ), ((d2Transfer558C0:ℚ):ℝ)*Real.log |x-((d2Transfer558S0:ℚ):ℝ)| + ((d2Transfer558C1:ℚ):ℝ)*Real.log |x-((d2Transfer558S1:ℚ):ℝ)| ≤ ((d2Transfer558Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer558S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer558S0,d2Transfer558Lo,d2Transfer558Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer558C0 then |x-((d2Transfer558S0:ℚ):ℝ)| ≤ ((d2Log156Q:ℚ):ℝ) else ((d2Log156Q:ℚ):ℝ) ≤ |x-((d2Transfer558S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer558S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer558S0,d2Transfer558Lo,d2Transfer558Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer558C0,d2Log156Q,d2Transfer558S0,d2Transfer558Lo,d2Transfer558Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer558C0 d2Transfer558S0 d2Log156Q d2Log156Lo d2Log156Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log156Bounds
  have hn1 : x-((d2Transfer558S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer558S1,d2Transfer558Lo,d2Transfer558Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer558C1 then |x-((d2Transfer558S1:ℚ):ℝ)| ≤ ((d2Log18Q:ℚ):ℝ) else ((d2Log18Q:ℚ):ℝ) ≤ |x-((d2Transfer558S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer558S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer558S1,d2Transfer558Lo,d2Transfer558Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer558C1,d2Log18Q,d2Transfer558S1,d2Transfer558Lo,d2Transfer558Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer558C1 d2Transfer558S1 d2Log18Q d2Log18Lo d2Log18Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log18Bounds
  have har : (((weightedUpper d2Transfer558C0 d2Log156Lo d2Log156Hi:ℚ):ℝ) + ((weightedUpper d2Transfer558C1 d2Log18Lo d2Log18Hi:ℚ):ℝ)) ≤ ((d2Transfer558Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer558Arithmetic
  linarith
#print axioms d2Transfer558Arithmetic
#print axioms d2Transfer558Bound
def d2Transfer559Lo : ℚ := (d2LitsNearTransfers069.q2 (1368011721) 1 (-31))
def d2Transfer559Hi : ℚ := (d2LitsNearTransfers069.q2 (684844721) 1 (-30))
def d2Transfer559Cap : ℚ := (d2LitsNearTransfers069.q2 (1450231853993301240833) 1 (-79))
def d2Transfer559C0 : ℚ := (d2LitsNearTransfers069.q2 (-1) 55 (-3))
def d2Transfer559S0 : ℚ := (d2LitsNearTransfers069.q2 (-1) 1 (0))
def d2Transfer559C1 : ℚ := (d2LitsNearTransfers069.q2 (-1) 55 (-3))
def d2Transfer559S1 : ℚ := (d2LitsNearTransfers069.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer559Arithmetic : weightedUpper d2Transfer559C0 d2Log156Lo d2Log156Hi + weightedUpper d2Transfer559C1 d2Log17Lo d2Log17Hi ≤ d2Transfer559Cap := by decide +kernel
theorem d2Transfer559Bound : ∀ x ∈ Set.Icc ((d2Transfer559Lo:ℚ):ℝ) ((d2Transfer559Hi:ℚ):ℝ), ((d2Transfer559C0:ℚ):ℝ)*Real.log |x-((d2Transfer559S0:ℚ):ℝ)| + ((d2Transfer559C1:ℚ):ℝ)*Real.log |x-((d2Transfer559S1:ℚ):ℝ)| ≤ ((d2Transfer559Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer559S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer559S0,d2Transfer559Lo,d2Transfer559Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer559C0 then |x-((d2Transfer559S0:ℚ):ℝ)| ≤ ((d2Log156Q:ℚ):ℝ) else ((d2Log156Q:ℚ):ℝ) ≤ |x-((d2Transfer559S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer559S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer559S0,d2Transfer559Lo,d2Transfer559Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer559C0,d2Log156Q,d2Transfer559S0,d2Transfer559Lo,d2Transfer559Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer559C0 d2Transfer559S0 d2Log156Q d2Log156Lo d2Log156Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log156Bounds
  have hn1 : x-((d2Transfer559S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer559S1,d2Transfer559Lo,d2Transfer559Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer559C1 then |x-((d2Transfer559S1:ℚ):ℝ)| ≤ ((d2Log17Q:ℚ):ℝ) else ((d2Log17Q:ℚ):ℝ) ≤ |x-((d2Transfer559S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer559S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer559S1,d2Transfer559Lo,d2Transfer559Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers069.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer559C1,d2Log17Q,d2Transfer559S1,d2Transfer559Lo,d2Transfer559Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer559C1 d2Transfer559S1 d2Log17Q d2Log17Lo d2Log17Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log17Bounds
  have har : (((weightedUpper d2Transfer559C0 d2Log156Lo d2Log156Hi:ℚ):ℝ) + ((weightedUpper d2Transfer559C1 d2Log17Lo d2Log17Hi:ℚ):ℝ)) ≤ ((d2Transfer559Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer559Arithmetic
  linarith
#print axioms d2Transfer559Arithmetic
#print axioms d2Transfer559Bound
end CatalanMeasure.GenD.Signed.Data.Cells

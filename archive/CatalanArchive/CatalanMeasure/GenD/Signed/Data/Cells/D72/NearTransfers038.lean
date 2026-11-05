module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
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
namespace d2LitsNearTransfers038
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers038
open D72.LogTransfer
def d2Transfer304Lo : ℚ := (d2LitsNearTransfers038.q2 (1347879069) 1 (-31))
def d2Transfer304Hi : ℚ := (d2LitsNearTransfers038.q2 (674778395) 1 (-30))
def d2Transfer304Cap : ℚ := (d2LitsNearTransfers038.q2 (19312113543620910650705) 1 (-80))
def d2Transfer304C0 : ℚ := (d2LitsNearTransfers038.q2 (1) 1 (-5))
def d2Transfer304S0 : ℚ := (d2LitsNearTransfers038.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer304Arithmetic : weightedUpper d2Transfer304C0 d2Log145Lo d2Log145Hi ≤ d2Transfer304Cap := by decide +kernel
theorem d2Transfer304Bound : ∀ x ∈ Set.Icc ((d2Transfer304Lo:ℚ):ℝ) ((d2Transfer304Hi:ℚ):ℝ), ((d2Transfer304C0:ℚ):ℝ)*Real.log |x-((d2Transfer304S0:ℚ):ℝ)| ≤ ((d2Transfer304Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer304S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer304S0,d2Transfer304Lo,d2Transfer304Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer304C0 then |x-((d2Transfer304S0:ℚ):ℝ)| ≤ ((d2Log145Q:ℚ):ℝ) else ((d2Log145Q:ℚ):ℝ) ≤ |x-((d2Transfer304S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer304S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer304S0,d2Transfer304Lo,d2Transfer304Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer304C0,d2Log145Q,d2Transfer304S0,d2Transfer304Lo,d2Transfer304Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer304C0 d2Transfer304S0 d2Log145Q d2Log145Lo d2Log145Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log145Bounds
  have har : (((weightedUpper d2Transfer304C0 d2Log145Lo d2Log145Hi:ℚ):ℝ)) ≤ ((d2Transfer304Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer304Arithmetic
  linarith
#print axioms d2Transfer304Arithmetic
#print axioms d2Transfer304Bound
def d2Transfer305Lo : ℚ := (d2LitsNearTransfers038.q2 (1347879069) 1 (-31))
def d2Transfer305Hi : ℚ := (d2LitsNearTransfers038.q2 (674778395) 1 (-30))
def d2Transfer305Cap : ℚ := (d2LitsNearTransfers038.q2 (35676950865912418014545) 1 (-80))
def d2Transfer305C0 : ℚ := (d2LitsNearTransfers038.q2 (1) 11 (-5))
def d2Transfer305S0 : ℚ := (d2LitsNearTransfers038.q2 (-1) 1 (0))
def d2Transfer305C1 : ℚ := (d2LitsNearTransfers038.q2 (-5) 11 (-4))
def d2Transfer305S1 : ℚ := (d2LitsNearTransfers038.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer305Arithmetic : weightedUpper d2Transfer305C0 d2Log145Lo d2Log145Hi + weightedUpper d2Transfer305C1 d2Log29Lo d2Log29Hi ≤ d2Transfer305Cap := by decide +kernel
theorem d2Transfer305Bound : ∀ x ∈ Set.Icc ((d2Transfer305Lo:ℚ):ℝ) ((d2Transfer305Hi:ℚ):ℝ), ((d2Transfer305C0:ℚ):ℝ)*Real.log |x-((d2Transfer305S0:ℚ):ℝ)| + ((d2Transfer305C1:ℚ):ℝ)*Real.log |x-((d2Transfer305S1:ℚ):ℝ)| ≤ ((d2Transfer305Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer305S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer305S0,d2Transfer305Lo,d2Transfer305Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer305C0 then |x-((d2Transfer305S0:ℚ):ℝ)| ≤ ((d2Log145Q:ℚ):ℝ) else ((d2Log145Q:ℚ):ℝ) ≤ |x-((d2Transfer305S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer305S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer305S0,d2Transfer305Lo,d2Transfer305Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer305C0,d2Log145Q,d2Transfer305S0,d2Transfer305Lo,d2Transfer305Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer305C0 d2Transfer305S0 d2Log145Q d2Log145Lo d2Log145Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log145Bounds
  have hn1 : x-((d2Transfer305S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer305S1,d2Transfer305Lo,d2Transfer305Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer305C1 then |x-((d2Transfer305S1:ℚ):ℝ)| ≤ ((d2Log29Q:ℚ):ℝ) else ((d2Log29Q:ℚ):ℝ) ≤ |x-((d2Transfer305S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer305S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer305S1,d2Transfer305Lo,d2Transfer305Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer305C1,d2Log29Q,d2Transfer305S1,d2Transfer305Lo,d2Transfer305Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer305C1 d2Transfer305S1 d2Log29Q d2Log29Lo d2Log29Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log29Bounds
  have har : (((weightedUpper d2Transfer305C0 d2Log145Lo d2Log145Hi:ℚ):ℝ) + ((weightedUpper d2Transfer305C1 d2Log29Lo d2Log29Hi:ℚ):ℝ)) ≤ ((d2Transfer305Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer305Arithmetic
  linarith
#print axioms d2Transfer305Arithmetic
#print axioms d2Transfer305Bound
def d2Transfer306Lo : ℚ := (d2LitsNearTransfers038.q2 (674778395) 1 (-30))
def d2Transfer306Hi : ℚ := (d2LitsNearTransfers038.q2 (1351234511) 1 (-31))
def d2Transfer306Cap : ℚ := (d2LitsNearTransfers038.q2 (1456343657972225333883) 1 (-79))
def d2Transfer306C0 : ℚ := (d2LitsNearTransfers038.q2 (1) 25 (-4))
def d2Transfer306S0 : ℚ := (d2LitsNearTransfers038.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer306Arithmetic : weightedUpper d2Transfer306C0 d2Log146Lo d2Log146Hi ≤ d2Transfer306Cap := by decide +kernel
theorem d2Transfer306Bound : ∀ x ∈ Set.Icc ((d2Transfer306Lo:ℚ):ℝ) ((d2Transfer306Hi:ℚ):ℝ), ((d2Transfer306C0:ℚ):ℝ)*Real.log |x-((d2Transfer306S0:ℚ):ℝ)| ≤ ((d2Transfer306Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer306S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer306S0,d2Transfer306Lo,d2Transfer306Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer306C0 then |x-((d2Transfer306S0:ℚ):ℝ)| ≤ ((d2Log146Q:ℚ):ℝ) else ((d2Log146Q:ℚ):ℝ) ≤ |x-((d2Transfer306S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer306S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer306S0,d2Transfer306Lo,d2Transfer306Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer306C0,d2Log146Q,d2Transfer306S0,d2Transfer306Lo,d2Transfer306Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer306C0 d2Transfer306S0 d2Log146Q d2Log146Lo d2Log146Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log146Bounds
  have har : (((weightedUpper d2Transfer306C0 d2Log146Lo d2Log146Hi:ℚ):ℝ)) ≤ ((d2Transfer306Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer306Arithmetic
  linarith
#print axioms d2Transfer306Arithmetic
#print axioms d2Transfer306Bound
def d2Transfer307Lo : ℚ := (d2LitsNearTransfers038.q2 (674778395) 1 (-30))
def d2Transfer307Hi : ℚ := (d2LitsNearTransfers038.q2 (1351234511) 1 (-31))
def d2Transfer307Cap : ℚ := (d2LitsNearTransfers038.q2 (2081493742290093005435) 1 (-79))
def d2Transfer307C0 : ℚ := (d2LitsNearTransfers038.q2 (1) 275 (-4))
def d2Transfer307S0 : ℚ := (d2LitsNearTransfers038.q2 (-1) 1 (0))
def d2Transfer307C1 : ℚ := (d2LitsNearTransfers038.q2 (-1) 55 (-3))
def d2Transfer307S1 : ℚ := (d2LitsNearTransfers038.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer307Arithmetic : weightedUpper d2Transfer307C0 d2Log146Lo d2Log146Hi + weightedUpper d2Transfer307C1 d2Log28Lo d2Log28Hi ≤ d2Transfer307Cap := by decide +kernel
theorem d2Transfer307Bound : ∀ x ∈ Set.Icc ((d2Transfer307Lo:ℚ):ℝ) ((d2Transfer307Hi:ℚ):ℝ), ((d2Transfer307C0:ℚ):ℝ)*Real.log |x-((d2Transfer307S0:ℚ):ℝ)| + ((d2Transfer307C1:ℚ):ℝ)*Real.log |x-((d2Transfer307S1:ℚ):ℝ)| ≤ ((d2Transfer307Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer307S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer307S0,d2Transfer307Lo,d2Transfer307Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer307C0 then |x-((d2Transfer307S0:ℚ):ℝ)| ≤ ((d2Log146Q:ℚ):ℝ) else ((d2Log146Q:ℚ):ℝ) ≤ |x-((d2Transfer307S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer307S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer307S0,d2Transfer307Lo,d2Transfer307Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer307C0,d2Log146Q,d2Transfer307S0,d2Transfer307Lo,d2Transfer307Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer307C0 d2Transfer307S0 d2Log146Q d2Log146Lo d2Log146Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log146Bounds
  have hn1 : x-((d2Transfer307S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer307S1,d2Transfer307Lo,d2Transfer307Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer307C1 then |x-((d2Transfer307S1:ℚ):ℝ)| ≤ ((d2Log28Q:ℚ):ℝ) else ((d2Log28Q:ℚ):ℝ) ≤ |x-((d2Transfer307S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer307S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer307S1,d2Transfer307Lo,d2Transfer307Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer307C1,d2Log28Q,d2Transfer307S1,d2Transfer307Lo,d2Transfer307Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer307C1 d2Transfer307S1 d2Log28Q d2Log28Lo d2Log28Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log28Bounds
  have har : (((weightedUpper d2Transfer307C0 d2Log146Lo d2Log146Hi:ℚ):ℝ) + ((weightedUpper d2Transfer307C1 d2Log28Lo d2Log28Hi:ℚ):ℝ)) ≤ ((d2Transfer307Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer307Arithmetic
  linarith
#print axioms d2Transfer307Arithmetic
#print axioms d2Transfer307Bound
def d2Transfer308Lo : ℚ := (d2LitsNearTransfers038.q2 (674778395) 1 (-30))
def d2Transfer308Hi : ℚ := (d2LitsNearTransfers038.q2 (1351234511) 1 (-31))
def d2Transfer308Cap : ℚ := (d2LitsNearTransfers038.q2 (9693024787501573266043) 1 (-79))
def d2Transfer308C0 : ℚ := (d2LitsNearTransfers038.q2 (1) 1 (-5))
def d2Transfer308S0 : ℚ := (d2LitsNearTransfers038.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer308Arithmetic : weightedUpper d2Transfer308C0 d2Log146Lo d2Log146Hi ≤ d2Transfer308Cap := by decide +kernel
theorem d2Transfer308Bound : ∀ x ∈ Set.Icc ((d2Transfer308Lo:ℚ):ℝ) ((d2Transfer308Hi:ℚ):ℝ), ((d2Transfer308C0:ℚ):ℝ)*Real.log |x-((d2Transfer308S0:ℚ):ℝ)| ≤ ((d2Transfer308Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer308S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer308S0,d2Transfer308Lo,d2Transfer308Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer308C0 then |x-((d2Transfer308S0:ℚ):ℝ)| ≤ ((d2Log146Q:ℚ):ℝ) else ((d2Log146Q:ℚ):ℝ) ≤ |x-((d2Transfer308S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer308S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer308S0,d2Transfer308Lo,d2Transfer308Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer308C0,d2Log146Q,d2Transfer308S0,d2Transfer308Lo,d2Transfer308Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer308C0 d2Transfer308S0 d2Log146Q d2Log146Lo d2Log146Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log146Bounds
  have har : (((weightedUpper d2Transfer308C0 d2Log146Lo d2Log146Hi:ℚ):ℝ)) ≤ ((d2Transfer308Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer308Arithmetic
  linarith
#print axioms d2Transfer308Arithmetic
#print axioms d2Transfer308Bound
def d2Transfer309Lo : ℚ := (d2LitsNearTransfers038.q2 (674778395) 1 (-30))
def d2Transfer309Hi : ℚ := (d2LitsNearTransfers038.q2 (1351234511) 1 (-31))
def d2Transfer309Cap : ℚ := (d2LitsNearTransfers038.q2 (17875443448647326947963) 1 (-79))
def d2Transfer309C0 : ℚ := (d2LitsNearTransfers038.q2 (1) 11 (-5))
def d2Transfer309S0 : ℚ := (d2LitsNearTransfers038.q2 (-1) 1 (0))
def d2Transfer309C1 : ℚ := (d2LitsNearTransfers038.q2 (-5) 11 (-4))
def d2Transfer309S1 : ℚ := (d2LitsNearTransfers038.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer309Arithmetic : weightedUpper d2Transfer309C0 d2Log146Lo d2Log146Hi + weightedUpper d2Transfer309C1 d2Log28Lo d2Log28Hi ≤ d2Transfer309Cap := by decide +kernel
theorem d2Transfer309Bound : ∀ x ∈ Set.Icc ((d2Transfer309Lo:ℚ):ℝ) ((d2Transfer309Hi:ℚ):ℝ), ((d2Transfer309C0:ℚ):ℝ)*Real.log |x-((d2Transfer309S0:ℚ):ℝ)| + ((d2Transfer309C1:ℚ):ℝ)*Real.log |x-((d2Transfer309S1:ℚ):ℝ)| ≤ ((d2Transfer309Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer309S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer309S0,d2Transfer309Lo,d2Transfer309Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer309C0 then |x-((d2Transfer309S0:ℚ):ℝ)| ≤ ((d2Log146Q:ℚ):ℝ) else ((d2Log146Q:ℚ):ℝ) ≤ |x-((d2Transfer309S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer309S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer309S0,d2Transfer309Lo,d2Transfer309Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer309C0,d2Log146Q,d2Transfer309S0,d2Transfer309Lo,d2Transfer309Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer309C0 d2Transfer309S0 d2Log146Q d2Log146Lo d2Log146Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log146Bounds
  have hn1 : x-((d2Transfer309S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer309S1,d2Transfer309Lo,d2Transfer309Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer309C1 then |x-((d2Transfer309S1:ℚ):ℝ)| ≤ ((d2Log28Q:ℚ):ℝ) else ((d2Log28Q:ℚ):ℝ) ≤ |x-((d2Transfer309S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer309S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer309S1,d2Transfer309Lo,d2Transfer309Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer309C1,d2Log28Q,d2Transfer309S1,d2Transfer309Lo,d2Transfer309Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer309C1 d2Transfer309S1 d2Log28Q d2Log28Lo d2Log28Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log28Bounds
  have har : (((weightedUpper d2Transfer309C0 d2Log146Lo d2Log146Hi:ℚ):ℝ) + ((weightedUpper d2Transfer309C1 d2Log28Lo d2Log28Hi:ℚ):ℝ)) ≤ ((d2Transfer309Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer309Arithmetic
  linarith
#print axioms d2Transfer309Arithmetic
#print axioms d2Transfer309Bound
def d2Transfer310Lo : ℚ := (d2LitsNearTransfers038.q2 (1351234511) 1 (-31))
def d2Transfer310Hi : ℚ := (d2LitsNearTransfers038.q2 (169114029) 1 (-28))
def d2Transfer310Cap : ℚ := (d2LitsNearTransfers038.q2 (1493387516446464078587) 1 (-79))
def d2Transfer310C0 : ℚ := (d2LitsNearTransfers038.q2 (1) 25 (-4))
def d2Transfer310S0 : ℚ := (d2LitsNearTransfers038.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer310Arithmetic : weightedUpper d2Transfer310C0 d2Log147Lo d2Log147Hi ≤ d2Transfer310Cap := by decide +kernel
theorem d2Transfer310Bound : ∀ x ∈ Set.Icc ((d2Transfer310Lo:ℚ):ℝ) ((d2Transfer310Hi:ℚ):ℝ), ((d2Transfer310C0:ℚ):ℝ)*Real.log |x-((d2Transfer310S0:ℚ):ℝ)| ≤ ((d2Transfer310Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer310S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer310S0,d2Transfer310Lo,d2Transfer310Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer310C0 then |x-((d2Transfer310S0:ℚ):ℝ)| ≤ ((d2Log147Q:ℚ):ℝ) else ((d2Log147Q:ℚ):ℝ) ≤ |x-((d2Transfer310S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer310S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer310S0,d2Transfer310Lo,d2Transfer310Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer310C0,d2Log147Q,d2Transfer310S0,d2Transfer310Lo,d2Transfer310Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer310C0 d2Transfer310S0 d2Log147Q d2Log147Lo d2Log147Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log147Bounds
  have har : (((weightedUpper d2Transfer310C0 d2Log147Lo d2Log147Hi:ℚ):ℝ)) ≤ ((d2Transfer310Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer310Arithmetic
  linarith
#print axioms d2Transfer310Arithmetic
#print axioms d2Transfer310Bound
def d2Transfer311Lo : ℚ := (d2LitsNearTransfers038.q2 (1351234511) 1 (-31))
def d2Transfer311Hi : ℚ := (d2LitsNearTransfers038.q2 (169114029) 1 (-28))
def d2Transfer311Cap : ℚ := (d2LitsNearTransfers038.q2 (2118537600764331750139) 1 (-79))
def d2Transfer311C0 : ℚ := (d2LitsNearTransfers038.q2 (1) 275 (-4))
def d2Transfer311S0 : ℚ := (d2LitsNearTransfers038.q2 (-1) 1 (0))
def d2Transfer311C1 : ℚ := (d2LitsNearTransfers038.q2 (-1) 55 (-3))
def d2Transfer311S1 : ℚ := (d2LitsNearTransfers038.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer311Arithmetic : weightedUpper d2Transfer311C0 d2Log147Lo d2Log147Hi + weightedUpper d2Transfer311C1 d2Log27Lo d2Log27Hi ≤ d2Transfer311Cap := by decide +kernel
theorem d2Transfer311Bound : ∀ x ∈ Set.Icc ((d2Transfer311Lo:ℚ):ℝ) ((d2Transfer311Hi:ℚ):ℝ), ((d2Transfer311C0:ℚ):ℝ)*Real.log |x-((d2Transfer311S0:ℚ):ℝ)| + ((d2Transfer311C1:ℚ):ℝ)*Real.log |x-((d2Transfer311S1:ℚ):ℝ)| ≤ ((d2Transfer311Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer311S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer311S0,d2Transfer311Lo,d2Transfer311Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer311C0 then |x-((d2Transfer311S0:ℚ):ℝ)| ≤ ((d2Log147Q:ℚ):ℝ) else ((d2Log147Q:ℚ):ℝ) ≤ |x-((d2Transfer311S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer311S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer311S0,d2Transfer311Lo,d2Transfer311Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer311C0,d2Log147Q,d2Transfer311S0,d2Transfer311Lo,d2Transfer311Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer311C0 d2Transfer311S0 d2Log147Q d2Log147Lo d2Log147Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log147Bounds
  have hn1 : x-((d2Transfer311S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer311S1,d2Transfer311Lo,d2Transfer311Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer311C1 then |x-((d2Transfer311S1:ℚ):ℝ)| ≤ ((d2Log27Q:ℚ):ℝ) else ((d2Log27Q:ℚ):ℝ) ≤ |x-((d2Transfer311S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer311S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer311S1,d2Transfer311Lo,d2Transfer311Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer311C1,d2Log27Q,d2Transfer311S1,d2Transfer311Lo,d2Transfer311Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer311C1 d2Transfer311S1 d2Log27Q d2Log27Lo d2Log27Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log27Bounds
  have har : (((weightedUpper d2Transfer311C0 d2Log147Lo d2Log147Hi:ℚ):ℝ) + ((weightedUpper d2Transfer311C1 d2Log27Lo d2Log27Hi:ℚ):ℝ)) ≤ ((d2Transfer311Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer311Arithmetic
  linarith
#print axioms d2Transfer311Arithmetic
#print axioms d2Transfer311Bound
end CatalanMeasure.GenD.Signed.Data.Cells

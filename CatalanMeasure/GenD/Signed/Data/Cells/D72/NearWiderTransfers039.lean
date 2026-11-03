module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
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
namespace d2LitsNearWiderTransfers039
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers039
open D72.LogTransfer
def d2WiderTransfer312Lo : ℚ := (d2LitsNearWiderTransfers039.q2 (336550337) 1 (-29))
def d2WiderTransfer312Hi : ℚ := (d2LitsNearWiderTransfers039.q2 (1347879069) 1 (-31))
def d2WiderTransfer312Cap : ℚ := (d2LitsNearWiderTransfers039.q2 (34130874385935324799375) 1 (-80))
def d2WiderTransfer312C0 : ℚ := (d2LitsNearWiderTransfers039.q2 (3) 275 (-5))
def d2WiderTransfer312S0 : ℚ := (d2LitsNearWiderTransfers039.q2 (-1) 1 (0))
def d2WiderTransfer312C1 : ℚ := (d2LitsNearWiderTransfers039.q2 (-5) 11 (-4))
def d2WiderTransfer312S1 : ℚ := (d2LitsNearWiderTransfers039.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer312Arithmetic : weightedUpper d2WiderTransfer312C0 d2Log144Lo d2Log144Hi + weightedUpper d2WiderTransfer312C1 d2Log30Lo d2Log30Hi ≤ d2WiderTransfer312Cap := by decide +kernel
theorem d2WiderTransfer312Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer312Lo:ℚ):ℝ) ((d2WiderTransfer312Hi:ℚ):ℝ), ((d2WiderTransfer312C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer312S0:ℚ):ℝ)| + ((d2WiderTransfer312C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer312S1:ℚ):ℝ)| ≤ ((d2WiderTransfer312Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer312S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer312S0,d2WiderTransfer312Lo,d2WiderTransfer312Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer312C0 then |x-((d2WiderTransfer312S0:ℚ):ℝ)| ≤ ((d2Log144Q:ℚ):ℝ) else ((d2Log144Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer312S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer312S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer312S0,d2WiderTransfer312Lo,d2WiderTransfer312Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer312C0,d2Log144Q,d2WiderTransfer312S0,d2WiderTransfer312Lo,d2WiderTransfer312Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer312C0 d2WiderTransfer312S0 d2Log144Q d2Log144Lo d2Log144Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log144Bounds
  have hn1 : x-((d2WiderTransfer312S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer312S1,d2WiderTransfer312Lo,d2WiderTransfer312Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer312C1 then |x-((d2WiderTransfer312S1:ℚ):ℝ)| ≤ ((d2Log30Q:ℚ):ℝ) else ((d2Log30Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer312S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer312S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer312S1,d2WiderTransfer312Lo,d2WiderTransfer312Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer312C1,d2Log30Q,d2WiderTransfer312S1,d2WiderTransfer312Lo,d2WiderTransfer312Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer312C1 d2WiderTransfer312S1 d2Log30Q d2Log30Lo d2Log30Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log30Bounds
  have har : (((weightedUpper d2WiderTransfer312C0 d2Log144Lo d2Log144Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer312C1 d2Log30Lo d2Log30Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer312Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer312Arithmetic
  linarith
#print axioms d2WiderTransfer312Arithmetic
#print axioms d2WiderTransfer312Bound
def d2WiderTransfer313Lo : ℚ := (d2LitsNearWiderTransfers039.q2 (1347879069) 1 (-31))
def d2WiderTransfer313Hi : ℚ := (d2LitsNearWiderTransfers039.q2 (674778395) 1 (-30))
def d2WiderTransfer313Cap : ℚ := (d2LitsNearWiderTransfers039.q2 (2020425790803095201589) 1 (-80))
def d2WiderTransfer313C0 : ℚ := (d2LitsNearWiderTransfers039.q2 (-1) 55 (-3))
def d2WiderTransfer313S0 : ℚ := (d2LitsNearWiderTransfers039.q2 (-1) 1 (0))
def d2WiderTransfer313C1 : ℚ := (d2LitsNearWiderTransfers039.q2 (-1) 55 (-3))
def d2WiderTransfer313S1 : ℚ := (d2LitsNearWiderTransfers039.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer313Arithmetic : weightedUpper d2WiderTransfer313C0 d2Log144Lo d2Log144Hi + weightedUpper d2WiderTransfer313C1 d2Log29Lo d2Log29Hi ≤ d2WiderTransfer313Cap := by decide +kernel
theorem d2WiderTransfer313Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer313Lo:ℚ):ℝ) ((d2WiderTransfer313Hi:ℚ):ℝ), ((d2WiderTransfer313C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer313S0:ℚ):ℝ)| + ((d2WiderTransfer313C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer313S1:ℚ):ℝ)| ≤ ((d2WiderTransfer313Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer313S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer313S0,d2WiderTransfer313Lo,d2WiderTransfer313Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer313C0 then |x-((d2WiderTransfer313S0:ℚ):ℝ)| ≤ ((d2Log144Q:ℚ):ℝ) else ((d2Log144Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer313S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer313S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer313S0,d2WiderTransfer313Lo,d2WiderTransfer313Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer313C0,d2Log144Q,d2WiderTransfer313S0,d2WiderTransfer313Lo,d2WiderTransfer313Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer313C0 d2WiderTransfer313S0 d2Log144Q d2Log144Lo d2Log144Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log144Bounds
  have hn1 : x-((d2WiderTransfer313S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer313S1,d2WiderTransfer313Lo,d2WiderTransfer313Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer313C1 then |x-((d2WiderTransfer313S1:ℚ):ℝ)| ≤ ((d2Log29Q:ℚ):ℝ) else ((d2Log29Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer313S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer313S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer313S1,d2WiderTransfer313Lo,d2WiderTransfer313Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer313C1,d2Log29Q,d2WiderTransfer313S1,d2WiderTransfer313Lo,d2WiderTransfer313Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer313C1 d2WiderTransfer313S1 d2Log29Q d2Log29Lo d2Log29Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log29Bounds
  have har : (((weightedUpper d2WiderTransfer313C0 d2Log144Lo d2Log144Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer313C1 d2Log29Lo d2Log29Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer313Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer313Arithmetic
  linarith
#print axioms d2WiderTransfer313Arithmetic
#print axioms d2WiderTransfer313Bound
def d2WiderTransfer314Lo : ℚ := (d2LitsNearWiderTransfers039.q2 (1347879069) 1 (-31))
def d2WiderTransfer314Hi : ℚ := (d2LitsNearWiderTransfers039.q2 (674778395) 1 (-30))
def d2WiderTransfer314Cap : ℚ := (d2LitsNearWiderTransfers039.q2 (17352221664729382135605) 1 (-80))
def d2WiderTransfer314C0 : ℚ := (d2LitsNearWiderTransfers039.q2 (23) 25 (-5))
def d2WiderTransfer314S0 : ℚ := (d2LitsNearWiderTransfers039.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer314Arithmetic : weightedUpper d2WiderTransfer314C0 d2Log145Lo d2Log145Hi ≤ d2WiderTransfer314Cap := by decide +kernel
theorem d2WiderTransfer314Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer314Lo:ℚ):ℝ) ((d2WiderTransfer314Hi:ℚ):ℝ), ((d2WiderTransfer314C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer314S0:ℚ):ℝ)| ≤ ((d2WiderTransfer314Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer314S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer314S0,d2WiderTransfer314Lo,d2WiderTransfer314Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer314C0 then |x-((d2WiderTransfer314S0:ℚ):ℝ)| ≤ ((d2Log145Q:ℚ):ℝ) else ((d2Log145Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer314S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer314S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer314S0,d2WiderTransfer314Lo,d2WiderTransfer314Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer314C0,d2Log145Q,d2WiderTransfer314S0,d2WiderTransfer314Lo,d2WiderTransfer314Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer314C0 d2WiderTransfer314S0 d2Log145Q d2Log145Lo d2Log145Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log145Bounds
  have har : (((weightedUpper d2WiderTransfer314C0 d2Log145Lo d2Log145Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer314Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer314Arithmetic
  linarith
#print axioms d2WiderTransfer314Arithmetic
#print axioms d2WiderTransfer314Bound
def d2WiderTransfer315Lo : ℚ := (d2LitsNearWiderTransfers039.q2 (1347879069) 1 (-31))
def d2WiderTransfer315Hi : ℚ := (d2LitsNearWiderTransfers039.q2 (674778395) 1 (-30))
def d2WiderTransfer315Cap : ℚ := (d2LitsNearWiderTransfers039.q2 (34203209055996652431157) 1 (-80))
def d2WiderTransfer315C0 : ℚ := (d2LitsNearWiderTransfers039.q2 (3) 275 (-5))
def d2WiderTransfer315S0 : ℚ := (d2LitsNearWiderTransfers039.q2 (-1) 1 (0))
def d2WiderTransfer315C1 : ℚ := (d2LitsNearWiderTransfers039.q2 (-5) 11 (-4))
def d2WiderTransfer315S1 : ℚ := (d2LitsNearWiderTransfers039.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer315Arithmetic : weightedUpper d2WiderTransfer315C0 d2Log145Lo d2Log145Hi + weightedUpper d2WiderTransfer315C1 d2Log29Lo d2Log29Hi ≤ d2WiderTransfer315Cap := by decide +kernel
theorem d2WiderTransfer315Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer315Lo:ℚ):ℝ) ((d2WiderTransfer315Hi:ℚ):ℝ), ((d2WiderTransfer315C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer315S0:ℚ):ℝ)| + ((d2WiderTransfer315C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer315S1:ℚ):ℝ)| ≤ ((d2WiderTransfer315Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer315S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer315S0,d2WiderTransfer315Lo,d2WiderTransfer315Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer315C0 then |x-((d2WiderTransfer315S0:ℚ):ℝ)| ≤ ((d2Log145Q:ℚ):ℝ) else ((d2Log145Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer315S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer315S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer315S0,d2WiderTransfer315Lo,d2WiderTransfer315Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer315C0,d2Log145Q,d2WiderTransfer315S0,d2WiderTransfer315Lo,d2WiderTransfer315Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer315C0 d2WiderTransfer315S0 d2Log145Q d2Log145Lo d2Log145Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log145Bounds
  have hn1 : x-((d2WiderTransfer315S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer315S1,d2WiderTransfer315Lo,d2WiderTransfer315Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer315C1 then |x-((d2WiderTransfer315S1:ℚ):ℝ)| ≤ ((d2Log29Q:ℚ):ℝ) else ((d2Log29Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer315S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer315S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer315S1,d2WiderTransfer315Lo,d2WiderTransfer315Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer315C1,d2Log29Q,d2WiderTransfer315S1,d2WiderTransfer315Lo,d2WiderTransfer315Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer315C1 d2WiderTransfer315S1 d2Log29Q d2Log29Lo d2Log29Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log29Bounds
  have har : (((weightedUpper d2WiderTransfer315C0 d2Log145Lo d2Log145Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer315C1 d2Log29Lo d2Log29Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer315Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer315Arithmetic
  linarith
#print axioms d2WiderTransfer315Arithmetic
#print axioms d2WiderTransfer315Bound
def d2WiderTransfer316Lo : ℚ := (d2LitsNearWiderTransfers039.q2 (674778395) 1 (-30))
def d2WiderTransfer316Hi : ℚ := (d2LitsNearWiderTransfers039.q2 (1351234511) 1 (-31))
def d2WiderTransfer316Cap : ℚ := (d2LitsNearWiderTransfers039.q2 (1046456100392806920763) 1 (-79))
def d2WiderTransfer316C0 : ℚ := (d2LitsNearWiderTransfers039.q2 (-1) 55 (-3))
def d2WiderTransfer316S0 : ℚ := (d2LitsNearWiderTransfers039.q2 (-1) 1 (0))
def d2WiderTransfer316C1 : ℚ := (d2LitsNearWiderTransfers039.q2 (-1) 55 (-3))
def d2WiderTransfer316S1 : ℚ := (d2LitsNearWiderTransfers039.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer316Arithmetic : weightedUpper d2WiderTransfer316C0 d2Log145Lo d2Log145Hi + weightedUpper d2WiderTransfer316C1 d2Log28Lo d2Log28Hi ≤ d2WiderTransfer316Cap := by decide +kernel
theorem d2WiderTransfer316Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer316Lo:ℚ):ℝ) ((d2WiderTransfer316Hi:ℚ):ℝ), ((d2WiderTransfer316C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer316S0:ℚ):ℝ)| + ((d2WiderTransfer316C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer316S1:ℚ):ℝ)| ≤ ((d2WiderTransfer316Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer316S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer316S0,d2WiderTransfer316Lo,d2WiderTransfer316Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer316C0 then |x-((d2WiderTransfer316S0:ℚ):ℝ)| ≤ ((d2Log145Q:ℚ):ℝ) else ((d2Log145Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer316S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer316S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer316S0,d2WiderTransfer316Lo,d2WiderTransfer316Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer316C0,d2Log145Q,d2WiderTransfer316S0,d2WiderTransfer316Lo,d2WiderTransfer316Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer316C0 d2WiderTransfer316S0 d2Log145Q d2Log145Lo d2Log145Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log145Bounds
  have hn1 : x-((d2WiderTransfer316S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer316S1,d2WiderTransfer316Lo,d2WiderTransfer316Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer316C1 then |x-((d2WiderTransfer316S1:ℚ):ℝ)| ≤ ((d2Log28Q:ℚ):ℝ) else ((d2Log28Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer316S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer316S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer316S1,d2WiderTransfer316Lo,d2WiderTransfer316Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer316C1,d2Log28Q,d2WiderTransfer316S1,d2WiderTransfer316Lo,d2WiderTransfer316Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer316C1 d2WiderTransfer316S1 d2Log28Q d2Log28Lo d2Log28Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log28Bounds
  have har : (((weightedUpper d2WiderTransfer316C0 d2Log145Lo d2Log145Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer316C1 d2Log28Lo d2Log28Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer316Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer316Arithmetic
  linarith
#print axioms d2WiderTransfer316Arithmetic
#print axioms d2WiderTransfer316Bound
def d2WiderTransfer317Lo : ℚ := (d2LitsNearWiderTransfers039.q2 (674778395) 1 (-30))
def d2WiderTransfer317Hi : ℚ := (d2LitsNearWiderTransfers039.q2 (1351234511) 1 (-31))
def d2WiderTransfer317Cap : ℚ := (d2LitsNearWiderTransfers039.q2 (8712354037355950387771) 1 (-79))
def d2WiderTransfer317C0 : ℚ := (d2LitsNearWiderTransfers039.q2 (23) 25 (-5))
def d2WiderTransfer317S0 : ℚ := (d2LitsNearWiderTransfers039.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer317Arithmetic : weightedUpper d2WiderTransfer317C0 d2Log146Lo d2Log146Hi ≤ d2WiderTransfer317Cap := by decide +kernel
theorem d2WiderTransfer317Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer317Lo:ℚ):ℝ) ((d2WiderTransfer317Hi:ℚ):ℝ), ((d2WiderTransfer317C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer317S0:ℚ):ℝ)| ≤ ((d2WiderTransfer317Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer317S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer317S0,d2WiderTransfer317Lo,d2WiderTransfer317Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer317C0 then |x-((d2WiderTransfer317S0:ℚ):ℝ)| ≤ ((d2Log146Q:ℚ):ℝ) else ((d2Log146Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer317S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer317S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer317S0,d2WiderTransfer317Lo,d2WiderTransfer317Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer317C0,d2Log146Q,d2WiderTransfer317S0,d2WiderTransfer317Lo,d2WiderTransfer317Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer317C0 d2WiderTransfer317S0 d2Log146Q d2Log146Lo d2Log146Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log146Bounds
  have har : (((weightedUpper d2WiderTransfer317C0 d2Log146Lo d2Log146Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer317Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer317Arithmetic
  linarith
#print axioms d2WiderTransfer317Arithmetic
#print axioms d2WiderTransfer317Bound
def d2WiderTransfer318Lo : ℚ := (d2LitsNearWiderTransfers039.q2 (674778395) 1 (-30))
def d2WiderTransfer318Hi : ℚ := (d2LitsNearWiderTransfers039.q2 (1351234511) 1 (-31))
def d2WiderTransfer318Cap : ℚ := (d2LitsNearWiderTransfers039.q2 (17137847732989585535547) 1 (-79))
def d2WiderTransfer318C0 : ℚ := (d2LitsNearWiderTransfers039.q2 (3) 275 (-5))
def d2WiderTransfer318S0 : ℚ := (d2LitsNearWiderTransfers039.q2 (-1) 1 (0))
def d2WiderTransfer318C1 : ℚ := (d2LitsNearWiderTransfers039.q2 (-5) 11 (-4))
def d2WiderTransfer318S1 : ℚ := (d2LitsNearWiderTransfers039.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer318Arithmetic : weightedUpper d2WiderTransfer318C0 d2Log146Lo d2Log146Hi + weightedUpper d2WiderTransfer318C1 d2Log28Lo d2Log28Hi ≤ d2WiderTransfer318Cap := by decide +kernel
theorem d2WiderTransfer318Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer318Lo:ℚ):ℝ) ((d2WiderTransfer318Hi:ℚ):ℝ), ((d2WiderTransfer318C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer318S0:ℚ):ℝ)| + ((d2WiderTransfer318C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer318S1:ℚ):ℝ)| ≤ ((d2WiderTransfer318Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer318S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer318S0,d2WiderTransfer318Lo,d2WiderTransfer318Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer318C0 then |x-((d2WiderTransfer318S0:ℚ):ℝ)| ≤ ((d2Log146Q:ℚ):ℝ) else ((d2Log146Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer318S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer318S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer318S0,d2WiderTransfer318Lo,d2WiderTransfer318Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer318C0,d2Log146Q,d2WiderTransfer318S0,d2WiderTransfer318Lo,d2WiderTransfer318Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer318C0 d2WiderTransfer318S0 d2Log146Q d2Log146Lo d2Log146Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log146Bounds
  have hn1 : x-((d2WiderTransfer318S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer318S1,d2WiderTransfer318Lo,d2WiderTransfer318Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer318C1 then |x-((d2WiderTransfer318S1:ℚ):ℝ)| ≤ ((d2Log28Q:ℚ):ℝ) else ((d2Log28Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer318S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer318S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer318S1,d2WiderTransfer318Lo,d2WiderTransfer318Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer318C1,d2Log28Q,d2WiderTransfer318S1,d2WiderTransfer318Lo,d2WiderTransfer318Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer318C1 d2WiderTransfer318S1 d2Log28Q d2Log28Lo d2Log28Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log28Bounds
  have har : (((weightedUpper d2WiderTransfer318C0 d2Log146Lo d2Log146Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer318C1 d2Log28Lo d2Log28Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer318Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer318Arithmetic
  linarith
#print axioms d2WiderTransfer318Arithmetic
#print axioms d2WiderTransfer318Bound
def d2WiderTransfer319Lo : ℚ := (d2LitsNearWiderTransfers039.q2 (1351234511) 1 (-31))
def d2WiderTransfer319Hi : ℚ := (d2LitsNearWiderTransfers039.q2 (169114029) 1 (-28))
def d2WiderTransfer319Cap : ℚ := (d2LitsNearWiderTransfers039.q2 (2165550991296720462783) 1 (-80))
def d2WiderTransfer319C0 : ℚ := (d2LitsNearWiderTransfers039.q2 (-1) 55 (-3))
def d2WiderTransfer319S0 : ℚ := (d2LitsNearWiderTransfers039.q2 (-1) 1 (0))
def d2WiderTransfer319C1 : ℚ := (d2LitsNearWiderTransfers039.q2 (-1) 55 (-3))
def d2WiderTransfer319S1 : ℚ := (d2LitsNearWiderTransfers039.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer319Arithmetic : weightedUpper d2WiderTransfer319C0 d2Log146Lo d2Log146Hi + weightedUpper d2WiderTransfer319C1 d2Log27Lo d2Log27Hi ≤ d2WiderTransfer319Cap := by decide +kernel
theorem d2WiderTransfer319Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer319Lo:ℚ):ℝ) ((d2WiderTransfer319Hi:ℚ):ℝ), ((d2WiderTransfer319C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer319S0:ℚ):ℝ)| + ((d2WiderTransfer319C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer319S1:ℚ):ℝ)| ≤ ((d2WiderTransfer319Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer319S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer319S0,d2WiderTransfer319Lo,d2WiderTransfer319Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer319C0 then |x-((d2WiderTransfer319S0:ℚ):ℝ)| ≤ ((d2Log146Q:ℚ):ℝ) else ((d2Log146Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer319S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer319S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer319S0,d2WiderTransfer319Lo,d2WiderTransfer319Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer319C0,d2Log146Q,d2WiderTransfer319S0,d2WiderTransfer319Lo,d2WiderTransfer319Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer319C0 d2WiderTransfer319S0 d2Log146Q d2Log146Lo d2Log146Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log146Bounds
  have hn1 : x-((d2WiderTransfer319S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer319S1,d2WiderTransfer319Lo,d2WiderTransfer319Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer319C1 then |x-((d2WiderTransfer319S1:ℚ):ℝ)| ≤ ((d2Log27Q:ℚ):ℝ) else ((d2Log27Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer319S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer319S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer319S1,d2WiderTransfer319Lo,d2WiderTransfer319Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer319C1,d2Log27Q,d2WiderTransfer319S1,d2WiderTransfer319Lo,d2WiderTransfer319Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer319C1 d2WiderTransfer319S1 d2Log27Q d2Log27Lo d2Log27Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log27Bounds
  have har : (((weightedUpper d2WiderTransfer319C0 d2Log146Lo d2Log146Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer319C1 d2Log27Lo d2Log27Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer319Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer319Arithmetic
  linarith
#print axioms d2WiderTransfer319Arithmetic
#print axioms d2WiderTransfer319Bound
end CatalanMeasure.GenD.Signed.Data.Cells

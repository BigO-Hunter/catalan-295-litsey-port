module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache011
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers082
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers082
open D72.LogTransfer
def d2Transfer656Lo : ℚ := (d2LitsNearTransfers082.q2 (4095) 1 (-12))
def d2Transfer656Hi : ℚ := (d2LitsNearTransfers082.q2 (8191) 1 (-13))
def d2Transfer656Cap : ℚ := (d2LitsNearTransfers082.q2 (26184054587818403476383) 1 (-80))
def d2Transfer656C0 : ℚ := (d2LitsNearTransfers082.q2 (1) 1 (-5))
def d2Transfer656S0 : ℚ := (d2LitsNearTransfers082.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer656Arithmetic : weightedUpper d2Transfer656C0 d2Log179Lo d2Log179Hi ≤ d2Transfer656Cap := by decide +kernel
theorem d2Transfer656Bound : ∀ x ∈ Set.Icc ((d2Transfer656Lo:ℚ):ℝ) ((d2Transfer656Hi:ℚ):ℝ), ((d2Transfer656C0:ℚ):ℝ)*Real.log |x-((d2Transfer656S0:ℚ):ℝ)| ≤ ((d2Transfer656Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer656S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer656S0,d2Transfer656Lo,d2Transfer656Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer656C0 then |x-((d2Transfer656S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2Transfer656S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer656S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer656S0,d2Transfer656Lo,d2Transfer656Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer656C0,d2Log179Q,d2Transfer656S0,d2Transfer656Lo,d2Transfer656Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer656C0 d2Transfer656S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2Transfer656C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2Transfer656Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer656Arithmetic
  linarith
#print axioms d2Transfer656Arithmetic
#print axioms d2Transfer656Bound
def d2Transfer657Lo : ℚ := (d2LitsNearTransfers082.q2 (8191) 1 (-13))
def d2Transfer657Hi : ℚ := (d2LitsNearTransfers082.q2 (16383) 1 (-14))
def d2Transfer657Cap : ℚ := (d2LitsNearTransfers082.q2 (1055569478202211169405) 1 (-79))
def d2Transfer657C0 : ℚ := (d2LitsNearTransfers082.q2 (1) 25 (-4))
def d2Transfer657S0 : ℚ := (d2LitsNearTransfers082.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer657Arithmetic : weightedUpper d2Transfer657C0 d2Log180Lo d2Log180Hi ≤ d2Transfer657Cap := by decide +kernel
theorem d2Transfer657Bound : ∀ x ∈ Set.Icc ((d2Transfer657Lo:ℚ):ℝ) ((d2Transfer657Hi:ℚ):ℝ), ((d2Transfer657C0:ℚ):ℝ)*Real.log |x-((d2Transfer657S0:ℚ):ℝ)| ≤ ((d2Transfer657Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer657S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer657S0,d2Transfer657Lo,d2Transfer657Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer657C0 then |x-((d2Transfer657S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2Transfer657S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer657S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer657S0,d2Transfer657Lo,d2Transfer657Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer657C0,d2Log180Q,d2Transfer657S0,d2Transfer657Lo,d2Transfer657Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer657C0 d2Transfer657S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2Transfer657C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2Transfer657Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer657Arithmetic
  linarith
#print axioms d2Transfer657Arithmetic
#print axioms d2Transfer657Bound
def d2Transfer658Lo : ℚ := (d2LitsNearTransfers082.q2 (8191) 1 (-13))
def d2Transfer658Hi : ℚ := (d2LitsNearTransfers082.q2 (16383) 1 (-14))
def d2Transfer658Cap : ℚ := (d2LitsNearTransfers082.q2 (1055569268745246078077) 1 (-79))
def d2Transfer658C0 : ℚ := (d2LitsNearTransfers082.q2 (1) 25 (-4))
def d2Transfer658S0 : ℚ := (d2LitsNearTransfers082.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer658Arithmetic : weightedUpper d2Transfer658C0 d2Log180Lo d2Log180Hi ≤ d2Transfer658Cap := by decide +kernel
theorem d2Transfer658Bound : ∀ x ∈ Set.Icc ((d2Transfer658Lo:ℚ):ℝ) ((d2Transfer658Hi:ℚ):ℝ), ((d2Transfer658C0:ℚ):ℝ)*Real.log |x-((d2Transfer658S0:ℚ):ℝ)| ≤ ((d2Transfer658Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer658S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer658S0,d2Transfer658Lo,d2Transfer658Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer658C0 then |x-((d2Transfer658S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2Transfer658S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer658S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer658S0,d2Transfer658Lo,d2Transfer658Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer658C0,d2Log180Q,d2Transfer658S0,d2Transfer658Lo,d2Transfer658Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer658C0 d2Transfer658S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2Transfer658C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2Transfer658Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer658Arithmetic
  linarith
#print axioms d2Transfer658Arithmetic
#print axioms d2Transfer658Bound
def d2Transfer659Lo : ℚ := (d2LitsNearTransfers082.q2 (8191) 1 (-13))
def d2Transfer659Hi : ℚ := (d2LitsNearTransfers082.q2 (16383) 1 (-14))
def d2Transfer659Cap : ℚ := (d2LitsNearTransfers082.q2 (13092603583138943988861) 1 (-79))
def d2Transfer659C0 : ℚ := (d2LitsNearTransfers082.q2 (1) 1 (-5))
def d2Transfer659S0 : ℚ := (d2LitsNearTransfers082.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer659Arithmetic : weightedUpper d2Transfer659C0 d2Log180Lo d2Log180Hi ≤ d2Transfer659Cap := by decide +kernel
theorem d2Transfer659Bound : ∀ x ∈ Set.Icc ((d2Transfer659Lo:ℚ):ℝ) ((d2Transfer659Hi:ℚ):ℝ), ((d2Transfer659C0:ℚ):ℝ)*Real.log |x-((d2Transfer659S0:ℚ):ℝ)| ≤ ((d2Transfer659Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer659S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer659S0,d2Transfer659Lo,d2Transfer659Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer659C0 then |x-((d2Transfer659S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2Transfer659S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer659S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer659S0,d2Transfer659Lo,d2Transfer659Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer659C0,d2Log180Q,d2Transfer659S0,d2Transfer659Lo,d2Transfer659Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer659C0 d2Transfer659S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2Transfer659C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2Transfer659Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer659Arithmetic
  linarith
#print axioms d2Transfer659Arithmetic
#print axioms d2Transfer659Bound
def d2Transfer660Lo : ℚ := (d2LitsNearTransfers082.q2 (8191) 1 (-13))
def d2Transfer660Hi : ℚ := (d2LitsNearTransfers082.q2 (16383) 1 (-14))
def d2Transfer660Cap : ℚ := (d2LitsNearTransfers082.q2 (13092603781051036988541) 1 (-79))
def d2Transfer660C0 : ℚ := (d2LitsNearTransfers082.q2 (1) 1 (-5))
def d2Transfer660S0 : ℚ := (d2LitsNearTransfers082.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer660Arithmetic : weightedUpper d2Transfer660C0 d2Log180Lo d2Log180Hi ≤ d2Transfer660Cap := by decide +kernel
theorem d2Transfer660Bound : ∀ x ∈ Set.Icc ((d2Transfer660Lo:ℚ):ℝ) ((d2Transfer660Hi:ℚ):ℝ), ((d2Transfer660C0:ℚ):ℝ)*Real.log |x-((d2Transfer660S0:ℚ):ℝ)| ≤ ((d2Transfer660Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer660S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer660S0,d2Transfer660Lo,d2Transfer660Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer660C0 then |x-((d2Transfer660S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2Transfer660S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer660S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer660S0,d2Transfer660Lo,d2Transfer660Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer660C0,d2Log180Q,d2Transfer660S0,d2Transfer660Lo,d2Transfer660Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer660C0 d2Transfer660S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2Transfer660C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2Transfer660Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer660Arithmetic
  linarith
#print axioms d2Transfer660Arithmetic
#print axioms d2Transfer660Bound
def d2Transfer661Lo : ℚ := (d2LitsNearTransfers082.q2 (16383) 1 (-14))
def d2Transfer661Hi : ℚ := (d2LitsNearTransfers082.q2 (32767) 1 (-15))
def d2Transfer661Cap : ℚ := (d2LitsNearTransfers082.q2 (2111715430351178477989) 1 (-80))
def d2Transfer661C0 : ℚ := (d2LitsNearTransfers082.q2 (1) 25 (-4))
def d2Transfer661S0 : ℚ := (d2LitsNearTransfers082.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer661Arithmetic : weightedUpper d2Transfer661C0 d2Log181Lo d2Log181Hi ≤ d2Transfer661Cap := by decide +kernel
theorem d2Transfer661Bound : ∀ x ∈ Set.Icc ((d2Transfer661Lo:ℚ):ℝ) ((d2Transfer661Hi:ℚ):ℝ), ((d2Transfer661C0:ℚ):ℝ)*Real.log |x-((d2Transfer661S0:ℚ):ℝ)| ≤ ((d2Transfer661Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer661S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer661S0,d2Transfer661Lo,d2Transfer661Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer661C0 then |x-((d2Transfer661S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2Transfer661S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer661S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer661S0,d2Transfer661Lo,d2Transfer661Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer661C0,d2Log181Q,d2Transfer661S0,d2Transfer661Lo,d2Transfer661Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer661C0 d2Transfer661S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2Transfer661C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2Transfer661Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer661Arithmetic
  linarith
#print axioms d2Transfer661Arithmetic
#print axioms d2Transfer661Bound
def d2Transfer662Lo : ℚ := (d2LitsNearTransfers082.q2 (16383) 1 (-14))
def d2Transfer662Hi : ℚ := (d2LitsNearTransfers082.q2 (32767) 1 (-15))
def d2Transfer662Cap : ℚ := (d2LitsNearTransfers082.q2 (2111715011437248295333) 1 (-80))
def d2Transfer662C0 : ℚ := (d2LitsNearTransfers082.q2 (1) 25 (-4))
def d2Transfer662S0 : ℚ := (d2LitsNearTransfers082.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer662Arithmetic : weightedUpper d2Transfer662C0 d2Log181Lo d2Log181Hi ≤ d2Transfer662Cap := by decide +kernel
theorem d2Transfer662Bound : ∀ x ∈ Set.Icc ((d2Transfer662Lo:ℚ):ℝ) ((d2Transfer662Hi:ℚ):ℝ), ((d2Transfer662C0:ℚ):ℝ)*Real.log |x-((d2Transfer662S0:ℚ):ℝ)| ≤ ((d2Transfer662Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer662S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer662S0,d2Transfer662Lo,d2Transfer662Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer662C0 then |x-((d2Transfer662S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2Transfer662S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer662S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer662S0,d2Transfer662Lo,d2Transfer662Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer662C0,d2Log181Q,d2Transfer662S0,d2Transfer662Lo,d2Transfer662Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer662C0 d2Transfer662S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2Transfer662C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2Transfer662Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer662Arithmetic
  linarith
#print axioms d2Transfer662Arithmetic
#print axioms d2Transfer662Bound
def d2Transfer663Lo : ℚ := (d2LitsNearTransfers082.q2 (16383) 1 (-14))
def d2Transfer663Hi : ℚ := (d2LitsNearTransfers082.q2 (32767) 1 (-15))
def d2Transfer663Cap : ℚ := (d2LitsNearTransfers082.q2 (26185783640224644116901) 1 (-80))
def d2Transfer663C0 : ℚ := (d2LitsNearTransfers082.q2 (1) 1 (-5))
def d2Transfer663S0 : ℚ := (d2LitsNearTransfers082.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer663Arithmetic : weightedUpper d2Transfer663C0 d2Log181Lo d2Log181Hi ≤ d2Transfer663Cap := by decide +kernel
theorem d2Transfer663Bound : ∀ x ∈ Set.Icc ((d2Transfer663Lo:ℚ):ℝ) ((d2Transfer663Hi:ℚ):ℝ), ((d2Transfer663C0:ℚ):ℝ)*Real.log |x-((d2Transfer663S0:ℚ):ℝ)| ≤ ((d2Transfer663Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer663S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer663S0,d2Transfer663Lo,d2Transfer663Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer663C0 then |x-((d2Transfer663S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2Transfer663S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer663S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer663S0,d2Transfer663Lo,d2Transfer663Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers082.q2, d2LitsNearLogCache011.q2, d2Transfer663C0,d2Log181Q,d2Transfer663S0,d2Transfer663Lo,d2Transfer663Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer663C0 d2Transfer663S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2Transfer663C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2Transfer663Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer663Arithmetic
  linarith
#print axioms d2Transfer663Arithmetic
#print axioms d2Transfer663Bound
end CatalanMeasure.GenD.Signed.Data.Cells

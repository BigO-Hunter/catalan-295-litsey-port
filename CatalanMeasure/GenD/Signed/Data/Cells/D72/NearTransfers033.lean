module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
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
namespace d2LitsNearTransfers033
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers033
open D72.LogTransfer
def d2Transfer264Lo : ℚ := (d2LitsNearTransfers033.q2 (1331101859) 1 (-31))
def d2Transfer264Hi : ℚ := (d2LitsNearTransfers033.q2 (333194895) 1 (-29))
def d2Transfer264Cap : ℚ := (d2LitsNearTransfers033.q2 (18580956822309071680435) 1 (-80))
def d2Transfer264C0 : ℚ := (d2LitsNearTransfers033.q2 (1) 1 (-5))
def d2Transfer264S0 : ℚ := (d2LitsNearTransfers033.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer264Arithmetic : weightedUpper d2Transfer264C0 d2Log135Lo d2Log135Hi ≤ d2Transfer264Cap := by decide +kernel
theorem d2Transfer264Bound : ∀ x ∈ Set.Icc ((d2Transfer264Lo:ℚ):ℝ) ((d2Transfer264Hi:ℚ):ℝ), ((d2Transfer264C0:ℚ):ℝ)*Real.log |x-((d2Transfer264S0:ℚ):ℝ)| ≤ ((d2Transfer264Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer264S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer264S0,d2Transfer264Lo,d2Transfer264Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer264C0 then |x-((d2Transfer264S0:ℚ):ℝ)| ≤ ((d2Log135Q:ℚ):ℝ) else ((d2Log135Q:ℚ):ℝ) ≤ |x-((d2Transfer264S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer264S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer264S0,d2Transfer264Lo,d2Transfer264Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer264C0,d2Log135Q,d2Transfer264S0,d2Transfer264Lo,d2Transfer264Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer264C0 d2Transfer264S0 d2Log135Q d2Log135Lo d2Log135Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log135Bounds
  have har : (((weightedUpper d2Transfer264C0 d2Log135Lo d2Log135Hi:ℚ):ℝ)) ≤ ((d2Transfer264Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer264Arithmetic
  linarith
#print axioms d2Transfer264Arithmetic
#print axioms d2Transfer264Bound
def d2Transfer265Lo : ℚ := (d2LitsNearTransfers033.q2 (1331101859) 1 (-31))
def d2Transfer265Hi : ℚ := (d2LitsNearTransfers033.q2 (333194895) 1 (-29))
def d2Transfer265Cap : ℚ := (d2LitsNearTransfers033.q2 (34945794144600579044275) 1 (-80))
def d2Transfer265C0 : ℚ := (d2LitsNearTransfers033.q2 (1) 11 (-5))
def d2Transfer265S0 : ℚ := (d2LitsNearTransfers033.q2 (-1) 1 (0))
def d2Transfer265C1 : ℚ := (d2LitsNearTransfers033.q2 (-5) 11 (-4))
def d2Transfer265S1 : ℚ := (d2LitsNearTransfers033.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer265Arithmetic : weightedUpper d2Transfer265C0 d2Log135Lo d2Log135Hi + weightedUpper d2Transfer265C1 d2Log39Lo d2Log39Hi ≤ d2Transfer265Cap := by decide +kernel
theorem d2Transfer265Bound : ∀ x ∈ Set.Icc ((d2Transfer265Lo:ℚ):ℝ) ((d2Transfer265Hi:ℚ):ℝ), ((d2Transfer265C0:ℚ):ℝ)*Real.log |x-((d2Transfer265S0:ℚ):ℝ)| + ((d2Transfer265C1:ℚ):ℝ)*Real.log |x-((d2Transfer265S1:ℚ):ℝ)| ≤ ((d2Transfer265Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer265S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer265S0,d2Transfer265Lo,d2Transfer265Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer265C0 then |x-((d2Transfer265S0:ℚ):ℝ)| ≤ ((d2Log135Q:ℚ):ℝ) else ((d2Log135Q:ℚ):ℝ) ≤ |x-((d2Transfer265S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer265S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer265S0,d2Transfer265Lo,d2Transfer265Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer265C0,d2Log135Q,d2Transfer265S0,d2Transfer265Lo,d2Transfer265Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer265C0 d2Transfer265S0 d2Log135Q d2Log135Lo d2Log135Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log135Bounds
  have hn1 : x-((d2Transfer265S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer265S1,d2Transfer265Lo,d2Transfer265Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer265C1 then |x-((d2Transfer265S1:ℚ):ℝ)| ≤ ((d2Log39Q:ℚ):ℝ) else ((d2Log39Q:ℚ):ℝ) ≤ |x-((d2Transfer265S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer265S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer265S1,d2Transfer265Lo,d2Transfer265Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer265C1,d2Log39Q,d2Transfer265S1,d2Transfer265Lo,d2Transfer265Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer265C1 d2Transfer265S1 d2Log39Q d2Log39Lo d2Log39Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log39Bounds
  have har : (((weightedUpper d2Transfer265C0 d2Log135Lo d2Log135Hi:ℚ):ℝ) + ((weightedUpper d2Transfer265C1 d2Log39Lo d2Log39Hi:ℚ):ℝ)) ≤ ((d2Transfer265Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer265Arithmetic
  linarith
#print axioms d2Transfer265Arithmetic
#print axioms d2Transfer265Bound
def d2Transfer266Lo : ℚ := (d2LitsNearTransfers033.q2 (333194895) 1 (-29))
def d2Transfer266Hi : ℚ := (d2LitsNearTransfers033.q2 (1334457301) 1 (-31))
def d2Transfer266Cap : ℚ := (d2LitsNearTransfers033.q2 (17031627778554332461) 1 (-73))
def d2Transfer266C0 : ℚ := (d2LitsNearTransfers033.q2 (1) 25 (-4))
def d2Transfer266S0 : ℚ := (d2LitsNearTransfers033.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer266Arithmetic : weightedUpper d2Transfer266C0 d2Log136Lo d2Log136Hi ≤ d2Transfer266Cap := by decide +kernel
theorem d2Transfer266Bound : ∀ x ∈ Set.Icc ((d2Transfer266Lo:ℚ):ℝ) ((d2Transfer266Hi:ℚ):ℝ), ((d2Transfer266C0:ℚ):ℝ)*Real.log |x-((d2Transfer266S0:ℚ):ℝ)| ≤ ((d2Transfer266Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer266S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer266S0,d2Transfer266Lo,d2Transfer266Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer266C0 then |x-((d2Transfer266S0:ℚ):ℝ)| ≤ ((d2Log136Q:ℚ):ℝ) else ((d2Log136Q:ℚ):ℝ) ≤ |x-((d2Transfer266S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer266S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer266S0,d2Transfer266Lo,d2Transfer266Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer266C0,d2Log136Q,d2Transfer266S0,d2Transfer266Lo,d2Transfer266Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer266C0 d2Transfer266S0 d2Log136Q d2Log136Lo d2Log136Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log136Bounds
  have har : (((weightedUpper d2Transfer266C0 d2Log136Lo d2Log136Hi:ℚ):ℝ)) ≤ ((d2Transfer266Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer266Arithmetic
  linarith
#print axioms d2Transfer266Arithmetic
#print axioms d2Transfer266Bound
def d2Transfer267Lo : ℚ := (d2LitsNearTransfers033.q2 (333194895) 1 (-29))
def d2Transfer267Hi : ℚ := (d2LitsNearTransfers033.q2 (1334457301) 1 (-31))
def d2Transfer267Cap : ℚ := (d2LitsNearTransfers033.q2 (26799597846021014829) 1 (-73))
def d2Transfer267C0 : ℚ := (d2LitsNearTransfers033.q2 (1) 275 (-4))
def d2Transfer267S0 : ℚ := (d2LitsNearTransfers033.q2 (-1) 1 (0))
def d2Transfer267C1 : ℚ := (d2LitsNearTransfers033.q2 (-1) 55 (-3))
def d2Transfer267S1 : ℚ := (d2LitsNearTransfers033.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer267Arithmetic : weightedUpper d2Transfer267C0 d2Log136Lo d2Log136Hi + weightedUpper d2Transfer267C1 d2Log38Lo d2Log38Hi ≤ d2Transfer267Cap := by decide +kernel
theorem d2Transfer267Bound : ∀ x ∈ Set.Icc ((d2Transfer267Lo:ℚ):ℝ) ((d2Transfer267Hi:ℚ):ℝ), ((d2Transfer267C0:ℚ):ℝ)*Real.log |x-((d2Transfer267S0:ℚ):ℝ)| + ((d2Transfer267C1:ℚ):ℝ)*Real.log |x-((d2Transfer267S1:ℚ):ℝ)| ≤ ((d2Transfer267Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer267S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer267S0,d2Transfer267Lo,d2Transfer267Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer267C0 then |x-((d2Transfer267S0:ℚ):ℝ)| ≤ ((d2Log136Q:ℚ):ℝ) else ((d2Log136Q:ℚ):ℝ) ≤ |x-((d2Transfer267S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer267S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer267S0,d2Transfer267Lo,d2Transfer267Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer267C0,d2Log136Q,d2Transfer267S0,d2Transfer267Lo,d2Transfer267Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer267C0 d2Transfer267S0 d2Log136Q d2Log136Lo d2Log136Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log136Bounds
  have hn1 : x-((d2Transfer267S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer267S1,d2Transfer267Lo,d2Transfer267Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer267C1 then |x-((d2Transfer267S1:ℚ):ℝ)| ≤ ((d2Log38Q:ℚ):ℝ) else ((d2Log38Q:ℚ):ℝ) ≤ |x-((d2Transfer267S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer267S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer267S1,d2Transfer267Lo,d2Transfer267Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer267C1,d2Log38Q,d2Transfer267S1,d2Transfer267Lo,d2Transfer267Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer267C1 d2Transfer267S1 d2Log38Q d2Log38Lo d2Log38Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log38Bounds
  have har : (((weightedUpper d2Transfer267C0 d2Log136Lo d2Log136Hi:ℚ):ℝ) + ((weightedUpper d2Transfer267C1 d2Log38Lo d2Log38Hi:ℚ):ℝ)) ≤ ((d2Transfer267Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer267Arithmetic
  linarith
#print axioms d2Transfer267Arithmetic
#print axioms d2Transfer267Bound
def d2Transfer268Lo : ℚ := (d2LitsNearTransfers033.q2 (333194895) 1 (-29))
def d2Transfer268Hi : ℚ := (d2LitsNearTransfers033.q2 (1334457301) 1 (-31))
def d2Transfer268Cap : ℚ := (d2LitsNearTransfers033.q2 (145729770427450393901) 1 (-73))
def d2Transfer268C0 : ℚ := (d2LitsNearTransfers033.q2 (1) 1 (-5))
def d2Transfer268S0 : ℚ := (d2LitsNearTransfers033.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer268Arithmetic : weightedUpper d2Transfer268C0 d2Log136Lo d2Log136Hi ≤ d2Transfer268Cap := by decide +kernel
theorem d2Transfer268Bound : ∀ x ∈ Set.Icc ((d2Transfer268Lo:ℚ):ℝ) ((d2Transfer268Hi:ℚ):ℝ), ((d2Transfer268C0:ℚ):ℝ)*Real.log |x-((d2Transfer268S0:ℚ):ℝ)| ≤ ((d2Transfer268Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer268S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer268S0,d2Transfer268Lo,d2Transfer268Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer268C0 then |x-((d2Transfer268S0:ℚ):ℝ)| ≤ ((d2Log136Q:ℚ):ℝ) else ((d2Log136Q:ℚ):ℝ) ≤ |x-((d2Transfer268S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer268S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer268S0,d2Transfer268Lo,d2Transfer268Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer268C0,d2Log136Q,d2Transfer268S0,d2Transfer268Lo,d2Transfer268Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer268C0 d2Transfer268S0 d2Log136Q d2Log136Lo d2Log136Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log136Bounds
  have har : (((weightedUpper d2Transfer268C0 d2Log136Lo d2Log136Hi:ℚ):ℝ)) ≤ ((d2Transfer268Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer268Arithmetic
  linarith
#print axioms d2Transfer268Arithmetic
#print axioms d2Transfer268Bound
def d2Transfer269Lo : ℚ := (d2LitsNearTransfers033.q2 (333194895) 1 (-29))
def d2Transfer269Hi : ℚ := (d2LitsNearTransfers033.q2 (1334457301) 1 (-31))
def d2Transfer269Cap : ℚ := (d2LitsNearTransfers033.q2 (273580062007852795181) 1 (-73))
def d2Transfer269C0 : ℚ := (d2LitsNearTransfers033.q2 (1) 11 (-5))
def d2Transfer269S0 : ℚ := (d2LitsNearTransfers033.q2 (-1) 1 (0))
def d2Transfer269C1 : ℚ := (d2LitsNearTransfers033.q2 (-5) 11 (-4))
def d2Transfer269S1 : ℚ := (d2LitsNearTransfers033.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer269Arithmetic : weightedUpper d2Transfer269C0 d2Log136Lo d2Log136Hi + weightedUpper d2Transfer269C1 d2Log38Lo d2Log38Hi ≤ d2Transfer269Cap := by decide +kernel
theorem d2Transfer269Bound : ∀ x ∈ Set.Icc ((d2Transfer269Lo:ℚ):ℝ) ((d2Transfer269Hi:ℚ):ℝ), ((d2Transfer269C0:ℚ):ℝ)*Real.log |x-((d2Transfer269S0:ℚ):ℝ)| + ((d2Transfer269C1:ℚ):ℝ)*Real.log |x-((d2Transfer269S1:ℚ):ℝ)| ≤ ((d2Transfer269Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer269S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer269S0,d2Transfer269Lo,d2Transfer269Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer269C0 then |x-((d2Transfer269S0:ℚ):ℝ)| ≤ ((d2Log136Q:ℚ):ℝ) else ((d2Log136Q:ℚ):ℝ) ≤ |x-((d2Transfer269S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer269S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer269S0,d2Transfer269Lo,d2Transfer269Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer269C0,d2Log136Q,d2Transfer269S0,d2Transfer269Lo,d2Transfer269Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer269C0 d2Transfer269S0 d2Log136Q d2Log136Lo d2Log136Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log136Bounds
  have hn1 : x-((d2Transfer269S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer269S1,d2Transfer269Lo,d2Transfer269Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer269C1 then |x-((d2Transfer269S1:ℚ):ℝ)| ≤ ((d2Log38Q:ℚ):ℝ) else ((d2Log38Q:ℚ):ℝ) ≤ |x-((d2Transfer269S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer269S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer269S1,d2Transfer269Lo,d2Transfer269Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer269C1,d2Log38Q,d2Transfer269S1,d2Transfer269Lo,d2Transfer269Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer269C1 d2Transfer269S1 d2Log38Q d2Log38Lo d2Log38Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log38Bounds
  have har : (((weightedUpper d2Transfer269C0 d2Log136Lo d2Log136Hi:ℚ):ℝ) + ((weightedUpper d2Transfer269C1 d2Log38Lo d2Log38Hi:ℚ):ℝ)) ≤ ((d2Transfer269Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer269Arithmetic
  linarith
#print axioms d2Transfer269Arithmetic
#print axioms d2Transfer269Bound
def d2Transfer270Lo : ℚ := (d2LitsNearTransfers033.q2 (1334457301) 1 (-31))
def d2Transfer270Hi : ℚ := (d2LitsNearTransfers033.q2 (668067511) 1 (-30))
def d2Transfer270Cap : ℚ := (d2LitsNearTransfers033.q2 (2252647598101690118919) 1 (-80))
def d2Transfer270C0 : ℚ := (d2LitsNearTransfers033.q2 (1) 25 (-4))
def d2Transfer270S0 : ℚ := (d2LitsNearTransfers033.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer270Arithmetic : weightedUpper d2Transfer270C0 d2Log137Lo d2Log137Hi ≤ d2Transfer270Cap := by decide +kernel
theorem d2Transfer270Bound : ∀ x ∈ Set.Icc ((d2Transfer270Lo:ℚ):ℝ) ((d2Transfer270Hi:ℚ):ℝ), ((d2Transfer270C0:ℚ):ℝ)*Real.log |x-((d2Transfer270S0:ℚ):ℝ)| ≤ ((d2Transfer270Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer270S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer270S0,d2Transfer270Lo,d2Transfer270Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer270C0 then |x-((d2Transfer270S0:ℚ):ℝ)| ≤ ((d2Log137Q:ℚ):ℝ) else ((d2Log137Q:ℚ):ℝ) ≤ |x-((d2Transfer270S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer270S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer270S0,d2Transfer270Lo,d2Transfer270Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer270C0,d2Log137Q,d2Transfer270S0,d2Transfer270Lo,d2Transfer270Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer270C0 d2Transfer270S0 d2Log137Q d2Log137Lo d2Log137Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log137Bounds
  have har : (((weightedUpper d2Transfer270C0 d2Log137Lo d2Log137Hi:ℚ):ℝ)) ≤ ((d2Transfer270Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer270Arithmetic
  linarith
#print axioms d2Transfer270Arithmetic
#print axioms d2Transfer270Bound
def d2Transfer271Lo : ℚ := (d2LitsNearTransfers033.q2 (1334457301) 1 (-31))
def d2Transfer271Hi : ℚ := (d2LitsNearTransfers033.q2 (668067511) 1 (-30))
def d2Transfer271Cap : ℚ := (d2LitsNearTransfers033.q2 (3502947766737425462023) 1 (-80))
def d2Transfer271C0 : ℚ := (d2LitsNearTransfers033.q2 (1) 275 (-4))
def d2Transfer271S0 : ℚ := (d2LitsNearTransfers033.q2 (-1) 1 (0))
def d2Transfer271C1 : ℚ := (d2LitsNearTransfers033.q2 (-1) 55 (-3))
def d2Transfer271S1 : ℚ := (d2LitsNearTransfers033.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer271Arithmetic : weightedUpper d2Transfer271C0 d2Log137Lo d2Log137Hi + weightedUpper d2Transfer271C1 d2Log37Lo d2Log37Hi ≤ d2Transfer271Cap := by decide +kernel
theorem d2Transfer271Bound : ∀ x ∈ Set.Icc ((d2Transfer271Lo:ℚ):ℝ) ((d2Transfer271Hi:ℚ):ℝ), ((d2Transfer271C0:ℚ):ℝ)*Real.log |x-((d2Transfer271S0:ℚ):ℝ)| + ((d2Transfer271C1:ℚ):ℝ)*Real.log |x-((d2Transfer271S1:ℚ):ℝ)| ≤ ((d2Transfer271Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer271S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer271S0,d2Transfer271Lo,d2Transfer271Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer271C0 then |x-((d2Transfer271S0:ℚ):ℝ)| ≤ ((d2Log137Q:ℚ):ℝ) else ((d2Log137Q:ℚ):ℝ) ≤ |x-((d2Transfer271S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer271S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer271S0,d2Transfer271Lo,d2Transfer271Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer271C0,d2Log137Q,d2Transfer271S0,d2Transfer271Lo,d2Transfer271Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer271C0 d2Transfer271S0 d2Log137Q d2Log137Lo d2Log137Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log137Bounds
  have hn1 : x-((d2Transfer271S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer271S1,d2Transfer271Lo,d2Transfer271Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer271C1 then |x-((d2Transfer271S1:ℚ):ℝ)| ≤ ((d2Log37Q:ℚ):ℝ) else ((d2Log37Q:ℚ):ℝ) ≤ |x-((d2Transfer271S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer271S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer271S1,d2Transfer271Lo,d2Transfer271Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers033.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer271C1,d2Log37Q,d2Transfer271S1,d2Transfer271Lo,d2Transfer271Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer271C1 d2Transfer271S1 d2Log37Q d2Log37Lo d2Log37Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log37Bounds
  have har : (((weightedUpper d2Transfer271C0 d2Log137Lo d2Log137Hi:ℚ):ℝ) + ((weightedUpper d2Transfer271C1 d2Log37Lo d2Log37Hi:ℚ):ℝ)) ≤ ((d2Transfer271Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer271Arithmetic
  linarith
#print axioms d2Transfer271Arithmetic
#print axioms d2Transfer271Bound
end CatalanMeasure.GenD.Signed.Data.Cells

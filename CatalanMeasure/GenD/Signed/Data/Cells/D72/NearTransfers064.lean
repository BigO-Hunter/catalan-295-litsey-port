module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache001
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
namespace d2LitsNearTransfers064
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers064
open D72.LogTransfer
def d2Transfer512Lo : ℚ := (d2LitsNearTransfers064.q2 (41859077) 1 (-26))
def d2Transfer512Hi : ℚ := (d2LitsNearTransfers064.q2 (671422953) 1 (-30))
def d2Transfer512Cap : ℚ := (d2LitsNearTransfers064.q2 (4265946769536687764057) 1 (-78))
def d2Transfer512C0 : ℚ := (d2LitsNearTransfers064.q2 (23) 25 (-5))
def d2Transfer512S0 : ℚ := (d2LitsNearTransfers064.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer512Arithmetic : weightedUpper d2Transfer512C0 d2Log141Lo d2Log141Hi ≤ d2Transfer512Cap := by decide +kernel
theorem d2Transfer512Bound : ∀ x ∈ Set.Icc ((d2Transfer512Lo:ℚ):ℝ) ((d2Transfer512Hi:ℚ):ℝ), ((d2Transfer512C0:ℚ):ℝ)*Real.log |x-((d2Transfer512S0:ℚ):ℝ)| ≤ ((d2Transfer512Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer512S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer512S0,d2Transfer512Lo,d2Transfer512Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer512C0 then |x-((d2Transfer512S0:ℚ):ℝ)| ≤ ((d2Log141Q:ℚ):ℝ) else ((d2Log141Q:ℚ):ℝ) ≤ |x-((d2Transfer512S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer512S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer512S0,d2Transfer512Lo,d2Transfer512Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer512C0,d2Log141Q,d2Transfer512S0,d2Transfer512Lo,d2Transfer512Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer512C0 d2Transfer512S0 d2Log141Q d2Log141Lo d2Log141Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log141Bounds
  have har : (((weightedUpper d2Transfer512C0 d2Log141Lo d2Log141Hi:ℚ):ℝ)) ≤ ((d2Transfer512Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer512Arithmetic
  linarith
#print axioms d2Transfer512Arithmetic
#print axioms d2Transfer512Bound
def d2Transfer513Lo : ℚ := (d2LitsNearTransfers064.q2 (41859077) 1 (-26))
def d2Transfer513Hi : ℚ := (d2LitsNearTransfers064.q2 (671422953) 1 (-30))
def d2Transfer513Cap : ℚ := (d2LitsNearTransfers064.q2 (8478693617353505337945) 1 (-78))
def d2Transfer513C0 : ℚ := (d2LitsNearTransfers064.q2 (3) 275 (-5))
def d2Transfer513S0 : ℚ := (d2LitsNearTransfers064.q2 (-1) 1 (0))
def d2Transfer513C1 : ℚ := (d2LitsNearTransfers064.q2 (-5) 11 (-4))
def d2Transfer513S1 : ℚ := (d2LitsNearTransfers064.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer513Arithmetic : weightedUpper d2Transfer513C0 d2Log141Lo d2Log141Hi + weightedUpper d2Transfer513C1 d2Log33Lo d2Log33Hi ≤ d2Transfer513Cap := by decide +kernel
theorem d2Transfer513Bound : ∀ x ∈ Set.Icc ((d2Transfer513Lo:ℚ):ℝ) ((d2Transfer513Hi:ℚ):ℝ), ((d2Transfer513C0:ℚ):ℝ)*Real.log |x-((d2Transfer513S0:ℚ):ℝ)| + ((d2Transfer513C1:ℚ):ℝ)*Real.log |x-((d2Transfer513S1:ℚ):ℝ)| ≤ ((d2Transfer513Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer513S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer513S0,d2Transfer513Lo,d2Transfer513Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer513C0 then |x-((d2Transfer513S0:ℚ):ℝ)| ≤ ((d2Log141Q:ℚ):ℝ) else ((d2Log141Q:ℚ):ℝ) ≤ |x-((d2Transfer513S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer513S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer513S0,d2Transfer513Lo,d2Transfer513Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer513C0,d2Log141Q,d2Transfer513S0,d2Transfer513Lo,d2Transfer513Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer513C0 d2Transfer513S0 d2Log141Q d2Log141Lo d2Log141Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log141Bounds
  have hn1 : x-((d2Transfer513S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer513S1,d2Transfer513Lo,d2Transfer513Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer513C1 then |x-((d2Transfer513S1:ℚ):ℝ)| ≤ ((d2Log33Q:ℚ):ℝ) else ((d2Log33Q:ℚ):ℝ) ≤ |x-((d2Transfer513S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer513S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer513S1,d2Transfer513Lo,d2Transfer513Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer513C1,d2Log33Q,d2Transfer513S1,d2Transfer513Lo,d2Transfer513Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer513C1 d2Transfer513S1 d2Log33Q d2Log33Lo d2Log33Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log33Bounds
  have har : (((weightedUpper d2Transfer513C0 d2Log141Lo d2Log141Hi:ℚ):ℝ) + ((weightedUpper d2Transfer513C1 d2Log33Lo d2Log33Hi:ℚ):ℝ)) ≤ ((d2Transfer513Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer513Arithmetic
  linarith
#print axioms d2Transfer513Arithmetic
#print axioms d2Transfer513Bound
def d2Transfer514Lo : ℚ := (d2LitsNearTransfers064.q2 (671422953) 1 (-30))
def d2Transfer514Hi : ℚ := (d2LitsNearTransfers064.q2 (1344523627) 1 (-31))
def d2Transfer514Cap : ℚ := (d2LitsNearTransfers064.q2 (1803874458056511115589) 1 (-80))
def d2Transfer514C0 : ℚ := (d2LitsNearTransfers064.q2 (-1) 55 (-3))
def d2Transfer514S0 : ℚ := (d2LitsNearTransfers064.q2 (-1) 1 (0))
def d2Transfer514C1 : ℚ := (d2LitsNearTransfers064.q2 (-1) 55 (-3))
def d2Transfer514S1 : ℚ := (d2LitsNearTransfers064.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer514Arithmetic : weightedUpper d2Transfer514C0 d2Log141Lo d2Log141Hi + weightedUpper d2Transfer514C1 d2Log32Lo d2Log32Hi ≤ d2Transfer514Cap := by decide +kernel
theorem d2Transfer514Bound : ∀ x ∈ Set.Icc ((d2Transfer514Lo:ℚ):ℝ) ((d2Transfer514Hi:ℚ):ℝ), ((d2Transfer514C0:ℚ):ℝ)*Real.log |x-((d2Transfer514S0:ℚ):ℝ)| + ((d2Transfer514C1:ℚ):ℝ)*Real.log |x-((d2Transfer514S1:ℚ):ℝ)| ≤ ((d2Transfer514Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer514S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer514S0,d2Transfer514Lo,d2Transfer514Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer514C0 then |x-((d2Transfer514S0:ℚ):ℝ)| ≤ ((d2Log141Q:ℚ):ℝ) else ((d2Log141Q:ℚ):ℝ) ≤ |x-((d2Transfer514S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer514S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer514S0,d2Transfer514Lo,d2Transfer514Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer514C0,d2Log141Q,d2Transfer514S0,d2Transfer514Lo,d2Transfer514Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer514C0 d2Transfer514S0 d2Log141Q d2Log141Lo d2Log141Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log141Bounds
  have hn1 : x-((d2Transfer514S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer514S1,d2Transfer514Lo,d2Transfer514Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer514C1 then |x-((d2Transfer514S1:ℚ):ℝ)| ≤ ((d2Log32Q:ℚ):ℝ) else ((d2Log32Q:ℚ):ℝ) ≤ |x-((d2Transfer514S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer514S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer514S1,d2Transfer514Lo,d2Transfer514Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer514C1,d2Log32Q,d2Transfer514S1,d2Transfer514Lo,d2Transfer514Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer514C1 d2Transfer514S1 d2Log32Q d2Log32Lo d2Log32Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log32Bounds
  have har : (((weightedUpper d2Transfer514C0 d2Log141Lo d2Log141Hi:ℚ):ℝ) + ((weightedUpper d2Transfer514C1 d2Log32Lo d2Log32Hi:ℚ):ℝ)) ≤ ((d2Transfer514Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer514Arithmetic
  linarith
#print axioms d2Transfer514Arithmetic
#print axioms d2Transfer514Bound
def d2Transfer515Lo : ℚ := (d2LitsNearTransfers064.q2 (671422953) 1 (-30))
def d2Transfer515Hi : ℚ := (d2LitsNearTransfers064.q2 (1344523627) 1 (-31))
def d2Transfer515Cap : ℚ := (d2LitsNearTransfers064.q2 (17135670331982798049605) 1 (-80))
def d2Transfer515C0 : ℚ := (d2LitsNearTransfers064.q2 (23) 25 (-5))
def d2Transfer515S0 : ℚ := (d2LitsNearTransfers064.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer515Arithmetic : weightedUpper d2Transfer515C0 d2Log142Lo d2Log142Hi ≤ d2Transfer515Cap := by decide +kernel
theorem d2Transfer515Bound : ∀ x ∈ Set.Icc ((d2Transfer515Lo:ℚ):ℝ) ((d2Transfer515Hi:ℚ):ℝ), ((d2Transfer515C0:ℚ):ℝ)*Real.log |x-((d2Transfer515S0:ℚ):ℝ)| ≤ ((d2Transfer515Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer515S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer515S0,d2Transfer515Lo,d2Transfer515Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer515C0 then |x-((d2Transfer515S0:ℚ):ℝ)| ≤ ((d2Log142Q:ℚ):ℝ) else ((d2Log142Q:ℚ):ℝ) ≤ |x-((d2Transfer515S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer515S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer515S0,d2Transfer515Lo,d2Transfer515Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer515C0,d2Log142Q,d2Transfer515S0,d2Transfer515Lo,d2Transfer515Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer515C0 d2Transfer515S0 d2Log142Q d2Log142Lo d2Log142Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log142Bounds
  have har : (((weightedUpper d2Transfer515C0 d2Log142Lo d2Log142Hi:ℚ):ℝ)) ≤ ((d2Transfer515Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer515Arithmetic
  linarith
#print axioms d2Transfer515Arithmetic
#print axioms d2Transfer515Bound
def d2Transfer516Lo : ℚ := (d2LitsNearTransfers064.q2 (671422953) 1 (-30))
def d2Transfer516Hi : ℚ := (d2LitsNearTransfers064.q2 (1344523627) 1 (-31))
def d2Transfer516Cap : ℚ := (d2LitsNearTransfers064.q2 (33986657723250068345157) 1 (-80))
def d2Transfer516C0 : ℚ := (d2LitsNearTransfers064.q2 (3) 275 (-5))
def d2Transfer516S0 : ℚ := (d2LitsNearTransfers064.q2 (-1) 1 (0))
def d2Transfer516C1 : ℚ := (d2LitsNearTransfers064.q2 (-5) 11 (-4))
def d2Transfer516S1 : ℚ := (d2LitsNearTransfers064.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer516Arithmetic : weightedUpper d2Transfer516C0 d2Log142Lo d2Log142Hi + weightedUpper d2Transfer516C1 d2Log32Lo d2Log32Hi ≤ d2Transfer516Cap := by decide +kernel
theorem d2Transfer516Bound : ∀ x ∈ Set.Icc ((d2Transfer516Lo:ℚ):ℝ) ((d2Transfer516Hi:ℚ):ℝ), ((d2Transfer516C0:ℚ):ℝ)*Real.log |x-((d2Transfer516S0:ℚ):ℝ)| + ((d2Transfer516C1:ℚ):ℝ)*Real.log |x-((d2Transfer516S1:ℚ):ℝ)| ≤ ((d2Transfer516Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer516S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer516S0,d2Transfer516Lo,d2Transfer516Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer516C0 then |x-((d2Transfer516S0:ℚ):ℝ)| ≤ ((d2Log142Q:ℚ):ℝ) else ((d2Log142Q:ℚ):ℝ) ≤ |x-((d2Transfer516S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer516S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer516S0,d2Transfer516Lo,d2Transfer516Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer516C0,d2Log142Q,d2Transfer516S0,d2Transfer516Lo,d2Transfer516Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer516C0 d2Transfer516S0 d2Log142Q d2Log142Lo d2Log142Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log142Bounds
  have hn1 : x-((d2Transfer516S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer516S1,d2Transfer516Lo,d2Transfer516Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer516C1 then |x-((d2Transfer516S1:ℚ):ℝ)| ≤ ((d2Log32Q:ℚ):ℝ) else ((d2Log32Q:ℚ):ℝ) ≤ |x-((d2Transfer516S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer516S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer516S1,d2Transfer516Lo,d2Transfer516Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer516C1,d2Log32Q,d2Transfer516S1,d2Transfer516Lo,d2Transfer516Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer516C1 d2Transfer516S1 d2Log32Q d2Log32Lo d2Log32Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log32Bounds
  have har : (((weightedUpper d2Transfer516C0 d2Log142Lo d2Log142Hi:ℚ):ℝ) + ((weightedUpper d2Transfer516C1 d2Log32Lo d2Log32Hi:ℚ):ℝ)) ≤ ((d2Transfer516Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer516Arithmetic
  linarith
#print axioms d2Transfer516Arithmetic
#print axioms d2Transfer516Bound
def d2Transfer517Lo : ℚ := (d2LitsNearTransfers064.q2 (1344523627) 1 (-31))
def d2Transfer517Hi : ℚ := (d2LitsNearTransfers064.q2 (336550337) 1 (-29))
def d2Transfer517Cap : ℚ := (d2LitsNearTransfers064.q2 (937953777010828006371) 1 (-79))
def d2Transfer517C0 : ℚ := (d2LitsNearTransfers064.q2 (-1) 55 (-3))
def d2Transfer517S0 : ℚ := (d2LitsNearTransfers064.q2 (-1) 1 (0))
def d2Transfer517C1 : ℚ := (d2LitsNearTransfers064.q2 (-1) 55 (-3))
def d2Transfer517S1 : ℚ := (d2LitsNearTransfers064.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer517Arithmetic : weightedUpper d2Transfer517C0 d2Log142Lo d2Log142Hi + weightedUpper d2Transfer517C1 d2Log31Lo d2Log31Hi ≤ d2Transfer517Cap := by decide +kernel
theorem d2Transfer517Bound : ∀ x ∈ Set.Icc ((d2Transfer517Lo:ℚ):ℝ) ((d2Transfer517Hi:ℚ):ℝ), ((d2Transfer517C0:ℚ):ℝ)*Real.log |x-((d2Transfer517S0:ℚ):ℝ)| + ((d2Transfer517C1:ℚ):ℝ)*Real.log |x-((d2Transfer517S1:ℚ):ℝ)| ≤ ((d2Transfer517Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer517S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer517S0,d2Transfer517Lo,d2Transfer517Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer517C0 then |x-((d2Transfer517S0:ℚ):ℝ)| ≤ ((d2Log142Q:ℚ):ℝ) else ((d2Log142Q:ℚ):ℝ) ≤ |x-((d2Transfer517S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer517S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer517S0,d2Transfer517Lo,d2Transfer517Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer517C0,d2Log142Q,d2Transfer517S0,d2Transfer517Lo,d2Transfer517Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer517C0 d2Transfer517S0 d2Log142Q d2Log142Lo d2Log142Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log142Bounds
  have hn1 : x-((d2Transfer517S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer517S1,d2Transfer517Lo,d2Transfer517Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer517C1 then |x-((d2Transfer517S1:ℚ):ℝ)| ≤ ((d2Log31Q:ℚ):ℝ) else ((d2Log31Q:ℚ):ℝ) ≤ |x-((d2Transfer517S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer517S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer517S1,d2Transfer517Lo,d2Transfer517Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer517C1,d2Log31Q,d2Transfer517S1,d2Transfer517Lo,d2Transfer517Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer517C1 d2Transfer517S1 d2Log31Q d2Log31Lo d2Log31Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log31Bounds
  have har : (((weightedUpper d2Transfer517C0 d2Log142Lo d2Log142Hi:ℚ):ℝ) + ((weightedUpper d2Transfer517C1 d2Log31Lo d2Log31Hi:ℚ):ℝ)) ≤ ((d2Transfer517Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer517Arithmetic
  linarith
#print axioms d2Transfer517Arithmetic
#print axioms d2Transfer517Bound
def d2Transfer518Lo : ℚ := (d2LitsNearTransfers064.q2 (1344523627) 1 (-31))
def d2Transfer518Hi : ℚ := (d2LitsNearTransfers064.q2 (336550337) 1 (-29))
def d2Transfer518Cap : ℚ := (d2LitsNearTransfers064.q2 (8603851713973971473379) 1 (-79))
def d2Transfer518C0 : ℚ := (d2LitsNearTransfers064.q2 (23) 25 (-5))
def d2Transfer518S0 : ℚ := (d2LitsNearTransfers064.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer518Arithmetic : weightedUpper d2Transfer518C0 d2Log143Lo d2Log143Hi ≤ d2Transfer518Cap := by decide +kernel
theorem d2Transfer518Bound : ∀ x ∈ Set.Icc ((d2Transfer518Lo:ℚ):ℝ) ((d2Transfer518Hi:ℚ):ℝ), ((d2Transfer518C0:ℚ):ℝ)*Real.log |x-((d2Transfer518S0:ℚ):ℝ)| ≤ ((d2Transfer518Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer518S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer518S0,d2Transfer518Lo,d2Transfer518Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer518C0 then |x-((d2Transfer518S0:ℚ):ℝ)| ≤ ((d2Log143Q:ℚ):ℝ) else ((d2Log143Q:ℚ):ℝ) ≤ |x-((d2Transfer518S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer518S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer518S0,d2Transfer518Lo,d2Transfer518Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer518C0,d2Log143Q,d2Transfer518S0,d2Transfer518Lo,d2Transfer518Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer518C0 d2Transfer518S0 d2Log143Q d2Log143Lo d2Log143Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log143Bounds
  have har : (((weightedUpper d2Transfer518C0 d2Log143Lo d2Log143Hi:ℚ):ℝ)) ≤ ((d2Transfer518Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer518Arithmetic
  linarith
#print axioms d2Transfer518Arithmetic
#print axioms d2Transfer518Bound
def d2Transfer519Lo : ℚ := (d2LitsNearTransfers064.q2 (1344523627) 1 (-31))
def d2Transfer519Hi : ℚ := (d2LitsNearTransfers064.q2 (336550337) 1 (-29))
def d2Transfer519Cap : ℚ := (d2LitsNearTransfers064.q2 (17029345409607606621155) 1 (-79))
def d2Transfer519C0 : ℚ := (d2LitsNearTransfers064.q2 (3) 275 (-5))
def d2Transfer519S0 : ℚ := (d2LitsNearTransfers064.q2 (-1) 1 (0))
def d2Transfer519C1 : ℚ := (d2LitsNearTransfers064.q2 (-5) 11 (-4))
def d2Transfer519S1 : ℚ := (d2LitsNearTransfers064.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer519Arithmetic : weightedUpper d2Transfer519C0 d2Log143Lo d2Log143Hi + weightedUpper d2Transfer519C1 d2Log31Lo d2Log31Hi ≤ d2Transfer519Cap := by decide +kernel
theorem d2Transfer519Bound : ∀ x ∈ Set.Icc ((d2Transfer519Lo:ℚ):ℝ) ((d2Transfer519Hi:ℚ):ℝ), ((d2Transfer519C0:ℚ):ℝ)*Real.log |x-((d2Transfer519S0:ℚ):ℝ)| + ((d2Transfer519C1:ℚ):ℝ)*Real.log |x-((d2Transfer519S1:ℚ):ℝ)| ≤ ((d2Transfer519Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer519S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer519S0,d2Transfer519Lo,d2Transfer519Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer519C0 then |x-((d2Transfer519S0:ℚ):ℝ)| ≤ ((d2Log143Q:ℚ):ℝ) else ((d2Log143Q:ℚ):ℝ) ≤ |x-((d2Transfer519S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer519S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer519S0,d2Transfer519Lo,d2Transfer519Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer519C0,d2Log143Q,d2Transfer519S0,d2Transfer519Lo,d2Transfer519Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer519C0 d2Transfer519S0 d2Log143Q d2Log143Lo d2Log143Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log143Bounds
  have hn1 : x-((d2Transfer519S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer519S1,d2Transfer519Lo,d2Transfer519Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer519C1 then |x-((d2Transfer519S1:ℚ):ℝ)| ≤ ((d2Log31Q:ℚ):ℝ) else ((d2Log31Q:ℚ):ℝ) ≤ |x-((d2Transfer519S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer519S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer519S1,d2Transfer519Lo,d2Transfer519Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers064.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer519C1,d2Log31Q,d2Transfer519S1,d2Transfer519Lo,d2Transfer519Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer519C1 d2Transfer519S1 d2Log31Q d2Log31Lo d2Log31Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log31Bounds
  have har : (((weightedUpper d2Transfer519C0 d2Log143Lo d2Log143Hi:ℚ):ℝ) + ((weightedUpper d2Transfer519C1 d2Log31Lo d2Log31Hi:ℚ):ℝ)) ≤ ((d2Transfer519Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer519Arithmetic
  linarith
#print axioms d2Transfer519Arithmetic
#print axioms d2Transfer519Bound
end CatalanMeasure.GenD.Signed.Data.Cells

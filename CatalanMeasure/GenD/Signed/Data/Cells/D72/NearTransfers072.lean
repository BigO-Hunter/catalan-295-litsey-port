module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers072
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers072
open D72.LogTransfer
def d2Transfer576Lo : ℚ := (d2LitsNearTransfers072.q2 (346616663) 1 (-29))
def d2Transfer576Hi : ℚ := (d2LitsNearTransfers072.q2 (21768399) 1 (-25))
def d2Transfer576Cap : ℚ := (d2LitsNearTransfers072.q2 (36139119136045530132903) 1 (-80))
def d2Transfer576C0 : ℚ := (d2LitsNearTransfers072.q2 (3) 275 (-5))
def d2Transfer576S0 : ℚ := (d2LitsNearTransfers072.q2 (-1) 1 (0))
def d2Transfer576C1 : ℚ := (d2LitsNearTransfers072.q2 (-5) 11 (-4))
def d2Transfer576S1 : ℚ := (d2LitsNearTransfers072.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer576Arithmetic : weightedUpper d2Transfer576C0 d2Log162Lo d2Log162Hi + weightedUpper d2Transfer576C1 d2Log12Lo d2Log12Hi ≤ d2Transfer576Cap := by decide +kernel
theorem d2Transfer576Bound : ∀ x ∈ Set.Icc ((d2Transfer576Lo:ℚ):ℝ) ((d2Transfer576Hi:ℚ):ℝ), ((d2Transfer576C0:ℚ):ℝ)*Real.log |x-((d2Transfer576S0:ℚ):ℝ)| + ((d2Transfer576C1:ℚ):ℝ)*Real.log |x-((d2Transfer576S1:ℚ):ℝ)| ≤ ((d2Transfer576Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer576S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer576S0,d2Transfer576Lo,d2Transfer576Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer576C0 then |x-((d2Transfer576S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2Transfer576S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer576S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer576S0,d2Transfer576Lo,d2Transfer576Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer576C0,d2Log162Q,d2Transfer576S0,d2Transfer576Lo,d2Transfer576Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer576C0 d2Transfer576S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have hn1 : x-((d2Transfer576S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer576S1,d2Transfer576Lo,d2Transfer576Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer576C1 then |x-((d2Transfer576S1:ℚ):ℝ)| ≤ ((d2Log12Q:ℚ):ℝ) else ((d2Log12Q:ℚ):ℝ) ≤ |x-((d2Transfer576S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer576S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer576S1,d2Transfer576Lo,d2Transfer576Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer576C1,d2Log12Q,d2Transfer576S1,d2Transfer576Lo,d2Transfer576Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer576C1 d2Transfer576S1 d2Log12Q d2Log12Lo d2Log12Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log12Bounds
  have har : (((weightedUpper d2Transfer576C0 d2Log162Lo d2Log162Hi:ℚ):ℝ) + ((weightedUpper d2Transfer576C1 d2Log12Lo d2Log12Hi:ℚ):ℝ)) ≤ ((d2Transfer576Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer576Arithmetic
  linarith
#print axioms d2Transfer576Arithmetic
#print axioms d2Transfer576Bound
def d2Transfer577Lo : ℚ := (d2LitsNearTransfers072.q2 (21768399) 1 (-25))
def d2Transfer577Hi : ℚ := (d2LitsNearTransfers072.q2 (175824913) 1 (-28))
def d2Transfer577Cap : ℚ := (d2LitsNearTransfers072.q2 (1143626764448916994303) 1 (-78))
def d2Transfer577C0 : ℚ := (d2LitsNearTransfers072.q2 (-1) 55 (-3))
def d2Transfer577S0 : ℚ := (d2LitsNearTransfers072.q2 (-1) 1 (0))
def d2Transfer577C1 : ℚ := (d2LitsNearTransfers072.q2 (-1) 55 (-3))
def d2Transfer577S1 : ℚ := (d2LitsNearTransfers072.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer577Arithmetic : weightedUpper d2Transfer577C0 d2Log162Lo d2Log162Hi + weightedUpper d2Transfer577C1 d2Log11Lo d2Log11Hi ≤ d2Transfer577Cap := by decide +kernel
theorem d2Transfer577Bound : ∀ x ∈ Set.Icc ((d2Transfer577Lo:ℚ):ℝ) ((d2Transfer577Hi:ℚ):ℝ), ((d2Transfer577C0:ℚ):ℝ)*Real.log |x-((d2Transfer577S0:ℚ):ℝ)| + ((d2Transfer577C1:ℚ):ℝ)*Real.log |x-((d2Transfer577S1:ℚ):ℝ)| ≤ ((d2Transfer577Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer577S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer577S0,d2Transfer577Lo,d2Transfer577Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer577C0 then |x-((d2Transfer577S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2Transfer577S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer577S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer577S0,d2Transfer577Lo,d2Transfer577Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer577C0,d2Log162Q,d2Transfer577S0,d2Transfer577Lo,d2Transfer577Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer577C0 d2Transfer577S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have hn1 : x-((d2Transfer577S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer577S1,d2Transfer577Lo,d2Transfer577Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer577C1 then |x-((d2Transfer577S1:ℚ):ℝ)| ≤ ((d2Log11Q:ℚ):ℝ) else ((d2Log11Q:ℚ):ℝ) ≤ |x-((d2Transfer577S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer577S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer577S1,d2Transfer577Lo,d2Transfer577Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer577C1,d2Log11Q,d2Transfer577S1,d2Transfer577Lo,d2Transfer577Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer577C1 d2Transfer577S1 d2Log11Q d2Log11Lo d2Log11Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log11Bounds
  have har : (((weightedUpper d2Transfer577C0 d2Log162Lo d2Log162Hi:ℚ):ℝ) + ((weightedUpper d2Transfer577C1 d2Log11Lo d2Log11Hi:ℚ):ℝ)) ≤ ((d2Transfer577Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer577Arithmetic
  linarith
#print axioms d2Transfer577Arithmetic
#print axioms d2Transfer577Bound
def d2Transfer578Lo : ℚ := (d2LitsNearTransfers072.q2 (21768399) 1 (-25))
def d2Transfer578Hi : ℚ := (d2LitsNearTransfers072.q2 (175824913) 1 (-28))
def d2Transfer578Cap : ℚ := (d2LitsNearTransfers072.q2 (4976575732930488727807) 1 (-78))
def d2Transfer578C0 : ℚ := (d2LitsNearTransfers072.q2 (23) 25 (-5))
def d2Transfer578S0 : ℚ := (d2LitsNearTransfers072.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer578Arithmetic : weightedUpper d2Transfer578C0 d2Log163Lo d2Log163Hi ≤ d2Transfer578Cap := by decide +kernel
theorem d2Transfer578Bound : ∀ x ∈ Set.Icc ((d2Transfer578Lo:ℚ):ℝ) ((d2Transfer578Hi:ℚ):ℝ), ((d2Transfer578C0:ℚ):ℝ)*Real.log |x-((d2Transfer578S0:ℚ):ℝ)| ≤ ((d2Transfer578Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer578S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer578S0,d2Transfer578Lo,d2Transfer578Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer578C0 then |x-((d2Transfer578S0:ℚ):ℝ)| ≤ ((d2Log163Q:ℚ):ℝ) else ((d2Log163Q:ℚ):ℝ) ≤ |x-((d2Transfer578S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer578S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer578S0,d2Transfer578Lo,d2Transfer578Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer578C0,d2Log163Q,d2Transfer578S0,d2Transfer578Lo,d2Transfer578Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer578C0 d2Transfer578S0 d2Log163Q d2Log163Lo d2Log163Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log163Bounds
  have har : (((weightedUpper d2Transfer578C0 d2Log163Lo d2Log163Hi:ℚ):ℝ)) ≤ ((d2Transfer578Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer578Arithmetic
  linarith
#print axioms d2Transfer578Arithmetic
#print axioms d2Transfer578Bound
def d2Transfer579Lo : ℚ := (d2LitsNearTransfers072.q2 (21768399) 1 (-25))
def d2Transfer579Hi : ℚ := (d2LitsNearTransfers072.q2 (175824913) 1 (-28))
def d2Transfer579Cap : ℚ := (d2LitsNearTransfers072.q2 (9189322580747306301695) 1 (-78))
def d2Transfer579C0 : ℚ := (d2LitsNearTransfers072.q2 (3) 275 (-5))
def d2Transfer579S0 : ℚ := (d2LitsNearTransfers072.q2 (-1) 1 (0))
def d2Transfer579C1 : ℚ := (d2LitsNearTransfers072.q2 (-5) 11 (-4))
def d2Transfer579S1 : ℚ := (d2LitsNearTransfers072.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer579Arithmetic : weightedUpper d2Transfer579C0 d2Log163Lo d2Log163Hi + weightedUpper d2Transfer579C1 d2Log11Lo d2Log11Hi ≤ d2Transfer579Cap := by decide +kernel
theorem d2Transfer579Bound : ∀ x ∈ Set.Icc ((d2Transfer579Lo:ℚ):ℝ) ((d2Transfer579Hi:ℚ):ℝ), ((d2Transfer579C0:ℚ):ℝ)*Real.log |x-((d2Transfer579S0:ℚ):ℝ)| + ((d2Transfer579C1:ℚ):ℝ)*Real.log |x-((d2Transfer579S1:ℚ):ℝ)| ≤ ((d2Transfer579Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer579S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer579S0,d2Transfer579Lo,d2Transfer579Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer579C0 then |x-((d2Transfer579S0:ℚ):ℝ)| ≤ ((d2Log163Q:ℚ):ℝ) else ((d2Log163Q:ℚ):ℝ) ≤ |x-((d2Transfer579S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer579S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer579S0,d2Transfer579Lo,d2Transfer579Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer579C0,d2Log163Q,d2Transfer579S0,d2Transfer579Lo,d2Transfer579Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer579C0 d2Transfer579S0 d2Log163Q d2Log163Lo d2Log163Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log163Bounds
  have hn1 : x-((d2Transfer579S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer579S1,d2Transfer579Lo,d2Transfer579Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer579C1 then |x-((d2Transfer579S1:ℚ):ℝ)| ≤ ((d2Log11Q:ℚ):ℝ) else ((d2Log11Q:ℚ):ℝ) ≤ |x-((d2Transfer579S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer579S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer579S1,d2Transfer579Lo,d2Transfer579Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer579C1,d2Log11Q,d2Transfer579S1,d2Transfer579Lo,d2Transfer579Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer579C1 d2Transfer579S1 d2Log11Q d2Log11Lo d2Log11Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log11Bounds
  have har : (((weightedUpper d2Transfer579C0 d2Log163Lo d2Log163Hi:ℚ):ℝ) + ((weightedUpper d2Transfer579C1 d2Log11Lo d2Log11Hi:ℚ):ℝ)) ≤ ((d2Transfer579Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer579Arithmetic
  linarith
#print axioms d2Transfer579Arithmetic
#print axioms d2Transfer579Bound
def d2Transfer580Lo : ℚ := (d2LitsNearTransfers072.q2 (175824913) 1 (-28))
def d2Transfer580Hi : ℚ := (d2LitsNearTransfers072.q2 (88751317) 1 (-27))
def d2Transfer580Cap : ℚ := (d2LitsNearTransfers072.q2 (325246597409181460825) 1 (-76))
def d2Transfer580C0 : ℚ := (d2LitsNearTransfers072.q2 (-1) 55 (-3))
def d2Transfer580S0 : ℚ := (d2LitsNearTransfers072.q2 (-1) 1 (0))
def d2Transfer580C1 : ℚ := (d2LitsNearTransfers072.q2 (-1) 55 (-3))
def d2Transfer580S1 : ℚ := (d2LitsNearTransfers072.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer580Arithmetic : weightedUpper d2Transfer580C0 d2Log163Lo d2Log163Hi + weightedUpper d2Transfer580C1 d2Log10Lo d2Log10Hi ≤ d2Transfer580Cap := by decide +kernel
theorem d2Transfer580Bound : ∀ x ∈ Set.Icc ((d2Transfer580Lo:ℚ):ℝ) ((d2Transfer580Hi:ℚ):ℝ), ((d2Transfer580C0:ℚ):ℝ)*Real.log |x-((d2Transfer580S0:ℚ):ℝ)| + ((d2Transfer580C1:ℚ):ℝ)*Real.log |x-((d2Transfer580S1:ℚ):ℝ)| ≤ ((d2Transfer580Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer580S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer580S0,d2Transfer580Lo,d2Transfer580Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer580C0 then |x-((d2Transfer580S0:ℚ):ℝ)| ≤ ((d2Log163Q:ℚ):ℝ) else ((d2Log163Q:ℚ):ℝ) ≤ |x-((d2Transfer580S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer580S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer580S0,d2Transfer580Lo,d2Transfer580Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer580C0,d2Log163Q,d2Transfer580S0,d2Transfer580Lo,d2Transfer580Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer580C0 d2Transfer580S0 d2Log163Q d2Log163Lo d2Log163Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log163Bounds
  have hn1 : x-((d2Transfer580S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer580S1,d2Transfer580Lo,d2Transfer580Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer580C1 then |x-((d2Transfer580S1:ℚ):ℝ)| ≤ ((d2Log10Q:ℚ):ℝ) else ((d2Log10Q:ℚ):ℝ) ≤ |x-((d2Transfer580S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer580S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer580S1,d2Transfer580Lo,d2Transfer580Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer580C1,d2Log10Q,d2Transfer580S1,d2Transfer580Lo,d2Transfer580Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer580C1 d2Transfer580S1 d2Log10Q d2Log10Lo d2Log10Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log10Bounds
  have har : (((weightedUpper d2Transfer580C0 d2Log163Lo d2Log163Hi:ℚ):ℝ) + ((weightedUpper d2Transfer580C1 d2Log10Lo d2Log10Hi:ℚ):ℝ)) ≤ ((d2Transfer580Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer580Arithmetic
  linarith
#print axioms d2Transfer580Arithmetic
#print axioms d2Transfer580Bound
def d2Transfer581Lo : ℚ := (d2LitsNearTransfers072.q2 (175824913) 1 (-28))
def d2Transfer581Hi : ℚ := (d2LitsNearTransfers072.q2 (88751317) 1 (-27))
def d2Transfer581Cap : ℚ := (d2LitsNearTransfers072.q2 (1283483839529574394201) 1 (-76))
def d2Transfer581C0 : ℚ := (d2LitsNearTransfers072.q2 (23) 25 (-5))
def d2Transfer581S0 : ℚ := (d2LitsNearTransfers072.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer581Arithmetic : weightedUpper d2Transfer581C0 d2Log164Lo d2Log164Hi ≤ d2Transfer581Cap := by decide +kernel
theorem d2Transfer581Bound : ∀ x ∈ Set.Icc ((d2Transfer581Lo:ℚ):ℝ) ((d2Transfer581Hi:ℚ):ℝ), ((d2Transfer581C0:ℚ):ℝ)*Real.log |x-((d2Transfer581S0:ℚ):ℝ)| ≤ ((d2Transfer581Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer581S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer581S0,d2Transfer581Lo,d2Transfer581Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer581C0 then |x-((d2Transfer581S0:ℚ):ℝ)| ≤ ((d2Log164Q:ℚ):ℝ) else ((d2Log164Q:ℚ):ℝ) ≤ |x-((d2Transfer581S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer581S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer581S0,d2Transfer581Lo,d2Transfer581Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer581C0,d2Log164Q,d2Transfer581S0,d2Transfer581Lo,d2Transfer581Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer581C0 d2Transfer581S0 d2Log164Q d2Log164Lo d2Log164Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log164Bounds
  have har : (((weightedUpper d2Transfer581C0 d2Log164Lo d2Log164Hi:ℚ):ℝ)) ≤ ((d2Transfer581Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer581Arithmetic
  linarith
#print axioms d2Transfer581Arithmetic
#print axioms d2Transfer581Bound
def d2Transfer582Lo : ℚ := (d2LitsNearTransfers072.q2 (175824913) 1 (-28))
def d2Transfer582Hi : ℚ := (d2LitsNearTransfers072.q2 (88751317) 1 (-27))
def d2Transfer582Cap : ℚ := (d2LitsNearTransfers072.q2 (2336670551483778787673) 1 (-76))
def d2Transfer582C0 : ℚ := (d2LitsNearTransfers072.q2 (3) 275 (-5))
def d2Transfer582S0 : ℚ := (d2LitsNearTransfers072.q2 (-1) 1 (0))
def d2Transfer582C1 : ℚ := (d2LitsNearTransfers072.q2 (-5) 11 (-4))
def d2Transfer582S1 : ℚ := (d2LitsNearTransfers072.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer582Arithmetic : weightedUpper d2Transfer582C0 d2Log164Lo d2Log164Hi + weightedUpper d2Transfer582C1 d2Log10Lo d2Log10Hi ≤ d2Transfer582Cap := by decide +kernel
theorem d2Transfer582Bound : ∀ x ∈ Set.Icc ((d2Transfer582Lo:ℚ):ℝ) ((d2Transfer582Hi:ℚ):ℝ), ((d2Transfer582C0:ℚ):ℝ)*Real.log |x-((d2Transfer582S0:ℚ):ℝ)| + ((d2Transfer582C1:ℚ):ℝ)*Real.log |x-((d2Transfer582S1:ℚ):ℝ)| ≤ ((d2Transfer582Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer582S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer582S0,d2Transfer582Lo,d2Transfer582Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer582C0 then |x-((d2Transfer582S0:ℚ):ℝ)| ≤ ((d2Log164Q:ℚ):ℝ) else ((d2Log164Q:ℚ):ℝ) ≤ |x-((d2Transfer582S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer582S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer582S0,d2Transfer582Lo,d2Transfer582Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer582C0,d2Log164Q,d2Transfer582S0,d2Transfer582Lo,d2Transfer582Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer582C0 d2Transfer582S0 d2Log164Q d2Log164Lo d2Log164Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log164Bounds
  have hn1 : x-((d2Transfer582S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer582S1,d2Transfer582Lo,d2Transfer582Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer582C1 then |x-((d2Transfer582S1:ℚ):ℝ)| ≤ ((d2Log10Q:ℚ):ℝ) else ((d2Log10Q:ℚ):ℝ) ≤ |x-((d2Transfer582S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer582S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer582S1,d2Transfer582Lo,d2Transfer582Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer582C1,d2Log10Q,d2Transfer582S1,d2Transfer582Lo,d2Transfer582Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer582C1 d2Transfer582S1 d2Log10Q d2Log10Lo d2Log10Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log10Bounds
  have har : (((weightedUpper d2Transfer582C0 d2Log164Lo d2Log164Hi:ℚ):ℝ) + ((weightedUpper d2Transfer582C1 d2Log10Lo d2Log10Hi:ℚ):ℝ)) ≤ ((d2Transfer582Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer582Arithmetic
  linarith
#print axioms d2Transfer582Arithmetic
#print axioms d2Transfer582Bound
def d2Transfer583Lo : ℚ := (d2LitsNearTransfers072.q2 (88751317) 1 (-27))
def d2Transfer583Hi : ℚ := (d2LitsNearTransfers072.q2 (45214519) 1 (-26))
def d2Transfer583Cap : ℚ := (d2LitsNearTransfers072.q2 (1624582038057085385233) 1 (-78))
def d2Transfer583C0 : ℚ := (d2LitsNearTransfers072.q2 (-1) 55 (-3))
def d2Transfer583S0 : ℚ := (d2LitsNearTransfers072.q2 (-1) 1 (0))
def d2Transfer583C1 : ℚ := (d2LitsNearTransfers072.q2 (-1) 55 (-3))
def d2Transfer583S1 : ℚ := (d2LitsNearTransfers072.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer583Arithmetic : weightedUpper d2Transfer583C0 d2Log164Lo d2Log164Hi + weightedUpper d2Transfer583C1 d2Log9Lo d2Log9Hi ≤ d2Transfer583Cap := by decide +kernel
theorem d2Transfer583Bound : ∀ x ∈ Set.Icc ((d2Transfer583Lo:ℚ):ℝ) ((d2Transfer583Hi:ℚ):ℝ), ((d2Transfer583C0:ℚ):ℝ)*Real.log |x-((d2Transfer583S0:ℚ):ℝ)| + ((d2Transfer583C1:ℚ):ℝ)*Real.log |x-((d2Transfer583S1:ℚ):ℝ)| ≤ ((d2Transfer583Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer583S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer583S0,d2Transfer583Lo,d2Transfer583Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer583C0 then |x-((d2Transfer583S0:ℚ):ℝ)| ≤ ((d2Log164Q:ℚ):ℝ) else ((d2Log164Q:ℚ):ℝ) ≤ |x-((d2Transfer583S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer583S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer583S0,d2Transfer583Lo,d2Transfer583Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer583C0,d2Log164Q,d2Transfer583S0,d2Transfer583Lo,d2Transfer583Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer583C0 d2Transfer583S0 d2Log164Q d2Log164Lo d2Log164Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log164Bounds
  have hn1 : x-((d2Transfer583S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer583S1,d2Transfer583Lo,d2Transfer583Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer583C1 then |x-((d2Transfer583S1:ℚ):ℝ)| ≤ ((d2Log9Q:ℚ):ℝ) else ((d2Log9Q:ℚ):ℝ) ≤ |x-((d2Transfer583S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer583S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer583S1,d2Transfer583Lo,d2Transfer583Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers072.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer583C1,d2Log9Q,d2Transfer583S1,d2Transfer583Lo,d2Transfer583Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer583C1 d2Transfer583S1 d2Log9Q d2Log9Lo d2Log9Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log9Bounds
  have har : (((weightedUpper d2Transfer583C0 d2Log164Lo d2Log164Hi:ℚ):ℝ) + ((weightedUpper d2Transfer583C1 d2Log9Lo d2Log9Hi:ℚ):ℝ)) ≤ ((d2Transfer583Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer583Arithmetic
  linarith
#print axioms d2Transfer583Arithmetic
#print axioms d2Transfer583Bound
end CatalanMeasure.GenD.Signed.Data.Cells

module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers058
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers058
open D72.LogTransfer
def d2Transfer464Lo : ℚ := (d2LitsNearTransfers058.q2 (21726425) 1 (-26))
def d2Transfer464Hi : ℚ := (d2LitsNearTransfers058.q2 (11702073) 1 (-25))
def d2Transfer464Cap : ℚ := (d2LitsNearTransfers058.q2 (15113656175) 1 (-40))
def d2Transfer464C0 : ℚ := (d2LitsNearTransfers058.q2 (23) 25 (-5))
def d2Transfer464S0 : ℚ := (d2LitsNearTransfers058.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer464Arithmetic : weightedUpper d2Transfer464C0 d2Log115Lo d2Log115Hi ≤ d2Transfer464Cap := by decide +kernel
theorem d2Transfer464Bound : ∀ x ∈ Set.Icc ((d2Transfer464Lo:ℚ):ℝ) ((d2Transfer464Hi:ℚ):ℝ), ((d2Transfer464C0:ℚ):ℝ)*Real.log |x-((d2Transfer464S0:ℚ):ℝ)| ≤ ((d2Transfer464Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer464S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer464S0,d2Transfer464Lo,d2Transfer464Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer464C0 then |x-((d2Transfer464S0:ℚ):ℝ)| ≤ ((d2Log115Q:ℚ):ℝ) else ((d2Log115Q:ℚ):ℝ) ≤ |x-((d2Transfer464S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer464S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer464S0,d2Transfer464Lo,d2Transfer464Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer464C0,d2Log115Q,d2Transfer464S0,d2Transfer464Lo,d2Transfer464Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer464C0 d2Transfer464S0 d2Log115Q d2Log115Lo d2Log115Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log115Bounds
  have har : (((weightedUpper d2Transfer464C0 d2Log115Lo d2Log115Hi:ℚ):ℝ)) ≤ ((d2Transfer464Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer464Arithmetic
  linarith
#print axioms d2Transfer464Arithmetic
#print axioms d2Transfer464Bound
def d2Transfer465Lo : ℚ := (d2LitsNearTransfers058.q2 (21726425) 1 (-26))
def d2Transfer465Hi : ℚ := (d2LitsNearTransfers058.q2 (11702073) 1 (-25))
def d2Transfer465Cap : ℚ := (d2LitsNearTransfers058.q2 (30439539927) 1 (-40))
def d2Transfer465C0 : ℚ := (d2LitsNearTransfers058.q2 (3) 275 (-5))
def d2Transfer465S0 : ℚ := (d2LitsNearTransfers058.q2 (-1) 1 (0))
def d2Transfer465C1 : ℚ := (d2LitsNearTransfers058.q2 (-5) 11 (-4))
def d2Transfer465S1 : ℚ := (d2LitsNearTransfers058.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer465Arithmetic : weightedUpper d2Transfer465C0 d2Log115Lo d2Log115Hi + weightedUpper d2Transfer465C1 d2Log59Lo d2Log59Hi ≤ d2Transfer465Cap := by decide +kernel
theorem d2Transfer465Bound : ∀ x ∈ Set.Icc ((d2Transfer465Lo:ℚ):ℝ) ((d2Transfer465Hi:ℚ):ℝ), ((d2Transfer465C0:ℚ):ℝ)*Real.log |x-((d2Transfer465S0:ℚ):ℝ)| + ((d2Transfer465C1:ℚ):ℝ)*Real.log |x-((d2Transfer465S1:ℚ):ℝ)| ≤ ((d2Transfer465Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer465S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer465S0,d2Transfer465Lo,d2Transfer465Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer465C0 then |x-((d2Transfer465S0:ℚ):ℝ)| ≤ ((d2Log115Q:ℚ):ℝ) else ((d2Log115Q:ℚ):ℝ) ≤ |x-((d2Transfer465S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer465S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer465S0,d2Transfer465Lo,d2Transfer465Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer465C0,d2Log115Q,d2Transfer465S0,d2Transfer465Lo,d2Transfer465Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer465C0 d2Transfer465S0 d2Log115Q d2Log115Lo d2Log115Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log115Bounds
  have hn1 : x-((d2Transfer465S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer465S1,d2Transfer465Lo,d2Transfer465Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer465C1 then |x-((d2Transfer465S1:ℚ):ℝ)| ≤ ((d2Log59Q:ℚ):ℝ) else ((d2Log59Q:ℚ):ℝ) ≤ |x-((d2Transfer465S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer465S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer465S1,d2Transfer465Lo,d2Transfer465Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer465C1,d2Log59Q,d2Transfer465S1,d2Transfer465Lo,d2Transfer465Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer465C1 d2Transfer465S1 d2Log59Q d2Log59Lo d2Log59Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log59Bounds
  have har : (((weightedUpper d2Transfer465C0 d2Log115Lo d2Log115Hi:ℚ):ℝ) + ((weightedUpper d2Transfer465C1 d2Log59Lo d2Log59Hi:ℚ):ℝ)) ≤ ((d2Transfer465Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer465Arithmetic
  linarith
#print axioms d2Transfer465Arithmetic
#print axioms d2Transfer465Bound
def d2Transfer466Lo : ℚ := (d2LitsNearTransfers058.q2 (11702073) 1 (-25))
def d2Transfer466Hi : ℚ := (d2LitsNearTransfers058.q2 (25081867) 1 (-26))
def d2Transfer466Cap : ℚ := (d2LitsNearTransfers058.q2 (1169469059) 1 (-40))
def d2Transfer466C0 : ℚ := (d2LitsNearTransfers058.q2 (-1) 55 (-3))
def d2Transfer466S0 : ℚ := (d2LitsNearTransfers058.q2 (-1) 1 (0))
def d2Transfer466C1 : ℚ := (d2LitsNearTransfers058.q2 (-1) 55 (-3))
def d2Transfer466S1 : ℚ := (d2LitsNearTransfers058.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer466Arithmetic : weightedUpper d2Transfer466C0 d2Log115Lo d2Log115Hi + weightedUpper d2Transfer466C1 d2Log58Lo d2Log58Hi ≤ d2Transfer466Cap := by decide +kernel
theorem d2Transfer466Bound : ∀ x ∈ Set.Icc ((d2Transfer466Lo:ℚ):ℝ) ((d2Transfer466Hi:ℚ):ℝ), ((d2Transfer466C0:ℚ):ℝ)*Real.log |x-((d2Transfer466S0:ℚ):ℝ)| + ((d2Transfer466C1:ℚ):ℝ)*Real.log |x-((d2Transfer466S1:ℚ):ℝ)| ≤ ((d2Transfer466Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer466S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer466S0,d2Transfer466Lo,d2Transfer466Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer466C0 then |x-((d2Transfer466S0:ℚ):ℝ)| ≤ ((d2Log115Q:ℚ):ℝ) else ((d2Log115Q:ℚ):ℝ) ≤ |x-((d2Transfer466S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer466S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer466S0,d2Transfer466Lo,d2Transfer466Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer466C0,d2Log115Q,d2Transfer466S0,d2Transfer466Lo,d2Transfer466Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer466C0 d2Transfer466S0 d2Log115Q d2Log115Lo d2Log115Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log115Bounds
  have hn1 : x-((d2Transfer466S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer466S1,d2Transfer466Lo,d2Transfer466Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer466C1 then |x-((d2Transfer466S1:ℚ):ℝ)| ≤ ((d2Log58Q:ℚ):ℝ) else ((d2Log58Q:ℚ):ℝ) ≤ |x-((d2Transfer466S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer466S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer466S1,d2Transfer466Lo,d2Transfer466Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer466C1,d2Log58Q,d2Transfer466S1,d2Transfer466Lo,d2Transfer466Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer466C1 d2Transfer466S1 d2Log58Q d2Log58Lo d2Log58Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log58Bounds
  have har : (((weightedUpper d2Transfer466C0 d2Log115Lo d2Log115Hi:ℚ):ℝ) + ((weightedUpper d2Transfer466C1 d2Log58Lo d2Log58Hi:ℚ):ℝ)) ≤ ((d2Transfer466Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer466Arithmetic
  linarith
#print axioms d2Transfer466Arithmetic
#print axioms d2Transfer466Bound
def d2Transfer467Lo : ℚ := (d2LitsNearTransfers058.q2 (11702073) 1 (-25))
def d2Transfer467Hi : ℚ := (d2LitsNearTransfers058.q2 (25081867) 1 (-26))
def d2Transfer467Cap : ℚ := (d2LitsNearTransfers058.q2 (15113656175) 1 (-40))
def d2Transfer467C0 : ℚ := (d2LitsNearTransfers058.q2 (23) 25 (-5))
def d2Transfer467S0 : ℚ := (d2LitsNearTransfers058.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer467Arithmetic : weightedUpper d2Transfer467C0 d2Log116Lo d2Log116Hi ≤ d2Transfer467Cap := by decide +kernel
theorem d2Transfer467Bound : ∀ x ∈ Set.Icc ((d2Transfer467Lo:ℚ):ℝ) ((d2Transfer467Hi:ℚ):ℝ), ((d2Transfer467C0:ℚ):ℝ)*Real.log |x-((d2Transfer467S0:ℚ):ℝ)| ≤ ((d2Transfer467Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer467S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer467S0,d2Transfer467Lo,d2Transfer467Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer467C0 then |x-((d2Transfer467S0:ℚ):ℝ)| ≤ ((d2Log116Q:ℚ):ℝ) else ((d2Log116Q:ℚ):ℝ) ≤ |x-((d2Transfer467S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer467S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer467S0,d2Transfer467Lo,d2Transfer467Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer467C0,d2Log116Q,d2Transfer467S0,d2Transfer467Lo,d2Transfer467Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer467C0 d2Transfer467S0 d2Log116Q d2Log116Lo d2Log116Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log116Bounds
  have har : (((weightedUpper d2Transfer467C0 d2Log116Lo d2Log116Hi:ℚ):ℝ)) ≤ ((d2Transfer467Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer467Arithmetic
  linarith
#print axioms d2Transfer467Arithmetic
#print axioms d2Transfer467Bound
def d2Transfer468Lo : ℚ := (d2LitsNearTransfers058.q2 (11702073) 1 (-25))
def d2Transfer468Hi : ℚ := (d2LitsNearTransfers058.q2 (25081867) 1 (-26))
def d2Transfer468Cap : ℚ := (d2LitsNearTransfers058.q2 (30439539927) 1 (-40))
def d2Transfer468C0 : ℚ := (d2LitsNearTransfers058.q2 (3) 275 (-5))
def d2Transfer468S0 : ℚ := (d2LitsNearTransfers058.q2 (-1) 1 (0))
def d2Transfer468C1 : ℚ := (d2LitsNearTransfers058.q2 (-5) 11 (-4))
def d2Transfer468S1 : ℚ := (d2LitsNearTransfers058.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer468Arithmetic : weightedUpper d2Transfer468C0 d2Log116Lo d2Log116Hi + weightedUpper d2Transfer468C1 d2Log58Lo d2Log58Hi ≤ d2Transfer468Cap := by decide +kernel
theorem d2Transfer468Bound : ∀ x ∈ Set.Icc ((d2Transfer468Lo:ℚ):ℝ) ((d2Transfer468Hi:ℚ):ℝ), ((d2Transfer468C0:ℚ):ℝ)*Real.log |x-((d2Transfer468S0:ℚ):ℝ)| + ((d2Transfer468C1:ℚ):ℝ)*Real.log |x-((d2Transfer468S1:ℚ):ℝ)| ≤ ((d2Transfer468Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer468S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer468S0,d2Transfer468Lo,d2Transfer468Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer468C0 then |x-((d2Transfer468S0:ℚ):ℝ)| ≤ ((d2Log116Q:ℚ):ℝ) else ((d2Log116Q:ℚ):ℝ) ≤ |x-((d2Transfer468S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer468S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer468S0,d2Transfer468Lo,d2Transfer468Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer468C0,d2Log116Q,d2Transfer468S0,d2Transfer468Lo,d2Transfer468Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer468C0 d2Transfer468S0 d2Log116Q d2Log116Lo d2Log116Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log116Bounds
  have hn1 : x-((d2Transfer468S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer468S1,d2Transfer468Lo,d2Transfer468Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer468C1 then |x-((d2Transfer468S1:ℚ):ℝ)| ≤ ((d2Log58Q:ℚ):ℝ) else ((d2Log58Q:ℚ):ℝ) ≤ |x-((d2Transfer468S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer468S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer468S1,d2Transfer468Lo,d2Transfer468Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer468C1,d2Log58Q,d2Transfer468S1,d2Transfer468Lo,d2Transfer468Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer468C1 d2Transfer468S1 d2Log58Q d2Log58Lo d2Log58Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log58Bounds
  have har : (((weightedUpper d2Transfer468C0 d2Log116Lo d2Log116Hi:ℚ):ℝ) + ((weightedUpper d2Transfer468C1 d2Log58Lo d2Log58Hi:ℚ):ℝ)) ≤ ((d2Transfer468Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer468Arithmetic
  linarith
#print axioms d2Transfer468Arithmetic
#print axioms d2Transfer468Bound
def d2Transfer469Lo : ℚ := (d2LitsNearTransfers058.q2 (25081867) 1 (-26))
def d2Transfer469Hi : ℚ := (d2LitsNearTransfers058.q2 (6689897) 1 (-24))
def d2Transfer469Cap : ℚ := (d2LitsNearTransfers058.q2 (1169469059) 1 (-40))
def d2Transfer469C0 : ℚ := (d2LitsNearTransfers058.q2 (-1) 55 (-3))
def d2Transfer469S0 : ℚ := (d2LitsNearTransfers058.q2 (-1) 1 (0))
def d2Transfer469C1 : ℚ := (d2LitsNearTransfers058.q2 (-1) 55 (-3))
def d2Transfer469S1 : ℚ := (d2LitsNearTransfers058.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer469Arithmetic : weightedUpper d2Transfer469C0 d2Log116Lo d2Log116Hi + weightedUpper d2Transfer469C1 d2Log57Lo d2Log57Hi ≤ d2Transfer469Cap := by decide +kernel
theorem d2Transfer469Bound : ∀ x ∈ Set.Icc ((d2Transfer469Lo:ℚ):ℝ) ((d2Transfer469Hi:ℚ):ℝ), ((d2Transfer469C0:ℚ):ℝ)*Real.log |x-((d2Transfer469S0:ℚ):ℝ)| + ((d2Transfer469C1:ℚ):ℝ)*Real.log |x-((d2Transfer469S1:ℚ):ℝ)| ≤ ((d2Transfer469Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer469S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer469S0,d2Transfer469Lo,d2Transfer469Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer469C0 then |x-((d2Transfer469S0:ℚ):ℝ)| ≤ ((d2Log116Q:ℚ):ℝ) else ((d2Log116Q:ℚ):ℝ) ≤ |x-((d2Transfer469S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer469S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer469S0,d2Transfer469Lo,d2Transfer469Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer469C0,d2Log116Q,d2Transfer469S0,d2Transfer469Lo,d2Transfer469Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer469C0 d2Transfer469S0 d2Log116Q d2Log116Lo d2Log116Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log116Bounds
  have hn1 : x-((d2Transfer469S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer469S1,d2Transfer469Lo,d2Transfer469Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer469C1 then |x-((d2Transfer469S1:ℚ):ℝ)| ≤ ((d2Log57Q:ℚ):ℝ) else ((d2Log57Q:ℚ):ℝ) ≤ |x-((d2Transfer469S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer469S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer469S1,d2Transfer469Lo,d2Transfer469Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer469C1,d2Log57Q,d2Transfer469S1,d2Transfer469Lo,d2Transfer469Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer469C1 d2Transfer469S1 d2Log57Q d2Log57Lo d2Log57Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log57Bounds
  have har : (((weightedUpper d2Transfer469C0 d2Log116Lo d2Log116Hi:ℚ):ℝ) + ((weightedUpper d2Transfer469C1 d2Log57Lo d2Log57Hi:ℚ):ℝ)) ≤ ((d2Transfer469Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer469Arithmetic
  linarith
#print axioms d2Transfer469Arithmetic
#print axioms d2Transfer469Bound
def d2Transfer470Lo : ℚ := (d2LitsNearTransfers058.q2 (25081867) 1 (-26))
def d2Transfer470Hi : ℚ := (d2LitsNearTransfers058.q2 (6689897) 1 (-24))
def d2Transfer470Cap : ℚ := (d2LitsNearTransfers058.q2 (15113656175) 1 (-40))
def d2Transfer470C0 : ℚ := (d2LitsNearTransfers058.q2 (23) 25 (-5))
def d2Transfer470S0 : ℚ := (d2LitsNearTransfers058.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer470Arithmetic : weightedUpper d2Transfer470C0 d2Log117Lo d2Log117Hi ≤ d2Transfer470Cap := by decide +kernel
theorem d2Transfer470Bound : ∀ x ∈ Set.Icc ((d2Transfer470Lo:ℚ):ℝ) ((d2Transfer470Hi:ℚ):ℝ), ((d2Transfer470C0:ℚ):ℝ)*Real.log |x-((d2Transfer470S0:ℚ):ℝ)| ≤ ((d2Transfer470Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer470S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer470S0,d2Transfer470Lo,d2Transfer470Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer470C0 then |x-((d2Transfer470S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2Transfer470S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer470S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer470S0,d2Transfer470Lo,d2Transfer470Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer470C0,d2Log117Q,d2Transfer470S0,d2Transfer470Lo,d2Transfer470Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer470C0 d2Transfer470S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have har : (((weightedUpper d2Transfer470C0 d2Log117Lo d2Log117Hi:ℚ):ℝ)) ≤ ((d2Transfer470Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer470Arithmetic
  linarith
#print axioms d2Transfer470Arithmetic
#print axioms d2Transfer470Bound
def d2Transfer471Lo : ℚ := (d2LitsNearTransfers058.q2 (25081867) 1 (-26))
def d2Transfer471Hi : ℚ := (d2LitsNearTransfers058.q2 (6689897) 1 (-24))
def d2Transfer471Cap : ℚ := (d2LitsNearTransfers058.q2 (30439539927) 1 (-40))
def d2Transfer471C0 : ℚ := (d2LitsNearTransfers058.q2 (3) 275 (-5))
def d2Transfer471S0 : ℚ := (d2LitsNearTransfers058.q2 (-1) 1 (0))
def d2Transfer471C1 : ℚ := (d2LitsNearTransfers058.q2 (-5) 11 (-4))
def d2Transfer471S1 : ℚ := (d2LitsNearTransfers058.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer471Arithmetic : weightedUpper d2Transfer471C0 d2Log117Lo d2Log117Hi + weightedUpper d2Transfer471C1 d2Log57Lo d2Log57Hi ≤ d2Transfer471Cap := by decide +kernel
theorem d2Transfer471Bound : ∀ x ∈ Set.Icc ((d2Transfer471Lo:ℚ):ℝ) ((d2Transfer471Hi:ℚ):ℝ), ((d2Transfer471C0:ℚ):ℝ)*Real.log |x-((d2Transfer471S0:ℚ):ℝ)| + ((d2Transfer471C1:ℚ):ℝ)*Real.log |x-((d2Transfer471S1:ℚ):ℝ)| ≤ ((d2Transfer471Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer471S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer471S0,d2Transfer471Lo,d2Transfer471Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer471C0 then |x-((d2Transfer471S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2Transfer471S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer471S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer471S0,d2Transfer471Lo,d2Transfer471Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer471C0,d2Log117Q,d2Transfer471S0,d2Transfer471Lo,d2Transfer471Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer471C0 d2Transfer471S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have hn1 : x-((d2Transfer471S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer471S1,d2Transfer471Lo,d2Transfer471Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer471C1 then |x-((d2Transfer471S1:ℚ):ℝ)| ≤ ((d2Log57Q:ℚ):ℝ) else ((d2Log57Q:ℚ):ℝ) ≤ |x-((d2Transfer471S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer471S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer471S1,d2Transfer471Lo,d2Transfer471Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers058.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer471C1,d2Log57Q,d2Transfer471S1,d2Transfer471Lo,d2Transfer471Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer471C1 d2Transfer471S1 d2Log57Q d2Log57Lo d2Log57Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log57Bounds
  have har : (((weightedUpper d2Transfer471C0 d2Log117Lo d2Log117Hi:ℚ):ℝ) + ((weightedUpper d2Transfer471C1 d2Log57Lo d2Log57Hi:ℚ):ℝ)) ≤ ((d2Transfer471Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer471Arithmetic
  linarith
#print axioms d2Transfer471Arithmetic
#print axioms d2Transfer471Bound
end CatalanMeasure.GenD.Signed.Data.Cells

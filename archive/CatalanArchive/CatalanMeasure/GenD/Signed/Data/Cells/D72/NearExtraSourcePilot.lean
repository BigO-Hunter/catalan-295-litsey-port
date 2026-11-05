module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace D72.NearExtraSourcePilot
open D72.LogTransfer
set_option profiler true
set_option profiler.threshold 0
namespace d2LitsNearLogCache005
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearLogCache005
def d2Log86Q : ℚ := (d2LitsNearLogCache005.q2 (7560241) 1 (-23))
def d2Log86V : ℚ := (d2LitsNearLogCache005.q2 (-6458528414257936498022158566478484041766255823937875065338457986609174129229373151836477309441949039597887929414923674474890701414886465812137820299551276564719598924509015696875021196761877016375397605718647299710920337816040551758912751203157388433952776681004180833) 182549104792811022502744314048587730221255374636976715777306602725919914775477141845440173454340486665751183934334454085216458266642805840109518858784289589393634091940595984105700278100242774112652807535832929424941539764404296875 (-128))
def d2Log86E : ℚ := (d2LitsNearLogCache005.q2 (1496571967636073764401049035557596014147129393020929) 262143 (-278))
def d2Log86Lo : ℚ := (d2LitsNearLogCache005.q2 (-8844919318542010458829597346063851033) 1 (-126))
def d2Log86Hi : ℚ := (d2LitsNearLogCache005.q2 (-35379677274168041835318389384255404123) 1 (-128))
-- kcost: one shared-node rational log at n16; per-log declaration, outward dyadic endpoints.
theorem d2Log86Eval : logQ 16 d2Log86Q = some (d2Log86V,d2Log86E) := by decide +kernel
theorem d2Log86Bounds : ((d2Log86Lo : ℚ):ℝ) ≤ Real.log ((d2Log86Q:ℚ):ℝ) ∧ Real.log ((d2Log86Q:ℚ):ℝ) ≤ ((d2Log86Hi:ℚ):ℝ) := log_interval d2Log86Eval (by decide +kernel) (by decide +kernel)
#print axioms d2Log86Eval
#print axioms d2Log86Bounds
def d2Log88Q : ℚ := (d2LitsNearLogCache005.q2 (9216975) 1 (-23))
def d2Log88V : ℚ := (d2LitsNearLogCache005.q2 (9390549237782338896177158119927754061782758885619589419435028328685005618172507653361612316112379142696076310635303935758656890090649267192195619268905589178143112471587336296388526609245743062874272687357125148969245108951287708237536716337692766426517270357255805001249037) 586081992692055212649426635506117033339714245919074508213635773977923619558288797388720500753202358747659483741896550276818757746234925122024890910788820481298005208417753463052340203970799399798109221679584171067169144165329754403397575 (-127))
def d2Log88E : ℚ := (d2LitsNearLogCache005.q2 (748285983818036882200524517778798007073564696510465) 262143 (-278))
def d2Log88Lo : ℚ := (d2LitsNearLogCache005.q2 (32045172364530949821831959661090036331) 1 (-128))
def d2Log88Hi : ℚ := (d2LitsNearLogCache005.q2 (2002823272783184363864497478818127271) 1 (-124))
-- kcost: one shared-node rational log at n16; per-log declaration, outward dyadic endpoints.
theorem d2Log88Eval : logQ 16 d2Log88Q = some (d2Log88V,d2Log88E) := by decide +kernel
theorem d2Log88Bounds : ((d2Log88Lo : ℚ):ℝ) ≤ Real.log ((d2Log88Q:ℚ):ℝ) ∧ Real.log ((d2Log88Q:ℚ):ℝ) ≤ ((d2Log88Hi:ℚ):ℝ) := log_interval d2Log88Eval (by decide +kernel) (by decide +kernel)
#print axioms d2Log88Eval
#print axioms d2Log88Bounds
namespace d2LitsNearTransfers084
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers084
def d2Transfer673Lo : ℚ := (d2LitsNearTransfers084.q2 (999) 125 (-3))
def d2Transfer673Hi : ℚ := (d2LitsNearTransfers084.q2 (16760439) 1 (-24))
def d2Transfer673Cap : ℚ := (d2LitsNearTransfers084.q2 (241850313660495) 1 (-78))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer673Arithmetic : (0 : ℚ) ≤ d2Transfer673Cap := by decide +kernel
theorem d2Transfer673Bound : ∀ x ∈ Set.Icc ((d2Transfer673Lo:ℚ):ℝ) ((d2Transfer673Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2Transfer673Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2Transfer673Arithmetic
#print axioms d2Transfer673Arithmetic
#print axioms d2Transfer673Bound
namespace d2LitsNearTransfers000
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers000
def d2Transfer0Lo : ℚ := (d2LitsNearTransfers000.q2 (98749) 15625 (-6))
def d2Transfer0Hi : ℚ := (d2LitsNearTransfers000.q2 (828367) 1 (-23))
def d2Transfer0Cap : ℚ := (d2LitsNearTransfers000.q2 (648894057) 1 (-39))
def d2Transfer0C0 : ℚ := (d2LitsNearTransfers000.q2 (1) 25 (-4))
def d2Transfer0S0 : ℚ := (d2LitsNearTransfers000.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer0Arithmetic : weightedUpper d2Transfer0C0 d2Log88Lo d2Log88Hi ≤ d2Transfer0Cap := by decide +kernel
theorem d2Transfer0Bound : ∀ x ∈ Set.Icc ((d2Transfer0Lo:ℚ):ℝ) ((d2Transfer0Hi:ℚ):ℝ), ((d2Transfer0C0:ℚ):ℝ)*Real.log |x-((d2Transfer0S0:ℚ):ℝ)| ≤ ((d2Transfer0Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer0S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer0S0,d2Transfer0Lo,d2Transfer0Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer0C0 then |x-((d2Transfer0S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2Transfer0S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer0S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer0S0,d2Transfer0Lo,d2Transfer0Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer0C0,d2Log88Q,d2Transfer0S0,d2Transfer0Lo,d2Transfer0Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer0C0 d2Transfer0S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have har : (((weightedUpper d2Transfer0C0 d2Log88Lo d2Log88Hi:ℚ):ℝ)) ≤ ((d2Transfer0Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer0Arithmetic
  linarith
#print axioms d2Transfer0Arithmetic
#print axioms d2Transfer0Bound
def d2Transfer1Lo : ℚ := (d2LitsNearTransfers000.q2 (98749) 15625 (-6))
def d2Transfer1Hi : ℚ := (d2LitsNearTransfers000.q2 (828367) 1 (-23))
def d2Transfer1Cap : ℚ := (d2LitsNearTransfers000.q2 (2432512853) 1 (-40))
def d2Transfer1C0 : ℚ := (d2LitsNearTransfers000.q2 (1) 275 (-4))
def d2Transfer1S0 : ℚ := (d2LitsNearTransfers000.q2 (-1) 1 (0))
def d2Transfer1C1 : ℚ := (d2LitsNearTransfers000.q2 (-1) 55 (-3))
def d2Transfer1S1 : ℚ := (d2LitsNearTransfers000.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer1Arithmetic : weightedUpper d2Transfer1C0 d2Log88Lo d2Log88Hi + weightedUpper d2Transfer1C1 d2Log86Lo d2Log86Hi ≤ d2Transfer1Cap := by decide +kernel
theorem d2Transfer1Bound : ∀ x ∈ Set.Icc ((d2Transfer1Lo:ℚ):ℝ) ((d2Transfer1Hi:ℚ):ℝ), ((d2Transfer1C0:ℚ):ℝ)*Real.log |x-((d2Transfer1S0:ℚ):ℝ)| + ((d2Transfer1C1:ℚ):ℝ)*Real.log |x-((d2Transfer1S1:ℚ):ℝ)| ≤ ((d2Transfer1Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer1S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer1S0,d2Transfer1Lo,d2Transfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer1C0 then |x-((d2Transfer1S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2Transfer1S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer1S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer1S0,d2Transfer1Lo,d2Transfer1Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer1C0,d2Log88Q,d2Transfer1S0,d2Transfer1Lo,d2Transfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer1C0 d2Transfer1S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have hn1 : x-((d2Transfer1S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer1S1,d2Transfer1Lo,d2Transfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer1C1 then |x-((d2Transfer1S1:ℚ):ℝ)| ≤ ((d2Log86Q:ℚ):ℝ) else ((d2Log86Q:ℚ):ℝ) ≤ |x-((d2Transfer1S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer1S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer1S1,d2Transfer1Lo,d2Transfer1Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers000.q2, d2LitsNearLogCache005.q2, d2Transfer1C1,d2Log86Q,d2Transfer1S1,d2Transfer1Lo,d2Transfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer1C1 d2Transfer1S1 d2Log86Q d2Log86Lo d2Log86Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log86Bounds
  have har : (((weightedUpper d2Transfer1C0 d2Log88Lo d2Log88Hi:ℚ):ℝ) + ((weightedUpper d2Transfer1C1 d2Log86Lo d2Log86Hi:ℚ):ℝ)) ≤ ((d2Transfer1Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer1Arithmetic
  linarith
#print axioms d2Transfer1Arithmetic
#print axioms d2Transfer1Bound
end D72.NearExtraSourcePilot
end CatalanMeasure.GenD.Signed.Data.Cells

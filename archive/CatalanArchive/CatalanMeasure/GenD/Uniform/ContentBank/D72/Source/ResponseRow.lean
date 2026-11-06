module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Response
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open Finset CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Charts6
noncomputable section
variable {p : Nat} [Fact p.Prime]

def optionalProjection {n : Nat} (c : Option (Fin n)) :
    (Fin n → ZMod p) →ₗ[ZMod p] ZMod p :=
  match c with
  | none => 0
  | some i => LinearMap.proj i

def foldedResponseLinear {n b ex K : Nat} (hK : K = b * 4 + 2 + ex)
    (k0 : Int) (ah aq : Nat) (slots : Fin n → Option (Fin K))
    (H J : Nat) (S : Int) (low : Fin n) (slack : Option (Fin n)) :
    (Fin n → ZMod p) →ₗ[ZMod p] ZMod p :=
  (∑ j ∈ range (aq + 1), ((-1 : ZMod p) ^ (aq - j) * (aq.choose j : ZMod p)) •
    (((responseProf hK k0 ah).psi H (J + j) S).comp (sparseSourceIns slots))) -
    LinearMap.proj low - optionalProjection slack

def foldedTargetCheck {n b ex K : Nat} (hK : K = b * 4 + 2 + ex)
    (k0 : Int) (ah aq : Nat) (slots : Fin n → Option (Fin K)) (J : Nat) (S : Int)
    (low : Fin n) (slack : Option (Fin n)) (target : List Int) : Bool :=
  decide (target.length = n) &&
    (List.finRange n).all (fun c => decide (sourceFoldedCoeff? hK k0 ah aq (slots c) J S
      (decide (c = low)) (decide (slack = some c)) = some (target.getD c.val 0)))

theorem foldedTargetCheck_sound {n b ex K H : Nat} (hK : K = b * 4 + 2 + ex)
    (k0 : Int) (ah aq : Nat) (slots : Fin n → Option (Fin K)) (J : Nat) (S : Int)
    (low : Fin n) (slack : Option (Fin n)) (target : List Int)
    (hp : 44 < p) (hz : (momentData.scale : ZMod p) ≠ 0) (hp2 : p ≠ 2)
    (hS : S.toNat + 3 ≤ 41) (hH : S.toNat + 3 ≤ H)
    (hc : foldedTargetCheck hK k0 ah aq slots J S low slack target = true) (c : Fin n) :
    (target.getD c.val 0 : ZMod p) =
      (sourceResponseScale : ZMod p) *
        foldedResponseLinear hK k0 ah aq slots H J S low slack (Pi.single c 1) := by
  simp only [foldedTargetCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  have he := sourceFoldedCoeff?_sound (p := p) (H := H) hK k0 ah aq (slots c)
    (decide (c = low)) (decide (slack = some c)) hp hz hp2 hS hH (hc.2 c (by simp))
  have hsc := sourceResponseScale_ne_zero hp hz
  have hlin : foldedResponseLinear (p := p) hK k0 ah aq slots H J S low slack (Pi.single c 1) =
      (target.getD c.val 0 : ZMod p) / (sourceResponseScale : ZMod p) := by
    cases slack with
    | none =>
      simpa [foldedResponseLinear, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        sparseSourceIns_single, optionalProjection, Pi.single_apply, eq_comm] using he
    | some s =>
      simpa [foldedResponseLinear, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        sparseSourceIns_single, optionalProjection, Pi.single_apply, eq_comm] using he
  exact ((eq_div_iff hsc).mp hlin).symm.trans (mul_comm _ _)

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source

module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Bank
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open Finset CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : Nat} [Fact p.Prime]

def sourceResponseScale : Int := 2 * momentData.scale

theorem sourceResponseScale_ne_zero (hp : 44 < p) (hz : (momentData.scale : ZMod p) ≠ 0) :
    (sourceResponseScale : ZMod p) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz2
    have hzI : ((2 : Int) : ZMod p) = 0 := by simpa using hz2
    have hdivI := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp hzI
    have hdiv : p ∣ 2 := by exact_mod_cast hdivI
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    omega
  unfold sourceResponseScale
  push_cast
  exact mul_ne_zero h2 hz

def sourceSlotCoeff? {b ex K : Nat} (hK : K = b * 4 + 2 + ex)
    (k0 : Int) (ah : Nat) (slot : Option (Fin K)) (J : Nat) (S : Int) : Option Int :=
  match slot with
  | none => some 0
  | some k => sourceCoeff? (SourceExpr.profile k0 ah (ckEquiv hK k)) J S

def sourceVector {K : Nat} (slot : Option (Fin K)) : Fin K → ZMod p :=
  match slot with
  | none => 0
  | some k => Pi.single k 1

def sparseSourceIns {n K : Nat} (slots : Fin n → Option (Fin K)) :
    (Fin n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p) :=
  ∑ c : Fin n, (LinearMap.proj c).smulRight (sourceVector (p := p) (slots c))

theorem sparseSourceIns_single {n K : Nat} (slots : Fin n → Option (Fin K)) (c : Fin n) :
    sparseSourceIns (p := p) slots (Pi.single c 1) = sourceVector (slots c) := by
  simp only [sparseSourceIns, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single c]
  · simp
  · intro i _ hi
    simp [Pi.single_apply, hi, Ne.symm hi]
  · simp

def responseProf {b ex K : Nat} (hK : K = b * 4 + 2 + ex) (k0 : Int) (ah : Nat) : Prof p K :=
  ⟨sumProf hK (uCoefs k0 ah),sumProf hK (tCoefs k0 ah)⟩

theorem sourceSlotCoeff?_sound {b ex K H : Nat} (hK : K = b * 4 + 2 + ex)
    (k0 : Int) (ah : Nat) (slot : Option (Fin K)) {J : Nat} {S v : Int}
    (hp : 44 < p) (hz : (momentData.scale : ZMod p) ≠ 0)
    (hS : S.toNat + 3 ≤ 41) (hH : S.toNat + 3 ≤ H)
    (h : sourceSlotCoeff? hK k0 ah slot J S = some v) :
    (responseProf (p := p) hK k0 ah).psi H J S (sourceVector slot) =
      (v : ZMod p) / (sourceResponseScale : ZMod p) := by
  cases slot with
  | none =>
    simp [sourceSlotCoeff?] at h
    subst v
    simp [sourceVector]
  | some k =>
    obtain ⟨i, hi, hv⟩ := sourceCoeff?_index _ h
    obtain ⟨hg, ht⟩ := sourcePair_check i
    rw [hi] at hg ht
    have hil := i.isLt
    have hJ : J < momentData.L := by change J < 35; omega
    exact SourceExpr.profile_psi_sound hK k0 ah k momentData (sourcePair i).1 (sourcePair i).2
      J hJ hp hz momentData_check hg ht hS hH hv

/-- The computed ambient response numerator includes the common low
coordinate and, when present, a local graph slack. -/
def sourceFoldedCoeff? {b ex K : Nat} (hK : K = b * 4 + 2 + ex)
    (k0 : Int) (ah aq : Nat) (slot : Option (Fin K)) (J : Nat) (S : Int)
    (low slack : Bool) : Option Int := do
  let u ← sourceSlotCoeff? hK k0 ah slot J S
  let w ← if aq = 0 then some u else
    if aq = 1 then (sourceSlotCoeff? hK k0 ah slot (J + 1) S).map (· - u) else none
  pure (w - (if low then sourceResponseScale else 0) - (if slack then sourceResponseScale else 0))

theorem sourceFoldedCoeff?_sound {b ex K H : Nat} (hK : K = b * 4 + 2 + ex)
    (k0 : Int) (ah aq : Nat) (slot : Option (Fin K)) {J : Nat} {S v : Int}
    (low slack : Bool) (hp : 44 < p) (hz : (momentData.scale : ZMod p) ≠ 0)
    (hp2 : p ≠ 2) (hS : S.toNat + 3 ≤ 41) (hH : S.toNat + 3 ≤ H)
    (h : sourceFoldedCoeff? hK k0 ah aq slot J S low slack = some v) :
    (∑ j ∈ range (aq + 1), ((-1 : ZMod p) ^ (aq - j) * (aq.choose j : ZMod p)) *
        (responseProf (p := p) hK k0 ah).psi H (J + j) S (sourceVector slot)) -
      (if low then 1 else 0) - (if slack then 1 else 0) =
      (v : ZMod p) / (sourceResponseScale : ZMod p) := by
  have hsc := sourceResponseScale_ne_zero hp hz
  cases he : sourceSlotCoeff? hK k0 ah slot J S with
  | none => simp [sourceFoldedCoeff?, he] at h
  | some u =>
    have hu := sourceSlotCoeff?_sound (p := p) hK k0 ah slot hp hz hS hH he
    by_cases h0 : aq = 0
    · subst aq
      simp [sourceFoldedCoeff?, he] at h
      subst v
      cases low <;> cases slack <;> simp [hu, Int.cast_sub, sub_div, hsc] <;> ring
    · by_cases h1 : aq = 1
      · subst aq
        cases hw : sourceSlotCoeff? hK k0 ah slot (J + 1) S with
        | none => simp [sourceFoldedCoeff?, he, hw] at h
        | some w =>
          have hw' := sourceSlotCoeff?_sound (p := p) hK k0 ah slot hp hz hS hH hw
          simp [sourceFoldedCoeff?, he, hw] at h
          subst v
          cases low <;> cases slack <;>
            simp [Finset.sum_range_succ, hu, hw', Int.cast_sub, sub_div, hsc] <;> ring
      · simp [sourceFoldedCoeff?, he, h0, h1] at h

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source

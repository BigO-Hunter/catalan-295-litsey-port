module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Response
public import CatalanMeasure.GenD.Uniform.W.Thin.TKill
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open Polynomial Polynomial.Chebyshev Finset
open CatalanMeasure.GenD.Uniform.W.Charts6 CatalanMeasure.GenD.Uniform.W.Slots
open CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {p : Nat} [Fact p.Prime]

theorem thin_basis_coeff {K : Nat} (k0 : Int) (k : Fin K) {H J : Nat} {S v : Int}
    (hp : 44 < p) (hz : (momentData.scale : ZMod p) ≠ 0)
    (hS : S.toNat + 3 ≤ 41) (hH : S.toNat + 3 ≤ H)
    (hv : sourceCoeff? (.tm (k0 + k.val)) J S = some v) :
    psiLin p K k0 H J S (Pi.single k 1) = (v : ZMod p) / (sourceResponseScale : ZMod p) := by
  obtain ⟨i, hi, he⟩ := sourceCoeff?_index _ hv
  obtain ⟨hg, ht⟩ := sourcePair_check i
  rw [hi] at hg ht
  have hil := i.isLt
  have hJ : J < momentData.L := by change J < 35; omega
  let F : Prof p K := ⟨tyMap p K k0, gyMap p K k0⟩
  change F.psi H J S (Pi.single k 1) = _
  refine (SourceExpr.tm (k0 + k.val)).psi_sound momentData (sourcePair i).1 (sourcePair i).2
    J hJ hp hz momentData_check hg ht F k ?_ ?_ hS hH he
  · intro j
    rw [SourceExpr.tm_polys]
    change (gyMap p K k0 (Pi.single k 1)).coeff j =
      ((((X ^ 2 - 1) * U Int (k0 + k.val - 1) : Int[X]).coeff j : Int) : ZMod p)
    have hy : uyMap p K k0 (Pi.single k 1) = U (ZMod p) (k0 + k.val - 1) := by
      rw [uyMap_apply, Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb, Ne.symm hb]
      · simp
    rw [show gyMap p K k0 (Pi.single k 1) = (X ^ 2 - 1) * U (ZMod p) (k0 + k.val - 1) by
      simp only [gyMap, LinearMap.comp_apply, LinearMap.mulLeft_apply, hy]]
    have hm : map (Int.castRingHom (ZMod p)) ((X ^ 2 - 1) * U Int (k0 + k.val - 1)) =
        (X ^ 2 - 1) * U (ZMod p) (k0 + k.val - 1) := by simp [map_U]
    have he := congrArg (fun f : (ZMod p)[X] => f.coeff j) hm
    rw [Polynomial.coeff_map] at he
    exact he.symm
  · intro j
    rw [SourceExpr.tm_polys]
    change (tyMap p K k0 (Pi.single k 1)).coeff j =
      (((T Int (k0 + k.val)).coeff j : Int) : ZMod p)
    have ht' : tyMap p K k0 (Pi.single k 1) = T (ZMod p) (k0 + k.val) := by
      rw [tyMap_apply, Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb, Ne.symm hb]
      · simp
    rw [ht']
    have hm := map_T (Int.castRingHom (ZMod p)) (k0 + k.val)
    have he := congrArg (fun f : (ZMod p)[X] => f.coeff j) hm
    rw [Polynomial.coeff_map] at he
    exact he.symm

def thinNumeratorOn? {K : Nat} (k0 : Int) (z : Fin K → Int) (J : Nat) (S : Int) :
    List (Fin K) → Option Int
  | [] => some 0
  | k::ks => do
    let v ← sourceCoeff? (.tm (k0 + k.val)) J S
    let tail ← thinNumeratorOn? k0 z J S ks
    pure (z k * v + tail)

def thinNumerator? {K : Nat} (k0 : Int) (z : Fin K → Int) (J : Nat) (S : Int) : Option Int :=
  thinNumeratorOn? k0 z J S (List.finRange K)

theorem thinNumeratorOn_sound {K H J : Nat} (k0 : Int) (z : Fin K → Int) (S : Int)
    (hp : 44 < p) (hz : (momentData.scale : ZMod p) ≠ 0)
    (hS : S.toNat + 3 ≤ 41) (hH : S.toNat + 3 ≤ H) :
    ∀ (ks : List (Fin K)) (v : Int), thinNumeratorOn? k0 z J S ks = some v →
      (ks.map (fun k => (z k : ZMod p) * psiLin p K k0 H J S (Pi.single k 1))).sum =
        (v : ZMod p) / (sourceResponseScale : ZMod p) := by
  intro ks
  induction ks with
  | nil =>
    intro v h
    simp [thinNumeratorOn?] at h
    simp [← h]
  | cons k ks ih =>
    intro v hv
    cases h1 : sourceCoeff? (.tm (k0 + k.val)) J S with
    | none => simp [thinNumeratorOn?, h1] at hv
    | some x =>
      cases h2 : thinNumeratorOn? k0 z J S ks with
      | none => simp [thinNumeratorOn?, h1, h2] at hv
      | some y =>
        have he : z k * x + y = v := by simpa [thinNumeratorOn?, h1, h2] using hv
        simp only [List.map_cons, List.sum_cons]
        rw [thin_basis_coeff k0 k hp hz hS hH h1, ih y h2, ← he]
        push_cast
        ring

private theorem sum_finRange' {A : Type*} [AddCommMonoid A] (K : Nat) (f : Fin K → A) :
    ((List.finRange K).map f).sum = ∑ k, f k := by
  induction K with
  | zero => simp
  | succ K ih =>
    simp [List.finRange_succ, List.map_map, Fin.sum_univ_succ, ih, Function.comp_def]

theorem thinNumerator_sound {K H J : Nat} (k0 : Int) (z : Fin K → Int) {S v : Int}
    (hp : 44 < p) (hz : (momentData.scale : ZMod p) ≠ 0)
    (hS : S.toNat + 3 ≤ 41) (hH : S.toNat + 3 ≤ H)
    (hv : thinNumerator? k0 z J S = some v) :
    psiLin p K k0 H J S (fun k => (z k : ZMod p)) =
      (v : ZMod p) / (sourceResponseScale : ZMod p) := by
  classical
  have hvec : (fun k => (z k : ZMod p)) = ∑ k : Fin K, (z k : ZMod p) • Pi.single k 1 := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb, Ne.symm hb]
    · simp
  rw [hvec, map_sum]
  simp only [map_smul, smul_eq_mul]
  have h := thinNumeratorOn_sound (H := H) (J := J) k0 z S hp hz hS hH (List.finRange K) v hv
  simpa only [sum_finRange'] using h

def thinDifference? {K : Nat} (k0 : Int) (z : Fin K → Int) (J : Nat) (S : Int) : Option Int := do
  let a ← thinNumerator? k0 z J (S-1)
  let b ← thinNumerator? k0 z J S
  pure (a-b)

theorem thinDifference_sound {K H J : Nat} (k0 : Int) (z : Fin K → Int) {S v : Int}
    (hp : 44 < p) (hz : (momentData.scale : ZMod p) ≠ 0)
    (hS : S.toNat + 3 ≤ 41) (hS' : (S-1).toNat + 3 ≤ 41)
    (hH : S.toNat + 3 ≤ H) (hH' : (S-1).toNat + 3 ≤ H)
    (hv : thinDifference? k0 z J S = some v) :
    psiLin p K k0 H J (S-1) (fun k => (z k : ZMod p)) -
      psiLin p K k0 H J S (fun k => (z k : ZMod p)) =
      (v : ZMod p) / (sourceResponseScale : ZMod p) := by
  cases h1 : thinNumerator? k0 z J (S-1) with
  | none => simp [thinDifference?, h1] at hv
  | some a =>
    cases h2 : thinNumerator? k0 z J S with
    | none => simp [thinDifference?, h1, h2] at hv
    | some b =>
      have he : a-b=v := by simpa [thinDifference?, h1, h2] using hv
      rw [thinNumerator_sound k0 z hp hz hS' hH' h1, thinNumerator_sound k0 z hp hz hS hH h2, ← he]
      push_cast
      ring

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source

module

public import CatalanMeasure.GenD.Signed.RouteI.RowCert.DataP

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The opposite constant and the logarithms, sign P

kcost: 554 keys, seeds of about 100 products each.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.Davis.CircleCheb
open Set
open CatalanMeasure.GenD.Signed.RouteI

theorem kQbP : keyB GqP = true := by
  decide +kernel -- kcost: 277 comparisons
theorem lgQP : ((segEv GqP).all fun e => lgOK qLP e.1) = true := by
  decide +kernel -- kcost: 554 seeds
theorem kKeyP : ((segEv GqP).all fun e => decide ((e.1 : ℚ) / 10 ^ 12 ≤ 11)) = true := by
  decide +kernel -- kcost: 554 comparisons
theorem sumQP : (348423759397407209041 / 1180591620717411303424) ≤ ((segEv GqP).map fun e => e.2 * hxX qLP e).sum := by
  decide +kernel -- kcost: 554 seeds, rational sum
theorem wQP : ((segEv GqP).map fun e => |e.2|).sum ≤ 2069544 := by
  decide +kernel -- kcost: 554 rational additions
set_option exponentiation.threshold 2000 in
theorem hLqP : pint (GqP.map segR) (fun y => Real.log (YCell.physX y)) ≤ (-21776484962337950565 / 73786976294838206464) := by
  have hA : Atoms (GqP.map segR) ((segEv GqP).map atomR) := fun F => by
    rw [evS_segEv, evE_atomR]
  have hl : ∀ e ∈ segEv GqP, lgOK qLP e.1 = true := fun e he => by
    simpa using List.all_eq_true.1 lgQP e he
  have hK : ∀ e ∈ segEv GqP, (e.1 : ℚ) / 10 ^ 12 ≤ 11 := fun e he => by
    simpa using List.all_eq_true.1 kKeyP e he
  have hL : lgErr qLP ≤ (5729705329673784473 / 1532495540865888858358347027150309183618739122183602176) := by
    unfold lgErr
    norm_num [qLP]
  have hL0 : 0 ≤ lgErr qLP := by
    unfold lgErr
    norm_num [qLP]
  have key := opp_const hA (keyB_real kQbP) hl hK hL0 (by norm_num)
  have a1 : (((348423759397407209041 / 1180591620717411303424) : ℚ) : ℝ) ≤ (((segEv GqP).map fun e => e.2 * hxX qLP e).sum : ℚ) := by
    exact_mod_cast sumQP
  have a2 : ((((segEv GqP).map fun e => |e.2|).sum : ℚ) : ℝ) ≤ 2069544 := by exact_mod_cast wQP
  have a0 : (0 : ℝ) ≤ ((((segEv GqP).map fun e => |e.2|).sum : ℚ) : ℝ) := by
    exact_mod_cast List.sum_nonneg (by
      intro x hx
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact abs_nonneg _)
  have a3 : ((11 : ℚ) : ℝ) * lgErr qLP + 1 / (2 ^ qLP.kP * 10 ^ 12) ≤ 11 * (5729705329673784473 / 1532495540865888858358347027150309183618739122183602176) + 1 / (2 ^ 96 * 10 ^ 12) := by
    have : qLP.kP = 96 := rfl
    rw [this]
    push_cast
    linarith
  have a4 := mul_le_mul a2 a3 (by
    have : qLP.kP = 96 := rfl
    rw [this]
    push_cast
    have := hL0
    positivity) (by norm_num)
  refine key.trans ?_
  push_cast at a1 a4 ⊢
  norm_num at a1 a4 ⊢
  linarith
theorem ltEP : LTP = [(11 / 29, -((333478053761407113059987234146060318538 : ℚ) / (2 ^ 128 + 51)), -((6670895254112225679457018435638214825 : ℚ) / (2 ^ 128 + 51)))] := by
  decide +kernel -- kcost: one atom
theorem ltOKP : (((333478053761407113059987234146060318538 : ℚ) / (2 ^ 128 + 51)) ^ 2 + ((6670895254112225679457018435638214825 : ℚ) / (2 ^ 128 + 51)) ^ 2 < 1) ∧ rRe ((333478053761407113059987234146060318538 : ℚ) / (2 ^ 128 + 51), (6670895254112225679457018435638214825 : ℚ) / (2 ^ 128 + 51)) ≤ 1 := by
  decide +kernel -- kcost: two rational checks
theorem lfEP : LFP = [(3 / 29, (337646629504660563162822044569303556274 : ℚ) / (2 ^ 128 + 51), (2615478009853628089945605673425757934 : ℚ) / (2 ^ 128 + 51))] := by
  decide +kernel -- kcost: one atom
theorem lfOKP : (((337646629504660563162822044569303556274 : ℚ) / (2 ^ 128 + 51)) ^ 2 + ((2615478009853628089945605673425757934 : ℚ) / (2 ^ 128 + 51)) ^ 2 < 1) ∧ rRe ((337646629504660563162822044569303556274 : ℚ) / (2 ^ 128 + 51), (2615478009853628089945605673425757934 : ℚ) / (2 ^ 128 + 51)) ≤ 1 := by
  decide +kernel -- kcost: two rational checks
theorem hLogP : ∀ t ∈ Ioo (0 : ℝ) 1, (11 / 29 - (((0 : ℚ)) : ℝ)) * Real.log t + 3 / 29 * Real.log (1 - sgOf Sign.pos * t) ≤
    avQ false LFP t + avQ true LTP t := by
  intro t ht
  have a := log_t_atomC (c := 11 / 29) (q := ((333478053761407113059987234146060318538 : ℚ) / (2 ^ 128 + 51), (6670895254112225679457018435638214825 : ℚ) / (2 ^ 128 + 51))) (by norm_num) ltOKP.1 ltOKP.2 ht.1 ht.2.le
  have b := log_sub_atomC (c := 3 / 29) (q := ((337646629504660563162822044569303556274 : ℚ) / (2 ^ 128 + 51), (2615478009853628089945605673425757934 : ℚ) / (2 ^ 128 + 51))) (by norm_num) lfOKP.1 lfOKP.2 ht.1 ht.2
  rw [ltEP, lfEP]
  simp only [sgOf, one_mul, Rat.cast_zero, sub_zero]
  push_cast at a b ⊢
  linarith

end CatalanMeasure.GenD.Signed.RouteI.RowCert

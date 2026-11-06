module

public import CatalanMeasure.GenD.Signed.RouteI.RowCert.DataN

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The opposite constant and the logarithms, sign N

kcost: 854 keys, seeds of about 100 products each.
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

theorem kQbN : keyB GqN = true := by
  decide +kernel -- kcost: 427 comparisons
theorem lgQN : ((segEv GqN).all fun e => lgOK qLN e.1) = true := by
  decide +kernel -- kcost: 854 seeds
theorem kKeyN : ((segEv GqN).all fun e => decide ((e.1 : ℚ) / 10 ^ 12 ≤ 11)) = true := by
  decide +kernel -- kcost: 854 comparisons
theorem sumQN : (466825709793360587707 / 1180591620717411303424) ≤ ((segEv GqN).map fun e => e.2 * hxX qLN e).sum := by
  decide +kernel -- kcost: 854 seeds, rational sum
theorem wQN : ((segEv GqN).map fun e => |e.2|).sum ≤ 8175 := by
  decide +kernel -- kcost: 854 rational additions
set_option exponentiation.threshold 2000 in
theorem hLqN : pint (GqN.map segR) (fun y => Real.log (YCell.physX y)) ≤ (-233412854896680293853 / 590295810358705651712) := by
  have hA : Atoms (GqN.map segR) ((segEv GqN).map atomR) := fun F => by
    rw [evS_segEv, evE_atomR]
  have hl : ∀ e ∈ segEv GqN, lgOK qLN e.1 = true := fun e he => by
    simpa using List.all_eq_true.1 lgQN e he
  have hK : ∀ e ∈ segEv GqN, (e.1 : ℚ) / 10 ^ 12 ≤ 11 := fun e he => by
    simpa using List.all_eq_true.1 kKeyN e he
  have hL : lgErr qLN ≤ (67134999 / 1532495540865888858358347027150309183618739122183602176) := by
    unfold lgErr
    norm_num [qLN]
  have hL0 : 0 ≤ lgErr qLN := by
    unfold lgErr
    norm_num [qLN]
  have key := opp_const hA (keyB_real kQbN) hl hK hL0 (by norm_num)
  have a1 : (((466825709793360587707 / 1180591620717411303424) : ℚ) : ℝ) ≤ (((segEv GqN).map fun e => e.2 * hxX qLN e).sum : ℚ) := by
    exact_mod_cast sumQN
  have a2 : ((((segEv GqN).map fun e => |e.2|).sum : ℚ) : ℝ) ≤ 8175 := by exact_mod_cast wQN
  have a0 : (0 : ℝ) ≤ ((((segEv GqN).map fun e => |e.2|).sum : ℚ) : ℝ) := by
    exact_mod_cast List.sum_nonneg (by
      intro x hx
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact abs_nonneg _)
  have a3 : ((11 : ℚ) : ℝ) * lgErr qLN + 1 / (2 ^ qLN.kP * 10 ^ 12) ≤ 11 * (67134999 / 1532495540865888858358347027150309183618739122183602176) + 1 / (2 ^ 120 * 10 ^ 12) := by
    have : qLN.kP = 120 := rfl
    rw [this]
    push_cast
    linarith
  have a4 := mul_le_mul a2 a3 (by
    have : qLN.kP = 120 := rfl
    rw [this]
    push_cast
    have := hL0
    positivity) (by norm_num)
  refine key.trans ?_
  push_cast at a1 a4 ⊢
  norm_num at a1 a4 ⊢
  linarith
theorem ltEN : LTN = [(11 / 29, -((333478053761407113059987234146060318538 : ℚ) / (2 ^ 128 + 51)), -((6670895254112225679457018435638214825 : ℚ) / (2 ^ 128 + 51)))] := by
  decide +kernel -- kcost: one atom
theorem ltOKN : (((333478053761407113059987234146060318538 : ℚ) / (2 ^ 128 + 51)) ^ 2 + ((6670895254112225679457018435638214825 : ℚ) / (2 ^ 128 + 51)) ^ 2 < 1) ∧ rRe ((333478053761407113059987234146060318538 : ℚ) / (2 ^ 128 + 51), (6670895254112225679457018435638214825 : ℚ) / (2 ^ 128 + 51)) ≤ 1 := by
  decide +kernel -- kcost: two rational checks
theorem lfEN : LFN = [(3 / 29, (-58383224090797757041725353749760872438 : ℚ) / (2 ^ 128 + 51), 0)] := by
  decide +kernel -- kcost: one atom
theorem lfOKN : rQ ((-58383224090797757041725353749760872438 : ℚ) / (2 ^ 128 + 51)) ≤ -1 := by
  decide +kernel -- kcost: one rational check
theorem hLogN : ∀ t ∈ Ioc (0 : ℝ) 1, (11 / 29 - (((0 : ℚ)) : ℝ)) * Real.log t + 3 / 29 * Real.log (1 - sgOf Sign.neg * t) ≤
    avQ false LFN t + avQ true LTN t := by
  intro t ht
  have a := log_t_atomC (c := 11 / 29) (q := ((333478053761407113059987234146060318538 : ℚ) / (2 ^ 128 + 51), (6670895254112225679457018435638214825 : ℚ) / (2 ^ 128 + 51))) (by norm_num) ltOKN.1 ltOKN.2 ht.1 ht.2
  have b := log_add_atom (c := 3 / 29) (q := (-58383224090797757041725353749760872438 : ℚ) / (2 ^ 128 + 51)) (by norm_num) lfOKN ht.1
  rw [ltEN, lfEN]
  have e : (1 : ℝ) - sgOf Sign.neg * t = 1 + t := by simp [sgOf]
  rw [e]
  simp only [Rat.cast_zero, sub_zero]
  push_cast at a b ⊢
  linarith

end CatalanMeasure.GenD.Signed.RouteI.RowCert

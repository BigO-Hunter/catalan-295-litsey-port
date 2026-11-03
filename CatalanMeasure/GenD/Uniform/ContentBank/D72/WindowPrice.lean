module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.WindowTape
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
public import CatalanMeasure.GenD.Uniform.LedgerW.Growth
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic
noncomputable section

def WindowQ.toKapWindow (q : WindowQ) : KapWindow :=
  ⟨q.a, q.b, ⟨q.c0, q.c1, []⟩, ⟨144, 0, []⟩⟩

def windows72 (ws : List WindowQ) : List KapWindow := ws.map WindowQ.toKapWindow

theorem windows72_order {ws : List WindowQ} (h : windowTapeCheck 97 0 ws = true) :
    (∀ w ∈ windows72 ws, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ (P72.H 1 : ℝ)) ∧
    (windows72 ws).Pairwise (fun s t => s.b ≤ t.a) ∧
    (∀ w ∈ windows72 ws, w.b ≤ 1 ∨ 2 ≤ w.a) := by
  obtain ⟨hs, ht⟩ := windowTapeCheck_sound 97 ws 0 h
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
    obtain ⟨ha, hab, hb, _⟩ := (hs q hq).2
    change 0 < (q.a : ℝ) ∧ (q.a : ℝ) < q.b ∧ (q.b : ℝ) ≤ (P72.H 1 : ℝ)
    rw [p72_H]
    norm_num
    exact ⟨by exact_mod_cast ha, by exact_mod_cast hab, by exact_mod_cast hb⟩
  · exact ht.map _ (fun a b h => by
      change (a.b : ℝ) ≤ b.a
      exact_mod_cast h)
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
    change (q.b : ℝ) ≤ 1 ∨ 2 ≤ (q.a : ℝ)
    rcases (hs q hq).2.2.2.2 with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h

theorem windowQ_area72 (q : WindowQ) : q.toKapWindow.area 72 = (q.area : ℝ) := by
  simp [WindowQ.toKapWindow, KapWindow.area, PL.Prof.area, PL.hingeInt, WindowQ.area] <;>
    push_cast <;> ring

theorem windowQ_area_sum72 (ws : List WindowQ) :
    ((windows72 ws).map (KapWindow.area 72)).sum = (windowAreaQ ws : ℝ) := by
  induction ws with
  | nil => simp [windows72, windowAreaQ]
  | cons w ws ih =>
    change w.toKapWindow.area 72 + ((windows72 ws).map (KapWindow.area 72)).sum =
      ((w.area + windowAreaQ ws : Rat) : ℝ)
    rw [windowQ_area72, ih]
    push_cast <;> rfl

theorem window_price72 (ws : List WindowQ) :
    gD P72 f72 kappa072 (windows72 ws) =
      (1057 / 2 : ℝ) * Real.log 2 + (19129 / 2 - (windowAreaQ ws : ℝ)) := by
  have hH : (P72.H 1 : ℝ) = 97 := by rw [p72_H]; norm_num
  have ha : kappa072 + f72.area 1 97 = 19129 / 2 := by
    rw [← PL.Prof.integral_eval f72 (by norm_num : (1 : ℝ) ≤ 97)]
    exact odd_area72
  have h2 : TwoAdic.A2 (72 : ℝ) 97 11 = 1057 / 2 := by
    norm_num [TwoAdic.A2, CatalanMeasure.GenD.Uniform.Ledger.B2]
  unfold gD
  change TwoAdic.A2 (72 : ℝ) (P72.H 1 : ℝ) 11 * Real.log 2 +
    (kappa072 + f72.area 1 (P72.H 1 : ℝ)) -
      ((windows72 ws).map (KapWindow.area 72)).sum = _
  rw [hH, ha, h2, windowQ_area_sum72]
  ring

theorem full_window_price72 :
    gD P72 f72 kappa072 (windows72 fullWindowTape) =
      (1057 / 2 : ℝ) * Real.log 2 + (19129 / 2 - (fullLedgerQ : ℝ)) := by
  rw [window_price72, fullLedger_eq]

theorem fallback_window_price72 :
    gD P72 f72 kappa072 (windows72 fallbackWindowTape) =
      (1057 / 2 : ℝ) * Real.log 2 + (19129 / 2 - (fallbackLedgerQ : ℝ)) := by
  rw [window_price72, fallbackLedger_eq]

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72

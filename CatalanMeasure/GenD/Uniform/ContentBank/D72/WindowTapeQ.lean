module
public import CatalanMeasure.GenD.PL
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72

structure WindowQ where
  a : Rat
  b : Rat
  c0 : Rat
  c1 : Rat

def WindowQ.area (w : WindowQ) : Rat :=
  w.c0 * (w.b - w.a) + w.c1 * ((w.b ^ 2 - w.a ^ 2) / 2)

def windowAreaQ (ws : List WindowQ) : Rat := (ws.map WindowQ.area).sum

def WindowQ.valid (cut : Rat) (w : WindowQ) : Prop :=
  0 < w.a ∧ w.a < w.b ∧ w.b ≤ cut ∧ (w.b ≤ 1 ∨ 2 ≤ w.a)

def windowTapeCheck (cut : Rat) : Rat → List WindowQ → Bool
  | _, [] => true
  | floor, w::ws =>
    decide (floor ≤ w.a ∧ 0 < w.a ∧ w.a < w.b ∧ w.b ≤ cut ∧ (w.b ≤ 1 ∨ 2 ≤ w.a)) &&
      windowTapeCheck cut w.b ws

theorem windowTapeCheck_sound (cut : Rat) :
    ∀ (ws : List WindowQ) (floor : Rat), windowTapeCheck cut floor ws = true →
      (∀ w ∈ ws, floor ≤ w.a ∧ w.valid cut) ∧
      ws.Pairwise (fun s t => s.b ≤ t.a) := by
  intro ws
  induction ws with
  | nil => simp
  | cons w ws ih =>
    intro floor h
    simp only [windowTapeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hall, hord⟩ := ih w.b h.2
    refine ⟨?_, List.Pairwise.cons (fun u hu => (hall u hu).1) hord⟩
    intro u hu
    rcases List.mem_cons.mp hu with hwu | hu'
    · subst u
      exact h.1
    · exact ⟨(h.1.1.trans h.1.2.2.1.le).trans (hall u hu').1, (hall u hu').2⟩

end CatalanMeasure.GenD.Uniform.ContentBank.D72

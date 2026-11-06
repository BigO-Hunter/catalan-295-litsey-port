module
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceLookup
@[expose] public section
set_option Elab.async false
/-! Small source expressions share checked signed U lookups. -/
namespace CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD OAI.InternalCatalan
noncomputable section
variable {p : Nat} [Fact p.Prime]

inductive SourceExpr where
  | zero
  | g (k : Int)
  | t (k : Int)
  | add (a b : SourceExpr)
  | sub (a b : SourceExpr)
  | shift (a : SourceExpr)

def SourceExpr.eval? (g t : IntSourceTree) (H : Nat) : SourceExpr → Int → Option Int
  | .zero, _ => some 0
  | .g k, S => g.signed? H k S
  | .t k, S => t.signed? H k S
  | .add a b, S => (a.eval? g t H S).bind fun x => (b.eval? g t H S).map (x + ·)
  | .sub a b, S => (a.eval? g t H S).bind fun x => (b.eval? g t H S).map (x - ·)
  | .shift a, S => a.eval? g t H (S - 1)

def SourceExpr.eval (G T : Int → Int → Rat) : SourceExpr → Int → Rat
  | .zero, _ => 0
  | .g k, S => G k S
  | .t k, S => T k S
  | .add a b, S => a.eval G T S + b.eval G T S
  | .sub a b, S => a.eval G T S - b.eval G T S
  | .shift a, S => a.eval G T (S - 1)

theorem SourceExpr.eval?_sound (g t : IntSourceTree) (H : Nat) (scale : Int)
    (G T : Int → Int → Rat)
    (hg : ∀ k S v, g.signed? H k S = some v → ResRec.Gd p (G k S)
      ((v : ZMod p) / (scale : ZMod p)))
    (ht : ∀ k S v, t.signed? H k S = some v → ResRec.Gd p (T k S)
      ((v : ZMod p) / (scale : ZMod p))) (a : SourceExpr) :
    ∀ S v, a.eval? g t H S = some v → ResRec.Gd p (a.eval G T S)
      ((v : ZMod p) / (scale : ZMod p)) := by
  induction a with
  | zero =>
    intro S v hv
    have h : (0 : Int) = v := Option.some.inj hv
    rw [← h]
    simpa [SourceExpr.eval] using (ResRec.Gd.nat (p := p) 0)
  | g k => exact hg k
  | t k => exact ht k
  | shift a ih => exact fun S v => ih (S - 1) v
  | add a b iha ihb =>
    intro S v hv
    change (a.eval? g t H S).bind (fun x => (b.eval? g t H S).map (x + ·)) = some v at hv
    cases ha : a.eval? g t H S with
    | none => simp [ha] at hv
    | some x =>
      cases hb : b.eval? g t H S with
      | none => simp [ha, hb] at hv
      | some y =>
        have he : x + y = v := by simpa [ha, hb] using hv
        rw [← he]
        simpa [SourceExpr.eval, Int.cast_add, add_div] using
          ResRec.Gd.add (iha S x ha) (ihb S y hb)
  | sub a b iha ihb =>
    intro S v hv
    change (a.eval? g t H S).bind (fun x => (b.eval? g t H S).map (x - ·)) = some v at hv
    cases ha : a.eval? g t H S with
    | none => simp [ha] at hv
    | some x =>
      cases hb : b.eval? g t H S with
      | none => simp [ha, hb] at hv
      | some y =>
        have he : x - y = v := by simpa [ha, hb] using hv
        rw [← he]
        simpa [SourceExpr.eval, Int.cast_sub, sub_div] using
          ResRec.Gd.sub (iha S x ha) (ihb S y hb)

end
end CatalanMeasure.GenD.Uniform.W.Charts6

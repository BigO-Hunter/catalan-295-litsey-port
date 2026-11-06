module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.ResponseRow
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostLowGraph
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.W.Charts6 CatalanMeasure.GenD.Uniform.W.Prof
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff Cert)
noncomputable section
variable {N p : Nat} [Fact p.Prime]

theorem unitTarget_coord {n : Nat} (s c : Fin n) :
    ((unitTarget s).getD c.val 0 : ZMod p) = (Pi.single c (1 : ZMod p) : Fin n → ZMod p) s := by
  simp [unitTarget, List.getD_eq_getElem?_getD, c.isLt, Pi.single_apply, eq_comm]

theorem unit_component_kill {pk : Packet} {l : JetLayout pk} {win : List Aff} {cs : Cert}
    (c : ResponseComponent pk) (s : Fin pk.n)
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f) (hodd : p % 2 = 1)
    (hoff : ∀ g, 0 ≤ affAt N p (l.offset g)) (hw : ∀ g, 0 ≤ affAt N p (l.width g))
    (hc : c.check l win cs (unitTarget s) = true)
    (hs : ∀ z ∈ c.zones, ¬ (p : Int) ∣ z.span.scale)
    (e : Fin p) (hlo : affAt N p c.lo ≤ (e.val : Int)) (hhi : (e.val : Int) < affAt N p c.hi)
    (x : Fin p → Fin pk.d → ZMod p)
    (hx : ∀ g (k : Fin (l.count N p g)),
      chartMap pk (pk.chart g) p pk.n (l.jet N p g k.val x) = 0) :
    emb pk p pk.n (x e) s = 0 :=
  ResponseComponent.eval_zero (c := c) hwin hodd hoff hw hc hs e hlo hhi (LinearMap.proj s) 1 one_ne_zero
    (fun i => by simpa only [LinearMap.proj_apply, one_mul] using unitTarget_coord (p := p) s i) x hx

theorem native_response_component_kill {pk : Packet} {l : JetLayout pk}
    {win : List Aff} {cs : Cert} {b ex K H : Nat} (hK : K = b * 4 + 2 + ex)
    (k0 : Int) (ah aq : Nat) (slots : Fin pk.n → Option (Fin K))
    (J : Nat) (S : Int) (low : Fin pk.n) (slack : Option (Fin pk.n))
    (c : ResponseComponent pk) (target : List Int)
    (hp : 44 < p) (hz : (momentData.scale : ZMod p) ≠ 0) (hp2 : p ≠ 2)
    (hS : S.toNat + 3 ≤ 41) (hH : S.toNat + 3 ≤ H)
    (hc0 : foldedTargetCheck hK k0 ah aq slots J S low slack target = true)
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f) (hodd : p % 2 = 1)
    (hoff : ∀ g, 0 ≤ affAt N p (l.offset g)) (hw : ∀ g, 0 ≤ affAt N p (l.width g))
    (hc : c.check l win cs target = true)
    (hs : ∀ z ∈ c.zones, ¬ (p : Int) ∣ z.span.scale)
    (e : Fin p) (hlo : affAt N p c.lo ≤ (e.val : Int)) (hhi : (e.val : Int) < affAt N p c.hi)
    (x : Fin p → Fin pk.d → ZMod p)
    (hx : ∀ g (k : Fin (l.count N p g)),
      chartMap pk (pk.chart g) p pk.n (l.jet N p g k.val x) = 0) :
    foldedResponseLinear hK k0 ah aq slots H J S low slack (emb pk p pk.n (x e)) = 0 :=
  ResponseComponent.eval_zero (c := c) hwin hodd hoff hw hc hs e hlo hhi
    (foldedResponseLinear hK k0 ah aq slots H J S low slack)
    (sourceResponseScale : ZMod p) (sourceResponseScale_ne_zero hp hz)
    (foldedTargetCheck_sound hK k0 ah aq slots J S low slack target hp hz hp2 hS hH hc0) x hx

theorem foldedResponse_no_slack {n b ex K : Nat} (hK : K = b * 4 + 2 + ex)
    (k0 : Int) (ah aq : Nat) (slots : Fin n → Option (Fin K))
    (H J : Nat) (S : Int) (low : Fin n) (slack : Option (Fin n)) (y : Fin n → ZMod p)
    (h : foldedResponseLinear hK k0 ah aq slots H J S low slack y = 0)
    (hs : ∀ c, slack = some c → y c = 0) :
    foldedResponseLinear hK k0 ah aq slots H J S low none y = 0 := by
  cases slack with
  | none => exact h
  | some c =>
    simpa [foldedResponseLinear, optionalProjection, hs c rfl] using h

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source

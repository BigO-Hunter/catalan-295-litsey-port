module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.GraphInj
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.HostRows
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Charts3
open CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff Cert)
noncomputable section
variable {P : Parameters} {N p : Nat} [Fact p.Prime]

theorem folded_native_eq_label {pk : Packet} {b ex K : Nat} (M : MonoData P N p K)
    (hK : K = b * 4 + 2 + ex) (k0 : Int) (ah aq : Nat)
    (slots : Fin pk.n → Option (Fin K)) (J : Nat) (S : Int) (low : Fin pk.n)
    (hp : M.prof = responseProf hK k0 ah) :
    foldedResponseLinear hK k0 ah aq slots (P.H N) J S low none =
      ambientLabelResponse M (sparseSourceIns slots) aq J S - LinearMap.proj low := by
  simp [foldedResponseLinear, ambientLabelResponse, optionalProjection, hp]

theorem checked_native_hG {pk : Packet} (l : JetLayout pk) {win : List Aff} {cs : Cert}
    (low : Fin pk.n) (r : Nat) (req : Aff)
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hoff : ∀ g, 0 ≤ affAt N p (l.offset g)) (hw : ∀ g, 0 ≤ affAt N p (l.width g))
    (hr : r ≤ p) (hrq : ((p - r : Nat) : Int) ≤ affAt N p req)
    (zs : List (ResponseZone pk)) (hc : lowPrefixCheck l win cs req low zs = true)
    (hs : ∀ z ∈ zs, ¬ (p : Int) ∣ z.span.scale)
    (x : Fin p → Fin pk.d → ZMod p)
    (hx : ∀ g (k : Fin (l.count N p g)),
      chartMap pk (pk.chart g) p pk.n (l.jet N p g k.val x) = 0) :
    ∃ G : Polynomial (ZMod p), G.degree < (r : WithBot Nat) ∧
      ∀ e : Fin p, G.eval (((P.H N : Int) - 1 - e : Int) : ZMod p) = emb pk p pk.n (x e) low := by
  obtain ⟨G, hd, he⟩ := hG_of_checked_prefix l low r req
    ((((P.H N : Int) - 1 : Int) : ZMod p)) hwin hoff hw hr hrq zs hc hs x hx
  refine ⟨G, hd, fun e => ?_⟩
  simpa only [Int.cast_sub, Int.cast_natCast] using he e

/-- Assemble the actual host identification once the checked domain, cover
and slack equations have been transported at the physical point. -/
def nativeHostIdent {pk : Packet} {K : Nat} (M : MonoData P N p K)
    (slots : Fin pk.n → Option (Fin K)) (hs : SlotsInjective slots) (low : Fin pk.n)
    (hSound : pk.Sound) (hδ : ¬ (p : Int) ∣ pk.delta)
    (l : JetLayout pk) (a r cm : Nat) (hcm : cm ≤ p)
    (hwide : P.b N + (a + 2) * p ≤ P.L N)
    (hdom : ∀ x : Fin p → Fin pk.d → ZMod p,
      (∀ e : Fin p, cm ≤ e.val → x e = 0) →
      (∀ g (j : Fin (l.count N p g)), chartMap pk (pk.chart g) p pk.n (l.jet N p g j.val x) = 0) →
      (fun e => sparseSourceIns slots (emb pk p pk.n (x e))) ∈ M.dom)
    (hG : ∀ x : Fin p → Fin pk.d → ZMod p,
      (∀ g (j : Fin (l.count N p g)), chartMap pk (pk.chart g) p pk.n (l.jet N p g j.val x) = 0) →
      ∃ G : Polynomial (ZMod p), G.degree < (r : WithBot Nat) ∧
        ∀ e : Fin p, G.eval (((P.H N : Int) - 1 - e : Int) : ZMod p) = emb pk p pk.n (x e) low)
    (hcov : CoverKernel pk M (sparseSourceIns slots) ((LinearMap.proj low).comp (emb pk p pk.n))
      (l.count N p) a cm (fun g j => l.jet N p g j.val))
    (hSlack : ∀ x : Fin p → Fin pk.d → ZMod p,
      (∀ g (j : Fin (l.count N p g)), chartMap pk (pk.chart g) p pk.n (l.jet N p g j.val x) = 0) →
      (∀ e, sparseSourceIns slots (emb pk p pk.n (x e)) = 0) →
      ∀ e : Fin p, e.val < cm → ∀ c : Fin pk.n, slots c = none → c ≠ low →
        emb pk p pk.n (x e) low = 0 → emb pk p pk.n (x e) c = 0) :
    HostIdent M.sys pk cm (l.count N p) a r :=
  monoHostKernel M (sparseSourceIns slots) (sparseSourceIns slots) (fun _ => rfl) (fun _ => rfl)
    ((LinearMap.proj low).comp (emb pk p pk.n)) a r cm (fun g j => l.jet N p g j.val)
    (fun x hout hx hn => native_graph_injective M slots hs low hSound hδ
      (fun g j => l.jet N p g j.val) hwide hcov x hx hout hn (hSlack x hx hn))
    hdom (fun x _ hx => hG x hx) hcm hcov

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source

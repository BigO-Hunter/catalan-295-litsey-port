module
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostResponseCover
public import CatalanMeasure.GenD.Uniform.W.Charts3.GraphJets
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts6
open Polynomial CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Charts3
open Check (Aff Cert holds holds_sound)
noncomputable section
variable {N p : Nat} [Fact p.Prime]

def unitTarget {n : Nat} (c : Fin n) : List Int :=
  List.ofFn fun i => if i = c then 1 else 0

def lowPrefixCheck {pk : Packet} (l : JetLayout pk) (win : List Aff) (cs : Cert)
    (r : Aff) (c : Fin pk.n) (zs : List (ResponseZone pk)) : Bool :=
  responseChain win cs r ⟨0, 0, 0⟩ zs &&
    zs.all fun z => z.span.check (unitTarget c) &&
      (List.finRange z.span.terms.length).all fun i =>
        let g := (z.span.terms.get i).group
        decide (l.point g = .plus) &&
        holds win cs (z.lo.sub (l.offset g)) &&
        holds win cs (((l.offset g).add (l.width g)).sub z.hi)

theorem hG_of_checked_prefix {pk : Packet} (l : JetLayout pk) {win : List Aff} {cs : Cert}
    (c : Fin pk.n) (r : Nat) (req : Aff) (η : ZMod p)
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hoff : ∀ g, 0 ≤ affAt N p (l.offset g)) (hw : ∀ g, 0 ≤ affAt N p (l.width g))
    (hr : r ≤ p) (hrq : ((p - r : Nat) : Int) ≤ affAt N p req)
    (zs : List (ResponseZone pk)) (hc : lowPrefixCheck l win cs req c zs = true)
    (hs : ∀ z ∈ zs, ¬ (p : Int) ∣ z.span.scale)
    (x : Fin p → Fin pk.d → ZMod p)
    (hx : ∀ g (k : Fin (l.count N p g)),
      chartMap pk (pk.chart g) p pk.n (l.jet N p g k.val x) = 0) :
    ∃ G : (ZMod p)[X], G.degree < (r : WithBot Nat) ∧
      ∀ e : Fin p, G.eval (η - (e.val : ZMod p)) = emb pk p pk.n (x e) c := by
  let low : (Fin pk.d → ZMod p) →ₗ[ZMod p] ZMod p :=
    (LinearMap.proj c).comp (emb pk p pk.n)
  apply hG_of_taylor low η r hr x
  intro k hk
  simp only [lowPrefixCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  have hk0 : affAt N p (⟨0, 0, 0⟩ : Aff) ≤ (k : Int) := by simp [affAt, Aff.eval]
  have hk1 : (k : Int) < affAt N p req := lt_of_lt_of_le (by exact_mod_cast hk) hrq
  obtain ⟨z, hzm, hz0, hz1⟩ := response_chain_select hwin zs _ hc.1 k hk0 hk1
  obtain ⟨hz, hzall⟩ := hc.2 z hzm
  let y := Charts3.taylorJet (1 : ZMod p) k x
  refine RowSpanData.eval_zero hz (hs z hzm) 1 one_ne_zero (LinearMap.proj c) (fun i => ?_) y ?_
  ·
    simp [unitTarget, List.getD_eq_getElem?_getD, i.isLt, Pi.single_apply, eq_comm]
  · intro i
    let g := (z.span.terms.get i).group
    obtain ⟨⟨hp, h0⟩, h1⟩ := hzall i (by simp)
    have h0' := holds_sound win cs _ N (halfPrime p) hwin h0
    have h1' := holds_sound win cs _ N (halfPrime p) hwin h1
    simp only [Check.Aff.eval_sub, Check.Aff.eval_add] at h0' h1'
    change 0 ≤ affAt N p z.lo - affAt N p (l.offset g) at h0'
    change 0 ≤ affAt N p (l.offset g) + affAt N p (l.width g) - affAt N p z.hi at h1'
    have ho : (l.start N p g : Int) = affAt N p (l.offset g) := Int.toNat_of_nonneg (hoff g)
    have hw' : (l.count N p g : Int) = affAt N p (l.width g) := Int.toNat_of_nonneg (hw g)
    let j := k - l.start N p g
    have hj : j < l.count N p g := by dsimp [j]; omega
    have hsum : l.start N p g + j = k := by dsimp [j]; omega
    have hy := hx g ⟨j,hj⟩
    change l.point g = PhysicalPoint.plus at hp
    change chartMap pk (pk.chart g) p pk.n y = 0
    simpa [JetLayout.jet, hp, hsum, y] using hy

end
end CatalanMeasure.GenD.Uniform.W.Charts6

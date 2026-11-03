module
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostResponseCover
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Charts4
open Check (Aff Cert holds holds_sound)
noncomputable section
variable {N p : Nat} [Fact p.Prime]

def physicalJet {d : Nat} (point : PhysicalPoint) (j : Nat) :
    (Fin p → Fin d → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p) :=
  match point with
  | .zero => jet0 j
  | .infinity => jetInf j
  | .plus => Charts3.taylorJet 1 j
  | .minus => Charts3.taylorJet (-1) j

theorem jetLayout_eq {pk : Packet} (l : JetLayout pk) (g : Fin pk.charts.length) (j : Nat) :
    l.jet N p g j = physicalJet (l.point g) (l.start N p g + j) := by rfl

def jetPrefixCheck {pk : Packet} (l : JetLayout pk) (win : List Aff) (cs : Cert)
    (point : PhysicalPoint) (order : Aff) (target : List Int) (zs : List (ResponseZone pk)) : Bool :=
  responseChain win cs order ⟨0, 0, 0⟩ zs &&
    zs.all fun z => z.span.check target &&
      (List.finRange z.span.terms.length).all fun i =>
        let g := (z.span.terms.get i).group
        decide (l.point g = point) &&
        holds win cs (z.lo.sub (l.offset g)) &&
        holds win cs (((l.offset g).add (l.width g)).sub z.hi)

theorem jetPrefixCheck_kill {pk : Packet} {l : JetLayout pk} {win : List Aff} {cs : Cert}
    (point : PhysicalPoint) (order : Aff) (target : List Int) (zs : List (ResponseZone pk))
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hoff : ∀ g, 0 ≤ affAt N p (l.offset g)) (hw : ∀ g, 0 ≤ affAt N p (l.width g))
    (hc : jetPrefixCheck l win cs point order target zs = true)
    (hs : ∀ z ∈ zs, ¬ (p : Int) ∣ z.span.scale)
    (F : (Fin pk.n → ZMod p) →ₗ[ZMod p] ZMod p) (clear : ZMod p) (hu : clear ≠ 0)
    (hF : ∀ i : Fin pk.n, (target.getD i.val 0 : ZMod p) = clear * F (Pi.single i 1))
    (x : Fin p → Fin pk.d → ZMod p)
    (hx : ∀ g (k : Fin (l.count N p g)),
      chartMap pk (pk.chart g) p pk.n (l.jet N p g k.val x) = 0)
    (k : Nat) (hk : (k : Int) < affAt N p order) :
    F (emb pk p pk.n (physicalJet point k x)) = 0 := by
  simp only [jetPrefixCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  have hk0 : affAt N p (⟨0, 0, 0⟩ : Aff) ≤ (k : Int) := by simp [affAt, Aff.eval]
  obtain ⟨z, hzm, hz0, hz1⟩ := response_chain_select hwin zs _ hc.1 k hk0 hk
  obtain ⟨hz, hzall⟩ := hc.2 z hzm
  apply RowSpanData.eval_zero hz (hs z hzm) clear hu F hF
  intro i
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
  change l.point g = point at hp
  change chartMap pk (pk.chart g) p pk.n (physicalJet point k x) = 0
  simpa [jetLayout_eq, hp, hsum] using hy

end
end CatalanMeasure.GenD.Uniform.W.Charts6

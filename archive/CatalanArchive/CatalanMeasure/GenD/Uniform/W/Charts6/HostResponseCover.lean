module
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostResponseZones
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts6
open Finset CatalanMeasure.Parametric CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Charts3
open Check (Aff Cert)
noncomputable section
variable {P : Parameters} {N p : Nat} [Fact p.Prime]

/-- One component of a response is checked against each of its actual active
jet groups. A target is an argument evaluated by the source compiler. -/
structure ResponseComponent (pk : Packet) where
  lo : Aff
  hi : Aff
  zones : List (ResponseZone pk)

def ResponseComponent.check {pk : Packet} (c : ResponseComponent pk) (l : JetLayout pk)
    (win : List Aff) (cs : Cert) (target : List Int) : Bool :=
  responseChain win cs c.hi c.lo c.zones &&
    c.zones.all (fun z => z.check l win cs target)

theorem ResponseComponent.eval_zero {pk : Packet} {c : ResponseComponent pk} {l : JetLayout pk}
    {win : List Aff} {cs : Cert} {target : List Int}
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f) (hodd : p % 2 = 1)
    (hoff : ∀ g, 0 ≤ affAt N p (l.offset g)) (hw : ∀ g, 0 ≤ affAt N p (l.width g))
    (hc : c.check l win cs target = true)
    (hs : ∀ z ∈ c.zones, ¬ (p : Int) ∣ z.span.scale)
    (e : Fin p) (hlo : affAt N p c.lo ≤ (e.val : Int)) (hhi : (e.val : Int) < affAt N p c.hi)
    (F : (Fin pk.n → ZMod p) →ₗ[ZMod p] ZMod p) (clear : ZMod p) (hu : clear ≠ 0)
    (hF : ∀ i : Fin pk.n, (target.getD i.val 0 : ZMod p) = clear * F (Pi.single i 1))
    (x : Fin p → Fin pk.d → ZMod p)
    (hx : ∀ g (k : Fin (l.count N p g)),
      chartMap pk (pk.chart g) p pk.n (l.jet N p g k.val x) = 0) :
    F (emb pk p pk.n (x e)) = 0 := by
  simp only [ResponseComponent.check, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨z, hzm, hzlo, hzhi⟩ := response_chain_select hwin c.zones c.lo hc.1 e.val hlo hhi
  obtain ⟨hz, hzker⟩ := response_zone_active hwin hodd hoff hw (hc.2 z hzm) e hzlo hzhi
  exact RowSpanData.eval_zero hz (hs z hzm) clear hu F hF (x e) (hzker x hx)

theorem response_quotient_range {b L a j J0 J1 : Nat}
    (hp : 0 < p) (hb : b ≤ j) (hL : j + a * p < L)
    (h0 : J0 * p ≤ b) (h1 : L ≤ (J1 + a + 1) * p) :
    J0 ≤ j / p ∧ j / p ≤ J1 := by
  constructor
  · exact (Nat.le_div_iff_mul_le hp).2 (h0.trans hb)
  · apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hp).2
    change j < (J1 + 1) * p
    rw [Nat.add_mul, Nat.add_mul] at h1
    rw [Nat.add_mul, Nat.one_mul]
    omega

def ambientLabelResponse {pk : Packet} {K : Nat} (M : MonoData P N p K)
    (ins : (Fin pk.n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p))
    (a J : Nat) (S : Int) : (Fin pk.n → ZMod p) →ₗ[ZMod p] ZMod p :=
  ∑ v ∈ range (a + 1), ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) •
    ((M.sys.prof.psi (P.H N) (J + v) S).comp ins)

/-- Only the two feasible S labels and the bounded J table are required.
The source identity may be split into independently activated components. -/
theorem coverKernel_of_response_labels (pk : Packet) {K : Nat} (M : MonoData P N p K)
    (ins : (Fin pk.n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p))
    (low : (Fin pk.n → ZMod p) →ₗ[ZMod p] ZMod p)
    (l : JetLayout pk) (a cm J0 J1 : Nat) (S0 : Int)
    (h0 : J0 * p ≤ P.b N) (h1 : P.L N ≤ (J1 + a + 1) * p)
    (hs0 : S0 * p ≤ (P.H N : Int) - 1) (hs1 : (P.H N : Int) - 1 < (S0 + 1) * p)
    (hlabel : ∀ J, J0 ≤ J → J ≤ J1 → ∀ S : Int, (S = S0 ∨ S = S0 - 1) →
      ∀ e : Fin p,
      responseLo (P.H N) (P.L N) p a J S ≤ (e.val : Int) →
      (e.val : Int) < responseHi (P.H N) (P.b N) p cm J S →
      ∀ x : Fin p → Fin pk.d → ZMod p,
      (∀ g (k : Fin (l.count N p g)),
        chartMap pk (pk.chart g) p pk.n (l.jet N p g k.val x) = 0) →
      (ambientLabelResponse M ins a J S - low) (emb pk p pk.n (x e)) = 0) :
    CoverKernel pk M ins (low.comp (emb pk p pk.n)) (l.count N p) a cm
      (fun g k => l.jet N p g k.val) := by
  intro j hj hL e he hd x hx
  have hp : 0 < p := Nat.Prime.pos (Fact.out : p.Prime)
  obtain ⟨hJ0,hJ1⟩ := response_quotient_range hp hj hL h0 h1
  have hS := response_label_cases hp e.isLt hs0 hs1 hd
  obtain ⟨hlo,hhi⟩ := response_in_exact_interval hp hj hL e.isLt he hd
  have h := hlabel _ hJ0 hJ1 _ hS e hlo hhi x hx
  have heq := sub_eq_zero.mp (show ambientLabelResponse M ins a (j / p)
      (((P.H N : Int) - 1 - ((j % p : Nat) : Int) - e) / p) (emb pk p pk.n (x e)) -
      low (emb pk p pk.n (x e)) = 0 from h)
  simpa [ambientLabelResponse, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using heq

end
end CatalanMeasure.GenD.Uniform.W.Charts6

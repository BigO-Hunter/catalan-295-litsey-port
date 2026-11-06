module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.DomainTransport
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open Polynomial CatalanMeasure.GenD.Uniform.W.Prof
open CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff Cert)
noncomputable section

structure NativeDomainCtx {N p K : Nat} [Fact p.Prime] {pk : Packet}
    (l : JetLayout pk) (win : List Aff) (cs : Cert) (slots : Fin pk.n → Option (Fin K))
    (x : Fin p → Fin pk.d → ZMod p) : Prop where
  win_ok : ∀ f ∈ win, 0 ≤ affAt N p f
  offset_ok : ∀ g, 0 ≤ affAt N p (l.offset g)
  width_ok : ∀ g, 0 ≤ affAt N p (l.width g)
  kernel_ok : ∀ g (k : Fin (l.count N p g)),
    chartMap pk (pk.chart g) p pk.n (l.jet N p g k.val x) = 0

variable {N p K : Nat} [Fact p.Prime] {pk : Packet} {l : JetLayout pk}
  {win : List Aff} {cs : Cert} {slots : Fin pk.n → Option (Fin K)}
  {x : Fin p → Fin pk.d → ZMod p}

theorem NativeDomainCtx.prefix
    (C : NativeDomainCtx (N := N) l win cs slots x)
    (terms : List (Fin K × Int)) (point : PhysicalPoint) (order : Aff)
    (zs : List (ResponseZone pk))
    (hc : jetPrefixCheck l win cs point order (nativeDomainTarget slots terms) zs = true)
    (hs : ∀ z ∈ zs, ¬ (p : Int) ∣ z.span.scale)
    (j : Nat) (hj : (j : Int) < affAt N p order) :
    slotLinear terms (((sparseSourceIns slots).comp (emb pk p pk.n))
      (physicalJet point j x)) = 0 :=
  native_domain_prefix_zero slots terms point order zs C.win_ok C.offset_ok C.width_ok
    hc hs x C.kernel_ok j hj

theorem NativeDomainCtx.plus
    (C : NativeDomainCtx (N := N) l win cs slots x)
    (terms : List (Fin K × Int)) (order : Aff) (zs : List (ResponseZone pk))
    (hc : jetPrefixCheck l win cs .plus order (nativeDomainTarget slots terms) zs = true)
    (hs : ∀ z ∈ zs, ¬ (p : Int) ∣ z.span.scale)
    (j : Nat) (hj : (j : Int) < affAt N p order) :
    (taylor 1 (slotPolynomial (fun e => sparseSourceIns slots (emb pk p pk.n (x e))) terms)).coeff j = 0 :=
  slotPolynomial_taylor_zero ((sparseSourceIns slots).comp (emb pk p pk.n)) x terms 1 j
    (C.prefix terms .plus order zs hc hs j hj)

theorem NativeDomainCtx.minus
    (C : NativeDomainCtx (N := N) l win cs slots x)
    (terms : List (Fin K × Int)) (order : Aff) (zs : List (ResponseZone pk))
    (hc : jetPrefixCheck l win cs .minus order (nativeDomainTarget slots terms) zs = true)
    (hs : ∀ z ∈ zs, ¬ (p : Int) ∣ z.span.scale)
    (j : Nat) (hj : (j : Int) < affAt N p order) :
    (taylor (-1) (slotPolynomial (fun e => sparseSourceIns slots (emb pk p pk.n (x e))) terms)).coeff j = 0 :=
  slotPolynomial_taylor_zero ((sparseSourceIns slots).comp (emb pk p pk.n)) x terms (-1) j
    (C.prefix terms .minus order zs hc hs j hj)

theorem NativeDomainCtx.tail
    (C : NativeDomainCtx (N := N) l win cs slots x)
    (terms : List (Fin K × Int)) (order : Aff) (zs : List (ResponseZone pk))
    (hc : jetPrefixCheck l win cs .infinity order (nativeDomainTarget slots terms) zs = true)
    (hs : ∀ z ∈ zs, ¬ (p : Int) ∣ z.span.scale)
    (r : Nat) (hr : ((p-r : Nat) : Int) ≤ affAt N p order) :
    ∀ i, r ≤ i →
      (slotPolynomial (fun e => sparseSourceIns slots (emb pk p pk.n (x e))) terms).coeff i = 0 :=
  slotPolynomial_tail_zero ((sparseSourceIns slots).comp (emb pk p pk.n)) x terms r
    (fun j hj => C.prefix terms .infinity order zs hc hs j
      (lt_of_lt_of_le (by exact_mod_cast hj) hr))

theorem NativeDomainCtx.zero
    (C : NativeDomainCtx (N := N) l win cs slots x)
    (terms : List (Fin K × Int)) (order : Aff) (zs : List (ResponseZone pk))
    (hc : jetPrefixCheck l win cs .zero order (nativeDomainTarget slots terms) zs = true)
    (hs : ∀ z ∈ zs, ¬ (p : Int) ∣ z.span.scale)
    (hr : (p : Int) ≤ affAt N p order) :
    slotPolynomial (fun e => sparseSourceIns slots (emb pk p pk.n (x e))) terms = 0 :=
  slotPolynomial_zero ((sparseSourceIns slots).comp (emb pk p pk.n)) x terms
    (fun j hj => C.prefix terms .zero order zs hc hs j
      (lt_of_lt_of_le (by exact_mod_cast hj) hr))

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source

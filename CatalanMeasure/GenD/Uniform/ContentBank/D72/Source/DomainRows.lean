module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Response
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostDomainJets
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.W.Charts6 CatalanMeasure.GenD.Uniform.W.Prof
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff Cert)
noncomputable section
variable {N p : Nat} [Fact p.Prime]

def slotLinear {K : Nat} : List (Fin K × Int) → (Fin K → ZMod p) →ₗ[ZMod p] ZMod p
  | [] => 0
  | (k,z)::ts => (z : ZMod p) • LinearMap.proj k + slotLinear ts

def slotEntry {K : Nat} (atSlot : Option (Fin K)) : List (Fin K × Int) → Int
  | [] => 0
  | (k,z)::ts => (if atSlot = some k then z else 0) + slotEntry atSlot ts

theorem slotLinear_sourceVector {K : Nat} (atSlot : Option (Fin K)) (ts : List (Fin K × Int)) :
    slotLinear (p := p) ts (sourceVector atSlot) = (slotEntry atSlot ts : ZMod p) := by
  induction ts generalizing atSlot with
  | nil => simp [slotLinear, slotEntry]
  | cons t ts ih =>
    obtain ⟨k,z⟩ := t
    cases atSlot with
    | none =>
      simp [slotLinear, slotEntry, sourceVector]
      simpa [sourceVector] using ih none
    | some j =>
      by_cases hj : j = k
      · subst j
        simp [slotLinear, slotEntry, sourceVector]
        simpa [sourceVector] using ih (some k)
      · simp [slotLinear, slotEntry, sourceVector, Pi.single_apply, hj, Ne.symm hj]
        simpa [sourceVector] using ih (some j)

def nativeDomainTarget {n K : Nat} (slots : Fin n → Option (Fin K)) (ts : List (Fin K × Int)) :
    List Int :=
  (List.finRange n).map fun i => slotEntry (slots i) ts

theorem nativeDomainTarget_coord {n K : Nat} (slots : Fin n → Option (Fin K))
    (ts : List (Fin K × Int)) (i : Fin n) :
    ((nativeDomainTarget slots ts).getD i.val 0 : ZMod p) =
      ((slotLinear ts).comp (sparseSourceIns slots)) (Pi.single i 1) := by
  rw [LinearMap.comp_apply, sparseSourceIns_single, slotLinear_sourceVector]
  simp [nativeDomainTarget, List.getD_eq_getElem?_getD, i.isLt]

theorem native_domain_prefix_zero {pk : Packet} {K : Nat} {l : JetLayout pk}
    {win : List Aff} {cs : Cert}
    (slots : Fin pk.n → Option (Fin K)) (terms : List (Fin K × Int))
    (point : PhysicalPoint) (order : Aff) (zs : List (ResponseZone pk))
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hoff : ∀ g, 0 ≤ affAt N p (l.offset g)) (hw : ∀ g, 0 ≤ affAt N p (l.width g))
    (hc : jetPrefixCheck l win cs point order (nativeDomainTarget slots terms) zs = true)
    (hs : ∀ z ∈ zs, ¬ (p : Int) ∣ z.span.scale)
    (x : Fin p → Fin pk.d → ZMod p)
    (hx : ∀ g (k : Fin (l.count N p g)),
      chartMap pk (pk.chart g) p pk.n (l.jet N p g k.val x) = 0)
    (j : Nat) (hj : (j : Int) < affAt N p order) :
    slotLinear terms (sparseSourceIns slots (emb pk p pk.n (physicalJet point j x))) = 0 :=
  jetPrefixCheck_kill point order _ zs hwin hoff hw hc hs
    ((slotLinear terms).comp (sparseSourceIns slots)) 1 one_ne_zero
    (fun i => by simpa only [one_mul] using nativeDomainTarget_coord (p := p) slots terms i)
    x hx j hj

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source

module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Response
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostSeenPositions
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open Finset CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.Charts6 CatalanMeasure.GenD.Uniform.W.Charts3
open CatalanMeasure.GenD.Uniform.W.Prof
noncomputable section
variable {P : Parameters} {N p : Nat} [Fact p.Prime]

def SlotsInjective {n K : Nat} (slots : Fin n → Option (Fin K)) : Prop :=
  ∀ c c' k, slots c = some k → slots c' = some k → c = c'

theorem sparseSourceIns_coord {n K : Nat} (slots : Fin n → Option (Fin K))
    (hinj : SlotsInjective slots) (y : Fin n → ZMod p) (c : Fin n) (k : Fin K)
    (hc : slots c = some k) :
    sparseSourceIns slots y k = y c := by
  simp only [sparseSourceIns, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single c]
  · simp [sourceVector, hc]
  · intro i _ hi
    cases hsi : slots i with
    | none => simp [sourceVector, hsi]
    | some j =>
      have hj : j ≠ k := by
        intro h
        subst j
        exact hi (hinj i c k hsi hc)
      simp [sourceVector, hsi, Pi.single_apply, hj, Ne.symm hj]
  · simp

/-- The lower graph prefix and the upper slack cutoff determine the
slack at every position, even when the two tested ranges overlap. -/
theorem zero_of_slack_halves {e lo hi : Int} {x : ZMod p}
    (hord : lo ≤ hi) (hlo : e < hi → x = 0) (hhi : lo ≤ e → x = 0) : x = 0 := by
  by_cases h : e < hi
  · exact hlo h
  · exact hhi (by omega)

/-- Once checked source rows and graph halves cover the physical slots,
there is no auxiliary dimension correction. -/
theorem native_graph_injective {pk : Packet} {K : Nat} (M : MonoData P N p K)
    (slots : Fin pk.n → Option (Fin K)) (hs : SlotsInjective slots) (lc : Fin pk.n)
    (hSound : pk.Sound) (hδ : ¬ (p : Int) ∣ pk.delta)
    {width : Fin pk.charts.length → Nat} {a cm : Nat}
    (jet : ∀ g, Fin (width g) → (Fin p → Fin pk.d → ZMod p) →ₗ[ZMod p] (Fin pk.d → ZMod p))
    (hwide : P.b N + (a + 2) * p ≤ P.L N)
    (hcov : CoverKernel pk M (sparseSourceIns slots)
      ((LinearMap.proj lc).comp (emb pk p pk.n)) width a cm jet)
    (x : Fin p → Fin pk.d → ZMod p)
    (hx : ∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0)
    (hOutside : ∀ e : Fin p, cm ≤ e.val → x e = 0)
    (hNative : ∀ e, sparseSourceIns slots (emb pk p pk.n (x e)) = 0)
    (hSlack : ∀ e : Fin p, e.val < cm → ∀ c : Fin pk.n, slots c = none → c ≠ lc →
      emb pk p pk.n (x e) lc = 0 → emb pk p pk.n (x e) c = 0) :
    x = 0 := by
  funext e
  by_cases he : e.val < cm
  · have hl : emb pk p pk.n (x e) lc = 0 :=
      low_eq_zero_of_cover M (sparseSourceIns slots)
        ((LinearMap.proj lc).comp (emb pk p pk.n)) jet hwide hcov x hx hNative e he
    have hin : Function.Injective (emb pk p pk.n) :=
      emb_injective hSound rfl hδ
    apply hin
    change emb pk p pk.n (x e) = emb pk p pk.n (0 : Fin pk.d → ZMod p)
    rw [map_zero]
    funext c
    change emb pk p pk.n (x e) c = 0
    cases hc : slots c with
    | none =>
      by_cases hcl : c = lc
      · simpa [hcl] using hl
      · exact hSlack e he c hc hcl hl
    | some k =>
      have hh := congrFun (hNative e) k
      rw [sparseSourceIns_coord slots hs _ c k hc] at hh
      exact hh
  · exact hOutside e (by omega)

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source

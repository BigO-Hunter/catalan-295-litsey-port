module
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostGeneric
@[expose] public section
set_option Elab.async false
/-! Transport exact checked integer row spans to physical response maps. -/
namespace CatalanMeasure.GenD.Uniform.W.Charts6
open Finset Module CatalanMeasure.Parametric CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Charts3
noncomputable section
variable {P : Parameters} {N p : Nat} [Fact p.Prime]

theorem ambient_eval_from_single {n : Nat} (F : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p)
    (x : Fin n → ZMod p) : F x = ∑ c, x c * F (Pi.single c 1) := by
  have he : (∑ c : Fin n, x c • Pi.single c (1 : ZMod p)) = x := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro c _ hc; simp [Pi.single_apply, hc, Ne.symm hc]
    · simp
  calc
    F x = F (∑ c : Fin n, x c • Pi.single c (1 : ZMod p)) := congrArg F he.symm
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

/-- A row-span equality in ambient coordinates kills a linear response on
the actual embedded vector. The span scale and source clear are separate. -/
theorem RowSpanData.eval_zero {pk : Packet} {s : RowSpanData pk} {target : List Int}
    (hcheck : s.check target = true) (hscale : ¬ (p : Int) ∣ s.scale)
    (clear : ZMod p) (hclear : clear ≠ 0)
    (F : (Fin pk.n → ZMod p) →ₗ[ZMod p] ZMod p)
    (hcoord : ∀ c : Fin pk.n, (target.getD c.val 0 : ZMod p) = clear * F (Pi.single c 1))
    (y : Fin pk.d → ZMod p)
    (hker : ∀ i : Fin s.terms.length,
      chartMap pk (pk.chart (s.terms.get i).group) p pk.n y = 0) : F (emb pk p pk.n y) = 0 := by
  have hk := RowSpanData.kill (s := s) hcheck hscale y hker
  apply (mul_eq_zero.mp ?_).resolve_left hclear
  calc
    clear * F (emb pk p pk.n y) = ∑ c : Fin pk.n,
        (target.getD c.val 0 : ZMod p) * emb pk p pk.n y c := by
      rw [ambient_eval_from_single F, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [hcoord c]
      ring
    _ = 0 := hk

/-- The actual ambient p-step source response at one seen position. -/
def ambientResponse {pk : Packet} {K : Nat} (M : MonoData P N p K)
    (ins : (Fin pk.n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p))
    (a j : Nat) (e : Fin p) : (Fin pk.n → ZMod p) →ₗ[ZMod p] ZMod p :=
  ∑ v ∈ Finset.range (a + 1),
    ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) •
      ((M.sys.prof.psi (P.H N) (j / p + v)
        (((P.H N : Int) - 1 - ((j % p : Nat) : Int) - e) / p)).comp ins)

/-- Finite data supply one proved source row per applicable request and the
jet-kernel membership of its references. The unchanged CoverKernel follows. -/
theorem coverKernel_of_checked_rows (pk : Packet) {K : Nat} (M : MonoData P N p K)
    (ins : (Fin pk.n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p))
    (low : (Fin pk.n → ZMod p) →ₗ[ZMod p] ZMod p)
    (width : Fin pk.charts.length → Nat) (a cm : Nat)
    (jet : ∀ g, Fin (width g) → (Fin p → Fin pk.d → ZMod p) →ₗ[ZMod p] (Fin pk.d → ZMod p))
    (hrows : ∀ j : Nat, P.b N ≤ j → j + a * p < P.L N → ∀ e : Fin p, e.val < cm →
      (p : Int) ∣ (P.H N : Int) - 1 - ((j % p : Nat) : Int) - e →
      ∃ (target : List Int) (s : RowSpanData pk) (clear : ZMod p),
        s.check target = true ∧ (¬ (p : Int) ∣ s.scale) ∧ clear ≠ 0 ∧
        (∀ c : Fin pk.n, (target.getD c.val 0 : ZMod p) =
          clear * (ambientResponse M ins a j e - low) (Pi.single c 1)) ∧
        ∀ x : Fin p → Fin pk.d → ZMod p,
          (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) →
          ∀ i : Fin s.terms.length,
            chartMap pk (pk.chart (s.terms.get i).group) p pk.n (x e) = 0) :
    CoverKernel pk M ins (low.comp (emb pk p pk.n)) width a cm jet := by
  intro j hj hl e he hdiv x hx
  obtain ⟨target, s, clear, hc, hs, hclear, hcoord, hk⟩ := hrows j hj hl e he hdiv
  have hz := RowSpanData.eval_zero (s := s) hc hs clear hclear (ambientResponse M ins a j e - low) hcoord
    (x e) (hk x hx)
  have hh := sub_eq_zero.mp (show ambientResponse M ins a j e (emb pk p pk.n (x e)) -
      low (emb pk p pk.n (x e)) = 0 from hz)
  simpa [ambientResponse, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using hh

end
end CatalanMeasure.GenD.Uniform.W.Charts6

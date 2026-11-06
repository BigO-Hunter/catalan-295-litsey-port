module
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostResponseCover
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts6
open Finset CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Charts3
noncomputable section
variable {P : Parameters} {N p : Nat} [Fact p.Prime]

/-- A whole residue system lies in the usable starting columns when the
available interval is at least two p-blocks after the p-step reserve. -/
theorem response_every_position {H b L a : Nat} (hwide : b + (a + 2) * p ≤ L)
    (e : Fin p) :
    ∃ j, b ≤ j ∧ j + a * p < L ∧
      (p : Int) ∣ (H : Int) - 1 - ((j % p : Nat) : Int) - e := by
  obtain ⟨t, ht, _⟩ := exists_unique_pos (p := p) ((H : Int) - 1 - e)
  have hp : 0 < p := Nat.Prime.pos (Fact.out : p.Prime)
  let j := p * (b / p + 1) + t.val
  have hmod := Nat.mod_lt b hp
  have hdiv := Nat.div_add_mod b p
  have hts := t.isLt
  have hbase : p * (b / p + 1) = p * (b / p) + p := by ring
  have hwide' : b + a * p + 2 * p ≤ L := by
    simpa [Nat.add_mul, Nat.add_assoc] using hwide
  refine ⟨j, ?_, ?_, ?_⟩
  · dsimp [j]; omega
  · dsimp [j]; omega
  · have hm : j % p = t.val := by
      dsimp [j]
      rw [Nat.add_mod]
      simp [Nat.mul_mod, Nat.mod_eq_of_lt t.isLt]
    rw [hm]
    have he : (H : Int) - 1 - (t.val : Int) - e = (H : Int) - 1 - e - t.val := by ring
    rw [he]
    exact ht

theorem low_eq_zero_of_cover {pk : Packet} {K : Nat} (M : MonoData P N p K)
    (ins : (Fin pk.n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p))
    (low : (Fin pk.d → ZMod p) →ₗ[ZMod p] ZMod p)
    {width : Fin pk.charts.length → Nat} {a cm : Nat}
    (jet : ∀ g, Fin (width g) → (Fin p → Fin pk.d → ZMod p) →ₗ[ZMod p] (Fin pk.d → ZMod p))
    (hwide : P.b N + (a + 2) * p ≤ P.L N)
    (hcov : CoverKernel pk M ins low width a cm jet)
    (x : Fin p → Fin pk.d → ZMod p)
    (hx : ∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0)
    (hzero : ∀ e : Fin p, ins (emb pk p pk.n (x e)) = 0)
    (e : Fin p) (he : e.val < cm) : low (x e) = 0 := by
  obtain ⟨j, hj, hL, hdiv⟩ := response_every_position (H := P.H N) hwide e
  have hh := hcov j hj hL e he hdiv x hx
  simpa [hzero e] using hh.symm

end
end CatalanMeasure.GenD.Uniform.W.Charts6

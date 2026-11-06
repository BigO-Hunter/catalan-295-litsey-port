module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowAffineSupport
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PhysicalGate
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Finset CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.LStar CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section

def finResidueInterval (p lo hi : Nat) : Finset (Fin p) :=
  Finset.univ.filter (fun e => lo ≤ e.val ∧ e.val < hi)

theorem finResidueInterval_card {p lo hi : Nat} (hh : hi ≤ p) :
    (finResidueInterval p lo hi).card = hi-lo := by
  have he : (finResidueInterval p lo hi).map Fin.valEmbedding = Finset.Ico lo hi := by
    ext j
    simp only [Finset.mem_map, finResidueInterval, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact he
    · intro hj
      exact ⟨⟨j, hj.2.trans_le hh⟩, hj, rfl⟩
  rw [← Finset.card_map, he, Nat.card_Ico]

theorem idxQuo_from_residue_band {H p l s : Nat} (hp : 0 < p) (hl : l < p)
    (hb : (s : Int) * p ≤ (H : Int) - 1 - idxRes H p l)
    (ht : (H : Int) - 1 - idxRes H p l < ((s : Int)+1)*p) :
    idxQuo H p l = s ∧ (l : Int) = (H : Int) - 1 - (s : Int)*p - idxRes H p l := by
  have hpI : (0 : Int) < p := by exact_mod_cast hp
  have hn := Int.emod_nonneg ((H : Int)-1-l) hpI.ne'
  have hh : ((idxRes H p l : Nat) : Int) = ((H : Int)-1-l) % p :=
    Int.toNat_of_nonneg hn
  have he := Int.emod_add_mul_ediv ((H : Int)-1-l) p
  rw [← hh] at he
  change (idxRes H p l : Int) + p * idxQuo H p l = (H : Int)-1-l at he
  have hsum : (H : Int)-1-idxRes H p l = idxQuo H p l * p + l := by
    rw [Int.mul_comm (idxQuo H p l)]
    omega
  have hbq : idxQuo H p l * (p : Int) ≤ (H : Int)-1-idxRes H p l := by
    rw [hsum]
    omega
  have htq : (H : Int)-1-idxRes H p l < (idxQuo H p l+1)*p := by
    rw [hsum, add_mul, one_mul]
    omega
  have heq := (int_div_eq_of_bounds hpI hbq htq).symm.trans (int_div_eq_of_bounds hpI hb ht)
  refine ⟨heq, ?_⟩
  rw [heq] at hsum
  omega

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72

module
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceSparse
@[expose] public section
set_option Elab.async false
/-! Signed source dispatch. Upper cutoffs and missing keys remain failures. -/
namespace CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD OAI.InternalCatalan
noncomputable section
variable {p : Nat} [Fact p.Prime]

def IntSourceTree.signed? (tree : IntSourceTree) (H : Nat) (k S : Int) : Option Int :=
  if S < -1 ∨ k = -1 then some 0 else
  if (S + 1).toNat < H then
    if 0 ≤ k then tree.get? (H * k.toNat + (S + 1).toNat)
    else (tree.get? (H * (-k - 2).toNat + (S + 1).toNat)).map Neg.neg
  else none

theorem source_key_encode (A : Int → Int → Rat) {H : Nat} (hH : 0 < H)
    {k S : Int} (hk : 0 ≤ k) (hS : -1 ≤ S) (hSH : (S + 1).toNat < H) :
    sourceKey A H (H * k.toNat + (S + 1).toNat) = A k S := by
  unfold sourceKey
  rw [Nat.mul_add_div hH, Nat.div_eq_of_lt hSH, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hSH]
  rw [Int.toNat_of_nonneg hk, Int.toNat_of_nonneg (by omega : 0 ≤ S + 1)]
  congr 1 <;> omega

/-- Semantic premises describe the source family once; a failed finite lookup
never becomes an assumed zero. -/
theorem IntSourceTree.signed?_sound (tree : IntSourceTree) (H : Nat) (hH : 0 < H)
    (scale : Int) (A : Int → Int → Rat)
    (hbelow : ∀ k S, S < -1 → A k S = 0)
    (hminus : ∀ S, A (-1) S = 0)
    (hreflect : ∀ k S, A k S = -A (-k - 2) S)
    (hget : ∀ n v, tree.get? n = some v → ResRec.Gd p (sourceKey A H n)
      ((v : ZMod p) / (scale : ZMod p))) :
    ∀ k S v, tree.signed? H k S = some v → ResRec.Gd p (A k S)
      ((v : ZMod p) / (scale : ZMod p)) := by
  intro k S v hg
  unfold IntSourceTree.signed? at hg
  split_ifs at hg with hz hSH hk
  · have hv : (0 : Int) = v := Option.some.inj hg
    rw [← hv]
    have ha : A k S = 0 := by
      rcases hz with hs | hm
      · exact hbelow k S hs
      · simpa only [hm] using hminus S
    rw [ha]
    simpa using (ResRec.Gd.nat (p := p) 0)
  · have hs : -1 ≤ S := by omega
    have he := source_key_encode A hH hk hs hSH
    simpa only [he] using hget _ v hg
  · have hs : -1 ≤ S := by omega
    have hkm : k ≠ -1 := by omega
    have hk' : 0 ≤ -k - 2 := by omega
    cases he : tree.get? (H * (-k - 2).toNat + (S + 1).toNat) with
    | none => simp [he] at hg
    | some w =>
      have hv : -w = v := by simpa only [he, Option.map_some, Option.some.injEq] using hg
      have hw := hget _ w he
      rw [source_key_encode A hH hk' hs hSH] at hw
      have hn := ResRec.Gd.sub (ResRec.Gd.nat (p := p) 0) hw
      rw [hreflect k S]
      rw [← hv]
      simpa [neg_div] using hn

end
end CatalanMeasure.GenD.Uniform.W.Charts6

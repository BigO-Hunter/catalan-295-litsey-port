module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapWindow
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapDamage

@[expose] public section

/-! # Actual selected-colour damage and surviving representatives -/

open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.UFMember CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapMemberCount

variable {p N q o r s l : ℕ} [Fact p.Prime] {Fr : Frame} {T : TwoTermData Fr q o}
variable (W : WrapWindow.Window Fr q o r s l p N T)

noncomputable def colour : Fin (s+1-l) ⊕ Fin (s+1-l) → ZMod p :=
  Sum.elim (fun i => (W.rowBorder i:ZMod p)) (fun i => (W.colBorder i:ZMod p))
noncomputable def slots := W.Jr.disjSum W.Jc
noncomputable def selected := (slots W).image (colour W)
noncomputable def edited (K : Finset (Fin r)) := K.image (colOf (p:=p) (fun i:Fin r => (i:ℕ)))
open Classical in
noncomputable def rows (K : Finset (Fin r)) := W.Jr.filter (fun i => (W.rowBorder i:ZMod p)∉edited K)
open Classical in
noncomputable def cols (K : Finset (Fin r)) := W.Jc.filter (fun i => (W.colBorder i:ZMod p)∉edited K)
open Classical in
noncomputable def unedited (K : Finset (Fin r)) := (slots W).filter (fun i => colour W i∉edited K)

/-- Every surplus row and column has its own distinct colour. -/
theorem colour_injective : Function.Injective (colour W) := by
  let off : Fin (s+1-l) ⊕ Fin (s+1-l) → ℕ := Sum.elim (fun i => 2*(i:ℕ)+1) (fun i => 2*(i:ℕ))
  have he (i) : colour W i=((r+2*l-1:ℕ):ZMod p)+(off i:ZMod p) := by
    rcases i with i|i
    · change (W.rowBorder i:ZMod p)=_
      rw [W.rowBorder_eq]
      simp only [off,Sum.elim_inl,Nat.cast_add,add_assoc]
    · change (W.colBorder i:ZMod p)=_
      rw [W.colBorder_eq]
      simp only [off,Sum.elim_inr,Nat.cast_add]
  have hb (i) : off i<p := by
    have hp := W.hp; have hl := W.hl; have hls := W.hls
    rcases i with i|i <;> have hi := i.2 <;> dsimp only [off,Sum.elim_inl,Sum.elim_inr] <;> omega
  intro i j hij
  rw [he i,he j] at hij
  have hz := (ZMod.natCast_eq_natCast_iff' (off i) (off j) p).mp (add_left_cancel hij)
  rw [Nat.mod_eq_of_lt (hb i),Nat.mod_eq_of_lt (hb j)] at hz
  rcases i with i|i <;> rcases j with j|j <;> dsimp only [off,Sum.elim_inl,Sum.elim_inr] at hz
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · omega
  · omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem selected_card : (selected W).card=W.Jr.card+W.Jc.card := by
  rw [selected,Finset.card_image_of_injective _ (colour_injective W)]
  exact Finset.card_disjSum _ _

theorem unedited_card (K : Finset (Fin r)) :
    (unedited W K).card=(rows W K).card+(cols W K).card := by
  have he : unedited W K=(rows W K).disjSum (cols W K) := by
    classical
    apply Finset.ext; intro i
    rcases i with i|i
    · constructor
      · intro hi
        have hh := Finset.mem_filter.mp hi
        apply Finset.inl_mem_disjSum.mpr
        exact Finset.mem_filter.mpr ⟨Finset.inl_mem_disjSum.mp hh.1,hh.2⟩
      · intro hi
        have hh := Finset.mem_filter.mp (Finset.inl_mem_disjSum.mp hi)
        exact Finset.mem_filter.mpr ⟨Finset.inl_mem_disjSum.mpr hh.1,hh.2⟩
    · constructor
      · intro hi
        have hh := Finset.mem_filter.mp hi
        apply Finset.inr_mem_disjSum.mpr
        exact Finset.mem_filter.mpr ⟨Finset.inr_mem_disjSum.mp hh.1,hh.2⟩
      · intro hi
        have hh := Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hi)
        exact Finset.mem_filter.mpr ⟨Finset.inr_mem_disjSum.mpr hh.1,hh.2⟩
  rw [he,Finset.card_disjSum]

theorem unedited_image (K : Finset (Fin r)) :
    (unedited W K).image (colour W)=selected W \ edited K := by
  apply Finset.ext; intro u
  simp only [Finset.mem_image,unedited,Finset.mem_filter,Finset.mem_sdiff,selected]
  constructor
  · rintro ⟨i,⟨hi,hu⟩,rfl⟩
    exact ⟨⟨i,hi,rfl⟩,hu⟩
  · rintro ⟨⟨i,hi,rfl⟩,hu⟩
    exact ⟨i,⟨hi,hu⟩,rfl⟩

/-- Each edited selected colour costs at most one selected coordinate,
so the truncated kernel count loses at most t1+t2. -/
theorem sigma_loss (K : Finset (Fin r)) :
    (W.Jr.card+W.Jc.card-(s+1-l))-
      ((WrapDamage.single K (colOf (p:=p) (fun i:Fin r => (i:ℕ))) (selected W)).card+
       (WrapDamage.multiple K (colOf (p:=p) (fun i:Fin r => (i:ℕ))) (selected W)).card)≤
      (rows W K).card+(cols W K).card-(s+1-l) := by
  have h := WrapDamage.selected_loss K (colOf (p:=p) (fun i:Fin r => (i:ℕ))) (selected W)
  have hc := Finset.card_image_of_injective (unedited W K) (colour_injective W)
  rw [unedited_image,unedited_card] at hc
  rw [selected_card] at h
  change W.Jr.card+W.Jc.card-_≤(selected W \ edited K).card at h
  rw [hc] at h
  omega

/-- A positive surviving kernel count supplies an untouched selected
representative, including when the original representative was edited. -/
theorem representative_exists (K : Finset (Fin r))
    (hpos : 0<(rows W K).card+(cols W K).card-(s+1-l)) :
    ∃ t,W.t0≤t ∧ t≤W.tv ∧ t<r+p ∧ (t:ZMod p)∉edited K := by
  have hp : 0<(unedited W K).card := by rw [unedited_card]; omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hp
  have h := (Finset.mem_filter.mp hi)
  rcases i with i|i
  · have hj : i∈W.Jr := by simpa only [slots,Finset.inl_mem_disjSum] using h.1
    have hh := (Finset.mem_filter.mp hj).2
    exact ⟨W.rowBorder i,hh.1,hh.2,(W.rowBorder_range i).2,h.2⟩
  · have hj : i∈W.Jc := by simpa only [slots,Finset.inr_mem_disjSum] using h.1
    have hh := (Finset.mem_filter.mp hj).2
    exact ⟨W.colBorder i,hh.1,hh.2,(W.colBorder_range i).2,h.2⟩

end CatalanCore.Uniform.Content.UFSimple.WrapMemberCount

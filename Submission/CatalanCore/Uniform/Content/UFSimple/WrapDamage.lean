module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapCount
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! # Exact finite-colour common-deletion budget -/

open Finset

namespace CatalanCore.Uniform.Content.UFSimple.WrapDamage

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- Number of deleted common coordinates of a given colour. -/
def multiplicity (K : Finset ι) (f : ι → κ) (u : κ) : ℕ :=
  (K.filter (fun i => f i=u)).card

/-- Edited selected colours with exactly one deletion. -/
def single (K : Finset ι) (f : ι → κ) (J : Finset κ) : Finset κ :=
  (K.image f).filter (fun u => u∈J ∧ multiplicity K f u=1)

/-- Edited selected colours with at least two deletions. -/
def multiple (K : Finset ι) (f : ι → κ) (J : Finset κ) : Finset κ :=
  (K.image f).filter (fun u => u∈J ∧ 2≤multiplicity K f u)

/-- Every edited colour outside J, including common top extensions. -/
def outside (K : Finset ι) (f : ι → κ) (J : Finset κ) : Finset κ := K.image f \ J

theorem multiplicity_pos (K : Finset ι) (f : ι → κ) {u : κ} (hu : u∈K.image f) :
    1≤multiplicity K f u := by
  rcases Finset.mem_image.mp hu with ⟨i,hi,rfl⟩
  exact Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,rfl⟩⟩

/-- Every single selected edit costs one deletion, every multiple edit
two, and every outside colour one. This covers all edited source classes. -/
theorem deletion_budget (K : Finset ι) (f : ι → κ) (J : Finset κ) :
    (single K f J).card+2*(multiple K f J).card+(outside K f J).card≤K.card := by
  have h : ∀ u∈K.image f,
      (if u∈J ∧ multiplicity K f u=1 then 1 else 0)+
      (if u∈J ∧ 2≤multiplicity K f u then 2 else 0)+
      (if u∉J then 1 else 0)≤multiplicity K f u := by
    intro u hu
    have hp := multiplicity_pos K f hu
    by_cases hj : u∈J
    · by_cases hs : multiplicity K f u=1
      · simp [hj,hs]
      · have hm : 2≤multiplicity K f u := by omega
        simp [hj,hs,hm]
    · simp [hj]
      exact hp
  have hh := Finset.sum_le_sum h
  have he : K.card=∑ u∈K.image f,multiplicity K f u :=
    Finset.card_eq_sum_card_image f K
  rw [← he] at hh
  have hs : (single K f J).card=∑ u∈K.image f,if u∈J ∧ multiplicity K f u=1 then 1 else 0 := by
    simp only [single,Finset.card_eq_sum_ones,Finset.sum_filter]
  have hm : 2*(multiple K f J).card=∑ u∈K.image f,if u∈J ∧ 2≤multiplicity K f u then 2 else 0 := by
    simp only [multiple,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u hu
    split <;> simp
  have ho : (outside K f J).card=∑ u∈K.image f,if u∉J then 1 else 0 := by
    simp only [outside,Finset.sdiff_eq_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [hs,hm,ho]
  simpa only [Finset.sum_add_distrib] using hh

/-- Deleting edited selected colours loses exactly the single and
multiple classes. No assumptions on the sizes of the colour fibres. -/
theorem selected_partition (K : Finset ι) (f : ι → κ) (J : Finset κ) :
    J ∩ K.image f=single K f J ∪ multiple K f J := by
  apply Finset.ext; intro u
  simp only [Finset.mem_inter,single,multiple,Finset.mem_union,Finset.mem_filter]
  constructor
  · rintro ⟨hj,hk⟩
    have hpos := multiplicity_pos K f hk
    by_cases hs : multiplicity K f u=1
    · exact Or.inl ⟨hk,hj,hs⟩
    · exact Or.inr ⟨hk,hj,by omega⟩
  · rintro (⟨hk,hj,_⟩|⟨hk,hj,_⟩) <;> exact ⟨hj,hk⟩

theorem selected_loss (K : Finset ι) (f : ι → κ) (J : Finset κ) :
    J.card-((single K f J).card+(multiple K f J).card)≤(J \ K.image f).card := by
  have h := Finset.card_union_le (single K f J) (multiple K f J)
  rw [← selected_partition K f J] at h
  have he := Finset.card_sdiff_add_card_inter J (K.image f)
  omega

/-- The concrete finite-colour budget feeds the zero-debit price lemma. -/
theorem price_zero (K : Finset ι) (f : ι → κ) (J : Finset κ)
    (n d sigma retained sigma' retained' : ℕ)
    (hsigma : sigma-((single K f J).card+(multiple K f J).card)≤sigma')
    (hret : retained'≤retained+(multiple K f J).card+(outside K f J).card) :
    2*(n-K.card)-(d+WrapCount.gain sigma' retained')≤
      2*n-(d+WrapCount.gain sigma retained) :=
  WrapCount.candidate_debit_zero n K.card d sigma retained _ _ _ sigma' retained'
    (deletion_budget K f J) hsigma hret

/-- After unchanged colours are compared with the original source and
single edited selected colours are cancelled or killed, only multiply
edited selected colours and edited outside colours can enlarge support. -/
theorem retained_support (K : Finset ι) (f : ι → κ) (J R R' : Finset κ)
    (hquiet : ∀ u,u∉K.image f → u∈R' → u∈R)
    (hsingle : ∀ u,u∈single K f J → u∉R') :
    R'⊆R ∪ multiple K f J ∪ outside K f J := by
  intro u hu
  by_cases hk : u∈K.image f
  · by_cases hj : u∈J
    · have hp := multiplicity_pos K f hk
      by_cases hm : 2≤multiplicity K f u
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk,hj,hm⟩))
      · have hs : u∈single K f J := Finset.mem_filter.mpr ⟨hk,hj,by omega⟩
        exact False.elim (hsingle u hs hu)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hk,hj⟩)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hquiet u hk hu))

theorem retained_count (K : Finset ι) (f : ι → κ) (J R R' : Finset κ)
    (hquiet : ∀ u,u∉K.image f → u∈R' → u∈R)
    (hsingle : ∀ u,u∈single K f J → u∉R') :
    R'.card≤R.card+(multiple K f J).card+(outside K f J).card := by
  have h := Finset.card_le_card (retained_support K f J R R' hquiet hsingle)
  have h1 := Finset.card_union_le R (multiple K f J)
  have h2 := Finset.card_union_le (R ∪ multiple K f J) (outside K f J)
  omega

/-- The complete zero-debit arithmetic once the actual matrix source
has supplied unchanged-colour comparison and single-class cancellation. -/
theorem price_from_source (K : Finset ι) (f : ι → κ) (J R R' : Finset κ)
    (n d sigma sigma' : ℕ)
    (hsigma : sigma-((single K f J).card+(multiple K f J).card)≤sigma')
    (hquiet : ∀ u,u∉K.image f → u∈R' → u∈R)
    (hsingle : ∀ u,u∈single K f J → u∉R') :
    2*(n-K.card)-(d+WrapCount.gain sigma' R'.card)≤
      2*n-(d+WrapCount.gain sigma R.card) :=
  price_zero K f J n d sigma R.card sigma' R'.card hsigma
    (retained_count K f J R R' hquiet hsingle)

end CatalanCore.Uniform.Content.UFSimple.WrapDamage

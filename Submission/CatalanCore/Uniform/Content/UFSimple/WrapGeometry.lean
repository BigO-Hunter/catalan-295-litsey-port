module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # Actual alternating row and column chain orderings

Write p=2s+1 and m=s+l, where 1≤l≤s. The 2l-1 balanced
classes supply the mixed core, and s+1-l surplus rows/columns remain.
The two bijections below select the actual original border indices.
-/

namespace CatalanCore.Uniform.Content.UFSimple.WrapGeometry

/-- Original row index of balanced lower-node offset t. -/
def rowBalanced (s t : ℕ) : ℕ := if t % 2 = 0 then t / 2 else s + 1 + t / 2

/-- Original column index of balanced lower-node offset t. -/
def colBalanced (s t : ℕ) : ℕ := if t % 2 = 0 then s + t / 2 else t / 2

theorem rowBalanced_bound {s l t : ℕ} (hl : 1 ≤ l) (hls : l ≤ s) (ht : t < 2*l-1) :
    rowBalanced s t < s+l := by
  unfold rowBalanced
  split_ifs <;> omega

theorem colBalanced_bound {s l t : ℕ} (hl : 1 ≤ l) (hls : l ≤ s) (ht : t < 2*l-1) :
    colBalanced s t < s+l := by
  unfold colBalanced
  split_ifs <;> omega

theorem rowBalanced_range {s l t : ℕ} (hl : 1 ≤ l) (ht : t < 2*l-1) :
    rowBalanced s t < l ∨ s+1 ≤ rowBalanced s t := by
  unfold rowBalanced
  split_ifs <;> omega

theorem colBalanced_range {s l t : ℕ} (hl : 1 ≤ l) (ht : t < 2*l-1) :
    colBalanced s t < l-1 ∨ s ≤ colBalanced s t := by
  unfold colBalanced
  split_ifs <;> omega

theorem rowBalanced_inj {s l t u : ℕ} (hl : 1 ≤ l) (hls : l ≤ s)
    (ht : t < 2*l-1) (hu : u < 2*l-1) (he : rowBalanced s t = rowBalanced s u) : t=u := by
  unfold rowBalanced at he
  split_ifs at he <;> omega

theorem colBalanced_inj {s l t u : ℕ} (hl : 1 ≤ l) (hls : l ≤ s)
    (ht : t < 2*l-1) (hu : u < 2*l-1) (he : colBalanced s t = colBalanced s u) : t=u := by
  unfold colBalanced at he
  split_ifs at he <;> omega

/-- Balanced indices followed by surplus row indices. -/
def rowSlot (s l : ℕ) (hl : 1 ≤ l) (hls : l ≤ s) :
    Fin (2*l-1) ⊕ Fin (s+1-l) → Fin (s+l)
  | Sum.inl t => ⟨rowBalanced s t, rowBalanced_bound hl hls t.2⟩
  | Sum.inr i => ⟨l+i, by have := i.2; omega⟩

/-- Balanced indices followed by surplus column indices. -/
def colSlot (s l : ℕ) (hl : 1 ≤ l) (hls : l ≤ s) :
    Fin (2*l-1) ⊕ Fin (s+1-l) → Fin (s+l)
  | Sum.inl t => ⟨colBalanced s t, colBalanced_bound hl hls t.2⟩
  | Sum.inr i => ⟨l-1+i, by have := i.2; omega⟩

theorem rowSlot_injective (s l : ℕ) (hl : 1 ≤ l) (hls : l ≤ s) :
    Function.Injective (rowSlot s l hl hls) := by
  intro x y he
  have hv := congrArg Fin.val he
  rcases x with x | x <;> rcases y with y | y
  · have hxy : x=y := Fin.ext (rowBalanced_inj hl hls x.2 y.2 hv)
    exact congrArg Sum.inl hxy
  · have hr := rowBalanced_range (s := s) hl x.2
    have hy := y.2
    change rowBalanced s x = l+y at hv
    rcases hr with hr | hr <;> omega
  · have hr := rowBalanced_range (s := s) hl y.2
    have hx := x.2
    change l+x = rowBalanced s y at hv
    rcases hr with hr | hr <;> omega
  · have hxy : x=y := by apply Fin.ext; change l+x = l+y at hv; omega
    exact congrArg Sum.inr hxy

theorem colSlot_injective (s l : ℕ) (hl : 1 ≤ l) (hls : l ≤ s) :
    Function.Injective (colSlot s l hl hls) := by
  intro x y he
  have hv := congrArg Fin.val he
  rcases x with x | x <;> rcases y with y | y
  · have hxy : x=y := Fin.ext (colBalanced_inj hl hls x.2 y.2 hv)
    exact congrArg Sum.inl hxy
  · have hr := colBalanced_range (s := s) hl x.2
    have hy := y.2
    change colBalanced s x = l-1+y at hv
    rcases hr with hr | hr <;> omega
  · have hr := colBalanced_range (s := s) hl y.2
    have hx := x.2
    change l-1+x = colBalanced s y at hv
    rcases hr with hr | hr <;> omega
  · have hxy : x=y := by apply Fin.ext; change l-1+x = l-1+y at hv; omega
    exact congrArg Sum.inr hxy

/-- The actual wrapped border row ordering. -/
noncomputable def rowEquiv (s l : ℕ) (hl : 1 ≤ l) (hls : l ≤ s) :
    (Fin (2*l-1) ⊕ Fin (s+1-l)) ≃ Fin (s+l) :=
  Equiv.ofBijective (rowSlot s l hl hls)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨rowSlot_injective s l hl hls, by simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩)

/-- The actual wrapped border column ordering. -/
noncomputable def colEquiv (s l : ℕ) (hl : 1 ≤ l) (hls : l ≤ s) :
    (Fin (2*l-1) ⊕ Fin (s+1-l)) ≃ Fin (s+l) :=
  Equiv.ofBijective (colSlot s l hl hls)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨colSlot_injective s l hl hls, by simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩)

/-- Balanced row nodes are the actual lower or upper node of each pair. -/
theorem rowBalanced_node (r s t : ℕ) :
    r + 2 * rowBalanced s t = r+t + (if t%2=0 then 0 else 2*s+1) := by
  unfold rowBalanced
  split_ifs <;> omega

/-- Balanced column nodes occupy the opposite end of the actual pair. -/
theorem colBalanced_node (r s t : ℕ) :
    r + 2 * colBalanced s t + 1 = r+t + (if t%2=0 then 2*s+1 else 0) := by
  unfold colBalanced
  split_ifs <;> omega

/-- The original surplus rows have the opposite parity to the virtual rows. -/
theorem surplus_row_node (r l i : ℕ) (hl : 1 ≤ l) :
    r+2*(l+i) = (r+2*l-1)+2*i+1 := by omega

/-- The original surplus columns start the complementary interval. -/
theorem surplus_col_node (r l i : ℕ) (hl : 1 ≤ l) :
    r+2*(l-1+i)+1 = (r+2*l-1)+2*i := by omega

/-- Convert the ordinary wrapped inequalities into the explicit odd-prime
parameters used by the actual chain bijections. -/
theorem wrap_parameters {p m : ℕ} (hp : p%2=1) (hm : m<p) (hmp : p≤2*m) :
    1≤m-p/2 ∧ m-p/2≤p/2 ∧ p=2*(p/2)+1 ∧ m=p/2+(m-p/2) := by
  omega

/-- Original common nodes together with the actual mixed balanced rows,
followed by the actual surplus rows. -/
noncomputable def rowFullEquiv (ι : Type*) (s l : ℕ) (hl : 1 ≤ l) (hls : l ≤ s) :
    ((ι ⊕ Fin (2*l-1)) ⊕ Fin (s+1-l)) ≃ (ι ⊕ Fin (s+l)) :=
  (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) (rowEquiv s l hl hls))

/-- The corresponding independently ordered original columns. -/
noncomputable def colFullEquiv (ι : Type*) (s l : ℕ) (hl : 1 ≤ l) (hls : l ≤ s) :
    ((ι ⊕ Fin (2*l-1)) ⊕ Fin (s+1-l)) ≃ (ι ⊕ Fin (s+l)) :=
  (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) (colEquiv s l hl hls))

/-- Each actual balanced pair has the same residue on both axes. -/
theorem balanced_same_colour (r s t : ℕ) :
    ((r+2*rowBalanced s t : ℕ) : ZMod (2*s+1)) =
      ((r+2*colBalanced s t+1 : ℕ) : ZMod (2*s+1)) := by
  rw [rowBalanced_node, colBalanced_node]
  by_cases ht : t%2=0 <;> simp [ht, Nat.cast_add, ZMod.natCast_self]

/-- The remaining surplus rows and columns are disjoint modulo p. -/
theorem surplus_distinct_colour (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (i j : Fin (s+1-l)) :
    ((r+2*(l+i) : ℕ) : ZMod (2*s+1)) ≠
      ((r+2*(l-1+j)+1 : ℕ) : ZMod (2*s+1)) := by
  intro he
  rw [surplus_row_node r l i hl, surplus_col_node r l j hl] at he
  have hi := i.2
  have hj := j.2
  have he' : (((2*(i:ℕ)+1) : ℕ) : ZMod (2*s+1)) =
      (((2*(j:ℕ)) : ℕ) : ZMod (2*s+1)) := by
    apply add_left_cancel (a := (((r+2*l-1 : ℕ) : ZMod (2*s+1))))
    simpa only [Nat.cast_add, add_assoc] using he
  have hmod := (ZMod.natCast_eq_natCast_iff' (2*(i:ℕ)+1) (2*(j:ℕ)) (2*s+1)).mp he'
  rw [Nat.mod_eq_of_lt (by omega : 2*(i:ℕ)+1<2*s+1),
    Nat.mod_eq_of_lt (by omega : 2*(j:ℕ)<2*s+1)] at hmod
  omega

end CatalanCore.Uniform.Content.UFSimple.WrapGeometry

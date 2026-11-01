module

public import Mathlib.Tactic
public import Mathlib.Data.Nat.ModEq
public import CatalanCore.Uniform.Content.UFSimple.WrapCycles
public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixCoreGeometry

@[expose] public section

namespace CatalanCore.Uniform.Content.UFSimple.WrapJointProfile

def count (p r gamma : ℕ) : ℕ := r/p+if gamma<r%p then 1 else 0

def lower (p r gamma : ℕ) : ℕ := gamma+count p r gamma*p

def bit (p r gamma : ℕ) : ℕ := (lower p r gamma-r)%2

/-- The first ORIGINAL node of a colour at or above the common prefix. -/
theorem lower_bounds (p r gamma : ℕ) (hp : 0<p) (hg : gamma<p) :
    r≤lower p r gamma ∧ lower p r gamma<r+p := by
  have hd := Nat.mod_add_div r p
  have hm := Nat.mod_lt r hp
  have hm0 := Nat.zero_le (r%p)
  unfold lower count
  by_cases h : gamma<r%p
  · simp only [if_pos h,Nat.add_mul,one_mul]
    constructor <;> nlinarith
  · simp only [if_neg h,Nat.add_zero]
    constructor <;> nlinarith

/-- Exact common-fibre count, including the gamma=0 endpoint. -/
theorem common_bound (p r gamma a : ℕ) (hp : 0<p) (hg : gamma<p) :
    gamma+a*p<r ↔ a<count p r gamma := by
  have hl := lower_bounds p r gamma hp hg
  constructor
  · intro ha
    by_contra hn
    have hm := Nat.mul_le_mul_right p (show count p r gamma≤a by omega)
    unfold lower at hl
    nlinarith
  · intro ha
    have hm := Nat.mul_le_mul_right p (show a+1≤count p r gamma by omega)
    unfold lower at hl
    nlinarith

/-- The two actual candidates in one original doubled period. -/
theorem two_candidates (p r gamma a : ℕ) (hp : 0<p) (hg : gamma<p)
    (ha0 : r≤a) (ha1 : a<r+2*p) (hc : a%p=gamma) :
    a=lower p r gamma ∨ a=lower p r gamma+p := by
  have hl := lower_bounds p r gamma hp hg
  have he := Nat.mod_add_div a p
  rw [hc] at he
  have hlo : count p r gamma≤a/p := by
    by_contra hn
    have hm := Nat.mul_le_mul_right p (show a/p+1≤count p r gamma by omega)
    unfold lower at hl
    nlinarith
  have hhi : a/p≤count p r gamma+1 := by
    by_contra hn
    have hm := Nat.mul_le_mul_right p (show count p r gamma+2≤a/p by omega)
    unfold lower at hl
    nlinarith
  have hq : a/p=count p r gamma ∨ a/p=count p r gamma+1 := by omega
  rcases hq with hq|hq
  · left
    unfold lower
    rw [hq] at he
    nlinarith
  · right
    unfold lower
    rw [hq] at he
    nlinarith

theorem bit_lt (p r gamma : ℕ) : bit p r gamma<2 := Nat.mod_lt _ (by decide)

/-- The even ORIGINAL row is the lower or upper node according to the
actual parity bit; no compressed common-node replacement is used. -/
theorem row_node (p r gamma a : ℕ) (hp : 0<p) (hodd : p%2=1) (hg : gamma<p)
    (ha0 : r≤a) (ha1 : a<r+2*p) (hc : a%p=gamma) (hrow : (a-r)%2=0) :
    a=lower p r gamma+bit p r gamma*p := by
  have hl := lower_bounds p r gamma hp hg
  rcases two_candidates p r gamma a hp hg ha0 ha1 hc with he|he
  · have hb : bit p r gamma=0 := by simpa only [bit,he] using hrow
    rw [he,hb,zero_mul,add_zero]
  · have hs : lower p r gamma+p-r=(lower p r gamma-r)+p := by omega
    have hb : (bit p r gamma+1)%2=0 := by
      rw [he,hs,Nat.add_mod,hodd] at hrow
      exact hrow
    have hbit := bit_lt p r gamma
    have hb1 : bit p r gamma=1 := by omega
    rw [he,hb1,one_mul]

/-- The odd ORIGINAL column uses the complementary quotient bit. -/
theorem col_node (p r gamma a : ℕ) (hp : 0<p) (hodd : p%2=1) (hg : gamma<p)
    (ha0 : r≤a) (ha1 : a<r+2*p) (hc : a%p=gamma) (hcol : (a-r)%2=1) :
    a=lower p r gamma+(1-bit p r gamma)*p := by
  have hl := lower_bounds p r gamma hp hg
  rcases two_candidates p r gamma a hp hg ha0 ha1 hc with he|he
  · have hb : bit p r gamma=1 := by simpa only [bit,he] using hcol
    rw [he,hb,Nat.sub_self,zero_mul,add_zero]
  · have hs : lower p r gamma+p-r=(lower p r gamma-r)+p := by omega
    have hb : (bit p r gamma+1)%2=1 := by
      rw [he,hs,Nat.add_mod,hodd] at hcol
      exact hcol
    have hbit := bit_lt p r gamma
    have hb0 : bit p r gamma=0 := by omega
    rw [he,hb0,Nat.sub_zero,one_mul]


/-- Inside a fixed common-count cell, odd residue displacement exchanges
the two original quotient profiles and even displacement preserves them. -/
theorem bit_transport (p r gamma delta : ℕ) (hp : 0<p) (hg : gamma<p) (hd : delta<p)
    (hgd : gamma≤delta) (hcount : count p r gamma=count p r delta) :
    bit p r delta=(bit p r gamma+(delta-gamma)%2)%2 := by
  have hl := (lower_bounds p r gamma hp hg).1
  have he : lower p r delta-r=(lower p r gamma-r)+(delta-gamma) := by
    unfold lower at hl ⊢
    rw [← hcount]
    omega
  change (lower p r delta-r)%2=((lower p r gamma-r)%2+(delta-gamma)%2)%2
  rw [he,Nat.add_mod]


/-- Canonical original nodes of all full balanced periods. -/
def rowProfile (p r gamma c : ℕ) : ℕ := lower p r gamma+(2*c+bit p r gamma)*p

def colProfile (p r gamma c : ℕ) : ℕ := lower p r gamma+(2*c+(1-bit p r gamma))*p

/-- The actual full-cycle row, not a replacement common spectral node. -/
theorem full_row_profile (p r gamma : ℕ) (hp : 0<p) (hodd : p%2=1) (hg : gamma<p)
    {n : ℕ} (c : Fin n) (i : Fin p)
    (hcolour : WrapCycles.row r p c i%p=gamma) :
    WrapCycles.row r p c i=rowProfile p r gamma c := by
  have hbase : (r+2*(i:ℕ))%p=gamma := by
    have he : WrapCycles.row r p c i=(r+2*(i:ℕ))+2*(c:ℕ)*p := by
      unfold WrapCycles.row
      ring
    rw [he,Nat.add_mul_mod_self_right] at hcolour
    exact hcolour
  have hn := row_node p r gamma (r+2*(i:ℕ)) hp hodd hg (by omega) (by omega) hbase (by omega)
  unfold WrapCycles.row rowProfile
  rw [show r+2*((c:ℕ)*p+(i:ℕ))=(r+2*(i:ℕ))+2*(c:ℕ)*p by ring,hn]
  ring

/-- The independently permuted full-cycle column has the complementary
quotient profile in that same original period. -/
theorem full_col_profile (p r gamma shift : ℕ) (hp : 0<p) (hodd : p%2=1) (hg : gamma<p)
    {n : ℕ} (c : Fin n) (i : Fin p)
    (hcolour : WrapCycles.col r p hp shift c i%p=gamma) :
    WrapCycles.col r p hp shift c i=colProfile p r gamma c := by
  let j := WrapCycles.shift p hp shift i
  have hbase : (r+2*(j:ℕ)+1)%p=gamma := by
    have he : WrapCycles.col r p hp shift c i=(r+2*(j:ℕ)+1)+2*(c:ℕ)*p := by
      unfold WrapCycles.col
      dsimp only [j]
      ring
    rw [he,Nat.add_mul_mod_self_right] at hcolour
    exact hcolour
  have hj := j.2
  have hn := col_node p r gamma (r+2*(j:ℕ)+1) hp hodd hg (by omega) (by omega) hbase (by omega)
  have he : WrapCycles.col r p hp shift c i=(r+2*(j:ℕ)+1)+2*(c:ℕ)*p := by
    unfold WrapCycles.col
    dsimp only [j]
    ring
  rw [he,hn]
  unfold colProfile
  ring

/-- Even joint-type transport preserves both independent original
profiles. The common count is the original common-node count. -/
theorem profile_even (p r gamma delta : ℕ) (hgd : gamma≤delta)
    (hcount : count p r gamma=count p r delta)
    (hbit : bit p r gamma=bit p r delta) (c : ℕ) :
    rowProfile p r delta c=rowProfile p r gamma c+(delta-gamma) ∧
    colProfile p r delta c=colProfile p r gamma c+(delta-gamma) := by
  have hl : lower p r delta=lower p r gamma+(delta-gamma) := by
    unfold lower
    rw [← hcount]
    omega
  unfold rowProfile colProfile
  rw [hl,← hbit]
  constructor <;> omega

/-- Odd joint-type transport exchanges the two actual original profiles.
This is why the mixed core transposes instead of becoming symmetric. -/
theorem profile_odd (p r gamma delta : ℕ) (hgd : gamma≤delta)
    (hcount : count p r gamma=count p r delta)
    (hbit : bit p r delta=1-bit p r gamma) (c : ℕ) :
    rowProfile p r delta c=colProfile p r gamma c+(delta-gamma) ∧
    colProfile p r delta c=rowProfile p r gamma c+(delta-gamma) := by
  have hl : lower p r delta=lower p r gamma+(delta-gamma) := by
    unfold lower
    rw [← hcount]
    omega
  have hb := bit_lt p r gamma
  have he : 1-(1-bit p r gamma)=bit p r gamma := by omega
  unfold rowProfile colProfile
  rw [hl,hbit,he]
  constructor <;> omega


section ActualFibres
variable (p : ℕ) [Fact p.Prime]

/-- Enumerate the ORIGINAL common fibre by its quotient, preserving the
actual common spectral coordinates. -/
noncomputable def commonEquiv (r : ℕ) (gamma : ZMod p) :
    Fin (count p r gamma.val) ≃ WrapFibreIndex.Common p (fun i:Fin r => (i:ℕ)) gamma where
  toFun i := ⟨⟨gamma.val+(i:ℕ)*p,
    (common_bound p r gamma.val i (Fact.out:p.Prime).pos (ZMod.val_lt gamma)).mpr i.2⟩,by simp⟩
  invFun a := ⟨(a.1:ℕ)/p,
    (common_bound p r gamma.val ((a.1:ℕ)/p) (Fact.out:p.Prime).pos (ZMod.val_lt gamma)).mp (by
      rw [← WrapFibreIndex.node_eq p (a.1:ℕ) gamma a.2]
      exact a.1.2)⟩
  left_inv i := by
    apply Fin.ext
    change (gamma.val+(i:ℕ)*p)/p=(i:ℕ)
    rw [Nat.add_mul_div_right _ _ (Fact.out:p.Prime).pos,Nat.div_eq_of_lt (ZMod.val_lt gamma),zero_add]
  right_inv a := by
    apply Subtype.ext
    apply Fin.ext
    exact (WrapFibreIndex.node_eq p (a.1:ℕ) gamma a.2).symm

noncomputable def colourSlot (r : ℕ) (hp2 : 2<p) (gamma : ZMod p) : Fin p :=
  (Equiv.ofBijective (WrapFibreCount.colour p r) (WrapFibreCount.colour_bijective p r hp2)).symm gamma

theorem colourSlot_spec (r : ℕ) (hp2 : 2<p) (gamma : ZMod p) :
    WrapFibreCount.colour p r (colourSlot p r hp2 gamma)=gamma :=
  (Equiv.ofBijective (WrapFibreCount.colour p r) (WrapFibreCount.colour_bijective p r hp2)).apply_symm_apply gamma

/-- The selected own fibre has exactly the actual full-cycle nodes;
residual balanced colours are excluded by the surplus arc geometry. -/
noncomputable def fullBalancedEquiv (r n e b d : ℕ) (hp2 : 2<p)
    (er : (Fin b ⊕ Fin d) ≃ Fin e) (gamma : ZMod p)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r er (Sum.inr i):ZMod p)≠gamma) :
    Fin n ≃ WrapFibreIndex.Balanced p (WrapPrefixCoreGeometry.xs p (n:=n) r er) gamma where
  toFun c := ⟨Sum.inl (c,colourSlot p r hp2 gamma),by
    unfold WrapPrefixCoreGeometry.xs
    rw [WrapPrefixGeometry.row_cycle,WrapFibreCount.full_colour,colourSlot_spec]⟩
  invFun a := match a with
    | ⟨Sum.inl (c,_),_⟩ => c
    | ⟨Sum.inr i,h⟩ => False.elim (hres i h)
  left_inv _ := rfl
  right_inv a := by
    rcases a with ⟨⟨c,i⟩|i,h⟩
    · apply Subtype.ext
      apply congrArg Sum.inl
      change (c,colourSlot p r hp2 gamma)=(c,i)
      apply Prod.ext
      · rfl
      · apply WrapFibreCount.colour_injective p r hp2
        unfold WrapPrefixCoreGeometry.xs at h
        rw [WrapPrefixGeometry.row_cycle,WrapFibreCount.full_colour] at h
        exact (colourSlot_spec p r hp2 gamma).trans h.symm
    · exact False.elim (hres i h)

/-- Bind the canonical quotient profile to the actual original row
selected by the fibre equivalence. -/
theorem fullBalanced_row (r n e b d : ℕ) (hp2 : 2<p) (hodd : p%2=1)
    (er : (Fin b ⊕ Fin d) ≃ Fin e) (gamma : ZMod p)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r er (Sum.inr i):ZMod p)≠gamma)
    (c : Fin n) :
    WrapPrefixCoreGeometry.xs p r er (fullBalancedEquiv p r n e b d hp2 er gamma hres c).1=
      rowProfile p r gamma.val c := by
  change r+2*(WrapPrefixGeometry.rowBorderEquiv er
    (Sum.inl (Sum.inl (c,colourSlot p r hp2 gamma))):ℕ)=_
  rw [WrapPrefixGeometry.row_cycle]
  apply full_row_profile p r gamma.val (Fact.out:p.Prime).pos hodd (ZMod.val_lt gamma) c
  have he : (WrapCycles.row r p c (colourSlot p r hp2 gamma):ZMod p)=gamma := by
    rw [WrapFibreCount.full_colour,colourSlot_spec]
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast] using hv

/-- The corresponding column retains its independent physical node
in that same original full period. -/
theorem fullBalanced_col (r n e b d shift : ℕ) (hp : p=2*shift+1) (hp2 : 2<p)
    (er ec : (Fin b ⊕ Fin d) ≃ Fin e) (gamma : ZMod p)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r er (Sum.inr i):ZMod p)≠gamma)
    (c : Fin n) :
    WrapPrefixCoreGeometry.ys p r (Fact.out:p.Prime).pos shift ec
      (fullBalancedEquiv p r n e b d hp2 er gamma hres c).1=colProfile p r gamma.val c := by
  change r+2*(WrapPrefixGeometry.colBorderEquiv (Fact.out:p.Prime).pos shift ec
    (Sum.inl (Sum.inl (c,colourSlot p r hp2 gamma))):ℕ)+1=_
  rw [WrapPrefixGeometry.col_cycle]
  apply full_col_profile p r gamma.val shift (Fact.out:p.Prime).pos (by omega) (ZMod.val_lt gamma) c
  have he : (WrapCycles.col r p (Fact.out:p.Prime).pos shift c (colourSlot p r hp2 gamma):ZMod p)=gamma := by
    rw [← WrapCycles.colour_eq r p shift hp c (colourSlot p r hp2 gamma),
      WrapFibreCount.full_colour,colourSlot_spec]
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast] using hv


/-- Canonical independent row/column enumeration of the ACTUAL whole
selected colour fibre, including exactly its original common nodes. -/
noncomputable def wholeEquiv (r n e b d : ℕ) (hp2 : 2<p)
    (er : (Fin b ⊕ Fin d) ≃ Fin e) (gamma : ZMod p)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r er (Sum.inr i):ZMod p)≠gamma) :
    (Fin (count p r gamma.val) ⊕ Fin n) ≃
      WrapFibreIndex.Whole p (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er) gamma :=
  (Equiv.sumCongr (commonEquiv p r gamma)
    (fullBalancedEquiv p r n e b d hp2 er gamma hres)).trans
      (Equiv.subtypeSum (p:=fun a => WrapFibreIndex.colour p (fun i:Fin r => (i:ℕ))
        (WrapPrefixCoreGeometry.xs p (n:=n) r er) a=gamma)).symm

theorem whole_row (r n e b d : ℕ) (hp2 : 2<p) (hodd : p%2=1)
    (er : (Fin b ⊕ Fin d) ≃ Fin e) (gamma : ZMod p)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r er (Sum.inr i):ZMod p)≠gamma)
    (i : Fin (count p r gamma.val) ⊕ Fin n) :
    Sum.elim (fun j:Fin r => (j:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er)
      (wholeEquiv p r n e b d hp2 er gamma hres i).1=
        Sum.elim (fun j:Fin (count p r gamma.val) => gamma.val+(j:ℕ)*p)
          (fun c:Fin n => rowProfile p r gamma.val c) i := by
  cases i with
  | inl i => rfl
  | inr i => exact fullBalanced_row p r n e b d hp2 hodd er gamma hres i

theorem whole_col (r n e b d shift : ℕ) (hp : p=2*shift+1) (hp2 : 2<p)
    (er ec : (Fin b ⊕ Fin d) ≃ Fin e) (gamma : ZMod p)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r er (Sum.inr i):ZMod p)≠gamma)
    (i : Fin (count p r gamma.val) ⊕ Fin n) :
    Sum.elim (fun j:Fin r => (j:ℕ))
      (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec)
      (wholeEquiv p r n e b d hp2 er gamma hres i).1=
        Sum.elim (fun j:Fin (count p r gamma.val) => gamma.val+(j:ℕ)*p)
          (fun c:Fin n => colProfile p r gamma.val c) i := by
  cases i with
  | inl i => rfl
  | inr i => exact fullBalanced_col p r n e b d shift hp hp2 er ec gamma hres i


/-- Exact matrix binding of the original whole colour block to the
canonical mixed profile. Original common spectral nodes stay common. -/
theorem whole_core (r n e b d shift q o : ℕ) (hp : p=2*shift+1) (hp2 : 2<p)
    (s u : CatalanCore.Uniform.Content.UFMoments.GaussLoc p)
    (er ec : (Fin b ⊕ Fin d) ≃ Fin e) (gamma : ZMod p)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r er (Sum.inr i):ZMod p)≠gamma) :
    (WrapFibreCore.core p q o s u (fun i:Fin r => (i:ℕ))
      (WrapPrefixCoreGeometry.xs p (n:=n) r er)
      (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec)).submatrix
        (fun i => (wholeEquiv p r n e b d hp2 er gamma hres i).1)
        (fun j => (wholeEquiv p r n e b d hp2 er gamma hres j).1)=
    WrapFibreCore.core p q o s u (fun i:Fin (count p r gamma.val) => gamma.val+(i:ℕ)*p)
      (fun c:Fin n => rowProfile p r gamma.val c) (fun c:Fin n => colProfile p r gamma.val c) := by
  classical
  have he (i j : Fin (count p r gamma.val) ⊕ Fin n) :
      WrapDeformedEntry.entry p q o u
        (Sum.elim (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er)
          (wholeEquiv p r n e b d hp2 er gamma hres i).1)
        (Sum.elim (fun i:Fin r => (i:ℕ))
          (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec)
          (wholeEquiv p r n e b d hp2 er gamma hres j).1)=
      WrapDeformedEntry.entry p q o u
        (Sum.elim (fun i:Fin (count p r gamma.val) => gamma.val+(i:ℕ)*p)
          (fun c:Fin n => rowProfile p r gamma.val c) i)
        (Sum.elim (fun i:Fin (count p r gamma.val) => gamma.val+(i:ℕ)*p)
          (fun c:Fin n => colProfile p r gamma.val c) j) := by
    rw [whole_row p r n e b d hp2 (by omega) er gamma hres i,
      whole_col p r n e b d shift hp hp2 er ec gamma hres j]
  ext i j
  simp only [WrapFibreCore.core,Matrix.submatrix_apply,Matrix.add_apply,Matrix.of_apply]
  rw [he]
  congr 1
  rcases i with i|i <;> rcases j with j|j
  · change WrapOwnCore.constants p s*(if (commonEquiv p r gamma i).1=(commonEquiv p r gamma j).1 then 1 else 0)=
      WrapOwnCore.constants p s*(if i=j then 1 else 0)
    have heq : (commonEquiv p r gamma i).1=(commonEquiv p r gamma j).1 ↔ i=j :=
      ⟨fun h => (commonEquiv p r gamma).injective (Subtype.ext h),fun h => by rw [h]⟩
    simp only [heq]
  · rfl
  · rfl
  · rfl


/-- Transfer the already-proved actual own-colour unit through the exact
original profile equivalence. -/
theorem whole_core_unit (r n e b d shift q o : ℕ) (hp : p=2*shift+1) (hp2 : 2<p)
    (s u : CatalanCore.Uniform.Content.UFMoments.GaussLoc p)
    (er ec : (Fin b ⊕ Fin d) ≃ Fin e) (gamma : ZMod p)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r er (Sum.inr i):ZMod p)≠gamma)
    (hu : IsUnit ((WrapFibreCore.core p q o s u (fun i:Fin r => (i:ℕ))
      (WrapPrefixCoreGeometry.xs p (n:=n) r er)
      (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec)).toSquareBlock
        (WrapFibreIndex.colour p (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er)) gamma).det) :
    IsUnit (WrapFibreCore.core p q o s u (fun i:Fin (count p r gamma.val) => gamma.val+(i:ℕ)*p)
      (fun c:Fin n => rowProfile p r gamma.val c) (fun c:Fin n => colProfile p r gamma.val c)).det := by
  rw [← whole_core p r n e b d shift q o hp hp2 s u er ec gamma hres]
  change IsUnit (((WrapFibreCore.core p q o s u (fun i:Fin r => (i:ℕ))
      (WrapPrefixCoreGeometry.xs p (n:=n) r er)
      (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec)).toSquareBlock
        (WrapFibreIndex.colour p (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er)) gamma).submatrix
          (wholeEquiv p r n e b d hp2 er gamma hres) (wholeEquiv p r n e b d hp2 er gamma hres)).det
  rw [Matrix.det_submatrix_equiv_self]
  exact hu

end ActualFibres

end CatalanCore.Uniform.Content.UFSimple.WrapJointProfile

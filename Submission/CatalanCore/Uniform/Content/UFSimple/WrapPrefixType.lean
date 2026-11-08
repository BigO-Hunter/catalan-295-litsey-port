module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapPrefixSource
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapJointProfile

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixType

variable (p : ℕ) [Fact p.Prime]

noncomputable def core (q o r k n gamma : ℕ) (s u : GaussLoc p) :=
  WrapFibreCore.core p q o s u (fun i:Fin k => gamma+(i:ℕ)*p)
    (fun c:Fin n => WrapJointProfile.rowProfile p r gamma c)
    (fun c:Fin n => WrapJointProfile.colProfile p r gamma c)

def rows (r k n gamma : ℕ) : Fin k ⊕ Fin n → ℕ :=
  Sum.elim (fun i:Fin k => gamma+(i:ℕ)*p) (fun c:Fin n => WrapJointProfile.rowProfile p r gamma c)

def cols (r k n gamma : ℕ) : Fin k ⊕ Fin n → ℕ :=
  Sum.elim (fun i:Fin k => gamma+(i:ℕ)*p) (fun c:Fin n => WrapJointProfile.colProfile p r gamma c)

noncomputable def spectral (k n : ℕ) (s : GaussLoc p) :
    Matrix (Fin k ⊕ Fin n) (Fin k ⊕ Fin n) (WrapDeform.Extension p) :=
  Matrix.fromBlocks (WrapOwnCore.constants p s • (1:Matrix (Fin k) (Fin k) (WrapDeform.Extension p))) 0 0 0

theorem core_entry (q o r k n gamma : ℕ) (s u : GaussLoc p) (i j : Fin k ⊕ Fin n) :
    core p q o r k n gamma s u i j=
      WrapDeformedEntry.entry p q o u (rows p r k n gamma i) (cols p r k n gamma j)+spectral p k n s i j := rfl

theorem rows_colour (r k n gamma : ℕ) (i : Fin k ⊕ Fin n) :
    (rows p r k n gamma i:ZMod p)=(gamma:ZMod p) := by
  cases i with
  | inl i => simp [rows]
  | inr i => simp [rows,WrapJointProfile.rowProfile,WrapJointProfile.lower]

theorem cols_colour (r k n gamma : ℕ) (i : Fin k ⊕ Fin n) :
    (cols p r k n gamma i:ZMod p)=(gamma:ZMod p) := by
  cases i with
  | inl i => simp [cols]
  | inr i => simp [cols,WrapJointProfile.colProfile,WrapJointProfile.lower]

/-- The actual original profiles either translate or exchange axes.
The common spectral coordinates are preserved in both cases. -/
theorem profile_even (r k n gamma delta : ℕ) (hgd : gamma≤delta)
    (hcount : WrapJointProfile.count p r gamma=WrapJointProfile.count p r delta)
    (hbit : WrapJointProfile.bit p r gamma=WrapJointProfile.bit p r delta) :
    (∀ i,rows p r k n delta i=rows p r k n gamma i+(delta-gamma)) ∧
    (∀ i,cols p r k n delta i=cols p r k n gamma i+(delta-gamma)) := by
  constructor <;> intro i <;> cases i with
  | inl i => simp only [rows,cols,Sum.elim_inl]; omega
  | inr i => first
      | exact (WrapJointProfile.profile_even p r gamma delta hgd hcount hbit i).1
      | exact (WrapJointProfile.profile_even p r gamma delta hgd hcount hbit i).2

theorem profile_odd (r k n gamma delta : ℕ) (hgd : gamma≤delta)
    (hcount : WrapJointProfile.count p r gamma=WrapJointProfile.count p r delta)
    (hbit : WrapJointProfile.bit p r delta=1-WrapJointProfile.bit p r gamma) :
    (∀ i,rows p r k n delta i=cols p r k n gamma i+(delta-gamma)) ∧
    (∀ i,cols p r k n delta i=rows p r k n gamma i+(delta-gamma)) := by
  constructor <;> intro i <;> cases i with
  | inl i => simp only [rows,cols,Sum.elim_inl]; omega
  | inr i => first
      | exact (WrapJointProfile.profile_odd p r gamma delta hgd hcount hbit i).1
      | exact (WrapJointProfile.profile_odd p r gamma delta hgd hcount hbit i).2

theorem spectral_transpose (k n : ℕ) (s : GaussLoc p) : (spectral p k n s)ᵀ=spectral p k n s := by
  ext i j
  cases i <;> cases j <;> simp [spectral,Matrix.transpose_apply,Matrix.one_apply,eq_comm]

/-- An even actual joint-type shift supplies every premise of the
already-proved actual own-block transport, including original loads. -/
theorem even_transport (q o r k n gamma delta t : ℕ) (s u : GaussLoc p)
    (hgd : gamma≤delta) (hcount : WrapJointProfile.count p r gamma=WrapJointProfile.count p r delta)
    (hbit : WrapJointProfile.bit p r gamma=WrapJointProfile.bit p r delta)
    (htcol : (t:ZMod p)=(gamma:ZMod p))
    (hw : ∀ h∈Icc 1 (delta-gamma),res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0)
    (hQ0 : IsUnit (core p q o r k n gamma s u).det)
    (hQ1 : IsUnit (core p q o r k n delta s u).det) (direction : WrapDeform.Extension p)
    (hz : (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-direction)-
      (fun i => WrapDeformedEntry.entry p q o u t (cols p r k n gamma i)) ⬝ᵥ
        (core p q o r k n gamma s u)⁻¹ *ᵥ
          (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows p r k n gamma i)-direction)=0) :
    ∃ e : WrapDeform.Extension p,
      (WrapOwnCore.constants p u*WrapEntryRelation.load p q o (t+(delta-gamma))-direction)-
        (fun i => WrapDeformedEntry.entry p q o u (t+(delta-gamma)) (cols p r k n delta i)) ⬝ᵥ
          (core p q o r k n delta s u)⁻¹ *ᵥ
            (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows p r k n delta i)-direction)=
      (WrapOwnCore.constants p u*∑ h∈Icc 1 (delta-gamma),WrapPrefixSource.regular p q o (t+h))*
        (1-∑ i,((fun j => WrapDeformedEntry.entry p q o u t (cols p r k n gamma j)) ᵥ*
          (core p q o r k n gamma s u)⁻¹) i)*WrapDeform.uniformizer p+WrapDeform.uniformizer p^2*e := by
  have hp := profile_even p r k n gamma delta hgd hcount hbit
  have he1 : ∀ i j,core p q o r k n delta s u i j=
      WrapDeformedEntry.entry p q o u (rows p r k n gamma i+(delta-gamma))
        (cols p r k n gamma j+(delta-gamma))+spectral p k n s i j := by
    intro i j
    rw [core_entry,hp.1 i,hp.2 j]
  obtain ⟨e,he⟩ := WrapPrefixSource.actual_own_transport p q o t (delta-gamma) u
    (rows p r k n gamma) (cols p r k n gamma) (spectral p k n s)
    (fun i => (rows_colour p r k n gamma i).trans htcol.symm)
    (fun i => (cols_colour p r k n gamma i).trans htcol.symm) hw
    (core p q o r k n gamma s u) (core p q o r k n delta s u)
    (core_entry p q o r k n gamma s u) he1 hQ0 hQ1 direction hz
  refine ⟨e,?_⟩
  simpa only [← hp.1,← hp.2] using he


/-- Transposing the actual mixed core exchanges both physical node
families while preserving the original common spectral diagonal. -/
theorem core_transpose_entry (q o r k n gamma : ℕ) (s u : GaussLoc p) (i j : Fin k ⊕ Fin n) :
    (core p q o r k n gamma s u)ᵀ i j=
      WrapDeformedEntry.entry p q o u (cols p r k n gamma i) (rows p r k n gamma j)+spectral p k n s i j := by
  have hs := congrArg (fun M : Matrix (Fin k ⊕ Fin n) (Fin k ⊕ Fin n) (WrapDeform.Extension p) => M i j)
    (spectral_transpose p k n s)
  change spectral p k n s j i=spectral p k n s i j at hs
  rw [Matrix.transpose_apply,core_entry,WrapEntryRelation.entry_symm,hs]

/-- Odd original colour displacement transposes the anchored core and
exchanges its actual loads. No symmetry premise is introduced. -/
theorem odd_transport (q o r k n gamma delta t : ℕ) (s u : GaussLoc p)
    (hgd : gamma≤delta) (hcount : WrapJointProfile.count p r gamma=WrapJointProfile.count p r delta)
    (hbit : WrapJointProfile.bit p r delta=1-WrapJointProfile.bit p r gamma)
    (htcol : (t:ZMod p)=(gamma:ZMod p))
    (hw : ∀ h∈Icc 1 (delta-gamma),res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0)
    (hQ0 : IsUnit (core p q o r k n gamma s u).det)
    (hQ1 : IsUnit (core p q o r k n delta s u).det) (direction : WrapDeform.Extension p)
    (hz : (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-direction)-
      (fun i => WrapDeformedEntry.entry p q o u t (rows p r k n gamma i)) ⬝ᵥ
        (core p q o r k n gamma s u)ᵀ⁻¹ *ᵥ
          (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (cols p r k n gamma i)-direction)=0) :
    ∃ e : WrapDeform.Extension p,
      (WrapOwnCore.constants p u*WrapEntryRelation.load p q o (t+(delta-gamma))-direction)-
        (fun i => WrapDeformedEntry.entry p q o u (t+(delta-gamma)) (cols p r k n delta i)) ⬝ᵥ
          (core p q o r k n delta s u)⁻¹ *ᵥ
            (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows p r k n delta i)-direction)=
      (WrapOwnCore.constants p u*∑ h∈Icc 1 (delta-gamma),WrapPrefixSource.regular p q o (t+h))*
        (1-∑ i,((fun j => WrapDeformedEntry.entry p q o u t (rows p r k n gamma j)) ᵥ*
          (core p q o r k n gamma s u)ᵀ⁻¹) i)*WrapDeform.uniformizer p+WrapDeform.uniformizer p^2*e := by
  have hp := profile_odd p r k n gamma delta hgd hcount hbit
  have he1 : ∀ i j,core p q o r k n delta s u i j=
      WrapDeformedEntry.entry p q o u (cols p r k n gamma i+(delta-gamma))
        (rows p r k n gamma j+(delta-gamma))+spectral p k n s i j := by
    intro i j
    rw [core_entry,hp.1 i,hp.2 j]
  have hQT : IsUnit (core p q o r k n gamma s u)ᵀ.det := by
    rwa [Matrix.det_transpose]
  obtain ⟨e,he⟩ := WrapPrefixSource.actual_own_transport p q o t (delta-gamma) u
    (cols p r k n gamma) (rows p r k n gamma) (spectral p k n s)
    (fun i => (cols_colour p r k n gamma i).trans htcol.symm)
    (fun i => (rows_colour p r k n gamma i).trans htcol.symm) hw
    (core p q o r k n gamma s u)ᵀ (core p q o r k n delta s u)
    (core_transpose_entry p q o r k n gamma s u) he1 hQT hQ1 direction hz
  refine ⟨e,?_⟩
  simpa only [← hp.1,← hp.2] using he


def rowQuot (r k n gamma : ℕ) (i : Fin n) : ℕ := k+2*(i:ℕ)+WrapJointProfile.bit p r gamma

def colQuot (r k n gamma : ℕ) (i : Fin n) : ℕ := k+2*(i:ℕ)+(1-WrapJointProfile.bit p r gamma)

theorem row_profile_eq (r k n gamma : ℕ) (hk : WrapJointProfile.count p r gamma=k) (i : Fin n) :
    WrapJointProfile.rowProfile p r gamma i=gamma+rowQuot p r k n gamma i*p := by
  unfold WrapJointProfile.rowProfile WrapJointProfile.lower rowQuot
  rw [hk]
  ring

theorem col_profile_eq (r k n gamma : ℕ) (hk : WrapJointProfile.count p r gamma=k) (i : Fin n) :
    WrapJointProfile.colProfile p r gamma i=gamma+colQuot p r k n gamma i*p := by
  unfold WrapJointProfile.colProfile WrapJointProfile.lower colQuot
  rw [hk]
  ring

/-- Actual original profile geometry constructs the arithmetic hypothesis
used by the existing Cauchy pivot and reference proofs. -/
theorem profile_hyp (q o root j0 r k n gamma m N : ℕ)
    (hcount : WrapJointProfile.count p r gamma=k)
    (hq0 : 0<q) (hqp : q<p) (hq2 : 2≤q) (hoq : o<q) (hroot0 : 0<root) (hrootp : root≤p)
    (hg : gamma<p) (hroot : q*root=j0*p+o) (hsize : 2*m≤N) (hN : q*N<p*p)
    (hn : 1≤n) (hb : n≤m/p+1)
    (hx : ∀ i:Fin n,WrapJointProfile.rowProfile p r gamma i<N)
    (hy : ∀ i:Fin n,WrapJointProfile.colProfile p r gamma i<N) :
    WrapBalancedResidue.Hyp p q o root j0 gamma m N n
      (rowQuot p r k n gamma) (colQuot p r k n gamma) := by
  refine {
    hq0 := hq0
    hqp := hqp
    hq2 := hq2
    hoq := hoq
    hk0 := hroot0
    hk := hrootp
    hg := hg
    hroot := hroot
    hsize := hsize
    hN := hN
    hb := hb
    hb0 := hn
    hx := ?_
    hy := ?_
    hxN := ?_
    hyN := ?_
    hxy := ?_
  }
  · intro i j he
    apply Fin.ext
    unfold rowQuot at he
    omega
  · intro i j he
    apply Fin.ext
    unfold colQuot at he
    omega
  · intro i
    rw [← row_profile_eq p r k n gamma hcount i]
    exact hx i
  · intro i
    rw [← col_profile_eq p r k n gamma hcount i]
    exact hy i
  · intro i j he
    have hbit := WrapJointProfile.bit_lt p r gamma
    unfold rowQuot colQuot at he
    omega

/-- The canonical profile core is literally the existing actual own
core, with common spectral coordinates and independent balanced axes. -/
theorem actual_core {q o root j0 r k n gamma m N : ℕ}
    (H : WrapBalancedResidue.Hyp p q o root j0 gamma m N n
      (rowQuot p r k n gamma) (colQuot p r k n gamma))
    (hcount : WrapJointProfile.count p r gamma=k) (s u : GaussLoc p) :
    WrapOwnCore.actual H s u (fun i:Fin k => (i:ℕ))=core p q o r k n gamma s u := by
  classical
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · change WrapOwnCore.constants p s*(if i=j then 1 else 0)+
      WrapDeformedEntry.entry p q o u (gamma+(i:ℕ)*p) (gamma+(j:ℕ)*p)=
      WrapDeformedEntry.entry p q o u (gamma+(i:ℕ)*p) (gamma+(j:ℕ)*p)+
        WrapOwnCore.constants p s*(if i=j then 1 else 0)
    ring
  · change WrapDeformedEntry.entry p q o u (gamma+(i:ℕ)*p) (gamma+colQuot p r k n gamma j*p)=
      WrapDeformedEntry.entry p q o u (gamma+(i:ℕ)*p) (WrapJointProfile.colProfile p r gamma j)+0
    rw [col_profile_eq p r k n gamma hcount j,add_zero]
  · change WrapDeformedEntry.entry p q o u (gamma+rowQuot p r k n gamma i*p) (gamma+(j:ℕ)*p)=
      WrapDeformedEntry.entry p q o u (WrapJointProfile.rowProfile p r gamma i) (gamma+(j:ℕ)*p)+0
    rw [row_profile_eq p r k n gamma hcount i,add_zero]
  · change WrapDeformedEntry.entry p q o u (gamma+rowQuot p r k n gamma i*p) (gamma+colQuot p r k n gamma j*p)=
      WrapDeformedEntry.entry p q o u (WrapJointProfile.rowProfile p r gamma i) (WrapJointProfile.colProfile p r gamma j)+0
    rw [row_profile_eq p r k n gamma hcount i,col_profile_eq p r k n gamma hcount j,add_zero]

/-- The actual profile unit is derived from arithmetic/node geometry,
without assuming a pivot, reference or source unit. -/
theorem core_unit {q o root j0 r k n gamma m N : ℕ}
    (H : WrapBalancedResidue.Hyp p q o root j0 gamma m N n
      (rowQuot p r k n gamma) (colQuot p r k n gamma))
    (hcount : WrapJointProfile.count p r gamma=k) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hc : ∀ i:Fin k,gamma+(i:ℕ)*p<N) : IsUnit (core p q o r k n gamma s u).det := by
  have hgN : gamma<N := by have hh := H.hxN ⟨0,H.hb0⟩; omega
  let J := (N-1-gamma)/p
  have hJ := WrapFibreCore.quotient_cap p gamma N hgN
  have hcJ : ∀ i:Fin k,(i:ℕ)≤J := fun i => WrapFibreCore.le_quotient_cap p gamma N _ (hc i)
  have hxJ : ∀ i:Fin n,rowQuot p r k n gamma i≤J := fun i =>
    WrapFibreCore.le_quotient_cap p gamma N _ (H.hxN i)
  have hyJ : ∀ i:Fin n,colQuot p r k n gamma i≤J := fun i =>
    WrapFibreCore.le_quotient_cap p gamma N _ (H.hyN i)
  rw [← actual_core p H hcount s u]
  exact WrapOwnCore.unit H s u hs hu huc (fun i:Fin k => (i:ℕ)) J hJ hcJ hxJ hyJ


/-- Exact shared anchor direction after exchanging the two original
own-fibre axes. Units are derived from the original arithmetic theorem. -/
theorem direction_swap {q o root j0 gamma m N b : ℕ} {x y : Fin b → ℕ}
    (H : WrapBalancedResidue.Hyp p q o root j0 gamma m N b x y)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (c : ι → ℕ)
    (J : ℕ) (hJ : gamma+J*p<N) (hc : ∀ i,c i≤J) (hx : ∀ i,x i≤J) (hy : ∀ i,y i≤J)
    (t : ℕ) (ht : t≤J) (hxt : ∀ i,x i≠t) (hyt : ∀ i,y i≠t) :
    WrapOwnLoads.direction (WrapOwnTranspose.swap H) s u c t=WrapOwnLoads.direction H s u c t := by
  rw [WrapOwnLoads.shared_direction H s u hs hu huc c J hJ hc hx hy t ht hxt hyt]
  unfold WrapOwnLoads.direction
  have hl : WrapOwnLoads.load (WrapOwnTranspose.swap H) u t=WrapOwnLoads.load H u t := rfl
  have hr : WrapOwnLoads.rowLoad (WrapOwnTranspose.swap H) u c=WrapOwnLoads.colLoad H u c := rfl
  rw [hl,hr,WrapOwnTranspose.actual_transpose H,WrapOwnTranspose.swap_sigma H]
  rw [← WrapTransport.response_transpose (WrapOwnCore.actual H s u c)
      (WrapOwnTranspose.colSigma H u c t) (WrapOwnLoads.colLoad H u c),
    ← WrapTransport.response_transpose (WrapOwnCore.actual H s u c)
      (WrapOwnTranspose.colSigma H u c t) (1:ι ⊕ Fin b → WrapDeform.Extension p)]

section ProfileAnchor
variable {q o root j0 r k n gamma m N : ℕ}
variable (H : WrapBalancedResidue.Hyp p q o root j0 gamma m N n
  (rowQuot p r k n gamma) (colQuot p r k n gamma))
variable (hcount : WrapJointProfile.count p r gamma=k)

include H hcount

theorem sigma_profile (u : GaussLoc p) (t : ℕ) :
    WrapOwnReference.sigma H u (fun i:Fin k => (i:ℕ)) t=
      fun i => WrapDeformedEntry.entry p q o u (gamma+t*p) (cols p r k n gamma i) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    change WrapDeformedEntry.entry p q o u (gamma+t*p) (gamma+colQuot p r k n gamma i*p)=_
    rw [← col_profile_eq p r k n gamma hcount i]
    rfl

theorem sigma_profile_swap (u : GaussLoc p) (t : ℕ) :
    WrapOwnReference.sigma (WrapOwnTranspose.swap H) u (fun i:Fin k => (i:ℕ)) t=
      fun i => WrapDeformedEntry.entry p q o u (gamma+t*p) (rows p r k n gamma i) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    change WrapDeformedEntry.entry p q o u (gamma+t*p) (gamma+rowQuot p r k n gamma i*p)=_
    rw [← row_profile_eq p r k n gamma hcount i]
    rfl

theorem load_profile (u : GaussLoc p) (i : Fin k ⊕ Fin n) :
    WrapOwnLoads.rowLoad H u (fun i:Fin k => (i:ℕ)) i=
      WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows p r k n gamma i) := by
  cases i with
  | inl i => rfl
  | inr i =>
    change WrapOwnCore.constants p u*WrapEntryRelation.load p q o (gamma+rowQuot p r k n gamma i*p)=_
    rw [← row_profile_eq p r k n gamma hcount i]
    rfl

theorem load_profile_swap (u : GaussLoc p) (i : Fin k ⊕ Fin n) :
    WrapOwnLoads.rowLoad (WrapOwnTranspose.swap H) u (fun i:Fin k => (i:ℕ)) i=
      WrapOwnCore.constants p u*WrapEntryRelation.load p q o (cols p r k n gamma i) := by
  cases i with
  | inl i => rfl
  | inr i =>
    change WrapOwnCore.constants p u*WrapEntryRelation.load p q o (gamma+colQuot p r k n gamma i*p)=_
    rw [← col_profile_eq p r k n gamma hcount i]
    rfl

/-- Original arithmetic constructs a direction annihilating BOTH
independent own responses at the actual first surplus node. -/
theorem anchor (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hc : ∀ i:Fin k,gamma+(i:ℕ)*p<N) (ht : gamma+(k+2*n)*p<N) :
    ∃ direction : WrapDeform.Extension p,
      ((WrapOwnCore.constants p u*WrapEntryRelation.load p q o (gamma+(k+2*n)*p)-direction)-
        (fun i => WrapDeformedEntry.entry p q o u (gamma+(k+2*n)*p) (cols p r k n gamma i)) ⬝ᵥ
          (core p q o r k n gamma s u)⁻¹ *ᵥ
            (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows p r k n gamma i)-direction)=0) ∧
      ((WrapOwnCore.constants p u*WrapEntryRelation.load p q o (gamma+(k+2*n)*p)-direction)-
        (fun i => WrapDeformedEntry.entry p q o u (gamma+(k+2*n)*p) (rows p r k n gamma i)) ⬝ᵥ
          (core p q o r k n gamma s u)ᵀ⁻¹ *ᵥ
            (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (cols p r k n gamma i)-direction)=0) ∧
      IsUnit (1-(fun i => WrapDeformedEntry.entry p q o u (gamma+(k+2*n)*p) (cols p r k n gamma i)) ⬝ᵥ
        (core p q o r k n gamma s u)⁻¹ *ᵥ 1) ∧
      IsUnit (1-(fun i => WrapDeformedEntry.entry p q o u (gamma+(k+2*n)*p) (rows p r k n gamma i)) ⬝ᵥ
        (core p q o r k n gamma s u)ᵀ⁻¹ *ᵥ 1) := by
  have hgN : gamma<N := by omega
  let J := (N-1-gamma)/p
  have hJ := WrapFibreCore.quotient_cap p gamma N hgN
  have hcJ : ∀ i:Fin k,(i:ℕ)≤J := fun i => WrapFibreCore.le_quotient_cap p gamma N _ (hc i)
  have hxJ : ∀ i:Fin n,rowQuot p r k n gamma i≤J := fun i =>
    WrapFibreCore.le_quotient_cap p gamma N _ (H.hxN i)
  have hyJ : ∀ i:Fin n,colQuot p r k n gamma i≤J := fun i =>
    WrapFibreCore.le_quotient_cap p gamma N _ (H.hyN i)
  have htJ : k+2*n≤J := WrapFibreCore.le_quotient_cap p gamma N _ ht
  have hx : ∀ i:Fin n,rowQuot p r k n gamma i≠k+2*n := by
    intro i
    have hi := i.2
    have hb := WrapJointProfile.bit_lt p r gamma
    unfold rowQuot
    omega
  have hy : ∀ i:Fin n,colQuot p r k n gamma i≠k+2*n := by
    intro i
    have hi := i.2
    have hb := WrapJointProfile.bit_lt p r gamma
    unfold colQuot
    omega
  have hB := WrapOwnReference.unit H s u hs hu huc (fun i:Fin k => (i:ℕ)) J hJ hcJ hxJ hyJ
    (k+2*n) htJ hx hy
  have hBS := WrapOwnReference.unit (WrapOwnTranspose.swap H) s u hs hu huc
    (fun i:Fin k => (i:ℕ)) J hJ hcJ hyJ hxJ (k+2*n) htJ hy hx
  have hz := WrapOwnLoads.direction_zero H s u (fun i:Fin k => (i:ℕ)) (k+2*n) hB
  have hzS := WrapOwnLoads.direction_zero (WrapOwnTranspose.swap H) s u (fun i:Fin k => (i:ℕ)) (k+2*n) hBS
  have hd := direction_swap p H s u hs hu huc (fun i:Fin k => (i:ℕ)) J hJ hcJ hxJ hyJ (k+2*n) htJ hx hy
  rw [hd] at hzS
  refine ⟨WrapOwnLoads.direction H s u (fun i:Fin k => (i:ℕ)) (k+2*n),?_,?_,?_,?_⟩
  · rw [sigma_profile p H hcount,actual_core p H hcount] at hz
    simp_rw [load_profile p H hcount] at hz
    exact hz
  · rw [sigma_profile_swap p H hcount,WrapOwnTranspose.actual_transpose H,
      actual_core p H hcount] at hzS
    simp_rw [load_profile_swap p H hcount] at hzS
    exact hzS

  · rw [sigma_profile p H hcount,actual_core p H hcount] at hB
    exact hB
  · rw [sigma_profile_swap p H hcount,WrapOwnTranspose.actual_transpose H,
      actual_core p H hcount] at hBS
    exact hBS

end ProfileAnchor


/-- Reduction of an inverse response depends only on the reduced matrix
and independent loads, provided the original determinants are units. -/
theorem response_map_congr {R K α : Type*} [CommRing R] [Field K]
    [Fintype α] [DecidableEq α] (f : R →+* K)
    (Q Q' : Matrix α α R) (hQ : IsUnit Q.det) (hQ' : IsUnit Q'.det)
    (yR yC yR' yC' : α → R) (hm : Q.map f=Q'.map f)
    (hr : ∀ i,f (yR i)=f (yR' i)) (hc : ∀ i,f (yC i)=f (yC' i)) :
    f (yC ⬝ᵥ Q⁻¹ *ᵥ yR)=f (yC' ⬝ᵥ Q'⁻¹ *ᵥ yR') := by
  have hi : Q⁻¹.map f=Q'⁻¹.map f := by
    rw [← map_inv_of_unit f Q hQ,← map_inv_of_unit f Q' hQ',hm]
  simp only [dotProduct,mulVec,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he := congrArg (fun M : Matrix α α K => M i j) hi
  change f (Q⁻¹ i j)=f (Q'⁻¹ i j) at he
  rw [he,hr]

theorem reference_map_congr {R K α : Type*} [CommRing R] [Field K]
    [Fintype α] [DecidableEq α] (f : R →+* K)
    (Q Q' : Matrix α α R) (hQ : IsUnit Q.det) (hQ' : IsUnit Q'.det)
    (s s' : α → R) (hm : Q.map f=Q'.map f) (hs : ∀ i,f (s i)=f (s' i)) :
    f (1-s ⬝ᵥ Q⁻¹ *ᵥ 1)=f (1-s' ⬝ᵥ Q'⁻¹ *ᵥ 1) := by
  rw [map_sub,map_sub,map_one]
  exact congrArg (fun z : K => 1-z) (response_map_congr f Q Q' hQ hQ' 1 s 1 s' hm (fun _ => rfl) hs)


theorem residue_square (a b : WrapDeform.Extension p)
    (h : WrapDeform.uniformizer p^2∣a-b) : WrapDeform.residue p a=WrapDeform.residue p b := by
  obtain ⟨z,hz⟩ := h
  have hp : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have he := congrArg (WrapDeform.residue p) hz
  simp only [map_sub,map_mul,map_pow,hp,zero_pow (by decide : (2:ℕ)≠0),zero_mul] at he
  exact sub_eq_zero.mp he

/-- Actual entry reduction under regular original-node translation. -/
theorem entry_residue_shift (q o a b t d : ℕ) (u : GaussLoc p)
    (ha : (a:ZMod p)=(t:ZMod p)) (hb : (b:ZMod p)=(t:ZMod p))
    (hw : ∀ h∈Icc 1 d,res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0) :
    WrapDeform.residue p (WrapDeformedEntry.entry p q o u (a+d) (b+d))=
      WrapDeform.residue p (WrapDeformedEntry.entry p q o u a b) :=
  residue_square p _ _ (WrapPrefixSource.entry_shift_congr p q o a b d u (ha.trans hb.symm)
    (WrapPrefixSource.regular_window_of_colour p q o a t d ha hw)
    (WrapPrefixSource.regular_window_of_colour p q o b t d hb hw))

/-- Actual load reduction under a regular original-node translation. -/
theorem load_residue_shift (q o a t d : ℕ) (u : GaussLoc p)
    (ha : (a:ZMod p)=(t:ZMod p))
    (hw : ∀ h∈Icc 1 d,res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0) :
    WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o (a+d))=
      WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o a) := by
  have he := congrArg (WrapDeform.residue p) (WrapPrefixSource.load_shift_factor p q o a d u
    (WrapPrefixSource.regular_window_of_colour p q o a t d ha hw))
  have hp : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  simp only [map_mul,map_sub,hp,zero_mul] at he
  rw [map_mul,map_mul]
  linear_combination he

section ReducedTransport
variable {q o r k n gamma delta t : ℕ}
variable (s u : GaussLoc p)
variable (hgd : gamma≤delta)
variable (hcount : WrapJointProfile.count p r gamma=WrapJointProfile.count p r delta)
variable (htcol : (t:ZMod p)=(gamma:ZMod p))
variable (hw : ∀ h∈Icc 1 (delta-gamma),res p ((t+h:ℕ):GaussLoc p)≠0 ∧
  res p (WrapIncrement.argument p q o (t+h))≠0)
include hgd hcount htcol hw

theorem core_map_even (hbit : WrapJointProfile.bit p r gamma=WrapJointProfile.bit p r delta) :
    (core p q o r k n delta s u).map (WrapDeform.residue p)=
      (core p q o r k n gamma s u).map (WrapDeform.residue p) := by
  have hp := profile_even p r k n gamma delta hgd hcount hbit
  ext i j
  simp only [Matrix.map_apply,core_entry,map_add]
  rw [hp.1 i,hp.2 j,entry_residue_shift p q o _ _ t (delta-gamma) u
    ((rows_colour p r k n gamma i).trans htcol.symm)
    ((cols_colour p r k n gamma j).trans htcol.symm) hw]

theorem core_map_odd (hbit : WrapJointProfile.bit p r delta=1-WrapJointProfile.bit p r gamma) :
    (core p q o r k n delta s u).map (WrapDeform.residue p)=
      (core p q o r k n gamma s u)ᵀ.map (WrapDeform.residue p) := by
  have hp := profile_odd p r k n gamma delta hgd hcount hbit
  ext i j
  simp only [Matrix.map_apply,core_entry,core_transpose_entry,map_add]
  rw [hp.1 i,hp.2 j,entry_residue_shift p q o _ _ t (delta-gamma) u
    ((cols_colour p r k n gamma i).trans htcol.symm)
    ((rows_colour p r k n gamma j).trans htcol.symm) hw]

theorem sigma_map_even (hbit : WrapJointProfile.bit p r gamma=WrapJointProfile.bit p r delta)
    (i : Fin k ⊕ Fin n) :
    WrapDeform.residue p (WrapDeformedEntry.entry p q o u (t+(delta-gamma)) (cols p r k n delta i))=
      WrapDeform.residue p (WrapDeformedEntry.entry p q o u t (cols p r k n gamma i)) := by
  rw [(profile_even p r k n gamma delta hgd hcount hbit).2 i]
  exact entry_residue_shift p q o t _ t (delta-gamma) u rfl
    ((cols_colour p r k n gamma i).trans htcol.symm) hw

theorem sigma_map_odd (hbit : WrapJointProfile.bit p r delta=1-WrapJointProfile.bit p r gamma)
    (i : Fin k ⊕ Fin n) :
    WrapDeform.residue p (WrapDeformedEntry.entry p q o u (t+(delta-gamma)) (cols p r k n delta i))=
      WrapDeform.residue p (WrapDeformedEntry.entry p q o u t (rows p r k n gamma i)) := by
  rw [(profile_odd p r k n gamma delta hgd hcount hbit).2 i]
  exact entry_residue_shift p q o t _ t (delta-gamma) u rfl
    ((rows_colour p r k n gamma i).trans htcol.symm) hw

end ReducedTransport


section ReducedResponses
variable {q o r k n gamma delta t : ℕ}
variable (s u : GaussLoc p)
variable (hgd : gamma≤delta)
variable (hcount : WrapJointProfile.count p r gamma=WrapJointProfile.count p r delta)
variable (htcol : (t:ZMod p)=(gamma:ZMod p))
variable (hw : ∀ h∈Icc 1 (delta-gamma),res p ((t+h:ℕ):GaussLoc p)≠0 ∧
  res p (WrapIncrement.argument p q o (t+h))≠0)
variable (hQ0 : IsUnit (core p q o r k n gamma s u).det)
variable (hQ1 : IsUnit (core p q o r k n delta s u).det)
include hgd hcount htcol hw hQ0 hQ1

theorem reference_even (hbit : WrapJointProfile.bit p r gamma=WrapJointProfile.bit p r delta) :
    WrapDeform.residue p (1-(fun i => WrapDeformedEntry.entry p q o u (t+(delta-gamma))
      (cols p r k n delta i)) ⬝ᵥ (core p q o r k n delta s u)⁻¹ *ᵥ 1)=
    WrapDeform.residue p (1-(fun i => WrapDeformedEntry.entry p q o u t
      (cols p r k n gamma i)) ⬝ᵥ (core p q o r k n gamma s u)⁻¹ *ᵥ 1) := by
  exact reference_map_congr (WrapDeform.residue p) _ _ hQ1 hQ0 _ _
    (core_map_even p s u hgd hcount htcol hw hbit)
    (sigma_map_even p u hgd hcount htcol hw hbit)

theorem reference_odd (hbit : WrapJointProfile.bit p r delta=1-WrapJointProfile.bit p r gamma) :
    WrapDeform.residue p (1-(fun i => WrapDeformedEntry.entry p q o u (t+(delta-gamma))
      (cols p r k n delta i)) ⬝ᵥ (core p q o r k n delta s u)⁻¹ *ᵥ 1)=
    WrapDeform.residue p (1-(fun i => WrapDeformedEntry.entry p q o u t
      (rows p r k n gamma i)) ⬝ᵥ (core p q o r k n gamma s u)ᵀ⁻¹ *ᵥ 1) := by
  have hQT : IsUnit (core p q o r k n gamma s u)ᵀ.det := by rwa [Matrix.det_transpose]
  exact reference_map_congr (WrapDeform.residue p) _ _ hQ1 hQT _ _
    (core_map_odd p s u hgd hcount htcol hw hbit)
    (sigma_map_odd p u hgd hcount htcol hw hbit)

/-- The actual mixed own moment is constant on an even joint-type
translation, in the fixed original anchor direction. -/
theorem moment_even (hbit : WrapJointProfile.bit p r gamma=WrapJointProfile.bit p r delta)
    (direction : WrapDeform.Extension p) :
    WrapDeform.residue p ((fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (cols p r k n delta i)-direction) ⬝ᵥ (core p q o r k n delta s u)⁻¹ *ᵥ
        (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows p r k n delta i)-direction))=
    WrapDeform.residue p ((fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (cols p r k n gamma i)-direction) ⬝ᵥ (core p q o r k n gamma s u)⁻¹ *ᵥ
        (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows p r k n gamma i)-direction)) := by
  have hp := profile_even p r k n gamma delta hgd hcount hbit
  apply response_map_congr (WrapDeform.residue p) _ _ hQ1 hQ0 _ _ _ _
    (core_map_even p s u hgd hcount htcol hw hbit)
  · intro i
    rw [hp.1 i,map_sub,map_sub,load_residue_shift p q o _ t (delta-gamma) u
      ((rows_colour p r k n gamma i).trans htcol.symm) hw]
  · intro i
    rw [hp.2 i,map_sub,map_sub,load_residue_shift p q o _ t (delta-gamma) u
      ((cols_colour p r k n gamma i).trans htcol.symm) hw]

/-- The same actual mixed moment is constant on an odd translation,
using transpose and exchange of the independent loads. -/
theorem moment_odd (hbit : WrapJointProfile.bit p r delta=1-WrapJointProfile.bit p r gamma)
    (direction : WrapDeform.Extension p) :
    WrapDeform.residue p ((fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (cols p r k n delta i)-direction) ⬝ᵥ (core p q o r k n delta s u)⁻¹ *ᵥ
        (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows p r k n delta i)-direction))=
    WrapDeform.residue p ((fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (cols p r k n gamma i)-direction) ⬝ᵥ (core p q o r k n gamma s u)⁻¹ *ᵥ
        (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows p r k n gamma i)-direction)) := by
  have hp := profile_odd p r k n gamma delta hgd hcount hbit
  have hQT : IsUnit (core p q o r k n gamma s u)ᵀ.det := by rwa [Matrix.det_transpose]
  have hr : ∀ i,WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (rows p r k n delta i)-direction)=WrapDeform.residue p
      (WrapOwnCore.constants p u*WrapEntryRelation.load p q o (cols p r k n gamma i)-direction) := by
    intro i
    rw [hp.1 i,map_sub,map_sub,load_residue_shift p q o _ t (delta-gamma) u
      ((cols_colour p r k n gamma i).trans htcol.symm) hw]
  have hc : ∀ i,WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (cols p r k n delta i)-direction)=WrapDeform.residue p
      (WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows p r k n gamma i)-direction) := by
    intro i
    rw [hp.2 i,map_sub,map_sub,load_residue_shift p q o _ t (delta-gamma) u
      ((rows_colour p r k n gamma i).trans htcol.symm) hw]
  have he := response_map_congr (WrapDeform.residue p) _ _ hQ1 hQT _ _ _ _
    (core_map_odd p s u hgd hcount htcol hw hbit) hr hc
  exact he.trans (congrArg (WrapDeform.residue p) (WrapTransport.response_transpose
    (core p q o r k n gamma s u)
    (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows p r k n gamma i)-direction)
    (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (cols p r k n gamma i)-direction)).symm)

end ReducedResponses


/-- The existing two-term cyclic weight is constant on an actual
regular endpoint window; both singular exclusions come from original data. -/
theorem cyclic_weight_const (q o t d : ℕ) (ho : (o:ZMod p)≠0) (hq : (q:ZMod p)≠0)
    (hw : ∀ h∈Icc 1 d,res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0) :
    wT p q o ((t+d:ℕ):ZMod p)=wT p q o (t:ZMod p) := by
  have hm : ∀ j,j≤d → wT p q o ((t+j:ℕ):ZMod p)=wT p q o (t:ZMod p) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hn := hw (j+1) (by simp only [mem_Icc]; omega)
      have ha0 : ((t+(j+1):ℕ):ZMod p)≠0 := by
        intro hz
        apply hn.1
        have he := congrArg (CatalanCore.Uniform.Content.Hybrid.rfH p) hz
        simpa only [WrapSimplePole.res_nat,map_zero] using he
      have ha1 : (q:ZMod p)*((t+(j+1):ℕ):ZMod p)-(o:ZMod p)≠0 := by
        intro hz
        apply hn.2
        have he := congrArg (CatalanCore.Uniform.Content.Hybrid.rfH p) hz
        simpa only [WrapIncrement.argument,map_sub,map_mul,map_natCast,map_zero] using he
      have hc : ((t+(j+1):ℕ):ZMod p)=((t+j:ℕ):ZMod p)+1 := by push_cast; ring
      rw [hc] at ha0 ha1
      have hn0 : ((t+j:ℕ):ZMod p)≠-1 := by intro he; rw [he] at ha0; exact ha0 (by ring)
      have hn1 : ((t+j:ℕ):ZMod p)≠(o:ZMod p)*(q:ZMod p)⁻¹-1 := by
        intro he
        apply ha1
        rw [he]
        field_simp
        <;> ring
      have hnot : ((t+j:ℕ):ZMod p)∉ttPoles p q o := by
        simp only [ttPoles,mem_insert,mem_singleton,hn0,hn1,or_self,not_false_eq_true]
      rw [hc]
      have hs : wT p q o (((t+j:ℕ):ZMod p)+1)=wT p q o ((t+j:ℕ):ZMod p) := by
        unfold wT
        rw [prim_succ _ (sum_ttJump q o ho hq),ttJump,if_neg hnot,neg_zero,add_zero]
      rw [hs,hprev]
  exact hm d le_rfl

noncomputable def moment (q o r k n gamma : ℕ) (s u : GaussLoc p) (direction : WrapDeform.Extension p) :=
  WrapDeform.residue p ((fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (cols p r k n gamma i)-direction) ⬝ᵥ (core p q o r k n gamma s u)⁻¹ *ᵥ
        (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows p r k n gamma i)-direction))

noncomputable def weight (q o r k n gamma : ℕ) (s u : GaussLoc p)
    (direction : WrapDeform.Extension p) (C0 : RatFunc (RatFunc (ZMod p))) :=
  RatFunc.C (RatFunc.C (wT p q o (gamma:ZMod p)))*WrapDeform.residue p (WrapOwnCore.constants p u)-
    moment p q o r k n gamma s u direction-C0

/-- The actual normalized source weight is constant across either
original joint-type parity. Core units are supplied by core_unit above. -/
theorem weight_transport (q o r k n gamma delta t : ℕ) (s u : GaussLoc p)
    (hg : gamma<p) (hd : delta<p) (hgd : gamma≤delta)
    (hcount : WrapJointProfile.count p r gamma=WrapJointProfile.count p r delta)
    (ho : (o:ZMod p)≠0) (hq : (q:ZMod p)≠0) (htcol : (t:ZMod p)=(gamma:ZMod p))
    (hw : ∀ h∈Icc 1 (delta-gamma),res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0)
    (hQ0 : IsUnit (core p q o r k n gamma s u).det)
    (hQ1 : IsUnit (core p q o r k n delta s u).det)
    (direction : WrapDeform.Extension p) (C0 : RatFunc (RatFunc (ZMod p))) :
    weight p q o r k n delta s u direction C0=weight p q o r k n gamma s u direction C0 := by
  have hcast : ((t+(delta-gamma):ℕ):ZMod p)=(delta:ZMod p) := by
    rw [Nat.cast_add,Nat.cast_sub hgd,htcol]
    ring
  have hwT := cyclic_weight_const p q o t (delta-gamma) ho hq hw
  rw [hcast,htcol] at hwT
  have hbits := WrapJointProfile.bit_transport p r gamma delta (Fact.out:p.Prime).pos hg hd hgd hcount
  have hmoment : moment p q o r k n delta s u direction=moment p q o r k n gamma s u direction := by
    have hh := Nat.mod_lt (delta-gamma) (by decide:0<2)
    have he : (delta-gamma)%2=0 ∨ (delta-gamma)%2=1 := by omega
    rcases he with he|he
    · have hb : WrapJointProfile.bit p r gamma=WrapJointProfile.bit p r delta := by
        rw [he] at hbits
        have hblt := WrapJointProfile.bit_lt p r gamma
        omega
      exact moment_even p s u hgd hcount htcol hw hQ0 hQ1 hb direction
    · have hb : WrapJointProfile.bit p r delta=1-WrapJointProfile.bit p r gamma := by
        rw [he] at hbits
        have hblt := WrapJointProfile.bit_lt p r gamma
        omega
      exact moment_odd p s u hgd hcount htcol hw hQ0 hQ1 hb direction
  unfold weight
  rw [hwT,hmoment]

/-- The original representative constructs the source constant; every
same-type regular selected colour then has zero source weight. -/
theorem weight_zero (q o r k n gamma delta t : ℕ) (s u : GaussLoc p)
    (hg : gamma<p) (hd : delta<p) (hgd : gamma≤delta)
    (hcount : WrapJointProfile.count p r gamma=WrapJointProfile.count p r delta)
    (ho : (o:ZMod p)≠0) (hq : (q:ZMod p)≠0) (htcol : (t:ZMod p)=(gamma:ZMod p))
    (hw : ∀ h∈Icc 1 (delta-gamma),res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0)
    (hQ0 : IsUnit (core p q o r k n gamma s u).det)
    (hQ1 : IsUnit (core p q o r k n delta s u).det) (direction : WrapDeform.Extension p) :
    weight p q o r k n delta s u direction
      (RatFunc.C (RatFunc.C (wT p q o (gamma:ZMod p)))*WrapDeform.residue p (WrapOwnCore.constants p u)-
        moment p q o r k n gamma s u direction)=0 := by
  rw [weight_transport p q o r k n gamma delta t s u hg hd hgd hcount ho hq htcol hw hQ0 hQ1]
  unfold weight
  ring


/-- Normalize the actual source by its original unit reference, keeping
all arithmetic in the integral generic parameter ring. -/
theorem normalized_response {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Matrix α α (WrapDeform.Extension p)) (sigma y : α → WrapDeform.Extension p)
    (yt direction W : WrapDeform.Extension p)
    (hunit : IsUnit (1-sigma ⬝ᵥ Q⁻¹ *ᵥ 1))
    (hm : (yt-direction)-sigma ⬝ᵥ Q⁻¹ *ᵥ (fun i => y i-direction)=WrapDeform.uniformizer p*W) :
    ∃ F : WrapDeform.Extension p,
      yt-sigma ⬝ᵥ Q⁻¹ *ᵥ y=direction*(1-sigma ⬝ᵥ Q⁻¹ *ᵥ 1)+
        WrapDeform.uniformizer p*((1-sigma ⬝ᵥ Q⁻¹ *ᵥ 1)*F) ∧
      WrapDeform.residue p F=WrapDeform.residue p W/
        WrapDeform.residue p (1-sigma ⬝ᵥ Q⁻¹ *ᵥ 1) := by
  let A := 1-sigma ⬝ᵥ Q⁻¹ *ᵥ 1
  have hv : (fun i => y i-direction)=y-direction • (1:α → WrapDeform.Extension p) := by
    funext i
    simp only [Pi.sub_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]
  rw [hv,Matrix.mulVec_sub,Matrix.mulVec_smul,dotProduct_sub,dotProduct_smul] at hm
  simp only [smul_eq_mul] at hm
  have he : yt-sigma ⬝ᵥ Q⁻¹ *ᵥ y=direction*A+WrapDeform.uniformizer p*W := by
    dsimp only [A]
    linear_combination hm
  have hi : A*Ring.inverse A=1 := Ring.mul_inverse_cancel A hunit
  refine ⟨W*Ring.inverse A,?_,?_⟩
  · change yt-sigma ⬝ᵥ Q⁻¹ *ᵥ y=direction*A+WrapDeform.uniformizer p*(A*(W*Ring.inverse A))
    rw [he]
    have hc : A*(W*Ring.inverse A)=W := by
      calc
        _=W*(A*Ring.inverse A) := by ring
        _=W := by rw [hi,mul_one]
    rw [hc]
  · rw [map_mul,WrapPoleResidue.inverse p A hunit,div_eq_mul_inv]


/-- Normalized source for the ACTUAL original mixed prefix core. The
transported own coefficient is consumed directly; all cross-colour source
and reference reductions are derived from original entries. -/
theorem actual_normalized_source {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (q o N t : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : β → ℕ)
    (hN : N<p*p) (ht : t<N) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p))
    (hQ : IsUnit (WrapFibreCore.core p q o s u c xs ys).det)
    (direction G1 : WrapDeform.Extension p) (K0 : RatFunc (RatFunc (ZMod p))) :
    let Q := WrapFibreCore.core p q o s u c xs ys
    let col := WrapFibreIndex.colour p c xs
    let D := WrapPrefixSource.own p col Q
    let sig := fun i => WrapDeformedEntry.entry p q o u t (Sum.elim c ys i)
    let sigOwn := fun i => if col i=(t:ZMod p) then sig i else 0
    let LR := fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c xs i)
    let LC := fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c ys i)
    let Lt := WrapOwnCore.constants p u*WrapEntryRelation.load p q o t
    let B := 1-∑ j,(sigOwn ᵥ* D⁻¹) j
    (Lt-direction)-(sigOwn ᵥ* D⁻¹) ⬝ᵥ (fun i => LR i-direction)=WrapDeform.uniformizer p*G1 →
    WrapDeform.residue p G1=K0*WrapDeform.residue p B → WrapDeform.residue p B≠0 →
    ∃ F : WrapDeform.Extension p,
      Lt-sig ⬝ᵥ Q⁻¹ *ᵥ LR=direction*(1-sig ⬝ᵥ Q⁻¹ *ᵥ 1)+
        WrapDeform.uniformizer p*((1-sig ⬝ᵥ Q⁻¹ *ᵥ 1)*F) ∧
      WrapDeform.residue p F=K0-
        ∑ colour : ZMod p,if colour=(t:ZMod p) then 0 else
          (∑ a∈univ.filter (fun a => col a=colour),
            WrapDeform.residue p ((D⁻¹ *ᵥ (fun i => LR i-direction)) a)*
              WrapDeform.residue p (LC a-direction))/
                (RatFunc.C (RatFunc.C colour)-RatFunc.C (RatFunc.C (t:ZMod p))) := by
  classical
  let Q := WrapFibreCore.core p q o s u c xs ys
  let col := WrapFibreIndex.colour p c xs
  let D := WrapPrefixSource.own p col Q
  let sig : ι ⊕ β → WrapDeform.Extension p := fun i => WrapDeformedEntry.entry p q o u t (Sum.elim c ys i)
  let sigOwn : ι ⊕ β → WrapDeform.Extension p := fun i => if col i=(t:ZMod p) then sig i else 0
  let LR : ι ⊕ β → WrapDeform.Extension p := fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c xs i)
  let LC : ι ⊕ β → WrapDeform.Extension p := fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c ys i)
  let Lt := WrapOwnCore.constants p u*WrapEntryRelation.load p q o t
  let B := 1-∑ j,(sigOwn ᵥ* D⁻¹) j
  change (Lt-direction)-(sigOwn ᵥ* D⁻¹) ⬝ᵥ (fun i => LR i-direction)=WrapDeform.uniformizer p*G1 →
    WrapDeform.residue p G1=K0*WrapDeform.residue p B → WrapDeform.residue p B≠0 → _
  intro hG hGres hB
  obtain ⟨Bk,Rem,hm,hBk⟩ := WrapPrefixSource.actual_node_source p q o N t s u c xs ys
    hN ht hc hx hy hcol hQ direction G1 hG
  obtain ⟨E,hQE,hD,hE0,hE⟩ := WrapPrefixSource.actual_core_source p q o N s u c xs ys hN hc hx hy hcol hQ
  have hpi : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have hmap : Q.map (WrapDeform.residue p)=D.map (WrapDeform.residue p) := by
    ext i j
    have he := congrArg (fun M : Matrix (ι ⊕ β) (ι ⊕ β) (WrapDeform.Extension p) => WrapDeform.residue p (M i j)) hQE
    simpa only [Matrix.map_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      map_add,map_mul,hpi,zero_mul,add_zero] using he
  have hcols (i : ι ⊕ β) : ((Sum.elim c ys i:ℕ):ZMod p)=col i := by
    cases i with
    | inl i => rfl
    | inr i => exact (hcol i).symm
  have hcolN : ∀ i:ι ⊕ β,Sum.elim c ys i<N := by
    intro i
    cases i with
    | inl i => exact hc i
    | inr i => exact hy i
  obtain ⟨sp,hsp,hsp0,hspr⟩ := WrapPrefixSource.actual_border_source p q o N t u (Sum.elim c ys) hN ht hcolN
  have hsplit : sig=sigOwn+WrapDeform.uniformizer p • sp := by simpa only [hcols] using hsp
  have hsig : ∀ i,WrapDeform.residue p (sig i)=WrapDeform.residue p (sigOwn i) := by
    intro i
    have he := congrArg (fun v : ι ⊕ β → WrapDeform.Extension p => WrapDeform.residue p (v i)) hsplit
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_add,map_mul,hpi,zero_mul,add_zero] using he
  have hA := reference_map_congr (WrapDeform.residue p) Q D hQ hD sig sigOwn hmap hsig
  have hBref : 1-sigOwn ⬝ᵥ D⁻¹ *ᵥ 1=B := by
    rw [dotProduct_mulVec,dotProduct]
    simp only [Pi.one_apply,mul_one]
    rfl
  rw [hBref] at hA
  have hunit : IsUnit (1-sig ⬝ᵥ Q⁻¹ *ᵥ 1) :=
    WrapBalancedTest.unit_ne p _ (by
      change WrapDeform.residue p (1-sig ⬝ᵥ Q⁻¹ *ᵥ 1)≠0
      rw [hA]; exact hB)
  obtain ⟨F,hF,hr⟩ := normalized_response p Q sig LR Lt direction (G1-Bk+WrapDeform.uniformizer p*Rem) hunit hm
  refine ⟨F,hF,?_⟩
  rw [hr,map_add,map_sub,map_mul,hpi,zero_mul,add_zero,hGres,hBk,hA]
  field_simp [hB]
  <;> ring


/-- The actual global own response is computed entirely in its literal
original colour block. This connects the source expansion to the original
fibre equivalences, uniformly in every retained common family. -/
theorem own_response_local {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Matrix α α (WrapDeform.Extension p)) (col : α → ZMod p) (tau : ZMod p)
    (sigma y : α → WrapDeform.Extension p) (hD : IsUnit (WrapPrefixSource.own p col Q).det) :
    ((fun i => if col i=tau then sigma i else 0) ᵥ* (WrapPrefixSource.own p col Q)⁻¹) ⬝ᵥ y=
      (fun i:{a // col a=tau} => sigma i.1) ⬝ᵥ (Q.toSquareBlock col tau)⁻¹ *ᵥ (fun i => y i.1) := by
  classical
  let D := WrapPrefixSource.own p col Q
  let sigOwn : α → WrapDeform.Extension p := fun i => if col i=tau then sigma i else 0
  have hb : ∀ a b,col a≠col b → D a b=0 := by intro a b hab; exact if_neg hab
  have hs : ∀ a,col a≠tau → sigOwn a=0 := by intro a ha; exact if_neg ha
  have hblk : blk D col tau=Q.toSquareBlock col tau := by
    ext i j
    change (if col i.1=col j.1 then Q i.1 j.1 else 0)=Q i.1 j.1
    rw [if_pos (i.2.trans j.2.symm)]
  have hsig : (fun i:{a // col a=tau} => sigOwn i.1)=(fun i => sigma i.1) := by
    funext i
    exact if_pos i.2
  have he := own_fiber_form D col hD hb tau sigOwn y hs
  rw [hblk,hsig] at he
  rw [dotProduct_mulVec]
  simpa only [dotProduct] using he

theorem own_reference_local {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Matrix α α (WrapDeform.Extension p)) (col : α → ZMod p) (tau : ZMod p)
    (sigma : α → WrapDeform.Extension p) (hD : IsUnit (WrapPrefixSource.own p col Q).det) :
    1-∑ i,((fun i => if col i=tau then sigma i else 0) ᵥ* (WrapPrefixSource.own p col Q)⁻¹) i=
      1-(fun i:{a // col a=tau} => sigma i.1) ⬝ᵥ (Q.toSquareBlock col tau)⁻¹ *ᵥ 1 := by
  have he := own_response_local p Q col tau sigma (1:α → WrapDeform.Extension p) hD
  simpa only [dotProduct,Matrix.mulVec,Pi.one_apply,mul_one] using congrArg (fun z : WrapDeform.Extension p => 1-z) he

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixType

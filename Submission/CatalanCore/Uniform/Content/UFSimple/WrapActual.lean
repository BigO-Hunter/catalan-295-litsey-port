module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapCore
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapBalanced
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapEntries
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapSchur
public import Submission.CatalanCore.Uniform.Content.UFMoments.TypeDataLift
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapType

@[expose] public section

/-! # Primitive mixed core of the original scaled alternating matrix

The constant balanced block below is selected from the original matrix.
Its rows and columns are reordered independently; only original common
indices retain the spectral diagonal.
-/

open Polynomial Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Rect CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapActual

open WrapGeometry

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {q o : ℕ}
  {ι : Type} [Fintype ι] [DecidableEq ι]

def xs (r : ℕ) {m : ℕ} (i : Fin m) : ℕ := r+2*i

def ys (r : ℕ) {m : ℕ} (i : Fin m) : ℕ := r+2*i+1

/-- Integrality of the original scaled entries restricts to the actual
balanced constant block. -/
theorem balanced_hint (c : ι → ℕ) (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hint : ∀ i j, (p:ℚ)^2*Fr.Mn (rowNode c (xs r (m:=s+l)) i)
      (colNode c (ys r (m:=s+l)) j) ∈ LocRing p)
    (i j : Fin (2*l-1)) :
    (p:ℚ)^2*Fr.Mn (WrapBalanced.rowNode r s i) (WrapBalanced.colNode r s j) ∈ LocRing p := by
  exact hint (Sum.inr (rowSlot s l hl hls (Sum.inl i)))
    (Sum.inr (colSlot s l hl hls (Sum.inl j)))

/-- Literal equality of the balanced block of the reordered original
constant matrix with the actual full-period entry matrix. -/
theorem balanced_block_eq (c : ι → ℕ) (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hint : ∀ i j, (p:ℚ)^2*Fr.Mn (rowNode c (xs r (m:=s+l)) i)
      (colNode c (ys r (m:=s+l)) j) ∈ LocRing p) :
    (WrapCore.constantCore s l hl hls (sConst c (xs r) (ys r) hint)).toBlocks₂₂ =
      WrapBalanced.lift r s l (balanced_hint c r s l hl hls hint) := by
  rfl

/-- The original scaled alternating matrix has a primitive actual mixed
core throughout the wrapped range. -/
theorem core_primitive (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (c : ι → ℕ) (r s l : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hint : ∀ i j, (p:ℚ)^2*Fr.Mn (rowNode c (xs r (m:=s+l)) i)
      (colNode c (ys r (m:=s+l)) j) ∈ LocRing p) :
    phiP p (((sLift c (xs r) (ys r) hint).submatrix
      (rowFullEquiv ι s l hl hls) (colFullEquiv ι s l hl hls)).toBlocks₁₁.det) ≠ 0 := by
  have hD := WrapBalanced.det_ne T hqp hN hsq hnorm hnorm0 r s l hl hls hp hsize
    (balanced_hint c r s l hl hls hint)
  rw [← balanced_block_eq c r s l hl hls hint] at hD
  have hh := WrapCore.det_map_liftCore_ne_zero (redQ p) s l hl hls
    (sConst c (xs r) (ys r) hint) hD
  unfold phiP
  rw [RingHom.comp_apply, Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective (ZMod p))]
  exact hh

/-- Original lift in the actual independent row and column ordering. -/
noncomputable def reordered (c : ι → ℕ) (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hint : ∀ i j, (p:ℚ)^2*Fr.Mn (rowNode c (xs r (m:=s+l)) i)
      (colNode c (ys r (m:=s+l)) j) ∈ LocRing p) :=
  (sLift c (xs r) (ys r) hint).submatrix
    (rowFullEquiv ι s l hl hls) (colFullEquiv ι s l hl hls)

noncomputable def rowCoords (c : ι → ℕ) (r s l : ℕ) (hl : 1≤l) (hls : l≤s) :=
  rowNode c (xs r) ∘ rowFullEquiv ι s l hl hls

noncomputable def colCoords (c : ι → ℕ) (r s l : ℕ) (hl : 1≤l) (hls : l≤s) :=
  colNode c (ys r) ∘ colFullEquiv ι s l hl hls

/-- The actual mixed core has matching residue colours on its two axes. -/
theorem core_colours (c : ι → ℕ) (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hp : p=2*s+1) (a : ι ⊕ Fin (2*l-1)) :
    ((rowCoords c r s l hl hls (Sum.inl a) : ℕ) : ZMod p) =
      ((colCoords c r s l hl hls (Sum.inl a) : ℕ) : ZMod p) := by
  rcases a with a | a
  · rfl
  · change ((WrapBalanced.rowNode r s a : ℕ) : ZMod p) =
      ((WrapBalanced.colNode r s a : ℕ) : ZMod p)
    rw [WrapBalanced.row_colour r s a hp, WrapBalanced.col_colour r s a hp]

/-- After absorbing the balanced pairs, the remaining actual surplus
row and column residues are disjoint. -/
theorem surplus_colours (c : ι → ℕ) (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hp : p=2*s+1) (i j : Fin (s+1-l)) :
    ((rowCoords c r s l hl hls (Sum.inr i) : ℕ) : ZMod p) ≠
      ((colCoords c r s l hl hls (Sum.inr j) : ℕ) : ZMod p) := by
  subst p
  exact surplus_distinct_colour r s l hl hls i j

/-- Exact divided Schur identity for the original two-term matrix in
wrapped coordinates. No global border-disjointness assumption is used. -/
theorem schur_eq (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (c : ι → ℕ) (r s l : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a, c a<N)
    (hx : ∀ i : Fin (s+l), xs r i<N) (hy : ∀ i : Fin (s+l), ys r i<N) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let A := reordered c r s l hl hls (hint_of_poleData D hN hc hx hy)
    A.toBlocks₁₁.det • A.toBlocks₂₂ - A.toBlocks₂₁ * A.toBlocks₁₁.adjugate * A.toBlocks₁₂ =
      Polynomial.C ((p:ℕ) : LocRing p) • WrapSchur.dividedSchur A := by
  intro D A
  apply WrapSchur.mixed_schur_eq A
    (fun i => ((rowCoords c r s l hl hls i : ℕ) : ZMod p))
    (fun i => ((colCoords c r s l hl hls i : ℕ) : ZMod p))
  · exact core_colours c r s l hl hls hp
  · intro i j hij
    exact WrapEntries.sLift_cross_zero D hN c (xs r) (ys r) hc hx hy _ _ hij
  · exact core_primitive T hqp hN hsq hnorm hnorm0 c r s l hl hls hp hsize _
  · exact surplus_colours c r s l hl hls hp

/-- Distinct offsets inside one complete period have distinct colours. -/
theorem offset_colours {r u v : ℕ} (hu : u<p) (hv : v<p) (huv : u≠v) :
    (((r+u:ℕ):ZMod p)) ≠ (((r+v:ℕ):ZMod p)) := by
  intro he
  have he' : ((u:ℕ):ZMod p) = ((v:ℕ):ZMod p) := by
    apply add_left_cancel (a := (r:ZMod p))
    simpa only [Nat.cast_add] using he
  have hh := (ZMod.natCast_eq_natCast_iff' u v p).mp he'
  rw [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at hh
  exact huv hh

/-- No absorbed balanced pair has the colour of a node in the remaining
surplus interval. This includes a representative of either parity. -/
theorem balanced_not_surplus (r s l t : ℕ) (hl : 1≤l) (hls : l≤s)
    (hp : p=2*s+1) (htlo : r+2*l-1≤t) (hthi : t<r+p)
    (i : Fin (2*l-1)) :
    ((WrapBalanced.rowNode r s i:ℕ):ZMod p) ≠ ((t:ℕ):ZMod p) := by
  rw [WrapBalanced.row_colour r s i hp]
  have hi := i.2
  have hrt : r≤t := by omega
  have he : t=r+(t-r) := by omega
  rw [he]
  exact offset_colours (by omega) (by omega) (by omega)

/-- Remove the balanced summand from an own fibre when its colour lies
in the actual surplus interval. -/
noncomputable def surplus_fibre_equiv (c : ι → ℕ) (r s l t : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (htlo : r+2*l-1≤t) (hthi : t<r+p) :
    {a : ι ⊕ Fin (2*l-1) //
      ((rowCoords c r s l hl hls (Sum.inl a):ℕ):ZMod p) = ((t:ℕ):ZMod p)} ≃
    {a : ι // ((c a:ℕ):ZMod p) = ((t:ℕ):ZMod p)} where
  toFun a := match a with
    | ⟨Sum.inl i, hi⟩ => ⟨i,hi⟩
    | ⟨Sum.inr i, hi⟩ => False.elim (balanced_not_surplus r s l t hl hls hp htlo hthi i hi)
  invFun a := ⟨Sum.inl a.1,a.2⟩
  left_inv a := by
    rcases a with ⟨a,ha⟩
    rcases a with a | a
    · rfl
    · exact False.elim (balanced_not_surplus r s l t hl hls hp htlo hthi a ha)
  right_inv a := by rfl


/-- Transport of the original common-chain data to the actual mixed
core. The absorbed balanced fibres are excluded by the surplus interval,
so every equality below is an equality of original matrix entries. -/
theorem typeData_transfer (c : ι → ℕ) (r s l t0 t : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (ht0lo : r+2*l-1≤t0) (ht0hi : t0<r+p)
    (htlo : r+2*l-1≤t) (hthi : t<r+p)
    (hint : ∀ i j, (p:ℚ)^2*Fr.Mn (rowNode c (xs r (m:=s+l)) i)
      (colNode c (ys r (m:=s+l)) j) ∈ LocRing p)
    (sigma0 sigma : (ι ⊕ Fin (2*l-1)) → (LocRing p)[X])
    (K0 : RatFunc (ZMod p)) (W : ZMod p → RatFunc (ZMod p))
    (H : TypeData Fr c (sLift c (xs r) (ys r) hint).toBlocks₁₁ t0
      (fun a => sigma0 (Sum.inl a)) K0 W t (fun a => sigma (Sum.inl a))) :
    TypeData Fr (fun a => rowCoords c r s l hl hls (Sum.inl a))
      (reordered c r s l hl hls hint).toBlocks₁₁ t0 sigma0 K0 W t sigma := by
  obtain ⟨e,kappa,hDD,hss,hell,hkappa,hres⟩ := H
  let F := surplus_fibre_equiv c r s l t hl hls hp htlo hthi
  let F0 := surplus_fibre_equiv c r s l t0 hl hls hp ht0lo ht0hi
  let E := (F.trans e).trans F0.symm
  refine ⟨E,kappa,?_,?_,?_,hkappa,hres⟩
  · intro i j
    obtain ⟨i,rfl⟩ := F0.symm.surjective i
    obtain ⟨j,rfl⟩ := F0.symm.surjective j
    exact hDD i j
  · intro i
    obtain ⟨i,rfl⟩ := F0.symm.surjective i
    exact hss i
  · intro i
    obtain ⟨i,rfl⟩ := F0.symm.surjective i
    exact hell i

/-- Every reordered entry retains the actual frame commutator. -/
theorem reordered_commutator (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hc : ∀ a, c a<N) (hx : ∀ i : Fin (s+l), xs r i<N)
    (hy : ∀ i : Fin (s+l), ys r i<N)
    (i j : (ι ⊕ Fin (2*l-1)) ⊕ Fin (s+1-l)) :
    nL p Fr * (nd p (colCoords c r s l hl hls j)-nd p (rowCoords c r s l hl hls i))*
      reordered c r s l hl hls (hint_of_poleData D hN hc hx hy) i j =
      PF p Fr (colCoords c r s l hl hls j)-PF p Fr (rowCoords c r s l hl hls i) := by
  exact WrapEntries.sLift_commutator D hN c (xs r) (ys r) hc hx hy _ _

/-- At every surplus colour, the global mixed source moment equals the
original common-fibre moment exactly. -/
theorem surplus_mixedFibMom (c : ι → ℕ) (r s l t : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (htlo : r+2*l-1≤t) (hthi : t<r+p)
    (hint : ∀ i j, (p:ℚ)^2*Fr.Mn (rowNode c (xs r (m:=s+l)) i)
      (colNode c (ys r (m:=s+l)) j) ∈ LocRing p) (d : GaussLoc p)
    (hDa : IsUnit (Dmat (fun a => rowCoords c r s l hl hls (Sum.inl a))
      (reordered c r s l hl hls hint).toBlocks₁₁).det)
    (hDo : IsUnit (Dmat c (sLift c (xs r) (ys r) hint).toBlocks₁₁).det) :
    WrapNodes.mixedFibMom (fun a => rowCoords c r s l hl hls (Sum.inl a))
      (Dmat (fun a => rowCoords c r s l hl hls (Sum.inl a))
        (reordered c r s l hl hls hint).toBlocks₁₁)
      (fun a => ellL p Fr (rowCoords c r s l hl hls (Sum.inl a))-d)
      (fun a => ellL p Fr (colCoords c r s l hl hls (Sum.inl a))-d) ((t:ℕ):ZMod p) =
      fibMom c (Dmat c (sLift c (xs r) (ys r) hint).toBlocks₁₁)
        (fun a => ellL p Fr (c a)-d) ((t:ℕ):ZMod p) := by
  let cr := fun a => rowCoords c r s l hl hls (Sum.inl a)
  let cc := fun a => colCoords c r s l hl hls (Sum.inl a)
  let DA := Dmat cr (reordered c r s l hl hls hint).toBlocks₁₁
  let DO := Dmat c (sLift c (xs r) (ys r) hint).toBlocks₁₁
  let tau : ZMod p := ((t:ℕ):ZMod p)
  let yR := fun a => ellL p Fr (cr a)-d
  let yC := fun a => ellL p Fr (cc a)-d
  let y := fun a => ellL p Fr (c a)-d
  have hbA : ∀ a b, colOf (p:=p) cr a≠colOf cr b → DA a b=0 := by
    intro a b h; simp [DA,Dmat,h]
  have hbO : ∀ a b, colOf (p:=p) c a≠colOf c b → DO a b=0 := by
    intro a b h; simp [DO,Dmat,h]
  change (∑ a ∈ Finset.univ.filter (fun a => colOf (p:=p) cr a=tau),
    res p ((DA⁻¹ *ᵥ yR) a)*res p (yC a)) =
    ∑ a ∈ Finset.univ.filter (fun a => colOf (p:=p) c a=tau),
      res p ((DO⁻¹ *ᵥ y) a)*res p (y a)
  rw [WrapType.mixed_fiber_moment_response DA (colOf cr) hDa hbA tau yR yC (res p),
    WrapType.mixed_fiber_moment_response DO (colOf c) hDo hbO tau y y (res p)]
  let E := surplus_fibre_equiv c r s l t hl hls hp htlo hthi
  have hh := WrapTransport.response_reindex (blk DA (colOf cr) tau) E.symm E.symm
    (fun a => yR a.1) (fun a => yC a.1)
  exact congrArg (res p) hh.symm

/-- The complete own-fibre linear response at a surplus node equals
the original common-fibre response, for any load vector. -/
theorem surplus_own_response (c : ι → ℕ) (r s l t : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (htlo : r+2*l-1≤t) (hthi : t<r+p)
    (hint : ∀ i j, (p:ℚ)^2*Fr.Mn (rowNode c (xs r (m:=s+l)) i)
      (colNode c (ys r (m:=s+l)) j) ∈ LocRing p)
    (sigma : (ι ⊕ Fin (2*l-1)) → (LocRing p)[X])
    (v : (ι ⊕ Fin (2*l-1)) → GaussLoc p)
    (hDa : IsUnit (Dmat (fun a => rowCoords c r s l hl hls (Sum.inl a))
      (reordered c r s l hl hls hint).toBlocks₁₁).det)
    (hDo : IsUnit (Dmat c (sLift c (xs r) (ys r) hint).toBlocks₁₁).det) :
    (sOwn (fun a => rowCoords c r s l hl hls (Sum.inl a)) t sigma ᵥ*
      (Dmat (fun a => rowCoords c r s l hl hls (Sum.inl a))
        (reordered c r s l hl hls hint).toBlocks₁₁)⁻¹) ⬝ᵥ v =
      (sOwn c t (fun a => sigma (Sum.inl a)) ᵥ*
        (Dmat c (sLift c (xs r) (ys r) hint).toBlocks₁₁)⁻¹) ⬝ᵥ
          (fun a => v (Sum.inl a)) := by
  let cr := fun a => rowCoords c r s l hl hls (Sum.inl a)
  let DA := Dmat cr (reordered c r s l hl hls hint).toBlocks₁₁
  let DO := Dmat c (sLift c (xs r) (ys r) hint).toBlocks₁₁
  let tau : ZMod p := ((t:ℕ):ZMod p)
  have hbA : ∀ a b, colOf (p:=p) cr a≠colOf cr b → DA a b=0 := by
    intro a b h; simp [DA,Dmat,h]
  have hbO : ∀ a b, colOf (p:=p) c a≠colOf c b → DO a b=0 := by
    intro a b h; simp [DO,Dmat,h]
  have hsA : ∀ a, colOf (p:=p) cr a≠tau → sOwn cr t sigma a=0 := by
    intro a h; simp [sOwn,h,tau] at *
  have hsO : ∀ a, colOf (p:=p) c a≠tau → sOwn c t (fun a => sigma (Sum.inl a)) a=0 := by
    intro a h; simp [sOwn,h,tau] at *
  change (sOwn cr t sigma ᵥ* DA⁻¹) ⬝ᵥ v =
    (sOwn c t (fun a => sigma (Sum.inl a)) ᵥ* DO⁻¹) ⬝ᵥ (fun a => v (Sum.inl a))
  rw [own_fiber_form DA (colOf cr) hDa hbA tau (sOwn cr t sigma) v hsA,
    own_fiber_form DO (colOf c) hDo hbO tau
      (sOwn c t (fun a => sigma (Sum.inl a))) (fun a => v (Sum.inl a)) hsO]
  let E := surplus_fibre_equiv c r s l t hl hls hp htlo hthi
  have hh := WrapTransport.response_reindex (blk DA (colOf cr) tau) E.symm E.symm
    (fun a => v a.1) (fun a => sOwn cr t sigma a.1)
  rw [Matrix.dotProduct_mulVec,Matrix.dotProduct_mulVec] at hh
  exact hh.symm

/-- The corresponding own-fibre equivalence on the independent column
axis. Its image is still exactly the original common indices. -/
noncomputable def surplus_col_fibre_equiv (c : ι → ℕ) (r s l t : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (htlo : r+2*l-1≤t) (hthi : t<r+p) :
    {a : ι ⊕ Fin (2*l-1) //
      ((colCoords c r s l hl hls (Sum.inl a):ℕ):ZMod p) = ((t:ℕ):ZMod p)} ≃
    {a : ι // ((c a:ℕ):ZMod p) = ((t:ℕ):ZMod p)} where
  toFun a := match a with
    | ⟨Sum.inl i, hi⟩ => ⟨i,hi⟩
    | ⟨Sum.inr i, hi⟩ => False.elim (balanced_not_surplus r s l t hl hls hp htlo hthi i
        ((core_colours c r s l hl hls hp (Sum.inr i)).trans hi))
  invFun a := ⟨Sum.inl a.1,a.2⟩
  left_inv a := by
    rcases a with ⟨a,ha⟩
    rcases a with a | a
    · rfl
    · exact False.elim (balanced_not_surplus r s l t hl hls hp htlo hthi a
        ((core_colours c r s l hl hls hp (Sum.inr a)).trans ha))
  right_inv a := by rfl

/-- Original chain transport also supplies the actual transposed core.
No symmetry of the full mixed core is required. -/
theorem typeData_transfer_col (c : ι → ℕ) (r s l t0 t : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (ht0lo : r+2*l-1≤t0) (ht0hi : t0<r+p)
    (htlo : r+2*l-1≤t) (hthi : t<r+p)
    (hint : ∀ i j, (p:ℚ)^2*Fr.Mn (rowNode c (xs r (m:=s+l)) i)
      (colNode c (ys r (m:=s+l)) j) ∈ LocRing p)
    (sigma0 sigma : (ι ⊕ Fin (2*l-1)) → (LocRing p)[X])
    (K0 : RatFunc (ZMod p)) (W : ZMod p → RatFunc (ZMod p))
    (H : TypeData Fr c (sLift c (xs r) (ys r) hint).toBlocks₁₁ t0
      (fun a => sigma0 (Sum.inl a)) K0 W t (fun a => sigma (Sum.inl a))) :
    TypeData Fr (fun a => colCoords c r s l hl hls (Sum.inl a))
      (reordered c r s l hl hls hint).toBlocks₁₁ᵀ t0 sigma0 K0 W t sigma := by
  obtain ⟨e,kappa,hDD,hss,hell,hkappa,hres⟩ := H
  let F := surplus_col_fibre_equiv c r s l t hl hls hp htlo hthi
  let F0 := surplus_col_fibre_equiv c r s l t0 hl hls hp ht0lo ht0hi
  let E := (F.trans e).trans F0.symm
  refine ⟨E,kappa,?_,?_,?_,hkappa,hres⟩
  · intro i j
    obtain ⟨i,rfl⟩ := F0.symm.surjective i
    obtain ⟨j,rfl⟩ := F0.symm.surjective j
    exact hDD j i
  · intro i
    obtain ⟨i,rfl⟩ := F0.symm.surjective i
    exact hss i
  · intro i
    obtain ⟨i,rfl⟩ := F0.symm.surjective i
    exact hell i

/-- Assemble source data of the ACTUAL divided Schur complement into
a scaled-gauge Smith witness for the original matrix in mixed ordering. -/
noncomputable def witness_of_data (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (c : ι → ℕ) (r s l : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a, c a<N)
    (hx : ∀ i : Fin (s+l), xs r i<N) (hy : ∀ i : Fin (s+l), ys r i<N)
    {a b : ℕ}
    (D2 : TwoLevelData (phiP p) (Polynomial.C ((p:ℕ):LocRing p))
      (WrapSchur.dividedSchur (reordered c r s l hl hls
        (hint_of_poleData (twoTermPoleData T hN.le hsq hnorm hnorm0) hN hc hx hy))) a b) :
    ThreeLevelWit p (((FullN Fr c (xs r (m:=s+l)) (ys r) (X:ℚ[X])).map (scaleU p)).submatrix
      (rowFullEquiv ι s l hl hls) (colFullEquiv ι s l hl hls)) b :=
  ThreeLevelWit.ofSchurData _ (reordered c r s l hl hls _)
    (fun i j => sLift_hB c (xs r) (ys r) _ _ _)
    (core_primitive T hqp hN hsq hnorm hnorm0 c r s l hl hls hp hsize _) _
    (schur_eq T hqp hN hsq hnorm hnorm0 c r s l hl hls hp hsize hc hx hy) D2

/-- Exact price of the actual mixed-coordinate witness. -/
theorem witness_of_data_price (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (c : ι → ℕ) (r s l : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a, c a<N)
    (hx : ∀ i : Fin (s+l), xs r i<N) (hy : ∀ i : Fin (s+l), ys r i<N)
    {a b : ℕ}
    (D2 : TwoLevelData (phiP p) (Polynomial.C ((p:ℕ):LocRing p))
      (WrapSchur.dividedSchur (reordered c r s l hl hls
        (hint_of_poleData (twoTermPoleData T hN.le hsq hnorm hnorm0) hN hc hx hy))) a b) :
    (witness_of_data T hqp hN hsq hnorm hnorm0 c r s l hl hls hp hsize hc hx hy D2).price =
      2*(Fintype.card ι+s+l)-((s+1-l)+(a+(a-b))) := by
  calc
    _ = 2*Fintype.card ((ι ⊕ Fin (2*l-1)) ⊕ Fin (s+1-l)) -
        (Fintype.card (Fin (s+1-l))+(a+(a-b))) :=
      ThreeLevelWit.ofSchurData_price _ _ _ _ _ _ D2
    _ = _ := by
      simp only [Fintype.card_sum,Fintype.card_fin]
      omega

/-- In a virtual common interval shorter than one extra period, the
only appended node with the designated balanced colour is its lower node. -/
theorem virtual_extra_unique (r b t : ℕ) (hbp : b<p) (ht : t<b)
    (x : Fin (r+b)) (hxr : r≤x)
    (hcol : ((x:ℕ):ZMod p)=((r+t:ℕ):ZMod p)) : (x:ℕ)=r+t := by
  have hx := x.2
  have he : ((r+((x:ℕ)-r):ℕ):ZMod p)=((r+t:ℕ):ZMod p) := by
    simpa only [Nat.add_sub_of_le hxr] using hcol
  by_contra hh
  exact (offset_colours (by omega : (x:ℕ)-r<p) (by omega : t<p) (by omega)) he

/-- The virtual common fibre is the original common fibre plus precisely
one lower balanced node, with no matrix or spectral assumptions. -/
noncomputable def virtual_fibre_equiv (r b t : ℕ) (hbp : b<p) (ht : t<b) :
    {x : Fin (r+b) // ((x:ℕ):ZMod p)=((r+t:ℕ):ZMod p)} ≃
      ({x : Fin r // ((x:ℕ):ZMod p)=((r+t:ℕ):ZMod p)} ⊕ Unit) where
  toFun x := if hx : (x.1:ℕ)<r then Sum.inl ⟨⟨x.1,hx⟩,x.2⟩ else Sum.inr ()
  invFun x := match x with
    | Sum.inl x => ⟨⟨x.1,by have := x.1.2; omega⟩,x.2⟩
    | Sum.inr _ => ⟨⟨r+t,by omega⟩,rfl⟩
  left_inv x := by
    dsimp only
    split_ifs with hx
    · rfl
    · have he := virtual_extra_unique r b t hbp ht x.1 (by omega) x.2
      apply Subtype.ext
      apply Fin.ext
      exact he.symm
  right_inv x := by
    rcases x with x | x
    · simp only [show (x.1:ℕ)<r from x.1.2,↓reduceDIte]
    · cases x
      simp only [show ¬r+t<r by omega,↓reduceDIte]

/-- Virtual fibre coordinates are literally the original common nodes
followed by the actual lower balanced node. -/
theorem virtual_fibre_coords (r b t : ℕ) (hbp : b<p) (ht : t<b)
    (x : {x : Fin r // ((x:ℕ):ZMod p)=((r+t:ℕ):ZMod p)} ⊕ Unit) :
    (((virtual_fibre_equiv r b t hbp ht).symm x).1:ℕ)=
      WrapBalanced.extendNodes (fun a => (a.1:ℕ)) (r+t) x := by
  rcases x with x | x <;> rfl

/-- A balanced colour has exactly one balanced index in the actual core. -/
theorem balanced_index_unique (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hp : p=2*s+1) (i j : Fin (2*l-1))
    (he : ((WrapBalanced.rowNode r s i:ℕ):ZMod p)=
      ((WrapBalanced.rowNode r s j:ℕ):ZMod p)) : i=j := by
  rw [WrapBalanced.row_colour r s i hp,WrapBalanced.row_colour r s j hp] at he
  have hi := i.2
  have hj := j.2
  by_contra hh
  exact (offset_colours (by omega : (i:ℕ)<p) (by omega : (j:ℕ)<p)
    (fun hv => hh (Fin.ext hv))) he

/-- Actual balanced own fibre: original common nodes of this colour,
plus the unique actual balanced index. -/
noncomputable def balanced_fibre_equiv (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hp : p=2*s+1) (t : Fin (2*l-1)) :
    {x : Fin r ⊕ Fin (2*l-1) //
      ((rowCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inl x):ℕ):ZMod p)=
        ((r+(t:ℕ):ℕ):ZMod p)} ≃
      ({x : Fin r // ((x:ℕ):ZMod p)=((r+(t:ℕ):ℕ):ZMod p)} ⊕ Unit) where
  toFun x := match x with
    | ⟨Sum.inl a,ha⟩ => Sum.inl ⟨a,ha⟩
    | ⟨Sum.inr _,_⟩ => Sum.inr ()
  invFun x := match x with
    | Sum.inl a => ⟨Sum.inl a.1,a.2⟩
    | Sum.inr _ => ⟨Sum.inr t,WrapBalanced.row_colour r s t hp⟩
  left_inv x := by
    rcases x with ⟨x,hx⟩
    rcases x with a | a
    · rfl
    · have he : a=t := balanced_index_unique r s l hl hls hp a t
        (hx.trans (WrapBalanced.row_colour r s t hp).symm)
      subst a
      rfl
  right_inv x := by
    rcases x with x | x
    · rfl
    · cases x; rfl

/-- Both actual coordinate axes of a balanced fibre are precisely the
original common fibre with the corresponding actual endpoint appended. -/
theorem balanced_fibre_coords (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hp : p=2*s+1) (t : Fin (2*l-1))
    (x : {x : Fin r // ((x:ℕ):ZMod p)=((r+(t:ℕ):ℕ):ZMod p)} ⊕ Unit) :
    rowCoords (fun a:Fin r => (a:ℕ)) r s l hl hls
      (Sum.inl ((balanced_fibre_equiv r s l hl hls hp t).symm x).1)=
        WrapBalanced.extendNodes (fun a => (a.1:ℕ)) (WrapBalanced.rowNode r s t) x ∧
    colCoords (fun a:Fin r => (a:ℕ)) r s l hl hls
      (Sum.inl ((balanced_fibre_equiv r s l hl hls hp t).symm x).1)=
        WrapBalanced.extendNodes (fun a => (a.1:ℕ)) (WrapBalanced.colNode r s t) x := by
  rcases x with x | x <;> exact ⟨rfl,rfl⟩

/-- Exact polynomial entry of the original scaled lift. -/
theorem scaled_entry {κ : Type} [Fintype κ] [DecidableEq κ]
    (D : PoleData Fr p N) (hN : N<p*p) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a<N) (hx : ∀ i, xs i<N) (hy : ∀ j, ys j<N) (i j : ι ⊕ κ) :
    sLift c xs ys (hint_of_poleData D hN hc hx hy) i j=
      Polynomial.C (Hybrid.liftQ p ((p:ℚ)^2*Fr.Mn (rowNode c xs i) (colNode c ys j)))+
        Matrix.fromBlocks ((X:(LocRing p)[X]) • (1:Matrix ι ι (LocRing p)[X])) 0 0 0 i j := by
  exact congrArg (fun a => Polynomial.C a+
    Matrix.fromBlocks ((X:(LocRing p)[X]) • (1:Matrix ι ι (LocRing p)[X])) 0 0 0 i j)
      (sConst_eq_liftQ D hN c xs ys hc hx hy i j)

/-- Injective restriction of a genuine common core preserves exactly
its original spectral diagonals. -/
theorem commonLift_submatrix {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (c : α → ℕ) (f : β → α) (hf : Function.Injective f) :
    (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c).submatrix f f=
      WrapBalanced.commonLift (p:=p) (Fr:=Fr) (c ∘ f) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i=j
  · subst j; simp [WrapBalanced.commonLift,Function.comp_def]
  · have hne : f i≠f j := fun h => hij (hf h)
    simp [WrapBalanced.commonLift,Matrix.one_apply,hij,hne,Function.comp_def]

/-- The virtual own fibre is exactly the reference common fibre used
in the actual column-replacement cancellation. -/
theorem virtual_fibre_lift (r b t : ℕ) (hbp : b<p) (ht : t<b) :
    (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun a:Fin (r+b) => (a:ℕ))).submatrix
      (fun x => ((virtual_fibre_equiv r b t hbp ht).symm x).1)
      (fun x => ((virtual_fibre_equiv r b t hbp ht).symm x).1)=
      WrapBalanced.commonLift (p:=p) (Fr:=Fr)
        (WrapBalanced.extendNodes (fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+t:ℕ):ZMod p)} =>
          (a.1:ℕ)) (r+t)) := by
  rw [commonLift_submatrix _ _ (fun i j h =>
    (virtual_fibre_equiv r b t hbp ht).symm.injective (Subtype.ext h))]
  congr 1
  funext x
  exact virtual_fibre_coords r b t hbp ht x

/-- The actual reordered balanced own fibre is the concrete mixed entry
matrix used in both response-cancellation lemmas. -/
theorem balanced_fibre_lift (D : PoleData Fr p N) (hN : N<p*p)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), xs r i<N)
    (hy : ∀ i:Fin (s+l), ys r i<N) (t : Fin (2*l-1)) :
    ((reordered (fun a:Fin r => (a:ℕ)) r s l hl hls
      (hint_of_poleData D hN hc hx hy)).toBlocks₁₁).submatrix
        (fun x => ((balanced_fibre_equiv r s l hl hls hp t).symm x).1)
        (fun x => ((balanced_fibre_equiv r s l hl hls hp t).symm x).1)=
      WrapBalanced.mixedLift (p:=p) (Fr:=Fr)
        (fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+(t:ℕ):ℕ):ZMod p)} => (a.1:ℕ))
        (WrapBalanced.rowNode r s t) (WrapBalanced.colNode r s t) := by
  apply Matrix.ext
  intro i j
  change sLift (fun a:Fin r => (a:ℕ)) (xs r) (ys r) (hint_of_poleData D hN hc hx hy)
    (rowFullEquiv (Fin r) s l hl hls (Sum.inl ((balanced_fibre_equiv r s l hl hls hp t).symm i).1))
    (colFullEquiv (Fin r) s l hl hls (Sum.inl ((balanced_fibre_equiv r s l hl hls hp t).symm j).1))=_
  rw [scaled_entry D hN _ _ _ hc hx hy]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [WrapBalanced.mixedLift,WrapBalanced.extendNodes,
      rowFullEquiv,colFullEquiv,rowEquiv,colEquiv,rowSlot,colSlot,balanced_fibre_equiv,
      WrapBalanced.rowNode,WrapBalanced.colNode,xs,ys,UFMember.rowNode,UFMember.colNode,
      Matrix.one_apply,Subtype.ext_iff]

/-- All actual mixed own-fibre blocks are invertible in the Gauss
localization, as a consequence of the actual primitive core. -/
theorem actual_Dmat_unit (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (c : ι → ℕ) (r s l : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a, c a<N)
    (hx : ∀ i : Fin (s+l), xs r i<N) (hy : ∀ i : Fin (s+l), ys r i<N) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    IsUnit (Dmat (fun a => rowCoords c r s l hl hls (Sum.inl a))
      (reordered c r s l hl hls (hint_of_poleData D hN hc hx hy)).toBlocks₁₁).det := by
  intro D
  apply WrapNodes.isUnit_mixedDmat_det D
    (fun a => rowCoords c r s l hl hls (Sum.inl a))
    (fun a => colCoords c r s l hl hls (Sum.inl a))
  · intro a
    exact rowNode_lt hc hx (rowFullEquiv ι s l hl hls (Sum.inl a))
  · intro a
    exact colNode_lt hc hy (colFullEquiv ι s l hl hls (Sum.inl a))
  · exact core_colours c r s l hl hls hp
  · intro a b
    exact reordered_commutator D hN c r s l hl hls hc hx hy (Sum.inl a) (Sum.inl b)
  · exact core_primitive T hqp hN hsq hnorm hnorm0 c r s l hl hls hp hsize _

/-- The actual balanced source moment is the concrete mixed response of
its original common fibre and its two actual endpoints. -/
theorem balanced_mixedFibMom (D : PoleData Fr p N) (hN : N<p*p)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), xs r i<N)
    (hy : ∀ i:Fin (s+l), ys r i<N) (t : Fin (2*l-1)) (d : GaussLoc p)
    (hDa : IsUnit (Dmat
      (fun a => rowCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inl a))
      (reordered (fun a:Fin r => (a:ℕ)) r s l hl hls
        (hint_of_poleData D hN hc hx hy)).toBlocks₁₁).det) :
    let cr := fun a => rowCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inl a)
    let cc := fun a => colCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inl a)
    let Q := (reordered (fun a:Fin r => (a:ℕ)) r s l hl hls
      (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    WrapNodes.mixedFibMom cr (Dmat cr Q) (fun a => ellL p Fr (cr a)-d)
      (fun a => ellL p Fr (cc a)-d) ((r+(t:ℕ):ℕ):ZMod p)=
      res p (WrapBalanced.mixedResponse (p:=p) (Fr:=Fr)
        (fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+(t:ℕ):ℕ):ZMod p)} => (a.1:ℕ))
        (WrapBalanced.rowNode r s t) (WrapBalanced.colNode r s t) d) := by
  intro cr cc Q
  let DA := Dmat cr Q
  let tau : ZMod p := ((r+(t:ℕ):ℕ):ZMod p)
  let yR := fun a => ellL p Fr (cr a)-d
  let yC := fun a => ellL p Fr (cc a)-d
  have hb : ∀ a b, colOf (p:=p) cr a≠colOf cr b → DA a b=0 := by
    intro a b h; simp [DA,Dmat,h]
  change (∑ a ∈ Finset.univ.filter (fun a => colOf (p:=p) cr a=tau),
    res p ((DA⁻¹ *ᵥ yR) a)*res p (yC a))=_
  rw [WrapType.mixed_fiber_moment_response DA (colOf cr) hDa hb tau yR yC (res p)]
  let E := balanced_fibre_equiv r s l hl hls hp t
  let c0 := fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+(t:ℕ):ℕ):ZMod p)} => (a.1:ℕ)
  have hblock : (blk DA (colOf cr) tau).submatrix E.symm E.symm=
      (WrapBalanced.mixedLift (p:=p) (Fr:=Fr) c0
        (WrapBalanced.rowNode r s t) (WrapBalanced.colNode r s t)).map (algebraMap _ (GaussLoc p)) := by
    rw [← balanced_fibre_lift D hN r s l hl hls hp hc hx hy t]
    apply Matrix.ext
    intro i j
    have he : colOf (p:=p) cr (E.symm i).1=colOf cr (E.symm j).1 :=
      ((E.symm i).2).trans ((E.symm j).2).symm
    change (if colOf (p:=p) cr (E.symm i).1=colOf cr (E.symm j).1 then
      algebraMap (LocRing p)[X] (GaussLoc p) (Q (E.symm i).1 (E.symm j).1) else 0)=_
    rw [if_pos he]
    rfl
  have hr : (fun a => yR a.1) ∘ E.symm=
      fun a => ellL p Fr (WrapBalanced.extendNodes c0 (WrapBalanced.rowNode r s t) a)-d := by
    funext a
    change ellL p Fr (rowCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inl (E.symm a).1))-d=_
    rw [(balanced_fibre_coords r s l hl hls hp t a).1]
  have hcc : (fun a => yC a.1) ∘ E.symm=
      fun a => ellL p Fr (WrapBalanced.extendNodes c0 (WrapBalanced.colNode r s t) a)-d := by
    funext a
    change ellL p Fr (colCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inl (E.symm a).1))-d=_
    rw [(balanced_fibre_coords r s l hl hls hp t a).2]
  have hh := WrapTransport.response_reindex (blk DA (colOf cr) tau) E.symm E.symm
    (fun a => yR a.1) (fun a => yC a.1)
  erw [hblock,hr,hcc] at hh
  exact congrArg (res p) hh.symm

/-- Primitivity of the actual mixed core supplies the inverse of each
concrete balanced fibre; no template-invertibility premise remains. -/
theorem balanced_fibre_inverse_unit (D : PoleData Fr p N) (hN : N<p*p)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), xs r i<N)
    (hy : ∀ i:Fin (s+l), ys r i<N) (t : Fin (2*l-1))
    (hDa : IsUnit (Dmat
      (fun a => rowCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inl a))
      (reordered (fun a:Fin r => (a:ℕ)) r s l hl hls
        (hint_of_poleData D hN hc hx hy)).toBlocks₁₁).det) :
    IsUnit ((WrapBalanced.mixedLift (p:=p) (Fr:=Fr)
      (fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+(t:ℕ):ℕ):ZMod p)} => (a.1:ℕ))
      (WrapBalanced.rowNode r s t) (WrapBalanced.colNode r s t)).map
        (algebraMap _ (GaussLoc p))).det := by
  let cr := fun a => rowCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inl a)
  let Q := (reordered (fun a:Fin r => (a:ℕ)) r s l hl hls (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
  let DA := Dmat cr Q
  let tau : ZMod p := ((r+(t:ℕ):ℕ):ZMod p)
  let E := balanced_fibre_equiv r s l hl hls hp t
  have hb : ∀ a b, colOf (p:=p) cr a≠colOf cr b → DA a b=0 := by
    intro a b h; simp [DA,Dmat,h]
  have hu := (inv_restrict DA (colOf cr) hDa hb tau).1
  have he : (blk DA (colOf cr) tau).submatrix E.symm E.symm=
      (WrapBalanced.mixedLift (p:=p) (Fr:=Fr)
        (fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+(t:ℕ):ℕ):ZMod p)} => (a.1:ℕ))
        (WrapBalanced.rowNode r s t) (WrapBalanced.colNode r s t)).map
          (algebraMap _ (GaussLoc p)) := by
    rw [← balanced_fibre_lift D hN r s l hl hls hp hc hx hy t]
    apply Matrix.ext
    intro i j
    have heq : colOf (p:=p) cr (E.symm i).1=colOf cr (E.symm j).1 :=
      ((E.symm i).2).trans ((E.symm j).2).symm
    change (if colOf (p:=p) cr (E.symm i).1=colOf cr (E.symm j).1 then
      algebraMap (LocRing p)[X] (GaussLoc p) (Q (E.symm i).1 (E.symm j).1) else 0)=_
    rw [if_pos heq]
    rfl
  erw [← he,Matrix.det_submatrix_equiv_self]
  exact hu

/-- The actual source moment uses the same lower/upper local response
in either balanced parity. -/
theorem balanced_moment_normalize (D : PoleData Fr p N) (hN : N<p*p)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), xs r i<N)
    (hy : ∀ i:Fin (s+l), ys r i<N) (t : Fin (2*l-1)) (d : GaussLoc p)
    (hDa : IsUnit (Dmat
      (fun a => rowCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inl a))
      (reordered (fun a:Fin r => (a:ℕ)) r s l hl hls
        (hint_of_poleData D hN hc hx hy)).toBlocks₁₁).det) :
    let cr := fun a => rowCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inl a)
    let cc := fun a => colCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inl a)
    let Q := (reordered (fun a:Fin r => (a:ℕ)) r s l hl hls
      (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    WrapNodes.mixedFibMom cr (Dmat cr Q) (fun a => ellL p Fr (cr a)-d)
      (fun a => ellL p Fr (cc a)-d) ((r+(t:ℕ):ℕ):ZMod p)=
      res p (WrapBalanced.mixedResponse (p:=p) (Fr:=Fr)
        (fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+(t:ℕ):ℕ):ZMod p)} => (a.1:ℕ))
        (r+(t:ℕ)) (r+(t:ℕ)+p) d) := by
  intro cr cc Q
  have hh := balanced_mixedFibMom D hN r s l hl hls hp hc hx hy t d hDa
  unfold WrapBalanced.rowNode WrapBalanced.colNode at hh
  rw [rowBalanced_node,colBalanced_node] at hh
  by_cases ht : (t:ℕ)%2=0
  · simpa only [ht,↓reduceIte,Nat.add_zero,← hp] using hh
  · simp only [ht,↓reduceIte,Nat.add_zero,← hp] at hh
    rw [WrapBalanced.mixedResponse_swap] at hh
    exact hh

/-- Original common colour blocks are units, without a range or parity
restriction on the common-node list. -/
theorem reference_Dmat_unit (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (hc : ∀ a, c a<N) :
    IsUnit (Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)).det := by
  rw [WrapBalanced.commonLift_eq_core D hN c (fun i:Fin 0 => Fin.elim0 i)
    (fun i:Fin 0 => Fin.elim0 i) hc (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)]
  exact isUnit_Dmat_det D c hc _
    (sLift_core_rel D hN c _ _ hc (fun i:Fin 0 => Fin.elim0 i) (fun i:Fin 0 => Fin.elim0 i))
    (sLift_core_det c _ _ _)

/-- Exact local block of the virtual reference core in the lower-node
fibre ordering. -/
theorem virtual_fibre_Dmat (r b t : ℕ) (hbp : b<p) (ht : t<b) :
    let cv := fun a:Fin (r+b) => (a:ℕ)
    let DV := Dmat cv (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv)
    let E := virtual_fibre_equiv r b t hbp ht
    (blk DV (colOf cv) ((r+t:ℕ):ZMod p)).submatrix E.symm E.symm=
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr)
        (WrapBalanced.extendNodes (fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+t:ℕ):ZMod p)} =>
          (a.1:ℕ)) (r+t))).map (algebraMap _ (GaussLoc p)) := by
  intro cv DV E
  rw [← virtual_fibre_lift r b t hbp ht]
  apply Matrix.ext
  intro i j
  have he : colOf (p:=p) cv (E.symm i).1=colOf cv (E.symm j).1 :=
    ((E.symm i).2).trans ((E.symm j).2).symm
  change (if colOf (p:=p) cv (E.symm i).1=colOf cv (E.symm j).1 then
    algebraMap (LocRing p)[X] (GaussLoc p)
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv (E.symm i).1 (E.symm j).1) else 0)=_
  rw [if_pos he]
  rfl

/-- The virtual source moment is exactly the original common response
with its unique lower balanced node appended. -/
theorem virtual_fibre_moment (r b t : ℕ) (hbp : b<p) (ht : t<b) (d : GaussLoc p)
    (hDu : IsUnit (Dmat (fun a:Fin (r+b) => (a:ℕ))
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun a:Fin (r+b) => (a:ℕ)))).det) :
    fibMom (fun a:Fin (r+b) => (a:ℕ))
      (Dmat (fun a:Fin (r+b) => (a:ℕ))
        (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun a:Fin (r+b) => (a:ℕ))))
      (fun a => ellL p Fr (a:ℕ)-d) ((r+t:ℕ):ZMod p)=
      res p (WrapBalanced.commonResponse (p:=p) (Fr:=Fr)
        (WrapBalanced.extendNodes (fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+t:ℕ):ZMod p)} =>
          (a.1:ℕ)) (r+t)) d) := by
  let cv := fun a:Fin (r+b) => (a:ℕ)
  let DV := Dmat cv (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv)
  let tau : ZMod p := ((r+t:ℕ):ZMod p)
  let y := fun a => ellL p Fr (cv a)-d
  have hb : ∀ a b, colOf (p:=p) cv a≠colOf cv b → DV a b=0 := by
    intro a b h; simp [DV,Dmat,h]
  change (∑ a ∈ Finset.univ.filter (fun a => colOf (p:=p) cv a=tau),
    res p ((DV⁻¹ *ᵥ y) a)*res p (y a))=_
  rw [WrapType.mixed_fiber_moment_response DV (colOf cv) hDu hb tau y y (res p)]
  let E := virtual_fibre_equiv r b t hbp ht
  have hy : (fun a => y a.1) ∘ E.symm=
      fun a => ellL p Fr (WrapBalanced.extendNodes
        (fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+t:ℕ):ZMod p)} => (a.1:ℕ)) (r+t) a)-d := by
    funext a
    change ellL p Fr ((E.symm a).1:ℕ)-d=_
    rw [virtual_fibre_coords r b t hbp ht a]
  have hh := WrapTransport.response_reindex (blk DV (colOf cv) tau) E.symm E.symm
    (fun a => y a.1) (fun a => y a.1)
  erw [virtual_fibre_Dmat r b t hbp ht,hy] at hh
  exact congrArg (res p) hh.symm

set_option maxHeartbeats 1600000 in
/-- Virtual own-direction response restricts to the same concrete
common fibre used by actual balanced cancellation. -/
theorem virtual_own_response (r b t : ℕ) (hbp : b<p) (ht : t<b)
    (z : ℕ) (hz : ((z:ℕ):ZMod p)=((r+t:ℕ):ZMod p)) (d : GaussLoc p)
    (hDu : IsUnit (Dmat (fun a:Fin (r+b) => (a:ℕ))
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun a:Fin (r+b) => (a:ℕ)))).det) :
    let cv := fun a:Fin (r+b) => (a:ℕ)
    let cref := WrapBalanced.extendNodes
      (fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+t:ℕ):ZMod p)} => (a.1:ℕ)) (r+t)
    (sOwn cv z (loewRow p Fr cv z) ᵥ*
      (Dmat cv (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv))⁻¹) ⬝ᵥ
        (fun a => ellL p Fr (cv a)-d)=
    (sOwn cref z (loewRow p Fr cref z) ᵥ*
      (Dmat cref (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cref))⁻¹) ⬝ᵥ
        (fun a => ellL p Fr (cref a)-d) := by
  intro cv cref
  let DV := Dmat cv (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv)
  let tau : ZMod p := ((r+t:ℕ):ZMod p)
  let E := virtual_fibre_equiv r b t hbp ht
  have hb : ∀ a b, colOf (p:=p) cv a≠colOf cv b → DV a b=0 := by
    intro a b h; simp [DV,Dmat,h]
  have hs : ∀ a, colOf (p:=p) cv a≠tau → sOwn cv z (loewRow p Fr cv z) a=0 := by
    intro a h
    have h' : colOf (p:=p) cv a≠((r+t:ℕ):ZMod p) := h
    simp only [sOwn,hz,if_neg h']
  have hc : ∀ a, colOf (p:=p) cref a=((z:ℕ):ZMod p) := by
    intro a
    change ((cref a:ℕ):ZMod p)=((z:ℕ):ZMod p)
    dsimp only [cref]
    rw [← virtual_fibre_coords r b t hbp ht a]
    exact ((E.symm a).2).trans hz.symm
  have hDm : Dmat cref (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cref)=
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cref).map (algebraMap _ (GaussLoc p)) := by
    apply Matrix.ext
    intro a b
    simp only [Dmat,Matrix.of_apply,hc a,hc b,↓reduceIte,Matrix.map_apply]
  rw [own_fiber_form DV (colOf cv) hDu hb tau (sOwn cv z (loewRow p Fr cv z))
    (fun a => ellL p Fr (cv a)-d) hs,hDm]
  change ((fun a : {a // colOf (p:=p) cv a=tau} => sOwn cv z (loewRow p Fr cv z) a.1) ᵥ*
    (blk DV (colOf cv) tau)⁻¹) ⬝ᵥ (fun a => ellL p Fr (cv a.1)-d)=_
  rw [← Matrix.dotProduct_mulVec,← Matrix.dotProduct_mulVec]
  have hy : (fun a => ellL p Fr (cv a.1)-d) ∘ E.symm=
      fun a => ellL p Fr (cref a)-d := by
    funext a
    change ellL p Fr ((E.symm a).1:ℕ)-d=ellL p Fr (cref a)-d
    rw [virtual_fibre_coords r b t hbp ht a]
  have hsig : (fun a => sOwn cv z (loewRow p Fr cv z) a.1) ∘ E.symm=
      sOwn cref z (loewRow p Fr cref z) := by
    funext a
    have he : cv (E.symm a).1=cref a := virtual_fibre_coords r b t hbp ht a
    simp only [Function.comp_def,sOwn,colOf,loewRow,he]
    rfl
  have hh := WrapTransport.response_reindex (blk DV (colOf cv) tau) E.symm E.symm
    (fun a => ellL p Fr (cv a.1)-d) (fun a => sOwn cv z (loewRow p Fr cv z) a.1)
  erw [virtual_fibre_Dmat r b t hbp ht,hsig,hy] at hh
  exact hh.symm

/-- Matching colours make transposition exchange the two mixed
coordinate maps in the exact colour-block part. -/
theorem Dmat_transpose {α : Type} [Fintype α] [DecidableEq α]
    (cr cc : α → ℕ) (hcol : ∀ a, colOf (p:=p) cr a=colOf cc a)
    (Q : Matrix α α (LocRing p)[X]) : Dmat cc Qᵀ=(Dmat cr Q)ᵀ := by
  apply Matrix.ext
  intro a b
  change (if colOf (p:=p) cc a=colOf cc b then
    algebraMap (LocRing p)[X] (GaussLoc p) (Q b a) else 0)=
    (if colOf (p:=p) cr b=colOf cr a then
      algebraMap (LocRing p)[X] (GaussLoc p) (Q b a) else 0)
  by_cases h : colOf (p:=p) cr a=colOf cr b
  · have he : colOf (p:=p) cc a=colOf cc b := (hcol a).symm.trans (h.trans (hcol b))
    rw [if_pos he,if_pos h.symm]
  · have he : colOf (p:=p) cc a≠colOf cc b :=
      fun he => h ((hcol a).trans (he.trans ((hcol b).symm)))
    rw [if_neg he,if_neg (Ne.symm h)]

/-- The transposed mixed own fibres inherit the actual inverse units. -/
theorem Dmat_transpose_unit {α : Type} [Fintype α] [DecidableEq α]
    (cr cc : α → ℕ) (hcol : ∀ a, colOf (p:=p) cr a=colOf cc a)
    (Q : Matrix α α (LocRing p)[X]) (hD : IsUnit (Dmat cr Q).det) :
    IsUnit (Dmat cc Qᵀ).det := by
  rw [Dmat_transpose cr cc hcol Q,Matrix.det_transpose]
  exact hD

/-- The column-axis own response restricts literally to the original
transposed common fibre; no symmetry of the mixed core is assumed. -/
theorem surplus_col_own_response (c : ι → ℕ) (r s l t : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (htlo : r+2*l-1≤t) (hthi : t<r+p)
    (hint : ∀ i j, (p:ℚ)^2*Fr.Mn (rowNode c (xs r (m:=s+l)) i)
      (colNode c (ys r (m:=s+l)) j) ∈ LocRing p)
    (sigma : (ι ⊕ Fin (2*l-1)) → (LocRing p)[X])
    (v : (ι ⊕ Fin (2*l-1)) → GaussLoc p)
    (hDa : IsUnit (Dmat (fun a => colCoords c r s l hl hls (Sum.inl a))
      (reordered c r s l hl hls hint).toBlocks₁₁ᵀ).det)
    (hDo : IsUnit (Dmat c (sLift c (xs r) (ys r) hint).toBlocks₁₁ᵀ).det) :
    (sOwn (fun a => colCoords c r s l hl hls (Sum.inl a)) t sigma ᵥ*
      (Dmat (fun a => colCoords c r s l hl hls (Sum.inl a))
        (reordered c r s l hl hls hint).toBlocks₁₁ᵀ)⁻¹) ⬝ᵥ v =
      (sOwn c t (fun a => sigma (Sum.inl a)) ᵥ*
        (Dmat c (sLift c (xs r) (ys r) hint).toBlocks₁₁ᵀ)⁻¹) ⬝ᵥ
          (fun a => v (Sum.inl a)) := by
  let cr := fun a => colCoords c r s l hl hls (Sum.inl a)
  let DA := Dmat cr (reordered c r s l hl hls hint).toBlocks₁₁ᵀ
  let DO := Dmat c (sLift c (xs r) (ys r) hint).toBlocks₁₁ᵀ
  let tau : ZMod p := ((t:ℕ):ZMod p)
  have hbA : ∀ a b, colOf (p:=p) cr a≠colOf cr b → DA a b=0 := by
    intro a b h; simp [DA,Dmat,h]
  have hbO : ∀ a b, colOf (p:=p) c a≠colOf c b → DO a b=0 := by
    intro a b h; simp [DO,Dmat,h]
  have hsA : ∀ a, colOf (p:=p) cr a≠tau → sOwn cr t sigma a=0 := by
    intro a h; simp [sOwn,h,tau] at *
  have hsO : ∀ a, colOf (p:=p) c a≠tau → sOwn c t (fun a => sigma (Sum.inl a)) a=0 := by
    intro a h; simp [sOwn,h,tau] at *
  change (sOwn cr t sigma ᵥ* DA⁻¹) ⬝ᵥ v =
    (sOwn c t (fun a => sigma (Sum.inl a)) ᵥ* DO⁻¹) ⬝ᵥ (fun a => v (Sum.inl a))
  rw [own_fiber_form DA (colOf cr) hDa hbA tau (sOwn cr t sigma) v hsA,
    own_fiber_form DO (colOf c) hDo hbO tau
      (sOwn c t (fun a => sigma (Sum.inl a))) (fun a => v (Sum.inl a)) hsO]
  let E := surplus_col_fibre_equiv c r s l t hl hls hp htlo hthi
  have hh := WrapTransport.response_reindex (blk DA (colOf cr) tau) E.symm E.symm
    (fun a => v a.1) (fun a => sOwn cr t sigma a.1)
  rw [Matrix.dotProduct_mulVec,Matrix.dotProduct_mulVec] at hh
  exact hh.symm

/-- The actual surplus row has its original constant Loewner load. -/
theorem surplus_row_load (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hc : ∀ a,c a<N) (hx : ∀ i:Fin (s+l),xs r i<N) (hy : ∀ i:Fin (s+l),ys r i<N)
    (z : Fin (s+1-l)) :
    let A := reordered c r s l hl hls (hint_of_poleData D hN hc hx hy)
    let cc := fun a => colCoords c r s l hl hls (Sum.inl a)
    A.toBlocks₂₁ z=loewRow p Fr cc (rowCoords c r s l hl hls (Sum.inr z)) := by
  intro A cc
  funext a
  have hh := scaled_entry D hN c (xs r) (ys r) hc hx hy
    (rowFullEquiv ι s l hl hls (Sum.inr z)) (colFullEquiv ι s l hl hls (Sum.inl a))
  change sLift c (xs r) (ys r) _ _ _=_
  rw [hh]
  have hz : Matrix.fromBlocks ((X:(LocRing p)[X]) • (1:Matrix ι ι (LocRing p)[X])) 0 0 0
      (rowFullEquiv ι s l hl hls (Sum.inr z)) (colFullEquiv ι s l hl hls (Sum.inl a))=0 := by
    change Matrix.fromBlocks _ _ _ _ (Sum.inr _) _=0
    cases colFullEquiv ι s l hl hls (Sum.inl a) <;> rfl
  rw [hz,add_zero]
  rfl

/-- The actual surplus column has its original constant Loewner load. -/
theorem surplus_col_load (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hc : ∀ a,c a<N) (hx : ∀ i:Fin (s+l),xs r i<N) (hy : ∀ i:Fin (s+l),ys r i<N)
    (z : Fin (s+1-l)) :
    let A := reordered c r s l hl hls (hint_of_poleData D hN hc hx hy)
    let cr := fun a => rowCoords c r s l hl hls (Sum.inl a)
    (fun a => A.toBlocks₁₂ a z)=loewRow p Fr cr (colCoords c r s l hl hls (Sum.inr z)) := by
  intro A cr
  funext a
  have hh := scaled_entry D hN c (xs r) (ys r) hc hx hy
    (rowFullEquiv ι s l hl hls (Sum.inl a)) (colFullEquiv ι s l hl hls (Sum.inr z))
  change sLift c (xs r) (ys r) _ _ _=_
  rw [hh]
  have hz : Matrix.fromBlocks ((X:(LocRing p)[X]) • (1:Matrix ι ι (LocRing p)[X])) 0 0 0
      (rowFullEquiv ι s l hl hls (Sum.inl a)) (colFullEquiv ι s l hl hls (Sum.inr z))=0 := by
    change Matrix.fromBlocks _ _ _ _ _ (Sum.inr _)=0
    cases rowFullEquiv ι s l hl hls (Sum.inl a) <;> rfl
  rw [hz,add_zero]
  change Polynomial.C (Hybrid.liftQ p ((p:ℚ)^2*Fr.Mn _ _))=
    Polynomial.C (Hybrid.liftQ p ((p:ℚ)^2*Fr.Mn _ _))
  rw [frame_Mn_symm Fr]
  rfl

end CatalanCore.Uniform.Content.UFSimple.WrapActual

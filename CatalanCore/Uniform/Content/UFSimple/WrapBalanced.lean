module

public import CatalanCore.Uniform.Content.UFSimple.WrapGeometry
public import CatalanCore.Uniform.Content.UFSimple.WrapPeriod
public import CatalanCore.Uniform.Content.UFSimple.WrapAlgebra
public import CatalanCore.Uniform.Content.UFSimple.WrapTransport

@[expose] public section

/-! # Actual balanced constant block is invertible after reduction

Each paired row/column differs by exactly p. Different pairs have distinct
colours. Thus reduction is diagonal with the nonzero full-period entries.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.UFMember

namespace CatalanCore.Uniform.Content.UFSimple.WrapBalanced

open WrapGeometry

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {q o : ℕ}

def rowNode (r s t : ℕ) : ℕ := r+2*rowBalanced s t
def colNode (r s t : ℕ) : ℕ := r+2*colBalanced s t+1

/-- Actual constant balanced block, lifted with its entrywise integral bound. -/
noncomputable def lift (r s l : ℕ)
    (hint : ∀ i j : Fin (2*l-1), (p:ℚ)^2*Fr.Mn (rowNode r s i) (colNode r s j) ∈ LocRing p) :
    Matrix (Fin (2*l-1)) (Fin (2*l-1)) (LocRing p) :=
  Matrix.of fun i j => ⟨(p:ℚ)^2*Fr.Mn (rowNode r s i) (colNode r s j),hint i j⟩

theorem row_colour (r s t : ℕ) (hp : p=2*s+1) :
    ((rowNode r s t : ℕ) : ZMod p) = ((r+t : ℕ) : ZMod p) := by
  unfold rowNode
  rw [rowBalanced_node]
  by_cases ht : t%2=0 <;> simp [ht, ← hp, Nat.cast_add, ZMod.natCast_self]

theorem col_colour (r s t : ℕ) (hp : p=2*s+1) :
    ((colNode r s t : ℕ) : ZMod p) = ((r+t : ℕ) : ZMod p) := by
  unfold colNode
  rw [colBalanced_node]
  by_cases ht : t%2=0 <;> simp [ht, ← hp, Nat.cast_add, ZMod.natCast_self]

theorem pair_colours_distinct (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (i j : Fin (2*l-1)) (hij : i≠j) :
    ((rowNode r s i : ℕ) : ZMod p) ≠ ((colNode r s j : ℕ) : ZMod p) := by
  rw [row_colour r s i hp, col_colour r s j hp]
  intro he
  have he' : ((i:ℕ) : ZMod p) = ((j:ℕ) : ZMod p) := by
    apply add_left_cancel (a := (r : ZMod p))
    simpa only [Nat.cast_add] using he
  have hv := (ZMod.natCast_eq_natCast_iff' (i:ℕ) (j:ℕ) p).mp he'
  have hi := i.2
  have hj := j.2
  rw [Nat.mod_eq_of_lt (by omega : (i:ℕ)<p),
    Nat.mod_eq_of_lt (by omega : (j:ℕ)<p)] at hv
  exact hij (Fin.ext hv)

theorem row_lt (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hsize : r+2*(s+l)≤N) (i : Fin (2*l-1)) : rowNode r s i<N := by
  have hh := rowBalanced_bound hl hls i.2
  unfold rowNode
  omega

theorem col_lt (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hsize : r+2*(s+l)≤N) (i : Fin (2*l-1)) : colNode r s i<N := by
  have hh := colBalanced_bound hl hls i.2
  unfold colNode
  omega

/-- Every actual diagonal pair has nonzero reduced entry. -/
theorem diagonal_ne (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hp : p=2*s+1) (hsize : r+2*(s+l)≤N) (i : Fin (2*l-1)) :
    red p ((p:ℚ)^2*Fr.Mn (rowNode r s i) (colNode r s i)) ≠ 0 := by
  have hi := i.2
  have ha : r+(i:ℕ)+p<N := by omega
  have hh := WrapPeriod.balanced_entry_ne T hqp hN hsq hnorm hnorm0 ha
  unfold rowNode colNode
  rw [rowBalanced_node, colBalanced_node]
  by_cases ht : (i:ℕ)%2=0
  · simpa only [ht, ↓reduceIte, Nat.add_zero, ← hp] using hh
  · simp only [ht, ↓reduceIte, Nat.add_zero, ← hp]
    rw [frame_Mn_symm]
    exact hh

/-- The actual reduced balanced block is diagonal and has nonzero determinant. -/
theorem det_ne (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hint : ∀ i j : Fin (2*l-1), (p:ℚ)^2*Fr.Mn (rowNode r s i) (colNode r s j) ∈ LocRing p) :
    ((lift r s l hint).map (redQ p)).det ≠ 0 := by
  let D := twoTermPoleData T hN.le hsq hnorm hnorm0
  have hz : ∀ i j : Fin (2*l-1), i≠j → redQ p (lift r s l hint i j)=0 := by
    intro i j hij
    have hg := D.good_cross (row_lt r s l hl hls hsize i)
      (col_lt r s l hl hls hsize j)
      (sub_ne_zero.mpr (Ne.symm (pair_colours_distinct r s l hl hls hp i j hij)))
    exact redQ_sq_eq_zero hg.mem (hint i j)
  have hd : ∀ i : Fin (2*l-1), redQ p (lift r s l hint i i)≠0 := by
    intro i
    exact diagonal_ne T hqp hN hsq hnorm hnorm0 r s l hl hls hp hsize i
  have he : (lift r s l hint).map (redQ p) =
      Matrix.diagonal (fun i => redQ p (lift r s l hint i i)) := by
    ext i j
    by_cases hij : i=j
    · subst j; simp
    · simp [Matrix.diagonal_apply, hij, hz i j hij]
  rw [he, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)

section OneFibre

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A common fibre with its actual lower balanced node appended. -/
def extendNodes (c : ι → ℕ) (lo : ℕ) : ι ⊕ Unit → ℕ := Sum.elim c (fun _ => lo)

/-- The actual polynomial common-fibre lift, before the balanced column
is replaced. Every common index carries its original spectral diagonal. -/
noncomputable def commonLift (c : ι → ℕ) : Matrix ι ι (LocRing p)[X] :=
  (Matrix.of fun i j => Polynomial.C (Hybrid.liftQ p ((p:ℚ)^2*Fr.Mn (c i) (c j))))+
    (X : (LocRing p)[X]) • 1

/-- Actual mixed fibre with the lower node on the row axis and the
upper node on the column axis. Only original common indices carry X. -/
noncomputable def mixedLift (c : ι → ℕ) (lo hi : ℕ) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) (LocRing p)[X] :=
  (Matrix.of fun i j => Polynomial.C (Hybrid.liftQ p ((p:ℚ)^2*
    Fr.Mn (extendNodes c lo i) (extendNodes c hi j))))+
      Matrix.fromBlocks ((X : (LocRing p)[X]) • (1 : Matrix ι ι (LocRing p)[X])) 0 0 0

/-- Exact entrywise column replacement of the actual frame fibre.
In particular the appended lower diagonal loses its spectral X. -/
theorem mixedLift_eq_updateCol (c : ι → ℕ) (lo hi : ℕ) :
    mixedLift (p:=p) (Fr:=Fr) c lo hi =
      (commonLift (p:=p) (Fr:=Fr) (extendNodes c lo)).updateCol (Sum.inr ())
        (loewRow p Fr (extendNodes c lo) hi) := by
  ext i j
  rcases j with j | j
  · rw [Matrix.updateCol_ne (by simp)]
    rcases i with i | i <;>
      simp [mixedLift,commonLift,extendNodes,Matrix.one_apply]
  · cases j
    rw [Matrix.updateCol_self]
    rcases i with i | i <;>
      simp [mixedLift,extendNodes,loewRow,frame_Mn_symm Fr hi]

/-- The original common-fibre polynomial is symmetric. -/
theorem commonLift_symm (c : ι → ℕ) :
    (commonLift (p:=p) (Fr:=Fr) c)ᵀ=commonLift (p:=p) (Fr:=Fr) c := by
  ext i j
  by_cases hij : i=j
  · subst j; rfl
  · simp [commonLift,Matrix.one_apply,hij,Ne.symm hij,frame_Mn_symm Fr (c j)]

/-- The actual zone prefix load satisfies the column-replacement load
identity of its own common fibre. All coordinates have this one colour. -/
theorem actual_zone_load (c : ι → ℕ) (t : ℕ)
    (hcol : ∀ a, colOf (p:=p) c a=((t:ℕ):ZMod p))
    (hB : IsUnit (1-∑ j, (sOwn c t (loewRow p Fr c t) ᵥ*
      (Dmat c (commonLift (p:=p) (Fr:=Fr) c))⁻¹) j)) :
    let Q := (commonLift (p:=p) (Fr:=Fr) c).map (algebraMap _ (GaussLoc p))
    let d := dirOf Fr c (commonLift (p:=p) (Fr:=Fr) c) t (loewRow p Fr c t)
    let u := fun a => ellL p Fr (c a)-d
    ellL p Fr t-d=(u ᵥ* Q⁻¹) ⬝ᵥ
      (fun a => algebraMap _ (GaussLoc p) (loewRow p Fr c t a)) := by
  intro Q d u
  have hDm : Dmat c (commonLift (p:=p) (Fr:=Fr) c)=Q := by
    ext a b
    simp only [Dmat,Matrix.of_apply,hcol a,hcol b,↓reduceIte,Matrix.map_apply]
    rfl
  have hs : sOwn c t (loewRow p Fr c t)=
      fun a => algebraMap _ (GaussLoc p) (loewRow p Fr c t a) := by
    funext a; simp only [sOwn,hcol a,↓reduceIte]
  have hz := own_dir_zero Fr c (commonLift (p:=p) (Fr:=Fr) c) t (loewRow p Fr c t) hB
  rw [hDm,hs] at hz
  have hQ : Qᵀ=Q := by
    change ((commonLift (p:=p) (Fr:=Fr) c).map (algebraMap _ (GaussLoc p)))ᵀ=_
    rw [← Matrix.transpose_map,commonLift_symm]
  have he : ellL p Fr t-d=
      (fun a => algebraMap _ (GaussLoc p) (loewRow p Fr c t a)) ⬝ᵥ Q⁻¹ *ᵥ u := by
    rw [Matrix.dotProduct_mulVec]
    exact sub_eq_zero.mp hz
  rw [WrapTransport.response_transpose Q u _,hQ,Matrix.dotProduct_mulVec] at he
  exact he

/-- Exact mixed response of the ACTUAL balanced fibre in ordinary
transport position. The replaced load is the actual upper-node prefix. -/
theorem actual_column_response (c : ι → ℕ) (lo hi : ℕ)
    (hcol : ∀ a, colOf (p:=p) (extendNodes c lo) a=((hi:ℕ):ZMod p))
    (hB : IsUnit (1-∑ j, (sOwn (extendNodes c lo) hi (loewRow p Fr (extendNodes c lo) hi) ᵥ*
      (Dmat (extendNodes c lo) (commonLift (p:=p) (Fr:=Fr) (extendNodes c lo)))⁻¹) j))
    (hQ : IsUnit ((commonLift (p:=p) (Fr:=Fr) (extendNodes c lo)).map
      (algebraMap _ (GaussLoc p))).det)
    (hM : IsUnit ((mixedLift (p:=p) (Fr:=Fr) c lo hi).map
      (algebraMap _ (GaussLoc p))).det) :
    let d := dirOf Fr (extendNodes c lo) (commonLift (p:=p) (Fr:=Fr) (extendNodes c lo)) hi
      (loewRow p Fr (extendNodes c lo) hi)
    (fun a => ellL p Fr (extendNodes c hi a)-d) ⬝ᵥ
      ((mixedLift (p:=p) (Fr:=Fr) c lo hi).map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
        (fun a => ellL p Fr (extendNodes c lo a)-d) =
      (fun a => ellL p Fr (extendNodes c lo a)-d) ⬝ᵥ
        ((commonLift (p:=p) (Fr:=Fr) (extendNodes c lo)).map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
          (fun a => ellL p Fr (extendNodes c lo a)-d) := by
  intro d
  let Q := (commonLift (p:=p) (Fr:=Fr) (extendNodes c lo)).map (algebraMap _ (GaussLoc p))
  let sig := fun a => algebraMap _ (GaussLoc p) (loewRow p Fr (extendNodes c lo) hi a)
  let u := fun a => ellL p Fr (extendNodes c lo a)-d
  have hz := actual_zone_load (extendNodes c lo) hi hcol hB
  have hmap : (mixedLift (p:=p) (Fr:=Fr) c lo hi).map (algebraMap _ (GaussLoc p)) =
      Q.updateCol (Sum.inr ()) sig := by
    rw [mixedLift_eq_updateCol,Matrix.map_updateCol]
    rfl
  have hv : (fun a => ellL p Fr (extendNodes c hi a)-d)=
      Function.update u (Sum.inr ()) (ellL p Fr hi-d) := by
    funext a
    rcases a with a | a
    · simp [u,extendNodes]
    · cases a; simp [extendNodes]
  have hh := WrapAlgebra.updateCol_response Q hQ u sig (Sum.inr ()) (by rw [← hmap]; exact hM)
  rw [hv,hz,hmap]
  exact hh

/-- Exact mixed response of the actual balanced fibre in top-extension
position. The lower-node load is fixed by its own-direction identity. -/
theorem actual_border_response (c : ι → ℕ) (lo hi : ℕ)
    (hcol : ∀ a, colOf (p:=p) c a=((lo:ℕ):ZMod p))
    (hB : IsUnit (1-∑ j, (sOwn c lo (loewRow p Fr c lo) ᵥ*
      (Dmat c (commonLift (p:=p) (Fr:=Fr) c))⁻¹) j))
    (hQ : IsUnit ((commonLift (p:=p) (Fr:=Fr) c).map (algebraMap _ (GaussLoc p))).det)
    (hM : IsUnit ((mixedLift (p:=p) (Fr:=Fr) c lo hi).map (algebraMap _ (GaussLoc p))).det) :
    let d := dirOf Fr c (commonLift (p:=p) (Fr:=Fr) c) lo (loewRow p Fr c lo)
    (fun a => ellL p Fr (extendNodes c hi a)-d) ⬝ᵥ
      ((mixedLift (p:=p) (Fr:=Fr) c lo hi).map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
        (fun a => ellL p Fr (extendNodes c lo a)-d) =
      (fun a => ellL p Fr (c a)-d) ⬝ᵥ
        ((commonLift (p:=p) (Fr:=Fr) c).map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
          (fun a => ellL p Fr (c a)-d) := by
  intro d
  let f := algebraMap (LocRing p)[X] (GaussLoc p)
  let Q := (commonLift (p:=p) (Fr:=Fr) c).map f
  let sx := fun a => f (loewRow p Fr c lo a)
  let sy := fun a => f (loewRow p Fr c hi a)
  let h := f (Polynomial.C (Hybrid.liftQ p ((p:ℚ)^2*Fr.Mn lo hi)))
  let u := fun a => ellL p Fr (c a)-d
  have hsym : Qᵀ=Q := by
    change ((commonLift (p:=p) (Fr:=Fr) c).map f)ᵀ=_
    rw [← Matrix.transpose_map,commonLift_symm]
  have hz := actual_zone_load c lo hcol hB
  have hx : sx ⬝ᵥ Q⁻¹ *ᵥ u=ellL p Fr lo-d := by
    rw [WrapTransport.response_transpose Q u sx,hsym,Matrix.dotProduct_mulVec]
    exact hz.symm
  have hm : (mixedLift (p:=p) (Fr:=Fr) c lo hi).map f=
      Matrix.fromBlocks Q (Matrix.of fun i (_:Unit) => sy i)
        (Matrix.of fun (_:Unit) j => sx j) (Matrix.of fun (_ _:Unit) => h) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [mixedLift,commonLift,extendNodes,Q,sx,sy,h,f,loewRow,frame_Mn_symm Fr hi]
  have hh := WrapAlgebra.mixedBorder_response_mixed Q hQ u u sx sy h
    (ellL p Fr lo-d) (ellL p Fr hi-d) hx (by rw [← hm]; exact hM)
  have hv (z : ℕ) : (fun a => ellL p Fr (extendNodes c z a)-d)=
      Sum.elim u (fun _:Unit => ellL p Fr z-d) := by
    funext a; rcases a with a | a <;> rfl
  rw [hm,hv hi,hv lo]
  exact hh

/-- The raw common-fibre lift equals the actual common block. -/
theorem commonLift_eq_core {κ : Type} [Fintype κ] [DecidableEq κ]
    (D : PoleData Fr p N) (hN : N<p*p) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a<N) (hx : ∀ i, xs i<N) (hy : ∀ j, ys j<N) :
    commonLift (p:=p) (Fr:=Fr) c=(sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ := by
  ext a b
  rw [sLift_core_entry D hN c xs ys hc hx hy]
  by_cases hab : a=b <;> simp [commonLift,Matrix.one_apply,hab]

/-- The raw mixed-fibre lift equals the original matrix entries in the
scaled gauge, including precisely the original common spectral indices. -/
theorem mixedLift_eq_actual (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (lo hi : ℕ) (hc : ∀ a, c a<N) (hlo : lo<N) (hhi : hi<N) :
    mixedLift (p:=p) (Fr:=Fr) c lo hi=
      sLift c (fun _:Unit => lo) (fun _:Unit => hi)
        (hint_of_poleData D hN hc (fun _ => hlo) (fun _ => hhi)) := by
  have he : (sConst c (fun _:Unit => lo) (fun _:Unit => hi)
      (hint_of_poleData D hN hc (fun _ => hlo) (fun _ => hhi))).map Polynomial.C =
      Matrix.of (fun i j => Polynomial.C (Hybrid.liftQ p ((p:ℚ)^2*
        Fr.Mn (extendNodes c lo i) (extendNodes c hi j)))) := by
    apply Matrix.ext
    intro i j
    exact congrArg Polynomial.C (sConst_eq_liftQ D hN c (fun _:Unit => lo) (fun _:Unit => hi)
      hc (fun _ => hlo) (fun _ => hhi) i j)
  unfold mixedLift sLift
  rw [he]

/-- Vanishing of the reduced own moment identifies the intrinsic
own direction modulo p; exact equality of directions is unnecessary. -/
theorem dirOf_residue (c : ι → ℕ) (Q : Matrix ι ι (LocRing p)[X])
    (t : ℕ) (sigma : ι → (LocRing p)[X]) (d : GaussLoc p)
    (hB : IsUnit (1-∑ j, (sOwn c t sigma ᵥ* (Dmat c Q)⁻¹) j))
    (hG : res p ((ellL p Fr t-d)-(sOwn c t sigma ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ
      (fun a => ellL p Fr (c a)-d))=0) :
    res p d=res p (dirOf Fr c Q t sigma) := by
  let d0 := dirOf Fr c Q t sigma
  let g := sOwn c t sigma ᵥ* (Dmat c Q)⁻¹
  let B := 1-∑ j, g j
  have hz := own_dir_zero Fr c Q t sigma hB
  have he : ((ellL p Fr t-d)-g ⬝ᵥ (fun a => ellL p Fr (c a)-d))-
      ((ellL p Fr t-d0)-g ⬝ᵥ (fun a => ellL p Fr (c a)-d0))=(d0-d)*B := by
    rw [dot_sub_const g (fun a => ellL p Fr (c a)) d,
      dot_sub_const g (fun a => ellL p Fr (c a)) d0]
    dsimp [B]
    ring
  have hh := congrArg (res p) he
  rw [map_sub,hG,hz,map_zero,sub_zero,map_mul,map_sub] at hh
  have hBn : res p B≠0 := (hB.map (res p)).ne_zero
  have hd : res p d0-res p d=0 := (mul_eq_zero.mp hh.symm).resolve_right hBn
  exact (sub_eq_zero.mp hd).symm

/-- A reduced mixed inverse response depends only on the direction's
residue. The original matrix is fixed throughout this comparison. -/
theorem response_residue_congr {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α (GaussLoc p)) (lr lc : α → GaussLoc p)
    (d e : GaussLoc p) (h : res p d=res p e) :
    res p ((fun a => lc a-d) ⬝ᵥ M⁻¹ *ᵥ (fun a => lr a-d)) =
      res p ((fun a => lc a-e) ⬝ᵥ M⁻¹ *ᵥ (fun a => lr a-e)) := by
  simp only [RingHom.map_dotProduct,RingHom.map_mulVec,Function.comp_def,map_sub,h]

/-- Mixed response of the original local frame entries. -/
noncomputable def mixedResponse (c : ι → ℕ) (lo hi : ℕ) (d : GaussLoc p) : GaussLoc p :=
  (fun a => ellL p Fr (extendNodes c hi a)-d) ⬝ᵥ
    ((mixedLift (p:=p) (Fr:=Fr) c lo hi).map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
      (fun a => ellL p Fr (extendNodes c lo a)-d)

/-- Response of the original common local frame entries. -/
noncomputable def commonResponse (c : ι → ℕ) (d : GaussLoc p) : GaussLoc p :=
  (fun a => ellL p Fr (c a)-d) ⬝ᵥ
    ((commonLift (p:=p) (Fr:=Fr) c).map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
      (fun a => ellL p Fr (c a)-d)

/-- Actual column cancellation for a transported direction. Only the
reduced own moment must vanish; its exact lift may contain a p term. -/
theorem actual_column_response_residue (c : ι → ℕ) (lo hi : ℕ) (d : GaussLoc p)
    (hcol : ∀ a, colOf (p:=p) (extendNodes c lo) a=((hi:ℕ):ZMod p))
    (hB : IsUnit (1-∑ j, (sOwn (extendNodes c lo) hi (loewRow p Fr (extendNodes c lo) hi) ᵥ*
      (Dmat (extendNodes c lo) (commonLift (p:=p) (Fr:=Fr) (extendNodes c lo)))⁻¹) j))
    (hQ : IsUnit ((commonLift (p:=p) (Fr:=Fr) (extendNodes c lo)).map (algebraMap _ (GaussLoc p))).det)
    (hM : IsUnit ((mixedLift (p:=p) (Fr:=Fr) c lo hi).map (algebraMap _ (GaussLoc p))).det)
    (hG : res p ((ellL p Fr hi-d)-
      (sOwn (extendNodes c lo) hi (loewRow p Fr (extendNodes c lo) hi) ᵥ*
        (Dmat (extendNodes c lo) (commonLift (p:=p) (Fr:=Fr) (extendNodes c lo)))⁻¹) ⬝ᵥ
          (fun a => ellL p Fr ((extendNodes c lo) a)-d))=0) :
    res p (mixedResponse (p:=p) (Fr:=Fr) c lo hi d)=
      res p (commonResponse (p:=p) (Fr:=Fr) (extendNodes c lo) d) := by
  let d0 := dirOf Fr (extendNodes c lo) (commonLift (p:=p) (Fr:=Fr) (extendNodes c lo)) hi
    (loewRow p Fr (extendNodes c lo) hi)
  have hd := dirOf_residue (extendNodes c lo) (commonLift (p:=p) (Fr:=Fr) (extendNodes c lo)) hi
    (loewRow p Fr (extendNodes c lo) hi) d hB hG
  calc
    _ = res p (mixedResponse (p:=p) (Fr:=Fr) c lo hi d0) :=
      response_residue_congr _ (fun a => ellL p Fr (extendNodes c lo a))
        (fun a => ellL p Fr (extendNodes c hi a)) d d0 hd
    _ = res p (commonResponse (p:=p) (Fr:=Fr) (extendNodes c lo) d0) :=
      congrArg (res p) (actual_column_response c lo hi hcol hB hQ hM)
    _ = _ := response_residue_congr _ (fun a => ellL p Fr ((extendNodes c lo) a))
      (fun a => ellL p Fr ((extendNodes c lo) a)) d0 d hd.symm

/-- Actual border cancellation for a transported direction. Only the
reduced own moment must vanish; its exact lift may contain a p term. -/
theorem actual_border_response_residue (c : ι → ℕ) (lo hi : ℕ) (d : GaussLoc p)
    (hcol : ∀ a, colOf (p:=p) (c) a=((lo:ℕ):ZMod p))
    (hB : IsUnit (1-∑ j, (sOwn (c) lo (loewRow p Fr (c) lo) ᵥ*
      (Dmat (c) (commonLift (p:=p) (Fr:=Fr) (c)))⁻¹) j))
    (hQ : IsUnit ((commonLift (p:=p) (Fr:=Fr) (c)).map (algebraMap _ (GaussLoc p))).det)
    (hM : IsUnit ((mixedLift (p:=p) (Fr:=Fr) c lo hi).map (algebraMap _ (GaussLoc p))).det)
    (hG : res p ((ellL p Fr lo-d)-
      (sOwn (c) lo (loewRow p Fr (c) lo) ᵥ*
        (Dmat (c) (commonLift (p:=p) (Fr:=Fr) (c)))⁻¹) ⬝ᵥ
          (fun a => ellL p Fr ((c) a)-d))=0) :
    res p (mixedResponse (p:=p) (Fr:=Fr) c lo hi d)=
      res p (commonResponse (p:=p) (Fr:=Fr) (c) d) := by
  let d0 := dirOf Fr (c) (commonLift (p:=p) (Fr:=Fr) (c)) lo
    (loewRow p Fr (c) lo)
  have hd := dirOf_residue (c) (commonLift (p:=p) (Fr:=Fr) (c)) lo
    (loewRow p Fr (c) lo) d hB hG
  calc
    _ = res p (mixedResponse (p:=p) (Fr:=Fr) c lo hi d0) :=
      response_residue_congr _ (fun a => ellL p Fr (extendNodes c lo a))
        (fun a => ellL p Fr (extendNodes c hi a)) d d0 hd
    _ = res p (commonResponse (p:=p) (Fr:=Fr) (c) d0) :=
      congrArg (res p) (actual_border_response c lo hi hcol hB hQ hM)
    _ = _ := response_residue_congr _ (fun a => ellL p Fr ((c) a))
      (fun a => ellL p Fr ((c) a)) d0 d hd.symm

/-- Monicity of the original common core supplies the local inverse. -/
theorem commonLift_primitive (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (hc : ∀ a, c a<N) :
    phiP p (commonLift (p:=p) (Fr:=Fr) c).det≠0 := by
  rw [commonLift_eq_core D hN c (fun i:Fin 0 => Fin.elim0 i)
    (fun i:Fin 0 => Fin.elim0 i) hc (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)]
  exact sLift_core_det c _ _ _

/-- The inverse of every original common fibre is integral in the Gauss
localization, with no additional prime exceptions. -/
theorem commonLift_isUnit (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (hc : ∀ a, c a<N) :
    IsUnit ((commonLift (p:=p) (Fr:=Fr) c).map (algebraMap _ (GaussLoc p))).det :=
  isUnit_map_det _ (commonLift_primitive D hN c hc)

/-- The original own-direction denominator is automatically a unit. -/
theorem commonLift_own_unit (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (hc : ∀ a, c a<N) (t : ℕ) (ht : t<N) :
    IsUnit (1-∑ j, (sOwn c t (loewRow p Fr c t) ᵥ*
      (Dmat c (commonLift (p:=p) (Fr:=Fr) c))⁻¹) j) := by
  rw [commonLift_eq_core D hN c (fun i:Fin 0 => Fin.elim0 i)
    (fun i:Fin 0 => Fin.elim0 i) hc (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)]
  exact isUnit_of_res_ne _ (hB0_auto D hN c _ _ hc
    (fun i:Fin 0 => Fin.elim0 i) (fun i:Fin 0 => Fin.elim0 i) t ht)

/-- Opposite balanced parity is the transpose of the same actual fibre. -/
theorem mixedLift_transpose (c : ι → ℕ) (lo hi : ℕ) :
    (mixedLift (p:=p) (Fr:=Fr) c lo hi)ᵀ=mixedLift (p:=p) (Fr:=Fr) c hi lo := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [mixedLift,extendNodes,Matrix.one_apply,eq_comm,frame_Mn_symm]

/-- Swapping balanced parity exchanges the two actual loads and preserves
the mixed response, without assuming symmetry of the mixed matrix. -/
theorem mixedResponse_swap (c : ι → ℕ) (lo hi : ℕ) (d : GaussLoc p) :
    mixedResponse (p:=p) (Fr:=Fr) c hi lo d=mixedResponse (p:=p) (Fr:=Fr) c lo hi d := by
  have hh := WrapTransport.response_transpose
    ((mixedLift (p:=p) (Fr:=Fr) c lo hi).map (algebraMap _ (GaussLoc p)))
    (fun a => ellL p Fr (extendNodes c lo a)-d) (fun a => ellL p Fr (extendNodes c hi a)-d)
  rw [← Matrix.transpose_map,mixedLift_transpose] at hh
  exact hh.symm

end OneFibre

end CatalanCore.Uniform.Content.UFSimple.WrapBalanced

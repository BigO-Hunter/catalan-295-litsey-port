module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapActual
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapResponse
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapExpr
public import Submission.CatalanCore.Uniform.Content.UFSimple.Closed

@[expose] public section

/-! # Wrapped finite-window source and counting

The virtual starting node may be odd. All chain and window arguments
below are pointwise and use no alternating-geometry parity hypothesis.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.UFFamily3 CatalanCore.Uniform.Content.UFFamily.SevE

namespace CatalanCore.Uniform.Content.UFSimple.WrapCell

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {q o : ℕ}

/-- Chain translation on an actual finite common interval. -/
noncomputable def finChainShift (r t0 delta : ℕ)
    (hr : r≤t0) (htp : t0+delta<r+p) (hq : (t0+delta)/p=t0/p) :
    {a:Fin r // ((a:ℕ):ZMod p)=((t0+delta:ℕ):ZMod p)} ≃
      {a:Fin r // ((a:ℕ):ZMod p)=((t0:ℕ):ZMod p)} where
  toFun a :=
    have h := down_ok a.1.2 hr hq a.2
    ⟨⟨(a.1:ℕ)-delta,by have := a.1.2; omega⟩,h.2⟩
  invFun a :=
    have h := up_ok a.1.2 hr htp a.2
    ⟨⟨(a.1:ℕ)+delta,h.1⟩,h.2⟩
  left_inv a := by
    have h := down_ok a.1.2 hr hq a.2
    apply Subtype.ext
    apply Fin.ext
    change (a.1:ℕ)-delta+delta=(a.1:ℕ)
    omega
  right_inv a := by
    apply Subtype.ext
    apply Fin.ext
    change (a.1:ℕ)+delta-delta=(a.1:ℕ)
    omega

/-- Two-term regular windows supply the original chain transport at
any virtual starting node, including the odd wrapped starting node. -/
theorem fin_shiftData (T : TwoTermData Fr q o) (hN : N≤p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (r t0 delta : ℕ)
    (hr : r≤t0) (htp : t0+delta<r+p) (hq : (t0+delta)/p=t0/p)
    (hw : NoSingWin (twoTermPoleData T hN hsq hnorm hnorm0) t0 delta) :
    ShiftData (twoTermPoleData T hN hsq hnorm hnorm0) (fun a:Fin r => (a:ℕ)) t0 (t0+delta) := by
  refine ⟨delta,rfl,hw,finChainShift r t0 delta hr htp hq,fun i => rfl,fun i => ?_⟩
  exact window_periodic (x := (i.1:ℕ)) T hN hsq hnorm hnorm0 (by have := i.1.2; omega) i.2 hw

/-- Actual two-term window source on a finite common interval. This
is the existing regular-prefix identity and original-entry transport,
with no parity assumption on the virtual starting node. -/
theorem typeData_window (T : TwoTermData Fr q o) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r t0 delta : ℕ) (hc : ∀ a:Fin r, (a:ℕ)<N)
    (hr : r≤t0) (htp : t0+delta<r+p) (hq : (t0+delta)/p=t0/p)
    (htN : t0+delta<N)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 delta)
    (C0 : RatFunc (ZMod p)) :
    let cv := fun a:Fin r => (a:ℕ)
    let n := (rfH p (red p Fr.norm))⁻¹
    let K0 := -(rfH p (cauchyH (wT p q o) ((t0:ℕ):ZMod p)))*n
    let W := fun c' => rfH p (wT p q o c')*n-C0
    TypeData Fr cv (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv) t0 (loewRow p Fr cv t0)
      K0 W (t0+delta) (loewRow p Fr cv (t0+delta)) := by
  intro cv n K0 W
  let D := twoTermPoleData T hN.le hsq hnorm hnorm0
  rw [WrapBalanced.commonLift_eq_core D hN cv (fun i:Fin 0 => Fin.elim0 i)
    (fun i:Fin 0 => Fin.elim0 i) hc (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)]
  refine typeData_of_shift D hN cv (fun i:Fin 0 => Fin.elim0 i) (fun i:Fin 0 => Fin.elim0 i)
    hc (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (tt_regRed T hN.le hsq hnorm hnorm0) t0 delta
    (loewRow p Fr cv t0) (loewRow p Fr cv (t0+delta))
    (fun a => rfl) (fun a => rfl) (finChainShift r t0 delta hr htp hq) (fun i => rfl)
    (fun i => window_periodic (x := (i.1:ℕ)) T hN.le hsq hnorm hnorm0
      (by have := i.1.2; omega) i.2 hw) hw htN K0 W ?_
  rw [tt_hres T hN.le hsq hnorm hnorm0 hp2 ho hq0 t0 delta htN hw]
  congr 1
  exact (sum_mul_inv_sub_const (rfH p) hp2 _ C0 _).symm

/-- Actual surplus rows have odd virtual offsets. -/
def rows (a d t0 tv : ℕ) : Finset (Fin d) :=
  univ.filter (fun i => t0≤a+2*(i:ℕ)+1 ∧ a+2*(i:ℕ)+1≤tv)

/-- Actual surplus columns have even virtual offsets. -/
def cols (a d t0 tv : ℕ) : Finset (Fin d) :=
  univ.filter (fun i => t0≤a+2*(i:ℕ) ∧ a+2*(i:ℕ)≤tv)

/-- The supported dimension count is the existing interval length,
with the two parity classes exchanged. -/
theorem rows_add_cols (a d t0 tv : ℕ) (ht0 : a≤t0) :
    (rows a d t0 tv).card+(cols a d t0 tv).card=min (tv+1) (a+2*d)-t0 := by
  unfold rows cols
  rw [card_fin_filter d (fun i => t0≤a+2*i+1 ∧ a+2*i+1≤tv),
    card_fin_filter d (fun i => t0≤a+2*i ∧ a+2*i≤tv),Nat.add_comm]
  exact card_win_sum a d t0 tv ht0


/-- The residue-union count needs no evenness assumption on its start. -/
theorem residue_union_count (a d w0 tv : ℕ) (hw : tv<w0+p) (hd : 2*d≤p)
    (hR : a+2*d≤w0+2*p) (hW : tv<a+2*p) :
    (tv+1-w0)+(2*d-beta3 d a p w0 tv) ≤
      ((Icc w0 tv).image (fun t:ℕ => ((t:ℕ):ZMod p)) ∪
        (outNodes p a d w0 tv).image (fun t:ℕ => ((t:ℕ):ZMod p))).card :=
  card_union_window (Fact.out : p.Prime).pos hw hd hR hW

/-- Original finite-window source supplies the actual row-axis
transport data of the reordered mixed core. -/
theorem actual_typeData_row (T : TwoTermData Fr q o) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l), WrapActual.ys r i<N)
    (t0 delta : ℕ) (ht0 : r+2*l-1≤t0)
    (htp : t0+delta<r+p) (hq : (t0+delta)/p=t0/p) (htN : t0+delta<N)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 delta)
    (C0 : RatFunc (ZMod p)) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let cv := fun a:Fin r => (a:ℕ)
    let cr := fun a => WrapActual.rowCoords cv r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords cv r s l hl hls (Sum.inl a)
    let Q := (WrapActual.reordered cv r s l hl hls (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    let n := (rfH p (red p Fr.norm))⁻¹
    let K0 := -(rfH p (cauchyH (wT p q o) ((t0:ℕ):ZMod p)))*n
    let W := fun c' => rfH p (wT p q o c')*n-C0
    TypeData Fr cr Q t0 (loewRow p Fr cc t0)
      K0 W (t0+delta) (loewRow p Fr cc (t0+delta)) := by
  intro D cv cr cc Q n K0 W
  apply WrapActual.typeData_transfer cv r s l t0 (t0+delta) hl hls hp ht0 (by omega)
    (by omega) htp (hint_of_poleData D hN hc hx hy)
  have hh := typeData_window T hN hsq hnorm hnorm0 hp2 ho hq0 r t0 delta hc
    (by omega) htp hq htN hw C0
  dsimp only at hh
  rw [WrapBalanced.commonLift_eq_core D hN cv (WrapActual.xs r) (WrapActual.ys r) hc hx hy] at hh
  exact hh

/-- Original finite-window source supplies the actual col-axis
transport data of the reordered mixed core. -/
theorem actual_typeData_col (T : TwoTermData Fr q o) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l), WrapActual.ys r i<N)
    (t0 delta : ℕ) (ht0 : r+2*l-1≤t0)
    (htp : t0+delta<r+p) (hq : (t0+delta)/p=t0/p) (htN : t0+delta<N)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 delta)
    (C0 : RatFunc (ZMod p)) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let cv := fun a:Fin r => (a:ℕ)
    let cr := fun a => WrapActual.rowCoords cv r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords cv r s l hl hls (Sum.inl a)
    let Q := (WrapActual.reordered cv r s l hl hls (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    let n := (rfH p (red p Fr.norm))⁻¹
    let K0 := -(rfH p (cauchyH (wT p q o) ((t0:ℕ):ZMod p)))*n
    let W := fun c' => rfH p (wT p q o c')*n-C0
    TypeData Fr cc Qᵀ t0 (loewRow p Fr cr t0)
      K0 W (t0+delta) (loewRow p Fr cr (t0+delta)) := by
  intro D cv cr cc Q n K0 W
  apply WrapActual.typeData_transfer_col cv r s l t0 (t0+delta) hl hls hp ht0 (by omega)
    (by omega) htp (hint_of_poleData D hN hc hx hy)
  have hh := typeData_window T hN hsq hnorm hnorm0 hp2 ho hq0 r t0 delta hc
    (by omega) htp hq htN hw C0
  dsimp only at hh
  rw [WrapBalanced.commonLift_eq_core D hN cv (WrapActual.xs r) (WrapActual.ys r) hc hx hy] at hh
  exact hh

/-- The actual row-axis representative has the original common
own direction and a nonzero direction denominator. -/
theorem representative_row_direction (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l), WrapActual.ys r i<N)
    (t0 : ℕ) (ht0 : r+2*l-1≤t0) (htp : t0<r+p) (htN : t0<N) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let cv := fun a:Fin r => (a:ℕ)
    let cr := fun a => WrapActual.rowCoords cv r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords cv r s l hl hls (Sum.inl a)
    let A := WrapActual.reordered cv r s l hl hls (hint_of_poleData D hN hc hx hy)
    let Q := A.toBlocks₁₁
    let Qorig := (sLift cv (WrapActual.xs r) (WrapActual.ys r) (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    let d := dirOf Fr cv Qorig t0 (loewRow p Fr cv t0)
    ((ellL p Fr t0-d)-(sOwn cr t0 (loewRow p Fr cc t0) ᵥ* (Dmat cr Q)⁻¹) ⬝ᵥ
      (fun a => ellL p Fr (cr a)-d)=0) ∧
      res p (1-∑ j, (sOwn cr t0 (loewRow p Fr cc t0) ᵥ* (Dmat cr Q)⁻¹) j)≠0 := by
  intro D cv cr cc A Q Qorig d
  have hDorig : IsUnit (Dmat cv Qorig).det :=
    isUnit_Dmat_det D cv hc Qorig (sLift_core_rel D hN cv (WrapActual.xs r) (WrapActual.ys r) hc hx hy)
      (sLift_core_det cv _ _ _)
  have hDa : IsUnit (Dmat cr Q).det :=
    WrapActual.actual_Dmat_unit T hqp hN hsq hnorm hnorm0 cv r s l hl hls hp hsize hc hx hy
  have hBorig : IsUnit (1-∑ j, (sOwn cv t0 (loewRow p Fr cv t0) ᵥ* (Dmat cv Qorig)⁻¹) j) :=
    isUnit_of_res_ne _ (hB0_auto D hN cv (WrapActual.xs r) (WrapActual.ys r) hc hx hy t0 htN)
  have hzorig := own_dir_zero Fr cv Qorig t0 (loewRow p Fr cv t0) hBorig
  have hresp := WrapActual.surplus_own_response cv r s l t0 hl hls hp ht0 htp
    (hint_of_poleData D hN hc hx hy) (loewRow p Fr cc t0)
    (fun a => ellL p Fr (cr a)-d) hDa hDorig
  have hresp1 := WrapActual.surplus_own_response cv r s l t0 hl hls hp ht0 htp
    (hint_of_poleData D hN hc hx hy) (loewRow p Fr cc t0) (fun _ => 1) hDa hDorig
  refine ⟨?_,?_⟩
  · rw [hresp]
    exact hzorig
  · simp only [dotProduct, mul_one] at hresp1
    rw [hresp1]
    exact (hBorig.map (res p)).ne_zero

/-- The actual col-axis representative has the original common
own direction and a nonzero direction denominator. -/
theorem representative_col_direction (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l), WrapActual.ys r i<N)
    (t0 : ℕ) (ht0 : r+2*l-1≤t0) (htp : t0<r+p) (htN : t0<N) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let cv := fun a:Fin r => (a:ℕ)
    let cr := fun a => WrapActual.rowCoords cv r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords cv r s l hl hls (Sum.inl a)
    let A := WrapActual.reordered cv r s l hl hls (hint_of_poleData D hN hc hx hy)
    let Q := A.toBlocks₁₁
    let Qorig := (sLift cv (WrapActual.xs r) (WrapActual.ys r) (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    let d := dirOf Fr cv Qorig t0 (loewRow p Fr cv t0)
    ((ellL p Fr t0-d)-(sOwn cc t0 (loewRow p Fr cr t0) ᵥ* (Dmat cc Qᵀ)⁻¹) ⬝ᵥ
      (fun a => ellL p Fr (cc a)-d)=0) ∧
      res p (1-∑ j, (sOwn cc t0 (loewRow p Fr cr t0) ᵥ* (Dmat cc Qᵀ)⁻¹) j)≠0 := by
  intro D cv cr cc A Q Qorig d
  have hDorig : IsUnit (Dmat cv Qorig).det :=
    isUnit_Dmat_det D cv hc Qorig (sLift_core_rel D hN cv (WrapActual.xs r) (WrapActual.ys r) hc hx hy)
      (sLift_core_det cv _ _ _)
  have hDa : IsUnit (Dmat cr Q).det :=
    WrapActual.actual_Dmat_unit T hqp hN hsq hnorm hnorm0 cv r s l hl hls hp hsize hc hx hy
  have hBorig : IsUnit (1-∑ j, (sOwn cv t0 (loewRow p Fr cv t0) ᵥ* (Dmat cv Qorig)⁻¹) j) :=
    isUnit_of_res_ne _ (hB0_auto D hN cv (WrapActual.xs r) (WrapActual.ys r) hc hx hy t0 htN)
  have hzorig := own_dir_zero Fr cv Qorig t0 (loewRow p Fr cv t0) hBorig
  have hDac : IsUnit (Dmat cc Qᵀ).det :=
    WrapActual.Dmat_transpose_unit cr cc (WrapActual.core_colours cv r s l hl hls hp) Q hDa
  have hDoc : IsUnit (Dmat cv Qorigᵀ).det :=
    WrapActual.Dmat_transpose_unit cv cv (fun _ => rfl) Qorig hDorig
  have hsym : Qorigᵀ=Qorig := sLift_core_symm D hN cv (WrapActual.xs r) (WrapActual.ys r) hc hx hy
  have hresp := WrapActual.surplus_col_own_response cv r s l t0 hl hls hp ht0 htp
    (hint_of_poleData D hN hc hx hy) (loewRow p Fr cr t0)
    (fun a => ellL p Fr (cc a)-d) hDac hDoc
  have hresp1 := WrapActual.surplus_col_own_response cv r s l t0 hl hls hp ht0 htp
    (hint_of_poleData D hN hc hx hy) (loewRow p Fr cr t0) (fun _ => 1) hDac hDoc
  rw [hsym] at hresp hresp1
  refine ⟨?_,?_⟩
  · rw [hresp]
    exact hzorig
  · simp only [dotProduct, mul_one] at hresp1
    rw [hresp1]
    exact (hBorig.map (res p)).ne_zero

/-- Every reordered row coordinate is an original bounded node. -/
theorem rowCoords_lt (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l), WrapActual.ys r i<N)
    (i : (Fin r ⊕ Fin (2*l-1)) ⊕ Fin (s+1-l)) :
    WrapActual.rowCoords (fun a:Fin r => (a:ℕ)) r s l hl hls i<N := by
  change rowNode _ _ (WrapGeometry.rowFullEquiv (Fin r) s l hl hls i)<N
  rcases WrapGeometry.rowFullEquiv (Fin r) s l hl hls i with a|j
  · exact hc a
  · exact hx j

/-- Every reordered col coordinate is an original bounded node. -/
theorem colCoords_lt (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l), WrapActual.ys r i<N)
    (i : (Fin r ⊕ Fin (2*l-1)) ⊕ Fin (s+1-l)) :
    WrapActual.colCoords (fun a:Fin r => (a:ℕ)) r s l hl hls i<N := by
  change colNode _ _ (WrapGeometry.colFullEquiv (Fin r) s l hl hls i)<N
  rcases WrapGeometry.colFullEquiv (Fin r) s l hl hls i with a|j
  · exact hc a
  · exact hy j

/-- The actual row-axis window has its polynomial second-order source. -/
theorem actual_row_source (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l), WrapActual.ys r i<N)
    (t0 delta : ℕ) (ht0 : r+2*l-1≤t0)
    (htp : t0+delta<r+p) (hq : (t0+delta)/p=t0/p) (htN : t0+delta<N)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 delta)
    (C0 : RatFunc (ZMod p)) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let cv := fun a:Fin r => (a:ℕ)
    let cr := fun a => WrapActual.rowCoords cv r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords cv r s l hl hls (Sum.inl a)
    let A := WrapActual.reordered cv r s l hl hls (hint_of_poleData D hN hc hx hy)
    let Q := A.toBlocks₁₁
    let Qorig := (sLift cv (WrapActual.xs r) (WrapActual.ys r) (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    let d := dirOf Fr cv Qorig t0 (loewRow p Fr cv t0)
    let n := (rfH p (red p Fr.norm))⁻¹
    let K0 := -(rfH p (cauchyH (wT p q o) ((t0:ℕ):ZMod p)))*n
    let W := fun c' => rfH p (wT p q o c')*n-C0
    let σ := loewRow p Fr cc (t0+delta)
    ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) (WrapResponse.prefixMomB (Fr:=Fr) Q cr (t0+delta) σ)=
        algebraMap _ (GaussLoc p) (WrapResponse.prefixMomA Q σ)*
          (CatalanCore.Uniform.Content.UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*d)+
            CatalanCore.Uniform.Content.UFMoments.piL p^2*Φ) ∧
      res p Φ=res p (algebraMap _ (GaussLoc p) (nL p Fr))*K0+
        hDer univ (WrapResponse.mixedV Fr cr cc Q d W) ((t0+delta:ℕ):ZMod p) := by
  intro D cv cr cc A Q Qorig d n K0 W σ
  have hcr : ∀ a, cr a<N := fun a => rowCoords_lt r s l hl hls hc hx hy (Sum.inl a)
  have hcc : ∀ a, cc a<N := fun a => colCoords_lt r s l hl hls hc hx hy (Sum.inl a)
  have hcq := WrapActual.core_colours cv r s l hl hls hp
  have hcomm := WrapActual.reordered_commutator D hN cv r s l hl hls hc hx hy
  have hdet : phiP p Q.det≠0 :=
    WrapActual.core_primitive T hqp hN hsq hnorm hnorm0 cv r s l hl hls hp hsize _
  have hd := representative_row_direction T hqp hN hsq hnorm hnorm0 r s l hl hls hp
    hsize hc hx hy t0 ht0 (by omega) (by omega)
  have hT := actual_typeData_row T hN hsq hnorm hnorm0 hp2 ho hq0 r s l hl hls hp
    hc hx hy t0 delta ht0 htp hq htN hw C0
  dsimp only at hd hT
  apply WrapResponse.prefix_source D cr cc hcr hcc
    (fun a => hcq a) Q ?_ ?_ t0 (loewRow p Fr cc t0) d hd.1 hd.2
    K0 W (t0+delta) htN σ (loewRow_rel D hN cc hcc (t0+delta) htN) hT
  · intro a b; exact hcomm (Sum.inl a) (Sum.inl b)
  · exact hdet

/-- The actual col-axis window has its polynomial second-order source. -/
theorem actual_col_source (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l), WrapActual.ys r i<N)
    (t0 delta : ℕ) (ht0 : r+2*l-1≤t0)
    (htp : t0+delta<r+p) (hq : (t0+delta)/p=t0/p) (htN : t0+delta<N)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 delta)
    (C0 : RatFunc (ZMod p)) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let cv := fun a:Fin r => (a:ℕ)
    let cr := fun a => WrapActual.rowCoords cv r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords cv r s l hl hls (Sum.inl a)
    let A := WrapActual.reordered cv r s l hl hls (hint_of_poleData D hN hc hx hy)
    let Q := A.toBlocks₁₁
    let Qorig := (sLift cv (WrapActual.xs r) (WrapActual.ys r) (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    let d := dirOf Fr cv Qorig t0 (loewRow p Fr cv t0)
    let n := (rfH p (red p Fr.norm))⁻¹
    let K0 := -(rfH p (cauchyH (wT p q o) ((t0:ℕ):ZMod p)))*n
    let W := fun c' => rfH p (wT p q o c')*n-C0
    let σ := loewRow p Fr cr (t0+delta)
    ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) (WrapResponse.prefixMomB (Fr:=Fr) Qᵀ cc (t0+delta) σ)=
        algebraMap _ (GaussLoc p) (WrapResponse.prefixMomA Qᵀ σ)*
          (CatalanCore.Uniform.Content.UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*d)+
            CatalanCore.Uniform.Content.UFMoments.piL p^2*Φ) ∧
      res p Φ=res p (algebraMap _ (GaussLoc p) (nL p Fr))*K0+
        hDer univ (WrapResponse.mixedV Fr cc cr Qᵀ d W) ((t0+delta:ℕ):ZMod p) := by
  intro D cv cr cc A Q Qorig d n K0 W σ
  have hcr : ∀ a, cr a<N := fun a => rowCoords_lt r s l hl hls hc hx hy (Sum.inl a)
  have hcc : ∀ a, cc a<N := fun a => colCoords_lt r s l hl hls hc hx hy (Sum.inl a)
  have hcq := WrapActual.core_colours cv r s l hl hls hp
  have hcomm := WrapActual.reordered_commutator D hN cv r s l hl hls hc hx hy
  have hdet : phiP p Q.det≠0 :=
    WrapActual.core_primitive T hqp hN hsq hnorm hnorm0 cv r s l hl hls hp hsize _
  have hd := representative_col_direction T hqp hN hsq hnorm hnorm0 r s l hl hls hp
    hsize hc hx hy t0 ht0 (by omega) (by omega)
  have hT := actual_typeData_col T hN hsq hnorm hnorm0 hp2 ho hq0 r s l hl hls hp
    hc hx hy t0 delta ht0 htp hq htN hw C0
  dsimp only at hd hT
  apply WrapResponse.prefix_source D cc cr hcc hcr
    (fun a => (hcq a).symm) Qᵀ ?_ ?_ t0 (loewRow p Fr cr t0) d hd.1 hd.2
    K0 W (t0+delta) htN σ (loewRow_rel D hN cr hcr (t0+delta) htN) hT
  · intro a b; exact WrapResponse.commutator_transpose A _ _ hcomm (Sum.inl a) (Sum.inl b)
  · simpa only [Matrix.det_transpose] using hdet

/-- Original polynomial row moments inherit the actual window source. -/
theorem actual_row_moment_source (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l), WrapActual.ys r i<N)
    (t0 delta : ℕ) (ht0 : r+2*l-1≤t0)
    (htp : t0+delta<r+p) (hq : (t0+delta)/p=t0/p) (htN : t0+delta<N)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 delta)
    (C0 : RatFunc (ZMod p)) (z : Fin (s+1-l))
    (heq : t0+delta=WrapActual.rowCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inr z)) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let cv := fun a:Fin r => (a:ℕ)
    let cr := fun a => WrapActual.rowCoords cv r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords cv r s l hl hls (Sum.inl a)
    let A := WrapActual.reordered cv r s l hl hls (hint_of_poleData D hN hc hx hy)
    let Q := A.toBlocks₁₁
    let Qorig := (sLift cv (WrapActual.xs r) (WrapActual.ys r) (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    let d := dirOf Fr cv Qorig t0 (loewRow p Fr cv t0)
    let n := (rfH p (red p Fr.norm))⁻¹
    let K0 := -(rfH p (cauchyH (wT p q o) ((t0:ℕ):ZMod p)))*n
    let W := fun c' => rfH p (wT p q o c')*n-C0
    let xx := fun z => WrapActual.rowCoords cv r s l hl hls (Sum.inr z)
    let σ := loewRow p Fr cc (t0+delta)
    ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) (rowMomB A Fr cr xx z)=
        algebraMap _ (GaussLoc p) (rowMomA A z)*
          (CatalanCore.Uniform.Content.UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*d)+
            CatalanCore.Uniform.Content.UFMoments.piL p^2*Φ) ∧
      res p Φ=res p (algebraMap _ (GaussLoc p) (nL p Fr))*K0+
        hDer univ (WrapResponse.mixedV Fr cr cc Q d W) ((t0+delta:ℕ):ZMod p) := by
  intro D cv cr cc A Q Qorig d n K0 W xx σ
  have hh := actual_row_source T hqp hN hsq hnorm hnorm0 hp2 ho hq0 r s l hl hls hp
    hsize hc hx hy t0 delta ht0 htp hq htN hw C0
  dsimp only at hh
  have hload := WrapActual.surplus_row_load D hN cv r s l hl hls hc hx hy z
  have hσ : σ=A.toBlocks₂₁ z := by
    dsimp only [σ]
    rw [heq]
    exact hload.symm
  have hc' : ∀ a,cr a<N := fun a => rowCoords_lt r s l hl hls hc hx hy (Sum.inl a)
  have hx' : ∀ i,xx i<N := fun i => rowCoords_lt r s l hl hls hc hx hy (Sum.inr i)
  have hA : WrapResponse.prefixMomA Q σ=rowMomA A z := by
    rw [hσ]
    rfl
  have hB : WrapResponse.prefixMomB (Fr:=Fr) Q cr (t0+delta) σ=rowMomB A Fr cr xx z := by
    rw [rowMomB_eq D A cr xx hc' hx' z]
    unfold WrapResponse.prefixMomB
    rw [heq,hσ]
  rw [hA,hB] at hh
  exact hh

/-- Original polynomial col moments inherit the actual window source. -/
theorem actual_col_moment_source (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l), WrapActual.ys r i<N)
    (t0 delta : ℕ) (ht0 : r+2*l-1≤t0)
    (htp : t0+delta<r+p) (hq : (t0+delta)/p=t0/p) (htN : t0+delta<N)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 delta)
    (C0 : RatFunc (ZMod p)) (z : Fin (s+1-l))
    (heq : t0+delta=WrapActual.colCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inr z)) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let cv := fun a:Fin r => (a:ℕ)
    let cr := fun a => WrapActual.rowCoords cv r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords cv r s l hl hls (Sum.inl a)
    let A := WrapActual.reordered cv r s l hl hls (hint_of_poleData D hN hc hx hy)
    let Q := A.toBlocks₁₁
    let Qorig := (sLift cv (WrapActual.xs r) (WrapActual.ys r) (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    let d := dirOf Fr cv Qorig t0 (loewRow p Fr cv t0)
    let n := (rfH p (red p Fr.norm))⁻¹
    let K0 := -(rfH p (cauchyH (wT p q o) ((t0:ℕ):ZMod p)))*n
    let W := fun c' => rfH p (wT p q o c')*n-C0
    let xx := fun z => WrapActual.colCoords cv r s l hl hls (Sum.inr z)
    let σ := loewRow p Fr cr (t0+delta)
    ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) (colMomB A Fr cc xx z)=
        algebraMap _ (GaussLoc p) (colMomA A z)*
          (CatalanCore.Uniform.Content.UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*d)+
            CatalanCore.Uniform.Content.UFMoments.piL p^2*Φ) ∧
      res p Φ=res p (algebraMap _ (GaussLoc p) (nL p Fr))*K0+
        hDer univ (WrapResponse.mixedV Fr cr cc Q d W) ((t0+delta:ℕ):ZMod p) := by
  intro D cv cr cc A Q Qorig d n K0 W xx σ
  have hh := actual_col_source T hqp hN hsq hnorm hnorm0 hp2 ho hq0 r s l hl hls hp
    hsize hc hx hy t0 delta ht0 htp hq htN hw C0
  dsimp only at hh
  have hload := WrapActual.surplus_col_load D hN cv r s l hl hls hc hx hy z
  have hσ : σ=Aᵀ.toBlocks₂₁ z := by
    dsimp only [σ]
    rw [heq]
    exact hload.symm
  have hc' : ∀ a,cc a<N := fun a => colCoords_lt r s l hl hls hc hx hy (Sum.inl a)
  have hx' : ∀ i,xx i<N := fun i => colCoords_lt r s l hl hls hc hx hy (Sum.inr i)
  have hA : WrapResponse.prefixMomA Qᵀ σ=rowMomA Aᵀ z := by
    rw [hσ]
    rfl
  have hB : WrapResponse.prefixMomB (Fr:=Fr) Qᵀ cc (t0+delta) σ=rowMomB Aᵀ Fr cc xx z := by
    rw [rowMomB_eq D Aᵀ cc xx hc' hx' z]
    unfold WrapResponse.prefixMomB
    rw [heq,hσ]
    rfl
  rw [hA,hB] at hh
  rw [WrapResponse.rowMomA_transpose,WrapResponse.rowMomB_transpose] at hh
  have hDa := WrapActual.actual_Dmat_unit T hqp hN hsq hnorm hnorm0 cv r s l hl hls hp hsize hc hx hy
  rw [WrapResponse.mixedV_transpose cr cc (WrapActual.core_colours cv r s l hl hls hp) Q hDa] at hh
  exact hh

end CatalanCore.Uniform.Content.UFSimple.WrapCell

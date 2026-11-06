module
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericB
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.MaximaAssembly
public import CatalanMeasure.GenD.Cert.WLogSpec
public import CatalanMeasure.CellCert.CellW
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: generic column terminal assembly (Y analogue of XGenericD.row_cap_terminal); no data
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.ColGenericD
noncomputable section
open Set CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr
  CatalanMeasure.GenD.Signed.RouteI.Maxima.HornerSign CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericB CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD
  CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCover CatalanMeasure.GenD.Signed.RouteI.Maxima.PartitionCover
  CatalanMeasure.CellCert CatalanMeasure.Cert

/-! ### column pole leaves and tree -/

def colLeavesOf (C : ColumnWeights) (V : List TailQ) : List Leaf :=
  (colPolesP C V false false).map leafOfPole

def colTreeOf (C : ColumnWeights) (V : List TailQ) : PoleTree :=
  buildPT 8 ((colLeavesOf C V).map PoleTree.leaf)

/-! ### column polynomial part and derivative form -/

theorem colZ_abs_le (Vc : List Int) (y : Real) (hy : |y|≤1) :
    |ptZ (colZ Vc) 0 y|≤((2*uBnd Vc : Rat) : Real) := by
  rw [← colZ_spec]
  push_cast
  rw [abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_left (finUR_abs_le Vc y hy) (by norm_num)

theorem col_deriv_form (C : ColumnWeights) {Vc : List Int} {V : List TailQ}
    (hV : tailsInDisk V=true) (hVz : ∀ t∈V,t.zr≠0 ∨ t.zi≠0)
    (t : PoleTree) (hpoles : colPolesP C V false false=t.leaves.map Leaf.pole)
    (hflags : ∀ r∈t.leaves,0<r.D ∧ 0<r.E ∧ SafePole r)
    {x : Real} (hx : x∈Ioo (-1 : Real) 1) (h0 : x≠0) :
    HasDerivAt (colFieldSP C Vc V false false)
      (reval (fullNum (colZ Vc) t) x/reval (fullDen t) x) x ∧
    0<reval (fullDen t) x := by
  have hd := colFieldSP_hasDerivAt C hV hVz (colZ Vc) (colZ_spec Vc) false false hx
    (Or.inr h0)
  rw [hpoles] at hd
  have hl : ∀ r∈t.leaves,0<r.D ∧ 0<r.E ∧ 0<reval r.den x := by
    intro r hr
    obtain ⟨hD,hE,hs⟩ := hflags r hr
    exact ⟨hD,hE,leaf_den_pos r x hD hE (safe_pole_ne r x hD hs hx h0)⟩
  obtain ⟨hpos,he⟩ := full_source_identity (colZ Vc) t x hl
  refine ⟨?_,hpos⟩
  have : ftZ (colZ Vc) (t.leaves.map Leaf.pole) 0 x=
      reval (fullNum (colZ Vc) t) x/reval (fullDen t) x := by
    rw [he]
    field_simp
  rwa [this] at hd

/-! ### evaluator enclosure to a field bound -/

theorem evLe_capC (C : ColumnWeights) {Vc : List Int} {V : List TailQ}
    (hV : tailsInDisk V=true) (c U : Rat)
    (hc : |(c : Real)|≤1) (h : evLe (colSpecW C Vc V 0).ev c U=true) :
    colFieldSP C Vc V false false c≤(U : Real) := by
  have hev : (colSpecW C Vc V 0).ev c=colApproxW C Vc V false false c := by
    simp [colSpecW,flag0,flag1]
  unfold evLe at h
  rw [hev] at h
  cases hh : colApproxW C Vc V false false c with
  | none => rw [hh] at h; simp at h
  | some ve =>
    rw [hh] at h
    simp only [decide_eq_true_eq] at h
    have h1 := colApproxW_le C hV false false hh hc
    have h2 : ((ve.1+ve.2 : Rat) : Real)≤(U : Real) := by exact_mod_cast h
    push_cast at h2
    linarith

/-! ### terminal theorem (column, open interval `(0,1)`, no boundary value) -/

theorem col_cap_terminal (C : ColumnWeights) (Vc : List Int) (V : List TailQ) (MY : Rat)
    (hV : tailsInDisk V=true) (hVz : ∀ t∈V,t.zr≠0 ∨ t.zi≠0)
    (hb : 0<C.b) (hq : 0<C.q)
    (cs : List Int) (scale : Int) (fs : List (Int × Int))
    (cells : List Cell) (vs : List Nat) (Ls keepLs : List Int)
    (hcs : cs≠[]) (hcsl : cs.length≤512) (hc0 : cs.getD 0 0≠0)
    (hscale : 0<scale) (hfs : ∀ f∈fs,SafeFactor f)
    (leavesX : List Leaf) (Zx : List Int)
    (hleq : colLeavesOf C V=leavesX) (hZeq : colZ Vc=Zx)
    (hlv : 0<(colLeavesOf C V).length) (hlvl : (colLeavesOf C V).length≤256)
    (hleaves : ∀ r∈colLeavesOf C V,0<r.D ∧ 0<r.E ∧ SafePole r)
    (hpack : PackOK Zx (buildPT 8 (leavesX.map PoleTree.leaf)) cs scale fs)
    (hcells : ∀ i : Fin cells.length,cellCheck cs (cells.get i) (vs.getD i 0)=true)
    (hvl : vs.length=cells.length)
    (hchain : chainOK 0 1 (cells.map ratCell)=true)
    (hsum : vs.sum=Ls.length)
    (hbr : ∀ l∈Ls,CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC.bracketOK cs l=true)
    (hord : adj Ls=true)
    (hpos : ∀ l∈Ls,dI≤l)
    (hkeep : ∀ l∈Ls,keepB cs fs l=true → l∈keepLs)
    (hvals : ∀ l∈keepLs,evLe (colSpecW C Vc V 0).ev (midQ l) (MY-1/2^28)=true)
    (hok : ∀ q∈colPolesP C V false false,PoleOK q)
    (hL : 2*uBnd Vc+(poleBoundC (1/2^50) (colPolesP C V false false) : Rat)≤2^50) :
    ∀ x∈Ioo (0 : Real) 1,colFieldS C Vc V x≤(MY : Real) := by
  classical
  subst hleq
  subst hZeq
  -- tree and derivative data
  have ht : (colTreeOf C V).leaves=colLeavesOf C V :=
    buildPT_leaves_map 8 _ (List.ne_nil_of_length_pos hlv) (by simpa using hlvl)
  have hpoles : colPolesP C V false false=(colTreeOf C V).leaves.map Leaf.pole := by
    rw [ht]; unfold colLeavesOf; rw [List.map_map]
    conv_lhs => rw [← List.map_id (colPolesP C V false false)]
    exact List.map_congr_left (fun q _ => (leafOfPole_pole q).symm)
  have hflags : ∀ r∈(colTreeOf C V).leaves,0<r.D ∧ 0<r.E ∧ SafePole r := by
    rw [ht]; exact hleaves
  have hid : fullNum (colZ Vc) (colTreeOf C V)=
      Polynomial.C scale*(listPoly cs*cancelPoly fs) := pack_sound _ _ cs hcs hcsl scale fs hpack
  -- polynomial setup
  have hPne : listPoly cs≠0 := by
    intro h
    apply hc0
    have := listPoly_coeff cs 0
    rw [h] at this
    simpa using this.symm
  have hp := map_ne_zero (listPoly cs) hPne
  have hq0 : (0 : Real)<(qB : Real) := by exact_mod_cast qB_pos
  have hsc : (scale : Real)≠0 := by exact_mod_cast hscale.ne'
  have hrng := coeffRange_listPoly cs
  have hn : (listPoly cs).natDegree<cs.length := listPoly_natDegree_lt cs hcs
  have hsmem : ∀ x∈Ioo (0 : Real) 1,x∈Ioo (-1 : Real) 1 ∧ x≠0 := by
    intro x hx
    exact ⟨⟨by linarith [hx.1],hx.2⟩,hx.1.ne'⟩
  have hdI : (0 : Int)<dI := by unfold dI; norm_num
  -- the counts
  have hcertAll : ∀ i : Fin cells.length,
      0<cellK cs (cells.get i) ∧
      CellCert (cellK cs (cells.get i)) (listPoly cs) (cells.get i) (buildTree 9 cs) cs.length
        (vs.getD i 0) ∧ ((cells.get i).b=(cells.get i).d ∨
          hornerF (cells.get i).d (cells.get i).b cs≠0) :=
    fun i => cellCheck_sound cs hcs hcsl _ _ (hcells i)
  have hchainR : Chain (0 : Real) 1 (cells.map cellReal) := by
    have h := chainOK_sound 0 1 (cells.map ratCell) hchain
    have e : (cells.map ratCell).map castCell=cells.map cellReal := by
      rw [List.map_map]
      exact List.map_congr_left (fun c _ => (cellReal_eq c).symm)
    rw [e] at h
    simpa using h
  have hcuts : ∀ c∈cells,(c.b : Real)/c.d≠1 →
      ((listPoly cs).map (Int.castRingHom Real)).eval ((c.b : Real)/c.d)≠0 := by
    intro c hc hne
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hc
    obtain ⟨_,hcert,hcut⟩ := hcertAll i
    have hd : 0<(cells.get i).d := hcert.1
    rcases hcut with h | h
    · exfalso; apply hne; rw [h]; exact div_self (by exact_mod_cast hd.ne')
    · have := cut_nonroot_sound (cells.get i).d (cells.get i).b hd (listPoly cs) cs.length hn
        (by rw [hrng, ← hornerF_eq]; exact h)
      exact this
  have hgd : ∀ i : Fin cells.length,cells.getD i ⟨0,1,1⟩=cells.get i :=
    fun i => List.getD_eq_getElem _ _ i.2
  have hcount := cover_count (fun j => cellK cs (cells.getD j ⟨0,1,1⟩)) (fun j => by
      by_cases hj : j<cells.length
      · have h := (hcertAll ⟨j,hj⟩).1
        have e := hgd ⟨j,hj⟩
        simp only at e
        rw [e]; exact h
      · rw [List.getD_eq_default _ _ (by omega : cells.length≤j)]
        unfold cellK; positivity)
    (listPoly cs) hPne 0 1 cells (fun _ => buildTree 9 cs) (fun _ => cs.length)
    (fun i => vs.getD i 0) hchainR hcuts
    (fun i => by
      have h := (hcertAll i).2.1
      have e := hgd i
      show CellCert (cellK cs (cells.getD i ⟨0,1,1⟩)) (listPoly cs) (cells.get i) _ _ _
      rw [e]; exact h)
  rw [fin_sum_getD vs cells.length hvl,hsum] at hcount
  -- brackets
  let Lf : Fin Ls.length → Int := fun i => Ls.get i
  have hbrF : ∀ i,CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC.bracketOK cs (Lf i)=true := fun i => hbr _ (List.get_mem _ _)
  have hboxF := fun i => boxOK_sound (Lf i) (by
    have := hbrF i; unfold CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC.bracketOK at this
    simp only [Bool.and_eq_true] at this; exact this.2)
  have hsignF : ∀ i,hornerQ qB (Lf i) (coeffRange (listPoly cs) cs.length)*
      hornerQ qB (Lf i+1) (coeffRange (listPoly cs) cs.length)<0 := by
    intro i
    have := hbrF i; unfold CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC.bracketOK at this
    simp only [Bool.and_eq_true,decide_eq_true_eq] at this
    rw [hrng,← hornerF_eq,← hornerF_eq]; exact this.1
  have hordF : ∀ i j : Fin Ls.length,i<j → Lf i+1<Lf j := by
    intro i j hij
    exact List.pairwise_iff_getElem.mp (adj_pairwise Ls hord) i j i.2 j.2 hij
  have hposR : ∀ i,(0 : Real)<(Lf i : Real)/qB := by
    intro i
    have h1 : (dI : Real)≤(Lf i : Real) := by exact_mod_cast hpos _ (List.get_mem _ _)
    have h2 : (0 : Real)<(dI : Real) := by exact_mod_cast hdI
    exact div_pos (by linarith) hq0
  -- the maxima theorem
  set F := colFieldSP C Vc V false false with hFdef
  set s : Set Real := Ioo (0 : Real) 1 with hs
  have hderivAll : ∀ x∈s,HasDerivAt F (reval (fullNum (colZ Vc) (colTreeOf C V)) x/
      reval (fullDen (colTreeOf C V)) x) x ∧ 0<reval (fullDen (colTreeOf C V)) x := by
    intro x hx
    obtain ⟨h1,h2⟩ := hsmem x hx
    exact col_deriv_form C hV hVz (colTreeOf C V) hpoles hflags h1 h2
  have hroots : ∀ x∈s,reval (fullNum (colZ Vc) (colTreeOf C V)) x=0 ↔
      ((listPoly cs).map (Int.castRingHom Real)).IsRoot x := by
    intro x hx
    obtain ⟨h1,h2⟩ := hsmem x hx
    rw [hid]
    simp only [reval_mul,reval_C]
    have hcn := cancelPoly_ne fs hfs h1 h2
    rw [Polynomial.IsRoot.def,← reval_eq_map_eval]
    constructor
    · intro h
      have := (mul_eq_zero.mp h).resolve_left hsc
      exact (mul_eq_zero.mp this).resolve_right hcn
    · intro h; rw [h]; simp
  have hmax := CatalanMeasure.GenD.Signed.RouteI.Maxima.MaximaAssembly.maxima_cap_of_root_brackets F
    (fun x => reval (fullNum (colZ Vc) (colTreeOf C V)) x)
    (fun x => reval (fullDen (colTreeOf C V)) x)
    ((listPoly cs).map (Int.castRingHom Real)) hp s Ls.length
    (fun i => (Lf i : Real)/qB) (fun i => ((Lf i+1 : Int) : Real)/qB)
    (fun i => keepB cs fs (Lf i)=true) (MY : Real)
    (fun i => by
      have : (Lf i : Real)<((Lf i+1 : Int) : Real) := by push_cast; linarith
      exact (div_lt_div_iff_of_pos_right hq0).mpr this)
    (fun i => bracket_sign_sound qB (Lf i) (Lf i+1) qB_pos (listPoly cs) cs.length hn (hsignF i))
    (fun i y hy => by
      obtain ⟨_,⟨_,hz⟩,hbx⟩ := hboxF i
      obtain ⟨_,_,_,_,hm⟩ := hbx y hy.1 hy.2
      rcases hm with hm | hm
      · exact absurd hm.1 (not_lt.mpr (by linarith [hy.1, hposR i]))
      · exact ⟨hm.1,hm.2⟩)
    (brackets_disjoint qB qB_pos Ls.length Lf (fun i => Lf i+1) hordF)
    hcount
    (fun x hx => (hderivAll x hx).1.continuousAt.continuousWithinAt)
    (by
      have e : (fun x : Real => reval (fullNum (colZ Vc) (colTreeOf C V)) x)=
          fun x => ((fullNum (colZ Vc) (colTreeOf C V)).map (Int.castRingHom Real)).eval x :=
        funext (reval_eq_map_eval _)
      rw [e]
      exact (Polynomial.continuous _).continuousOn)
    (fun x hx => (hderivAll x hx).2)
    (fun x hx => (hderivAll x hx).1.deriv)
    hroots
    (fun i hi => by
      have hi' : hornerF qB (Lf i) cs*cancelProd qB (Lf i) fs<0 := by
        by_contra hcon
        exact hi (by unfold keepB; simp [hcon])
      have he := eval_sign_of_horner qB (Lf i) qB_pos (listPoly cs) cs.length hn
      rw [hrng] at he
      simp only [← hornerF_eq,← reval_eq_map_eval] at he
      have hcs' := cancel_sign qB (Lf i) qB_pos fs
      have hN : reval (fullNum (colZ Vc) (colTreeOf C V)) ((Lf i : Real)/qB)=
          (scale : Real)*(reval (listPoly cs) ((Lf i : Real)/qB)*
            reval (cancelPoly fs) ((Lf i : Real)/qB)) := by
        rw [hid]; simp only [reval_mul,reval_C]
      have hsp : (0 : Real)<scale := by exact_mod_cast hscale
      show reval (fullNum (colZ Vc) (colTreeOf C V)) ((Lf i : Real)/qB)<0
      rw [hN]
      rcases mul_neg_iff.mp hi' with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · have ha := he.1.mp h1
        have hb := (hcs'.1).mp h2
        exact mul_neg_of_pos_of_neg hsp (mul_neg_of_pos_of_neg ha hb)
      · have ha := he.2.1.mp h1
        have hb0 : reval (cancelPoly fs) ((Lf i : Real)/qB)≠0 := (hcs'.2).mp h2.ne'
        have hb : 0<reval (cancelPoly fs) ((Lf i : Real)/qB) := by
          rcases lt_trichotomy (reval (cancelPoly fs) ((Lf i : Real)/qB)) 0 with h | h | h
          · exact absurd ((hcs'.1).mpr h) (not_lt.mpr h2.le)
          · exact absurd h hb0
          · exact h
        exact mul_neg_of_pos_of_neg hsp (mul_neg_of_neg_of_pos ha hb))
    (fun i hi => by
      have hmem : Lf i∈keepLs := hkeep _ (List.get_mem _ _) hi
      obtain ⟨hlb,_,hbx⟩ := hboxF i
      have hq80 : (qB : Real)=2^80 := by unfold qB; push_cast; ring
      obtain ⟨lq,hlqd⟩ : ∃ lq : Rat,lq=(Lf i : Rat)/qB := ⟨_,rfl⟩
      obtain ⟨rq,hrqd⟩ : ∃ rq : Rat,rq=((Lf i+1 : Int) : Rat)/qB := ⟨_,rfl⟩
      have hlq : (lq : Real)=(Lf i : Real)/qB := by rw [hlqd]; push_cast; rfl
      have hrq : (rq : Real)=((Lf i+1 : Int) : Real)/qB := by rw [hrqd]; push_cast; rfl
      have hlt : (Lf i : Real)/qB<((Lf i+1 : Int) : Real)/qB := by
        push_cast
        rw [← sub_pos,← sub_div]
        exact div_pos (by linarith) hq0
      have hF' : ∀ y∈Icc (lq : Real) (rq : Real),
          HasDerivAt F (ftZ (colZ Vc) (colPolesP C V false false) 0 y) y := by
        intro y hy
        rw [hlq,hrq] at hy
        obtain ⟨_,_,_,⟨hy1,hy2⟩,hy3⟩ := hbx y hy.1 hy.2
        have hy0 : y≠0 := by
          rcases hy3 with h | h
          · exact h.1.ne
          · exact h.1.ne'
        exact colFieldSP_hasDerivAt C hV hVz (colZ Vc) (colZ_spec Vc) false false
          ⟨hy1,hy2⟩ (Or.inr hy0)
      have hbox' : ∀ y∈Icc (lq : Real) (rq : Real),
          |y|≤1 ∧ ((1/2^50 : Rat) : Real)≤|y| ∧ ((1/2^50 : Rat) : Real)≤|y-1| := by
        intro y hy
        rw [hlq,hrq] at hy
        obtain ⟨a,b,c,_⟩ := hbx y hy.1 hy.2
        exact ⟨a,b,c⟩
      have hlr' : lq≤rq := by
        have : (lq : Real)≤rq := by rw [hlq,hrq]; exact hlt.le
        exact_mod_cast this
      have hmidR : (midQ (Lf i) : Real)=((lq : Real)+(rq : Real))/2 := by
        rw [midQ_eq,hlq,hrq]
      have hmid1 : |(midQ (Lf i) : Real)|≤1 := by
        obtain ⟨a,_⟩ := hbx (((Lf i : Real)/qB+((Lf i+1 : Int) : Real)/qB)/2)
          (by linarith) (by linarith)
        rw [midQ_eq]; exact a
      have hval := evLe_capC C hV (midQ (Lf i)) (MY-1/2^28) hmid1 (hvals _ hmem)
      have hpt : F (((lq : Real)+(rq : Real))/2)+((2^50 : Rat) : Real)*
          (((rq : Real)-(lq : Real))/2)≤(MY : Real) := by
        rw [← hmidR]
        have h1 : ((MY-1/2^28 : Rat) : Real)=(MY : Real)-1/2^28 := by push_cast; ring
        rw [h1] at hval
        have h2 : ((2^50 : Rat) : Real)*(((rq : Real)-(lq : Real))/2)=1/2^31 := by
          rw [hlq,hrq,hq80]; push_cast; field_simp; ring
        rw [h2]
        have : (1 : Real)/2^31≤1/2^28 := by
          apply one_div_le_one_div_of_le (by positivity); norm_num
        linarith
      have key := box_cap_of_ftZ (F:=F) (Z:=colZ Vc) (poles:=colPolesP C V false false)
        (l:=lq) (r:=rq) (L:=2^50) (M:=MY) (Bz:=2*uBnd Vc) (δ:=1/2^50) (by norm_num)
        hlr' hF' hbox' (fun y hy => colZ_abs_le Vc y hy) hok hL hpt
      intro x hx
      apply key
      rw [hlq,hrq]
      exact hx)
  have hb' : (0 : Real)<(C.b : Real) := by exact_mod_cast hb
  have hq' : (0 : Real)<(C.q : Real) := by exact_mod_cast hq
  have hfin := CatalanMeasure.GenD.Signed.RouteI.Maxima.Endpoints.col_original_cap C Vc V hV hb' hq' (MY : Real) hmax
  intro x hx
  rw [← colFieldSP_false]
  exact hfin x hx

#print axioms colZ_abs_le
#print axioms col_deriv_form
#print axioms evLe_capC
#print axioms col_cap_terminal
end
end CatalanMeasure.GenD.Signed.RouteI.Maxima.ColGenericD

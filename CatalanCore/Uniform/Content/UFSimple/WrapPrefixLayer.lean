module

public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixClosed
public import CatalanCore.Uniform.Content.BankShared.Reindex

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Arith.Hybrid.Periodic
  CatalanCore.Uniform CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.BankShared

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixLayer

/-- Complement deletion indexes precisely the original retained common set. -/
def keepEquiv {r : ℕ} (S : Finset (Fin r)) : WrapKeep.Keep (univ\S) ≃ S where
  toFun i := ⟨i.1,by simpa only [mem_sdiff,mem_univ,true_and,not_not] using i.2⟩
  invFun i := ⟨i.1,by simpa only [mem_sdiff,mem_univ,true_and,not_not] using i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

section WindowOnly
variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- The explicit original prefix window price on any retained common
minor, including the empty retained set. -/
theorem window_commonMinor_gle {Fr : Frame} (T : TwoTermData Fr q o)
    (D : CatalanCore.Arith.Hybrid.Periodic.PoleData Fr p N)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (Jr Jc : Finset (Fin d))
    (hinj : Function.Injective (Sum.elim
      (fun z => (WrapPrefixMember.Schur.surplusRow H z:ZMod p))
      (fun y => (WrapPrefixMember.Schur.surplusCol H y:ZMod p))))
    (hJr : ∀ z∈Jr,WrapPrefixMember.Schur.surplusRow H z∈Icc H.t0 H.tv)
    (hJc : ∀ y∈Jc,WrapPrefixMember.Schur.surplusCol H y∈Icc H.t0 H.tv)
    (S : Finset (Fin r)) :
    GLE p (2*(r+n*p+e)-(d+WrapCount.gain (Jr.card+Jc.card-d) (p-(H.tv+1-H.t0))))
      (commonMinorPoly Fr r (n*p+e) S) := by
  have hh := WrapPrefixClosed.window_price_gle H T D hsq Jr Jc hinj hJr hJc (univ\S)
  have he := CatalanCore.Uniform.Content.Wire.det_fullN_reindex Fr
    (fun a:S => (a.1:ℕ)) (WrapPrefixMember.common (univ\S))
    (keepEquiv S) (fun _ => rfl)
    (fun i:Fin (n*p+e) => r+2*(i:ℕ)) (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1)
  rw [he] at hh
  exact hh

end WindowOnly

/-! # The route-independent assembly

Section 1 fixes the numerical form of a closed cell price with an abstract
credited residue count `c` (the retained set then has at most `p - c`
elements).  Section 2 records the retained-set bound as an input (`Supply`):
route R1 supplies `c = (tv + 1) - w0`, the later routes supply the larger
counts with outside kills.  Sections 3-5 build the six-candidate Setup
instantiation for every original common-deletion member of every prefix
strip and take the minimum. -/

section Price

/-- The closed price of a cell with credited count `c`; the retained source
has at most `p - c` elements. -/
def pb (d a p t0 tv c : ℕ) : ℕ :=
  2*(a+d)-(d+((min (tv+1) (a+2*d)-t0)-d)+(((min (tv+1) (a+2*d)-t0)-d)-(p-c)))

/-- Route R1: the credited interval alone (the outside kill term dropped). -/
def cr1 (_d _a _p w0 w1 : ℕ) : ℕ := w1+1-w0

/-- The full credit of the existing checker: window plus outside border. -/
def cr3 (d a p w0 w1 : ℕ) : ℕ := (w1+1-w0)+(2*d-beta3 d a p w0 w1)

theorem closedBound_eq_pb (d a p t0 tv w0 : ℕ) :
    closedBound d a p t0 tv w0=pb d a p t0 tv (cr3 d a p w0 tv) := rfl

/-- One block-bit candidate in virtual coordinates (`B` the block start). -/
def cand0 (cr : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (d a p B lo hi : ℕ) : ℕ :=
  pb d a p (max a (B+lo)) (min (B+hi) (a+p-1))
    (cr d a p (B+lo) (min (B+hi) (a+p-1)))

def candG (cr : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (r p m k n j : ℕ) (z : Bool) : ℕ :=
  cand0 cr (WrapExpr.dim m p) (WrapExpr.virtual r m p) p (p*(r/p)+(n+j)*p)
    (if z then k else 0) (if z then p-1 else k-1)

/-- The minimum over the six unconditional candidates. -/
def priceG (cr : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (r p m k n : ℕ) : ℕ :=
  min (min (min (candG cr r p m k n 0 false) (candG cr r p m k n 0 true))
    (min (candG cr r p m k n 1 false) (candG cr r p m k n 1 true)))
    (min (candG cr r p m k n 2 false) (candG cr r p m k n 2 true))

theorem candidate_eq_candG (r p m k n j : ℕ) (z : Bool) :
    WrapExpr.candidate r p m k n j z=candG cr3 r p m k n j z := by
  cases z <;> rfl

theorem price_eq_priceG (r p m k n : ℕ) :
    WrapExpr.price r p m k n=priceG cr3 r p m k n := by
  unfold WrapExpr.price priceG
  simp only [candidate_eq_candG]

end Price

section Supply
variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]

/-- The standard spectral parameter and normalising unit of the family. -/
noncomputable abbrev stdS (p : ℕ) [Fact p.Prime] : GaussLoc p :=
  algebraMap (LocRing p)[X] (GaussLoc p) Polynomial.X

noncomputable abbrev stdU (p : ℕ) [Fact p.Prime] (Fr : Frame) : GaussLoc p :=
  WrapOriginalEntry.normInv p Fr

/-- The original arithmetic and geometry of a credited interval `[w0, w1]`
attached to a Setup window: exactly the hypotheses of
`credited_interval_zero` and of the outside count `retained_closed_bound`. -/
structure CreditWindow (H : WrapPrefixWindow.Setup p q o r n e b d shift N) (w0 w1 : ℕ) : Prop where
  hb : b≤p
  hcolour : ∀ i:Fin b,(H.xs (Sum.inr i):ZMod p)=((r+(i:ℕ):ℕ):ZMod p)
  h0 : H.t0∈Icc w0 w1
  hhi : w1<r+2*n*p+b+p
  hdiv : w1/p=w0/p
  hw : ∀ v∈Ioc w0 w1,res p (v:GaussLoc p)≠0 ∧ res p (WrapIncrement.argument p q o v)≠0
  hcover : ∀ v∈Ico (r+2*n*p+b) (r+2*n*p+b+2*d),
    (∃ z:Fin d,WrapPrefixSchur.surplusRow H z=v) ∨ (∃ y:Fin d,WrapPrefixSchur.surplusCol H y=v)
  hwidth : 2*d≤p
  hwin : w1<w0+p
  hR : r+2*n*p+b+2*d≤w0+2*p
  hW : w1<r+2*n*p+b+2*p
  /-- The interval starts at least one period after the strip origin
  (virtual start `≥ p`), so the three-translate overlap translates. -/
  hfar : n*p+p≤w0
  /-- The surplus nodes lie in one period after the origin. -/
  hext : b+2*d≤p
  hsurR : ∀ z:Fin d,r+2*n*p+b≤WrapPrefixSchur.surplusRow H z ∧
    WrapPrefixSchur.surplusRow H z<r+2*n*p+b+2*d
  hsurC : ∀ y:Fin d,r+2*n*p+b≤WrapPrefixSchur.surplusCol H y ∧
    WrapPrefixSchur.surplusCol H y<r+2*n*p+b+2*d
  /-- Maximality: an original pole closes the interval on each side. -/
  hleft : ∀ v,r+2*n*p+b≤v → v<w0 → ∃ k,(p∣k ∨ p∣q*k-o) ∧ v<k ∧ k≤w0
  hright : ∀ v,w1<v → v<r+2*n*p+b+2*d → ∃ k,(p∣k ∨ p∣q*k-o) ∧ w1<k ∧ k≤v

/-- **The retained-set input.**  For every credited interval of every
Setup window (in virtual coordinates `w0, w1`, the actual interval being
translated by `n` periods), the full retained source has at most
`p - cr d a p w0 w1` elements, `a = r + n p + b` the virtual start of the
surplus.  Route R1 proves it for `cr1`; the outside-kill routes for the
larger credits. -/
def Supply (Fr : Frame) (q o : ℕ) (cr : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (_T : TwoTermData Fr q o) (p r n e b d shift N : ℕ) [Fact p.Prime]
    (_hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (_D : PoleData Fr p N)
    (H : WrapPrefixWindow.Setup p q o r n e b d shift N) (w0 w1 : ℕ),
    CreditWindow H (w0+n*p) (w1+n*p) →
    (WrapPrefixMember.fullRetained H (stdS p) (stdU p Fr)).card≤p-cr d (r+n*p+b) p w0 w1

/-- **Route R1.**  The credited interval alone: built theorems only,
`credited_interval_zero` on the image interval and the residue-union count
`retained_credit_bound` with `O = ∅`. -/
theorem supply_R1 (Fr : Frame) (q o : ℕ) : Supply Fr q o cr1 := by
  intro T p r n e b d shift N _ hsq D H w0 w1 W
  classical
  have hs := WrapFrameResidue.spectral p
  have hu := WrapFrameResidue.normInv_ne p D
  have huc := WrapFrameResidue.normInv_constant p D
  have hI : ∀ gamma∈(Icc (w0+n*p) (w1+n*p)).image (fun t:ℕ => (t:ZMod p)),
      H.weight (stdS p) (stdU p Fr) gamma=0 := by
    intro gamma hg
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hg
    exact WrapPrefixClosed.credited_interval_zero H W.hb W.hcolour (w0+n*p) (w1+n*p) W.h0 W.hhi
      W.hdiv W.hw (stdS p) (stdU p Fr) hs hu huc t ht
  have hc := WrapPrefixClosed.retained_credit_bound H (stdS p) (stdU p Fr)
    ((Icc (w0+n*p) (w1+n*p)).image (fun t:ℕ => (t:ZMod p))) ∅ hI
    (fun gamma hg => absurd hg (notMem_empty gamma))
  have hcard := card_image_window (p:=p) (Fact.out:p.Prime).pos W.hwin
  rw [union_empty,hcard] at hc
  have hw := W.hwin
  unfold cr1
  omega

/-- **Route R2 ∪ R3: the full closed price.**  Every outside surplus node is
separated from the anchor by an original pole that closes the credited
interval: an integer pole (R3, top fractional coefficient and the Harmonic
Lemma) or a fractional pole (R2, central fractional test).  The kills feed
`retained_closed_bound`, and the virtual-to-actual translation of the
three-translate overlap gives the credit `cr3` of the existing checker. -/
theorem supply_R3 (Fr : Frame) (q o : ℕ) : Supply Fr q o cr3 := by
  intro T p r n e b d shift N _ hsq D H w0 w1 W
  classical
  have hs := WrapFrameResidue.spectral p
  have hu := WrapFrameResidue.normInv_ne p D
  have huc := WrapFrameResidue.normInv_constant p D
  have h0 := mem_Icc.mp W.h0
  have hext := W.hext
  have hkill (v : ℕ) (hv1 : r+2*n*p+b≤v) (hv2 : v<r+2*n*p+b+2*d)
      (hout : ¬∃ w∈Icc (w0+n*p) (w1+n*p),(v:ZMod p)=(w:ZMod p)) :
      ∃ k,(p∣k ∨ p∣q*k-o) ∧ ((v<k ∧ k≤H.t0) ∨ (H.t0<k ∧ k≤v)) := by
    by_cases hlt : v<w0+n*p
    · obtain ⟨k,hk,h1,h2⟩ := W.hleft v hv1 hlt
      exact ⟨k,hk,Or.inl ⟨h1,h2.trans h0.1⟩⟩
    · have hgt : w1+n*p<v := by
        by_contra hc
        exact hout ⟨v,mem_Icc.mpr ⟨by omega,by omega⟩,rfl⟩
      obtain ⟨k,hk,h1,h2⟩ := W.hright v hgt hv2
      exact ⟨k,hk,Or.inr ⟨by omega,h2⟩⟩
  have hc := WrapPrefixClosed.retained_closed_bound H W.hb W.hcolour (w0+n*p) (w1+n*p) W.h0 W.hhi
    W.hdiv W.hw W.hcover W.hwidth W.hwin W.hR W.hW (stdS p) (stdU p Fr) hs hu huc
    (fun z hz => by
      obtain ⟨hv1,hv2⟩ := W.hsurR z
      obtain ⟨k,hk,hsep⟩ := hkill _ hv1 hv2 hz
      exact Or.inr (WrapPrefixClosed.rowCoupling_pole_ne H (stdS p) (stdU p Fr) hs hu huc z k hk hsep
        (by omega) (by omega)))
    (fun y hy => by
      obtain ⟨hv1,hv2⟩ := W.hsurC y
      obtain ⟨k,hk,hsep⟩ := hkill _ hv1 hv2 hy
      exact Or.inr (WrapPrefixClosed.colCoupling_pole_ne H (stdS p) (stdU p Fr) hs hu huc y k hk hsep
        (by omega) (by omega)))
  have hfar := W.hfar
  have ht := WrapPrefixClosed.beta3_translate d (r+n*p+b) p w0 w1 (n*p) (by omega) (by omega)
  have he : r+2*n*p+b=r+n*p+b+n*p := by ring
  have hw : w1+n*p+1-(w0+n*p)=w1+1-w0 := by omega
  rw [he,ht,hw] at hc
  unfold cr3
  exact hc

end Supply

section Counting

/-- Injectivity of the alternating surplus colours, for either parity. -/
theorem inj_of_parity (p a d c0 : ℕ) (hc0 : c0≤1) (hwidth : 2*d≤p) (R C : Fin d → ℕ)
    (hR : ∀ z:Fin d,R z=a+2*(z:ℕ)+c0) (hC : ∀ y:Fin d,C y=a+2*(y:ℕ)+(1-c0)) :
    Function.Injective (Sum.elim (fun z => ((R z:ℕ):ZMod p)) (fun y => ((C y:ℕ):ZMod p))) := by
  have hal := WrapPrefixClosed.alternating_colour_injective p a d hwidth
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc0 with rfl|rfl
  · have h1 : (fun z:Fin d => ((R z:ℕ):ZMod p))=fun i:Fin d => ((a+2*(i:ℕ):ℕ):ZMod p) := by
      funext z; rw [hR z]; try rfl
    have h2 : (fun y:Fin d => ((C y:ℕ):ZMod p))=fun i:Fin d => ((a+2*(i:ℕ)+1:ℕ):ZMod p) := by
      funext y; rw [hC y]; try rfl
    rw [h1,h2]
    exact hal
  · have h1 : (fun z:Fin d => ((R z:ℕ):ZMod p))=fun i:Fin d => ((a+2*(i:ℕ)+1:ℕ):ZMod p) := by
      funext z; rw [hR z]; try rfl
    have h2 : (fun y:Fin d => ((C y:ℕ):ZMod p))=fun i:Fin d => ((a+2*(i:ℕ):ℕ):ZMod p) := by
      funext y; rw [hC y]; try rfl
    rw [h1,h2]
    have hs : Sum.elim (fun i:Fin d => ((a+2*(i:ℕ)+1:ℕ):ZMod p)) (fun i:Fin d => ((a+2*(i:ℕ):ℕ):ZMod p))=
        Sum.elim (fun i:Fin d => ((a+2*(i:ℕ):ℕ):ZMod p)) (fun i:Fin d => ((a+2*(i:ℕ)+1:ℕ):ZMod p))∘Sum.swap := by
      rw [← Sum.elim_swap]
    rw [hs]
    exact hal.comp Sum.swap_leftInverse.injective

/-- The supported dimension count: surplus nodes of either parity in the window. -/
theorem card_J (a d t0 tv c0 : ℕ) (hc0 : c0≤1) (ht0 : a≤t0) (R C : Fin d → ℕ)
    (hR : ∀ z:Fin d,R z=a+2*(z:ℕ)+c0) (hC : ∀ y:Fin d,C y=a+2*(y:ℕ)+(1-c0)) :
    (univ.filter (fun z:Fin d => R z∈Icc t0 tv)).card+(univ.filter (fun y:Fin d => C y∈Icc t0 tv)).card=
      min (tv+1) (a+2*d)-t0 := by
  have hrc := WrapCell.rows_add_cols a d t0 tv ht0
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc0 with rfl|rfl
  · have h1 : univ.filter (fun z:Fin d => R z∈Icc t0 tv)=WrapCell.cols a d t0 tv := by
      unfold WrapCell.cols
      apply Finset.filter_congr
      intro z _
      rw [hR z,mem_Icc]; try omega
    have h2 : univ.filter (fun y:Fin d => C y∈Icc t0 tv)=WrapCell.rows a d t0 tv := by
      unfold WrapCell.rows
      apply Finset.filter_congr
      intro y _
      rw [hC y,mem_Icc]; try omega
    rw [h1,h2,Nat.add_comm]
    exact hrc
  · have h1 : univ.filter (fun z:Fin d => R z∈Icc t0 tv)=WrapCell.rows a d t0 tv := by
      unfold WrapCell.rows
      apply Finset.filter_congr
      intro z _
      rw [hR z,mem_Icc]; try omega
    have h2 : univ.filter (fun y:Fin d => C y∈Icc t0 tv)=WrapCell.cols a d t0 tv := by
      unfold WrapCell.cols
      apply Finset.filter_congr
      intro y _
      rw [hC y,mem_Icc]; try omega
    rw [h1,h2]
    exact hrc

/-- A window with no singular index has nonzero residues at every node. -/
theorem res_ne_of_noSing {Fr : Frame} {q o p : ℕ} [Fact p.Prime] (T : TwoTermData Fr q o) {v : ℕ}
    (hv : 1≤v) (h : ¬ttSing p q o (v:ℤ)) :
    res p (v:GaussLoc p)≠0 ∧ res p (WrapIncrement.argument p q o v)≠0 := by
  rw [ttSing_nat T hv] at h
  have hle : o≤q*v := by have := T.o_lt; nlinarith
  refine ⟨fun hz => h (Or.inl ((WrapSimplePole.res_nat_zero p v).mp hz)),fun hz => h (Or.inr ?_)⟩
  rw [WrapSimplePole.argument_nat p q o v hle] at hz
  exact (WrapSimplePole.res_nat_zero p (q*v-o)).mp hz

end Counting

section WindowPrice
variable {Fr : Frame} {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- Window price with an arbitrary retained-count bound as input. -/
theorem window_price_gle_ret (T : TwoTermData Fr q o) (D : PoleData Fr p N)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (Jr Jc : Finset (Fin d))
    (hinj : Function.Injective (Sum.elim
      (fun z => (WrapPrefixMember.Schur.surplusRow H z:ZMod p))
      (fun y => (WrapPrefixMember.Schur.surplusCol H y:ZMod p))))
    (hJr : ∀ z∈Jr,WrapPrefixMember.Schur.surplusRow H z∈Icc H.t0 H.tv)
    (hJc : ∀ y∈Jc,WrapPrefixMember.Schur.surplusCol H y∈Icc H.t0 H.tv)
    (K : Finset (Fin r)) (R : ℕ)
    (hR : (WrapPrefixMember.fullRetained H (stdS p) (stdU p Fr)).card≤R) :
    GLE p (2*(r+n*p+e)-(d+WrapCount.gain (Jr.card+Jc.card-d) R))
      (CatalanCore.Rect.FullN Fr (WrapPrefixMember.common K) (fun i:Fin (n*p+e) => r+2*(i:ℕ))
        (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1) (Polynomial.X:ℚ[X])).det := by
  have hg := WrapPrefixFamily.window_gle H T D hsq Jr Jc hinj hJr hJc K
  apply hg.mono
  dsimp only [WrapCount.gain]
  change 2*(r+n*p+e)-(d+((Jr.card+Jc.card-d)+((Jr.card+Jc.card-d)-
      (WrapPrefixMember.fullRetained H (stdS p) (stdU p Fr)).card)))≤
    2*(r+n*p+e)-(d+((Jr.card+Jc.card-d)+((Jr.card+Jc.card-d)-R)))
  omega

/-- **The window price in the closed form `pb`**, for a Setup whose surplus
rows and columns sit at `a + 2z + c0`, `a + 2y + (1 - c0)`. -/
theorem window_gle_G (T : TwoTermData Fr q o) (D : PoleData Fr p N)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (c0 : ℕ) (hc0 : c0≤1)
    (hrow : ∀ z:Fin d,WrapPrefixMember.Schur.surplusRow H z=r+2*n*p+b+2*(z:ℕ)+c0)
    (hcol : ∀ y:Fin d,WrapPrefixMember.Schur.surplusCol H y=r+2*n*p+b+2*(y:ℕ)+(1-c0))
    (hwidth : 2*d≤p) (hbd : b+d=e) (ha : r+2*n*p+b≤H.t0)
    (t0v tvv c : ℕ) (ht0 : H.t0=t0v+n*p)
    (hmin : min (H.tv+1) (r+2*n*p+b+2*d)=min (tvv+1+n*p) (r+2*n*p+b+2*d))
    (hret : (WrapPrefixMember.fullRetained H (stdS p) (stdU p Fr)).card≤p-c)
    (K : Finset (Fin r)) :
    GLE p (pb d (r+n*p+b) p t0v tvv c)
      (CatalanCore.Rect.FullN Fr (WrapPrefixMember.common K) (fun i:Fin (n*p+e) => r+2*(i:ℕ))
        (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1) (Polynomial.X:ℚ[X])).det := by
  classical
  have hinj := inj_of_parity p (r+2*n*p+b) d c0 hc0 hwidth
    (fun z => WrapPrefixMember.Schur.surplusRow H z) (fun y => WrapPrefixMember.Schur.surplusCol H y) hrow hcol
  have hcard := card_J (r+2*n*p+b) d H.t0 H.tv c0 hc0 ha
    (fun z => WrapPrefixMember.Schur.surplusRow H z) (fun y => WrapPrefixMember.Schur.surplusCol H y) hrow hcol
  have hh := window_price_gle_ret H T D hsq
    (univ.filter (fun z:Fin d => WrapPrefixMember.Schur.surplusRow H z∈Icc H.t0 H.tv))
    (univ.filter (fun y:Fin d => WrapPrefixMember.Schur.surplusCol H y∈Icc H.t0 H.tv))
    hinj (fun z hz => (mem_filter.mp hz).2) (fun y hy => (mem_filter.mp hy).2) K (p-c) hret
  apply hh.mono
  rw [hcard]
  unfold pb WrapCount.gain
  have h2 : 2*n*p=2*(n*p) := by ring
  omega

end WindowPrice

/-! ### Shapes: the ordinary and the wrapped residual orientation -/

section Shapes
variable {p q o r n e shift N : ℕ} [Fact p.Prime]

/-- A reference Setup of one residual shape together with the geometry of
its surplus nodes.  `b` balanced pairs are absorbed, `d` surplus pairs sit
at `a + 2z + c0`, `a + 2y + (1 - c0)` with `a = r + 2 n p + b`. -/
structure Shape (p q o r n e shift N b d : ℕ) [Fact p.Prime] where
  H0 : WrapPrefixWindow.Setup p q o r n e b d shift N
  hbd : b+d=e
  hd1 : 1≤d
  hwidth : 2*d≤p
  hext : b+2*d≤p
  c0 : ℕ
  hc0 : c0≤1
  hrow : ∀ z:Fin d,WrapPrefixMember.Schur.surplusRow H0 z=r+2*n*p+b+2*(z:ℕ)+c0
  hcol : ∀ y:Fin d,WrapPrefixMember.Schur.surplusCol H0 y=r+2*n*p+b+2*(y:ℕ)+(1-c0)
  hcolour : ∀ i:Fin b,(H0.xs (Sum.inr i):ZMod p)=((r+(i:ℕ):ℕ):ZMod p)
  hfree : ∀ t,r+2*n*p+b≤t → t<r+2*n*p+p → ∀ i:Fin b,(H0.xs (Sum.inr i):ZMod p)≠(t:ZMod p)

variable {b d : ℕ}

/-- The Setup of an arbitrary arithmetic window of the shape. -/
noncomputable def Shape.win (S : Shape p q o r n e shift N b d) (t0 tv : ℕ)
    (hlo : r+2*n*p+b≤t0) (hle : t0≤tv) (hhi : tv<r+2*n*p+p) (htvN : tv<N)
    (hdiv : tv/p=t0/p)
    (hw : ∀ h∈Icc 1 (tv-t0),res p ((t0+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t0+h))≠0) :
    WrapPrefixWindow.Setup p q o r n e b d shift N :=
  { S.H0 with
    t0 := t0
    tv := tv
    hlo := by omega
    hle := hle
    hhi := hhi
    htvN := htvN
    hdiv := hdiv
    hw := hw
    hfree := fun t ht i => S.hfree t (hlo.trans (mem_Icc.mp ht).1)
      (lt_of_le_of_lt (mem_Icc.mp ht).2 hhi) i }

/-- Ordinary orientation: no absorbed pair, `d = e ≤ shift`. -/
noncomputable def ordinaryShape {Fr : Frame} {T : TwoTermData Fr q o}
    (A : WrapPrefixClosed.Region (p:=p) Fr q o r n e shift N T) (he1 : 1≤e) (hesh : e≤shift) :
    Shape p q o r n e shift N 0 e where
  H0 := A.ordinarySetup (r+2*n*p) (r+2*n*p) le_rfl le_rfl
    (by have := (Fact.out:p.Prime).pos; omega)
    (by have := A.hsize; have h2 : 2*n*p=2*(n*p) := by ring
        omega)
    rfl (by intro h hh; have := mem_Icc.mp hh; omega)
  hbd := by omega
  hd1 := he1
  hwidth := by have := A.hp; omega
  hext := by have := A.hp; omega
  c0 := 0
  hc0 := Nat.zero_le _
  hrow := by
    intro z
    have h := WrapPrefixClosed.ordinary_row (p:=p) r n e shift z
    refine h.trans ?_
    omega
  hcol := by
    intro y
    have h := WrapPrefixClosed.ordinary_col (p:=p) r n e shift y
    refine h.trans ?_
    omega
  hcolour := fun i => Fin.elim0 i
  hfree := fun _ _ _ i => Fin.elim0 i

/-- Wrapped orientation: `e = shift + l`, `2l - 1` absorbed pairs. -/
noncomputable def wrappedShape {Fr : Frame} {T : TwoTermData Fr q o} (l : ℕ) (hl : 1≤l) (hls : l≤shift)
    (A : WrapPrefixClosed.Region (p:=p) Fr q o r n (shift+l) shift N T) :
    Shape p q o r n (shift+l) shift N (2*l-1) (shift+1-l) where
  H0 := WrapPrefixClosed.wrappedSetup l hl hls A (r+2*n*p+(2*l-1)) (r+2*n*p+(2*l-1)) le_rfl le_rfl
    (by have := A.hp; omega)
    (by have := A.hsize; have h2 : 2*n*p=2*(n*p) := by ring
        omega)
    rfl (by intro h hh; have := mem_Icc.mp hh; omega)
  hbd := by omega
  hd1 := by omega
  hwidth := by have := A.hp; omega
  hext := by have := A.hp; omega
  c0 := 1
  hc0 := le_rfl
  hrow := by
    intro z
    exact WrapPrefixClosed.wrapped_row (p:=p) r n shift l hl hls z
  hcol := by
    intro y
    refine (WrapPrefixClosed.wrapped_col (p:=p) r n shift l hl hls y).trans ?_
    omega
  hcolour := fun i => WrapPrefixClosed.wrapped_residual_colour r n shift l hl hls A.hp i
  hfree := fun t h1 h2 i =>
    WrapPrefixWindow.wrapped_residual_absent p r n shift l t hl hls A.hp h1 h2 i

end Shapes

/-! ### The block-bit candidate -/

section Block
variable {Fr : Frame} {p q o r n e shift N b d : ℕ} [Fact p.Prime]

/-- A fractional pole translated by a multiple of the period is a pole. -/
theorem frac_shift (p q o B k : ℕ) (hB : p∣B) (hk : p∣q*k-o) (hle : o≤q*k) : p∣q*(B+k)-o := by
  have e : q*(B+k)-o=q*B+(q*k-o) := by rw [Nat.mul_add]; omega
  rw [e]
  exact dvd_add (Dvd.dvd.mul_left hB q) hk

/-- One block-bit candidate prices every original common-deletion member
of the strip, whatever the supplied retained-set bound. -/
theorem block_gle (cr : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (hsup : Supply Fr q o cr)
    (S : Shape p q o r n e shift N b d) (T : TwoTermData Fr q o) (D : PoleData Fr p N)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (B lo hi : ℕ) (hB : p∣B) (hBr : r+n*p<B+p)
    (hlo : lo<p) (hhi : hi<p)
    (hNo : ∀ v,B+n*p+lo<v → v≤B+n*p+hi → ¬ttSing p q o (v:ℤ))
    (hpl : p∣B+n*p+lo ∨ p∣q*(B+n*p+lo)-o) (hpr : p∣B+n*p+hi+1 ∨ p∣q*(B+n*p+hi+1)-o)
    (K : Finset (Fin r)) :
    GLE p (cand0 cr d (r+n*p+b) p B lo hi)
      (CatalanCore.Rect.FullN Fr (WrapPrefixMember.common K) (fun i:Fin (n*p+e) => r+2*(i:ℕ))
        (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1) (Polynomial.X:ℚ[X])).det := by
  classical
  have hp0 : 0<p := (Fact.out:p.Prime).pos
  have hsize := S.H0.hsize
  have hbd := S.hbd
  have hd1 := S.hd1
  have hext := S.hext
  have h2 : 2*n*p=2*(n*p) := by ring
  obtain ⟨L0,hL0⟩ := hB
  by_cases hok : max (r+n*p+b) (B+lo)≤min (min (B+hi) (r+n*p+b+p-1)) (r+n*p+b+2*d-1)
  · obtain ⟨t0v,ht0v⟩ : ∃ t0v,t0v=max (r+n*p+b) (B+lo) := ⟨_,rfl⟩
    obtain ⟨tvv,htvv⟩ : ∃ tvv,tvv=min (B+hi) (r+n*p+b+p-1) := ⟨_,rfl⟩
    obtain ⟨tvS,htvS⟩ : ∃ tvS,tvS=min tvv (r+n*p+b+2*d-1) := ⟨_,rfl⟩
    have hle : t0v≤tvS := by omega
    have hBL : B+n*p=(L0+n)*p := by rw [hL0]; ring
    have hdivq : ∀ x,B+n*p≤x → x<B+n*p+p → x/p=L0+n := fun x h1 h2' =>
      Nat.div_eq_of_lt_le (by rw [← hBL]; exact h1) (by rw [Nat.add_mul,one_mul,← hBL]; exact h2')
    have hnp : ∀ v,B+n*p+lo<v → v≤B+n*p+hi →
        res p (v:GaussLoc p)≠0 ∧ res p (WrapIncrement.argument p q o v)≠0 :=
      fun v h1 h2' => res_ne_of_noSing T (by omega) (hNo v h1 h2')
    have hdivT : (tvS+n*p)/p=(t0v+n*p)/p := by
      rw [hdivq (tvS+n*p) (by omega) (by omega),hdivq (t0v+n*p) (by omega) (by omega)]
    let H := S.win (t0v+n*p) (tvS+n*p) (by omega) (by omega) (by omega) (by omega) hdivT
      (by
        intro h hh
        have hh' := mem_Icc.mp hh
        have hv : B+n*p+lo<t0v+n*p+h ∧ t0v+n*p+h≤B+n*p+hi := by omega
        exact hnp _ hv.1 hv.2)
    have hHt0 : H.t0=t0v+n*p := rfl
    have hHtv : H.tv=tvS+n*p := rfl
    have hW : CreditWindow H (B+lo+n*p) (tvv+n*p) := by
      refine
        { hb := by have := S.H0.he; omega
          hcolour := S.hcolour
          h0 := ?_
          hhi := by omega
          hdiv := ?_
          hw := ?_
          hcover := ?_
          hwidth := S.hwidth
          hwin := by omega
          hR := by omega
          hW := by omega
          hfar := ?_
          hext := S.hext
          hsurR := ?_
          hsurC := ?_
          hleft := ?_
          hright := ?_ }
      · rw [hHt0]; exact mem_Icc.mpr ⟨by omega,by omega⟩
      · rw [hdivq (tvv+n*p) (by omega) (by omega),hdivq (B+lo+n*p) (by omega) (by omega)]
      · intro v hv
        have hv' := mem_Ioc.mp hv
        exact hnp v (by omega) (by omega)
      · intro v hv
        have hv' := mem_Ico.mp hv
        have hc0 := S.hc0
        obtain ⟨z,hz⟩ : ∃ z:Fin d,(z:ℕ)=(v-(r+2*n*p+b))/2 := ⟨⟨_,by omega⟩,rfl⟩
        by_cases hpar : (v-(r+2*n*p+b))%2=S.c0
        · left
          refine ⟨z,?_⟩
          have hr := S.hrow z
          change WrapPrefixMember.Schur.surplusRow S.H0 z=v
          omega
        · right
          refine ⟨z,?_⟩
          have hr := S.hcol z
          change WrapPrefixMember.Schur.surplusCol S.H0 z=v
          omega
      · have hBp : p≤B := by
          rcases Nat.eq_zero_or_pos L0 with h|h
          · subst h
            have : p≤n*p := Nat.le_mul_of_pos_left p S.H0.hn
            rw [hL0] at hBr
            simp only [mul_zero,zero_add] at hBr
            omega
          · rw [hL0]; exact Nat.le_mul_of_pos_right p h
        omega
      · intro z
        have hr := S.hrow z
        have hc0 := S.hc0
        have := z.2
        change r+2*n*p+b≤WrapPrefixMember.Schur.surplusRow S.H0 z ∧
          WrapPrefixMember.Schur.surplusRow S.H0 z<r+2*n*p+b+2*d
        omega
      · intro y
        have hr := S.hcol y
        have hc0 := S.hc0
        have := y.2
        change r+2*n*p+b≤WrapPrefixMember.Schur.surplusCol S.H0 y ∧
          WrapPrefixMember.Schur.surplusCol S.H0 y<r+2*n*p+b+2*d
        omega
      · intro v _ hv2
        exact ⟨B+lo+n*p,by rw [show B+lo+n*p=B+n*p+lo by ring]; exact hpl,hv2,le_rfl⟩
      · intro v hv1 hv2
        have hw := S.hwidth
        by_cases hc : B+hi≤r+n*p+b+p-1
        · exact ⟨B+n*p+hi+1,hpr,by omega,by omega⟩
        · exfalso; omega
    have hret := hsup T p r n e b d shift N hsq D H (B+lo) tvv hW
    have hg := window_gle_G H T D hsq S.c0 S.hc0 S.hrow S.hcol S.hwidth S.hbd (by omega)
      t0v tvv (cr d (r+n*p+b) p (B+lo) tvv) hHt0 (by omega) hret K
    unfold cand0
    rw [← ht0v,← htvv]
    exact hg
  · have hinj := inj_of_parity p (r+2*n*p+b) d S.c0 S.hc0 S.hwidth
      (fun z => WrapPrefixMember.Schur.surplusRow S.H0 z)
      (fun y => WrapPrefixMember.Schur.surplusCol S.H0 y) S.hrow S.hcol
    have hbase := WrapPrefixClosed.window_baseline_gle S.H0 T D hsq hinj K
    apply hbase.mono
    unfold cand0 pb
    omega

end Block

/-! ### Six candidates, all strips, all members -/

section Members
variable {Fr : Frame} {p q o r n e shift N b d : ℕ} [Fact p.Prime]

theorem dim_np_add (n e p : ℕ) (he : e<p) : WrapExpr.dim (n*p+e) p=min e (p-e) := by
  unfold WrapExpr.dim
  have : (n*p+e)%p=e := by
    rw [Nat.add_comm,Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt he
  rw [this]

/-- Six candidates, minimum, every original common-deletion member. -/
theorem member_gle_shape (cr : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (hsup : Supply Fr q o cr)
    (S : Shape p q o r n e shift N b d) (T : TwoTermData Fr q o) (D : PoleData Fr p N)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (k : ℕ) (hk0 : 1≤k) (hkp : k<p) (hrho : p∣q*k-o)
    (hd : WrapExpr.dim (n*p+e) p=d) (K : Finset (Fin r)) :
    GLE p (priceG cr r p (n*p+e) k n)
      (CatalanCore.Rect.FullN Fr (WrapPrefixMember.common K) (fun i:Fin (n*p+e) => r+2*(i:ℕ))
        (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1) (Polynomial.X:ℚ[X])).det := by
  have hp0 : 0<p := (Fact.out:p.Prime).pos
  have hbd := S.hbd
  have hvirt : WrapExpr.virtual r (n*p+e) p=r+n*p+b := by
    unfold WrapExpr.virtual
    rw [hd]
    omega
  have hcand : ∀ (j : ℕ) (z : Bool), GLE p (candG cr r p (n*p+e) k n j z)
      (CatalanCore.Rect.FullN Fr (WrapPrefixMember.common K) (fun i:Fin (n*p+e) => r+2*(i:ℕ))
        (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1) (Polynomial.X:ℚ[X])).det := by
    intro j z
    unfold candG
    rw [hd,hvirt]
    have hB : p∣p*(r/p)+(n+j)*p := ⟨r/p+(n+j),by ring⟩
    have hBa : p∣p*(r/p)+(n+j)*p+n*p := Nat.dvd_add hB ⟨n,by ring⟩
    have hBr : r+n*p<p*(r/p)+(n+j)*p+p := by
      have h1 := Nat.div_add_mod r p
      have h2 := Nat.mod_lt r hp0
      have h3 : (n+j)*p=n*p+j*p := by ring
      omega
    have hfr : p∣q*(p*(r/p)+(n+j)*p+n*p+k)-o :=
      frac_shift p q o _ k hBa hrho (le_of_lt (lt_of_lt_of_le S.H0.hoq (Nat.le_mul_of_pos_right q hk0)))
    cases z
    · have hNo := noSing_blk (ℓ:=0) (uz:=k-1) T S.H0.hqp hBa (show k-1<p by omega) hrho hk0 hkp (Or.inr (by omega))
      exact block_gle cr hsup S T D hsq _ 0 (k-1) hB hBr (by omega) (by omega) hNo
        (Or.inl (by rw [add_zero]; exact hBa))
        (Or.inr (by rw [show p*(r/p)+(n+j)*p+n*p+(k-1)+1=p*(r/p)+(n+j)*p+n*p+k by omega]; exact hfr)) K
    · have hNo := noSing_blk (ℓ:=k) (uz:=p-1) T S.H0.hqp hBa (show p-1<p by omega) hrho hk0 hkp (Or.inl le_rfl)
      exact block_gle cr hsup S T D hsq _ k (p-1) hB hBr hkp (by omega) hNo (Or.inr hfr)
        (Or.inl (by
          rw [show p*(r/p)+(n+j)*p+n*p+(p-1)+1=p*(r/p)+(n+j)*p+n*p+p*1 by omega]
          exact dvd_add hBa (dvd_mul_right p 1))) K
  unfold priceG
  exact WrapClosed.gle_min (WrapClosed.gle_min (WrapClosed.gle_min (hcand 0 false) (hcand 0 true))
    (WrapClosed.gle_min (hcand 1 false) (hcand 1 true)))
    (WrapClosed.gle_min (hcand 2 false) (hcand 2 true))

end Members

/-! ### The stronger common-minor theorem -/

section CommonMinor
variable {Fr : Frame} {q o : ℕ}

/-- **The stronger prefix layer.**  For every original strip `n ≥ 1`
(`m = n p + e`, `e < p`), every original common-deletion member (every
retained set `S`) has the six-candidate price `priceG cr`, for any retained
bound `cr` supplied as input. -/
theorem commonMinor_gle_G (cr : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (hsup : Supply Fr q o cr)
    {T : TwoTermData Fr q o} {p : ℕ} [Fact p.Prime] {r n e shift N : ℕ}
    (A : WrapPrefixClosed.Region (p:=p) Fr q o r n e shift N T) (k : ℕ) (hk0 : 1≤k) (hkp : k<p)
    (hrho : p∣q*k-o) (S : Finset (Fin r)) :
    GLE p (priceG cr r p (n*p+e) k n) (commonMinorPoly Fr r (n*p+e) S) := by
  have hp := A.hp
  have he := A.he
  have key : ∀ K : Finset (Fin r), GLE p (priceG cr r p (n*p+e) k n)
      (CatalanCore.Rect.FullN Fr (WrapPrefixMember.common K) (fun i:Fin (n*p+e) => r+2*(i:ℕ))
        (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1) (Polynomial.X:ℚ[X])).det := by
    intro K
    rcases Nat.eq_zero_or_pos e with h0|hpos
    · subst h0
      have hd0 : WrapExpr.dim (n*p+0) p=0 := by
        rw [dim_np_add n 0 p (Fact.out:p.Prime).pos]; simp
      have hq : 0<q := A.qpos
      have hNp : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N hq) A.hN
      have hg := WrapPrefixClosed.trivial_member_gle (r:=r) (m:=n*p+0) T A.D A.hqp hNp A.hsq A.hsize K
      have hcd : ∀ B lo hi,cand0 cr 0 (r+n*p) p B lo hi=2*(r+(n*p+0)) := by
        intro B lo hi
        unfold cand0 pb
        omega
      have hv : WrapExpr.virtual r (n*p+0) p=r+n*p := by
        unfold WrapExpr.virtual; rw [hd0]; omega
      have hcg : ∀ j z,candG cr r p (n*p+0) k n j z=2*(r+(n*p+0)) := by
        intro j z
        unfold candG
        rw [hd0,hv]
        exact hcd _ _ _
      unfold priceG
      simp only [hcg,min_self]
      exact hg
    · by_cases hesh : e≤shift
      · have hS := ordinaryShape A hpos hesh
        exact member_gle_shape cr hsup hS T A.D A.hsq k hk0 hkp hrho
          (by rw [dim_np_add n e p he]; omega) K
      · obtain ⟨l,rfl⟩ : ∃ l,e=shift+l := ⟨e-shift,by omega⟩
        have hl : 1≤l := by omega
        have hls : l≤shift := by omega
        have hS := wrappedShape l hl hls A
        exact member_gle_shape cr hsup hS T A.D A.hsq k hk0 hkp hrho
          (by rw [dim_np_add n (shift+l) p he]; omega) K
  have hh := key (univ\S)
  have hre := CatalanCore.Uniform.Content.Wire.det_fullN_reindex Fr
    (fun a:S => (a.1:ℕ)) (WrapPrefixMember.common (univ\S))
    (keepEquiv S) (fun _ => rfl)
    (fun i:Fin (n*p+e) => r+2*(i:ℕ)) (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1)
  rw [hre] at hh
  exact hh

end CommonMinor

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixLayer

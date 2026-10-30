module

public import CatalanCore.Uniform.Content.UFSimple.WrapFamilyClosed
public import CatalanCore.Uniform.Content.BankShared.Reindex

@[expose] public section

/-! # The uniform zero-debit wrapped layer on the actual alternating family -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared

namespace CatalanCore.Uniform.Content.UFSimple.WrapLayer

variable {p q o : ℕ} [Fact p.Prime] {Fr : Frame}

/-- The complement-deletion indexing is the retained indexing. -/
def keepEquiv {r : ℕ} (S : Finset (Fin r)) : WrapKeep.Keep (univ\S) ≃ S where
  toFun i := ⟨i.1,by simpa only [mem_sdiff,mem_univ,true_and,not_not] using i.2⟩
  invFun i := ⟨i.1,by simpa only [mem_sdiff,mem_univ,true_and,not_not] using i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Original common-minor polynomial, with arbitrary retained set. -/
theorem commonMinor_gle (T : TwoTermData Fr q o) (r m rho : ℕ)
    (hqp : q<p) (hN : r+2*m<p*p)
    (hsq : ∀ t,1≤t → t<r+2*m → ¬p^2∣q*t-o)
    (hnorm : Fr.norm∈CatalanCore.S p)
    (hnorm0 : red p Fr.norm≠0) (hm : m<p) (hmp : p≤2*m)
    (hrho1 : 1≤rho) (hrhop : rho<p) (hrho : p∣q*rho-o) (S : Finset (Fin r)) :
    GLE p ((WrapExpr.tWrap 0).evalN r p m rho) (commonMinorPoly Fr r m S) := by
  have hh := WrapFamilyClosed.wrapped_member_gle T hqp hN hsq hnorm hnorm0
    r m hm hmp le_rfl (univ\S) rho hrho1 hrhop hrho
  have he := CatalanCore.Uniform.Content.Wire.det_fullN_reindex Fr
    (fun a:S => (a.1:ℕ)) (fun a:WrapKeep.Keep (univ\S) => (a.1:ℕ))
    (keepEquiv S) (fun _ => rfl) (WrapActual.xs r (m:=m)) (WrapActual.ys r)
  rw [he] at hh
  exact hh

/-- Only arithmetic and frame hypotheses remain at the layer boundary. -/
structure Region (c : ℚ) (hc : 0<c) (Fr : Frame) (q o r p rho : ℕ) [Fact p.Prime] where
  hr : r%2=0
  hqp : q<p
  hN : r+2*(altGeom c hc).borderSize r<p*p
  hsq : ∀ t,1≤t → t<r+2*(altGeom c hc).borderSize r → ¬p^2∣q*t-o
  hnorm : Fr.norm∈CatalanCore.S p
  hnorm0 : red p Fr.norm≠0
  hm : (altGeom c hc).borderSize r<p
  hmp : p≤2*(altGeom c hc).borderSize r
  hrho1 : 1≤rho
  hrhop : rho<p
  hrho : p∣q*rho-o

omit [Fact p.Prime] in
/-- Uniform wrap-aware family content with debit exactly zero. -/
noncomputable def layer (c : ℚ) (hc : 0<c) (T : TwoTermData Fr q o) (depth : ℕ)
    (valid : ℕ → ℕ → Prop) (rho : ℕ → ℕ)
    (hv : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → Region c hc Fr q o r p (rho p)) :
    DebitLayer (altGeom c hc) Fr depth where
  base := fun r p => (WrapExpr.tWrap 0).evalN r p ((altGeom c hc).borderSize r) (rho p)
  debit := 0
  valid := valid
  gle := by
    intro i _ p _ h
    have H := hv i.1 p h
    rw [zero_mul,add_zero,altGeom_member_commonMinor c hc Fr depth H.hr i.2]
    exact commonMinor_gle T i.1 _ (rho p) H.hqp H.hN H.hsq H.hnorm H.hnorm0
      H.hm H.hmp H.hrho1 H.hrhop H.hrho _

end CatalanCore.Uniform.Content.UFSimple.WrapLayer

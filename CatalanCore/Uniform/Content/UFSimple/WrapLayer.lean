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



end CatalanCore.Uniform.Content.UFSimple.WrapLayer

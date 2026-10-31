module

public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixClosed
public import CatalanCore.Uniform.Content.BankShared.Reindex

@[expose] public section

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
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

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixLayer

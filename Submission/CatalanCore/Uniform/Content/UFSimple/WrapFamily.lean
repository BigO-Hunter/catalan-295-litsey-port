module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapMemberSupport

@[expose] public section

/-! # Uniform original wrapped window prices for every common deletion -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapFamily

variable {p N q o r s l : ℕ} [Fact p.Prime] {Fr : Frame} {T : TwoTermData Fr q o}
variable (W : WrapWindow.Window Fr q o r s l p N T)

/-- The actual member source pays every selected-colour loss through the
raw size reduction. No full-determinant tail inheritance is used. -/
theorem setup_price (M : WrapMemberWindow.Setup W) :
    2*(r-M.deleted.card+s+l)-((s+1-l)+
      WrapCount.gain (M.Jr.card+M.Jc.card-(s+1-l)) M.retained.card)≤W.witness.price := by
  have hh := WrapDamage.price_zero M.deleted (colOf (p:=p) (fun i:Fin r => (i:ℕ)))
    (WrapMemberCount.selected W) (r+s+l) (s+1-l)
    (W.Jr.card+W.Jc.card-(s+1-l)) M.oldRet.card
    (M.Jr.card+M.Jc.card-(s+1-l)) M.retained.card
    (WrapMemberCount.sigma_loss W M.deleted) M.retained_count
  rw [M.oldRet_count] at hh
  rw [W.witness_price]
  have hk : M.deleted.card≤r := by simpa using Finset.card_le_univ M.deleted
  have he : r-M.deleted.card+s+l=r+s+l-M.deleted.card := by omega
  simpa only [he,WrapCount.gain] using hh

/-- The closed regular-window bound holds for every original common
principal deletion, with zero debit. -/
theorem window_gle (K : Finset (Fin r)) :
    GLE p (closedBound (s+1-l) (r+2*l-1) p W.t0 W.tv W.w0)
      (FullN Fr (fun i : WrapKeep.Keep K => (i.1:ℕ))
        (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])).det := by
  by_cases hpos : 0<(WrapMemberCount.rows W K).card+(WrapMemberCount.cols W K).card-(s+1-l)
  · obtain ⟨t,ht0,htv,htp,hu⟩ := WrapMemberCount.representative_exists W K hpos
    let M : WrapMemberWindow.Setup W := ⟨K,t,⟨ht0,htv⟩,htp,hu⟩
    exact M.gle.mono ((setup_price W M).trans W.price_le)
  · have hs := WrapMemberCount.sigma_loss W K
    have hb := WrapDamage.deletion_budget K (colOf (p:=p) (fun i:Fin r => (i:ℕ)))
      (WrapMemberCount.selected W)
    have hpaid : (s+1-l)+WrapCount.gain (W.Jr.card+W.Jc.card-(s+1-l)) W.jblock.sJ≤
        (s+1-l)+2*K.card := by
      unfold WrapCount.gain
      omega
    have hh := WrapMember.large_deletion (WrapRestrict.windowHyp W) K _ hpaid
    have he : 2*(r+s+l)-((s+1-l)+WrapCount.gain
        (W.Jr.card+W.Jc.card-(s+1-l)) W.jblock.sJ)=W.witness.price := by
      rw [W.witness_price]; rfl
    rw [he] at hh
    exact hh.mono W.price_le

end CatalanCore.Uniform.Content.UFSimple.WrapFamily

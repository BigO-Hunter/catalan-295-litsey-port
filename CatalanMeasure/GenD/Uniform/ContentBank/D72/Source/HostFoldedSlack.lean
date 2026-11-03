module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.HostRows
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.W.Prof
noncomputable section

theorem responseProf_same_blocks {p b b' ex K : Nat} [Fact p.Prime]
    (hb : b = b') (hK : K = b * 4 + 2 + ex) (hK' : K = b' * 4 + 2 + ex)
    (k0 : Int) (ah : Nat) :
    responseProf (p := p) hK k0 ah = responseProf hK' k0 ah := by
  subst b'
  rfl

theorem slack_zero_of_folded {p n b ex K : Nat} [Fact p.Prime]
    (hK : K = b * 4 + 2 + ex) (k0 : Int) (ah aq : Nat) (slots : Fin n → Option (Fin K))
    (H J : Nat) (S : Int) (low c : Fin n) (y : Fin n → ZMod p)
    (h : foldedResponseLinear hK k0 ah aq slots H J S low (some c) y = 0)
    (hn : sparseSourceIns slots y = 0) (hl : y low = 0) : y c = 0 := by
  simpa [foldedResponseLinear, optionalProjection, LinearMap.sum_apply, hn, hl] using h

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source

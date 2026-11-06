module
public import CatalanMeasure.GenD.Uniform.W.Prof.Packet

@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy
open CatalanMeasure.GenD.Uniform.W.Prof

private theorem kerOK_append {V : List (List Int)} {n d : Nat} {K L B : List (List Int)}
    (hK : kerOK V n d K B = true) (hL : kerOK V n d L B = true) :
    kerOK V n d (K ++ L) B = true := by
  simp only [kerOK, lmul, List.map_append, List.all_append, Bool.and_eq_true] at *
  exact ⟨⟨⟨hK.1.1.1, hK.1.1.2, hL.1.1.2⟩, hK.1.2⟩, hK.2, hL.2⟩

theorem kerOK_join {V : List (List Int)} {n d i : Nat} {K B : List (List Int)}
    (hK : kerOK V n d (K.take i) B = true)
    (hL : kerOK V n d (K.drop i) B = true) : kerOK V n d K B = true := by
  simpa only [List.take_append_drop] using kerOK_append hK hL

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy

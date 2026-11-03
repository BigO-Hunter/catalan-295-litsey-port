module

public import CatalanMeasure.GenD.Uniform.W.Prof.Packet

@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD.Uniform.W.Prof

/-- Assemble the original head checker from its shape checks and its original
matrix product checked one row at a time. -/
theorem checkHead_of_rows (pk : Packet)
    (hsmall : (shape pk.v pk.d pk.n && shape pk.v pk.v.length pk.n &&
      pk.piv.length == pk.v.length && pk.piv.all (· < pk.n) &&
      shape pk.adj pk.v.length pk.v.length) = true)
    (hrows : ∀ i < pk.v.length,
      ((pivCols pk.v pk.piv).map (dot (pk.adj.getD i [])) ==
        (idScaled pk.v.length pk.delta).getD i []) = true) :
    pk.checkHead = true := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hsmall
  have hw : shape pk.adj pk.v.length pk.v.length = true := by tauto
  have ha := (shape_sound hw).1
  have hprod : lmul pk.adj (pivCols pk.v pk.piv) = idScaled pk.v.length pk.delta := by
    apply List.ext_getElem
    · simpa only [lmul, List.length_map, idScaled, List.length_range] using ha
    · intro i hl hr
      have hi : i < pk.v.length := by
        simpa only [idScaled, List.length_map, List.length_range] using hr
      have hl' : i < pk.adj.length := by simpa only [lmul, List.length_map] using hl
      have he := beq_iff_eq.mp (hrows i hi)
      have hL : (lmul pk.adj (pivCols pk.v pk.piv)).getD i [] =
          (pivCols pk.v pk.piv).map (dot (pk.adj.getD i [])) := by
        simp [lmul, List.getD_eq_getElem?_getD, hl']
      rw [← hL] at he
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl,
        List.getElem?_eq_getElem hr, Option.getD_some] using he
  simp only [Packet.checkHead, indOK, Bool.and_eq_true, beq_iff_eq]
  tauto

end CatalanMeasure.GenD.Uniform.ContentBank.D72

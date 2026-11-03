module
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceNative
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
/-! Exact cleared scalar moments shared by the full D72 source bank.
This is the first production source table and its check-class calibration. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.W.Charts6 OAI.InternalCatalan

#time def sourceScale : Int := 6440755335035039829226159204238433976320000

#time def scalarValues : List Int := [
  12881510670070079658452318408476867952640000,
  0,
  8587673780046719772301545605651245301760000,
  0,
  6870139024037375817841236484520996241408000,
  0,
  5888690592032036415292488415303711064064000,
  0,
  5234391637361810146926656369158854279168000,
  0,
  4758537852147100133569687608326231162880000,
  0,
  4392496478905015507910480869224213381120000,
  0,
  4099663380311347807383115477942599155712000,
  0,
  3858506710881268524595873391004799205376000,
  0,
  3655427410308570181196090580951915036672000,
  0,
  3481359438389114458281991029478014320640000,
  0,
  3329995984546109481834947941239839784960000,
  0,
  3196796145164265102561550023590246193561600,
  0,
  3078396287935958987651862985679496334540800,
  0,
  2972244691800236263939729779276755081625600,
  0,
  2876365830774422190909415915429117820928000,
  0,
  2789203229841863942700039675567629402112000,
  0,
  2709511708989239258622895684837125704908800,
  0,
  2636281662800340900281736342003689875046400,
  0,
  2568684697087511646428358487080518339788800,
  0,
  2506033850817084533100837548371237404672000,
  0]

-- kcost: 0.30s estimated (1500 provisional structural/arithmetic units *0.0002s/unit).
-- Includes zero-default list traversal; first measured check-class rate is pending.
#time theorem scalarValues_check : intScalarCheck 42 sourceScale scalarValues = true := by
  decide +kernel

#time theorem scalarValues_sound {p : Nat} [Fact p.Prime] (hp : 44 < p)
    (hz : (sourceScale : ZMod p) ≠ 0) :
    ∀ i, i < 42 → ResRec.Gd p (momentScalar i)
      ((intAt scalarValues i : ZMod p) / (sourceScale : ZMod p)) :=
  (intScalarCheck_sound 42 hp sourceScale hz scalarValues scalarValues_check).2.2

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source

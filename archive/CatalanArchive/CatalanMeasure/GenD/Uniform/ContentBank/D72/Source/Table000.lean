module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Encoding
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
/-! Exact cleared scalar moments shared by the full D72 source bank.
This is the first production source table and its check-class calibration. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.W.Charts6 OAI.InternalCatalan

#time def sourceScale : Int := sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 37 false

#time def scalarValues : List Int := [
  sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 38 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 39 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 41 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 42 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 45 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [67622890073651833142345248125]) 0) 46 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 48 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [7282465084854812799944872875]) 0) 49 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [428380299109106635290874875]) 0) 53 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [202916983788524195664098625]) 0) 54 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [48313567568696237062880625]) 0) 56 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [23106488837202548160508125]) 0) 57 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [2772778660464305779260975]) 0) 60 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [1335041577260591671496025]) 0) 61 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [322251415200832472430075]) 0) 63 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [155928104129435067304875]) 0) 64 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [4725094064528335372875]) 0) 69 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [2295045688485191466825]) 0) 70 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [558254356658560086525]) 0) 72 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [271970071192631837025]) 0) 73 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false,
  sourceLit (List.headD (raw_ints% [33167081852759980125]) 0) 76 false,
  sourceLit (List.headD (raw_ints% [0]) 0) 0 false]

-- kcost: 2s estimated (10000 provisional decoder/structural/arithmetic units *0.0002s/unit).
-- Includes zero-default list traversal; rescaled literal check-class rate is pending.
#time theorem scalarValues_check : intScalarCheck 42 sourceScale scalarValues = true := by
  decide +kernel

#time theorem scalarValues_sound {p : Nat} [Fact p.Prime] (hp : 44 < p)
    (hz : (sourceScale : ZMod p) ≠ 0) :
    ∀ i, i < 42 → ResRec.Gd p (momentScalar i)
      ((intAt scalarValues i : ZMod p) / (sourceScale : ZMod p)) :=
  (intScalarCheck_sound 42 hp sourceScale hz scalarValues scalarValues_check).2.2

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source

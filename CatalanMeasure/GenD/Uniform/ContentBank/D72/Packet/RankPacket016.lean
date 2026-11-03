module
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostRank
public import Mathlib.Tactic.FinCases
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankBasis004
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart036
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart037
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart038
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart039
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart040
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart041
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart086
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankPacket016
open CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Charts6

#time def delta : Int := CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankBasis004.signedLit (CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankBasis004.wordMag (raw_ints% [127278100439735, 156313565149999, 3425481356097, 208146354756969, 139328989948303, 106147160170999, 30308980896447, 145051791386946, 152230509811962, 111400423617388, 38129508999290, 65600139236120, 30558568634413, 40684545223777])) 7 false
#time def adj000 : Int := CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankBasis004.signedLit (CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankBasis004.wordMag (raw_ints% [157811384180019, 175812749223348, 75663101126999, 36402232315504, 268267420649032, 63433312147842, 185178200190001, 154138410034183, 160262212413264, 3876])) 7 false
#time def adj001 : Int := CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankBasis004.signedLit (CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankBasis004.wordMag (raw_ints% [28631511384303, 49120668327314, 35784554371988, 96669793072056, 13189191680434, 8488613993336, 198423692098423, 272242679792860, 41075000334069, 82707])) 7 false
#time def adj002 : Int := CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankBasis004.signedLit (CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankBasis004.wordMag (raw_ints% [35933753279709, 176097599212769, 280905174144095, 11020735026673, 831825419434])) 7 false

#time def pivots : List (Fin 33) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]
#time def adjTape : List Int := [adj000, adj001, adj002]
#time def head : DiagHead 3 33 :=
  ⟨fun i => pivots.getD i.val ⟨0, by decide⟩, fun i => adjTape.getD i.val 0, delta⟩
#time def headInput : PackedPacketInput := ⟨33, 3, CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankBasis004.basis, head, []⟩
-- kcost: 0.068 s provisional; 3 diagonal products and column tags, one nonzero delta guard.
#time theorem headCheck : head.check CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankBasis004.basis = true := by decide +kernel
#time def packet : Packet := { headInput.packet with charts := [CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart036.chart001, CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart037.chart001, CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart038.chart001, CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart039.chart002, CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart040.chart002, CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart040.chart003, CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart039.chart003, CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart041.chart002, CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart041.chart003, CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart086.chart] }
#time theorem ranks : PacketChartRanks packet := by
  apply packetChartRanks_of_rows_or_kernel packet
  · exact packedPacket_headOnly_sound headInput headCheck
  · intro g
    fin_cases g
    · exact Or.inr CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart036.chartSound001
    · exact Or.inr CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart037.chartSound001
    · exact Or.inr CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart038.chartSound001
    · exact Or.inr CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart039.chartSound002
    · exact Or.inr CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart040.chartSound002
    · exact Or.inr CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart040.chartSound003
    · exact Or.inr CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart039.chartSound003
    · exact Or.inr CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart041.chartSound002
    · exact Or.inr CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart041.chartSound003
    · exact Or.inl CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankChart086.rowCount

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.RankPacket016

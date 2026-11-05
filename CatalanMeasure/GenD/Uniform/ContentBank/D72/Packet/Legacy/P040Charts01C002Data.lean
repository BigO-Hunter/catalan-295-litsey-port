module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040Base

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C002
#time def pivTape : List (Fin 90) :=
  []

#time def freeTape : List (Fin 90) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 90) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inr ⟨17, by decide⟩, .inr ⟨18, by decide⟩, .inr ⟨19, by decide⟩, .inr ⟨20, by decide⟩, .inr ⟨21, by decide⟩, .inr ⟨22, by decide⟩, .inr ⟨23, by decide⟩, .inr ⟨24, by decide⟩, .inr ⟨25, by decide⟩, .inr ⟨26, by decide⟩, .inr ⟨27, by decide⟩, .inr ⟨28, by decide⟩, .inr ⟨29, by decide⟩, .inr ⟨30, by decide⟩, .inr ⟨31, by decide⟩, .inr ⟨32, by decide⟩, .inr ⟨33, by decide⟩, .inr ⟨34, by decide⟩, .inr ⟨35, by decide⟩, .inr ⟨36, by decide⟩, .inr ⟨37, by decide⟩, .inr ⟨38, by decide⟩, .inr ⟨39, by decide⟩, .inr ⟨40, by decide⟩, .inr ⟨41, by decide⟩, .inr ⟨42, by decide⟩, .inr ⟨43, by decide⟩, .inr ⟨44, by decide⟩, .inr ⟨45, by decide⟩, .inr ⟨46, by decide⟩, .inr ⟨47, by decide⟩, .inr ⟨48, by decide⟩, .inr ⟨49, by decide⟩, .inr ⟨50, by decide⟩, .inr ⟨51, by decide⟩, .inr ⟨52, by decide⟩, .inr ⟨53, by decide⟩, .inr ⟨54, by decide⟩, .inr ⟨55, by decide⟩, .inr ⟨56, by decide⟩, .inr ⟨57, by decide⟩, .inr ⟨58, by decide⟩, .inr ⟨59, by decide⟩, .inr ⟨60, by decide⟩, .inr ⟨61, by decide⟩, .inr ⟨62, by decide⟩, .inr ⟨63, by decide⟩, .inr ⟨64, by decide⟩, .inr ⟨65, by decide⟩, .inr ⟨66, by decide⟩, .inr ⟨67, by decide⟩, .inr ⟨68, by decide⟩, .inr ⟨69, by decide⟩, .inr ⟨70, by decide⟩, .inr ⟨71, by decide⟩, .inr ⟨72, by decide⟩, .inr ⟨73, by decide⟩, .inr ⟨74, by decide⟩, .inr ⟨75, by decide⟩, .inr ⟨76, by decide⟩, .inr ⟨77, by decide⟩, .inr ⟨78, by decide⟩, .inr ⟨79, by decide⟩, .inr ⟨80, by decide⟩, .inr ⟨81, by decide⟩, .inr ⟨82, by decide⟩, .inr ⟨83, by decide⟩, .inr ⟨84, by decide⟩, .inr ⟨85, by decide⟩, .inr ⟨86, by decide⟩, .inr ⟨87, by decide⟩, .inr ⟨88, by decide⟩, .inr ⟨89, by decide⟩]

#time def roles : GraphRoles 90 0 90 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [2290817805439991849134348951129995, 1824858382727774232772932165940904895, 1842047781949884156337594579837932409, 20637341296227282809757367434947555, 1712624841623834601557658660862640243, 1727466929583349851545780678531877459, 13276635961357089282473055697749747, 1659759652357955970294873226461324455, 836457805514769098321896443982116301, 13282629992669320093083986637080307, 1659518297778406244427766438071641255, 836460802530425213727201909451781581, 20627882522634506067219428343491555, 1712890172328633250667209173009645683, 1727460000098788759681926662227626579, 2291906876342621995352926248947595, 1824541357959482292965521864819573695, 1842056785187021675667659158880932729, 113326892840877959195774113650661735, 2006254252500488866072383732874937843, 31698823407357242792417608007779961, 166031546421160453007849517661558093, 2277848929322994129748618319422220635, 577020784333225487729587635952534333, 59840740853122809980537891145056315, 2670380438185130678103781803521170215, 2713477647166553643848351626051920685, 172308486503487482513710871854884675, 3235300782972959089437224577743121675, 3297457583586019848797924934341915295, 502164219984754909118510703637383105, 4048848330213030538213468778360247615]) [6, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 6, 0, 1, 1, 0, 7, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [2072119388288874861471928690844533875, 742385387346385143001883209771011495, 5243957662911978725911267392292654095, 2694394191954444887532125647548731175, 562374818150416301013787538217828105, 7018389879598571110221001617444293595, 7255923407556107520093709581304130055, 435069526654887951037004000952470763, 9742956208115309134021567698035278935, 10120951150476491926269300661549669317, 2783435814681216355392328840856322075, 13979502306076778326813065632683825803, 3661166267944315021452411376553968611, 4558817873673096788156131065950792705, 20876699466840174555590883061460567235, 2748364845016446653669763176627873653, 973101378429551834960854855497459815, 32214773800769165479437589896486996623, 34330547661241084697201075322953460449, 6806591014708599216904605735947324009, 52015943576585833274338238437379281315, 55728540718094697810697125638827786987, 25087599721001412895086755502729248373, 86667501918437959214674435784065588695, 47214661234256654569796546306725841689, 47206724704903751114638540041856625755, 152366342460591484854685260448296274807, 83361823447209236574659194079018778753, 47526918353806381085714189101010395695, 275494400738052963673228595951492091715, 308984208306934986435385306401914974651, 24252885801310376555877031334873058495]) [2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 4, 4, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 4] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000_p02 : List Int :=
  decoded (raw_ints% [532581689291042533540398773256379440367, 598061131425030761053829935282920234001, 433807321571178425395531632789646016207, 1051586746379985013461293598667429963555, 153236442425836524862047227343943839771, 969313101250888278957873661071175551669, 2267810975575756235122525304414963505195, 657252990557189725812445778153093071511, 615836089646021771625023867262626798945, 4928839151383538129292788242952132170231, 6061669422063734268707752242734055033493, 3045418364942266248353002743536930753935, 12121188409912104581122907180616992288315, 14615850510532353851913853198858423737143, 18261981071567970549654025117656221252905, 29292186070921668116116810191247578201711, 19484334155992428449136941901794253248959, 50645041413300557249677986431070466818831, 85169112696183986779739007651241877299935, 53937845398426692348802947676157597284827, 95835425787622472334768381308201829262677, 231872351724123897114828755915529445477035, 350191583785398886616820644399789319913839, 151669791706724916226218851297766403967505, 851852518997163765457886058116856511401351, 1148541602187543496191232812207258594309213, 1915353951723963895509893746274092249, 753455356705962029802808125, 753455356705962029802808125]) [0, 1, 1, 0, 4, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 0, 30, 30] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, true]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01 ++ chartRows000_p02

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01 ++ chartRows001_p02

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01 ++ chartRows002_p02

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002]

#time def graph : KernelGraph 90 0 90 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 904.6134 s provisional ×3 model; 1507689 exact original rank units.
end C002

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040

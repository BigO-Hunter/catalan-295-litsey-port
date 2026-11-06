module
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketGraphCert
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P042
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

#time def basisScales : List Int :=
  decoded (raw_ints% [6802845854504778166209900342431000139, 27934406670627741592585518251978101005, 9311468890209247197528506083992700335]) [1, 2, 2] [false, false, false]

#time def ambientRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 7823827741201168670735631557748019993, 0, 0, 713550938814468499152022111085972045, 0, 0, 0, 327671851773957495487144150746898825, 0, 0, 0, 1509163966934794284220285919602855, 0, 0, 0, 5910977195491304758273208464642707, 0, 0, 0, 7718055021138621324496032180693693, 0, 0, 0, 3468041793120954400271973632685345, 0, 0, 0, 0, 0, 1628514845635554302023542832460339647]) [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] [false, false, true, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, false, false, false]

#time def ambientRows000_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def ambientRows000 : List Int := ambientRows000_p00 ++ ambientRows000_p01

#time def ambientRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 40188699335585318468008394687080301085, 0, 0, 0, 16449984534528153641854396841360975985, 0, 0, 0, 2495368351135880637258950521743166455, 0, 0, 0, 1105195345021224723114870885252256185, 0, 0, 0, 377020896988536919737907842230778645, 0, 0, 0, 152405604882737394511986903529868625, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows001_p01 : List Int :=
  decoded (raw_ints% [2032447326046798957099935533986244213]) [4] [true]

#time def ambientRows001 : List Int := ambientRows001_p00 ++ ambientRows001_p01

#time def ambientRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 13346526416707396340142066893294878035, 0, 0, 0, 5547725526368932481828970164472657135, 0, 0, 0, 838195543698904957597061559467168055, 0, 0, 0, 376602987271113393693781636887367905, 0, 0, 0, 127644835775048464584061786311083115, 0, 0, 0, 52427330870249478242079644006534175, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows002_p01 : List Int :=
  decoded (raw_ints% [406212772402823165415231634510051279]) [5] [true]

#time def ambientRows002 : List Int := ambientRows002_p00 ++ ambientRows002_p01

#time def ambientRows : List (List Int) :=
  [ambientRows000, ambientRows001, ambientRows002]

#time def ambientIndex : List Nat :=
  [0, 0, 0, 1, 2, 0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]

#time def colTags : List (Option (Fin 3)) :=
  [some ⟨0, by decide⟩, some ⟨1, by decide⟩, none, none, none, some ⟨2, by decide⟩, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]

#time def basis : DiagView 3 36 :=
  ⟨fun x => colTags.getD x.val none, fun a => basisScales.getD a.val 0,
    fun a x => Mx ambientRows a.val (ambientIndex.getD x.val 0)⟩

namespace C000
#time def pivTape : List (Fin 3) :=
  []

#time def freeTape : List (Fin 3) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 3) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩]

#time def roles : GraphRoles 3 0 3 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [1, 1, 0, 0]) [0, 1, 0, 0] [false, true, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008]

#time def graph : KernelGraph 3 0 3 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 0.9882 s provisional ×3 model; 1647 exact original rank units.
#time theorem checked : chart.check 36 3 basis.matrix = true := by decide +kernel
end C000

namespace C001
#time def pivTape : List (Fin 3) :=
  [⟨0, by decide⟩]

#time def freeTape : List (Fin 3) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩]

#time def roleTape : List (Fin 1 ⊕ Fin 2) :=
  [.inl ⟨0, by decide⟩, .inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩]

#time def roles : GraphRoles 3 1 2 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [194529306226045326980582983426608094667]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [5181471675815793313014387083444277857505, 1964804446726569725226120214927459677435]) [0, 0] [false, false]

#time def tailRows : List (List Int) :=
  [tailRows000]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [2316023, 90255, 1618683, 2571411, 1559813, 137805, 862473, 2618961, 527993, 182151, 1894293, 2938917, 139525, 1041739, 1226775, 4162807, 2890521, 863313, 3977771, 6067859, 3914891, 6570605, 2953401, 13501777, 18080471, 5576295, 17118981, 25648677, 21093461, 120810987, 14105991, 152035959]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [1967353, 1330833, 11025, 0]) [0, 0, 7, 0] [false, true, true, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [664843, 70251, 527093, 2675603, 416353, 40341, 775583, 2645693, 52051, 493429, 283717, 3179463, 246687, 510349, 317253, 4183241, 684603, 3038029, 1077783, 7731619, 3913861, 2947693, 4307041, 13717341, 2097713, 48611037, 1006369, 65276071, 13272007, 48201573, 26459039, 162088681]) [1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 2, 0, 2, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 3, 0, 3, 0, 2, 0] [false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [68875, 1372927, 33075, 0]) [1, 0, 5, 0] [false, false, true, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [163601, 25883, 195241, 352435, 99671, 29597, 131311, 356149, 23453, 8465, 254435, 209803, 78857, 59893, 199031, 346519, 613405, 227353, 733579, 1159963, 693247, 3632129, 653737, 5019445, 8037347, 890801, 7997837, 6107389, 8255039, 14001335, 7780145, 20113679]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 0, 1] [false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [179421, 189159, 4725, 0]) [0, 0, 5, 0] [false, true, true, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [18101, 5197, 31051, 292653, 8339, 2995, 40813, 290451, 149, 92643, 65097, 386089, 109023, 93831, 174269, 572563, 31091, 1301047, 9933, 1967441, 90047, 1293967, 368829, 4562455, 1463173, 17409569, 1452895, 11553147, 15923975, 17441845, 15934253, 46404561]) [2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 5, 0, 5, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0] [false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [6475, 148925, 1575, 0]) [2, 0, 6, 0] [true, false, true, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [184283, 124359, 456827, 929383, 75653, 130329, 348197, 935353, 293635, 137939, 717485, 1203621, 387045, 2073635, 624075, 3415195, 4627725, 2055497, 4864755, 7544327, 4757411, 24238903, 4735069, 14639079, 43590709, 24342237, 43613051, 63220219, 43254355, 101776083, 43949405, 14213627]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [320555, 526871, 4725, 0]) [0, 0, 6, 0] [false, true, true, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [32087, 45395, 899753, 4000147, 145783, 26285, 1077623, 3981037, 37171, 3878837, 463019, 7886159, 2163895, 3889213, 1239115, 15654209, 4468999, 38710619, 4815251, 19167197, 34100411, 38773435, 33754159, 96651251, 16948193, 136051325, 4244773, 626639, 25589741, 135764629, 51148583, 272442593]) [1, 0, 1, 0, 1, 0, 1, 0, 4, 0, 2, 0, 2, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 4, 0, 3, 0, 2, 0] [false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [433833, 2022771, 33075, 0]) [1, 0, 5, 0] [true, false, true, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [1483, 158073, 172773, 475689, 29413, 159543, 144843, 477159, 376429, 1292391, 491859, 6386007, 1601389, 11640169, 1871763, 3961771, 9943107, 2918481, 9672733, 3409483, 9813679, 8078423, 9802161, 103689, 22629441, 32119663, 22640959, 57797259, 11476449, 63356161, 11158751, 26560761]) [3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 3, 0, 1, 0, 1, 0, 1, 2, 1, 3, 1, 2, 1, 6, 1, 0, 1, 0, 2, 0, 2, 0] [false, false, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [85645, 316881, 11025, 0]) [3, 3, 6, 0] [true, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [2995303, 78495, 2297963, 3706531, 2027413, 149565, 1330073, 3777601, 760393, 284351, 2597093, 4211517, 62075, 1278339, 1898775, 5774207, 3192921, 1230113, 5153771, 8282659, 3987691, 7636285, 4359001, 17149057, 20055031, 7262175, 20426341, 32047517, 21598021, 128061027, 18883351, 167370719]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [2646633, 1892513, 11025, 11025]) [0, 0, 7, 7] [false, true, true, true]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007]

#time def graph : KernelGraph 3 1 2 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 0.6528 s provisional ×3 model; 1088 exact original rank units.
#time theorem checked : chart.check 36 3 basis.matrix = true := by decide +kernel
end C001

namespace C002
#time def pivTape : List (Fin 3) :=
  []

#time def freeTape : List (Fin 3) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 3) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩]

#time def roles : GraphRoles 3 0 3 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [2995303, 78495, 2297963, 3706531, 2027413, 149565, 1330073, 3777601, 760393, 284351, 2597093, 4211517, 62075, 1278339, 1898775, 5774207, 3192921, 1230113, 5153771, 8282659, 3987691, 7636285, 4359001, 17149057, 20055031, 7262175, 20426341, 32047517, 21598021, 128061027, 18883351, 167370719]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [2646633, 1892513, 11025, 11025]) [0, 0, 7, 7] [false, true, true, true]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows : List (List Int) :=
  [chartRows000]

#time def graph : KernelGraph 3 0 3 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 0.2970 s provisional ×3 model; 495 exact original rank units.
#time theorem checked : chart.check 36 3 basis.matrix = true := by decide +kernel
end C002

namespace C003
#time def pivTape : List (Fin 3) :=
  [⟨0, by decide⟩]

#time def freeTape : List (Fin 3) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩]

#time def roleTape : List (Fin 1 ⊕ Fin 2) :=
  [.inl ⟨0, by decide⟩, .inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩]

#time def roles : GraphRoles 3 1 2 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows : List (List Int) :=
  [tailRows000]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017]

#time def graph : KernelGraph 3 1 2 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 1.3008 s provisional ×3 model; 2168 exact original rank units.
#time theorem checked : chart.check 36 3 basis.matrix = true := by decide +kernel
end C003

namespace C004
#time def pivTape : List (Fin 3) :=
  [⟨0, by decide⟩]

#time def freeTape : List (Fin 3) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩]

#time def roleTape : List (Fin 1 ⊕ Fin 2) :=
  [.inl ⟨0, by decide⟩, .inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩]

#time def roles : GraphRoles 3 1 2 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows : List (List Int) :=
  [tailRows000]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009]

#time def graph : KernelGraph 3 1 2 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 0.7824 s provisional ×3 model; 1304 exact original rank units.
#time theorem checked : chart.check 36 3 basis.matrix = true := by decide +kernel
end C004

namespace C005
#time def pivTape : List (Fin 3) :=
  [⟨0, by decide⟩]

#time def freeTape : List (Fin 3) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩]

#time def roleTape : List (Fin 1 ⊕ Fin 2) :=
  [.inl ⟨0, by decide⟩, .inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩]

#time def roles : GraphRoles 3 1 2 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows : List (List Int) :=
  [tailRows000]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008]

#time def graph : KernelGraph 3 1 2 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 0.7176 s provisional ×3 model; 1196 exact original rank units.
#time theorem checked : chart.check 36 3 basis.matrix = true := by decide +kernel
end C005

namespace C006
#time def pivTape : List (Fin 3) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩]

#time def freeTape : List (Fin 3) :=
  [⟨0, by decide⟩]

#time def roleTape : List (Fin 2 ⊕ Fin 1) :=
  [.inr ⟨0, by decide⟩, .inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩]

#time def roles : GraphRoles 3 2 1 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [39889, 6909087, 75729, 3254625, 47239, 27807, 83079, 10191519, 1719041, 10363825, 2451135, 144499, 8437391, 10381533, 7705297, 20889857, 4106145, 20673523, 3965199, 10597867, 6343167, 20445739, 6484113, 30521395, 13139219, 31042469, 12515341, 19924665, 17450365, 32609833, 18074243, 43727637]) [6, 0, 6, 0, 6, 0, 6, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0] [false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [57809, 1827231, 11025, 0]) [6, 0, 7, 0] [false, false, false, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [278221, 25377, 119091, 702681, 177751, 11487, 219561, 688791, 1387, 147443, 65289, 847721, 73829, 130683, 91751, 1125847, 253401, 951543, 261261, 2208073, 1310687, 804951, 1318547, 3964567, 781511, 15922699, 266553, 20692217, 2217257, 14858851, 8620623, 51473767]) [1, 0, 1, 0, 1, 0, 1, 0, 7, 0, 2, 0, 2, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 3, 0, 4, 0, 2, 0] [false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [79565, 364029, 11025, 0]) [1, 0, 5, 0] [false, false, true, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [199991, 25253, 231631, 413245, 124721, 30227, 156361, 418219, 11003, 39335, 292085, 487781, 68057, 252247, 235031, 779363, 629605, 247003, 796579, 1278613, 697147, 3689219, 729037, 5214835, 8143127, 3653519, 8175017, 12557573, 8282069, 55616945, 8036075, 39405853]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [215811, 219249, 4725, 0]) [0, 0, 5, 0] [false, true, true, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [22953, 5533, 26199, 260221, 11679, 2659, 37473, 257347, 3469, 89723, 55057, 349729, 106143, 87071, 164669, 526523, 32171, 1290567, 8883, 1904161, 11, 1263519, 363809, 4458247, 1491381, 17457737, 1405647, 11735971, 15916767, 17648989, 16002501, 46842697]) [2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 5, 0, 18, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0] [false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [1623, 132877, 1575, 0]) [2, 0, 6, 0] [true, false, true, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [77601, 41173, 168449, 336821, 36351, 43723, 127199, 339371, 92345, 48413, 255895, 431507, 124215, 696845, 224025, 1176765, 1549775, 693899, 1649585, 2567509, 1587537, 8054261, 1611823, 4792853, 14483223, 8073939, 14458937, 20921053, 14406105, 34097981, 14536055, 5102989]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [123025, 188997, 1575, 0]) [0, 0, 6, 0] [false, true, true, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [14981, 6845, 118139, 536701, 13669, 3395, 146789, 533251, 9731, 550991, 60767, 1087637, 307585, 548359, 174445, 2186987, 643057, 5541317, 669893, 2805971, 4870373, 5571685, 4843537, 13918973, 2406059, 19384295, 153181, 106363, 457201, 19173007, 7270379, 38450939]) [1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 2, 0, 2, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 6, 0, 6, 0, 2, 0] [false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [51579, 271773, 4725, 0]) [1, 0, 5, 0] [true, false, true, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [36523, 631557, 733547, 1973701, 88427, 638907, 608597, 1981051, 1491191, 652583, 2011361, 3272541, 1588789, 5805297, 1913763, 1880173, 9924207, 5814037, 9599233, 13499507, 9809129, 16223451, 9714311, 3090093, 22752851, 16165199, 22847669, 29298557, 22984433, 31224953, 22616087, 14238803]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [385035, 1302629, 11025, 0]) [0, 0, 5, 0] [false, true, true, false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026]

#time def graph : KernelGraph 3 2 1 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 1.2318 s provisional ×3 model; 2053 exact original rank units.
#time theorem checked : chart.check 36 3 basis.matrix = true := by decide +kernel
end C006

namespace C007
#time def pivTape : List (Fin 3) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

#time def freeTape : List (Fin 3) :=
  []

#time def roleTape : List (Fin 3 ⊕ Fin 0) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩]

#time def roles : GraphRoles 3 3 0 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows001 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows002 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [39889, 6909087, 75729, 3254625, 47239, 27807, 83079, 10191519, 1719041, 10363825, 2451135, 144499, 8437391, 10381533, 7705297, 20889857, 4106145, 20673523, 3965199, 10597867, 6343167, 20445739, 6484113, 30521395, 13139219, 31042469, 12515341, 19924665, 17450365, 32609833, 18074243, 43727637]) [6, 0, 6, 0, 6, 0, 6, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0] [false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [57809, 1827231, 11025, 0]) [6, 0, 7, 0] [false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [278221, 25377, 119091, 702681, 177751, 11487, 219561, 688791, 1387, 147443, 65289, 847721, 73829, 130683, 91751, 1125847, 253401, 951543, 261261, 2208073, 1310687, 804951, 1318547, 3964567, 781511, 15922699, 266553, 20692217, 2217257, 14858851, 8620623, 51473767]) [1, 0, 1, 0, 1, 0, 1, 0, 7, 0, 2, 0, 2, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 3, 0, 4, 0, 2, 0] [false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [79565, 364029, 11025, 0]) [1, 0, 5, 0] [false, false, true, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [199991, 25253, 231631, 413245, 124721, 30227, 156361, 418219, 11003, 39335, 292085, 487781, 68057, 252247, 235031, 779363, 629605, 247003, 796579, 1278613, 697147, 3689219, 729037, 5214835, 8143127, 3653519, 8175017, 12557573, 8282069, 55616945, 8036075, 39405853]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [215811, 219249, 4725, 0]) [0, 0, 5, 0] [false, true, true, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [22953, 5533, 26199, 260221, 11679, 2659, 37473, 257347, 3469, 89723, 55057, 349729, 106143, 87071, 164669, 526523, 32171, 1290567, 8883, 1904161, 11, 1263519, 363809, 4458247, 1491381, 17457737, 1405647, 11735971, 15916767, 17648989, 16002501, 46842697]) [2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 5, 0, 18, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0] [false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [1623, 132877, 1575, 0]) [2, 0, 6, 0] [true, false, true, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [77601, 41173, 168449, 336821, 36351, 43723, 127199, 339371, 92345, 48413, 255895, 431507, 124215, 696845, 224025, 1176765, 1549775, 693899, 1649585, 2567509, 1587537, 8054261, 1611823, 4792853, 14483223, 8073939, 14458937, 20921053, 14406105, 34097981, 14536055, 5102989]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [123025, 188997, 1575, 0]) [0, 0, 6, 0] [false, true, true, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [14981, 6845, 118139, 536701, 13669, 3395, 146789, 533251, 9731, 550991, 60767, 1087637, 307585, 548359, 174445, 2186987, 643057, 5541317, 669893, 2805971, 4870373, 5571685, 4843537, 13918973, 2406059, 19384295, 153181, 106363, 457201, 19173007, 7270379, 38450939]) [1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 2, 0, 2, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 6, 0, 6, 0, 2, 0] [false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [51579, 271773, 4725, 0]) [1, 0, 5, 0] [true, false, true, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [36523, 631557, 733547, 1973701, 88427, 638907, 608597, 1981051, 1491191, 652583, 2011361, 3272541, 1588789, 5805297, 1913763, 1880173, 9924207, 5814037, 9599233, 13499507, 9809129, 16223451, 9714311, 3090093, 22752851, 16165199, 22847669, 29298557, 22984433, 31224953, 22616087, 14238803]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [385035, 1302629, 11025, 0]) [0, 0, 5, 0] [false, true, true, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017]

#time def graph : KernelGraph 3 3 0 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 0.3888 s provisional ×3 model; 648 exact original rank units.
#time theorem checked : chart.check 36 3 basis.matrix = true := by decide +kernel
end C007

namespace C008
#time def pivTape : List (Fin 3) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩]

#time def freeTape : List (Fin 3) :=
  [⟨0, by decide⟩]

#time def roleTape : List (Fin 2 ⊕ Fin 1) :=
  [.inr ⟨0, by decide⟩, .inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩]

#time def roles : GraphRoles 3 2 1 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [39889, 6909087, 75729, 3254625, 47239, 27807, 83079, 10191519, 1719041, 10363825, 2451135, 144499, 8437391, 10381533, 7705297, 20889857, 4106145, 20673523, 3965199, 10597867, 6343167, 20445739, 6484113, 30521395, 13139219, 31042469, 12515341, 19924665, 17450365, 32609833, 18074243, 43727637]) [6, 0, 6, 0, 6, 0, 6, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0] [false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [57809, 1827231, 11025, 0]) [6, 0, 7, 0] [false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [278221, 25377, 119091, 702681, 177751, 11487, 219561, 688791, 1387, 147443, 65289, 847721, 73829, 130683, 91751, 1125847, 253401, 951543, 261261, 2208073, 1310687, 804951, 1318547, 3964567, 781511, 15922699, 266553, 20692217, 2217257, 14858851, 8620623, 51473767]) [1, 0, 1, 0, 1, 0, 1, 0, 7, 0, 2, 0, 2, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 3, 0, 4, 0, 2, 0] [false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [79565, 364029, 11025, 0]) [1, 0, 5, 0] [false, false, true, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [199991, 25253, 231631, 413245, 124721, 30227, 156361, 418219, 11003, 39335, 292085, 487781, 68057, 252247, 235031, 779363, 629605, 247003, 796579, 1278613, 697147, 3689219, 729037, 5214835, 8143127, 3653519, 8175017, 12557573, 8282069, 55616945, 8036075, 39405853]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [215811, 219249, 4725, 0]) [0, 0, 5, 0] [false, true, true, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [22953, 5533, 26199, 260221, 11679, 2659, 37473, 257347, 3469, 89723, 55057, 349729, 106143, 87071, 164669, 526523, 32171, 1290567, 8883, 1904161, 11, 1263519, 363809, 4458247, 1491381, 17457737, 1405647, 11735971, 15916767, 17648989, 16002501, 46842697]) [2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 5, 0, 18, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0] [false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [1623, 132877, 1575, 0]) [2, 0, 6, 0] [true, false, true, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [77601, 41173, 168449, 336821, 36351, 43723, 127199, 339371, 92345, 48413, 255895, 431507, 124215, 696845, 224025, 1176765, 1549775, 693899, 1649585, 2567509, 1587537, 8054261, 1611823, 4792853, 14483223, 8073939, 14458937, 20921053, 14406105, 34097981, 14536055, 5102989]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [123025, 188997, 1575, 0]) [0, 0, 6, 0] [false, true, true, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [14981, 6845, 118139, 536701, 13669, 3395, 146789, 533251, 9731, 550991, 60767, 1087637, 307585, 548359, 174445, 2186987, 643057, 5541317, 669893, 2805971, 4870373, 5571685, 4843537, 13918973, 2406059, 19384295, 153181, 106363, 457201, 19173007, 7270379, 38450939]) [1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 2, 0, 2, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 6, 0, 6, 0, 2, 0] [false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [51579, 271773, 4725, 0]) [1, 0, 5, 0] [true, false, true, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [36523, 631557, 733547, 1973701, 88427, 638907, 608597, 1981051, 1491191, 652583, 2011361, 3272541, 1588789, 5805297, 1913763, 1880173, 9924207, 5814037, 9599233, 13499507, 9809129, 16223451, 9714311, 3090093, 22752851, 16165199, 22847669, 29298557, 22984433, 31224953, 22616087, 14238803]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [385035, 1302629, 11025, 0]) [0, 0, 5, 0] [false, true, true, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009]

#time def graph : KernelGraph 3 2 1 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 0.4974 s provisional ×3 model; 829 exact original rank units.
#time theorem checked : chart.check 36 3 basis.matrix = true := by decide +kernel
end C008

namespace C009
#time def pivTape : List (Fin 3) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩]

#time def freeTape : List (Fin 3) :=
  [⟨0, by decide⟩]

#time def roleTape : List (Fin 2 ⊕ Fin 1) :=
  [.inr ⟨0, by decide⟩, .inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩]

#time def roles : GraphRoles 3 2 1 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [39889, 6909087, 75729, 3254625, 47239, 27807, 83079, 10191519, 1719041, 10363825, 2451135, 144499, 8437391, 10381533, 7705297, 20889857, 4106145, 20673523, 3965199, 10597867, 6343167, 20445739, 6484113, 30521395, 13139219, 31042469, 12515341, 19924665, 17450365, 32609833, 18074243, 43727637]) [6, 0, 6, 0, 6, 0, 6, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0] [false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [57809, 1827231, 11025, 0]) [6, 0, 7, 0] [false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [278221, 25377, 119091, 702681, 177751, 11487, 219561, 688791, 1387, 147443, 65289, 847721, 73829, 130683, 91751, 1125847, 253401, 951543, 261261, 2208073, 1310687, 804951, 1318547, 3964567, 781511, 15922699, 266553, 20692217, 2217257, 14858851, 8620623, 51473767]) [1, 0, 1, 0, 1, 0, 1, 0, 7, 0, 2, 0, 2, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 3, 0, 4, 0, 2, 0] [false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [79565, 364029, 11025, 0]) [1, 0, 5, 0] [false, false, true, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [199991, 25253, 231631, 413245, 124721, 30227, 156361, 418219, 11003, 39335, 292085, 487781, 68057, 252247, 235031, 779363, 629605, 247003, 796579, 1278613, 697147, 3689219, 729037, 5214835, 8143127, 3653519, 8175017, 12557573, 8282069, 55616945, 8036075, 39405853]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [215811, 219249, 4725, 0]) [0, 0, 5, 0] [false, true, true, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [22953, 5533, 26199, 260221, 11679, 2659, 37473, 257347, 3469, 89723, 55057, 349729, 106143, 87071, 164669, 526523, 32171, 1290567, 8883, 1904161, 11, 1263519, 363809, 4458247, 1491381, 17457737, 1405647, 11735971, 15916767, 17648989, 16002501, 46842697]) [2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 5, 0, 18, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0] [false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [1623, 132877, 1575, 0]) [2, 0, 6, 0] [true, false, true, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [77601, 41173, 168449, 336821, 36351, 43723, 127199, 339371, 92345, 48413, 255895, 431507, 124215, 696845, 224025, 1176765, 1549775, 693899, 1649585, 2567509, 1587537, 8054261, 1611823, 4792853, 14483223, 8073939, 14458937, 20921053, 14406105, 34097981, 14536055, 5102989]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [123025, 188997, 1575, 0]) [0, 0, 6, 0] [false, true, true, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [14981, 6845, 118139, 536701, 13669, 3395, 146789, 533251, 9731, 550991, 60767, 1087637, 307585, 548359, 174445, 2186987, 643057, 5541317, 669893, 2805971, 4870373, 5571685, 4843537, 13918973, 2406059, 19384295, 153181, 106363, 457201, 19173007, 7270379, 38450939]) [1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 2, 0, 2, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 6, 0, 6, 0, 2, 0] [false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [51579, 271773, 4725, 0]) [1, 0, 5, 0] [true, false, true, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [36523, 631557, 733547, 1973701, 88427, 638907, 608597, 1981051, 1491191, 652583, 2011361, 3272541, 1588789, 5805297, 1913763, 1880173, 9924207, 5814037, 9599233, 13499507, 9809129, 16223451, 9714311, 3090093, 22752851, 16165199, 22847669, 29298557, 22984433, 31224953, 22616087, 14238803]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [385035, 1302629, 11025, 0]) [0, 0, 5, 0] [false, true, true, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008]

#time def graph : KernelGraph 3 2 1 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 0.4542 s provisional ×3 model; 757 exact original rank units.
#time theorem checked : chart.check 36 3 basis.matrix = true := by decide +kernel
end C009

namespace C010
#time def pivTape : List (Fin 3) :=
  [⟨1, by decide⟩]

#time def freeTape : List (Fin 3) :=
  [⟨0, by decide⟩, ⟨2, by decide⟩]

#time def roleTape : List (Fin 1 ⊕ Fin 2) :=
  [.inr ⟨0, by decide⟩, .inl ⟨0, by decide⟩, .inr ⟨1, by decide⟩]

#time def roles : GraphRoles 3 1 2 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [290349618006685565299990790569463459]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 58030396057546166487890233501435897]) [0, 1] [false, false]

#time def tailRows : List (List Int) :=
  [tailRows000]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [278221, 25377, 119091, 702681, 177751, 11487, 219561, 688791, 1387, 147443, 65289, 847721, 73829, 130683, 91751, 1125847, 253401, 951543, 261261, 2208073, 1310687, 804951, 1318547, 3964567, 781511, 15922699, 266553, 20692217, 2217257, 14858851, 8620623, 51473767]) [1, 0, 1, 0, 1, 0, 1, 0, 7, 0, 2, 0, 2, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 3, 0, 4, 0, 2, 0] [false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [79565, 364029, 11025, 0]) [1, 0, 5, 0] [false, false, true, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [199991, 25253, 231631, 413245, 124721, 30227, 156361, 418219, 11003, 39335, 292085, 487781, 68057, 252247, 235031, 779363, 629605, 247003, 796579, 1278613, 697147, 3689219, 729037, 5214835, 8143127, 3653519, 8175017, 12557573, 8282069, 55616945, 8036075, 39405853]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [215811, 219249, 4725, 0]) [0, 0, 5, 0] [false, true, true, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [22953, 5533, 26199, 260221, 11679, 2659, 37473, 257347, 3469, 89723, 55057, 349729, 106143, 87071, 164669, 526523, 32171, 1290567, 8883, 1904161, 11, 1263519, 363809, 4458247, 1491381, 17457737, 1405647, 11735971, 15916767, 17648989, 16002501, 46842697]) [2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 5, 0, 18, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0] [false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [1623, 132877, 1575, 0]) [2, 0, 6, 0] [true, false, true, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [77601, 41173, 168449, 336821, 36351, 43723, 127199, 339371, 92345, 48413, 255895, 431507, 124215, 696845, 224025, 1176765, 1549775, 693899, 1649585, 2567509, 1587537, 8054261, 1611823, 4792853, 14483223, 8073939, 14458937, 20921053, 14406105, 34097981, 14536055, 5102989]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [123025, 188997, 1575, 0]) [0, 0, 6, 0] [false, true, true, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [14981, 6845, 118139, 536701, 13669, 3395, 146789, 533251, 9731, 550991, 60767, 1087637, 307585, 548359, 174445, 2186987, 643057, 5541317, 669893, 2805971, 4870373, 5571685, 4843537, 13918973, 2406059, 19384295, 153181, 106363, 457201, 19173007, 7270379, 38450939]) [1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 2, 0, 2, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 6, 0, 6, 0, 2, 0] [false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [51579, 271773, 4725, 0]) [1, 0, 5, 0] [true, false, true, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [36523, 631557, 733547, 1973701, 88427, 638907, 608597, 1981051, 1491191, 652583, 2011361, 3272541, 1588789, 5805297, 1913763, 1880173, 9924207, 5814037, 9599233, 13499507, 9809129, 16223451, 9714311, 3090093, 22752851, 16165199, 22847669, 29298557, 22984433, 31224953, 22616087, 14238803]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [385035, 1302629, 11025, 0]) [0, 0, 5, 0] [false, true, true, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006]

#time def graph : KernelGraph 3 1 2 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 0.5880 s provisional ×3 model; 980 exact original rank units.
#time theorem checked : chart.check 36 3 basis.matrix = true := by decide +kernel
end C010

#time def delta : Int := signedLit (wordMag (raw_ints% [242389191203401, 114728141531882, 271774695080179, 56267459393958, 277710339973174, 96313776542450, 5888149914050, 248673984519837, 180100804375894, 19300197358124, 280791])) 7 false
#time def adj000 : Int := signedLit (wordMag (raw_ints% [132579621795131, 33055863009274, 22164781032554, 33206535620310, 136564796622487, 260302275754352, 7236074572282, 920475078825])) 6 false
#time def adj001 : Int := signedLit (wordMag (raw_ints% [127321655002925, 161106517043186, 161650015090073, 199608027107832, 159378361584478, 40051137568850, 77016877371322, 224162630264])) 5 false
#time def adj002 : Int := signedLit (wordMag (raw_ints% [100489988298119, 201844574418903, 203475068559564, 35874127902185, 196660108042780, 120153412706551, 231050632113966, 672487890792])) 5 false
def pivots : List (Fin 36) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨5, by decide⟩]
def adjTape : List Int := [adj000, adj001, adj002]
def head : DiagHead 3 36 := ⟨fun i => pivots.getD i.val ⟨0, by decide⟩,
  fun i => adjTape.getD i.val 0, delta⟩
def input : PackedPacketInput := ⟨36, 3, basis, head, []⟩
#time def packet : Packet := { input.packet with charts := [C000.chart, C001.chart, C002.chart, C003.chart, C004.chart, C005.chart, C006.chart, C007.chart, C008.chart, C009.chart, C010.chart] }
-- kcost: 0.0162 s provisional ×3 model; 27 original head product units.
#time theorem headChecked : packet.checkHead = true := by decide +kernel
#time theorem checked : packet.check = true := by
  apply Packet.check_of_parts headChecked
  intro c hc
  change c ∈ [C000.chart, C001.chart, C002.chart, C003.chart, C004.chart, C005.chart, C006.chart, C007.chart, C008.chart, C009.chart, C010.chart] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact C000.checked
  · exact C001.checked
  · exact C002.checked
  · exact C003.checked
  · exact C004.checked
  · exact C005.checked
  · exact C006.checked
  · exact C007.checked
  · exact C008.checked
  · exact C009.checked
  · exact C010.checked
#time theorem sound : packet.Sound := Packet.check_sound checked
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P042

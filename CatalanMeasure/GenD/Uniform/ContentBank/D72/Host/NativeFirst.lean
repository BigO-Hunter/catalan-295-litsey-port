module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.ResponseRow
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.NativeFirst
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + 2 ^ (48 : Nat) * wordMag as
def value (ws : List Int) (e : Nat) (neg : Bool) : Int :=
  if neg then -(wordMag ws * 2 ^ e) else wordMag ws * 2 ^ e

def K : Nat := 110
theorem hK : K = 27 * 4 + 2 + 0 := by decide
def slotsTape : List (Option (Fin K)) := [some ⟨0, by decide⟩, some ⟨1, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩, some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩, some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩, some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩, some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩, some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩, some ⟨23, by decide⟩, some ⟨24, by decide⟩, some ⟨25, by decide⟩, some ⟨26, by decide⟩, some ⟨27, by decide⟩, some ⟨28, by decide⟩, some ⟨29, by decide⟩, some ⟨30, by decide⟩, some ⟨31, by decide⟩, some ⟨32, by decide⟩, some ⟨33, by decide⟩, some ⟨34, by decide⟩, some ⟨35, by decide⟩, some ⟨36, by decide⟩, some ⟨37, by decide⟩, some ⟨38, by decide⟩, some ⟨39, by decide⟩, some ⟨40, by decide⟩, some ⟨41, by decide⟩, some ⟨42, by decide⟩, some ⟨43, by decide⟩, some ⟨44, by decide⟩, some ⟨45, by decide⟩, some ⟨46, by decide⟩, some ⟨47, by decide⟩, some ⟨48, by decide⟩, some ⟨49, by decide⟩, some ⟨50, by decide⟩, some ⟨51, by decide⟩, some ⟨52, by decide⟩, some ⟨53, by decide⟩, some ⟨54, by decide⟩, some ⟨55, by decide⟩, some ⟨56, by decide⟩, some ⟨57, by decide⟩, some ⟨58, by decide⟩, some ⟨59, by decide⟩, some ⟨60, by decide⟩, some ⟨61, by decide⟩, some ⟨62, by decide⟩, some ⟨63, by decide⟩, some ⟨64, by decide⟩, some ⟨65, by decide⟩, some ⟨66, by decide⟩, some ⟨67, by decide⟩, some ⟨68, by decide⟩, some ⟨69, by decide⟩, some ⟨70, by decide⟩, some ⟨71, by decide⟩, some ⟨72, by decide⟩, some ⟨73, by decide⟩, some ⟨74, by decide⟩, some ⟨75, by decide⟩, some ⟨76, by decide⟩, some ⟨77, by decide⟩, some ⟨78, by decide⟩, some ⟨79, by decide⟩, some ⟨80, by decide⟩, some ⟨81, by decide⟩, some ⟨82, by decide⟩, some ⟨83, by decide⟩, some ⟨84, by decide⟩, some ⟨85, by decide⟩, some ⟨86, by decide⟩, some ⟨87, by decide⟩, some ⟨88, by decide⟩, some ⟨89, by decide⟩, some ⟨90, by decide⟩, some ⟨91, by decide⟩, some ⟨92, by decide⟩, some ⟨93, by decide⟩, some ⟨94, by decide⟩, some ⟨95, by decide⟩, some ⟨96, by decide⟩, some ⟨97, by decide⟩, some ⟨98, by decide⟩, some ⟨99, by decide⟩, some ⟨100, by decide⟩, some ⟨101, by decide⟩, some ⟨102, by decide⟩, some ⟨103, by decide⟩, some ⟨104, by decide⟩, some ⟨105, by decide⟩, some ⟨106, by decide⟩, some ⟨107, by decide⟩, some ⟨108, by decide⟩, some ⟨109, by decide⟩, none, none]
def slots (i : Fin 112) : Option (Fin K) := slotsTape.getD i.val none

#time def x000 : Int := value (raw_ints% [143800496445097, 47548825827569, 18421]) 36 true
#time def x001 : Int := value (raw_ints% [145961119721387, 30288214220831, 214998]) 30 true
#time def x002 : Int := value (raw_ints% [11761232975489, 167171245516200, 641493]) 32 false
#time def x003 : Int := value (raw_ints% [89982773019169, 134077194589721, 3529970]) 30 true
#time def x004 : Int := value (raw_ints% [197003340040191, 95419879009961, 52006]) 32 false
#time def x005 : Int := value (raw_ints% [62747132318927, 33375532008256, 832185]) 30 true
#time def x006 : Int := value (raw_ints% [23612370104825, 77697541698547, 147374]) 33 true
#time def x007 : Int := value (raw_ints% [173196760421629, 130989876802296, 2912783]) 30 false
#time def x008 : Int := value (raw_ints% [21142443417523, 100458426460777, 34682]) 31 true
#time def x009 : Int := value (raw_ints% [121504083177559, 100156670435747, 138697]) 30 false
#time def x010 : Int := value (raw_ints% [242250310342707, 19491982313487, 450802]) 31 false
#time def x011 : Int := value (raw_ints% [270420521635799, 278932651068948, 1941900]) 30 true
#time def x012 : Int := value (raw_ints% [33312507027213, 10124963795074, 34680]) 31 true
#time def x013 : Int := value (raw_ints% [272168859568809, 160660058326572, 138697]) 30 false
#time def x014 : Int := value (raw_ints% [254420373952397, 210633496358440, 450799]) 31 true
#time def x015 : Int := value (raw_ints% [139610321316393, 57961062249118, 1941901]) 30 false
#time def x016 : Int := value (raw_ints% [254080632821281, 261171766953928, 52009]) 32 false
#time def x017 : Int := value (raw_ints% [47490710474033, 124149957012386, 832184]) 30 true
#time def x018 : Int := value (raw_ints% [58236048300215, 256144242693007, 147374]) 33 false
#time def x019 : Int := value (raw_ints% [177794914648579, 61296100877421, 2912783]) 30 true
#time def x020 : Int := value (raw_ints% [250157966465709, 217207414790623, 18420]) 36 true
#time def x021 : Int := value (raw_ints% [144674746844075, 102983465360879, 2773942]) 30 false
#time def x022 : Int := value (raw_ints% [150955542213215, 26654238330085, 641492]) 32 true
#time def x023 : Int := value (raw_ints% [88485395256031, 6954546540031, 6518910]) 30 false
#time def x024 : Int := value (raw_ints% [233427253324841, 34589197096548, 1490993]) 31 false
#time def x025 : Int := value (raw_ints% [258033936502517, 20241145207770, 1525656]) 30 false
#time def x026 : Int := value (raw_ints% [96143963334279, 1660529290284, 3363442]) 31 false
#time def x027 : Int := value (raw_ints% [256601182308245, 89696866693139, 7767196]) 30 true
#time def x028 : Int := value (raw_ints% [4219092024551, 3182394934433, 5097107]) 31 false
#time def x029 : Int := value (raw_ints% [155715407570153, 54996777871095, 27878047]) 30 true
#time def x030 : Int := value (raw_ints% [237597828786743, 248407645258255, 242671]) 31 false
#time def x031 : Int := value (raw_ints% [157148161764425, 267016033096382, 21636506]) 30 true
#time def x032 : Int := value (raw_ints% [165544863389137, 161542784630022, 4793706]) 33 true
#time def x033 : Int := value (raw_ints% [163957920733817, 149897749443081, 31068069]) 30 false
#time def x034 : Int := value (raw_ints% [170523210473265, 167405612645733, 12257302]) 32 true
#time def x035 : Int := value (raw_ints% [195346513357739, 190435583699903, 80582623]) 30 false
#time def x036 : Int := value (raw_ints% [19360085780603, 9863507844454, 6189345]) 32 true
#time def x037 : Int := value (raw_ints% [23382421074325, 232693046755799, 95146046]) 30 false
#time def x038 : Int := value (raw_ints% [165834722700363, 95262831346497, 1956921]) 35 false
#time def x039 : Int := value (raw_ints% [54447036306575, 107640286387186, 16504646]) 30 true
#time def x040 : Int := value (raw_ints% [45171578087149, 276460200476761, 89563492]) 31 false
#time def x041 : Int := value (raw_ints% [15422581348957, 275660663118834, 183495929]) 30 true
#time def x042 : Int := value (raw_ints% [245285953549107, 179356798174987, 70631441]) 31 false
#time def x043 : Int := value (raw_ints% [265832942827363, 119238446776790, 262137330]) 30 true
#time def x044 : Int := value (raw_ints% [113640746386547, 15511776812940, 8009746]) 31 false
#time def x045 : Int := value (raw_ints% [163346115361867, 257006197858629, 206796899]) 30 true
#time def x046 : Int := value (raw_ints% [176816785249709, 158830245128152, 152185188]) 31 true
#time def x047 : Int := value (raw_ints% [117909408814453, 137892912036995, 238836360]) 30 false
#time def x048 : Int := value (raw_ints% [272093077048617, 110483933999426, 140170450]) 32 true
#time def x049 : Int := value (raw_ints% [205875481925491, 66876199959101, 613317261]) 30 false
#time def x050 : Int := value (raw_ints% [60126264404259, 80074919138119, 17020682]) 34 true
#time def x051 : Int := value (raw_ints% [251312188472905, 185989485780735, 581277800]) 30 false
#time def x052 : Int := value (raw_ints% [102809327724439, 113463404320105, 11156428]) 33 false
#time def x053 : Int := value (raw_ints% [172441621840911, 98382657549500, 329543779]) 30 false
#time def x054 : Int := value (raw_ints% [155266836693219, 94760465770802, 230566036]) 32 false
#time def x055 : Int := value (raw_ints% [3271071846829, 154483028190337, 865051282]) 30 true
#time def x056 : Int := value (raw_ints% [131727514180377, 101157853266573, 699136107]) 31 false
#time def x057 : Int := value (raw_ints% [260547426641471, 146657353996232, 1566858160]) 30 true
#time def x058 : Int := value (raw_ints% [254381460028151, 20733257865858, 193378321]) 31 false
#time def x059 : Int := value (raw_ints% [148242999924897, 90556983355396, 1031350657]) 30 true
#time def x060 : Int := value (raw_ints% [126854732467817, 116720288032851, 213211659]) 31 true
#time def x061 : Int := value (raw_ints% [212675132060829, 187934058664882, 376838923]) 30 true
#time def x062 : Int := value (raw_ints% [231488729965689, 238611399165283, 1105726087]) 31 true
#time def x063 : Int := value (raw_ints% [196115294505539, 49280278686746, 2221369894]) 30 false
#time def x064 : Int := value (raw_ints% [250685874341265, 206054049354972, 187799793]) 34 true
#time def x065 : Int := value (raw_ints% [276910299965789, 65505811415915, 3396962054]) 30 false
#time def x066 : Int := value (raw_ints% [260621812726995, 83600400399511, 91730301]) 32 true
#time def x067 : Int := value (raw_ints% [11995160810423, 204159591394052, 1552431083]) 30 false
#time def x068 : Int := value (raw_ints% [166720358461275, 272268003503864, 302688506]) 32 false
#time def x069 : Int := value (raw_ints% [179511309011129, 90500371876603, 191125171]) 30 false
#time def x070 : Int := value (raw_ints% [11355392500025, 167829835595650, 572808991]) 33 false
#time def x071 : Int := value (raw_ints% [109394151765083, 179165030933364, 4758267966]) 30 true
#time def x072 : Int := value (raw_ints% [37129970479789, 13255013625285, 2904277549]) 31 false
#time def x073 : Int := value (raw_ints% [160120306398161, 125055333799425, 6580749402]) 30 true
#time def x074 : Int := value (raw_ints% [221217636978451, 204774547788235, 7664568]) 31 false
#time def x075 : Int := value (raw_ints% [230237463644207, 36390674742664, 2013606607]) 30 true
#time def x076 : Int := value (raw_ints% [137826105650477, 80131360135272, 1377571318]) 31 true
#time def x077 : Int := value (raw_ints% [146207248020865, 150070769731906, 473930116]) 30 false
#time def x078 : Int := value (raw_ints% [114698736398061, 16685944838137, 4289513436]) 31 true
#time def x079 : Int := value (raw_ints% [255090041352577, 30041801563340, 9068286126]) 30 false
#time def x080 : Int := value (raw_ints% [224024955235267, 152460970437289, 2592745034]) 32 true
#time def x081 : Int := value (raw_ints% [63369754253655, 242460927981460, 11737352521]) 30 false
#time def x082 : Int := value (raw_ints% [162224965427493, 88711329380035, 120398671]) 33 false
#time def x083 : Int := value (raw_ints% [225022418301525, 62348356686212, 2195136279]) 30 false
#time def x084 : Int := value (raw_ints% [194611981581039, 210384155417770, 342992962]) 34 false
#time def x085 : Int := value (raw_ints% [217408742351437, 261995553824888, 1971147622]) 30 true
#time def x086 : Int := value (raw_ints% [115072997283125, 253624979926989, 3723919542]) 32 false
#time def x087 : Int := value (raw_ints% [224325938195961, 3854885071249, 15903636424]) 30 true
#time def x088 : Int := value (raw_ints% [248208129598505, 31373153206149, 8702229850]) 31 false
#time def x089 : Int := value (raw_ints% [65641230031027, 114776139906772, 19645729120]) 30 true
#time def x090 : Int := value (raw_ints% [131458834062777, 188625213015402, 1489552937]) 31 true
#time def x091 : Int := value (raw_ints% [186856502904941, 130400677721289, 1770945073]) 30 true
#time def x092 : Int := value (raw_ints% [220916639705, 46253216572702, 4985213122]) 31 true
#time def x093 : Int := value (raw_ints% [50533488906223, 49520382784713, 4777741011]) 30 false
#time def x094 : Int := value (raw_ints% [116970212175433, 170476133474105, 12197890034]) 31 true
#time def x095 : Int := value (raw_ints% [21556245131535, 13222223702119, 26194415205]) 30 false
#time def x096 : Int := value (raw_ints% [49529118492923, 229696033424702, 3473728770]) 33 true
#time def x097 : Int := value (raw_ints% [18113070926849, 124984079647188, 31262179082]) 30 false
#time def x098 : Int := value (raw_ints% [100274815777051, 211922561595311, 1644094036]) 32 false
#time def x099 : Int := value (raw_ints% [227498313599747, 62241473160355, 290022866]) 30 false
#time def x100 : Int := value (raw_ints% [92525496522241, 11259444543104, 4228781019]) 32 false
#time def x101 : Int := value (raw_ints% [217356582042723, 98590437843349, 9512380601]) 30 true
#time def x102 : Int := value (raw_ints% [93195973610423, 275788469982291, 2383036130]) 34 false
#time def x103 : Int := value (raw_ints% [181492989858663, 4341013940237, 41064582550]) 30 true
#time def x104 : Int := value (raw_ints% [69386901307277, 20806543895908, 21297658558]) 31 false
#time def x105 : Int := value (raw_ints% [186312474841861, 247313367627343, 47739234840]) 30 true
#time def x106 : Int := value (raw_ints% [16806950488621, 237695268074039, 6224192527]) 31 true
#time def x107 : Int := value (raw_ints% [212537097059525, 137093060866899, 2837728310]) 30 false
#time def x108 : Int := value (raw_ints% [60769362411793, 83527528625344, 936232]) 31 true
#time def x109 : Int := value (raw_ints% [253485803359547, 51894490184444, 1657486]) 30 false
#time def x110 : Int := value (raw_ints% [164783533433697, 137911993329342, 591]) 38 true

#time def target : List Int := [x000, x001, x002, x003, x004, x005, x006, x007, x008, x009, x010, x011, x012, x013, x014, x015, x016, x017, x018, x019, x020, x021, x022, x023, x024, x025, x026, x027, x028, x029, x030, x031, x032, x033, x034, x035, x036, x037, x038, x039, x040, x041, x042, x043, x044, x045, x046, x047, x048, x049, x050, x051, x052, x053, x054, x055, x056, x057, x058, x059, x060, x061, x062, x063, x064, x065, x066, x067, x068, x069, x070, x071, x072, x073, x074, x075, x076, x077, x078, x079, x080, x081, x082, x083, x084, x085, x086, x087, x088, x089, x090, x091, x092, x093, x094, x095, x096, x097, x098, x099, x100, x101, x102, x103, x104, x105, x106, x107, x108, x109, x110, 0]

-- kcost: 1.344 s provisional; 112 exact ambient coordinates.
#time theorem checked : foldedTargetCheck (b := 27) (ex := 0) hK (-3) 1 1
    slots 29 34 ⟨110, by decide⟩ none target = true := by
  decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.NativeFirst

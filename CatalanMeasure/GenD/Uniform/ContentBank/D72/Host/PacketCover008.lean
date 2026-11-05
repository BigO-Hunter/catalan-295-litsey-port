module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain008
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PhysicalGate
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostLowGraph
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover008
open CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008 (packet low value target)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain008 (jetLayout)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine001.P008 (win cert)

def gate : PhysicalGate72 := ⟨0, -1, 10, 1, 13, 14⟩
-- kcost: 0.100 s conservative; twelve affine quotient gates.
#time theorem gateCheck : gate.check win cert = true := by decide +kernel

#time def lowZones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨13, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -1, -1⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.250 s provisional; actual low-coordinate prefix and row checks.
#time theorem lowCheck : lowPrefixCheck jetLayout win cert ⟨-4, 2, 1⟩ low lowZones = true := by
  decide +kernel

#time def c000_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -26, -13⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨0, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 29 false)⟩]⟩⟩,
]
def c000_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨86, -26, -13⟩, c000_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c000_0Check : c000_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base000) = true := by decide +kernel

#time def c001_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -26, -13⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 29 true)⟩]⟩⟩,
  ⟨⟨86, -26, -13⟩, ⟨97, -28, -14⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨0, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 29 true)⟩]⟩⟩,
]
def c001_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -28, -14⟩, c001_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c001_0Check : c001_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base001) = true := by decide +kernel

#time def c002_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -26, -13⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 31 false)⟩]⟩⟩,
  ⟨⟨86, -26, -13⟩, ⟨97, -28, -14⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 31 false)⟩]⟩⟩,
]
def c002_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -28, -14⟩, c002_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c002_0Check : c002_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base002) = true := by decide +kernel

#time def c003_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -26, -13⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 31 true)⟩]⟩⟩,
  ⟨⟨86, -26, -13⟩, ⟨97, -28, -14⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 31 true)⟩]⟩⟩,
]
def c003_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -28, -14⟩, c003_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c003_0Check : c003_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base003) = true := by decide +kernel

#time def c004_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -26, -13⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 31 false)⟩]⟩⟩,
  ⟨⟨86, -26, -13⟩, ⟨97, -28, -14⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 31 false)⟩]⟩⟩,
]
def c004_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -28, -14⟩, c004_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c004_0Check : c004_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base004) = true := by decide +kernel

#time def c005_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -26, -13⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [212827307226293, 35200698397]) 31 true)⟩]⟩⟩,
  ⟨⟨86, -26, -13⟩, ⟨97, -28, -14⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [212827307226293, 35200698397]) 31 true)⟩]⟩⟩,
]
def c005_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -28, -14⟩, c005_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c005_0Check : c005_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base005) = true := by decide +kernel

#time def c006_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -26, -13⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [212827307226293, 35200698397]) 33 false)⟩]⟩⟩,
  ⟨⟨86, -26, -13⟩, ⟨97, -28, -14⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [212827307226293, 35200698397]) 33 false)⟩]⟩⟩,
]
def c006_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -28, -14⟩, c006_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c006_0Check : c006_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base006) = true := by decide +kernel

#time def c007_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -26, -13⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [212827307226293, 35200698397]) 34 true)⟩]⟩⟩,
  ⟨⟨86, -26, -13⟩, ⟨97, -28, -14⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [212827307226293, 35200698397]) 34 true)⟩]⟩⟩,
]
def c007_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -28, -14⟩, c007_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c007_0Check : c007_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base007) = true := by decide +kernel

#time def c008_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -26, -13⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 33 false)⟩]⟩⟩,
  ⟨⟨86, -26, -13⟩, ⟨97, -28, -14⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 33 false)⟩]⟩⟩,
]
def c008_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -28, -14⟩, c008_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c008_0Check : c008_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base008) = true := by decide +kernel

#time def c009_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -26, -13⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 33 true)⟩]⟩⟩,
  ⟨⟨86, -26, -13⟩, ⟨97, -28, -14⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 33 true)⟩]⟩⟩,
]
def c009_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -28, -14⟩, c009_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c009_0Check : c009_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base009) = true := by decide +kernel

#time def c010_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -26, -13⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨10, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 33 false)⟩]⟩⟩,
  ⟨⟨86, -26, -13⟩, ⟨97, -28, -14⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 33 false)⟩]⟩⟩,
]
def c010_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -28, -14⟩, c010_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c010_0Check : c010_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base010) = true := by decide +kernel

#time def c011_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -26, -13⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨11, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 32 true)⟩]⟩⟩,
  ⟨⟨86, -26, -13⟩, ⟨97, -28, -14⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨10, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 32 true)⟩]⟩⟩,
]
def c011_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -28, -14⟩, c011_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c011_0Check : c011_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base011) = true := by decide +kernel

#time def c012_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -26, -13⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨12, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 31 true)⟩]⟩⟩,
  ⟨⟨86, -26, -13⟩, ⟨97, -28, -14⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨11, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 31 true)⟩]⟩⟩,
]
def c012_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -28, -14⟩, c012_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c012_0Check : c012_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base012) = true := by decide +kernel

#time def c012_1Zones : List (ResponseZone packet) := [
  ⟨⟨10, -2, -1⟩, ⟨4, 0, -1⟩, ⟨1, [⟨⟨11, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, 0, -1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨13, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, 0, 0⟩, ⟨70, -20, -11⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨26, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨70, -20, -11⟩, ⟨97, -28, -14⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨27, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨39, by decide⟩, 1⟩]⟩⟩,
]
def c012_1 : ResponseComponent packet := ⟨⟨10, -2, -1⟩, ⟨0, 2, 1⟩, c012_1Zones⟩
-- kcost: 0.600 s provisional; 5 affine activation and row checks.
#time theorem c012_1Check : c012_1.check jetLayout win cert (unitTarget (n := packet.n) ⟨38, by decide⟩) = true := by decide +kernel

#time def c013_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨0, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 29 true)⟩]⟩⟩,
]
def c013_0 : ResponseComponent packet := ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, c013_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c013_0Check : c013_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base013) = true := by decide +kernel

#time def c014_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 31 false)⟩]⟩⟩,
]
def c014_0 : ResponseComponent packet := ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, c014_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c014_0Check : c014_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base014) = true := by decide +kernel

#time def c015_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 31 true)⟩]⟩⟩,
]
def c015_0 : ResponseComponent packet := ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, c015_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c015_0Check : c015_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base015) = true := by decide +kernel

#time def c016_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 31 false)⟩]⟩⟩,
]
def c016_0 : ResponseComponent packet := ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, c016_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c016_0Check : c016_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base016) = true := by decide +kernel

#time def c017_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [212827307226293, 35200698397]) 31 true)⟩]⟩⟩,
]
def c017_0 : ResponseComponent packet := ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, c017_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c017_0Check : c017_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base017) = true := by decide +kernel

#time def c018_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [212827307226293, 35200698397]) 33 false)⟩]⟩⟩,
]
def c018_0 : ResponseComponent packet := ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, c018_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c018_0Check : c018_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base018) = true := by decide +kernel

#time def c019_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [212827307226293, 35200698397]) 33 true)⟩]⟩⟩,
]
def c019_0 : ResponseComponent packet := ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, c019_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c019_0Check : c019_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base019) = true := by decide +kernel

#time def c020_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [212827307226293, 35200698397]) 33 false)⟩]⟩⟩,
]
def c020_0 : ResponseComponent packet := ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, c020_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c020_0Check : c020_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base020) = true := by decide +kernel

#time def c021_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 33 true)⟩]⟩⟩,
]
def c021_0 : ResponseComponent packet := ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, c021_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c021_0Check : c021_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base021) = true := by decide +kernel

#time def c022_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 33 false)⟩]⟩⟩,
]
def c022_0 : ResponseComponent packet := ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, c022_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c022_0Check : c022_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base022) = true := by decide +kernel

#time def c023_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨10, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 32 true)⟩]⟩⟩,
]
def c023_0 : ResponseComponent packet := ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, c023_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c023_0Check : c023_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base023) = true := by decide +kernel

#time def c024_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨11, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 31 true)⟩]⟩⟩,
]
def c024_0 : ResponseComponent packet := ⟨⟨97, -28, -14⟩, ⟨0, 2, 1⟩, c024_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c024_0Check : c024_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource008.base024) = true := by decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover008

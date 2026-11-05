module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain016
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PhysicalGate
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostLowGraph
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover016
open CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016 (packet low value target)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain016 (jetLayout)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine002.P016 (win cert)

def gate : PhysicalGate72 := ⟨0, -1, 8, 1, 11, 12⟩
-- kcost: 0.100 s conservative; twelve affine quotient gates.
#time theorem gateCheck : gate.check win cert = true := by decide +kernel

#time def lowZones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨11, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -1, -1⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.250 s provisional; actual low-coordinate prefix and row checks.
#time theorem lowCheck : lowPrefixCheck jetLayout win cert ⟨-4, 2, 1⟩ low lowZones = true := by
  decide +kernel

#time def c000_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -22, -11⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨0, by decide⟩, (value (raw_ints% [15604702432017, 13866941793]) 31 false)⟩]⟩⟩,
]
def c000_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨86, -22, -11⟩, c000_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c000_0Check : c000_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base000) = true := by decide +kernel

#time def c001_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -22, -11⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [171651726752187, 152536359723]) 31 true)⟩]⟩⟩,
  ⟨⟨86, -22, -11⟩, ⟨97, -24, -12⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨0, by decide⟩, (value (raw_ints% [171651726752187, 152536359723]) 31 true)⟩]⟩⟩,
]
def c001_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -24, -12⟩, c001_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c001_0Check : c001_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base001) = true := by decide +kernel

#time def c002_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -22, -11⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [171651726752187, 152536359723]) 31 false)⟩]⟩⟩,
  ⟨⟨86, -22, -11⟩, ⟨97, -24, -12⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [171651726752187, 152536359723]) 31 false)⟩]⟩⟩,
]
def c002_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -24, -12⟩, c002_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c002_0Check : c002_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base002) = true := by decide +kernel

#time def c003_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -22, -11⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [233480203545905, 457609079170]) 31 true)⟩]⟩⟩,
  ⟨⟨86, -22, -11⟩, ⟨97, -24, -12⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [233480203545905, 457609079170]) 31 true)⟩]⟩⟩,
]
def c003_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -24, -12⟩, c003_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c003_0Check : c003_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base003) = true := by decide +kernel

#time def c004_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -22, -11⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [233480203545905, 457609079170]) 33 false)⟩]⟩⟩,
  ⟨⟨86, -22, -11⟩, ⟨97, -24, -12⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [233480203545905, 457609079170]) 33 false)⟩]⟩⟩,
]
def c004_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -24, -12⟩, c004_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c004_0Check : c004_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base004) = true := by decide +kernel

#time def c005_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -22, -11⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [226986541268055, 3203263554195]) 33 true)⟩]⟩⟩,
  ⟨⟨86, -22, -11⟩, ⟨97, -24, -12⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [226986541268055, 3203263554195]) 33 true)⟩]⟩⟩,
]
def c005_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -24, -12⟩, c005_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c005_0Check : c005_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base005) = true := by decide +kernel

#time def c006_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -22, -11⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [233480203545905, 457609079170]) 32 false)⟩]⟩⟩,
  ⟨⟨86, -22, -11⟩, ⟨97, -24, -12⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [233480203545905, 457609079170]) 32 false)⟩]⟩⟩,
]
def c006_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -24, -12⟩, c006_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c006_0Check : c006_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base006) = true := by decide +kernel

#time def c007_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -22, -11⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [233480203545905, 457609079170]) 33 true)⟩]⟩⟩,
  ⟨⟨86, -22, -11⟩, ⟨97, -24, -12⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [233480203545905, 457609079170]) 33 true)⟩]⟩⟩,
]
def c007_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -24, -12⟩, c007_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c007_0Check : c007_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base007) = true := by decide +kernel

#time def c008_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -22, -11⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [171651726752187, 152536359723]) 33 false)⟩]⟩⟩,
  ⟨⟨86, -22, -11⟩, ⟨97, -24, -12⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [171651726752187, 152536359723]) 33 false)⟩]⟩⟩,
]
def c008_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -24, -12⟩, c008_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c008_0Check : c008_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base008) = true := by decide +kernel

#time def c009_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -22, -11⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [171651726752187, 152536359723]) 32 true)⟩]⟩⟩,
  ⟨⟨86, -22, -11⟩, ⟨97, -24, -12⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [171651726752187, 152536359723]) 32 true)⟩]⟩⟩,
]
def c009_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -24, -12⟩, c009_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c009_0Check : c009_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base009) = true := by decide +kernel

#time def c010_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -22, -11⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨10, by decide⟩, (value (raw_ints% [15604702432017, 13866941793]) 31 true)⟩]⟩⟩,
  ⟨⟨86, -22, -11⟩, ⟨97, -24, -12⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [15604702432017, 13866941793]) 31 true)⟩]⟩⟩,
]
def c010_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -24, -12⟩, c010_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c010_0Check : c010_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base010) = true := by decide +kernel

#time def c010_1Zones : List (ResponseZone packet) := [
  ⟨⟨10, -2, -1⟩, ⟨4, 0, -1⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, 0, -1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨11, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, 0, 0⟩, ⟨97, -24, -12⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨22, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨32, by decide⟩, 1⟩]⟩⟩,
]
def c010_1 : ResponseComponent packet := ⟨⟨10, -2, -1⟩, ⟨0, 2, 1⟩, c010_1Zones⟩
-- kcost: 0.480 s provisional; 4 affine activation and row checks.
#time theorem c010_1Check : c010_1.check jetLayout win cert (unitTarget (n := packet.n) ⟨32, by decide⟩) = true := by decide +kernel

#time def c011_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨0, by decide⟩, (value (raw_ints% [171651726752187, 152536359723]) 31 true)⟩]⟩⟩,
]
def c011_0 : ResponseComponent packet := ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, c011_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c011_0Check : c011_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base011) = true := by decide +kernel

#time def c012_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [171651726752187, 152536359723]) 31 false)⟩]⟩⟩,
]
def c012_0 : ResponseComponent packet := ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, c012_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c012_0Check : c012_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base012) = true := by decide +kernel

#time def c013_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [233480203545905, 457609079170]) 31 true)⟩]⟩⟩,
]
def c013_0 : ResponseComponent packet := ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, c013_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c013_0Check : c013_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base013) = true := by decide +kernel

#time def c014_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [233480203545905, 457609079170]) 33 false)⟩]⟩⟩,
]
def c014_0 : ResponseComponent packet := ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, c014_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c014_0Check : c014_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base014) = true := by decide +kernel

#time def c015_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [226986541268055, 3203263554195]) 33 true)⟩]⟩⟩,
]
def c015_0 : ResponseComponent packet := ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, c015_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c015_0Check : c015_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base015) = true := by decide +kernel

#time def c016_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [226986541268055, 3203263554195]) 32 false)⟩]⟩⟩,
]
def c016_0 : ResponseComponent packet := ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, c016_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c016_0Check : c016_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base016) = true := by decide +kernel

#time def c017_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [233480203545905, 457609079170]) 32 true)⟩]⟩⟩,
]
def c017_0 : ResponseComponent packet := ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, c017_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c017_0Check : c017_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base017) = true := by decide +kernel

#time def c018_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [233480203545905, 457609079170]) 33 false)⟩]⟩⟩,
]
def c018_0 : ResponseComponent packet := ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, c018_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c018_0Check : c018_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base018) = true := by decide +kernel

#time def c019_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [171651726752187, 152536359723]) 32 true)⟩]⟩⟩,
]
def c019_0 : ResponseComponent packet := ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, c019_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c019_0Check : c019_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base019) = true := by decide +kernel

#time def c020_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [171651726752187, 152536359723]) 31 true)⟩]⟩⟩,
]
def c020_0 : ResponseComponent packet := ⟨⟨97, -24, -12⟩, ⟨0, 2, 1⟩, c020_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c020_0Check : c020_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016.base020) = true := by decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover016

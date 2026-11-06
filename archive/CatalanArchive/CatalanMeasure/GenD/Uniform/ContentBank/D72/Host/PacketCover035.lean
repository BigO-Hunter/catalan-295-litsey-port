module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain035
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PhysicalGate
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostLowGraph
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035
open CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035 (packet low value target)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain035 (jetLayout)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine004.P035 (win cert)

def gate : PhysicalGate72 := ⟨1, -3, 23, 3, 29, 33⟩
-- kcost: 0.100 s conservative; twelve affine quotient gates.
#time theorem gateCheck : gate.check win cert = true := by decide +kernel

#time def lowZones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨27, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -2, -1⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.250 s provisional; actual low-coordinate prefix and row checks.
#time theorem lowCheck : lowPrefixCheck jetLayout win cert ⟨-4, 4, 2⟩ low lowZones = true := by
  decide +kernel

#time def c000_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨0, by decide⟩, (value (raw_ints% [71339959]) 13 false)⟩]⟩⟩,
]
def c000_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, c000_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c000_0Check : c000_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base000) = true := by decide +kernel

#time def c001_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [71339959]) 14 true)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨0, by decide⟩, (value (raw_ints% [71339959]) 14 true)⟩]⟩⟩,
]
def c001_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c001_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c001_0Check : c001_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base001) = true := by decide +kernel

#time def c002_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [2068858811]) 14 false)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [2068858811]) 14 false)⟩]⟩⟩,
]
def c002_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c002_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c002_0Check : c002_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base002) = true := by decide +kernel

#time def c003_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [2068858811]) 16 true)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [2068858811]) 16 true)⟩]⟩⟩,
]
def c003_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c003_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c003_0Check : c003_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base003) = true := by decide +kernel

#time def c004_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [18619729299]) 16 false)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [18619729299]) 16 false)⟩]⟩⟩,
]
def c004_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c004_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c004_0Check : c004_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base004) = true := by decide +kernel

#time def c005_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [6206576433]) 17 true)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [6206576433]) 17 true)⟩]⟩⟩,
]
def c005_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c005_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c005_0Check : c005_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base005) = true := by decide +kernel

#time def c006_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [31032882165]) 17 false)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [31032882165]) 17 false)⟩]⟩⟩,
]
def c006_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c006_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c006_0Check : c006_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base006) = true := by decide +kernel

#time def c007_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [31032882165]) 20 true)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [31032882165]) 20 true)⟩]⟩⟩,
]
def c007_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c007_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c007_0Check : c007_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base007) = true := by decide +kernel

#time def c008_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [713756289795]) 20 false)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [713756289795]) 20 false)⟩]⟩⟩,
]
def c008_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c008_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c008_0Check : c008_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base008) = true := by decide +kernel

#time def c009_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [713756289795]) 21 true)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [713756289795]) 21 true)⟩]⟩⟩,
]
def c009_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c009_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c009_0Check : c009_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base009) = true := by decide +kernel

#time def c010_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨10, by decide⟩, (value (raw_ints% [713756289795]) 21 false)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [713756289795]) 21 false)⟩]⟩⟩,
]
def c010_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c010_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c010_0Check : c010_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base010) = true := by decide +kernel

#time def c011_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨11, by decide⟩, (value (raw_ints% [713756289795]) 23 true)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨10, by decide⟩, (value (raw_ints% [713756289795]) 23 true)⟩]⟩⟩,
]
def c011_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c011_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c011_0Check : c011_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base011) = true := by decide +kernel

#time def c012_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨12, by decide⟩, (value (raw_ints% [13561369506105]) 23 false)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨11, by decide⟩, (value (raw_ints% [13561369506105]) 23 false)⟩]⟩⟩,
]
def c012_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c012_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c012_0Check : c012_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base012) = true := by decide +kernel

#time def c013_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨13, by decide⟩, (value (raw_ints% [40684108518315]) 24 true)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨12, by decide⟩, (value (raw_ints% [40684108518315]) 24 true)⟩]⟩⟩,
]
def c013_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c013_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c013_0Check : c013_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base013) = true := by decide +kernel

#time def c014_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨14, by decide⟩, (value (raw_ints% [13561369506105]) 24 false)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨13, by decide⟩, (value (raw_ints% [13561369506105]) 24 false)⟩]⟩⟩,
]
def c014_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c014_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c014_0Check : c014_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base014) = true := by decide +kernel

#time def c015_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨15, by decide⟩, (value (raw_ints% [713756289795]) 28 true)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨14, by decide⟩, (value (raw_ints% [713756289795]) 28 true)⟩]⟩⟩,
]
def c015_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c015_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c015_0Check : c015_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base015) = true := by decide +kernel

#time def c016_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨16, by decide⟩, (value (raw_ints% [713756289795]) 28 false)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨15, by decide⟩, (value (raw_ints% [713756289795]) 28 false)⟩]⟩⟩,
]
def c016_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c016_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c016_0Check : c016_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base016) = true := by decide +kernel

#time def c017_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨17, by decide⟩, (value (raw_ints% [713756289795]) 29 true)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨16, by decide⟩, (value (raw_ints% [713756289795]) 29 true)⟩]⟩⟩,
]
def c017_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c017_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c017_0Check : c017_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base017) = true := by decide +kernel

#time def c018_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨18, by decide⟩, (value (raw_ints% [713756289795]) 29 false)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨17, by decide⟩, (value (raw_ints% [713756289795]) 29 false)⟩]⟩⟩,
]
def c018_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c018_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c018_0Check : c018_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base018) = true := by decide +kernel

#time def c019_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨19, by decide⟩, (value (raw_ints% [31032882165]) 31 true)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨18, by decide⟩, (value (raw_ints% [31032882165]) 31 true)⟩]⟩⟩,
]
def c019_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c019_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c019_0Check : c019_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base019) = true := by decide +kernel

#time def c020_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨20, by decide⟩, (value (raw_ints% [31032882165]) 29 false)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨19, by decide⟩, (value (raw_ints% [31032882165]) 29 false)⟩]⟩⟩,
]
def c020_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c020_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c020_0Check : c020_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base020) = true := by decide +kernel

#time def c021_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨21, by decide⟩, (value (raw_ints% [6206576433]) 29 true)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨20, by decide⟩, (value (raw_ints% [6206576433]) 29 true)⟩]⟩⟩,
]
def c021_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c021_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c021_0Check : c021_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base021) = true := by decide +kernel

#time def c022_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨22, by decide⟩, (value (raw_ints% [18619729299]) 29 false)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨21, by decide⟩, (value (raw_ints% [18619729299]) 29 false)⟩]⟩⟩,
]
def c022_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c022_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c022_0Check : c022_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base022) = true := by decide +kernel

#time def c023_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨23, by decide⟩, (value (raw_ints% [2068858811]) 31 true)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨22, by decide⟩, (value (raw_ints% [2068858811]) 31 true)⟩]⟩⟩,
]
def c023_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c023_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c023_0Check : c023_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base023) = true := by decide +kernel

#time def c024_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨24, by decide⟩, (value (raw_ints% [2068858811]) 30 false)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨23, by decide⟩, (value (raw_ints% [2068858811]) 30 false)⟩]⟩⟩,
]
def c024_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c024_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c024_0Check : c024_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base024) = true := by decide +kernel

#time def c025_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨25, by decide⟩, (value (raw_ints% [71339959]) 30 true)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨24, by decide⟩, (value (raw_ints% [71339959]) 30 true)⟩]⟩⟩,
]
def c025_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c025_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c025_0Check : c025_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base025) = true := by decide +kernel

#time def c026_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -60, -30⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨26, by decide⟩, (value (raw_ints% [71339959]) 30 true)⟩]⟩⟩,
  ⟨⟨86, -60, -30⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨25, by decide⟩, (value (raw_ints% [71339959]) 30 true)⟩]⟩⟩,
]
def c026_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -66, -33⟩, c026_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c026_0Check : c026_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base026) = true := by decide +kernel

#time def c026_1Zones : List (ResponseZone packet) := [
  ⟨⟨10, -6, -3⟩, ⟨70, -48, -25⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨70, -48, -25⟩, ⟨97, -66, -33⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨28, by decide⟩, 1⟩]⟩⟩,
]
def c026_1 : ResponseComponent packet := ⟨⟨10, -6, -3⟩, ⟨0, 2, 1⟩, c026_1Zones⟩
-- kcost: 0.360 s provisional; 3 affine activation and row checks.
#time theorem c026_1Check : c026_1.check jetLayout win cert (unitTarget (n := packet.n) ⟨111, by decide⟩) = true := by decide +kernel

#time def c027_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨0, by decide⟩, (value (raw_ints% [71339959]) 14 true)⟩]⟩⟩,
]
def c027_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c027_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c027_0Check : c027_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base027) = true := by decide +kernel

#time def c028_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [2068858811]) 14 false)⟩]⟩⟩,
]
def c028_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c028_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c028_0Check : c028_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base028) = true := by decide +kernel

#time def c029_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [2068858811]) 16 true)⟩]⟩⟩,
]
def c029_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c029_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c029_0Check : c029_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base029) = true := by decide +kernel

#time def c030_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [18619729299]) 16 false)⟩]⟩⟩,
]
def c030_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c030_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c030_0Check : c030_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base030) = true := by decide +kernel

#time def c031_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [18619729299]) 17 true)⟩]⟩⟩,
]
def c031_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c031_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c031_0Check : c031_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base031) = true := by decide +kernel

#time def c032_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [31032882165]) 17 false)⟩]⟩⟩,
]
def c032_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c032_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c032_0Check : c032_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base032) = true := by decide +kernel

#time def c033_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [31032882165]) 20 true)⟩]⟩⟩,
]
def c033_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c033_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c033_0Check : c033_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base033) = true := by decide +kernel

#time def c034_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [713756289795]) 20 false)⟩]⟩⟩,
]
def c034_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c034_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c034_0Check : c034_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base034) = true := by decide +kernel

#time def c035_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [713756289795]) 21 true)⟩]⟩⟩,
]
def c035_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c035_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c035_0Check : c035_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base035) = true := by decide +kernel

#time def c036_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [713756289795]) 21 false)⟩]⟩⟩,
]
def c036_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c036_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c036_0Check : c036_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base036) = true := by decide +kernel

#time def c037_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨10, by decide⟩, (value (raw_ints% [713756289795]) 23 true)⟩]⟩⟩,
]
def c037_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c037_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c037_0Check : c037_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base037) = true := by decide +kernel

#time def c038_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨11, by decide⟩, (value (raw_ints% [13561369506105]) 23 false)⟩]⟩⟩,
]
def c038_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c038_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c038_0Check : c038_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base038) = true := by decide +kernel

#time def c039_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨12, by decide⟩, (value (raw_ints% [40684108518315]) 24 true)⟩]⟩⟩,
]
def c039_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c039_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c039_0Check : c039_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base039) = true := by decide +kernel

#time def c040_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨13, by decide⟩, (value (raw_ints% [40684108518315]) 24 false)⟩]⟩⟩,
]
def c040_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c040_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c040_0Check : c040_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base040) = true := by decide +kernel

#time def c041_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨14, by decide⟩, (value (raw_ints% [13561369506105]) 28 true)⟩]⟩⟩,
]
def c041_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c041_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c041_0Check : c041_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base041) = true := by decide +kernel

#time def c042_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨15, by decide⟩, (value (raw_ints% [713756289795]) 28 false)⟩]⟩⟩,
]
def c042_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c042_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c042_0Check : c042_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base042) = true := by decide +kernel

#time def c043_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨16, by decide⟩, (value (raw_ints% [713756289795]) 29 true)⟩]⟩⟩,
]
def c043_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c043_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c043_0Check : c043_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base043) = true := by decide +kernel

#time def c044_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨17, by decide⟩, (value (raw_ints% [713756289795]) 29 false)⟩]⟩⟩,
]
def c044_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c044_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c044_0Check : c044_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base044) = true := by decide +kernel

#time def c045_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨18, by decide⟩, (value (raw_ints% [713756289795]) 31 true)⟩]⟩⟩,
]
def c045_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c045_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c045_0Check : c045_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base045) = true := by decide +kernel

#time def c046_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨19, by decide⟩, (value (raw_ints% [31032882165]) 31 false)⟩]⟩⟩,
]
def c046_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c046_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c046_0Check : c046_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base046) = true := by decide +kernel

#time def c047_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨20, by decide⟩, (value (raw_ints% [31032882165]) 29 true)⟩]⟩⟩,
]
def c047_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c047_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c047_0Check : c047_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base047) = true := by decide +kernel

#time def c048_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨21, by decide⟩, (value (raw_ints% [18619729299]) 29 false)⟩]⟩⟩,
]
def c048_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c048_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c048_0Check : c048_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base048) = true := by decide +kernel

#time def c049_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨22, by decide⟩, (value (raw_ints% [18619729299]) 31 true)⟩]⟩⟩,
]
def c049_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c049_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c049_0Check : c049_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base049) = true := by decide +kernel

#time def c050_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨23, by decide⟩, (value (raw_ints% [2068858811]) 31 false)⟩]⟩⟩,
]
def c050_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c050_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c050_0Check : c050_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base050) = true := by decide +kernel

#time def c051_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨24, by decide⟩, (value (raw_ints% [2068858811]) 30 true)⟩]⟩⟩,
]
def c051_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c051_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c051_0Check : c051_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base051) = true := by decide +kernel

#time def c052_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨25, by decide⟩, (value (raw_ints% [71339959]) 30 true)⟩]⟩⟩,
]
def c052_0 : ResponseComponent packet := ⟨⟨97, -66, -33⟩, ⟨0, 2, 1⟩, c052_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c052_0Check : c052_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base052) = true := by decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035

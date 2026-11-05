module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain009
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PhysicalGate
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostLowGraph
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover009
open CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009 (packet low value target)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain009 (jetLayout)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine001.P009 (win cert)

def gate : PhysicalGate72 := ⟨0, -2, 12, 2, 15, 17⟩
-- kcost: 0.100 s conservative; twelve affine quotient gates.
#time theorem gateCheck : gate.check win cert = true := by decide +kernel

#time def lowZones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨16, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -1, -1⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.250 s provisional; actual low-coordinate prefix and row checks.
#time theorem lowCheck : lowPrefixCheck jetLayout win cert ⟨-4, 2, 1⟩ low lowZones = true := by
  decide +kernel

#time def c000_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨0, by decide⟩, (value (raw_ints% [215544919410329, 4826641]) 28 true)⟩]⟩⟩,
]
def c000_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, c000_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c000_0Check : c000_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base000) = true := by decide +kernel

#time def c001_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [215544919410329, 4826641]) 28 false)⟩]⟩⟩,
  ⟨⟨86, -30, -15⟩, ⟨97, -34, -17⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨0, by decide⟩, (value (raw_ints% [215544919410329, 4826641]) 28 false)⟩]⟩⟩,
]
def c001_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -34, -17⟩, c001_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c001_0Check : c001_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base001) = true := by decide +kernel

#time def c002_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [215544919410329, 4826641]) 29 true)⟩]⟩⟩,
  ⟨⟨86, -30, -15⟩, ⟨97, -34, -17⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [215544919410329, 4826641]) 29 true)⟩]⟩⟩,
]
def c002_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -34, -17⟩, c002_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c002_0Check : c002_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base002) = true := by decide +kernel

#time def c003_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [268809161938373, 62746342]) 29 false)⟩]⟩⟩,
  ⟨⟨86, -30, -15⟩, ⟨97, -34, -17⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [268809161938373, 62746342]) 29 false)⟩]⟩⟩,
]
def c003_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -34, -17⟩, c003_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c003_0Check : c003_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base003) = true := by decide +kernel

#time def c004_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [268809161938373, 62746342]) 31 true)⟩]⟩⟩,
  ⟨⟨86, -30, -15⟩, ⟨97, -34, -17⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [268809161938373, 62746342]) 31 true)⟩]⟩⟩,
]
def c004_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -34, -17⟩, c004_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c004_0Check : c004_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base004) = true := by decide +kernel

#time def c005_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [142151014215543, 690209772]) 31 false)⟩]⟩⟩,
  ⟨⟨86, -30, -15⟩, ⟨97, -34, -17⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [142151014215543, 690209772]) 31 false)⟩]⟩⟩,
]
def c005_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -34, -17⟩, c005_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c005_0Check : c005_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base005) = true := by decide +kernel

#time def c006_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [142151014215543, 690209772]) 30 true)⟩]⟩⟩,
  ⟨⟨86, -30, -15⟩, ⟨97, -34, -17⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [142151014215543, 690209772]) 30 true)⟩]⟩⟩,
]
def c006_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -34, -17⟩, c006_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c006_0Check : c006_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base006) = true := by decide +kernel

#time def c007_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [142151014215543, 690209772]) 30 false)⟩]⟩⟩,
  ⟨⟨86, -30, -15⟩, ⟨97, -34, -17⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [142151014215543, 690209772]) 30 false)⟩]⟩⟩,
]
def c007_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -34, -17⟩, c007_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c007_0Check : c007_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base007) = true := by decide +kernel

#time def c008_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [142151014215543, 690209772]) 32 true)⟩]⟩⟩,
  ⟨⟨86, -30, -15⟩, ⟨97, -34, -17⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [142151014215543, 690209772]) 32 true)⟩]⟩⟩,
]
def c008_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -34, -17⟩, c008_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c008_0Check : c008_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base008) = true := by decide +kernel

#time def c009_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [268809161938373, 62746342]) 32 false)⟩]⟩⟩,
  ⟨⟨86, -30, -15⟩, ⟨97, -34, -17⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [268809161938373, 62746342]) 32 false)⟩]⟩⟩,
]
def c009_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -34, -17⟩, c009_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c009_0Check : c009_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base009) = true := by decide +kernel

#time def c010_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨10, by decide⟩, (value (raw_ints% [268809161938373, 62746342]) 31 true)⟩]⟩⟩,
  ⟨⟨86, -30, -15⟩, ⟨97, -34, -17⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [268809161938373, 62746342]) 31 true)⟩]⟩⟩,
]
def c010_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -34, -17⟩, c010_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c010_0Check : c010_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base010) = true := by decide +kernel

#time def c011_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨11, by decide⟩, (value (raw_ints% [215544919410329, 4826641]) 31 false)⟩]⟩⟩,
  ⟨⟨86, -30, -15⟩, ⟨97, -34, -17⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨10, by decide⟩, (value (raw_ints% [215544919410329, 4826641]) 31 false)⟩]⟩⟩,
]
def c011_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -34, -17⟩, c011_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c011_0Check : c011_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base011) = true := by decide +kernel

#time def c012_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨12, by decide⟩, (value (raw_ints% [215544919410329, 4826641]) 32 true)⟩]⟩⟩,
  ⟨⟨86, -30, -15⟩, ⟨97, -34, -17⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨11, by decide⟩, (value (raw_ints% [215544919410329, 4826641]) 32 true)⟩]⟩⟩,
]
def c012_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -34, -17⟩, c012_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c012_0Check : c012_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base012) = true := by decide +kernel

#time def c013_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -30, -15⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨13, by decide⟩, (value (raw_ints% [215544919410329, 4826641]) 32 true)⟩]⟩⟩,
  ⟨⟨86, -30, -15⟩, ⟨97, -34, -17⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨12, by decide⟩, (value (raw_ints% [215544919410329, 4826641]) 32 true)⟩]⟩⟩,
]
def c013_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -34, -17⟩, c013_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c013_0Check : c013_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base013) = true := by decide +kernel

#time def c014_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -34, -17⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨0, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 28 false)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -24, -13⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 28 false)⟩]⟩⟩,
  ⟨⟨70, -24, -13⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 28 false)⟩]⟩⟩,
]
def c014_0 : ResponseComponent packet := ⟨⟨97, -34, -17⟩, ⟨0, 2, 1⟩, c014_0Zones⟩
-- kcost: 0.360 s provisional; 3 affine activation and row checks.
#time theorem c014_0Check : c014_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base014) = true := by decide +kernel

#time def c015_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -34, -17⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 29 true)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -24, -13⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 29 true)⟩]⟩⟩,
  ⟨⟨70, -24, -13⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 29 true)⟩]⟩⟩,
]
def c015_0 : ResponseComponent packet := ⟨⟨97, -34, -17⟩, ⟨0, 2, 1⟩, c015_0Zones⟩
-- kcost: 0.360 s provisional; 3 affine activation and row checks.
#time theorem c015_0Check : c015_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base015) = true := by decide +kernel

#time def c016_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -34, -17⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 29 false)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -24, -13⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 29 false)⟩]⟩⟩,
  ⟨⟨70, -24, -13⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 29 false)⟩]⟩⟩,
]
def c016_0 : ResponseComponent packet := ⟨⟨97, -34, -17⟩, ⟨0, 2, 1⟩, c016_0Zones⟩
-- kcost: 0.360 s provisional; 3 affine activation and row checks.
#time theorem c016_0Check : c016_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base016) = true := by decide +kernel

#time def c017_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -34, -17⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 31 true)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -24, -13⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 31 true)⟩]⟩⟩,
  ⟨⟨70, -24, -13⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 31 true)⟩]⟩⟩,
]
def c017_0 : ResponseComponent packet := ⟨⟨97, -34, -17⟩, ⟨0, 2, 1⟩, c017_0Zones⟩
-- kcost: 0.360 s provisional; 3 affine activation and row checks.
#time theorem c017_0Check : c017_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base017) = true := by decide +kernel

#time def c018_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -34, -17⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 31 false)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -24, -13⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 31 false)⟩]⟩⟩,
  ⟨⟨70, -24, -13⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 31 false)⟩]⟩⟩,
]
def c018_0 : ResponseComponent packet := ⟨⟨97, -34, -17⟩, ⟨0, 2, 1⟩, c018_0Zones⟩
-- kcost: 0.360 s provisional; 3 affine activation and row checks.
#time theorem c018_0Check : c018_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base018) = true := by decide +kernel

#time def c019_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -34, -17⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 31 true)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -24, -13⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 31 true)⟩]⟩⟩,
  ⟨⟨70, -24, -13⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 31 true)⟩]⟩⟩,
]
def c019_0 : ResponseComponent packet := ⟨⟨97, -34, -17⟩, ⟨0, 2, 1⟩, c019_0Zones⟩
-- kcost: 0.360 s provisional; 3 affine activation and row checks.
#time theorem c019_0Check : c019_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base019) = true := by decide +kernel

#time def c020_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -34, -17⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [212827307226293, 35200698397]) 30 false)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -24, -13⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [212827307226293, 35200698397]) 30 false)⟩]⟩⟩,
  ⟨⟨70, -24, -13⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [212827307226293, 35200698397]) 30 false)⟩]⟩⟩,
]
def c020_0 : ResponseComponent packet := ⟨⟨97, -34, -17⟩, ⟨0, 2, 1⟩, c020_0Zones⟩
-- kcost: 0.360 s provisional; 3 affine activation and row checks.
#time theorem c020_0Check : c020_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base020) = true := by decide +kernel

#time def c021_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -34, -17⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 33 true)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -24, -13⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 33 true)⟩]⟩⟩,
  ⟨⟨70, -24, -13⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨10, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 33 true)⟩]⟩⟩,
]
def c021_0 : ResponseComponent packet := ⟨⟨97, -34, -17⟩, ⟨0, 2, 1⟩, c021_0Zones⟩
-- kcost: 0.360 s provisional; 3 affine activation and row checks.
#time theorem c021_0Check : c021_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base021) = true := by decide +kernel

#time def c022_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -34, -17⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 32 false)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -24, -13⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨10, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 32 false)⟩]⟩⟩,
  ⟨⟨70, -24, -13⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨11, by decide⟩, (value (raw_ints% [164767427978983, 11733566132]) 32 false)⟩]⟩⟩,
]
def c022_0 : ResponseComponent packet := ⟨⟨97, -34, -17⟩, ⟨0, 2, 1⟩, c022_0Zones⟩
-- kcost: 0.360 s provisional; 3 affine activation and row checks.
#time theorem c022_0Check : c022_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base022) = true := by decide +kernel

#time def c023_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -34, -17⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 33 true)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -24, -13⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨11, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 33 true)⟩]⟩⟩,
  ⟨⟨70, -24, -13⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨12, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 33 true)⟩]⟩⟩,
]
def c023_0 : ResponseComponent packet := ⟨⟨97, -34, -17⟩, ⟨0, 2, 1⟩, c023_0Zones⟩
-- kcost: 0.360 s provisional; 3 affine activation and row checks.
#time theorem c023_0Check : c023_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base023) = true := by decide +kernel

#time def c024_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -34, -17⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨10, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 31 false)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -24, -13⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨12, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 31 false)⟩]⟩⟩,
  ⟨⟨70, -24, -13⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨13, by decide⟩, (value (raw_ints% [66156125581845, 1066687830]) 31 false)⟩]⟩⟩,
]
def c024_0 : ResponseComponent packet := ⟨⟨97, -34, -17⟩, ⟨0, 2, 1⟩, c024_0Zones⟩
-- kcost: 0.360 s provisional; 3 affine activation and row checks.
#time theorem c024_0Check : c024_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base024) = true := by decide +kernel

#time def c025_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -34, -17⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨11, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 33 true)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -24, -13⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨13, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 33 true)⟩]⟩⟩,
  ⟨⟨70, -24, -13⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨14, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 33 true)⟩]⟩⟩,
]
def c025_0 : ResponseComponent packet := ⟨⟨97, -34, -17⟩, ⟨0, 2, 1⟩, c025_0Zones⟩
-- kcost: 0.360 s provisional; 3 affine activation and row checks.
#time theorem c025_0Check : c025_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base025) = true := by decide +kernel

#time def c026_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -34, -17⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨12, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 32 true)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -24, -13⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨14, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 32 true)⟩]⟩⟩,
  ⟨⟨70, -24, -13⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨15, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 32 true)⟩]⟩⟩,
]
def c026_0 : ResponseComponent packet := ⟨⟨97, -34, -17⟩, ⟨0, 2, 1⟩, c026_0Zones⟩
-- kcost: 0.360 s provisional; 3 affine activation and row checks.
#time theorem c026_0Check : c026_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base026) = true := by decide +kernel

#time def c027_0Zones : List (ResponseZone packet) := [
  ⟨⟨10, -2, -1⟩, ⟨70, -24, -13⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 31 false)⟩]⟩⟩,
  ⟨⟨70, -24, -13⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [5088932737065, 82052910]) 31 false)⟩]⟩⟩,
]
def c027_0 : ResponseComponent packet := ⟨⟨10, -2, -1⟩, ⟨0, 2, 1⟩, c027_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c027_0Check : c027_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource009.base027) = true := by decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover009

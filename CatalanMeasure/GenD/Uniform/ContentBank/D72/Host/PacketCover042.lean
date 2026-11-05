module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain042
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PhysicalGate
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostLowGraph
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover042
open CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042 (packet low value target)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain042 (jetLayout)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine006.P042 (win cert)

def gate : PhysicalGate72 := ⟨0, -1, 6, 1, 8, 10⟩
-- kcost: 0.100 s conservative; twelve affine quotient gates.
#time theorem gateCheck : gate.check win cert = true := by decide +kernel

#time def lowZones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, 0, 0⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.250 s provisional; actual low-coordinate prefix and row checks.
#time theorem lowCheck : lowPrefixCheck jetLayout win cert ⟨-4, 2, 1⟩ low lowZones = true := by
  decide +kernel

#time def c000_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨0, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 31 false)⟩]⟩⟩,
]
def c000_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, c000_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c000_0Check : c000_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base000) = true := by decide +kernel

#time def c001_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [35007448609051, 5033699870879]) 33 false)⟩]⟩⟩,
]
def c001_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, c001_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c001_0Check : c001_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base001) = true := by decide +kernel

#time def c002_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [245052140263357, 35235899096153]) 33 false)⟩]⟩⟩,
]
def c002_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, c002_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c002_0Check : c002_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base002) = true := by decide +kernel

#time def c003_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [172206467368759, 105707697288461]) 32 false)⟩]⟩⟩,
]
def c003_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, c003_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c003_0Check : c003_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base003) = true := by decide +kernel

#time def c004_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [245052140263357, 35235899096153]) 32 false)⟩]⟩⟩,
]
def c004_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, c004_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c004_0Check : c004_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base004) = true := by decide +kernel

#time def c005_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [35007448609051, 5033699870879]) 33 false)⟩]⟩⟩,
]
def c005_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, c005_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c005_0Check : c005_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base005) = true := by decide +kernel

#time def c006_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 32 true)⟩]⟩⟩,
]
def c006_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, c006_0Zones⟩
-- kcost: 0.120 s provisional; 1 affine activation and row checks.
#time theorem c006_0Check : c006_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base006) = true := by decide +kernel

#time def c007_0Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨97, -20, -10⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 31 false)⟩]⟩⟩,
  ⟨⟨97, -20, -10⟩, ⟨86, -16, -8⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨0, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 31 false)⟩]⟩⟩,
]
def c007_0 : ResponseComponent packet := ⟨⟨0, 0, 0⟩, ⟨86, -16, -8⟩, c007_0Zones⟩
-- kcost: 0.240 s provisional; 2 affine activation and row checks.
#time theorem c007_0Check : c007_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base007) = true := by decide +kernel

#time def c007_1Zones : List (ResponseZone packet) := [
  ⟨⟨97, -20, -10⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -14, -8⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨70, -14, -8⟩, ⟨4, 0, -1⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, 0, -1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨11, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, 0, 0⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨20, by decide⟩, 1⟩]⟩⟩,
]
def c007_1 : ResponseComponent packet := ⟨⟨97, -20, -10⟩, ⟨0, 2, 1⟩, c007_1Zones⟩
-- kcost: 0.600 s provisional; 5 affine activation and row checks.
#time theorem c007_1Check : c007_1.check jetLayout win cert (unitTarget (n := packet.n) ⟨35, by decide⟩) = true := by decide +kernel

#time def c008_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -20, -10⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 33 false)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -14, -8⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 33 false)⟩]⟩⟩,
  ⟨⟨70, -14, -8⟩, ⟨4, 0, -1⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 33 false)⟩]⟩⟩,
  ⟨⟨4, 0, -1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨12, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 33 false)⟩]⟩⟩,
  ⟨⟨4, 0, 0⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨21, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 33 false)⟩]⟩⟩,
]
def c008_0 : ResponseComponent packet := ⟨⟨97, -20, -10⟩, ⟨0, 2, 1⟩, c008_0Zones⟩
-- kcost: 0.600 s provisional; 5 affine activation and row checks.
#time theorem c008_0Check : c008_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base008) = true := by decide +kernel

#time def c009_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -20, -10⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [245052140263357, 35235899096153]) 33 false)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -14, -8⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [245052140263357, 35235899096153]) 33 false)⟩]⟩⟩,
  ⟨⟨70, -14, -8⟩, ⟨4, 0, -1⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [245052140263357, 35235899096153]) 33 false)⟩]⟩⟩,
  ⟨⟨4, 0, -1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨13, by decide⟩, (value (raw_ints% [245052140263357, 35235899096153]) 33 false)⟩]⟩⟩,
  ⟨⟨4, 0, 0⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨22, by decide⟩, (value (raw_ints% [245052140263357, 35235899096153]) 33 false)⟩]⟩⟩,
]
def c009_0 : ResponseComponent packet := ⟨⟨97, -20, -10⟩, ⟨0, 2, 1⟩, c009_0Zones⟩
-- kcost: 0.600 s provisional; 5 affine activation and row checks.
#time theorem c009_0Check : c009_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base009) = true := by decide +kernel

#time def c010_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -20, -10⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨3, by decide⟩, (value (raw_ints% [172206467368759, 105707697288461]) 32 false)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -14, -8⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [172206467368759, 105707697288461]) 32 false)⟩]⟩⟩,
  ⟨⟨70, -14, -8⟩, ⟨4, 0, -1⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [172206467368759, 105707697288461]) 32 false)⟩]⟩⟩,
  ⟨⟨4, 0, -1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨14, by decide⟩, (value (raw_ints% [172206467368759, 105707697288461]) 32 false)⟩]⟩⟩,
  ⟨⟨4, 0, 0⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨23, by decide⟩, (value (raw_ints% [172206467368759, 105707697288461]) 32 false)⟩]⟩⟩,
]
def c010_0 : ResponseComponent packet := ⟨⟨97, -20, -10⟩, ⟨0, 2, 1⟩, c010_0Zones⟩
-- kcost: 0.600 s provisional; 5 affine activation and row checks.
#time theorem c010_0Check : c010_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base010) = true := by decide +kernel

#time def c011_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -20, -10⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨4, by decide⟩, (value (raw_ints% [172206467368759, 105707697288461]) 32 false)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -14, -8⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [172206467368759, 105707697288461]) 32 false)⟩]⟩⟩,
  ⟨⟨70, -14, -8⟩, ⟨4, 0, -1⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [172206467368759, 105707697288461]) 32 false)⟩]⟩⟩,
  ⟨⟨4, 0, -1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨15, by decide⟩, (value (raw_ints% [172206467368759, 105707697288461]) 32 false)⟩]⟩⟩,
  ⟨⟨4, 0, 0⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨24, by decide⟩, (value (raw_ints% [172206467368759, 105707697288461]) 32 false)⟩]⟩⟩,
]
def c011_0 : ResponseComponent packet := ⟨⟨97, -20, -10⟩, ⟨0, 2, 1⟩, c011_0Zones⟩
-- kcost: 0.600 s provisional; 5 affine activation and row checks.
#time theorem c011_0Check : c011_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base011) = true := by decide +kernel

#time def c012_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -20, -10⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨5, by decide⟩, (value (raw_ints% [245052140263357, 35235899096153]) 33 false)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -14, -8⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨7, by decide⟩, (value (raw_ints% [245052140263357, 35235899096153]) 33 false)⟩]⟩⟩,
  ⟨⟨70, -14, -8⟩, ⟨4, 0, -1⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [245052140263357, 35235899096153]) 33 false)⟩]⟩⟩,
  ⟨⟨4, 0, -1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨16, by decide⟩, (value (raw_ints% [245052140263357, 35235899096153]) 33 false)⟩]⟩⟩,
  ⟨⟨4, 0, 0⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨25, by decide⟩, (value (raw_ints% [245052140263357, 35235899096153]) 33 false)⟩]⟩⟩,
]
def c012_0 : ResponseComponent packet := ⟨⟨97, -20, -10⟩, ⟨0, 2, 1⟩, c012_0Zones⟩
-- kcost: 0.600 s provisional; 5 affine activation and row checks.
#time theorem c012_0Check : c012_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base012) = true := by decide +kernel

#time def c013_0Zones : List (ResponseZone packet) := [
  ⟨⟨97, -20, -10⟩, ⟨10, -2, -1⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨6, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 33 false)⟩]⟩⟩,
  ⟨⟨10, -2, -1⟩, ⟨70, -14, -8⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨8, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 33 false)⟩]⟩⟩,
  ⟨⟨70, -14, -8⟩, ⟨4, 0, -1⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨9, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 33 false)⟩]⟩⟩,
  ⟨⟨4, 0, -1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨17, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 33 false)⟩]⟩⟩,
  ⟨⟨4, 0, 0⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨26, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 33 false)⟩]⟩⟩,
]
def c013_0 : ResponseComponent packet := ⟨⟨97, -20, -10⟩, ⟨0, 2, 1⟩, c013_0Zones⟩
-- kcost: 0.600 s provisional; 5 affine activation and row checks.
#time theorem c013_0Check : c013_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base013) = true := by decide +kernel

#time def c014_0Zones : List (ResponseZone packet) := [
  ⟨⟨10, -2, -1⟩, ⟨70, -14, -8⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨1, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 31 true)⟩]⟩⟩,
  ⟨⟨70, -14, -8⟩, ⟨4, 0, -1⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨2, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 31 true)⟩]⟩⟩,
  ⟨⟨4, 0, -1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨10, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 31 true)⟩]⟩⟩,
  ⟨⟨4, 0, 0⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨19, by decide⟩, (value (raw_ints% [105022345827153, 15101099612637]) 31 true)⟩]⟩⟩,
]
def c014_0 : ResponseComponent packet := ⟨⟨10, -2, -1⟩, ⟨0, 2, 1⟩, c014_0Zones⟩
-- kcost: 0.480 s provisional; 4 affine activation and row checks.
#time theorem c014_0Check : c014_0.check jetLayout win cert (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042.base014) = true := by decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover042

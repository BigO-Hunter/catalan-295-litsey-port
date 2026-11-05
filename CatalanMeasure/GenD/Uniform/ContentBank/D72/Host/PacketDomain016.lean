module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.DomainRows
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine002
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain016
open CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource016 (packet slots slotCount)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine002.P016 (win cert)

def pointTape : List PhysicalPoint := [.minus, .zero, .zero, .plus, .plus, .plus, .infinity, .infinity, .infinity, .infinity, .infinity]
def offsetTape : List Aff := [⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ⟨86, -22, -11⟩, ⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨-4, 2, 1⟩, ⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨-4, 2, 2⟩, ⟨-10, 4, 2⟩]
def widthTape : List Aff := [⟨0, 1, 0⟩, ⟨86, -22, -11⟩, ⟨11, -2, -1⟩, ⟨4, -1, -1⟩, ⟨-8, 3, 2⟩, ⟨8, -2, -1⟩, ⟨-97, 26, 13⟩, ⟨93, -24, -12⟩, ⟨0, 0, 1⟩, ⟨-6, 2, 0⟩, ⟨-60, 16, 9⟩]
def jetLayout : JetLayout packet := ⟨fun g => pointTape.getD g.val .zero,
  fun g => offsetTape.getD g.val ⟨0, 0, 0⟩, fun g => widthTape.getD g.val ⟨0, 0, 0⟩⟩

def req000Terms : List (Fin slotCount × Int) := [(⟨1, by decide⟩, 1)]
#time def req000Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check000 : jetPrefixCheck jetLayout win cert .plus ⟨4, -1, -1⟩
    (nativeDomainTarget slots req000Terms) req000Zones = true := by decide +kernel

def req001Terms : List (Fin slotCount × Int) := [(⟨1, by decide⟩, 1)]
#time def req001Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨10, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.160 s provisional; 2 exact row/activation checks.
#time theorem check001 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 1⟩
    (nativeDomainTarget slots req001Terms) req001Zones = true := by decide +kernel

def req002Terms : List (Fin slotCount × Int) := [(⟨2, by decide⟩, 1)]
#time def req002Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨12, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -1, -1⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check002 : jetPrefixCheck jetLayout win cert .plus ⟨4, 0, 0⟩
    (nativeDomainTarget slots req002Terms) req002Zones = true := by decide +kernel

def req003Terms : List (Fin slotCount × Int) := [(⟨3, by decide⟩, 1)]
#time def req003Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨21, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨11, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨-4, 2, 2⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check003 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 2⟩
    (nativeDomainTarget slots req003Terms) req003Zones = true := by decide +kernel

def req004Terms : List (Fin slotCount × Int) := [(⟨5, by decide⟩, 1)]
#time def req004Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check004 : jetPrefixCheck jetLayout win cert .plus ⟨4, -1, -1⟩
    (nativeDomainTarget slots req004Terms) req004Zones = true := by decide +kernel

def req005Terms : List (Fin slotCount × Int) := [(⟨5, by decide⟩, 1)]
#time def req005Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨11, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.160 s provisional; 2 exact row/activation checks.
#time theorem check005 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 1⟩
    (nativeDomainTarget slots req005Terms) req005Zones = true := by decide +kernel

def req006Terms : List (Fin slotCount × Int) := [(⟨6, by decide⟩, 1)]
#time def req006Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨13, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -1, -1⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check006 : jetPrefixCheck jetLayout win cert .plus ⟨4, 0, 0⟩
    (nativeDomainTarget slots req006Terms) req006Zones = true := by decide +kernel

def req007Terms : List (Fin slotCount × Int) := [(⟨7, by decide⟩, 1)]
#time def req007Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨22, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨12, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨-4, 2, 2⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check007 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 2⟩
    (nativeDomainTarget slots req007Terms) req007Zones = true := by decide +kernel

def req008Terms : List (Fin slotCount × Int) := [(⟨9, by decide⟩, 1)]
#time def req008Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check008 : jetPrefixCheck jetLayout win cert .plus ⟨4, -1, -1⟩
    (nativeDomainTarget slots req008Terms) req008Zones = true := by decide +kernel

def req009Terms : List (Fin slotCount × Int) := [(⟨9, by decide⟩, 1)]
#time def req009Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨12, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.160 s provisional; 2 exact row/activation checks.
#time theorem check009 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 1⟩
    (nativeDomainTarget slots req009Terms) req009Zones = true := by decide +kernel

def req010Terms : List (Fin slotCount × Int) := [(⟨10, by decide⟩, 1)]
#time def req010Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨14, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -1, -1⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check010 : jetPrefixCheck jetLayout win cert .plus ⟨4, 0, 0⟩
    (nativeDomainTarget slots req010Terms) req010Zones = true := by decide +kernel

def req011Terms : List (Fin slotCount × Int) := [(⟨11, by decide⟩, 1)]
#time def req011Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨23, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨13, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨-4, 2, 2⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check011 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 2⟩
    (nativeDomainTarget slots req011Terms) req011Zones = true := by decide +kernel

def req012Terms : List (Fin slotCount × Int) := [(⟨13, by decide⟩, 1)]
#time def req012Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check012 : jetPrefixCheck jetLayout win cert .plus ⟨4, -1, -1⟩
    (nativeDomainTarget slots req012Terms) req012Zones = true := by decide +kernel

def req013Terms : List (Fin slotCount × Int) := [(⟨13, by decide⟩, 1)]
#time def req013Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨13, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.160 s provisional; 2 exact row/activation checks.
#time theorem check013 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 1⟩
    (nativeDomainTarget slots req013Terms) req013Zones = true := by decide +kernel

def req014Terms : List (Fin slotCount × Int) := [(⟨14, by decide⟩, 1)]
#time def req014Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨15, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -1, -1⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨4, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check014 : jetPrefixCheck jetLayout win cert .plus ⟨4, 0, 0⟩
    (nativeDomainTarget slots req014Terms) req014Zones = true := by decide +kernel

def req015Terms : List (Fin slotCount × Int) := [(⟨15, by decide⟩, 1)]
#time def req015Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨24, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨14, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨-4, 2, 2⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check015 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 2⟩
    (nativeDomainTarget slots req015Terms) req015Zones = true := by decide +kernel

def req016Terms : List (Fin slotCount × Int) := [(⟨17, by decide⟩, 1)]
#time def req016Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨4, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check016 : jetPrefixCheck jetLayout win cert .plus ⟨4, -1, -1⟩
    (nativeDomainTarget slots req016Terms) req016Zones = true := by decide +kernel

def req017Terms : List (Fin slotCount × Int) := [(⟨17, by decide⟩, 1)]
#time def req017Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨14, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨4, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.160 s provisional; 2 exact row/activation checks.
#time theorem check017 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 1⟩
    (nativeDomainTarget slots req017Terms) req017Zones = true := by decide +kernel

def req018Terms : List (Fin slotCount × Int) := [(⟨18, by decide⟩, 1)]
#time def req018Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨16, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -1, -1⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨5, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨4, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check018 : jetPrefixCheck jetLayout win cert .plus ⟨4, 0, 0⟩
    (nativeDomainTarget slots req018Terms) req018Zones = true := by decide +kernel

def req019Terms : List (Fin slotCount × Int) := [(⟨19, by decide⟩, 1)]
#time def req019Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨25, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨15, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨-4, 2, 2⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨4, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check019 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 2⟩
    (nativeDomainTarget slots req019Terms) req019Zones = true := by decide +kernel

def req020Terms : List (Fin slotCount × Int) := [(⟨21, by decide⟩, 1)]
#time def req020Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨5, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check020 : jetPrefixCheck jetLayout win cert .plus ⟨4, -1, -1⟩
    (nativeDomainTarget slots req020Terms) req020Zones = true := by decide +kernel

def req021Terms : List (Fin slotCount × Int) := [(⟨21, by decide⟩, 1)]
#time def req021Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨15, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨5, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.160 s provisional; 2 exact row/activation checks.
#time theorem check021 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 1⟩
    (nativeDomainTarget slots req021Terms) req021Zones = true := by decide +kernel

def req022Terms : List (Fin slotCount × Int) := [(⟨22, by decide⟩, 1)]
#time def req022Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨17, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -1, -1⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨6, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨5, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check022 : jetPrefixCheck jetLayout win cert .plus ⟨4, 0, 0⟩
    (nativeDomainTarget slots req022Terms) req022Zones = true := by decide +kernel

def req023Terms : List (Fin slotCount × Int) := [(⟨23, by decide⟩, 1)]
#time def req023Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨26, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨16, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨-4, 2, 2⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨5, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check023 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 2⟩
    (nativeDomainTarget slots req023Terms) req023Zones = true := by decide +kernel

def req024Terms : List (Fin slotCount × Int) := [(⟨25, by decide⟩, 1)]
#time def req024Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨6, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check024 : jetPrefixCheck jetLayout win cert .plus ⟨4, -1, -1⟩
    (nativeDomainTarget slots req024Terms) req024Zones = true := by decide +kernel

def req025Terms : List (Fin slotCount × Int) := [(⟨25, by decide⟩, 1)]
#time def req025Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨16, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨6, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.160 s provisional; 2 exact row/activation checks.
#time theorem check025 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 1⟩
    (nativeDomainTarget slots req025Terms) req025Zones = true := by decide +kernel

def req026Terms : List (Fin slotCount × Int) := [(⟨26, by decide⟩, 1)]
#time def req026Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨18, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -1, -1⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨7, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨6, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check026 : jetPrefixCheck jetLayout win cert .plus ⟨4, 0, 0⟩
    (nativeDomainTarget slots req026Terms) req026Zones = true := by decide +kernel

def req027Terms : List (Fin slotCount × Int) := [(⟨27, by decide⟩, 1)]
#time def req027Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨27, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨17, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨-4, 2, 2⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨6, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check027 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 2⟩
    (nativeDomainTarget slots req027Terms) req027Zones = true := by decide +kernel

def req028Terms : List (Fin slotCount × Int) := [(⟨29, by decide⟩, 1)]
#time def req028Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨7, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check028 : jetPrefixCheck jetLayout win cert .plus ⟨4, -1, -1⟩
    (nativeDomainTarget slots req028Terms) req028Zones = true := by decide +kernel

def req029Terms : List (Fin slotCount × Int) := [(⟨29, by decide⟩, 1)]
#time def req029Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨17, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨7, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.160 s provisional; 2 exact row/activation checks.
#time theorem check029 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 1⟩
    (nativeDomainTarget slots req029Terms) req029Zones = true := by decide +kernel

def req030Terms : List (Fin slotCount × Int) := [(⟨30, by decide⟩, 1)]
#time def req030Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨19, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -1, -1⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨7, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check030 : jetPrefixCheck jetLayout win cert .plus ⟨4, 0, 0⟩
    (nativeDomainTarget slots req030Terms) req030Zones = true := by decide +kernel

def req031Terms : List (Fin slotCount × Int) := [(⟨31, by decide⟩, 1)]
#time def req031Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨28, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨18, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨-4, 2, 2⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨7, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check031 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 2⟩
    (nativeDomainTarget slots req031Terms) req031Zones = true := by decide +kernel

def req032Terms : List (Fin slotCount × Int) := [(⟨33, by decide⟩, 1)]
#time def req032Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check032 : jetPrefixCheck jetLayout win cert .plus ⟨4, -1, -1⟩
    (nativeDomainTarget slots req032Terms) req032Zones = true := by decide +kernel

def req033Terms : List (Fin slotCount × Int) := [(⟨33, by decide⟩, 1)]
#time def req033Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨18, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.160 s provisional; 2 exact row/activation checks.
#time theorem check033 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 1⟩
    (nativeDomainTarget slots req033Terms) req033Zones = true := by decide +kernel

def req034Terms : List (Fin slotCount × Int) := [(⟨34, by decide⟩, 1)]
#time def req034Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨20, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -1, -1⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨9, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check034 : jetPrefixCheck jetLayout win cert .plus ⟨4, 0, 0⟩
    (nativeDomainTarget slots req034Terms) req034Zones = true := by decide +kernel

def req035Terms : List (Fin slotCount × Int) := [(⟨35, by decide⟩, 1)]
#time def req035Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨29, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨19, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨-4, 2, 2⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check035 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 2⟩
    (nativeDomainTarget slots req035Terms) req035Zones = true := by decide +kernel

def req036Terms : List (Fin slotCount × Int) := [(⟨37, by decide⟩, 1)]
#time def req036Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨9, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check036 : jetPrefixCheck jetLayout win cert .plus ⟨4, -1, -1⟩
    (nativeDomainTarget slots req036Terms) req036Zones = true := by decide +kernel

def req037Terms : List (Fin slotCount × Int) := [(⟨37, by decide⟩, 1)]
#time def req037Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨19, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨9, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.160 s provisional; 2 exact row/activation checks.
#time theorem check037 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 1⟩
    (nativeDomainTarget slots req037Terms) req037Zones = true := by decide +kernel

def req038Terms : List (Fin slotCount × Int) := [(⟨38, by decide⟩, 1)]
#time def req038Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨21, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -1, -1⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨10, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨4, 0, 0⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨9, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check038 : jetPrefixCheck jetLayout win cert .plus ⟨4, 0, 0⟩
    (nativeDomainTarget slots req038Terms) req038Zones = true := by decide +kernel

def req039Terms : List (Fin slotCount × Int) := [(⟨39, by decide⟩, 1)]
#time def req039Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨30, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨20, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨-4, 2, 2⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨9, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check039 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 2⟩
    (nativeDomainTarget slots req039Terms) req039Zones = true := by decide +kernel

def req040Terms : List (Fin slotCount × Int) := [(⟨41, by decide⟩, 1)]
#time def req040Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -1, -1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨10, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check040 : jetPrefixCheck jetLayout win cert .plus ⟨4, -1, -1⟩
    (nativeDomainTarget slots req040Terms) req040Zones = true := by decide +kernel

def req041Terms : List (Fin slotCount × Int) := [(⟨41, by decide⟩, 1)]
#time def req041Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨20, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨10, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.160 s provisional; 2 exact row/activation checks.
#time theorem check041 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 2, 1⟩
    (nativeDomainTarget slots req041Terms) req041Zones = true := by decide +kernel

def req042Terms : List (Fin slotCount × Int) := [(⟨2, by decide⟩, 1), (⟨3, by decide⟩, -2)]
#time def req042Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check042 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req042Terms) req042Zones = true := by decide +kernel

def req043Terms : List (Fin slotCount × Int) := [(⟨6, by decide⟩, 1), (⟨7, by decide⟩, -2)]
#time def req043Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check043 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req043Terms) req043Zones = true := by decide +kernel

def req044Terms : List (Fin slotCount × Int) := [(⟨10, by decide⟩, 1), (⟨11, by decide⟩, -2)]
#time def req044Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check044 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req044Terms) req044Zones = true := by decide +kernel

def req045Terms : List (Fin slotCount × Int) := [(⟨14, by decide⟩, 1), (⟨15, by decide⟩, -2)]
#time def req045Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check045 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req045Terms) req045Zones = true := by decide +kernel

def req046Terms : List (Fin slotCount × Int) := [(⟨18, by decide⟩, 1), (⟨19, by decide⟩, -2)]
#time def req046Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨4, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check046 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req046Terms) req046Zones = true := by decide +kernel

def req047Terms : List (Fin slotCount × Int) := [(⟨22, by decide⟩, 1), (⟨23, by decide⟩, -2)]
#time def req047Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨5, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check047 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req047Terms) req047Zones = true := by decide +kernel

def req048Terms : List (Fin slotCount × Int) := [(⟨26, by decide⟩, 1), (⟨27, by decide⟩, -2)]
#time def req048Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨6, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check048 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req048Terms) req048Zones = true := by decide +kernel

def req049Terms : List (Fin slotCount × Int) := [(⟨30, by decide⟩, 1), (⟨31, by decide⟩, -2)]
#time def req049Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨7, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check049 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req049Terms) req049Zones = true := by decide +kernel

def req050Terms : List (Fin slotCount × Int) := [(⟨34, by decide⟩, 1), (⟨35, by decide⟩, -2)]
#time def req050Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check050 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req050Terms) req050Zones = true := by decide +kernel

def req051Terms : List (Fin slotCount × Int) := [(⟨38, by decide⟩, 1), (⟨39, by decide⟩, -2)]
#time def req051Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨9, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check051 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req051Terms) req051Zones = true := by decide +kernel

def req052Terms : List (Fin slotCount × Int) := [(⟨40, by decide⟩, 1), (⟨41, by decide⟩, -2)]
#time def req052Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨10, by decide⟩, -2⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check052 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req052Terms) req052Zones = true := by decide +kernel

def req053Terms : List (Fin slotCount × Int) := [(⟨1, by decide⟩, 1), (⟨3, by decide⟩, -1), (⟨41, by decide⟩, 1)]
#time def req053Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨31, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨21, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨-4, 2, 2⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨10, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 2⟩, ⟨-10, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check053 : jetPrefixCheck jetLayout win cert .infinity ⟨-10, 4, 2⟩
    (nativeDomainTarget slots req053Terms) req053Zones = true := by decide +kernel

def req054Terms : List (Fin slotCount × Int) := [(⟨37, by decide⟩, 1), (⟨39, by decide⟩, 1)]
#time def req054Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-97, 26, 13⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨33, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-97, 26, 13⟩, ⟨-4, 2, 1⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨23, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 1⟩, ⟨-4, 2, 2⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨12, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 2, 2⟩, ⟨-10, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 4, 2⟩, ⟨-70, 20, 11⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.400 s provisional; 5 exact row/activation checks.
#time theorem check054 : jetPrefixCheck jetLayout win cert .infinity ⟨-70, 20, 11⟩
    (nativeDomainTarget slots req054Terms) req054Zones = true := by decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain016

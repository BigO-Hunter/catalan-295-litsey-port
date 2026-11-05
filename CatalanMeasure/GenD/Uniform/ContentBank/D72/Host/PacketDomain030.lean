module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.DomainRows
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource030
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine003
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain030
open CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource030 (packet slots slotCount)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine003.P030 (win cert)

def pointTape : List PhysicalPoint := [.minus, .zero, .zero, .zero, .plus, .plus, .plus, .infinity, .infinity, .infinity, .infinity, .infinity]
def offsetTape : List Aff := [⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ⟨86, -68, -34⟩, ⟨97, -76, -38⟩, ⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩]
def widthTape : List Aff := [⟨0, 1, 0⟩, ⟨86, -68, -34⟩, ⟨11, -8, -4⟩, ⟨-97, 78, 39⟩, ⟨4, -3, -2⟩, ⟨-8, 7, 4⟩, ⟨8, -6, -3⟩, ⟨-10, 8, 4⟩, ⟨-60, 48, 25⟩, ⟨66, -52, -27⟩, ⟨0, 0, 1⟩, ⟨-93, 74, 36⟩]
def jetLayout : JetLayout packet := ⟨fun g => pointTape.getD g.val .zero,
  fun g => offsetTape.getD g.val ⟨0, 0, 0⟩, fun g => widthTape.getD g.val ⟨0, 0, 0⟩⟩

def req000Terms : List (Fin slotCount × Int) := [(⟨1, by decide⟩, 1)]
#time def req000Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check000 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req000Terms) req000Zones = true := by decide +kernel

def req001Terms : List (Fin slotCount × Int) := [(⟨1, by decide⟩, 1)]
#time def req001Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check001 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req001Terms) req001Zones = true := by decide +kernel

def req002Terms : List (Fin slotCount × Int) := [(⟨2, by decide⟩, 1)]
#time def req002Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨32, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check002 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req002Terms) req002Zones = true := by decide +kernel

def req003Terms : List (Fin slotCount × Int) := [(⟨3, by decide⟩, 1)]
#time def req003Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨34, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨32, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨31, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check003 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req003Terms) req003Zones = true := by decide +kernel

def req004Terms : List (Fin slotCount × Int) := [(⟨5, by decide⟩, 1)]
#time def req004Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check004 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req004Terms) req004Zones = true := by decide +kernel

def req005Terms : List (Fin slotCount × Int) := [(⟨5, by decide⟩, 1)]
#time def req005Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨4, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check005 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req005Terms) req005Zones = true := by decide +kernel

def req006Terms : List (Fin slotCount × Int) := [(⟨6, by decide⟩, 1)]
#time def req006Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨33, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check006 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req006Terms) req006Zones = true := by decide +kernel

def req007Terms : List (Fin slotCount × Int) := [(⟨7, by decide⟩, 1)]
#time def req007Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨35, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨33, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨32, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check007 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req007Terms) req007Zones = true := by decide +kernel

def req008Terms : List (Fin slotCount × Int) := [(⟨9, by decide⟩, 1)]
#time def req008Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check008 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req008Terms) req008Zones = true := by decide +kernel

def req009Terms : List (Fin slotCount × Int) := [(⟨9, by decide⟩, 1)]
#time def req009Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨5, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check009 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req009Terms) req009Zones = true := by decide +kernel

def req010Terms : List (Fin slotCount × Int) := [(⟨10, by decide⟩, 1)]
#time def req010Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨34, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check010 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req010Terms) req010Zones = true := by decide +kernel

def req011Terms : List (Fin slotCount × Int) := [(⟨11, by decide⟩, 1)]
#time def req011Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨36, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨34, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨33, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check011 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req011Terms) req011Zones = true := by decide +kernel

def req012Terms : List (Fin slotCount × Int) := [(⟨13, by decide⟩, 1)]
#time def req012Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check012 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req012Terms) req012Zones = true := by decide +kernel

def req013Terms : List (Fin slotCount × Int) := [(⟨13, by decide⟩, 1)]
#time def req013Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨6, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨4, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check013 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req013Terms) req013Zones = true := by decide +kernel

def req014Terms : List (Fin slotCount × Int) := [(⟨14, by decide⟩, 1)]
#time def req014Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨35, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨4, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check014 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req014Terms) req014Zones = true := by decide +kernel

def req015Terms : List (Fin slotCount × Int) := [(⟨15, by decide⟩, 1)]
#time def req015Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨37, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨35, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨34, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check015 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req015Terms) req015Zones = true := by decide +kernel

def req016Terms : List (Fin slotCount × Int) := [(⟨17, by decide⟩, 1)]
#time def req016Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨4, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check016 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req016Terms) req016Zones = true := by decide +kernel

def req017Terms : List (Fin slotCount × Int) := [(⟨17, by decide⟩, 1)]
#time def req017Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨7, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨5, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨4, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check017 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req017Terms) req017Zones = true := by decide +kernel

def req018Terms : List (Fin slotCount × Int) := [(⟨18, by decide⟩, 1)]
#time def req018Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨36, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨5, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨4, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check018 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req018Terms) req018Zones = true := by decide +kernel

def req019Terms : List (Fin slotCount × Int) := [(⟨19, by decide⟩, 1)]
#time def req019Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨38, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨36, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨35, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨4, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check019 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req019Terms) req019Zones = true := by decide +kernel

def req020Terms : List (Fin slotCount × Int) := [(⟨21, by decide⟩, 1)]
#time def req020Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨5, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check020 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req020Terms) req020Zones = true := by decide +kernel

def req021Terms : List (Fin slotCount × Int) := [(⟨21, by decide⟩, 1)]
#time def req021Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨6, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨5, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check021 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req021Terms) req021Zones = true := by decide +kernel

def req022Terms : List (Fin slotCount × Int) := [(⟨22, by decide⟩, 1)]
#time def req022Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨37, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨6, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨5, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check022 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req022Terms) req022Zones = true := by decide +kernel

def req023Terms : List (Fin slotCount × Int) := [(⟨23, by decide⟩, 1)]
#time def req023Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨39, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨37, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨36, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨5, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check023 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req023Terms) req023Zones = true := by decide +kernel

def req024Terms : List (Fin slotCount × Int) := [(⟨25, by decide⟩, 1)]
#time def req024Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨6, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check024 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req024Terms) req024Zones = true := by decide +kernel

def req025Terms : List (Fin slotCount × Int) := [(⟨25, by decide⟩, 1)]
#time def req025Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨9, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨7, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨6, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check025 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req025Terms) req025Zones = true := by decide +kernel

def req026Terms : List (Fin slotCount × Int) := [(⟨26, by decide⟩, 1)]
#time def req026Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨38, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨7, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨6, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check026 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req026Terms) req026Zones = true := by decide +kernel

def req027Terms : List (Fin slotCount × Int) := [(⟨27, by decide⟩, 1)]
#time def req027Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨40, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨38, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨37, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨6, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check027 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req027Terms) req027Zones = true := by decide +kernel

def req028Terms : List (Fin slotCount × Int) := [(⟨29, by decide⟩, 1)]
#time def req028Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨7, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check028 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req028Terms) req028Zones = true := by decide +kernel

def req029Terms : List (Fin slotCount × Int) := [(⟨29, by decide⟩, 1)]
#time def req029Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨10, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨7, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check029 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req029Terms) req029Zones = true := by decide +kernel

def req030Terms : List (Fin slotCount × Int) := [(⟨30, by decide⟩, 1)]
#time def req030Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨39, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨7, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check030 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req030Terms) req030Zones = true := by decide +kernel

def req031Terms : List (Fin slotCount × Int) := [(⟨31, by decide⟩, 1)]
#time def req031Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨41, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨39, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨38, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨7, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check031 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req031Terms) req031Zones = true := by decide +kernel

def req032Terms : List (Fin slotCount × Int) := [(⟨33, by decide⟩, 1)]
#time def req032Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check032 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req032Terms) req032Zones = true := by decide +kernel

def req033Terms : List (Fin slotCount × Int) := [(⟨33, by decide⟩, 1)]
#time def req033Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨11, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨9, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check033 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req033Terms) req033Zones = true := by decide +kernel

def req034Terms : List (Fin slotCount × Int) := [(⟨34, by decide⟩, 1)]
#time def req034Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨40, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨9, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check034 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req034Terms) req034Zones = true := by decide +kernel

def req035Terms : List (Fin slotCount × Int) := [(⟨35, by decide⟩, 1)]
#time def req035Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨42, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨40, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨39, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check035 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req035Terms) req035Zones = true := by decide +kernel

def req036Terms : List (Fin slotCount × Int) := [(⟨37, by decide⟩, 1)]
#time def req036Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨9, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check036 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req036Terms) req036Zones = true := by decide +kernel

def req037Terms : List (Fin slotCount × Int) := [(⟨37, by decide⟩, 1)]
#time def req037Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨12, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨10, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨9, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check037 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req037Terms) req037Zones = true := by decide +kernel

def req038Terms : List (Fin slotCount × Int) := [(⟨38, by decide⟩, 1)]
#time def req038Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨41, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨10, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨9, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check038 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req038Terms) req038Zones = true := by decide +kernel

def req039Terms : List (Fin slotCount × Int) := [(⟨39, by decide⟩, 1)]
#time def req039Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨43, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨41, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨40, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨9, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check039 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req039Terms) req039Zones = true := by decide +kernel

def req040Terms : List (Fin slotCount × Int) := [(⟨41, by decide⟩, 1)]
#time def req040Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨10, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check040 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req040Terms) req040Zones = true := by decide +kernel

def req041Terms : List (Fin slotCount × Int) := [(⟨41, by decide⟩, 1)]
#time def req041Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨13, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨11, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨10, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check041 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req041Terms) req041Zones = true := by decide +kernel

def req042Terms : List (Fin slotCount × Int) := [(⟨42, by decide⟩, 1)]
#time def req042Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨42, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨11, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨10, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check042 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req042Terms) req042Zones = true := by decide +kernel

def req043Terms : List (Fin slotCount × Int) := [(⟨43, by decide⟩, 1)]
#time def req043Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨44, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨42, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨41, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨10, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check043 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req043Terms) req043Zones = true := by decide +kernel

def req044Terms : List (Fin slotCount × Int) := [(⟨45, by decide⟩, 1)]
#time def req044Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨11, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check044 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req044Terms) req044Zones = true := by decide +kernel

def req045Terms : List (Fin slotCount × Int) := [(⟨45, by decide⟩, 1)]
#time def req045Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨14, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨12, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨11, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check045 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req045Terms) req045Zones = true := by decide +kernel

def req046Terms : List (Fin slotCount × Int) := [(⟨46, by decide⟩, 1)]
#time def req046Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨43, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨12, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨11, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check046 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req046Terms) req046Zones = true := by decide +kernel

def req047Terms : List (Fin slotCount × Int) := [(⟨47, by decide⟩, 1)]
#time def req047Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨45, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨43, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨42, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨11, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check047 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req047Terms) req047Zones = true := by decide +kernel

def req048Terms : List (Fin slotCount × Int) := [(⟨49, by decide⟩, 1)]
#time def req048Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨12, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check048 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req048Terms) req048Zones = true := by decide +kernel

def req049Terms : List (Fin slotCount × Int) := [(⟨49, by decide⟩, 1)]
#time def req049Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨15, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨13, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨12, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check049 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req049Terms) req049Zones = true := by decide +kernel

def req050Terms : List (Fin slotCount × Int) := [(⟨50, by decide⟩, 1)]
#time def req050Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨44, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨13, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨12, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check050 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req050Terms) req050Zones = true := by decide +kernel

def req051Terms : List (Fin slotCount × Int) := [(⟨51, by decide⟩, 1)]
#time def req051Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨46, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨44, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨43, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨12, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check051 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req051Terms) req051Zones = true := by decide +kernel

def req052Terms : List (Fin slotCount × Int) := [(⟨53, by decide⟩, 1)]
#time def req052Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨13, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check052 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req052Terms) req052Zones = true := by decide +kernel

def req053Terms : List (Fin slotCount × Int) := [(⟨53, by decide⟩, 1)]
#time def req053Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨16, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨14, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨13, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check053 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req053Terms) req053Zones = true := by decide +kernel

def req054Terms : List (Fin slotCount × Int) := [(⟨54, by decide⟩, 1)]
#time def req054Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨45, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨14, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨13, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check054 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req054Terms) req054Zones = true := by decide +kernel

def req055Terms : List (Fin slotCount × Int) := [(⟨55, by decide⟩, 1)]
#time def req055Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨47, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨45, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨44, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨13, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check055 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req055Terms) req055Zones = true := by decide +kernel

def req056Terms : List (Fin slotCount × Int) := [(⟨57, by decide⟩, 1)]
#time def req056Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨14, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check056 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req056Terms) req056Zones = true := by decide +kernel

def req057Terms : List (Fin slotCount × Int) := [(⟨57, by decide⟩, 1)]
#time def req057Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨17, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨15, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨14, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check057 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req057Terms) req057Zones = true := by decide +kernel

def req058Terms : List (Fin slotCount × Int) := [(⟨58, by decide⟩, 1)]
#time def req058Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨46, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨15, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨14, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check058 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req058Terms) req058Zones = true := by decide +kernel

def req059Terms : List (Fin slotCount × Int) := [(⟨59, by decide⟩, 1)]
#time def req059Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨48, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨46, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨45, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨14, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check059 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req059Terms) req059Zones = true := by decide +kernel

def req060Terms : List (Fin slotCount × Int) := [(⟨61, by decide⟩, 1)]
#time def req060Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨15, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check060 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req060Terms) req060Zones = true := by decide +kernel

def req061Terms : List (Fin slotCount × Int) := [(⟨61, by decide⟩, 1)]
#time def req061Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨18, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨16, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨15, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check061 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req061Terms) req061Zones = true := by decide +kernel

def req062Terms : List (Fin slotCount × Int) := [(⟨62, by decide⟩, 1)]
#time def req062Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨47, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨16, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨15, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check062 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req062Terms) req062Zones = true := by decide +kernel

def req063Terms : List (Fin slotCount × Int) := [(⟨63, by decide⟩, 1)]
#time def req063Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨49, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨47, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨46, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨15, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check063 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req063Terms) req063Zones = true := by decide +kernel

def req064Terms : List (Fin slotCount × Int) := [(⟨65, by decide⟩, 1)]
#time def req064Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨16, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check064 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req064Terms) req064Zones = true := by decide +kernel

def req065Terms : List (Fin slotCount × Int) := [(⟨65, by decide⟩, 1)]
#time def req065Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨19, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨17, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨16, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check065 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req065Terms) req065Zones = true := by decide +kernel

def req066Terms : List (Fin slotCount × Int) := [(⟨66, by decide⟩, 1)]
#time def req066Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨48, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨17, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨16, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check066 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req066Terms) req066Zones = true := by decide +kernel

def req067Terms : List (Fin slotCount × Int) := [(⟨67, by decide⟩, 1)]
#time def req067Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨50, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨48, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨47, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨16, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check067 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req067Terms) req067Zones = true := by decide +kernel

def req068Terms : List (Fin slotCount × Int) := [(⟨69, by decide⟩, 1)]
#time def req068Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨17, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check068 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req068Terms) req068Zones = true := by decide +kernel

def req069Terms : List (Fin slotCount × Int) := [(⟨69, by decide⟩, 1)]
#time def req069Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨20, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨18, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨17, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check069 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req069Terms) req069Zones = true := by decide +kernel

def req070Terms : List (Fin slotCount × Int) := [(⟨70, by decide⟩, 1)]
#time def req070Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨49, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨18, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨17, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check070 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req070Terms) req070Zones = true := by decide +kernel

def req071Terms : List (Fin slotCount × Int) := [(⟨71, by decide⟩, 1)]
#time def req071Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨51, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨49, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨48, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨17, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check071 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req071Terms) req071Zones = true := by decide +kernel

def req072Terms : List (Fin slotCount × Int) := [(⟨73, by decide⟩, 1)]
#time def req072Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨18, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check072 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req072Terms) req072Zones = true := by decide +kernel

def req073Terms : List (Fin slotCount × Int) := [(⟨73, by decide⟩, 1)]
#time def req073Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨21, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨19, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨18, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check073 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req073Terms) req073Zones = true := by decide +kernel

def req074Terms : List (Fin slotCount × Int) := [(⟨74, by decide⟩, 1)]
#time def req074Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨50, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨19, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨18, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check074 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req074Terms) req074Zones = true := by decide +kernel

def req075Terms : List (Fin slotCount × Int) := [(⟨75, by decide⟩, 1)]
#time def req075Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨52, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨50, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨49, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨18, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check075 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req075Terms) req075Zones = true := by decide +kernel

def req076Terms : List (Fin slotCount × Int) := [(⟨77, by decide⟩, 1)]
#time def req076Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨19, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check076 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req076Terms) req076Zones = true := by decide +kernel

def req077Terms : List (Fin slotCount × Int) := [(⟨77, by decide⟩, 1)]
#time def req077Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨22, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨20, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨19, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check077 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req077Terms) req077Zones = true := by decide +kernel

def req078Terms : List (Fin slotCount × Int) := [(⟨78, by decide⟩, 1)]
#time def req078Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨51, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨20, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨19, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check078 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req078Terms) req078Zones = true := by decide +kernel

def req079Terms : List (Fin slotCount × Int) := [(⟨79, by decide⟩, 1)]
#time def req079Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨53, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨51, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨50, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨19, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check079 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req079Terms) req079Zones = true := by decide +kernel

def req080Terms : List (Fin slotCount × Int) := [(⟨81, by decide⟩, 1)]
#time def req080Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨20, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check080 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req080Terms) req080Zones = true := by decide +kernel

def req081Terms : List (Fin slotCount × Int) := [(⟨81, by decide⟩, 1)]
#time def req081Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨23, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨21, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨20, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check081 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req081Terms) req081Zones = true := by decide +kernel

def req082Terms : List (Fin slotCount × Int) := [(⟨82, by decide⟩, 1)]
#time def req082Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨52, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨21, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨20, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check082 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req082Terms) req082Zones = true := by decide +kernel

def req083Terms : List (Fin slotCount × Int) := [(⟨83, by decide⟩, 1)]
#time def req083Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨54, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨52, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨51, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨20, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check083 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req083Terms) req083Zones = true := by decide +kernel

def req084Terms : List (Fin slotCount × Int) := [(⟨85, by decide⟩, 1)]
#time def req084Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨21, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check084 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req084Terms) req084Zones = true := by decide +kernel

def req085Terms : List (Fin slotCount × Int) := [(⟨85, by decide⟩, 1)]
#time def req085Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨24, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨22, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨21, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check085 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req085Terms) req085Zones = true := by decide +kernel

def req086Terms : List (Fin slotCount × Int) := [(⟨86, by decide⟩, 1)]
#time def req086Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨53, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨22, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨21, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check086 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req086Terms) req086Zones = true := by decide +kernel

def req087Terms : List (Fin slotCount × Int) := [(⟨87, by decide⟩, 1)]
#time def req087Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨55, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨53, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨52, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨21, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check087 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req087Terms) req087Zones = true := by decide +kernel

def req088Terms : List (Fin slotCount × Int) := [(⟨89, by decide⟩, 1)]
#time def req088Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨22, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check088 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req088Terms) req088Zones = true := by decide +kernel

def req089Terms : List (Fin slotCount × Int) := [(⟨89, by decide⟩, 1)]
#time def req089Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨25, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨23, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨22, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check089 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req089Terms) req089Zones = true := by decide +kernel

def req090Terms : List (Fin slotCount × Int) := [(⟨90, by decide⟩, 1)]
#time def req090Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨54, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨23, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨22, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check090 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req090Terms) req090Zones = true := by decide +kernel

def req091Terms : List (Fin slotCount × Int) := [(⟨91, by decide⟩, 1)]
#time def req091Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨56, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨54, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨53, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨22, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check091 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req091Terms) req091Zones = true := by decide +kernel

def req092Terms : List (Fin slotCount × Int) := [(⟨93, by decide⟩, 1)]
#time def req092Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨23, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check092 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req092Terms) req092Zones = true := by decide +kernel

def req093Terms : List (Fin slotCount × Int) := [(⟨93, by decide⟩, 1)]
#time def req093Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨26, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨24, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨23, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check093 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req093Terms) req093Zones = true := by decide +kernel

def req094Terms : List (Fin slotCount × Int) := [(⟨94, by decide⟩, 1)]
#time def req094Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨55, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨24, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨23, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check094 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req094Terms) req094Zones = true := by decide +kernel

def req095Terms : List (Fin slotCount × Int) := [(⟨95, by decide⟩, 1)]
#time def req095Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨57, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨55, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨54, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨23, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check095 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req095Terms) req095Zones = true := by decide +kernel

def req096Terms : List (Fin slotCount × Int) := [(⟨97, by decide⟩, 1)]
#time def req096Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨24, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check096 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req096Terms) req096Zones = true := by decide +kernel

def req097Terms : List (Fin slotCount × Int) := [(⟨97, by decide⟩, 1)]
#time def req097Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨27, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨25, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨24, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check097 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req097Terms) req097Zones = true := by decide +kernel

def req098Terms : List (Fin slotCount × Int) := [(⟨98, by decide⟩, 1)]
#time def req098Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨56, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨25, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨24, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check098 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req098Terms) req098Zones = true := by decide +kernel

def req099Terms : List (Fin slotCount × Int) := [(⟨99, by decide⟩, 1)]
#time def req099Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨58, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨56, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨55, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨24, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check099 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req099Terms) req099Zones = true := by decide +kernel

def req100Terms : List (Fin slotCount × Int) := [(⟨101, by decide⟩, 1)]
#time def req100Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨25, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check100 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req100Terms) req100Zones = true := by decide +kernel

def req101Terms : List (Fin slotCount × Int) := [(⟨101, by decide⟩, 1)]
#time def req101Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨28, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨26, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨25, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check101 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req101Terms) req101Zones = true := by decide +kernel

def req102Terms : List (Fin slotCount × Int) := [(⟨102, by decide⟩, 1)]
#time def req102Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨57, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨26, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨25, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check102 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req102Terms) req102Zones = true := by decide +kernel

def req103Terms : List (Fin slotCount × Int) := [(⟨103, by decide⟩, 1)]
#time def req103Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨59, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨57, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨56, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨25, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check103 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req103Terms) req103Zones = true := by decide +kernel

def req104Terms : List (Fin slotCount × Int) := [(⟨105, by decide⟩, 1)]
#time def req104Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨26, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check104 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req104Terms) req104Zones = true := by decide +kernel

def req105Terms : List (Fin slotCount × Int) := [(⟨105, by decide⟩, 1)]
#time def req105Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨29, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨27, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨26, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check105 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req105Terms) req105Zones = true := by decide +kernel

def req106Terms : List (Fin slotCount × Int) := [(⟨106, by decide⟩, 1)]
#time def req106Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨58, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨27, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨26, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check106 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req106Terms) req106Zones = true := by decide +kernel

def req107Terms : List (Fin slotCount × Int) := [(⟨107, by decide⟩, 1)]
#time def req107Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨60, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨58, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨57, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨26, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check107 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req107Terms) req107Zones = true := by decide +kernel

def req108Terms : List (Fin slotCount × Int) := [(⟨109, by decide⟩, 1)]
#time def req108Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨27, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check108 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req108Terms) req108Zones = true := by decide +kernel

def req109Terms : List (Fin slotCount × Int) := [(⟨109, by decide⟩, 1)]
#time def req109Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨30, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨28, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨27, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check109 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req109Terms) req109Zones = true := by decide +kernel

def req110Terms : List (Fin slotCount × Int) := [(⟨110, by decide⟩, 1)]
#time def req110Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨59, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨28, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨27, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check110 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req110Terms) req110Zones = true := by decide +kernel

def req111Terms : List (Fin slotCount × Int) := [(⟨111, by decide⟩, 1)]
#time def req111Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨61, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨59, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨58, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨27, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check111 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req111Terms) req111Zones = true := by decide +kernel

def req112Terms : List (Fin slotCount × Int) := [(⟨113, by decide⟩, 1)]
#time def req112Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨28, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check112 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req112Terms) req112Zones = true := by decide +kernel

def req113Terms : List (Fin slotCount × Int) := [(⟨113, by decide⟩, 1)]
#time def req113Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨31, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨29, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨28, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check113 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req113Terms) req113Zones = true := by decide +kernel

def req114Terms : List (Fin slotCount × Int) := [(⟨114, by decide⟩, 1)]
#time def req114Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨60, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨29, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨28, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check114 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req114Terms) req114Zones = true := by decide +kernel

def req115Terms : List (Fin slotCount × Int) := [(⟨115, by decide⟩, 1)]
#time def req115Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨62, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨60, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨59, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨28, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check115 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req115Terms) req115Zones = true := by decide +kernel

def req116Terms : List (Fin slotCount × Int) := [(⟨117, by decide⟩, 1)]
#time def req116Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨29, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check116 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req116Terms) req116Zones = true := by decide +kernel

def req117Terms : List (Fin slotCount × Int) := [(⟨117, by decide⟩, 1)]
#time def req117Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨32, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨30, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨29, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check117 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req117Terms) req117Zones = true := by decide +kernel

def req118Terms : List (Fin slotCount × Int) := [(⟨118, by decide⟩, 1)]
#time def req118Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨61, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨4, -3, -2⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨5, by decide⟩, ⟨30, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨4, -2, -1⟩, ⟨1, [⟨⟨6, by decide⟩, ⟨29, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check118 : jetPrefixCheck jetLayout win cert .plus ⟨4, -2, -1⟩
    (nativeDomainTarget slots req118Terms) req118Zones = true := by decide +kernel

def req119Terms : List (Fin slotCount × Int) := [(⟨119, by decide⟩, 1)]
#time def req119Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨63, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨61, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨60, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-4, 4, 2⟩, ⟨-4, 4, 3⟩, ⟨1, [⟨⟨10, by decide⟩, ⟨29, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.320 s provisional; 4 exact row/activation checks.
#time theorem check119 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 3⟩
    (nativeDomainTarget slots req119Terms) req119Zones = true := by decide +kernel

def req120Terms : List (Fin slotCount × Int) := [(⟨121, by decide⟩, 1)]
#time def req120Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨4, -3, -2⟩, ⟨1, [⟨⟨4, by decide⟩, ⟨30, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check120 : jetPrefixCheck jetLayout win cert .plus ⟨4, -3, -2⟩
    (nativeDomainTarget slots req120Terms) req120Zones = true := by decide +kernel

def req121Terms : List (Fin slotCount × Int) := [(⟨121, by decide⟩, 1)]
#time def req121Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨33, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨31, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-70, 56, 29⟩, ⟨-4, 4, 2⟩, ⟨1, [⟨⟨9, by decide⟩, ⟨30, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check121 : jetPrefixCheck jetLayout win cert .infinity ⟨-4, 4, 2⟩
    (nativeDomainTarget slots req121Terms) req121Zones = true := by decide +kernel

def req122Terms : List (Fin slotCount × Int) := [(⟨2, by decide⟩, 1), (⟨3, by decide⟩, -2)]
#time def req122Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check122 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req122Terms) req122Zones = true := by decide +kernel

def req123Terms : List (Fin slotCount × Int) := [(⟨6, by decide⟩, 1), (⟨7, by decide⟩, -2)]
#time def req123Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check123 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req123Terms) req123Zones = true := by decide +kernel

def req124Terms : List (Fin slotCount × Int) := [(⟨10, by decide⟩, 1), (⟨11, by decide⟩, -2)]
#time def req124Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check124 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req124Terms) req124Zones = true := by decide +kernel

def req125Terms : List (Fin slotCount × Int) := [(⟨14, by decide⟩, 1), (⟨15, by decide⟩, -2)]
#time def req125Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨3, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check125 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req125Terms) req125Zones = true := by decide +kernel

def req126Terms : List (Fin slotCount × Int) := [(⟨18, by decide⟩, 1), (⟨19, by decide⟩, -2)]
#time def req126Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨4, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check126 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req126Terms) req126Zones = true := by decide +kernel

def req127Terms : List (Fin slotCount × Int) := [(⟨22, by decide⟩, 1), (⟨23, by decide⟩, -2)]
#time def req127Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨5, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check127 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req127Terms) req127Zones = true := by decide +kernel

def req128Terms : List (Fin slotCount × Int) := [(⟨26, by decide⟩, 1), (⟨27, by decide⟩, -2)]
#time def req128Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨6, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check128 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req128Terms) req128Zones = true := by decide +kernel

def req129Terms : List (Fin slotCount × Int) := [(⟨30, by decide⟩, 1), (⟨31, by decide⟩, -2)]
#time def req129Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨7, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check129 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req129Terms) req129Zones = true := by decide +kernel

def req130Terms : List (Fin slotCount × Int) := [(⟨34, by decide⟩, 1), (⟨35, by decide⟩, -2)]
#time def req130Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨8, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check130 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req130Terms) req130Zones = true := by decide +kernel

def req131Terms : List (Fin slotCount × Int) := [(⟨38, by decide⟩, 1), (⟨39, by decide⟩, -2)]
#time def req131Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨9, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check131 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req131Terms) req131Zones = true := by decide +kernel

def req132Terms : List (Fin slotCount × Int) := [(⟨42, by decide⟩, 1), (⟨43, by decide⟩, -2)]
#time def req132Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨10, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check132 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req132Terms) req132Zones = true := by decide +kernel

def req133Terms : List (Fin slotCount × Int) := [(⟨46, by decide⟩, 1), (⟨47, by decide⟩, -2)]
#time def req133Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨11, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check133 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req133Terms) req133Zones = true := by decide +kernel

def req134Terms : List (Fin slotCount × Int) := [(⟨50, by decide⟩, 1), (⟨51, by decide⟩, -2)]
#time def req134Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨12, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check134 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req134Terms) req134Zones = true := by decide +kernel

def req135Terms : List (Fin slotCount × Int) := [(⟨54, by decide⟩, 1), (⟨55, by decide⟩, -2)]
#time def req135Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨13, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check135 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req135Terms) req135Zones = true := by decide +kernel

def req136Terms : List (Fin slotCount × Int) := [(⟨58, by decide⟩, 1), (⟨59, by decide⟩, -2)]
#time def req136Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨14, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check136 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req136Terms) req136Zones = true := by decide +kernel

def req137Terms : List (Fin slotCount × Int) := [(⟨62, by decide⟩, 1), (⟨63, by decide⟩, -2)]
#time def req137Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨15, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check137 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req137Terms) req137Zones = true := by decide +kernel

def req138Terms : List (Fin slotCount × Int) := [(⟨66, by decide⟩, 1), (⟨67, by decide⟩, -2)]
#time def req138Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨16, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check138 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req138Terms) req138Zones = true := by decide +kernel

def req139Terms : List (Fin slotCount × Int) := [(⟨70, by decide⟩, 1), (⟨71, by decide⟩, -2)]
#time def req139Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨17, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check139 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req139Terms) req139Zones = true := by decide +kernel

def req140Terms : List (Fin slotCount × Int) := [(⟨74, by decide⟩, 1), (⟨75, by decide⟩, -2)]
#time def req140Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨18, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check140 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req140Terms) req140Zones = true := by decide +kernel

def req141Terms : List (Fin slotCount × Int) := [(⟨78, by decide⟩, 1), (⟨79, by decide⟩, -2)]
#time def req141Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨19, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check141 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req141Terms) req141Zones = true := by decide +kernel

def req142Terms : List (Fin slotCount × Int) := [(⟨82, by decide⟩, 1), (⟨83, by decide⟩, -2)]
#time def req142Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨20, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check142 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req142Terms) req142Zones = true := by decide +kernel

def req143Terms : List (Fin slotCount × Int) := [(⟨86, by decide⟩, 1), (⟨87, by decide⟩, -2)]
#time def req143Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨21, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check143 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req143Terms) req143Zones = true := by decide +kernel

def req144Terms : List (Fin slotCount × Int) := [(⟨90, by decide⟩, 1), (⟨91, by decide⟩, -2)]
#time def req144Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨22, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check144 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req144Terms) req144Zones = true := by decide +kernel

def req145Terms : List (Fin slotCount × Int) := [(⟨94, by decide⟩, 1), (⟨95, by decide⟩, -2)]
#time def req145Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨23, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check145 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req145Terms) req145Zones = true := by decide +kernel

def req146Terms : List (Fin slotCount × Int) := [(⟨98, by decide⟩, 1), (⟨99, by decide⟩, -2)]
#time def req146Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨24, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check146 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req146Terms) req146Zones = true := by decide +kernel

def req147Terms : List (Fin slotCount × Int) := [(⟨102, by decide⟩, 1), (⟨103, by decide⟩, -2)]
#time def req147Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨25, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check147 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req147Terms) req147Zones = true := by decide +kernel

def req148Terms : List (Fin slotCount × Int) := [(⟨106, by decide⟩, 1), (⟨107, by decide⟩, -2)]
#time def req148Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨26, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check148 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req148Terms) req148Zones = true := by decide +kernel

def req149Terms : List (Fin slotCount × Int) := [(⟨110, by decide⟩, 1), (⟨111, by decide⟩, -2)]
#time def req149Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨27, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check149 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req149Terms) req149Zones = true := by decide +kernel

def req150Terms : List (Fin slotCount × Int) := [(⟨114, by decide⟩, 1), (⟨115, by decide⟩, -2)]
#time def req150Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨28, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check150 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req150Terms) req150Zones = true := by decide +kernel

def req151Terms : List (Fin slotCount × Int) := [(⟨118, by decide⟩, 1), (⟨119, by decide⟩, -2)]
#time def req151Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨29, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check151 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req151Terms) req151Zones = true := by decide +kernel

def req152Terms : List (Fin slotCount × Int) := [(⟨120, by decide⟩, 1), (⟨121, by decide⟩, -2)]
#time def req152Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, [⟨⟨0, by decide⟩, ⟨30, by decide⟩, -2⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check152 : jetPrefixCheck jetLayout win cert .minus ⟨0, 1, 0⟩
    (nativeDomainTarget slots req152Terms) req152Zones = true := by decide +kernel

def req153Terms : List (Fin slotCount × Int) := [(⟨1, by decide⟩, 1), (⟨3, by decide⟩, -1), (⟨121, by decide⟩, 1)]
#time def req153Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -68, -34⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨30, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨86, -68, -34⟩, ⟨97, -76, -38⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨29, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨97, -76, -38⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check153 : jetPrefixCheck jetLayout win cert .zero ⟨0, 2, 1⟩
    (nativeDomainTarget slots req153Terms) req153Zones = true := by decide +kernel

def req154Terms : List (Fin slotCount × Int) := [(⟨0, by decide⟩, 1), (⟨2, by decide⟩, -1), (⟨120, by decide⟩, 1)]
#time def req154Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨0, by decide⟩, -1⟩]⟩⟩,
]
-- kcost: 0.080 s provisional; 1 exact row/activation checks.
#time theorem check154 : jetPrefixCheck jetLayout win cert .infinity ⟨-10, 8, 4⟩
    (nativeDomainTarget slots req154Terms) req154Zones = true := by decide +kernel

def req155Terms : List (Fin slotCount × Int) := [(⟨117, by decide⟩, 1), (⟨119, by decide⟩, 1)]
#time def req155Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨86, -68, -34⟩, ⟨1, [⟨⟨1, by decide⟩, ⟨31, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨86, -68, -34⟩, ⟨97, -76, -38⟩, ⟨1, [⟨⟨2, by decide⟩, ⟨30, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨97, -76, -38⟩, ⟨0, 2, 1⟩, ⟨1, [⟨⟨3, by decide⟩, ⟨1, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.240 s provisional; 3 exact row/activation checks.
#time theorem check155 : jetPrefixCheck jetLayout win cert .zero ⟨0, 2, 1⟩
    (nativeDomainTarget slots req155Terms) req155Zones = true := by decide +kernel

def req156Terms : List (Fin slotCount × Int) := [(⟨116, by decide⟩, 1), (⟨118, by decide⟩, 1)]
#time def req156Zones : List (ResponseZone packet) := [
  ⟨⟨0, 0, 0⟩, ⟨-10, 8, 4⟩, ⟨1, [⟨⟨7, by decide⟩, ⟨2, by decide⟩, 1⟩]⟩⟩,
  ⟨⟨-10, 8, 4⟩, ⟨-70, 56, 29⟩, ⟨1, [⟨⟨8, by decide⟩, ⟨0, by decide⟩, 1⟩]⟩⟩,
]
-- kcost: 0.160 s provisional; 2 exact row/activation checks.
#time theorem check156 : jetPrefixCheck jetLayout win cert .infinity ⟨-70, 56, 29⟩
    (nativeDomainTarget slots req156Terms) req156Zones = true := by decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain030

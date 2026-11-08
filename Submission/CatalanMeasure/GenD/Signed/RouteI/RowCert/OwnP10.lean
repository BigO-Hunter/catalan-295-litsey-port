module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.RowCert.DataP
public import Submission.CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnAccP3

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# Chunks of the direct stream, sign P

kcost: 320 complex products and one packed product per entry, priced at each declaration.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.Davis.CircleCheb
open Set

def EwP30 : List ℤ := raw_ints% [-12738165713806004378906129517978, -32394055340988433931370057912346, -35691710713204484329625144626854, -914064805510012247306887677354, -79831641314885122858089645708653, -24033138017096659061672469555123, -104545192160903079759264739, -1645258369073731504247405270]
def EaP30 : List ℤ := raw_ints% [-271231562873141182590516561538173863020, -272225893536750770770699685945414569206, -273360168093153486020137280328689073013, -274214557586229902424923157532902847710, -274494442649559831107159695772754984683, -275628717205962112679221723137054854303, -276762991762362998827713924305143539199, -277197552299317061507400303494399282073]
def EbP30 : List ℤ := raw_ints% [205488511938525305629519317068786011057, 204169420152563078078024764459060926904, 202648236452723827394761512981033550063, 201490609322381076799387878740710495036, 201109149945554949210243943334161289698, 199551746393540642058600990601987230844, 197975593516126088859378500913861760887, 197366679651311907787645077738456837441]
def EP30 : List Ent := List.zipWith (fun w ab => (w, ab.1, ab.2)) EwP30 (List.zip EaP30 EbP30)

theorem ownP30 : ownCk DoP BoP CoP 64 256 6 8 qLP DzoP e1P e2P dlP ggP
    ((AoP.drop 420).take 8) EP30 accP29 accP30 = true := by
  decide +kernel -- kcost: 8 entries, about .9 s per entry measured on OwnP5


end CatalanMeasure.GenD.Signed.RouteI.RowCert

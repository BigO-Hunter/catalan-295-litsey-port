module

public import CatalanMeasure.GenD.Signed.RouteI.RowCert.DataP

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The bounded-variation tail of the direct stream, sign P

kcost: grid, atoms and segments about 30 s; one packed convolution of 4096 bins, 40 s and 6 GB measured.
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

def bpP : BinPar := ⟨4096, 64, 64, 64⟩
theorem grP : gridOK bpP = true := by
  decide +kernel -- kcost: 4096 square roots
theorem atP : AoP.all (atomOK bpP) = true := by
  decide +kernel -- kcost: 428 atoms, bin arithmetic
theorem sgP : GoP.all (segOK bpP) = true := by
  decide +kernel -- kcost: 595 segments
theorem keP : (AoP.all fun e => decide (2000000000000 ≤ e.1)) = true := by
  decide +kernel -- kcost: 428 comparisons
theorem kgP : keyB GoP = true := by
  decide +kernel -- kcost: 595 comparisons
theorem hvP : hvCheck2 bpP 16382 200 563933227899905044179430988557838082449255005442438856704 13 (pairsAll bpP AoP GoP) = true := by
  decide +kernel -- kcost: packed convolution of 4096 bins, 40 s measured
theorem hVP : ∀ t ∈ Ioc (0 : ℝ) 1, dirV 16382 (GoP.map segR) (AoP.map atomR) t ≤ (809204496627583 / 9007199254740992) := by
  intro t ht
  have h := hV_of bpP 16382 200 563933227899905044179430988557838082449255005442438856704 (by norm_num [bpP]) (by norm_num) grP atP sgP
    (by rw [← hvCheck2_eq (lg := 13) (by norm_num [bpP])]; exact hvP) (keyB_spec kgP) (keyB_real kgP) (keyE_real keP) t ht
  refine h.trans (le_of_eq ?_)
  norm_num [bpP]

end CatalanMeasure.GenD.Signed.RouteI.RowCert

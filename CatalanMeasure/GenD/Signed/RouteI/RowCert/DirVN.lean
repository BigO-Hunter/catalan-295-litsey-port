module

public import CatalanMeasure.GenD.Signed.RouteI.RowCert.DataN

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The bounded-variation tail of the direct stream, sign N

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

def bpN : BinPar := ⟨4096, 64, 64, 64⟩
theorem grN : gridOK bpN = true := by
  decide +kernel -- kcost: 4096 square roots
theorem atN : AoN.all (atomOK bpN) = true := by
  decide +kernel -- kcost: 277 atoms, bin arithmetic
theorem sgN : GoN.all (segOK bpN) = true := by
  decide +kernel -- kcost: 1625 segments
theorem keN : (AoN.all fun e => decide (2000000000000 ≤ e.1)) = true := by
  decide +kernel -- kcost: 277 comparisons
theorem kgN : keyB GoN = true := by
  decide +kernel -- kcost: 1625 comparisons
theorem hvN : hvCheck2 bpN 8190 200 294567751758739954027301206446030190457583191448799412224 13 (pairsAll bpN AoN GoN) = true := by
  decide +kernel -- kcost: packed convolution of 4096 bins, 40 s measured
theorem hVN : ∀ t ∈ Ioc (0 : ℝ) 1, dirV 8190 (GoN.map segR) (AoN.map atomR) t ≤ (845367988590871 / 18014398509481984) := by
  intro t ht
  have h := hV_of bpN 8190 200 294567751758739954027301206446030190457583191448799412224 (by norm_num [bpN]) (by norm_num) grN atN sgN
    (by rw [← hvCheck2_eq (lg := 13) (by norm_num [bpN])]; exact hvN) (keyB_spec kgN) (keyB_real kgN) (keyE_real keN) t ht
  refine h.trans (le_of_eq ?_)
  norm_num [bpN]

end CatalanMeasure.GenD.Signed.RouteI.RowCert

module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace SignedSpT2ZeroTransferLiteral
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end SignedSpT2ZeroTransferLiteral
set_option profiler true

def ceSignedSpT2ZeroHi : ℚ := (SignedSpT2ZeroTransferLiteral.q2 (1) 1 (-3))
def ceSignedSpT2ZeroPlainCap : ℚ := (SignedSpT2ZeroTransferLiteral.q2 (-411093350182344919644072899367097800940090430121886826095904761297540575273695) 7 (-252))
def ceSignedSpT2ZeroCap : ℚ := (SignedSpT2ZeroTransferLiteral.q2 (-8922433729115) 1 (-40))
theorem ceSignedSpT2ZeroSeriesOK : l0OK ceSignedSpT2ZeroInputTs ceSignedSpT2ZeroHi 64 = true := by decide +kernel
theorem ceSignedSpT2ZeroSeriesCancel : l0C ceSignedSpT2ZeroInputTs = 0 := by decide +kernel
theorem ceSignedSpT2ZeroSeriesPoly : polyAB (vecAdd (vecAdd ceSignedSpT2ZeroInputFq.poly (l0P ceSignedSpT2ZeroInputTs 64))
    (ceSignedSpT2ZeroPlain.poly.map (fun t => (-1 : ℚ) * t))) 0 ceSignedSpT2ZeroHi ≤ 0 := by decide +kernel
theorem ceSignedSpT2ZeroSeriesBudget : ceSignedSpT2ZeroPlainCap + 0 + l0Err ceSignedSpT2ZeroHi 64 ceSignedSpT2ZeroInputTs ≤ ceSignedSpT2ZeroCap := by decide +kernel
theorem ceSignedSpT2ZeroTransfer (h : ∀ x ∈ Ioc (0 : ℝ) (ceSignedSpT2ZeroHi : ℝ),
    fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x ≤ (ceSignedSpT2ZeroPlainCap : ℝ)) :
    ∀ x ∈ Ioc (0 : ℝ) (ceSignedSpT2ZeroHi : ℝ),
      fieldTower ceSignedSpT2ZeroInputFq (poleF ceSignedSpT2ZeroInputFq.poles) 0 x + lfieldTower ceSignedSpT2ZeroInputTs 0 x ≤ (ceSignedSpT2ZeroCap : ℝ) := by
  intro x hx
  have h0 := l0_series_sound ceSignedSpT2ZeroInputFq ceSignedSpT2ZeroPlain ceSignedSpT2ZeroInputTs ceSignedSpT2ZeroHi 64 0 ceSignedSpT2ZeroPlainCap
    ceSignedSpT2ZeroSeriesOK ceSignedSpT2ZeroSeriesCancel rfl rfl ceSignedSpT2ZeroSeriesPoly
    (Ioc (0 : ℝ) (ceSignedSpT2ZeroHi : ℝ)) (fun y hy => hy) h x hx
  exact h0.trans ((Rat.cast_le (K := ℝ)).mpr ceSignedSpT2ZeroSeriesBudget)
#print axioms ceSignedSpT2ZeroSeriesOK
#print axioms ceSignedSpT2ZeroSeriesCancel
#print axioms ceSignedSpT2ZeroSeriesPoly
#print axioms ceSignedSpT2ZeroSeriesBudget
#print axioms ceSignedSpT2ZeroTransfer

end CatalanMeasure.GenD.Signed.Data.Cells

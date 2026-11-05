module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace SignedSpT1ZeroTransferLiteral
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end SignedSpT1ZeroTransferLiteral
set_option profiler true

def ceSignedSpT1ZeroHi : ℚ := (SignedSpT1ZeroTransferLiteral.q2 (1) 1 (-3))
def ceSignedSpT1ZeroPlainCap : ℚ := (SignedSpT1ZeroTransferLiteral.q2 (-4125939391141837029615117735270763662606618314135092347322129305048042021968329) 35 (-253))
def ceSignedSpT1ZeroCap : ℚ := (SignedSpT1ZeroTransferLiteral.q2 (-4477501371827) 1 (-39))
theorem ceSignedSpT1ZeroSeriesOK : l0OK ceSignedSpT1ZeroInputTs ceSignedSpT1ZeroHi 64 = true := by decide +kernel
theorem ceSignedSpT1ZeroSeriesCancel : l0C ceSignedSpT1ZeroInputTs = 0 := by decide +kernel
theorem ceSignedSpT1ZeroSeriesPoly : polyAB (vecAdd (vecAdd ceSignedSpT1ZeroInputFq.poly (l0P ceSignedSpT1ZeroInputTs 64))
    (ceSignedSpT1ZeroPlain.poly.map (fun t => (-1 : ℚ) * t))) 0 ceSignedSpT1ZeroHi ≤ 0 := by decide +kernel
theorem ceSignedSpT1ZeroSeriesBudget : ceSignedSpT1ZeroPlainCap + 0 + l0Err ceSignedSpT1ZeroHi 64 ceSignedSpT1ZeroInputTs ≤ ceSignedSpT1ZeroCap := by decide +kernel
theorem ceSignedSpT1ZeroTransfer (h : ∀ x ∈ Ioc (0 : ℝ) (ceSignedSpT1ZeroHi : ℝ),
    fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x ≤ (ceSignedSpT1ZeroPlainCap : ℝ)) :
    ∀ x ∈ Ioc (0 : ℝ) (ceSignedSpT1ZeroHi : ℝ),
      fieldTower ceSignedSpT1ZeroInputFq (poleF ceSignedSpT1ZeroInputFq.poles) 0 x + lfieldTower ceSignedSpT1ZeroInputTs 0 x ≤ (ceSignedSpT1ZeroCap : ℝ) := by
  intro x hx
  have h0 := l0_series_sound ceSignedSpT1ZeroInputFq ceSignedSpT1ZeroPlain ceSignedSpT1ZeroInputTs ceSignedSpT1ZeroHi 64 0 ceSignedSpT1ZeroPlainCap
    ceSignedSpT1ZeroSeriesOK ceSignedSpT1ZeroSeriesCancel rfl rfl ceSignedSpT1ZeroSeriesPoly
    (Ioc (0 : ℝ) (ceSignedSpT1ZeroHi : ℝ)) (fun y hy => hy) h x hx
  exact h0.trans ((Rat.cast_le (K := ℝ)).mpr ceSignedSpT1ZeroSeriesBudget)
#print axioms ceSignedSpT1ZeroSeriesOK
#print axioms ceSignedSpT1ZeroSeriesCancel
#print axioms ceSignedSpT1ZeroSeriesPoly
#print axioms ceSignedSpT1ZeroSeriesBudget
#print axioms ceSignedSpT1ZeroTransfer

end CatalanMeasure.GenD.Signed.Data.Cells

module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace SignedSpT0ZeroTransferLiteral
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end SignedSpT0ZeroTransferLiteral
set_option profiler true

def ceSignedSpT0ZeroHi : ℚ := (SignedSpT0ZeroTransferLiteral.q2 (1) 1 (-3))
def ceSignedSpT0ZeroPlainCap : ℚ := (SignedSpT0ZeroTransferLiteral.q2 (-102988191598820542775105217547844767057059176941991823714562039501040002768079) 7 (-250))
def ceSignedSpT0ZeroCap : ℚ := (SignedSpT0ZeroTransferLiteral.q2 (-8941086631679) 1 (-40))
theorem ceSignedSpT0ZeroSeriesOK : l0OK ceSignedSpT0ZeroInputTs ceSignedSpT0ZeroHi 64 = true := by decide +kernel
theorem ceSignedSpT0ZeroSeriesCancel : l0C ceSignedSpT0ZeroInputTs = 0 := by decide +kernel
theorem ceSignedSpT0ZeroSeriesPoly : polyAB (vecAdd (vecAdd ceSignedSpT0ZeroInputFq.poly (l0P ceSignedSpT0ZeroInputTs 64))
    (ceSignedSpT0ZeroPlain.poly.map (fun t => (-1 : ℚ) * t))) 0 ceSignedSpT0ZeroHi ≤ 0 := by decide +kernel
theorem ceSignedSpT0ZeroSeriesBudget : ceSignedSpT0ZeroPlainCap + 0 + l0Err ceSignedSpT0ZeroHi 64 ceSignedSpT0ZeroInputTs ≤ ceSignedSpT0ZeroCap := by decide +kernel
theorem ceSignedSpT0ZeroTransfer (h : ∀ x ∈ Ioc (0 : ℝ) (ceSignedSpT0ZeroHi : ℝ),
    fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x ≤ (ceSignedSpT0ZeroPlainCap : ℝ)) :
    ∀ x ∈ Ioc (0 : ℝ) (ceSignedSpT0ZeroHi : ℝ),
      fieldTower ceSignedSpT0ZeroInputFq (poleF ceSignedSpT0ZeroInputFq.poles) 0 x + lfieldTower ceSignedSpT0ZeroInputTs 0 x ≤ (ceSignedSpT0ZeroCap : ℝ) := by
  intro x hx
  have h0 := l0_series_sound ceSignedSpT0ZeroInputFq ceSignedSpT0ZeroPlain ceSignedSpT0ZeroInputTs ceSignedSpT0ZeroHi 64 0 ceSignedSpT0ZeroPlainCap
    ceSignedSpT0ZeroSeriesOK ceSignedSpT0ZeroSeriesCancel rfl rfl ceSignedSpT0ZeroSeriesPoly
    (Ioc (0 : ℝ) (ceSignedSpT0ZeroHi : ℝ)) (fun y hy => hy) h x hx
  exact h0.trans ((Rat.cast_le (K := ℝ)).mpr ceSignedSpT0ZeroSeriesBudget)
#print axioms ceSignedSpT0ZeroSeriesOK
#print axioms ceSignedSpT0ZeroSeriesCancel
#print axioms ceSignedSpT0ZeroSeriesPoly
#print axioms ceSignedSpT0ZeroSeriesBudget
#print axioms ceSignedSpT0ZeroTransfer

end CatalanMeasure.GenD.Signed.Data.Cells

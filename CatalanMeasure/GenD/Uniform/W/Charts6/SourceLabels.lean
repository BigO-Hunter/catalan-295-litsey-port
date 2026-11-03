module
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceExprSound
@[expose] public section
set_option Elab.async false
/-! Exact source expressions for the complete H tiling and its centre. -/
namespace CatalanMeasure.GenD.Uniform.W.Charts6
open Polynomial Polynomial.Chebyshev
noncomputable section

def SourceExpr.hp (k : Int) : SourceExpr :=
  .add (.add (.sub (.g k) (.g (k - 1))) (.shift (.sub (.g k) (.g (k - 1)))))
    (.add (.t k) (.t (k - 1)))

def SourceExpr.hm (k : Int) : SourceExpr :=
  .add (.sub (.shift (.add (.g k) (.g (k - 1)))) (.add (.g k) (.g (k - 1))))
    (.sub (.t k) (.t (k - 1)))

def SourceExpr.tp (k : Int) : SourceExpr :=
  .add (.sub (.g k) (.shift (.g (k - 1)))) (.t (k - 1))

def SourceExpr.tm (k : Int) : SourceExpr :=
  .add (.sub (.shift (.shift (.g (k - 1)))) (.g (k - 1)))
    (.sub (.t k) (.shift (.t (k - 1))))

def SourceExpr.td (k : Int) : SourceExpr := .sub (.shift (.tp k)) (.tp k)

theorem SourceExpr.hp_polys (k : Int) : (hp k).polys =
    ((1 + X) * (U Int k - U Int (k - 1)), U Int k + U Int (k - 1)) := by
  simp only [hp, polys]
  apply Prod.ext <;> dsimp <;> ring

theorem SourceExpr.hm_polys (k : Int) : (hm k).polys =
    ((X - 1) * (U Int k + U Int (k - 1)), U Int k - U Int (k - 1)) := by
  simp only [hm, polys]
  apply Prod.ext <;> dsimp <;> ring

theorem SourceExpr.tp_polys (k : Int) : (tp k).polys = (T Int k, U Int (k - 1)) := by
  simp only [tp, polys, T_eq_U_sub_X_mul_U]
  apply Prod.ext <;> dsimp <;> ring

theorem SourceExpr.tm_polys (k : Int) : (tm k).polys =
    ((X ^ 2 - 1) * U Int (k - 1), T Int k) := by
  simp only [tm, polys, T_eq_U_sub_X_mul_U]
  apply Prod.ext <;> dsimp <;> ring

theorem SourceExpr.td_eval (G T : Int → Int → Rat) (k S : Int) :
    (td k).eval G T S = (tp k).eval G T (S - 1) - (tp k).eval G T S := rfl

end
end CatalanMeasure.GenD.Uniform.W.Charts6

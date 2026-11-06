module
public import CatalanMeasure.GenD.Signed.Data.Trial72.RowsCaps72
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RowsBudget72
open Set CatalanMeasure.Signed
open RowsCaps72 NearBudgetBridges72 NearBudgetCorrected72 Inputs72 Davis.ScalarInstance72
noncomputable section

def base (i : Fin 2) (k α : ℝ) : ℝ :=
  interpCInf (I.αA i) (I.αB i) (cP i α) (rA i) (rB i) (κc i) α +
    fixLog2 (I.epsSplit i) α*Real.log 2 +
    k*chord (I.αA i) (I.αB i) (SnA i) (SnB i) α +
    (1-k-α)*chord (I.αA i) (I.αB i) (SpA i) (SpB i) α +
    (1-α)*chord (I.αA i) (I.αB i) (SyA i) (SyB i) α

def rhs (α : ℝ) : ℝ := (-I.target+Real.log 2/2)+I.cost*α

def cap (i : Fin 2) (c d β : ℝ) : ℝ :=
  zbCap ((capE i).toS (I.αA i) (I.αB i)) c d β

private theorem mix_le {c d β a b s : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hβ : 0 ≤ β) :
    c*a+d*b+β*s ≤ (c+d+β)*max a (max b s) := by
  have ha := mul_le_mul_of_nonneg_left (le_max_left a (max b s)) hc
  have hb := mul_le_mul_of_nonneg_left ((le_max_left b s).trans (le_max_right a (max b s))) hd
  have hs := mul_le_mul_of_nonneg_left ((le_max_right b s).trans (le_max_right a (max b s))) hβ
  nlinarith only [ha,hb,hs]


private theorem point0 (k c d β : ℝ) (hk : k ∈ Icc (0 : ℝ) (1/2))
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hb : 0 ≤ β)
    (hα : c+d+β ∈ Icc (0 : ℝ) (1/200 : ℝ)) :
    base 0 k (c+d+β) + cap 0 c d β ≤ rhs (c+d+β) - reserve := by
  let α : ℝ := c+d+β
  let x : ℝ := interpL (0) (1/200) α
  have ha : a0 x = α := alpha0 hα
  have hx : x ∈ Icc (0 : ℝ) 1 := ⟨interpL_nonneg _ _ _,interpL_le_one _ _ _⟩
  have hβ : β ∈ Icc 0 (a0 x) := ⟨hb,by rw [ha]; dsimp [α]; linarith⟩
  have h0 := actual0_low hx hβ
  have h1 := actual0_high hx hβ
  have hA : core0 k x (Real.log 2) =
      (1-2*k)*core0 0 x (Real.log 2) + 2*k*core0 (1/2) x (Real.log 2) := by
    unfold core0
    ring
  have hB := mul_le_mul_of_nonneg_left h0 (show 0 ≤ 1-2*k by linarith [hk.2])
  have hC := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2*k by linarith [hk.1])
  have hn : core0 k x (Real.log 2) +
      a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + correction0 x β ≤ -reserve := by
    rw [hA]
    norm_num at hB hC
    nlinarith only [hB,hC]
  have hm := mix_le (a := markN0 x) (b := markP0 x) (s := markS0 x) hc hd hb
  have hz : cap 0 c d β =
      c*markN0 x+d*markP0 x+β*markS0 x+correction0 x β := by
    change zbCap (cap0.toS (0) (1/200)) c d β = _
    rw [zb0_eq]
    simp only [correction0,ha] <;> rfl
  have hf : core0 k x (Real.log 2) = base 0 k α - rhs α := core0_eq k hα
  rw [hf,ha] at hn
  rw [hz]
  change base 0 k α + _ ≤ rhs α - reserve
  nlinarith only [hn,hm]


private theorem point1 (k c d β : ℝ) (hk : k ∈ Icc (0 : ℝ) (1/2))
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hb : 0 ≤ β)
    (hα : c+d+β ∈ Icc (1/200 : ℝ) (1/16 : ℝ)) :
    base 1 k (c+d+β) + cap 1 c d β ≤ rhs (c+d+β) - reserve := by
  let α : ℝ := c+d+β
  let x : ℝ := interpL (1/200) (1/16) α
  have ha : a1 x = α := alpha1 hα
  have hx : x ∈ Icc (0 : ℝ) 1 := ⟨interpL_nonneg _ _ _,interpL_le_one _ _ _⟩
  have hβ : β ∈ Icc 0 (a1 x) := ⟨hb,by rw [ha]; dsimp [α]; linarith⟩
  have h0 := actual1_low hx hβ
  have h1 := actual1_high hx hβ
  have hA : core1 k x (Real.log 2) =
      (1-2*k)*core1 0 x (Real.log 2) + 2*k*core1 (1/2) x (Real.log 2) := by
    unfold core1
    ring
  have hB := mul_le_mul_of_nonneg_left h0 (show 0 ≤ 1-2*k by linarith [hk.2])
  have hC := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2*k by linarith [hk.1])
  have hn : core1 k x (Real.log 2) +
      a1 x * max (markN1 x) (max (markP1 x) (markS1 x)) + correction1 x β ≤ -reserve := by
    rw [hA]
    norm_num at hB hC
    nlinarith only [hB,hC]
  have hm := mix_le (a := markN1 x) (b := markP1 x) (s := markS1 x) hc hd hb
  have hz : cap 1 c d β =
      c*markN1 x+d*markP1 x+β*markS1 x+correction1 x β := by
    change zbCap (cap1.toS (1/200) (1/16)) c d β = _
    rw [zb1_eq]
    simp only [correction1,ha] <;> rfl
  have hf : core1 k x (Real.log 2) = base 1 k α - rhs α := core1_eq k hα
  rw [hf,ha] at hn
  rw [hz]
  change base 1 k α + _ ≤ rhs α - reserve
  nlinarith only [hn,hm]


theorem point (i : Fin 2) (k c d β : ℝ) (hk : k ∈ Icc (0 : ℝ) (1/2))
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hb : 0 ≤ β) (hα : c+d+β ∈ Icc (I.lo i) (I.hi i)) :
    base i k (c+d+β) + cap i c d β ≤ rhs (c+d+β)-reserve := by
  fin_cases i
  · exact point0 k c d β hk hc hd hb hα
  · exact point1 k c d β hk hc hd hb hα

def capSet (i : Fin 2) (α : ℝ) : Set ℝ :=
  {z | ∃ c d β : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ β ∧ c+d+β=α ∧ z=cap i c d β}

def zb (i : Fin 2) (α : ℝ) : ℝ := sSup (capSet i α)

private theorem bound (i : Fin 2) {α k : ℝ} (hα : α ∈ Icc (I.lo i) (I.hi i))
    (hk : k ∈ Icc (0 : ℝ) (1/2)) :
    ∀ z ∈ capSet i α, z ≤ rhs α-reserve-base i k α := by
  intro z hz
  obtain ⟨c,d,β,hc,hd,hb,he,rfl⟩ := hz
  have h := point i k c d β hk hc hd hb (by rw [he]; exact hα)
  rw [he] at h
  linarith only [h]

theorem hZB (i : Fin 2) (c d β : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hb : 0 ≤ β)
    (hl : I.lo i ≤ c+d+β) (hh : c+d+β ≤ I.hi i) :
    cap i c d β ≤ zb i (c+d+β) := by
  apply le_csSup
  · exact ⟨_,bound i ⟨hl,hh⟩ (show (0 : ℝ) ∈ Icc 0 (1/2) by constructor <;> norm_num)⟩
  · exact ⟨c,d,β,hc,hd,hb,rfl,rfl⟩

theorem budget (i : Fin 2) {α k : ℝ} (hα : α ∈ Icc (I.lo i) (I.hi i))
    (hk : k ∈ Icc (0 : ℝ) (1/2)) :
    base i k α + zb i α ≤ rhs α := by
  have h0 : 0 ≤ α := (I.hlo0 i).trans hα.1
  have hn : (capSet i α).Nonempty := ⟨cap i α 0 0, α,0,0,h0,le_rfl,le_rfl,by ring,rfl⟩
  have hh := csSup_le hn (bound i hα hk)
  have hr : 0 ≤ reserve := by norm_num [reserve]
  unfold zb
  linarith only [hh,hr]

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RowsBudget72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RowsBudget72.budget

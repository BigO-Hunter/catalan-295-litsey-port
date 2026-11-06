module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core079
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core080
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core081
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core082
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core083
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core084
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core085
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core086
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core087
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core088
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core089
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core090
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core091
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core092
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core093
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core094
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell080 : ∀ y ∈ Icc ((((-2231871523344291 : ℚ) / 5497558138880000) : ℚ) : ℝ) ((((-1105263583190019 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P079Lo : ℝ) (ceSignedSnEntryT2P079Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P079Lo, ceSignedSnEntryT2P079Hi, SignedSnEntryT2Core079Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P079Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core079Literal.q2] at h ⊢
  exact h

private theorem cell081 : ∀ y ∈ Icc ((((-1105263583190019 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-52061525614863 : ℚ) / 137438953472000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P080Lo : ℝ) (ceSignedSnEntryT2P080Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P080Lo, ceSignedSnEntryT2P080Hi, SignedSnEntryT2Core080Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P080Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core080Literal.q2] at h ⊢
  exact h

private theorem cell082 : ∀ y ∈ Icc ((((-52061525614863 : ℚ) / 137438953472000) : ℚ) : ℝ) ((((-1019886155333007 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P081Lo : ℝ) (ceSignedSnEntryT2P081Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P081Lo, ceSignedSnEntryT2P081Hi, SignedSnEntryT2Core081Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P081Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core081Literal.q2] at h ⊢
  exact h

private theorem cell083 : ∀ y ∈ Icc ((((-1019886155333007 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-499270899184377 : ℚ) / 1374389534720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P082Lo : ℝ) (ceSignedSnEntryT2P082Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P082Lo, ceSignedSnEntryT2P082Hi, SignedSnEntryT2Core082Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P082Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core082Literal.q2] at h ⊢
  exact h

private theorem cell084 : ∀ y ∈ Icc ((((-499270899184377 : ℚ) / 1374389534720000) : ℚ) : ℝ) ((((-395147847954651 : ℚ) / 1099511627776000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P083Lo : ℝ) (ceSignedSnEntryT2P083Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P083Lo, ceSignedSnEntryT2P083Hi, SignedSnEntryT2Core083Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P083Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core083Literal.q2] at h ⊢
  exact h

private theorem cell085 : ∀ y ∈ Icc ((((-395147847954651 : ℚ) / 1099511627776000) : ℚ) : ℝ) ((((-977197441404501 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P084Lo : ℝ) (ceSignedSnEntryT2P084Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P084Lo, ceSignedSnEntryT2P084Hi, SignedSnEntryT2Core084Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P084Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core084Literal.q2] at h ⊢
  exact h

private theorem cell086 : ∀ y ∈ Icc ((((-977197441404501 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-119481635555031 : ℚ) / 343597383680000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P085Lo : ℝ) (ceSignedSnEntryT2P085Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P085Lo, ceSignedSnEntryT2P085Hi, SignedSnEntryT2Core085Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P085Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core085Literal.q2] at h ⊢
  exact h

private theorem cell087 : ∀ y ∈ Icc ((((-119481635555031 : ℚ) / 343597383680000) : ℚ) : ℝ) ((((-70491826805229 : ℚ) / 219902325555200) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P086Lo : ℝ) (ceSignedSnEntryT2P086Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P086Lo, ceSignedSnEntryT2P086Hi, SignedSnEntryT2Core086Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P086Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core086Literal.q2] at h ⊢
  exact h

private theorem cell088 : ∀ y ∈ Icc ((((-70491826805229 : ℚ) / 219902325555200) : ℚ) : ℝ) ((((-849131299618983 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P087Lo : ℝ) (ceSignedSnEntryT2P087Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P087Lo, ceSignedSnEntryT2P087Hi, SignedSnEntryT2Core087Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P087Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core087Literal.q2] at h ⊢
  exact h

private theorem cell089 : ∀ y ∈ Icc ((((-849131299618983 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-82778694265473 : ℚ) / 274877906944000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P088Lo : ℝ) (ceSignedSnEntryT2P088Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P088Lo, ceSignedSnEntryT2P088Hi, SignedSnEntryT2Core088Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P088Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core088Literal.q2] at h ⊢
  exact h

private theorem cell090 : ∀ y ∈ Icc ((((-82778694265473 : ℚ) / 274877906944000) : ℚ) : ℝ) ((((-49068639295389 : ℚ) / 171798691840000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P089Lo : ℝ) (ceSignedSnEntryT2P089Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P089Lo, ceSignedSnEntryT2P089Hi, SignedSnEntryT2Core089Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P089Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core089Literal.q2] at h ⊢
  exact h

private theorem cell091 : ∀ y ∈ Icc ((((-49068639295389 : ℚ) / 171798691840000) : ℚ) : ℝ) ((((-371204757398859 : ℚ) / 1374389534720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P090Lo : ℝ) (ceSignedSnEntryT2P090Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P090Lo, ceSignedSnEntryT2P090Hi, SignedSnEntryT2Core090Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P090Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core090Literal.q2] at h ⊢
  exact h

private theorem cell092 : ∀ y ∈ Icc ((((-371204757398859 : ℚ) / 1374389534720000) : ℚ) : ℝ) ((((-2905604988298113 : ℚ) / 10995116277760000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P091Lo : ℝ) (ceSignedSnEntryT2P091Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P091Lo, ceSignedSnEntryT2P091Hi, SignedSnEntryT2Core091Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P091Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core091Literal.q2] at h ⊢
  exact h

private theorem cell093 : ∀ y ∈ Icc ((((-2905604988298113 : ℚ) / 10995116277760000) : ℚ) : ℝ) ((((-144213031566693 : ℚ) / 549755813888000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P092Lo : ℝ) (ceSignedSnEntryT2P092Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P092Lo, ceSignedSnEntryT2P092Hi, SignedSnEntryT2Core092Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P092Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core092Literal.q2] at h ⊢
  exact h

private theorem cell094 : ∀ y ∈ Icc ((((-144213031566693 : ℚ) / 549755813888000) : ℚ) : ℝ) ((((-174930200217303 : ℚ) / 687194767360000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P093Lo : ℝ) (ceSignedSnEntryT2P093Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P093Lo, ceSignedSnEntryT2P093Hi, SignedSnEntryT2Core093Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P093Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core093Literal.q2] at h ⊢
  exact h

private theorem cell095 : ∀ y ∈ Icc ((((-174930200217303 : ℚ) / 687194767360000) : ℚ) : ℝ) ((((-1250031102988653 : ℚ) / 5497558138880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P094Lo : ℝ) (ceSignedSnEntryT2P094Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P094Lo, ceSignedSnEntryT2P094Hi, SignedSnEntryT2Core094Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P094Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core094Literal.q2] at h ⊢
  exact h

theorem cover005 : ∀ y ∈ Icc ((((-2231871523344291 : ℚ) / 5497558138880000) : ℚ) : ℝ) ((((-1250031102988653 : ℚ) / 5497558138880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell080 cell081) (cover_union cell082 cell083)) (cover_union (cover_union cell084 cell085) (cover_union cell086 cell087))) (cover_union (cover_union (cover_union cell088 cell089) (cover_union cell090 cell091)) (cover_union (cover_union cell092 cell093) (cover_union cell094 cell095))))
#print axioms cover005
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover

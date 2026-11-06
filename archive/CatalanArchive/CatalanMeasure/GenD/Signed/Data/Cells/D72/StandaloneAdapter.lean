module
public import CatalanMeasure.GenD.Signed.Data.Trial.Hid
public import CatalanMeasure.GenD.Analytic.FirstGlue
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter
open Set CatalanMeasure.CellCert CatalanMeasure.Cert
open CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Analytic
open OAI.InternalCatalan
noncomputable section
/-- Raw frozen first p is half the analytic first trial sequence. -/
def sequence (d : SeqQ) := tseq (fQ d.f) (d.tail.map TailQ.toC)
def tailS (d : SeqQ) := sConst (d.tail.map TailQ.toC)
def tailT (d : SeqQ) := tConst (d.tail.map TailQ.toC)
def S (d : SeqQ) := seqSFQ (polyS d.f) d.tail
def T (d : SeqQ) := seqTFQ (polyT d.f) d.tail

theorem sequenceS (d : SeqQ) (h : TailOK (d.tail.map TailQ.toC)) {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialS (sequence d) x = fval (S d) x + tailS d := by
  rw [S, fval_seqS]
  have hh := barrierTrialS_tseq (fQ_supp d.f) h hx
  simpa [sequence, tailS, SeqQ.form, SeqForm.Sform] using hh

theorem sequenceT (d : SeqQ) (h : TailOK (d.tail.map TailQ.toC)) {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialT (sequence d) x = fval (T d) x + tailT d := by
  rw [T, fval_seqT]
  have hh := barrierTrialT_tseq (fQ_supp d.f) h hx
  simpa [sequence, tailT, SeqQ.form, SeqForm.Tform] using hh

theorem barrierT_two (p : ℕ → ℝ) (x : ℝ) :
    barrierTrialT (fun k => 2 * p k) x = 2 * barrierTrialT p x := by
  unfold barrierTrialT
  rw [← tsum_mul_left]
  congr 1
  funext k
  ring

def firstRowQ (p v : SeqQ) : FieldQ := fqSum
  [logFQ (3/8) 0, logFQ (1/9) 1, sqFQ (61/72), fqScale (-4) (T p), fqScale (-1) (S v)]
def columnQ (v : SeqQ) : FieldQ := fqSum
  [logFQ (11/72) 0, logFQ (1/18) 1, fqScale 2 (T v)]
def referenceRowQ (p v : SeqQ) : FieldQ := fqSum
  [logFQ (3/8) 0, logFQ (1/9) 1, sqFQ (97/72), fqScale (-4) (T p), fqScale (-1) (S v)]
def residualQ (p : SeqQ) : FieldQ := fqSum [sqFQ (11/12), fqScale (-2) (T p)]
def nearQ (p1 : ℚ) : FieldQ := fqSum [sqFQ (11/12), logFQ (59/72) 0, fqPoly [0,-p1]]
def rowK (p v : SeqQ) : ℝ := -4*tailT p-tailS v
def columnK (v : SeqQ) : ℝ := 2*tailT v
def residualK (p : SeqQ) : ℝ := -2*tailT p
def firstRational (x : ℝ) : ℝ := (8/5)*(1/6-2*x^2/(1+x^2))

private theorem log_sub_one (x : ℝ) : Real.log |x-1| = Real.log (1-x) := by
  rw [abs_sub_comm, Real.log_abs]

theorem firstRowIdentity (p v : SeqQ)
    (hp : TailOK (p.tail.map TailQ.toC)) (hv : TailOK (v.tail.map TailQ.toC))
    {x : ℝ} (hx : |x| ≤ 1) :
    firstRowFieldG (3/8) (1/9) (97/72-1/2) (8/5) (1/6)
      (fun k => 2*sequence p k) (sequence v) x =
      fval (firstRowQ p v) x + rowK p v + firstRational x := by
  unfold firstRowFieldG firstRowReg
  rw [barrierT_two, sequenceT p hp hx, sequenceS v hv hx]
  simp only [firstRowQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, fval_log, fval_sq, fval_scale, rowK, firstRational]
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, sub_zero, log_sub_one]
  ring

theorem columnIdentity (v : SeqQ) (hv : TailOK (v.tail.map TailQ.toC))
    {x : ℝ} (hx : |x| ≤ 1) :
    colFieldG (11/72) (1/18) (sequence v) x = fval (columnQ v) x + columnK v := by
  unfold colFieldG colRegG
  rw [sequenceT v hv hx]
  simp only [columnQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, fval_log, fval_scale, columnK]
  norm_num only [Rat.cast_div, Rat.cast_ofNat, sub_zero, log_sub_one, Real.log_abs]
  have hl : Real.log (x-1) = Real.log (1-x) := by
    have he : x-1 = -(1-x) := by ring
    rw [he, Real.log_neg_eq_log]
  rw [hl]
  ring

theorem referenceRowIdentity (p v : SeqQ)
    (hp : TailOK (p.tail.map TailQ.toC)) (hv : TailOK (v.tail.map TailQ.toC))
    {x : ℝ} (hx : |x| ≤ 1) :
    rowFieldG (3/8) (1/9) (97/72) (sequence p) (sequence v) x =
      fval (referenceRowQ p v) x + rowK p v := by
  unfold rowFieldG rowRegG
  rw [sequenceT p hp hx, sequenceS v hv hx]
  simp only [referenceRowQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, fval_log, fval_sq, fval_scale, rowK]
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, sub_zero, log_sub_one]
  ring

theorem residualIdentity (p : SeqQ) (hp : TailOK (p.tail.map TailQ.toC))
    {x : ℝ} (hx : |x| ≤ 1) :
    resFieldGen (11/12) (sequence p) x = fval (residualQ p) x + residualK p := by
  unfold resFieldGen
  rw [sequenceT p hp hx]
  simp only [residualQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, fval_sq, fval_scale, residualK]
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  ring

theorem nearIdentity (p1 : ℚ) (x : ℝ) :
    -(11/12)*Real.log (1+x^2)+(59/72)*Real.log x-(p1:ℝ)*x = fval (nearQ p1) x := by
  simp only [nearQ, fval_sum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, fval_sq, fval_log, fval_poly, polyTow_zero_cons, polyTow_zero_nil]
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, sub_zero, Real.log_abs]
  ring
def rationalSeries (N : ℕ) (x : ℝ) : ℝ :=
  (8/5)*(1/6-2+∑ j ∈ Finset.range (N+1), ((1-x^2)/2)^j)

/-- Uniform positive remainder; the same dyadic polynomial is used for every first-row cell. -/
theorem rationalSeries_upper {x : ℝ} (hx : |x| ≤ 1) :
    firstRational x ≤ rationalSeries 32 x + (8/5)*(1/2:ℝ)^32 := by
  let q : ℝ := (1-x^2)/2
  have hx2 : x^2 ≤ 1 := by
    rcases abs_le.mp hx with ⟨hl,hu⟩
    nlinarith [sq_nonneg (x+1), sq_nonneg (x-1)]
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q ≤ (1/2:ℝ) := by dsimp [q]; nlinarith [sq_nonneg x]
  have hd : 0 < 1-q := by linarith
  have hg := geom_sum_mul_of_le_one (show q ≤ 1 by linarith) 33
  have hp : q^33 ≤ (1/2:ℝ)^33 := pow_le_pow_left₀ hq0 hq1 33
  have ht := mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ 1-q by linarith)
    (show 0 ≤ (1/2:ℝ)^32 by positivity)
  have hb : 1/(1-q) ≤ (∑ j ∈ Finset.range 33, q^j)+(1/2:ℝ)^32 := by
    apply (div_le_iff₀ hd).2
    norm_num at hp ht ⊢
    nlinarith [hg]
  have he : firstRational x = (8/5)*(1/6-2+1/(1-q)) := by
    dsimp [firstRational,q]
    have hh : 1+x^2 ≠ 0 := by positivity
    have heq : 1-(1-x^2)/2 = (1+x^2)/2 := by ring
    rw [heq]
    field_simp [hh]
    <;> ring
  rw [he]
  change (8/5)*(1/6-2+1/(1-q)) ≤
    (8/5)*(1/6-2+(∑ j ∈ Finset.range 33, q^j))+(8/5)*(1/2:ℝ)^32
  linarith [hb]

def rationalPoly : List ℚ := qlistC (raw_ints% [429496729, 1610612736, 0, 1, -4294967279, 1342177280, 0, 1, 858993403, 268435456, 0, 1, -4294964287, 1342177280, 0, 1, 4294943827, 1342177280, 0, 1, -4294825159, 1342177280, 0, 1, 858854275, 268435456, 0, 1, -4292135351, 1342177280, 0, 1, 4285193273, 1342177280, 0, 1, -4265909723, 1342177280, 0, 1, 4219629203, 1342177280, 0, 1, -4122860843, 1342177280, 0, 1, 3945452183, 1342177280, 0, 1, -3658868963, 1342177280, 0, 1, 3249464363, 1342177280, 0, 1, -2730885203, 1342177280, 0, 1, 8, 5, 0, 1, -1564082093, 1342177280, 0, 1, 1045502933, 1342177280, 0, 1, -636098333, 1342177280, 0, 1, 349515113, 1342177280, 0, 1, -172106453, 1342177280, 0, 1, 75338093, 1342177280, 0, 1, -29057573, 1342177280, 0, 1, 9774023, 1342177280, 0, 1, -566389, 268435456, 0, 1, 695921, 1342177280, 0, 1, -142137, 1342177280, 0, 1, 23469, 1342177280, 0, 1, -3009, 1342177280, 0, 1, 281, 1342177280, 0, 1, -17, 1342177280, 0, 1, 1, 2684354560])

theorem rationalPoly_eval (x : ℝ) : polyTow rationalPoly 0 x = rationalSeries 32 x := by
  norm_num [rationalPoly, qlistC, rationalSeries, Finset.sum_range_succ,
    polyTow_zero_cons, polyTow_zero_nil]
  ring

theorem firstRational_upper_poly {x : ℝ} (hx : |x| ≤ 1) :
    firstRational x ≤ polyTow rationalPoly 0 x + (8/5)*(1/2:ℝ)^32 := by
  rw [rationalPoly_eval]
  exact rationalSeries_upper hx

def firstApproxQ (p v : SeqQ) : FieldQ := fqAdd (firstRowQ p v) (fqPoly rationalPoly)

theorem firstRow_lift (p v : SeqQ)
    (hp : TailOK (p.tail.map TailQ.toC)) (hv : TailOK (v.tail.map TailQ.toC))
    (cap K : ℝ) (hK : rowK p v ≤ K) {x : ℝ} (hx : |x| ≤ 1)
    (h : fval (firstApproxQ p v) x ≤ cap-K-(8/5)*(1/2:ℝ)^32) :
    firstRowFieldG (3/8) (1/9) (97/72-1/2) (8/5) (1/6)
      (fun k => 2*sequence p k) (sequence v) x ≤ cap := by
  rw [firstRowIdentity p v hp hv hx]
  have hr := firstRational_upper_poly hx
  simp only [firstApproxQ, fval_add, fval_poly] at h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter

#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter.sequenceS
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter.sequenceT
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter.barrierT_two
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter.firstRowIdentity
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter.columnIdentity
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter.referenceRowIdentity
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter.residualIdentity
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter.nearIdentity

#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter.rationalSeries_upper

#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter.rationalPoly_eval
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter.firstRational_upper_poly
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter.firstRow_lift

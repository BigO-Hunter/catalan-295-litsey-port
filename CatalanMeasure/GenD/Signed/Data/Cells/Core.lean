module

public import CatalanMeasure.GenD.Signed.LogEval

@[expose] public section

/-!
# Field cell certificates, the generic layer (Theorem A, Phase 2 data lane D1)

What a data module needs, and nothing field-specific:

* `poleF poles`: the pole potential `y ↦ Σ_q Re[ρ_q log (y - p_q)]` (derivative `Σ qt q 0`), with
  `hasDerivAt_poleF` (real poles carry real weights).
* `blockOK` (a `Bool`) and `blockFacts_of_ok`: the block-level facts used by every cell of a block: the
  order-`M` tail bound `|f^(M)|/M! ≤ BM` on `[blo, bhi]` (`blockTailCheck_sound`, with the logarithm
  bounds `Lb = 7k/10` from `2^-k ≤ |x - e| ≤ 2^k`), the block avoids every logarithmic singularity and
  every pole, and the derivative of the pole potential.
* `anchorCheck`: the direct anchor `Enc (F c) A` from `logAbsQ`, `poleLogQ` (about 110 bits).
* `cellStep` and `cellStep_sound`: one cell of a block: `fieldCellCheck` (exact coefficients to order
  `|Bl| + 2`, remainder `BM`) **and** the chaining step to the next centre
  (`Enc (F c) A → Enc (F c') A'`) computed from the same coefficient vector, so that only one anchor
  per block is evaluated from logarithms.
-/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.Cert (qabs)

/-! ### 1. The pole potential -/

noncomputable def poleF (poles : List PoleR) (y : ℝ) : ℝ :=
  (poles.map (fun q => (q.rho * Complex.log ((y : ℂ) - q.pc)).re)).sum

theorem re_clog_real (q : PoleR) (hpi : q.pi = 0) (hri : q.ri = 0) (y : ℝ) :
    (q.rho * Complex.log ((y : ℂ) - q.pc)).re = (q.rr : ℝ) * Real.log |y - q.pr| := by
  have h1 : ((y : ℂ) - q.pc) = ((y - q.pr : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [PoleR.pc, hpi]
  have h2 : q.rho = ((q.rr : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [PoleR.rho, hri]
  rw [h1, h2, Complex.re_ofReal_mul, Complex.log_re, Complex.norm_real, Real.norm_eq_abs]

theorem hasDerivAt_pole_term (q : PoleR) (hreal : q.pi = 0 → q.ri = 0) (x : ℝ)
    (hx : (x : ℂ) ≠ q.pc) :
    HasDerivAt (fun y : ℝ => (q.rho * Complex.log ((y : ℂ) - q.pc)).re) (qt q 0 x) x := by
  by_cases hpi : q.pi = 0
  · have hri := hreal hpi
    have hxp : x ≠ (q.pr : ℝ) := by
      intro h
      apply hx
      apply Complex.ext <;> simp [PoleR.pc, hpi, h]
    have := hasDerivAt_log_abs_sub q.rr q.pr x hxp
    have hq : q = ⟨q.rr, 0, q.pr, 0⟩ := by
      cases q; simp_all
    have e : (fun y : ℝ => (q.rho * Complex.log ((y : ℂ) - q.pc)).re) =
        fun y => (q.rr : ℝ) * Real.log |y - q.pr| := by
      funext y; exact re_clog_real q hpi hri y
    rw [e]
    rw [hq] at *
    simpa using this
  · exact hasDerivAt_re_clog q hpi x

theorem hasDerivAt_poleF (poles : List PoleR) (hreal : ∀ q ∈ poles, q.pi = 0 → q.ri = 0)
    (x : ℝ) (hx : ∀ q ∈ poles, (x : ℂ) ≠ q.pc) :
    HasDerivAt (poleF poles) ((poles.map (fun q => qt q 0 x)).sum) x := by
  induction poles with
  | nil =>
    have e0 : poleF [] = fun _ => (0 : ℝ) := by funext y; simp [poleF]
    rw [e0]
    simpa using hasDerivAt_const x (0 : ℝ)
  | cons q qs ih =>
    have h1 := hasDerivAt_pole_term q (hreal q (by simp)) x (hx q (by simp))
    have h2 := ih (fun r hr => hreal r (by simp [hr])) (fun r hr => hx r (by simp [hr]))
    have h3 := h1.add h2
    have e : poleF (q :: qs) = fun y : ℝ =>
        (q.rho * Complex.log ((y : ℂ) - q.pc)).re + poleF qs y := by
      funext y; simp [poleF]
    rw [e, List.map_cons, List.sum_cons]
    exact h3

/-! ### 2. Block facts -/

/-- Horner value of a rational coefficient list. -/
def evalQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: as, c => a + c * evalQ as c

theorem polyTow_zero_cast (p : List ℚ) (c : ℚ) : polyTow p 0 (c : ℝ) = ((evalQ p c : ℚ) : ℝ) := by
  induction p with
  | nil => simp [polyTow, evalQ]
  | cons a as ih =>
    simp only [polyTow, evalQ, ih]
    push_cast; ring

/-- `|log |x - e|| ≤ 7k/10` when `2^-k ≤ |x - e| ≤ 2^k`. -/
theorem abs_log_le_of_pow (k : ℕ) (d : ℝ) (h1 : ((1 : ℝ) / 2) ^ k ≤ d) (h2 : d ≤ 2 ^ k) :
    |Real.log d| ≤ 7 * (k : ℝ) / 10 := by
  have hd : 0 < d := lt_of_lt_of_le (by positivity) h1
  have hl2 : Real.log 2 < 7 / 10 := by
    have := Real.log_two_lt_d9; linarith
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [abs_le]
  constructor
  · have h3 : Real.log (((1 : ℝ) / 2) ^ k) ≤ Real.log d := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h3
    have : Real.log ((1 : ℝ) / 2) = - Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [this] at h3
    nlinarith
  · have h3 : Real.log d ≤ Real.log ((2 : ℝ) ^ k) := Real.log_le_log hd h2
    rw [Real.log_pow] at h3
    nlinarith

/-- Boolean check of the logarithm bounds `Lb = 7k/10` of the pieces. -/
def lbOK (blo bhi : ℚ) : List (List ℚ × ℚ) → List PlogBlk → List ℕ → Bool
  | [], [], [] => true
  | t :: ts, b :: bs, k :: ks =>
    decide (b.Lb = 7 * (k : ℚ) / 10) && decide ((1 / 2 : ℚ) ^ k ≤ b.dm) &&
    decide (qabs' (blo - t.2) ≤ 2 ^ k) && decide (qabs' (bhi - t.2) ≤ 2 ^ k) &&
    lbOK blo bhi ts bs ks
  | _, _, _ => false

theorem logBnd_of_ok (blo bhi : ℚ) :
    ∀ (plogs : List (List ℚ × ℚ)) (pb : List PlogBlk) (ks : List ℕ),
      plogBlkOK ((blo + bhi) / 2) blo bhi plogs pb = true →
      lbOK blo bhi plogs pb ks = true → LogBnd blo bhi plogs pb := by
  intro plogs
  induction plogs with
  | nil =>
    intro pb ks _ h
    cases pb <;> cases ks <;> simp_all [LogBnd, lbOK]
  | cons t ts ih =>
    intro pb ks hp hl
    cases pb with
    | nil => simp [lbOK] at hl
    | cons b bs =>
      cases ks with
      | nil => simp [lbOK] at hl
      | cons k ks =>
        simp only [plogBlkOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hp
        obtain ⟨⟨⟨⟨hlen, hchk⟩, hdm⟩, hside⟩, hrest⟩ := hp
        simp only [lbOK, Bool.and_eq_true, decide_eq_true_eq] at hl
        obtain ⟨⟨⟨⟨hLb, hd1⟩, hd2⟩, hd3⟩, hlrest⟩ := hl
        refine ⟨?_, ih bs ks hrest hlrest⟩
        intro x hx
        have hdmR : (b.dm : ℝ) ≤ |x - (t.2 : ℝ)| := by
          rcases hside with h | h
          · have h' : (b.dm : ℝ) ≤ (t.2 : ℝ) - (bhi : ℝ) := by exact_mod_cast h
            rw [abs_sub_comm]
            exact h'.trans ((by linarith [hx.2] : (t.2 : ℝ) - bhi ≤ t.2 - x).trans (le_abs_self _))
          · have h' : (b.dm : ℝ) ≤ (blo : ℝ) - (t.2 : ℝ) := by exact_mod_cast h
            exact h'.trans ((by linarith [hx.1] : (blo : ℝ) - t.2 ≤ x - t.2).trans (le_abs_self _))
        have hlow : ((1 : ℝ) / 2) ^ k ≤ |x - (t.2 : ℝ)| := by
          refine le_trans ?_ hdmR
          have h0 : ((1 / 2 : ℚ) ^ k : ℚ) ≤ b.dm := hd1
          have h : (((1 / 2 : ℚ) ^ k : ℚ) : ℝ) ≤ (b.dm : ℝ) := Rat.cast_le.mpr h0
          push_cast at h
          exact h
        have hup : |x - (t.2 : ℝ)| ≤ 2 ^ k := by
          rw [abs_le]
          have u1 : ((qabs' (blo - t.2) : ℚ) : ℝ) ≤ 2 ^ k := by exact_mod_cast hd2
          have u2 : ((qabs' (bhi - t.2) : ℚ) : ℝ) ≤ 2 ^ k := by exact_mod_cast hd3
          rw [qabs'_cast] at u1 u2
          push_cast at u1 u2
          have w1 := abs_le.mp u1
          have w2 := abs_le.mp u2
          constructor <;> linarith [hx.1, hx.2, w1.1, w2.2]
        have := abs_log_le_of_pow k _ hlow hup
        rw [hLb]; push_cast; exact this


theorem plogAvoid_of_ok (cb blo bhi : ℚ) :
    ∀ (plogs : List (List ℚ × ℚ)) (pb : List PlogBlk),
      plogBlkOK cb blo bhi plogs pb = true →
      ∀ t ∈ plogs, ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ), x ≠ (t.2 : ℝ) := by
  intro plogs
  induction plogs with
  | nil => intro pb _ t ht; simp at ht
  | cons t0 ts ih =>
    intro pb hp t ht x hx hxe
    cases pb with
    | nil => simp [plogBlkOK] at hp
    | cons b bs =>
      simp only [plogBlkOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hp
      obtain ⟨⟨⟨⟨hlen, hchk⟩, hdm⟩, hside⟩, hrest⟩ := hp
      rcases List.mem_cons.mp ht with rfl | ht'
      · rcases hside with h | h
        · have h' : (b.dm : ℝ) ≤ (t.2 : ℝ) - (bhi : ℝ) := by exact_mod_cast h
          have : (0 : ℝ) < b.dm := by exact_mod_cast hdm
          linarith [hx.2]
        · have h' : (b.dm : ℝ) ≤ (blo : ℝ) - (t.2 : ℝ) := by exact_mod_cast h
          have : (0 : ℝ) < b.dm := by exact_mod_cast hdm
          linarith [hx.1]
      · exact ih bs hrest t ht' x hx hxe

/-- The Boolean check of a block. -/
def blockOK (fq : FieldQ) (blo bhi : ℚ) (M : ℕ) (CbP : List ℚ) (pb : List PlogBlk) (ks : List ℕ)
    (BM : ℚ) : Bool :=
  blockTailCheck fq blo bhi M CbP pb BM && lbOK blo bhi fq.plogs pb ks &&
  fq.poles.all (fun q => decide (q.pi ≠ 0 ∨ q.ri = 0)) &&
  fq.poles.all (fun q => decide (0 < poleDist q blo bhi))

structure BlockFacts (fq : FieldQ) (blo bhi : ℚ) (M : ℕ) (BM : ℚ) : Prop where
  tail : ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ),
    |fieldTower fq (poleF fq.poles) M x| / ((M.factorial : ℕ) : ℝ) ≤ (BM : ℝ)
  plog : ∀ t ∈ fq.plogs, ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ), x ≠ (t.2 : ℝ)
  pole : ∀ q ∈ fq.poles, ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ), (x : ℂ) ≠ q.pc
  deriv : ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ),
    HasDerivAt (poleF fq.poles) ((fq.poles.map (fun q => qt q 0 x)).sum) x

theorem blockFacts_of_ok (fq : FieldQ) (blo bhi : ℚ) (M : ℕ) (CbP : List ℚ) (pb : List PlogBlk)
    (ks : List ℕ) (BM : ℚ) (h : blockOK fq blo bhi M CbP pb ks BM = true) :
    BlockFacts fq blo bhi M BM := by
  simp only [blockOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hT, hL⟩, hreal⟩, hdist⟩ := h
  have hplogOK : plogBlkOK ((blo + bhi) / 2) blo bhi fq.plogs pb = true := by
    simp only [blockTailCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hT
    exact hT.1.1.2
  have hlog := logBnd_of_ok blo bhi fq.plogs pb ks hplogOK hL
  have hreal' : ∀ q ∈ fq.poles, q.pi = 0 → q.ri = 0 := by
    intro q hq hpi
    rcases hreal q hq with h | h
    · exact absurd hpi h
    · exact h
  have hpole : ∀ q ∈ fq.poles, ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ), (x : ℂ) ≠ q.pc := by
    intro q hq x hx heq
    have := poleDist_le_norm q blo bhi x hx.1 hx.2
    rw [heq, sub_self, norm_zero] at this
    have h2 : (0 : ℝ) < ((poleDist q blo bhi : ℚ) : ℝ) := by exact_mod_cast hdist q hq
    linarith
  exact ⟨blockTailCheck_sound fq (poleF fq.poles) blo bhi M CbP pb BM hT hlog,
    plogAvoid_of_ok _ blo bhi fq.plogs pb hplogOK, hpole,
    fun x hx => hasDerivAt_poleF fq.poles hreal' x (fun q hq => hpole q hq x hx)⟩

/-! ### 3. Logarithm values and the direct anchor -/

def logsOf (nL : ℕ) (c : ℚ) : List (List ℚ × ℚ) → Option (List ℚ × List ℚ)
  | [] => some ([], [])
  | t :: ts =>
    match logAbsQ nL (c - t.2), logsOf nL c ts with
    | some (v, e), some (Ls, εs) => some (v :: Ls, e :: εs)
    | _, _ => none

theorem logsOf_spec (nL : ℕ) (c : ℚ) : ∀ (plogs : List (List ℚ × ℚ)) (Ls εs : List ℚ),
    logsOf nL c plogs = some (Ls, εs) → LogVals c plogs Ls εs := by
  intro plogs
  induction plogs with
  | nil =>
    intro Ls εs h
    simp only [logsOf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    trivial
  | cons t ts ih =>
    intro Ls εs h
    simp only [logsOf] at h
    split at h
    · rename_i v e Ls' εs' h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ih Ls' εs' h2⟩
      have := (logAbsQ_spec h1).2
      unfold Enc at this
      have e1 : ((c - t.2 : ℚ) : ℝ) = (c : ℝ) - (t.2 : ℝ) := by push_cast; ring
      rw [e1] at this
      rw [abs_sub_comm]
      exact this
    · simp at h

def plogTerms (nL : ℕ) (c : ℚ) : List (List ℚ × ℚ) → Option (List (ℚ × ℚ))
  | [] => some []
  | t :: ts =>
    match logAbsQ nL (c - t.2), plogTerms nL c ts with
    | some (v, e), some r => some ((evalQ t.1 c * v, qabs (evalQ t.1 c) * e) :: r)
    | _, _ => none

theorem plogTerms_spec (nL : ℕ) (c : ℚ) : ∀ (plogs : List (List ℚ × ℚ)) (ts : List (ℚ × ℚ)),
    plogTerms nL c plogs = some ts →
    List.Forall₂ Enc (plogs.map (fun t => polyTow t.1 0 (c : ℝ) * Real.log |(c : ℝ) - (t.2 : ℝ)|)) ts := by
  intro plogs
  induction plogs with
  | nil =>
    intro ts h
    simp only [plogTerms, Option.some.injEq] at h
    subst h; exact List.Forall₂.nil
  | cons t tl ih =>
    intro ts h
    simp only [plogTerms] at h
    split at h
    · rename_i v e r h1 h2
      simp only [Option.some.injEq] at h
      subst h
      refine List.Forall₂.cons ?_ (ih r h2)
      have hl := (logAbsQ_spec h1).2
      have e1 : ((c - t.2 : ℚ) : ℝ) = (c : ℝ) - (t.2 : ℝ) := by push_cast; ring
      rw [e1] at hl
      have := hl.mulQ (evalQ t.1 c)
      show Enc (polyTow t.1 0 (c : ℝ) * Real.log |(c : ℝ) - (t.2 : ℝ)|) _
      rw [polyTow_zero_cast]
      exact this
    · simp at h

def poleTerms (nL nA : ℕ) (c : ℚ) : List PoleR → Option (List (ℚ × ℚ))
  | [] => some []
  | q :: qs =>
    match poleLogQ nL nA q c, poleTerms nL nA c qs with
    | some t, some r => some (t :: r)
    | _, _ => none

theorem poleTerms_spec (nL nA : ℕ) (c : ℚ) : ∀ (poles : List PoleR) (ts : List (ℚ × ℚ)),
    poleTerms nL nA c poles = some ts →
    List.Forall₂ Enc (poles.map (fun q => (q.rho * Complex.log (((c : ℝ) : ℂ) - q.pc)).re)) ts := by
  intro poles
  induction poles with
  | nil =>
    intro ts h
    simp only [poleTerms, Option.some.injEq] at h
    subst h; exact List.Forall₂.nil
  | cons q qs ih =>
    intro ts h
    simp only [poleTerms] at h
    split at h
    · rename_i t r h1 h2
      simp only [Option.some.injEq] at h
      subst h
      exact List.Forall₂.cons (poleLogQ_spec h1) (ih r h2)
    · simp at h

/-- The anchor: an enclosure of the field value at the rational point `c` from logarithm
evaluations (poly exactly, `P_e(c) log|c - e|` and the pole logs rounded to `2^-P`). -/
def anchorEnc (nL nA P : ℕ) (fq : FieldQ) (c : ℚ) : Option (ℚ × ℚ) :=
  match plogTerms nL c fq.plogs, poleTerms nL nA c fq.poles with
  | some a, some b =>
    some (evalQ fq.poly c + (encSumRound P a).1 + (encSumRound P b).1,
      (encSumRound P a).2 + (encSumRound P b).2)
  | _, _ => none

theorem fieldTower_zero_eq (fq : FieldQ) (c : ℚ) :
    fieldTower fq (poleF fq.poles) 0 (c : ℝ) =
      polyTow fq.poly 0 (c : ℝ) +
      (fq.plogs.map (fun t => polyTow t.1 0 (c : ℝ) * Real.log |(c : ℝ) - (t.2 : ℝ)|)).sum +
      (fq.poles.map (fun q => (q.rho * Complex.log (((c : ℝ) : ℂ) - q.pc)).re)).sum := by
  unfold fieldTower plogSumTower
  rw [poleTower_zero]
  unfold poleF
  congr 2
  congr 1
  apply List.map_congr_left
  intro t _
  simp [mulTower_zero, logTower]

theorem anchorEnc_spec (nL nA P : ℕ) (fq : FieldQ) (c : ℚ) (p : ℚ × ℚ)
    (h : anchorEnc nL nA P fq c = some p) : Enc (fieldTower fq (poleF fq.poles) 0 (c : ℝ)) p := by
  unfold anchorEnc at h
  split at h
  · rename_i a b ha hb
    simp only [Option.some.injEq] at h
    subst h
    have e1 := encSumRound_enc P _ _ (plogTerms_spec nL c fq.plogs a ha)
    have e2 := encSumRound_enc P _ _ (poleTerms_spec nL nA c fq.poles b hb)
    have e0 : Enc (polyTow fq.poly 0 (c : ℝ)) (evalQ fq.poly c, 0) := by
      rw [polyTow_zero_cast]; exact Enc.const _
    have := (e0.add e1).add e2
    rw [fieldTower_zero_eq]
    unfold Enc at this ⊢
    simp only [zero_add] at this
    simpa [add_assoc] using this
  · simp at h

def anchorCheck (nL nA P : ℕ) (fq : FieldQ) (c : ℚ) (A : ℚ × ℚ) : Bool :=
  match anchorEnc nL nA P fq c with
  | none => false
  | some p => decide (qabs' (p.1 - A.1) + p.2 ≤ A.2)

theorem encWiden {x : ℝ} {p : ℚ × ℚ} (hx : Enc x p) (A : ℚ × ℚ)
    (h : qabs' (p.1 - A.1) + p.2 ≤ A.2) : Enc x A := by
  unfold Enc at *
  have h' : |(p.1 : ℝ) - (A.1 : ℝ)| + (p.2 : ℝ) ≤ (A.2 : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr h
    rw [Rat.cast_add, qabs'_cast] at this
    push_cast at this
    exact this
  calc |x - (A.1 : ℝ)| = |(x - p.1) + (p.1 - A.1)| := by ring_nf
    _ ≤ |x - p.1| + |(p.1 : ℝ) - A.1| := abs_add_le _ _
    _ ≤ A.2 := by linarith

theorem anchorCheck_sound (nL nA P : ℕ) (fq : FieldQ) (c : ℚ) (A : ℚ × ℚ)
    (h : anchorCheck nL nA P fq c A = true) : Enc (fieldTower fq (poleF fq.poles) 0 (c : ℝ)) A := by
  unfold anchorCheck at h
  split at h
  · simp at h
  · rename_i p hp
    simp only [decide_eq_true_eq] at h
    exact encWiden (anchorEnc_spec nL nA P fq c p hp) A h


/-! ### 4. One cell and the chaining step -/

/-- One cell `[lo, hi]` of a block `[blo, bhi]`, followed by the next cell `[lo', hi']`: the cell
check of `fieldCellCheck` (anchor `A` of the field at the centre) and the chaining step to the next
centre, `A'` being a (wider) enclosure of the field at the next centre. -/
def cellStep (fq : FieldQ) (nL : ℕ) (blo bhi lo hi lo' hi' : ℚ) (A : ℚ × ℚ) (l1 u1 A2 : ℚ)
    (Bl : List ℚ) (BM T : ℚ) (A' : ℚ × ℚ) : Bool :=
  match logsOf nL ((lo + hi) / 2) fq.plogs with
  | none => false
  | some (Ls, εs) =>
    fieldCellCheck fq Ls εs lo hi (A.1 + A.2) l1 u1 A2 Bl BM T &&
    (let c := (lo + hi) / 2
     let h := (lo' + hi') / 2 - c
     let N := Bl.length + 2
     let B := chainQ (fun k => (fieldCoefs fq Ls c N).getD k 0)
       (fun k => (plogErrSum c N fq.plogs εs).getD k 0) h N BM A
     decide (qabs' (B.1 - A'.1) + B.2 ≤ A'.2) && decide (blo ≤ c - qabs' h) &&
     decide (c + qabs' h ≤ bhi) && decide (blo ≤ lo) && decide (hi ≤ bhi))

theorem cellStep_sound (fq : FieldQ) (nL : ℕ) (blo bhi lo hi lo' hi' : ℚ) (A : ℚ × ℚ)
    (l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ) (A' : ℚ × ℚ)
    (hchk : cellStep fq nL blo bhi lo hi lo' hi' A l1 u1 A2 Bl BM T A' = true)
    (hB : BlockFacts fq blo bhi (Bl.length + 3) BM)
    (hA : Enc (fieldTower fq (poleF fq.poles) 0 (((lo + hi) / 2 : ℚ) : ℝ)) A) :
    (∀ x ∈ Icc (lo : ℝ) (hi : ℝ), fieldTower fq (poleF fq.poles) 0 x ≤ (T : ℝ)) ∧
      Enc (fieldTower fq (poleF fq.poles) 0 (((lo' + hi') / 2 : ℚ) : ℝ)) A' := by
  unfold cellStep at hchk
  split at hchk
  · simp at hchk
  · rename_i Ls εs hls
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨hcell, ⟨⟨⟨hch, hb1⟩, hb2⟩, hb3⟩, hb4⟩ := hchk
    set c : ℚ := (lo + hi) / 2 with hc
    set h : ℚ := (lo' + hi') / 2 - c with hh
    have hLs := logsOf_spec nL c fq.plogs Ls εs hls
    have hsub : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), x ∈ Icc (blo : ℝ) (bhi : ℝ) := by
      intro x hx
      exact ⟨le_trans (by exact_mod_cast hb3) hx.1, le_trans hx.2 (by exact_mod_cast hb4)⟩
    refine ⟨?_, ?_⟩
    · exact fieldCellCheck_sound fq (poleF fq.poles) Ls εs lo hi (A.1 + A.2) l1 u1 A2 Bl BM T
        hcell hLs (fun x hx => hB.deriv x (hsub x hx)) hA.le_upper blo bhi hb3 hb4 hB.tail
    · -- chaining
      have hρ : (((c - qabs' h : ℚ)) : ℝ) = (c : ℝ) - |(h : ℝ)| := by
        push_cast; rw [qabs'_cast]
      have hρ' : (((c + qabs' h : ℚ)) : ℝ) = (c : ℝ) + |(h : ℝ)| := by
        push_cast; rw [qabs'_cast]
      have hseg : ∀ x ∈ Icc ((c : ℝ) - |(h : ℝ)|) ((c : ℝ) + |(h : ℝ)|),
          x ∈ Icc (blo : ℝ) (bhi : ℝ) := by
        intro x hx
        refine ⟨le_trans ?_ hx.1, le_trans hx.2 ?_⟩
        · rw [← hρ]; exact_mod_cast hb1
        · rw [← hρ']; exact_mod_cast hb2
      have hcmem : (c : ℝ) ∈ Icc (blo : ℝ) (bhi : ℝ) :=
        hseg _ ⟨by linarith [abs_nonneg (h : ℝ)], by linarith [abs_nonneg (h : ℝ)]⟩
      have hne : ∀ t ∈ fq.plogs, c - t.2 ≠ 0 := by
        intro t ht hz
        apply hB.plog t ht c hcmem
        have : c = t.2 := by linarith
        rw [this]
      have hT := isTower_fieldTower fq (poleF fq.poles) (c : ℝ) |(h : ℝ)| (Bl.length + 2 + 1)
        (fun t ht x hx => hB.plog t ht x (hseg x hx))
        (fun x hx q hq => hB.pole q hq x (hseg x hx))
        (fun x hx => hB.deriv x (hseg x hx))
      have hch' := chain_enc hT h (le_refl _)
        (fun k => (fieldCoefs fq Ls c (Bl.length + 2)).getD k 0)
        (fun k => (plogErrSum c (Bl.length + 2) fq.plogs εs).getD k 0) BM A hA
        (fun k hk1 hk2 => fieldCoefs_approx fq (poleF fq.poles) Ls εs c (Bl.length + 2) hLs hne k hk1
          hk2)
        (fun y hy => hB.tail y (hseg y hy))
      have hcc : (c : ℝ) + (h : ℝ) = (((lo' + hi') / 2 : ℚ) : ℝ) := by
        rw [hh]; push_cast; ring
      rw [hcc] at hch'
      exact encWiden hch' A' hch


/-! ### 5. Literal helpers (odd mantissas, separate exponents: no 2-adic literals) and covers -/

/-- `m / 2^e` (the mantissa `m` is odd or `0`, the exponent is a separate small literal). -/
def dy (m e : ℤ) : ℚ := (m : ℚ) / 2 ^ e.toNat

def dyList : List ℤ → List ℤ → List ℚ
  | m :: ms, e :: es => dy m e :: dyList ms es
  | _, _ => []


/-- `m 2^a / 2^e` with `m` odd or `0` (so that neither a numerator nor a denominator literal is a multiple of `2^64`). -/
def dy3 (m a e : ℤ) : ℚ := ((m : ℚ) * 2 ^ a.toNat) / 2 ^ e.toNat

def dyList3 : List ℤ → List ℤ → List ℤ → List ℚ
  | m :: ms, a :: as, e :: es => dy3 m a e :: dyList3 ms as es
  | _, _, _ => []

/-- `n 2^a / (d 2^b)` with `n`, `d` odd. -/
def qmk (n d a b : ℤ) : ℚ := ((n : ℚ) * 2 ^ a.toNat) / ((d : ℚ) * 2 ^ b.toNat)

/-- Poles from a flat list of `16` integers each: `(n, d, a, b)` for `rr, ri, pr, pi`. -/
def mkPoles : List ℤ → List PoleR
  | n1 :: d1 :: a1 :: b1 :: n2 :: d2 :: a2 :: b2 :: n3 :: d3 :: a3 :: b3 :: n4 :: d4 :: a4 :: b4 :: rest =>
    ⟨qmk n1 d1 a1 b1, qmk n2 d2 a2 b2, qmk n3 d3 a3 b3, qmk n4 d4 a4 b4⟩ :: mkPoles rest
  | _ => []

theorem cover_union {P : ℝ → Prop} {a b c : ℝ} (h1 : ∀ x ∈ Icc a b, P x) (h2 : ∀ x ∈ Icc b c, P x) :
    ∀ x ∈ Icc a c, P x := by
  intro x hx
  by_cases hxb : x ≤ b
  · exact h1 x ⟨hx.1, hxb⟩
  · exact h2 x ⟨le_of_lt (not_le.mp hxb), hx.2⟩


/-! ### 6. Lockstep (single-evaluation) forms and the direct-anchor cell -/

/-- `|T_i| ≤ b_i` in lockstep (each coefficient is evaluated once; `T` is padded with `0`). -/
def absLeL : List ℚ → List ℚ → Bool
  | _, [] => true
  | [], b :: bs => decide (qabs' 0 ≤ b) && absLeL [] bs
  | t :: ts, b :: bs => decide (qabs' t ≤ b) && absLeL ts bs

theorem absLeAll_eq : ∀ (Bl T : List ℚ) (k : ℕ), absLeAll T k Bl = absLeL (T.drop k) Bl := by
  intro Bl
  induction Bl with
  | nil => intro T k; simp [absLeAll, absLeL]
  | cons b bs ih =>
    intro T k
    simp only [absLeAll, ih T (k + 1)]
    cases hT : T.drop k with
    | nil =>
      have h0 : T[k]? = none := by
        have := congrArg (fun l => l[0]?) hT
        simpa [List.getElem?_drop] using this
      have h1 : T.getD k 0 = 0 := by rw [List.getD_eq_getElem?_getD, h0]; rfl
      have h2 : T.drop (k + 1) = [] := by
        rw [← List.drop_drop]; rw [hT]; simp
      rw [h1, h2]; simp [absLeL]
    | cons t ts =>
      have h3 : T[k]? = some t := by
        have := congrArg (fun l => l[0]?) hT
        simpa [List.getElem?_drop] using this
      have h1 : T.getD k 0 = t := by rw [List.getD_eq_getElem?_getD, h3]; rfl
      have h2 : T.drop (k + 1) = ts := by
        rw [← List.drop_drop]; rw [hT]; simp
      rw [h1, h2]; simp [absLeL]

/-- `|T_i| + E_i ≤ b_i` in lockstep. -/
def absLeEL : List ℚ → List ℚ → List ℚ → Bool
  | _, _, [] => true
  | t :: ts, e :: es, b :: bs => decide (qabs' t + e ≤ b) && absLeEL ts es bs
  | _, _, _ :: _ => false

/-- Block-tail checker with the lockstep polynomial test (same conclusion as `blockTailCheck`). -/
def blockTailCheck2 (fq : FieldQ) (blo bhi : ℚ) (M : ℕ) (CbP : List ℚ) (pb : List PlogBlk)
    (BM : ℚ) : Bool :=
  decide (blo ≤ bhi) && decide (1 ≤ M) &&
  decide (fq.poly.length ≤ CbP.length) &&
  absLeL (shiftL ((blo + bhi) / 2) CbP.length fq.poly) CbP &&
  plogBlkOK ((blo + bhi) / 2) blo bhi fq.plogs pb &&
  fq.poles.all (fun q => decide (0 < poleDist q blo bhi)) &&
  decide (blockTailQ fq blo bhi M CbP pb ≤ BM)

theorem blockTailCheck_of_2 (fq : FieldQ) (blo bhi : ℚ) (M : ℕ) (CbP : List ℚ)
    (pb : List PlogBlk) (BM : ℚ) (h : blockTailCheck2 fq blo bhi M CbP pb BM = true) :
    blockTailCheck fq blo bhi M CbP pb BM = true := by
  have e := absLeAll_eq CbP (shiftL ((blo + bhi) / 2) CbP.length fq.poly) 0
  simp only [List.drop_zero] at e
  unfold blockTailCheck2 at h
  unfold blockTailCheck
  rw [e]
  exact h

/-- The Boolean check of a block (lockstep). -/
def blockOK2 (fq : FieldQ) (blo bhi : ℚ) (M : ℕ) (CbP : List ℚ) (pb : List PlogBlk) (ks : List ℕ)
    (BM : ℚ) : Bool :=
  blockTailCheck2 fq blo bhi M CbP pb BM && lbOK blo bhi fq.plogs pb ks &&
  fq.poles.all (fun q => decide (q.pi ≠ 0 ∨ q.ri = 0)) &&
  fq.poles.all (fun q => decide (0 < poleDist q blo bhi))

theorem blockFacts_of_ok2 (fq : FieldQ) (blo bhi : ℚ) (M : ℕ) (CbP : List ℚ) (pb : List PlogBlk)
    (ks : List ℕ) (BM : ℚ) (h : blockOK2 fq blo bhi M CbP pb ks BM = true) :
    BlockFacts fq blo bhi M BM := by
  apply blockFacts_of_ok fq blo bhi M CbP pb ks BM
  simp only [blockOK2, Bool.and_eq_true] at h
  simp only [blockOK, Bool.and_eq_true]
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨⟨⟨blockTailCheck_of_2 _ _ _ _ _ _ _ h1, h2⟩, h3⟩, h4⟩

theorem absLeAllE_of_L : ∀ (Bl cs es : List ℚ), absLeEL (cs.drop 3) (es.drop 3) Bl = true →
    absLeAllE cs es 3 Bl = true := by
  suffices h : ∀ (Bl cs es : List ℚ) (k : ℕ), absLeEL (cs.drop k) (es.drop k) Bl = true →
      absLeAllE cs es k Bl = true from fun Bl cs es => h Bl cs es 3
  intro Bl
  induction Bl with
  | nil => intro cs es k _; simp [absLeAllE]
  | cons b bs ih =>
    intro cs es k hk
    simp only [absLeAllE, Bool.and_eq_true, decide_eq_true_eq]
    cases hc : cs.drop k with
    | nil => simp [hc, absLeEL] at hk
    | cons t ts =>
      cases he : es.drop k with
      | nil => simp [hc, he, absLeEL] at hk
      | cons e es' =>
        rw [hc, he] at hk
        simp only [absLeEL, Bool.and_eq_true, decide_eq_true_eq] at hk
        have h1 : cs.getD k 0 = t := by
          have h3 : cs[k]? = some t := by
            have := congrArg (fun l => l[0]?) hc
            simpa [List.getElem?_drop] using this
          rw [List.getD_eq_getElem?_getD, h3]; rfl
        have h2 : es.getD k 0 = e := by
          have h3 : es[k]? = some e := by
            have := congrArg (fun l => l[0]?) he
            simpa [List.getElem?_drop] using this
          rw [List.getD_eq_getElem?_getD, h3]; rfl
        refine ⟨by rw [h1, h2]; exact hk.1, ih cs es (k + 1) ?_⟩
        have h4 : cs.drop (k + 1) = ts := by rw [← List.drop_drop, hc]; simp
        have h5 : es.drop (k + 1) = es' := by rw [← List.drop_drop, he]; simp
        rw [h4, h5]; exact hk.2

/-- The anchor with separate precisions for the polynomial-log terms and the pole terms. -/
def anchorUB2 (nLc Pc nLp nAp Pp : ℕ) (fq : FieldQ) (c : ℚ) : Option ℚ :=
  match plogTerms nLc c fq.plogs, poleTerms nLp nAp c fq.poles with
  | some a, some b =>
    some (evalQ fq.poly c + (encSumRound Pc a).1 + (encSumRound Pp b).1 +
      ((encSumRound Pc a).2 + (encSumRound Pp b).2))
  | _, _ => none

theorem anchorUB2_spec (nLc Pc nLp nAp Pp : ℕ) (fq : FieldQ) (c : ℚ) (v : ℚ)
    (h : anchorUB2 nLc Pc nLp nAp Pp fq c = some v) :
    fieldTower fq (poleF fq.poles) 0 (c : ℝ) ≤ (v : ℝ) := by
  unfold anchorUB2 at h
  split at h
  · rename_i a b ha hb
    simp only [Option.some.injEq] at h
    subst h
    have e1 := encSumRound_enc Pc _ _ (plogTerms_spec nLc c fq.plogs a ha)
    have e2 := encSumRound_enc Pp _ _ (poleTerms_spec nLp nAp c fq.poles b hb)
    have e0 : Enc (polyTow fq.poly 0 (c : ℝ)) (evalQ fq.poly c, 0) := by
      rw [polyTow_zero_cast]; exact Enc.const _
    have := ((e0.add e1).add e2).le_upper
    rw [fieldTower_zero_eq]
    simp only [zero_add] at this
    push_cast at this ⊢
    linarith
  · simp at h

/-- One cell with a **direct** anchor (all coefficients computed once; lockstep tests). -/
def cellV (fq : FieldQ) (nLc Pc nLp nAp Pp : ℕ) (blo bhi lo hi : ℚ) (A0 l1 u1 A2 : ℚ)
    (Bl : List ℚ) (BM T : ℚ) : Bool :=
  match logsOf nLc ((lo + hi) / 2) fq.plogs, anchorUB2 nLc Pc nLp nAp Pp fq ((lo + hi) / 2) with
  | some (Ls, εs), some v =>
    decide (v ≤ A0) && decide (blo ≤ lo) && decide (hi ≤ bhi) &&
    (let cs := fieldCoefs fq Ls ((lo + hi) / 2) (Bl.length + 2)
     let es := plogErrSum ((lo + hi) / 2) (Bl.length + 2) fq.plogs εs
     decide (l1 ≤ cs.getD 1 0 - es.getD 1 0) && decide (cs.getD 1 0 + es.getD 1 0 ≤ u1) &&
     decide (cs.getD 2 0 + es.getD 2 0 ≤ A2) &&
     absLeEL (cs.drop 3) (es.drop 3) Bl &&
     decide (tmUBQ A0 l1 u1 A2 ((hi - lo) / 2) Bl BM ≤ T))
  | _, _ => false

theorem cellV_sound (fq : FieldQ) (nLc Pc nLp nAp Pp : ℕ) (blo bhi lo hi : ℚ) (A0 l1 u1 A2 : ℚ)
    (Bl : List ℚ) (BM T : ℚ)
    (hchk : cellV fq nLc Pc nLp nAp Pp blo bhi lo hi A0 l1 u1 A2 Bl BM T = true)
    (hB : BlockFacts fq blo bhi (Bl.length + 3) BM) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), fieldTower fq (poleF fq.poles) 0 x ≤ (T : ℝ) := by
  unfold cellV at hchk
  split at hchk
  · rename_i Ls εs v hls hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨hvA, hb1⟩, hb2⟩, ⟨⟨⟨⟨hl1, hu1⟩, hA2⟩, hL⟩, hT⟩⟩ := hchk
    set c : ℚ := (lo + hi) / 2 with hc
    set r : ℚ := (hi - lo) / 2 with hr
    have hLs := logsOf_spec nLc c fq.plogs Ls εs hls
    have e1 : (c : ℝ) - (r : ℝ) = (lo : ℝ) := by simp only [hc, hr]; push_cast; ring
    have e2 : (c : ℝ) + (r : ℝ) = (hi : ℝ) := by simp only [hc, hr]; push_cast; ring
    have hcell : Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)) = Icc (lo : ℝ) (hi : ℝ) := by
      rw [e1, e2]
    have hsub : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), x ∈ Icc (blo : ℝ) (bhi : ℝ) := by
      intro x hx
      exact ⟨le_trans (by exact_mod_cast hb1) hx.1, le_trans hx.2 (by exact_mod_cast hb2)⟩
    have hsub' : ∀ x ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)), x ∈ Icc (blo : ℝ) (bhi : ℝ) := by
      intro x hx; rw [hcell] at hx; exact hsub x hx
    intro x hx
    have hle : (lo : ℝ) ≤ hi := le_trans hx.1 hx.2
    have hr0 : (0 : ℝ) ≤ r := by simp only [hr]; push_cast; linarith
    have hnec : ∀ t ∈ fq.plogs, c - t.2 ≠ 0 := by
      intro t ht hz
      have hcm : (c : ℝ) ∈ Icc (blo : ℝ) (bhi : ℝ) := hsub' _ ⟨by linarith, by linarith⟩
      apply hB.plog t ht c hcm
      have : c = t.2 := by linarith
      rw [this]
    have hT0 := isTower_fieldTower fq (poleF fq.poles) (c : ℝ) (r : ℝ) (Bl.length + 3)
      (fun t ht y hy => hB.plog t ht y (hsub' y hy))
      (fun y hy q hq => hB.pole q hq y (hsub' y hy))
      (fun y hy => hB.deriv y (hsub' y hy))
    have hspec := fun k hk1 hk =>
      fieldCoefs_approx fq (poleF fq.poles) Ls εs c (Bl.length + 2) hLs hnec k hk1 hk
    have h0 : fieldTower fq (poleF fq.poles) 0 (c : ℝ) ≤ (A0 : ℝ) :=
      (anchorUB2_spec nLc Pc nLp nAp Pp fq c v hv).trans (by exact_mod_cast hvA)
    exact cellCore lo hi A0 l1 u1 A2 Bl BM T _ _ hT0 hspec hl1 hu1 hA2
      (absLeAllE_of_L Bl _ _ hL) hT h0 blo bhi hb1 hb2 hB.tail x hx
  · simp at hchk


/-! ### 7. Centres and logarithm values as normal-form literals (no re-evaluation in the kernel) -/

/-- `blockTailCheck2` with the centre passed as a (normal-form) literal. -/
def blockTailCheck3 (fq : FieldQ) (cb blo bhi : ℚ) (M : ℕ) (CbP : List ℚ) (pb : List PlogBlk)
    (BM : ℚ) : Bool :=
  decide (blo ≤ bhi) && decide (1 ≤ M) &&
  decide (fq.poly.length ≤ CbP.length) &&
  absLeL (shiftL cb CbP.length fq.poly) CbP &&
  plogBlkOK cb blo bhi fq.plogs pb &&
  fq.poles.all (fun q => decide (0 < poleDist q blo bhi)) &&
  decide (blockTailQ fq blo bhi M CbP pb ≤ BM)

def blockOK3 (fq : FieldQ) (cb blo bhi : ℚ) (M : ℕ) (CbP : List ℚ) (pb : List PlogBlk)
    (ks : List ℕ) (BM : ℚ) : Bool :=
  decide (cb = (blo + bhi) / 2) && blockTailCheck3 fq cb blo bhi M CbP pb BM &&
  lbOK blo bhi fq.plogs pb ks &&
  fq.poles.all (fun q => decide (q.pi ≠ 0 ∨ q.ri = 0)) &&
  fq.poles.all (fun q => decide (0 < poleDist q blo bhi))

theorem blockFacts_of_ok3 (fq : FieldQ) (cb blo bhi : ℚ) (M : ℕ) (CbP : List ℚ)
    (pb : List PlogBlk) (ks : List ℕ) (BM : ℚ)
    (h : blockOK3 fq cb blo bhi M CbP pb ks BM = true) : BlockFacts fq blo bhi M BM := by
  simp only [blockOK3, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hcb, h1⟩, h2⟩, h3⟩, h4⟩ := h
  subst hcb
  apply blockFacts_of_ok2 fq blo bhi M CbP pb ks BM
  simp only [blockOK2, blockTailCheck2, blockTailCheck3, Bool.and_eq_true] at h1 ⊢
  exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- the logarithm literals `Ls ± εs` enclose `log |c - e|` (checked against `logAbsQ`) -/
def logsCheck (nL : ℕ) (c : ℚ) : List (List ℚ × ℚ) → List ℚ → List ℚ → Bool
  | [], [], [] => true
  | t :: ts, L :: Ls, ε :: εs =>
    (match logAbsQ nL (c - t.2) with
     | some (v, e) => decide (qabs' (v - L) + e ≤ ε)
     | none => false) && logsCheck nL c ts Ls εs
  | _, _, _ => false

theorem logsCheck_spec (nL : ℕ) (c : ℚ) : ∀ (plogs : List (List ℚ × ℚ)) (Ls εs : List ℚ),
    logsCheck nL c plogs Ls εs = true → LogVals c plogs Ls εs := by
  intro plogs
  induction plogs with
  | nil =>
    intro Ls εs h
    cases Ls <;> cases εs <;> simp_all [logsCheck, LogVals]
  | cons t ts ih =>
    intro Ls εs h
    cases Ls with
    | nil => simp [logsCheck] at h
    | cons L Ls =>
      cases εs with
      | nil => simp [logsCheck] at h
      | cons ε εs =>
        simp only [logsCheck, Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        refine ⟨?_, ih Ls εs h2⟩
        split at h1
        · rename_i v e hv
          simp only [decide_eq_true_eq] at h1
          have hE := (logAbsQ_spec hv).2
          unfold Enc at hE
          have e1 : ((c - t.2 : ℚ) : ℝ) = (c : ℝ) - (t.2 : ℝ) := by push_cast; ring
          rw [e1] at hE
          have h1' : |(v : ℝ) - (L : ℝ)| + (e : ℝ) ≤ (ε : ℝ) := by
            have := (Rat.cast_le (K := ℝ)).mpr h1
            rw [Rat.cast_add, qabs'_cast] at this
            push_cast at this
            exact this
          generalize hlg : Real.log (abs ((c : ℝ) - (t.2 : ℝ))) = lg at hE ⊢
          have w1 := abs_le.mp hE
          have w2 := abs_le.mp (le_refl |(v : ℝ) - (L : ℝ)|)
          have w3 := abs_nonneg ((v : ℝ) - (L : ℝ))
          rw [abs_le]
          constructor <;> linarith [w1.1, w1.2, w2.1, w2.2]
        · simp at h1

/-- One cell with all heavy literals precomputed: centre `cc`, logarithm values `Ls ± εs`. -/
def cellW (fq : FieldQ) (nLc Pc nLp nAp Pp : ℕ) (cc blo bhi lo hi : ℚ) (Ls εs : List ℚ)
    (A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ) : Bool :=
  decide (cc = (lo + hi) / 2) && logsCheck nLc cc fq.plogs Ls εs &&
  (match anchorUB2 nLc Pc nLp nAp Pp fq cc with
   | some v => decide (v ≤ A0)
   | none => false) &&
  decide (blo ≤ lo) && decide (hi ≤ bhi) &&
  (let cs := fieldCoefs fq Ls cc (Bl.length + 2)
   let es := plogErrSum cc (Bl.length + 2) fq.plogs εs
   decide (l1 ≤ cs.getD 1 0 - es.getD 1 0) && decide (cs.getD 1 0 + es.getD 1 0 ≤ u1) &&
   decide (cs.getD 2 0 + es.getD 2 0 ≤ A2) &&
   absLeEL (cs.drop 3) (es.drop 3) Bl &&
   decide (tmUBQ A0 l1 u1 A2 ((hi - lo) / 2) Bl BM ≤ T))

theorem cellW_sound (fq : FieldQ) (nLc Pc nLp nAp Pp : ℕ) (cc blo bhi lo hi : ℚ) (Ls εs : List ℚ)
    (A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ)
    (hchk : cellW fq nLc Pc nLp nAp Pp cc blo bhi lo hi Ls εs A0 l1 u1 A2 Bl BM T = true)
    (hB : BlockFacts fq blo bhi (Bl.length + 3) BM) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), fieldTower fq (poleF fq.poles) 0 x ≤ (T : ℝ) := by
  unfold cellW at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hcc, hlc⟩, hanch⟩, hb1⟩, hb2⟩, ⟨⟨⟨⟨hl1, hu1⟩, hA2⟩, hL⟩, hT⟩⟩ := hchk
  subst hcc
  set c : ℚ := (lo + hi) / 2 with hc
  set r : ℚ := (hi - lo) / 2 with hr
  have hLs := logsCheck_spec nLc c fq.plogs Ls εs hlc
  obtain ⟨v, hv, hvA⟩ : ∃ v, anchorUB2 nLc Pc nLp nAp Pp fq c = some v ∧ v ≤ A0 := by
    revert hanch
    cases hh : anchorUB2 nLc Pc nLp nAp Pp fq c with
    | none => simp
    | some v => intro h; exact ⟨v, rfl, by simpa using h⟩
  have e1 : (c : ℝ) - (r : ℝ) = (lo : ℝ) := by simp only [hc, hr]; push_cast; ring
  have e2 : (c : ℝ) + (r : ℝ) = (hi : ℝ) := by simp only [hc, hr]; push_cast; ring
  have hcell : Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)) = Icc (lo : ℝ) (hi : ℝ) := by
    rw [e1, e2]
  have hsub : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), x ∈ Icc (blo : ℝ) (bhi : ℝ) := by
    intro x hx
    exact ⟨le_trans (by exact_mod_cast hb1) hx.1, le_trans hx.2 (by exact_mod_cast hb2)⟩
  have hsub' : ∀ x ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)), x ∈ Icc (blo : ℝ) (bhi : ℝ) := by
    intro x hx; rw [hcell] at hx; exact hsub x hx
  intro x hx
  have hle : (lo : ℝ) ≤ hi := le_trans hx.1 hx.2
  have hnec : ∀ t ∈ fq.plogs, c - t.2 ≠ 0 := by
    intro t ht hz
    have hcm : (c : ℝ) ∈ Icc (blo : ℝ) (bhi : ℝ) :=
      hsub' _ ⟨by simp only [hr]; push_cast; linarith, by simp only [hr]; push_cast; linarith⟩
    apply hB.plog t ht c hcm
    have : c = t.2 := by linarith
    rw [this]
  have hT0 := isTower_fieldTower fq (poleF fq.poles) (c : ℝ) (r : ℝ) (Bl.length + 3)
    (fun t ht y hy => hB.plog t ht y (hsub' y hy))
    (fun y hy q hq => hB.pole q hq y (hsub' y hy))
    (fun y hy => hB.deriv y (hsub' y hy))
  have hspec := fun k hk1 hk =>
    fieldCoefs_approx fq (poleF fq.poles) Ls εs c (Bl.length + 2) hLs hnec k hk1 hk
  have h0 : fieldTower fq (poleF fq.poles) 0 (c : ℝ) ≤ (A0 : ℝ) :=
    (anchorUB2_spec nLc Pc nLp nAp Pp fq c v hv).trans (by exact_mod_cast hvA)
  exact cellCore lo hi A0 l1 u1 A2 Bl BM T _ _ hT0 hspec hl1 hu1 hA2
    (absLeAllE_of_L Bl _ _ hL) hT h0 blo bhi hb1 hb2 hB.tail x hx

end CatalanMeasure.GenD.Signed.Data.Cells

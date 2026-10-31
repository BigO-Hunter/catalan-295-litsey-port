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

/-! ### 8. Fixed-point pole coefficients, and single-use coefficient tests

The exact coefficients of the pole part are sums over ~170 poles of terms `(-1)^(k-1)/k · Re[ρ u^k]`
(`u = 1/(c - p)` rational), each a rational of thousands of bits, and the kernel pays a few
reduction steps per big-rational operation.  The checker therefore evaluates the pole part in
**integer fixed point**: `U = ⌊2^Q u⌋` (componentwise), `W_{k+1} = ⌊W_k ⊗ U / 2^Q⌋`, weights
`⌊2^Q ρ⌋`, and the integer terms `⌊±(RR·Wr - RI·Wi)/k⌋` summed over the poles as integers; the
coefficient is the sum divided by `2^(2Q)`.  The error of every coefficient is bounded by an explicit
recurrence (`fpE`, `fpTermErr`, one soundness theorem `poleVecF_err`), after `ℓ¹`-norm checks of
`U` and of the weights by integers (`fpPoleOK`).  The coefficient tests read each (short dyadic)
coefficient once, matching on the `Rat` constructor (`absLeQ`). -/

theorem floorDiv_spec (X d : ℤ) (hd : 0 < d) :
    ((X / d : ℤ) : ℚ) ≤ (X : ℚ) / d ∧ (X : ℚ) / d < ((X / d : ℤ) : ℚ) + 1 := by
  have h1 : d * (X / d) + X % d = X := Int.mul_ediv_add_emod X d
  have hr0 : 0 ≤ X % d := Int.emod_nonneg _ hd.ne'
  have hr1 : X % d < d := Int.emod_lt_of_pos _ hd
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have h2 : (d : ℚ) * ((X / d : ℤ) : ℚ) + ((X % d : ℤ) : ℚ) = X := by exact_mod_cast h1
  have hr0q : (0 : ℚ) ≤ ((X % d : ℤ) : ℚ) := by exact_mod_cast hr0
  have hr1q : ((X % d : ℤ) : ℚ) < d := by exact_mod_cast hr1
  constructor
  · rw [le_div_iff₀ hdq]; linarith
  · rw [div_lt_iff₀ hdq]; nlinarith

/-- `⌊2^Q x⌋` -/
def fpRound (Q : ℕ) (x : ℚ) : ℤ := x.num * 2 ^ Q / (x.den : ℤ)

theorem fpRound_spec (Q : ℕ) (x : ℚ) :
    0 ≤ x - (fpRound Q x : ℚ) / 2 ^ Q ∧ x - (fpRound Q x : ℚ) / 2 ^ Q ≤ 1 / 2 ^ Q :=
  dyRound_spec Q x

def sgn (k : ℕ) : ℤ := if k % 2 = 1 then 1 else -1

theorem sgn_eq (k : ℕ) (hk : 1 ≤ k) : ((-1 : ℚ) ^ (k - 1)) = ((sgn k : ℤ) : ℚ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  rcases Nat.even_or_odd j with h | h
  · rw [h.neg_one_pow]
    have : (j + 1) % 2 = 1 := by obtain ⟨t, rfl⟩ := h; omega
    simp [sgn, this]
  · rw [h.neg_one_pow]
    have : ¬ (j + 1) % 2 = 1 := by obtain ⟨t, rfl⟩ := h; omega
    simp [sgn, this]

theorem sgn_abs (k : ℕ) : |((sgn k : ℤ) : ℚ)| = 1 := by
  unfold sgn
  split_ifs <;> simp

/-- fixed-point complex product: both components floor-divided by `2^Q` -/
def fpMul (Q : ℕ) (a b : ℤ × ℤ) : ℤ × ℤ :=
  ((a.1 * b.1 - a.2 * b.2) / (2 ^ Q : ℤ), (a.1 * b.2 + a.2 * b.1) / (2 ^ Q : ℤ))

/-- the powers `W_1, ..., W_n` (scaled by `2^Q`), each from the previous one -/
def fpLoop (Q : ℕ) (U : ℤ × ℤ) : ℕ → ℤ × ℤ → List (ℤ × ℤ)
  | 0, _ => []
  | n + 1, w => fpMul Q w U :: fpLoop Q U n (fpMul Q w U)

/-- integer terms `⌊(-1)^(k-1) (RR Wr - RI Wi) / k⌋`, `k = k0, k0+1, ...` -/
def fpTerms (RR RI : ℤ) : ℕ → List (ℤ × ℤ) → List ℤ
  | _, [] => []
  | k, w :: ws => (sgn k * (RR * w.1 - RI * w.2) / (k : ℤ)) :: fpTerms RR RI (k + 1) ws

/-- the integer coefficient vector `[0, T_1, ..., T_M]` of one pole -/
def fpPole (Q : ℕ) (q : PoleR) (c : ℚ) (M : ℕ) : List ℤ :=
  0 :: fpTerms (fpRound Q q.rr) (fpRound Q q.ri) 1
    (fpLoop Q (fpRound Q (uOf q c).1, fpRound Q (uOf q c).2) M ((2 : ℤ) ^ Q, 0))

def vecAddZ : List ℤ → List ℤ → List ℤ
  | a :: as, b :: bs => (a + b) :: vecAddZ as bs
  | [], bs => bs
  | as, [] => as

theorem vecAddZ_getD : ∀ (a b : List ℤ) (k : ℕ), (vecAddZ a b).getD k 0 = a.getD k 0 + b.getD k 0 := by
  intro a
  induction a with
  | nil => intro b k; simp [vecAddZ]
  | cons x xs ih =>
    intro b k
    cases b with
    | nil => simp [vecAddZ]
    | cons y ys =>
      cases k with
      | zero => simp [vecAddZ]
      | succ k =>
        simp only [vecAddZ, List.getD_cons_succ]
        rw [ih ys k]

def vecSumZ (ls : List (List ℤ)) : List ℤ := ls.foldr vecAddZ []

theorem vecSumZ_getD (ls : List (List ℤ)) (k : ℕ) :
    (vecSumZ ls).getD k 0 = (ls.map (fun v => v.getD k 0)).sum := by
  induction ls with
  | nil => simp [vecSumZ]
  | cons v vs ih => simp only [vecSumZ, List.foldr_cons] at ih ⊢; rw [vecAddZ_getD, ih]; simp

def poleVecZ (Q : ℕ) (poles : List PoleR) (c : ℚ) (M : ℕ) : List ℤ :=
  vecSumZ (poles.map (fun q => fpPole Q q c M))

/-- the pole coefficients as rationals (dyadic, denominator `2^(2Q)`) -/
def poleVecF (Q : ℕ) (poles : List PoleR) (c : ℚ) (M : ℕ) : List ℚ :=
  List.map (fun z : ℤ => (z : ℚ) / ((2 : ℚ) ^ Q) ^ 2) (poleVecZ Q poles c M)

/-- integer `ℓ¹` checks of `U = ⌊2^Q u⌋` (bound `Mi`) and of the weights (bound `Wi`) -/
def fpPoleOK (Q Mi Wi : ℕ) (q : PoleR) (c : ℚ) : Bool :=
  decide ((fpRound Q (uOf q c).1).natAbs + (fpRound Q (uOf q c).2).natAbs ≤ Mi) &&
  decide ((fpRound Q q.rr).natAbs + (fpRound Q q.ri).natAbs ≤ Wi)

/-- the error recurrence `E_{k+1} = E_k (m + δ) + m^k δ + η` of the fixed-point powers -/
def fpE (m δ η : ℚ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => fpE m δ η k * (m + δ) + m ^ k * δ + η

/-- error of one pole's `k`-th coefficient (`m = (Mi + 2)/2^Q`, `δ = η = 2/2^Q`) -/
def fpTermErr (Q Mi Wi k : ℕ) : ℚ :=
  (1 / (k : ℚ)) * ((1 / 2 ^ Q) * (((Mi : ℚ) + 2) / 2 ^ Q) ^ k +
      ((Wi : ℚ) / 2 ^ Q) * fpE (((Mi : ℚ) + 2) / 2 ^ Q) (2 / 2 ^ Q) (2 / 2 ^ Q) k) + 1 / ((2 : ℚ) ^ Q) ^ 2

def poleErrF (Q Mi Wi n N : ℕ) : List ℚ :=
  (List.range (N + 1)).map (fun k => (n : ℚ) * fpTermErr Q Mi Wi k)

def fpHat (Q : ℕ) (W : ℤ × ℤ) : ℚ × ℚ := ((W.1 : ℚ) / 2 ^ Q, (W.2 : ℚ) / 2 ^ Q)

def dn (x y : ℚ × ℚ) : ℚ := |x.1 - y.1| + |x.2 - y.2|
def n1 (x : ℚ × ℚ) : ℚ := |x.1| + |x.2|

theorem cmul_n1 (x y : ℚ × ℚ) : n1 (cmulQ x y) ≤ n1 x * n1 y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [n1, cmulQ]
  have h1 : |a * c - b * d| ≤ |a * c| + |b * d| := by
    have := abs_add_le (a * c) (-(b * d))
    rwa [abs_neg, ← sub_eq_add_neg] at this
  have h2 : |a * d + b * c| ≤ |a * d| + |b * c| := abs_add_le _ _
  simp only [abs_mul] at h1 h2
  nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg d]

theorem n1_cpow (u : ℚ × ℚ) (m : ℚ) (hm : n1 u ≤ m) : ∀ k, n1 (cpowQ u k) ≤ m ^ k := by
  intro k
  induction k with
  | zero => simp [cpowQ, n1]
  | succ k ih =>
    simp only [cpowQ]
    refine (cmul_n1 _ _).trans ?_
    rw [pow_succ]
    exact mul_le_mul ih hm (by simp [n1]; positivity) (le_trans (by simp [n1]; positivity) ih)

theorem fpE_nonneg (m δ η : ℚ) (hm : 0 ≤ m) (hδ : 0 ≤ δ) (hη : 0 ≤ η) : ∀ k, 0 ≤ fpE m δ η k := by
  intro k
  induction k with
  | zero => simp [fpE]
  | succ k ih =>
    simp only [fpE]
    have := pow_nonneg hm k
    positivity

/-- one floor division by `2^Q` -/
theorem comp_floor (X : ℤ) (Q : ℕ) :
    ∃ r : ℚ, 0 ≤ r ∧ r ≤ 1 / 2 ^ Q ∧
      ((X / (2 ^ Q : ℤ) : ℤ) : ℚ) / 2 ^ Q = (X : ℚ) / 2 ^ Q / 2 ^ Q - r := by
  have hG : (0 : ℤ) < 2 ^ Q := by positivity
  obtain ⟨f1, f2⟩ := floorDiv_spec X (2 ^ Q) hG
  have hGq : (0 : ℚ) < 2 ^ Q := by positivity
  push_cast at f1 f2
  refine ⟨(X : ℚ) / 2 ^ Q / 2 ^ Q - ((X / (2 ^ Q : ℤ) : ℤ) : ℚ) / 2 ^ Q, ?_, ?_, by ring⟩
  · rw [sub_nonneg]; exact div_le_div_of_nonneg_right f1 hGq.le
  · have : (X : ℚ) / 2 ^ Q / 2 ^ Q - ((X / (2 ^ Q : ℤ) : ℤ) : ℚ) / 2 ^ Q =
        ((X : ℚ) / 2 ^ Q - ((X / (2 ^ Q : ℤ) : ℤ) : ℚ)) / 2 ^ Q := by ring
    rw [this]
    exact div_le_div_of_nonneg_right (by linarith) hGq.le

theorem fpMul_hat (Q : ℕ) (a b : ℤ × ℤ) :
    ∃ r1 r2 : ℚ, 0 ≤ r1 ∧ r1 ≤ 1 / 2 ^ Q ∧ 0 ≤ r2 ∧ r2 ≤ 1 / 2 ^ Q ∧
      fpHat Q (fpMul Q a b) =
        ((cmulQ (fpHat Q a) (fpHat Q b)).1 - r1, (cmulQ (fpHat Q a) (fpHat Q b)).2 - r2) := by
  obtain ⟨r1, h1, h1', e1⟩ := comp_floor (a.1 * b.1 - a.2 * b.2) Q
  obtain ⟨r2, h2, h2', e2⟩ := comp_floor (a.1 * b.2 + a.2 * b.1) Q
  refine ⟨r1, r2, h1, h1', h2, h2', ?_⟩
  simp only [fpHat, fpMul, cmulQ]
  refine Prod.ext ?_ ?_
  · simp only
    rw [e1]; push_cast; ring
  · simp only
    rw [e2]; push_cast; ring

theorem poleVec_eq_sum (poles : List PoleR) (c : ℚ) (M k : ℕ) :
    (poleVec poles c M).getD k 0 =
      (poles.map (fun q => (poleVecTab q.rr q.ri (powTabQ q.pr q.pi c M)).getD k 0)).sum := by
  unfold poleVec poleVecShared poleTabs
  rw [vecSum_getD]
  have hzip : List.zipWith (fun q tab => poleVecTab q.rr q.ri tab) poles
      (poles.map (fun q => powTabQ q.pr q.pi c M)) =
      poles.map (fun q => poleVecTab q.rr q.ri (powTabQ q.pr q.pi c M)) := by
    induction poles with
    | nil => rfl
    | cons q qs ih => simp [List.zipWith_cons_cons, ih]
  rw [hzip, List.map_map]
  rfl

theorem sum_map_err {α : Type} (l : List α) (f g : α → ℚ) (δ : ℚ)
    (h : ∀ a ∈ l, |f a - g a| ≤ δ) :
    |(l.map f).sum - (l.map g).sum| ≤ (l.length : ℚ) * δ := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have e : f a + (as.map f).sum - (g a + (as.map g).sum) =
        (f a - g a) + ((as.map f).sum - (as.map g).sum) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    push_cast
    linarith

theorem powTabQ_getD' (q : PoleR) (c : ℚ) (M j : ℕ) (hj : j < M) :
    (powTabQ q.pr q.pi c M).getD j (0, 0) = cpowQ (uOf q c) (j + 1) := by
  unfold powTabQ
  have := powTabAux_getD (uOf ⟨0, 0, q.pr, q.pi⟩ c) M 1 (uOf ⟨0, 0, q.pr, q.pi⟩ c)
    (by simp [cpowQ, cmulQ]) j hj
  rw [this, add_comm 1 j]
  rfl

theorem n1_nonneg (x : ℚ × ℚ) : 0 ≤ n1 x := by unfold n1; positivity

theorem fp_step (x v Uh u : ℚ × ℚ) (r1 r2 m δ E mk : ℚ) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (hx : dn x v ≤ E) (hv : n1 v ≤ mk) (hu : n1 u ≤ m) (hd : dn Uh u ≤ δ) (hE : 0 ≤ E)
    (_hδ : 0 ≤ δ) (_hm : 0 ≤ m) :
    dn ((cmulQ x Uh).1 - r1, (cmulQ x Uh).2 - r2) (cmulQ v u) ≤ (mk + E) * δ + E * m + (r1 + r2) := by
  set d : ℚ × ℚ := (Uh.1 - u.1, Uh.2 - u.2) with hdd
  set e : ℚ × ℚ := (x.1 - v.1, x.2 - v.2) with hee
  have hA := cmul_n1 x d
  have hB := cmul_n1 e u
  have hn1d : n1 d = dn Uh u := rfl
  have hn1e : n1 e = dn x v := rfl
  have hnx : n1 x ≤ mk + E := by
    have h1 : |x.1| ≤ |v.1| + |x.1 - v.1| := by
      have := abs_add_le v.1 (x.1 - v.1); simpa using this
    have h2 : |x.2| ≤ |v.2| + |x.2 - v.2| := by
      have := abs_add_le v.2 (x.2 - v.2); simpa using this
    unfold n1 at *; unfold dn at hx; linarith
  have c1 : (cmulQ x Uh).1 - r1 - (cmulQ v u).1 = (cmulQ x d).1 + (cmulQ e u).1 - r1 := by
    simp only [cmulQ, hdd, hee]; ring
  have c2 : (cmulQ x Uh).2 - r2 - (cmulQ v u).2 = (cmulQ x d).2 + (cmulQ e u).2 - r2 := by
    simp only [cmulQ, hdd, hee]; ring
  have key : dn ((cmulQ x Uh).1 - r1, (cmulQ x Uh).2 - r2) (cmulQ v u) ≤
      n1 (cmulQ x d) + n1 (cmulQ e u) + (r1 + r2) := by
    unfold dn
    simp only []
    rw [c1, c2]
    unfold n1
    have t1 : |(cmulQ x d).1 + (cmulQ e u).1 - r1| ≤ |(cmulQ x d).1| + |(cmulQ e u).1| + r1 := by
      have := abs_add_le ((cmulQ x d).1 + (cmulQ e u).1) (-r1)
      rw [abs_neg, abs_of_nonneg hr1, ← sub_eq_add_neg] at this
      exact this.trans (by linarith [abs_add_le ((cmulQ x d).1) ((cmulQ e u).1)])
    have t2 : |(cmulQ x d).2 + (cmulQ e u).2 - r2| ≤ |(cmulQ x d).2| + |(cmulQ e u).2| + r2 := by
      have := abs_add_le ((cmulQ x d).2 + (cmulQ e u).2) (-r2)
      rw [abs_neg, abs_of_nonneg hr2, ← sub_eq_add_neg] at this
      exact this.trans (by linarith [abs_add_le ((cmulQ x d).2) ((cmulQ e u).2)])
    linarith
  have hu0 := n1_nonneg u
  have hnx0 := n1_nonneg x
  have hd0 := n1_nonneg d
  have he0 := n1_nonneg e
  have b1 : n1 (cmulQ x d) ≤ (mk + E) * δ :=
    hA.trans (mul_le_mul hnx (hn1d ▸ hd) hd0 (by linarith))
  have b2 : n1 (cmulQ e u) ≤ E * m :=
    hB.trans (mul_le_mul (hn1e ▸ hx) hu hu0 hE)
  linarith

/-- the fixed-point powers stay within `E_k` of the exact ones -/
theorem fpLoop_err (Q : ℕ) (u : ℚ × ℚ) (U : ℤ × ℤ) (m δ η : ℚ) (hm : 0 ≤ m) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hu : n1 u ≤ m) (hU : dn (fpHat Q U) u ≤ δ) (hη2 : 2 / 2 ^ Q ≤ η) :
    ∀ (n k : ℕ) (W : ℤ × ℤ), dn (fpHat Q W) (cpowQ u k) ≤ fpE m δ η k →
      ∀ i < n, dn (fpHat Q ((fpLoop Q U n W).getD i (0, 0))) (cpowQ u (k + i + 1)) ≤
        fpE m δ η (k + i + 1) := by
  intro n
  induction n with
  | zero => intro k W _ i hi; omega
  | succ n ih =>
    intro k W hW i hi
    have step : dn (fpHat Q (fpMul Q W U)) (cpowQ u (k + 1)) ≤ fpE m δ η (k + 1) := by
      obtain ⟨r1, r2, h1, h1', h2, h2', e⟩ := fpMul_hat Q W U
      have hn1v := n1_cpow u m hu k
      have hE := fpE_nonneg m δ η hm hδ hη k
      have hfm := fp_step (fpHat Q W) (cpowQ u k) (fpHat Q U) u r1 r2 m δ (fpE m δ η k) (m ^ k)
        h1 h2 hW hn1v hu hU hE hδ hm
      rw [e]
      have hc : cpowQ u (k + 1) = cmulQ (cpowQ u k) u := rfl
      rw [hc]
      refine hfm.trans ?_
      simp only [fpE]
      have : (2 : ℚ) / 2 ^ Q = 1 / 2 ^ Q + 1 / 2 ^ Q := by ring
      nlinarith
    cases i with
    | zero => simpa [fpLoop] using step
    | succ i =>
      have := ih (k + 1) (fpMul Q W U) step i (by omega)
      simp only [fpLoop, List.getD_cons_succ]
      rw [show k + 1 + i + 1 = k + (i + 1) + 1 by omega] at this
      exact this

theorem fpLoop_length (Q : ℕ) (U : ℤ × ℤ) : ∀ (n : ℕ) (W : ℤ × ℤ), (fpLoop Q U n W).length = n := by
  intro n
  induction n with
  | zero => intro W; rfl
  | succ n ih => intro W; simp [fpLoop, ih]

theorem fpTerms_getD (RR RI : ℤ) : ∀ (ws : List (ℤ × ℤ)) (k i : ℕ), i < ws.length →
    (fpTerms RR RI k ws).getD i 0 =
      sgn (k + i) * (RR * (ws.getD i (0, 0)).1 - RI * (ws.getD i (0, 0)).2) / ((k + i : ℕ) : ℤ) := by
  intro ws
  induction ws with
  | nil => intro k i hi; simp at hi
  | cons w ws ih =>
    intro k i hi
    cases i with
    | zero => simp [fpTerms]
    | succ i =>
      simp only [fpTerms, List.getD_cons_succ]
      rw [ih (k + 1) i (by simpa using hi), show k + 1 + i = k + (i + 1) by omega]

theorem lin2 (a b c d M : ℚ) (ha : |a| ≤ M) (hb : |b| ≤ M) : |a * c + b * d| ≤ M * (|c| + |d|) := by
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_right ha (abs_nonneg c), mul_le_mul_of_nonneg_right hb (abs_nonneg d)]

/-- one fixed-point term of a pole differs from the exact term by at most `fpTermErr` -/
theorem fpTerm_err (Q Wi : ℕ) (rr ri : ℚ) (RR RI : ℤ) (k : ℕ) (hk : 1 ≤ k) (W : ℤ × ℤ)
    (v : ℚ × ℚ) (E mk : ℚ)
    (hrr : 0 ≤ rr - (RR : ℚ) / 2 ^ Q ∧ rr - (RR : ℚ) / 2 ^ Q ≤ 1 / 2 ^ Q)
    (hri : 0 ≤ ri - (RI : ℚ) / 2 ^ Q ∧ ri - (RI : ℚ) / 2 ^ Q ≤ 1 / 2 ^ Q)
    (hW : RR.natAbs + RI.natAbs ≤ Wi) (hx : dn (fpHat Q W) v ≤ E) (hv : n1 v ≤ mk) :
    |poleTermQ rr ri k v - ((sgn k * (RR * W.1 - RI * W.2) / (k : ℤ) : ℤ) : ℚ) / ((2 : ℚ) ^ Q) ^ 2| ≤
      (1 / (k : ℚ)) * ((1 / 2 ^ Q) * mk + ((Wi : ℚ) / 2 ^ Q) * E) + 1 / ((2 : ℚ) ^ Q) ^ 2 := by
  have hG : (0 : ℚ) < 2 ^ Q := by positivity
  have hkq : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hkz : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  set X : ℤ := sgn k * (RR * W.1 - RI * W.2) with hXdef
  obtain ⟨f1, f2⟩ := floorDiv_spec X (k : ℤ) hkz
  push_cast at f1 f2
  set T : ℤ := X / (k : ℤ) with hT
  set G : ℚ := 2 ^ Q with hGdef
  set sg : ℚ := ((sgn k : ℤ) : ℚ) with hsgdef
  have hsg : |sg| = 1 := sgn_abs k
  have hterm : poleTermQ rr ri k v = sg / k * (rr * v.1 - ri * v.2) := by
    unfold poleTermQ; rw [sgn_eq k hk]
  set rhr : ℚ := (RR : ℚ) / G with hrhr
  set rhi : ℚ := (RI : ℚ) / G with hrhi
  set x1 : ℚ := (W.1 : ℚ) / G with hx1
  set x2 : ℚ := (W.2 : ℚ) / G with hx2
  have hX : (X : ℚ) = sg * G ^ 2 * (rhr * x1 - rhi * x2) := by
    simp only [hXdef, hrhr, hrhi, hx1, hx2, hsgdef]
    push_cast
    field_simp
  set B : ℚ := (rr * v.1 - ri * v.2) - (rhr * x1 - rhi * x2) with hB
  have e : poleTermQ rr ri k v - (T : ℚ) / G ^ 2 = sg / k * B + ((X : ℚ) / k - T) / G ^ 2 := by
    rw [hterm, hB]
    have : (X : ℚ) / k / G ^ 2 = sg / k * (rhr * x1 - rhi * x2) := by
      rw [hX]; field_simp
    have h2 : ((X : ℚ) / k - T) / G ^ 2 = (X : ℚ) / k / G ^ 2 - (T : ℚ) / G ^ 2 := by ring
    rw [h2, this]; ring
  -- bound on B
  have hrr0 := hrr.1
  have hrr1 := hrr.2
  have hri0 := hri.1
  have hri1 := hri.2
  have hWq : (RR.natAbs : ℚ) + (RI.natAbs : ℚ) ≤ (Wi : ℚ) := by exact_mod_cast hW
  have habsRR : |(RR : ℚ)| = (RR.natAbs : ℚ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  have habsRI : |(RI : ℚ)| = (RI.natAbs : ℚ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hrhr_le : |rhr| ≤ (Wi : ℚ) / G := by
    rw [hrhr, abs_div, abs_of_pos hG, habsRR]
    exact div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℚ) RI.natAbs]) hG.le
  have hrhi_le : |rhi| ≤ (Wi : ℚ) / G := by
    rw [hrhi, abs_div, abs_of_pos hG, habsRI]
    exact div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℚ) RR.natAbs]) hG.le
  have ha : |rr - rhr| ≤ 1 / G := by rw [abs_of_nonneg hrr0]; exact hrr1
  have hb : |-(ri - rhi)| ≤ 1 / G := by rw [abs_neg, abs_of_nonneg hri0]; exact hri1
  have hnrhi : |-rhi| ≤ (Wi : ℚ) / G := by rw [abs_neg]; exact hrhi_le
  have l1 := lin2 (rr - rhr) (-(ri - rhi)) v.1 v.2 (1 / G) ha hb
  have l2 := lin2 rhr (-rhi) (v.1 - x1) (v.2 - x2) ((Wi : ℚ) / G) hrhr_le hnrhi
  have hBeq : B = ((rr - rhr) * v.1 + (-(ri - rhi)) * v.2) + (rhr * (v.1 - x1) + (-rhi) * (v.2 - x2)) := by
    rw [hB]; ring
  have hxx : |v.1 - x1| + |v.2 - x2| ≤ E := by
    unfold dn at hx
    have a1 : |v.1 - x1| = |x1 - v.1| := abs_sub_comm _ _
    have a2 : |v.2 - x2| = |x2 - v.2| := abs_sub_comm _ _
    simp only [fpHat] at hx
    rw [a1, a2]; exact hx
  have hvv : |v.1| + |v.2| ≤ mk := hv
  have hBb : |B| ≤ (1 / G) * mk + ((Wi : ℚ) / G) * E := by
    rw [hBeq]
    refine (abs_add_le _ _).trans ?_
    have p1 : (1 / G) * (|v.1| + |v.2|) ≤ (1 / G) * mk :=
      mul_le_mul_of_nonneg_left hvv (by positivity)
    have p2 : ((Wi : ℚ) / G) * (|v.1 - x1| + |v.2 - x2|) ≤ ((Wi : ℚ) / G) * E :=
      mul_le_mul_of_nonneg_left hxx (by positivity)
    linarith
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have t1 : |sg / k * B| ≤ (1 / (k : ℚ)) * ((1 / G) * mk + ((Wi : ℚ) / G) * E) := by
    rw [abs_mul, abs_div, hsg, abs_of_pos hkq]
    exact mul_le_mul_of_nonneg_left hBb (by positivity)
  have t2 : |((X : ℚ) / k - T) / G ^ 2| ≤ 1 / G ^ 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℚ) < G ^ 2)]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [abs_of_nonneg (by linarith)]
    linarith
  linarith

theorem getD_map_zero {α : Type} (l : List α) (g : α → ℚ) (d : α) (hg : g d = 0) (k : ℕ) :
    (l.map g).getD k 0 = g (l.getD k d) := by
  induction l generalizing k with
  | nil => simp [hg]
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k => simp only [List.map_cons, List.getD_cons_succ]; exact ih k

theorem cast_sum_div {α : Type} (l : List α) (f : α → ℤ) (D : ℚ) :
    (((l.map f).sum : ℤ) : ℚ) / D = (l.map (fun a => ((f a : ℤ) : ℚ) / D)).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, Int.cast_add, add_div, ih]

/-- **Soundness of the fixed-point pole coefficients**: every coefficient `k ≥ 1` of `poleVecF`
is within `n · fpTermErr` of the exact one (`poleVec`), provided every pole passes `fpPoleOK`. -/
theorem poleVecF_err (Q Mi Wi : ℕ) (poles : List PoleR) (c : ℚ) (M k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ M)
    (hok : ∀ q ∈ poles, fpPoleOK Q Mi Wi q c = true) :
    |(poleVecF Q poles c M).getD k 0 - (poleVec poles c M).getD k 0| ≤
      (poles.length : ℚ) * fpTermErr Q Mi Wi k := by
  have hG : (0 : ℚ) < 2 ^ Q := by positivity
  have hD : (poleVecF Q poles c M).getD k 0 =
      (poles.map (fun q => (((fpPole Q q c M).getD k 0 : ℤ) : ℚ) / ((2 : ℚ) ^ Q) ^ 2)).sum := by
    unfold poleVecF
    rw [getD_map_zero (poleVecZ Q poles c M) (fun z : ℤ => (z : ℚ) / ((2 : ℚ) ^ Q) ^ 2) 0 (by simp)]
    unfold poleVecZ
    rw [vecSumZ_getD, cast_sum_div, List.map_map]
    rfl
  rw [hD, poleVec_eq_sum, abs_sub_comm]
  have key := sum_map_err poles
    (fun q => (poleVecTab q.rr q.ri (powTabQ q.pr q.pi c M)).getD k 0)
    (fun q => (((fpPole Q q c M).getD k 0 : ℤ) : ℚ) / ((2 : ℚ) ^ Q) ^ 2)
    (fpTermErr Q Mi Wi k) (by
      intro q hq
      have hqok := hok q hq
      unfold fpPoleOK at hqok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hqok
      obtain ⟨hMi, hWi⟩ := hqok
      -- data of the pole
      set u := uOf q c with hu
      set U : ℤ × ℤ := (fpRound Q u.1, fpRound Q u.2) with hUdef
      have s1 := fpRound_spec Q u.1
      have s2 := fpRound_spec Q u.2
      have hdU : dn (fpHat Q U) u ≤ 2 / 2 ^ Q := by
        unfold dn fpHat
        simp only [hUdef]
        rw [abs_sub_comm, abs_of_nonneg s1.1, abs_sub_comm (((fpRound Q u.2 : ℤ) : ℚ) / 2 ^ Q),
          abs_of_nonneg s2.1]
        have : 2 / (2 : ℚ) ^ Q = 1 / 2 ^ Q + 1 / 2 ^ Q := by ring
        linarith [s1.2, s2.2]
      have hn1u : n1 u ≤ ((Mi : ℚ) + 2) / 2 ^ Q := by
        have a1 : |u.1| ≤ |((fpRound Q u.1 : ℤ) : ℚ) / 2 ^ Q| + 1 / 2 ^ Q := by
          have := abs_add_le (((fpRound Q u.1 : ℤ) : ℚ) / 2 ^ Q) (u.1 - ((fpRound Q u.1 : ℤ) : ℚ) / 2 ^ Q)
          rw [abs_of_nonneg s1.1] at this
          simp only [add_sub_cancel] at this
          linarith [s1.2]
        have a2 : |u.2| ≤ |((fpRound Q u.2 : ℤ) : ℚ) / 2 ^ Q| + 1 / 2 ^ Q := by
          have := abs_add_le (((fpRound Q u.2 : ℤ) : ℚ) / 2 ^ Q) (u.2 - ((fpRound Q u.2 : ℤ) : ℚ) / 2 ^ Q)
          rw [abs_of_nonneg s2.1] at this
          simp only [add_sub_cancel] at this
          linarith [s2.2]
        have habs : ∀ z : ℤ, |((z : ℤ) : ℚ) / 2 ^ Q| = (z.natAbs : ℚ) / 2 ^ Q := by
          intro z
          rw [abs_div, abs_of_pos hG, Nat.cast_natAbs, Int.cast_abs]
        rw [habs] at a1 a2
        have hMq : ((fpRound Q u.1).natAbs : ℚ) + ((fpRound Q u.2).natAbs : ℚ) ≤ (Mi : ℚ) := by
          exact_mod_cast hMi
        unfold n1
        have : (((fpRound Q u.1).natAbs : ℚ) + ((fpRound Q u.2).natAbs : ℚ)) / 2 ^ Q ≤ (Mi : ℚ) / 2 ^ Q :=
          div_le_div_of_nonneg_right hMq hG.le
        rw [add_div] at this
        have h3 : ((Mi : ℚ) + 2) / 2 ^ Q = (Mi : ℚ) / 2 ^ Q + 1 / 2 ^ Q + 1 / 2 ^ Q := by ring
        linarith
      have hm0 : (0 : ℚ) ≤ ((Mi : ℚ) + 2) / 2 ^ Q := by positivity
      have hloop := fpLoop_err Q u U (((Mi : ℚ) + 2) / 2 ^ Q) (2 / 2 ^ Q) (2 / 2 ^ Q) hm0
        (by positivity) (by positivity) hn1u hdU le_rfl M 0 ((2 : ℤ) ^ Q, 0) (by
          simp [dn, fpHat, fpE, cpowQ])
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hjM : j < M := by omega
      have hl := hloop j hjM
      rw [zero_add] at hl
      -- the exact term
      have hex : (poleVecTab q.rr q.ri (powTabQ q.pr q.pi c M)).getD (j + 1) 0 =
          poleTermQ q.rr q.ri (j + 1) (cpowQ u (j + 1)) := by
        rw [poleVecTab_getD _ _ _ _ (by omega) (by rw [powTabQ_length]; exact hk),
          powTabQ_getD' q c M (j + 1 - 1) (by omega), Nat.add_sub_cancel]
      -- the integer term
      have hz : (fpPole Q q c M).getD (j + 1) 0 =
          sgn (j + 1) * (fpRound Q q.rr * ((fpLoop Q U M ((2 : ℤ) ^ Q, 0)).getD j (0, 0)).1 -
            fpRound Q q.ri * ((fpLoop Q U M ((2 : ℤ) ^ Q, 0)).getD j (0, 0)).2) / ((j + 1 : ℕ) : ℤ) := by
        unfold fpPole
        rw [List.getD_cons_succ, fpTerms_getD _ _ _ 1 j (by rw [fpLoop_length]; exact hjM),
          add_comm 1 j]
      rw [hex, hz]
      have hterm := fpTerm_err Q Wi q.rr q.ri (fpRound Q q.rr) (fpRound Q q.ri) (j + 1) (by omega)
        ((fpLoop Q U M ((2 : ℤ) ^ Q, 0)).getD j (0, 0)) (cpowQ u (j + 1))
        (fpE (((Mi : ℚ) + 2) / 2 ^ Q) (2 / 2 ^ Q) (2 / 2 ^ Q) (j + 1)) ((((Mi : ℚ) + 2) / 2 ^ Q) ^ (j + 1))
        (fpRound_spec Q q.rr) (fpRound_spec Q q.ri) hWi (by simpa using hl)
        (n1_cpow u _ hn1u (j + 1))
      simpa [fpTermErr] using hterm)
  exact key
/-- the coefficients of the field at `c` with the pole part evaluated in fixed point -/
def fieldCoefsF (fq : FieldQ) (Ls : List ℚ) (c : ℚ) (M Q : ℕ) : List ℚ :=
  vecAdd (shiftL c M fq.poly) (vecAdd (plogSumVec c M fq.plogs Ls) (poleVecF Q fq.poles c M))

theorem fieldCoefsF_approx (fq : FieldQ) (F : ℝ → ℝ) (Ls εs : List ℚ) (c : ℚ) (M Q Mi Wi : ℕ)
    (hL : LogVals c fq.plogs Ls εs) (hne : ∀ t ∈ fq.plogs, c - t.2 ≠ 0)
    (hok : ∀ q ∈ fq.poles, fpPoleOK Q Mi Wi q c = true) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ M) :
    |fieldTower fq F k (c : ℝ) / ((k.factorial : ℕ) : ℝ) -
        (((fieldCoefsF fq Ls c M Q).getD k 0 : ℚ) : ℝ)| ≤
      (((plogErrSum c M fq.plogs εs).getD k 0 +
        (fq.poles.length : ℚ) * fpTermErr Q Mi Wi k : ℚ) : ℝ) := by
  have h := fieldCoefs_approx fq F Ls εs c M hL hne k hk1 hk
  have hd : (fieldCoefsF fq Ls c M Q).getD k 0 - (fieldCoefs fq Ls c M).getD k 0 =
      (poleVecF Q fq.poles c M).getD k 0 - (poleVec fq.poles c M).getD k 0 := by
    unfold fieldCoefsF fieldCoefs
    rw [vecAdd_getD, vecAdd_getD, vecAdd_getD, vecAdd_getD]
    ring
  have hq := poleVecF_err Q Mi Wi fq.poles c M k hk1 hk hok
  rw [← hd] at hq
  have hq' : |(((fieldCoefsF fq Ls c M Q).getD k 0 : ℚ) : ℝ) -
      (((fieldCoefs fq Ls c M).getD k 0 : ℚ) : ℝ)| ≤
      (((fq.poles.length : ℚ) * fpTermErr Q Mi Wi k : ℚ) : ℝ) := by
    exact_mod_cast hq
  have e : fieldTower fq F k (c : ℝ) / ((k.factorial : ℕ) : ℝ) -
        (((fieldCoefsF fq Ls c M Q).getD k 0 : ℚ) : ℝ) =
      (fieldTower fq F k (c : ℝ) / ((k.factorial : ℕ) : ℝ) -
          (((fieldCoefs fq Ls c M).getD k 0 : ℚ) : ℝ)) +
        ((((fieldCoefs fq Ls c M).getD k 0 : ℚ) : ℝ) -
          (((fieldCoefsF fq Ls c M Q).getD k 0 : ℚ) : ℝ)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_sub_comm (((fieldCoefs fq Ls c M).getD k 0 : ℚ) : ℝ)] at *
  rw [Rat.cast_add]
  linarith

/-- the coefficient error vector: the logarithm-enclosure errors plus the pole rounding error -/
def errVecF (c : ℚ) (N : ℕ) (plogs : List (List ℚ × ℚ)) (εs : List ℚ) (Q Mi Wi n : ℕ) : List ℚ :=
  vecAdd (plogErrSum c N plogs εs) (poleErrF Q Mi Wi n N)

theorem errVecF_getD (c : ℚ) (N : ℕ) (plogs : List (List ℚ × ℚ)) (εs : List ℚ) (Q Mi Wi n : ℕ)
    (k : ℕ) (hk : k ≤ N) :
    (errVecF c N plogs εs Q Mi Wi n).getD k 0 =
      (plogErrSum c N plogs εs).getD k 0 + (n : ℚ) * fpTermErr Q Mi Wi k := by
  unfold errVecF
  rw [vecAdd_getD]
  unfold poleErrF
  rw [getD_map_range _ _ _ (by omega)]

theorem qabs'_eq_abs (t : ℚ) : qabs' t = |t| := by
  unfold qabs'
  split_ifs with h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (not_lt.mp h)).symm

/-- `|t| ≤ c`, reading `t` once (matching on the `Rat` constructor). -/
def absLeQ (t c : ℚ) : Bool :=
  match t with
  | ⟨n, d, _, _⟩ => decide ((n.natAbs : ℚ) / (d : ℚ) ≤ c)

theorem absLeQ_spec (t c : ℚ) (h : absLeQ t c = true) : qabs' t ≤ c := by
  obtain ⟨n, d, h1, h2⟩ := t
  simp only [absLeQ, decide_eq_true_eq] at h
  have ht : (⟨n, d, h1, h2⟩ : ℚ) = (n : ℚ) / (d : ℚ) :=
    (Rat.num_div_den (⟨n, d, h1, h2⟩ : ℚ)).symm
  have hd : (0 : ℚ) < (d : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero h1
  have e : qabs' (⟨n, d, h1, h2⟩ : ℚ) = (n.natAbs : ℚ) / (d : ℚ) := by
    rw [qabs'_eq_abs, ht, abs_div, abs_of_pos hd, Nat.cast_natAbs, Int.cast_abs]
  rw [e]
  exact h

/-- `|T_i| + E_i ≤ b_i` in lockstep, each coefficient read once. -/
def absLeELQ : List ℚ → List ℚ → List ℚ → Bool
  | _, _, [] => true
  | t :: ts, e :: es, b :: bs => absLeQ t (b - e) && absLeELQ ts es bs
  | _, _, _ :: _ => false

theorem absLeEL_of_Q : ∀ (bs ts es : List ℚ), absLeELQ ts es bs = true →
    absLeEL ts es bs = true := by
  intro bs
  induction bs with
  | nil => intro ts es _; simp [absLeEL]
  | cons b bs ih =>
    intro ts es h
    cases ts with
    | nil => simp [absLeELQ] at h
    | cons t ts =>
      cases es with
      | nil => simp [absLeELQ] at h
      | cons e es =>
        simp only [absLeELQ, Bool.and_eq_true] at h
        simp only [absLeEL, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by have := absLeQ_spec _ _ h.1; linarith, ih ts es h.2⟩

/-- The coefficient tests of a cell in one lockstep pass: `l1 ≤ a₁ - e₁`, `a₁ + e₁ ≤ u1`,
`a₂ + e₂ ≤ A2`, `|a_k| + e_k ≤ B_k` for `k ≥ 3`. -/
def coefTestR (l1 u1 A2 : ℚ) (Bl : List ℚ) : List ℚ → List ℚ → Bool
  | _ :: a1 :: a2 :: rest, _ :: e1 :: e2 :: erest =>
    decide (l1 + e1 ≤ a1) && decide (a1 + e1 ≤ u1) && decide (a2 + e2 ≤ A2) &&
      absLeELQ rest erest Bl
  | _, _ => false

theorem coefTestR_spec (l1 u1 A2 : ℚ) (Bl cs es : List ℚ)
    (h : coefTestR l1 u1 A2 Bl cs es = true) :
    l1 ≤ cs.getD 1 0 - es.getD 1 0 ∧ cs.getD 1 0 + es.getD 1 0 ≤ u1 ∧
      cs.getD 2 0 + es.getD 2 0 ≤ A2 ∧ absLeEL (cs.drop 3) (es.drop 3) Bl = true := by
  rcases cs with _ | ⟨c0, _ | ⟨a1, _ | ⟨a2, rest⟩⟩⟩ <;>
    rcases es with _ | ⟨e0, _ | ⟨e1, _ | ⟨e2, erest⟩⟩⟩ <;>
    first | (simp [coefTestR] at h; done) | skip
  simp only [coefTestR, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · show l1 ≤ a1 - e1
    linarith
  · show a1 + e1 ≤ u1
    exact h2
  · show a2 + e2 ≤ A2
    exact h3
  · show absLeEL rest erest Bl = true
    exact absLeEL_of_Q _ _ _ h4

/-- One cell with all heavy literals precomputed: centre `cc`, logarithm values `Ls ± εs`.  The pole
part of the coefficients is evaluated in fixed point with grid `2^-Q` (`fieldCoefsF`), after the
integer `ℓ¹` checks `fpPoleOK Q Mi Wi`. -/
def cellW (fq : FieldQ) (nLc Pc nLp nAp Pp Q Mi Wi : ℕ) (cc blo bhi lo hi : ℚ) (Ls εs : List ℚ)
    (A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ) : Bool :=
  decide (cc = (lo + hi) / 2) && logsCheck nLc cc fq.plogs Ls εs &&
  (match anchorUB2 nLc Pc nLp nAp Pp fq cc with
   | some v => decide (v ≤ A0)
   | none => false) &&
  decide (blo ≤ lo) && decide (hi ≤ bhi) &&
  fq.poles.all (fun q => fpPoleOK Q Mi Wi q cc) &&
  coefTestR l1 u1 A2 Bl (fieldCoefsF fq Ls cc (Bl.length + 2) Q)
    (errVecF cc (Bl.length + 2) fq.plogs εs Q Mi Wi fq.poles.length) &&
  decide (tmUBQ A0 l1 u1 A2 ((hi - lo) / 2) Bl BM ≤ T)

theorem cellW_sound (fq : FieldQ) (nLc Pc nLp nAp Pp Q Mi Wi : ℕ) (cc blo bhi lo hi : ℚ)
    (Ls εs : List ℚ) (A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ)
    (hchk : cellW fq nLc Pc nLp nAp Pp Q Mi Wi cc blo bhi lo hi Ls εs A0 l1 u1 A2 Bl BM T = true)
    (hB : BlockFacts fq blo bhi (Bl.length + 3) BM) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), fieldTower fq (poleF fq.poles) 0 x ≤ (T : ℝ) := by
  unfold cellW at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨hcc, hlc⟩, hanch⟩, hb1⟩, hb2⟩, hpok⟩, htest⟩, hT⟩ := hchk
  subst hcc
  rw [List.all_eq_true] at hpok
  obtain ⟨hl1, hu1, hA2, hL⟩ := coefTestR_spec _ _ _ _ _ _ htest
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
  have hspec : ∀ k, 1 ≤ k → k ≤ Bl.length + 2 →
      |fieldTower fq (poleF fq.poles) k (c : ℝ) / ((k.factorial : ℕ) : ℝ) -
        (((fieldCoefsF fq Ls c (Bl.length + 2) Q).getD k 0 : ℚ) : ℝ)| ≤
      (((errVecF c (Bl.length + 2) fq.plogs εs Q Mi Wi fq.poles.length).getD k 0 : ℚ) : ℝ) := by
    intro k hk1 hk
    rw [errVecF_getD _ _ _ _ _ _ _ _ _ hk]
    exact fieldCoefsF_approx fq (poleF fq.poles) Ls εs c (Bl.length + 2) Q Mi Wi hLs hnec hpok k hk1 hk
  have h0 : fieldTower fq (poleF fq.poles) 0 (c : ℝ) ≤ (A0 : ℝ) :=
    (anchorUB2_spec nLc Pc nLp nAp Pp fq c v hv).trans (by exact_mod_cast hvA)
  exact cellCore lo hi A0 l1 u1 A2 Bl BM T _ _ hT0 hspec hl1 hu1 hA2
    (absLeAllE_of_L Bl _ _ hL) hT h0 blo bhi hb1 hb2 hB.tail x hx

end CatalanMeasure.GenD.Signed.Data.Cells

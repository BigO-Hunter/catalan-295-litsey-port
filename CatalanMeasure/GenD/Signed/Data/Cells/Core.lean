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
* `cellW` and `cellW_sound`: one cell of a block (integer Taylor shifts `shiftLK`, truncated fixed-point
  pole part, per-cell anchor); the block check is split into `blockRestOK`, the polynomial shift and one
  `plogItemOK` per logarithmic piece (`blockOK4`), each a separate `decide +kernel`.
* `shiftLK` (Kronecker form of `shiftLI`, proved equal to `shiftL`): the Horner steps of the Taylor
  shift on one packed integer (`hzB`, `hzC`, `unpkS`).
* `cellStep` and `cellStep_sound`: the older chained cell (not used by the Phase 2 data modules).
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


/-! ### 6b. Integer Taylor shift (exact, GMP arithmetic)

`shiftLI c M p = shiftL c M p` (`shiftLI_eq`), computed with integer Horner steps on the common
denominator `D` of `p` and `c = n / d`: after `j` steps the entry `k` is stored as
`T_k = t_k D d^(j-k)` up to the factor `d^k` (undone at the end), so no entry carries a high power
of two, and the kernel does GMP integer arithmetic instead of rational arithmetic. -/

def zStep (n : ℤ) : ℕ → List ℤ → ℤ → List ℤ
  | 0, _, _ => []
  | _ + 1, [], prev => [prev]
  | m + 1, s :: ss, prev => (n * s + prev) :: zStep n m ss s

def shZ (n : ℤ) (d cap : ℕ) : List ℤ → List ℤ × ℕ
  | [] => ([], 1)
  | A :: as =>
    match shZ n d cap as with
    | (L, pw) => (zStep n cap L (((d * pw : ℕ) : ℤ) * A), d * pw)

def toZ (D : ℕ) (a : ℚ) : ℤ := a.num * ((D / a.den : ℕ) : ℤ)

def polyD (p : List ℚ) : ℕ := p.foldl (fun m a => Nat.lcm m a.den) 1

def descaleL (d : ℕ) (S : ℚ) : ℕ → List ℤ → List ℚ
  | _, [] => []
  | k, y :: ys => (((y * ((d ^ k : ℕ) : ℤ) : ℤ) : ℚ) / S) :: descaleL d S (k + 1) ys

def shiftLI (c : ℚ) (M : ℕ) (p : List ℚ) : List ℚ :=
  match shZ c.num c.den (M + 1) (p.map (toZ (polyD p))) with
  | (L, pw) => descaleL c.den ((polyD p * pw : ℕ) : ℚ) 0 (L ++ List.replicate (M + 1 - L.length) 0)

theorem zStep_getD (n : ℤ) : ∀ (cap : ℕ) (L : List ℤ) (prev : ℤ) (k : ℕ), k < cap →
    (zStep n cap L prev).getD k 0 = n * L.getD k 0 + (if k = 0 then prev else L.getD (k - 1) 0) := by
  intro cap
  induction cap with
  | zero => intro L prev k hk; omega
  | succ m ih =>
    intro L prev k hk
    cases L with
    | nil =>
      cases k with
      | zero => simp [zStep]
      | succ k => simp [zStep]
    | cons s ss =>
      cases k with
      | zero => simp [zStep]
      | succ k =>
        simp only [zStep, List.getD_cons_succ]
        rw [ih ss s k (by omega)]
        cases k with
        | zero => simp
        | succ k => simp

theorem zStep_length_le (n : ℤ) : ∀ (cap : ℕ) (L : List ℤ) (prev : ℤ), (zStep n cap L prev).length ≤ cap := by
  intro cap
  induction cap with
  | zero => intro L prev; simp [zStep]
  | succ m ih =>
    intro L prev
    cases L with
    | nil => simp [zStep]
    | cons s ss => simp only [zStep, List.length_cons]; have := ih ss s; omega

theorem shZ_snd (n : ℤ) (d cap : ℕ) : ∀ A : List ℤ, (shZ n d cap A).2 = d ^ A.length := by
  intro A
  induction A with
  | nil => simp [shZ]
  | cons a as ih =>
    simp only [shZ, List.length_cons]
    rcases h : shZ n d cap as with ⟨L, pw⟩
    rw [h] at ih
    simp only at ih ⊢
    rw [ih, pow_succ]; ring

theorem shZ_fst_length_le (n : ℤ) (d cap : ℕ) : ∀ A : List ℤ, (shZ n d cap A).1.length ≤ cap := by
  intro A
  induction A with
  | nil => simp [shZ]
  | cons a as ih =>
    simp only [shZ]
    rcases h : shZ n d cap as with ⟨L, pw⟩
    exact zStep_length_le n cap L _

theorem polyD_dvd (p : List ℚ) : ∀ a ∈ p, a.den ∣ polyD p := by
  have key : ∀ (p : List ℚ) (init : ℕ), init ∣ p.foldl (fun m a => Nat.lcm m a.den) init ∧
      ∀ a ∈ p, a.den ∣ p.foldl (fun m a => Nat.lcm m a.den) init := by
    intro p
    induction p with
    | nil => intro init; simp
    | cons b bs ih =>
      intro init
      obtain ⟨h1, h2⟩ := ih (Nat.lcm init b.den)
      refine ⟨(Nat.dvd_lcm_left init b.den).trans h1, ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact (Nat.dvd_lcm_right init a.den).trans h1
      · exact h2 a ha
  exact (key p 1).2

theorem polyD_pos (p : List ℚ) : 0 < polyD p := by
  have key : ∀ (p : List ℚ) (init : ℕ), 0 < init → 0 < p.foldl (fun m a => Nat.lcm m a.den) init := by
    intro p
    induction p with
    | nil => intro init h; simpa using h
    | cons b bs ih =>
      intro init h
      exact ih _ (Nat.lcm_pos h b.den_pos)
  exact key p 1 one_pos

theorem toZ_spec (D : ℕ) (a : ℚ) (hD : 0 < D) (h : a.den ∣ D) : ((toZ D a : ℤ) : ℚ) / (D : ℚ) = a := by
  unfold toZ
  have hden : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hq : ((((D / a.den : ℕ) : ℤ)) : ℚ) = (D : ℚ) / (a.den : ℚ) := by
    rw [Int.cast_natCast, Nat.cast_div h hden]
  rw [Int.cast_mul, hq]
  have : a = (a.num : ℚ) / (a.den : ℚ) := (Rat.num_div_den a).symm
  conv_rhs => rw [this]
  field_simp

theorem shiftL_main (c : ℚ) (M : ℕ) (n : ℤ) (d : ℕ) (hd : 0 < d) (hc : c = (n : ℚ) / (d : ℚ))
    (D : ℕ) (hD : 0 < D) : ∀ (A : List ℤ) (k : ℕ), k ≤ M →
    (shiftL c M (A.map (fun z : ℤ => (z : ℚ) / (D : ℚ)))).getD k 0 =
      ((((shZ n d (M + 1) A).1.getD k 0 * ((d ^ k : ℕ) : ℤ) : ℤ) : ℚ)) / ((D : ℚ) * ((d ^ A.length : ℕ) : ℚ)) := by
  intro A
  induction A with
  | nil =>
    intro k hk
    simp [shiftL, shZ]
  | cons a as ih =>
    intro k hk
    have hl := shiftL_length c M (as.map (fun z : ℤ => (z : ℚ) / (D : ℚ)))
    rw [List.map_cons]
    have e0 : shiftL c M (((a : ℚ) / (D : ℚ)) :: as.map (fun z : ℤ => (z : ℚ) / (D : ℚ))) =
        shiftStep c (shiftL c M (as.map (fun z : ℤ => (z : ℚ) / (D : ℚ)))) ((a : ℚ) / (D : ℚ)) := rfl
    rw [e0, shiftStep_getD c _ _ k (by omega)]
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    have hdn : ((d ^ as.length : ℕ) : ℚ) ≠ 0 := by positivity
    simp only [shZ]
    rcases hh : shZ n d (M + 1) as with ⟨L, pw⟩
    have hpw : pw = d ^ as.length := by
      have := shZ_snd n d (M + 1) as
      rw [hh] at this; exact this
    subst hpw
    simp only [List.length_cons]
    rw [zStep_getD n (M + 1) L _ k (by omega)]
    have ih1 := ih k hk
    rw [hh] at ih1
    simp only at ih1
    rw [ih1]
    cases k with
    | zero =>
      simp only [ite_true, pow_zero, Nat.cast_one, mul_one]
      rw [hc]
      push_cast
      field_simp
      ring
    | succ j =>
      simp only [Nat.succ_ne_zero, ite_false]
      have ih2 := ih j (by omega)
      rw [hh] at ih2
      simp only at ih2
      rw [Nat.add_sub_cancel, ih2, hc]
      push_cast
      field_simp
      ring

theorem descaleL_getD (d : ℕ) (S : ℚ) : ∀ (Y : List ℤ) (k0 k : ℕ),
    (descaleL d S k0 Y).getD k 0 = (((Y.getD k 0 * ((d ^ (k0 + k) : ℕ) : ℤ) : ℤ) : ℚ)) / S ∨ (k ≥ Y.length ∧ (descaleL d S k0 Y).getD k 0 = 0) := by
  intro Y
  induction Y with
  | nil => intro k0 k; right; simp [descaleL]
  | cons y ys ih =>
    intro k0 k
    cases k with
    | zero => left; simp [descaleL]
    | succ k =>
      simp only [descaleL, List.getD_cons_succ, List.length_cons]
      rcases ih (k0 + 1) k with h | h
      · left; rw [h, show k0 + 1 + k = k0 + (k + 1) by omega]
      · right; exact ⟨by omega, h.2⟩

theorem descaleL_length (d : ℕ) (S : ℚ) : ∀ (Y : List ℤ) (k0 : ℕ), (descaleL d S k0 Y).length = Y.length := by
  intro Y
  induction Y with
  | nil => intro k0; simp [descaleL]
  | cons y ys ih => intro k0; simp [descaleL, ih]

theorem getD_pad (L : List ℤ) (m k : ℕ) (hL : L.length ≤ m) :
    (L ++ List.replicate (m - L.length) 0).getD k 0 = L.getD k 0 := by
  by_cases h : k < L.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · have h2 : L.getD k 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [h2]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [List.getElem?_replicate]
    split_ifs <;> simp

theorem shiftLI_eq (c : ℚ) (M : ℕ) (p : List ℚ) : shiftLI c M p = shiftL c M p := by
  have hD := polyD_pos p
  have hdq : 0 < c.den := c.den_pos
  have hcq : c = (c.num : ℚ) / (c.den : ℚ) := (Rat.num_div_den c).symm
  set D := polyD p with hDdef
  set A : List ℤ := p.map (toZ D) with hA
  have hpA : p = A.map (fun z : ℤ => (z : ℚ) / (D : ℚ)) := by
    rw [hA, List.map_map]
    conv_lhs => rw [← List.map_id p]
    apply List.map_congr_left
    intro a ha
    simp only [Function.comp, id]
    exact (toZ_spec D a hD (polyD_dvd p a ha)).symm
  have hlenA : A.length = p.length := by rw [hA, List.length_map]
  have hLle := shZ_fst_length_le c.num c.den (M + 1) A
  have hpw := shZ_snd c.num c.den (M + 1) A
  apply List.ext_getElem
  · unfold shiftLI
    rcases hh : shZ c.num c.den (M + 1) A with ⟨L, pw⟩
    rw [hh] at hLle
    simp only [descaleL_length, List.length_append, List.length_replicate, shiftL_length]
    simp only at hLle
    omega
  · intro k h1 h2
    have hk : k ≤ M := by rw [shiftL_length] at h2; omega
    rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2]
    have hmain := shiftL_main c M c.num c.den hdq hcq D hD A k hk
    rw [← hpA] at hmain
    rw [hmain]
    unfold shiftLI
    rcases hh : shZ c.num c.den (M + 1) A with ⟨L, pw⟩
    rw [hh] at hLle hpw
    simp only at hLle hpw
    have hlen : (L ++ List.replicate (M + 1 - L.length) 0).length = M + 1 := by
      simp only [List.length_append, List.length_replicate]; omega
    rcases descaleL_getD c.den ((D * pw : ℕ) : ℚ) (L ++ List.replicate (M + 1 - L.length) 0) 0 k with h | h
    · rw [h, getD_pad L (M + 1) k hLle, zero_add, hpw, hlenA]
      push_cast
      rfl
    · omega


/-! ### Kronecker form of the integer Taylor shift

The Horner steps of `shZ` act on a packed integer `Z = Σ_k Y_k 2^(B k)`: one step is
`Z ↦ (n + 2^B) Z + prev`, a single GMP multiplication, instead of one integer operation per entry. -/

/-- packed Horner evaluation at `z = n + 2^B`; the second component is `d ^ length` -/
def hzB (n : ℤ) (d : ℕ) (z : ℤ) : List ℤ → ℤ × ℕ
  | [] => (0, 1)
  | A :: as =>
    match hzB n d z as with
    | (Z, pw) => (z * Z + (((d * pw : ℕ) : ℤ) * A), d * pw)

/-- the same Horner evaluation, reduced modulo `W` after every step (only the low digits are needed) -/
def hzC (n : ℤ) (d : ℕ) (z W : ℤ) : List ℤ → ℤ × ℕ
  | [] => (0, 1)
  | A :: as =>
    match hzC n d z W as with
    | (Z, pw) => ((z * Z + (((d * pw : ℕ) : ℤ) * A)) % W, d * pw)

/-- an upper bound of the entries of the integer Horner scheme, and `d ^ length` -/
def bdN (n : ℤ) (d : ℕ) : List ℤ → ℕ × ℕ
  | [] => (0, 1)
  | A :: as =>
    match bdN n d as with
    | (S, pw) => ((n.natAbs + 1) * S + d * pw * A.natAbs, d * pw)

/-- digit extraction from a packed integer with balanced (signed) digits `[-h, h)`, `h = 2^(B-1)` -/
def unpkS (B : ℕ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | m + 1, X =>
    match (X + ((2 ^ (B - 1) : ℕ) : ℤ)) % ((2 ^ B : ℕ) : ℤ) - ((2 ^ (B - 1) : ℕ) : ℤ) with
    | r => r :: unpkS B m ((X - r) / ((2 ^ B : ℕ) : ℤ))

theorem unpkS_succ (B m : ℕ) (X : ℤ) : unpkS B (m + 1) X =
    ((X + (2 : ℤ) ^ (B - 1)) % (2 : ℤ) ^ B - (2 : ℤ) ^ (B - 1)) ::
      unpkS B m ((X - ((X + (2 : ℤ) ^ (B - 1)) % (2 : ℤ) ^ B - (2 : ℤ) ^ (B - 1))) / (2 : ℤ) ^ B) := by
  simp only [unpkS, Nat.cast_pow, Nat.cast_ofNat]

/-- packing -/
def packZ (B : ℕ) : List ℤ → ℤ
  | [] => 0
  | y :: ys => y + (2 : ℤ) ^ B * packZ B ys

theorem unpkS_pack (B : ℕ) (hB : 1 ≤ B) : ∀ (ys : List ℤ), (∀ y ∈ ys, -(2 : ℤ) ^ (B - 1) ≤ y ∧ y < (2 : ℤ) ^ (B - 1)) →
    ∀ (m k : ℕ), k < m → (unpkS B m (packZ B ys)).getD k 0 = ys.getD k 0 := by
  have hpow : (2 : ℤ) ^ B = 2 * (2 : ℤ) ^ (B - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : (0 : ℤ) < (2 : ℤ) ^ (B - 1) := by positivity
  intro ys
  induction ys with
  | nil =>
    intro _ m k _
    have : ∀ (m : ℕ), unpkS B m 0 = List.replicate m 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ihm =>
        simp only [unpkS_succ, List.replicate_succ]
        have e1 : ((0 : ℤ) + (2 : ℤ) ^ (B - 1)) % (2 : ℤ) ^ B - (2 : ℤ) ^ (B - 1) = 0 := by
          rw [zero_add, Int.emod_eq_of_lt hpos.le (by linarith)]; ring
        simp only [e1]
        simp only [sub_zero, Int.zero_ediv]
        rw [ihm]
    simp [packZ, this]
  | cons y ys ih =>
    intro hys m k hk
    obtain ⟨hy1, hy2⟩ := hys y (by simp)
    have hrest : ∀ z ∈ ys, -(2 : ℤ) ^ (B - 1) ≤ z ∧ z < (2 : ℤ) ^ (B - 1) :=
      fun z hz => hys z (by simp [hz])
    cases m with
    | zero => omega
    | succ m =>
      have e1 : (packZ B (y :: ys) + (2 : ℤ) ^ (B - 1)) % (2 : ℤ) ^ B - (2 : ℤ) ^ (B - 1) = y := by
        simp only [packZ]
        have : y + (2 : ℤ) ^ B * packZ B ys + (2 : ℤ) ^ (B - 1) = (y + (2 : ℤ) ^ (B - 1)) + (2 : ℤ) ^ B * packZ B ys := by ring
        rw [this, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by linarith) (by linarith)]
        ring
      have e2 : (packZ B (y :: ys) - y) / (2 : ℤ) ^ B = packZ B ys := by
        simp only [packZ]
        have : y + (2 : ℤ) ^ B * packZ B ys - y = (2 : ℤ) ^ B * packZ B ys := by ring
        rw [this, Int.mul_ediv_cancel_left _ (by positivity)]
      simp only [unpkS_succ, e1, e2]
      cases k with
      | zero => simp
      | succ k => simp only [List.getD_cons_succ]; exact ih hrest m k (by omega)

theorem unpkS_length (B : ℕ) : ∀ (m : ℕ) (X : ℤ), (unpkS B m X).length = m := by
  intro m
  induction m with
  | zero => intro X; rfl
  | succ m ih => intro X; simp only [unpkS_succ, List.length_cons, ih]

theorem unpkS_congr (B : ℕ) (hB : 1 ≤ B) : ∀ (m : ℕ) (X X' : ℤ),
    X ≡ X' [ZMOD (2 : ℤ) ^ (B * m)] → unpkS B m X = unpkS B m X' := by
  have hpow : (2 : ℤ) ^ B = 2 * (2 : ℤ) ^ (B - 1) := by
    rw [← pow_succ']; congr 1; omega
  intro m
  induction m with
  | zero => intro X X' _; rfl
  | succ m ih =>
    intro X X' h
    have hdvd : (2 : ℤ) ^ B ∣ (2 : ℤ) ^ (B * (m + 1)) := pow_dvd_pow 2 (by nlinarith)
    have h1 : X ≡ X' [ZMOD (2 : ℤ) ^ B] := h.of_dvd hdvd
    have hm : (X + (2 : ℤ) ^ (B - 1)) % (2 : ℤ) ^ B = (X' + (2 : ℤ) ^ (B - 1)) % (2 : ℤ) ^ B :=
      Int.ModEq.add_right _ h1
    simp only [unpkS_succ, hm]
    congr 1
    apply ih
    set r : ℤ := (X' + (2 : ℤ) ^ (B - 1)) % (2 : ℤ) ^ B - (2 : ℤ) ^ (B - 1) with hr
    -- both numerators are divisible by 2^B
    have hX : (2 : ℤ) ^ B ∣ X - r := by
      have : X ≡ r [ZMOD (2 : ℤ) ^ B] := by
        have e : r ≡ X' [ZMOD (2 : ℤ) ^ B] := by
          have := Int.mod_modEq (X' + (2 : ℤ) ^ (B - 1)) ((2 : ℤ) ^ B)
          have h2 := this.sub_right ((2 : ℤ) ^ (B - 1))
          simpa [hr] using h2
        exact h1.trans e.symm
      exact (Int.modEq_iff_dvd.mp this.symm)
    have hX' : (2 : ℤ) ^ B ∣ X' - r := by
      have e : r ≡ X' [ZMOD (2 : ℤ) ^ B] := by
        have := Int.mod_modEq (X' + (2 : ℤ) ^ (B - 1)) ((2 : ℤ) ^ B)
        have h2 := this.sub_right ((2 : ℤ) ^ (B - 1))
        simpa [hr] using h2
      exact (Int.modEq_iff_dvd.mp e)
    obtain ⟨a, ha⟩ := hX
    obtain ⟨a', ha'⟩ := hX'
    have hp : (0 : ℤ) < (2 : ℤ) ^ B := by positivity
    rw [ha, ha', Int.mul_ediv_cancel_left _ hp.ne', Int.mul_ediv_cancel_left _ hp.ne']
    have hd : (2 : ℤ) ^ (B * (m + 1)) = (2 : ℤ) ^ B * (2 : ℤ) ^ (B * m) := by
      rw [← pow_add]; congr 1; ring
    rw [hd] at h
    have h3 : (2 : ℤ) ^ B * a ≡ (2 : ℤ) ^ B * a' [ZMOD (2 : ℤ) ^ B * (2 : ℤ) ^ (B * m)] := by
      have e1 : (2 : ℤ) ^ B * a + r = X := by linarith
      have e2 : (2 : ℤ) ^ B * a' + r = X' := by linarith
      have := h.add_right (-r)
      simpa [← e1, ← e2] using this
    exact (Int.ModEq.mul_left_cancel' hp.ne' h3)

theorem hzC_modEq (n : ℤ) (d : ℕ) (z W : ℤ) : ∀ A : List ℤ,
    (hzC n d z W A).1 ≡ (hzB n d z A).1 [ZMOD W] ∧ (hzC n d z W A).2 = (hzB n d z A).2 := by
  intro A
  induction A with
  | nil => simp [hzC, hzB]
  | cons a as ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [hzC, hzB]
    rcases hc : hzC n d z W as with ⟨Zc, pc⟩
    rcases hb : hzB n d z as with ⟨Zb, pb⟩
    rw [hc, hb] at h1 h2
    simp only at h1 h2 ⊢
    subst h2
    refine ⟨?_, rfl⟩
    refine (Int.mod_modEq _ _).trans ?_
    exact ((h1.mul_left z).add_right _)

theorem zStep_length_le' (n : ℤ) : ∀ (cap : ℕ) (L : List ℤ) (prev : ℤ),
    (zStep n cap L prev).length ≤ L.length + 1 := by
  intro cap
  induction cap with
  | zero => intro L prev; simp [zStep]
  | succ m ih =>
    intro L prev
    cases L with
    | nil => simp [zStep]
    | cons s ss => simp only [zStep, List.length_cons]; have := ih ss s; omega

theorem shZ_fst_length_le' (n : ℤ) (d cap : ℕ) : ∀ A : List ℤ, (shZ n d cap A).1.length ≤ A.length := by
  intro A
  induction A with
  | nil => simp [shZ]
  | cons a as ih =>
    simp only [shZ, List.length_cons]
    rcases h : shZ n d cap as with ⟨L, pw⟩
    rw [h] at ih
    simp only at ih ⊢
    have := zStep_length_le' n cap L (((d * pw : ℕ) : ℤ) * a)
    omega

theorem zStep_pack (n : ℤ) (B : ℕ) : ∀ (L : List ℤ) (cap : ℕ) (prev : ℤ), L.length < cap →
    packZ B (zStep n cap L prev) = (n + (2 : ℤ) ^ B) * packZ B L + prev := by
  intro L
  induction L with
  | nil =>
    intro cap prev h
    cases cap with
    | zero => omega
    | succ m => simp [zStep, packZ]
  | cons s ss ih =>
    intro cap prev h
    cases cap with
    | zero => omega
    | succ m =>
      simp only [zStep, packZ]
      rw [ih m s (by simp at h; omega)]
      ring

theorem hzB_pack (n : ℤ) (d B : ℕ) : ∀ (A : List ℤ) (cap : ℕ), A.length < cap →
    (hzB n d (n + (2 : ℤ) ^ B) A).1 = packZ B (shZ n d cap A).1 ∧
    (hzB n d (n + (2 : ℤ) ^ B) A).2 = d ^ A.length := by
  intro A
  induction A with
  | nil => intro cap _; simp [hzB, shZ, packZ]
  | cons a as ih =>
    intro cap hcap
    obtain ⟨h1, h2⟩ := ih cap (by simp at hcap; omega)
    have hlen := shZ_fst_length_le' n d cap as
    have hsnd := shZ_snd n d cap as
    simp only [hzB, shZ, List.length_cons]
    rcases hh : hzB n d (n + (2 : ℤ) ^ B) as with ⟨Z, pw⟩
    rcases hs : shZ n d cap as with ⟨L, pw'⟩
    rw [hh, hs] at h1
    rw [hh] at h2
    rw [hs] at hsnd hlen
    simp only at h1 h2 hsnd hlen ⊢
    subst h1
    subst h2
    subst hsnd
    refine ⟨?_, by ring⟩
    rw [zStep_pack n B L cap _ (by simp at hcap; omega)]


theorem bdN_snd (n : ℤ) (d : ℕ) : ∀ A : List ℤ, (bdN n d A).2 = d ^ A.length := by
  intro A
  induction A with
  | nil => simp [bdN]
  | cons a as ih =>
    simp only [bdN, List.length_cons]
    rcases h : bdN n d as with ⟨S, pw⟩
    rw [h] at ih
    simp only at ih ⊢
    rw [ih, pow_succ]; ring

theorem zStep_bound (n : ℤ) : ∀ (L : List ℤ) (cap : ℕ) (prev : ℤ) (S Sp : ℕ),
    (∀ s ∈ L, s.natAbs ≤ S) → prev.natAbs ≤ Sp →
    ∀ y ∈ zStep n cap L prev, y.natAbs ≤ n.natAbs * S + max S Sp := by
  intro L
  induction L with
  | nil =>
    intro cap prev S Sp _ hp y hy
    cases cap with
    | zero => simp [zStep] at hy
    | succ m =>
      simp only [zStep, List.mem_singleton] at hy
      subst hy
      have := le_max_right S Sp
      omega
  | cons s ss ih =>
    intro cap prev S Sp hs hp y hy
    cases cap with
    | zero => simp [zStep] at hy
    | succ m =>
      simp only [zStep, List.mem_cons] at hy
      have hs0 : s.natAbs ≤ S := hs s (by simp)
      rcases hy with rfl | hy
      · have h1 := Int.natAbs_add_le (n * s) prev
        rw [Int.natAbs_mul] at h1
        have h2 : n.natAbs * s.natAbs ≤ n.natAbs * S := Nat.mul_le_mul_left _ hs0
        have := le_max_right S Sp
        omega
      · have := ih m s S S (fun t ht => hs t (by simp [ht])) hs0 y hy
        have h3 := le_max_left S Sp
        have : max S S = S := max_self S
        omega

theorem shZ_bound (n : ℤ) (d cap : ℕ) : ∀ A : List ℤ, ∀ y ∈ (shZ n d cap A).1,
    y.natAbs ≤ (bdN n d A).1 := by
  intro A
  induction A with
  | nil => intro y hy; simp [shZ] at hy
  | cons a as ih =>
    intro y hy
    have hsnd := shZ_snd n d cap as
    have hb := bdN_snd n d as
    simp only [shZ, bdN] at hy ⊢
    rcases hh : shZ n d cap as with ⟨L, pw⟩
    rcases hb2 : bdN n d as with ⟨S, pw2⟩
    rw [hh] at hy hsnd ih
    rw [hb2] at hb ih
    simp only at hy hsnd hb ih ⊢
    have hp : (((d * pw : ℕ) : ℤ) * a).natAbs ≤ d * pw2 * a.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_natCast, hsnd, hb]
    have := zStep_bound n L cap _ S (d * pw2 * a.natAbs) ih hp y hy
    have h3 := le_max_left S (d * pw2 * a.natAbs)
    have h4 := le_max_right S (d * pw2 * a.natAbs)
    have h5 : n.natAbs * S + max S (d * pw2 * a.natAbs) ≤ (n.natAbs + 1) * S + d * pw2 * a.natAbs := by
      have e : (n.natAbs + 1) * S = n.natAbs * S + S := by ring
      rcases le_total S (d * pw2 * a.natAbs) with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega
    omega

theorem shZ_cap_getD (n : ℤ) (d : ℕ) : ∀ (A : List ℤ) (cap cap' k : ℕ), k < cap → cap ≤ cap' →
    (shZ n d cap A).1.getD k 0 = (shZ n d cap' A).1.getD k 0 := by
  intro A
  induction A with
  | nil => intro cap cap' k _ _; simp [shZ]
  | cons a as ih =>
    intro cap cap' k hk hc
    have h1 := shZ_snd n d cap as
    have h2 := shZ_snd n d cap' as
    simp only [shZ]
    rcases hh : shZ n d cap as with ⟨L, pw⟩
    rcases hh' : shZ n d cap' as with ⟨L', pw'⟩
    rw [hh] at h1
    rw [hh'] at h2
    simp only at h1 h2 ⊢
    rw [zStep_getD n cap L _ k hk, zStep_getD n cap' L' _ k (by omega)]
    rw [h1, h2]
    have e0 := ih cap cap' k hk hc
    rw [hh, hh'] at e0
    simp only at e0
    rw [e0]
    cases k with
    | zero => simp
    | succ j =>
      have e1 := ih cap cap' j (by omega) hc
      rw [hh, hh'] at e1
      simp only at e1
      simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, e1]

theorem descaleL_congr (d : ℕ) (S : ℚ) : ∀ (Y Y' : List ℤ) (k0 : ℕ), Y.length = Y'.length →
    (∀ k, k < Y.length → Y.getD k 0 = Y'.getD k 0) → descaleL d S k0 Y = descaleL d S k0 Y' := by
  intro Y
  induction Y with
  | nil => intro Y' k0 hl _; cases Y' <;> simp_all [descaleL]
  | cons y ys ih =>
    intro Y' k0 hl hg
    cases Y' with
    | nil => simp at hl
    | cons y' ys' =>
      have h0 := hg 0 (by simp)
      simp only [List.getD_cons_zero] at h0
      simp only [descaleL, h0]
      congr 1
      exact ih ys' (k0 + 1) (by simpa using hl) (fun k hk => by
        have := hg (k + 1) (by simpa using hk)
        simpa using this)

/-- Kronecker form: all Horner steps on one packed integer -/
def shiftLKc (n : ℤ) (d M : ℕ) (A : List ℤ) (D : ℕ) : List ℚ :=
  match bdN n d A with
  | (S, pw) => descaleL d ((D * pw : ℕ) : ℚ) 0
      (unpkS (Nat.log2 S + 2) (M + 1)
        (hzC n d (n + ((2 ^ (Nat.log2 S + 2) : ℕ) : ℤ)) ((2 ^ ((Nat.log2 S + 2) * (M + 1)) : ℕ) : ℤ) A).1)

def shiftLK (c : ℚ) (M : ℕ) (p : List ℚ) : List ℚ :=
  shiftLKc c.num c.den M (p.map (toZ (polyD p))) (polyD p)

theorem shiftLK_eq (c : ℚ) (M : ℕ) (p : List ℚ) : shiftLK c M p = shiftLI c M p := by
  unfold shiftLK shiftLKc shiftLI
  set A : List ℤ := p.map (toZ (polyD p)) with hA
  have hS := bdN_snd c.num c.den A
  have hsn := shZ_snd c.num c.den (M + 1) A
  rcases hb : bdN c.num c.den A with ⟨S, pw⟩
  rcases hs : shZ c.num c.den (M + 1) A with ⟨L, pw'⟩
  rw [hb] at hS
  rw [hs] at hsn
  simp only at hS hsn ⊢
  subst hS hsn
  have hlenL := shZ_fst_length_le' c.num c.den (M + 1) A
  have hlenL2 := shZ_fst_length_le c.num c.den (M + 1) A
  rw [hs] at hlenL hlenL2
  simp only at hlenL hlenL2
  have hpk := hzB_pack c.num c.den (Nat.log2 S + 2) A (A.length + 1) (Nat.lt_succ_self _)
  have hpk1 : (hzB c.num c.den (c.num + ((2 ^ (Nat.log2 S + 2) : ℕ) : ℤ)) A).1 =
      packZ (Nat.log2 S + 2) (shZ c.num c.den (A.length + 1) A).1 := by
    have := hpk.1
    simpa [Nat.cast_pow] using this
  have hcongr := unpkS_congr (Nat.log2 S + 2) (by omega) (M + 1)
    (hzC c.num c.den (c.num + ((2 ^ (Nat.log2 S + 2) : ℕ) : ℤ)) ((2 ^ ((Nat.log2 S + 2) * (M + 1)) : ℕ) : ℤ) A).1
    (hzB c.num c.den (c.num + ((2 ^ (Nat.log2 S + 2) : ℕ) : ℤ)) A).1
    (by simpa [Nat.cast_pow] using (hzC_modEq c.num c.den (c.num + ((2 ^ (Nat.log2 S + 2) : ℕ) : ℤ)) ((2 ^ ((Nat.log2 S + 2) * (M + 1)) : ℕ) : ℤ) A).1)
  rw [hcongr, hpk1]
  -- digit bounds
  have hSlt : S < 2 ^ (Nat.log2 S + 1) := Nat.lt_log2_self
  have hdig : ∀ y ∈ (shZ c.num c.den (A.length + 1) A).1,
      -(2 : ℤ) ^ (Nat.log2 S + 2 - 1) ≤ y ∧ y < (2 : ℤ) ^ (Nat.log2 S + 2 - 1) := by
    intro y hy
    have hb' := shZ_bound c.num c.den (A.length + 1) A y hy
    rw [hb] at hb'
    simp only at hb'
    have : (S : ℤ) < (2 : ℤ) ^ (Nat.log2 S + 2 - 1) := by
      have := hSlt
      have e : Nat.log2 S + 2 - 1 = Nat.log2 S + 1 := by omega
      rw [e]; exact_mod_cast this
    have hy' : |y| ≤ (S : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hb'
    constructor
    · have := neg_abs_le y; linarith [abs_le.mp hy']
    · linarith [(abs_le.mp hy').2]
  apply descaleL_congr
  · rw [unpkS_length]
    simp only [List.length_append, List.length_replicate]
    omega
  · intro k hk
    rw [unpkS_length] at hk
    rw [unpkS_pack (Nat.log2 S + 2) (by omega) _ hdig (M + 1) k hk]
    rw [getD_pad L (M + 1) k hlenL2]
    by_cases hk2 : k < A.length + 1
    · have e1 := shZ_cap_getD c.num c.den A (min (M + 1) (A.length + 1)) (M + 1) k (lt_min hk hk2) (min_le_left _ _)
      have e2 := shZ_cap_getD c.num c.den A (min (M + 1) (A.length + 1)) (A.length + 1) k (lt_min hk hk2) (min_le_right _ _)
      rw [hs] at e1
      simp only at e1
      exact e2.symm.trans e1
    · have h0 : L.getD k 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      have hfull := shZ_fst_length_le' c.num c.den (A.length + 1) A
      have h1 : (shZ c.num c.den (A.length + 1) A).1.getD k 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [h0, h1]


theorem shiftLK_eq' (c : ℚ) (M : ℕ) (p : List ℚ) : shiftLK c M p = shiftL c M p :=
  (shiftLK_eq c M p).trans (shiftLI_eq c M p)

/-- `plogVec` with the integer Taylor shift -/
def plogVecI (P : List ℚ) (e c L : ℚ) (M : ℕ) : List ℚ :=
  let Pk := shiftLK c M P
  (List.range (M + 1)).map (fun k => plogCoefQ Pk (c - e) L k)

def plogSumVecI (c : ℚ) (M : ℕ) : List (List ℚ × ℚ) → List ℚ → List ℚ
  | t :: ts, L :: Ls => vecAdd (plogVecI t.1 t.2 c L M) (plogSumVecI c M ts Ls)
  | _, _ => []

theorem plogVecI_eq (P : List ℚ) (e c L : ℚ) (M : ℕ) : plogVecI P e c L M = plogVec P e c L M := by
  unfold plogVecI plogVec
  rw [shiftLK_eq']

theorem plogSumVecI_eq (c : ℚ) (M : ℕ) : ∀ (plogs : List (List ℚ × ℚ)) (Ls : List ℚ),
    plogSumVecI c M plogs Ls = plogSumVec c M plogs Ls := by
  intro plogs
  induction plogs with
  | nil => intro Ls; cases Ls <;> simp [plogSumVecI, plogSumVec]
  | cons t ts ih =>
    intro Ls
    cases Ls with
    | nil => simp [plogSumVecI, plogSumVec]
    | cons L Ls => simp only [plogSumVecI, plogSumVec, plogVecI_eq, ih]

/-- `plogErr1` with the integer Taylor shift -/
def plogErr1I (P : List ℚ) (c ε : ℚ) (M : ℕ) : List ℚ :=
  let Pk := shiftLK c M P
  (List.range (M + 1)).map (fun k => ε * qabs' (Pk.getD k 0))

def plogErrSumI (c : ℚ) (M : ℕ) : List (List ℚ × ℚ) → List ℚ → List ℚ
  | t :: ts, ε :: εs => vecAdd (plogErr1I t.1 c ε M) (plogErrSumI c M ts εs)
  | _, _ => []

theorem plogErrSumI_eq (c : ℚ) (M : ℕ) : ∀ (plogs : List (List ℚ × ℚ)) (εs : List ℚ),
    plogErrSumI c M plogs εs = plogErrSum c M plogs εs := by
  intro plogs
  induction plogs with
  | nil => intro εs; cases εs <;> simp [plogErrSumI, plogErrSum]
  | cons t ts ih =>
    intro εs
    cases εs with
    | nil => simp [plogErrSumI, plogErrSum]
    | cons ε εs =>
      simp only [plogErrSumI, plogErrSum, ih]
      unfold plogErr1I plogErr1
      rw [shiftLK_eq']

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
recurrence (`fpE`, `fpTermErr`, closed forms `crudeErr`/`tailErr`), after `ℓ¹`-norm checks of
`U` and of the weights by integers (`fpPoleOK`).  The poles are split in two classes (`isFar`): the far
ones (`|u|₁` and weight below the thresholds `MiF`, `WiF`) are summed only to order `K0` and their
dropped terms are bounded by `tailErr`; one soundness theorem `poleVecT_err` covers both classes.  The coefficient tests read each (short dyadic)
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

/-- `2^Q` as an integer through the natural-number power: the kernel computes `Nat.pow` in one step,
while the integer power `(2 : ℤ) ^ Q` unfolds `Q` times, at every evaluation of the term. -/
def pw2 (Q : ℕ) : ℤ := ((2 ^ Q : ℕ) : ℤ)

theorem pw2_eq (Q : ℕ) : pw2 Q = (2 : ℤ) ^ Q := by unfold pw2; push_cast; rfl

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

/-- one pole, one coefficient: the fixed-point term is within `fpTermErr` of the exact term -/
theorem fpPole_term_err (Q Mi Wi : ℕ) (q : PoleR) (c : ℚ) (M k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ M)
    (hok : fpPoleOK Q Mi Wi q c = true) :
    |poleTermQ q.rr q.ri k (cpowQ (uOf q c) k) -
        (((fpPole Q q c M).getD k 0 : ℤ) : ℚ) / ((2 : ℚ) ^ Q) ^ 2| ≤ fpTermErr Q Mi Wi k := by
  have hG : (0 : ℚ) < 2 ^ Q := by positivity
  have hqok := hok
  unfold fpPoleOK at hqok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hqok
  obtain ⟨hMi, hWi⟩ := hqok
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
  have hz : (fpPole Q q c M).getD (j + 1) 0 =
      sgn (j + 1) * (fpRound Q q.rr * ((fpLoop Q U M ((2 : ℤ) ^ Q, 0)).getD j (0, 0)).1 -
        fpRound Q q.ri * ((fpLoop Q U M ((2 : ℤ) ^ Q, 0)).getD j (0, 0)).2) / ((j + 1 : ℕ) : ℤ) := by
    unfold fpPole
    rw [List.getD_cons_succ, fpTerms_getD _ _ _ 1 j (by rw [fpLoop_length]; exact hjM),
      add_comm 1 j]
  rw [hz]
  have hterm := fpTerm_err Q Wi q.rr q.ri (fpRound Q q.rr) (fpRound Q q.ri) (j + 1) (by omega)
    ((fpLoop Q U M ((2 : ℤ) ^ Q, 0)).getD j (0, 0)) (cpowQ u (j + 1))
    (fpE (((Mi : ℚ) + 2) / 2 ^ Q) (2 / 2 ^ Q) (2 / 2 ^ Q) (j + 1)) ((((Mi : ℚ) + 2) / 2 ^ Q) ^ (j + 1))
    (fpRound_spec Q q.rr) (fpRound_spec Q q.ri) hWi (by simpa using hl)
    (n1_cpow u _ hn1u (j + 1))
  simpa [fpTermErr] using hterm

theorem fpTerms_length (RR RI : ℤ) : ∀ (ws : List (ℤ × ℤ)) (k : ℕ), (fpTerms RR RI k ws).length = ws.length := by
  intro ws
  induction ws with
  | nil => intro k; rfl
  | cons w ws ih => intro k; simp [fpTerms, ih]

theorem fpPole_length (Q : ℕ) (q : PoleR) (c : ℚ) (K : ℕ) : (fpPole Q q c K).length = K + 1 := by
  unfold fpPole
  simp [fpTerms_length, fpLoop_length]

theorem fpPole_getD_gt (Q : ℕ) (q : PoleR) (c : ℚ) (K k : ℕ) (h : K < k) : (fpPole Q q c K).getD k 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [fpPole_length]; omega)]
  rfl

/-- crude closed-form error of a kept term (`μ = (Mi+4)/2^Q ≥ 1`) -/
def crudeErr (Q Mi Wi k : ℕ) : ℚ :=
  (((Mi + 4) ^ k * (2 ^ Q + 4 * Wi + 1) : ℕ) : ℚ) / ((2 ^ (Q * (k + 2)) : ℕ) : ℚ)

/-- crude closed-form bound of a dropped term -/
def tailErr (Q Mi Wi k : ℕ) : ℚ :=
  (((Wi + 2) * (Mi + 4) ^ k : ℕ) : ℚ) / ((2 ^ (Q * (k + 1)) : ℕ) : ℚ)

theorem fpE_crude (m δ : ℚ) (hm : 0 ≤ m) (hδ : 0 ≤ δ) (h1 : 1 ≤ m + δ) :
    ∀ k : ℕ, fpE m δ δ k ≤ 2 * δ * k * (m + δ) ^ k := by
  intro k
  induction k with
  | zero => simp [fpE]
  | succ k ih =>
    simp only [fpE]
    have hμ : 0 ≤ m + δ := by linarith
    have hpk : 1 ≤ (m + δ) ^ k := one_le_pow₀ h1
    have hmk : m ^ k ≤ (m + δ) ^ k := pow_le_pow_left₀ hm (by linarith) k
    have hmu : (m + δ) ^ k ≤ (m + δ) ^ (k + 1) := pow_le_pow_right₀ h1 (by omega)
    have e1 : (m + δ) ^ (k + 1) = (m + δ) ^ k * (m + δ) := pow_succ _ _
    have a1 : fpE m δ δ k * (m + δ) ≤ 2 * δ * k * (m + δ) ^ k * (m + δ) :=
      mul_le_mul_of_nonneg_right ih hμ
    have b1 : 2 * δ * k * (m + δ) ^ k * (m + δ) = 2 * δ * k * (m + δ) ^ (k + 1) := by rw [e1]; ring
    have b2 : m ^ k * δ ≤ (m + δ) ^ k * δ := mul_le_mul_of_nonneg_right hmk hδ
    have b3 : δ ≤ δ * (m + δ) ^ k := by nlinarith [mul_le_mul_of_nonneg_left hpk hδ]
    have b4 : δ * (m + δ) ^ k ≤ δ * (m + δ) ^ (k + 1) := mul_le_mul_of_nonneg_left hmu hδ
    push_cast
    nlinarith [b1, b2, b3, b4, a1]

theorem fpTermErr_le_crude (Q Mi Wi k : ℕ) (hk : 1 ≤ k) (hMi : 2 ^ Q ≤ Mi + 4) :
    fpTermErr Q Mi Wi k ≤ crudeErr Q Mi Wi k := by
  have hG : (0 : ℚ) < 2 ^ Q := by positivity
  set G : ℚ := 2 ^ Q with hGdef
  have hMiq : G ≤ (Mi : ℚ) + 4 := by rw [hGdef]; exact_mod_cast hMi
  set m : ℚ := ((Mi : ℚ) + 2) / G with hm
  set δ : ℚ := 2 / G with hδ
  have hm0 : 0 ≤ m := by positivity
  have hδ0 : 0 ≤ δ := by positivity
  have hμ : m + δ = ((Mi : ℚ) + 4) / G := by rw [hm, hδ]; ring
  have h1 : 1 ≤ m + δ := by rw [hμ, le_div_iff₀ hG]; linarith
  have hE := fpE_crude m δ hm0 hδ0 h1 k
  have hkq : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hpk : 1 ≤ (m + δ) ^ k := one_le_pow₀ h1
  have hmk : m ^ k ≤ (m + δ) ^ k := pow_le_pow_left₀ hm0 (by linarith) k
  have hWi : (0 : ℚ) ≤ Wi := Nat.cast_nonneg _
  unfold fpTermErr
  change (1 / (k : ℚ)) * ((1 / G) * m ^ k + ((Wi : ℚ) / G) * fpE m δ δ k) + 1 / G ^ 2 ≤ _
  have hc : crudeErr Q Mi Wi k = (m + δ) ^ k * (G + 4 * Wi + 1) / G ^ 2 := by
    unfold crudeErr
    rw [hμ]
    push_cast
    rw [pow_mul, div_pow]
    simp only [← hGdef]
    field_simp
    ring
  rw [hc]
  have step1 : (1 / (k : ℚ)) * ((1 / G) * m ^ k + ((Wi : ℚ) / G) * fpE m δ δ k) ≤
      (1 / (k : ℚ)) * ((1 / G) * (m + δ) ^ k + ((Wi : ℚ) / G) * (2 * δ * k * (m + δ) ^ k)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have a : (1 / G) * m ^ k ≤ (1 / G) * (m + δ) ^ k := mul_le_mul_of_nonneg_left hmk (by positivity)
    have b : ((Wi : ℚ) / G) * fpE m δ δ k ≤ ((Wi : ℚ) / G) * (2 * δ * k * (m + δ) ^ k) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    linarith
  have step2 : (1 / (k : ℚ)) * ((1 / G) * (m + δ) ^ k + ((Wi : ℚ) / G) * (2 * δ * k * (m + δ) ^ k)) =
      (m + δ) ^ k / (k * G) + 4 * Wi * (m + δ) ^ k / G ^ 2 := by
    rw [hδ]
    have hk0 : (k : ℚ) ≠ 0 := by positivity
    field_simp
    ring
  have step3 : (m + δ) ^ k / (k * G) ≤ (m + δ) ^ k * G / G ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℚ) ≤ (m + δ) ^ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hkq (mul_nonneg this hG.le), mul_nonneg this hG.le]
  have step4 : 1 / G ^ 2 ≤ (m + δ) ^ k * 1 / G ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have e5 : (m + δ) ^ k * (G + 4 * Wi + 1) / G ^ 2 =
      (m + δ) ^ k * G / G ^ 2 + 4 * Wi * (m + δ) ^ k / G ^ 2 + (m + δ) ^ k * 1 / G ^ 2 := by ring
  rw [e5]
  linarith

theorem uOf_n1_le (Q Mi Wi : ℕ) (q : PoleR) (c : ℚ) (hok : fpPoleOK Q Mi Wi q c = true) :
    n1 (uOf q c) ≤ ((Mi : ℚ) + 2) / 2 ^ Q := by
  have hG : (0 : ℚ) < 2 ^ Q := by positivity
  have hqok := hok
  unfold fpPoleOK at hqok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hqok
  obtain ⟨hMi, -⟩ := hqok
  set u := uOf q c with hu
  have s1 := fpRound_spec Q u.1
  have s2 := fpRound_spec Q u.2
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

/-- a dropped term of a pole passing `fpPoleOK Q Mi Wi` is at most `tailErr` -/
theorem pole_tail_err (Q Mi Wi : ℕ) (q : PoleR) (c : ℚ) (k : ℕ) (hk1 : 1 ≤ k)
    (hok : fpPoleOK Q Mi Wi q c = true) :
    |poleTermQ q.rr q.ri k (cpowQ (uOf q c) k)| ≤ tailErr Q Mi Wi k := by
  have hG : (0 : ℚ) < 2 ^ Q := by positivity
  have hn1u := uOf_n1_le Q Mi Wi q c hok
  have hqok := hok
  unfold fpPoleOK at hqok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hqok
  obtain ⟨-, hWi⟩ := hqok
  have hkq : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk1
  set u := uOf q c with hu
  set v := cpowQ u k with hv
  have hsg : |((sgn k : ℤ) : ℚ)| = 1 := sgn_abs k
  have hterm : poleTermQ q.rr q.ri k v = ((sgn k : ℤ) : ℚ) / k * (q.rr * v.1 - q.ri * v.2) := by
    unfold poleTermQ; rw [sgn_eq k hk1]
  have s1 := fpRound_spec Q q.rr
  have s2 := fpRound_spec Q q.ri
  have habsRR : |((fpRound Q q.rr : ℤ) : ℚ)| = ((fpRound Q q.rr).natAbs : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have habsRI : |((fpRound Q q.ri : ℤ) : ℚ)| = ((fpRound Q q.ri).natAbs : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hWq : ((fpRound Q q.rr).natAbs : ℚ) + ((fpRound Q q.ri).natAbs : ℚ) ≤ (Wi : ℚ) := by
    exact_mod_cast hWi
  have b1 : |q.rr| ≤ ((Wi : ℚ) + 1) / 2 ^ Q := by
    have h0 := abs_add_le (((fpRound Q q.rr : ℤ) : ℚ) / 2 ^ Q) (q.rr - ((fpRound Q q.rr : ℤ) : ℚ) / 2 ^ Q)
    simp only [add_sub_cancel] at h0
    have h1 : |((fpRound Q q.rr : ℤ) : ℚ) / 2 ^ Q| = ((fpRound Q q.rr).natAbs : ℚ) / 2 ^ Q := by
      rw [abs_div, abs_of_pos hG, habsRR]
    have h2 : |q.rr - ((fpRound Q q.rr : ℤ) : ℚ) / 2 ^ Q| ≤ 1 / 2 ^ Q := by
      rw [abs_of_nonneg s1.1]; exact s1.2
    have h3 : ((fpRound Q q.rr).natAbs : ℚ) / 2 ^ Q ≤ (Wi : ℚ) / 2 ^ Q :=
      div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℚ) (fpRound Q q.ri).natAbs]) hG.le
    have : ((Wi : ℚ) + 1) / 2 ^ Q = (Wi : ℚ) / 2 ^ Q + 1 / 2 ^ Q := by ring
    linarith
  have b2 : |-q.ri| ≤ ((Wi : ℚ) + 1) / 2 ^ Q := by
    rw [abs_neg]
    have h0 := abs_add_le (((fpRound Q q.ri : ℤ) : ℚ) / 2 ^ Q) (q.ri - ((fpRound Q q.ri : ℤ) : ℚ) / 2 ^ Q)
    simp only [add_sub_cancel] at h0
    have h1 : |((fpRound Q q.ri : ℤ) : ℚ) / 2 ^ Q| = ((fpRound Q q.ri).natAbs : ℚ) / 2 ^ Q := by
      rw [abs_div, abs_of_pos hG, habsRI]
    have h2 : |q.ri - ((fpRound Q q.ri : ℤ) : ℚ) / 2 ^ Q| ≤ 1 / 2 ^ Q := by
      rw [abs_of_nonneg s2.1]; exact s2.2
    have h3 : ((fpRound Q q.ri).natAbs : ℚ) / 2 ^ Q ≤ (Wi : ℚ) / 2 ^ Q :=
      div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℚ) (fpRound Q q.rr).natAbs]) hG.le
    have : ((Wi : ℚ) + 1) / 2 ^ Q = (Wi : ℚ) / 2 ^ Q + 1 / 2 ^ Q := by ring
    linarith
  have l := lin2 q.rr (-q.ri) v.1 v.2 (((Wi : ℚ) + 1) / 2 ^ Q) b1 b2
  have hn1v : n1 v ≤ (((Mi : ℚ) + 2) / 2 ^ Q) ^ k := n1_cpow u _ hn1u k
  have hcomb : |q.rr * v.1 - q.ri * v.2| ≤ (((Wi : ℚ) + 1) / 2 ^ Q) * (((Mi : ℚ) + 2) / 2 ^ Q) ^ k := by
    have e : q.rr * v.1 - q.ri * v.2 = q.rr * v.1 + (-q.ri) * v.2 := by ring
    rw [e]
    refine l.trans ?_
    exact mul_le_mul_of_nonneg_left hn1v (by positivity)
  rw [hterm, abs_mul, abs_div, hsg, abs_of_pos (by linarith : (0 : ℚ) < k)]
  have hkk : 1 / (k : ℚ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hkq
  have hM : (0 : ℚ) ≤ (((Wi : ℚ) + 1) / 2 ^ Q) * (((Mi : ℚ) + 2) / 2 ^ Q) ^ k := by positivity
  have c1 : 1 / (k : ℚ) * |q.rr * v.1 - q.ri * v.2| ≤
      (((Wi : ℚ) + 1) / 2 ^ Q) * (((Mi : ℚ) + 2) / 2 ^ Q) ^ k := by
    calc 1 / (k : ℚ) * |q.rr * v.1 - q.ri * v.2| ≤ 1 * |q.rr * v.1 - q.ri * v.2| :=
          mul_le_mul_of_nonneg_right hkk (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hcomb
  refine c1.trans ?_
  unfold tailErr
  push_cast
  rw [pow_mul]
  have e2 : (((Wi : ℚ) + 1) / 2 ^ Q) * (((Mi : ℚ) + 2) / 2 ^ Q) ^ k =
      ((Wi : ℚ) + 1) * ((Mi : ℚ) + 2) ^ k / (2 ^ Q) ^ (k + 1) := by
    rw [div_pow, pow_succ]; field_simp
  rw [e2]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hMk : ((Mi : ℚ) + 2) ^ k ≤ ((Mi : ℚ) + 4) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
  have : (0 : ℚ) ≤ (Wi : ℚ) := Nat.cast_nonneg _
  nlinarith [pow_nonneg (by positivity : (0 : ℚ) ≤ (Mi : ℚ) + 2) k, mul_le_mul_of_nonneg_left hMk (by positivity : (0 : ℚ) ≤ (Wi : ℚ) + 1)]

/-! ### Two-class (near / far) pole part -/

def isFar (Q MiF WiF : ℕ) (c : ℚ) (q : PoleR) : Bool := fpPoleOK Q MiF WiF q c

def poleKq (Q K0 MiF WiF M : ℕ) (c : ℚ) (q : PoleR) : ℕ :=
  if isFar Q MiF WiF c q = true then min K0 M else M

def poleVecZT (Q K0 MiF WiF : ℕ) (poles : List PoleR) (c : ℚ) (M : ℕ) : List ℤ :=
  vecSumZ (poles.map (fun q => fpPole Q q c (poleKq Q K0 MiF WiF M c q)))

def poleVecT (Q K0 MiF WiF : ℕ) (poles : List PoleR) (c : ℚ) (M : ℕ) : List ℚ :=
  List.map (fun z : ℤ => (z : ℚ) / ((2 : ℚ) ^ Q) ^ 2) (poleVecZT Q K0 MiF WiF poles c M)

def poleErrT (Q K0 Mi Wi MiF WiF nN nF N : ℕ) : List ℚ :=
  (List.range (N + 1)).map (fun k => (nN : ℚ) * crudeErr Q Mi Wi k +
    (nF : ℚ) * (if k ≤ K0 then crudeErr Q MiF WiF k else tailErr Q MiF WiF k))

theorem sum_map_err' {α : Type} (l : List α) (f g δ : α → ℚ)
    (h : ∀ a ∈ l, |f a - g a| ≤ δ a) :
    |(l.map f).sum - (l.map g).sum| ≤ (l.map δ).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons]
    have e : f a + (as.map f).sum - (g a + (as.map g).sum) =
        (f a - g a) + ((as.map f).sum - (as.map g).sum) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    linarith

theorem sum_ite_count {α : Type} (l : List α) (p : α → Bool) (x y : ℚ) :
    (l.map (fun a => if p a = true then x else y)).sum =
      (l.countP p : ℚ) * x + ((l.length - l.countP p : ℕ) : ℚ) * y := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have hle := List.countP_le_length (p := p) (l := as)
    by_cases h : p a = true
    · simp only [List.map_cons, List.sum_cons, h, ite_true, List.countP_cons_of_pos h, List.length_cons, ih]
      have : as.length + 1 - (as.countP p + 1) = as.length - as.countP p := by omega
      rw [this]; push_cast; ring
    · simp only [List.map_cons, List.sum_cons, h, List.countP_cons_of_neg h, List.length_cons, ih]
      have : as.length + 1 - as.countP p = (as.length - as.countP p) + 1 := by omega
      rw [this]; push_cast; ring

theorem exact_term_eq (q : PoleR) (c : ℚ) (M k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ M) :
    (poleVecTab q.rr q.ri (powTabQ q.pr q.pi c M)).getD k 0 =
      poleTermQ q.rr q.ri k (cpowQ (uOf q c) k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [poleVecTab_getD _ _ _ _ (by omega) (by rw [powTabQ_length]; exact hk),
    powTabQ_getD' q c M (j + 1 - 1) (by omega), Nat.add_sub_cancel]

theorem poleVecT_err (Q K0 Mi Wi MiF WiF : ℕ) (poles : List PoleR) (c : ℚ) (M k : ℕ)
    (hk1 : 1 ≤ k) (hk : k ≤ M) (hMi : 2 ^ Q ≤ Mi + 4) (hMiF : 2 ^ Q ≤ MiF + 4)
    (hnear : ∀ q ∈ poles, isFar Q MiF WiF c q = false → fpPoleOK Q Mi Wi q c = true) :
    |(poleVecT Q K0 MiF WiF poles c M).getD k 0 - (poleVec poles c M).getD k 0| ≤
      ((poles.length - poles.countP (isFar Q MiF WiF c) : ℕ) : ℚ) * crudeErr Q Mi Wi k +
        (poles.countP (isFar Q MiF WiF c) : ℚ) *
          (if k ≤ K0 then crudeErr Q MiF WiF k else tailErr Q MiF WiF k) := by
  have hD : (poleVecT Q K0 MiF WiF poles c M).getD k 0 =
      (poles.map (fun q => (((fpPole Q q c (poleKq Q K0 MiF WiF M c q)).getD k 0 : ℤ) : ℚ) /
        ((2 : ℚ) ^ Q) ^ 2)).sum := by
    unfold poleVecT
    rw [getD_map_zero (poleVecZT Q K0 MiF WiF poles c M) (fun z : ℤ => (z : ℚ) / ((2 : ℚ) ^ Q) ^ 2) 0 (by simp)]
    unfold poleVecZT
    rw [vecSumZ_getD, cast_sum_div, List.map_map]
    rfl
  rw [hD, poleVec_eq_sum, abs_sub_comm]
  set δF : ℚ := if k ≤ K0 then crudeErr Q MiF WiF k else tailErr Q MiF WiF k with hδF
  set δN : ℚ := crudeErr Q Mi Wi k with hδN
  have key := sum_map_err' poles
    (fun q => (poleVecTab q.rr q.ri (powTabQ q.pr q.pi c M)).getD k 0)
    (fun q => (((fpPole Q q c (poleKq Q K0 MiF WiF M c q)).getD k 0 : ℤ) : ℚ) / ((2 : ℚ) ^ Q) ^ 2)
    (fun q => if isFar Q MiF WiF c q = true then δF else δN) (by
      intro q hq
      rw [exact_term_eq q c M k hk1 hk]
      by_cases hf : isFar Q MiF WiF c q = true
      · simp only [hf, ite_true]
        have hfok : fpPoleOK Q MiF WiF q c = true := hf
        have hkq : poleKq Q K0 MiF WiF M c q = min K0 M := by simp [poleKq, hf]
        rw [hkq]
        by_cases hk0 : k ≤ K0
        · have h1 := fpPole_term_err Q MiF WiF q c (min K0 M) k hk1 (le_min hk0 hk) hfok
          have h2 := fpTermErr_le_crude Q MiF WiF k hk1 hMiF
          have : δF = crudeErr Q MiF WiF k := by simp [hδF, hk0]
          rw [this]
          exact h1.trans h2
        · have hgt : min K0 M < k := lt_of_le_of_lt (min_le_left _ _) (by omega)
          rw [fpPole_getD_gt Q q c _ k hgt]
          have h3 := pole_tail_err Q MiF WiF q c k hk1 hfok
          have : δF = tailErr Q MiF WiF k := by simp [hδF, hk0]
          rw [this]
          simpa using h3
      · have hf' : isFar Q MiF WiF c q = false := by simpa using hf
        simp only [hf]
        have hkq : poleKq Q K0 MiF WiF M c q = M := by simp [poleKq, hf]
        rw [hkq]
        have h1 := fpPole_term_err Q Mi Wi q c M k hk1 hk (hnear q hq hf')
        exact h1.trans (fpTermErr_le_crude Q Mi Wi k hk1 hMi))
  refine key.trans ?_
  rw [sum_ite_count]
  have e : ((poles.countP (isFar Q MiF WiF c) : ℕ) : ℚ) * δF +
      ((poles.length - poles.countP (isFar Q MiF WiF c) : ℕ) : ℚ) * δN =
      ((poles.length - poles.countP (isFar Q MiF WiF c) : ℕ) : ℚ) * crudeErr Q Mi Wi k +
        (poles.countP (isFar Q MiF WiF c) : ℚ) * δF := by rw [hδN]; ring
  rw [e]

/-- the coefficients of the field at `c`: integer Taylor shifts, two-class truncated fixed-point poles -/
def fieldCoefsT (fq : FieldQ) (Ls : List ℚ) (c : ℚ) (M Q K0 MiF WiF : ℕ) : List ℚ :=
  vecAdd (shiftLK c M fq.poly)
    (vecAdd (plogSumVecI c M fq.plogs Ls) (poleVecT Q K0 MiF WiF fq.poles c M))

def errVecT (c : ℚ) (N : ℕ) (plogs : List (List ℚ × ℚ)) (εs : List ℚ) (Q Mi Wi K0 MiF WiF nN nF : ℕ) :
    List ℚ :=
  vecAdd (plogErrSumI c N plogs εs) (poleErrT Q K0 Mi Wi MiF WiF nN nF N)

theorem errVecT_getD (c : ℚ) (N : ℕ) (plogs : List (List ℚ × ℚ)) (εs : List ℚ)
    (Q Mi Wi K0 MiF WiF nN nF : ℕ) (k : ℕ) (hk : k ≤ N) :
    (errVecT c N plogs εs Q Mi Wi K0 MiF WiF nN nF).getD k 0 =
      (plogErrSum c N plogs εs).getD k 0 + ((nN : ℚ) * crudeErr Q Mi Wi k +
        (nF : ℚ) * (if k ≤ K0 then crudeErr Q MiF WiF k else tailErr Q MiF WiF k)) := by
  unfold errVecT
  rw [plogErrSumI_eq, vecAdd_getD]
  unfold poleErrT
  rw [getD_map_range _ _ _ (by omega)]

theorem fieldCoefsT_approx (fq : FieldQ) (F : ℝ → ℝ) (Ls εs : List ℚ) (c : ℚ)
    (M Q Mi Wi K0 MiF WiF : ℕ)
    (hL : LogVals c fq.plogs Ls εs) (hne : ∀ t ∈ fq.plogs, c - t.2 ≠ 0)
    (hMi : 2 ^ Q ≤ Mi + 4) (hMiF : 2 ^ Q ≤ MiF + 4)
    (hnear : ∀ q ∈ fq.poles, isFar Q MiF WiF c q = false → fpPoleOK Q Mi Wi q c = true)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ M) :
    |fieldTower fq F k (c : ℝ) / ((k.factorial : ℕ) : ℝ) -
        (((fieldCoefsT fq Ls c M Q K0 MiF WiF).getD k 0 : ℚ) : ℝ)| ≤
      (((plogErrSum c M fq.plogs εs).getD k 0 +
        (((fq.poles.length - fq.poles.countP (isFar Q MiF WiF c) : ℕ) : ℚ) * crudeErr Q Mi Wi k +
          (fq.poles.countP (isFar Q MiF WiF c) : ℚ) *
            (if k ≤ K0 then crudeErr Q MiF WiF k else tailErr Q MiF WiF k)) : ℚ) : ℝ) := by
  have h := fieldCoefs_approx fq F Ls εs c M hL hne k hk1 hk
  have hd : (fieldCoefsT fq Ls c M Q K0 MiF WiF).getD k 0 - (fieldCoefs fq Ls c M).getD k 0 =
      (poleVecT Q K0 MiF WiF fq.poles c M).getD k 0 - (poleVec fq.poles c M).getD k 0 := by
    unfold fieldCoefsT fieldCoefs
    rw [shiftLK_eq', plogSumVecI_eq]
    rw [vecAdd_getD, vecAdd_getD, vecAdd_getD, vecAdd_getD]
    ring
  have hq := poleVecT_err Q K0 Mi Wi MiF WiF fq.poles c M k hk1 hk hMi hMiF hnear
  rw [← hd] at hq
  have hq' : |(((fieldCoefsT fq Ls c M Q K0 MiF WiF).getD k 0 : ℚ) : ℝ) -
      (((fieldCoefs fq Ls c M).getD k 0 : ℚ) : ℝ)| ≤
      ((((fq.poles.length - fq.poles.countP (isFar Q MiF WiF c) : ℕ) : ℚ) * crudeErr Q Mi Wi k +
          (fq.poles.countP (isFar Q MiF WiF c) : ℚ) *
            (if k ≤ K0 then crudeErr Q MiF WiF k else tailErr Q MiF WiF k) : ℚ) : ℝ) := by
    exact_mod_cast hq
  have e : fieldTower fq F k (c : ℝ) / ((k.factorial : ℕ) : ℝ) -
        (((fieldCoefsT fq Ls c M Q K0 MiF WiF).getD k 0 : ℚ) : ℝ) =
      (fieldTower fq F k (c : ℝ) / ((k.factorial : ℕ) : ℝ) -
          (((fieldCoefs fq Ls c M).getD k 0 : ℚ) : ℝ)) +
        ((((fieldCoefs fq Ls c M).getD k 0 : ℚ) : ℝ) -
          (((fieldCoefsT fq Ls c M Q K0 MiF WiF).getD k 0 : ℚ) : ℝ)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_sub_comm (((fieldCoefs fq Ls c M).getD k 0 : ℚ) : ℝ)] at *
  rw [Rat.cast_add]
  linarith


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

/-! ### The anchor in integers

The pole part `Σ_q Re[ρ_q log (c - p_q)]` of the field value at the centre, from the integer front end of
`WLog` (`expPQ`, `findOctI`, `octRotI`): the series values of `lnQP` and `atanPosI` are evaluated as
exact integer fractions (`lnQP_eq`, `atanPosI_eq`: equal to the rational values), floored to the grid
`2^-Pg`, with an explicit error in units of the grid (`poleTermI_spec`).  The polynomial and
logarithmic parts of the anchor are the entry `0` of the coefficient vector, read from the Taylor
shifts that the coefficient test computes anyway. -/

section IntegerAnchor
open CatalanMeasure.WLog (LNTAB ATTAB expPQ expPQ_spec lnQP lnQP_spec serH atanPosI atanPosI_spec atanI argI argI_spec findOctI findOctI_spec octRotI octOKI)
open OAI.InternalCatalan

/-- slot `j` of the node table of `log (1 + j/256)` (scale `2^96`) -/
def tabN (j : ℕ) : ℕ := (LNTAB >>> (100 * j)) % 2 ^ 100

theorem lnTab_eq (j : ℕ) : CatalanMeasure.WLog.lnTab j = (tabN j : ℚ) / 2 ^ 96 := rfl

def lnJ (P Q : ℕ) : ℕ := (P - Q) * 256 / Q
def lnNN (P Q : ℕ) : ℤ := 256 * (P : ℤ) - (256 + (lnJ P Q : ℤ)) * Q
def lnDD (P Q : ℕ) : ℤ := 256 * (P : ℤ) + (256 + (lnJ P Q : ℤ)) * Q

/-- numerator and denominator of the value of `lnQP 3 m P Q` -/
def lnNum (m : ℤ) (P Q : ℕ) : ℤ :=
  let N := lnNN P Q
  let D := lnDD P Q
  let D2 := D * D
  let N2 := N * N
  let D4 := D2 * D2
  (m * (tabN 256 : ℤ) + (tabN (lnJ P Q) : ℤ)) * (15 * D4 * D) +
    pw2 97 * N * (15 * D4 + 5 * N2 * D2 + 3 * N2 * N2)

def lnDen (P Q : ℕ) : ℤ :=
  let D := lnDD P Q
  let D2 := D * D
  pw2 96 * 15 * (D2 * D2 * D)

def lnE (m : ℤ) : ℚ :=
  ((CatalanMeasure.Cert.qabs (m : ℚ)) + 1) * (1 / 2 ^ 95) + 2 * (1 / 512) ^ (2 * 3 + 1) / (1 - (1 / 512) ^ 2)

theorem lnGuard (P Q : ℕ) (hQ : 0 < Q) (hPQ : Q ≤ P) (hP2 : P ≤ 2 * Q) :
    lnJ P Q ≤ 256 ∧ 0 ≤ lnNN P Q ∧ 0 < lnDD P Q ∧ 512 * lnNN P Q ≤ lnDD P Q := by
  obtain ⟨d, rfl⟩ : ∃ d, P = Q + d := ⟨P - Q, by omega⟩
  have hd : Q + d - Q = d := by omega
  have hdQ : d ≤ Q := by omega
  unfold lnNN lnDD lnJ
  rw [hd]
  have hdm := Nat.div_add_mod (d * 256) Q
  have hr : d * 256 % Q < Q := Nat.mod_lt _ hQ
  set j := d * 256 / Q with hj
  set r := d * 256 % Q with hr'
  have hj256 : j ≤ 256 := by
    rw [hj, Nat.div_le_iff_le_mul_add_pred hQ]
    nlinarith
  have hz : (Q : ℤ) * j + r = d * 256 := by exact_mod_cast hdm
  have hQz : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hrz : (r : ℤ) < Q := by exact_mod_cast hr
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg _
  have hjz : (0 : ℤ) ≤ j := Int.natCast_nonneg _
  have hdz : (0 : ℤ) ≤ d := Int.natCast_nonneg _
  have hN : 256 * ((Q + d : ℕ) : ℤ) - (256 + (j : ℤ)) * Q = r := by push_cast; linarith
  refine ⟨hj256, ?_, ?_, ?_⟩
  · rw [hN]; exact hr0
  · push_cast; nlinarith
  · rw [hN]; push_cast; nlinarith

theorem lnVal_alg (m Tm Tj N D : ℚ) (hD : D ≠ 0) :
    m * (Tm / 2 ^ 96) + Tj / 2 ^ 96 + 2 * (N / D) * serH ((N / D) ^ 2) 3 1 =
      ((m * Tm + Tj) * (15 * (D * D * (D * D)) * D) +
        2 ^ 97 * N * (15 * (D * D * (D * D)) + 5 * (N * N) * (D * D) + 3 * (N * N) * (N * N))) /
      (2 ^ 96 * 15 * (D * D * (D * D) * D)) := by
  simp only [serH]
  field_simp
  push_cast
  ring

theorem lnQP_eq (m : ℤ) (P Q : ℕ) (hQ : 0 < Q) (hPQ : Q ≤ P) (hP2 : P ≤ 2 * Q) :
    lnQP 3 m P Q = some ((lnNum m P Q : ℚ) / (lnDen P Q : ℚ), lnE m) := by
  have hg := lnGuard P Q hQ hPQ hP2
  have hD : (0 : ℚ) < (lnDD P Q : ℚ) := by exact_mod_cast hg.2.2.1
  show (if lnJ P Q ≤ 256 ∧ 0 ≤ lnNN P Q ∧ 0 < lnDD P Q ∧ 512 * lnNN P Q ≤ lnDD P Q then
      some ((m : ℚ) * CatalanMeasure.WLog.lnTab 256 + CatalanMeasure.WLog.lnTab (lnJ P Q) +
          2 * Rat.divInt (lnNN P Q) (lnDD P Q) * serH (Rat.divInt (lnNN P Q) (lnDD P Q) ^ 2) 3 1, lnE m)
      else none) = _
  rw [if_pos hg]
  congr 2
  rw [Rat.divInt_eq_div]
  simp only [CatalanMeasure.WLog.lnTab]
  have := lnVal_alg (m : ℚ) ((tabN 256 : ℕ) : ℚ) ((tabN (lnJ P Q) : ℕ) : ℚ) (lnNN P Q : ℚ) (lnDD P Q : ℚ) hD.ne'
  rw [show (((LNTAB >>> (100 * 256)) % 2 ^ 100 : ℕ) : ℚ) = ((tabN 256 : ℕ) : ℚ) from rfl,
    show (((LNTAB >>> (100 * lnJ P Q)) % 2 ^ 100 : ℕ) : ℚ) = ((tabN (lnJ P Q) : ℕ) : ℚ) from rfl]
  rw [this]
  unfold lnNum lnDen
  simp only [pw2_eq]
  push_cast
  ring

theorem qabs_le_natAbs (m : ℤ) : CatalanMeasure.Cert.qabs (m : ℚ) ≤ (m.natAbs : ℚ) := by
  rw [CatalanMeasure.Cert.qabs_eq]
  have : |(m : ℚ)| = (m.natAbs : ℚ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
  rw [this]

theorem lnE_le (m : ℤ) (hm : m.natAbs ≤ 2 ^ 20) : lnE m ≤ 1 / 2 ^ 56 := by
  unfold lnE
  have h1 := qabs_le_natAbs m
  have h2 : (m.natAbs : ℚ) ≤ 2 ^ 20 := by exact_mod_cast hm
  have h3 : CatalanMeasure.Cert.qabs (m : ℚ) + 1 ≤ 2 ^ 20 + 1 := by linarith
  have h4 : (CatalanMeasure.Cert.qabs (m : ℚ) + 1) * (1 / 2 ^ 95) ≤ (2 ^ 20 + 1) * (1 / 2 ^ 95) := by
    apply mul_le_mul_of_nonneg_right h3; positivity
  have h5 : ((2 ^ 20 + 1 : ℚ)) * (1 / 2 ^ 95) + 2 * (1 / 512 : ℚ) ^ (2 * 3 + 1) / (1 - (1 / 512) ^ 2) ≤ 1 / 2 ^ 56 := by
    norm_num
  linarith

def lnVI (Pg : ℕ) (m : ℤ) (P Q : ℕ) : ℤ := lnNum m P Q * pw2 Pg / lnDen P Q

theorem lnDen_pos (P Q : ℕ) (hQ : 0 < Q) (hPQ : Q ≤ P) (hP2 : P ≤ 2 * Q) : 0 < lnDen P Q := by
  have hg := lnGuard P Q hQ hPQ hP2
  have hD := hg.2.2.1
  unfold lnDen
  rw [pw2_eq]
  set D := lnDD P Q
  have : 0 < D * D * (D * D) * D := by positivity
  positivity

/-- flooring a value `X/d` known to `e ≤ 2^-Pg` to the grid `2^-Pg` costs one more unit -/
theorem floor_enc (Pg : ℕ) (X d : ℤ) (hd : 0 < d) (x : ℝ) (e : ℝ) (hx : |x - (X : ℝ) / (d : ℝ)| ≤ e)
    (he : e ≤ 1 / 2 ^ Pg) :
    |x - ((X * 2 ^ Pg / d : ℤ) : ℝ) / 2 ^ Pg| ≤ 2 / 2 ^ Pg := by
  have hfl := floorDiv_spec (X * 2 ^ Pg) d hd
  have hdq : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hP2g : (0 : ℝ) < 2 ^ Pg := by positivity
  obtain ⟨f1, f2⟩ := hfl
  have g1 : ((X * 2 ^ Pg / d : ℤ) : ℝ) ≤ (X : ℝ) * 2 ^ Pg / (d : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr f1
    push_cast at this; exact this
  have g2 : (X : ℝ) * 2 ^ Pg / (d : ℝ) < ((X * 2 ^ Pg / d : ℤ) : ℝ) + 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr f2
    push_cast at this; exact this
  set v : ℝ := (X : ℝ) / (d : ℝ) with hvdef
  have e1 : (X : ℝ) * 2 ^ Pg / (d : ℝ) = v * 2 ^ Pg := by rw [hvdef]; ring
  rw [e1] at g1 g2
  have k1 : ((X * 2 ^ Pg / d : ℤ) : ℝ) / 2 ^ Pg ≤ v := by
    rw [div_le_iff₀ hP2g]; exact g1
  have k2 : v < (((X * 2 ^ Pg / d : ℤ) : ℝ) + 1) / 2 ^ Pg := by
    rw [lt_div_iff₀ hP2g]; exact g2
  have k3 : (((X * 2 ^ Pg / d : ℤ) : ℝ) + 1) / 2 ^ Pg = ((X * 2 ^ Pg / d : ℤ) : ℝ) / 2 ^ Pg + 1 / 2 ^ Pg := by ring
  rw [abs_le] at hx ⊢
  have : (2 : ℝ) / 2 ^ Pg = 1 / 2 ^ Pg + 1 / 2 ^ Pg := by ring
  rw [this]
  constructor <;> linarith [hx.1, hx.2]

theorem lnVI_spec (Pg : ℕ) (hPg : Pg ≤ 56) (m : ℤ) (hm : m.natAbs ≤ 2 ^ 20) (P Q : ℕ)
    (hQ : 0 < Q) (hPQ : Q ≤ P) (hP2 : P ≤ 2 * Q) :
    |Real.log ((2 : ℝ) ^ m * ((P : ℝ) / (Q : ℝ))) - ((lnVI Pg m P Q : ℤ) : ℝ) / 2 ^ Pg| ≤ 2 / 2 ^ Pg := by
  have h := lnQP_spec hQ hPQ hP2 (lnQP_eq m P Q hQ hPQ hP2)
  have hden := lnDen_pos P Q hQ hPQ hP2
  have hE := lnE_le m hm
  have hE' : ((lnE m : ℚ) : ℝ) ≤ 1 / 2 ^ 56 := by
    have := (Rat.cast_le (K := ℝ)).mpr hE
    push_cast at this; exact this
  have hP2g : (0 : ℝ) < 2 ^ Pg := by positivity
  have h56 : (1 : ℝ) / 2 ^ 56 ≤ 1 / 2 ^ Pg := by
    apply one_div_le_one_div_of_le hP2g
    exact pow_le_pow_right₀ (by norm_num) hPg
  have hv : (((lnNum m P Q : ℚ) / (lnDen P Q : ℚ) : ℚ) : ℝ) = ((lnNum m P Q : ℤ) : ℝ) / ((lnDen P Q : ℤ) : ℝ) := by
    push_cast; rfl
  rw [hv] at h
  have hVe : lnVI Pg m P Q = lnNum m P Q * 2 ^ Pg / lnDen P Q := by unfold lnVI; rw [pw2_eq]
  rw [hVe]
  exact floor_enc Pg _ _ hden _ _ h (hE'.trans h56)

/-! ### the arctangent node evaluation in integers -/

def tabA (j : ℕ) : ℕ := (ATTAB >>> (100 * j)) % 2 ^ 100

def atJ (S R : ℕ) : ℕ := S * 128 / R
def atNN (S R : ℕ) : ℤ := 128 * (S : ℤ) - (atJ S R : ℤ) * R
def atDD (S R : ℕ) : ℤ := 128 * (R : ℤ) + (atJ S R : ℤ) * S

def atNum (S R : ℕ) : ℤ :=
  let N := atNN S R
  let D := atDD S R
  let D2 := D * D
  let D4 := D2 * D2
  let D6 := D4 * D2
  let N2 := N * N
  let N4 := N2 * N2
  (tabA (atJ S R) : ℤ) * (105 * (D6 * D)) + pw2 96 * N * (105 * D6 - 35 * N2 * D4 + 21 * N4 * D2 - 15 * (N4 * N2))

def atDen (S R : ℕ) : ℤ :=
  let D := atDD S R
  let D2 := D * D
  let D4 := D2 * D2
  pw2 96 * 105 * (D4 * D2 * D)

def atE : ℚ := 1 / 2 ^ 95 + (1 / 128) ^ (2 * 4 + 1) / (1 - (1 / 128) ^ 2)

theorem atGuard (S R : ℕ) (hR : 0 < R) (h2 : 2 * S ≤ R) :
    atJ S R ≤ 64 ∧ 0 ≤ atNN S R ∧ 0 < atDD S R ∧ 128 * atNN S R ≤ atDD S R := by
  unfold atNN atDD atJ
  have hdm := Nat.div_add_mod (S * 128) R
  have hr : S * 128 % R < R := Nat.mod_lt _ hR
  set j := S * 128 / R with hj
  set r := S * 128 % R with hr'
  have hj64 : j ≤ 64 := by
    rw [hj, Nat.div_le_iff_le_mul_add_pred hR]
    nlinarith
  have hz : (R : ℤ) * j + r = S * 128 := by exact_mod_cast hdm
  have hRz : (0 : ℤ) < R := by exact_mod_cast hR
  have hrz : (r : ℤ) < R := by exact_mod_cast hr
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg _
  have hjz : (0 : ℤ) ≤ j := Int.natCast_nonneg _
  have hSz : (0 : ℤ) ≤ S := Int.natCast_nonneg _
  have hN : 128 * (S : ℤ) - (j : ℤ) * R = r := by linarith
  refine ⟨hj64, ?_, ?_, ?_⟩
  · rw [hN]; exact hr0
  · nlinarith
  · rw [hN]; nlinarith

theorem atVal_alg (Ta N D : ℚ) (hD : D ≠ 0) :
    Ta / 2 ^ 96 + (N / D) * serH (-((N / D) ^ 2)) 4 1 =
      (Ta * (105 * (D * D * (D * D) * (D * D) * D)) +
        2 ^ 96 * N * (105 * (D * D * (D * D) * (D * D)) - 35 * (N * N) * (D * D * (D * D)) +
          21 * (N * N * (N * N)) * (D * D) - 15 * (N * N * (N * N) * (N * N)))) /
      (2 ^ 96 * 105 * (D * D * (D * D) * (D * D) * D)) := by
  simp only [serH]
  field_simp
  push_cast
  ring

theorem atanPosI_eq (S R : ℕ) (hR : 0 < R) (h2 : 2 * S ≤ R) :
    atanPosI 4 S R = some ((atNum S R : ℚ) / (atDen S R : ℚ), atE) := by
  have hg := atGuard S R hR h2
  have hD : (0 : ℚ) < (atDD S R : ℚ) := by exact_mod_cast hg.2.2.1
  show (if atJ S R ≤ 64 ∧ 0 ≤ atNN S R ∧ 0 < atDD S R ∧ 128 * atNN S R ≤ atDD S R then
      some (CatalanMeasure.WLog.atTab (atJ S R) + Rat.divInt (atNN S R) (atDD S R) *
          serH (-(Rat.divInt (atNN S R) (atDD S R) ^ 2)) 4 1, atE)
      else none) = _
  rw [if_pos hg]
  congr 2
  rw [Rat.divInt_eq_div]
  simp only [CatalanMeasure.WLog.atTab]
  have := atVal_alg ((tabA (atJ S R) : ℕ) : ℚ) (atNN S R : ℚ) (atDD S R : ℚ) hD.ne'
  rw [show (((ATTAB >>> (100 * atJ S R)) % 2 ^ 100 : ℕ) : ℚ) = ((tabA (atJ S R) : ℕ) : ℚ) from rfl]
  rw [this]
  unfold atNum atDen
  simp only [pw2_eq]
  push_cast
  ring

def pi4n : ℤ := 3141592653589793238465
def pi4d : ℤ := 4000000000000000000000

theorem PI4_eq : CatalanMeasure.WLog.PI4 = (pi4n : ℚ) / (pi4d : ℚ) := by
  unfold CatalanMeasure.WLog.PI4 pi4n pi4d; norm_num

def argVI (Pg : ℕ) (A B : ℤ) : Option ℤ :=
  match findOctI (A, B) with
  | none => none
  | some k =>
    let p := octRotI k (A, B)
    let S := p.2.natAbs
    let R := p.1.toNat
    let sg : ℤ := if p.2 < 0 then -1 else 1
    some ((k * pi4n * atDen S R + sg * atNum S R * pi4d) * pw2 Pg / (pi4d * atDen S R))

theorem atDen_pos (S R : ℕ) (hR : 0 < R) (h2 : 2 * S ≤ R) : 0 < atDen S R := by
  have hg := atGuard S R hR h2
  have hD := hg.2.2.1
  unfold atDen
  rw [pw2_eq]
  set D := atDD S R
  have : 0 < D * D * (D * D) * (D * D) * D := by positivity
  positivity

theorem octFacts {A B : ℤ} {k : ℤ} (hk : findOctI (A, B) = some k) :
    0 < (octRotI k (A, B)).1 ∧ 2 * (octRotI k (A, B)).2.natAbs ≤ (octRotI k (A, B)).1.toNat ∧ |k| ≤ 4 := by
  obtain ⟨hok, hkabs⟩ := findOctI_spec hk
  unfold octOKI at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  refine ⟨hok.1.1.1, ?_, hkabs⟩
  have h1 := hok.1.1.2
  have h0 := hok.1.1.1
  omega

theorem argI_eq (A B : ℤ) (k : ℤ) (hk : findOctI (A, B) = some k) :
    argI 4 A B = some (((k * pi4n * atDen (octRotI k (A, B)).2.natAbs (octRotI k (A, B)).1.toNat +
        (if (octRotI k (A, B)).2 < 0 then -1 else 1) * atNum (octRotI k (A, B)).2.natAbs (octRotI k (A, B)).1.toNat * pi4d : ℤ) : ℚ) /
      ((pi4d * atDen (octRotI k (A, B)).2.natAbs (octRotI k (A, B)).1.toNat : ℤ) : ℚ),
      CatalanMeasure.Cert.qabs (k : ℚ) * CatalanMeasure.WLog.PI4E + atE) := by
  obtain ⟨h0, h2, _⟩ := octFacts hk
  set p := octRotI k (A, B) with hp
  have hR : 0 < p.1.toNat := by omega
  have hat := atanPosI_eq p.2.natAbs p.1.toNat hR h2
  have hden : (0 : ℚ) < (atDen p.2.natAbs p.1.toNat : ℚ) := by exact_mod_cast atDen_pos _ _ hR h2
  have hpi : (pi4d : ℚ) ≠ 0 := by unfold pi4d; norm_num
  unfold argI
  rw [hk]
  show (match atanI 4 p.2 p.1 with
    | none => none
    | some (v, e) => some ((k : ℚ) * CatalanMeasure.WLog.PI4 + v, CatalanMeasure.Cert.qabs (k : ℚ) * CatalanMeasure.WLog.PI4E + e)) = _
  unfold atanI
  rw [hat]
  simp only []
  rw [PI4_eq]
  by_cases hs : p.2 < 0
  · simp only [hs, if_true]
    congr 2
    push_cast
    field_simp
  · simp only [hs, if_false]
    congr 2
    push_cast
    field_simp

theorem argE_le (k : ℤ) (hk : |k| ≤ 4) : CatalanMeasure.Cert.qabs (k : ℚ) * CatalanMeasure.WLog.PI4E + atE ≤ 1 / 2 ^ 56 := by
  have h1 : CatalanMeasure.Cert.qabs (k : ℚ) ≤ 4 := by
    rw [CatalanMeasure.Cert.qabs_eq]
    have : |(k : ℚ)| = ((|k| : ℤ) : ℚ) := by push_cast; rfl
    rw [this]
    exact_mod_cast hk
  have h2 : CatalanMeasure.Cert.qabs (k : ℚ) * CatalanMeasure.WLog.PI4E ≤ 4 * CatalanMeasure.WLog.PI4E := by
    apply mul_le_mul_of_nonneg_right h1; unfold CatalanMeasure.WLog.PI4E; norm_num
  have h3 : 4 * CatalanMeasure.WLog.PI4E + atE ≤ 1 / 2 ^ 56 := by
    unfold CatalanMeasure.WLog.PI4E atE; norm_num
  linarith

theorem argVI_spec (Pg : ℕ) (hPg : Pg ≤ 56) (A B : ℤ) (L : ℕ) (hL : 0 < L) (V : ℤ)
    (h : argVI Pg A B = some V) :
    |Complex.arg ⟨(A : ℝ) / (L : ℝ), (B : ℝ) / (L : ℝ)⟩ - (V : ℝ) / 2 ^ Pg| ≤ 2 / 2 ^ Pg := by
  unfold argVI at h
  split at h
  · simp at h
  · rename_i k hk
    simp only [Option.some.injEq] at h
    obtain ⟨h0, h2, hkabs⟩ := octFacts hk
    have heq := argI_eq A B k hk
    have hs := argI_spec hL heq
    have hR : 0 < (octRotI k (A, B)).1.toNat := by omega
    have hden := atDen_pos _ _ hR h2
    have hpd : 0 < pi4d := by unfold pi4d; norm_num
    have hd : 0 < pi4d * atDen (octRotI k (A, B)).2.natAbs (octRotI k (A, B)).1.toNat := by positivity
    have hE := argE_le k hkabs
    have hE' : (((CatalanMeasure.Cert.qabs (k : ℚ) * CatalanMeasure.WLog.PI4E + atE : ℚ)) : ℝ) ≤ 1 / 2 ^ 56 := by
      have := (Rat.cast_le (K := ℝ)).mpr hE
      push_cast at this ⊢; exact this
    have hP2g : (0 : ℝ) < 2 ^ Pg := by positivity
    have h56 : (1 : ℝ) / 2 ^ 56 ≤ 1 / 2 ^ Pg := by
      apply one_div_le_one_div_of_le hP2g
      exact pow_le_pow_right₀ (by norm_num) hPg
    rw [← h]
    simp only [pw2_eq]
    have hs2 : |Complex.arg ⟨(A : ℝ) / (L : ℝ), (B : ℝ) / (L : ℝ)⟩ -
        ((k * pi4n * atDen (octRotI k (A, B)).2.natAbs (octRotI k (A, B)).1.toNat +
          (if (octRotI k (A, B)).2 < 0 then -1 else 1) * atNum (octRotI k (A, B)).2.natAbs
            (octRotI k (A, B)).1.toNat * pi4d : ℤ) : ℝ) /
          ((pi4d * atDen (octRotI k (A, B)).2.natAbs (octRotI k (A, B)).1.toNat : ℤ) : ℝ)| ≤
        (((CatalanMeasure.Cert.qabs (k : ℚ) * CatalanMeasure.WLog.PI4E + atE : ℚ)) : ℝ) := by
      have := hs
      by_cases hn : (octRotI k (A, B)).2 < 0
      · simp only [hn, if_true] at this ⊢
        push_cast at this ⊢
        exact this
      · simp only [hn, if_false] at this ⊢
        push_cast at this ⊢
        exact this
    exact floor_enc Pg _ _ hd _ _ hs2 (hE'.trans h56)

/-! ### the pole terms -/

def zA (c : ℚ) (q : PoleR) : ℤ := (c.num * (q.pr.den : ℤ) - q.pr.num * (c.den : ℤ)) * (q.pi.den : ℤ)
def zB (c : ℚ) (q : PoleR) : ℤ := -(q.pi.num) * ((c.den * q.pr.den : ℕ) : ℤ)
def zL (c : ℚ) (q : PoleR) : ℕ := c.den * q.pr.den * q.pi.den

theorem zL_pos (c : ℚ) (q : PoleR) : 0 < zL c q := by
  unfold zL
  have := c.den_pos; have := q.pr.den_pos; have := q.pi.den_pos
  positivity

theorem zA_spec (c : ℚ) (q : PoleR) : (c : ℝ) - (q.pr : ℝ) = (zA c q : ℝ) / (zL c q : ℝ) := by
  have h1 : (c.den : ℝ) ≠ 0 := by exact_mod_cast c.den_nz
  have h2 : (q.pr.den : ℝ) ≠ 0 := by exact_mod_cast q.pr.den_nz
  have h3 : (q.pi.den : ℝ) ≠ 0 := by exact_mod_cast q.pi.den_nz
  unfold zA zL
  rw [Rat.cast_def c, Rat.cast_def q.pr]
  push_cast
  field_simp

theorem zB_spec (c : ℚ) (q : PoleR) : -(q.pi : ℝ) = (zB c q : ℝ) / (zL c q : ℝ) := by
  have h1 : (c.den : ℝ) ≠ 0 := by exact_mod_cast c.den_nz
  have h2 : (q.pr.den : ℝ) ≠ 0 := by exact_mod_cast q.pr.den_nz
  have h3 : (q.pi.den : ℝ) ≠ 0 := by exact_mod_cast q.pi.den_nz
  unfold zB zL
  rw [Rat.cast_def q.pi]
  push_cast
  field_simp

/-- the integer value `W` (in units `2^-Pg`) and the error `E` (same units) of the pole term -/
def poleTermI (Pg : ℕ) (q : PoleR) (c : ℚ) : Option (ℤ × ℕ) :=
  match expPQ (zA c q * zA c q + zB c q * zB c q).toNat (zL c q * zL c q) with
  | none => none
  | some (m, P, Q) =>
    if m.natAbs ≤ 2 ^ 20 then
      if q.ri = 0 then
        some (q.rr.num * lnVI Pg m P Q / (2 * (q.rr.den : ℤ)), q.rr.num.natAbs / q.rr.den + 2)
      else
        match argVI Pg (zA c q) (zB c q) with
        | none => none
        | some Va =>
          some (q.rr.num * lnVI Pg m P Q / (2 * (q.rr.den : ℤ)) - q.ri.num * Va / (q.ri.den : ℤ),
            (q.rr.num.natAbs / q.rr.den + 2) + (2 * (q.ri.num.natAbs / q.ri.den + 1) + 1))
    else none

theorem abs_cast_le_div (r : ℚ) : |(r : ℝ)| ≤ ((r.num.natAbs / r.den : ℕ) : ℝ) + 1 := by
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have h1 := Nat.lt_mul_div_succ r.num.natAbs r.den_pos
  have h1' : (r.num.natAbs : ℝ) < (r.den : ℝ) * (((r.num.natAbs / r.den : ℕ) : ℝ) + 1) := by
    exact_mod_cast h1
  have e : |(r : ℝ)| = (r.num.natAbs : ℝ) / (r.den : ℝ) := by
    rw [Rat.cast_def, abs_div, abs_of_pos hd]
    congr 1
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
  rw [e, div_le_iff₀ hd]
  nlinarith

/-- a weight `a/d` times a value `ℓ` known to `δ`, floored to the grid -/
theorem scaled_floor (Pg : ℕ) (a : ℤ) (d : ℕ) (hd : 0 < d) (V : ℤ) (ℓ δ : ℝ)
    (hℓ : |ℓ - (V : ℝ) / 2 ^ Pg| ≤ δ) :
    |((a : ℝ) / (d : ℝ)) * ℓ - ((a * V / (d : ℤ) : ℤ) : ℝ) / 2 ^ Pg| ≤
      |(a : ℝ) / (d : ℝ)| * δ + 1 / 2 ^ Pg := by
  have hdz : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  obtain ⟨f1, f2⟩ := floorDiv_spec (a * V) (d : ℤ) hdz
  have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hP2g : (0 : ℝ) < 2 ^ Pg := by positivity
  have g1 : ((a * V / (d : ℤ) : ℤ) : ℝ) ≤ (a : ℝ) * V / (d : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr f1
    push_cast at this; exact this
  have g2 : (a : ℝ) * V / (d : ℝ) < ((a * V / (d : ℤ) : ℤ) : ℝ) + 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr f2
    push_cast at this; exact this
  set W : ℝ := ((a * V / (d : ℤ) : ℤ) : ℝ) with hW
  have key : ((a : ℝ) / (d : ℝ)) * ℓ - W / 2 ^ Pg =
      ((a : ℝ) / (d : ℝ)) * (ℓ - (V : ℝ) / 2 ^ Pg) + ((a : ℝ) * V / (d : ℝ) - W) / 2 ^ Pg := by
    field_simp
    ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have t1 : |(a : ℝ) / (d : ℝ)| * |ℓ - (V : ℝ) / 2 ^ Pg| ≤ |(a : ℝ) / (d : ℝ)| * δ :=
    mul_le_mul_of_nonneg_left hℓ (abs_nonneg _)
  have t2 : |((a : ℝ) * V / (d : ℝ) - W) / 2 ^ Pg| ≤ 1 / 2 ^ Pg := by
    rw [abs_div, abs_of_pos hP2g]
    apply div_le_div_of_nonneg_right _ hP2g.le
    rw [abs_le]; constructor <;> linarith
  linarith

theorem poleTermI_spec (Pg : ℕ) (hPg : Pg ≤ 56) (q : PoleR) (c : ℚ) (w : ℤ) (e : ℕ)
    (h : poleTermI Pg q c = some (w, e)) :
    |(q.rho * Complex.log (((c : ℝ) : ℂ) - q.pc)).re - (w : ℝ) / 2 ^ Pg| ≤ (e : ℝ) / 2 ^ Pg := by
  have hL := zL_pos c q
  have hLR : (0 : ℝ) < (zL c q : ℝ) := by exact_mod_cast hL
  have hz : (((c : ℝ) : ℂ) - q.pc) = ⟨(zA c q : ℝ) / (zL c q : ℝ), (zB c q : ℝ) / (zL c q : ℝ)⟩ := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.ofReal_re, PoleR.pc]; exact zA_spec c q
    · simp only [Complex.sub_im, Complex.ofReal_im, PoleR.pc]; rw [zero_sub]; exact zB_spec c q
  have hval : (q.rho * Complex.log (((c : ℝ) : ℂ) - q.pc)).re =
      (q.rr : ℝ) * (Real.log (((zA c q : ℝ) / (zL c q : ℝ)) ^ 2 + ((zB c q : ℝ) / (zL c q : ℝ)) ^ 2) / 2) -
        (q.ri : ℝ) * Complex.arg ⟨(zA c q : ℝ) / (zL c q : ℝ), (zB c q : ℝ) / (zL c q : ℝ)⟩ := by
    rw [hz, barrierComplexLog_weighted_re]
    rfl
  rw [hval]
  unfold poleTermI at h
  split at h
  · simp at h
  · rename_i m P Q hexp
    obtain ⟨hQ, hPQ, hP2, hN⟩ := expPQ_spec hexp
    have hnn : 0 ≤ zA c q * zA c q + zB c q * zB c q := by nlinarith [sq_nonneg (zA c q), sq_nonneg (zB c q)]
    have hcast : (((zA c q * zA c q + zB c q * zB c q).toNat : ℕ) : ℝ) =
        (zA c q : ℝ) * zA c q + (zB c q : ℝ) * zB c q := by
      have : (((zA c q * zA c q + zB c q * zB c q).toNat : ℕ) : ℤ) = zA c q * zA c q + zB c q * zB c q :=
        Int.toNat_of_nonneg hnn
      have h2 : (((zA c q * zA c q + zB c q * zB c q).toNat : ℕ) : ℝ) =
          ((zA c q * zA c q + zB c q * zB c q : ℤ) : ℝ) := by exact_mod_cast this
      rw [h2]; push_cast; ring
    have hlogarg : ((zA c q : ℝ) / (zL c q : ℝ)) ^ 2 + ((zB c q : ℝ) / (zL c q : ℝ)) ^ 2 =
        (2 : ℝ) ^ m * ((P : ℝ) / (Q : ℝ)) := by
      rw [← hN, hcast]
      push_cast
      field_simp
    rw [hlogarg]
    split_ifs at h with hm hri
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hl := lnVI_spec Pg hPg m hm P Q hQ hPQ hP2
      have hd : 0 < 2 * q.rr.den := by have := q.rr.den_pos; omega
      have hs := scaled_floor Pg q.rr.num (2 * q.rr.den) hd (lnVI Pg m P Q)
        (Real.log ((2 : ℝ) ^ m * ((P : ℝ) / (Q : ℝ)))) (2 / 2 ^ Pg) hl
      have hri0 : (q.ri : ℝ) = 0 := by exact_mod_cast hri
      have hrr : ((q.rr.num : ℝ) / ((2 * q.rr.den : ℕ) : ℝ)) = (q.rr : ℝ) / 2 := by
        rw [Rat.cast_def q.rr]; push_cast; field_simp
      rw [hrr] at hs
      push_cast at hs
      rw [hri0, zero_mul, sub_zero]
      have hb := abs_cast_le_div q.rr
      have hP2g : (0 : ℝ) < 2 ^ Pg := by positivity
      have e1 : (q.rr : ℝ) * (Real.log ((2 : ℝ) ^ m * ((P : ℝ) / (Q : ℝ))) / 2) =
          (q.rr : ℝ) / 2 * Real.log ((2 : ℝ) ^ m * ((P : ℝ) / (Q : ℝ))) := by ring
      rw [e1]
      refine hs.trans ?_
      have : |(q.rr : ℝ) / 2| * (2 / 2 ^ Pg) + 1 / 2 ^ Pg ≤ (((q.rr.num.natAbs / q.rr.den + 2 : ℕ)) : ℝ) / 2 ^ Pg := by
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        push_cast
        rw [← sub_nonneg]
        have : (((q.rr.num.natAbs / q.rr.den : ℕ) : ℝ) + 2) / 2 ^ Pg -
            (|(q.rr : ℝ)| / 2 * (2 / 2 ^ Pg) + 1 / 2 ^ Pg) =
            (((q.rr.num.natAbs / q.rr.den : ℕ) : ℝ) + 1 - |(q.rr : ℝ)|) / 2 ^ Pg := by
          field_simp; ring
        rw [this]
        apply div_nonneg _ hP2g.le
        linarith
      exact this
    · -- complex pole
      split at h
      · simp at h
      · rename_i Va hVa
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hl := lnVI_spec Pg hPg m hm P Q hQ hPQ hP2
        have hA := argVI_spec Pg hPg (zA c q) (zB c q) (zL c q) hL Va hVa
        have hd : 0 < 2 * q.rr.den := by have := q.rr.den_pos; omega
        have hs1 := scaled_floor Pg q.rr.num (2 * q.rr.den) hd (lnVI Pg m P Q)
          (Real.log ((2 : ℝ) ^ m * ((P : ℝ) / (Q : ℝ)))) (2 / 2 ^ Pg) hl
        have hs2 := scaled_floor Pg q.ri.num q.ri.den q.ri.den_pos Va
          (Complex.arg ⟨(zA c q : ℝ) / (zL c q : ℝ), (zB c q : ℝ) / (zL c q : ℝ)⟩) (2 / 2 ^ Pg) hA
        have hrr : ((q.rr.num : ℝ) / ((2 * q.rr.den : ℕ) : ℝ)) = (q.rr : ℝ) / 2 := by
          rw [Rat.cast_def q.rr]; push_cast; field_simp
        have hri' : ((q.ri.num : ℝ) / (q.ri.den : ℝ)) = (q.ri : ℝ) := by
          rw [Rat.cast_def q.ri]
        rw [hrr] at hs1
        rw [hri'] at hs2
        push_cast at hs1 hs2 ⊢
        have hb1 := abs_cast_le_div q.rr
        have hb2 := abs_cast_le_div q.ri
        have hP2g : (0 : ℝ) < 2 ^ Pg := by positivity
        set ℓ := Real.log ((2 : ℝ) ^ m * ((P : ℝ) / (Q : ℝ))) with hℓ
        set ar := Complex.arg ⟨(zA c q : ℝ) / (zL c q : ℝ), (zB c q : ℝ) / (zL c q : ℝ)⟩ with har
        set W1 : ℝ := ((q.rr.num * lnVI Pg m P Q / (2 * (q.rr.den : ℤ)) : ℤ) : ℝ) with hW1
        set W2 : ℝ := ((q.ri.num * Va / (q.ri.den : ℤ) : ℤ) : ℝ) with hW2
        have key : (q.rr : ℝ) * (ℓ / 2) - (q.ri : ℝ) * ar - (W1 - W2) / 2 ^ Pg =
            ((q.rr : ℝ) / 2 * ℓ - W1 / 2 ^ Pg) - ((q.ri : ℝ) * ar - W2 / 2 ^ Pg) := by ring
        rw [key]
        refine (abs_sub _ _).trans ?_
        have c1 : |(q.rr : ℝ) / 2| * (2 / 2 ^ Pg) + 1 / 2 ^ Pg ≤ (((q.rr.num.natAbs / q.rr.den : ℕ) : ℝ) + 2) / 2 ^ Pg := by
          rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          rw [← sub_nonneg]
          have : (((q.rr.num.natAbs / q.rr.den : ℕ) : ℝ) + 2) / 2 ^ Pg -
              (|(q.rr : ℝ)| / 2 * (2 / 2 ^ Pg) + 1 / 2 ^ Pg) =
              (((q.rr.num.natAbs / q.rr.den : ℕ) : ℝ) + 1 - |(q.rr : ℝ)|) / 2 ^ Pg := by
            field_simp; ring
          rw [this]
          apply div_nonneg _ hP2g.le
          linarith
        have c2 : |(q.ri : ℝ)| * (2 / 2 ^ Pg) + 1 / 2 ^ Pg ≤
            (2 * (((q.ri.num.natAbs / q.ri.den : ℕ) : ℝ) + 1) + 1) / 2 ^ Pg := by
          rw [← sub_nonneg]
          have : (2 * (((q.ri.num.natAbs / q.ri.den : ℕ) : ℝ) + 1) + 1) / 2 ^ Pg -
              (|(q.ri : ℝ)| * (2 / 2 ^ Pg) + 1 / 2 ^ Pg) =
              2 * ((((q.ri.num.natAbs / q.ri.den : ℕ) : ℝ) + 1) - |(q.ri : ℝ)|) / 2 ^ Pg := by
            field_simp; ring
          rw [this]
          apply div_nonneg _ hP2g.le
          linarith
        have c3 : ((((q.rr.num.natAbs / q.rr.den : ℕ) : ℝ) + 2) + (2 * (((q.ri.num.natAbs / q.ri.den : ℕ) : ℝ) + 1) + 1)) / 2 ^ Pg =
            (((q.rr.num.natAbs / q.rr.den : ℕ) : ℝ) + 2) / 2 ^ Pg + (2 * (((q.ri.num.natAbs / q.ri.den : ℕ) : ℝ) + 1) + 1) / 2 ^ Pg := by ring
        rw [c3]
        have t1 := hs1.trans c1
        have t2 := hs2.trans c2
        linarith [t1, t2]

def poleSumI (Pg : ℕ) (c : ℚ) : List PoleR → Option (ℤ × ℕ)
  | [] => some (0, 0)
  | q :: qs =>
    match poleTermI Pg q c, poleSumI Pg c qs with
    | some (w, e), some (s, t) => some (w + s, e + t)
    | _, _ => none

theorem poleSumI_spec (Pg : ℕ) (hPg : Pg ≤ 56) (c : ℚ) : ∀ (poles : List PoleR) (S : ℤ) (E : ℕ),
    poleSumI Pg c poles = some (S, E) →
    |(poles.map (fun q => (q.rho * Complex.log (((c : ℝ) : ℂ) - q.pc)).re)).sum - (S : ℝ) / 2 ^ Pg| ≤
      (E : ℝ) / 2 ^ Pg := by
  intro poles
  induction poles with
  | nil => intro S E h; simp [poleSumI] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | cons q qs ih =>
    intro S E h
    simp only [poleSumI] at h
    split at h
    · rename_i w e s t h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have a1 := poleTermI_spec Pg hPg q c w e h1
      have a2 := ih s t h2
      simp only [List.map_cons, List.sum_cons]
      rw [Int.cast_add, Nat.cast_add]
      have : (q.rho * Complex.log (((c : ℝ) : ℂ) - q.pc)).re + (qs.map (fun q => (q.rho * Complex.log (((c : ℝ) : ℂ) - q.pc)).re)).sum - ((w : ℝ) + s) / 2 ^ Pg =
        ((q.rho * Complex.log (((c : ℝ) : ℂ) - q.pc)).re - (w : ℝ) / 2 ^ Pg) + ((qs.map (fun q => (q.rho * Complex.log (((c : ℝ) : ℂ) - q.pc)).re)).sum - (s : ℝ) / 2 ^ Pg) := by ring
      rw [this]
      have := (abs_add_le _ _).trans (add_le_add a1 a2)
      refine this.trans (le_of_eq ?_)
      ring
    · simp at h


theorem poleVecT_zero (Q K0 MiF WiF : ℕ) (poles : List PoleR) (c : ℚ) (M : ℕ) :
    (poleVecT Q K0 MiF WiF poles c M).getD 0 0 = 0 := by
  unfold poleVecT
  rw [getD_map_zero _ _ 0 (by simp)]
  have : (poleVecZT Q K0 MiF WiF poles c M).getD 0 0 = 0 := by
    unfold poleVecZT
    rw [vecSumZ_getD, List.map_map]
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨q, _, rfl⟩ := hx
    simp [fpPole]
  rw [this]; simp

theorem coefs0_approx (fq : FieldQ) (Ls εs : List ℚ) (c : ℚ) (M Q K0 MiF WiF : ℕ)
    (hL : LogVals c fq.plogs Ls εs) (hne : ∀ t ∈ fq.plogs, c - t.2 ≠ 0) :
    |polyTow fq.poly 0 (c : ℝ) + plogSumTower fq.plogs 0 (c : ℝ) -
        (((fieldCoefsT fq Ls c M Q K0 MiF WiF).getD 0 0 : ℚ) : ℝ)| ≤
      (((plogErrSum c M fq.plogs εs).getD 0 0 : ℚ) : ℝ) := by
  have h1 := shiftL_spec c M fq.poly 0 (Nat.zero_le _)
  have h2 := plogSumVec_approx c M fq.plogs Ls εs hL hne 0 (Nat.zero_le _)
  unfold fieldCoefsT
  rw [shiftLK_eq', plogSumVecI_eq, vecAdd_getD, vecAdd_getD, poleVecT_zero, add_zero]
  simp only [Nat.factorial_zero, Nat.cast_one, div_one] at h1 h2
  push_cast
  rw [h1]
  have e : polyTow fq.poly 0 (c : ℝ) + plogSumTower fq.plogs 0 (c : ℝ) -
      (polyTow fq.poly 0 (c : ℝ) + (((plogSumVec c M fq.plogs Ls).getD 0 0 : ℚ) : ℝ)) =
      plogSumTower fq.plogs 0 (c : ℝ) - (((plogSumVec c M fq.plogs Ls).getD 0 0 : ℚ) : ℝ) := by ring
  rw [e]
  exact h2

theorem errVecT0_ge (c : ℚ) (N : ℕ) (plogs : List (List ℚ × ℚ)) (εs : List ℚ)
    (Q Mi Wi K0 MiF WiF nN nF : ℕ) :
    (plogErrSum c N plogs εs).getD 0 0 ≤
      (errVecT c N plogs εs Q Mi Wi K0 MiF WiF nN nF).getD 0 0 := by
  rw [errVecT_getD _ _ _ _ _ _ _ _ _ _ _ _ _ (Nat.zero_le _)]
  have h1 : 0 ≤ (nN : ℚ) * crudeErr Q Mi Wi 0 := by unfold crudeErr; positivity
  have h2 : 0 ≤ (nF : ℚ) * (if 0 ≤ K0 then crudeErr Q MiF WiF 0 else tailErr Q MiF WiF 0) := by
    split_ifs
    · unfold crudeErr; positivity
    · unfold tailErr; positivity
  linarith

theorem anchorI_sound (fq : FieldQ) (Ls εs : List ℚ) (c : ℚ) (M Q Mi Wi K0 MiF WiF nN nF Pg : ℕ)
    (hPg : Pg ≤ 56) (hL : LogVals c fq.plogs Ls εs) (hne : ∀ t ∈ fq.plogs, c - t.2 ≠ 0)
    (S : ℤ) (E : ℕ) (hS : poleSumI Pg c fq.poles = some (S, E)) (A0 : ℚ)
    (hcheck : (fieldCoefsT fq Ls c M Q K0 MiF WiF).getD 0 0 +
        (errVecT c M fq.plogs εs Q Mi Wi K0 MiF WiF nN nF).getD 0 0 + ((S + E : ℤ) : ℚ) / 2 ^ Pg ≤ A0) :
    fieldTower fq (poleF fq.poles) 0 (c : ℝ) ≤ (A0 : ℝ) := by
  have h1 := coefs0_approx fq Ls εs c M Q K0 MiF WiF hL hne
  have h2 := errVecT0_ge c M fq.plogs εs Q Mi Wi K0 MiF WiF nN nF
  have h2' : (((plogErrSum c M fq.plogs εs).getD 0 0 : ℚ) : ℝ) ≤
      (((errVecT c M fq.plogs εs Q Mi Wi K0 MiF WiF nN nF).getD 0 0 : ℚ) : ℝ) := by exact_mod_cast h2
  have h3 := poleSumI_spec Pg hPg c fq.poles S E hS
  have hc : (((fieldCoefsT fq Ls c M Q K0 MiF WiF).getD 0 0 +
        (errVecT c M fq.plogs εs Q Mi Wi K0 MiF WiF nN nF).getD 0 0 + ((S + E : ℤ) : ℚ) / 2 ^ Pg : ℚ) : ℝ) ≤ (A0 : ℝ) := by
    exact_mod_cast hcheck
  push_cast at hc
  have e : fieldTower fq (poleF fq.poles) 0 (c : ℝ) =
      polyTow fq.poly 0 (c : ℝ) + plogSumTower fq.plogs 0 (c : ℝ) +
        (fq.poles.map (fun q => (q.rho * Complex.log (((c : ℝ) : ℂ) - q.pc)).re)).sum := rfl
  rw [e]
  rw [abs_le] at h1 h3
  have hP : (0 : ℝ) < 2 ^ Pg := by positivity
  have : ((S : ℝ) + E) / 2 ^ Pg = (S : ℝ) / 2 ^ Pg + (E : ℝ) / 2 ^ Pg := by ring
  linarith [h1.1, h1.2, h3.1, h3.2]

end IntegerAnchor

/-- One cell with all heavy literals precomputed: centre `cc`, logarithm values `Ls ± εs`.  The pole
part of the coefficients is evaluated in fixed point with grid `2^-Q` (`fieldCoefsT`): the poles
passing `fpPoleOK Q MiF WiF` (the far class) only to order `K0` (their dropped terms are
bounded by `tailErr`), the others (bounds `Mi`, `Wi`) to the full order. -/
def cellW (fq : FieldQ) (nLc Pg Q Mi Wi K0 MiF WiF : ℕ) (cc blo bhi lo hi : ℚ)
    (Ls εs : List ℚ) (A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ) : Bool :=
  decide (cc = (lo + hi) / 2) && decide (Pg ≤ 56) && logsCheck nLc cc fq.plogs Ls εs &&
  (match poleSumI Pg cc fq.poles with
   | some (S, E) => decide ((fieldCoefsT fq Ls cc (Bl.length + 2) Q K0 MiF WiF).getD 0 0 +
        (errVecT cc (Bl.length + 2) fq.plogs εs Q Mi Wi K0 MiF WiF
          (fq.poles.length - fq.poles.countP (isFar Q MiF WiF cc)) (fq.poles.countP (isFar Q MiF WiF cc))).getD 0 0 +
        ((S + E : ℤ) : ℚ) / 2 ^ Pg ≤ A0)
   | none => false) &&
  decide (blo ≤ lo) && decide (hi ≤ bhi) &&
  fq.poles.all (fun q => isFar Q MiF WiF cc q || fpPoleOK Q Mi Wi q cc) &&
  decide (2 ^ Q ≤ Mi + 4) && decide (2 ^ Q ≤ MiF + 4) &&
  coefTestR l1 u1 A2 Bl (fieldCoefsT fq Ls cc (Bl.length + 2) Q K0 MiF WiF)
    (errVecT cc (Bl.length + 2) fq.plogs εs Q Mi Wi K0 MiF WiF
      (fq.poles.length - fq.poles.countP (isFar Q MiF WiF cc)) (fq.poles.countP (isFar Q MiF WiF cc))) &&
  decide (tmUBQ A0 l1 u1 A2 ((hi - lo) / 2) Bl BM ≤ T)

theorem cellW_sound (fq : FieldQ) (nLc Pg Q Mi Wi K0 MiF WiF : ℕ) (cc blo bhi lo hi : ℚ)
    (Ls εs : List ℚ) (A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ)
    (hchk : cellW fq nLc Pg Q Mi Wi K0 MiF WiF cc blo bhi lo hi Ls εs A0 l1 u1 A2 Bl BM T = true)
    (hB : BlockFacts fq blo bhi (Bl.length + 3) BM) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), fieldTower fq (poleF fq.poles) 0 x ≤ (T : ℝ) := by
  unfold cellW at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcc, hPg⟩, hlc⟩, hanch⟩, hb1⟩, hb2⟩, hpok⟩, hMi⟩, hMiF⟩, htest⟩, hT⟩ := hchk
  subst hcc
  have hnear : ∀ q ∈ fq.poles, isFar Q MiF WiF ((lo + hi) / 2) q = false →
      fpPoleOK Q Mi Wi q ((lo + hi) / 2) = true := by
    intro q hq hf
    rw [List.all_eq_true] at hpok
    have := hpok q hq
    rw [hf, Bool.false_or] at this
    exact this
  obtain ⟨hl1, hu1, hA2, hL⟩ := coefTestR_spec _ _ _ _ _ _ htest
  set c : ℚ := (lo + hi) / 2 with hc
  set r : ℚ := (hi - lo) / 2 with hr
  have hLs := logsCheck_spec nLc c fq.plogs Ls εs hlc
  obtain ⟨S, E, hSE, hanch2⟩ : ∃ S E, poleSumI Pg c fq.poles = some (S, E) ∧
      (fieldCoefsT fq Ls c (Bl.length + 2) Q K0 MiF WiF).getD 0 0 +
        (errVecT c (Bl.length + 2) fq.plogs εs Q Mi Wi K0 MiF WiF
          (fq.poles.length - fq.poles.countP (isFar Q MiF WiF c)) (fq.poles.countP (isFar Q MiF WiF c))).getD 0 0 +
        ((S + E : ℤ) : ℚ) / 2 ^ Pg ≤ A0 := by
    revert hanch
    cases hh : poleSumI Pg c fq.poles with
    | none => simp
    | some p => intro h; exact ⟨p.1, p.2, rfl, by simpa using h⟩
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
        (((fieldCoefsT fq Ls c (Bl.length + 2) Q K0 MiF WiF).getD k 0 : ℚ) : ℝ)| ≤
      (((errVecT c (Bl.length + 2) fq.plogs εs Q Mi Wi K0 MiF WiF
        (fq.poles.length - fq.poles.countP (isFar Q MiF WiF c))
        (fq.poles.countP (isFar Q MiF WiF c))).getD k 0 : ℚ) : ℝ) := by
    intro k hk1 hk
    rw [errVecT_getD _ _ _ _ _ _ _ _ _ _ _ _ _ hk]
    exact fieldCoefsT_approx fq (poleF fq.poles) Ls εs c (Bl.length + 2) Q Mi Wi K0 MiF WiF hLs hnec
      hMi hMiF hnear k hk1 hk
  have h0 : fieldTower fq (poleF fq.poles) 0 (c : ℝ) ≤ (A0 : ℝ) :=
    anchorI_sound fq Ls εs c (Bl.length + 2) Q Mi Wi K0 MiF WiF _ _ Pg (by simpa using hPg) hLs hnec S E hSE A0 hanch2
  exact cellCore lo hi A0 l1 u1 A2 Bl BM T _ _ hT0 hspec hl1 hu1 hA2
    (absLeAllE_of_L Bl _ _ hL) hT h0 blo bhi hb1 hb2 hB.tail x hx


/-! ### The block check, split into independently checkable parts -/

/-- one logarithmic piece of the block data (shift with the integer Horner steps) -/
def plogItemOK (cb blo bhi : ℚ) (t : List ℚ × ℚ) (b : PlogBlk) : Bool :=
  decide (t.1.length ≤ b.Cb.length) && absLeL (shiftLK cb b.Cb.length t.1) b.Cb &&
  decide (0 < b.dm) && (decide (b.dm ≤ t.2 - bhi) || decide (b.dm ≤ blo - t.2))

def plogBlkOK2 (cb blo bhi : ℚ) : List (List ℚ × ℚ) → List PlogBlk → Bool
  | [], [] => true
  | t :: ts, b :: bs => plogItemOK cb blo bhi t b && plogBlkOK2 cb blo bhi ts bs
  | _, _ => false

theorem plogBlkOK2_nil (cb blo bhi : ℚ) : plogBlkOK2 cb blo bhi [] [] = true := rfl

theorem plogBlkOK2_cons {cb blo bhi : ℚ} {t : List ℚ × ℚ} {ts : List (List ℚ × ℚ)} {b : PlogBlk}
    {bs : List PlogBlk} (h : plogItemOK cb blo bhi t b = true)
    (hr : plogBlkOK2 cb blo bhi ts bs = true) : plogBlkOK2 cb blo bhi (t :: ts) (b :: bs) = true := by
  simp only [plogBlkOK2, h, hr, Bool.and_self]

theorem plogBlkOK_of_2 (cb blo bhi : ℚ) : ∀ (plogs : List (List ℚ × ℚ)) (pb : List PlogBlk),
    plogBlkOK2 cb blo bhi plogs pb = true → plogBlkOK cb blo bhi plogs pb = true := by
  intro plogs
  induction plogs with
  | nil => intro pb h; cases pb <;> simp_all [plogBlkOK2, plogBlkOK]
  | cons t ts ih =>
    intro pb h
    cases pb with
    | nil => simp [plogBlkOK2] at h
    | cons b bs =>
      simp only [plogBlkOK2, plogItemOK, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      have e := absLeAll_eq b.Cb (shiftL cb b.Cb.length t.1) 0
      simp only [List.drop_zero] at e
      simp only [plogBlkOK, Bool.and_eq_true]
      refine ⟨⟨⟨⟨h1, ?_⟩, h3⟩, h4⟩, ih bs h5⟩
      rw [e, ← shiftLK_eq']
      exact h2

/-- the part of the block check without Taylor shifts -/
def blockRestOK (fq : FieldQ) (cb blo bhi : ℚ) (M : ℕ) (CbP : List ℚ) (pb : List PlogBlk)
    (ks : List ℕ) (BM : ℚ) : Bool :=
  decide (cb = (blo + bhi) / 2) && decide (blo ≤ bhi) && decide (1 ≤ M) &&
  decide (fq.poly.length ≤ CbP.length) &&
  fq.poles.all (fun q => decide (0 < poleDist q blo bhi)) &&
  decide (blockTailQ fq blo bhi M CbP pb ≤ BM) &&
  lbOK blo bhi fq.plogs pb ks &&
  fq.poles.all (fun q => decide (q.pi ≠ 0 ∨ q.ri = 0))

def blockOK4 (fq : FieldQ) (cb blo bhi : ℚ) (M : ℕ) (CbP : List ℚ) (pb : List PlogBlk)
    (ks : List ℕ) (BM : ℚ) : Bool :=
  blockRestOK fq cb blo bhi M CbP pb ks BM &&
  absLeL (shiftLK cb CbP.length fq.poly) CbP && plogBlkOK2 cb blo bhi fq.plogs pb

theorem blockOK4_of_parts {fq : FieldQ} {cb blo bhi : ℚ} {M : ℕ} {CbP : List ℚ} {pb : List PlogBlk}
    {ks : List ℕ} {BM : ℚ} (h1 : blockRestOK fq cb blo bhi M CbP pb ks BM = true)
    (h2 : absLeL (shiftLK cb CbP.length fq.poly) CbP = true)
    (h3 : plogBlkOK2 cb blo bhi fq.plogs pb = true) : blockOK4 fq cb blo bhi M CbP pb ks BM = true := by
  simp only [blockOK4, h1, h2, h3, Bool.and_self]

theorem blockFacts_of_ok4 (fq : FieldQ) (cb blo bhi : ℚ) (M : ℕ) (CbP : List ℚ)
    (pb : List PlogBlk) (ks : List ℕ) (BM : ℚ)
    (h : blockOK4 fq cb blo bhi M CbP pb ks BM = true) : BlockFacts fq blo bhi M BM := by
  apply blockFacts_of_ok3 fq cb blo bhi M CbP pb ks BM
  simp only [blockOK4, blockRestOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hcb, hbb⟩, hM⟩, hlen⟩, hpd⟩, hBM⟩, hlb⟩, hpoles⟩, hpoly⟩, hpl⟩ := h
  have hpl' := plogBlkOK_of_2 cb blo bhi _ _ hpl
  have e := absLeAll_eq CbP (shiftL cb CbP.length fq.poly) 0
  simp only [List.drop_zero] at e
  have hpoly' : absLeAll (shiftL cb CbP.length fq.poly) 0 CbP = true := by
    rw [e, ← shiftLK_eq']; exact hpoly
  have e2 : absLeL (shiftL cb CbP.length fq.poly) CbP = true := by rw [← shiftLK_eq']; exact hpoly
  simp only [blockOK3, blockTailCheck3, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨hcb, ⟨⟨⟨⟨⟨⟨hbb, hM⟩, hlen⟩, e2⟩, hpl'⟩, hpd⟩, hBM⟩⟩, hlb⟩, hpoles⟩, hpd⟩

end CatalanMeasure.GenD.Signed.Data.Cells

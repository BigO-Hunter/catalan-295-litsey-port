module

public import Submission.CatalanMeasure.GenD.Signed.Count.ChartSource
public import Submission.CatalanMeasure.GenD.Signed.Count.WinCertGlue

@[expose] public section
set_option Elab.async false

/-!
# Count layer: assembling a content ledger

A ledger is a list of rational rows `(a, b, c0, c1)`.  Each row must lie inside a checked count
piece or inside a row of a list of retained windows, each certified against some family.  All other
requirements of `WinCertGlue.hcontent_terminal` become one Boolean on the rows and one rational
inequality for the area.

* `exists_cert`: finite chart checks give one `NullityLB` certifying every count row, through
  `wincert_count`.
* `content_of_ledger`: the conclusion of `hcontent_terminal`, with `gain ≥ 220607/10000`.
-/

namespace CatalanMeasure.GenD.Signed.Count.ContentAssembly
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
  CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
  CatalanMeasure.GenD.Uniform.Bank540.Ledger4
  CatalanMeasure.GenD.Signed.Count.NullityConstructor
  CatalanMeasure.GenD.Signed.Count.PrefixSource CatalanMeasure.GenD.Signed.Count.ChartSource
  CatalanMeasure.GenD.Signed.Count.WinCertGlue D58

/-- A window `(a, b]` with the affine nullity profile `c0 + c1 x`. -/
structure Row where
  a : ℚ
  b : ℚ
  c0 : ℚ
  c1 : ℚ

/-- The area of the saving profile of a row. -/
def Row.area (r : Row) : ℚ := r.c0 * (r.b - r.a) + r.c1 * ((r.b ^ 2 - r.a ^ 2) / 2)

/-- `r` is a sub-window of `o` with the same profile. -/
def Row.within (o r : Row) : Bool :=
  decide (o.a ≤ r.a) && decide (r.b ≤ o.b) && decide (o.c0 = r.c0) && decide (o.c1 = r.c1)

/-- The numeric side conditions of one row. -/
def Row.good (r : Row) : Bool := decide (2 ≤ r.a) && decide (r.a < r.b) && decide (r.b ≤ 78)

/-- Consecutive rows are ordered. -/
def chainOK : List Row → Bool
  | a :: b :: r => decide (a.b ≤ b.a) && chainOK (b :: r)
  | _ => true

/-- The row of a count piece. -/
def cntRow (c : Spec × Cnt) : Row :=
  ⟨(c.1.W.aN : ℚ) / c.1.W.aD, (c.1.W.bN : ℚ) / c.1.W.bD, (c.2.pu : ℚ) / c.2.pd,
    (c.2.pv : ℚ) / c.2.pd⟩

/-- All finite conditions of a ledger: `cnt` are the count rows, `old` the retained rows. -/
def ledgerOK (cnt old rows : List Row) : Bool :=
  cnt.all (fun r => decide (0 < r.b) && decide (r.b ≤ 59 / 2)) && rows.all Row.good && chainOK rows &&
    rows.all fun r => cnt.any (fun o => o.within r) || old.any (fun o => o.within r)

noncomputable section

/-- The window of a row. -/
def Row.win (r : Row) : KapWindow := cw r.a r.b r.c0 r.c1

theorem Row.within_cert {lb : NullityLB design} {o r : Row} (h : o.within r = true)
    (hc : WinCert lb o.win) : WinCert lb r.win := by
  simp only [Row.within, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have := WinCert.shrink (a' := r.a) (b' := r.b) hc (by exact_mod_cast h1) (by exact_mod_cast h2)
  simpa only [Row.win, h3, h4] using this

theorem sum_area (rows : List Row) :
    ((rows.map Row.win).map (KapWindow.area 58)).sum = (((rows.map Row.area).sum : ℚ) : ℝ) := by
  induction rows with
  | nil => simp
  | cons r t ih =>
    simp only [List.map_cons, List.sum_cons, ih, Row.win, cw_area, Row.area]
    push_cast
    ring

theorem chain_pairwise (rows : List Row) (hab : ∀ r ∈ rows, r.a ≤ r.b)
    (hc : chainOK rows = true) : (rows.map Row.win).Pairwise (fun s t => s.b ≤ t.a) := by
  have key : ∀ (s : Row) (t : List Row), (∀ r ∈ s :: t, r.a ≤ r.b) → chainOK (s :: t) = true →
      ∀ y ∈ t, s.b ≤ y.a := by
    intro s t
    induction t generalizing s with
    | nil => intro _ _ y hy; simp at hy
    | cons u t ih =>
      intro hab hc y hy
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hc.1
      · have h1 := ih u (fun w hw => hab w (List.mem_cons_of_mem _ hw)) hc.2 y hy
        have h2 := hab u (by simp)
        linarith [hc.1]
  induction rows with
  | nil => simp
  | cons s t ih =>
    simp only [List.map_cons, List.pairwise_cons, List.mem_map]
    refine ⟨?_, ih (fun w hw => hab w (List.mem_cons_of_mem _ hw)) ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      have := key s t hab hc y hy
      simp only [Row.win, cw]
      exact_mod_cast this
    · cases t with
      | nil => rfl
      | cons u t =>
        simp only [chainOK, Bool.and_eq_true] at hc
        exact hc.2

/-- **Finite chart checks certify every count row against one `NullityLB`.** -/
theorem exists_cert (cs : List (Spec × Cnt))
    (h : ∀ c ∈ cs, c.1.P = design ∧ c.1.Check = true ∧ c.2.ok c.1 = true)
    (hb : ∀ c ∈ cs, 0 < (cntRow c).b ∧ (cntRow c).b ≤ 59 / 2) :
    ∃ lbC : NullityLB design, ∀ c ∈ cs, WinCert lbC (cntRow c).win := by
  obtain ⟨N0, h1, -⟩ := exists_common_N0 design (cs.map fun c => c.2.piece c.1)
    (fun w hw => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
      exact piece_a_pos _ (h c hc).2.1)
    (fun w hw => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
      obtain ⟨e, h2, h3⟩ := h c hc
      exact ⟨c.1.W.N1, e ▸ pieceBound_of_check h2 h3⟩)
  refine ⟨countLB design _ N0 h1, fun c hc => ?_⟩
  obtain ⟨-, hS, hC⟩ := h c hc
  have hpa := piece_a_pos c.2 hS
  obtain ⟨hb0, hbc⟩ := hb c hc
  simp only [Cnt.ok, Bool.and_eq_true, decide_eq_true_eq] at hC
  obtain ⟨⟨⟨⟨⟨-, -⟩, hpd⟩, -⟩, -⟩, hmar⟩ := hC
  simp only [Win.aNN, Bool.and_eq_true, decide_eq_true_eq] at hmar
  obtain ⟨⟨⟨haD, hbD⟩, -⟩, -⟩ := hmar
  have haDr : (0 : ℝ) < c.1.W.aD := by exact_mod_cast haD
  have hbDq : (0 : ℚ) < c.1.W.bD := by exact_mod_cast hbD
  have haN : 0 < c.1.W.aN := by
    have h2 : (0 : ℝ) < c.1.W.aN := by
      have := mul_pos hpa haDr
      simpa only [Cnt.piece, div_mul_cancel₀ _ haDr.ne'] using this
    exact_mod_cast h2
  have hbb : 2 * c.1.W.bN ≤ 59 * c.1.W.bD := by
    simp only [cntRow] at hbc
    rw [div_le_iff₀ hbDq] at hbc
    have : (2 : ℚ) * c.1.W.bN ≤ 59 * c.1.W.bD := by linarith
    exact_mod_cast this
  have hbN : 0 < c.1.W.bN := by
    simp only [cntRow] at hb0
    have : (0 : ℚ) < c.1.W.bN := by
      have := mul_pos hb0 hbDq
      simpa only [div_mul_cancel₀ _ hbDq.ne'] using this
    exact_mod_cast this
  have e : ∀ z : ℤ, 0 ≤ z → ((z.toNat : ℕ) : ℝ) = (z : ℝ) := fun z hz => by
    exact_mod_cast Int.toNat_of_nonneg hz
  have hpdr : (0 : ℝ) < c.2.pd := by exact_mod_cast hpd
  have hbDr : (0 : ℝ) < c.1.W.bD := by exact_mod_cast hbD
  have hw := wincert_count (cs.map fun c => c.2.piece c.1) N0 h1 (c.2.piece c.1).a
    (c.2.piece c.1).b (c.2.piece c.1).c0 (c.2.piece c.1).c1 (List.mem_map.mpr ⟨c, hc, rfl⟩)
    (na := c.1.W.aN.toNat) (da := c.1.W.aD.toNat) (nb := c.1.W.bN.toNat) (db := c.1.W.bD.toNat)
    (A := c.2.pu) (B := c.2.pv) (d := c.2.pd.toNat) (by omega) (by omega) (by omega)
    (by
      rw [e _ haD.le, e _ haN.le]
      simp only [Cnt.piece]
      field_simp)
    (by
      rw [e _ hbD.le, e _ hbN.le]
      simp only [Cnt.piece]
      field_simp)
    (by
      rw [e _ hpd.le]
      simp only [Cnt.piece]
      field_simp)
    (by
      rw [e _ hpd.le]
      simp only [Cnt.piece]
      field_simp)
    (by omega)
  have e2 : (cntRow c).win = cw (c.2.piece c.1).a (c.2.piece c.1).b (c.2.piece c.1).c0
      (c.2.piece c.1).c1 := by
    simp [Row.win, cntRow, Cnt.piece]
  rw [e2]
  exact hw

/-- **Content from a ledger.**  The conclusion of `hcontent_terminal` for the family list
`lbC :: fams0`, with `gain ≥ 220607/10000`: `cs` are checked count pieces, `old` are windows
certified against `fams0`, and `rows` is a ledger drawn from both. -/
theorem content_of_ledger (cs : List (Spec × Cnt))
    (h : ∀ c ∈ cs, c.1.P = design ∧ c.1.Check = true ∧ c.2.ok c.1 = true)
    (fams0 : List (NullityLB design)) (old rows : List Row)
    (hold : ∀ o ∈ old, ∃ lb ∈ fams0, WinCert lb o.win)
    (hok : ledgerOK (cs.map cntRow) old rows = true)
    (hgain : (220607 / 10000 : ℚ) ≤ (rows.map Row.area).sum) :
    ∃ (lbC : NullityLB design) (gain : ℝ), (220607 / 10000 : ℝ) ≤ gain ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        Real.log ((canonicalNormalizer Signed.dc58.toParameters Signed.dc58.admissible
          (famLB (lbC :: fams0)) 79 Signed.RouteI.dc58_normalizer_cut).D N : ℝ) ≤
          (gDg gain + ε) * (N : ℝ) ^ 2 := by
  simp only [ledgerOK, Bool.and_eq_true, List.all_eq_true, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true] at hok
  obtain ⟨⟨⟨hb, hgood⟩, hchain⟩, hsub⟩ := hok
  obtain ⟨lbC, hC⟩ := exists_cert cs h hb
  have hg : ∀ r ∈ rows, 2 ≤ r.a ∧ r.a < r.b ∧ r.b ≤ 78 := fun r hr => by
    have := hgood r hr
    simp only [Row.good, Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  refine ⟨lbC, (((rows.map Row.area).sum : ℚ) : ℝ), ?_, ?_⟩
  · have h2 := (Rat.cast_le (K := ℝ)).mpr hgain
    have e : (((220607 / 10000 : ℚ)) : ℝ) = 220607 / 10000 := by norm_num
    rwa [e] at h2
  refine hcontent_terminal lbC (rows.map Row.win) _ (sum_area rows) ?_
    (chain_pairwise rows (fun r hr => (hg r hr).2.1.le) hchain) ?_ fams0 ?_
  · intro w hw
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
    obtain ⟨h1, h2, h3⟩ := hg r hr
    simp only [Row.win, cw]
    refine ⟨?_, ?_, ?_⟩
    · have : (0 : ℚ) < r.a := by linarith
      exact_mod_cast this
    · exact_mod_cast h2
    · exact_mod_cast h3
  · intro w hw
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
    right
    simp only [Row.win, cw]
    exact_mod_cast (hg r hr).1
  · intro w hw
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
    rcases hsub r hr with ⟨o, ho, hin⟩ | ⟨o, ho, hin⟩
    · left
      obtain ⟨c, hc, rfl⟩ := ho
      exact Row.within_cert hin (hC c hc)
    · right
      obtain ⟨lb, hl, hcert⟩ := hold o ho
      exact ⟨lb, hl, Row.within_cert hin hcert⟩

end
end CatalanMeasure.GenD.Signed.Count.ContentAssembly

#print axioms CatalanMeasure.GenD.Signed.Count.ContentAssembly.exists_cert
#print axioms CatalanMeasure.GenD.Signed.Count.ContentAssembly.content_of_ledger

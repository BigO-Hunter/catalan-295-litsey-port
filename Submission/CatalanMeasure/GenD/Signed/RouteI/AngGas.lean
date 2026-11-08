module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.GasCert
public import Submission.CatalanMeasure.GenD.Signed.RouteI.CapSourceData
public import Submission.CatalanMeasure.GenD.Cert.WLog
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Perm.Lattice

@[expose] public section
set_option Elab.async false

/-!
# Route I `AngGas`: the gas side of `AngRadiusCert`, generic in species, radius, grid, degree, precision

Generalises the gas part of the pilot `AngPilot`. No radius constants, no sign-specific literals.

* (G1) `qcOf`, `cutsZ`, `binsQ`, `cutsOK`, `partitioned_species`.
* (G2) `momPass`/`MomSpec` (radius free, once per species), `alpha1OK`/`alpha2OK` (per radius).
* (G3) `rec_ok1`, `rec_ok2`, `rad_enc`.
* (G4) `constSum`, `constSum_spec`.
* (G5) `glFast_eq`, `glFastNeg_eq`.
* (G6) `gas_cert_pos`, `gas_cert_neg`, `gas_final_pos`, `gas_final_neg`.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.AngGas
open CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MomentSource
open CatalanMeasure.GenD.Signed.RouteI.MomentInputs

noncomputable section

/-- A rational uniform cell. -/
structure QC where
  lo : ℚ
  hi : ℚ
  w : ℚ
deriving DecidableEq

@[reducible] def QC.ok (c : QC) : Prop := c.lo < c.hi ∧ 0 ≤ c.w

def QC.toY (c : QC) : YCell :=
  if h : c.lo < c.hi ∧ 0 ≤ c.w then
    ⟨(c.lo : ℝ), (c.hi : ℝ), (c.w : ℝ), by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  else ⟨0, 1, 0, zero_lt_one, le_rfl⟩

theorem QC.toY_lo {c : QC} (h : c.ok) : c.toY.lo = (c.lo : ℝ) := by
  unfold QC.toY; simp only [dif_pos h]
theorem QC.toY_hi {c : QC} (h : c.ok) : c.toY.hi = (c.hi : ℝ) := by
  unfold QC.toY; simp only [dif_pos h]
theorem QC.toY_w {c : QC} (h : c.ok) : c.toY.w = (c.w : ℝ) := by
  unfold QC.toY; simp only [dif_pos h]

def QC.left (c : QC) (m : ℚ) : QC := ⟨c.lo, m, c.w * (m - c.lo) / (c.hi - c.lo)⟩
def QC.right (c : QC) (m : ℚ) : QC := ⟨m, c.hi, c.w * (c.hi - m) / (c.hi - c.lo)⟩

def cutQ (c : QC) : List ℚ → List QC
  | [] => [c]
  | m :: ms => c.left m :: cutQ (c.right m) ms

def cutOK : QC → List ℚ → Bool
  | c, [] => decide (c.lo < c.hi ∧ 0 ≤ c.w)
  | c, m :: ms => decide (c.lo < m ∧ m < c.hi ∧ 0 ≤ c.w) && cutOK (c.right m) ms

theorem left_ok {c : QC} {m : ℚ} (h1 : c.lo < m) (h2 : m < c.hi) (hw : 0 ≤ c.w) : (c.left m).ok := by
  refine ⟨h1, ?_⟩
  show 0 ≤ c.w * (m - c.lo) / (c.hi - c.lo)
  exact div_nonneg (mul_nonneg hw (by linarith)) (by linarith)

theorem right_ok {c : QC} {m : ℚ} (h1 : c.lo < m) (h2 : m < c.hi) (hw : 0 ≤ c.w) : (c.right m).ok := by
  refine ⟨h2, ?_⟩
  show 0 ≤ c.w * (c.hi - m) / (c.hi - c.lo)
  exact div_nonneg (mul_nonneg hw (by linarith)) (by linarith)

theorem YCell.ext_of (a b : YCell) (h1 : a.lo = b.lo) (h2 : a.hi = b.hi) (h3 : a.w = b.w) : a = b := by
  cases a; cases b; simp_all

theorem toY_left {c : QC} {m : ℚ} (h1 : c.lo < m) (h2 : m < c.hi) (hw : 0 ≤ c.w)
    (g1 g2) : (c.left m).toY = c.toY.left (m : ℝ) g1 g2 := by
  have hc : c.ok := ⟨by linarith, hw⟩
  have hl := left_ok h1 h2 hw
  apply YCell.ext_of
  · rw [QC.toY_lo hl]; simp [QC.left, YCell.left, QC.toY_lo hc]
  · rw [QC.toY_hi hl]; simp [QC.left, YCell.left]
  · rw [QC.toY_w hl]; simp only [YCell.left, QC.left, QC.toY_lo hc, QC.toY_hi hc, QC.toY_w hc]; push_cast; rfl

theorem toY_right {c : QC} {m : ℚ} (h1 : c.lo < m) (h2 : m < c.hi) (hw : 0 ≤ c.w)
    (g1 g2) : (c.right m).toY = c.toY.right (m : ℝ) g1 g2 := by
  have hc : c.ok := ⟨by linarith, hw⟩
  have hl := right_ok h1 h2 hw
  apply YCell.ext_of
  · rw [QC.toY_lo hl]; simp [QC.right, YCell.right]
  · rw [QC.toY_hi hl]; simp [QC.right, YCell.right, QC.toY_hi hc]
  · rw [QC.toY_w hl]; simp only [YCell.right, QC.right, QC.toY_lo hc, QC.toY_hi hc, QC.toY_w hc]; push_cast; rfl

theorem cutQ_ok : ∀ (ms : List ℚ) (c : QC), cutOK c ms = true → ∀ p ∈ cutQ c ms, p.ok := by
  intro ms
  induction ms with
  | nil => intro c h p hp; simp [cutOK] at h; simp [cutQ] at hp; subst hp; exact h
  | cons m ms ih =>
    intro c h p hp
    simp only [cutOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2, hw⟩, h3⟩ := h
    simp only [cutQ, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact left_ok h1 h2 hw
    · exact ih _ h3 p hp

theorem cutQ_sound : ∀ (ms : List ℚ) (c : QC), cutOK c ms = true →
    CellCut c.toY ((cutQ c ms).map QC.toY) := by
  intro ms
  induction ms with
  | nil =>
    intro c h
    simp only [cutQ, List.map_cons, List.map_nil]
    exact CellCut.refl _
  | cons m ms ih =>
    intro c h
    simp only [cutOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2, hw⟩, h3⟩ := h
    have hc : c.ok := ⟨by linarith, hw⟩
    have g1 : c.toY.lo < (m : ℝ) := by rw [QC.toY_lo hc]; exact_mod_cast h1
    have g2 : (m : ℝ) < c.toY.hi := by rw [QC.toY_hi hc]; exact_mod_cast h2
    have ih' := ih (c.right m) h3
    rw [toY_right h1 h2 hw g1 g2] at ih'
    have := CellCut.split c.toY (m : ℝ) g1 g2 (L1 := [(c.left m).toY]) (L2 := (cutQ (c.right m) ms).map QC.toY)
      (by rw [toY_left h1 h2 hw g1 g2]; exact CellCut.refl _) ih'
    simpa [cutQ] using this




theorem group_perm {α : Type*} (idx : α → ℕ) (l : List α) :
    ∀ K : ℕ, ((List.range K).map fun j => l.filter fun a => idx a == j).flatten.Perm
      (l.filter fun a => decide (idx a < K)) := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.flatten_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    have h1 : (l.filter fun a => decide (idx a < K + 1)).Perm
        ((l.filter fun a => decide (idx a < K)) ++ (l.filter fun a => idx a == K)) := by
      have := List.filter_append_perm (fun a => decide (idx a < K)) (l.filter fun a => decide (idx a < K + 1))
      have e1 : (l.filter fun a => decide (idx a < K + 1)).filter (fun a => decide (idx a < K)) =
          l.filter fun a => decide (idx a < K) := by
        rw [List.filter_filter]; apply List.filter_congr; intro a _
        by_cases h : idx a < K
        · simp [h, show idx a < K + 1 by omega]
        · simp [h]
      have e2 : (l.filter fun a => decide (idx a < K + 1)).filter (fun a => !decide (idx a < K)) =
          l.filter fun a => idx a == K := by
        rw [List.filter_filter]; apply List.filter_congr; intro a _
        by_cases h : idx a < K
        · simp [h]; omega
        · by_cases h2 : idx a = K
          · simp [h, h2]
          · have : ¬ idx a < K + 1 := by omega
            simp [h, h2, this]
      rw [e1, e2] at this
      exact this.symm
    exact (ih.append (List.Perm.refl _)).trans h1.symm

theorem flatten_filter_ne_nil {α : Type*} (L : List (List α)) :
    (L.filter fun b => decide (b ≠ [])).flatten = L.flatten := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    by_cases h : b = []
    · subst h; rw [List.filter_cons_of_neg (by simp), ih]; simp
    · rw [List.filter_cons_of_pos (by simpa using h), List.flatten_cons, ih, List.flatten_cons]


/-! ### Generic cells, cuts and bins -/
open CapSourceData

/-- the rational cell of the integer triple `(a, b, p)` at total weight `T`. -/
def qcOf (T : ℤ) (t : Tr) : QC := ⟨(t.1 : ℚ) / 10 ^ 12, (t.2.1 : ℚ) / 10 ^ 12, (t.2.2 : ℚ) / (T : ℚ)⟩

theorem qcOf_ok {T : ℤ} (hT0 : 0 < T) {t : Tr} (hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2) : (qcOf T t).ok := by
  have hT : (0 : ℚ) < T := by exact_mod_cast hT0
  refine ⟨?_, ?_⟩
  · show (t.1 : ℚ) / 10 ^ 12 < (t.2.1 : ℚ) / 10 ^ 12
    have : (t.1 : ℚ) < t.2.1 := by exact_mod_cast hv.1
    linarith
  · show 0 ≤ (t.2.2 : ℚ) / (T : ℚ)
    have : (0 : ℚ) ≤ t.2.2 := by exact_mod_cast hv.2
    exact div_nonneg this hT.le

theorem qcOf_toY {T : ℤ} (hT0 : 0 < T) {t : Tr} (hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2) :
    (qcOf T t).toY = mkCell 1 T t := by
  have hok := qcOf_ok hT0 hv
  have h := mkCell_eq (m := 1) (T := T) hv hT0.le zero_le_one
  apply YCell.ext_of
  · rw [QC.toY_lo hok, h.1]; simp [qcOf]
  · rw [QC.toY_hi hok, h.2.1]; simp [qcOf]
  · rw [QC.toY_w hok, h.2.2]; simp [qcOf]

/-- reflection of an integer triple (`[a, b]` to `[-b, -a]`). -/
def reflT (t : Tr) : Tr := (-t.2.1, -t.1, t.2.2)

theorem reflT_ok {t : Tr} (hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2) :
    (reflT t).1 < (reflT t).2.1 ∧ 0 ≤ (reflT t).2.2 :=
  ⟨by simpa [reflT] using hv.1, hv.2⟩

theorem qcOf_reflT_toY {T : ℤ} (hT0 : 0 < T) {t : Tr} (hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2) :
    (qcOf T (reflT t)).toY = (mkCell 1 T t).reflect := by
  have hok := qcOf_ok hT0 (reflT_ok hv)
  have h := mkCell_eq (m := 1) (T := T) hv hT0.le zero_le_one
  apply YCell.ext_of
  · rw [QC.toY_lo hok]; simp only [YCell.reflect, h.2.1]; simp [qcOf, reflT]; ring
  · rw [QC.toY_hi hok]; simp only [YCell.reflect, h.1]; simp [qcOf, reflT]; ring
  · rw [QC.toY_w hok]; simp only [YCell.reflect, h.2.2]; simp [qcOf, reflT]

/-- the rational cell list of a species. -/
def gasQ (T : ℤ) (L : List Tr) : List QC := L.map (qcOf T)

/-- cut points `Y_j = (j^2 + K^2) / (K j)`, ascending (`j = K-1, ..., 1`), as (numerator, denominator). -/
def cutsZ (K : ℕ) : List (ℤ × ℤ) :=
  (List.range (K - 1)).reverse.map fun k =>
    (((k + 1 : ℕ) : ℤ) * ((k + 1 : ℕ) : ℤ) + (K : ℤ) * (K : ℤ), (K : ℤ) * ((k + 1 : ℕ) : ℤ))

/-- The cut points strictly inside each cell (cells ascending, so each cut is visited once). -/
def cutLists : List Tr → List (ℤ × ℤ) → List (List ℚ)
  | [], _ => []
  | t :: ts, cs =>
    let cs1 := cs.dropWhile fun x => decide (x.1 * 10 ^ 12 ≤ t.1 * x.2)
    ((cs1.takeWhile fun x => decide (x.1 * 10 ^ 12 < t.2.1 * x.2)).map fun x => Rat.divInt x.1 x.2) ::
      cutLists ts cs1

theorem cutLists_length : ∀ (ts : List Tr) (cs : List (ℤ × ℤ)), (cutLists ts cs).length = ts.length
  | [], _ => rfl
  | t :: ts, cs => by simp [cutLists, cutLists_length ts]

def cellCuts (K : ℕ) (L : List Tr) : List (Tr × List ℚ) := L.zip (cutLists L (cutsZ K))

def allPieces (K : ℕ) (T : ℤ) (L : List Tr) : List (List QC) :=
  (cellCuts K L).map fun x => cutQ (qcOf T x.1) x.2

/-- bin index: the number of cut points `<= lo`. -/
def binOf (K : ℕ) (p : QC) : ℕ :=
  ((cutsZ K).takeWhile fun x => decide (x.1 * p.lo.den ≤ p.lo.num * x.2)).length

def tagged (K : ℕ) (T : ℤ) (L : List Tr) : List (ℕ × QC) :=
  (allPieces K T L).flatten.map fun p => (binOf K p, p)

/-- the nonempty bins of the grid `K`. -/
def binsQ (K : ℕ) (T : ℤ) (L : List Tr) : List (List QC) :=
  ((List.range K).map fun j => ((tagged K T L).filter fun a => a.1 == j).map Prod.snd).filter
    fun b => decide (b ≠ [])

/-- the data check of the cuts (decided by the instance). -/
def cutsOK (K : ℕ) (T : ℤ) (L : List Tr) : Bool :=
  (cellCuts K L).all fun x => cutOK (qcOf T x.1) x.2

theorem cutsZ_length (K : ℕ) : (cutsZ K).length = K - 1 := by simp [cutsZ]

theorem cellCuts_fst (K : ℕ) (L : List Tr) : (cellCuts K L).map Prod.fst = L := by
  unfold cellCuts
  apply List.map_fst_zip
  rw [cutLists_length]

theorem forall2_cut (T : ℤ) (L : List (Tr × List ℚ)) (h : ∀ x ∈ L, cutOK (qcOf T x.1) x.2 = true) :
    List.Forall₂ CellCut ((L.map fun x => qcOf T x.1).map QC.toY)
      ((L.map fun x => cutQ (qcOf T x.1) x.2).map (List.map QC.toY)) := by
  induction L with
  | nil => exact List.Forall₂.nil
  | cons x L ih =>
    exact List.Forall₂.cons (cutQ_sound _ _ (h x (by simp))) (ih fun d hd => h d (by simp [hd]))

theorem takeWhile_length_le' {α : Type*} (p : α → Bool) : ∀ l : List α, (l.takeWhile p).length ≤ l.length
  | [] => by simp
  | a :: l => by
    have ih := takeWhile_length_le' p l
    simp only [List.takeWhile_cons]
    split <;> simp <;> omega

theorem binOf_lt {K : ℕ} (hK : 0 < K) (p : QC) : binOf K p < K := by
  have := takeWhile_length_le' (fun x : ℤ × ℤ => decide (x.1 * p.lo.den ≤ p.lo.num * x.2)) (cutsZ K)
  rw [cutsZ_length] at this
  unfold binOf; omega

/-- **(G1), generic form**: cutting the cells of `L` and regrouping is a partition. -/
theorem partitioned_cells {K : ℕ} (hK : 0 < K) (T : ℤ) (L : List Tr) (hc : cutsOK K T L = true) :
    Partitioned (L.map fun t => (qcOf T t).toY) ((binsQ K T L).map (List.map QC.toY)) := by
  refine ⟨(allPieces K T L).map (List.map QC.toY), ?_, ?_⟩
  · have h0 : (L.map fun t => (qcOf T t).toY) = (((cellCuts K L).map fun x => qcOf T x.1).map QC.toY) := by
      conv_lhs => rw [← cellCuts_fst K L]
      simp only [List.map_map]; rfl
    rw [h0]
    apply forall2_cut
    intro x hx
    exact List.all_eq_true.1 hc x hx
  · rw [← List.map_flatten, ← List.map_flatten]
    apply List.Perm.map
    have h1 : (binsQ K T L).flatten = (((List.range K).map fun j =>
        ((tagged K T L).filter fun a => a.1 == j).map Prod.snd)).flatten :=
      flatten_filter_ne_nil _
    rw [h1]
    have h2 : ((List.range K).map fun j => ((tagged K T L).filter fun a => a.1 == j).map Prod.snd).flatten =
        (((List.range K).map fun j => (tagged K T L).filter fun a => a.1 == j).flatten).map Prod.snd := by
      rw [List.map_flatten, List.map_map]; rfl
    rw [h2]
    have h3 := group_perm (fun a : ℕ × QC => a.1) (tagged K T L) K
    have h4 : ((tagged K T L).filter fun a => decide (a.1 < K)) = tagged K T L :=
      List.filter_eq_self.2 (fun a ha => by
        obtain ⟨p, _, rfl⟩ := List.mem_map.1 ha
        simpa using binOf_lt hK p)
    rw [h4] at h3
    have h5 : (tagged K T L).map Prod.snd = (allPieces K T L).flatten := by
      simp [tagged, List.map_map, Function.comp_def]
    rw [← h5]
    exact (h3.map Prod.snd).symm

theorem Partitioned.of_perm {g g' : List YCell} {bins : List (List YCell)} (h : g.Perm g')
    (hp : Partitioned g' bins) : Partitioned g bins := by
  obtain ⟨pc, hF, hperm⟩ := hp
  obtain ⟨pc', hF', hq⟩ := List.perm_comp_forall₂ h hF
  exact ⟨pc', hF', (hq.flatten).trans hperm⟩

/-- species cells in the POSITIVE coordinate, ascending (the source's negative cells are ascending,
so the reflected list is reversed). -/
def gasT : Sign → List Tr
  | Sign.pos => gasPosT
  | Sign.neg => (gasNegT.map reflT).reverse

/-- the species gas in the positive coordinate. -/
def gasR : Sign → List YCell
  | Sign.pos => capSource.gas Sign.pos
  | Sign.neg => reflectL (capSource.gas Sign.neg)

theorem gasR_perm {T : ℤ} (hT : sumP row0 = T) (σ : Sign) :
    (gasR σ).Perm ((gasT σ).map fun t => (qcOf T t).toY) := by
  subst hT
  cases σ with
  | pos =>
    show (gasPosT.map (mkCell 1 (sumP row0))).Perm _
    apply List.Perm.of_eq
    apply List.map_congr_left
    intro t ht
    exact (qcOf_toY row0_tot (row0_ok t (List.mem_of_mem_filter ht))).symm
  | neg =>
    show ((gasNegT.map (mkCell 1 (sumP row0))).map YCell.reflect).Perm
      ((gasNegT.map reflT).reverse.map fun t => (qcOf (sumP row0) t).toY)
    have e : ((gasNegT.map reflT).reverse.map fun t => (qcOf (sumP row0) t).toY) =
        ((gasNegT.map (mkCell 1 (sumP row0))).map YCell.reflect).reverse := by
      rw [List.map_reverse]
      congr 1
      simp only [List.map_map]
      apply List.map_congr_left
      intro t ht
      exact qcOf_reflT_toY row0_tot (row0_ok t (List.mem_of_mem_filter ht))
    rw [e]
    exact (List.reverse_perm _).symm

/-- **(G1)**: the species gas in the positive coordinate is partitioned by the bins. -/
theorem partitioned_species {K : ℕ} (hK : 0 < K) {T : ℤ} (hT : sumP row0 = T) (σ : Sign)
    (hc : cutsOK K T (gasT σ) = true) :
    Partitioned (gasR σ) ((binsQ K T (gasT σ)).map (List.map QC.toY)) :=
  Partitioned.of_perm (gasR_perm hT σ) (partitioned_cells hK T _ hc)

/-! ### Logarithm of a positive rational through WLog -/
open CatalanMeasure.WLog in
def logQ (x : ℚ) : Option (ℚ × ℚ) :=
  match expPQ x.num.natAbs x.den with
  | some (m, P, Q) => lnQP 5 m P Q
  | none => none

open CatalanMeasure.WLog in
theorem logQ_spec {x v e : ℚ} (hx : 0 < x) (h : logQ x = some (v, e)) :
    |Real.log (x : ℝ) - (v : ℝ)| ≤ (e : ℝ) := by
  unfold logQ at h
  cases h1 : expPQ x.num.natAbs x.den with
  | none => rw [h1] at h; simp at h
  | some t =>
    obtain ⟨m, P, Q⟩ := t
    rw [h1] at h
    simp only at h
    obtain ⟨hQ, hQP, hP2, hq⟩ := expPQ_spec h1
    have hs := lnQP_spec hQ hQP hP2 h
    have hnum : (x.num.natAbs : ℝ) = (x.num : ℝ) := by
      have : 0 < x.num := Rat.num_pos.2 hx
      have h2 : ((x.num.natAbs : ℤ) : ℝ) = (x.num : ℝ) := by
        rw [Int.natAbs_of_nonneg this.le]
      simpa using h2
    have hxr : (x : ℝ) = (x.num.natAbs : ℝ) / (x.den : ℝ) := by
      rw [hnum]; exact Rat.cast_def x
    rw [hxr, hq]
    exact hs

/-- Evaluated primitives at a root `x' = n / 2^128`: `H1 ≈ log x' - x'^2/2`, `H2 ≈ x' - x'^3/3`, error of `H1`. -/
structure HS where
  h1 : ℚ
  h2 : ℚ
  e : ℚ

def XB : ℕ := 2 ^ 128

def Hat (Y : ℚ) (n : ℕ) : Option HS :=
  if 0 < n ∧ n + 1 ≤ XB ∧ (1 : ℚ) / 16 ≤ (n : ℚ) / XB ∧ 0 ≤ ((n : ℚ) / XB) ^ 2 - Y * ((n : ℚ) / XB) + 1 ∧
      (((n : ℚ) + 1) / XB) ^ 2 - Y * (((n : ℚ) + 1) / XB) + 1 ≤ 0 then
    match logQ ((n : ℚ) / XB) with
    | some (v, e) => some ⟨v - ((n : ℚ) / XB) ^ 2 / 2, (n : ℚ) / XB - ((n : ℚ) / XB) ^ 3 / 3,
        e + (16 + (2 + 1 / (XB : ℚ)) / 2) * (1 / (XB : ℚ))⟩
    | none => none
  else none

theorem vY_bracket {Y x x1 : ℝ} (hY : 2 ≤ Y) (hx0 : 0 ≤ x) (hx1 : x1 ≤ 1) (hxx : x ≤ x1)
    (h0 : 0 ≤ x ^ 2 - Y * x + 1) (h1 : x1 ^ 2 - Y * x1 + 1 ≤ 0) : x ≤ vY Y ∧ vY Y ≤ x1 := by
  have hq := vY_quad hY
  have hp := vY_pos hY
  have hle := vY_le_one hY
  constructor
  · by_contra hc
    push_neg at hc
    nlinarith [mul_pos (sub_pos.2 hc) (by nlinarith : 0 < Y - (x + vY Y))]
  · by_contra hc
    push_neg at hc
    nlinarith [mul_pos (sub_pos.2 hc) (by nlinarith : 0 < Y - (x1 + vY Y))]

theorem Hat_spec {Y : ℚ} {n : ℕ} {hs : HS} (hY : (2 : ℝ) ≤ Y) (h : Hat Y n = some hs) :
    |(hs.h1 : ℝ) - H1 (vY Y)| ≤ hs.e ∧ |(hs.h2 : ℝ) - H2 (vY Y)| ≤ 4 / (XB : ℝ) := by
  unfold Hat at h
  split_ifs at h with hc
  obtain ⟨hn0, hn1, hxm, hg0, hg1⟩ := hc
  cases hl : logQ ((n : ℚ) / XB) with
  | none => rw [hl] at h; simp at h
  | some t =>
    obtain ⟨v, e⟩ := t
    rw [hl] at h
    simp only [Option.some.injEq] at h
    subst h
    have hXB : (0 : ℝ) < XB := by unfold XB; positivity
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hn1' : (n : ℝ) + 1 ≤ XB := by exact_mod_cast hn1
    have hx0 : (0 : ℝ) < (n : ℝ) / XB := by positivity
    have hxq : (0 : ℚ) < (n : ℚ) / XB := by
      have : (0 : ℚ) < XB := by unfold XB; positivity
      positivity
    have hlog := logQ_spec hxq hl
    push_cast at hlog
    have hg0' : 0 ≤ ((n : ℝ) / XB) ^ 2 - Y * ((n : ℝ) / XB) + 1 := by
      have h' := (Rat.cast_le (K := ℝ)).2 hg0; push_cast at h'; exact h'
    have hg1' : (((n : ℝ) + 1) / XB) ^ 2 - Y * (((n : ℝ) + 1) / XB) + 1 ≤ 0 := by
      have h' := (Rat.cast_le (K := ℝ)).2 hg1; push_cast at h'; exact h'
    have hx1 : ((n : ℝ) + 1) / XB ≤ 1 := by rw [div_le_one hXB]; exact hn1'
    have hxx : (n : ℝ) / XB ≤ ((n : ℝ) + 1) / XB := by gcongr; linarith
    obtain ⟨hb1, hb2⟩ := vY_bracket hY hx0.le hx1 hxx hg0' hg1'
    have hxm' : (1 : ℝ) / 16 ≤ (n : ℝ) / XB := by
      have h' := (Rat.cast_le (K := ℝ)).2 hxm; push_cast at h'; exact h'
    have hδ : (0 : ℝ) ≤ 1 / (XB : ℝ) := by positivity
    have hd : |vY Y - (n : ℝ) / XB| ≤ 1 / (XB : ℝ) := by
      rw [abs_le]; constructor
      · linarith
      · have : ((n : ℝ) + 1) / XB = (n : ℝ) / XB + 1 / XB := by ring
        linarith
    have hδ1 : 1 / (XB : ℝ) ≤ 1 := by
      rw [div_le_one hXB]; unfold XB; norm_num
    have hvle := vY_le_one hY
    have hvp := vY_pos hY
    constructor
    · have := H1_approx (x := vY Y) (x' := (n : ℝ) / XB) (L' := (v : ℝ)) (δ := 1 / (XB : ℝ)) (η := (e : ℝ))
        (xm := 1 / 16) (by norm_num) (by linarith) hxm' hvle (by
          have : (n : ℝ) / XB ≤ 1 := by linarith
          linarith) hδ hd (by rw [abs_sub_comm]; exact hlog)
      push_cast
      convert this using 2
      ring
    · have := H2_approx (x := vY Y) (x' := (n : ℝ) / XB) (δ := 1 / (XB : ℝ)) hvp.le hvle hx0.le
        (by have : (n : ℝ) / XB ≤ 1 := by linarith
            linarith) hδ hδ1 hd
      push_cast
      convert this using 2
      ring


/-! ### Moment accumulation over the pieces of a bin -/

structure Acc where
  A : ℚ
  B : ℚ
  eA : ℚ
  eB : ℚ

def Acc.add (a b : Acc) : Acc := ⟨a.A + b.A, a.B + b.B, a.eA + b.eA, a.eB + b.eB⟩
def Acc.zero : Acc := ⟨0, 0, 0, 0⟩

def pieceAcc (p : QC) (hl hh : HS) : Acc :=
  ⟨p.w / (p.hi - p.lo) * (hl.h1 - hh.h1), p.w / (p.hi - p.lo) * (hl.h2 - hh.h2),
   2 * (p.w / (p.hi - p.lo)) * (hl.e + hh.e), 2 * (p.w / (p.hi - p.lo)) * (4 / (XB : ℚ))⟩

/-- Fold over the pieces; the endpoint evaluation is reused when a piece starts where the previous one ended. -/
def binFold : List QC → List ℕ → ℚ → HS → Option Acc
  | [], _, _, _ => some Acc.zero
  | p :: ps, nlo :: nhi :: ns, Yc, Hc =>
    match (if p.lo = Yc then some Hc else Hat p.lo nlo), Hat p.hi nhi with
    | some hl, some hh =>
      match binFold ps ns p.hi hh with
      | some r => some ((pieceAcc p hl hh).add r)
      | none => none
    | _, _ => none
  | _ :: _, _, _, _ => none

def Good (Y : ℚ) (h : HS) : Prop :=
  (2 : ℝ) ≤ Y ∧ |(h.h1 : ℝ) - H1 (vY Y)| ≤ h.e ∧ |(h.h2 : ℝ) - H2 (vY Y)| ≤ 4 / (XB : ℝ)

theorem Good_of_Hat {Y : ℚ} {n : ℕ} {hs : HS} (hY : (2 : ℝ) ≤ Y) (h : Hat Y n = some hs) : Good Y hs :=
  ⟨hY, (Hat_spec hY h).1, (Hat_spec hY h).2⟩

theorem Good_e_nonneg {Y : ℚ} {h : HS} (hg : Good Y h) : (0 : ℝ) ≤ h.e :=
  le_trans (abs_nonneg _) hg.2.1

theorem piece_err {p : QC} (hp : p.ok) (h2 : (2 : ℚ) ≤ p.lo) {hl hh : HS}
    (gl : Good p.lo hl) (gh : Good p.hi hh) :
    |((pieceAcc p hl hh).A : ℝ) - p.toY.phys id| ≤ (pieceAcc p hl hh).eA ∧
    |((pieceAcc p hl hh).B : ℝ) - p.toY.phys (fun x => x ^ 2)| ≤ (pieceAcc p hl hh).eB := by
  have hlo := QC.toY_lo hp
  have hhi := QC.toY_hi hp
  have hw := QC.toY_w hp
  have h2' : (2 : ℝ) ≤ p.toY.lo := by rw [hlo]; exact_mod_cast h2
  have el := Good_e_nonneg gl
  have eh := Good_e_nonneg gh
  constructor
  · have := cell_A_err (cl := p.toY) h2' (Hl := (hl.h1 : ℝ)) (Hh := (hh.h1 : ℝ)) (e := (hl.e : ℝ) + (hh.e : ℝ))
      (by rw [hlo]; linarith [gl.2.1]) (by rw [hhi]; linarith [gh.2.1])
    rw [hlo, hhi, hw] at this
    simp only [pieceAcc]
    push_cast
    exact this
  · have := cell_B_err (cl := p.toY) h2' (Hl := (hl.h2 : ℝ)) (Hh := (hh.h2 : ℝ)) (e := 4 / (XB : ℝ))
      (by rw [hlo]; exact gl.2.2) (by rw [hhi]; exact gh.2.2)
    rw [hlo, hhi, hw] at this
    simp only [pieceAcc]
    push_cast
    convert this using 2

theorem binFold_spec : ∀ (ps : List QC) (ns : List ℕ) (Yc : ℚ) (Hc : HS) (acc : Acc),
    (Yc = 0 ∨ Good Yc Hc) → (∀ p ∈ ps, p.ok ∧ (2 : ℚ) ≤ p.lo) → binFold ps ns Yc Hc = some acc →
    |(acc.A : ℝ) - physL (ps.map QC.toY) id| ≤ acc.eA ∧
    |(acc.B : ℝ) - physL (ps.map QC.toY) (fun x => x ^ 2)| ≤ acc.eB := by
  intro ps
  induction ps with
  | nil =>
    intro ns Yc Hc acc _ _ h
    simp only [binFold, Option.some.injEq] at h
    subst h
    simp [Acc.zero, physL]
  | cons p ps ih =>
    intro ns Yc Hc acc hinit hps h
    obtain ⟨hpok, hp2⟩ := hps p (by simp)
    have hrest : ∀ q ∈ ps, q.ok ∧ (2 : ℚ) ≤ q.lo := fun q hq => hps q (by simp [hq])
    cases ns with
    | nil => simp [binFold] at h
    | cons nlo ns1 =>
      cases ns1 with
      | nil => simp [binFold] at h
      | cons nhi ns =>
        simp only [binFold] at h
        have hp2' : (2 : ℝ) ≤ (p.lo : ℝ) := by exact_mod_cast hp2
        -- the left endpoint
        generalize hL : (if p.lo = Yc then some Hc else Hat p.lo nlo) = L at h
        rcases L with _ | hl
        · simp at h
        · have gl : Good p.lo hl := by
            by_cases hc : p.lo = Yc
            · rw [if_pos hc] at hL
              have : Hc = hl := Option.some.inj hL
              subst this
              rcases hinit with h0 | hg
              · exfalso; rw [← hc] at h0; linarith
              · rw [hc]; exact hg
            · rw [if_neg hc] at hL
              exact Good_of_Hat hp2' hL
          cases hh : Hat p.hi nhi with
          | none => rw [hh] at h; simp at h
          | some hhh =>
            rw [hh] at h
            simp only at h
            have gh : Good p.hi hhh := by
              apply Good_of_Hat _ hh
              have : p.lo < p.hi := hpok.1
              have : (p.lo : ℝ) < p.hi := by exact_mod_cast this
              linarith
            cases hr : binFold ps ns p.hi hhh with
            | none => rw [hr] at h; simp at h
            | some r =>
              rw [hr] at h
              simp only [Option.some.injEq] at h
              subst h
              have hih := ih ns p.hi hhh r (Or.inr gh) hrest hr
              have hpe := piece_err hpok hp2 gl gh
              simp only [List.map_cons, physL_cons, Acc.add]
              push_cast
              constructor
              · have := abs_add_le (((pieceAcc p hl hhh).A : ℝ) - p.toY.phys id)
                  ((r.A : ℝ) - physL (ps.map QC.toY) id)
                have e : ((pieceAcc p hl hhh).A : ℝ) + (r.A : ℝ) - (p.toY.phys id + physL (ps.map QC.toY) id) =
                    (((pieceAcc p hl hhh).A : ℝ) - p.toY.phys id) + ((r.A : ℝ) - physL (ps.map QC.toY) id) := by ring
                rw [e]; linarith [hpe.1, hih.1]
              · have := abs_add_le (((pieceAcc p hl hhh).B : ℝ) - p.toY.phys (fun x => x ^ 2))
                  ((r.B : ℝ) - physL (ps.map QC.toY) (fun x => x ^ 2))
                have e : ((pieceAcc p hl hhh).B : ℝ) + (r.B : ℝ) - (p.toY.phys (fun x => x ^ 2) + physL (ps.map QC.toY) (fun x => x ^ 2)) =
                    (((pieceAcc p hl hhh).B : ℝ) - p.toY.phys (fun x => x ^ 2)) + ((r.B : ℝ) - physL (ps.map QC.toY) (fun x => x ^ 2)) := by ring
                rw [e]; linarith [hpe.2, hih.2]


/-! ### Bin data and the radius-free moment pass (G2a) -/

def binMass (b : List QC) : ℚ := (b.map QC.w).sum

theorem massL_map_toY : ∀ b : List QC, (∀ p ∈ b, p.ok) → massL (b.map QC.toY) = (binMass b : ℝ)
  | [], _ => by simp [massL, binMass]
  | p :: b, h => by
    have ih := massL_map_toY b (fun q hq => h q (by simp [hq]))
    have hw := QC.toY_w (h p (by simp))
    simp only [massL_cons, List.map_cons, ih, hw]
    simp [binMass]

/-- radius-free data of one bin: pieces, exact mass, rounded moment numerators, mass seed. -/
structure BD where
  pcs : List QC
  m : ℚ
  A : ℤ
  B : ℤ
  s0 : ℕ

def BD.cells (x : BD) : List YCell := x.pcs.map QC.toY
def BD.A2 (P : ℕ) (x : BD) : ℚ := (x.A : ℚ) / 2 ^ P
def BD.B2 (P : ℕ) (x : BD) : ℚ := (x.B : ℚ) / 2 ^ P

/-- the moment check of one bin (`ns`: root numerators of the piece endpoints). -/
def momPass (P : ℕ) (eA eB : ℚ) (x : BD) (ns : List ℕ) : Bool :=
  match binFold x.pcs ns 0 ⟨0, 0, 0⟩ with
  | none => false
  | some acc =>
    decide (x.pcs ≠ [] ∧ (∀ p ∈ x.pcs, p.ok ∧ (2 : ℚ) ≤ p.lo ∧ 0 < p.w) ∧ x.m = binMass x.pcs ∧
      (x.A : ℚ) ≤ acc.A * 2 ^ P ∧ acc.A * 2 ^ P < x.A + 1 ∧
      (x.B : ℚ) ≤ acc.B * 2 ^ P ∧ acc.B * 2 ^ P < x.B + 1 ∧
      acc.eA + 1 / 2 ^ P ≤ eA ∧ acc.eB + 1 / 2 ^ P ≤ eB ∧
      0 ≤ x.A ∧ 0 ≤ x.B ∧ x.B2 P ≤ x.m ∧
      (x.s0 : ℚ) ≤ x.m * 2 ^ P ∧ x.m * 2 ^ P < x.s0 + 1)

/-- what the moment pass proves. -/
structure MomSpec (P : ℕ) (eA eB : ℚ) (x : BD) : Prop where
  ne : x.pcs ≠ []
  pos : ∀ p ∈ x.pcs, p.ok ∧ (2 : ℚ) ≤ p.lo ∧ 0 < p.w
  mass : massL x.cells = (x.m : ℝ)
  hA : |physL x.cells id - ((x.A2 P : ℚ) : ℝ)| ≤ (eA : ℝ)
  hB : |physL x.cells (fun y => y ^ 2) - ((x.B2 P : ℚ) : ℝ)| ≤ (eB : ℝ)
  A0 : (0 : ℚ) ≤ x.A2 P
  B0 : (0 : ℚ) ≤ x.B2 P
  Bm : x.B2 P ≤ x.m
  s1 : (x.s0 : ℝ) ≤ (x.m : ℝ) * 2 ^ P
  s2 : (x.m : ℝ) * 2 ^ P < x.s0 + 1

theorem floor_close {P : ℕ} {d q : ℚ} {f : ℝ} {e0 eu : ℚ} (h1 : d ≤ q * 2 ^ P) (h2 : q * 2 ^ P < d + 1)
    (h3 : |(q : ℝ) - f| ≤ (e0 : ℝ)) (h4 : e0 + 1 / 2 ^ P ≤ eu) :
    |f - ((d / 2 ^ P : ℚ) : ℝ)| ≤ (eu : ℝ) := by
  have hP2q : (0 : ℚ) < 2 ^ P := by positivity
  have a1 : d / 2 ^ P ≤ q := by rw [div_le_iff₀ hP2q]; exact h1
  have a2 : q ≤ d / 2 ^ P + 1 / 2 ^ P := by
    rw [← add_div, le_div_iff₀ hP2q]; linarith
  have a1' := (Rat.cast_le (K := ℝ)).2 a1
  have a2' := (Rat.cast_le (K := ℝ)).2 a2
  have h4' := (Rat.cast_le (K := ℝ)).2 h4
  push_cast at a1' a2' h4' ⊢
  rw [abs_sub_comm] at h3
  rw [abs_le] at h3 ⊢
  constructor <;> linarith [h3.1, h3.2]

theorem momPass_spec {P : ℕ} {eA eB : ℚ} {x : BD} {ns : List ℕ} (h : momPass P eA eB x ns = true) :
    MomSpec P eA eB x := by
  unfold momPass at h
  cases hf : binFold x.pcs ns 0 ⟨0, 0, 0⟩ with
  | none => rw [hf] at h; simp at h
  | some acc =>
    rw [hf] at h
    simp only [decide_eq_true_eq] at h
    obtain ⟨hne, hall, hm, hA1, hA2, hB1, hB2, hea, heb, hA0, hB0, hBm, hs1, hs2⟩ := h
    have hok : ∀ p ∈ x.pcs, p.ok := fun p hp => (hall p hp).1
    have hsp := binFold_spec x.pcs ns 0 ⟨0, 0, 0⟩ acc (Or.inl rfl)
      (fun p hp => ⟨(hall p hp).1, (hall p hp).2.1⟩) hf
    refine ⟨hne, hall, ?_, floor_close hA1 hA2 hsp.1 hea, floor_close hB1 hB2 hsp.2 heb, ?_, ?_, hBm, ?_, ?_⟩
    · rw [hm]; exact massL_map_toY _ hok
    · unfold BD.A2
      have : (0 : ℚ) ≤ x.A := by exact_mod_cast hA0
      positivity
    · unfold BD.B2
      have : (0 : ℚ) ≤ x.B := by exact_mod_cast hB0
      positivity
    · exact_mod_cast hs1
    · exact_mod_cast hs2

/-- the moment check of a list of bins. -/
def momAll (P : ℕ) (eA eB : ℚ) : List BD → List (List ℕ) → Bool
  | [], [] => true
  | x :: xs, n :: ns => momPass P eA eB x n && momAll P eA eB xs ns
  | _, _ => false

theorem momAll_spec {P : ℕ} {eA eB : ℚ} : ∀ {T : List BD} {ns : List (List ℕ)},
    momAll P eA eB T ns = true → ∀ x ∈ T, MomSpec P eA eB x
  | [], [], _, _, hx => by simp at hx
  | [], _ :: _, h, _, _ => by simp [momAll] at h
  | _ :: _, [], h, _, _ => by simp [momAll] at h
  | y :: ys, n :: ns, h, x, hx => by
    simp only [momAll, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact momPass_spec h.1
    · exact momAll_spec h.2 x hx

theorem MomSpec.posL {P : ℕ} {eA eB : ℚ} {x : BD} (h : MomSpec P eA eB x) : PosL x.cells := by
  intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  rw [QC.toY_lo (h.pos p hp).1]; exact_mod_cast (h.pos p hp).2.1

theorem MomSpec.wpos {P : ℕ} {eA eB : ℚ} {x : BD} (h : MomSpec P eA eB x) : ∀ c ∈ x.cells, 0 < c.w := by
  intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  rw [QC.toY_w (h.pos p hp).1]; exact_mod_cast (h.pos p hp).2.2

theorem MomSpec.cne {P : ℕ} {eA eB : ℚ} {x : BD} (h : MomSpec P eA eB x) : x.cells ≠ [] := by
  simpa [BD.cells] using h.ne

theorem MomSpec.mpos {P : ℕ} {eA eB : ℚ} {x : BD} (h : MomSpec P eA eB x) : (0 : ℝ) < x.m := by
  have := massL_pos h.cne h.wpos
  rwa [h.mass] at this

theorem MomSpec.eA0 {P : ℕ} {eA eB : ℚ} {x : BD} (h : MomSpec P eA eB x) : (0 : ℝ) ≤ eA :=
  le_trans (abs_nonneg _) h.hA

theorem MomSpec.eB0 {P : ℕ} {eA eB : ℚ} {x : BD} (h : MomSpec P eA eB x) : (0 : ℝ) ≤ eB :=
  le_trans (abs_nonneg _) h.hB

/-! ### The radius -/

def expS (s : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => expS s n + s ^ n / (n.factorial : ℚ)

theorem expS_cast (s : ℚ) (N : ℕ) : (expS s N : ℝ) = ∑ i ∈ Finset.range N, (s : ℝ) ^ i / (i.factorial : ℝ) := by
  induction N with
  | zero => simp [expS]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; simp [expS]

def expLoQ (t : ℚ) (N : ℕ) : ℚ :=
  (1 / (expS (t / 8) N + (t / 8) ^ N * (N + 1) / ((N.factorial : ℚ) * N))) ^ 8
def expHiQ (t : ℚ) (N : ℕ) : ℚ := (1 / expS (t / 8) N) ^ 8

theorem expQ_enc (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 8) (N : ℕ) (hN : 0 < N) :
    (expLoQ t N : ℝ) ≤ Real.exp (-(t : ℝ)) ∧ Real.exp (-(t : ℝ)) ≤ (expHiQ t N : ℝ) := by
  set s : ℝ := (t : ℝ) / 8 with hs
  have hs0 : 0 ≤ s := by rw [hs]; have : (0:ℝ) ≤ t := by exact_mod_cast ht0
                         positivity
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one (by norm_num)]; exact_mod_cast ht1
  have hlo : ∑ i ∈ Finset.range N, s ^ i / (i.factorial : ℝ) ≤ Real.exp s := Real.sum_le_exp_of_nonneg hs0 N
  have hhi := Real.exp_bound' hs0 hs1 hN
  have hE0 : 0 < ∑ i ∈ Finset.range N, s ^ i / (i.factorial : ℝ) := by
    obtain ⟨n', rfl⟩ : ∃ n', N = n' + 1 := ⟨N - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have : 0 ≤ ∑ i ∈ Finset.range n', s ^ (i + 1) / ((i + 1).factorial : ℝ) :=
      Finset.sum_nonneg fun i _ => by positivity
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    linarith
  have hexp : Real.exp (-(t : ℝ)) = (Real.exp s)⁻¹ ^ 8 := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1; rw [hs]; push_cast; ring
  have e1 : (expLoQ t N : ℝ) = (1 / (∑ i ∈ Finset.range N, s ^ i / (i.factorial : ℝ) +
      s ^ N * (N + 1) / ((N.factorial : ℝ) * N))) ^ 8 := by
    unfold expLoQ; push_cast; rw [expS_cast]; simp [hs]
  have e2 : (expHiQ t N : ℝ) = (1 / ∑ i ∈ Finset.range N, s ^ i / (i.factorial : ℝ)) ^ 8 := by
    unfold expHiQ; push_cast; rw [expS_cast]; simp [hs]
  rw [e1, e2, hexp]
  have hexp_pos := Real.exp_pos s
  constructor
  · apply pow_le_pow_left₀ (by positivity)
    rw [← one_div]
    exact one_div_le_one_div_of_le hexp_pos hhi
  · apply pow_le_pow_left₀ (by positivity)
    rw [one_div]
    exact inv_anti₀ hE0 hlo

/-- what is needed of the radius: a dyadic enclosure `rH <= rad <= rH + 2^-P`, `rad <= 1`. -/
structure RadSpec (P : ℕ) (rad : ℝ) (rH : ℚ) : Prop where
  pos : (0 : ℝ) < rH
  lo : (rH : ℝ) ≤ rad
  hi : rad ≤ rH + 1 / 2 ^ P
  le1 : rad ≤ 1

/-- the radius check; `N` is the series length. -/
def radPass (P N : ℕ) (sig rH : ℚ) : Bool :=
  decide (0 < N ∧ 0 ≤ sig ∧ sig ≤ 8 ∧ 0 < rH ∧ rH ≤ expLoQ sig N ∧ expHiQ sig N ≤ rH + 1 / 2 ^ P)

theorem rad_enc (S : CapSource) (i : ℕ) {P N : ℕ} {sig rH : ℚ} (hsig : S.sigma i = (sig : ℝ))
    (h : radPass P N sig rH = true) : RadSpec P (S.rad i) rH := by
  simp only [radPass, decide_eq_true_eq] at h
  obtain ⟨hN, h0, h8, hr, n1, n2⟩ := h
  have he := expQ_enc sig h0 h8 N hN
  have e : S.rad i = Real.exp (-(sig : ℝ)) := by
    show Real.exp (-S.sigma i) = _
    rw [hsig]
  have a := (Rat.cast_le (K := ℝ)).2 n1
  have b := (Rat.cast_le (K := ℝ)).2 n2
  push_cast at a b
  rw [e]
  refine ⟨by exact_mod_cast hr, by linarith [he.1], by linarith [he.2], ?_⟩
  rw [Real.exp_le_one_iff]
  have : (0 : ℝ) ≤ sig := by exact_mod_cast h0
  linarith

/-- the `sigma` seeds of the source as rationals. -/
def sigQ (i : ℕ) : ℚ := (sigN.getD (min i 15) 0 : ℚ) / 10 ^ 17

theorem capSource_sigma (i : ℕ) : capSource.sigma i = (sigQ i : ℝ) := by
  show (sigN.getD (min i 15) 0 : ℝ) / 10 ^ 17 = _
  simp [sigQ]

theorem RadSpec.gap {P : ℕ} {rad : ℝ} {rH : ℚ} (h : RadSpec P rad rH) :
    0 ≤ rad ^ 2 - (rH : ℝ) ^ 2 ∧ rad ^ 2 - (rH : ℝ) ^ 2 ≤ 2 / 2 ^ P := by
  have hr0 := h.pos
  have hr1 := h.lo
  have hr2 := h.hi
  have hrad1 := h.le1
  have hrr : rad ^ 2 - (rH : ℝ) ^ 2 ≤ 2 / 2 ^ P := by
    have h1 : rad - rH ≤ 1 / 2 ^ P := by linarith
    have h2 : (rad - rH) * (rad + rH) ≤ 1 / 2 ^ P * (rad + rH) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have h3 : 1 / 2 ^ P * (rad + rH) ≤ 1 / 2 ^ P * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e1 : rad ^ 2 - (rH : ℝ) ^ 2 = (rad - rH) * (rad + rH) := by ring
    have e2 : (2 : ℝ) / 2 ^ P = 1 / 2 ^ P * 2 := by ring
    rw [e1, e2]; linarith
  exact ⟨by nlinarith, hrr⟩

/-! ### The per-radius alpha checks (G2b) -/

/-- `0 < D`, `num / D <= 1`, `a = floor (num / D * 2^P)`, `a <= 2^P`. -/
@[reducible] def alphaCore (P : ℕ) (D num : ℚ) (a : ℕ) : Prop :=
  0 < D ∧ num ≤ D ∧ (a : ℚ) * D ≤ num * 2 ^ P ∧ num * 2 ^ P < ((a : ℚ) + 1) * D ∧ a ≤ 2 ^ P

/-- rounded denominator of kernel 1 (`m rH^2 + B2`). -/
def D1 (P : ℕ) (rH : ℚ) (x : BD) : ℚ := x.m * rH ^ 2 + x.B2 P
/-- rounded denominator of kernel 2 (`m + rH^2 B2`). -/
def D2 (P : ℕ) (rH : ℚ) (x : BD) : ℚ := x.m + rH ^ 2 * x.B2 P
/-- rounded numerator `2 rH A2`, both kernels. -/
def numA (P : ℕ) (rH : ℚ) (x : BD) : ℚ := 2 * rH * x.A2 P

/-- kernel 1 check; the last conjunct gives `2 rad m <= kA (m rad^2 + B)` for the true moment. -/
def alpha1OK (P : ℕ) (rH eB kA : ℚ) (x : BD) (a : ℕ) : Bool :=
  decide (alphaCore P (D1 P rH x) (numA P rH x) a ∧ 0 ≤ kA ∧
    2 * (rH + 1 / 2 ^ P) * x.m ≤ kA * (D1 P rH x - eB))

/-- kernel 2 check. -/
def alpha2OK (P : ℕ) (rH : ℚ) (x : BD) (a : ℕ) : Bool :=
  decide (alphaCore P (D2 P rH x) (numA P rH x) a)

theorem alphaCore_spec {P : ℕ} {D num : ℚ} {a : ℕ} (h : alphaCore P D num a) :
    (0 : ℝ) < D ∧ (num : ℝ) / D ≤ 1 ∧ |(a : ℝ) / 2 ^ P - (num : ℝ) / D| ≤ 1 / 2 ^ P ∧ a ≤ 2 ^ P := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have hD : (0 : ℝ) < D := by exact_mod_cast h0
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have h1' : (num : ℝ) ≤ D := by exact_mod_cast h1
  have h2' : (a : ℝ) * D ≤ num * 2 ^ P := by exact_mod_cast h2
  have h3' : (num : ℝ) * 2 ^ P < ((a : ℝ) + 1) * D := by exact_mod_cast h3
  refine ⟨hD, (div_le_one hD).2 h1', ?_, h4⟩
  have c1 : (a : ℝ) / 2 ^ P ≤ num / D := by rw [div_le_div_iff₀ hP hD]; exact h2'
  have c2 : (num : ℝ) / D ≤ (a : ℝ) / 2 ^ P + 1 / 2 ^ P := by
    rw [← add_div, div_le_div_iff₀ hD hP]; linarith
  rw [abs_le]; constructor <;> linarith

/-- one record. -/
def recOf (x : BD) (a : ℕ) : BinRec := ⟨x.cells, a, x.s0⟩

/-- common core of the two kernels. -/
theorem rec_ok_core {P : ℕ} {eA eB : ℚ} {x : BD} {a : ℕ} (hM : MomSpec P eA eB x)
    {pa pb pc pa' pb' pc' kA d0 eD : ℝ} (ha : 0 < pa) (hb : 0 < pb) (hc : 0 < pc)
    (hbac : pb ^ 2 ≤ pa * pc) (hpb' : 0 < pb') (hale : a ≤ 2 ^ P)
    (hD : 0 < (x.m : ℝ) * pa' + pc' * ((x.B2 P : ℚ) : ℝ))
    (hα : 2 * pb' * ((x.A2 P : ℚ) : ℝ) / ((x.m : ℝ) * pa' + pc' * ((x.B2 P : ℚ) : ℝ)) ≤ 1)
    (hra : |(a : ℝ) / 2 ^ P - 2 * pb' * ((x.A2 P : ℚ) : ℝ) / ((x.m : ℝ) * pa' + pc' * ((x.B2 P : ℚ) : ℝ))| ≤
      1 / 2 ^ P)
    (hEb : |pb - pb'| ≤ 1 / 2 ^ P)
    (hED : |((x.m : ℝ) * pa + pc * physL x.cells (fun y => y ^ 2)) -
        ((x.m : ℝ) * pa' + pc' * ((x.B2 P : ℚ) : ℝ))| ≤ eD)
    (hkA : 2 * pb * (x.m : ℝ) ≤ kA * ((x.m : ℝ) * pa + pc * physL x.cells (fun y => y ^ 2)))
    (hd0 : d0 ≤ (x.m : ℝ) * pa + pc * physL x.cells (fun y => y ^ 2)) (hd0pos : 0 < d0) :
    RecOK P pa pb pc (alphaBudget P (x.m : ℝ) eA kA (1 / 2 ^ P) pb' eD d0) (recOf x a) := by
  have hmass : massL (recOf x a).cells = (x.m : ℝ) := hM.mass
  have hA0 : (0 : ℝ) ≤ ((x.A2 P : ℚ) : ℝ) := by exact_mod_cast hM.A0
  have key := recOK_of_prepared (P := P) (pa := pa) (pb := pb) (pc := pc) (r := recOf x a)
    hM.posL hM.cne hM.wpos ha hb hc hbac
    (by rw [hmass]; exact hM.s1) (by rw [hmass]; exact hM.s2) hale
    (A' := ((x.A2 P : ℚ) : ℝ)) (B' := ((x.B2 P : ℚ) : ℝ)) (pa' := pa') (pb' := pb') (pc' := pc')
    hA0 hpb' (by rw [hmass]; exact hD) (by rw [hmass]; exact hα) (by rw [hmass]; exact hra)
    (eA := (eA : ℝ)) (eb := 1 / 2 ^ P) (eD := eD) (kA := kA) (β := pb') (d0 := d0)
    hM.hA hEb (by rw [hmass]; exact hED) (by rw [hmass]; exact hkA) (by rw [hmass]; exact hd0)
    hd0pos le_rfl hpb' hM.eA0 (by positivity) (le_trans (abs_nonneg _) hED)
  rw [hmass] at key
  exact key

theorem ed1 {P : ℕ} {eA eB : ℚ} {x : BD} {rad : ℝ} {rH : ℚ} (hM : MomSpec P eA eB x)
    (hR : RadSpec P rad rH) :
    |((x.m : ℝ) * rad ^ 2 + 1 * physL x.cells (fun y => y ^ 2)) -
      ((x.m : ℝ) * (rH : ℝ) ^ 2 + 1 * ((x.B2 P : ℚ) : ℝ))| ≤ (x.m : ℝ) * (2 / 2 ^ P) + eB := by
  have hm := hM.mpos
  obtain ⟨g0, g1⟩ := hR.gap
  have h3 : (x.m : ℝ) * (rad ^ 2 - (rH : ℝ) ^ 2) ≤ x.m * (2 / 2 ^ P) := mul_le_mul_of_nonneg_left g1 hm.le
  have h4 : 0 ≤ (x.m : ℝ) * (rad ^ 2 - (rH : ℝ) ^ 2) := mul_nonneg hm.le g0
  have hB := abs_le.1 hM.hB
  rw [abs_le]; constructor <;> nlinarith [hB.1, hB.2]

theorem ed2 {P : ℕ} {eA eB : ℚ} {x : BD} {rad : ℝ} {rH : ℚ} (hM : MomSpec P eA eB x)
    (hR : RadSpec P rad rH) :
    |((x.m : ℝ) * 1 + rad ^ 2 * physL x.cells (fun y => y ^ 2)) -
      ((x.m : ℝ) * 1 + (rH : ℝ) ^ 2 * ((x.B2 P : ℚ) : ℝ))| ≤ (x.m : ℝ) * (2 / 2 ^ P) + eB := by
  have hm := hM.mpos
  obtain ⟨g0, g1⟩ := hR.gap
  have hB0 : (0 : ℝ) ≤ ((x.B2 P : ℚ) : ℝ) := by exact_mod_cast hM.B0
  have hBm : ((x.B2 P : ℚ) : ℝ) ≤ (x.m : ℝ) := by exact_mod_cast hM.Bm
  have hr0 : 0 < rad := lt_of_lt_of_le hR.pos hR.lo
  have hr2 : rad ^ 2 ≤ 1 := by nlinarith [hR.le1]
  set Bt := physL x.cells (fun y => y ^ 2) with hBt
  have e : ((x.m : ℝ) * 1 + rad ^ 2 * Bt) - ((x.m : ℝ) * 1 + (rH : ℝ) ^ 2 * ((x.B2 P : ℚ) : ℝ)) =
      rad ^ 2 * (Bt - ((x.B2 P : ℚ) : ℝ)) + (rad ^ 2 - (rH : ℝ) ^ 2) * ((x.B2 P : ℚ) : ℝ) := by ring
  rw [e]
  have t1 : |rad ^ 2 * (Bt - ((x.B2 P : ℚ) : ℝ))| ≤ eB := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc rad ^ 2 * |Bt - ((x.B2 P : ℚ) : ℝ)| ≤ 1 * eB :=
          mul_le_mul hr2 hM.hB (abs_nonneg _) zero_le_one
      _ = eB := one_mul _
  have t2 : |(rad ^ 2 - (rH : ℝ) ^ 2) * ((x.B2 P : ℚ) : ℝ)| ≤ (x.m : ℝ) * (2 / 2 ^ P) := by
    rw [abs_of_nonneg (mul_nonneg g0 hB0), mul_comm]
    exact mul_le_mul hBm g1 g0 hm.le
  have := abs_add_le (rad ^ 2 * (Bt - ((x.B2 P : ℚ) : ℝ))) ((rad ^ 2 - (rH : ℝ) ^ 2) * ((x.B2 P : ℚ) : ℝ))
  linarith

/-- **(G3)** kernel 1 (`pa = rad^2`, `pb = rad`, `pc = 1`) with a general constant `kA`. -/
theorem rec_ok1 {P : ℕ} {eA eB kA rH : ℚ} {rad : ℝ} {x : BD} {a : ℕ}
    (hR : RadSpec P rad rH) (hM : MomSpec P eA eB x) (h : alpha1OK P rH eB kA x a = true) :
    RecOK P (rad ^ 2) rad 1
      (alphaBudget P (x.m : ℝ) eA kA (1 / 2 ^ P) rH ((x.m : ℝ) * (2 / 2 ^ P) + eB) ((x.m : ℝ) * (rH : ℝ) ^ 2))
      (recOf x a) := by
  simp only [alpha1OK, decide_eq_true_eq] at h
  obtain ⟨hc, hk0, hk⟩ := h
  obtain ⟨hD, hα, hra, hale⟩ := alphaCore_spec hc
  have hr0 := hR.pos
  have hrad0 : 0 < rad := lt_of_lt_of_le hr0 hR.lo
  have hm := hM.mpos
  have eD1 : ((D1 P rH x : ℚ) : ℝ) = (x.m : ℝ) * (rH : ℝ) ^ 2 + 1 * ((x.B2 P : ℚ) : ℝ) := by
    simp [D1]
  have eN : ((numA P rH x : ℚ) : ℝ) = 2 * (rH : ℝ) * ((x.A2 P : ℚ) : ℝ) := by simp [numA]
  rw [eD1] at hD hα hra
  rw [eN] at hα hra
  obtain ⟨g0, g1⟩ := hR.gap
  have hsq := physL_sq_nonneg x.cells
  refine rec_ok_core hM (by positivity) hrad0 one_pos (by simp) hr0 hale hD hα hra ?_ (ed1 hM hR) ?_ ?_
    (by positivity)
  · rw [abs_le]; constructor <;> linarith [hR.lo, hR.hi]
  · have hk0' : (0 : ℝ) ≤ kA := by exact_mod_cast hk0
    have hk' : 2 * ((rH : ℝ) + 1 / 2 ^ P) * (x.m : ℝ) ≤
        (kA : ℝ) * ((x.m : ℝ) * (rH : ℝ) ^ 2 + 1 * ((x.B2 P : ℚ) : ℝ) - (eB : ℝ)) := by
      have hq := (Rat.cast_le (K := ℝ)).2 hk
      have e1 : ((2 * (rH + 1 / 2 ^ P) * x.m : ℚ) : ℝ) = 2 * ((rH : ℝ) + 1 / 2 ^ P) * (x.m : ℝ) := by
        push_cast; ring
      have e2 : ((kA * (D1 P rH x - eB) : ℚ) : ℝ) = (kA : ℝ) * (((D1 P rH x : ℚ) : ℝ) - (eB : ℝ)) := by
        push_cast; ring
      rw [e1, e2, eD1] at hq
      exact hq
    have h1 : 2 * rad * (x.m : ℝ) ≤ 2 * ((rH : ℝ) + 1 / 2 ^ P) * (x.m : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith [hR.hi]) hm.le
    have hB := (abs_le.1 hM.hB).1
    have h2 : (x.m : ℝ) * (rH : ℝ) ^ 2 + 1 * ((x.B2 P : ℚ) : ℝ) - (eB : ℝ) ≤
        (x.m : ℝ) * rad ^ 2 + 1 * physL x.cells (fun y => y ^ 2) := by
      nlinarith [mul_nonneg hm.le g0]
    exact h1.trans (hk'.trans (mul_le_mul_of_nonneg_left h2 hk0'))
  · nlinarith [mul_nonneg hm.le g0]

/-- **(G3)** kernel 2 (`pa = 1`, `pb = rad`, `pc = rad^2`), `kA = 2`. -/
theorem rec_ok2 {P : ℕ} {eA eB rH : ℚ} {rad : ℝ} {x : BD} {a : ℕ}
    (hR : RadSpec P rad rH) (hM : MomSpec P eA eB x) (h : alpha2OK P rH x a = true) :
    RecOK P 1 rad (rad ^ 2)
      (alphaBudget P (x.m : ℝ) eA 2 (1 / 2 ^ P) rH ((x.m : ℝ) * (2 / 2 ^ P) + eB) (x.m : ℝ))
      (recOf x a) := by
  simp only [alpha2OK, decide_eq_true_eq] at h
  obtain ⟨hD, hα, hra, hale⟩ := alphaCore_spec h
  have hr0 := hR.pos
  have hrad0 : 0 < rad := lt_of_lt_of_le hr0 hR.lo
  have hm := hM.mpos
  have eD2 : ((D2 P rH x : ℚ) : ℝ) = (x.m : ℝ) * 1 + (rH : ℝ) ^ 2 * ((x.B2 P : ℚ) : ℝ) := by
    simp [D2]
  have eN : ((numA P rH x : ℚ) : ℝ) = 2 * (rH : ℝ) * ((x.A2 P : ℚ) : ℝ) := by simp [numA]
  rw [eD2] at hD hα hra
  rw [eN] at hα hra
  have hsq := physL_sq_nonneg x.cells
  have hrB : 0 ≤ rad ^ 2 * physL x.cells (fun y => y ^ 2) := by positivity
  refine rec_ok_core hM one_pos hrad0 (by positivity) (by simp) hr0 hale hD hα hra ?_ (ed2 hM hR) ?_ ?_ hm
  · rw [abs_le]; constructor <;> linarith [hR.lo, hR.hi]
  · nlinarith [hR.le1]
  · linarith

/-! ### Families of bins -/

def recsOf (T : List BD) (as : List ℕ) : List BinRec := List.zipWith recOf T as

def binsY (T : List BD) : List (List YCell) := T.map BD.cells

/-- the per-radius check of all bins (`f` is `alpha1OK ..` or `alpha2OK ..`). -/
def alphaAll (f : BD → ℕ → Bool) : List BD → List ℕ → Bool
  | [], [] => true
  | x :: xs, a :: as => f x a && alphaAll f xs as
  | _, _ => false

theorem alphaAll_len {f : BD → ℕ → Bool} : ∀ {T : List BD} {as : List ℕ},
    alphaAll f T as = true → as.length = T.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [alphaAll] at h
  | _ :: _, [], h => by simp [alphaAll] at h
  | _ :: _, _ :: _, h => by
    simp only [alphaAll, Bool.and_eq_true] at h
    simpa using alphaAll_len h.2

theorem alphaAll_mem {f : BD → ℕ → Bool} : ∀ {T : List BD} {as : List ℕ},
    alphaAll f T as = true → ∀ r ∈ recsOf T as, ∃ x ∈ T, ∃ a, f x a = true ∧ r = recOf x a
  | [], [], _, r, hr => by simp [recsOf] at hr
  | [], _ :: _, h, _, _ => by simp [alphaAll] at h
  | _ :: _, [], h, _, _ => by simp [alphaAll] at h
  | y :: ys, b :: bs, h, r, hr => by
    simp only [alphaAll, Bool.and_eq_true] at h
    simp only [recsOf, List.zipWith_cons_cons, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨y, by simp, b, h.1, rfl⟩
    · obtain ⟨x, hx, a, ha, e⟩ := alphaAll_mem h.2 r hr
      exact ⟨x, by simp [hx], a, ha, e⟩

theorem recsOf_cells {T : List BD} {as : List ℕ} (h : as.length = T.length) :
    (recsOf T as).map BinRec.cells = binsY T := by
  induction T generalizing as with
  | nil => cases as <;> simp_all [recsOf, binsY]
  | cons x T ih =>
    cases as with
    | nil => simp at h
    | cons a as =>
      have := ih (as := as) (by simpa using h)
      simp only [recsOf, binsY] at this
      simp [recsOf, binsY, this, recOf]

theorem recsOf_a {T : List BD} {as : List ℕ} (h : as.length = T.length) :
    (recsOf T as).map BinRec.a = as := by
  induction T generalizing as with
  | nil => cases as <;> simp_all [recsOf]
  | cons x T ih =>
    cases as with
    | nil => simp at h
    | cons a as =>
      have := ih (as := as) (by simpa using h)
      simp only [recsOf] at this
      simp [recsOf, this, recOf]

theorem recsOf_s0 {T : List BD} {as : List ℕ} (h : as.length = T.length) :
    (recsOf T as).map BinRec.s0 = T.map BD.s0 := by
  induction T generalizing as with
  | nil => cases as <;> simp_all [recsOf]
  | cons x T ih =>
    cases as with
    | nil => simp at h
    | cons a as =>
      have := ih (as := as) (by simpa using h)
      simp only [recsOf] at this
      simp [recsOf, this, recOf]

/-- alpha budget of kernel 1. -/
def delta1 (P : ℕ) (eA eB kA rH : ℚ) (r : BinRec) : ℝ :=
  alphaBudget P (massL r.cells) eA kA (1 / 2 ^ P) rH (massL r.cells * (2 / 2 ^ P) + eB)
    (massL r.cells * (rH : ℝ) ^ 2)

/-- alpha budget of kernel 2. -/
def delta2 (P : ℕ) (eA eB rH : ℚ) (r : BinRec) : ℝ :=
  alphaBudget P (massL r.cells) eA 2 (1 / 2 ^ P) rH (massL r.cells * (2 / 2 ^ P) + eB) (massL r.cells)

theorem delta1_rec {P : ℕ} {eA eB kA rH : ℚ} {x : BD} (a : ℕ) (hM : MomSpec P eA eB x) :
    delta1 P eA eB kA rH (recOf x a) =
      alphaBudget P (x.m : ℝ) eA kA (1 / 2 ^ P) rH ((x.m : ℝ) * (2 / 2 ^ P) + eB) ((x.m : ℝ) * (rH : ℝ) ^ 2) := by
  have hmass : massL (recOf x a).cells = (x.m : ℝ) := hM.mass
  unfold delta1
  rw [hmass]

theorem delta2_rec {P : ℕ} {eA eB rH : ℚ} {x : BD} (a : ℕ) (hM : MomSpec P eA eB x) :
    delta2 P eA eB rH (recOf x a) =
      alphaBudget P (x.m : ℝ) eA 2 (1 / 2 ^ P) rH ((x.m : ℝ) * (2 / 2 ^ P) + eB) (x.m : ℝ) := by
  have hmass : massL (recOf x a).cells = (x.m : ℝ) := hM.mass
  unfold delta2
  rw [hmass]

theorem recOK_family1 {P : ℕ} {eA eB kA rH : ℚ} {rad : ℝ} {T : List BD} {as : List ℕ}
    (hR : RadSpec P rad rH) (hM : ∀ x ∈ T, MomSpec P eA eB x)
    (hA : alphaAll (alpha1OK P rH eB kA) T as = true) :
    ∀ r ∈ recsOf T as, RecOK P (rad ^ 2) rad 1 (delta1 P eA eB kA rH r) r := by
  intro r hr
  obtain ⟨x, hx, a, ha, rfl⟩ := alphaAll_mem hA r hr
  rw [delta1_rec a (hM x hx)]
  exact rec_ok1 hR (hM x hx) ha

theorem recOK_family2 {P : ℕ} {eA eB rH : ℚ} {rad : ℝ} {T : List BD} {as : List ℕ}
    (hR : RadSpec P rad rH) (hM : ∀ x ∈ T, MomSpec P eA eB x)
    (hA : alphaAll (alpha2OK P rH) T as = true) :
    ∀ r ∈ recsOf T as, RecOK P 1 rad (rad ^ 2) (delta2 P eA eB rH r) r := by
  intro r hr
  obtain ⟨x, hx, a, ha, rfl⟩ := alphaAll_mem hA r hr
  rw [delta2_rec a (hM x hx)]
  exact rec_ok2 hR (hM x hx) ha

/-- `eD = m 2 / 2^P + eB`. -/
def eDq (P : ℕ) (eB m : ℚ) : ℚ := m * (2 / 2 ^ P) + eB

/-- per-bin coefficient budget of kernel 1 (`m * delta`). -/
def budQ1 (P : ℕ) (eA eB kA rH m : ℚ) : ℚ :=
  m / 2 ^ P + kA * eA + m * ((1 / 2 ^ P) / rH * (1 + eDq P eB m / (m * rH ^ 2))) +
    m * (eDq P eB m / (m * rH ^ 2))

/-- per-bin coefficient budget of kernel 2 (`m * delta`). -/
def budQ2 (P : ℕ) (eA eB rH m : ℚ) : ℚ :=
  m / 2 ^ P + 2 * eA + m * ((1 / 2 ^ P) / rH * (1 + eDq P eB m / m)) + eDq P eB m

theorem mass_delta1 {P : ℕ} {eA eB kA rH m : ℚ} (hm : (0 : ℝ) < m) :
    (m : ℝ) * alphaBudget P (m : ℝ) eA kA (1 / 2 ^ P) rH ((m : ℝ) * (2 / 2 ^ P) + eB) ((m : ℝ) * (rH : ℝ) ^ 2) =
      (budQ1 P eA eB kA rH m : ℝ) := by
  rw [mass_mul_alphaBudget hm]
  unfold budQ1 eDq
  push_cast
  ring

theorem mass_delta2 {P : ℕ} {eA eB rH m : ℚ} (hm : (0 : ℝ) < m) :
    (m : ℝ) * alphaBudget P (m : ℝ) eA 2 (1 / 2 ^ P) rH ((m : ℝ) * (2 / 2 ^ P) + eB) (m : ℝ) =
      (budQ2 P eA eB rH m : ℝ) := by
  rw [mass_mul_alphaBudget hm]
  unfold budQ2 eDq
  push_cast
  have : (m : ℝ) * (((m : ℝ) * (2 / 2 ^ P) + (eB : ℝ)) / (m : ℝ)) = (m : ℝ) * (2 / 2 ^ P) + (eB : ℝ) := by
    field_simp
  rw [this]

/-- the coefficient budget `1/2^P + sum_b (1/2^P + bud m_b / 2)`. -/
def cbQ (P : ℕ) (bud : ℚ → ℚ) (T : List BD) : ℚ :=
  1 / 2 ^ P + (T.map fun x => 1 / 2 ^ P + bud x.m / 2).sum

theorem coefBudget_eq {P : ℕ} {δ : BinRec → ℝ} {bud : ℚ → ℚ} {T : List BD} {as : List ℕ}
    (hlen : as.length = T.length)
    (h : ∀ x ∈ T, ∀ a, massL (recOf x a).cells * δ (recOf x a) = (bud x.m : ℝ)) :
    coefBudget P δ (recsOf T as) = (cbQ P bud T : ℝ) := by
  have key : ∀ (T : List BD) (as : List ℕ), as.length = T.length →
      (∀ x ∈ T, ∀ a, massL (recOf x a).cells * δ (recOf x a) = (bud x.m : ℝ)) →
      ((recsOf T as).map fun r => 1 / 2 ^ P + massL r.cells * δ r / 2).sum =
        (((T.map fun x => 1 / 2 ^ P + bud x.m / 2).sum : ℚ) : ℝ) := by
    intro T
    induction T with
    | nil => intro as h _; cases as <;> simp_all [recsOf]
    | cons x T ih =>
      intro as hl hx
      cases as with
      | nil => simp at hl
      | cons a as =>
        have := ih as (by simpa using hl) (fun y hy => hx y (by simp [hy]))
        simp only [recsOf, List.zipWith_cons_cons, List.map_cons, List.sum_cons] at this ⊢
        rw [this, hx x (by simp) a]
        push_cast
        rfl
  unfold coefBudget cbQ
  rw [key T as hlen h]
  push_cast
  rfl

/-! ### The constant coefficients (G4) -/

/-- `pa + pc B2 / m`: kernel 1 `pa = rH^2, pc = 1`; kernel 2 `pa = 1, pc = rH^2`. -/
def dHat (P : ℕ) (pa pc : ℚ) (x : BD) : ℚ := pa + pc * x.B2 P / x.m

/-- the perturbation of the log: `lb` is a lower bound of the two arguments. -/
def eBin (P : ℕ) (eB lb : ℚ) (x : BD) : ℚ := (2 / 2 ^ P + eB / x.m) / lb

def logD (P : ℕ) (eB pa pc lb : ℚ) (x : BD) : Option (ℚ × ℚ) :=
  match logQ (dHat P pa pc x) with
  | some (v, e) => some (v, e + eBin P eB lb x)
  | none => none

/-- `(sum_b m_b/2 log D_b, error)`. Kernel 1: `constSum P eB (rH^2) 1 (rH^2)`;
kernel 2: `constSum P eB 1 (rH^2) 1`. -/
def constSum (P : ℕ) (eB pa pc lb : ℚ) : List BD → Option (ℚ × ℚ)
  | [] => some (0, 0)
  | x :: xs =>
    match logD P eB pa pc lb x, constSum P eB pa pc lb xs with
    | some (v, e), some (S, H) => some (x.m / 2 * v + S, x.m / 2 * e + H)
    | _, _ => none

theorem logD_spec {P : ℕ} {eA eB pa pc lb : ℚ} {x : BD} (hM : MomSpec P eA eB x) {Pa Pc : ℝ}
    (hlb : 0 < lb) (hpa : lb ≤ pa) (hpc : 0 ≤ pc) (hPa : (lb : ℝ) ≤ Pa) (hPc : 0 ≤ Pc)
    (hE : |((x.m : ℝ) * Pa + Pc * physL x.cells (fun y => y ^ 2)) -
      ((x.m : ℝ) * pa + pc * ((x.B2 P : ℚ) : ℝ))| ≤ (x.m : ℝ) * (2 / 2 ^ P) + eB)
    {v e : ℚ} (h : logD P eB pa pc lb x = some (v, e)) :
    |Real.log (binD Pa Pc x.cells) - (v : ℝ)| ≤ (e : ℝ) := by
  unfold logD at h
  cases hl : logQ (dHat P pa pc x) with
  | none => rw [hl] at h; simp at h
  | some t =>
    obtain ⟨v0, e0⟩ := t
    rw [hl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hmr : (0 : ℝ) < x.m := hM.mpos
    have hmq : (0 : ℚ) < x.m := by exact_mod_cast hmr
    have hB0 : (0 : ℝ) ≤ ((x.B2 P : ℚ) : ℝ) := by exact_mod_cast hM.B0
    have hlbr : (0 : ℝ) < lb := by exact_mod_cast hlb
    have hpar : (lb : ℝ) ≤ pa := by exact_mod_cast hpa
    have hpcr : (0 : ℝ) ≤ pc := by exact_mod_cast hpc
    have hsq := physL_sq_nonneg x.cells
    set Bt := physL x.cells (fun y => y ^ 2) with hBt
    set B2 : ℝ := ((x.B2 P : ℚ) : ℝ) with hB2
    set m : ℝ := (x.m : ℝ) with hm
    have hxdef : binD Pa Pc x.cells = Pa + Pc * Bt / m := by
      unfold binD; rw [hM.mass]
    have hydef : ((dHat P pa pc x : ℚ) : ℝ) = (pa : ℝ) + (pc : ℝ) * B2 / m := by
      unfold dHat; simp only [hB2, hm]; push_cast; ring
    have hx1 : (lb : ℝ) ≤ Pa + Pc * Bt / m := by
      have : 0 ≤ Pc * Bt / m := div_nonneg (mul_nonneg hPc hsq) hmr.le
      linarith
    have hy1 : (lb : ℝ) ≤ ((dHat P pa pc x : ℚ) : ℝ) := by
      rw [hydef]
      have : 0 ≤ (pc : ℝ) * B2 / m := div_nonneg (mul_nonneg hpcr hB0) hmr.le
      linarith
    have hdq : (0 : ℚ) < dHat P pa pc x := by
      have : (0 : ℝ) < ((dHat P pa pc x : ℚ) : ℝ) := lt_of_lt_of_le hlbr hy1
      exact_mod_cast this
    have hlog := logQ_spec hdq hl
    have hdiff : |Pa + Pc * Bt / m - ((dHat P pa pc x : ℚ) : ℝ)| ≤ 2 / 2 ^ P + (eB : ℝ) / m := by
      rw [hydef]
      have e : Pa + Pc * Bt / m - ((pa : ℝ) + (pc : ℝ) * B2 / m) =
          ((m * Pa + Pc * Bt) - (m * (pa : ℝ) + (pc : ℝ) * B2)) / m := by
        field_simp
      rw [e, abs_div, abs_of_pos hmr]
      calc _ ≤ (m * (2 / 2 ^ P) + (eB : ℝ)) / m := div_le_div_of_nonneg_right hE hmr.le
        _ = 2 / 2 ^ P + (eB : ℝ) / m := by field_simp
    rw [hxdef]
    have hxpos : 0 < Pa + Pc * Bt / m := lt_of_lt_of_le hlbr hx1
    have hypos : 0 < ((dHat P pa pc x : ℚ) : ℝ) := lt_of_lt_of_le hlbr hy1
    have hl1 := abs_log_sub_le hxpos hypos
    have hmin : (lb : ℝ) ≤ min (Pa + Pc * Bt / m) ((dHat P pa pc x : ℚ) : ℝ) := le_min hx1 hy1
    have hq : |Pa + Pc * Bt / m - ((dHat P pa pc x : ℚ) : ℝ)| /
        min (Pa + Pc * Bt / m) ((dHat P pa pc x : ℚ) : ℝ) ≤ (2 / 2 ^ P + (eB : ℝ) / m) / (lb : ℝ) := by
      calc _ ≤ |Pa + Pc * Bt / m - ((dHat P pa pc x : ℚ) : ℝ)| / (lb : ℝ) :=
            div_le_div_of_nonneg_left (abs_nonneg _) hlbr hmin
        _ ≤ _ := div_le_div_of_nonneg_right hdiff hlbr.le
    have hbin : ((eBin P eB lb x : ℚ) : ℝ) = (2 / 2 ^ P + (eB : ℝ) / m) / (lb : ℝ) := by
      unfold eBin; simp only [hm]; push_cast; ring
    have t := abs_add_le (Real.log (Pa + Pc * Bt / m) - Real.log ((dHat P pa pc x : ℚ) : ℝ))
      (Real.log ((dHat P pa pc x : ℚ) : ℝ) - (v0 : ℝ))
    have e2 : Real.log (Pa + Pc * Bt / m) - (v0 : ℝ) =
        (Real.log (Pa + Pc * Bt / m) - Real.log ((dHat P pa pc x : ℚ) : ℝ)) +
        (Real.log ((dHat P pa pc x : ℚ) : ℝ) - (v0 : ℝ)) := by ring
    rw [e2]
    push_cast
    rw [hbin]
    linarith

theorem constSum_spec {P : ℕ} {eA eB pa pc lb : ℚ} {Pa Pc : ℝ}
    (hlb : 0 < lb) (hpa : lb ≤ pa) (hpc : 0 ≤ pc) (hPa : (lb : ℝ) ≤ Pa) (hPc : 0 ≤ Pc) :
    ∀ (T : List BD) {S H : ℚ}, (∀ x ∈ T, MomSpec P eA eB x) →
    (∀ x ∈ T, |((x.m : ℝ) * Pa + Pc * physL x.cells (fun y => y ^ 2)) -
      ((x.m : ℝ) * pa + pc * ((x.B2 P : ℚ) : ℝ))| ≤ (x.m : ℝ) * (2 / 2 ^ P) + eB) →
    constSum P eB pa pc lb T = some (S, H) →
    |(S : ℝ) - (T.map fun x => (x.m : ℝ) / 2 * Real.log (binD Pa Pc x.cells)).sum| ≤ H
  | [], S, H, _, _, h => by
    simp only [constSum, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | x :: xs, S, H, hM, hE, h => by
    unfold constSum at h
    cases hl : logD P eB pa pc lb x with
    | none => rw [hl] at h; simp at h
    | some t =>
      obtain ⟨v, e⟩ := t
      rw [hl] at h
      cases hc : constSum P eB pa pc lb xs with
      | none => rw [hc] at h; simp at h
      | some t2 =>
        obtain ⟨S2, H2⟩ := t2
        rw [hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hMx := hM x (by simp)
        have ih := constSum_spec hlb hpa hpc hPa hPc xs (fun y hy => hM y (by simp [hy]))
          (fun y hy => hE y (by simp [hy])) hc
        have hls := logD_spec hMx hlb hpa hpc hPa hPc (hE x (by simp)) hl
        have hmpos : (0 : ℝ) < x.m := hMx.mpos
        simp only [List.map_cons, List.sum_cons]
        push_cast
        set rest := (xs.map fun x => (x.m : ℝ) / 2 * Real.log (binD Pa Pc x.cells)).sum with hrest
        have t1 : |(x.m : ℝ) / 2 * ((v : ℝ) - Real.log (binD Pa Pc x.cells))| ≤ (x.m : ℝ) / 2 * (e : ℝ) := by
          rw [abs_mul, abs_of_pos (by positivity)]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [abs_sub_comm]; exact hls
        have t2 := abs_add_le ((x.m : ℝ) / 2 * ((v : ℝ) - Real.log (binD Pa Pc x.cells))) ((S2 : ℝ) - rest)
        have e1 : (x.m : ℝ) / 2 * (v : ℝ) + (S2 : ℝ) -
            ((x.m : ℝ) / 2 * Real.log (binD Pa Pc x.cells) + rest) =
            (x.m : ℝ) / 2 * ((v : ℝ) - Real.log (binD Pa Pc x.cells)) + ((S2 : ℝ) - rest) := by ring
        rw [e1]
        linarith

theorem constTrue_recsOf {P : ℕ} {eA eB : ℚ} {Pa Pc : ℝ} {T : List BD} {as : List ℕ}
    (hlen : as.length = T.length) (hM : ∀ x ∈ T, MomSpec P eA eB x) :
    constTrue Pa Pc (recsOf T as) = (T.map fun x => (x.m : ℝ) / 2 * Real.log (binD Pa Pc x.cells)).sum := by
  induction T generalizing as with
  | nil => cases as <;> simp_all [recsOf, constTrue]
  | cons x T ih =>
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have := ih (as := as) (by simpa using hlen) (fun y hy => hM y (by simp [hy]))
      simp only [constTrue, recsOf] at this
      have hmass : massL x.cells = (x.m : ℝ) := (hM x (by simp)).mass
      simp only [constTrue, recsOf, List.zipWith_cons_cons, List.map_cons, List.sum_cons, this]
      show massL x.cells / 2 * Real.log (binD Pa Pc x.cells) + _ = _
      rw [hmass]

/-- kernel 1 constant. -/
theorem const1_err {P : ℕ} {eA eB rH : ℚ} {rad : ℝ} {T : List BD} {as : List ℕ}
    (hR : RadSpec P rad rH) (hlen : as.length = T.length) (hM : ∀ x ∈ T, MomSpec P eA eB x)
    {c H : ℚ} (hS : constSum P eB (rH ^ 2) 1 (rH ^ 2) T = some (c, H)) :
    |(c : ℝ) - constTrue (rad ^ 2) 1 (recsOf T as)| ≤ H := by
  rw [constTrue_recsOf hlen hM]
  have hr0 : (0 : ℚ) < rH := by exact_mod_cast hR.pos
  refine constSum_spec (eA := eA) (by positivity) le_rfl zero_le_one ?_ zero_le_one T hM ?_ hS
  · have := hR.gap.1
    push_cast; linarith
  · intro x hx
    have := ed1 (hM x hx) hR
    push_cast
    exact this

/-- kernel 2 constant. -/
theorem const2_err {P : ℕ} {eA eB rH : ℚ} {rad : ℝ} {T : List BD} {as : List ℕ}
    (hR : RadSpec P rad rH) (hlen : as.length = T.length) (hM : ∀ x ∈ T, MomSpec P eA eB x)
    {c H : ℚ} (hS : constSum P eB 1 (rH ^ 2) 1 T = some (c, H)) :
    |(c : ℝ) - constTrue 1 (rad ^ 2) (recsOf T as)| ≤ H := by
  rw [constTrue_recsOf hlen hM]
  refine constSum_spec (eA := eA) one_pos le_rfl (by positivity) (by simp) (by positivity) T hM ?_ hS
  intro x hx
  have := ed2 (hM x hx) hR
  push_cast
  exact this

/-! ### Fast evaluation of the power streams (G5) -/

theorem stream_shift (P a s0 : ℕ) : ∀ k, stream P a s0 (k + 1) = stream P a (s0 * a / 2 ^ P) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [stream, ih]; rfl

def stepAll (P : ℕ) (as ss : List ℕ) : List ℕ := List.zipWith (fun a s => s * a / 2 ^ P) as ss

def aggLoop (P : ℕ) (as : List ℕ) : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | n + 1, ss => ss.sum :: aggLoop P as n (stepAll P as ss)

theorem stepAll_length (P : ℕ) (as ss : List ℕ) : (stepAll P as ss).length = min as.length ss.length := by
  simp [stepAll]

theorem aggLoop_spec (P : ℕ) (as : List ℕ) : ∀ (n : ℕ) (ss : List ℕ), ss.length = as.length →
    aggLoop P as n ss = (List.range n).map fun k => (List.zipWith (fun a s => stream P a s k) as ss).sum := by
  intro n
  induction n with
  | zero => intro ss _; simp [aggLoop]
  | succ n ih =>
    intro ss hlen
    rw [aggLoop, List.range_succ_eq_map, List.map_cons, List.map_map]
    have hlen' : (stepAll P as ss).length = as.length := by
      rw [stepAll_length]; omega
    rw [ih _ hlen']
    congr 1
    · -- k = 0 term
      have : ∀ (as ss : List ℕ), ss.length = as.length →
          (List.zipWith (fun a s => stream P a s 0) as ss).sum = ss.sum := by
        intro as
        induction as with
        | nil => intro ss h; cases ss <;> simp_all
        | cons a as ih2 =>
          intro ss h
          cases ss with
          | nil => simp at h
          | cons s ss =>
            simp only [List.zipWith_cons_cons, List.sum_cons]
            rw [ih2 ss (by simpa using h)]; rfl
      exact (this as ss hlen).symm
    · -- shift
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_apply]
      have : ∀ (as ss : List ℕ), ss.length = as.length →
          (List.zipWith (fun a s => stream P a s (k + 1)) as ss).sum =
          (List.zipWith (fun a s => stream P a s k) as (stepAll P as ss)).sum := by
        intro as
        induction as with
        | nil => intro ss h; cases ss <;> simp_all [stepAll]
        | cons a as ih2 =>
          intro ss h
          cases ss with
          | nil => simp at h
          | cons s ss =>
            simp only [stepAll, List.zipWith_cons_cons, List.sum_cons, stream_shift] at ih2 ⊢
            rw [ih2 ss (by simpa using h)]
      exact (this as ss hlen).symm

def coefsFrom : ℕ → List ℕ → List ℤ
  | _, [] => []
  | k, S :: Ss => (-(coefNum k S : ℤ)) :: coefsFrom (k + 1) Ss

theorem coefsFrom_eq : ∀ (Ss : List ℕ) (j : ℕ),
    coefsFrom j Ss = (List.range Ss.length).map fun i => -(coefNum (j + i) (Ss.getD i 0) : ℤ)
  | [], j => by simp [coefsFrom]
  | S :: Ss, j => by
    rw [coefsFrom, coefsFrom_eq Ss (j + 1), List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.getD_cons_zero, Nat.add_zero, List.cons.injEq, true_and]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, List.getD_cons_succ]
    congr 3
    omega

def glFast (P : ℕ) (as ss : List ℕ) (cnum : ℤ) (n : ℕ) : List ℤ :=
  cnum :: coefsFrom 1 ((aggLoop P as (n + 1) ss).tail)

theorem Sagg_eq_zip (P : ℕ) (recs : List BinRec) (k : ℕ) :
    Sagg P recs k = (List.zipWith (fun a s => stream P a s k) (recs.map BinRec.a) (recs.map BinRec.s0)).sum := by
  unfold Sagg
  induction recs with
  | nil => simp
  | cons r recs ih => simp [ih]

theorem aggLoop_tail (P : ℕ) (recs : List BinRec) (n : ℕ) :
    (aggLoop P (recs.map BinRec.a) (n + 1) (recs.map BinRec.s0)).tail =
      (List.range n).map fun k => Sagg P recs (k + 1) := by
  have hlen : (recs.map BinRec.s0).length = (recs.map BinRec.a).length := by simp
  rw [aggLoop_spec _ _ (n + 1) _ hlen, List.range_succ_eq_map, List.map_cons, List.tail_cons, List.map_map]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply]
  rw [Sagg_eq_zip]

theorem glFast_eq (P : ℕ) (recs : List BinRec) (cnum : ℤ) (n : ℕ) :
    glFast P (recs.map BinRec.a) (recs.map BinRec.s0) cnum n = GasCert.glPos P recs cnum n := by
  unfold glFast GasCert.glPos
  congr 1
  rw [aggLoop_tail, coefsFrom_eq]
  simp only [List.length_map, List.length_range]
  apply List.map_congr_left
  intro k hk
  have hk0 : k < n := by simpa using hk
  have h1 : 1 + k = k + 1 := by omega
  rw [h1]
  congr 3
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hk0]

/-- negative species: sign `(-1)^k` times `-(c1 + c2)` by parity of `k`. -/
def coefsNeg : ℕ → List ℕ → List ℕ → List ℤ
  | k, S :: Ss, R :: Rs =>
    (if k % 2 = 0 then -((coefNum k S + coefNum k R : ℕ) : ℤ) else ((coefNum k S + coefNum k R : ℕ) : ℤ)) ::
      coefsNeg (k + 1) Ss Rs
  | _, _, _ => []

def glFastNeg (P : ℕ) (as₁ as₂ ss : List ℕ) (cnum : ℤ) (n : ℕ) : List ℤ :=
  cnum :: coefsNeg 1 ((aggLoop P as₁ (n + 1) ss).tail) ((aggLoop P as₂ (n + 1) ss).tail)

theorem neg_sign (j c : ℕ) : (-1 : ℤ) ^ j * (-(c : ℤ)) = if j % 2 = 0 then -(c : ℤ) else (c : ℤ) := by
  split
  · have : Even j := Nat.even_iff.2 ‹_›
    rw [this.neg_one_pow]; ring
  · have : Odd j := Nat.odd_iff.2 (by omega)
    rw [this.neg_one_pow]; ring

theorem coefsNeg_map (f g : ℕ → ℕ) : ∀ (n j : ℕ),
    coefsNeg j ((List.range n).map fun k => f (j + k)) ((List.range n).map fun k => g (j + k)) =
      (List.range n).map fun k => (-1 : ℤ) ^ (j + k) *
        (-((coefNum (j + k) (f (j + k)) + coefNum (j + k) (g (j + k)) : ℕ) : ℤ)) := by
  intro n
  induction n with
  | zero => intro j; simp [coefsNeg]
  | succ n ih =>
    intro j
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, coefsNeg]
    have := ih (j + 1)
    simp only [Nat.add_zero]
    rw [neg_sign]
    congr 1
    have e : ∀ h : ℕ → ℕ, (fun k => h (j + k)) ∘ Nat.succ = fun k => h (j + 1 + k) := by
      intro h; funext k; simp only [Function.comp_apply]; congr 1; omega
    rw [e f, e g, this]
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply]
    have : j + k.succ = j + 1 + k := by omega
    rw [this]

theorem glFastNeg_eq (P : ℕ) (recs₁ recs₂ : List BinRec) (hs : recs₂.map BinRec.s0 = recs₁.map BinRec.s0)
    (cnum : ℤ) (n : ℕ) :
    glFastNeg P (recs₁.map BinRec.a) (recs₂.map BinRec.a) (recs₁.map BinRec.s0) cnum n =
      GasCert.glNeg P recs₁ recs₂ cnum n := by
  unfold glFastNeg GasCert.glNeg
  congr 1
  have h2 := aggLoop_tail P recs₂ n
  rw [hs] at h2
  rw [aggLoop_tail, h2]
  have h := coefsNeg_map (fun k => Sagg P recs₁ k) (fun k => Sagg P recs₂ k) n 1
  have e : ∀ h : ℕ → ℕ, (fun k => h (k + 1)) = fun k => h (1 + k) := by
    intro h; funext k; congr 1; omega
  rw [e (fun k => Sagg P recs₁ k), e (fun k => Sagg P recs₂ k), h]
  apply List.map_congr_left
  intro k _
  have h1 : 1 + k = k + 1 := by omega
  rw [h1]

/-! ### The gas side of the certificate (G6) -/

theorem floor_err {P : ℕ} {c : ℚ} {cnum : ℤ} (hc1 : (cnum : ℚ) ≤ c * 2 ^ P) (hc2 : c * 2 ^ P < cnum + 1) :
    |(cnum : ℝ) / 2 ^ P - (c : ℝ)| ≤ 1 / 2 ^ P := by
  have hP2q : (0 : ℚ) < 2 ^ P := by positivity
  have a1 : (cnum : ℚ) / 2 ^ P ≤ c := by rw [div_le_iff₀ hP2q]; exact hc1
  have a2 : c ≤ (cnum : ℚ) / 2 ^ P + 1 / 2 ^ P := by
    rw [← add_div, le_div_iff₀ hP2q]; linarith
  have a1' := (Rat.cast_le (K := ℝ)).2 a1
  have a2' := (Rat.cast_le (K := ℝ)).2 a2
  push_cast at a1' a2'
  rw [abs_le]; constructor <;> linarith

/-- budget lists of the two kernels. -/
def cb1 (P : ℕ) (eA eB kA rH : ℚ) (T : List BD) : ℚ := cbQ P (budQ1 P eA eB kA rH) T
def cb2 (P : ℕ) (eA eB rH : ℚ) (T : List BD) : ℚ := cbQ P (budQ2 P eA eB rH) T

theorem coefBudget1 {P : ℕ} {eA eB kA rH : ℚ} {T : List BD} {as : List ℕ}
    (hlen : as.length = T.length) (hM : ∀ x ∈ T, MomSpec P eA eB x) :
    coefBudget P (delta1 P eA eB kA rH) (recsOf T as) = (cb1 P eA eB kA rH T : ℝ) := by
  apply coefBudget_eq hlen
  intro x hx a
  have hmass : massL (recOf x a).cells = (x.m : ℝ) := (hM x hx).mass
  rw [delta1_rec a (hM x hx), hmass]
  exact mass_delta1 (hM x hx).mpos

theorem coefBudget2 {P : ℕ} {eA eB rH : ℚ} {T : List BD} {as : List ℕ}
    (hlen : as.length = T.length) (hM : ∀ x ∈ T, MomSpec P eA eB x) :
    coefBudget P (delta2 P eA eB rH) (recsOf T as) = (cb2 P eA eB rH T : ℝ) := by
  apply coefBudget_eq hlen
  intro x hx a
  have hmass : massL (recOf x a).cells = (x.m : ℝ) := (hM x hx).mass
  rw [delta2_rec a (hM x hx), hmass]
  exact mass_delta2 (hM x hx).mpos

/-- **(G6), positive species**. -/
theorem gas_cert_pos (S : CapSource) (i : ℕ) {P : ℕ} {eA eB kA rH : ℚ} {T : List BD} {as : List ℕ}
    (hp : Partitioned (S.gas Sign.pos) (binsY T)) (hM : ∀ x ∈ T, MomSpec P eA eB x)
    (hR : RadSpec P (S.rad i) rH) (hA : alphaAll (alpha1OK P rH eB kA) T as = true)
    {c H : ℚ} (hS : constSum P eB (rH ^ 2) 1 (rH ^ 2) T = some (c, H))
    {cnum : ℤ} (hc1 : (cnum : ℚ) ≤ c * 2 ^ P) (hc2 : c * 2 ^ P < cnum + 1) (n : ℕ) :
    AngularSource.Binning (S.gas Sign.pos) (binsY T) ∧
    ∑ j ∈ Finset.range (n + 1),
      |AngularCap.gasA S Sign.pos i (binsY T) j -
        (((glFast P as (T.map BD.s0) cnum n).getD j 0 : ℤ) : ℝ) / ((2 ^ P : ℕ) : ℝ)| ≤
      (((1 / 2 ^ P + H) + n * cb1 P eA eB kA rH T : ℚ) : ℝ) := by
  have hlen := alphaAll_len hA
  have hcells := recsOf_cells hlen
  have hc := const1_err hR hlen hM hS
  have hf := floor_err hc1 hc2
  have hc0 : |(cnum : ℝ) / 2 ^ P - constTrue ((S.rad i) ^ 2) 1 (recsOf T as)| ≤
      ((1 / 2 ^ P + H : ℚ) : ℝ) := by
    push_cast
    rw [abs_le] at hc hf ⊢
    constructor <;> linarith [hc.1, hc.2, hf.1, hf.2]
  have h := GasCert.gasCert_pos S (recs := recsOf T as) i (by rw [hcells]; exact hp) (n := n) (P := P)
    (δ := delta1 P eA eB kA rH) (recOK_family1 hR hM hA) cnum hc0
  rw [hcells, ← glFast_eq, recsOf_a hlen, recsOf_s0 hlen, coefBudget1 hlen hM] at h
  refine ⟨h.1, ?_⟩
  push_cast at h ⊢
  exact h.2

/-- **(G6), negative species**: cells in the positive coordinate, `T` shared by the two kernels. -/
theorem gas_cert_neg (S : CapSource) (i : ℕ) {P : ℕ} {eA eB kA rH : ℚ} {T : List BD} {as₁ as₂ : List ℕ}
    (hp : Partitioned (reflectL (S.gas Sign.neg)) (binsY T))
    (hg : ∀ c ∈ S.gas Sign.neg, c.hi ≤ -2) (hw : ∀ c ∈ S.gas Sign.neg, 0 < c.w)
    (hM : ∀ x ∈ T, MomSpec P eA eB x) (hR : RadSpec P (S.rad i) rH)
    (hA₁ : alphaAll (alpha1OK P rH eB kA) T as₁ = true) (hA₂ : alphaAll (alpha2OK P rH) T as₂ = true)
    {c₁ H₁ c₂ H₂ : ℚ} (hS₁ : constSum P eB (rH ^ 2) 1 (rH ^ 2) T = some (c₁, H₁))
    (hS₂ : constSum P eB 1 (rH ^ 2) 1 T = some (c₂, H₂))
    {cnum : ℤ} (hc1 : (cnum : ℚ) ≤ (c₁ + c₂) * 2 ^ P) (hc2 : (c₁ + c₂) * 2 ^ P < cnum + 1) (n : ℕ) :
    AngularSource.Binning (S.gas Sign.neg) ((binsY T).map reflectL) ∧
    ∑ j ∈ Finset.range (n + 1),
      |AngularCap.gasA S Sign.neg i ((binsY T).map reflectL) j -
        (((glFastNeg P as₁ as₂ (T.map BD.s0) cnum n).getD j 0 : ℤ) : ℝ) / ((2 ^ P : ℕ) : ℝ)| ≤
      (((1 / 2 ^ P + H₁ + H₂) + n * (cb1 P eA eB kA rH T + cb2 P eA eB rH T) : ℚ) : ℝ) := by
  have hl₁ := alphaAll_len hA₁
  have hl₂ := alphaAll_len hA₂
  have hcells₁ := recsOf_cells hl₁
  have hcells₂ := recsOf_cells hl₂
  have hk₁ := const1_err hR hl₁ hM hS₁
  have hk₂ := const2_err hR hl₂ hM hS₂
  have hf := floor_err hc1 hc2
  have hk₁' : |((cnum : ℝ) / 2 ^ P - (c₂ : ℝ)) - constTrue ((S.rad i) ^ 2) 1 (recsOf T as₁)| ≤
      1 / 2 ^ P + (H₁ : ℝ) := by
    push_cast at hf
    rw [abs_le] at hk₁ hf ⊢
    constructor <;> linarith [hk₁.1, hk₁.2, hf.1, hf.2]
  have h := GasCert.gasCert_neg S (recs₁ := recsOf T as₁) (recs₂ := recsOf T as₂) i
    (by rw [hcells₁]; exact hp) (by rw [hcells₁, hcells₂]) hg hw (n := n) (P := P)
    (δ₁ := delta1 P eA eB kA rH) (δ₂ := delta2 P eA eB rH)
    (recOK_family1 hR hM hA₁) (recOK_family2 hR hM hA₂) cnum hk₁' hk₂ (by ring)
  rw [hcells₁, ← glFastNeg_eq P _ _ (by rw [recsOf_s0 hl₁, recsOf_s0 hl₂]), recsOf_a hl₁, recsOf_a hl₂,
    recsOf_s0 hl₁, coefBudget1 hl₁ hM, coefBudget2 hl₂ hM] at h
  refine ⟨h.1, ?_⟩
  push_cast at h ⊢
  exact h.2

/-! ### Boolean front ends: explicit error `eG` -/

/-- kernel 1 constant check at the positive species: `cnum = floor (c 2^P)`, error `<= Hb`. -/
def constOKpos (P : ℕ) (eB rH Hb : ℚ) (T : List BD) (cnum : ℤ) : Bool :=
  match constSum P eB (rH ^ 2) 1 (rH ^ 2) T with
  | some (c, H) => decide ((cnum : ℚ) ≤ c * 2 ^ P ∧ c * 2 ^ P < cnum + 1 ∧ H ≤ Hb)
  | none => false

/-- both constants at the negative species: `cnum = floor ((c1 + c2) 2^P)`, errors `<= Hb1, Hb2`. -/
def constOKneg (P : ℕ) (eB rH Hb₁ Hb₂ : ℚ) (T : List BD) (cnum : ℤ) : Bool :=
  match constSum P eB (rH ^ 2) 1 (rH ^ 2) T, constSum P eB 1 (rH ^ 2) 1 T with
  | some (c₁, H₁), some (c₂, H₂) =>
    decide ((cnum : ℚ) ≤ (c₁ + c₂) * 2 ^ P ∧ (c₁ + c₂) * 2 ^ P < cnum + 1 ∧ H₁ ≤ Hb₁ ∧ H₂ ≤ Hb₂)
  | _, _ => false

/-- the explicit gas error, positive species. -/
def eGpos (P n : ℕ) (Hb cb : ℚ) : ℚ := 1 / 2 ^ P + Hb + n * cb
/-- the explicit gas error, negative species. -/
def eGneg (P n : ℕ) (Hb₁ Hb₂ cb₁ cb₂ : ℚ) : ℚ := 1 / 2 ^ P + Hb₁ + Hb₂ + n * (cb₁ + cb₂)

theorem gas_final_pos (S : CapSource) (i : ℕ) {P : ℕ} {eA eB kA rH Hb cb : ℚ} {T : List BD} {as : List ℕ}
    (hp : Partitioned (S.gas Sign.pos) (binsY T)) (hM : ∀ x ∈ T, MomSpec P eA eB x)
    (hR : RadSpec P (S.rad i) rH) (hA : alphaAll (alpha1OK P rH eB kA) T as = true)
    {cnum : ℤ} (hc : constOKpos P eB rH Hb T cnum = true) (hcb : cb1 P eA eB kA rH T ≤ cb) (n : ℕ) :
    AngularSource.Binning (S.gas Sign.pos) (binsY T) ∧
    ∑ j ∈ Finset.range (n + 1),
      |AngularCap.gasA S Sign.pos i (binsY T) j -
        (((glFast P as (T.map BD.s0) cnum n).getD j 0 : ℤ) : ℝ) / ((2 ^ P : ℕ) : ℝ)| ≤
      (eGpos P n Hb cb : ℝ) := by
  unfold constOKpos at hc
  cases hk : constSum P eB (rH ^ 2) 1 (rH ^ 2) T with
  | none => rw [hk] at hc; simp at hc
  | some t =>
    obtain ⟨c, H⟩ := t
    rw [hk] at hc
    simp only [decide_eq_true_eq] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    have hg := gas_cert_pos S i hp hM hR hA hk h1 h2 n
    refine ⟨hg.1, hg.2.trans ?_⟩
    have : (1 / 2 ^ P + H + n * cb1 P eA eB kA rH T : ℚ) ≤ eGpos P n Hb cb := by
      unfold eGpos
      have := mul_le_mul_of_nonneg_left hcb (Nat.cast_nonneg (α := ℚ) n)
      linarith
    exact_mod_cast this

theorem gas_final_neg (S : CapSource) (i : ℕ) {P : ℕ} {eA eB kA rH Hb₁ Hb₂ cbb₁ cbb₂ : ℚ} {T : List BD}
    {as₁ as₂ : List ℕ} (hp : Partitioned (reflectL (S.gas Sign.neg)) (binsY T))
    (hg : ∀ c ∈ S.gas Sign.neg, c.hi ≤ -2) (hw : ∀ c ∈ S.gas Sign.neg, 0 < c.w)
    (hM : ∀ x ∈ T, MomSpec P eA eB x) (hR : RadSpec P (S.rad i) rH)
    (hA₁ : alphaAll (alpha1OK P rH eB kA) T as₁ = true) (hA₂ : alphaAll (alpha2OK P rH) T as₂ = true)
    {cnum : ℤ} (hc : constOKneg P eB rH Hb₁ Hb₂ T cnum = true)
    (hcb₁ : cb1 P eA eB kA rH T ≤ cbb₁) (hcb₂ : cb2 P eA eB rH T ≤ cbb₂) (n : ℕ) :
    AngularSource.Binning (S.gas Sign.neg) ((binsY T).map reflectL) ∧
    ∑ j ∈ Finset.range (n + 1),
      |AngularCap.gasA S Sign.neg i ((binsY T).map reflectL) j -
        (((glFastNeg P as₁ as₂ (T.map BD.s0) cnum n).getD j 0 : ℤ) : ℝ) / ((2 ^ P : ℕ) : ℝ)| ≤
      (eGneg P n Hb₁ Hb₂ cbb₁ cbb₂ : ℝ) := by
  unfold constOKneg at hc
  cases hk₁ : constSum P eB (rH ^ 2) 1 (rH ^ 2) T with
  | none => rw [hk₁] at hc; simp at hc
  | some t₁ =>
    obtain ⟨c₁, H₁⟩ := t₁
    rw [hk₁] at hc
    cases hk₂ : constSum P eB 1 (rH ^ 2) 1 T with
    | none => rw [hk₂] at hc; simp at hc
    | some t₂ =>
      obtain ⟨c₂, H₂⟩ := t₂
      rw [hk₂] at hc
      simp only [decide_eq_true_eq] at hc
      obtain ⟨h1, h2, h3, h4⟩ := hc
      have hc' := gas_cert_neg S i hp hg hw hM hR hA₁ hA₂ hk₁ hk₂ h1 h2 n
      refine ⟨hc'.1, hc'.2.trans ?_⟩
      have : (1 / 2 ^ P + H₁ + H₂ + n * (cb1 P eA eB kA rH T + cb2 P eA eB rH T) : ℚ) ≤
          eGneg P n Hb₁ Hb₂ cbb₁ cbb₂ := by
        unfold eGneg
        have := mul_le_mul_of_nonneg_left (add_le_add hcb₁ hcb₂) (Nat.cast_nonneg (α := ℚ) n)
        linarith
      exact_mod_cast this

/-! ### The concrete source -/

theorem binsY_of_bins {T : List BD} {Q : List (List QC)} (h : T.map BD.pcs = Q) :
    binsY T = Q.map (List.map QC.toY) := by
  rw [← h]; simp [binsY, BD.cells, List.map_map, Function.comp_def]

/-- `hp` of `gas_cert_pos`/`gas_final_pos` on `capSource`. -/
theorem partitioned_pos {K : ℕ} (hK : 0 < K) {Tt : ℤ} (hT : sumP row0 = Tt)
    (hc : cutsOK K Tt (gasT Sign.pos) = true) {T : List BD}
    (hb : T.map BD.pcs = binsQ K Tt (gasT Sign.pos)) :
    Partitioned (capSource.gas Sign.pos) (binsY T) := by
  rw [binsY_of_bins hb]
  exact partitioned_species hK hT Sign.pos hc

/-- `hp` of `gas_cert_neg`/`gas_final_neg` on `capSource`. -/
theorem partitioned_neg {K : ℕ} (hK : 0 < K) {Tt : ℤ} (hT : sumP row0 = Tt)
    (hc : cutsOK K Tt (gasT Sign.neg) = true) {T : List BD}
    (hb : T.map BD.pcs = binsQ K Tt (gasT Sign.neg)) :
    Partitioned (reflectL (capSource.gas Sign.neg)) (binsY T) := by
  rw [binsY_of_bins hb]
  exact partitioned_species hK hT Sign.neg hc

theorem capSource_neg_hi : ∀ c ∈ capSource.gas Sign.neg, c.hi ≤ -2 := gas_neg_hi

/-- `hw` of the negative species (the instance decides `∀ t ∈ gasNegT, 0 < t.2.2`). -/
theorem capSource_neg_w (h : ∀ t ∈ gasNegT, 0 < t.2.2) : ∀ c ∈ capSource.gas Sign.neg, 0 < c.w := by
  intro c hc
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
  have hv := row0_ok t (List.mem_of_mem_filter ht)
  rw [(mkCell_eq (m := 1) hv row0_tot.le zero_le_one).2.2]
  have h1 : (0 : ℝ) < t.2.2 := by exact_mod_cast h t ht
  have h2 : (0 : ℝ) < sumP row0 := by exact_mod_cast row0_tot
  exact div_pos (mul_pos one_pos h1) h2

#print axioms partitioned_species
#print axioms rad_enc
#print axioms momAll_spec
#print axioms gas_cert_pos
#print axioms gas_cert_neg
#print axioms gas_final_pos
#print axioms gas_final_neg
#print axioms glFastNeg_eq

end
end CatalanMeasure.GenD.Signed.RouteI.AngGas

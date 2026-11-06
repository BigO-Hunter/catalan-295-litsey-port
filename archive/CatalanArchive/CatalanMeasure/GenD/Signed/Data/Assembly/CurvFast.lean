module

public import CatalanMeasure.GenD.Signed.Data.Assembly.Curv
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMomMerge
public import CatalanMeasure.Cert.IvEval

@[expose] public section

/-!
# Real tails: `lbNorm` through rational powers

`tailValQ` evaluates a pole through `cpowQ`, a complex power by repeated multiplication, recomputed
for every index. The trial tails have real poles (`zi = 0`), where `cpowQ (zr, 0) k = (zr ^ k, 0)`,
and a rational power is one big-integer power. `lbNorm_real` rewrites `lbNorm` to `lbNormR`, which
uses `zr ^ k`.

The kernel checks of the assembly do not evaluate these sums exactly: `lbNorm_ge`, `lbNorm_ge_same`,
`rbQ_le`, `le_rbQ`, `ipDiffRQ_le` and `le_ipPartQ` bound them through the fixed-point enclosures of
`CatalanMeasure.Cert.IvEval` (scale `3⁸¹`), so each check is one integer comparison against a loop of
small-integer operations.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open CatalanMeasure.Cert CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Cert.Iv
open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef CatalanMeasure.Signed.FieldForm

theorem cpowQ_real (zr : ℚ) : ∀ k : ℕ, cpowQ (zr, 0) k = (zr ^ k, 0)
  | 0 => by simp [cpowQ]
  | k + 1 => by
    rw [cpowQ, cpowQ_real zr k]
    simp [cmulQ, pow_succ]

/-- `tailValQ` of a tail with real poles. -/
def tailValR (tail : List TailQ) (k : ℕ) : ℚ := (tail.map fun t => t.rr * t.zr ^ k).sum

theorem tailValQ_real (tail : List TailQ) (h : ∀ t ∈ tail, t.zi = 0) (k : ℕ) :
    tailValQ tail k = tailValR tail k := by
  unfold tailValQ tailValR
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [h t ht, cpowQ_real]
  simp [cmulQ]

def sqR (s : SeqQ) (k : ℕ) : ℚ := s.f.getD k 0 + tailValR s.tail (k + 1)

def lbNormR (s t : SeqQ) (K : ℕ) : ℚ :=
  ∑ k ∈ Finset.range K, (sqR s k - sqR t k) ^ 2 / ((k : ℚ) + 1)

theorem lbNorm_real {s t : SeqQ} (hs : ∀ x ∈ s.tail, x.zi = 0) (ht : ∀ x ∈ t.tail, x.zi = 0)
    (K : ℕ) : lbNorm s t K = lbNormR s t K := by
  unfold lbNorm lbNormR
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [sqQ, sqR, tailValQ_real _ hs, tailValQ_real _ ht]

/-! ### Bounds through fixed-point enclosures -/

/-- The poles `(z, r)` of a tail with real poles, and with the residues negated. -/
def polesP (l : List TailQ) : List (ℚ × ℚ) := l.map fun x => (x.zr, x.rr)

def polesN (l : List TailQ) : List (ℚ × ℚ) := l.map fun x => (x.zr, -x.rr)

theorem pv_append (a b : List (ℚ × ℚ)) (k : ℕ) : pv (a ++ b) k = pv a k + pv b k := by
  simp [pv]

theorem pv_polesP (l : List TailQ) (k : ℕ) : pv (polesP l) k = tailValR l k := by
  induction l with
  | nil => simp [pv, polesP, tailValR]
  | cons x l ih =>
    simp only [pv, polesP, tailValR, List.map_cons, List.sum_cons] at ih ⊢
    linarith

theorem pv_polesN (l : List TailQ) (k : ℕ) : pv (polesN l) k = -tailValR l k := by
  induction l with
  | nil => simp [pv, polesN, tailValR]
  | cons x l ih =>
    simp only [pv, polesN, tailValR, List.map_cons, List.sum_cons] at ih ⊢
    linarith

theorem ivS2_pos : 0 < ivS * ivS := Nat.mul_pos ivS_pos ivS_pos

/-- The poles of `s − t`. -/
def pdiff (s t : SeqQ) : List (ℚ × ℚ) := polesP s.tail ++ polesN t.tail

theorem lbNormR_eq (s t : SeqQ) (K : ℕ) :
    lbNormR s t K = ∑ k ∈ Finset.range K, useq (dl s.f t.f) (pdiff s t) k ^ 2 / ((k : ℚ) + 1) := by
  unfold lbNormR
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [useq, dl_getD, pdiff, pv_append, pv_polesP, pv_polesN]
  unfold sqR
  ring_nf

def normIv (s t : SeqQ) (K : ℕ) : Iv :=
  seqLoop ivS (pdiff s t) sqDiv K 0 (dl s.f t.f) (initIv ivS (pdiff s t)) zero

theorem enc_normIv (s t : SeqQ) (K : ℕ) :
    Enc ((ivS * ivS : ℕ) : ℚ) (normIv s t K) (lbNormR s t K) := by
  rw [ivS2_cast, lbNormR_eq]
  have h := seqLoop_enc (S := ivS) (S' := (ivS : ℚ) * (ivS : ℚ)) (pdiff s t) sqDiv
    (fun k x => x ^ 2 / ((k : ℚ) + 1)) enc_sqDiv (dl s.f t.f) K 0 _ zero 0
    (polesEnc_init ivS _) (enc_zero _)
  simpa [normIv] using h

/-- `L ≤ lbNorm s t K` from the enclosure `normIv s t K` (tails with real poles). -/
theorem lbNorm_ge {s t : SeqQ} (hs : ∀ x ∈ s.tail, x.zi = 0) (ht : ∀ x ∈ t.tail, x.zi = 0)
    (K : ℕ) (L : ℚ) (hc : L.num * ((ivS * ivS : ℕ) : ℤ) ≤ (normIv s t K).lo * L.den) :
    L ≤ lbNorm s t K := by
  rw [lbNorm_real hs ht]
  exact le_of_enc ivS2_pos (enc_normIv s t K) L hc

theorem lbNorm_same {s t : SeqQ} (h : s.tail = t.tail) (K : ℕ) :
    lbNorm s t K = ∑ k ∈ Finset.range K, useq (dl s.f t.f) [] k ^ 2 / ((k : ℚ) + 1) := by
  unfold lbNorm
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [sqQ, useq, dl_getD, h, pv, List.map_nil, List.sum_nil]
  ring_nf

def normIvS (s t : SeqQ) (K : ℕ) : Iv := seqLoop ivS [] sqDiv K 0 (dl s.f t.f) [] zero

/-- `L ≤ lbNorm s t K` when `s` and `t` have the same tail: only the finite parts enter. -/
theorem lbNorm_ge_same {s t : SeqQ} (h : s.tail = t.tail) (K : ℕ) (L : ℚ)
    (hc : L.num * ((ivS * ivS : ℕ) : ℤ) ≤ (normIvS s t K).lo * L.den) : L ≤ lbNorm s t K := by
  have e := seqLoop_enc (S := ivS) (S' := (ivS : ℚ) * (ivS : ℚ)) [] sqDiv
    (fun k x => x ^ 2 / ((k : ℚ) + 1)) enc_sqDiv (dl s.f t.f) K 0 [] zero 0
    List.Forall₂.nil (enc_zero _)
  rw [← ivS2_cast] at e
  rw [lbNorm_same h]
  exact le_of_enc ivS2_pos (by simpa [normIvS] using e) L hc

/-- The weight `-(-1)^(n+1) R_n / (n + 1)` of `rbQ`. -/
def wt (r : List ℚ) (k : ℕ) : ℚ := -(-1 : ℚ) ^ (k + 1) * r.getD k 0 / ((k : ℚ) + 1)

theorem rbQ_eq (X Y : FamPar) (hY : ∀ x ∈ Y.T.a.tail, x.zi = 0) :
    rbQ X Y = ∑ n ∈ Finset.range X.T.R.f.length, useq Y.T.a.f (polesP Y.T.a.tail) n * wt X.T.R.f n := by
  unfold rbQ
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [useq, pv_polesP, sqQ, tailValQ_real _ hY, wt]
  ring

def rbIv (r : List ℚ) (u : SeqQ) : Iv :=
  seqLoop ivS (polesP u.tail) (fun k I => mulC I (wt r k)) r.length 0 u.f (initIv ivS (polesP u.tail)) zero

theorem enc_rbIv (X Y : FamPar) (hY : ∀ x ∈ Y.T.a.tail, x.zi = 0) :
    Enc (ivS : ℚ) (rbIv X.T.R.f Y.T.a) (rbQ X Y) := by
  rw [rbQ_eq X Y hY]
  have h := seqLoop_enc (S := ivS) (S' := (ivS : ℚ)) (polesP Y.T.a.tail)
    (fun k I => mulC I (wt X.T.R.f k)) (fun k x => x * wt X.T.R.f k) (fun k I x hx => enc_mulC hx _)
    Y.T.a.f X.T.R.f.length 0 _ zero 0 (polesEnc_init ivS _) (enc_zero _)
  simpa [rbIv] using h

theorem rbQ_le (X Y : FamPar) (hY : ∀ x ∈ Y.T.a.tail, x.zi = 0) (U : ℚ)
    (hc : (rbIv X.T.R.f Y.T.a).hi * U.den ≤ U.num * (ivS : ℤ)) : rbQ X Y ≤ U :=
  le_of_enc' ivS_pos (enc_rbIv X Y hY) U hc

theorem le_rbQ (X Y : FamPar) (hY : ∀ x ∈ Y.T.a.tail, x.zi = 0) (L : ℚ)
    (hc : L.num * (ivS : ℤ) ≤ (rbIv X.T.R.f Y.T.a).lo * L.den) : L ≤ rbQ X Y :=
  le_of_enc ivS_pos (enc_rbIv X Y hY) L hc

theorem raQ_eq_rbQ (X : FamPar) : raQ X = rbQ X X := rfl

/-! ### Shared geometric-tail table consumer

The numeric table can be tested independently of the held FamPar assembly.
The bridge here preserves the existing rbQ statement and exact checker.
-/

def rbIvCached (r : List ℚ) (u : SeqQ) (ts : List Iv) : Iv :=
  cachedLoop ivS (fun k I => mulC I (wt r k)) 0 u.f ts zero

theorem rbIvCached_eq (r : List ℚ) (u : SeqQ) (ts : List Iv)
    (ht : ts = tailTable (polesP u.tail) r.length (initIv ivS (polesP u.tail))) :
    rbIvCached r u ts = rbIv r u := by
  rw [rbIvCached, ht, cachedLoop_tailTable]
  rfl

theorem le_rbQ_cached (X Y : FamPar) (hY : ∀ x ∈ Y.T.a.tail, x.zi = 0)
    (ts : List Iv)
    (ht : ts = tailTable (polesP Y.T.a.tail) X.T.R.f.length (initIv ivS (polesP Y.T.a.tail)))
    (L : ℚ) (hc : L.num * (ivS : ℤ) ≤ (rbIvCached X.T.R.f Y.T.a ts).lo * L.den) :
    L ≤ rbQ X Y := by
  apply le_rbQ X Y hY L
  rwa [rbIvCached_eq _ _ _ ht] at hc

/-- Reuse the same two individual tail tables for an A-difference norm. -/
def normIvCached (s t : SeqQ) (a b : List Iv) : Iv :=
  cachedLoop ivS sqDiv 0 (dl s.f t.f) (diffTable a b) zero

theorem enc_normIvCached (s t : SeqQ) (K : ℕ) (a b : List Iv)
    (ha : a = tailTable (polesP s.tail) K (initIv ivS (polesP s.tail)))
    (hb : b = tailTable (polesP t.tail) K (initIv ivS (polesP t.tail))) :
    Enc ((ivS * ivS : ℕ) : ℚ) (normIvCached s t a b) (lbNormR s t K) := by
  have hA : TableEnc (ivS : ℚ) (fun j => pv (polesP s.tail) (j + 1)) 0 a := by
    rw [ha]; exact tailTable_enc _ K 0 _ (polesEnc_init ivS _)
  have hB : TableEnc (ivS : ℚ) (fun j => pv (polesP t.tail) (j + 1)) 0 b := by
    rw [hb]; exact tailTable_enc _ K 0 _ (polesEnc_init ivS _)
  have hlA : a.length = K := by rw [ha, tailTable_length]
  have hlB : b.length = K := by rw [hb, tailTable_length]
  have hl : (diffTable a b).length = K :=
    (diffTable_length a b (hlA.trans hlB.symm)).trans hlA
  have h := cachedLoop_tableEnc (S := ivS) (S' := (ivS : ℚ) * (ivS : ℚ)) sqDiv
    (fun k x => x ^ 2 / ((k : ℚ) + 1)) enc_sqDiv (dl s.f t.f)
    (fun j => pv (polesP s.tail) (j + 1) - pv (polesP t.tail) (j + 1))
    (diffTable a b) 0 zero 0 (tableEnc_diff _ _ a b 0 hA hB) (enc_zero _)
  rw [hl] at h
  rw [ivS2_cast, lbNormR_eq]
  simpa only [normIvCached, useq, pdiff, pv_append, pv_polesP, pv_polesN,
    sub_eq_add_neg, zero_add, Nat.zero_add, List.drop_zero] using h

theorem lbNorm_ge_cached {s t : SeqQ} (hs : ∀ x ∈ s.tail, x.zi = 0)
    (ht : ∀ x ∈ t.tail, x.zi = 0) (K : ℕ) (a b : List Iv)
    (ha : a = tailTable (polesP s.tail) K (initIv ivS (polesP s.tail)))
    (hb : b = tailTable (polesP t.tail) K (initIv ivS (polesP t.tail)))
    (L : ℚ) (hc : L.num * ((ivS * ivS : ℕ) : ℤ) ≤ (normIvCached s t a b).lo * L.den) :
    L ≤ lbNorm s t K := by
  rw [lbNorm_real hs ht]
  exact le_of_enc ivS2_pos (enc_normIvCached s t K a b ha hb) L hc

/-! ### Moments of a single-piece reference -/

theorem momAux_one_zero (k : ℕ) : ∀ (l : List ℚ) (j : ℕ), momAux 1 0 k j l = mom1 l (j + k + 1)
  | [], j => by simp [momAux, mom1]
  | x :: xs, j => by
    rw [momAux, momAux_one_zero k xs (j + 1), mom1, one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero,
      mul_one, show j + 1 + k + 1 = j + k + 1 + 1 by omega]

theorem mposQ_single (R : RefQ) (p : List ℚ) (h1 : R.pT = [⟨0, 1, p⟩]) (h2 : R.nT = []) (n : ℕ) :
    mposQ R n = mom1 p (n + 2) := by
  rw [mposQ, h1, h2]
  simp only [sumMom, momQ, momAux_one_zero, add_zero, sub_zero]
  exact congrArg (mom1 p) (by omega)

theorem ipDiffRQ_single {R S : RefQ} {p q : List ℚ} (h1 : R.pT = [⟨0, 1, p⟩]) (h2 : R.nT = [])
    (h3 : S.pT = [⟨0, 1, q⟩]) (h4 : S.nT = []) (K : ℕ) :
    ipDiffRQ R S K = ∑ n ∈ Finset.range K, mom1 (dl p q) (n + 2) ^ 2 / ((n : ℚ) + 1) := by
  unfold ipDiffRQ
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mposQ_single R p h1 h2, mposQ_single S q h3 h4, mom1_dl]

def ipDiffIv (p q : List ℚ) (K : ℕ) : Iv := momLoop sqDiv (fun n => momIv ivS (dl p q) (n + 2)) K 0 zero

theorem ipDiffRQ_le {R S : RefQ} {p q : List ℚ} (h1 : R.pT = [⟨0, 1, p⟩]) (h2 : R.nT = [])
    (h3 : S.pT = [⟨0, 1, q⟩]) (h4 : S.nT = []) (K : ℕ) (U : ℚ)
    (hc : (ipDiffIv p q K).hi * U.den ≤ U.num * ((ivS * ivS : ℕ) : ℤ)) : ipDiffRQ R S K ≤ U := by
  have h := momLoop_enc (S := (ivS : ℚ)) (S' := (ivS : ℚ) * (ivS : ℚ)) sqDiv
    (fun k x => x ^ 2 / ((k : ℚ) + 1)) enc_sqDiv (fun n => momIv ivS (dl p q) (n + 2))
    (fun n => mom1 (dl p q) (n + 2)) (fun n => enc_momIv ivS _ (by omega)) K 0 zero 0 (enc_zero _)
  rw [← ivS2_cast] at h
  rw [ipDiffRQ_single h1 h2 h3 h4]
  exact le_of_enc' ivS2_pos (by simpa [ipDiffIv] using h) U hc

def ipPartIv (p : List ℚ) (K : ℕ) : Iv := momLoop sqDiv (fun n => momIv ivS p (n + 2)) K 0 zero

theorem le_ipPartQ {R : RefQ} {p : List ℚ} (h1 : R.pT = [⟨0, 1, p⟩]) (h2 : R.nT = []) (K : ℕ) (L : ℚ)
    (hc : L.num * ((ivS * ivS : ℕ) : ℤ) ≤ (ipPartIv p K).lo * L.den) : L ≤ ipPartQ R K := by
  have h := momLoop_enc (S := (ivS : ℚ)) (S' := (ivS : ℚ) * (ivS : ℚ)) sqDiv
    (fun k x => x ^ 2 / ((k : ℚ) + 1)) enc_sqDiv (fun n => momIv ivS p (n + 2))
    (fun n => mom1 p (n + 2)) (fun n => enc_momIv ivS _ (by omega)) K 0 zero 0 (enc_zero _)
  rw [← ivS2_cast] at h
  have e : ipPartQ R K = ∑ n ∈ Finset.range K, mom1 p (n + 2) ^ 2 / ((n : ℚ) + 1) := by
    unfold ipPartQ
    exact Finset.sum_congr rfl fun n _ => by rw [mposQ_single R p h1 h2]
  rw [e]
  exact le_of_enc ivS2_pos (by simpa [ipPartIv] using h) L hc

end CatalanMeasure.GenD.Signed.Data.Assembly

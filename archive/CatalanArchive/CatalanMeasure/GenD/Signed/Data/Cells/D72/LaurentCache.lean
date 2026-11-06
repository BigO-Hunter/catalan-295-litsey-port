module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells.LaurentCache
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval
open scoped BigOperators

/-- Factorial-free exact coefficients. Each coefficient is checked once, before convolution. -/
def zBinomAux : Nat → List ℚ → ℚ → Nat → ℚ
  | _, [], _, _ => 0
  | s, a :: as, c, k =>
      a * ((-1)^k * (invBinom s k : ℚ) / c^(s+k)) + zBinomAux (s+1) as c k

theorem zBinomAux_eq (a : List ℚ) (s k : Nat) (c : ℚ) :
    zBinomAux s a c k = zHatAux s a c k := by
  induction a generalizing s with
  | nil => rfl
  | cons a as ih =>
      simp only [zBinomAux, zHatAux, ih, invBinom_asc]
      ring

/-- A finite cache must contain every requested coefficient; missing entries never pass. -/
def tableOK (n : Nat) (xs : List ℚ) (f : Nat → ℚ) : Bool :=
  decide (xs.length = n) && (List.range n).all (fun k => decide (xs.getD k 0 = f k))

theorem tableOK_spec {n : Nat} {xs : List ℚ} {f : Nat → ℚ}
    (h : tableOK n xs f = true) {k : Nat} (hk : k < n) : xs.getD k 0 = f k := by
  simp only [tableOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact of_decide_eq_true ((List.all_eq_true.mp h.2) k (List.mem_range.mpr hk))

theorem convQ_congr_upto (u v u' v' : Nat → ℚ) (k n : Nat) (hn : n ≤ k+1)
    (hu : ∀ i, i ≤ k → u i = u' i) (hv : ∀ i, i ≤ k → v i = v' i) :
    convQ u v k n = convQ u' v' k n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [convQ, convQ, ih (by omega), hu n (by omega), hv (k-n) (Nat.sub_le _ _)]

/-- Linear checked recurrence for the complete positive infinite remainder R. -/
def rTableOK (K : Nat) (q : ℚ) (rs : Nat → ℚ) (n : Nat) : Prop :=
  rs 0 = 0 ∧ ∀ s, s < n → rs (s+1) = (rs s + (invBinom (s+1) K : ℚ)*q^(K+1))/(1-q)

theorem rTable_spec {K n : Nat} {q : ℚ} {rs : Nat → ℚ}
    (h : rTableOK K q rs n) : ∀ s, s ≤ n → rs s = invTailPosQ K q s := by
  intro s hs
  induction s with
  | zero => exact h.1
  | succ s ih => rw [h.2 s (by omega), invTailPosQ, ih (by omega)]

theorem jTable_spec {K n s : Nat} {q : ℚ} {rs : Nat → ℚ}
    (h : rTableOK K q rs n) (hs : s+1 ≤ n) :
    q*(rs (s+1)+(invBinom (s+1) K : ℚ)*q^K) = logInvTailQ s K q := by
  rw [rTable_spec h (s+1) hs]
  rfl

def rCheck (K : Nat) (q : ℚ) (xs : List ℚ) (n : Nat) : Bool :=
  decide (xs.length = n+1) && decide (xs.getD 0 0 = 0) &&
    (List.range n).all (fun s => decide (xs.getD (s+1) 0 =
      (xs.getD s 0 + (invBinom (s+1) K : ℚ)*q^(K+1))/(1-q)))

theorem rCheck_spec {K n : Nat} {q : ℚ} {xs : List ℚ}
    (h : rCheck K q xs n = true) : rTableOK K q (fun i => xs.getD i 0) n := by
  simp only [rCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, fun s hs => of_decide_eq_true
    ((List.all_eq_true.mp h.2) s (List.mem_range.mpr hs))⟩

def tailSum (c : ℚ) (f : Nat → ℚ) : Nat → List ℚ → ℚ
  | _, [] => 0
  | s, a :: as => qabs' a/(qabs' c)^s*f s + tailSum c f (s+1) as

theorem tailSum_congr (c : ℚ) (f g : Nat → ℚ) (a : List ℚ) (s : Nat)
    (h : ∀ i, s ≤ i → i < s+a.length → f i = g i) :
    tailSum c f s a = tailSum c g s a := by
  induction a generalizing s with
  | nil => rfl
  | cons a as ih =>
      rw [tailSum, tailSum, h s (by omega) (by simp)]
      rw [ih (s+1) (by intro i hi hi'; apply h i (by omega); simp only [List.length_cons]; omega)]

theorem invMajTail_sum (c q : ℚ) (K : Nat) (a : List ℚ) (s : Nat) :
    invMajTail c q K s a = tailSum c (invTailPosQ K q) s a := by
  induction a generalizing s with
  | nil => rfl
  | cons a as ih => simp only [invMajTail, tailSum, ih]

theorem geoMajTail_sum (c q L : ℚ) (K : Nat) (a : List ℚ) (s : Nat) :
    geoMajTail c q L K s a = tailSum c (fun i => geoInvTail i K L q) s a := by
  induction a generalizing s with
  | nil => rfl
  | cons a as ih => simp only [geoMajTail, tailSum, ih]

def coarse (c q L : ℚ) (K : Nat) (t : LTerm) (rs : Nat → ℚ) : ℚ :=
  match t.2 with
  | none => tailSum c rs 0 t.1
  | some ab => if ab.1 = 0 then L*tailSum c rs 0 t.1 else
      tailSum c (fun s => L*rs s + q*(rs (s+1)+(invBinom (s+1) K : ℚ)*q^K)) 0 t.1

theorem coarse_eq (c q L : ℚ) (K : Nat) (t : LTerm) (rs : Nat → ℚ)
    (h : ∀ i, i ≤ t.1.length → rs i = invTailPosQ K q i) :
    coarse c q L K t rs = laurentCoarseTail c q L K t := by
  rcases t with ⟨a,o⟩
  change (∀ i, i ≤ a.length → rs i = invTailPosQ K q i) at h
  cases o with
  | none =>
      simp only [coarse, laurentCoarseTail, invMajTail_sum]
      exact tailSum_congr c _ _ a 0 (by intro i hi hi'; apply h i; omega)
  | some ab =>
      simp only [coarse, laurentCoarseTail]
      split_ifs with ha
      · rw [invMajTail_sum]
        congr 1
        exact tailSum_congr c _ _ a 0 (by intro i hi hi'; apply h i; omega)
      · rw [geoMajTail_sum]
        apply tailSum_congr
        intro i hi hi'
        rw [h i (by omega), h (i+1) (by omega)]
        rfl

theorem coef_eq {t : LTerm} {c L : ℚ} {Z H : Nat → ℚ} {k : Nat}
    (hz : ∀ i, i ≤ k → Z i = zHat t.1 c i)
    (hh : ∀ i, i ≤ k → H i = lfHat t.2 c L i) :
    convQ Z H k (k+1) = lTermCoef t c L k :=
  convQ_congr_upto _ _ _ _ k (k+1) (by omega) hz hh

theorem fine_eq {t : LTerm} {c q0 qL L : ℚ} {U V : Nat → ℚ} {k : Nat}
    (hu : ∀ i, i ≤ k → U i = invMajAux c q0 0 t.1 i)
    (hv : ∀ i, i ≤ k → V i = lfMaj t.2 L qL i) :
    convQ U V k (k+1) = laurentFineCoef c q0 qL L t k :=
  convQ_congr_upto _ _ _ _ k (k+1) (by omega) hu hv

/-- The cached expression keeps the original geometry/log checks and full coarse tail. -/
def apx (nL M P : Nat) (c r : ℚ) (t : LTerm) (d : LaurentPieceData)
    (Z C F : Nat → ℚ) (coarse : ℚ) : Option (List ℚ × ℚ) :=
  if laurentGeom c r M t d && llogsCheck nL c [t] [(d.L,d.eps)] then
    some ((List.range (M+1)).map (fun k => dyRound P (C k)),
      (∑ k ∈ Finset.range (M+1),
        (lEps t.2 d.eps*qabs' (Z k) + qabs' (C k-dyRound P (C k)))*r^k) +
      ((∑ k ∈ Finset.Ico (M+1) (d.K+1), F k) + coarse))
  else none

theorem apx_eq {nL M P : Nat} {c r : ℚ} {t : LTerm} {d : LaurentPieceData}
    {Z C F : Nat → ℚ} {coarse : ℚ}
    (hz : ∀ k, k ≤ M → Z k = zHat t.1 c k)
    (hc : ∀ k, k ≤ M → C k = lTermCoef t c d.L k)
    (hf : ∀ k, k ∈ Finset.Ico (M+1) (d.K+1) →
      F k = laurentFineCoef c d.q0 (laurentQL t d) (qabs' d.L+d.eps) t k)
    (ht : coarse = laurentCoarseTail c (max d.q0 (laurentQL t d)) (qabs' d.L+d.eps) d.K t) :
    apx nL M P c r t d Z C F coarse = laurentApx nL M P c r t d := by
  have hp : (List.range (M+1)).map (fun k => dyRound P (C k)) = laurentPoly t c d.L M P := by
    apply List.map_congr_left
    intro k hk
    rw [hc k (by simpa only [List.mem_range, Nat.lt_succ_iff] using hk)]
  have he : (∑ k ∈ Finset.range (M+1),
      (lEps t.2 d.eps*qabs' (Z k) + qabs' (C k-dyRound P (C k)))*r^k) =
      laurentCoeffErr t c d.L d.eps r M P := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ M := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    rw [hz k hk', hc k hk']
  have hf' : (∑ k ∈ Finset.Ico (M+1) (d.K+1), F k) =
      ∑ k ∈ Finset.Ico (M+1) (d.K+1),
        laurentFineCoef c d.q0 (laurentQL t d) (qabs' d.L+d.eps) t k := by
    exact Finset.sum_congr rfl hf
  simp only [apx, laurentApx, hp, he, hf', ht, laurentTail]

#print axioms rCheck_spec
#print axioms tailSum_congr
#print axioms invMajTail_sum
#print axioms geoMajTail_sum
#print axioms coarse_eq
#print axioms coef_eq
#print axioms fine_eq
#print axioms zBinomAux_eq
#print axioms tableOK_spec
#print axioms convQ_congr_upto
#print axioms rTable_spec
#print axioms jTable_spec
#print axioms apx_eq
end CatalanMeasure.GenD.Signed.Data.Cells.LaurentCache

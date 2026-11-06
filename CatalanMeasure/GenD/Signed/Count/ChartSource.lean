module

public import CatalanMeasure.GenD.Signed.Count.PrefixSource
public import CatalanMeasure.GenD.Signed.Count.SourceTemplate

@[expose] public section
set_option Elab.async false

/-!
# Count layer: charts from finite data

A `Spec` is the finite description of a source chart: level windows with affine orders, row labels,
and the constant subspace as an integer matrix.  A `Cnt` is the finite description of one count piece:
rank certificates and a relation.  `Spec.Check` and `Cnt.ok` are Booleans on this data.

Fixed rows are integer combinations of coordinates.  Raw rows are not data: a raw label evaluates to
the actual source covector `labelRow` of the physical profile, so the response clause holds by
construction and no moment value, raw identity or reduction mod `p` is needed.  The count uses only
upper bounds for ranks, which a certificate gives by vanishing on independent vectors.

* `chartHost`: the physical host at every `(N, p)` of the window.
* `pieceBound_of_check`: `S.Check` and `C.ok S` give `PieceBound S.P (C.piece S) S.W.N1`.
* `exists_countLB_of_checks`: a list of checked pieces gives a `countLB`.
-/

namespace CatalanMeasure.GenD.Signed.Count.ChartSource
open Finset Module Polynomial Decay2ScalarJetHost CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Signed.Count.DualRestriction
  CatalanMeasure.GenD.Signed.Count.PrefixSource CatalanMeasure.GenD.Signed.Count.Relations
  CatalanMeasure.GenD.Signed.Count.NullityConstructor
noncomputable section

/-! ### Affine forms on a window -/

/-- The affine form `c + n N + h hp`, with `hp = (p - 1) / 2`. -/
structure Form where
  c : ℤ
  n : ℤ
  h : ℤ
  deriving DecidableEq

namespace Form
def ev (f : Form) (N hp : ℕ) : ℤ := f.c + f.n * N + f.h * hp
def add (f g : Form) : Form := ⟨f.c + g.c, f.n + g.n, f.h + g.h⟩
def sub (f g : Form) : Form := ⟨f.c - g.c, f.n - g.n, f.h - g.h⟩
def smul (z : ℤ) (f : Form) : Form := ⟨z * f.c, z * f.n, z * f.h⟩
def z : Form := ⟨0, 0, 0⟩
def one (c : ℤ) : Form := ⟨c, 0, 0⟩
def lin (a : ℤ) : Form := ⟨0, a, 0⟩
def hp : Form := ⟨0, 0, 1⟩
def pp : Form := ⟨1, 0, 2⟩

@[simp] theorem ev_add (f g : Form) (N k : ℕ) : (add f g).ev N k = f.ev N k + g.ev N k := by
  simp only [ev, add]; ring
@[simp] theorem ev_sub (f g : Form) (N k : ℕ) : (sub f g).ev N k = f.ev N k - g.ev N k := by
  simp only [ev, sub]; ring
@[simp] theorem ev_smul (a : ℤ) (f : Form) (N k : ℕ) : (smul a f).ev N k = a * f.ev N k := by
  simp only [ev, smul]; ring
@[simp] theorem ev_z (N k : ℕ) : z.ev N k = 0 := by simp [ev, z]
@[simp] theorem ev_one (c : ℤ) (N k : ℕ) : (one c).ev N k = c := by simp [ev, one]
@[simp] theorem ev_lin (a : ℤ) (N k : ℕ) : (lin a).ev N k = a * N := by simp [ev, lin]
@[simp] theorem ev_hp (N k : ℕ) : hp.ev N k = k := by simp [ev, hp]
@[simp] theorem ev_pp (N k : ℕ) : pp.ev N k = 2 * k + 1 := by simp [ev, pp]; ring
end Form

/-- A window `aN/aD ≤ p/N ≤ bN/bD` past the threshold `N1`. -/
structure Win where
  aN : ℤ
  aD : ℤ
  bN : ℤ
  bD : ℤ
  N1 : ℕ
  deriving DecidableEq

/-- `(N, hp)` lies in the window, with `p = 2 hp + 1`. -/
def Win.Mem (W : Win) (N k : ℕ) : Prop :=
  W.N1 ≤ N ∧ W.aN * N ≤ W.aD * (2 * k + 1) ∧ W.bD * (2 * k + 1) ≤ W.bN * N

/-- The window check of `0 ≤ f`: the two rays are nondecreasing and nonnegative at the threshold. -/
def Win.nn (W : Win) (f : Form) : Bool :=
  let A := 2 * f.c - f.h
  let Bn := 2 * f.n
  let G := f.h
  decide (0 < W.aD) && decide (0 < W.bD) &&
  decide (0 ≤ Bn * W.aD + G * W.aN) && decide (0 ≤ (Bn * W.aD + G * W.aN) * W.N1 + A * W.aD) &&
  decide (0 ≤ Bn * W.bD + G * W.bN) && decide (0 ≤ (Bn * W.bD + G * W.bN) * W.N1 + A * W.bD)

theorem Win.nn_sound {W : Win} {f : Form} (h : W.nn f = true) {N k : ℕ} (hm : W.Mem N k) :
    0 ≤ f.ev N k := by
  obtain ⟨h1, h2, h3⟩ := hm
  simp only [Win.nn, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨ha, hb⟩, r1⟩, r2⟩, r3⟩, r4⟩ := h
  have hN : (W.N1 : ℤ) ≤ N := by exact_mod_cast h1
  have key : 2 * f.ev N k = (2 * f.c - f.h) + 2 * f.n * N + f.h * (2 * k + 1) := by
    simp only [Form.ev]; ring
  by_cases hG : 0 ≤ f.h
  · have e1 : f.h * (W.aN * N) ≤ f.h * (W.aD * (2 * k + 1)) := mul_le_mul_of_nonneg_left h2 hG
    have e2 : (2 * f.n * W.aD + f.h * W.aN) * W.N1 ≤ (2 * f.n * W.aD + f.h * W.aN) * N :=
      mul_le_mul_of_nonneg_left hN r1
    have e3 : 0 ≤ W.aD * (2 * f.ev N k) := by
      rw [key]; nlinarith
    nlinarith [(mul_nonneg_iff_of_pos_left ha).mp e3]
  · have hG' : f.h ≤ 0 := by omega
    have e1 : f.h * (W.bN * N) ≤ f.h * (W.bD * (2 * k + 1)) :=
      mul_le_mul_of_nonpos_left h3 hG'
    have e2 : (2 * f.n * W.bD + f.h * W.bN) * W.N1 ≤ (2 * f.n * W.bD + f.h * W.bN) * N :=
      mul_le_mul_of_nonneg_left hN r3
    have e3 : 0 ≤ W.bD * (2 * f.ev N k) := by
      rw [key]; nlinarith
    nlinarith [(mul_nonneg_iff_of_pos_left hb).mp e3]

/-- `g ≤ f` on the window. -/
def Win.ge (W : Win) (f g : Form) : Bool := W.nn (f.sub g)

theorem Win.ge_sound {W : Win} {f g : Form} (h : W.ge f g = true) {N k : ℕ} (hm : W.Mem N k) :
    g.ev N k ≤ f.ev N k := by
  have := Win.nn_sound h hm
  simpa using this

/-! ### Row labels -/

/-- Chart coordinates: blocks `(k, u)`, `u = A_F, A_E, C_F, C_E`, the centre, the extras. -/
inductive Co
  | blk (k u : ℕ)
  | cen (z : ℕ)
  | ext (t : ℕ)
  deriving DecidableEq

/-- Row labels. -/
inductive Lab
  /-- A coordinate. -/
  | c (x : Co)
  /-- The prefix combination `F - 2 E`. -/
  | minus (F E : Co)
  /-- Bottom virtual combination, part `u` (`0 = F`, `1 = E`). -/
  | vbot (u : ℕ)
  /-- Top virtual combination, part `u`. -/
  | vtop (u : ℕ)
  /-- Source row of the label `(J, S0 - s)` minus `low`. -/
  | raw (J s : ℕ)
  /-- The source row minus `low` minus the graph coordinate `t`. -/
  | graph (J s t : ℕ)
  deriving DecidableEq

inductive PtD
  | zero | inf | plus | minus
  deriving DecidableEq

def PtD.pt : PtD → Pt
  | .zero => .zero | .inf => .inf | .plus => .plus | .minus => .minus

/-- A jet level: orders `[lo, hi)` at a point, with its rows. -/
structure Level where
  pt : PtD
  lo : Form
  hi : Form
  rows : List Lab
  deriving DecidableEq

/-- The finite description of a chart. -/
structure Spec where
  P : Parameters
  b : ℕ
  ex : ℕ
  m : ℕ
  S0 : ℤ
  k0 : ℤ
  k1 : ℤ
  Jlo : ℕ
  Jhi : ℕ
  /-- Coordinates as integer rows on `Fin m` (the constant subspace), position-major. -/
  zs : List (List ℤ)
  /-- The diagonal block of `zs`: the coordinate of the `i`-th basis vector. -/
  sel : List Co
  levels : List Level
  /-- The graph coordinates beyond `jet_0`: `t + 1` belongs to the raw label `aux[t]`. -/
  aux : List (ℕ × ℕ)
  lowA : Bool
  botLow : Bool
  topLow : Bool
  W : Win

namespace Spec
variable (S : Spec)

def pos : Co → ℕ
  | .blk k u => 4 * k + u
  | .cen z => 4 * S.b + z
  | .ext t => 4 * S.b + 2 + t

def zrow (x : Co) : List ℤ := S.zs.getD (S.pos x) []

/-- The chart's total coordinate count. -/
def K : ℕ := S.b * 4 + 2 + S.ex

def fH : Form := .lin (S.P.n0 + S.P.b0 + S.P.q0 + S.P.g0 + S.P.h0)
def fL : Form := .lin (S.P.n0 + S.P.b0 + S.P.q0)
def fb : Form := .lin S.P.b0
def fq : Form := .lin S.P.q0
def fg : Form := .lin S.P.g0
def fh : Form := .lin S.P.h0
def fn : Form := .lin S.P.n0

/-- `ja = -g - k0 p`. -/
def fja : Form := (Form.smul (-1) S.fg).sub (Form.smul S.k0 Form.pp)
/-- `rho = n - 1 - g - k1 p`. -/
def frho : Form := ((S.fn.sub (Form.one 1)).sub S.fg).sub (Form.smul S.k1 Form.pp)

/-- The order reached at a point for a label, walking the levels from `cur`. -/
def reach (pt : PtD) (l : Lab) : List Level → Form → Form
  | [], cur => cur
  | v :: t, cur =>
    reach pt l t (if v.pt = pt ∧ v.lo = cur ∧ l ∈ v.rows then v.hi else cur)

/-- The order of a label at a point. -/
def ord (pt : PtD) (l : Lab) : Form := reach pt l S.levels .z

/-- The label has order at least `n` at the point. -/
def has (pt : PtD) (l : Lab) (n : Form) : Bool := S.W.ge (S.ord pt l) n

/-- The label is killed on coefficients `≥ s`, read at infinity. -/
def top (l : Lab) (s : Form) : Bool := S.has .inf l (Form.pp.sub s)

end Spec

section Chart
variable (S : Spec) {p : ℕ} [Fact p.Prime]

/-- The coordinate functional on the constant space. -/
def cf (x : Co) : (Fin S.m → ZMod p) →ₗ[ZMod p] ZMod p :=
  ∑ j : Fin S.m, (((S.zrow x).getD j.val 0 : ℤ) : ZMod p) • LinearMap.proj j

/-- Chart coordinate of a profile index. -/
def coOf {b ex : ℕ} : CK b ex → Co
  | .inl (k, u) => .blk k.val u.val
  | .inr (.inl z) => .cen z.val
  | .inr (.inr t) => .ext t.val

variable {P : Parameters} {N : ℕ}

/-- The insertion of the constant space. -/
def insZ {b : ℕ} (hK : S.K = b * 4 + 2 + S.ex) :
    (Fin S.m → ZMod p) →ₗ[ZMod p] (Fin S.K → ZMod p) :=
  LinearMap.pi fun idx => cf S (coOf (ckEquiv hK idx))

theorem crd_insZ (hK : S.K = bN P N p * 4 + 2 + S.ex) (i : CK (bN P N p) S.ex) :
    crd hK (insZ S hK) i = cf S (coOf i) := by
  ext v
  simp [crd, insZ]

/-- The value of a label as a functional. -/
def Lab.eval (hK : S.K = bN P N p * 4 + 2 + S.ex) :
    Lab → ((Fin S.m → ZMod p) →ₗ[ZMod p] ZMod p)
  | .c x => cf S x
  | .minus F E => cf S F - (2 : ZMod p) • cf S E
  | .vbot u => cf S (.blk 0 u) - cf S (.blk 0 (u + 2)) + cf S (.cen u)
  | .vtop u => cf S (.blk (S.b - 1) u) + cf S (.blk (S.b - 1) (u + 2))
  | .raw J s => labelRow hK (insZ S hK) 0 J (S.S0 - s) - cf S (.ext 0)
  | .graph J s t => labelRow hK (insZ S hK) 0 J (S.S0 - s) - cf S (.ext 0) - cf S (.ext t)

variable (hK : S.K = bN P N p * 4 + 2 + S.ex)

/-- The chart maps, one per level. -/
def Bm (c : Fin S.levels.length) :
    (Fin S.m → ZMod p) →ₗ[ZMod p] (Fin (S.levels.get c).rows.length → ZMod p) :=
  LinearMap.pi fun i => Lab.eval S hK ((S.levels.get c).rows.get i)

/-- The start of a level at `(N, hp)`. -/
def loN (k : ℕ) (c : Fin S.levels.length) : ℕ := ((S.levels.get c).lo.ev N k).toNat

/-- The width of a level. -/
def wdN (k : ℕ) (c : Fin S.levels.length) : ℕ :=
  ((S.levels.get c).hi.ev N k).toNat - ((S.levels.get c).lo.ev N k).toNat

/-- The chart jets, one window per level. -/
def lamC (k : ℕ) (c : Fin S.levels.length) :
    Fin (wdN S (N := N) k c) → Fin p → ZMod p :=
  fun t => jetLam p (S.levels.get c).pt.pt (loN S (N := N) k c + t.val)

/-- A row of a level is killed along its window. -/
theorem killed_level (k : ℕ) {v : Level} (hv : v ∈ S.levels) {l : Lab} (hl : l ∈ v.rows) {t : ℕ}
    (h1 : (v.lo.ev N k).toNat ≤ t) (h2 : t < (v.hi.ev N k).toNat) :
    Killed (Bm S hK) (lamC S (N := N) (p := p) k) (Lab.eval S hK l) (jetLam p v.pt.pt t) := by
  obtain ⟨c, rfl⟩ := List.get_of_mem hv
  obtain ⟨i, rfl⟩ := List.get_of_mem hl
  refine killed_of_rowsAt (mem_rowsAt_of_flag c _ (loN S (N := N) k c) (fun _ => rfl) ?_ h1 ?_)
  · exact ⟨LinearMap.proj i, by ext x; simp [Bm]⟩
  · have : wdN S (N := N) k c = _ := rfl
    simp only [loN, wdN]
    omega

/-- The levels certify a label up to its reached order. -/
theorem killed_reach (k : ℕ) (pt : PtD) (l : Lab) (ls : List Level) (hls : ∀ v ∈ ls, v ∈ S.levels)
    (cur : Form)
    (h : ∀ t < (cur.ev N k).toNat,
      Killed (Bm S hK) (lamC S (N := N) (p := p) k) (Lab.eval S hK l) (jetLam p pt.pt t)) :
    ∀ t < ((Spec.reach pt l ls cur).ev N k).toNat,
      Killed (Bm S hK) (lamC S (N := N) (p := p) k) (Lab.eval S hK l) (jetLam p pt.pt t) := by
  induction ls generalizing cur with
  | nil => exact h
  | cons v w ih =>
    refine ih (fun u hu => hls u (List.mem_cons_of_mem _ hu)) _ ?_
    by_cases hc : v.pt = pt ∧ v.lo = cur ∧ l ∈ v.rows
    · rw [if_pos hc]
      obtain ⟨h1, h2, h3⟩ := hc
      intro t ht
      by_cases hlt : t < (cur.ev N k).toNat
      · exact h t hlt
      · subst h1
        subst h2
        exact killed_level S hK k (hls v List.mem_cons_self) h3 (by omega) ht
    · rw [if_neg hc]
      exact h

theorem killed_ord (k : ℕ) (pt : PtD) (l : Lab) {t : ℕ}
    (ht : t < ((S.ord pt l).ev N k).toNat) :
    Killed (Bm S hK) (lamC S (N := N) (p := p) k) (Lab.eval S hK l) (jetLam p pt.pt t) :=
  killed_reach S hK k pt l S.levels (fun _ h => h) .z (by simp) t ht

end Chart

/-! ### The finite checks -/

namespace Spec
variable (S : Spec)

/-- Geometry of the cell: quotients of the design at `p`. -/
def geoOK : Bool :=
  decide (Admissible S.P) && decide (1 ≤ S.W.N1) &&
  decide (S.W.aD ≤ S.W.aN) &&
  S.W.ge (Form.pp.sub (.one 1)) S.fq && S.W.ge (Form.pp.sub (.one 1)) S.fh &&
  S.W.ge (Form.smul (-1) S.fg) (Form.smul S.k0 Form.pp) &&
  S.W.ge ((Form.smul (S.k0 + 1) Form.pp).sub (.one 1)) (Form.smul (-1) S.fg) &&
  S.W.ge ((S.fn.sub (.one 1)).sub S.fg) (Form.smul S.k1 Form.pp) &&
  S.W.ge ((Form.smul (S.k1 + 1) Form.pp).sub (.one 1)) ((S.fn.sub (.one 1)).sub S.fg) &&
  decide ((S.b : ℤ) = S.k1 - S.k0 + 1) && decide (0 < S.b) &&
  S.W.ge (S.fH.sub (.one 1)) (Form.smul S.S0 Form.pp) &&
  S.W.ge ((Form.smul (S.S0 + 1) Form.pp).sub (.one 1)) (S.fH.sub (.one 1)) &&
  S.W.ge S.fb (Form.smul S.Jlo Form.pp) &&
  S.W.ge (Form.smul (S.Jhi + 1) Form.pp) S.fL

/-- The coordinate row is zero. -/
def zeroCo (x : Co) : Bool := (S.zrow x).all (· = 0)

def aOK (F E : Co) : Bool :=
  (if S.lowA then
    S.W.ge (Form.pp.sub (.one 1)) (S.fh.add .hp) && S.has .plus (.c F) (S.fh.add .hp)
  else
    S.W.ge (S.fh.add .hp) Form.pp && S.zeroCo F &&
      S.has .plus (.c E) ((S.fh.add .hp).sub Form.pp)) &&
  S.top (.c E) S.fh

def cOK (F E : Co) : Bool :=
  S.W.ge S.fh (.one 1) && S.has .plus (.c F) S.fh && S.has .minus (.minus F E) .hp &&
    S.top (.c E) (S.fh.sub (.one 1))

def vOK (l0 l1 : Lab) (D : Form) (low : Bool) : Bool :=
  if low then S.W.ge Form.pp D && S.has .zero l1 Form.pp && S.top l0 D
  else S.W.ge D (Form.pp.add (.one 1)) && S.top l1 (D.sub Form.pp)

def slotOK : Bool :=
  (List.range S.b).all (fun k => S.aOK (.blk k 0) (.blk k 1) && S.cOK (.blk k 2) (.blk k 3)) &&
  S.aOK (.cen 0) (.cen 1) && S.has .minus (.minus (.cen 0) (.cen 1)) .hp &&
  S.vOK (.vbot 0) (.vbot 1) ((S.fh.add Form.pp).sub S.fja) S.botLow &&
  S.vOK (.vtop 0) (.vtop 1) (S.fh.add S.frho) S.topLow &&
  S.has .plus (.c (.ext 0)) (Form.pp.sub S.fq)

def loA (J : ℤ) (T : ℤ) : Form := S.fH.sub (Form.smul (T + 1) Form.pp)
def loB (J : ℤ) (T : ℤ) : Form := (S.fH.sub S.fL).add (Form.smul (J - T) Form.pp)
def hiA (J : ℤ) (T : ℤ) : Form := S.fH.sub (Form.smul T Form.pp)
def hiB (J : ℤ) (T : ℤ) : Form := (S.fH.sub S.fb).add (Form.smul (J - T) Form.pp)

/-- `f ≤ e` on the interval of the label. -/
def belowLo (J T : ℤ) (f : Form) : Bool := S.W.ge (S.loA J T) f || S.W.ge (S.loB J T) f
/-- `e < f` on the interval of the label. -/
def aboveHi (J T : ℤ) (f : Form) : Bool := S.W.ge f (S.hiA J T) || S.W.ge f (S.hiB J T)

/-- The graph coordinate of an auxiliary index. -/
def auxOf (J s t : ℕ) : Bool :=
  S.aboveHi J (S.S0 - s) (S.ord .zero (.graph J s (t + 1))) &&
    S.belowLo J (S.S0 - s) (Form.pp.sub (S.ord .inf (.c (.ext (t + 1)))))

/-- The label's interval is empty or covered. -/
def respOK (J s : ℕ) : Bool :=
  let T := S.S0 - s
  let O := S.ord .zero (.raw J s)
  let I := S.ord .inf (.raw J s)
  S.belowLo J T (S.hiA J T) || S.belowLo J T (S.hiB J T) ||
  S.aboveHi J T O || S.belowLo J T (Form.pp.sub I) || S.W.ge (O.add I) Form.pp ||
  (List.range S.aux.length).any (fun t => S.auxOf J s t)

def respAll : Bool :=
  (List.range (S.Jhi + 1)).all fun J => decide (J < S.Jlo) || (S.respOK J 0 && S.respOK J 1)

/-- Each graph coordinate is determined. -/
def extraOK : Bool :=
  decide (S.ex = S.aux.length + 1) &&
  (List.range S.aux.length).all fun t =>
    S.W.ge ((S.ord .zero (.graph (S.aux.getD t (0, 0)).1 (S.aux.getD t (0, 0)).2 (t + 1))).add
      (S.ord .inf (.c (.ext (t + 1))))) Form.pp

def validCo : Co → Bool
  | .blk k u => decide (k < S.b) && decide (u < 4)
  | .cen z => decide (z < 2)
  | .ext t => decide (t < S.ex)

/-- A diagonal block with small nonzero entries. -/
def diagOK (m N1 : ℕ) (f : ℕ → ℕ → ℤ) : Bool :=
  (List.range m).all fun i => (List.range m).all fun j =>
    if i = j then decide (f i j ≠ 0) && decide ((f i j).natAbs < N1) else decide (f i j = 0)

/-- The constant space embeds. -/
def injOK : Bool :=
  decide (S.sel.length = S.m) &&
  (List.range S.m).all (fun i => S.validCo (S.sel.getD i (.ext 0))) &&
  diagOK S.m S.W.N1 fun i j => (S.zrow (S.sel.getD i (.ext 0))).getD j 0

/-- All chart checks. -/
def Check : Bool := S.geoOK && S.slotOK && S.respAll && S.extraOK && S.injOK

end Spec

/-! ### Geometry on the window -/

section Geo
variable {S : Spec} {N p : ℕ} [Fact p.Prime]

theorem ev_fH (N k : ℕ) : S.fH.ev N k = S.P.H N := by
  simp only [Spec.fH, Form.ev_lin, Parameters.H, Parameters.C, Parameters.L, Parameters.n,
    Parameters.b, Parameters.q, Parameters.g, Parameters.h]
  push_cast; ring
theorem ev_fL (N k : ℕ) : S.fL.ev N k = S.P.L N := by
  simp only [Spec.fL, Form.ev_lin, Parameters.L, Parameters.n, Parameters.b, Parameters.q]
  push_cast; ring
theorem ev_fb (N k : ℕ) : S.fb.ev N k = S.P.b N := by
  simp only [Spec.fb, Form.ev_lin, Parameters.b]; push_cast; ring
theorem ev_fq (N k : ℕ) : S.fq.ev N k = S.P.q N := by
  simp only [Spec.fq, Form.ev_lin, Parameters.q]; push_cast; ring
theorem ev_fg (N k : ℕ) : S.fg.ev N k = S.P.g N := by
  simp only [Spec.fg, Form.ev_lin, Parameters.g]; push_cast; ring
theorem ev_fh (N k : ℕ) : S.fh.ev N k = S.P.h N := by
  simp only [Spec.fh, Form.ev_lin, Parameters.h]; push_cast; ring
theorem ev_fn (N k : ℕ) : S.fn.ev N k = S.P.n N := by
  simp only [Spec.fn, Form.ev_lin, Parameters.n]; push_cast; ring

/-- The arithmetic of the cell at `(N, p)`. -/
structure Geo (S : Spec) (N p : ℕ) : Prop where
  adm : Admissible S.P
  hN : 0 < N
  hn : 1 ≤ S.P.n N
  hqp : S.P.q N < p
  hhp : S.P.h N < p
  hk0 : gk0 (S.P.g N) p = S.k0
  hk1 : gk1 (S.P.n N) (S.P.g N) p = S.k1
  hb : bN S.P N p = S.b
  bpos : 0 < S.b
  hS0a : S.S0 * p ≤ (S.P.H N : ℤ) - 1
  hS0b : (S.P.H N : ℤ) - 1 < (S.S0 + 1) * p
  hJlo : (S.Jlo : ℤ) * p ≤ S.P.b N
  hJhi : (S.P.L N : ℤ) ≤ ((S.Jhi : ℤ) + 1) * p
  hp1 : N ≤ p

theorem ediv_eq_of_bounds {a q b : ℤ} (hb : 0 < b) (h1 : q * b ≤ a) (h2 : a < (q + 1) * b) :
    a / b = q := by
  have e1 : q ≤ a / b := Int.le_ediv_of_mul_le hb h1
  have e2 : a / b < q + 1 := Int.ediv_lt_of_lt_mul hb (by linarith)
  omega

theorem geo_of_check (hS : S.geoOK = true) {k : ℕ} (hm : S.W.Mem N k) (hpk : p = 2 * k + 1) :
    Geo S N p := by
  simp only [Spec.geoOK, Bool.and_eq_true, decide_eq_true_eq] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩,
    c15⟩ := hS
  have hpz : (p : ℤ) = 2 * k + 1 := by exact_mod_cast hpk
  have hp0 : (0 : ℤ) < p := by omega
  have g4 := Win.ge_sound c4 hm
  have g5 := Win.ge_sound c5 hm
  have g6 := Win.ge_sound c6 hm
  have g7 := Win.ge_sound c7 hm
  have g8 := Win.ge_sound c8 hm
  have g9 := Win.ge_sound c9 hm
  have g12 := Win.ge_sound c12 hm
  have g13 := Win.ge_sound c13 hm
  have g14 := Win.ge_sound c14 hm
  have g15 := Win.ge_sound c15 hm
  simp only [Form.ev_sub, Form.ev_smul, Form.ev_one, Form.ev_pp, ev_fq, ev_fh, ev_fg, ev_fn,
    ev_fH, ev_fL, ev_fb, ← hpz] at g4 g5 g6 g7 g8 g9 g12 g13 g14 g15
  have hN1 : 0 < N := lt_of_lt_of_le c2 hm.1
  have hk0 : gk0 (S.P.g N) p = S.k0 := by
    unfold gk0
    exact ediv_eq_of_bounds hp0 (by linarith) (by linarith)
  have hk1 : gk1 (S.P.n N) (S.P.g N) p = S.k1 := by
    unfold gk1
    exact ediv_eq_of_bounds hp0 (by linarith) (by linarith)
  have hn : 1 ≤ S.P.n N := by
    have h1 := c1.1
    simp only [Parameters.n]
    exact Nat.mul_pos h1 hN1
  have hb : bN S.P N p = S.b := by
    obtain ⟨-, h2⟩ := gb_spec (n := S.P.n N) (g := S.P.g N) (Fact.out : p.Prime).pos hn
    have : ((bN S.P N p : ℕ) : ℤ) = S.b := by
      show ((gb (S.P.n N) (S.P.g N) p : ℕ) : ℤ) = _
      rw [h2, hk0, hk1, c10]
    exact_mod_cast this
  have hNp : N ≤ p := by
    have h1 := hm.2.1
    have hN' : (0 : ℤ) ≤ N := by positivity
    have hk' : (2 * (k : ℤ) + 1) = p := hpz.symm
    rw [hk'] at h1
    have hd : 0 < S.W.aD := by
      simp only [Win.ge, Win.nn, Bool.and_eq_true, decide_eq_true_eq] at c4
      exact c4.1.1.1.1.1
    have : S.W.aD * N ≤ S.W.aD * p := by
      have : S.W.aD * (N : ℤ) ≤ S.W.aN * N := mul_le_mul_of_nonneg_right c3 hN'
      linarith
    have := le_of_mul_le_mul_left this hd
    exact_mod_cast this
  exact
    { adm := c1
      hN := hN1
      hn := hn
      hqp := by zify; linarith
      hhp := by zify; linarith
      hk0 := hk0
      hk1 := hk1
      hb := hb
      bpos := c11
      hS0a := by linarith
      hS0b := by linarith
      hJlo := by linarith
      hJhi := by linarith
      hp1 := hNp }

end Geo

section KilledOps
variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  [FiniteDimensional (ZMod p) V] {ι : Type*} {e width : ι → ℕ} {m : ℕ}
  {B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p)} {lam : ∀ c, Fin (width c) → Fin m → ZMod p}
  {φ ψ : V →ₗ[ZMod p] ZMod p} {μ : Fin m → ZMod p}

theorem killed_add (h1 : Killed B lam φ μ) (h2 : Killed B lam ψ μ) : Killed B lam (φ + ψ) μ :=
  fun x hx => by simp [h1 x hx, h2 x hx]
theorem killed_neg (h1 : Killed B lam φ μ) : Killed B lam (-φ) μ :=
  fun x hx => by simp [h1 x hx]
theorem killed_zero : Killed B lam (0 : V →ₗ[ZMod p] ZMod p) μ :=
  fun x _ => by simp
end KilledOps

section Rows
variable {S : Spec} {N p k : ℕ} [Fact p.Prime] (hK : S.K = bN S.P N p * 4 + 2 + S.ex)

/-- The killed rows of the chart. -/
abbrev KdC (S : Spec) {N p : ℕ} [Fact p.Prime] (hK : S.K = bN S.P N p * 4 + 2 + S.ex) (k : ℕ) :=
  Killed (Bm S hK) (lamC S (N := N) (p := p) k)

include hK in
theorem zeroK {l : Lab} {e : ℕ} (h : (e : ℤ) < (S.ord .zero l).ev N k) :
    KdC S hK k (Lab.eval S hK l) (coefLam e) :=
  killed_ord S hK k .zero l (t := e) (Int.lt_toNat.mpr h)

theorem infK {l : Lab} {e : ℕ} (he : e < p) (h : (p : ℤ) - (S.ord .inf l).ev N k ≤ e) :
    KdC S hK k (Lab.eval S hK l) (coefLam e) := by
  have h3 := killed_ord S hK k .inf l (N := N) (p := p) (t := p - 1 - e)
    (Int.lt_toNat.mpr (by omega))
  have h4 : p - 1 - (p - 1 - e) = e := by omega
  simpa only [PtD.pt, jetLam, h4] using h3

theorem hasK {pt : PtD} {l : Lab} {f : Form} (h : S.has pt l f = true) (hm : S.W.Mem N k) {t : ℕ}
    (ht : (t : ℤ) < f.ev N k) : KdC S hK k (Lab.eval S hK l) (jetLam p pt.pt t) :=
  killed_ord S hK k pt l (Int.lt_toNat.mpr (lt_of_lt_of_le ht (Win.ge_sound h hm)))

theorem ordPlus {l : Lab} {f : Form} (h : S.has .plus l f = true) (hm : S.W.Mem N k) {n : ℕ}
    (hn : (n : ℤ) ≤ f.ev N k) : OrdAt (KdC S hK k) 1 (Lab.eval S hK l) n :=
  fun t ht => hasK hK h hm (t := t) (by omega)

theorem ordMinus {l : Lab} {f : Form} (h : S.has .minus l f = true) (hm : S.W.Mem N k) {n : ℕ}
    (hn : (n : ℤ) ≤ f.ev N k) : OrdAt (KdC S hK k) (-1) (Lab.eval S hK l) n :=
  fun t ht => hasK hK h hm (t := t) (by omega)

theorem topK {l : Lab} {f : Form} (h : S.top l f = true) (hm : S.W.Mem N k) (hpk : p = 2 * k + 1)
    {n : ℕ} (hn : f.ev N k ≤ n) : TopFrom (KdC S hK k) (Lab.eval S hK l) n := by
  refine topFrom_of_inf fun t ht => hasK hK h hm (t := t) ?_
  simp only [Form.ev_sub, Form.ev_pp]
  omega

theorem zeroTop {l : Lab} {f : Form} (h : S.has .zero l f = true) (hm : S.W.Mem N k)
    (hn : (p : ℤ) ≤ f.ev N k) : TopFrom (KdC S hK k) (Lab.eval S hK l) 0 :=
  fun i _ hi => hasK hK h hm (t := i) (by omega)

theorem cf_zero {x : Co} (h : S.zeroCo x = true) : cf S (p := p) x = 0 := by
  have h1 : ∀ z ∈ S.zrow x, z = 0 := by
    simpa [Spec.zeroCo] using h
  refine Finset.sum_eq_zero fun j _ => ?_
  have h2 : (S.zrow x).getD j.val 0 = 0 := by
    by_cases hj : j.val < (S.zrow x).length
    · rw [List.getD_eq_getElem _ _ hj]
      exact h1 _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]
  rw [h2]
  simp

theorem aslot_of (g : Geo S N p) (hm : S.W.Mem N k) (hpk : p = 2 * k + 1) {F E : Co}
    (h : S.aOK F E = true) : ASlot (KdC S hK k) (S.P.h N % p) (cf S F) (cf S E) := by
  have hh : S.P.h N % p = S.P.h N := Nat.mod_eq_of_lt g.hhp
  have hk2 : (p - 1) / 2 = k := by omega
  rw [hh]
  unfold ASlot
  rw [hk2]
  simp only [Spec.aOK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, topK hK (l := .c E) h2 hm hpk (by simp [ev_fh])⟩
  cases hl : S.lowA with
  | true =>
    simp only [hl, if_true, Bool.and_eq_true] at h1
    obtain ⟨h3, h4⟩ := h1
    have h5 := Win.ge_sound h3 hm
    simp only [Form.ev_add, Form.ev_sub, Form.ev_pp, Form.ev_one, Form.ev_hp, ev_fh] at h5
    rw [if_pos (by omega)]
    exact ordPlus hK (l := .c F) h4 hm (by simp [ev_fh])
  | false =>
    simp only [hl, Bool.false_eq_true, if_false, Bool.and_eq_true] at h1
    obtain ⟨⟨h3, h4⟩, h6⟩ := h1
    have h5 := Win.ge_sound h3 hm
    simp only [Form.ev_add, Form.ev_pp, Form.ev_hp, ev_fh] at h5
    rw [if_neg (by omega)]
    refine ⟨?_, ordPlus hK (l := .c E) h6 hm ?_⟩
    · rw [cf_zero h4]
      exact fun _ _ _ => killed_zero
    · simp only [Form.ev_add, Form.ev_sub, Form.ev_pp, Form.ev_hp, ev_fh]
      omega

theorem cslot_of (g : Geo S N p) (hm : S.W.Mem N k) (hpk : p = 2 * k + 1) {F E : Co}
    (h : S.cOK F E = true) : CSlot (KdC S hK k) (S.P.h N % p) (cf S F) (cf S E) := by
  have hh : S.P.h N % p = S.P.h N := Nat.mod_eq_of_lt g.hhp
  have hk2 : (p - 1) / 2 = k := by omega
  rw [hh]
  unfold CSlot
  simp only [Spec.cOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have h5 := Win.ge_sound h1 hm
  simp only [Form.ev_one, ev_fh] at h5
  rw [if_neg (by omega), hk2]
  refine ⟨ordPlus hK (l := .c F) h2 hm (by simp [ev_fh]),
    ordMinus hK (l := .minus F E) h3 hm (by simp), topK hK (l := .c E) h4 hm hpk ?_⟩
  simp only [Form.ev_sub, Form.ev_one, ev_fh]
  omega

theorem vdeg_of (hm : S.W.Mem N k) (hpk : p = 2 * k + 1) {l0 l1 : Lab} {D : Form} {low : Bool}
    (h : S.vOK l0 l1 D low = true) {n : ℕ} (hn : (n : ℤ) = D.ev N k) :
    VDeg (KdC S hK k) (Lab.eval S hK l0) (Lab.eval S hK l1) n := by
  unfold VDeg
  cases low with
  | true =>
    simp only [Spec.vOK, if_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have h5 := Win.ge_sound h1 hm
    simp only [Form.ev_pp] at h5
    rw [if_pos (by omega)]
    exact ⟨zeroTop hK h2 hm (by simp only [Form.ev_pp]; omega), topK hK h3 hm hpk hn.ge⟩
  | false =>
    simp only [Spec.vOK, Bool.false_eq_true, if_false, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have h5 := Win.ge_sound h1 hm
    simp only [Form.ev_add, Form.ev_pp, Form.ev_one] at h5
    rw [if_neg (by omega)]
    refine topK hK h2 hm hpk ?_
    simp only [Form.ev_sub, Form.ev_pp]
    omega

theorem belowLo_sound {J T : ℤ} {f : Form} (h : S.belowLo J T f = true) (hm : S.W.Mem N k) {e : ℤ}
    (h1 : (S.loA J T).ev N k ≤ e) (h2 : (S.loB J T).ev N k ≤ e) : f.ev N k ≤ e := by
  simp only [Spec.belowLo, Bool.or_eq_true] at h
  rcases h with h | h
  · exact (Win.ge_sound h hm).trans h1
  · exact (Win.ge_sound h hm).trans h2

theorem aboveHi_sound {J T : ℤ} {f : Form} (h : S.aboveHi J T f = true) (hm : S.W.Mem N k) {e : ℤ}
    (h1 : e < (S.hiA J T).ev N k) (h2 : e < (S.hiB J T).ev N k) : e < f.ev N k := by
  simp only [Spec.aboveHi, Bool.or_eq_true] at h
  rcases h with h | h
  · exact lt_of_lt_of_le h1 (Win.ge_sound h hm)
  · exact lt_of_lt_of_le h2 (Win.ge_sound h hm)

theorem raw_eq_graph (J s t : ℕ) :
    Lab.eval S hK (.raw J s) = Lab.eval S hK (.graph J s t) + cf S (.ext t) := by
  simp [Lab.eval]

/-- A label's raw row is killed at a position of its interval. -/
theorem respK {J s : ℕ} (h : S.respOK J s = true) (hm : S.W.Mem N k) (hpk : p = 2 * k + 1)
    {e : ℕ} (hep : e < p)
    (h1 : (S.loA J (S.S0 - s)).ev N k ≤ e) (h2 : (S.loB J (S.S0 - s)).ev N k ≤ e)
    (h3 : (e : ℤ) < (S.hiA J (S.S0 - s)).ev N k) (h4 : (e : ℤ) < (S.hiB J (S.S0 - s)).ev N k) :
    KdC S hK k (Lab.eval S hK (.raw J s)) (coefLam e) := by
  simp only [Spec.respOK, Bool.or_eq_true] at h
  have hp1 : ∀ {f : Form}, S.belowLo J (S.S0 - s) (Form.pp.sub f) = true →
      (p : ℤ) - f.ev N k ≤ e := by
    intro f hf
    have := belowLo_sound hf hm h1 h2
    simp only [Form.ev_sub, Form.ev_pp] at this
    omega
  rcases h with ((((h | h) | h) | h) | h) | h
  · exact absurd (belowLo_sound h hm h1 h2) (by omega)
  · exact absurd (belowLo_sound h hm h1 h2) (by omega)
  · exact (zeroK hK (aboveHi_sound h hm h3 h4))
  · exact infK hK hep (hp1 h)
  · have h5 := Win.ge_sound h hm
    simp only [Form.ev_add, Form.ev_pp] at h5
    by_cases h6 : (e : ℤ) < (S.ord .zero (.raw J s)).ev N k
    · exact zeroK hK h6
    · exact infK hK hep (by omega)
  · simp only [List.any_eq_true, List.mem_range] at h
    obtain ⟨t, -, ht⟩ := h
    simp only [Spec.auxOf, Bool.and_eq_true] at ht
    rw [raw_eq_graph hK J s (t + 1)]
    exact killed_add (zeroK hK (aboveHi_sound ht.1 hm h3 h4)) (infK hK (l := .c (.ext (t + 1))) hep
      (hp1 ht.2))

theorem label_range (g : Geo S N p) (hpk : p = 2 * k + 1) {J : ℕ} {Sz : ℤ} {e : ℕ}
    (hlo : respLo (S.P.H N) (S.P.L N) p 0 J Sz ≤ e) (hhi : (e : ℤ) < respHi (S.P.H N) (S.P.b N) p J Sz) :
    (∃ s : ℕ, (s = 0 ∨ s = 1) ∧ Sz = S.S0 - s) ∧ S.Jlo ≤ J ∧ J < S.Jhi + 1 ∧ e < p ∧
      (S.loA J Sz).ev N k ≤ e ∧ (S.loB J Sz).ev N k ≤ e ∧
      (e : ℤ) < (S.hiA J Sz).ev N k ∧ (e : ℤ) < (S.hiB J Sz).ev N k := by
  have hpz : (p : ℤ) = 2 * k + 1 := by exact_mod_cast hpk
  have hp0 : (0 : ℤ) < p := by omega
  simp only [respLo, respHi, max_le_iff, lt_min_iff, Nat.cast_zero, add_zero] at hlo hhi
  obtain ⟨l1, l2, l3⟩ := hlo
  obtain ⟨u1, u2, u3⟩ := hhi
  have hA := g.hS0a
  have hB := g.hS0b
  have hC := g.hJlo
  have hD := g.hJhi
  have hs1 : Sz < S.S0 + 1 := by
    refine lt_of_mul_lt_mul_right (a := (p : ℤ)) ?_ hp0.le
    nlinarith only [u2, hB, l1]
  have hs2 : S.S0 < Sz + 2 := by
    refine lt_of_mul_lt_mul_right (a := (p : ℤ)) ?_ hp0.le
    nlinarith only [l2, hA, u1]
  have hj1 : (S.Jlo : ℤ) < (J : ℤ) + 1 := by
    refine lt_of_mul_lt_mul_right (a := (p : ℤ)) ?_ hp0.le
    nlinarith only [l2, u3, hC]
  have hj2 : (J : ℤ) < (S.Jhi : ℤ) + 1 := by
    refine lt_of_mul_lt_mul_right (a := (p : ℤ)) ?_ hp0.le
    nlinarith only [l3, u2, hD]
  refine ⟨?_, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · have : Sz = S.S0 ∨ Sz = S.S0 - 1 := by omega
    rcases this with h | h
    · exact ⟨0, Or.inl rfl, by simp [h]⟩
    · exact ⟨1, Or.inr rfl, by simp [h]⟩
  all_goals
    simp only [Spec.loA, Spec.loB, Spec.hiA, Spec.hiB, Form.ev_sub, Form.ev_add, Form.ev_smul,
      Form.ev_pp, ev_fH, ev_fL, ev_fb, ← hpz]
  · linarith only [l2]
  · linarith only [l3]
  · linarith only [u2]
  · linarith only [u3]

theorem response_rows (g : Geo S N p) (hS : S.respAll = true) (hm : S.W.Mem N k)
    (hpk : p = 2 * k + 1) :
    ∀ j, S.P.b N ≤ j → j + 0 * p < S.P.L N → ∀ e : Fin p,
      (p : ℤ) ∣ (S.P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e →
      KdC S hK k (rawRow hK (insZ S hK) 0 j e - cf S (.ext 0)) (coefLam e.val) := by
  refine response_of_labels fun J Sz e h1 h2 => ?_
  obtain ⟨⟨s, hs, rfl⟩, h3, h4, h5, h6, h7, h8, h9⟩ := label_range g hpk h1 h2
  simp only [Spec.respAll, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true] at hS
  rcases hS J h4 with h | ⟨ha, hb⟩
  · omega
  · rcases hs with rfl | rfl
    · exact respK hK ha hm hpk h5 h6 h7 h8 h9
    · exact respK hK hb hm hpk h5 h6 h7 h8 h9

theorem labelRow_physical (a J : ℕ) (Sz : ℤ) :
    Physical hK (insZ S hK) (labelRow hK (insZ S hK) a J Sz) := by
  intro y hy
  simp only [labelRow, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [← psi_projExtras, hy, map_zero, smul_zero]

theorem extra_rows (g : Geo S N p) (hS : S.extraOK = true) (hm : S.W.Mem N k)
    (hpk : p = 2 * k + 1) (t : Fin S.ex) (e : Fin p) :
    ∃ (ψ : (Fin S.m → ZMod p) →ₗ[ZMod p] ZMod p) (c : ZMod p),
      Physical hK (insZ S hK) ψ ∧
      KdC S hK k (crd hK (insZ S hK) (Sum.inr (Sum.inr t)) - ψ - c • cf S (.ext 0))
        (coefLam e.val) := by
  simp only [Spec.extraOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hS
  obtain ⟨hl, ha⟩ := hS
  rw [crd_insZ]
  obtain ⟨tv, ht⟩ := t
  cases tv with
  | zero =>
    refine ⟨0, 1, fun _ _ => rfl, ?_⟩
    have : cf S (p := p) (coOf (b := bN S.P N p) (ex := S.ex) (Sum.inr (Sum.inr ⟨0, ht⟩))) - 0 -
        (1 : ZMod p) • cf S (.ext 0) = 0 := by
      simp [coOf]
    rw [this]
    exact killed_zero
  | succ u =>
    have hu : u < S.aux.length := by omega
    have h5 := Win.ge_sound (ha u hu) hm
    simp only [Form.ev_add, Form.ev_pp] at h5
    set J := (S.aux.getD u (0, 0)).1
    set s := (S.aux.getD u (0, 0)).2
    have hpz : (p : ℤ) = 2 * k + 1 := by exact_mod_cast hpk
    by_cases h6 : (e.val : ℤ) < (S.ord .zero (.graph J s (u + 1))).ev N k
    · refine ⟨labelRow hK (insZ S hK) 0 J (S.S0 - s), -1, labelRow_physical hK _ _ _, ?_⟩
      have : cf S (p := p) (coOf (b := bN S.P N p) (ex := S.ex) (Sum.inr (Sum.inr ⟨u + 1, ht⟩))) -
          labelRow hK (insZ S hK) 0 J (S.S0 - s) - (-1 : ZMod p) • cf S (.ext 0) =
          -Lab.eval S hK (.graph J s (u + 1)) := by
        have h7 : (-1 : ZMod p) • cf S (p := p) (.ext 0) = -cf S (.ext 0) := by
          ext y
          simp
        rw [h7]
        simp only [Lab.eval, coOf]
        abel
      rw [this]
      exact killed_neg (zeroK hK h6)
    · refine ⟨0, 0, fun _ _ => rfl, ?_⟩
      have : cf S (p := p) (coOf (b := bN S.P N p) (ex := S.ex) (Sum.inr (Sum.inr ⟨u + 1, ht⟩))) -
          0 - (0 : ZMod p) • cf S (.ext 0) = Lab.eval S hK (.c (.ext (u + 1))) := by
        simp [Lab.eval, coOf]
      rw [this]
      exact infK hK e.isLt (by omega)

/-- **The chart's source rows at every `(N, p)` of the window.** -/
theorem sourceRows (g : Geo S N p) (hslot : S.slotOK = true) (hresp : S.respAll = true)
    (hex : S.extraOK = true) (hm : S.W.Mem N k) (hpk : p = 2 * k + 1) (hb : 0 < bN S.P N p) :
    SourceRows (KdC S hK k) hK hb (insZ S hK) (cf S (.ext 0)) 0 (S.P.q N) := by
  have hbe : bN S.P N p = S.b := g.hb
  simp only [Spec.slotOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hslot
  obtain ⟨⟨⟨⟨⟨hblk, hz1⟩, hz2⟩, hbot⟩, htop⟩, hlow⟩ := hslot
  have hpz : (p : ℤ) = 2 * k + 1 := by exact_mod_cast hpk
  have hhm : S.P.h N % p = S.P.h N := Nat.mod_eq_of_lt g.hhp
  refine
    { slotA := fun i => ?_
      slotC := fun i => ?_
      slotZ := ?_
      bottom := ?_
      top := ?_
      lowJet := ?_
      response := response_rows hK g hresp hm hpk
      extra := extra_rows hK g hex hm hpk }
  · rw [crd_insZ, crd_insZ]
    exact aslot_of hK g hm hpk (hblk i.val (hbe ▸ i.isLt)).1
  · rw [crd_insZ, crd_insZ]
    exact cslot_of hK g hm hpk (hblk i.val (hbe ▸ i.isLt)).2
  · rw [crd_insZ, crd_insZ]
    have hk2 : (p - 1) / 2 = k := by omega
    refine ⟨aslot_of hK g hm hpk hz1, ?_⟩
    rw [hk2]
    exact ordMinus hK (l := .minus (.cen 0) (.cen 1)) hz2 hm (by simp)
  · simp only [crd_insZ]
    obtain ⟨j1, j2⟩ := gja_spec (g := S.P.g N) (Fact.out : p.Prime).pos
    refine vdeg_of hK hm hpk (l0 := .vbot 0) (l1 := .vbot 1) hbot ?_
    rw [hhm, g.hk0] at *
    simp only [Spec.fja, Form.ev_sub, Form.ev_add, Form.ev_smul, Form.ev_pp, ev_fh, ev_fg, ← hpz]
    push_cast [Nat.cast_sub j2.le]
    rw [j1]
    ring
  · have hv := vdeg_of (n := S.P.h N % p + grho (S.P.n N) (S.P.g N) p) hK hm hpk
      (l0 := .vtop 0) (l1 := .vtop 1) htop (by
        obtain ⟨j1, -⟩ := grho_spec (n := S.P.n N) (g := S.P.g N) (Fact.out : p.Prime).pos
        rw [hhm]
        push_cast
        rw [j1, g.hk1]
        simp only [Spec.frho, Form.ev_sub, Form.ev_add, Form.ev_smul, Form.ev_pp, Form.ev_one,
          ev_fh, ev_fg, ev_fn, ← hpz])
    have e1 : ∀ (h : bN S.P N p - 1 < bN S.P N p) (u : Fin 4),
        coOf (b := bN S.P N p) (ex := S.ex) (Sum.inl (⟨bN S.P N p - 1, h⟩, u)) =
          .blk (S.b - 1) u.val := by
      intro h u
      simp [coOf, hbe]
    simp only [crd_insZ, e1]
    exact hv
  · refine ordPlus hK (l := .c (.ext 0)) hlow hm ?_
    have := g.hqp
    simp only [Form.ev_sub, Form.ev_pp, ev_fq, ← hpz]
    omega

theorem diag_zero {m N1 : ℕ} {f : ℕ → ℕ → ℤ} (h : Spec.diagOK m N1 f = true) (hp : N1 ≤ p)
    (y : Fin m → ZMod p)
    (hy : ∀ i : Fin m, ∑ j : Fin m, ((f i.val j.val : ℤ) : ZMod p) * y j = 0) : y = 0 := by
  simp only [Spec.diagOK, List.all_eq_true, List.mem_range] at h
  funext i
  have h1 := hy i
  rw [Finset.sum_eq_single i] at h1
  · have h2 := h i.val i.isLt i.val i.isLt
    simp only [if_true, Bool.and_eq_true, decide_eq_true_eq] at h2
    rcases mul_eq_zero.mp h1 with h3 | h3
    · exfalso
      have h4 : (p : ℤ) ∣ f i.val i.val := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h3
      refine h2.1 (Int.eq_zero_of_abs_lt_dvd h4 ?_)
      have h5 := h2.2
      rw [Int.abs_eq_natAbs]
      omega
    · exact h3
  · intro j _ hj
    have h2 := h i.val i.isLt j.val j.isLt
    have hne : i.val ≠ j.val := fun e => hj (Fin.ext e.symm)
    simp only [hne, if_false, decide_eq_true_eq] at h2
    simp [h2]
  · simp

theorem exists_co {x : Co} (g : Geo S N p) (h : S.validCo x = true) :
    ∃ i : CK (bN S.P N p) S.ex, coOf i = x := by
  have hbe : bN S.P N p = S.b := g.hb
  cases x with
  | blk k u =>
    simp only [Spec.validCo, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨Sum.inl (⟨k, hbe ▸ h.1⟩, ⟨u, h.2⟩), rfl⟩
  | cen z =>
    simp only [Spec.validCo, decide_eq_true_eq] at h
    exact ⟨Sum.inr (Sum.inl ⟨z, h⟩), rfl⟩
  | ext t =>
    simp only [Spec.validCo, decide_eq_true_eq] at h
    exact ⟨Sum.inr (Sum.inr ⟨t, h⟩), rfl⟩

theorem insZ_injective (g : Geo S N p) (h : S.injOK = true) (hN1 : S.W.N1 ≤ p) :
    Function.Injective (insZ S (p := p) hK) := by
  simp only [Spec.injOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨-, h2⟩, h3⟩ := h
  refine (injective_iff_map_eq_zero _).mpr fun y hy => ?_
  refine diag_zero h3 hN1 y fun i => ?_
  obtain ⟨c, hc⟩ := exists_co g (h2 i.val i.isLt)
  have h4 := congrFun hy ((ckEquiv hK).symm c)
  simp only [insZ, LinearMap.pi_apply, Equiv.apply_symm_apply, hc, Pi.zero_apply] at h4
  simpa [cf] using h4

/-- **The physical host of a chart at every `(N, p)` of its window.**  Nothing is assumed but the
finite check. -/
def chartHost (hS : S.Check = true) (hm : S.W.Mem N k) (hpk : p = 2 * k + 1) (hp2 : p ≠ 2)
    (hn : 1 ≤ S.P.n N) :
    CountHost (monoData hp2 hn hK).sys p (fun c => (S.levels.get c).rows.length)
      (wdN S (N := N) k) (Bm S hK) (lamC S (N := N) (p := p) k) 0 (S.P.q N) :=
  have hc : S.geoOK = true ∧ S.slotOK = true ∧ S.respAll = true ∧ S.extraOK = true ∧
      S.injOK = true := by
    simp only [Spec.Check, Bool.and_eq_true] at hS
    exact ⟨hS.1.1.1.1, hS.1.1.1.2, hS.1.1.2, hS.1.2, hS.2⟩
  have g : Geo S N p := geo_of_check hc.1 hm hpk
  physicalHost (Bm S hK) (lamC S (N := N) (p := p) k) hp2 hn hK (bN_pos hn) (insZ S hK)
    (insZ_injective hK g hc.2.2.2.2 (hm.1.trans g.hp1)) (cf S (.ext 0)) 0 (S.P.q N) g.hqp.le
    (by simp) (sourceRows hK g hc.2.1 hc.2.2.1 hc.2.2.2.1 hm hpk (bN_pos hn))

end Rows

/-! ### Rank certificates -/

/-- Integer dot product. -/
def dot : List ℤ → List ℤ → ℤ
  | a :: s, b :: t => a * b + dot s t
  | _, _ => 0

theorem dot_sum (w : List ℤ) (a : List ℤ) (m : ℕ) (h : w.length ≤ m) :
    ∑ j ∈ range m, a.getD j 0 * w.getD j 0 = dot a w := by
  induction w generalizing a m with
  | nil =>
    cases a <;> simp [dot]
  | cons b t ih =>
    cases a with
    | nil => simp [dot]
    | cons x s =>
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at h; omega⟩
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, dot]
      rw [ih s m (by simpa using h)]
      ring

/-- A rank certificate.  `mode 2`: count all rows.  `mode 1`: count the physical rows, the others
vanish on `W`.  `mode 0`: all rows vanish on `W`.  `W` has a diagonal block at the pivots `pv`. -/
structure RCert where
  mode : ℕ
  W : List (List ℤ)
  pv : List ℕ

/-- The rows that read the source covectors. -/
def Lab.phys : Lab → Bool
  | .raw _ _ => true
  | .graph _ _ _ => true
  | _ => false

namespace Spec
variable (S : Spec)

/-- The chart coordinate `x` of the constant vector `w`. -/
def yv (w : List ℤ) (x : Co) : ℤ := dot (S.zrow x) w

/-- The label vanishes on `w`, the source part being checked separately. -/
def zeroOn (w : List ℤ) : Lab → Bool
  | .c x => decide (S.yv w x = 0)
  | .minus F E => decide (S.yv w F - 2 * S.yv w E = 0)
  | .vbot u => decide (S.yv w (.blk 0 u) - S.yv w (.blk 0 (u + 2)) + S.yv w (.cen u) = 0)
  | .vtop u => decide (S.yv w (.blk (S.b - 1) u) + S.yv w (.blk (S.b - 1) (u + 2)) = 0)
  | .raw _ _ => decide (S.yv w (.ext 0) = 0)
  | .graph _ _ t => decide (S.yv w (.ext 0) = 0) && decide (S.yv w (.ext t) = 0)

/-- Node `m`, part `u`, of the vector `w`. -/
def nodeV (w : List ℤ) (u m : ℕ) : ℤ :=
  (if m < S.b then S.yv w (.blk m u) - S.yv w (.blk m (u + 2)) else 0) +
    (if 0 < m then S.yv w (.blk (m - 1) u) + S.yv w (.blk (m - 1) (u + 2)) else 0) +
    (if m = 0 then S.yv w (.cen u) else 0)

def nodesZero (w : List ℤ) : Bool :=
  (List.range (S.b + 1)).all fun m => decide (S.nodeV w 0 m = 0) && decide (S.nodeV w 1 m = 0)

/-- The rows the certificate does not count. -/
def rest (c : RCert) (ls : List Lab) : List Lab :=
  if c.mode = 1 then ls.filter (fun l => !l.phys) else ls

/-- The certificate's bound. -/
def capOf (c : RCert) (ls : List Lab) : ℕ :=
  if c.mode = 2 then ls.length
  else if c.mode = 1 then S.m - c.W.length + (ls.filter Lab.phys).length
  else S.m - c.W.length

def certOK (c : RCert) (ls : List Lab) : Bool :=
  decide (c.mode = 2) ||
  (decide (c.pv.length = c.W.length) && c.pv.all (fun i => decide (i < S.m)) &&
    diagOK c.W.length S.W.N1 (fun i j => (c.W.getD j []).getD (c.pv.getD i 0) 0) &&
    c.W.all fun w => decide (w.length ≤ S.m) && (Spec.rest c ls).all (S.zeroOn w) &&
      (!(Spec.rest c ls).any Lab.phys || S.nodesZero w))

end Spec

section Cert
variable {S : Spec} {N p k : ℕ} [Fact p.Prime] (hK : S.K = bN S.P N p * 4 + 2 + S.ex)

/-- The constant vector of an integer list. -/
def vec (S : Spec) (p : ℕ) (w : List ℤ) : Fin S.m → ZMod p := fun j => ((w.getD j.val 0 : ℤ) : ZMod p)

theorem cf_vec {w : List ℤ} (hw : w.length ≤ S.m) (x : Co) :
    cf S (p := p) x (vec S p w) = ((S.yv w x : ℤ) : ZMod p) := by
  have h1 := dot_sum w (S.zrow x) S.m hw
  rw [Spec.yv, ← h1, ← Fin.sum_univ_eq_sum_range (fun j => (S.zrow x).getD j 0 * w.getD j 0)]
  simp [cf, vec, LinearMap.sum_apply]

theorem blkL_ins (g : Geo S N p) {u : Fin 4} {m : ℕ} (hm : m < S.b) (y : Fin S.m → ZMod p) :
    blkL hK u m (insZ S hK y) = cf S (.blk m u.val) y := by
  have hbe : bN S.P N p = S.b := g.hb
  have hm' : m < bN S.P N p := hbe ▸ hm
  simp [blkL, hm', insZ, coOf]

theorem cenL_ins (u : Fin 2) (y : Fin S.m → ZMod p) :
    cenL hK u (insZ S hK y) = cf S (.cen u.val) y := by
  simp [cenL, insZ, coOf]

theorem nodeL_vec (g : Geo S N p) {w : List ℤ} (hw : w.length ≤ S.m) (u : Fin 2) {m : ℕ}
    (hm : m < S.b + 1) :
    nodeL hK u m (insZ S hK (vec S p w)) = ((S.nodeV w u.val m : ℤ) : ZMod p) := by
  have hbe : bN S.P N p = S.b := g.hb
  have hb1 : (m < bN S.P N p) = (m < S.b) := by rw [hbe]
  simp only [nodeL, LinearMap.add_apply, Spec.nodeV, hb1]
  have e1 : (if u = 0 then (0 : Fin 4) else 1).val = u.val := by
    fin_cases u <;> rfl
  have e2 : (if u = 0 then (2 : Fin 4) else 3).val = u.val + 2 := by
    fin_cases u <;> rfl
  by_cases h1 : m < S.b
  · by_cases h2 : 0 < m
    · have h3 : m ≠ 0 := by omega
      simp only [h1, h2, h3, if_true, if_false, LinearMap.sub_apply, blkL_ins hK g h1,
        blkL_ins hK g (show m - 1 < S.b by omega), LinearMap.zero_apply, e1, e2, cf_vec hw,
        LinearMap.add_apply]
      push_cast
      ring
    · have h3 : m = 0 := by omega
      subst h3
      simp only [h1, lt_irrefl, if_true, if_false, LinearMap.sub_apply, blkL_ins hK g h1,
        LinearMap.zero_apply, e1, e2, cf_vec hw, cenL_ins]
      push_cast
      ring
  · have h3 : m = S.b := by omega
    have h4 : 0 < m := by have := g.bpos; omega
    have h5 : m ≠ 0 := by omega
    simp only [h1, h4, h5, if_true, if_false, blkL_ins hK g (show m - 1 < S.b by omega),
      LinearMap.zero_apply, e1, e2, cf_vec hw, LinearMap.add_apply]
    push_cast
    ring

theorem nodeMap_vec (g : Geo S N p) {w : List ℤ} (hw : w.length ≤ S.m)
    (h : S.nodesZero w = true) : nodeMap hK (insZ S hK (vec S p w)) = 0 := by
  have hbe : bN S.P N p = S.b := g.hb
  simp only [Spec.nodesZero, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  funext m u
  have hm : m.val < S.b + 1 := hbe ▸ m.isLt
  have h1 := h m.val hm
  show nodeL hK u m.val (insZ S hK (vec S p w)) = 0
  rw [nodeL_vec hK g hw u hm]
  fin_cases u
  · simp [h1.1]
  · simp [h1.2]

theorem eval_vec (g : Geo S N p) {w : List ℤ} (hw : w.length ≤ S.m) {l : Lab}
    (h1 : S.zeroOn w l = true) (h2 : l.phys = true → S.nodesZero w = true) :
    Lab.eval S hK l (vec S p w) = 0 := by
  have hbe : bN S.P N p = S.b := g.hb
  cases l with
  | c x =>
    simp only [Spec.zeroOn, decide_eq_true_eq] at h1
    simp [Lab.eval, cf_vec hw, h1]
  | minus F E =>
    simp only [Spec.zeroOn, decide_eq_true_eq] at h1
    have : ((S.yv w F - 2 * S.yv w E : ℤ) : ZMod p) = 0 := by rw [h1]; simp
    simpa [Lab.eval, cf_vec hw] using this
  | vbot u =>
    simp only [Spec.zeroOn, decide_eq_true_eq] at h1
    have : ((S.yv w (.blk 0 u) - S.yv w (.blk 0 (u + 2)) + S.yv w (.cen u) : ℤ) : ZMod p) = 0 := by
      rw [h1]; simp
    simpa [Lab.eval, cf_vec hw] using this
  | vtop u =>
    simp only [Spec.zeroOn, decide_eq_true_eq] at h1
    have : ((S.yv w (.blk (S.b - 1) u) + S.yv w (.blk (S.b - 1) (u + 2)) : ℤ) : ZMod p) = 0 := by
      rw [h1]; simp
    simpa [Lab.eval, cf_vec hw] using this
  | raw J s =>
    simp only [Spec.zeroOn, decide_eq_true_eq] at h1
    have := labelRow_of_node hK (insZ S hK) 0 J (S.S0 - s) (nodeMap_vec hK g hw (h2 rfl))
    simp [Lab.eval, cf_vec hw, h1, this]
  | graph J s t =>
    simp only [Spec.zeroOn, Bool.and_eq_true, decide_eq_true_eq] at h1
    have := labelRow_of_node hK (insZ S hK) 0 J (S.S0 - s) (nodeMap_vec hK g hw (h2 rfl))
    simp [Lab.eval, cf_vec hw, h1.1, h1.2, this]

/-- The span of the rows of a label list. -/
def spanL (ls : List Lab) : Submodule (ZMod p) (Dual (ZMod p) (Fin S.m → ZMod p)) :=
  Submodule.span _ (Set.range fun i : Fin ls.length => Lab.eval S hK (ls.get i))

theorem mem_spanL {ls : List Lab} {l : Lab} (h : l ∈ ls) : Lab.eval S hK l ∈ spanL hK ls := by
  obtain ⟨i, rfl⟩ := List.get_of_mem h
  exact Submodule.subset_span ⟨i, rfl⟩

theorem spanL_le {ls : List Lab} {X : Submodule (ZMod p) (Dual (ZMod p) (Fin S.m → ZMod p))}
    (h : ∀ l ∈ ls, Lab.eval S hK l ∈ X) : spanL hK ls ≤ X :=
  Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact h _ (List.get_mem _ _))

theorem spanL_mono {a b : List Lab} (h : ∀ l ∈ a, l ∈ b) : spanL (p := p) hK a ≤ spanL hK b :=
  spanL_le hK fun l hl => mem_spanL hK (h l hl)

theorem finrank_spanL_le (ls : List Lab) : finrank (ZMod p) (spanL (p := p) hK ls) ≤ ls.length := by
  have := finrank_range_le_card (R := ZMod p) (M := Dual (ZMod p) (Fin S.m → ZMod p))
    (fun i : Fin ls.length => Lab.eval (p := p) S hK (ls.get i))
  rw [Fintype.card_fin] at this
  exact this

/-- The rows of a level span its row space. -/
theorem rowSpace_Bm (c : Fin S.levels.length) :
    rowSpace (Bm (p := p) S hK c) = spanL hK (S.levels.get c).rows := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    have h1 : LinearMap.dualMap (Bm (p := p) S hK c) f =
        ∑ i, f (fun j => if i = j then 1 else 0) • Lab.eval S hK ((S.levels.get c).rows.get i) := by
      refine LinearMap.ext fun y => ?_
      rw [LinearMap.dualMap_apply, LinearMap.pi_apply_eq_sum_univ f]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Bm, LinearMap.pi_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h1]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine spanL_le hK fun l hl => ?_
    obtain ⟨i, rfl⟩ := List.get_of_mem hl
    exact ⟨LinearMap.proj i, by ext x; simp [Bm]⟩

end Cert

section Cap
variable {S : Spec} {N p : ℕ} [Fact p.Prime] (hK : S.K = bN S.P N p * 4 + 2 + S.ex)

theorem independent_of_cert (hN1 : S.W.N1 ≤ p) {c : RCert} (h1 : c.pv.length = c.W.length)
    (h2 : c.pv.all (fun i => decide (i < S.m)) = true)
    (h3 : Spec.diagOK c.W.length S.W.N1
      (fun i j => (c.W.getD j []).getD (c.pv.getD i 0) 0) = true) :
    LinearIndependent (ZMod p) (fun i : Fin c.W.length => vec S p (c.W.get i)) := by
  simp only [List.all_eq_true, decide_eq_true_eq] at h2
  rw [Fintype.linearIndependent_iff]
  intro gg hg
  have h4 := diag_zero (p := p) h3 hN1 gg fun i => ?_
  · exact fun i => congrFun h4 i
  · have hi : c.pv.getD i.val 0 < S.m := by
      have hi' : i.val < c.pv.length := by omega
      rw [List.getD_eq_getElem _ _ hi']
      exact h2 _ (List.getElem_mem hi')
    have h5 := congrFun hg ⟨c.pv.getD i.val 0, hi⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, vec] at h5
    rw [← h5]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, List.getD_eq_getElem _ _ j.isLt]
    rfl

/-- **Rank certificates are sound.** -/
theorem cap_sound (g : Geo S N p) (hN1 : S.W.N1 ≤ p) {c : RCert} {ls : List Lab}
    (h : S.certOK c ls = true) : finrank (ZMod p) (spanL (p := p) hK ls) ≤ S.capOf c ls := by
  by_cases hm2 : c.mode = 2
  · simp only [Spec.capOf, hm2, if_true]
    exact finrank_spanL_le hK ls
  simp only [Spec.certOK, Bool.or_eq_true, decide_eq_true_eq, hm2, false_or, Bool.and_eq_true,
    List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hli := independent_of_cert (p := p) hN1 h1 (by simpa using h2) h3
  set U : Submodule (ZMod p) (Fin S.m → ZMod p) :=
    Submodule.span _ (Set.range fun i : Fin c.W.length => vec S p (c.W.get i)) with hU
  have hUr : finrank (ZMod p) U = c.W.length := by
    rw [hU, finrank_span_eq_card hli, Fintype.card_fin]
  have hdim : finrank (ZMod p) (Fin S.m → ZMod p) = S.m := by simp
  have hann : finrank (ZMod p) U.dualAnnihilator = S.m - c.W.length := by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq U
    omega
  have hrest : spanL (p := p) hK (Spec.rest c ls) ≤ U.dualAnnihilator := by
    refine spanL_le hK fun l hl => ?_
    rw [Submodule.mem_dualAnnihilator]
    suffices hle : U ≤ LinearMap.ker (Lab.eval S hK l) from fun u hu => hle hu
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨⟨h5, h6⟩, h7⟩ := h4 _ (List.get_mem c.W i)
    refine eval_vec hK g h5 (h6 l hl) fun hp => ?_
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_false] at h7
    rcases h7 with h7 | h7
    · exact absurd hp (by simpa using h7 l hl)
    · exact h7
  have hle := Submodule.finrank_mono hrest
  by_cases hm1 : c.mode = 1
  · simp only [Spec.capOf, hm2, hm1, if_true, if_false, Nat.succ_ne_self, OfNat.one_ne_ofNat]
    have hsplit : spanL (p := p) hK ls ≤
        spanL hK (Spec.rest c ls) ⊔ spanL hK (ls.filter Lab.phys) := by
      refine spanL_le hK fun l hl => ?_
      by_cases hp : l.phys = true
      · exact Submodule.mem_sup_right (mem_spanL hK (List.mem_filter.mpr ⟨hl, hp⟩))
      · refine Submodule.mem_sup_left (mem_spanL hK ?_)
        simp only [Spec.rest, hm1, if_true]
        exact List.mem_filter.mpr ⟨hl, by simpa using hp⟩
    have h8 := Submodule.finrank_mono hsplit
    have h9 := Submodule.finrank_add_le_finrank_add_finrank
      (spanL (p := p) hK (Spec.rest c ls)) (spanL hK (ls.filter Lab.phys))
    have h10 := finrank_spanL_le (p := p) hK (ls.filter Lab.phys)
    omega
  · have : Spec.rest c ls = ls := by simp [Spec.rest, hm1]
    rw [this] at hle
    simp only [Spec.capOf, hm2, hm1, if_false]
    omega

end Cap

/-! ### Affine lines on the window -/

/-- `(A, B)` is the line `A + B x`. -/
abbrev Aff := ℤ × ℤ

def Aff.ev (f : Aff) (x : ℝ) : ℝ := (f.1 : ℝ) + f.2 * x
def Aff.sc (z : ℤ) (f : Aff) : Aff := (z * f.1, z * f.2)

@[simp] theorem Aff.ev_add (f g : Aff) (x : ℝ) : (f + g).ev x = f.ev x + g.ev x := by
  simp only [Aff.ev, Prod.fst_add, Prod.snd_add]; push_cast; ring
@[simp] theorem Aff.ev_sub (f g : Aff) (x : ℝ) : (f - g).ev x = f.ev x - g.ev x := by
  simp only [Aff.ev, Prod.fst_sub, Prod.snd_sub]; push_cast; ring
@[simp] theorem Aff.ev_sc (z : ℤ) (f : Aff) (x : ℝ) : (Aff.sc z f).ev x = z * f.ev x := by
  simp only [Aff.ev, Aff.sc]; push_cast; ring
@[simp] theorem Aff.ev_zero (x : ℝ) : (0 : Aff).ev x = 0 := by
  simp [Aff.ev]

/-- Sum over `0, …, n-1`. -/
def fsum {α : Type} [Add α] [Zero α] (f : ℕ → α) : ℕ → α
  | 0 => 0
  | n + 1 => fsum f n + f n

theorem ev_fsum (f : ℕ → Aff) (n : ℕ) (x : ℝ) :
    (fsum f n).ev x = ∑ j ∈ range n, (f j).ev x := by
  induction n with
  | zero => simp [fsum]
  | succ n ih => rw [fsum, Aff.ev_add, ih, Finset.sum_range_succ]

theorem fsum_int (f : ℕ → ℤ) (n : ℕ) : fsum f n = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp [fsum]
  | succ n ih => rw [fsum, ih, Finset.sum_range_succ]

/-- `x` lies in the window. -/
def Win.Xin (W : Win) (x : ℝ) : Prop := (W.aN : ℝ) ≤ W.aD * x ∧ (W.bD : ℝ) * x ≤ W.bN

/-- The line is nonnegative at both ends of the window. -/
def Win.aNN (W : Win) (f : Aff) : Bool :=
  decide (0 < W.aD) && decide (0 < W.bD) && decide (0 ≤ f.1 * W.aD + f.2 * W.aN) &&
    decide (0 ≤ f.1 * W.bD + f.2 * W.bN)

theorem Win.aNN_sound {W : Win} {f : Aff} (h : W.aNN f = true) {x : ℝ} (hx : W.Xin x) :
    0 ≤ f.ev x := by
  simp only [Win.aNN, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, r1⟩, r2⟩ := h
  have ha' : (0 : ℝ) < W.aD := by exact_mod_cast ha
  have hb' : (0 : ℝ) < W.bD := by exact_mod_cast hb
  have r1' : (0 : ℝ) ≤ f.1 * W.aD + f.2 * W.aN := by exact_mod_cast r1
  have r2' : (0 : ℝ) ≤ f.1 * W.bD + f.2 * W.bN := by exact_mod_cast r2
  by_cases hf : (0 : ℝ) ≤ f.2
  · have e1 := mul_le_mul_of_nonneg_left hx.1 hf
    have e2 : 0 ≤ (W.aD : ℝ) * f.ev x := by
      simp only [Aff.ev]; nlinarith
    exact (mul_nonneg_iff_of_pos_left ha').mp e2
  · have hf' : (f.2 : ℝ) ≤ 0 := by linarith
    have e1 := mul_le_mul_of_nonpos_left hx.2 hf'
    have e2 : 0 ≤ (W.bD : ℝ) * f.ev x := by
      simp only [Aff.ev]; nlinarith
    exact (mul_nonneg_iff_of_pos_left hb').mp e2

/-! ### The count of a chart -/

/-- The relation of a piece. -/
inductive Fam
  | whole
  | pair (a b : ℕ) (I : List ℕ) (ls : List Lab) (c : RCert) (h : Aff)
  | multi (as : List ℕ) (Is : List (List ℕ)) (ls : List Lab) (c : RCert) (h : Aff)
  | kill (zl : List ℕ) (ls : List Lab) (c : RCert) (d : ℕ)

/-- The finite description of one count piece: lines are doubled. -/
structure Cnt where
  certs : List RCert
  om : List ℕ
  fam : Fam
  B0 : ℕ
  pu : ℤ
  pv : ℤ
  pd : ℤ
  E : ℤ

def dfltLevel : Level := ⟨.zero, .z, .z, []⟩
def Spec.lev (S : Spec) (j : ℕ) : Level := S.levels.getD j dfltLevel
def Spec.rowsOf (S : Spec) (j : ℕ) : List Lab := (S.lev j).rows
/-- The doubled weight of a level. -/
def Spec.wl (S : Spec) (j : ℕ) : Aff :=
  (2 * ((S.lev j).hi.sub (S.lev j).lo).n, ((S.lev j).hi.sub (S.lev j).lo).h)
def subL (a b : List Lab) : Bool := a.all fun l => decide (l ∈ b)

namespace Cnt
variable (C : Cnt) (S : Spec)

def n : ℕ := S.levels.length
def wj (j : ℕ) : Aff := if j ∈ C.om then 0 else S.wl j
def cen : Aff := (0, 2) - fsum (fun j => if j ∈ C.om then S.wl j else 0) (n S)
def cert (j : ℕ) : RCert := C.certs.getD j ⟨2, [], []⟩
def r (j : ℕ) : ℕ := S.capOf (C.cert j) (S.rowsOf j)
def eZ : Aff := Aff.sc S.m (C.cen S) - fsum (fun j => Aff.sc (C.r S j) (C.wj S j)) (n S)
def sumI (I : List ℕ) : Aff := fsum (fun j => if j ∈ I then C.wj S j else 0) (n S)

/-- The doubled value of the piece. -/
def val : Aff :=
  match C.fam with
  | .whole => C.eZ S
  | .pair a b _ ls c h =>
    C.eZ S + Aff.sc (max 0 ((C.r S a : ℤ) + C.r S b - S.capOf c ls)) h
  | .multi as _ ls c h =>
    C.eZ S + Aff.sc (max 0 (fsum (fun i => (C.r S (as.getD i 0) : ℤ)) as.length - S.capOf c ls)) h
  | .kill zl _ _ d =>
    Aff.sc d (C.cen S) -
      fsum (fun j => if j ∈ zl then 0 else Aff.sc (min (C.r S j) d) (C.wj S j)) (n S)

def famOK : Bool :=
  match C.fam with
  | .whole => true
  | .pair a b I ls c h =>
    decide (a ≠ b) && decide (a < n S) && decide (b < n S) && decide (a ∈ I) && decide (b ∈ I) &&
    I.all (fun j => subL (S.rowsOf a) (S.rowsOf j) || subL (S.rowsOf b) (S.rowsOf j)) &&
    subL (S.rowsOf a) ls && subL (S.rowsOf b) ls && S.certOK c ls &&
    S.W.aNN h && S.W.aNN (C.wj S a - h) && S.W.aNN (C.wj S b - h) &&
    S.W.aNN (C.sumI S I - C.cen S - h)
  | .multi as Is ls c h =>
    decide (Is.length = as.length) && as.all (fun a => decide (a < n S)) &&
    (List.range as.length).all (fun i =>
      decide (as.getD i 0 ∈ Is.getD i []) &&
      (Is.getD i []).all (fun j => subL (S.rowsOf (as.getD i 0)) (S.rowsOf j)) &&
      S.W.aNN (C.cen S - C.sumI S (Is.getD i [])) &&
      subL (S.rowsOf (as.getD i 0)) ls &&
      S.W.aNN (C.wj S (as.getD i 0) - h) &&
      (List.range as.length).all (fun i' =>
        decide (i = i') || (Is.getD i []).all (fun j => decide (j ∉ Is.getD i' [])))) &&
    S.W.aNN (C.cen S) && S.certOK c ls && S.W.aNN h &&
    S.W.aNN (fsum (fun i => C.sumI S (Is.getD i [])) as.length -
      Aff.sc ((as.length : ℤ) - 1) (C.cen S) - h)
  | .kill zl ls c d =>
    zl.all (fun j => subL (S.rowsOf j) ls) && S.certOK c ls &&
      decide (d + S.capOf c ls ≤ S.m)

/-- All count checks. -/
def ok : Bool :=
  (List.range (n S)).all (fun j =>
    S.certOK (C.cert j) (S.rowsOf j) && S.W.nn (S.lev j).lo &&
    S.W.ge (S.lev j).hi (S.lev j).lo && S.W.aNN (S.wl j) &&
    decide ((2 * ((S.lev j).hi.sub (S.lev j).lo).c - ((S.lev j).hi.sub (S.lev j).lo).h).natAbs ≤
      2 * C.B0)) &&
  C.famOK S && decide (0 < C.pd) && decide (0 < C.E) &&
  decide (C.E * (S.m * (1 + n S) * C.B0) ≤ S.W.N1) &&
  S.W.aNN (Aff.sc (C.pd * C.E) (C.val S) - Aff.sc (2 * C.E) (C.pu, C.pv) - (2 * C.pd, 0))

/-- The count piece. -/
def piece : CountPiece :=
  ⟨(S.W.aN : ℝ) / S.W.aD, (S.W.bN : ℝ) / S.W.bD, (C.pu : ℝ) / C.pd, (C.pv : ℝ) / C.pd⟩

end Cnt

section Rel
variable {S : Spec} (C : Cnt) {N p : ℕ} [Fact p.Prime] (hK : S.K = bN S.P N p * 4 + 2 + S.ex)

theorem lev_get (c : Fin S.levels.length) : S.lev c.val = S.levels.get c := by
  simp [Spec.lev, List.getD_eq_getElem _ _ c.isLt]

theorem rowsOf_get (c : Fin S.levels.length) : S.rowsOf c.val = (S.levels.get c).rows := by
  rw [Spec.rowsOf, lev_get]

/-- Row spaces of the chart. -/
abbrev RC (hK : S.K = bN S.P N p * 4 + 2 + S.ex) (c : Fin S.levels.length) :
    Submodule (ZMod p) (Dual (ZMod p) (Fin S.m → ZMod p)) :=
  rowSpace (Bm (p := p) S hK c)

theorem RC_le {a b : Fin S.levels.length} (h : subL (S.rowsOf a.val) (S.rowsOf b.val) = true) :
    RC hK a ≤ RC hK b := by
  simp only [subL, List.all_eq_true, decide_eq_true_eq, rowsOf_get] at h
  simp only [RC, rowSpace_Bm]
  exact spanL_mono hK h

theorem RC_le_span {a : Fin S.levels.length} {ls : List Lab}
    (h : subL (S.rowsOf a.val) ls = true) : RC hK a ≤ spanL (p := p) hK ls := by
  simp only [subL, List.all_eq_true, decide_eq_true_eq, rowsOf_get] at h
  simp only [RC, rowSpace_Bm]
  exact spanL_mono hK h

/-- The real weights. -/
def wR (S : Spec) (C : Cnt) (x : ℝ) (j : Fin S.levels.length) : ℝ := (C.wj S j.val).ev x / 2
def wF (S : Spec) (x : ℝ) (j : Fin S.levels.length) : ℝ := (S.wl j.val).ev x / 2
def cR (S : Spec) (C : Cnt) (x : ℝ) : ℝ := (C.cen S).ev x / 2
def rR (S : Spec) (C : Cnt) (j : Fin S.levels.length) : ℝ := (C.r S j.val : ℝ)
def finI (S : Spec) (I : List ℕ) : Finset (Fin S.levels.length) :=
  Finset.univ.filter fun j => j.val ∈ I

theorem sumI_ev (I : List ℕ) (x : ℝ) : (C.sumI S I).ev x / 2 = ∑ j ∈ finI S I, wR S C x j := by
  rw [Cnt.sumI, ev_fsum, Cnt.n, ← Fin.sum_univ_eq_sum_range
    (fun j => (if j ∈ I then C.wj S j else (0 : Aff)).ev x), finI, Finset.sum_filter,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j.val ∈ I <;> simp [h, wR]

theorem eZ_ev (x : ℝ) : (C.eZ S).ev x / 2 =
    e0 (cR S C x) (wR S C x) (rR S C) (finrank (ZMod p) (Fin S.m → ZMod p)) := by
  rw [Cnt.eZ, Aff.ev_sub, Aff.ev_sc, ev_fsum, Cnt.n, ← Fin.sum_univ_eq_sum_range
    (fun j => (Aff.sc (C.r S j) (C.wj S j)).ev x)]
  simp only [e0, cR, wR, rR, Module.finrank_fin_fun, Aff.ev_sc, Int.cast_natCast, sub_div,
    Finset.sum_div]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun j _ => by ring

theorem euler_bot' {J K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype J] (c : ℝ) (w r : J → ℝ) (R : J → Submodule K (Dual K V)) (hw : ∀ j, 0 ≤ w j)
    (hr : ∀ j, (finrank K (R j) : ℝ) ≤ r j) : e0 c w r (finrank K V) ≤ euler c w R ⊥ := by
  unfold e0 euler
  have h0 : ∀ j, ((finrank K (R j ⊓ ⊥ : Submodule K (Dual K V)) : ℕ) : ℝ) = 0 := fun j => by
    rw [inf_bot_eq]; simp
  simp only [finrank_bot, Nat.cast_zero, sub_zero, h0]
  have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hr j) (hw j)
  linarith

variable {C}

/-- **The relation of the piece.** -/
theorem relation (g : Geo S N p) (hN1 : S.W.N1 ≤ p) (hf : C.famOK S = true) {x : ℝ}
    (hx : S.W.Xin x) (hw : ∀ j, 0 ≤ wR S C x j)
    (hr : ∀ j, (finrank (ZMod p) (RC hK j) : ℝ) ≤ rR S C j) :
    ∃ Sd : Submodule (ZMod p) (Dual (ZMod p) (Fin S.m → ZMod p)),
      (C.val S).ev x / 2 ≤ euler (cR S C x) (wR S C x) (RC hK) Sd := by
  simp only [Cnt.famOK] at hf
  simp only [Cnt.val]
  cases hc : C.fam with
  | whole =>
    refine ⟨⊥, ?_⟩
    simp only [eZ_ev (p := p)]
    exact euler_bot' _ _ _ _ hw hr
  | pair a b I ls c h =>
    simp only [hc, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at hf
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hab, ha⟩, hb⟩, haI⟩, hbI⟩, hanc⟩, hsa⟩, hsb⟩, hcert⟩, h0⟩, h1⟩, h2⟩, h3⟩ := hf
    have hs : (finrank (ZMod p) (RC hK ⟨a, ha⟩ ⊔ RC hK ⟨b, hb⟩ : Submodule _ _) : ℝ) ≤
        (S.capOf c ls : ℝ) := by
      have := (Submodule.finrank_mono (sup_le (RC_le_span hK (a := ⟨a, ha⟩) hsa)
        (RC_le_span hK (a := ⟨b, hb⟩) hsb))).trans
        (cap_sound hK g hN1 hcert)
      exact_mod_cast this
    have e1 := Win.aNN_sound h0 hx
    have e2 := Win.aNN_sound h1 hx
    have e3 := Win.aNN_sound h2 hx
    have e4 := Win.aNN_sound h3 hx
    simp only [Aff.ev_sub] at e2 e3 e4
    obtain ⟨Sd, hSd⟩ := exists_euler_pair (cR S C x) (wR S C x) (rR S C) (RC hK) hw hr
      ⟨a, ha⟩ ⟨b, hb⟩ (fun e => hab (congrArg Fin.val e)) (finI S I)
      (by simp [finI, haI]) (by simp [finI, hbI])
      (fun j hj => by
        have hj' : j.val ∈ I := by simpa [finI] using hj
        rcases hanc _ hj' with h | h
        · exact Or.inl (RC_le hK h)
        · exact Or.inr (RC_le hK h))
      (S.capOf c ls : ℝ) hs (h.ev x / 2) (by linarith)
      (by simp only [wR]; linarith) (by simp only [wR]; linarith)
      (by rw [← sumI_ev]; simp only [cR]; linarith)
    refine ⟨Sd, le_trans (le_of_eq ?_) hSd⟩
    simp only [Aff.ev_add, Aff.ev_sc, add_div, eZ_ev (p := p), rR]
    congr 1
    push_cast
    ring
  | multi as Is ls c h =>
    simp only [hc, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
      List.mem_range] at hf
    obtain ⟨⟨⟨⟨⟨⟨hlen, has⟩, hall⟩, hc0⟩, hcert⟩, h0⟩, hτ⟩ := hf
    have hai : ∀ i : Fin as.length, as.getD i.val 0 < S.levels.length := by
      intro i
      rw [List.getD_eq_getElem _ _ i.isLt]
      exact has _ (List.getElem_mem i.isLt)
    have e1 := Win.aNN_sound h0 hx
    have e0' := Win.aNN_sound hc0 hx
    have e4 := Win.aNN_sound hτ hx
    simp only [Aff.ev_sub, Aff.ev_sc, ev_fsum] at e4
    have hτ' : h.ev x / 2 ≤ (∑ i : Fin as.length, ∑ j ∈ finI S (Is.getD i.val []), wR S C x j) -
        (((Fintype.card (Fin as.length) : ℕ) : ℝ) - 1) * cR S C x := by
      simp only [← sumI_ev, Fintype.card_fin, cR]
      rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun i => (C.sumI S (Is.getD i [])).ev x)]
      push_cast at e4
      linarith
    obtain ⟨Sd, hSd⟩ := exists_euler_multi (ι := Fin as.length) (cR S C x) (wR S C x) (rR S C)
      (RC hK) hw hr (fun i => ⟨as.getD i.val 0, hai i⟩) (fun i => finI S (Is.getD i.val []))
      (fun i => by
        have := (hall i.val i.isLt).1.1.1.1.1
        simpa [finI] using this)
      (fun i i' hne => by
        rw [Finset.disjoint_left]
        intro j hj hj'
        have h1 : j.val ∈ Is.getD i.val [] := by simpa [finI] using hj
        have h2 : j.val ∈ Is.getD i'.val [] := by simpa [finI] using hj'
        rcases (hall i.val i.isLt).2 i'.val i'.isLt with h3 | h3
        · exact hne (Fin.ext h3)
        · exact h3 _ h1 h2)
      (fun i j hj => by
        have h1 : j.val ∈ Is.getD i.val [] := by simpa [finI] using hj
        exact RC_le hK ((hall i.val i.isLt).1.1.1.1.2 _ h1))
      (by simp only [cR]; linarith)
      (fun i => by
        have := Win.aNN_sound (hall i.val i.isLt).1.1.1.2 hx
        simp only [Aff.ev_sub] at this
        rw [← sumI_ev]
        simp only [cR]
        linarith)
      (S.capOf c ls : ℝ)
      (by
        have h1 : (⨆ i : Fin as.length, RC hK ⟨as.getD i.val 0, hai i⟩) ≤
            spanL (p := p) hK ls :=
          iSup_le fun i => RC_le_span hK (a := ⟨as.getD i.val 0, hai i⟩)
            (hall i.val i.isLt).1.1.2
        have := (Submodule.finrank_mono h1).trans (cap_sound hK g hN1 hcert)
        exact_mod_cast this)
      (h.ev x / 2) (by linarith)
      (fun i => by
        have := Win.aNN_sound (hall i.val i.isLt).1.2 hx
        simp only [Aff.ev_sub] at this
        simp only [wR]
        linarith)
      hτ'
    refine ⟨Sd, le_trans (le_of_eq ?_) hSd⟩
    simp only [Aff.ev_add, Aff.ev_sc, add_div, eZ_ev (p := p), rR, fsum_int]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i => (C.r S (as.getD i 0) : ℤ))]
    push_cast
    ring
  | kill zl ls c d =>
    simp only [hc, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hf
    obtain ⟨⟨hz, hcert⟩, hd⟩ := hf
    obtain ⟨Sd, hSd⟩ := exists_euler_kill (cR S C x) (wR S C x) (rR S C) (RC hK) hw hr
      (spanL (p := p) hK ls) (S.capOf c ls) (cap_sound hK g hN1 hcert) (finI S zl)
      (fun j hj => RC_le_span hK (hz j.val (by simpa [finI] using hj))) d (by simpa using hd)
    refine ⟨Sd, le_trans (le_of_eq ?_) hSd⟩
    have hcomp : (finI S zl)ᶜ = Finset.univ.filter fun j => j.val ∉ zl := by
      ext j
      simp [finI]
    rw [hcomp, Finset.sum_filter]
    simp only [Aff.ev_sub, Aff.ev_sc, ev_fsum, Cnt.n, sub_div]
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => (if j ∈ zl then (0 : Aff) else Aff.sc (min (C.r S j : ℤ) d) (C.wj S j)).ev x),
      Finset.sum_div]
    congr 1
    · simp only [cR, Int.cast_natCast]
      ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : j.val ∈ zl
      · simp [h]
      · simp only [h, if_false, not_false_eq_true, if_true, Aff.ev_sc, wR, rR]
        push_cast
        ring

/-- Compression: the omitted levels lower the central coefficient. -/
theorem euler_om (hK : S.K = bN S.P N p * 4 + 2 + S.ex) {x : ℝ} (hw : ∀ j, 0 ≤ wF S x j)
    (Sd : Submodule (ZMod p) (Dual (ZMod p) (Fin S.m → ZMod p))) :
    euler (cR S C x) (wR S C x) (RC hK) Sd ≤ euler x (wF S x) (RC hK) Sd := by
  classical
  set O : Finset (Fin S.levels.length) := finI S C.om with hO
  have h1 := euler_compress x (wF S x) (RC hK) hw O Sd
  refine le_trans (le_of_eq ?_) h1
  have hc : cR S C x = x - ∑ j ∈ O, wF S x j := by
    simp only [cR, Cnt.cen, Aff.ev_sub, ev_fsum, Cnt.n, hO, finI, Finset.sum_filter, wF]
    rw [← Fin.sum_univ_eq_sum_range (fun j => (if j ∈ C.om then S.wl j else (0 : Aff)).ev x),
      sub_div, Finset.sum_congr rfl (g := fun j : Fin S.levels.length =>
        if j.val ∈ C.om then 2 * ((S.wl j.val).ev x / 2) else 0)]
    · simp only [Aff.ev]
      rw [show (∑ j : Fin S.levels.length, if j.val ∈ C.om then 2 * ((((S.wl j.val).1 : ℝ) +
          ((S.wl j.val).2 : ℝ) * x) / 2) else 0) = 2 * ∑ j : Fin S.levels.length,
          if j.val ∈ C.om then (((S.wl j.val).1 : ℝ) + ((S.wl j.val).2 : ℝ) * x) / 2 else 0 by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp]
      push_cast
      ring
    · intro j _
      by_cases h : j.val ∈ C.om
      · simp only [h, if_true]; ring
      · simp [h]
  unfold euler
  rw [hc]
  congr 1
  have h2 : ∀ j ∈ Oᶜ, wF S x j * ((finrank (ZMod p) (RC hK j) : ℝ) -
      finrank (ZMod p) (RC hK j ⊓ Sd : Submodule _ _)) =
      wR S C x j * ((finrank (ZMod p) (RC hK j) : ℝ) -
      finrank (ZMod p) (RC hK j ⊓ Sd : Submodule _ _)) := by
    intro j hj
    have hj' : j.val ∉ C.om := by simpa [hO, finI] using hj
    simp [wF, wR, Cnt.wj, hj']
  rw [Finset.sum_congr rfl h2]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
  have hj' : j.val ∈ C.om := by simpa [hO, finI] using hj
  simp [wR, Cnt.wj, hj']

end Rel

/-- The closing arithmetic of a piece. -/
theorem piece_arith {u v d e A x N P M nu : ℝ} (hd : 0 < d) (he : 0 < e) (hN : 0 ≤ N)
    (hc : 0 ≤ d * e * A - 2 * e * (u + v * x) - 2 * d) (hNx : N * x = P) (hM : e * M ≤ N)
    (hnu : N * (A / 2) - M ≤ nu) : u / d * N + v / d * P - 2 ≤ nu := by
  have h1 : (u + v * x) / d ≤ A / 2 - 1 / e := by
    rw [div_le_iff₀ hd]
    have h2 : (A / 2 - 1 / e) * d - (u + v * x) =
        (d * e * A - 2 * e * (u + v * x) - 2 * d) / (2 * e) := by
      field_simp
      ring
    have h3 : 0 ≤ (d * e * A - 2 * e * (u + v * x) - 2 * d) / (2 * e) := by positivity
    linarith
  have h4 : M ≤ N * (1 / e) := by
    rw [mul_one_div, le_div_iff₀ he]
    linarith
  have h5 : u / d * N + v / d * P = N * ((u + v * x) / d) := by
    rw [← hNx]
    field_simp
  have h6 := mul_le_mul_of_nonneg_left h1 hN
  nlinarith

/-- **One chart reaches a `PieceBound`, with nothing assumed but finite checks.** -/
theorem pieceBound_of_check {S : Spec} {C : Cnt} (hS : S.Check = true) (hC : C.ok S = true) :
    PieceBound S.P (C.piece S) S.W.N1 := by
  intro N p hN1 hN hp hp2 hH ha hb
  haveI : Fact p.Prime := ⟨hp⟩
  simp only [Cnt.ok, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hC
  obtain ⟨⟨⟨⟨⟨hlev, hfam⟩, hpd⟩, hE⟩, hM⟩, hmar⟩ := hC
  have hW := hmar
  simp only [Win.aNN, Bool.and_eq_true, decide_eq_true_eq] at hW
  obtain ⟨⟨⟨haD, hbD⟩, -⟩, -⟩ := hW
  have haD' : (0 : ℝ) < S.W.aD := by exact_mod_cast haD
  have hbD' : (0 : ℝ) < S.W.bD := by exact_mod_cast hbD
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpR : (p : ℝ) = 2 * k + 1 := by exact_mod_cast hk
  simp only [Cnt.piece] at ha hb ⊢
  rw [div_mul_eq_mul_div, div_lt_iff₀ haD'] at ha
  rw [div_mul_eq_mul_div, le_div_iff₀ hbD'] at hb
  have hm : S.W.Mem N k := by
    refine ⟨hN1, ?_, ?_⟩
    · have : ((S.W.aN * N : ℤ) : ℝ) ≤ ((S.W.aD * (2 * k + 1) : ℤ) : ℝ) := by
        push_cast
        rw [← hpR]
        linarith
      exact_mod_cast this
    · have : ((S.W.bD * (2 * k + 1) : ℤ) : ℝ) ≤ ((S.W.bN * N : ℤ) : ℝ) := by
        push_cast
        rw [← hpR]
        linarith
      exact_mod_cast this
  set x : ℝ := (p : ℝ) / N with hxdef
  have hNx : (N : ℝ) * x = p := by
    rw [hxdef]
    field_simp
  have hx : S.W.Xin x := by
    constructor
    · have h1 : (S.W.aN : ℝ) * N ≤ S.W.aD * x * N := by
        have : (S.W.aD : ℝ) * x * N = S.W.aD * p := by rw [← hNx]; ring
        linarith
      exact le_of_mul_le_mul_right h1 hNr
    · have h1 : (S.W.bD : ℝ) * x * N ≤ S.W.bN * N := by
        have : (S.W.bD : ℝ) * x * N = S.W.bD * p := by rw [← hNx]; ring
        linarith
      exact le_of_mul_le_mul_right h1 hNr
  have hgeo : S.geoOK = true := by
    simp only [Spec.Check, Bool.and_eq_true] at hS
    exact hS.1.1.1.1
  have g : Geo S N p := geo_of_check hgeo hm hk
  have hK : S.K = bN S.P N p * 4 + 2 + S.ex := by simp [Spec.K, g.hb]
  have hN1p : S.W.N1 ≤ p := hN1.trans g.hp1
  have I := chartHost hK hS hm hk hp2 g.hn
  have hwF : ∀ j, 0 ≤ wF S x j := fun j => by
    have := Win.aNN_sound (hlev j.val j.isLt).1.2 hx
    simp only [wF]
    linarith
  have hwR : ∀ j, 0 ≤ wR S C x j := fun j => by
    by_cases h : j.val ∈ C.om
    · simp [wR, Cnt.wj, h]
    · simpa [wR, wF, Cnt.wj, h] using hwF j
  have hr : ∀ j, (finrank (ZMod p) (RC (p := p) hK j) : ℝ) ≤ rR S C j := fun j => by
    have h1 := cap_sound hK g hN1p (hlev j.val j.isLt).1.1.1.1
    rw [rowsOf_get, ← rowSpace_Bm] at h1
    have h2 : finrank (ZMod p) (RC (p := p) hK j) ≤ C.r S j.val := by
      rw [Cnt.r, rowsOf_get]
      exact h1
    simp only [rR]
    exact_mod_cast h2
  obtain ⟨Sd, hSd⟩ := relation hK g hN1p hfam hx hwR hr
  have hrel : ∃ Sd : Submodule (ZMod p) (Dual (ZMod p) (Fin S.m → ZMod p)),
      (C.val S).ev x / 2 ≤ euler x (wF S x) (fun c => rowSpace (Bm (p := p) S hK c)) Sd :=
    ⟨Sd, hSd.trans (euler_om hK hwF Sd)⟩
  have hw : ∀ c : Fin S.levels.length, ((wdN S (N := N) k c : ℕ) : ℝ) = N * wF S x c +
      (((2 * ((S.lev c.val).hi.sub (S.lev c.val).lo).c -
        ((S.lev c.val).hi.sub (S.lev c.val).lo).h : ℤ) : ℝ) / 2) := fun c => by
    have h1 := Win.nn_sound (hlev c.val c.isLt).1.1.1.2 hm
    have h2 := Win.ge_sound (hlev c.val c.isLt).1.1.2 hm
    have h3 : (((wdN S (N := N) k c : ℕ) : ℤ)) =
        ((S.lev c.val).hi.sub (S.lev c.val).lo).ev N k := by
      rw [Form.ev_sub]
      simp only [wdN, ← lev_get]
      omega
    have h4 : ((wdN S (N := N) k c : ℕ) : ℝ) =
        ((((S.lev c.val).hi.sub (S.lev c.val).lo).ev N k : ℤ) : ℝ) := by
      exact_mod_cast h3
    rw [h4]
    simp only [wF, Spec.wl, Aff.ev, Form.ev]
    generalize (S.lev c.val).hi.sub (S.lev c.val).lo = f
    have h5 : (N : ℝ) * ((f.h : ℝ) * x) = f.h * (2 * k + 1) := by
      rw [mul_left_comm, hNx, hpR]
    push_cast
    linear_combination (-1 / 2 : ℝ) * h5
  have hbw : ∀ c : Fin S.levels.length, |(((2 * ((S.lev c.val).hi.sub (S.lev c.val).lo).c -
      ((S.lev c.val).hi.sub (S.lev c.val).lo).h : ℤ) : ℝ) / 2)| ≤ (C.B0 : ℝ) := fun c => by
    have h1 := (hlev c.val c.isLt).2
    generalize (2 * ((S.lev c.val).hi.sub (S.lev c.val).lo).c -
      ((S.lev c.val).hi.sub (S.lev c.val).lo).h : ℤ) = z at h1 ⊢
    rw [abs_div, abs_two, div_le_iff₀ (by norm_num), ← Int.cast_abs, Int.abs_eq_natAbs]
    have : ((z.natAbs : ℤ) : ℝ) ≤ ((2 * C.B0 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this ⊢
    linarith
  have hnu := SourceTemplate.nullity_ge_scaled I g.adm hN hp2 hH (by simp) x 0 (C.B0 : ℝ)
    ((C.val S).ev x / 2) (wF S x) _ (by rw [hNx]; simp) hw (by simp) hbw hrel
  have hE' : (0 : ℝ) < C.E := by exact_mod_cast hE
  have hpd' : (0 : ℝ) < C.pd := by exact_mod_cast hpd
  have hc := Win.aNN_sound hmar hx
  simp only [Aff.ev_sub, Aff.ev_sc] at hc
  have hM' : (C.E : ℝ) * ((S.m : ℝ) * (1 + (Cnt.n S : ℝ)) * C.B0) ≤ N := by
    have h1 : ((C.E * (S.m * (1 + Cnt.n S) * C.B0) : ℤ) : ℝ) ≤ ((S.W.N1 : ℤ) : ℝ) := by
      exact_mod_cast hM
    have h2 : ((S.W.N1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN1
    push_cast at h1
    linarith
  refine piece_arith (x := x) (A := (C.val S).ev x)
    (M := (S.m : ℝ) * (1 + (Cnt.n S : ℝ)) * C.B0) hpd' hE' hNr.le ?_ hNx hM' ?_
  · simpa [Aff.ev, Aff.sc] using hc
  · simpa [Cnt.n] using hnu

theorem piece_a_pos {S : Spec} (C : Cnt) (hS : S.Check = true) : 0 < (C.piece S).a := by
  have hg : S.geoOK = true := by
    simp only [Spec.Check, Bool.and_eq_true] at hS
    exact hS.1.1.1.1
  simp only [Spec.geoOK, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, h4⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg
  simp only [Win.ge, Win.nn, Bool.and_eq_true, decide_eq_true_eq] at h4
  have h5 : 0 < S.W.aD := h4.1.1.1.1.1
  have h6 : (0 : ℝ) < S.W.aD := by exact_mod_cast h5
  have h7 : (0 : ℝ) < S.W.aN := by exact_mod_cast lt_of_lt_of_le h5 h3
  exact div_pos h7 h6

/-- **`countLB` from finite checks.**  A list of checked pieces of one design gives a nullity lower
bound carrying every piece. -/
theorem exists_countLB_of_checks (P : Parameters) (cs : List (Spec × Cnt))
    (h : ∀ c ∈ cs, c.1.P = P ∧ c.1.Check = true ∧ c.2.ok c.1 = true) :
    ∃ (lb : NullityLB P) (N0 : ℕ), ∀ c ∈ cs, ∀ N p : ℕ, N0 ≤ N →
      (c.2.piece c.1).a * N < p → (p : ℝ) ≤ (c.2.piece c.1).b * N → P.H N < p ^ 2 ∧
      (c.2.piece c.1).c0 * N + (c.2.piece c.1).c1 * p - 2 ≤ (lb.kap N p : ℝ) := by
  obtain ⟨lb, N0, h1⟩ := exists_countLB P (cs.map fun c => c.2.piece c.1)
    (fun w hw => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
      exact piece_a_pos _ (h c hc).2.1)
    (fun w hw => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
      obtain ⟨e, h2, h3⟩ := h c hc
      exact ⟨c.1.W.N1, e ▸ pieceBound_of_check h2 h3⟩)
  exact ⟨lb, N0, fun c hc => h1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩


end
end CatalanMeasure.GenD.Signed.Count.ChartSource

#print axioms CatalanMeasure.GenD.Signed.Count.ChartSource.chartHost
#print axioms CatalanMeasure.GenD.Signed.Count.ChartSource.sourceRows
#print axioms CatalanMeasure.GenD.Signed.Count.ChartSource.cap_sound
#print axioms CatalanMeasure.GenD.Signed.Count.ChartSource.pieceBound_of_check
#print axioms CatalanMeasure.GenD.Signed.Count.ChartSource.exists_countLB_of_checks

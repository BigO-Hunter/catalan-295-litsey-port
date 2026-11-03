module
public import CatalanMeasure.GenD.ResRec
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
/-! Native integer source recurrence certificates, independent of physical hosts.
This helper belongs to the generic physical-source bridge. -/
namespace CatalanMeasure.GenD.Uniform.W.Charts6
open OAI.InternalCatalan CatalanMeasure.GenD
noncomputable section
variable {p : Nat} [Fact p.Prime]

/-- Integer table getter with the same zero-default convention as ResRec. -/
def intAt : List Int → Nat → Int
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => intAt xs i

/-- Residue view used only by the generic proof; data checks stay in Int. -/
def scaledResidues (p : Nat) [Fact p.Prime] (Z : Int) (xs : List Int) : List Nat :=
  xs.map (fun x => (((x : ZMod p) / (Z : ZMod p)).val))

theorem scaledResidues_at (Z : Int) (xs : List Int) (i : Nat) :
    (ResRec.tl (scaledResidues p Z xs) i : ZMod p) =
      (intAt xs i : ZMod p) / (Z : ZMod p) := by
  induction xs generalizing i with
  | nil => simp [scaledResidues, ResRec.tl, ResRec.nth, intAt]
  | cons x xs ih =>
    cases i with
    | zero => simp [scaledResidues, ResRec.tl, ResRec.nth, intAt]
    | succ i => simpa [scaledResidues, ResRec.tl, ResRec.nth, intAt] using ih i

/-- Checked cleared scalar moments give their actual rational residues at every
prime avoiding the explicit common scale. This does not test a single prime. -/
theorem int_ms_sound (N : Nat) (hN : N + 2 < p)
    (Z : Int) (hZ : (Z : ZMod p) ≠ 0) (MS : List Int)
    (h0 : intAt MS 0 = 2 * Z)
    (hodd : ∀ i, i < N → i % 2 = 1 → intAt MS i = 0)
    (hev : ∀ m, 2 * m + 2 < N →
      (2 * m + 3 : Int) * intAt MS (2 * m + 2) =
        (2 * m + 2 : Int) * intAt MS (2 * m)) :
    ∀ i, i < N → ResRec.Gd p (momentScalar i)
      ((intAt MS i : ZMod p) / (Z : ZMod p)) := by
  have hbase : (ResRec.tl (scaledResidues p Z MS) 0 : ZMod p) = 2 := by
    rw [scaledResidues_at, h0]
    simp [hZ]
  have ho : ∀ i, i < N → i % 2 = 1 →
      (ResRec.tl (scaledResidues p Z MS) i : ZMod p) = 0 := by
    intro i hi hod
    rw [scaledResidues_at, hodd i hi hod]
    simp
  have he : ∀ m, 2 * m + 2 < N →
      (((2 * m + 3) * ResRec.tl (scaledResidues p Z MS) (2 * m + 2) : Nat) : ZMod p) =
        (((2 * m + 2) * ResRec.tl (scaledResidues p Z MS) (2 * m) : Nat) : ZMod p) := by
    intro m hm
    have e := congrArg (fun z : Int => (z : ZMod p)) (hev m hm)
    push_cast at e ⊢
    rw [scaledResidues_at, scaledResidues_at]
    simpa only [mul_div_assoc] using congrArg (fun z : ZMod p => z / (Z : ZMod p)) e
  intro i hi
  exact ResRec.Gd.val (scaledResidues_at Z MS i)
    (ResRec.ms_sound N hN (scaledResidues p Z MS) hbase ho he i hi)

/-- Native integer-only scalar table checker. The length and positive scale are
part of the finite certificate; all odd entries are explicitly checked. -/
def intScalarCheck (N : Nat) (Z : Int) (MS : List Int) : Bool :=
  decide (0 < Z) && decide (MS.length = N) && decide (intAt MS 0 = 2 * Z) &&
    (List.range N).all (fun i => decide (i % 2 = 1 → intAt MS i = 0)) &&
    (List.range N).all (fun m => decide (2 * m + 2 < N →
      (2 * m + 3 : Int) * intAt MS (2 * m + 2) =
        (2 * m + 2 : Int) * intAt MS (2 * m)))

theorem intScalarCheck_sound (N : Nat) (hN : N + 2 < p)
    (Z : Int) (hZ : (Z : ZMod p) ≠ 0) (MS : List Int)
    (hc : intScalarCheck N Z MS = true) :
    0 < Z ∧ MS.length = N ∧ ∀ i, i < N →
      ResRec.Gd p (momentScalar i) ((intAt MS i : ZMod p) / (Z : ZMod p)) := by
  simp only [intScalarCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hc
  refine ⟨hc.1.1.1.1, hc.1.1.1.2, ?_⟩
  exact int_ms_sound N hN Z hZ MS hc.1.1.2 hc.1.2 (fun m hm => hc.2 m (by omega) hm)


/-- Exact cleared boundary-minus recurrences inherit the existing uniform
rational-residue theorem. The common scale is never evaluated in Rat. -/
theorem int_bm_sound (N : Nat) (hN : N + 2 < p)
    (Z : Int) (hZ : (Z : ZMod p) ≠ 0) (MS BM : List Int)
    (hms : ∀ i, i < N → ResRec.Gd p (momentScalar i)
      ((intAt MS i : ZMod p) / (Z : ZMod p)))
    (h0 : intAt BM 0 = 0) (h1 : intAt BM 1 = 2 * Z)
    (hstep : ∀ d, d + 2 < N →
      (d + 2 : Int) * intAt BM (d + 2) =
        (d + 1 : Int) * intAt BM d + intAt MS d + intAt MS (d + 1)) :
    ∀ d, d < N → ResRec.Gd p (boundaryMinus d)
      ((intAt BM d : ZMod p) / (Z : ZMod p)) := by
  have hs : ∀ i, i < N → ResRec.Gd p (momentScalar i)
      (ResRec.tl (scaledResidues p Z MS) i : ZMod p) := by
    intro i hi
    exact ResRec.Gd.val (scaledResidues_at Z MS i).symm (hms i hi)
  have hb0 : (ResRec.tl (scaledResidues p Z BM) 0 : ZMod p) = 0 := by
    rw [scaledResidues_at, h0]
    simp
  have hb1 : (ResRec.tl (scaledResidues p Z BM) 1 : ZMod p) = 2 := by
    rw [scaledResidues_at, h1]
    simp [hZ]
  have he : ∀ d, d + 2 < N →
      (((d + 2) * ResRec.tl (scaledResidues p Z BM) (d + 2) : Nat) : ZMod p) =
        (((d + 1) * ResRec.tl (scaledResidues p Z BM) d +
          ResRec.tl (scaledResidues p Z MS) d +
          ResRec.tl (scaledResidues p Z MS) (d + 1) : Nat) : ZMod p) := by
    intro d hd
    have e := congrArg (fun z : Int => (z : ZMod p)) (hstep d hd)
    push_cast at e ⊢
    rw [scaledResidues_at, scaledResidues_at, scaledResidues_at, scaledResidues_at]
    simpa only [add_div, mul_div_assoc] using
      congrArg (fun z : ZMod p => z / (Z : ZMod p)) e
  intro d hd
  exact ResRec.Gd.val (scaledResidues_at Z BM d)
    (ResRec.bm_sound N hN (scaledResidues p Z MS) (scaledResidues p Z BM)
      hs hb0 hb1 he d hd)

/-- Cleared reciprocal table entries are actual inverses after normalization. -/
theorem int_inverse_sound (Z : Int) (hZ : (Z : ZMod p) ≠ 0)
    (IV : List Int) {n : Nat} (he : (n : Int) * intAt IV n = Z) :
    ((n * ResRec.tl (scaledResidues p Z IV) n : Nat) : ZMod p) = 1 := by
  have e := congrArg (fun z : Int => (z : ZMod p)) he
  push_cast at e ⊢
  rw [scaledResidues_at, ← mul_div_assoc, e]
  exact div_self hZ

/-- Cleared boundary-plus recurrence, including its reciprocal source. -/
theorem int_bp_sound (N : Nat) (hN : N + 2 < p)
    (Z : Int) (hZ : (Z : ZMod p) ≠ 0) (BP IV : List Int)
    (hIV : ∀ n, 0 < n → n < N → (n : Int) * intAt IV n = Z)
    (h0 : intAt BP 0 = 0) (h1 : intAt BP 1 = 0)
    (hstep : ∀ d, d + 2 < N →
      (d + 1 : Int) * intAt BP (d + 2) =
        (d : Int) * intAt BP d + 2 * intAt IV (d + 1)) :
    ∀ d, d < N → ResRec.Gd p (boundaryPlus d)
      ((intAt BP d : ZMod p) / (Z : ZMod p)) := by
  have hiv : ∀ n, 0 < n → n < N →
      ((n * ResRec.tl (scaledResidues p Z IV) n : Nat) : ZMod p) = 1 := by
    intro n hn hlt
    exact int_inverse_sound Z hZ IV (hIV n hn hlt)
  have hb0 : (ResRec.tl (scaledResidues p Z BP) 0 : ZMod p) = 0 := by
    rw [scaledResidues_at, h0]
    simp
  have hb1 : (ResRec.tl (scaledResidues p Z BP) 1 : ZMod p) = 0 := by
    rw [scaledResidues_at, h1]
    simp
  have he : ∀ d, d + 2 < N →
      (((d + 1) * ResRec.tl (scaledResidues p Z BP) (d + 2) : Nat) : ZMod p) =
        ((d * ResRec.tl (scaledResidues p Z BP) d +
          2 * ResRec.tl (scaledResidues p Z IV) (d + 1) : Nat) : ZMod p) := by
    intro d hd
    have e := congrArg (fun z : Int => (z : ZMod p)) (hstep d hd)
    push_cast at e ⊢
    rw [scaledResidues_at, scaledResidues_at, scaledResidues_at]
    simpa only [add_div, mul_div_assoc] using
      congrArg (fun z : ZMod p => z / (Z : ZMod p)) e
  intro d hd
  exact ResRec.Gd.val (scaledResidues_at Z BP d)
    (ResRec.bp_sound N hN (scaledResidues p Z BP) (scaledResidues p Z IV)
      hiv hb0 hb1 he d hd)


/-- Cleared first harmonic table with an exact integer increment. -/
theorem int_h1_sound (N : Nat) (hN : N < p)
    (Z : Int) (hZ : (Z : ZMod p) ≠ 0) (H1 IV : List Int)
    (hIV : ∀ n, 0 < n → n < N + 1 → (n : Int) * intAt IV n = Z)
    (h0 : intAt H1 0 = 0)
    (hstep : ∀ n, n + 1 < N + 1 →
      intAt H1 (n + 1) = intAt H1 n + intAt IV (n + 1)) :
    ∀ n, n < N + 1 → ResRec.Gd p (harmonicRat 1 n)
      ((intAt H1 n : ZMod p) / (Z : ZMod p)) := by
  have hiv : ∀ n, 0 < n → n < N + 1 →
      ((n * ResRec.tl (scaledResidues p Z IV) n : Nat) : ZMod p) = 1 := by
    intro n hn hlt
    exact int_inverse_sound Z hZ IV (hIV n hn hlt)
  have hb : (ResRec.tl (scaledResidues p Z H1) 0 : ZMod p) = 0 := by
    rw [scaledResidues_at, h0]
    simp
  have he : ∀ n, n + 1 < N + 1 →
      (ResRec.tl (scaledResidues p Z H1) (n + 1) : ZMod p) =
        ((ResRec.tl (scaledResidues p Z H1) n +
          ResRec.tl (scaledResidues p Z IV) (n + 1) : Nat) : ZMod p) := by
    intro n hn
    have e := congrArg (fun z : Int => (z : ZMod p)) (hstep n hn)
    push_cast at e ⊢
    rw [scaledResidues_at, scaledResidues_at, scaledResidues_at]
    simpa only [add_div] using congrArg (fun z : ZMod p => z / (Z : ZMod p)) e
  intro n hn
  exact ResRec.Gd.val (scaledResidues_at Z H1 n)
    (ResRec.h1_sound N hN (scaledResidues p Z H1) (scaledResidues p Z IV) hiv hb he n hn)

/-- Integer two-dimensional source table, with explicit zero defaults. -/
def intAt2 (T : List (List Int)) (i j : Nat) : Int := intAt (T.getD i []) j

/-- Cleared moment diagonal equations prove both the actual rational residue
and its denominator unit, avoiding the weaker residue-only interface. -/
theorem int_moment_sound (H L : Nat) (hH : H + 3 < p) (hLH : L ≤ H)
    (Z : Int) (hZ : (Z : ZMod p) ≠ 0) (MS BM BP : List Int) (MT : List (List Int))
    (hms : ∀ i, i < H → ResRec.Gd p (momentScalar i)
      ((intAt MS i : ZMod p) / (Z : ZMod p)))
    (hbm : ∀ i, i < H → ResRec.Gd p (boundaryMinus i)
      ((intAt BM i : ZMod p) / (Z : ZMod p)))
    (hbp : ∀ j, j < L → ResRec.Gd p (boundaryPlus j)
      ((intAt BP j : ZMod p) / (Z : ZMod p)))
    (hcol : ∀ i, i < H → intAt2 MT i 0 = intAt BM i)
    (hrow : ∀ j, j < L → intAt2 MT 0 j = intAt BP j)
    (hdiag : ∀ i j, i + 1 < H → j + 1 < L →
      (j + 1 : Int) * (intAt2 MT i j - intAt2 MT (i + 1) (j + 1)) = intAt MS i) :
    ∀ i j, i < H → j < L → ResRec.Gd p (momentRat i j)
      ((intAt2 MT i j : ZMod p) / (Z : ZMod p)) := by
  refine ResRec.diag_sound momentRat
    (fun i j => momentScalar i / ((j + 1 : Nat) : Rat))
    (fun i j => (intAt2 MT i j : ZMod p) / (Z : ZMod p))
    (fun i j => ((intAt MS i : ZMod p) / (Z : ZMod p)) *
      (((j + 1 : Nat) : ZMod p)⁻¹)) H L momentRat_step ?_ ?_ ?_ ?_
  · intro i j hi hj
    simpa only [div_eq_mul_inv, one_mul] using
      ResRec.Gd.mul (hms i (by omega))
        (ResRec.Gd.inv_nat (p := p) (n := j + 1) (by omega) (by omega))
  · intro i j hi hj
    have hn : ((j + 1 : Nat) : ZMod p) ≠ 0 :=
      ResRec.natCast_ne_zero_of_lt (by omega) (by omega)
    rw [eq_mul_inv_iff_mul_eq₀ hn]
    have e := congrArg (fun z : Int => (z : ZMod p)) (hdiag i j hi hj)
    push_cast at e
    have ed := congrArg (fun z : ZMod p => z / (Z : ZMod p)) e
    push_cast
    convert ed using 1 <;> ring
  · intro i hi
    rw [momentRat_zero_right, hcol i hi]
    exact hbm i hi
  · intro j hj
    rw [momentRat_zero_left, hrow j hj]
    exact hbp j hj



/-- Cleared zeta table, retaining both the denominator unit and actual residue. -/
theorem int_zeta_sound (H L : Nat) (hH : H + 3 < p) (hLH : L ≤ H)
    (Z : Int) (hZ : (Z : ZMod p) ≠ 0) (H1 : List Int) (ZT : List (List Int))
    (hh1 : ∀ n, n < H + 1 → ResRec.Gd p (harmonicRat 1 n)
      ((intAt H1 n : ZMod p) / (Z : ZMod p)))
    (hz00 : intAt2 ZT 0 0 = 0)
    (hcol : ∀ i, 0 < i → i < H → (i : Int) * intAt2 ZT i 0 = intAt H1 i)
    (hrow : ∀ j, j < L → intAt2 ZT 0 j = intAt2 ZT j 0)
    (hdiag : ∀ i j, i + 1 < H → j + 1 < L →
      (i + 1 : Int) * (j + 1 : Int) *
        (intAt2 ZT i j - intAt2 ZT (i + 1) (j + 1)) = Z) :
    ∀ i j, i < H → j < L → ResRec.Gd p (zetaRat i j)
      ((intAt2 ZT i j : ZMod p) / (Z : ZMod p)) := by
  have col0 : ∀ i, i < H → ResRec.Gd p (zetaRat i 0)
      ((intAt2 ZT i 0 : ZMod p) / (Z : ZMod p)) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hz00]
      simpa [zetaRat_diagonal] using (ResRec.Gd.nat (p := p) 0)
    · have e : zetaRat i 0 = harmonicRat 1 i * (1 / (i : Rat)) := by
        rw [zetaRat_of_ne (by omega)]
        simp [harmonicRat_zero, div_eq_mul_inv]
      refine ResRec.Gd.of_eq e (ResRec.Gd.val ?_
        (ResRec.Gd.mul (hh1 i (by omega)) (ResRec.Gd.inv_nat hpos (by omega))))
      have hn : (i : ZMod p) ≠ 0 := ResRec.natCast_ne_zero_of_lt hpos (by omega)
      rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hn]
      have ec := congrArg (fun z : Int => (z : ZMod p)) (hcol i hpos hi)
      push_cast at ec
      have ed := congrArg (fun z : ZMod p => z / (Z : ZMod p)) ec
      convert ed using 1 <;> ring
  refine ResRec.diag_sound zetaRat
    (fun i j => 1 / (((i + 1 : Nat) : Rat) * ((j + 1 : Nat) : Rat)))
    (fun i j => (intAt2 ZT i j : ZMod p) / (Z : ZMod p))
    (fun i j => (((i + 1 : Nat) : ZMod p)⁻¹) * (((j + 1 : Nat) : ZMod p)⁻¹))
    H L zetaRat_step ?_ ?_ ?_ ?_
  · intro i j hi hj
    refine ResRec.Gd.of_eq (by rw [one_div_mul_one_div])
      (ResRec.Gd.mul
        (ResRec.Gd.inv_nat (p := p) (n := i + 1) (by omega) (by omega))
        (ResRec.Gd.inv_nat (p := p) (n := j + 1) (by omega) (by omega)))
  · intro i j hi hj
    have hn : ((i + 1 : Nat) : ZMod p) ≠ 0 :=
      ResRec.natCast_ne_zero_of_lt (by omega) (by omega)
    have hm : ((j + 1 : Nat) : ZMod p) ≠ 0 :=
      ResRec.natCast_ne_zero_of_lt (by omega) (by omega)
    apply (mul_right_inj' (mul_ne_zero hn hm)).mp
    have ec := congrArg (fun z : Int => (z : ZMod p)) (hdiag i j hi hj)
    push_cast at ec
    have ed := congrArg (fun z : ZMod p => z / (Z : ZMod p)) ec
    calc
      _ = ((((i + 1 : Nat) : ZMod p) * ((j + 1 : Nat) : ZMod p)) *
          ((intAt2 ZT i j : ZMod p) - (intAt2 ZT (i + 1) (j + 1) : ZMod p))) /
            (Z : ZMod p) := by push_cast; ring
      _ = (Z : ZMod p) / (Z : ZMod p) := by
        simpa only [Nat.cast_add, Nat.cast_one] using ed
      _ = 1 := div_self hZ
      _ = _ := by field_simp [hn, hm]
  · exact col0
  · intro j hj
    rw [zetaRat_symm, hrow j hj]
    exact col0 j (by omega)

end
end CatalanMeasure.GenD.Uniform.W.Charts6

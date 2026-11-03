module
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceNative
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
/-! Sparse source recurrence certificates and exact finite source key decoding.
Required non-boundary lookup misses are never converted to zero. -/
namespace CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD OAI.InternalCatalan
noncomputable section
variable {p : Nat} [Fact p.Prime]

/-- Signed source coordinates decoded from a finite natural key. -/
def sourceKey (A : Int → Int → Rat) (H n : Nat) : Rat :=
  A (n / H : Nat) ((n % H : Nat) - (1 : Int))

theorem source_key_shift_first {H n : Nat} (hH : 0 < H) (hn : H ≤ n)
    (hs : n % H ≠ 0) :
    (n - H - 1) / H = n / H - 1 ∧ (n - H - 1) % H = n % H - 1 := by
  have hk : 0 < n / H := Nat.div_pos hn hH
  have hsp : 0 < n % H := Nat.pos_of_ne_zero hs
  have hsl : n % H < H := Nat.mod_lt n hH
  let k := n / H - 1
  let s := n % H - 1
  have hkn : n / H = k + 1 := by dsimp [k]; omega
  have hsn : n % H = s + 1 := by dsimp [s]; omega
  have hrep : n = H * (k + 1) + (s + 1) := by
    simpa only [hkn, hsn] using (Nat.div_add_mod n H).symm
  have hex : n = H * k + H + s + 1 := by
    calc
      n = H * (k + 1) + (s + 1) := hrep
      _ = H * k + H + s + 1 := by ring
  have hsub : n - H - 1 = H * k + s := by omega
  have hlt : s < H := by omega
  constructor
  · rw [hsub, Nat.mul_add_div hH, Nat.div_eq_of_lt hlt, Nat.add_zero]
  · rw [hsub, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

theorem source_key_shift_two {H n : Nat} (hn : 2 * H ≤ n) :
    (n - 2 * H) / H = n / H - 2 ∧ (n - 2 * H) % H = n % H := by
  constructor
  · simpa only [Nat.mul_comm] using Nat.sub_mul_div n H 2
  · simpa only [Nat.mul_comm] using
      (Nat.sub_mul_mod (x := n) (n := H) (k := 2) (by omega))

/-- Integer-index source recurrence becomes exactly the finite sparse-key
recurrence; both semantic lower branches are proved, rather than defaulted. -/
theorem source_key_recurrence (A : Int → Int → Rat) (H : Nat) (hH : 0 < H)
    (hstep : ∀ k S, A (k + 2) S = 2 * A (k + 1) (S - 1) - A k S)
    (hminus : ∀ S, A (-1) S = 0)
    (hbelow : ∀ k S, S < -1 → A k S = 0) :
    ∀ n, H ≤ n → sourceKey A H n =
      2 * (if n % H = 0 then 0 else sourceKey A H (n - H - 1)) -
        (if n < 2 * H then 0 else sourceKey A H (n - 2 * H)) := by
  intro n hn
  have hk : 0 < n / H := Nat.div_pos hn hH
  have hst := hstep ((n / H : Nat) - (2 : Int)) ((n % H : Nat) - (1 : Int))
  have hki2 : ((n / H : Nat) - (2 : Int)) + 2 = (n / H : Nat) := by ring
  have hki1 : ((n / H : Nat) - (2 : Int)) + 1 = (n / H : Nat) - (1 : Int) := by ring
  rw [hki2, hki1] at hst
  have hl : A ((n / H : Nat) - (1 : Int)) (((n % H : Nat) - (1 : Int)) - 1) =
      (if n % H = 0 then 0 else sourceKey A H (n - H - 1)) := by
    by_cases hs : n % H = 0
    · rw [if_pos hs]
      apply hbelow
      rw [hs]
      norm_num
    · rw [if_neg hs]
      obtain ⟨hq, hr⟩ := source_key_shift_first hH hn hs
      unfold sourceKey
      rw [hq, hr]
      have hkc : ((n / H - 1 : Nat) : Int) = (n / H : Nat) - (1 : Int) := by omega
      have hsc : ((n % H - 1 : Nat) : Int) = (n % H : Nat) - (1 : Int) := by omega
      rw [hkc, hsc]
  have hr : A ((n / H : Nat) - (2 : Int)) ((n % H : Nat) - (1 : Int)) =
      (if n < 2 * H then 0 else sourceKey A H (n - 2 * H)) := by
    by_cases hn2 : n < 2 * H
    · rw [if_pos hn2]
      have hklt : n / H < 2 := by
        apply Nat.lt_of_not_ge
        intro h
        have hh := (Nat.le_div_iff_mul_le hH).mp h
        omega
      have hk1 : n / H = 1 := by omega
      rw [hk1]
      norm_num only [Nat.cast_one, show (1 : Int) - 2 = -1 by norm_num]
      exact hminus _
    · rw [if_neg hn2]
      obtain ⟨hq, hmod⟩ := source_key_shift_two (H := H) (n := n) (by omega)
      unfold sourceKey
      rw [hq, hmod]
      have hk2 : 2 ≤ n / H := (Nat.le_div_iff_mul_le hH).mpr (by omega)
      have hkc : ((n / H - 2 : Nat) : Int) = (n / H : Nat) - (2 : Int) := by omega
      rw [hkc]
  unfold sourceKey
  rw [hst, hl, hr]
  rfl


/-- Sparse finite source values. A failed lookup is never interpreted as zero. -/
inductive IntSourceTree where
  | empty
  | node (key : Nat) (value : Int) (left right : IntSourceTree)

def IntSourceTree.get? : IntSourceTree → Nat → Option Int
  | .empty, _ => none
  | .node k v left right, n =>
    if n = k then some v else if n < k then left.get? n else right.get? n

def IntSourceTree.all (tree : IntSourceTree) (P : Nat → Int → Bool) : Bool :=
  match tree with
  | .empty => true
  | .node k v left right => P k v && left.all P && right.all P

/-- No sorting hypothesis is needed: successful lookup always visits a node
covered by the all-node checker. -/
theorem IntSourceTree.all_get? (tree : IntSourceTree) :
    ∀ (P : Nat → Int → Bool), tree.all P = true →
      ∀ n v, tree.get? n = some v → P n v = true := by
  induction tree with
  | empty =>
    intro P hc n v hg
    simp [IntSourceTree.get?] at hg
  | node k w left right ihL ihR =>
    intro P hc n v hg
    simp only [IntSourceTree.all, Bool.and_eq_true] at hc
    simp only [IntSourceTree.get?] at hg
    split_ifs at hg with he hl
    · subst n
      have hv : w = v := Option.some.inj hg
      subst v
      exact hc.1.1
    · exact ihL P hc.1.2 n v hg
    · exact ihR P hc.2 n v hg

/-- Exact recurrence RHS, with both semantic lower-boundary zeros explicit. -/
def IntSourceTree.rhs? (tree : IntSourceTree) (H : Nat) (base : Nat → Int)
    (n : Nat) : Option Int :=
  if n < H then some (base n) else
    (if n % H = 0 then some (0 : Int) else tree.get? (n - H - 1)).bind
      (fun x => (if n < 2 * H then some (0 : Int) else tree.get? (n - 2 * H)).map
        (fun y => 2 * x - y))

def IntSourceTree.check (tree : IntSourceTree) (H : Nat) (base : Nat → Int) : Bool :=
  decide (0 < H) && tree.all (fun n v => decide (tree.rhs? H base n = some v))

/-- Every successfully requested source value has its actual rational residue
at an arbitrary prime. Base/recurrence facts are mathematical hypotheses of
the generic family theorem, never fields of the finite certificate. -/
theorem IntSourceTree.check_sound (tree : IntSourceTree) (H : Nat) (hH : 0 < H)
    (scale : Int) (base : Nat → Int) (F : Nat → Rat)
    (hz : (scale : ZMod p) ≠ 0)
    (hbase : ∀ n, n < H → ResRec.Gd p (F n)
      ((base n : ZMod p) / (scale : ZMod p)))
    (hrec : ∀ n, H ≤ n → F n =
      2 * (if n % H = 0 then 0 else F (n - H - 1)) -
        (if n < 2 * H then 0 else F (n - 2 * H)))
    (hc : tree.check H base = true) :
    ∀ n v, tree.get? n = some v → ResRec.Gd p (F n)
      ((v : ZMod p) / (scale : ZMod p)) := by
  have hc' := hc
  simp only [IntSourceTree.check, Bool.and_eq_true] at hc'
  have hall : tree.all (fun n v => decide (tree.rhs? H base n = some v)) = true := hc'.2
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v hg
    have he : tree.rhs? H base n = some v :=
      of_decide_eq_true (tree.all_get? _ hall n v hg)
    by_cases hn : n < H
    · have hv : base n = v := by simpa [IntSourceTree.rhs?, hn] using he
      simpa only [hv] using hbase n hn
    · let lv : Option Int := if n % H = 0 then some 0 else tree.get? (n - H - 1)
      let rv : Option Int := if n < 2 * H then some 0 else tree.get? (n - 2 * H)
      have hs : lv.bind (fun x => rv.map (fun y => 2 * x - y)) = some v := by
        simpa only [IntSourceTree.rhs?, if_neg hn] using he
      cases hl : lv with
      | none => simp [hl] at hs
      | some x =>
        cases hr : rv with
        | none => simp [hl, hr] at hs
        | some y =>
          have hv : 2 * x - y = v := by simpa [hl, hr] using hs
          have gx : ResRec.Gd p (if n % H = 0 then 0 else F (n - H - 1))
              ((x : ZMod p) / (scale : ZMod p)) := by
            by_cases hleft : n % H = 0
            · have hx : (0 : Int) = x := by simpa [lv, hleft] using hl
              rw [← hx]
              simpa [hleft] using (ResRec.Gd.nat (p := p) 0)
            · have hget : tree.get? (n - H - 1) = some x := by simpa [lv, hleft] using hl
              simpa only [hleft, if_false] using ih (n - H - 1) (by omega) x hget
          have gy : ResRec.Gd p (if n < 2 * H then 0 else F (n - 2 * H))
              ((y : ZMod p) / (scale : ZMod p)) := by
            by_cases hright : n < 2 * H
            · have hy : (0 : Int) = y := by simpa [rv, hright] using hr
              rw [← hy]
              simpa [hright] using (ResRec.Gd.nat (p := p) 0)
            · have hget : tree.get? (n - 2 * H) = some y := by simpa [rv, hright] using hr
              simpa only [hright, if_false] using ih (n - 2 * H) (by omega) y hget
          have gs := ResRec.Gd.sub (ResRec.Gd.mul (ResRec.Gd.nat (p := p) 2) gx) gy
          refine ResRec.Gd.of_eq (hrec n (by omega)) (ResRec.Gd.val ?_ gs)
          have hvp := congrArg (fun z : Int => (z : ZMod p)) hv
          push_cast at hvp
          rw [← hvp]
          ring

end
end CatalanMeasure.GenD.Uniform.W.Charts6

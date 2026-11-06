module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.ResponseBranches
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.HostRows
public import Mathlib.Tactic.IntervalCases
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketLabels004
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Prof
open CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff holds)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004 (packet slots slots_eq blockCount k0 ah aq low target)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain004 (jetLayout)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine000.P004 (win cert)
noncomputable section
variable {N p : Nat} [Fact p.Prime]

private theorem one_not_dvd (hp : 44 < p) : ¬ (p : Int) ∣ 1 := by
  intro h
  have hd : p ∣ 1 := by exact_mod_cast h
  have hl := Nat.le_of_dvd (by decide : 0 < (1 : Nat)) hd
  omega

private theorem case000
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 1 (12) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 1 (12))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 1 (12) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 1) (S := 12) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 1) (S := 12) hodd ⟨2, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c000_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c000_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c000_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c000_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 1 12
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c000_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base000) hp hz hp2 (by decide)
    (le_trans (by decide : (12 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check000
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c000_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case001
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 1 (11) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 1 (11))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 1 (11) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 1) (S := 11) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 1) (S := 11) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c011_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c011_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c011_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c011_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 1 11
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c011_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base011) hp hz hp2 (by decide)
    (le_trans (by decide : (11 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check011
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c011_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case002
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 2 (12) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 2 (12))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 2 (12) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 2) (S := 12) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 2) (S := 12) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c001_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c001_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c001_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c001_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 2 12
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c001_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base001) hp hz hp2 (by decide)
    (le_trans (by decide : (12 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check001
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c001_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case003
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 2 (11) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 2 (11))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 2 (11) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 2) (S := 11) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 2) (S := 11) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c012_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c012_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c012_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c012_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 2 11
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c012_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base012) hp hz hp2 (by decide)
    (le_trans (by decide : (11 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check012
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c012_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case004
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 3 (12) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 3 (12))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 3 (12) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 3) (S := 12) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 3) (S := 12) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c002_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c002_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c002_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c002_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 3 12
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c002_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base002) hp hz hp2 (by decide)
    (le_trans (by decide : (12 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check002
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c002_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case005
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 3 (11) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 3 (11))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 3 (11) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 3) (S := 11) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 3) (S := 11) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c013_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c013_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c013_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c013_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 3 11
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c013_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base013) hp hz hp2 (by decide)
    (le_trans (by decide : (11 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check013
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c013_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case006
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 4 (12) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 4 (12))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 4 (12) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 4) (S := 12) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 4) (S := 12) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c003_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c003_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c003_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c003_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 4 12
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c003_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base003) hp hz hp2 (by decide)
    (le_trans (by decide : (12 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check003
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c003_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case007
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 4 (11) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 4 (11))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 4 (11) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 4) (S := 11) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 4) (S := 11) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c014_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c014_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c014_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c014_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 4 11
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c014_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base014) hp hz hp2 (by decide)
    (le_trans (by decide : (11 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check014
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c014_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case008
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 5 (12) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 5 (12))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 5 (12) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 5) (S := 12) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 5) (S := 12) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c004_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c004_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c004_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c004_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 5 12
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c004_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base004) hp hz hp2 (by decide)
    (le_trans (by decide : (12 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check004
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c004_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case009
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 5 (11) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 5 (11))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 5 (11) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 5) (S := 11) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 5) (S := 11) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c015_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c015_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c015_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c015_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 5 11
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c015_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base015) hp hz hp2 (by decide)
    (le_trans (by decide : (11 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check015
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c015_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case010
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 6 (12) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 6 (12))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 6 (12) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 6) (S := 12) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 6) (S := 12) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c005_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c005_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c005_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c005_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 6 12
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c005_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base005) hp hz hp2 (by decide)
    (le_trans (by decide : (12 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check005
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c005_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case011
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 6 (11) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 6 (11))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 6 (11) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 6) (S := 11) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 6) (S := 11) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c016_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c016_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c016_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c016_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 6 11
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c016_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base016) hp hz hp2 (by decide)
    (le_trans (by decide : (11 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check016
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c016_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case012
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 7 (12) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 7 (12))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 7 (12) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 7) (S := 12) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 7) (S := 12) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c006_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c006_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c006_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c006_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 7 12
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c006_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base006) hp hz hp2 (by decide)
    (le_trans (by decide : (12 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check006
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c006_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case013
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 7 (11) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 7 (11))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 7 (11) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 7) (S := 11) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 7) (S := 11) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c017_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c017_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c017_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c017_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 7 11
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c017_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base017) hp hz hp2 (by decide)
    (le_trans (by decide : (11 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check017
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c017_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case014
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 8 (12) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 8 (12))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 8 (12) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 8) (S := 12) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 8) (S := 12) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c007_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c007_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c007_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c007_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 8 12
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c007_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base007) hp hz hp2 (by decide)
    (le_trans (by decide : (12 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check007
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c007_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case015
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 8 (11) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 8 (11))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 8 (11) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 8) (S := 11) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 8) (S := 11) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c018_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c018_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c018_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c018_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 8 11
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c018_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base018) hp hz hp2 (by decide)
    (le_trans (by decide : (11 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check018
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c018_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case016
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 9 (12) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 9 (12))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 9 (12) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 9) (S := 12) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 9) (S := 12) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c008_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c008_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c008_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c008_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 9 12
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c008_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base008) hp hz hp2 (by decide)
    (le_trans (by decide : (12 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check008
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c008_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case017
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 9 (11) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 9 (11))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 9 (11) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 9) (S := 11) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 9) (S := 11) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c019_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c019_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c019_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c019_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 9 11
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c019_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base019) hp hz hp2 (by decide)
    (le_trans (by decide : (11 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check019
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c019_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case018
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 10 (12) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 10 (12))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 10 (12) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 10) (S := 12) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 10) (S := 12) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c009_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c009_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c009_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c009_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 10 12
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c009_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base009) hp hz hp2 (by decide)
    (le_trans (by decide : (12 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check009
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c009_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case019
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 10 (11) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 10 (11))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 10 (11) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 10) (S := 11) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 10) (S := 11) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c020_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c020_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c020_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c020_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 10 11
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c020_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base020) hp hz hp2 (by decide)
    (le_trans (by decide : (11 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check020
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c020_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case020
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 11 (12) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 11 (12))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 11 (12) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 11) (S := 12) hodd ⟨2, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 11) (S := 12) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c010_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c010_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c010_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c010_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 11 12
    low (some ⟨32, by decide⟩) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c010_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.base010) hp hz hp2 (by decide)
    (le_trans (by decide : (12 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource004.check010
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c010_0Check hs e hl0 hu0 x hx
  have hs1 : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c010_1.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c010_1.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hu1 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c010_1.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h1 := unit_component_kill CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c010_1 ⟨32, by decide⟩
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover004.c010_1Check hs1 e hl hu1 x hx
  refine foldedResponse_no_slack (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 11 12 low _ _ h0 ?_
  intro s hs
  injection hs with hs'
  subst s; exact h1

private theorem case021
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 11 (11) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 11 (11))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 11 (11) low none
      (emb packet p packet.n (x e)) = 0 := by
  exact (response_empty72 (cs := cert) hodd hwin ⟨2, by decide⟩ ⟨0, by decide⟩
    (by decide +kernel) hlo hhi).elim

-- kcost: 0.250 s conservative model; finite empty and component scale guards only.
theorem labelKill
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (J : Nat) (hj0 : 1 ≤ J) (hj1 : J ≤ 11)
    (S : Int) (hS : S = 12 ∨ S = 11)
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq J (S) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p J (S))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) J (S) low none
      (emb packet p packet.n (x e)) = 0 := by
  rcases hS with rfl | rfl
  · interval_cases J
    · exact case000 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case002 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case004 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case006 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case008 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case010 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case012 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case014 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case016 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case018 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case020 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
  · interval_cases J
    · exact case001 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case003 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case005 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case007 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case009 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case011 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case013 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case015 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case017 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case019 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case021 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketLabels004

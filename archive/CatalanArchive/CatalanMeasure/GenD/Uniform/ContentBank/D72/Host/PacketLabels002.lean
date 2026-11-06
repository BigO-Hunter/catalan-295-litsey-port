module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.ResponseBranches
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.HostRows
public import Mathlib.Tactic.IntervalCases
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketLabels002
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Prof
open CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff holds)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002 (packet slots slots_eq blockCount k0 ah aq low target)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain002 (jetLayout)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine000.P002 (win cert)
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
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 2 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 2 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 2 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 2) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 2) (S := 18) hodd ⟨2, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c000_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c000_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c000_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c000_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 2 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c000_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base000) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check000
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c000_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case001
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 2 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 2 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 2 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 2) (S := 17) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 2) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c015_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c015_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c015_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c015_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 2 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c015_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base015) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check015
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c015_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case002
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 3 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 3 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 3 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 3) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 3) (S := 18) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c001_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c001_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c001_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c001_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 3 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c001_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base001) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check001
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c001_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case003
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 3 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 3 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 3 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 3) (S := 17) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 3) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c016_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c016_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c016_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c016_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 3 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c016_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base016) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check016
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c016_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case004
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 4 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 4 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 4 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 4) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 4) (S := 18) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c002_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c002_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c002_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c002_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 4 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c002_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base002) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check002
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c002_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case005
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 4 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 4 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 4 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 4) (S := 17) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 4) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c017_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c017_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c017_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c017_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 4 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c017_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base017) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check017
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c017_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case006
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 5 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 5 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 5 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 5) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 5) (S := 18) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c003_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c003_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c003_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c003_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 5 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c003_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base003) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check003
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c003_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case007
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 5 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 5 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 5 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 5) (S := 17) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 5) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c018_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c018_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c018_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c018_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 5 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c018_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base018) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check018
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c018_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case008
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 6 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 6 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 6 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 6) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 6) (S := 18) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c004_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c004_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c004_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c004_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 6 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c004_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base004) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check004
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c004_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case009
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 6 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 6 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 6 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 6) (S := 17) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 6) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c019_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c019_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c019_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c019_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 6 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c019_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base019) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check019
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c019_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case010
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 7 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 7 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 7 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 7) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 7) (S := 18) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c005_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c005_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c005_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c005_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 7 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c005_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base005) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check005
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c005_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case011
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 7 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 7 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 7 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 7) (S := 17) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 7) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c020_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c020_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c020_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c020_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 7 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c020_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base020) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check020
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c020_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case012
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 8 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 8 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 8 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 8) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 8) (S := 18) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c006_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c006_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c006_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c006_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 8 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c006_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base006) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check006
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c006_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case013
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 8 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 8 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 8 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 8) (S := 17) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 8) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c021_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c021_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c021_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c021_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 8 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c021_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base021) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check021
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c021_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case014
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 9 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 9 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 9 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 9) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 9) (S := 18) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c007_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c007_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c007_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c007_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 9 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c007_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base007) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check007
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c007_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case015
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 9 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 9 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 9 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 9) (S := 17) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 9) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c022_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c022_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c022_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c022_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 9 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c022_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base022) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check022
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c022_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case016
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 10 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 10 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 10 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 10) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 10) (S := 18) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c008_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c008_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c008_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c008_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 10 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c008_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base008) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check008
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c008_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case017
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 10 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 10 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 10 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 10) (S := 17) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 10) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c023_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c023_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c023_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c023_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 10 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c023_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base023) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check023
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c023_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case018
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 11 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 11 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 11 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 11) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 11) (S := 18) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c009_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c009_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c009_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c009_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 11 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c009_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base009) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check009
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c009_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case019
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 11 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 11 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 11 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 11) (S := 17) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 11) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c024_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c024_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c024_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c024_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 11 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c024_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base024) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check024
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c024_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case020
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 12 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 12 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 12 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 12) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 12) (S := 18) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c010_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c010_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c010_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c010_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 12 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c010_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base010) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check010
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c010_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case021
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 12 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 12 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 12 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 12) (S := 17) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 12) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c025_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c025_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c025_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c025_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 12 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c025_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base025) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check025
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c025_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case022
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 13 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 13 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 13 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 13) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 13) (S := 18) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c011_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c011_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c011_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c011_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 13 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c011_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base011) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check011
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c011_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case023
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 13 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 13 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 13 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 13) (S := 17) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 13) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c026_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c026_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c026_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c026_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 13 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c026_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base026) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check026
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c026_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case024
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 14 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 14 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 14 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 14) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 14) (S := 18) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c012_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c012_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c012_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c012_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 14 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c012_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base012) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check012
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c012_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case025
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 14 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 14 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 14 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 14) (S := 17) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 14) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c027_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c027_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c027_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c027_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 14 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c027_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base027) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check027
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c027_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case026
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 15 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 15 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 15 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 15) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 15) (S := 18) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c013_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c013_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c013_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c013_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 15 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c013_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base013) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check013
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c013_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case027
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 15 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 15 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 15 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 15) (S := 17) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 15) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c028_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c028_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c028_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c028_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 15 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c028_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base028) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check028
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c028_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case028
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 16 (18) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 16 (18))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 16 (18) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 16) (S := 18) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 16) (S := 18) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c014_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c014_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c014_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c014_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 16 18
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c014_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base014) hp hz hp2 (by decide)
    (le_trans (by decide : (18 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check014
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c014_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case029
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 16 (17) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 16 (17))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 16 (17) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 16) (S := 17) hodd ⟨2, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 16) (S := 17) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c029_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c029_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c029_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c029_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 16 17
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c029_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.base029) hp hz hp2 (by decide)
    (le_trans (by decide : (17 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource002.check029
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover002.c029_0Check hs e hl0 hu0 x hx
  exact h0

-- kcost: 0.250 s conservative model; finite empty and component scale guards only.
theorem labelKill
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (J : Nat) (hj0 : 2 ≤ J) (hj1 : J ≤ 16)
    (S : Int) (hS : S = 18 ∨ S = 17)
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
    · exact case022 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case024 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case026 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case028 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
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
    · exact case023 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case025 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case027 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case029 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketLabels002

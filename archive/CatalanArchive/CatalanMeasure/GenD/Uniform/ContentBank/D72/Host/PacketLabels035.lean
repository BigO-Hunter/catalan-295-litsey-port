module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.ResponseBranches
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.HostRows
public import Mathlib.Tactic.IntervalCases
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketLabels035
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Prof
open CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff holds)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035 (packet slots slots_eq blockCount k0 ah aq low target)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain035 (jetLayout)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine004.P035 (win cert)
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
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 3 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 3 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 3 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 3) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 3) (S := 33) hodd ⟨2, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c000_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c000_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c000_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c000_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 3 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c000_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base000) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check000
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c000_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case001
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 3 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 3 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 3 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 3) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 3) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c027_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c027_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c027_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c027_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 3 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c027_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base027) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check027
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c027_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case002
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 4 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 4 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 4 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 4) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 4) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c001_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c001_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c001_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c001_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 4 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c001_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base001) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check001
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c001_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case003
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 4 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 4 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 4 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 4) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 4) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c028_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c028_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c028_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c028_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 4 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c028_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base028) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check028
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c028_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case004
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 5 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 5 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 5 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 5) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 5) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c002_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c002_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c002_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c002_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 5 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c002_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base002) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check002
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c002_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case005
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 5 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 5 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 5 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 5) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 5) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c029_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c029_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c029_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c029_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 5 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c029_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base029) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check029
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c029_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case006
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 6 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 6 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 6 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 6) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 6) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c003_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c003_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c003_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c003_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 6 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c003_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base003) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check003
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c003_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case007
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 6 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 6 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 6 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 6) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 6) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c030_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c030_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c030_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c030_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 6 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c030_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base030) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check030
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c030_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case008
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 7 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 7 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 7 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 7) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 7) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c004_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c004_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c004_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c004_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 7 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c004_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base004) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check004
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c004_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case009
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 7 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 7 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 7 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 7) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 7) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c031_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c031_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c031_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c031_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 7 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c031_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base031) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check031
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c031_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case010
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 8 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 8 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 8 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 8) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 8) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c005_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c005_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c005_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c005_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 8 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c005_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base005) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check005
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c005_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case011
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 8 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 8 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 8 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 8) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 8) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c032_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c032_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c032_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c032_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 8 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c032_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base032) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check032
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c032_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case012
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 9 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 9 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 9 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 9) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 9) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c006_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c006_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c006_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c006_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 9 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c006_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base006) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check006
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c006_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case013
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 9 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 9 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 9 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 9) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 9) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c033_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c033_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c033_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c033_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 9 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c033_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base033) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check033
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c033_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case014
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 10 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 10 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 10 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 10) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 10) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c007_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c007_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c007_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c007_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 10 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c007_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base007) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check007
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c007_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case015
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 10 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 10 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 10 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 10) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 10) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c034_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c034_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c034_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c034_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 10 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c034_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base034) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check034
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c034_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case016
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 11 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 11 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 11 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 11) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 11) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c008_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c008_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c008_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c008_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 11 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c008_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base008) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check008
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c008_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case017
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 11 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 11 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 11 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 11) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 11) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c035_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c035_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c035_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c035_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 11 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c035_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base035) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check035
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c035_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case018
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 12 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 12 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 12 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 12) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 12) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c009_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c009_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c009_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c009_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 12 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c009_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base009) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check009
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c009_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case019
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 12 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 12 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 12 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 12) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 12) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c036_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c036_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c036_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c036_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 12 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c036_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base036) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check036
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c036_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case020
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 13 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 13 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 13 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 13) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 13) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c010_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c010_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c010_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c010_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 13 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c010_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base010) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check010
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c010_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case021
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 13 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 13 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 13 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 13) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 13) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c037_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c037_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c037_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c037_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 13 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c037_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base037) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check037
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c037_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case022
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 14 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 14 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 14 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 14) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 14) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c011_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c011_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c011_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c011_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 14 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c011_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base011) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check011
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c011_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case023
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 14 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 14 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 14 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 14) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 14) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c038_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c038_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c038_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c038_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 14 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c038_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base038) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check038
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c038_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case024
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 15 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 15 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 15 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 15) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 15) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c012_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c012_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c012_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c012_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 15 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c012_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base012) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check012
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c012_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case025
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 15 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 15 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 15 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 15) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 15) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c039_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c039_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c039_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c039_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 15 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c039_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base039) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check039
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c039_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case026
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 16 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 16 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 16 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 16) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 16) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c013_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c013_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c013_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c013_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 16 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c013_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base013) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check013
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c013_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case027
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 16 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 16 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 16 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 16) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 16) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c040_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c040_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c040_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c040_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 16 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c040_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base040) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check040
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c040_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case028
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 17 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 17 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 17 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 17) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 17) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c014_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c014_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c014_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c014_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 17 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c014_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base014) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check014
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c014_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case029
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 17 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 17 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 17 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 17) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 17) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c041_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c041_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c041_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c041_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 17 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c041_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base041) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check041
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c041_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case030
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 18 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 18 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 18 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 18) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 18) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c015_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c015_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c015_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c015_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 18 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c015_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base015) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check015
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c015_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case031
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 18 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 18 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 18 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 18) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 18) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c042_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c042_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c042_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c042_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 18 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c042_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base042) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check042
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c042_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case032
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 19 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 19 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 19 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 19) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 19) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c016_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c016_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c016_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c016_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 19 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c016_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base016) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check016
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c016_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case033
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 19 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 19 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 19 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 19) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 19) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c043_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c043_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c043_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c043_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 19 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c043_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base043) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check043
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c043_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case034
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 20 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 20 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 20 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 20) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 20) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c017_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c017_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c017_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c017_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 20 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c017_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base017) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check017
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c017_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case035
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 20 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 20 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 20 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 20) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 20) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c044_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c044_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c044_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c044_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 20 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c044_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base044) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check044
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c044_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case036
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 21 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 21 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 21 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 21) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 21) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c018_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c018_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c018_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c018_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 21 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c018_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base018) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check018
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c018_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case037
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 21 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 21 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 21 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 21) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 21) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c045_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c045_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c045_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c045_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 21 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c045_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base045) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check045
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c045_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case038
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 22 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 22 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 22 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 22) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 22) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c019_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c019_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c019_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c019_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 22 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c019_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base019) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check019
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c019_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case039
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 22 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 22 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 22 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 22) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 22) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c046_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c046_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c046_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c046_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 22 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c046_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base046) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check046
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c046_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case040
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 23 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 23 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 23 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 23) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 23) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c020_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c020_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c020_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c020_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 23 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c020_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base020) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check020
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c020_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case041
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 23 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 23 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 23 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 23) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 23) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c047_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c047_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c047_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c047_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 23 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c047_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base047) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check047
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c047_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case042
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 24 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 24 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 24 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 24) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 24) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c021_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c021_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c021_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c021_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 24 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c021_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base021) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check021
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c021_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case043
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 24 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 24 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 24 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 24) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 24) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c048_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c048_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c048_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c048_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 24 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c048_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base048) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check048
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c048_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case044
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 25 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 25 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 25 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 25) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 25) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c022_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c022_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c022_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c022_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 25 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c022_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base022) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check022
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c022_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case045
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 25 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 25 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 25 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 25) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 25) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c049_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c049_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c049_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c049_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 25 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c049_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base049) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check049
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c049_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case046
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 26 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 26 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 26 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 26) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 26) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c023_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c023_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c023_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c023_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 26 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c023_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base023) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check023
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c023_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case047
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 26 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 26 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 26 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 26) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 26) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c050_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c050_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c050_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c050_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 26 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c050_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base050) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check050
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c050_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case048
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 27 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 27 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 27 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 27) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 27) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c024_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c024_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c024_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c024_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 27 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c024_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base024) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check024
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c024_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case049
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 27 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 27 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 27 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 27) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 27) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c051_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c051_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c051_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c051_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 27 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c051_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base051) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check051
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c051_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case050
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 28 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 28 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 28 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 28) (S := 33) hodd ⟨0, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 28) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c025_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c025_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c025_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c025_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 28 33
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c025_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base025) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check025
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c025_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case051
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 28 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 28 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 28 (32) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 28) (S := 32) hodd ⟨1, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 28) (S := 32) hodd ⟨0, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c052_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c052_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c052_0.lo ≤ (e.val : Int) := by
    exact hl
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c052_0.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 28 32
    low none CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c052_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base052) hp hz hp2 (by decide)
    (le_trans (by decide : (32 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check052
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c052_0Check hs e hl0 hu0 x hx
  exact h0

private theorem case052
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 29 (33) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 29 (33))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 29 (33) low none
      (emb packet p packet.n (x e)) = 0 := by
  have hl := (response_lower_branch72 (N := N) (a := aq) (J := 29) (S := 33) hodd ⟨2, by decide⟩).trans hlo
  have hu := hhi.trans_le (response_upper_branch72 (N := N) (J := 29) (S := 33) hodd ⟨1, by decide⟩)
  have hs : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c026_0.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c026_0.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hl0 : affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c026_0.lo ≤ (e.val : Int) := by
    change affAt N p (⟨0,0,0⟩ : Aff) ≤ (e.val : Int)
    simp [affAt, Aff.eval]
  have hu0 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c026_0.hi := by
    exact hu
  have h0 := native_response_component_kill (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 29 33
    low (some ⟨111, by decide⟩) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c026_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.base026) hp hz hp2 (by decide)
    (le_trans (by decide : (33 : Int).toNat + 3 ≤ 41) hH) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource035.check026
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c026_0Check hs e hl0 hu0 x hx
  have hs1 : ∀ z ∈ CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c026_1.zones, ¬ (p : Int) ∣ z.span.scale := by
    intro z hm
    have h1 : CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c026_1.zones.all (fun z => decide (z.span.scale = 1)) = true := by decide +kernel
    rw [of_decide_eq_true ((List.all_eq_true.mp h1) z hm)]; exact one_not_dvd hp
  have hu1 : (e.val : Int) < affAt N p CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c026_1.hi := by
    change (e.val : Int) < affAt N p pAff72
    rw [pAff72_eval hodd]; exact_mod_cast e.isLt
  have h1 := unit_component_kill CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c026_1 ⟨111, by decide⟩
    hwin hodd hoff hw CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover035.c026_1Check hs1 e hl hu1 x hx
  refine foldedResponse_no_slack (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 29 33 low _ _ h0 ?_
  intro s hs
  injection hs with hs'
  subst s; exact h1

private theorem case053
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (hodd : p % 2 = 1) (hp : 44 < p) (hp2 : p ≠ 2)
    (hz : (momentData.scale : ZMod p) ≠ 0) (hH : 41 ≤ P72.H N)
    (hoff : ∀ g, 0 ≤ affAt N p (jetLayout.offset g))
    (hw : ∀ g, 0 ≤ affAt N p (jetLayout.width g))
    (e : Fin p) (hlo : responseLo (P72.H N) (P72.L N) p aq 29 (32) ≤ (e.val : Int))
    (hhi : (e.val : Int) < responseHi (P72.H N) (P72.b N) p p 29 (32))
    (x : Fin p → Fin packet.d → ZMod p)
    (hx : ∀ g (j : Fin (jetLayout.count N p g)),
      chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) :
    foldedResponseLinear (b := blockCount) (ex := 0) slots_eq k0 ah aq slots (P72.H N) 29 (32) low none
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
    (J : Nat) (hj0 : 3 ≤ J) (hj1 : J ≤ 29)
    (S : Int) (hS : S = 33 ∨ S = 32)
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
    · exact case030 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case032 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case034 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case036 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case038 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case040 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case042 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case044 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case046 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case048 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case050 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case052 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
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
    · exact case031 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case033 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case035 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case037 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case039 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case041 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case043 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case045 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case047 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case049 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case051 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx
    · exact case053 hwin hodd hp hp2 hz hH hoff hw e hlo hhi x hx

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketLabels035

module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.HostDomainFrame
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.HostDomainCert
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover030
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.DomainSound030
open Polynomial CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Charts3
open CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff exists_rows_low_gen exists_rows_high_gen)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource030 (packet slots slotCount blockCount)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain030
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover030 (gate)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine003.P030 (win cert)
noncomputable section

theorem packet_hdom {N p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 1 ≤ P72.n N) (hodd : p % 2 = 1)
    (facts : PhysicalGateFacts72 gate N p)
    (hK : slotCount = bN P72 N p * 4 + 2 + 0)
    (x : Fin p → Fin packet.d → ZMod p)
    (ctx : NativeDomainCtx (N := N) jetLayout win cert slots x) :
    (fun e => sparseSourceIns slots (emb packet p packet.n (x e))) ∈ (monoData hp2 hn hK).dom := by
  let y := fun e => sparseSourceIns slots (emb packet p packet.n (x e))
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hhalf : halfPrime p = (((p-1)/2 : Nat) : Int) := by
    unfold halfPrime
    omega
  have hb : bN P72 N p = 30 := by
    simpa [gate] using PhysicalGateFacts72.block_count facts
  have hbpos : 0 < bN P72 N p := by omega
  have hr := PhysicalGateFacts72.hrem facts
  change P72.h N % p = 4 * N - 1 * p at hr
  have hwin := ctx.win_ok
  simp [win, affAt, Aff.eval, hhalf] at hwin
  have hja := (gja_spec (g := P72.g N) hp).1
  rw [facts.left] at hja
  change (gja (P72.g N) p : Int) = -(↑(6 * N : Nat)) - (-3 : Int) * p at hja
  have hrt := (grho_spec (n := P72.n N) (g := P72.g N) hp).1
  rw [facts.right] at hrt
  change (grho (P72.n N) (P72.g N) p : Int) =
    ↑(72 * N : Nat) - 1 - ↑(6 * N : Nat) - (26 : Int) * p at hrt
  have hrpos : 0 < P72.h N % p := by omega
  have hphase : ¬ (P72.h N % p + (p-1)/2 < p) := by omega
  have hX (e : Fin p) (j : Fin 0) : y e ((ckEquiv hK).symm (Sum.inr (Sum.inr j))) = 0 :=
    Fin.elim0 j
  have hI (k : Fin (bN P72 N p)) (u : Fin 4) (j : Fin slotCount)
      (hj : j.val = 4 * k.val + u.val) :
      (ckEquiv hK).symm (Sum.inl (k,u)) = j := Fin.ext ((ck_block_val hK k u).trans hj.symm)
  have hZ (z : Fin 2) (j : Fin slotCount) (hj : j.val = bN P72 N p * 4 + z.val) :
      (ckEquiv hK).symm (Sum.inr (Sum.inl z)) = j := Fin.ext ((ck_center_val hK z).trans hj.symm)
  have absent0 : polx y (⟨0, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨0, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent4 : polx y (⟨4, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨4, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent8 : polx y (⟨8, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨8, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent12 : polx y (⟨12, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨12, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent16 : polx y (⟨16, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨16, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent20 : polx y (⟨20, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨20, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent24 : polx y (⟨24, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨24, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent28 : polx y (⟨28, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨28, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent32 : polx y (⟨32, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨32, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent36 : polx y (⟨36, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨36, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent40 : polx y (⟨40, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨40, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent44 : polx y (⟨44, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨44, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent48 : polx y (⟨48, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨48, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent52 : polx y (⟨52, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨52, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent56 : polx y (⟨56, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨56, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent60 : polx y (⟨60, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨60, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent64 : polx y (⟨64, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨64, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent68 : polx y (⟨68, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨68, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent72 : polx y (⟨72, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨72, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent76 : polx y (⟨76, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨76, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent80 : polx y (⟨80, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨80, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent84 : polx y (⟨84, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨84, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent88 : polx y (⟨88, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨88, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent92 : polx y (⟨92, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨92, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent96 : polx y (⟨96, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨96, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent100 : polx y (⟨100, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨100, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent104 : polx y (⟨104, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨104, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent108 : polx y (⟨108, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨108, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent112 : polx y (⟨112, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨112, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent116 : polx y (⟨116, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨116, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))
  have absent120 : polx y (⟨120, by decide⟩ : Fin slotCount) = 0 := by
    exact sparse_polx_absent slots (⟨120, by decide⟩ : Fin slotCount) (by decide +kernel) (fun e => emb packet p packet.n (x e))

  let Bfull : Nat := P72.h N % p + (p - gja (P72.g N) p)
  let Tfull : Nat := P72.h N % p + grho (P72.n N) (P72.g N) p
  let Bdeg : Nat := Bfull - p
  let Tdeg : Nat := Tfull - p
  have row000 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨1, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req000Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req000Zones, z.span.scale = 1 := by simp [req000Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req000Terms = polx y (⟨1, by decide⟩ : Fin slotCount) := by
      simp [req000Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req000Terms ⟨4, -3, -2⟩ req000Zones check000 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row001 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨1, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req001Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req001Zones, z.span.scale = 1 := by simp [req001Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req001Terms = polx y (⟨1, by decide⟩ : Fin slotCount) := by
      simp [req001Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req001Terms ⟨-4, 4, 2⟩ req001Zones check001 hs (P72.h N % p) horder
  have row002 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨2, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req002Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req002Zones, z.span.scale = 1 := by simp [req002Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req002Terms = polx y (⟨2, by decide⟩ : Fin slotCount) := by
      simp [req002Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req002Terms ⟨4, -2, -1⟩ req002Zones check002 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row003 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨2, by decide⟩ : Fin slotCount) - 2 * polx y (⟨3, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req122Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req122Zones, z.span.scale = 1 := by simp [req122Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req122Terms = polx y (⟨2, by decide⟩ : Fin slotCount) - 2 * polx y (⟨3, by decide⟩ : Fin slotCount) := by
      simp [req122Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req122Terms ⟨0, 1, 0⟩ req122Zones check122 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row004 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨3, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req003Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req003Zones, z.span.scale = 1 := by simp [req003Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req003Terms = polx y (⟨3, by decide⟩ : Fin slotCount) := by
      simp [req003Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req003Terms ⟨-4, 4, 3⟩ req003Zones check003 hs (P72.h N % p - 1) horder
  have row005 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨5, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req004Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req004Zones, z.span.scale = 1 := by simp [req004Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req004Terms = polx y (⟨5, by decide⟩ : Fin slotCount) := by
      simp [req004Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req004Terms ⟨4, -3, -2⟩ req004Zones check004 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row006 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨5, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req005Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req005Zones, z.span.scale = 1 := by simp [req005Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req005Terms = polx y (⟨5, by decide⟩ : Fin slotCount) := by
      simp [req005Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req005Terms ⟨-4, 4, 2⟩ req005Zones check005 hs (P72.h N % p) horder
  have row007 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨6, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req006Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req006Zones, z.span.scale = 1 := by simp [req006Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req006Terms = polx y (⟨6, by decide⟩ : Fin slotCount) := by
      simp [req006Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req006Terms ⟨4, -2, -1⟩ req006Zones check006 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row008 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨6, by decide⟩ : Fin slotCount) - 2 * polx y (⟨7, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req123Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req123Zones, z.span.scale = 1 := by simp [req123Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req123Terms = polx y (⟨6, by decide⟩ : Fin slotCount) - 2 * polx y (⟨7, by decide⟩ : Fin slotCount) := by
      simp [req123Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req123Terms ⟨0, 1, 0⟩ req123Zones check123 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row009 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨7, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req007Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req007Zones, z.span.scale = 1 := by simp [req007Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req007Terms = polx y (⟨7, by decide⟩ : Fin slotCount) := by
      simp [req007Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req007Terms ⟨-4, 4, 3⟩ req007Zones check007 hs (P72.h N % p - 1) horder
  have row010 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨9, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req008Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req008Zones, z.span.scale = 1 := by simp [req008Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req008Terms = polx y (⟨9, by decide⟩ : Fin slotCount) := by
      simp [req008Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req008Terms ⟨4, -3, -2⟩ req008Zones check008 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row011 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨9, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req009Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req009Zones, z.span.scale = 1 := by simp [req009Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req009Terms = polx y (⟨9, by decide⟩ : Fin slotCount) := by
      simp [req009Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req009Terms ⟨-4, 4, 2⟩ req009Zones check009 hs (P72.h N % p) horder
  have row012 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨10, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req010Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req010Zones, z.span.scale = 1 := by simp [req010Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req010Terms = polx y (⟨10, by decide⟩ : Fin slotCount) := by
      simp [req010Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req010Terms ⟨4, -2, -1⟩ req010Zones check010 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row013 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨10, by decide⟩ : Fin slotCount) - 2 * polx y (⟨11, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req124Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req124Zones, z.span.scale = 1 := by simp [req124Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req124Terms = polx y (⟨10, by decide⟩ : Fin slotCount) - 2 * polx y (⟨11, by decide⟩ : Fin slotCount) := by
      simp [req124Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req124Terms ⟨0, 1, 0⟩ req124Zones check124 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row014 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨11, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req011Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req011Zones, z.span.scale = 1 := by simp [req011Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req011Terms = polx y (⟨11, by decide⟩ : Fin slotCount) := by
      simp [req011Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req011Terms ⟨-4, 4, 3⟩ req011Zones check011 hs (P72.h N % p - 1) horder
  have row015 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨13, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req012Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req012Zones, z.span.scale = 1 := by simp [req012Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req012Terms = polx y (⟨13, by decide⟩ : Fin slotCount) := by
      simp [req012Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req012Terms ⟨4, -3, -2⟩ req012Zones check012 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row016 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨13, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req013Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req013Zones, z.span.scale = 1 := by simp [req013Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req013Terms = polx y (⟨13, by decide⟩ : Fin slotCount) := by
      simp [req013Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req013Terms ⟨-4, 4, 2⟩ req013Zones check013 hs (P72.h N % p) horder
  have row017 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨14, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req014Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req014Zones, z.span.scale = 1 := by simp [req014Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req014Terms = polx y (⟨14, by decide⟩ : Fin slotCount) := by
      simp [req014Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req014Terms ⟨4, -2, -1⟩ req014Zones check014 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row018 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨14, by decide⟩ : Fin slotCount) - 2 * polx y (⟨15, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req125Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req125Zones, z.span.scale = 1 := by simp [req125Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req125Terms = polx y (⟨14, by decide⟩ : Fin slotCount) - 2 * polx y (⟨15, by decide⟩ : Fin slotCount) := by
      simp [req125Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req125Terms ⟨0, 1, 0⟩ req125Zones check125 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row019 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨15, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req015Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req015Zones, z.span.scale = 1 := by simp [req015Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req015Terms = polx y (⟨15, by decide⟩ : Fin slotCount) := by
      simp [req015Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req015Terms ⟨-4, 4, 3⟩ req015Zones check015 hs (P72.h N % p - 1) horder
  have row020 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨17, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req016Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req016Zones, z.span.scale = 1 := by simp [req016Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req016Terms = polx y (⟨17, by decide⟩ : Fin slotCount) := by
      simp [req016Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req016Terms ⟨4, -3, -2⟩ req016Zones check016 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row021 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨17, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req017Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req017Zones, z.span.scale = 1 := by simp [req017Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req017Terms = polx y (⟨17, by decide⟩ : Fin slotCount) := by
      simp [req017Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req017Terms ⟨-4, 4, 2⟩ req017Zones check017 hs (P72.h N % p) horder
  have row022 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨18, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req018Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req018Zones, z.span.scale = 1 := by simp [req018Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req018Terms = polx y (⟨18, by decide⟩ : Fin slotCount) := by
      simp [req018Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req018Terms ⟨4, -2, -1⟩ req018Zones check018 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row023 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨18, by decide⟩ : Fin slotCount) - 2 * polx y (⟨19, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req126Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req126Zones, z.span.scale = 1 := by simp [req126Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req126Terms = polx y (⟨18, by decide⟩ : Fin slotCount) - 2 * polx y (⟨19, by decide⟩ : Fin slotCount) := by
      simp [req126Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req126Terms ⟨0, 1, 0⟩ req126Zones check126 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row024 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨19, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req019Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req019Zones, z.span.scale = 1 := by simp [req019Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req019Terms = polx y (⟨19, by decide⟩ : Fin slotCount) := by
      simp [req019Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req019Terms ⟨-4, 4, 3⟩ req019Zones check019 hs (P72.h N % p - 1) horder
  have row025 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨21, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req020Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req020Zones, z.span.scale = 1 := by simp [req020Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req020Terms = polx y (⟨21, by decide⟩ : Fin slotCount) := by
      simp [req020Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req020Terms ⟨4, -3, -2⟩ req020Zones check020 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row026 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨21, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req021Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req021Zones, z.span.scale = 1 := by simp [req021Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req021Terms = polx y (⟨21, by decide⟩ : Fin slotCount) := by
      simp [req021Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req021Terms ⟨-4, 4, 2⟩ req021Zones check021 hs (P72.h N % p) horder
  have row027 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨22, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req022Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req022Zones, z.span.scale = 1 := by simp [req022Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req022Terms = polx y (⟨22, by decide⟩ : Fin slotCount) := by
      simp [req022Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req022Terms ⟨4, -2, -1⟩ req022Zones check022 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row028 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨22, by decide⟩ : Fin slotCount) - 2 * polx y (⟨23, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req127Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req127Zones, z.span.scale = 1 := by simp [req127Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req127Terms = polx y (⟨22, by decide⟩ : Fin slotCount) - 2 * polx y (⟨23, by decide⟩ : Fin slotCount) := by
      simp [req127Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req127Terms ⟨0, 1, 0⟩ req127Zones check127 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row029 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨23, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req023Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req023Zones, z.span.scale = 1 := by simp [req023Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req023Terms = polx y (⟨23, by decide⟩ : Fin slotCount) := by
      simp [req023Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req023Terms ⟨-4, 4, 3⟩ req023Zones check023 hs (P72.h N % p - 1) horder
  have row030 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨25, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req024Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req024Zones, z.span.scale = 1 := by simp [req024Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req024Terms = polx y (⟨25, by decide⟩ : Fin slotCount) := by
      simp [req024Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req024Terms ⟨4, -3, -2⟩ req024Zones check024 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row031 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨25, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req025Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req025Zones, z.span.scale = 1 := by simp [req025Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req025Terms = polx y (⟨25, by decide⟩ : Fin slotCount) := by
      simp [req025Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req025Terms ⟨-4, 4, 2⟩ req025Zones check025 hs (P72.h N % p) horder
  have row032 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨26, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req026Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req026Zones, z.span.scale = 1 := by simp [req026Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req026Terms = polx y (⟨26, by decide⟩ : Fin slotCount) := by
      simp [req026Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req026Terms ⟨4, -2, -1⟩ req026Zones check026 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row033 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨26, by decide⟩ : Fin slotCount) - 2 * polx y (⟨27, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req128Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req128Zones, z.span.scale = 1 := by simp [req128Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req128Terms = polx y (⟨26, by decide⟩ : Fin slotCount) - 2 * polx y (⟨27, by decide⟩ : Fin slotCount) := by
      simp [req128Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req128Terms ⟨0, 1, 0⟩ req128Zones check128 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row034 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨27, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req027Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req027Zones, z.span.scale = 1 := by simp [req027Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req027Terms = polx y (⟨27, by decide⟩ : Fin slotCount) := by
      simp [req027Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req027Terms ⟨-4, 4, 3⟩ req027Zones check027 hs (P72.h N % p - 1) horder
  have row035 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨29, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req028Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req028Zones, z.span.scale = 1 := by simp [req028Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req028Terms = polx y (⟨29, by decide⟩ : Fin slotCount) := by
      simp [req028Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req028Terms ⟨4, -3, -2⟩ req028Zones check028 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row036 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨29, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req029Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req029Zones, z.span.scale = 1 := by simp [req029Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req029Terms = polx y (⟨29, by decide⟩ : Fin slotCount) := by
      simp [req029Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req029Terms ⟨-4, 4, 2⟩ req029Zones check029 hs (P72.h N % p) horder
  have row037 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨30, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req030Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req030Zones, z.span.scale = 1 := by simp [req030Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req030Terms = polx y (⟨30, by decide⟩ : Fin slotCount) := by
      simp [req030Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req030Terms ⟨4, -2, -1⟩ req030Zones check030 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row038 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨30, by decide⟩ : Fin slotCount) - 2 * polx y (⟨31, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req129Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req129Zones, z.span.scale = 1 := by simp [req129Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req129Terms = polx y (⟨30, by decide⟩ : Fin slotCount) - 2 * polx y (⟨31, by decide⟩ : Fin slotCount) := by
      simp [req129Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req129Terms ⟨0, 1, 0⟩ req129Zones check129 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row039 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨31, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req031Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req031Zones, z.span.scale = 1 := by simp [req031Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req031Terms = polx y (⟨31, by decide⟩ : Fin slotCount) := by
      simp [req031Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req031Terms ⟨-4, 4, 3⟩ req031Zones check031 hs (P72.h N % p - 1) horder
  have row040 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨33, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req032Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req032Zones, z.span.scale = 1 := by simp [req032Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req032Terms = polx y (⟨33, by decide⟩ : Fin slotCount) := by
      simp [req032Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req032Terms ⟨4, -3, -2⟩ req032Zones check032 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row041 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨33, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req033Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req033Zones, z.span.scale = 1 := by simp [req033Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req033Terms = polx y (⟨33, by decide⟩ : Fin slotCount) := by
      simp [req033Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req033Terms ⟨-4, 4, 2⟩ req033Zones check033 hs (P72.h N % p) horder
  have row042 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨34, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req034Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req034Zones, z.span.scale = 1 := by simp [req034Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req034Terms = polx y (⟨34, by decide⟩ : Fin slotCount) := by
      simp [req034Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req034Terms ⟨4, -2, -1⟩ req034Zones check034 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row043 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨34, by decide⟩ : Fin slotCount) - 2 * polx y (⟨35, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req130Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req130Zones, z.span.scale = 1 := by simp [req130Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req130Terms = polx y (⟨34, by decide⟩ : Fin slotCount) - 2 * polx y (⟨35, by decide⟩ : Fin slotCount) := by
      simp [req130Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req130Terms ⟨0, 1, 0⟩ req130Zones check130 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row044 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨35, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req035Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req035Zones, z.span.scale = 1 := by simp [req035Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req035Terms = polx y (⟨35, by decide⟩ : Fin slotCount) := by
      simp [req035Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req035Terms ⟨-4, 4, 3⟩ req035Zones check035 hs (P72.h N % p - 1) horder
  have row045 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨37, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req036Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req036Zones, z.span.scale = 1 := by simp [req036Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req036Terms = polx y (⟨37, by decide⟩ : Fin slotCount) := by
      simp [req036Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req036Terms ⟨4, -3, -2⟩ req036Zones check036 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row046 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨37, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req037Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req037Zones, z.span.scale = 1 := by simp [req037Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req037Terms = polx y (⟨37, by decide⟩ : Fin slotCount) := by
      simp [req037Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req037Terms ⟨-4, 4, 2⟩ req037Zones check037 hs (P72.h N % p) horder
  have row047 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨38, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req038Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req038Zones, z.span.scale = 1 := by simp [req038Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req038Terms = polx y (⟨38, by decide⟩ : Fin slotCount) := by
      simp [req038Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req038Terms ⟨4, -2, -1⟩ req038Zones check038 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row048 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨38, by decide⟩ : Fin slotCount) - 2 * polx y (⟨39, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req131Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req131Zones, z.span.scale = 1 := by simp [req131Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req131Terms = polx y (⟨38, by decide⟩ : Fin slotCount) - 2 * polx y (⟨39, by decide⟩ : Fin slotCount) := by
      simp [req131Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req131Terms ⟨0, 1, 0⟩ req131Zones check131 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row049 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨39, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req039Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req039Zones, z.span.scale = 1 := by simp [req039Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req039Terms = polx y (⟨39, by decide⟩ : Fin slotCount) := by
      simp [req039Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req039Terms ⟨-4, 4, 3⟩ req039Zones check039 hs (P72.h N % p - 1) horder
  have row050 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨41, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req040Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req040Zones, z.span.scale = 1 := by simp [req040Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req040Terms = polx y (⟨41, by decide⟩ : Fin slotCount) := by
      simp [req040Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req040Terms ⟨4, -3, -2⟩ req040Zones check040 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row051 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨41, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req041Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req041Zones, z.span.scale = 1 := by simp [req041Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req041Terms = polx y (⟨41, by decide⟩ : Fin slotCount) := by
      simp [req041Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req041Terms ⟨-4, 4, 2⟩ req041Zones check041 hs (P72.h N % p) horder
  have row052 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨42, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req042Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req042Zones, z.span.scale = 1 := by simp [req042Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req042Terms = polx y (⟨42, by decide⟩ : Fin slotCount) := by
      simp [req042Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req042Terms ⟨4, -2, -1⟩ req042Zones check042 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row053 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨42, by decide⟩ : Fin slotCount) - 2 * polx y (⟨43, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req132Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req132Zones, z.span.scale = 1 := by simp [req132Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req132Terms = polx y (⟨42, by decide⟩ : Fin slotCount) - 2 * polx y (⟨43, by decide⟩ : Fin slotCount) := by
      simp [req132Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req132Terms ⟨0, 1, 0⟩ req132Zones check132 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row054 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨43, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req043Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req043Zones, z.span.scale = 1 := by simp [req043Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req043Terms = polx y (⟨43, by decide⟩ : Fin slotCount) := by
      simp [req043Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req043Terms ⟨-4, 4, 3⟩ req043Zones check043 hs (P72.h N % p - 1) horder
  have row055 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨45, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req044Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req044Zones, z.span.scale = 1 := by simp [req044Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req044Terms = polx y (⟨45, by decide⟩ : Fin slotCount) := by
      simp [req044Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req044Terms ⟨4, -3, -2⟩ req044Zones check044 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row056 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨45, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req045Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req045Zones, z.span.scale = 1 := by simp [req045Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req045Terms = polx y (⟨45, by decide⟩ : Fin slotCount) := by
      simp [req045Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req045Terms ⟨-4, 4, 2⟩ req045Zones check045 hs (P72.h N % p) horder
  have row057 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨46, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req046Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req046Zones, z.span.scale = 1 := by simp [req046Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req046Terms = polx y (⟨46, by decide⟩ : Fin slotCount) := by
      simp [req046Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req046Terms ⟨4, -2, -1⟩ req046Zones check046 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row058 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨46, by decide⟩ : Fin slotCount) - 2 * polx y (⟨47, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req133Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req133Zones, z.span.scale = 1 := by simp [req133Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req133Terms = polx y (⟨46, by decide⟩ : Fin slotCount) - 2 * polx y (⟨47, by decide⟩ : Fin slotCount) := by
      simp [req133Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req133Terms ⟨0, 1, 0⟩ req133Zones check133 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row059 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨47, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req047Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req047Zones, z.span.scale = 1 := by simp [req047Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req047Terms = polx y (⟨47, by decide⟩ : Fin slotCount) := by
      simp [req047Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req047Terms ⟨-4, 4, 3⟩ req047Zones check047 hs (P72.h N % p - 1) horder
  have row060 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨49, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req048Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req048Zones, z.span.scale = 1 := by simp [req048Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req048Terms = polx y (⟨49, by decide⟩ : Fin slotCount) := by
      simp [req048Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req048Terms ⟨4, -3, -2⟩ req048Zones check048 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row061 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨49, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req049Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req049Zones, z.span.scale = 1 := by simp [req049Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req049Terms = polx y (⟨49, by decide⟩ : Fin slotCount) := by
      simp [req049Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req049Terms ⟨-4, 4, 2⟩ req049Zones check049 hs (P72.h N % p) horder
  have row062 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨50, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req050Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req050Zones, z.span.scale = 1 := by simp [req050Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req050Terms = polx y (⟨50, by decide⟩ : Fin slotCount) := by
      simp [req050Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req050Terms ⟨4, -2, -1⟩ req050Zones check050 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row063 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨50, by decide⟩ : Fin slotCount) - 2 * polx y (⟨51, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req134Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req134Zones, z.span.scale = 1 := by simp [req134Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req134Terms = polx y (⟨50, by decide⟩ : Fin slotCount) - 2 * polx y (⟨51, by decide⟩ : Fin slotCount) := by
      simp [req134Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req134Terms ⟨0, 1, 0⟩ req134Zones check134 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row064 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨51, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req051Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req051Zones, z.span.scale = 1 := by simp [req051Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req051Terms = polx y (⟨51, by decide⟩ : Fin slotCount) := by
      simp [req051Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req051Terms ⟨-4, 4, 3⟩ req051Zones check051 hs (P72.h N % p - 1) horder
  have row065 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨53, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req052Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req052Zones, z.span.scale = 1 := by simp [req052Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req052Terms = polx y (⟨53, by decide⟩ : Fin slotCount) := by
      simp [req052Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req052Terms ⟨4, -3, -2⟩ req052Zones check052 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row066 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨53, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req053Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req053Zones, z.span.scale = 1 := by simp [req053Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req053Terms = polx y (⟨53, by decide⟩ : Fin slotCount) := by
      simp [req053Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req053Terms ⟨-4, 4, 2⟩ req053Zones check053 hs (P72.h N % p) horder
  have row067 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨54, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req054Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req054Zones, z.span.scale = 1 := by simp [req054Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req054Terms = polx y (⟨54, by decide⟩ : Fin slotCount) := by
      simp [req054Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req054Terms ⟨4, -2, -1⟩ req054Zones check054 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row068 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨54, by decide⟩ : Fin slotCount) - 2 * polx y (⟨55, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req135Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req135Zones, z.span.scale = 1 := by simp [req135Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req135Terms = polx y (⟨54, by decide⟩ : Fin slotCount) - 2 * polx y (⟨55, by decide⟩ : Fin slotCount) := by
      simp [req135Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req135Terms ⟨0, 1, 0⟩ req135Zones check135 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row069 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨55, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req055Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req055Zones, z.span.scale = 1 := by simp [req055Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req055Terms = polx y (⟨55, by decide⟩ : Fin slotCount) := by
      simp [req055Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req055Terms ⟨-4, 4, 3⟩ req055Zones check055 hs (P72.h N % p - 1) horder
  have row070 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨57, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req056Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req056Zones, z.span.scale = 1 := by simp [req056Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req056Terms = polx y (⟨57, by decide⟩ : Fin slotCount) := by
      simp [req056Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req056Terms ⟨4, -3, -2⟩ req056Zones check056 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row071 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨57, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req057Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req057Zones, z.span.scale = 1 := by simp [req057Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req057Terms = polx y (⟨57, by decide⟩ : Fin slotCount) := by
      simp [req057Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req057Terms ⟨-4, 4, 2⟩ req057Zones check057 hs (P72.h N % p) horder
  have row072 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨58, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req058Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req058Zones, z.span.scale = 1 := by simp [req058Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req058Terms = polx y (⟨58, by decide⟩ : Fin slotCount) := by
      simp [req058Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req058Terms ⟨4, -2, -1⟩ req058Zones check058 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row073 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨58, by decide⟩ : Fin slotCount) - 2 * polx y (⟨59, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req136Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req136Zones, z.span.scale = 1 := by simp [req136Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req136Terms = polx y (⟨58, by decide⟩ : Fin slotCount) - 2 * polx y (⟨59, by decide⟩ : Fin slotCount) := by
      simp [req136Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req136Terms ⟨0, 1, 0⟩ req136Zones check136 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row074 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨59, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req059Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req059Zones, z.span.scale = 1 := by simp [req059Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req059Terms = polx y (⟨59, by decide⟩ : Fin slotCount) := by
      simp [req059Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req059Terms ⟨-4, 4, 3⟩ req059Zones check059 hs (P72.h N % p - 1) horder
  have row075 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨61, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req060Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req060Zones, z.span.scale = 1 := by simp [req060Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req060Terms = polx y (⟨61, by decide⟩ : Fin slotCount) := by
      simp [req060Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req060Terms ⟨4, -3, -2⟩ req060Zones check060 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row076 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨61, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req061Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req061Zones, z.span.scale = 1 := by simp [req061Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req061Terms = polx y (⟨61, by decide⟩ : Fin slotCount) := by
      simp [req061Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req061Terms ⟨-4, 4, 2⟩ req061Zones check061 hs (P72.h N % p) horder
  have row077 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨62, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req062Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req062Zones, z.span.scale = 1 := by simp [req062Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req062Terms = polx y (⟨62, by decide⟩ : Fin slotCount) := by
      simp [req062Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req062Terms ⟨4, -2, -1⟩ req062Zones check062 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row078 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨62, by decide⟩ : Fin slotCount) - 2 * polx y (⟨63, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req137Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req137Zones, z.span.scale = 1 := by simp [req137Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req137Terms = polx y (⟨62, by decide⟩ : Fin slotCount) - 2 * polx y (⟨63, by decide⟩ : Fin slotCount) := by
      simp [req137Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req137Terms ⟨0, 1, 0⟩ req137Zones check137 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row079 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨63, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req063Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req063Zones, z.span.scale = 1 := by simp [req063Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req063Terms = polx y (⟨63, by decide⟩ : Fin slotCount) := by
      simp [req063Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req063Terms ⟨-4, 4, 3⟩ req063Zones check063 hs (P72.h N % p - 1) horder
  have row080 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨65, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req064Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req064Zones, z.span.scale = 1 := by simp [req064Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req064Terms = polx y (⟨65, by decide⟩ : Fin slotCount) := by
      simp [req064Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req064Terms ⟨4, -3, -2⟩ req064Zones check064 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row081 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨65, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req065Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req065Zones, z.span.scale = 1 := by simp [req065Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req065Terms = polx y (⟨65, by decide⟩ : Fin slotCount) := by
      simp [req065Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req065Terms ⟨-4, 4, 2⟩ req065Zones check065 hs (P72.h N % p) horder
  have row082 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨66, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req066Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req066Zones, z.span.scale = 1 := by simp [req066Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req066Terms = polx y (⟨66, by decide⟩ : Fin slotCount) := by
      simp [req066Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req066Terms ⟨4, -2, -1⟩ req066Zones check066 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row083 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨66, by decide⟩ : Fin slotCount) - 2 * polx y (⟨67, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req138Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req138Zones, z.span.scale = 1 := by simp [req138Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req138Terms = polx y (⟨66, by decide⟩ : Fin slotCount) - 2 * polx y (⟨67, by decide⟩ : Fin slotCount) := by
      simp [req138Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req138Terms ⟨0, 1, 0⟩ req138Zones check138 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row084 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨67, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req067Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req067Zones, z.span.scale = 1 := by simp [req067Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req067Terms = polx y (⟨67, by decide⟩ : Fin slotCount) := by
      simp [req067Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req067Terms ⟨-4, 4, 3⟩ req067Zones check067 hs (P72.h N % p - 1) horder
  have row085 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨69, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req068Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req068Zones, z.span.scale = 1 := by simp [req068Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req068Terms = polx y (⟨69, by decide⟩ : Fin slotCount) := by
      simp [req068Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req068Terms ⟨4, -3, -2⟩ req068Zones check068 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row086 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨69, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req069Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req069Zones, z.span.scale = 1 := by simp [req069Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req069Terms = polx y (⟨69, by decide⟩ : Fin slotCount) := by
      simp [req069Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req069Terms ⟨-4, 4, 2⟩ req069Zones check069 hs (P72.h N % p) horder
  have row087 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨70, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req070Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req070Zones, z.span.scale = 1 := by simp [req070Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req070Terms = polx y (⟨70, by decide⟩ : Fin slotCount) := by
      simp [req070Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req070Terms ⟨4, -2, -1⟩ req070Zones check070 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row088 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨70, by decide⟩ : Fin slotCount) - 2 * polx y (⟨71, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req139Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req139Zones, z.span.scale = 1 := by simp [req139Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req139Terms = polx y (⟨70, by decide⟩ : Fin slotCount) - 2 * polx y (⟨71, by decide⟩ : Fin slotCount) := by
      simp [req139Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req139Terms ⟨0, 1, 0⟩ req139Zones check139 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row089 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨71, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req071Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req071Zones, z.span.scale = 1 := by simp [req071Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req071Terms = polx y (⟨71, by decide⟩ : Fin slotCount) := by
      simp [req071Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req071Terms ⟨-4, 4, 3⟩ req071Zones check071 hs (P72.h N % p - 1) horder
  have row090 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨73, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req072Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req072Zones, z.span.scale = 1 := by simp [req072Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req072Terms = polx y (⟨73, by decide⟩ : Fin slotCount) := by
      simp [req072Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req072Terms ⟨4, -3, -2⟩ req072Zones check072 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row091 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨73, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req073Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req073Zones, z.span.scale = 1 := by simp [req073Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req073Terms = polx y (⟨73, by decide⟩ : Fin slotCount) := by
      simp [req073Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req073Terms ⟨-4, 4, 2⟩ req073Zones check073 hs (P72.h N % p) horder
  have row092 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨74, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req074Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req074Zones, z.span.scale = 1 := by simp [req074Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req074Terms = polx y (⟨74, by decide⟩ : Fin slotCount) := by
      simp [req074Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req074Terms ⟨4, -2, -1⟩ req074Zones check074 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row093 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨74, by decide⟩ : Fin slotCount) - 2 * polx y (⟨75, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req140Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req140Zones, z.span.scale = 1 := by simp [req140Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req140Terms = polx y (⟨74, by decide⟩ : Fin slotCount) - 2 * polx y (⟨75, by decide⟩ : Fin slotCount) := by
      simp [req140Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req140Terms ⟨0, 1, 0⟩ req140Zones check140 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row094 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨75, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req075Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req075Zones, z.span.scale = 1 := by simp [req075Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req075Terms = polx y (⟨75, by decide⟩ : Fin slotCount) := by
      simp [req075Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req075Terms ⟨-4, 4, 3⟩ req075Zones check075 hs (P72.h N % p - 1) horder
  have row095 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨77, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req076Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req076Zones, z.span.scale = 1 := by simp [req076Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req076Terms = polx y (⟨77, by decide⟩ : Fin slotCount) := by
      simp [req076Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req076Terms ⟨4, -3, -2⟩ req076Zones check076 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row096 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨77, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req077Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req077Zones, z.span.scale = 1 := by simp [req077Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req077Terms = polx y (⟨77, by decide⟩ : Fin slotCount) := by
      simp [req077Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req077Terms ⟨-4, 4, 2⟩ req077Zones check077 hs (P72.h N % p) horder
  have row097 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨78, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req078Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req078Zones, z.span.scale = 1 := by simp [req078Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req078Terms = polx y (⟨78, by decide⟩ : Fin slotCount) := by
      simp [req078Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req078Terms ⟨4, -2, -1⟩ req078Zones check078 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row098 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨78, by decide⟩ : Fin slotCount) - 2 * polx y (⟨79, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req141Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req141Zones, z.span.scale = 1 := by simp [req141Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req141Terms = polx y (⟨78, by decide⟩ : Fin slotCount) - 2 * polx y (⟨79, by decide⟩ : Fin slotCount) := by
      simp [req141Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req141Terms ⟨0, 1, 0⟩ req141Zones check141 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row099 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨79, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req079Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req079Zones, z.span.scale = 1 := by simp [req079Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req079Terms = polx y (⟨79, by decide⟩ : Fin slotCount) := by
      simp [req079Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req079Terms ⟨-4, 4, 3⟩ req079Zones check079 hs (P72.h N % p - 1) horder
  have row100 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨81, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req080Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req080Zones, z.span.scale = 1 := by simp [req080Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req080Terms = polx y (⟨81, by decide⟩ : Fin slotCount) := by
      simp [req080Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req080Terms ⟨4, -3, -2⟩ req080Zones check080 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row101 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨81, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req081Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req081Zones, z.span.scale = 1 := by simp [req081Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req081Terms = polx y (⟨81, by decide⟩ : Fin slotCount) := by
      simp [req081Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req081Terms ⟨-4, 4, 2⟩ req081Zones check081 hs (P72.h N % p) horder
  have row102 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨82, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req082Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req082Zones, z.span.scale = 1 := by simp [req082Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req082Terms = polx y (⟨82, by decide⟩ : Fin slotCount) := by
      simp [req082Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req082Terms ⟨4, -2, -1⟩ req082Zones check082 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row103 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨82, by decide⟩ : Fin slotCount) - 2 * polx y (⟨83, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req142Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req142Zones, z.span.scale = 1 := by simp [req142Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req142Terms = polx y (⟨82, by decide⟩ : Fin slotCount) - 2 * polx y (⟨83, by decide⟩ : Fin slotCount) := by
      simp [req142Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req142Terms ⟨0, 1, 0⟩ req142Zones check142 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row104 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨83, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req083Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req083Zones, z.span.scale = 1 := by simp [req083Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req083Terms = polx y (⟨83, by decide⟩ : Fin slotCount) := by
      simp [req083Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req083Terms ⟨-4, 4, 3⟩ req083Zones check083 hs (P72.h N % p - 1) horder
  have row105 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨85, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req084Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req084Zones, z.span.scale = 1 := by simp [req084Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req084Terms = polx y (⟨85, by decide⟩ : Fin slotCount) := by
      simp [req084Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req084Terms ⟨4, -3, -2⟩ req084Zones check084 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row106 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨85, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req085Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req085Zones, z.span.scale = 1 := by simp [req085Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req085Terms = polx y (⟨85, by decide⟩ : Fin slotCount) := by
      simp [req085Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req085Terms ⟨-4, 4, 2⟩ req085Zones check085 hs (P72.h N % p) horder
  have row107 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨86, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req086Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req086Zones, z.span.scale = 1 := by simp [req086Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req086Terms = polx y (⟨86, by decide⟩ : Fin slotCount) := by
      simp [req086Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req086Terms ⟨4, -2, -1⟩ req086Zones check086 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row108 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨86, by decide⟩ : Fin slotCount) - 2 * polx y (⟨87, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req143Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req143Zones, z.span.scale = 1 := by simp [req143Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req143Terms = polx y (⟨86, by decide⟩ : Fin slotCount) - 2 * polx y (⟨87, by decide⟩ : Fin slotCount) := by
      simp [req143Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req143Terms ⟨0, 1, 0⟩ req143Zones check143 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row109 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨87, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req087Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req087Zones, z.span.scale = 1 := by simp [req087Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req087Terms = polx y (⟨87, by decide⟩ : Fin slotCount) := by
      simp [req087Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req087Terms ⟨-4, 4, 3⟩ req087Zones check087 hs (P72.h N % p - 1) horder
  have row110 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨89, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req088Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req088Zones, z.span.scale = 1 := by simp [req088Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req088Terms = polx y (⟨89, by decide⟩ : Fin slotCount) := by
      simp [req088Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req088Terms ⟨4, -3, -2⟩ req088Zones check088 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row111 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨89, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req089Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req089Zones, z.span.scale = 1 := by simp [req089Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req089Terms = polx y (⟨89, by decide⟩ : Fin slotCount) := by
      simp [req089Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req089Terms ⟨-4, 4, 2⟩ req089Zones check089 hs (P72.h N % p) horder
  have row112 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨90, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req090Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req090Zones, z.span.scale = 1 := by simp [req090Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req090Terms = polx y (⟨90, by decide⟩ : Fin slotCount) := by
      simp [req090Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req090Terms ⟨4, -2, -1⟩ req090Zones check090 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row113 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨90, by decide⟩ : Fin slotCount) - 2 * polx y (⟨91, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req144Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req144Zones, z.span.scale = 1 := by simp [req144Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req144Terms = polx y (⟨90, by decide⟩ : Fin slotCount) - 2 * polx y (⟨91, by decide⟩ : Fin slotCount) := by
      simp [req144Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req144Terms ⟨0, 1, 0⟩ req144Zones check144 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row114 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨91, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req091Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req091Zones, z.span.scale = 1 := by simp [req091Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req091Terms = polx y (⟨91, by decide⟩ : Fin slotCount) := by
      simp [req091Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req091Terms ⟨-4, 4, 3⟩ req091Zones check091 hs (P72.h N % p - 1) horder
  have row115 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨93, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req092Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req092Zones, z.span.scale = 1 := by simp [req092Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req092Terms = polx y (⟨93, by decide⟩ : Fin slotCount) := by
      simp [req092Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req092Terms ⟨4, -3, -2⟩ req092Zones check092 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row116 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨93, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req093Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req093Zones, z.span.scale = 1 := by simp [req093Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req093Terms = polx y (⟨93, by decide⟩ : Fin slotCount) := by
      simp [req093Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req093Terms ⟨-4, 4, 2⟩ req093Zones check093 hs (P72.h N % p) horder
  have row117 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨94, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req094Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req094Zones, z.span.scale = 1 := by simp [req094Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req094Terms = polx y (⟨94, by decide⟩ : Fin slotCount) := by
      simp [req094Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req094Terms ⟨4, -2, -1⟩ req094Zones check094 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row118 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨94, by decide⟩ : Fin slotCount) - 2 * polx y (⟨95, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req145Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req145Zones, z.span.scale = 1 := by simp [req145Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req145Terms = polx y (⟨94, by decide⟩ : Fin slotCount) - 2 * polx y (⟨95, by decide⟩ : Fin slotCount) := by
      simp [req145Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req145Terms ⟨0, 1, 0⟩ req145Zones check145 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row119 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨95, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req095Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req095Zones, z.span.scale = 1 := by simp [req095Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req095Terms = polx y (⟨95, by decide⟩ : Fin slotCount) := by
      simp [req095Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req095Terms ⟨-4, 4, 3⟩ req095Zones check095 hs (P72.h N % p - 1) horder
  have row120 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨97, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req096Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req096Zones, z.span.scale = 1 := by simp [req096Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req096Terms = polx y (⟨97, by decide⟩ : Fin slotCount) := by
      simp [req096Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req096Terms ⟨4, -3, -2⟩ req096Zones check096 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row121 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨97, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req097Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req097Zones, z.span.scale = 1 := by simp [req097Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req097Terms = polx y (⟨97, by decide⟩ : Fin slotCount) := by
      simp [req097Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req097Terms ⟨-4, 4, 2⟩ req097Zones check097 hs (P72.h N % p) horder
  have row122 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨98, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req098Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req098Zones, z.span.scale = 1 := by simp [req098Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req098Terms = polx y (⟨98, by decide⟩ : Fin slotCount) := by
      simp [req098Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req098Terms ⟨4, -2, -1⟩ req098Zones check098 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row123 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨98, by decide⟩ : Fin slotCount) - 2 * polx y (⟨99, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req146Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req146Zones, z.span.scale = 1 := by simp [req146Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req146Terms = polx y (⟨98, by decide⟩ : Fin slotCount) - 2 * polx y (⟨99, by decide⟩ : Fin slotCount) := by
      simp [req146Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req146Terms ⟨0, 1, 0⟩ req146Zones check146 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row124 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨99, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req099Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req099Zones, z.span.scale = 1 := by simp [req099Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req099Terms = polx y (⟨99, by decide⟩ : Fin slotCount) := by
      simp [req099Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req099Terms ⟨-4, 4, 3⟩ req099Zones check099 hs (P72.h N % p - 1) horder
  have row125 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨101, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req100Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req100Zones, z.span.scale = 1 := by simp [req100Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req100Terms = polx y (⟨101, by decide⟩ : Fin slotCount) := by
      simp [req100Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req100Terms ⟨4, -3, -2⟩ req100Zones check100 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row126 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨101, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req101Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req101Zones, z.span.scale = 1 := by simp [req101Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req101Terms = polx y (⟨101, by decide⟩ : Fin slotCount) := by
      simp [req101Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req101Terms ⟨-4, 4, 2⟩ req101Zones check101 hs (P72.h N % p) horder
  have row127 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨102, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req102Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req102Zones, z.span.scale = 1 := by simp [req102Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req102Terms = polx y (⟨102, by decide⟩ : Fin slotCount) := by
      simp [req102Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req102Terms ⟨4, -2, -1⟩ req102Zones check102 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row128 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨102, by decide⟩ : Fin slotCount) - 2 * polx y (⟨103, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req147Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req147Zones, z.span.scale = 1 := by simp [req147Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req147Terms = polx y (⟨102, by decide⟩ : Fin slotCount) - 2 * polx y (⟨103, by decide⟩ : Fin slotCount) := by
      simp [req147Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req147Terms ⟨0, 1, 0⟩ req147Zones check147 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row129 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨103, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req103Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req103Zones, z.span.scale = 1 := by simp [req103Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req103Terms = polx y (⟨103, by decide⟩ : Fin slotCount) := by
      simp [req103Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req103Terms ⟨-4, 4, 3⟩ req103Zones check103 hs (P72.h N % p - 1) horder
  have row130 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨105, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req104Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req104Zones, z.span.scale = 1 := by simp [req104Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req104Terms = polx y (⟨105, by decide⟩ : Fin slotCount) := by
      simp [req104Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req104Terms ⟨4, -3, -2⟩ req104Zones check104 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row131 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨105, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req105Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req105Zones, z.span.scale = 1 := by simp [req105Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req105Terms = polx y (⟨105, by decide⟩ : Fin slotCount) := by
      simp [req105Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req105Terms ⟨-4, 4, 2⟩ req105Zones check105 hs (P72.h N % p) horder
  have row132 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨106, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req106Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req106Zones, z.span.scale = 1 := by simp [req106Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req106Terms = polx y (⟨106, by decide⟩ : Fin slotCount) := by
      simp [req106Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req106Terms ⟨4, -2, -1⟩ req106Zones check106 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row133 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨106, by decide⟩ : Fin slotCount) - 2 * polx y (⟨107, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req148Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req148Zones, z.span.scale = 1 := by simp [req148Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req148Terms = polx y (⟨106, by decide⟩ : Fin slotCount) - 2 * polx y (⟨107, by decide⟩ : Fin slotCount) := by
      simp [req148Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req148Terms ⟨0, 1, 0⟩ req148Zones check148 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row134 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨107, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req107Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req107Zones, z.span.scale = 1 := by simp [req107Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req107Terms = polx y (⟨107, by decide⟩ : Fin slotCount) := by
      simp [req107Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req107Terms ⟨-4, 4, 3⟩ req107Zones check107 hs (P72.h N % p - 1) horder
  have row135 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨109, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req108Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req108Zones, z.span.scale = 1 := by simp [req108Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req108Terms = polx y (⟨109, by decide⟩ : Fin slotCount) := by
      simp [req108Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req108Terms ⟨4, -3, -2⟩ req108Zones check108 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row136 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨109, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req109Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req109Zones, z.span.scale = 1 := by simp [req109Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req109Terms = polx y (⟨109, by decide⟩ : Fin slotCount) := by
      simp [req109Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req109Terms ⟨-4, 4, 2⟩ req109Zones check109 hs (P72.h N % p) horder
  have row137 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨110, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req110Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req110Zones, z.span.scale = 1 := by simp [req110Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req110Terms = polx y (⟨110, by decide⟩ : Fin slotCount) := by
      simp [req110Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req110Terms ⟨4, -2, -1⟩ req110Zones check110 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row138 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨110, by decide⟩ : Fin slotCount) - 2 * polx y (⟨111, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req149Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req149Zones, z.span.scale = 1 := by simp [req149Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req149Terms = polx y (⟨110, by decide⟩ : Fin slotCount) - 2 * polx y (⟨111, by decide⟩ : Fin slotCount) := by
      simp [req149Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req149Terms ⟨0, 1, 0⟩ req149Zones check149 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row139 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨111, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req111Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req111Zones, z.span.scale = 1 := by simp [req111Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req111Terms = polx y (⟨111, by decide⟩ : Fin slotCount) := by
      simp [req111Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req111Terms ⟨-4, 4, 3⟩ req111Zones check111 hs (P72.h N % p - 1) horder
  have row140 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨113, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req112Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req112Zones, z.span.scale = 1 := by simp [req112Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req112Terms = polx y (⟨113, by decide⟩ : Fin slotCount) := by
      simp [req112Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req112Terms ⟨4, -3, -2⟩ req112Zones check112 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row141 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨113, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req113Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req113Zones, z.span.scale = 1 := by simp [req113Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req113Terms = polx y (⟨113, by decide⟩ : Fin slotCount) := by
      simp [req113Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req113Terms ⟨-4, 4, 2⟩ req113Zones check113 hs (P72.h N % p) horder
  have row142 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨114, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req114Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req114Zones, z.span.scale = 1 := by simp [req114Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req114Terms = polx y (⟨114, by decide⟩ : Fin slotCount) := by
      simp [req114Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req114Terms ⟨4, -2, -1⟩ req114Zones check114 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row143 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨114, by decide⟩ : Fin slotCount) - 2 * polx y (⟨115, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req150Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req150Zones, z.span.scale = 1 := by simp [req150Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req150Terms = polx y (⟨114, by decide⟩ : Fin slotCount) - 2 * polx y (⟨115, by decide⟩ : Fin slotCount) := by
      simp [req150Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req150Terms ⟨0, 1, 0⟩ req150Zones check150 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row144 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨115, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req115Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req115Zones, z.span.scale = 1 := by simp [req115Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req115Terms = polx y (⟨115, by decide⟩ : Fin slotCount) := by
      simp [req115Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req115Terms ⟨-4, 4, 3⟩ req115Zones check115 hs (P72.h N % p - 1) horder
  have row145 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨117, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req116Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req116Zones, z.span.scale = 1 := by simp [req116Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req116Terms = polx y (⟨117, by decide⟩ : Fin slotCount) := by
      simp [req116Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req116Terms ⟨4, -3, -2⟩ req116Zones check116 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row146 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨117, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req117Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req117Zones, z.span.scale = 1 := by simp [req117Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req117Terms = polx y (⟨117, by decide⟩ : Fin slotCount) := by
      simp [req117Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req117Terms ⟨-4, 4, 2⟩ req117Zones check117 hs (P72.h N % p) horder
  have row147 : ∀ j < (P72.h N % p), (taylor (1) (polx y (⟨118, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req118Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req118Zones, z.span.scale = 1 := by simp [req118Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req118Terms = polx y (⟨118, by decide⟩ : Fin slotCount) := by
      simp [req118Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req118Terms ⟨4, -2, -1⟩ req118Zones check118 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row148 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨118, by decide⟩ : Fin slotCount) - 2 * polx y (⟨119, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req151Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req151Zones, z.span.scale = 1 := by simp [req151Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req151Terms = polx y (⟨118, by decide⟩ : Fin slotCount) - 2 * polx y (⟨119, by decide⟩ : Fin slotCount) := by
      simp [req151Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req151Terms ⟨0, 1, 0⟩ req151Zones check151 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row149 : ∀ j, (P72.h N % p - 1) ≤ j → (polx y (⟨119, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req119Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req119Zones, z.span.scale = 1 := by simp [req119Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req119Terms = polx y (⟨119, by decide⟩ : Fin slotCount) := by
      simp [req119Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p - 1) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 3⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req119Terms ⟨-4, 4, 3⟩ req119Zones check119 hs (P72.h N % p - 1) horder
  have row150 : ∀ j < (P72.h N % p + (p-1)/2 - p), (taylor (1) (polx y (⟨121, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req120Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req120Zones, z.span.scale = 1 := by simp [req120Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req120Terms = polx y (⟨121, by decide⟩ : Fin slotCount) := by
      simp [req120Terms, slotPolynomial, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.plus req120Terms ⟨4, -3, -2⟩ req120Zones check120 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row151 : ∀ j, (P72.h N % p) ≤ j → (polx y (⟨121, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req121Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req121Zones, z.span.scale = 1 := by simp [req121Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req121Terms = polx y (⟨121, by decide⟩ : Fin slotCount) := by
      simp [req121Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : ((p - (P72.h N % p) : Nat) : Int) ≤ affAt N p ⟨-4, 4, 2⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req121Terms ⟨-4, 4, 2⟩ req121Zones check121 hs (P72.h N % p) horder
  have row152 : ∀ j < ((p-1)/2), (taylor (-1) (polx y (⟨120, by decide⟩ : Fin slotCount) - 2 * polx y (⟨121, by decide⟩ : Fin slotCount))).coeff j = 0 := by
    have hs : ∀ z ∈ req152Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req152Zones, z.span.scale = 1 := by simp [req152Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req152Terms = polx y (⟨120, by decide⟩ : Fin slotCount) - 2 * polx y (⟨121, by decide⟩ : Fin slotCount) := by
      simp [req152Terms, slotPolynomial, absent120, map_ofNat] <;> ring
    intro j hj
    rw [← he]
    apply ctx.minus req152Terms ⟨0, 1, 0⟩ req152Zones check152 hs j
    simp [affAt, Aff.eval, hhalf]
    omega
  have row153 : polx y (⟨1, by decide⟩ : Fin slotCount) - polx y (⟨3, by decide⟩ : Fin slotCount) + polx y (⟨121, by decide⟩ : Fin slotCount) = 0 := by
    have hs : ∀ z ∈ req153Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req153Zones, z.span.scale = 1 := by simp [req153Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req153Terms = polx y (⟨1, by decide⟩ : Fin slotCount) - polx y (⟨3, by decide⟩ : Fin slotCount) + polx y (⟨121, by decide⟩ : Fin slotCount) := by
      simp [req153Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : (p : Int) ≤ affAt N p ⟨0, 2, 1⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.zero req153Terms ⟨0, 2, 1⟩ req153Zones check153 hs horder
  have row154 : ∀ j, (Bfull) ≤ j → (polx y (⟨0, by decide⟩ : Fin slotCount) - polx y (⟨2, by decide⟩ : Fin slotCount) + polx y (⟨120, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req154Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req154Zones, z.span.scale = 1 := by simp [req154Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req154Terms = polx y (⟨0, by decide⟩ : Fin slotCount) - polx y (⟨2, by decide⟩ : Fin slotCount) + polx y (⟨120, by decide⟩ : Fin slotCount) := by
      simp [req154Terms, slotPolynomial, absent0, absent120, map_ofNat] <;> ring
    have horder : ((p - (Bfull) : Nat) : Int) ≤ affAt N p ⟨-10, 8, 4⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req154Terms ⟨-10, 8, 4⟩ req154Zones check154 hs (Bfull) horder
  have row155 : polx y (⟨117, by decide⟩ : Fin slotCount) + polx y (⟨119, by decide⟩ : Fin slotCount) = 0 := by
    have hs : ∀ z ∈ req155Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req155Zones, z.span.scale = 1 := by simp [req155Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req155Terms = polx y (⟨117, by decide⟩ : Fin slotCount) + polx y (⟨119, by decide⟩ : Fin slotCount) := by
      simp [req155Terms, slotPolynomial, map_ofNat] <;> ring
    have horder : (p : Int) ≤ affAt N p ⟨0, 2, 1⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.zero req155Terms ⟨0, 2, 1⟩ req155Zones check155 hs horder
  have row156 : ∀ j, (Tfull) ≤ j → (polx y (⟨116, by decide⟩ : Fin slotCount) + polx y (⟨118, by decide⟩ : Fin slotCount)).coeff j = 0 := by
    have hs : ∀ z ∈ req156Zones, ¬ (p : Int) ∣ z.span.scale := by
      have hscale : ∀ z ∈ req156Zones, z.span.scale = 1 := by simp [req156Zones]
      intro z hz
      rw [hscale z hz]
      exact fun hd => by have := Int.natAbs_dvd_natAbs.mpr hd; simp at this; omega
    have he : slotPolynomial y req156Terms = polx y (⟨116, by decide⟩ : Fin slotCount) + polx y (⟨118, by decide⟩ : Fin slotCount) := by
      simp [req156Terms, slotPolynomial, absent116, map_ofNat] <;> ring
    have horder : ((p - (Tfull) : Nat) : Int) ≤ affAt N p ⟨-70, 56, 29⟩ := by
      simp only [affAt, Aff.eval, hhalf, Bdeg, Tdeg, Bfull, Tfull, hr]
      omega
    rw [← he]
    exact ctx.tail req156Terms ⟨-70, 56, 29⟩ req156Zones check156 hs (Tfull) horder
  apply theta_range_mem hp2 hn hK y
  refine exists_rows_high_gen hp2 hn hK hbpos y hX hrpos hphase ?_ ?_ Bdeg Tdeg ?_ ?_ ?_ ?_ ?_
  · intro k
    have hkv : k.val < 30 := by have := k.isLt; omega
    interval_cases hk : k.val
    · rw [hI k 0 (⟨0, by decide⟩ : Fin slotCount) (by change 0 = 4 * k.val + 0; omega)]
      exact absent0
    · rw [hI k 0 (⟨4, by decide⟩ : Fin slotCount) (by change 4 = 4 * k.val + 0; omega)]
      exact absent4
    · rw [hI k 0 (⟨8, by decide⟩ : Fin slotCount) (by change 8 = 4 * k.val + 0; omega)]
      exact absent8
    · rw [hI k 0 (⟨12, by decide⟩ : Fin slotCount) (by change 12 = 4 * k.val + 0; omega)]
      exact absent12
    · rw [hI k 0 (⟨16, by decide⟩ : Fin slotCount) (by change 16 = 4 * k.val + 0; omega)]
      exact absent16
    · rw [hI k 0 (⟨20, by decide⟩ : Fin slotCount) (by change 20 = 4 * k.val + 0; omega)]
      exact absent20
    · rw [hI k 0 (⟨24, by decide⟩ : Fin slotCount) (by change 24 = 4 * k.val + 0; omega)]
      exact absent24
    · rw [hI k 0 (⟨28, by decide⟩ : Fin slotCount) (by change 28 = 4 * k.val + 0; omega)]
      exact absent28
    · rw [hI k 0 (⟨32, by decide⟩ : Fin slotCount) (by change 32 = 4 * k.val + 0; omega)]
      exact absent32
    · rw [hI k 0 (⟨36, by decide⟩ : Fin slotCount) (by change 36 = 4 * k.val + 0; omega)]
      exact absent36
    · rw [hI k 0 (⟨40, by decide⟩ : Fin slotCount) (by change 40 = 4 * k.val + 0; omega)]
      exact absent40
    · rw [hI k 0 (⟨44, by decide⟩ : Fin slotCount) (by change 44 = 4 * k.val + 0; omega)]
      exact absent44
    · rw [hI k 0 (⟨48, by decide⟩ : Fin slotCount) (by change 48 = 4 * k.val + 0; omega)]
      exact absent48
    · rw [hI k 0 (⟨52, by decide⟩ : Fin slotCount) (by change 52 = 4 * k.val + 0; omega)]
      exact absent52
    · rw [hI k 0 (⟨56, by decide⟩ : Fin slotCount) (by change 56 = 4 * k.val + 0; omega)]
      exact absent56
    · rw [hI k 0 (⟨60, by decide⟩ : Fin slotCount) (by change 60 = 4 * k.val + 0; omega)]
      exact absent60
    · rw [hI k 0 (⟨64, by decide⟩ : Fin slotCount) (by change 64 = 4 * k.val + 0; omega)]
      exact absent64
    · rw [hI k 0 (⟨68, by decide⟩ : Fin slotCount) (by change 68 = 4 * k.val + 0; omega)]
      exact absent68
    · rw [hI k 0 (⟨72, by decide⟩ : Fin slotCount) (by change 72 = 4 * k.val + 0; omega)]
      exact absent72
    · rw [hI k 0 (⟨76, by decide⟩ : Fin slotCount) (by change 76 = 4 * k.val + 0; omega)]
      exact absent76
    · rw [hI k 0 (⟨80, by decide⟩ : Fin slotCount) (by change 80 = 4 * k.val + 0; omega)]
      exact absent80
    · rw [hI k 0 (⟨84, by decide⟩ : Fin slotCount) (by change 84 = 4 * k.val + 0; omega)]
      exact absent84
    · rw [hI k 0 (⟨88, by decide⟩ : Fin slotCount) (by change 88 = 4 * k.val + 0; omega)]
      exact absent88
    · rw [hI k 0 (⟨92, by decide⟩ : Fin slotCount) (by change 92 = 4 * k.val + 0; omega)]
      exact absent92
    · rw [hI k 0 (⟨96, by decide⟩ : Fin slotCount) (by change 96 = 4 * k.val + 0; omega)]
      exact absent96
    · rw [hI k 0 (⟨100, by decide⟩ : Fin slotCount) (by change 100 = 4 * k.val + 0; omega)]
      exact absent100
    · rw [hI k 0 (⟨104, by decide⟩ : Fin slotCount) (by change 104 = 4 * k.val + 0; omega)]
      exact absent104
    · rw [hI k 0 (⟨108, by decide⟩ : Fin slotCount) (by change 108 = 4 * k.val + 0; omega)]
      exact absent108
    · rw [hI k 0 (⟨112, by decide⟩ : Fin slotCount) (by change 112 = 4 * k.val + 0; omega)]
      exact absent112
    · rw [hI k 0 (⟨116, by decide⟩ : Fin slotCount) (by change 116 = 4 * k.val + 0; omega)]
      exact absent116
  · rw [hZ 0 (⟨120, by decide⟩ : Fin slotCount) (by change 120 = bN P72 N p * 4 + 0; omega)]
    exact absent120
  · intro k
    have hkv : k.val < 30 := by have := k.isLt; omega
    interval_cases hk : k.val
    · rw [hI k 1 (⟨1, by decide⟩ : Fin slotCount) (by change 1 = 4 * k.val + 1; omega)]
      exact ⟨row000, row001⟩
    · rw [hI k 1 (⟨5, by decide⟩ : Fin slotCount) (by change 5 = 4 * k.val + 1; omega)]
      exact ⟨row005, row006⟩
    · rw [hI k 1 (⟨9, by decide⟩ : Fin slotCount) (by change 9 = 4 * k.val + 1; omega)]
      exact ⟨row010, row011⟩
    · rw [hI k 1 (⟨13, by decide⟩ : Fin slotCount) (by change 13 = 4 * k.val + 1; omega)]
      exact ⟨row015, row016⟩
    · rw [hI k 1 (⟨17, by decide⟩ : Fin slotCount) (by change 17 = 4 * k.val + 1; omega)]
      exact ⟨row020, row021⟩
    · rw [hI k 1 (⟨21, by decide⟩ : Fin slotCount) (by change 21 = 4 * k.val + 1; omega)]
      exact ⟨row025, row026⟩
    · rw [hI k 1 (⟨25, by decide⟩ : Fin slotCount) (by change 25 = 4 * k.val + 1; omega)]
      exact ⟨row030, row031⟩
    · rw [hI k 1 (⟨29, by decide⟩ : Fin slotCount) (by change 29 = 4 * k.val + 1; omega)]
      exact ⟨row035, row036⟩
    · rw [hI k 1 (⟨33, by decide⟩ : Fin slotCount) (by change 33 = 4 * k.val + 1; omega)]
      exact ⟨row040, row041⟩
    · rw [hI k 1 (⟨37, by decide⟩ : Fin slotCount) (by change 37 = 4 * k.val + 1; omega)]
      exact ⟨row045, row046⟩
    · rw [hI k 1 (⟨41, by decide⟩ : Fin slotCount) (by change 41 = 4 * k.val + 1; omega)]
      exact ⟨row050, row051⟩
    · rw [hI k 1 (⟨45, by decide⟩ : Fin slotCount) (by change 45 = 4 * k.val + 1; omega)]
      exact ⟨row055, row056⟩
    · rw [hI k 1 (⟨49, by decide⟩ : Fin slotCount) (by change 49 = 4 * k.val + 1; omega)]
      exact ⟨row060, row061⟩
    · rw [hI k 1 (⟨53, by decide⟩ : Fin slotCount) (by change 53 = 4 * k.val + 1; omega)]
      exact ⟨row065, row066⟩
    · rw [hI k 1 (⟨57, by decide⟩ : Fin slotCount) (by change 57 = 4 * k.val + 1; omega)]
      exact ⟨row070, row071⟩
    · rw [hI k 1 (⟨61, by decide⟩ : Fin slotCount) (by change 61 = 4 * k.val + 1; omega)]
      exact ⟨row075, row076⟩
    · rw [hI k 1 (⟨65, by decide⟩ : Fin slotCount) (by change 65 = 4 * k.val + 1; omega)]
      exact ⟨row080, row081⟩
    · rw [hI k 1 (⟨69, by decide⟩ : Fin slotCount) (by change 69 = 4 * k.val + 1; omega)]
      exact ⟨row085, row086⟩
    · rw [hI k 1 (⟨73, by decide⟩ : Fin slotCount) (by change 73 = 4 * k.val + 1; omega)]
      exact ⟨row090, row091⟩
    · rw [hI k 1 (⟨77, by decide⟩ : Fin slotCount) (by change 77 = 4 * k.val + 1; omega)]
      exact ⟨row095, row096⟩
    · rw [hI k 1 (⟨81, by decide⟩ : Fin slotCount) (by change 81 = 4 * k.val + 1; omega)]
      exact ⟨row100, row101⟩
    · rw [hI k 1 (⟨85, by decide⟩ : Fin slotCount) (by change 85 = 4 * k.val + 1; omega)]
      exact ⟨row105, row106⟩
    · rw [hI k 1 (⟨89, by decide⟩ : Fin slotCount) (by change 89 = 4 * k.val + 1; omega)]
      exact ⟨row110, row111⟩
    · rw [hI k 1 (⟨93, by decide⟩ : Fin slotCount) (by change 93 = 4 * k.val + 1; omega)]
      exact ⟨row115, row116⟩
    · rw [hI k 1 (⟨97, by decide⟩ : Fin slotCount) (by change 97 = 4 * k.val + 1; omega)]
      exact ⟨row120, row121⟩
    · rw [hI k 1 (⟨101, by decide⟩ : Fin slotCount) (by change 101 = 4 * k.val + 1; omega)]
      exact ⟨row125, row126⟩
    · rw [hI k 1 (⟨105, by decide⟩ : Fin slotCount) (by change 105 = 4 * k.val + 1; omega)]
      exact ⟨row130, row131⟩
    · rw [hI k 1 (⟨109, by decide⟩ : Fin slotCount) (by change 109 = 4 * k.val + 1; omega)]
      exact ⟨row135, row136⟩
    · rw [hI k 1 (⟨113, by decide⟩ : Fin slotCount) (by change 113 = 4 * k.val + 1; omega)]
      exact ⟨row140, row141⟩
    · rw [hI k 1 (⟨117, by decide⟩ : Fin slotCount) (by change 117 = 4 * k.val + 1; omega)]
      exact ⟨row145, row146⟩
  · intro k
    have hkv : k.val < 30 := by have := k.isLt; omega
    interval_cases hk : k.val
    · rw [hI k 2 (⟨2, by decide⟩ : Fin slotCount) (by change 2 = 4 * k.val + 2; omega), hI k 3 (⟨3, by decide⟩ : Fin slotCount) (by change 3 = 4 * k.val + 3; omega)]
      exact ⟨row002, row003, row004⟩
    · rw [hI k 2 (⟨6, by decide⟩ : Fin slotCount) (by change 6 = 4 * k.val + 2; omega), hI k 3 (⟨7, by decide⟩ : Fin slotCount) (by change 7 = 4 * k.val + 3; omega)]
      exact ⟨row007, row008, row009⟩
    · rw [hI k 2 (⟨10, by decide⟩ : Fin slotCount) (by change 10 = 4 * k.val + 2; omega), hI k 3 (⟨11, by decide⟩ : Fin slotCount) (by change 11 = 4 * k.val + 3; omega)]
      exact ⟨row012, row013, row014⟩
    · rw [hI k 2 (⟨14, by decide⟩ : Fin slotCount) (by change 14 = 4 * k.val + 2; omega), hI k 3 (⟨15, by decide⟩ : Fin slotCount) (by change 15 = 4 * k.val + 3; omega)]
      exact ⟨row017, row018, row019⟩
    · rw [hI k 2 (⟨18, by decide⟩ : Fin slotCount) (by change 18 = 4 * k.val + 2; omega), hI k 3 (⟨19, by decide⟩ : Fin slotCount) (by change 19 = 4 * k.val + 3; omega)]
      exact ⟨row022, row023, row024⟩
    · rw [hI k 2 (⟨22, by decide⟩ : Fin slotCount) (by change 22 = 4 * k.val + 2; omega), hI k 3 (⟨23, by decide⟩ : Fin slotCount) (by change 23 = 4 * k.val + 3; omega)]
      exact ⟨row027, row028, row029⟩
    · rw [hI k 2 (⟨26, by decide⟩ : Fin slotCount) (by change 26 = 4 * k.val + 2; omega), hI k 3 (⟨27, by decide⟩ : Fin slotCount) (by change 27 = 4 * k.val + 3; omega)]
      exact ⟨row032, row033, row034⟩
    · rw [hI k 2 (⟨30, by decide⟩ : Fin slotCount) (by change 30 = 4 * k.val + 2; omega), hI k 3 (⟨31, by decide⟩ : Fin slotCount) (by change 31 = 4 * k.val + 3; omega)]
      exact ⟨row037, row038, row039⟩
    · rw [hI k 2 (⟨34, by decide⟩ : Fin slotCount) (by change 34 = 4 * k.val + 2; omega), hI k 3 (⟨35, by decide⟩ : Fin slotCount) (by change 35 = 4 * k.val + 3; omega)]
      exact ⟨row042, row043, row044⟩
    · rw [hI k 2 (⟨38, by decide⟩ : Fin slotCount) (by change 38 = 4 * k.val + 2; omega), hI k 3 (⟨39, by decide⟩ : Fin slotCount) (by change 39 = 4 * k.val + 3; omega)]
      exact ⟨row047, row048, row049⟩
    · rw [hI k 2 (⟨42, by decide⟩ : Fin slotCount) (by change 42 = 4 * k.val + 2; omega), hI k 3 (⟨43, by decide⟩ : Fin slotCount) (by change 43 = 4 * k.val + 3; omega)]
      exact ⟨row052, row053, row054⟩
    · rw [hI k 2 (⟨46, by decide⟩ : Fin slotCount) (by change 46 = 4 * k.val + 2; omega), hI k 3 (⟨47, by decide⟩ : Fin slotCount) (by change 47 = 4 * k.val + 3; omega)]
      exact ⟨row057, row058, row059⟩
    · rw [hI k 2 (⟨50, by decide⟩ : Fin slotCount) (by change 50 = 4 * k.val + 2; omega), hI k 3 (⟨51, by decide⟩ : Fin slotCount) (by change 51 = 4 * k.val + 3; omega)]
      exact ⟨row062, row063, row064⟩
    · rw [hI k 2 (⟨54, by decide⟩ : Fin slotCount) (by change 54 = 4 * k.val + 2; omega), hI k 3 (⟨55, by decide⟩ : Fin slotCount) (by change 55 = 4 * k.val + 3; omega)]
      exact ⟨row067, row068, row069⟩
    · rw [hI k 2 (⟨58, by decide⟩ : Fin slotCount) (by change 58 = 4 * k.val + 2; omega), hI k 3 (⟨59, by decide⟩ : Fin slotCount) (by change 59 = 4 * k.val + 3; omega)]
      exact ⟨row072, row073, row074⟩
    · rw [hI k 2 (⟨62, by decide⟩ : Fin slotCount) (by change 62 = 4 * k.val + 2; omega), hI k 3 (⟨63, by decide⟩ : Fin slotCount) (by change 63 = 4 * k.val + 3; omega)]
      exact ⟨row077, row078, row079⟩
    · rw [hI k 2 (⟨66, by decide⟩ : Fin slotCount) (by change 66 = 4 * k.val + 2; omega), hI k 3 (⟨67, by decide⟩ : Fin slotCount) (by change 67 = 4 * k.val + 3; omega)]
      exact ⟨row082, row083, row084⟩
    · rw [hI k 2 (⟨70, by decide⟩ : Fin slotCount) (by change 70 = 4 * k.val + 2; omega), hI k 3 (⟨71, by decide⟩ : Fin slotCount) (by change 71 = 4 * k.val + 3; omega)]
      exact ⟨row087, row088, row089⟩
    · rw [hI k 2 (⟨74, by decide⟩ : Fin slotCount) (by change 74 = 4 * k.val + 2; omega), hI k 3 (⟨75, by decide⟩ : Fin slotCount) (by change 75 = 4 * k.val + 3; omega)]
      exact ⟨row092, row093, row094⟩
    · rw [hI k 2 (⟨78, by decide⟩ : Fin slotCount) (by change 78 = 4 * k.val + 2; omega), hI k 3 (⟨79, by decide⟩ : Fin slotCount) (by change 79 = 4 * k.val + 3; omega)]
      exact ⟨row097, row098, row099⟩
    · rw [hI k 2 (⟨82, by decide⟩ : Fin slotCount) (by change 82 = 4 * k.val + 2; omega), hI k 3 (⟨83, by decide⟩ : Fin slotCount) (by change 83 = 4 * k.val + 3; omega)]
      exact ⟨row102, row103, row104⟩
    · rw [hI k 2 (⟨86, by decide⟩ : Fin slotCount) (by change 86 = 4 * k.val + 2; omega), hI k 3 (⟨87, by decide⟩ : Fin slotCount) (by change 87 = 4 * k.val + 3; omega)]
      exact ⟨row107, row108, row109⟩
    · rw [hI k 2 (⟨90, by decide⟩ : Fin slotCount) (by change 90 = 4 * k.val + 2; omega), hI k 3 (⟨91, by decide⟩ : Fin slotCount) (by change 91 = 4 * k.val + 3; omega)]
      exact ⟨row112, row113, row114⟩
    · rw [hI k 2 (⟨94, by decide⟩ : Fin slotCount) (by change 94 = 4 * k.val + 2; omega), hI k 3 (⟨95, by decide⟩ : Fin slotCount) (by change 95 = 4 * k.val + 3; omega)]
      exact ⟨row117, row118, row119⟩
    · rw [hI k 2 (⟨98, by decide⟩ : Fin slotCount) (by change 98 = 4 * k.val + 2; omega), hI k 3 (⟨99, by decide⟩ : Fin slotCount) (by change 99 = 4 * k.val + 3; omega)]
      exact ⟨row122, row123, row124⟩
    · rw [hI k 2 (⟨102, by decide⟩ : Fin slotCount) (by change 102 = 4 * k.val + 2; omega), hI k 3 (⟨103, by decide⟩ : Fin slotCount) (by change 103 = 4 * k.val + 3; omega)]
      exact ⟨row127, row128, row129⟩
    · rw [hI k 2 (⟨106, by decide⟩ : Fin slotCount) (by change 106 = 4 * k.val + 2; omega), hI k 3 (⟨107, by decide⟩ : Fin slotCount) (by change 107 = 4 * k.val + 3; omega)]
      exact ⟨row132, row133, row134⟩
    · rw [hI k 2 (⟨110, by decide⟩ : Fin slotCount) (by change 110 = 4 * k.val + 2; omega), hI k 3 (⟨111, by decide⟩ : Fin slotCount) (by change 111 = 4 * k.val + 3; omega)]
      exact ⟨row137, row138, row139⟩
    · rw [hI k 2 (⟨114, by decide⟩ : Fin slotCount) (by change 114 = 4 * k.val + 2; omega), hI k 3 (⟨115, by decide⟩ : Fin slotCount) (by change 115 = 4 * k.val + 3; omega)]
      exact ⟨row142, row143, row144⟩
    · rw [hI k 2 (⟨118, by decide⟩ : Fin slotCount) (by change 118 = 4 * k.val + 2; omega), hI k 3 (⟨119, by decide⟩ : Fin slotCount) (by change 119 = 4 * k.val + 3; omega)]
      exact ⟨row147, row148, row149⟩
  · rw [hZ 0 (⟨120, by decide⟩ : Fin slotCount) (by change 120 = bN P72 N p * 4 + 0; omega), hZ 1 (⟨121, by decide⟩ : Fin slotCount) (by change 121 = bN P72 N p * 4 + 1; omega)]
    exact ⟨row150, row151, row152⟩
  · rw [hI ⟨0, hbpos⟩ 0 (⟨0, by decide⟩ : Fin slotCount) (by change 0 = 4 * 0 + 0; omega), hI ⟨0, hbpos⟩ 1 (⟨1, by decide⟩ : Fin slotCount) (by change 1 = 4 * 0 + 1; omega), hI ⟨0, hbpos⟩ 2 (⟨2, by decide⟩ : Fin slotCount) (by change 2 = 4 * 0 + 2; omega), hI ⟨0, hbpos⟩ 3 (⟨3, by decide⟩ : Fin slotCount) (by change 3 = 4 * 0 + 3; omega), hZ 0 (⟨120, by decide⟩ : Fin slotCount) (by change 120 = bN P72 N p * 4 + 0; omega), hZ 1 (⟨121, by decide⟩ : Fin slotCount) (by change 121 = bN P72 N p * 4 + 1; omega)]
    refine Or.inr ⟨?_, row154⟩
    intro j; rw [row153, coeff_zero]
  · rw [hI ⟨bN P72 N p - 1, by omega⟩ 0 (⟨116, by decide⟩ : Fin slotCount) (by change 116 = 4 * (bN P72 N p - 1) + 0; omega), hI ⟨bN P72 N p - 1, by omega⟩ 1 (⟨117, by decide⟩ : Fin slotCount) (by change 117 = 4 * (bN P72 N p - 1) + 1; omega), hI ⟨bN P72 N p - 1, by omega⟩ 2 (⟨118, by decide⟩ : Fin slotCount) (by change 118 = 4 * (bN P72 N p - 1) + 2; omega), hI ⟨bN P72 N p - 1, by omega⟩ 3 (⟨119, by decide⟩ : Fin slotCount) (by change 119 = 4 * (bN P72 N p - 1) + 3; omega)]
    refine Or.inr ⟨?_, row156⟩
    intro j; rw [row155, coeff_zero]

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.DomainSound030

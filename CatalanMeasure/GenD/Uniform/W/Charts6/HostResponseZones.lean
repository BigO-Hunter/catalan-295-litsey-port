module
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostResponseGeometry
public import CatalanMeasure.GenD.Uniform.W.Charts6.Check.Cert
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Prof
open CatalanMeasure.GenD.Uniform.W.Charts4
open Check (Aff Cert holds holds_sound)
noncomputable section

inductive PhysicalPoint | zero | infinity | plus | minus
  deriving DecidableEq

structure JetLayout (pk : Packet) where
  point : Fin pk.charts.length → PhysicalPoint
  offset : Fin pk.charts.length → Aff
  width : Fin pk.charts.length → Aff

def halfPrime (p : Nat) : Int := ((p : Int) - 1) / 2

def affAt (N p : Nat) (a : Aff) : Int := a.eval N (halfPrime p)

def JetLayout.start {pk : Packet} (l : JetLayout pk) (N p : Nat)
    (g : Fin pk.charts.length) : Nat := (affAt N p (l.offset g)).toNat

def JetLayout.count {pk : Packet} (l : JetLayout pk) (N p : Nat)
    (g : Fin pk.charts.length) : Nat := (affAt N p (l.width g)).toNat

def JetLayout.jet {pk : Packet} (l : JetLayout pk) (N p : Nat) [Fact p.Prime]
    (g : Fin pk.charts.length) (k : Nat) :
    (Fin p → Fin pk.d → ZMod p) →ₗ[ZMod p] (Fin pk.d → ZMod p) :=
  let j := l.start N p g + k
  match l.point g with
  | .zero => jet0 j
  | .infinity => jetInf j
  | .plus => Charts3.taylorJet 1 j
  | .minus => Charts3.taylorJet (-1) j

def JetLayout.active {pk : Packet} (l : JetLayout pk) (win : List Aff) (cs : Cert)
    (g : Fin pk.charts.length) (lo hi : Aff) : Bool :=
  let off := l.offset g
  let last := off.add (l.width g)
  let P : Aff := ⟨0, 2, 1⟩
  match l.point g with
  | .zero => holds win cs (lo.sub off) && holds win cs (last.sub hi)
  | .infinity => holds win cs (lo.sub (P.sub last)) && holds win cs ((P.sub off).sub hi)
  | _ => false

theorem JetLayout.active_sound {pk : Packet} (l : JetLayout pk) {N p : Nat} [Fact p.Prime]
    {win : List Aff} {cs : Cert} (g : Fin pk.charts.length) {lo hi : Aff}
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f) (hodd : p % 2 = 1)
    (hoff : 0 ≤ affAt N p (l.offset g)) (hw : 0 ≤ affAt N p (l.width g))
    (ha : l.active win cs g lo hi = true) (e : Fin p)
    (he1 : affAt N p lo ≤ (e.val : Int)) (he2 : (e.val : Int) < affAt N p hi) :
    ∃ k, k < l.count N p g ∧ l.jet N p g k = LinearMap.proj e := by
  have ho : (l.start N p g : Int) = affAt N p (l.offset g) := Int.toNat_of_nonneg hoff
  have hd : (l.count N p g : Int) = affAt N p (l.width g) := Int.toNat_of_nonneg hw
  have hP : affAt N p (⟨0, 2, 1⟩ : Aff) = (p : Int) := by
    simp [affAt, halfPrime, Aff.eval] <;> omega
  have get (f : Aff) (h : holds win cs f = true) : 0 ≤ affAt N p f :=
    holds_sound win cs f N (halfPrime p) hwin h
  have ep := e.isLt
  unfold JetLayout.active at ha
  cases hpt : l.point g with
  | plus => simp [hpt] at ha
  | minus => simp [hpt] at ha
  | zero =>
    simp only [hpt, Bool.and_eq_true] at ha
    have h1 := get _ ha.1
    have h2 := get _ ha.2
    simp only [affAt, Check.Aff.eval_sub, Check.Aff.eval_add] at h1 h2
    change 0 ≤ affAt N p lo - affAt N p (l.offset g) at h1
    change 0 ≤ affAt N p (l.offset g) + affAt N p (l.width g) - affAt N p hi at h2
    let k := e.val - l.start N p g
    have hk : l.start N p g + k = e.val := by dsimp [k]; omega
    refine ⟨k, by dsimp [k]; omega, ?_⟩
    simp only [JetLayout.jet, hpt, hk]
    simp [jet0, ep]
  | infinity =>
    simp only [hpt, Bool.and_eq_true] at ha
    have h1 := get _ ha.1
    have h2 := get _ ha.2
    simp only [affAt, Check.Aff.eval_sub, Check.Aff.eval_add] at h1 h2
    change 0 ≤ affAt N p lo -
      (affAt N p (⟨0, 2, 1⟩ : Aff) - (affAt N p (l.offset g) + affAt N p (l.width g))) at h1
    change 0 ≤ affAt N p (⟨0, 2, 1⟩ : Aff) - affAt N p (l.offset g) - affAt N p hi at h2
    rw [hP] at h1 h2
    let j := p - 1 - e.val
    let k := j - l.start N p g
    have hj : j < p := by dsimp [j]; omega
    have hk : l.start N p g + k = j := by dsimp [k, j]; omega
    have hre : p - 1 - j = e.val := by dsimp [j]; omega
    refine ⟨k, by dsimp [k, j]; omega, ?_⟩
    simp only [JetLayout.jet, hpt, hk]
    simp [jetInf, hj, hre]

structure ResponseZone (pk : Packet) where
  lo : Aff
  hi : Aff
  span : RowSpanData pk

def ResponseZone.check {pk : Packet} (z : ResponseZone pk) (l : JetLayout pk)
    (win : List Aff) (cs : Cert) (target : List Int) : Bool :=
  z.span.check target && (List.finRange z.span.terms.length).all (fun i =>
    l.active win cs (z.span.terms.get i).group z.lo z.hi)

def responseChain {pk : Packet} (win : List Aff) (cs : Cert) (hi : Aff) :
    Aff → List (ResponseZone pk) → Bool
  | lo, [] => holds win cs (lo.sub hi)
  | lo, z::zs => holds win cs (lo.sub z.lo) && responseChain win cs hi z.hi zs

theorem response_chain_select {pk : Packet} {win : List Aff} {cs : Cert} {N p : Nat}
    {hi : Aff} (hwin : ∀ f ∈ win, 0 ≤ affAt N p f) :
    ∀ (zs : List (ResponseZone pk)) (lo : Aff), responseChain win cs hi lo zs = true →
      ∀ e : Int, affAt N p lo ≤ e → e < affAt N p hi →
        ∃ z ∈ zs, affAt N p z.lo ≤ e ∧ e < affAt N p z.hi := by
  have get (f g : Aff) (h : holds win cs (f.sub g) = true) : affAt N p g ≤ affAt N p f := by
    have hk := holds_sound win cs _ N (halfPrime p) hwin h
    rw [Check.Aff.eval_sub] at hk
    exact sub_nonneg.mp hk
  intro zs
  induction zs with
  | nil =>
    intro lo h e hlo hhi
    have := get lo hi h
    omega
  | cons z zs ih =>
    intro lo hc e hlo hhi
    simp only [responseChain, Bool.and_eq_true] at hc
    by_cases hz : e < affAt N p z.hi
    · exact ⟨z, List.mem_cons_self, (get lo z.lo hc.1).trans hlo, hz⟩
    · obtain ⟨zz, hm, hl, hh⟩ := ih z.hi hc.2 e (le_of_not_gt hz) hhi
      exact ⟨zz, List.mem_cons_of_mem _ hm, hl, hh⟩

theorem response_zone_active {pk : Packet} {z : ResponseZone pk} {l : JetLayout pk}
    {win : List Aff} {cs : Cert} {N p : Nat} [Fact p.Prime] {target : List Int}
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f) (hodd : p % 2 = 1)
    (hoff : ∀ g, 0 ≤ affAt N p (l.offset g)) (hw : ∀ g, 0 ≤ affAt N p (l.width g))
    (hc : z.check l win cs target = true) (e : Fin p)
    (hlo : affAt N p z.lo ≤ (e.val : Int)) (hhi : (e.val : Int) < affAt N p z.hi) :
    z.span.check target = true ∧
    ∀ x : Fin p → Fin pk.d → ZMod p,
      (∀ g (k : Fin (l.count N p g)), chartMap pk (pk.chart g) p pk.n (l.jet N p g k.val x) = 0) →
      ∀ i : Fin z.span.terms.length,
        chartMap pk (pk.chart (z.span.terms.get i).group) p pk.n (x e) = 0 := by
  simp only [ResponseZone.check, Bool.and_eq_true, List.all_eq_true] at hc
  refine ⟨hc.1, ?_⟩
  intro x hx i
  let g := (z.span.terms.get i).group
  obtain ⟨k, hk, hjet⟩ := l.active_sound g hwin hodd (hoff g) (hw g) (hc.2 i (by simp)) e hlo hhi
  have h := hx g ⟨k, hk⟩
  rw [hjet] at h
  exact h

end
end CatalanMeasure.GenD.Uniform.W.Charts6

module

public import CatalanMeasure.GenD.Signed.Gate
public import CatalanMeasure.GenD.Uniform.ContentBank.Gate

@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed
open CatalanMeasure.GenD D58 Uniform Uniform.Bank540.Ledger Uniform.Bank535
noncomputable section

/-- `w = 3/5`, `B = 417`, `eta = 38.3257`. -/
theorem pay417_w35 :
    PayW (3 / 5) D58.d0 Bank540.rho (383257 / 10000) (417 / Bank540.rho) D58.delta 417 := by
  have hr : Bank540.rho = 301.54258 := by
    norm_num [Bank540.rho, K590.rho, K590.secondCost, D58.wcap, D58.t]
  have hd : D58.delta = 29 / 100000000 := by norm_num [D58.delta, D58.t, D58.deltaRef]
  have h0 : D58.d0 = 53 := rfl
  rw [hr, hd, h0]
  exact Generic.payB dc58 _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Gate inequality for the improved budget `tD = tDelta + A`, with `A >= 8.2847` the Theorem A
gain per `N^2` (`A = 58^2 (target0 - target)`), and `g >= 22.05325` the ledger gain. -/
theorem gain_ok417 (g A tD : ℝ) (hT : tD = Bank540.tDelta + A) (h : 2205325 / 100000 ≤ g)
    (hA : 82847 / 10000 ≤ A) : (383257 / 10000 : ℝ) < tD - gDg g := by
  have := eta_lt_of_gain (383257 / 10000 - A) g (by norm_num; linarith)
  exact Generic.gain_ok _ _ _ _ _ hT this

/-- `w = 3/5`, `B = 410`, `rho' = K590.rhoEnd 87.9663`, `eta = 38.33924`. -/
theorem pay410_w35 :
    PayW (3 / 5) D58.d0 (K590.rhoEnd (879663 / 10000)) (3833924 / 100000)
      (410 / K590.rhoEnd (879663 / 10000)) D58.delta 410 := by
  have hr : K590.rhoEnd (879663 / 10000) = 296586094 / 1000000 := by
    rw [K590.rhoEnd_val]; norm_num
  have hd : D58.delta = 29 / 100000000 := by norm_num [D58.delta, D58.t, D58.deltaRef]
  have h0 : D58.d0 = 53 := rfl
  rw [hr, hd, h0]
  exact Generic.payB dc58 _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Gate inequality for `B = 410`: with the Theorem A gain `A >= 8.29824` per `N^2`
(`A = 58^2 (target0 - K590.target)`) and the ledger gain `g >= 22.05325`. -/
theorem gain_ok410 (g A tD : ℝ) (hT : tD = Bank540.tDelta + A) (h : 2205325 / 100000 ≤ g)
    (hA : 829824 / 100000 ≤ A) : (3833924 / 100000 : ℝ) < tD - gDg g := by
  have := eta_lt_of_gain (3833924 / 100000 - A) g (by norm_num; linarith)
  exact Generic.gain_ok _ _ _ _ _ hT this

end
end CatalanMeasure.GenD.Signed
#print axioms CatalanMeasure.GenD.Signed.pay417_w35
#print axioms CatalanMeasure.GenD.Signed.gain_ok417
#print axioms CatalanMeasure.GenD.Signed.pay410_w35
#print axioms CatalanMeasure.GenD.Signed.gain_ok410

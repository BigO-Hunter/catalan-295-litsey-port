import CatalanMeasure.GenD.Signed.Data.Consts.EvalRefX12

open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef

-- shape of the plan for X12 (trial refs Rm1, Rm2)
#eval (refPlan Rm1 Rm2).length
#eval (planLits Rm1 Rm2).length
#eval ((planLits Rm1 Rm2).map (fun f => f.ts.length))
#eval ((LF.sumL (planLits Rm1 Rm2)).ts.length)
#eval ((mergeT (LF.sumL (planLits Rm1 Rm2)).ts).length)
-- the atomic enclosure the kernel must reproduce
#eval (LF.sumL (planLits Rm1 Rm2)).enc 7
#eval xU12

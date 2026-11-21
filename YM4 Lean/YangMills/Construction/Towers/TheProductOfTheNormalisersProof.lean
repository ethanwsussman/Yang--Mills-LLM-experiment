import YangMills.Construction.Towers.LogarithmOfTheTotalNormaliserAlongAStep
import YangMills.Construction.Towers.TheProductOfTheNormalisers
import YangMills.Construction.Towers.TotalNormaliserIsAProduct
import YangMills.Construction.Towers.TotalNormaliserLogarithmIsGaugeInvariant
import YangMills.Construction.Towers.TotalNormaliserLogarithmIsIsometryInvariant
import YangMills.Construction.Towers.TotalNormaliserLogarithmIsRealAnalytic
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
theorem normaliserProductTheorem_holds (hProd : TotalNormaliserFactorises)
    (hLog : LogTotalNormaliserStep.Statement)
    (hAnalytic : LogTotalNormaliserAnalytic)
    (hGauge : LogTotalNormaliserGaugeInvariant)
    (hSymm : LogTotalNormaliserSymmetryInvariant) :
    NormaliserProductTheorem := by
  intro L n k h hn
  have hP := hProd L n (k + 1) h hn (Nat.succ_le_succ (Nat.zero_le k))
  exact
    { wellDefined := hP.mono fun _ hW => hW.1
      prod_eq := hP.mono fun _ hW => hW.2
      log_eq := hLog L n k h hn _
      analytic := hAnalytic L n k h hn
      gauge_invariant := hGauge L n k h hn
      symmetry_invariant := hSymm L n k h hn }
end YangMills.Construction.Tower
end

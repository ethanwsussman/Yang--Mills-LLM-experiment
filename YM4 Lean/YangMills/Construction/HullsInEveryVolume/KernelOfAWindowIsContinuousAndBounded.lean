import YangMills.Construction.InfiniteLattice.WilsonWindows
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace HullsInEveryVolume
def windowKernelContinuousBounded : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (β : ℝ), 0 < β → ∀ W : InfiniteLattice.LinkWindow a,
    Continuous (fun x : W.Assignments × InfiniteLattice.GaugeField a => W.densityKernel ha β x.1 x.2) ∧
      (∀ (V : W.Assignments) (U : InfiniteLattice.GaugeField a),
        Real.exp (-(2 * β * W.faceCount)) ≤ W.densityKernel ha β V U ∧
          W.densityKernel ha β V U ≤ Real.exp (2 * β * W.faceCount)) ∧
      ∀ U : InfiniteLattice.GaugeField a, ∫ V, W.densityKernel ha β V U ∂W.haarProd = 1
end HullsInEveryVolume
end YangMills.Construction
end

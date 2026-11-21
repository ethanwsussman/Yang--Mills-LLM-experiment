import YangMills.Construction.PositiveDefinite.KernelOnSet
import YangMills.Construction.RotationInvariance.GramKernelOnLabelledTubePoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open ForwardTube PositiveDefinite
namespace GramKernelImagPosSemidef
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (_ : PlaneDataWithAperture m S),
    KernelPosSemidefOnSet (gramKernel S) ∧
    ∀ s : ℝ,
      KernelPosSemidefOnSet (gramKernelImag S s) ∧
      (∀ (p r : LabelledTuple) (h : 2 ≤ p.length + r.length),
        gramKernelImag S s p r =
          planeKernel S (q := p.length + r.length - 1)
            (fun k => gramLabelOrder p.labels r.labels (Fin.cast (by omega) k))
            (fun k => imagBoost s (gramKernelArgs p.points r.points k))) ∧
      (∀ p r : LabelledTuple, p.length = 0 → r.length = 0 →
        gramKernelImag S s p r = 1) ∧
      (∀ p r : LabelledTuple, p.length + r.length = 1 →
        gramKernelImag S s p r = 0)
end GramKernelImagPosSemidef
end YangMills.Construction.EuclideanFunctionals
end

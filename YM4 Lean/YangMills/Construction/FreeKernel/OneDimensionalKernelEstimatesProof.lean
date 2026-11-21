import YangMills.Construction.Constants.HeatKernelNumbersFinite
import YangMills.Construction.FreeKernel.BoundOfTheDerivativesOfTheGaussianKernel
import YangMills.Construction.FreeKernel.DifferencesOfTheHeatKernelAgainstTheGaussian
import YangMills.Construction.FreeKernel.DiscreteHeatKernelSeries
import YangMills.Construction.FreeKernel.LongTimeBoundOfTheDifferencesOfTheHeatKernel
import YangMills.Construction.FreeKernel.OneDimensionalKernelEstimates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
theorem oneDimensionalEstimates_holds
    (hSeries : YangMills.Construction.FreeKernel.DiscreteHeatKernelSeries)
    (hLong : HeatKernelDiffLongTimeBound)
    (hGaussian : GaussianDerivativeBound)
    (hComparison : HeatKernelGaussianDifferenceBound)
    (hNumbers : YangMills.Construction.Constants.HeatKernel.finite_and_pos) :
    YangMills.Construction.LatticeKernelBounds.OneDimensionalEstimates := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hSeries
  obtain ⟨-, -, -, -, -, -, -, -, -, hB, -⟩ := hNumbers
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, fun n => ⟨(hB n).1, fun α =>
    ⟨hLong n α, hGaussian n α, hComparison n α⟩⟩⟩
end YangMills.Construction.FreeKernel
end

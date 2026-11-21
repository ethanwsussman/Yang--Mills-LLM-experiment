import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ThreeKernelsDescend
open LocalKernels LocalKernels.Periodisation
open PeriodicOperators (swapKernel applyKernel)
def DescentStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    ∀ U ∈ smallIterateFields L n k,
      (∃ M, (∀ f : (CellClass.quotSpace L n (edgesAtZero k)).complexSubmodule,
          CellClass.quotCoeffsOn L n (CellClass.edgeClass k k le_rfl)
            (iterCovariantDeriv L n k U k f.1) =
          applyKernel M (CellClass.quotCoeffsOn L n (edgesAtZero k) f.1)) ∧
        KernelDescends L n (edgesAtZero k).colourPairs
          (CellClass.edgeClass k k le_rfl).colourPairs
          (fun ι' ι => FullSpace.iterCovariantKernel L k
            (liftGaugeField L n k 0 U) ι'.2 ι.2) M ∧
        KernelDescends L n (CellClass.edgeClass k k le_rfl).colourPairs
          (edgesAtZero k).colourPairs
          (fun ι' ι => FullSpace.iterCovariantKernel L k
            (liftGaugeField L n k 0 U) ι.2 ι'.2) (swapKernel M)) ∧
      (∃ M, (∀ f : (CellClass.quotSpace L n (verticesAtZero k)).complexSubmodule,
          CellClass.quotCoeffsOn L n (CellClass.vertexClass k k le_rfl)
            (iterAdjointCubeAverage L n k U k f.1) =
          applyKernel M (CellClass.quotCoeffsOn L n (verticesAtZero k) f.1)) ∧
        KernelDescends L n (verticesAtZero k).colourPairs
          (CellClass.vertexClass k k le_rfl).colourPairs
          (fun ι' ι => FullSpace.iterAverageKernel L k
            (liftGaugeField L n k 0 U) ι'.2 ι.2) M ∧
        KernelDescends L n (CellClass.vertexClass k k le_rfl).colourPairs
          (verticesAtZero k).colourPairs
          (fun ι' ι => FullSpace.iterAverageKernel L k
            (liftGaugeField L n k 0 U) ι.2 ι'.2) (swapKernel M)) ∧
      (∃ M, (∀ f : (CellClass.quotSpace L n (verticesAtZero k)).complexSubmodule,
          CellClass.quotCoeffsOn L n (edgesAtZero k) (covDiff U f.1) =
          applyKernel M (CellClass.quotCoeffsOn L n (verticesAtZero k) f.1)) ∧
        KernelDescends L n (verticesAtZero k).colourPairs (edgesAtZero k).colourPairs
          (fun ι' ι => FullSpace.covDiffKernel L k 0
            (liftGaugeField L n k 0 U) ι'.2 ι.2) M ∧
        KernelDescends L n (edgesAtZero k).colourPairs (verticesAtZero k).colourPairs
          (fun ι' ι => FullSpace.covDiffKernel L k 0
            (liftGaugeField L n k 0 U) ι.2 ι'.2) (swapKernel M))
end YangMills.Construction.Tower.ThreeKernelsDescend
end

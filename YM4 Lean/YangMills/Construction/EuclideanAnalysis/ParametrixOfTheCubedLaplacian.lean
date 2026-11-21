import YangMills.Construction.EuclideanAnalysis.KernelsOfACubedLaplacianParametrix
import Mathlib
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanAnalysis.CubedLaplacian
def testLaplacianCubed (φ : SmoothTestFunction) : SmoothTestFunction :=
  testLaplacian (testLaplacian (testLaplacian φ))
def IsContinuousDensityOf (T : Distribution) (u : RealSpace 4 → ℂ) : Prop :=
  Continuous u ∧ ∀ φ : SmoothTestFunction, T φ = ∫ y, u y * φ y
def remainderDensityOne : RealSpace 4 → ℂ :=
  Classical.epsilon (IsContinuousDensityOf parametrixRemainderOne)
def remainderDensity (ρ : ℝ) (y : RealSpace 4) : ℂ :=
  ((ρ : ℂ) ^ 4)⁻¹ * remainderDensityOne (ρ⁻¹ • y)
def FundSolProperty : Prop :=
  IsContDiffOne (fun y => (fundSolLaplacianCubed y : ℂ)) ∧
    ∀ φ : SmoothTestFunction,
      ∫ y, (fundSolLaplacianCubed y : ℂ) * testLaplacianCubed φ y = φ 0
def RemainderIsSmooth : Prop :=
  (∃! u : RealSpace 4 → ℂ, IsContinuousDensityOf parametrixRemainderOne u) ∧
    IsContinuousDensityOf parametrixRemainderOne remainderDensityOne ∧
    ContDiff ℝ ∞ remainderDensityOne ∧
    ∀ (ρ : ℝ) (hρ : 0 < ρ) (u : RealSpace 4 → ℂ),
      IsContinuousDensityOf (laplacianCubedRemainder ρ hρ) u ↔ u = remainderDensity ρ
def KernelsRegularAndLocal (ρ : ℝ) : Prop :=
  ContDiff ℝ 1 (laplacianCubedParametrix ρ) ∧
    ContDiff ℝ ∞ (remainderDensity ρ) ∧
    (∀ y, (remainderDensity ρ y).im = 0) ∧
    HasCompactSupport (laplacianCubedParametrix ρ) ∧
    tsupport (laplacianCubedParametrix ρ) ⊆ Metric.ball 0 ρ ∧
    HasCompactSupport (remainderDensity ρ) ∧
    tsupport (remainderDensity ρ) ⊆ Metric.ball 0 ρ
def ReproducingIdentity (ρ : ℝ) : Prop :=
  ∀ (φ : SmoothTestFunction) (y : RealSpace 4),
    φ y = convolution (testLaplacianCubed φ) (fun z => (laplacianCubedParametrix ρ z : ℂ)) y +
      convolution φ (remainderDensity ρ) y
def KernelNormsScaling (ρ : ℝ) : Prop :=
  TestFunctions.uniformNorm (laplacianCubedParametrix ρ) =
      ρ ^ 2 * TestFunctions.uniformNorm parametrixOne ∧
    gradUniformNorm (laplacianCubedParametrix ρ) = ρ * gradUniformNorm parametrixOne ∧
    TestFunctions.uniformNorm (remainderDensity ρ) =
      (ρ ^ 4)⁻¹ * TestFunctions.uniformNorm remainderDensityOne ∧
    gradUniformNorm (remainderDensity ρ) = (ρ ^ 5)⁻¹ * gradUniformNorm remainderDensityOne
def OneScaleNormsFinite : Prop :=
  TestFunctions.IsBoundedFun parametrixOne ∧
    TestFunctions.IsBoundedFun (gradNorm parametrixOne) ∧
    TestFunctions.IsBoundedFun remainderDensityOne ∧
    TestFunctions.IsBoundedFun (gradNorm remainderDensityOne)
def ParametrixSpec : Prop :=
  FundSolProperty ∧
    RemainderIsSmooth ∧
    (∀ ρ : ℝ, 0 < ρ → KernelsRegularAndLocal ρ) ∧
    (∀ ρ : ℝ, 0 < ρ → ReproducingIdentity ρ ∧ KernelNormsScaling ρ) ∧
    OneScaleNormsFinite
end YangMills.Construction.EuclideanAnalysis.CubedLaplacian

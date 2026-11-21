import YangMills.Construction.EuclideanAnalysis.FunctionsAndDistributions
import Mathlib
open Set TopologicalSpace
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanAnalysis.CubedLaplacian
def fundSolLaplacianCubed (x : YangMills.Construction.EuclideanAnalysis.RealSpace 4) : ℝ :=
  if x = 0 then 0 else -(64 * Real.pi ^ 2)⁻¹ * ‖x‖ ^ 2 * Real.log ‖x‖
def unitBallOpens : Opens (YangMills.Construction.EuclideanAnalysis.RealSpace 4) :=
  ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
def IsRadialBump
    (χ : YangMills.Construction.EuclideanAnalysis.CompactSupportClass ⊤ unitBallOpens ℝ) : Prop :=
  YangMills.Construction.EuclideanAnalysis.IsRadial χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
    ∀ᶠ x in 𝓝 (0 : YangMills.Construction.EuclideanAnalysis.RealSpace 4), χ x = 1
def radialBump : YangMills.Construction.EuclideanAnalysis.CompactSupportClass ⊤ unitBallOpens ℝ :=
  haveI : Nonempty
      (YangMills.Construction.EuclideanAnalysis.CompactSupportClass ⊤ unitBallOpens ℝ) := ⟨0⟩
  Classical.epsilon IsRadialBump
def parametrixOne (x : YangMills.Construction.EuclideanAnalysis.RealSpace 4) : ℝ :=
  radialBump x * fundSolLaplacianCubed x
def parametrixRemainderOne : YangMills.Construction.EuclideanAnalysis.Distribution :=
  YangMills.Construction.EuclideanAnalysis.dirac -
    YangMills.Construction.EuclideanAnalysis.distribLaplacian
      (YangMills.Construction.EuclideanAnalysis.distribLaplacian
        (YangMills.Construction.EuclideanAnalysis.distribLaplacian
          (YangMills.Construction.EuclideanAnalysis.ofFunction
            fun x => (parametrixOne x : ℂ))))
def testFunctionRescale (r : ℝ) (hr : 0 < r) :
    YangMills.Construction.EuclideanAnalysis.SmoothTestFunction →ₗ[ℂ]
      YangMills.Construction.EuclideanAnalysis.SmoothTestFunction where
  toFun ψ :=
    { toFun := fun x => ψ (r • x)
      contDiff' := ψ.contDiff.comp (contDiff_const_smul r)
      hasCompactSupport' := ψ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero r hr.ne')
      tsupport_subset' := fun _ _ => trivial }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def distribRescale (r : ℝ) (hr : 0 < r) (T : YangMills.Construction.EuclideanAnalysis.Distribution) :
    YangMills.Construction.EuclideanAnalysis.Distribution :=
  ((r : ℂ) ^ 4) • (T ∘ₗ testFunctionRescale r hr)
def laplacianCubedParametrix (r : ℝ) (x : YangMills.Construction.EuclideanAnalysis.RealSpace 4) : ℝ :=
  r ^ 2 * parametrixOne (r⁻¹ • x)
def laplacianCubedRemainder (r : ℝ) (hr : 0 < r) :
    YangMills.Construction.EuclideanAnalysis.Distribution :=
  ((r : ℂ) ^ 4)⁻¹ • distribRescale r hr parametrixRemainderOne
end YangMills.Construction.EuclideanAnalysis.CubedLaplacian

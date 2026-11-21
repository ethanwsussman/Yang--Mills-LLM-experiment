import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def PointwiseDerivativeRules.Over (𝕜 : Type) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 ComplexMatrix2] : Prop :=
  ∀ (U : Set 𝕜) (A B C : 𝕜 → ComplexMatrix2) (A' B' C' : ComplexMatrix2), U ∈ 𝓝 (0 : 𝕜) →
    HasDerivAt A A' 0 → HasDerivAt B B' 0 → HasDerivAt C C' 0 →
    HasDerivAt (fun s => A s * B s * C s)
        (A' * B 0 * C 0 + A 0 * B' * C 0 + A 0 * B 0 * C') 0 ∧
      (A 0 = 1 →
        (∀ᶠ s in 𝓝 (0 : 𝕜), IsUnit (A s) ∧ A s ∈ logBall) ∧
        HasDerivAt (fun s => (A s)⁻¹) (-A') 0 ∧
        HasDerivAt (fun s => logSeries (A s)) A' 0 ∧
        ((∀ s ∈ U, (A s).det = 1) → fullTrace A' = 0 ∧ A' ∈ traceless)) ∧
      (B 0 = 0 → HasDerivAt (fun s => matExp (B s)) B' 0)
def PointwiseDerivativeRules.RealAndComplex : Prop :=
  PointwiseDerivativeRules.Over ℝ ∧ PointwiseDerivativeRules.Over ℂ
end YangMills.Construction.Matrices.ComplexMatrix2
end

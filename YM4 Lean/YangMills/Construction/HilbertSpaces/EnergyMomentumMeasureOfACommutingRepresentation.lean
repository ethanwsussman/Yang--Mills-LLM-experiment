import YangMills.Construction.HilbertSpaces.ReconstructionFromAPositiveFormDefs
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ComplexOrder InnerProductSpace
open YangMills.Construction.EuclideanBorel (Space BorelSubset SpectralIntegralIs IsSpectralIntegralOp
  IsSpectralMeasureOf StronglyCommute jointSpectrum spectralParamCoord momentumCoord momentumExpChar
  pvmSupport spectralMeasureOf sqIntegrableDomain expMomentumOp)
open YangMills.Construction.FormsOperators (IsSelfAdj IsC0Semigroup IsStronglyContUnitaryRep UnitaryMap)
open YangMills.Construction.SpectralTheory (UnboundedOp)
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction.CommutingJointSpectrum
def SatisfiesConditions {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : ℝ≥0 → E →L[ℂ] E) (A : UnboundedOp E) (G : Space 3 → UnitaryMap E E)
    (μ : BorelSubset (1 + 3) → E →L[ℂ] E) : Prop :=
  IsJointSpectralMeasure A G μ ∧
    IsSpectralIntegralOp A μ spectralParamCoord ∧
    (∀ s, SpectralIntegralIs μ (expNegEnergy s) (T s)) ∧
    IsSpectralMeasureOf G (momentumMarginal μ) ∧
    momentumMarginal μ = spectralMeasureOf G ∧
    (∀ i, IsSpectralIntegralOp (momentumOp μ i) μ (momentumCoord i) ∧
      IsSelfAdj (momentumOp μ i)) ∧
    (∀ a, sqIntegrableDomain μ (momentumExpChar a) = univ ∧
      ∀ x, expMomentumOp μ a x = G a x.1) ∧
    StronglyCommute ![A, momentumOp μ 0, momentumOp μ 1, momentumOp μ 2] ∧
    jointSpectrum μ = pvmSupport μ ∧
    pvmSupport μ ⊆ {q | 0 ≤ q energyCoordIndex}
def Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : ℝ≥0 → E →L[ℂ] E) (A : UnboundedOp E) (G : Space 3 → UnitaryMap E E),
    IsC0Semigroup T → IsSemigroupGenerator T A → IsNegLogOf A (T 1) →
    IsStronglyContUnitaryRep G →
    (∀ a s, toCLM (G a) * T s = T s * toCLM (G a)) →
    ExistsUnique (IsJointSpectralMeasure A G) ∧
    SatisfiesConditions T A G (jointSpectralMeasure A G)
end YangMills.Construction.PositiveFormReconstruction.CommutingJointSpectrum

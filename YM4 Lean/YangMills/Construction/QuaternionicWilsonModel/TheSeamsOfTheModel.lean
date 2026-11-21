import YangMills.Construction.ClusterExpansionOfAStep.FieldsAsConfigurations
import YangMills.Construction.ClusterExpansionOfAStep.TheFlowIsTheLawOfTheChain
import YangMills.Construction.TotalDensitiesGiveASystem.TopStatementDefs
import YangMills.Construction.WindowOfTheParameters.CoefficientAsAMixedMoment
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction.ModelSeams
structure ArraysAreChainDensities (ℓ : TorusLumps.StepParameters) : Prop where
  isChainDensity : ∀ (β : ℝ) (t n : ℕ) [NeZero n],
    ClusterExpansionOfAStep.IsChainDensity ℓ β (TotalDensityFlow.coupling ℓ β) t n ((TotalDensityFlow.flowData ℓ β t).2)
  bottom_eq : ∀ (β : ℝ) (m K n : ℕ) [NeZero n], 1 ≤ m → n = 2 * ℓ.side ^ m →
    ClusterExpansionOfAStep.wilsonPartition β (WeightedResponses.fineSide ℓ.side K n) =
        PeriodicLattice.partitionFunction ℓ.side m K β ∧
    ∀ G : (PeriodicLattice.Bond ℓ.side m (K : ℤ) → Matrices.ComplexMatrix2) → ℝ,
      ClusterExpansionOfAStep.IsBoundedMeasurable G →
      ∫ u, G (ClusterExpansionOfAStep.gaugeFieldOfTorusField ℓ.side m (K : ℤ) (WeightedResponses.initialField ℓ K n u))
          ∂(WeightedResponses.chainJointLaw ℓ β (TotalDensityFlow.coupling ℓ β) K n) =
        ∫ U, G U ∂(PeriodicLattice.wilsonGibbsMeasure ℓ.side m K β)
def hermitianOfImaginary (X : BlockAverages.imaginaryQuaternions) : Matrices.ComplexMatrix2 :=
  (-Complex.I) • SoftAverages.quaternionToMatrix (X : ℍ[ℝ])
def imagQuaternion (a b c : ℝ) : BlockAverages.imaginaryQuaternions := ⟨⟨0, a, b, c⟩, rfl⟩
structure ImaginaryQuaternionsArePauliAlgebra : Prop where
  matrix_eq : ∀ X : BlockAverages.imaginaryQuaternions,
    SoftAverages.quaternionToMatrix (X : ℍ[ℝ]) = Complex.I • hermitianOfImaginary X
  isHermitian : ∀ X : BlockAverages.imaginaryQuaternions, (hermitianOfImaginary X).IsHermitian
  trace_eq_zero : ∀ X : BlockAverages.imaginaryQuaternions,
    Matrices.ComplexMatrix2.fullTrace (hermitianOfImaginary X) = 0
  existsUnique : ∀ A : Matrices.ComplexMatrix2, A.IsHermitian → Matrices.ComplexMatrix2.fullTrace A = 0 →
    ∃! X : BlockAverages.imaginaryQuaternions, hermitianOfImaginary X = A
  inner_eq_half_trace : ∀ X X' : BlockAverages.imaginaryQuaternions,
    ((inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) : ℝ) : ℂ) =
      (1 / 2) * Matrices.ComplexMatrix2.fullTrace (hermitianOfImaginary X * hermitianOfImaginary X')
  pauli_i : hermitianOfImaginary (imagQuaternion 1 0 0) = !![1, 0; 0, -1]
  pauli_j : hermitianOfImaginary (imagQuaternion 0 1 0) = !![0, -Complex.I; Complex.I, 0]
  pauli_k : hermitianOfImaginary (imagQuaternion 0 0 1) = !![0, 1; 1, 0]
  exp_eq : ∀ X : BlockAverages.imaginaryQuaternions,
    ((ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary (BlockAverages.expUnit X) :
        Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      Matrices.ComplexMatrix2.matExp (Complex.I • hermitianOfImaginary X)
  perturb_eq : ∀ {n k : ℕ} (c : Fin k → TorusFields.TorusBond n) (X : Fin k → BlockAverages.imaginaryQuaternions)
      (σ : Fin k → ℝ) (x : TorusFields.TorusSite n) (i : Fin 4),
    ((ClusterExpansionOfAStep.unitQuaternionEquivSpecialUnitary
        (TorusFields.perturb c X σ (TorusFields.trivialField n) x i) :
        Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      Matrices.ComplexMatrix2.matExp (Complex.I • ∑ l, if c l = (x, i) then (σ l : ℂ) • hermitianOfImaginary (X l) else 0)
def wilsonWeightMixedMomentEqNegCoupling : Prop :=
  ∀ (L : ℕ) (β : ℝ), 2 ≤ L → TotalDensityFlow.HasNextCoupling L (TorusLumps.wilsonWeight β) β ∧
    ∀ b : ℝ, SlopeCoefficient.HasMixedSecondMoment (TotalDensityFlow.sideFilter L)
      (TotalDensityFlow.logRatio (TorusLumps.wilsonWeight β)) b ↔ b = -β
def seamsStatement : Prop :=
  (∀ ℓ : TorusLumps.StepParameters, TotalDensitySystem.IsUnitMeshStepParameters ℓ → ArraysAreChainDensities ℓ) ∧
    ImaginaryQuaternionsArePauliAlgebra ∧
    wilsonWeightMixedMomentEqNegCoupling
end YangMills.Construction.ModelSeams
end

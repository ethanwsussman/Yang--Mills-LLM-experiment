import YangMills.Construction.EuclideanFunctionals.InsertionBoundOfAReconstructionFromTheBoundOnTheFreeSlab
import YangMills.Construction.LimitTheorem.AssertionsAtGivenConstants
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.LimitAlongPeriodicGibbsStatesIsTheLimitOfABoundedApproximation
import YangMills.Construction.RotationInvariance.TwoPointFunctionDecidesRotationInvariance
import YangMills.Construction.TwoPoints.RotationInvarianceFromMirrorPairs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FirstPassageSeqs.CenteredLimitRotation
structure TwoPointHypotheses (S : EuclideanFunctionals.ConnFamily) (C : ℕ → ℝ → ℝ → ℝ) : Prop where
  linear : PairFunctions.IsBilinearOnPairs (S.fn 2 le_rfl)
  nonneg : ∀ d R : ℝ, 0 < d → 0 < R → 0 ≤ C 2 d R
  antitone : ∀ d d' R : ℝ, 0 < d → d ≤ d' → 0 < R → C 2 d' R ≤ C 2 d R
  reflectedBound : ∃ (d₀ : ℝ) (u : ℝ → ℝ), TwoPoints.ReflectedUpperBound
    (PairFunctions.realPartForm (S.fn 2 le_rfl)) d₀ u
def Claim : Prop :=
  ∀ (M : ReflectionPositivity.AxisMirror.MirrorData)
    (T : LimitConventions.ApproxTriple M.L) (S : EuclideanFunctionals.ConnFamily)
    (τ : SeparatedTuples.TupleFunctional),
    τ.toFun = onSepTuples (EuclideanFunctionals.centeredFn S) →
    ReflectionPositivity.ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM M T →
    LimitConventions.ApproxTriple.IsReflPos T →
    LimitConventions.ApproxTriple.ConvergesTo T (onSepTuples (EuclideanFunctionals.centeredFn S)) →
    ∀ (c : EuclideanFunctionals.SharpScale) (C : ℕ → ℝ → ℝ → ℝ),
    EuclideanFunctionals.HasClusterBounds S c C → TwoPointHypotheses S C →
    ∀ (ς : SeparatedTuples.TupleFunctional) (p A a : ℝ), 0 ≤ p → 0 < a → a < 1 / 8 →
      EuclideanFunctionals.SlabInsertionTransfer.AgreesWithCenteredFn ς S →
      EuclideanFunctionals.SlabInsertionTransfer.FreeSlabBound ς c.M p A a →
      EuclideanFunctionals.TwoPointRotationCriterion.OrthogonalInvariantConnected S ∧
        EuclideanFunctionals.TwoPointRotationCriterion.OrthogonalInvariantOnComplexTuples S ∧
        LimitTheorem.IsO4InvariantFunctional τ
end YangMills.Construction.FirstPassageSeqs.CenteredLimitRotation
end

import YangMills.Construction.Continuum.ForwardConeDefs
import YangMills.Construction.Continuum.HilbertSpaceOfAReflectionPositiveFunctional
import YangMills.Construction.Continuum.RulesOfTheOrthogonalAction
import YangMills.Construction.Continuum.SettingOfRotationsOfAFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.TupleForm ReflectionPositiveHilbert
open OrthogonalAction Orthogonal TestFunctions SeparatedTuples
namespace Continuum.RotationModulus
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
structure RotationHypotheses (M : ℝ) (φ : TupleFunctional) (B : ℕ → ℝ → ℝ → ℝ) : Prop where
  entrywiseLinear : φ.IsEntrywiseLinear
  permInvariant : φ.IsPermInvariant
  reflectionPositive : ForwardCone.IsRPTimeZero φ
  bound_nonneg : ∀ k : ℕ, 1 ≤ k → ∀ d r : ℝ, 0 < d → 0 < r → 0 ≤ B k d r
  bound_spec : ∀ k : ℕ, 1 ≤ k → ∀ d r : ℝ, 0 < d → 0 < r →
    Rotations.SeparatedBound M φ k d r (B k d r)
  orthogonal_invariant : ∀ Q : orthogonalGroupThree, φ.IsInvariant (matMap (embedOrthogonal Q))
def reflectedAndSupports (X : SepTuple) : Fin X.1.length ⊕ Fin X.1.length → Set AmbientSpace :=
  Sum.elim (fun i => TimeAxis.timeReflection '' tsupport (X.1.get i)) fun i => tsupport (X.1.get i)
def pairwiseSupportDists (X : SepTuple) : Set ENNReal :=
  {t | ∃ i j, i ≠ j ∧
    t = setDistR4 (reflectedAndSupports X i) (reflectedAndSupports X j)}
def minSupportDist (X : SepTuple) : ℝ := (sInf (pairwiseSupportDists X)).toReal
def maxSupportRadius (X : SepTuple) : ℝ :=
  sSup {r | ∃ x ∈ ⋃ i, tsupport (X.1.get i), r = euclidNormVec x}
def tupleState (φ : TupleFunctional) (X : SepTuple)
    (hX : X ∈ supportedIn TimeAxis.upperHalfSpace) : StateSpace φ :=
  stateOf φ ⟨basisVec X, Submodule.subset_span ⟨⟨X, hX⟩, rfl⟩⟩
def continuityBound (M : ℝ) (X : SepTuple) (Q : orthogonalGroupThree) (b : ℝ) : ℝ :=
  2 * b * (∏ i, sharpNormR4 M (X.1.get i)) *
    ∑ i, sharpNormR4 M (orthogonalAct (embedOrthogonal Q) (X.1.get i) - X.1.get i) *
      ∏ j ∈ Finset.univ.erase i, sharpNormR4 M (X.1.get j)
def ModulusEstimate : Prop :=
  ∀ (M : ℝ) (φ : TupleFunctional) (B : ℕ → ℝ → ℝ → ℝ), 1 ≤ M → RotationHypotheses M φ B →
    ∀ X : SepTuple, ∀ hX : X ∈ supportedIn TimeAxis.upperHalfSpace, 1 ≤ X.size →
      (∀ f ∈ X.1, f ≠ 0) →
      0 < minSupportDist X ∧ 0 < maxSupportRadius X ∧
      ∀ Q : orthogonalGroupThree,
        matrixOperatorNorm (Q.1 - 1) * maxSupportRadius X ≤ minSupportDist X / 4 →
        ∃ hQ : push (matMap (embedOrthogonal Q)) X ∈ supportedIn TimeAxis.upperHalfSpace,
          ‖tupleState φ _ hQ - tupleState φ X hX‖ ^ 2 =
            2 * (φ (SepTuple.juxt (push TimeAxis.timeReflection X) X) -
              φ (SepTuple.juxt (push TimeAxis.timeReflection X)
                (push (matMap (embedOrthogonal Q)) X))) ∧
          2 * (φ (SepTuple.juxt (push TimeAxis.timeReflection X) X) -
              φ (SepTuple.juxt (push TimeAxis.timeReflection X)
                (push (matMap (embedOrthogonal Q)) X))) ≤
            continuityBound M X Q
              (B (2 * X.size) (minSupportDist X / 2) (maxSupportRadius X + minSupportDist X))
end Continuum.RotationModulus
end YangMills.Construction
end

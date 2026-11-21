import YangMills.Construction.Continuum.ForwardConeDefs
import YangMills.Construction.Continuum.HilbertSpaceOfAReflectionPositiveFunctional
import YangMills.Construction.Continuum.RulesOfTheOrthogonalAction
import YangMills.Construction.HilbertSpace.EuclideanProjectionMeasures
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
open EuclideanSpectral
open ReflectionPositivity.TupleForm ReflectionPositiveHilbert
open OrthogonalAction Orthogonal SeparatedTuples
namespace RotationInvariance
def IsRotationLift (σ : TupleFunctional) (R : orthogonalGroupThree)
    (U : StateSpace σ →L[ℂ] StateSpace σ) : Prop :=
  ∀ F F' : PositiveSpan,
    (F' : FormalSpan) = pushSpan (matMap (embedOrthogonal R)) (F : FormalSpan) →
    U (stateOf σ F) = stateOf σ F'
def rotationUnitary (σ : TupleFunctional) (R : orthogonalGroupThree) :
    StateSpace σ →L[ℂ] StateSpace σ :=
  Classical.epsilon (IsRotationLift σ R)
def PreservesReflectionForm (σ : TupleFunctional) (R : orthogonalGroupThree) : Prop :=
  ∀ F F' G G' : PositiveSpan,
    (G : FormalSpan) = pushSpan (matMap (embedOrthogonal R)) (F : FormalSpan) →
    (G' : FormalSpan) = pushSpan (matMap (embedOrthogonal R)) (F' : FormalSpan) →
    reflectionForm σ G G' = reflectionForm σ F F'
def ActsUnitarily (σ : TupleFunctional) (R : orthogonalGroupThree) : Prop :=
  (∃! U : StateSpace σ →L[ℂ] StateSpace σ, IsRotationLift σ R U) ∧
  IsUnitaryMap (rotationUnitary σ R : StateSpace σ →ₗ[ℂ] StateSpace σ) ∧
  rotationUnitary σ R (vacuum σ) = vacuum σ
def MulActsByComp (σ : TupleFunctional) (R : orthogonalGroupThree) : Prop :=
  ∀ R' : orthogonalGroupThree, σ.IsInvariant (matMap (embedOrthogonal R')) →
    σ.IsInvariant (matMap (embedOrthogonal (R * R'))) ∧
    rotationUnitary σ (R * R') = (rotationUnitary σ R).comp (rotationUnitary σ R')
def InvariantRotationIsUnitary : Prop :=
  ∀ (σ : TupleFunctional) (R : orthogonalGroupThree),
    ForwardCone.IsRPTimeZero σ → σ.IsInvariant (matMap (embedOrthogonal R)) →
      PreservesReflectionForm σ R ∧ ActsUnitarily σ R ∧ MulActsByComp σ R
end RotationInvariance
end
end YangMills.Construction

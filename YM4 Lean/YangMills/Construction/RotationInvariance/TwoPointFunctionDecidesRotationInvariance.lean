import YangMills.Construction.EuclideanFunctionals.ElementOfTheOrthogonalGroupAsAnIsometry
import YangMills.Construction.EuclideanFunctionals.TransportOfAReconstructionAndThePlateBoundInACoordinatePlane
import YangMills.Construction.RotationInvariance.ComplexTuplesAndPlaneData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TwoPointRotationCriterion
open RealPlane
def TwoPointLocallyRotationInvariant (S : ConnFamily) (w : hyperoctahedral) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ f g : R4 → ℝ,
    f ∈ C1c ℝ → g ∈ C1c ℝ → Disjoint (supp f) (supp g) →
      ReflectionPositivity.AxisMirror.Ambient.evalOrZero (S.fn 2 le_rfl)
          [(imagePlaneRotation w t).actFn f, (imagePlaneRotation w t).actFn g] =
        ReflectionPositivity.AxisMirror.Ambient.evalOrZero (S.fn 2 le_rfl) [f, g]
def OrthogonalInvariantConnected (S : ConnFamily) : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (Q : Matrix.orthogonalGroup (Fin 4) ℝ), ∀ X ∈ sepN k,
    ReflectionPositivity.AxisMirror.Ambient.evalOrZero (S.fn k hk)
        ((EuclidMotion.ofOrthogonalMatrix Q).actList X) =
      ReflectionPositivity.AxisMirror.Ambient.evalOrZero (S.fn k hk) X
def OrthogonalInvariantOnComplexTuples (S : ConnFamily) : Prop :=
  ∀ (Q : Matrix.orthogonalGroup (Fin 4) ℝ) (k : ℕ), ∀ g ∈ disjointComplexTuples k,
    centeredFnFree S ((EuclidMotion.ofOrthogonalMatrix Q).actFree (complexTuple g)) =
      centeredFnFree S (complexTuple g)
def TwoPointCriterion : Prop :=
  ∀ (M : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon M S), σ.ConeCondition →
    ∀ (w : hyperoctahedral) (p c : ℝ) (hp : 0 < p) (hc : c ∈ productBoundFractions),
      ImagePlaneProductBound σ w hp hc →
        (TwoPointLocallyRotationInvariant S w ↔
            OrthogonalInvariantConnected S) ∧
          (TwoPointLocallyRotationInvariant S w →
            OrthogonalInvariantConnected S →
              OrthogonalInvariantOnComplexTuples S)
end YangMills.Construction.EuclideanFunctionals.TwoPointRotationCriterion
end

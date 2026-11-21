import YangMills.Construction.EuclideanFunctionals.JointSpectralMeasureOfAReconstructionAndTheConeCondition
import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.EuclidFunctionalWithRecon
open SpectralPoint
open HilbertSpaceBasics (ofBounded)
open OperatorTransport (IsBoundedAdjoint)
open BorelCalculus (IsBoundedFn conjFn)
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
def pyramidCalc (f : pyramid.1 → ℂ) : σ.space →L[ℂ] σ.space :=
  σ.jointMeasure.integralOpOn pyramid f
namespace ConeForms
def Holds : Prop :=
  ∀ {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S),
    (σ.ConeCondition ↔ ∀ j : Fin 3, σ.HamGeAbsMomentum j) ∧
    ((∀ j : Fin 3, σ.HamGeAbsMomentum j) ↔ σ.jointMeasure.IsCarriedBy pyramid) ∧
    (σ.ConeCondition → (∀ j : Fin 3, σ.HamGeAbsMomentum j) →
      σ.jointMeasure.IsCarriedBy pyramid →
      (∀ f : pyramid.1 → ℂ, Measurable f → IsBoundedFn f →
        σ.borelCalculus pyramid f = ofBounded (σ.pyramidCalc f) ∧
        ‖σ.pyramidCalc f‖ ≤ ⨆ p, ‖f p‖ ∧
        IsBoundedAdjoint (σ.pyramidCalc (conjFn f))
          (σ.pyramidCalc f)) ∧
      ∀ f g : pyramid.1 → ℂ, Measurable f → IsBoundedFn f → Measurable g →
        IsBoundedFn g →
        σ.pyramidCalc (f + g) =
            σ.pyramidCalc f + σ.pyramidCalc g ∧
        (∀ a : ℂ, σ.pyramidCalc (a • f) = a • σ.pyramidCalc f) ∧
        σ.pyramidCalc (f * g) =
          σ.pyramidCalc f * σ.pyramidCalc g)
end ConeForms
end YangMills.Construction.EuclideanFunctionals.EuclidFunctionalWithRecon

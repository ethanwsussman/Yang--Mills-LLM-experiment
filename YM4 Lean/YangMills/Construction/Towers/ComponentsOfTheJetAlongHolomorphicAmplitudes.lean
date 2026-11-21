import YangMills.Construction.Towers.OperatorFunctionsOfTheScaledPictureDefs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.JetAlongAmplitudes
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions
def JetComponentsHolomorphicAlongAmplitudes : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
      JetComponentsHolomorphic L k I I'
end YangMills.Construction.Tower.FullSpace.JetAlongAmplitudes
end

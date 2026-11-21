import YangMills.Construction.RunningCouplingSlope.ExcessOfAStepForm
import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import Mathlib
set_option autoImplicit false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Conventions
namespace RunningCouplingSlope
def ChainActionIsSumOfExcesses : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ (X : ChainPoint L n (k + 1)), IsCompactValued X →
      ∀ (Z : (j : Fin (k + 1)) → (frameAtStep L n (k + 1) j).GaugeField (frameAtStep L n (k + 1) j).depth)
        (Z' : (j : Fin (k + 1)) → (frameAtStep L n (k + 1) j).GaugeField (frameAtStep L n (k + 1) j).top),
        (∀ (j : Fin (k + 1)) (b : (frameAtStep L n (k + 1) j).Site (frameAtStep L n (k + 1) j).depth × Fin 4),
          levelField X j (edgeOfCoords j b) =
            SoftAverages.quaternionToMatrix ((Z j b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) →
        (∀ (j : Fin (k + 1)) (b : (frameAtStep L n (k + 1) j).Site (frameAtStep L n (k + 1) j).top × Fin 4),
          levelField X (j + 1) (edgeOfCoords (j + 1) b) =
            SoftAverages.quaternionToMatrix ((Z' j b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) →
        chainAction a X =
          minimalAction a (finiteCells (frameAtStep L n (k + 1) (Fin.last k)))
              (frameAtStep L n (k + 1) (Fin.last k)).top (Z' (Fin.last k)) +
            ∑ j : Fin (k + 1), excessEnergy a (Z j) (Z' j)
end RunningCouplingSlope
end YangMills.Construction
end

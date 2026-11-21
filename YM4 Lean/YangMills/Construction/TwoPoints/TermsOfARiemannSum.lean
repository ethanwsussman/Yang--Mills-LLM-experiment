import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def RiemannSumTermProperties.Statement : Prop :=
  ∀ k ∈ ccIn (Set.univ : Set AmbientSpace), ∀ φ ∈ compactC1Complex, ∀ δ : ℝ, 0 < δ →
    (∀ j, MeasurableSet (gridCube δ j)) ∧
      (∀ j, ∀ z ∈ gridCube δ j, euclidNorm (z - gridCenter δ j) ≤ δ) ∧
      (∀ j, setIntegralOf (gridCube δ j) k ≠ 0 → ∃ z ∈ tsupport k, z ∈ gridCube δ j) ∧
      {j : Fin 4 → ℤ | setIntegralOf (gridCube δ j) k • translateFun (gridCenter δ j) φ ≠ 0}.Finite ∧
      cubeRiemannSum δ k φ ∈ compactC1Complex ∧
      tsupport (cubeRiemannSum δ k φ) ⊆
        minkowskiSum (minkowskiSum (tsupport k) (euclidClosedBall (0 : AmbientSpace) δ)) (tsupport φ)
end YangMills.Construction.TwoPoints
end

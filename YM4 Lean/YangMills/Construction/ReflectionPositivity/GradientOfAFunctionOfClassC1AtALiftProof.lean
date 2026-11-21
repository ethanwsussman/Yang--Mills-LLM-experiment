import YangMills.Construction.ReflectionPositivity.FactsOfTheCoveringMap
import YangMills.Construction.ReflectionPositivity.GradientOfAFunctionOfClassC1AtALift
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
theorem gradAtAnyLift_holds (hProj : ProjectionFacts) : gradAtAnyLift := by
  intro D 𝕜 _ f _ y
  have hTrans := (hProj D).1.2.2.2.1
  have hChoice : D.projection (D.liftChoice (D.projection y)) = D.projection y :=
    Classical.epsilon_spec (p := fun z => D.projection z = D.projection y) ⟨y, rfl⟩
  funext μ
  show TestFunctions.partialDerivR4 μ (f ∘ D.projection) (D.liftChoice (D.projection y)) =
    TestFunctions.partialDerivR4 μ (f ∘ D.projection) y
  unfold TestFunctions.partialDerivR4
  congr 1
  funext t
  simp only [Function.comp_apply]
  rw [← hTrans, hChoice, hTrans]
end YangMills.Construction.ReflectionPositivity.AxisMirror

import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import YangMills.Construction.Torus.TestFunctionsAndDistributionsOnOpenSetsOfTuples
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ContDiff
noncomputable section
namespace YangMills.Construction
namespace AmbientPoints
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ}
theorem isOpen_pairwiseDistinctTuples : IsOpen (pairwiseDistinctTuples s E n) := by
  have key : pairwiseDistinctTuples s E n =
      ⋂ a : Fin n, ⋂ b : Fin n, ⋂ _ : a ≠ b, {x : Tuple s E n | x a ≠ x b} := by
    ext x
    simp only [mem_iInter]
    exact ⟨fun (hx : Function.Injective x) a b hab => hx.ne hab,
      fun hx a b hab => by_contra fun hne => hx a b hne hab⟩
  rw [key]
  exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
    isOpen_iInter_of_finite fun _ => isOpen_ne_fun (continuous_apply a) (continuous_apply b)
def HasOrderLEOn (k : ℕ) {U U' : Set (Tuple s E n)} (hU : U' ⊆ U)
    (T : testFns U → ℂ) : Prop :=
  HasOrderLE k (restrictDistrib hU T)
def IsSmoothReal (g : Pt s E → ℝ) : Prop := ContDiff ℝ ∞ (g ∘ proj s E)
def realTensor (g : Fin n → Pt s E → ℝ) : Tuple s E n → ℂ :=
  tensorProd fun a p => (g a p : ℂ)
end AmbientPoints
end YangMills.Construction

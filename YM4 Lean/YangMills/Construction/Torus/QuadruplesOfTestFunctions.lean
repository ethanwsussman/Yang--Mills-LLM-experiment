import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace TestFunctions
def pairwiseQuadruples {Y : Type*} (dist : Y → Y → ℝ) (T : Set ((Y → ℝ) × (Y → ℝ))) :
    Set (Fin 4 → Y → ℝ) :=
  {f | (∀ i, IsLipschitzFor dist (f i) ∧ ∀ y, 0 ≤ f i y) ∧ ∀ i j, i ≠ j → (f i, f j) ∈ T}
def IsScaleShape (d ϑ : ℝ) : Prop := 0 < d ∧ ϑ ∈ Ioc (0 : ℝ) 1
end TestFunctions
end YangMills.Construction

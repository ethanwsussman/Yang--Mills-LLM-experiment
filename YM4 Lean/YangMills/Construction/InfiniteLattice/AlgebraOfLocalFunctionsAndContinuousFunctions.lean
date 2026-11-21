import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
abbrev ContinuousGaugeFunctions (a : ℝ) : Type := C(GaugeField a, ℂ)
theorem DependsOnlyOnLinks.mono {E : Type*} {S T : Set (Link a)} (hST : S ⊆ T)
    {F : GaugeField a → E} (hF : DependsOnlyOnLinks S F) : DependsOnlyOnLinks T F :=
  fun U V h => hF U V (funext fun l => congrFun h ⟨l, hST l.2⟩)
def cylinderAlgebra (a : ℝ) : Subalgebra ℂ (GaugeField a → ℂ) where
  carrier := continuousCylinderFunctions a
  mul_mem' := by
    rintro F G ⟨hF, S, hS, hSB, hSF⟩ ⟨hG, T, hT, hTB, hTG⟩
    refine ⟨hF.mul hG, S ∪ T, hS.union hT, union_subset hSB hTB, fun U V h => ?_⟩
    simp only [Pi.mul_apply]
    rw [hSF.mono subset_union_left U V h, hTG.mono subset_union_right U V h]
  add_mem' := by
    rintro F G ⟨hF, S, hS, hSB, hSF⟩ ⟨hG, T, hT, hTB, hTG⟩
    refine ⟨hF.add hG, S ∪ T, hS.union hT, union_subset hSB hTB, fun U V h => ?_⟩
    simp only [Pi.add_apply]
    rw [hSF.mono subset_union_left U V h, hTG.mono subset_union_right U V h]
  algebraMap_mem' z :=
    ⟨continuous_const, ∅, finite_empty, empty_subset _, fun _ _ _ => rfl⟩
end YangMills.Construction.InfiniteLattice

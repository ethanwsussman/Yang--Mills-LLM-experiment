import YangMills.Construction.TorusOrFourSpace.ZeroFamilyObeysEveryBoundFunction
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicSpace.Kind.ZeroFamily
theorem zeroHierarchyExists_holds : ZeroHierarchyExists := by
  intro D E C
  refine ⟨⟨fun _ _ _ => 0, fun _ _ _ _ _ _ => ⟨fun _ => by simp, fun _ _ => by simp⟩,
    fun _ _ _ _ _ => rfl⟩, ?_, fun _ _ _ => rfl⟩
  intro n hn d R _ _ f _
  simp
end YangMills.Construction.PeriodicSpace.Kind.ZeroFamily

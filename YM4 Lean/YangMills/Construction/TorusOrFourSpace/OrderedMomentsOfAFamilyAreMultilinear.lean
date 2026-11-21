import YangMills.Construction.TorusOrFourSpace.FamiliesOfMultilinearFunctionalsAndOrderedMoments
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
def Hierarchy.toMultilinearFamily {D : Params} {E : Kind} (Φ : Hierarchy D E) :
    MultilinearFamily D E :=
  ⟨Φ.func, Φ.multilinear⟩
namespace OrderedMoments
def MultilinearityStatement : Prop :=
  ∀ (D : Params) (E : Kind),
    (∀ Φ : MultilinearFamily D E,
      (∀ (q : ℕ) (hq : 1 ≤ q),
        IsMultilinearOn D E (sepC1Tuples D E q) (Φ.indexOrderedMoment hq)) ∧
      ∀ f : sepC1Tuples D E 1, Φ.indexOrderedMoment le_rfl f = 0) ∧
    partitionsNoSingletons 1 = ∅ ∧
    ∀ Φ : Hierarchy D E,
      (∀ (n : ℕ) (hn : 2 ≤ n), Φ.toMultilinearFamily.func n hn = Φ.func n hn) ∧
      ∀ (q : ℕ) (hq : 1 ≤ q) (f : sepC1Tuples D E q),
        Φ.toMultilinearFamily.indexOrderedMoment hq f = Φ.partitionMoment f
end OrderedMoments
end YangMills.Construction.PeriodicSpace.Kind

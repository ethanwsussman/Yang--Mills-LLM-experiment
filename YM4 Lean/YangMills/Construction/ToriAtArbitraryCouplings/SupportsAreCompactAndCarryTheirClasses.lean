import YangMills.Construction.ToriAtArbitraryCouplings.ClassesOfFunctionsSeparatedTuplesAndTheSeparation
import YangMills.Construction.ToriAtArbitraryCouplings.TheCountableFamilyOfSupportsAndCharts
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace CompactSupports
def Statement : Prop :=
  ∀ (s : TorusSide) (E : Ambient) (K : Set (s.Point E)), K ∈ s.supportFamily E →
    s.IsCompactWrt E K ∧ s.c1VanishingOutside E K = s.c1SuppIn E K
end CompactSupports
end YangMills.Construction.ToriAtArbitraryCouplings
end

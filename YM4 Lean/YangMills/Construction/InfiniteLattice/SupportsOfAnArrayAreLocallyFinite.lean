import YangMills.Construction.InfiniteLattice.PropertiesOfToriArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def ArraySupportsLocallyFinite : Prop :=
  ∀ A : LocalObservableArray, A.SupportsLocallyFinite
end YangMills.Construction.InfiniteLattice

import YangMills.Construction.Towers.LogarithmsSectorsAndDensityDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open UnitLatticeL2
namespace AbelianFieldDensity.SectorDecomposition
def TranslationPreservesTrace : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n : Fin 4 → ℤ,
    PreservesTraceDensity (L := L) (vertexPos L) (vertexShift (L := L) n) n ∧
      PreservesTraceDensity (L := L) (edgePos L) (edgeShift (L := L) n) n
end AbelianFieldDensity.SectorDecomposition
end YangMills.Construction.Tower
end

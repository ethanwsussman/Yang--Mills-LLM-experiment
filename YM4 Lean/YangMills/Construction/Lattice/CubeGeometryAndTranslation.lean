import YangMills.Construction.Lattice.CubesOfASeparatedSequence
import YangMills.Construction.Lattice.TranslationAdjointLaws
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open ScaledFun
variable {d N : ℕ}
namespace Scales
variable {L j : ℕ} (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh))
def centeringSite : GridPoint d S.fineMesh := S.fineOffset + S.unitToFine S.coarseOffset
def centeringFormEquiv : OneForm d S.fineMesh ≃ₗ[ℝ] OneForm d S.fineMesh :=
  multiFieldTranslation (Fin d) S.centeringSite
def conjCentering (O : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh) :
    OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh :=
  S.centeringFormEquiv.symm.toLinearMap ∘ₗ O ∘ₗ S.centeringFormEquiv.toLinearMap
end Scales
end PeriodicLattice
namespace CubeCovering
open SeparatedSequences
variable {L m : ℕ}
namespace CubeData
variable (C : CubeData L m)
end CubeData
namespace Cube
variable {C : CubeData L m} (Q : Cube C)
end Cube
end CubeCovering
end YangMills.Construction
end

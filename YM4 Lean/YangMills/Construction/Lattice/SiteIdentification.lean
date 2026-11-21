import YangMills.Construction.Lattice.PeriodicTorus
import YangMills.Construction.LatticeFields.FieldsAndDifferences
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
section Transport
variable {M : ℕ} {κ : LatticeFields.LatticeShape d} {s : Mesh N}
end Transport
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
def uniformTorusShape : LatticeFields.LatticeShape d := .torus (fun _ => N) fun _ => S.period_pos
structure IsQuotientMapPair
    (φ : LatticeFields.LatticeSite (L ^ j) S.uniformTorusShape ≃ GridPoint d S.fineMesh)
    (φ₁ : LatticeFields.LatticeSite 1 S.uniformTorusShape ≃ GridPoint d S.unitMesh) : Prop where
  apply_toSite : ∀ v : LatticeFields.scaledIntLattice d (L ^ j),
    ((φ (LatticeFields.toSite (L ^ j) S.uniformTorusShape v) : GridPoint d S.fineMesh) : Torus d N) =
      fun μ => (((v : Fin d → ℝ) μ : ℝ) : AddCircle (N : ℝ))
  apply_toSite_unit : ∀ v : LatticeFields.scaledIntLattice d 1,
    ((φ₁ (LatticeFields.toSite 1 S.uniformTorusShape v) : GridPoint d S.unitMesh) : Torus d N) =
      fun μ => (((v : Fin d → ℝ) μ : ℝ) : AddCircle (N : ℝ))
end Scales
end YangMills.Construction.PeriodicLattice

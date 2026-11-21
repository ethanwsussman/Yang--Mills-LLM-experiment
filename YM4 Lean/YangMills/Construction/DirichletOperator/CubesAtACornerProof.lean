import YangMills.Construction.Dirichlet.CutoffDifferenceBoundsProof
import YangMills.Construction.Dirichlet.NearCentresOfCubeProof
import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubesAndCutoffs
import YangMills.Construction.RegionSequence.SeparatedNestedRegions
import YangMills.Construction.Lattice.StandardPartitionCubeGeometryArgument
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Torus
namespace PartitionCubes.CornerCells
variable {d : ℕ} {S : ℝ}
theorem exists_lift_norm_eq_supNorm (hS : 0 < S) (p : PeriodicTorus d S) :
    ∃ v : Fin d → ℝ, torusProj d S v = p ∧ ‖v‖ = supNorm p := by apply _root_.YangMills.Construction.Dirichlet.NearCentres.exists_lift_norm_eq_supNorm <;> assumption
theorem torusProj_add (u v : Fin d → ℝ) :
    torusProj d S (u + v) = torusProj d S u + torusProj d S v := by apply _root_.YangMills.Construction.Dirichlet.Commutator.torusProj_add <;> assumption
theorem torusProj_sub (u v : Fin d → ℝ) :
    torusProj d S (u - v) = torusProj d S u - torusProj d S v := by apply _root_.YangMills.Construction.Dirichlet.CutoffDifferences.torusProj_sub <;> assumption
theorem mem_spacingLattice_iff {σ : ℝ} {x : PeriodicTorus d S} :
    x ∈ spacingLattice d S σ ↔ ∃ k : Fin d → ℤ, x = torusProj d S fun μ => (k μ : ℝ) * σ :=
  Iff.rfl
variable {w : ℝ} {z : PeriodicTorus 4 S}
end PartitionCubes.CornerCells
end YangMills.Construction

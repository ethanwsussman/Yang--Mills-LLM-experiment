import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeAtOneSpacingProof
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import YangMills.Construction.InfiniteLattice.WindowDensitiesAndStandardWindows
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace FixedSpacing
namespace Setup
variable (S : Setup)
theorem mesh_pos : 0 < S.mesh := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.mesh_pos <;> assumption
variable {S}
theorem isLinkSet_window (W : LinkWindow S.mesh) :
    FixedSpacing.IsLinkSet (W.links : Set (Link S.mesh)) :=
  fun e he => mem_positiveLinks_iff.mpr (W.isPositive e he)
theorem finite_faces (W : LinkWindow S.mesh) : W.faces.Finite :=
  WilsonOperator.facesTouching_finite W.links
variable (S) (W : LinkWindow S.mesh)
def localAction (U : S.Fields) : ℝ :=
  -S.β * ∑ᶠ p ∈ W.faces, InfiniteLattice.faceEnergy U p
def localPartition (U' : S.Fields) : ℝ :=
  ∫ V, Real.exp (S.localAction W (W.glue S.mesh_pos V U')) ∂W.haarProd
def conditionalDensity (V : W.Assignments) (U' : S.Fields) : ℝ :=
  Real.exp (S.localAction W (W.glue S.mesh_pos V U')) / S.localPartition W U'
def conditionalKernel (F : S.Fields → ℂ) (U' : S.Fields) : ℂ :=
  ∫ V, F (W.glue S.mesh_pos V U') * (S.conditionalDensity W V U' : ℂ) ∂W.haarProd
theorem finite_linksInCube (r : ℝ) :
    (S.links ∩ linksWithin (FixedSpacing.closedCube r) : Set (Link S.mesh)).Finite :=
  (linksWithin_supNormVec_le_finite S.mesh r).subset inter_subset_right
def cubeWindow (r : ℝ) : LinkWindow S.mesh where
  links := (S.finite_linksInCube r).toFinset
  isPositive _ he :=
    mem_positiveLinks_iff.mp ((Set.Finite.mem_toFinset _).mp he).1
theorem mem_cubeWindow {r : ℝ} {e : Link S.mesh} :
    e ∈ (S.cubeWindow r).links ↔
      e ∈ S.links ∧ (e.initial : AmbientSpace) ∈ FixedSpacing.closedCube r ∧
        (e.terminal : AmbientSpace) ∈ FixedSpacing.closedCube r :=
  Set.Finite.mem_toFinset _
end Setup
end FixedSpacing
end YangMills.Construction

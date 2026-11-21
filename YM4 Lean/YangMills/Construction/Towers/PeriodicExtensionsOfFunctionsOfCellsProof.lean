import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import YangMills.Construction.Towers.PeriodicExtensionsOfFunctionsOfCells
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels.PeriodicLiftOfCellFunctions
theorem periodicLift_liftProperties (hproj : Tower.EdgeProjectionProperties)
    (hcells : PeriodicLiftCells.CellsAndClassesHold) : PeriodicLift.LiftProperties := by
  intro L hL k n hn A
  obtain ⟨j, hj, kind⟩ := A
  cases kind with
  | vertex =>
    refine ⟨fun f hf => ?_, fun f c => rfl⟩
    exact Submodule.mem_pi.2 fun x _ => Submodule.mem_pi.1 hf _ (Set.mem_univ _)
  | face =>
    refine ⟨fun f hf => ?_, fun f c => rfl⟩
    exact Submodule.mem_pi.2 fun x _ => Submodule.mem_pi.1 hf _ (Set.mem_univ _)
  | edge =>
    refine ⟨fun f hf => ?_, fun f c => ?_⟩
    · have h1 := (hproj L n k j hL hn hj).1
      have hf' : PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra f := hf
      refine And.intro (fun b hb => hf'.1 _ ((h1 b).2.2.1 hb)) fun b => ?_
      change f (Tower.FullSpace.projEdge L n k j b.opposite) = -f (Tower.FullSpace.projEdge L n k j b)
      rw [← (h1 b).2.2.2]
      exact hf'.2 _
    · have h2 := ((hcells L hL k n hn).1 j hj).2.2.1 c
      change f (Tower.FullSpace.projEdge L n k j c.1) = f (projPositiveEdge L n k j c).1
      rw [h2]
end YangMills.Construction.LocalKernels.PeriodicLiftOfCellFunctions

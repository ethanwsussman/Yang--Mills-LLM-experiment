import YangMills.Construction.Lattice.ContoursWithinBlocks
import YangMills.Construction.Lattice.DoubleBlockContours
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
theorem contoursWithinBlock_holds (hC : DoubleBlock.DoubleBlockContoursStatement) :
    ContoursWithinBlockStatement := by
  intro L m K i hL hm hi y x hx Γ hΓ
  obtain ⟨-, hsite⟩ := (hC L m K hL.1 hL.2 hm i hi (Bond.forwardFrom y 0)).1 y (Or.inl rfl)
  obtain ⟨⟨n, hn⟩, hall⟩ := hsite x hx
  obtain ⟨-, -, -, -, hcentre, hbonds⟩ := hall n hn
  refine ⟨?_, fun b hb => hbonds Γ hΓ b hb⟩
  rintro z (rfl | rfl | ⟨b, hb, rfl | rfl⟩)
  · exact hcentre _ ⟨0, fun μ _ => by simp [abs_nonneg], by simp⟩
  · exact hx
  · exact (hbonds Γ hΓ b hb).1
  · exact (hbonds Γ hΓ b hb).2
end YangMills.Construction.PeriodicLattice

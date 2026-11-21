import YangMills.Construction.Lattice.BondsOfAContourLieInTheDoubleBlock
import YangMills.Construction.Lattice.DoubleBlockContours
import Mathlib
namespace YangMills.Construction.PeriodicLattice
theorem contourBondsInDoubleBlock_of_contours
    (hC : DoubleBlock.DoubleBlockContoursStatement) : ContourBondsInDoubleBlock := by
  intro L m K n hL hm hn c y hy x hx Γ hΓ b hb
  obtain ⟨hsub, hsite⟩ := (hC L m K hL.1 hL.2 hm n hn c).1 y hy
  obtain ⟨⟨d, hd⟩, hall⟩ := hsite x hx
  obtain ⟨-, -, -, -, -, hbonds⟩ := hall d hd
  exact ⟨hsub (hbonds Γ hΓ b hb).1, hsub (hbonds Γ hΓ b hb).2⟩
end YangMills.Construction.PeriodicLattice

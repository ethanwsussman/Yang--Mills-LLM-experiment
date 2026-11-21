import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import YangMills.Construction.Towers.EndPointsOfTheContours
import Mathlib
noncomputable section
namespace YangMills.Construction.Tower
open InfiniteLattice (AmbientSpace)
theorem contourEndpoints_of_blockPaths
    (hPaths : PeriodicLattice.BlockPaths.Statement)
    (hStair : FullSpace.StaircaseContoursWellDefined) :
    ContourEndpoints := by
  intro L k j hL hk hj hjk
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  refine ⟨fun n hn y x hx γ hγ => ?_, fun y x hx γ hγ => ?_⟩
  · obtain ⟨⟨⟨-, hImg⟩, -, -⟩, -, hCont⟩ :=
      (hPaths L n k hL.1 hL.2 hn i (by omega)).1 y
    rw [← hImg] at hx
    obtain ⟨q, hq, hqx⟩ := hx
    have hOff : PeriodicLattice.offsetSite
        (y.toSublattice (PeriodicLattice.levelDepth k i)) q = x := Subtype.ext hqx
    have hC := (hCont q hq).1
    rw [hOff] at hC
    exact (hC γ hγ).1
  · obtain ⟨s, hs, -, ⟨ν, -, -, hFam⟩, -⟩ := hStair L k (i + 1) hL hk hj hjk y x hx
    have hsx : s = x := Subtype.ext hs
    subst hsx
    rw [hFam] at hγ
    obtain ⟨σ, -, hOnPath, -⟩ := hγ
    exact hOnPath
end YangMills.Construction.Tower
end

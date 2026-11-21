import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import YangMills.Construction.ChessboardTori.SitesOffTheFacePlanes
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace PointsOffWalls
theorem gridPoint_not_mem_walls {D : ChessboardSetup} (g : ReflectionGrid D) {x : AmbientSpace}
    (hx : x ∈ D.gridPoints) : x ∉ g.walls := by
  obtain ⟨n, hn⟩ := hx
  intro hmem
  simp only [ReflectionGrid.walls, mem_iUnion] at hmem
  obtain ⟨ν, k, hk⟩ := hmem
  obtain ⟨i, hi⟩ := g.origin_mem ν
  have hk' : x ν = g.origin ν + k * g.cellSide := hk
  rw [hn ν, hi, g.cellSide_eq] at hk'
  have hmesh : D.mesh ≠ 0 := D.mesh_pos.ne'
  have h1 : 2 * (n ν : ℝ) = 2 * i + 1 + 2 * (k * g.cellRatio) := by
    have h : D.mesh * (2 * (n ν : ℝ)) = D.mesh * (2 * i + 1 + 2 * (k * g.cellRatio)) := by
      linear_combination 2 * hk'
    exact mul_left_cancel₀ hmesh h
  have h2 : 2 * n ν = 2 * i + 1 + 2 * (k * g.cellRatio) := by exact_mod_cast h1
  omega
theorem preservesDist_translate (v : AmbientSpace) : PreservesDist (translate v) := by apply _root_.YangMills.Construction.SeparatedTuples.isEuclidIsometry_translate <;> assumption
theorem translate_image_gridPoints {D : ChessboardSetup} {v : AmbientSpace} (hv : v ∈ D.gridPoints) :
    translate v '' (D.gridPoints : Set AmbientSpace) = D.gridPoints := by
  refine Subset.antisymm ?_ fun x hx => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact D.gridPoints.add_mem hx hv
  · exact ⟨x - v, D.gridPoints.sub_mem hx hv, by simp [translate]⟩
theorem statement_holds : PointsOffWalls.Statement :=
  fun _ g => ⟨fun _ hx => gridPoint_not_mem_walls g hx,
    fun _ hr => g.reflectionGroup_le_latticeSymGroup hr,
    fun _ hv => ⟨preservesDist_translate _, translate_image_gridPoints hv⟩⟩
end PointsOffWalls
end YangMills.Construction.ChessboardTori

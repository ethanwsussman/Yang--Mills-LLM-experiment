import YangMills.Construction.Continuum.TimeAxisAndTheReflectionOfTime
import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix
noncomputable section
namespace YangMills.Construction.Mirrors
open YangMills.Construction.InfiniteLattice (AmbientSpace latticeSubgroup)
open YangMills.Construction.PeriodicLattice (coordVec)
def axialNormals : Set AmbientSpace := {v | ∃ μ : Fin 4, v = coordVec μ}
def diagonalNormals : Set AmbientSpace :=
  {v | ∃ μ ν : Fin 4, μ < ν ∧
    (v = coordVec μ + coordVec ν ∨ v = coordVec μ - coordVec ν)}
def sixteenNormals : Set AmbientSpace := axialNormals ∪ diagonalNormals
theorem exists_first_nonzero_eq_one {v : AmbientSpace} (hv : v ∈ sixteenNormals) :
    ∃ μ : Fin 4, v μ = 1 ∧ ∀ κ, κ < μ → v κ = 0 := by
  rcases hv with ⟨μ, rfl⟩ | ⟨μ, ν, hμν, rfl | rfl⟩
  · exact ⟨μ, by simp [coordVec], fun κ hκ => by
      simp [coordVec, Pi.single_eq_of_ne hκ.ne]⟩
  · exact ⟨μ, by simp [coordVec, Pi.single_eq_of_ne hμν.ne], fun κ hκ => by
      simp [coordVec, Pi.single_eq_of_ne hκ.ne, Pi.single_eq_of_ne (hκ.trans hμν).ne]⟩
  · exact ⟨μ, by simp [coordVec, Pi.single_eq_of_ne hμν.ne], fun κ hκ => by
      simp [coordVec, Pi.single_eq_of_ne hκ.ne, Pi.single_eq_of_ne (hκ.trans hμν).ne]⟩
theorem dotProduct_self_ne_zero_of_mem {v : AmbientSpace} (hv : v ∈ sixteenNormals) :
    v ⬝ᵥ v ≠ 0 := by
  obtain ⟨μ, hμ, -⟩ := exists_first_nonzero_eq_one hv
  intro hzero
  rw [dotProduct_self_eq_zero.mp hzero] at hμ
  norm_num at hμ
@[ext]
structure ReflectingHyperplane where
  normalVec : AmbientSpace
  normalVec_mem : normalVec ∈ sixteenNormals
  offset : ℝ
namespace ReflectingHyperplane
variable (H : ReflectingHyperplane)
def carrier : Set AmbientSpace := {x | H.normalVec ⬝ᵥ x = H.offset}
def reflect (x : AmbientSpace) : AmbientSpace :=
  x - (2 * (H.normalVec ⬝ᵥ x - H.offset) / (H.normalVec ⬝ᵥ H.normalVec)) • H.normalVec
def positiveSide : Set AmbientSpace := {x | H.normalVec ⬝ᵥ x > H.offset}
def HasAxialNormal : Prop := H.normalVec ∈ axialNormals
def IsLatticeSymmetric (a : ℝ) : Prop :=
  0 < a ∧ H.reflect '' (latticeSubgroup a : Set AmbientSpace) = latticeSubgroup a
theorem reflect_eq_hyperplaneReflect :
    H.reflect = InfiniteLattice.hyperplaneReflect H.normalVec H.offset := rfl
end ReflectingHyperplane
def axialHyperplane (μ : Fin 4) (c : ℝ) : ReflectingHyperplane :=
  ⟨coordVec μ, Or.inl ⟨μ, rfl⟩, c⟩
def axialReflection (μ : Fin 4) : AmbientSpace → AmbientSpace := (axialHyperplane μ 0).reflect
theorem timeReflection_eq_axialReflection :
    TimeAxis.timeReflection = axialReflection TimeAxis.timeIdx := by
  funext x κ
  fin_cases κ <;>
    simp [TimeAxis.timeReflection, TimeAxis.timeIdx, axialReflection, ReflectingHyperplane.reflect,
      axialHyperplane, coordVec, single_dotProduct]
  ring
theorem upperHalfSpace_eq_positiveSide :
    TimeAxis.upperHalfSpace = (axialHyperplane TimeAxis.timeIdx 0).positiveSide := by
  ext x
  simp [TimeAxis.upperHalfSpace, TimeAxis.timeComponent, ReflectingHyperplane.positiveSide,
    axialHyperplane, coordVec, single_dotProduct]
end YangMills.Construction.Mirrors

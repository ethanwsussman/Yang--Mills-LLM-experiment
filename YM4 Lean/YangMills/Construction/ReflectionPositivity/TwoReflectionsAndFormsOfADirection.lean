import YangMills.Construction.InfiniteLattice.BoxRepresentsTheTorusAndItsThinBoundaryLayerProof
import YangMills.Construction.InfiniteLattice.IsometriesOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.ObservablesOfTheUnitLatticeAndItsHalfSpaces
import YangMills.Construction.ReflectionPositivity.ClassesOfReflectionPositiveMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
open YangMills.Construction.InfiniteLattice
  (GaugeField AmbientSpace UnitLatticeSymmetry halfSpaceLocalObservables)
def linkPlane (μ : Fin 4) : UnitMirrorPair where
  normal := basisVec μ
  height := -(1 / 2)
  admissible := Or.inl ⟨⟨μ, rfl⟩, -1, by norm_num⟩
def sitePlane (μ : Fin 4) : UnitMirrorPair where
  normal := basisVec μ
  height := 0
  admissible := Or.inl ⟨⟨μ, rfl⟩, 0, by norm_num⟩
def linkReflect (μ : Fin 4) : UnitLatticeSymmetry := (linkPlane μ).reflect
def siteReflect (μ : Fin 4) : UnitLatticeSymmetry := (sitePlane μ).reflect
theorem basisVec_dotProduct (μ : Fin 4) (x : AmbientSpace) : basisVec μ ⬝ᵥ x = x μ := by apply _root_.YangMills.Construction.InfiniteLattice.BoxQuotient.coordVec_dotProduct <;> assumption
theorem linkReflect_apply (μ : Fin 4) (x : AmbientSpace) :
    (linkReflect μ).toFun x = x - (2 * x μ + 1) • basisVec μ := by
  change InfiniteLattice.hyperplaneReflect (basisVec μ) (-(1 / 2)) x = _
  have h : basisVec μ ⬝ᵥ basisVec μ = 1 := by rw [basisVec_dotProduct]; simp [basisVec]
  rw [InfiniteLattice.hyperplaneReflect, basisVec_dotProduct, h]
  congr 2
  ring
theorem siteReflect_apply (μ : Fin 4) (x : AmbientSpace) :
    (siteReflect μ).toFun x = x - (2 * x μ) • basisVec μ := by
  change InfiniteLattice.hyperplaneReflect (basisVec μ) 0 x = _
  have h : basisVec μ ⬝ᵥ basisVec μ = 1 := by rw [basisVec_dotProduct]; simp [basisVec]
  rw [InfiniteLattice.hyperplaneReflect, basisVec_dotProduct, h]
  congr 2
  ring
def linkReflectionForm (ν : unitPositiveClass) (μ : Fin 4)
    (F H : halfSpaceLocalObservables μ) : ℂ :=
  ∫ U, conj ((linkReflect μ).actOn (F : GaugeField (1 : ℝ) → ℂ) U) *
    (H : GaugeField (1 : ℝ) → ℂ) U ∂(ν : Measure (GaugeField (1 : ℝ)))
def siteReflectionForm (ν : unitPositiveClass) (μ : Fin 4)
    (F H : halfSpaceLocalObservables μ) : ℂ :=
  ∫ U, conj ((siteReflect μ).actOn (F : GaugeField (1 : ℝ) → ℂ) U) *
    (H : GaugeField (1 : ℝ) → ℂ) U ∂(ν : Measure (GaugeField (1 : ℝ)))
end YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
end

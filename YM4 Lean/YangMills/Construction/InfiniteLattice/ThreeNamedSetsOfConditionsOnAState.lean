import YangMills.Construction.InfiniteLattice.DataOfTheThreePictures
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAtAMirrorGivenWithANormal
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.LatticeConventions
open YangMills.Construction.InfiniteLattice (GaugeField IsShiftInvariant)
theorem sum_basisVector (μ : Direction) : ∑ κ, basisVector μ κ = 1 := by
  simp [basisVector]
theorem basisVector_not_isFaceDiagonalNormal (μ : Direction) :
    ¬ IsFaceDiagonalNormal (basisVector μ) := by
  rintro ⟨κ, ρ, -, h | h⟩
  · have := congrArg (fun x : Point => ∑ ι, x ι) h
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_basisVector] at this
    norm_num at this
  · have := congrArg (fun x : Point => ∑ ι, x ι) h
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_basisVector] at this
    norm_num at this
theorem add_basisVector_not_isAxialNormal (μ ρ : Direction) :
    ¬ IsAxialNormal (basisVector μ + basisVector ρ) := by
  rintro ⟨κ, h⟩
  have := congrArg (fun x : Point => ∑ ι, x ι) h
  simp only [Pi.add_apply, Finset.sum_add_distrib, sum_basisVector] at this
  norm_num at this
theorem sub_basisVector_not_isAxialNormal (μ ρ : Direction) :
    ¬ IsAxialNormal (basisVector μ - basisVector ρ) := by
  rintro ⟨κ, h⟩
  have := congrArg (fun x : Point => ∑ ι, x ι) h
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_basisVector] at this
  norm_num at this
namespace NormalHyperplane
variable {a : ℝ}
def antidiagonal (μ ρ : Direction) (hne : μ ≠ ρ) (c : ℝ) : NormalHyperplane :=
  ⟨basisVector μ - basisVector ρ, c, Or.inr ⟨μ, ρ, hne, Or.inr rfl⟩⟩
theorem axial_isLatticeMirror (μ : Direction) (q : ℤ) :
    (axial μ ((q : ℝ) * (a / 2))).IsLatticeMirror a :=
  ⟨fun _ => ⟨q, rfl⟩, fun h => absurd h (basisVector_not_isFaceDiagonalNormal μ)⟩
theorem diagonal_isLatticeMirror {μ ρ : Direction} (hne : μ ≠ ρ) (q : ℤ) :
    (diagonal μ ρ hne ((q : ℝ) * a)).IsLatticeMirror a :=
  ⟨fun h => absurd h (add_basisVector_not_isAxialNormal μ ρ), fun _ => ⟨q, rfl⟩⟩
theorem antidiagonal_isLatticeMirror {μ ρ : Direction} (hne : μ ≠ ρ) (q : ℤ) :
    (antidiagonal μ ρ hne ((q : ℝ) * a)).IsLatticeMirror a :=
  ⟨fun h => absurd h (sub_basisVector_not_isAxialNormal μ ρ), fun _ => ⟨q, rfl⟩⟩
end NormalHyperplane
open NormalHyperplane
variable {a : ℝ}
def PairConditions {μ ρ : Direction} (hne : μ ≠ ρ)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] : Prop :=
  IsShiftInvariant ν ∧
    (∀ q : ℤ, IsReflectionPositiveAcrossMirror (axial_isLatticeMirror (a := a) μ q) ν) ∧
      ∀ q : ℤ, IsReflectionPositiveAcrossMirror (diagonal_isLatticeMirror (a := a) hne q) ν
def IsReflectionPositiveAtEveryMirror (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] : Prop :=
  ∀ (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror a), IsReflectionPositiveAcrossMirror hQ ν
end YangMills.Construction.LatticeConventions
end

import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.ThreeNamedSetsOfConditionsOnAState
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing
open YangMills.Construction.InfiniteLattice (GaugeField IsShiftInvariant)
open YangMills.Construction.LatticeConventions (Direction NormalHyperplane IsAxialNormal
  IsFaceDiagonalNormal Point conjFun euclidDot basisVector)
open YangMills.Construction.LatticeConventions.NormalHyperplane (reflectSymmetry)
variable {a : ℝ}
theorem euclidDot_basisVector (μ : Direction) (x : Point) : euclidDot (basisVector μ) x = x μ := by
  simp [euclidDot, basisVector, Pi.single_apply]
theorem not_isFaceDiagonalNormal_basisVector (μ : Direction) :
    ¬ IsFaceDiagonalNormal (basisVector μ) := by apply _root_.YangMills.Construction.LatticeConventions.basisVector_not_isFaceDiagonalNormal <;> assumption
theorem not_isAxialNormal_of_isFaceDiagonalNormal {n : Point} (h : IsFaceDiagonalNormal n) :
    ¬ IsAxialNormal n := by
  rintro ⟨μ, rfl⟩
  exact not_isFaceDiagonalNormal_basisVector μ h
def reflectedPairing {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a) (ρ : BorelProb a)
    (F : GaugeField a → ℂ) : ℂ :=
  ρ.integral fun U => conjFun ((reflectSymmetry hQ).actOn F) U * F U
def IsLocallyReflectionPositive {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a)
    (ρ : BorelProb a) : Prop :=
  ∀ F ∈ locallyMeasurableIn a Q.upperHalfSpace, 0 ≤ reflectedPairing hQ ρ F
def IsFullyReflectionPositive {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a)
    (ρ : BorelProb a) : Prop :=
  (∀ F ∈ boundedMeasurableIn a Q.upperHalfSpace, 0 ≤ reflectedPairing hQ ρ F) ∧
    ∀ F ∈ boundedMeasurableIn a Q.lowerHalfSpace, 0 ≤ reflectedPairing hQ ρ F
def reflectionPositiveSet (a : ℝ) : Set (BorelProb a) :=
  {ρ | IsShiftInvariant ρ.1 ∧
    ∀ (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror a), IsLocallyReflectionPositive hQ ρ}
end YangMills.Construction.GibbsAtFixedSpacing
end

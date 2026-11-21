import YangMills.Construction.Lattice.AdicGridPoints
import YangMills.Construction.ReflectionPositivity.SixteenFamiliesOfMirrors
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
open scoped ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.SeparatedTuples
open InfiniteLattice (AmbientSpace latticeSubgroup)
open Mirrors (ReflectingHyperplane diagonalNormals)
open PeriodicLattice (adicGridPoints meshSize)
abbrev latticeSpacing (L : ℕ) (K : ℕ+) : ℝ := meshSize L ((K : ℕ) : ℤ)
abbrev scaleLattice (L : ℕ) (K : ℕ+) : AddSubgroup AmbientSpace :=
  latticeSubgroup (latticeSpacing L K)
def posAdicGridPoints (L : ℕ) : Set ℝ := adicGridPoints L ∩ Set.Ioi 0
def halfAdicGridPoints (L : ℕ) : Set ℝ := {c | ∃ d ∈ adicGridPoints L, c = d / 2}
def IsAdicPlaced (L : ℕ) (H : ReflectingHyperplane) : Prop :=
  (H.offset ∈ halfAdicGridPoints L ∧ H.HasAxialNormal) ∨
    (H.offset ∈ adicGridPoints L ∧ H.normalVec ∈ diagonalNormals)
end YangMills.Construction.SeparatedTuples

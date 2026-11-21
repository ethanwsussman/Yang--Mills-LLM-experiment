import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace NormalFamilies
open InfiniteLattice
structure MirrorLadder where
  normal : AmbientSpace
  normal_mem : normal ∈ normalSet
  offset : ℝ
  offset_allowed : IsAllowedLevel 1 normal offset
  spacing : ℤ
  even_spacing : Even spacing
  two_le_spacing : 2 ≤ spacing
namespace MirrorLadder
variable (L : MirrorLadder)
def rungs : Set (NormalLevelPair 1) :=
  {P | P.normal = L.normal ∧ ∃ k : ℤ, P.level = L.offset + (k : ℝ) * (L.spacing : ℝ)}
def slab (k : ℤ) : Set AmbientSpace :=
  {x | L.offset + (k : ℝ) * (L.spacing : ℝ) ≤ L.normal ⬝ᵥ x ∧
    L.normal ⬝ᵥ x ≤ L.offset + ((k : ℝ) + 1) * (L.spacing : ℝ)}
end MirrorLadder
end NormalFamilies
end YangMills.Construction

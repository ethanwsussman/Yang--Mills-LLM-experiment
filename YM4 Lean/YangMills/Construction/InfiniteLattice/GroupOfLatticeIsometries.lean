import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace LatticeSymmetryGroup
open TorusMetric (euclidNormVec)
def motionPerms (a : ℝ) : Set (Equiv.Perm AmbientSpace) :=
  {g | ⇑g ∈ affineHyperoctahedralMaps a}
def shiftPerms (a : ℝ) : Set (Equiv.Perm AmbientSpace) :=
  {g | ∃ v : LatticePoint a, ⇑g = (shift v).toFun}
def hyperoctahedralPerms : Set (Equiv.Perm AmbientSpace) :=
  {g | ∃ w ∈ hyperoctahedralLinearGroup, ⇑g = ⇑w}
def IsometryIffMotion (a : ℝ) : Prop :=
  ∀ r : AmbientSpace → AmbientSpace,
    ((∀ x y, euclidNormVec (r x - r y) = euclidNormVec (x - y)) ∧
        r '' (latticeSubgroup a : Set AmbientSpace) = latticeSubgroup a) ↔
      ∃ w ∈ hyperoctahedralLinearGroup, ∃ v : LatticePoint a, ∀ x, r x = w x + v
def MotionPartsUnique (a : ℝ) : Prop :=
  ∀ w ∈ hyperoctahedralLinearGroup, ∀ w' ∈ hyperoctahedralLinearGroup, ∀ v v' : LatticePoint a,
    (∀ x, w x + (v : AmbientSpace) = w' x + (v' : AmbientSpace)) → w = w' ∧ v = v'
def MotionBijective (a : ℝ) : Prop :=
  ∀ f ∈ affineHyperoctahedralMaps a, Function.Bijective f
def MotionSemidirect (a : ℝ) : Prop :=
  ∃ G N H : Subgroup (Equiv.Perm AmbientSpace),
    (G : Set (Equiv.Perm AmbientSpace)) = motionPerms a ∧
    (N : Set (Equiv.Perm AmbientSpace)) = shiftPerms a ∧
    (H : Set (Equiv.Perm AmbientSpace)) = hyperoctahedralPerms ∧
    N ≤ G ∧ H ≤ G ∧ (N.subgroupOf G).Normal ∧
    Subgroup.IsComplement' (N.subgroupOf G) (H.subgroupOf G)
def MotionShiftLinearDecomp (a : ℝ) : Prop :=
  ∀ g ∈ motionPerms a, ∃! p : LatticePoint a × hyperoctahedralLinearGroup,
    ⇑g = (shift p.1).toFun ∘ ⇑(p.2 : AmbientSpace ≃ₗ[ℝ] AmbientSpace)
def SymmetryGroupStatement : Prop :=
  ∀ a : ℝ, 0 < a →
    IsometryIffMotion a ∧ MotionPartsUnique a ∧ MotionBijective a ∧
      MotionSemidirect a ∧ MotionShiftLinearDecomp a
end LatticeSymmetryGroup
end InfiniteLattice
end YangMills.Construction
end

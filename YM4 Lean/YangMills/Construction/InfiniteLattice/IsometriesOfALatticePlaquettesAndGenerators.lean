import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import YangMills.Construction.ReflectionPositivity.SixteenFamiliesOfMirrors
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def permuteCoords (σ : Equiv.Perm (Fin 4)) : AmbientSpace ≃ₗ[ℝ] AmbientSpace :=
  LinearEquiv.funCongrLeft ℝ ℝ σ.symm
def signedPermutationGroup : Subgroup (AmbientSpace ≃ₗ[ℝ] AmbientSpace) :=
  Subgroup.closure (range permuteCoords ∪ (signFlipGroup : Set (AmbientSpace ≃ₗ[ℝ] AmbientSpace)))
def shiftsAndMirrorReflections (a : ℝ) : Set (Equiv.Perm AmbientSpace) :=
  {g | (∃ v : LatticePoint a, ⇑g = (shift v).toFun) ∨
    ∃ H : Mirrors.ReflectingHyperplane, H.IsLatticeSymmetric a ∧ ⇑g = H.reflect}
def SymmetriesFacesAndGenerators.Claim : Prop :=
  ∀ a : ℝ, 0 < a →
    (∀ f : AmbientSpace →ₗ[ℝ] AmbientSpace,
      (∃ w ∈ signedPermutationGroup, ⇑w = ⇑f) ↔ BijOn f signedUnitVectors signedUnitVectors) ∧
    signedPermutationGroup = hyperoctahedralLinearGroup ∧
    (∀ s : AmbientSpace → AmbientSpace,
      (∃ r : LatticeSymmetry a, r.toFun = s) ↔ s ∈ affineHyperoctahedralMaps a) ∧
    (∀ (r : LatticeSymmetry a) (p : ElementaryPlaquette a),
      (∃! q : ElementaryPlaquette a, q.cornerSet = r.pointMap '' p.cornerSet) ∧
      (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet ∧
      (r.plaquetteMap p).center = r.toFun p.center ∧
      r.actOn (fun U : GaugeField a => faceEnergy U p) =
        fun U : GaugeField a => faceEnergy U (r.plaquetteMap p)) ∧
    (∀ r : LatticeSymmetry a,
      ∃ g ∈ Subgroup.closure (shiftsAndMirrorReflections a), ⇑g = r.toFun) ∧
    ∀ g ∈ Subgroup.closure (shiftsAndMirrorReflections a),
      ∃ r : LatticeSymmetry a, r.toFun = ⇑g
end InfiniteLattice
end YangMills.Construction

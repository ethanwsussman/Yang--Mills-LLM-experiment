import YangMills.Construction.InfiniteLattice.ReflectionInALatticeMirrorGivenWithANormal
import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import Mathlib
set_option autoImplicit false
open YangMills.Construction.NormalFamilies YangMills.Construction.LatticeConventions
open scoped ComplexConjugate Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def LatticeMirrorNaming.Statement : Prop :=
  ∀ a : ℝ, 0 < a →
    (∀ P : NormalLevelPair a,
      (∃ r : LatticeSymmetry a, r.toFun = reflectAcross P.normal P.level) ∧
      reflectAcross P.normal P.level ∘ reflectAcross P.normal P.level = id) ∧
    (∀ (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror a),
      ∃ (P : NormalLevelPair a) (ς : ℤˣ),
        ((Q.normal ∈ normalSet ∧ P.normal = Q.normal ∧ P.level = Q.level ∧ ς = 1) ∨
          (Q.normal ∉ normalSet ∧ P.normal = -Q.normal ∧ P.level = -Q.level ∧ ς = -1)) ∧
        Q.carrier = {x | P.normal ⬝ᵥ x = P.level} ∧
        Q.reflect = reflectAcross P.normal P.level ∧
        (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
          (fun U => conj ((NormalHyperplane.reflectSymmetry hQ).actOn F U)) =
            P.conjReflectObservable F) ∧
        regionObservables a Q.upperHalfSpace = halfSpaceObservables a P.normal P.level ς ∧
        regionObservables a Q.lowerHalfSpace = halfSpaceObservables a P.normal P.level (-ς)) ∧
    ∀ P : NormalLevelPair a,
      ∃ Q : NormalHyperplane, Q.normal = P.normal ∧ Q.level = P.level ∧
        Q.IsLatticeMirror a
end YangMills.Construction.InfiniteLattice
end

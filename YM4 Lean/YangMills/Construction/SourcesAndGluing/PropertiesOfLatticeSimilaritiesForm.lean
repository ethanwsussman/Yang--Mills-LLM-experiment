import YangMills.Construction.SourcesAndGluing.PredicatesOfLatticeSimilarities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def ScaledMotionPropertiesClaim : Prop :=
  ∀ (S : GluingSetup) (n : ScaleExponent S) (φ : ScaledLatticeMotion n),
    φ.IsDilatingBijectionOfSpace ∧ φ.IsDilatingBijectionOfTori ∧
      φ.RotationDetermined ∧ φ.InvIsScaledMotion ∧
      φ.CompIsScaledMotion ∧
      φ.MapsLinksOfSpace ∧ φ.MapsLinksOfTori ∧
      φ.MapsPlaquettesOfSpace ∧ φ.MapsPlaquettesOfTori ∧
      φ.PullsFieldsOfSpace ∧ φ.PullsFieldsOfTori ∧
      φ.PullsObservablesOfSpace ℝ ∧ φ.PullsObservablesOfSpace ℂ ∧
      φ.PullsObservablesOfTori ℝ ∧ φ.PullsObservablesOfTori ℂ ∧
      φ.PreservesAction ∧ φ.PreservesMeasures ∧ φ.CommutesWithLift
end YangMills.Construction.SourcesAndGluing
end

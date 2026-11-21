import YangMills.Construction.ReflectionPositivity.CentredFunctionalsAlongAConvergentSequence
import YangMills.Construction.ReflectionPositivity.InstancesOfTheInequalityAtAMirror
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq
variable {D : MirrorData}
def lipLimitCenteredFunctional (S : LatticeDataSeq D torus)
    (X : sepLipTuples D) : ℝ :=
  YangMills.Construction.LimitSpaces.Ambient.periodic.centredSum D.toStandingParameters
    S.lipLimitFamily ⟨X.1.get, X.2⟩
def PositivityPassesToLimit : Prop :=
  (∀ (D : MirrorData) (E : Ambient) (S : LatticeDataSeq D E) (T : FunctionalFamily D E),
    S.TendsToFamily T → ∀ (μ : Fin 4) (h : ℝ),
      h ∈ YangMills.Construction.LimitSpaces.edgeMidCoordsAll D.toStandingParameters →
      ∀ I : (CoordMirror.mk μ h).PositivityInstance D E, I.HoldsReal T.centeredFunctional) ∧
  ∀ (D : MirrorData) (S : LatticeDataSeq D torus) (T : FunctionalFamily D torus),
    S.TendsToFamily T → ∀ (μ : Fin 4) (h : ℝ),
      h ∈ YangMills.Construction.LimitSpaces.edgeMidCoordsAll D.toStandingParameters →
      S.LipLimitsExist →
      ∀ I : (CoordMirror.mk μ h).LipPositivityInstance D,
        I.HoldsReal S.lipLimitCenteredFunctional
end YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq
end

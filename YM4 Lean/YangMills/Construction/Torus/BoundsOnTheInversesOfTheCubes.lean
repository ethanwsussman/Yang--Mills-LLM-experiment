import YangMills.Construction.Torus.ApproximateInverseAndRemainderOfTheCubes
import YangMills.Construction.Torus.FloorOfTheInverseBounds
import YangMills.Construction.Torus.TermsOfTheChangeOfTheSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus
def CubeInverseBounds : Prop :=
  ∀ (S : CubeGaugeSetting) (m K t : ℕ), S.IsExpansionSetting m K t →
    S.ChangeAboveThresholds → ∀ Q ∈ S.chain.allCubes,
      IsUnit (S.compress (S.bondsIn Q) (S.cubeGreen Q)) ∧
      ∀ b ∈ S.bondsIn Q, ∀ b' ∈ S.bondsIn Q,
        |S.matrixEntry (S.localInverse Q) b b'| ≤
          2 * (SeparatedSequences.compressedGreenLowerBound 4 1)⁻¹ * (GaugeSetting.coarseSpacing b)⁻¹ *
            (GaugeSetting.coarseSpacing b')⁻¹ *
            Real.exp (-InverseBounds.decayRateOfInverse S.data.L * GaugeSetting.coarseDist b b')
end YangMills.Construction.GeneralTorus
end

import YangMills.Construction.Torus.TermsOfTheChangeOfTheSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus
def LocalChainChangeBondSumBound : Prop :=
  ∀ (S : CubeGaugeSetting) (m K t : ℕ), S.IsExpansionSetting m K t →
    S.ChangeAboveThresholds → ∀ Q ∈ S.chain.allCubes, ∀ b ∈ S.bondsIn Q,
    ∀ b'' ∈ S.bondsIn Q, ∀ f'' : (S.localSetting Q).CoarseBond,
      GaugeSetting.levelBond f'' = GaugeSetting.levelBond b'' →
      |∑ᶠ b₁ ∈ S.changeBonds Q, S.changeTerm Q
          (S.greenOp (S.meanOpAdjoint (S.coarseDelta b))).1
          ((S.localSetting Q).greenOp
            ((S.localSetting Q).meanOpAdjoint ((S.localSetting Q).coarseDelta f''))).1 b₁| ≤
      18 * 4 *
          SeparatedSequences.compressedEntryConstant 4 S.data.L
            (GreenBounds.chosen S.data.L).rate
            (GreenBounds.chosen S.data.L).bound ^ 2 *
          (ScaleData.cubeScale Q)⁻¹ * S.changeSiteSum Q b b''
end YangMills.Construction.GeneralTorus
end

import YangMills.Construction.Torus.TermsOfTheChangeOfTheSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.GeneralTorus
def LocalChainChange : Prop :=
  ∀ (S : CubeGaugeSetting) (m K t : ℕ), S.IsExpansionSetting m K t →
    S.ChangeAboveThresholds → ∀ Q ∈ S.chain.allCubes, ∀ b ∈ S.bondsIn Q, ∀ b'' ∈ S.bondsIn Q,
      ∃ (f f'' : (S.localSetting Q).CoarseBond),
        GaugeSetting.levelBond f = GaugeSetting.levelBond b ∧
        GaugeSetting.levelBond f'' = GaugeSetting.levelBond b'' ∧
        (GaugeSetting.coarseSpacing b ^ 4 *
            ((S.localSetting Q).kernelEntry (S.localSetting Q).coarseGreen f f'' -
              S.kernelEntry S.coarseGreen b b'') =
          S.data.plaquetteInner
              (S.data.plaquetteCurl (S.greenOp (S.meanOpAdjoint (S.coarseDelta b))).1)
              (S.data.leibnizTerm (ScaleData.cutoffOnSites Q)
                ((S.localSetting Q).greenOp
                  ((S.localSetting Q).meanOpAdjoint ((S.localSetting Q).coarseDelta f''))).1) -
            S.data.plaquetteInner
              (S.data.leibnizTerm (ScaleData.cutoffOnSites Q)
                (S.greenOp (S.meanOpAdjoint (S.coarseDelta b))).1)
              (S.data.plaquetteCurl ((S.localSetting Q).greenOp
                ((S.localSetting Q).meanOpAdjoint ((S.localSetting Q).coarseDelta f''))).1) +
            ∑ᶠ b₁ ∈ S.changeBonds Q, S.changeTerm Q
              (S.greenOp (S.meanOpAdjoint (S.coarseDelta b))).1
              ((S.localSetting Q).greenOp
                ((S.localSetting Q).meanOpAdjoint ((S.localSetting Q).coarseDelta f''))).1 b₁) ∧
        (S.unityWeight Q b'' ≠ 0 →
          (GaugeSetting.coarseSpacing b)⁻¹ * (GaugeSetting.coarseSpacing b'')⁻¹ *
              |(S.localSetting Q).matrixEntry (S.localSetting Q).coarseGreen f f'' -
                S.matrixEntry S.coarseGreen b b''| ≤
            S.changeBound b b'')
end YangMills.Construction.GeneralTorus
end

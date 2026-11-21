import YangMills.Construction.SeparatedSequences.ExplicitConstants
import YangMills.Construction.Torus.CubesPartitionOfUnityAndCutSequencesOnAGeneralTorus
import YangMills.Construction.Torus.SettingOfTheExpansionOnThePhysicalTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace GaugeSetting
def levelBond {W : GaugeSetting} (e : W.CoarseBond) :
    Σ k : Fin (W.data.lastLevel + 1), W.data.PosBond k :=
  ⟨e.1, e.2.1⟩
theorem levelBond_injective {W : GaugeSetting} : Function.Injective (levelBond (W := W)) := by
  rintro ⟨k, b, hb⟩ ⟨k', b', hb'⟩ heq
  simp only [levelBond, Sigma.mk.injEq] at heq
  obtain ⟨rfl, heq⟩ := heq
  obtain rfl := eq_of_heq heq
  rfl
end GaugeSetting
namespace CubeGaugeSetting
variable (S : CubeGaugeSetting)
def localBondsIn (Q : S.data.CubeIndex) : Set (S.localSetting Q).CoarseBond :=
  {e' | ∃ e ∈ S.bondsIn Q, GaugeSetting.levelBond e' = GaugeSetting.levelBond e}
open Classical in
def toLocal (Q : S.data.CubeIndex) : S.CoarseField →ₗ[ℝ] (S.localSetting Q).CoarseField where
  toFun u e' :=
    if h : ∃ e ∈ S.bondsIn Q, GaugeSetting.levelBond e' = GaugeSetting.levelBond e then
      u h.choose else 0
  map_add' u v := by
    funext e'
    by_cases h : ∃ e ∈ S.bondsIn Q, GaugeSetting.levelBond e' = GaugeSetting.levelBond e
    · simp only [Pi.add_apply, dif_pos h]
    · simp only [Pi.add_apply, dif_neg h, add_zero]
  map_smul' r u := by
    funext e'
    by_cases h : ∃ e ∈ S.bondsIn Q, GaugeSetting.levelBond e' = GaugeSetting.levelBond e
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, dif_pos h]
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, dif_neg h, mul_zero]
open Classical in
def fromLocal (Q : S.data.CubeIndex) : (S.localSetting Q).CoarseField →ₗ[ℝ] S.CoarseField where
  toFun v e :=
    if h : e ∈ S.bondsIn Q ∧
        ∃ e' : (S.localSetting Q).CoarseBond, GaugeSetting.levelBond e' = GaugeSetting.levelBond e then
      v h.2.choose
    else 0
  map_add' u v := by
    funext e
    by_cases h : e ∈ S.bondsIn Q ∧
      ∃ e' : (S.localSetting Q).CoarseBond, GaugeSetting.levelBond e' = GaugeSetting.levelBond e
    · simp only [Pi.add_apply, dif_pos h]
    · simp only [Pi.add_apply, dif_neg h, add_zero]
  map_smul' r u := by
    funext e
    by_cases h : e ∈ S.bondsIn Q ∧
      ∃ e' : (S.localSetting Q).CoarseBond, GaugeSetting.levelBond e' = GaugeSetting.levelBond e
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, dif_pos h]
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, dif_neg h, mul_zero]
def cubeGreen (Q : S.data.CubeIndex) : Module.End ℝ S.CoarseField :=
  S.fromLocal Q ∘ₗ (S.localSetting Q).coarseGreen ∘ₗ S.toLocal Q
end CubeGaugeSetting
def CubeGreenCompression : Prop :=
  ∀ (S : CubeGaugeSetting) (m K t : ℕ), S.IsExpansionSetting m K t →
    ∀ Q ∈ S.chain.allCubes,
      (∀ e ∈ S.bondsIn Q, ∃ e' : (S.localSetting Q).CoarseBond,
        GaugeSetting.levelBond e' = GaugeSetting.levelBond e ∧
          GaugeSetting.coarseLevel e' = GaugeSetting.coarseLevel e ∧
          GaugeSetting.coarseSpacing e' = GaugeSetting.coarseSpacing e ∧
          GaugeSetting.coarseAnchor e' = GaugeSetting.coarseAnchor e) ∧
      (∀ u ∈ S.supportedOn (S.bondsIn Q),
        S.toLocal Q u ∈ (S.localSetting Q).supportedOn (S.localBondsIn Q) ∧
          S.fromLocal Q (S.toLocal Q u) = u) ∧
      (∀ v ∈ (S.localSetting Q).supportedOn (S.localBondsIn Q),
        S.fromLocal Q v ∈ S.supportedOn (S.bondsIn Q) ∧
          S.toLocal Q (S.fromLocal Q v) = v) ∧
      (∀ u ∈ S.supportedOn (S.bondsIn Q), ∀ u' ∈ S.supportedOn (S.bondsIn Q),
        (S.localSetting Q).coarseInner (S.toLocal Q u) (S.toLocal Q u') = S.coarseInner u u') ∧
      (∀ u u', S.coarseInner (S.cubeGreen Q u) u' =
        S.coarseInner u (S.cubeGreen Q u')) ∧
      (∀ B ∈ S.supportedOn (S.bondsIn Q),
        SeparatedSequences.compressedGreenLowerBound 4 1 * S.coarseL2Norm (S.spacingMul B) ^ 2 ≤
            (S.localSetting Q).coarseInner (S.toLocal Q B)
              ((S.localSetting Q).coarseGreen (S.toLocal Q B)) ∧
          (S.localSetting Q).coarseInner (S.toLocal Q B)
              ((S.localSetting Q).coarseGreen (S.toLocal Q B)) ≤
            S.coarseL2Norm (S.spacingMul B) ^ 2) ∧
      (∀ B ∈ S.supportedOn (S.bondsIn Q), B ≠ 0 →
        0 < S.coarseInner B (S.cubeGreen Q B))
end YangMills.Construction.GeneralTorus

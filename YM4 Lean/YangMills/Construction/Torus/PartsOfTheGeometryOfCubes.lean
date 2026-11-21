import YangMills.Construction.SeparatedSequences.InverseExpansionCutoff
import YangMills.Construction.Torus.CubesPartitionOfUnityAndCutSequencesOnAGeneralTorus
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.GeneralTorus.CubeGaugeSetting
variable (C : CubeGaugeSetting)
def LevelsNearCube (Q : C.data.CubeIndex) : Prop :=
  ScaleData.scaledCube Q 2 ∩ C.chain.set (Q.1 + 2) = ∅ ∧
  (1 ≤ Q.1 → ScaleData.cubeSet Q ⊆ C.chain.set (Q.1 - 1)) ∧
  (∀ m : ℕ, ∀ y ∈ C.chain.shellSites m ∩ ScaleData.cubeSet Q, Q.1 ≤ m + 1 ∧ m ≤ Q.1 + 1) ∧
  ∀ c : C.CoarseBond, (ScaleData.bondSupport c.2.1 ∩ ScaleData.scaledCube Q 2).Nonempty →
    GaugeSetting.coarseLevel c ≤ Q.1 + 1
def CoarsePartitionOfUnity : Prop :=
  ∀ c : C.CoarseBond,
    1 ≤ ∑ᶠ Q' ∈ C.chain.allCubes, C.coarseBump Q' c ^ 2 ∧
    {Q' ∈ C.chain.allCubes | C.coarseBump Q' c ≠ 0}.encard ≤ 3 * 2 ^ 4 ∧
    ∑ᶠ Q' ∈ C.chain.allCubes, C.unityWeight Q' c ^ 2 = 1 ∧
    ∀ Q' ∈ C.chain.allCubes, 0 ≤ C.unityWeight Q' c ∧ C.unityWeight Q' c ≤ 1
def UnityWeightLocalLipschitz (Q : C.data.CubeIndex) : Prop :=
  C.unityMul Q = C.cubeIndicator Q ∘ₗ C.unityMul Q ∧
  ∀ c c' : C.CoarseBond, |C.unityWeight Q c - C.unityWeight Q c'| ≤
    SeparatedSequences.partitionOfUnityLipschitzConstant 4 C.data.L *
      (C.data.blockCount : ℝ)⁻¹ * GaugeSetting.coarseDist c c'
def LocalSetsAgreeNearCube (Q : C.data.CubeIndex) : Prop :=
  (∃ B', C.chain.IsLocalization Q B') ∧
  ∀ m ≤ C.data.lastLevel, ∀ x : C.data.BaseSite, (x : C.data.Space) ∈ ScaleData.scaledCube Q 2 →
    ((x : C.data.Space) ∈ C.chain.localSet Q m ↔ (x : C.data.Space) ∈ C.chain.set m)
def LocalObjectsAgreeNearCube (Q : C.data.CubeIndex) : Prop :=
  (∀ b : C.data.BaseBond, (b.1.src : C.data.Space) ∈ ScaleData.scaledCube Q 2 →
    (b.1.tgt : C.data.Space) ∈ ScaleData.scaledCube Q 2 →
      (b ∈ C.bondSet ↔ b ∈ (C.localSetting Q).bondSet)) ∧
  (∀ (m : Fin (C.data.lastLevel + 1)) (c : C.data.PosBond m),
    (c.1.src : C.data.Space) ∈ ScaleData.scaledCube Q 2 →
    (c.1.tgt : C.data.Space) ∈ ScaleData.scaledCube Q 2 →
      (c ∈ C.coarseBondsAt m ↔ c ∈ (C.localSetting Q).coarseBondsAt m) ∧
      ∀ (h : c ∈ C.coarseBondsAt m) (h' : c ∈ (C.localSetting Q).coarseBondsAt m),
        GaugeSetting.coarseAnchor (W := C.toGaugeSetting) ⟨m, c, h⟩ =
          GaugeSetting.coarseAnchor (W := (C.localSetting Q).toGaugeSetting) ⟨m, c, h'⟩) ∧
  ∀ m ≤ C.data.lastLevel, ∀ y ∈ C.data.levelSublattice m, y ∈ ScaleData.scaledCube Q 2 →
    (y ∈ C.chain.shellSites m ↔ y ∈ (C.chain.localization Q).shellSites m)
def BondSupportsNearCube (Q : C.data.CubeIndex) : Prop :=
  (∀ (m : Fin (C.data.lastLevel + 1)) (c : C.data.PosBond m),
    (c ∈ C.coarseBondsAt m ∨ c ∈ (C.localSetting Q).coarseBondsAt m) →
    (ScaleData.bondSupport c ∩ ScaleData.scaledCube Q (5 / 3 + 1 / 12)).Nonempty →
      ScaleData.bondSupport c ⊆ ScaleData.scaledCube Q 2) ∧
  ∀ c ∈ C.bondsIn Q, ScaleData.bondSupport c.2.1 ⊆ ScaleData.scaledCube Q (4 / 3)
def DistancesNearCube (Q : C.data.CubeIndex) : Prop :=
  (∀ x x' : C.data.Space, C.chain.scaledDist x x' ≤
    (C.chain.localization Q).scaledDist x x') ∧
  ∀ (x x' : C.data.Space) (r r' : ℝ), torusSupNorm (x - Q.2) ≤ r * ScaleData.cubeScale Q →
    r' * ScaleData.cubeScale Q ≤ torusSupNorm (x' - Q.2) → r < r' → r' ≤ 2 →
      (r' - r) * (C.data.blockCount : ℝ) / (C.data.L : ℝ) ≤ C.chain.scaledDist x x'
end YangMills.Construction.GeneralTorus.CubeGaugeSetting

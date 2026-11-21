import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeparatedClasses
namespace SingleSequence.SequenceData
variable (s : SequenceData)
structure Requirements : Prop where
  isSeparated : (s.Ω 0).Nonempty ∧
    SeparatedSequences.IsSeparatedSequence s.data.scales (s.data.gapSize : ℝ) s.Ω
  separatedOnTorus : s.L_le_blockSize → Torus.IsSeparatedChain s.data.L s.mesh
    s.data.blockSize s.data.gapSize s.data.t (s.regionOn s.unitTorusSide)
  exists_blockSetting : s.L_le_blockSize → ∃ 𝒮, s.IsBlockSetting 𝒮
  exists_weightedTorus : s.L_le_blockSize → ∃ D B, s.IsWeightedTorus D B
  exists_nestedRegions : ∃ 𝒮, s.IsNestedRegions 𝒮
  exists_gaugeSetting : ∃ W, s.IsGaugeSetting W
  blockSetting_geometry : ∀ 𝒮, s.IsBlockSetting 𝒮 → s.BlockSettingGeometry 𝒮
  weightedTorus_geometry : ∀ D B, s.IsWeightedTorus D B → s.WeightedGeometry B
  nestedRegions_geometry : ∀ 𝒮, s.IsNestedRegions 𝒮 → s.NestedGeometry 𝒮
  gaugeSetting_geometry : ∀ W, s.IsGaugeSetting W → s.GaugeGeometry W
  unitMassWeights : s.WeightsAtUnitMass
  blockSetting_scalarData : ∀ 𝒮, s.IsBlockSetting 𝒮 →
    s.scalarData.Corresponds (scalarDataOfBlockSetting 𝒮) (s.toTorus s.unitTorusSide)
  weightedTorus_scalarData : ∀ D B, s.IsWeightedTorus D B →
    s.scalarData.Corresponds (scalarDataOfWeighted B) (s.toTorus D.side)
  nestedRegions_scalarData : ∀ 𝒮, s.IsNestedRegions 𝒮 →
    s.scalarData.Corresponds (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side)
  weightedTorus_projections : ∀ D B, s.IsWeightedTorus D B → s.WeightedProjections B
  nestedRegions_projections : ∀ 𝒮, s.IsNestedRegions 𝒮 → s.NestedProjections 𝒮
  gaugeSetting_projection : ∀ W, s.IsGaugeSetting W → s.GaugeProjection W
  classOneForms_eq : OneFormData.Corresponds s.oneFormData.toOneFormData s.classOneForms id
  expansionSetAt_eq : ∀ n ≤ s.data.t,
    s.data.expansionSetAt s.Ω s.frame n = s.params.layerBondSet s.Ω s.frame n
  nestedRegions_oneFormData : ∀ 𝒮, s.IsNestedRegions 𝒮 →
    s.oneFormData.Corresponds (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side)
  gaugeSetting_oneFormData : ∀ W, s.IsGaugeSetting W →
    s.oneFormData.Corresponds (oneFormDataOfGauge W) (s.toTorus W.data.torusSide)
  nestedRegions_massForm : ∀ 𝒮, s.IsNestedRegions 𝒮 → s.NestedMassForm 𝒮
  gaugeSetting_coarseOperators : ∀ W, s.IsGaugeSetting W → s.GaugeCoarseOperators W
  nestedRegions_anchors : ∀ 𝒮, s.IsNestedRegions 𝒮 → s.NestedAnchors 𝒮
  gaugeSetting_anchors : ∀ W, s.IsGaugeSetting W → s.GaugeAnchors W
end SingleSequence.SequenceData
open SingleSequence
def SingleSequenceObjectsAgree : Prop :=
  (∀ s : SequenceData, s.Requirements) ∧
    ∀ L : ℕ, Blocking.DimFourOddBlockingFactorGeThirteen 4 L →
      ∀ c : Propagator.PropagatorConstants, c.ValidFor L → (L : ℝ) ≤ c.blockLower →
        (torusGreenConstants c).Valid L
end YangMills.Construction.SeparatedClasses

import YangMills.Construction.SeparatedSequences.ClassBasePointsInASettingOfRegions
import YangMills.Construction.SeparatedSequences.ClassBasePointsOnAGeneralTorus
import YangMills.Construction.SeparatedSequences.ClassExpansionOperatorsOnAGeneralTorus
import YangMills.Construction.SeparatedSequences.ClassExpansionsAgreeWithSymbols
import YangMills.Construction.SeparatedSequences.ClassExpansionsInASettingOfRegions
import YangMills.Construction.SeparatedSequences.ClassExpansionsOnAGeneralTorus
import YangMills.Construction.SeparatedSequences.ClassFormsAgreeWithDefiningForms
import YangMills.Construction.SeparatedSequences.ClassGeometryInASettingOfRegions
import YangMills.Construction.SeparatedSequences.ClassGeometryInASettingOfTheTorusOfLevelSide
import YangMills.Construction.SeparatedSequences.ClassGeometryInWeightedData
import YangMills.Construction.SeparatedSequences.ClassGeometryOnAGeneralTorus
import YangMills.Construction.SeparatedSequences.ClassProjectionOnAGeneralTorus
import YangMills.Construction.SeparatedSequences.ClassProjectionsInASettingOfRegions
import YangMills.Construction.SeparatedSequences.ClassProjectionsInWeightedData
import YangMills.Construction.SeparatedSequences.ClassSequenceHasASettingOfRegions
import YangMills.Construction.SeparatedSequences.ClassSequenceHasASettingOfTheTorusOfLevelSide
import YangMills.Construction.SeparatedSequences.ClassSequenceHasASettingOnAGeneralTorus
import YangMills.Construction.SeparatedSequences.ClassSequenceHasWeightedData
import YangMills.Construction.SeparatedSequences.ClassSequenceIsSeparatedForItsNumbers
import YangMills.Construction.SeparatedSequences.ClassSequenceIsSeparatedOnTheTorusOfLevelSide
import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInASettingOfRegions
import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInASettingOfTheTorusOfLevelSide
import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInWeightedData
import YangMills.Construction.SeparatedSequences.ClassWeightInASettingOfRegions
import YangMills.Construction.SeparatedSequences.NumbersOfThePropagatorServeOnTheTori
import YangMills.Construction.SeparatedSequences.OneSequenceOneSetOfObjects
import YangMills.Construction.SeparatedSequences.WeightsOfAClassSequenceAtOne
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SeparatedClasses
theorem SingleSequenceObjectsAgree.proof
    (h1 : IsSeparatedForOwnParameters)
    (h2 : IsSeparatedOnUnitTorus)
    (h3 : SingleSequence.ExistsBlockSetting)
    (h4 : ExistsWeightedTorus)
    (h5 : SingleSequence.ExistsNestedRegions)
    (h6 : ExistsGaugeSetting)
    (h7 : BlockGeometryOfClass.Statement)
    (h8 : WeightedGeometryOfClass.Statement)
    (h9 : NestedGeometryOfClass.Statement)
    (h10 : GaugeGeometryOfClass.Statement)
    (h11 : UnitMassWeightsStatement)
    (h12 : ScalarDataOfBlockSettingCorresponds)
    (h13 : ScalarDataOfWeightedCorresponds)
    (h14 : ScalarDataOfNestedCorresponds)
    (h15 : WeightedProjectionsOfClass.Statement)
    (h16 : NestedProjectionsOfClass.Statement)
    (h17 : GaugeProjectionOfClass.Statement)
    (h18 : ClassOneFormsOfParameters.Statement)
    (h19 : SingleSequence.ExpansionSetAtEqLayerBonds)
    (h20 : SingleSequence.NestedOneFormsCorrespond)
    (h21 : SingleSequence.GaugeOneFormsCorrespond)
    (h22 : NestedMassFormHolds)
    (h23 : GaugeCoarseOperatorsOfClass.Statement)
    (h24 : SingleSequence.NestedAnchorsOfClass)
    (h25 : GaugeAnchorsOfClass.Statement)
    (h26 : PropagatorConstantsServeOnTori) :
    SingleSequenceObjectsAgree := by
  unfold SingleSequenceObjectsAgree
  exact ⟨fun s => ⟨h1 s, h2 s, h3 s, h4 s, h5 s, h6 s, h7 s, h8 s, h9 s, h10 s, h11 s, h12 s, h13 s, h14 s, h15 s, h16 s, h17 s, h18 s, h19 s, h20 s, h21 s, h22 s, h23 s, h24 s, h25 s⟩, h26⟩
end YangMills.Construction.SeparatedClasses

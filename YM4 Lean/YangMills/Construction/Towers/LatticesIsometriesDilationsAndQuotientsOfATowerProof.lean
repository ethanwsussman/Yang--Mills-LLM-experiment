import YangMills.Construction.Towers.DilationCarriesObjectsAtAStepOfASide
import YangMills.Construction.Towers.DilationCarriesObjectsAtAnIndexOfATower
import YangMills.Construction.Towers.DilationCarriesSetsAtAStepOfTheWholeSpace
import YangMills.Construction.Towers.DilationCarriesTheActionOfATower
import YangMills.Construction.Towers.DilationCarriesTheLatticesOfATower
import YangMills.Construction.Towers.DilationCarriesValuesAtAStepOfTheWholeSpace
import YangMills.Construction.Towers.IsometriesOfATowerAreHypercubicMotions
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import YangMills.Construction.Towers.LatticesOfATowerAreNestedAndCounted
import YangMills.Construction.Towers.PairsOfATowerAreThePairsOfItsSide
import YangMills.Construction.Towers.QuotientOfATowerCarriesConfigurations
import YangMills.Construction.Towers.QuotientOfATowerCarriesSets
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower
theorem sublatticesSymmetriesScalingsAndProjections_of
    (hnested : SublatticesNestedAndCounted.Statement)
    (hsymm : SymmetriesAreHypercubicMotions)
    (hlat : ScalingPreservesSublatticesAllSides)
    (hact : ScalingPreservesActionAllSides)
    (hlevel : ScalingPreservesObjectsAtLevel.Statement)
    (hside : ScalingPreservesStepsAtSide.Statement)
    (hsets : FullSpaceScalingPreservesStepSets.Statement)
    (hvals : FullSpaceScalingPreservesValues)
    (hpairs : towerPairsStatement)
    (hproj : ProjectionCarriesSetsStatement)
    (hfields : FullSpace.ProjPreservesFieldsEverywhere) :
    SublatticesSymmetriesScalingsAndProjections.Statement := by
  intro L hL hS k
  refine ⟨hpairs L hL hS k, (hnested L hL hS k).1, (hnested L hL hS k).2,
    (hsymm L hL hS k).1, (hsymm L hL hS k).2, ?_, ?_⟩
  · intro j hj
    refine ⟨fun n hn => ?_, ?_⟩
    · exact { toScalingPreservesSublattices := (hlat L hL hS k j hj).1 n hn
              toScalingPreservesAction := hact L hL hS k j hj n hn
              preserves := fun hpos => ⟨fun i hi => (hlevel L hL hS k j hj hpos i hi).1 n hn,
                fun i hi => hside L hL hS k j hj hpos i hi n hn⟩ }
    · exact { toScalingPreservesSublattices := (hlat L hL hS k j hj).2
              preserves := fun hpos => ⟨fun i hi => (hlevel L hL hS k j hj hpos i hi).2,
                fun i hi => { toPreservesSetsAtStep := hsets L hL hS k j hj hpos i hi
                              toPreservesValuesAtStep := hvals L hL hS k j hj hpos i hi }⟩ }
  · intro hk n hn
    exact ⟨(hproj L hL hS k hk n hn).1, fun i hi c hc =>
      { toProjPreservesSets := (hproj L hL hS k hk n hn).2 i hi c hc
        toProjPreservesFields := hfields L hL hS k hk n hn i hi c hc }⟩
end YangMills.Construction.Tower

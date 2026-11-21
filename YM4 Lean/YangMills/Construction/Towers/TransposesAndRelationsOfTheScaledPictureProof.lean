import YangMills.Construction.Towers.BackgroundFormOfTheFunctionalOnASide
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnASide
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnASide
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASide
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.RelationsOfTheIteratedAveragesOfTheScaledPictureOnASide
import YangMills.Construction.Towers.RelationsOfTheIteratedAveragesOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.SaddleOperatorsOfTheScaledPictureOnASide
import YangMills.Construction.Towers.SaddleOperatorsOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnASide
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.TransposesAndRelationsOfTheScaledPicture
import YangMills.Construction.Towers.TransposesOfTheIteratedAveragesOfTheScaledPictureOnASide
import YangMills.Construction.Towers.TransposesOfTheIteratedAveragesOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.WeightedTransposesOfTheScaledPictureOnASide
import YangMills.Construction.Towers.WeightedTransposesOfTheScaledPictureOnTheWhole
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower.RescaledConditions
theorem holds_of_conditions
    (h0 : Tower.WeightedTransposesOnTorus.Claim)
    (h1 : Tower.FullSpace.MeshTransposes.TransposeScalingHolds)
    (h2 : Tower.ComplexFieldRescaledRelations.Statement)
    (h3 : Tower.FullSpace.ComplexFieldRescaledRelations.Statement)
    (h4 : Tower.IterTransposesOnTorus.Claim)
    (h5 : Tower.FullSpace.IterTransposesOnFullSpace.Claim)
    (h6 : Tower.RescaledIterRelations)
    (h7 : Tower.FullSpace.RescaledIterRelations)
    (h8 : Tower.RescaledSaddleOperators.Statement)
    (h9 : Tower.FullSpace.RescaledSaddleScaling)
    (h10 : Tower.RescaledTrivialSteps)
    (h11 : Tower.FullSpace.RescaledTrivialSteps)
    (h12 : Tower.TrivialFieldRescaledRelations.Statement)
    (h13 : Tower.FullSpace.RescaledTrivialRelations)
    (h14 : Tower.TrivialAveragesOnEverySide)
    (h15 : Tower.FullSpace.TrivialFieldMeansCondition)
    (h16 : Tower.RescaledBackgroundFormFiniteSide.Statement) :
    Holds := by
  intro L hL k hk
  refine ⟨fun n hn => ⟨⟨h0 L hL k hk n hn, h2 L hL k hk n hn, fun U hU =>
    ⟨h4 L hL k hk n hn U hU, h6 L hL k hk n hn U hU, h8 L hL k hk n hn U hU⟩,
    (h10 L hL k hk n hn).1, (h10 L hL k hk n hn).2, h12 L hL k hk n hn, h14 L hL k hk n hn⟩,
    h16 L hL k hk n hn⟩, ?_⟩
  exact ⟨h1 L hL k hk, h3 L hL k hk, fun U hU =>
    ⟨h5 L hL k hk U hU, h7 L hL k hk U hU, h9 L hL k hk U hU⟩,
    (h11 L hL k hk).1, (h11 L hL k hk).2, h13 L hL k hk, h15 L hL k hk⟩
end YangMills.Construction.Tower.RescaledConditions

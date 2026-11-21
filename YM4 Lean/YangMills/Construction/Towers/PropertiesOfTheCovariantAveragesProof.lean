import YangMills.Construction.Towers.BlockAverageTimesItsTransposeAtTheSideInfinity
import YangMills.Construction.Towers.CovarianceOfTheIteratesUnderIsometriesOnTheSides
import YangMills.Construction.Towers.CovariantDifferenceRelationsOfAStepOfASide
import YangMills.Construction.Towers.GaugeCovarianceOfTheCovariantAveragesAtTheSideInfinity
import YangMills.Construction.Towers.GaugeCovarianceOfTheCovariantAveragesOnTheSides
import YangMills.Construction.Towers.IsometryCovarianceOfTheCovariantAveragesOnTheWholeLattice
import YangMills.Construction.Towers.ProductOfTheBlockAverageWithItsTransposeOnTheSides
import YangMills.Construction.Towers.PropertiesOfTheCovariantAverages
import YangMills.Construction.Towers.RelationsOfOneCovariantStepAtTheSideInfinity
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOfTheWholeLattice
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOnTheSides
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
theorem CovariantSmoothingProperties.of_parts
    (hStep : CovDiffStepRelations)
    (hAdj : AdjointCubeAverageMulTranspose)
    (hIter : CovariantIterRelations)
    (hGauge : AveragesGaugeCovariant)
    (hIsom : IteratesIsometryCovariant)
    (hStepFull : FullSpace.CovariantStepRelations)
    (hAdjFull : FullSpace.CubeAverageMulTranspose.Statement)
    (hIterFull : FullSpace.CovariantIterRelations)
    (hGaugeFull : FullSpace.AveragesGaugeCovariant)
    (hIsomFull : FullSpace.CovariantSmoothingIsometryEquivariance) :
    CovariantSmoothingProperties.Statement := by
  intro L hL
  refine ⟨fun n k hn => ⟨fun j hj V hV => ⟨fun l hl => hStep L hL n k j hn hj V hV l hl,
      hAdj L hL n k j hn hj V hV⟩,
    fun j hj => ⟨fun U hU => hIter L hL n k j hn hj U hU,
      fun U hU u hu huU => hGauge L hL n k j hn hj U hU u hu huU,
      fun f hf hfk U hU => hIsom L hL n k j hn hj f hf hfk U hU⟩⟩,
    fun k => ⟨fun j hj V hV => ⟨fun l hl => hStepFull L hL k j hj V hV l hl,
      hAdjFull L hL k j hj V hV⟩,
    fun j hj => ⟨fun U hU => hIterFull L hL k j hj U hU,
      fun U hU u hu huU => hGaugeFull L hL k j hj U hU u hu huU,
      fun f hf hfk U hU => hIsomFull L hL k j hj f hf hfk U hU⟩⟩⟩
end YangMills.Construction.Tower
end

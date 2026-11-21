import YangMills.Construction.ReflectionsAndOneInsertion.OneInsertionAtOneCutoff
import YangMills.Construction.ReflectionsAndOneInsertion.ReflectionsObservablesAndCellData
import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
open RenormalizationStepParameters TorusLumps TestFunctions
open InfiniteLattice (localObsAbove periodicGibbsSet reflectionSeminorm timeConj)
open ChessboardTori (GridCell)
open ReflectionsAndOneInsertion (complexSmeared)
def WindowInsertionBound (ℓ : StepParameters) (Bs g CI q M : ℝ) : Prop :=
  ∀ (D : ChessboardTori.ChessboardSetup), D.L = ℓ.side → IsFirstPassagePoint ℓ Bs g D.K D.β →
    ∀ (c : GridCell D) (h : InfiniteLattice.AmbientSpace → ℝ), IsLipschitzFor euclidDistR4 h →
      tsupport h ⊆ closedBallR4 c.centre (1 / 4 * c.side) → c.side ≤ 1 →
      ∀ ρ ∈ periodicGibbsSet D.L D.K D.β, ∀ ν ∈ periodicGibbsSet D.L D.K D.β,
      ∀ P ∈ localObsAbove c.baseTime, ∀ Q ∈ localObsAbove c.baseTime,
        ‖∫ U, timeConj c.baseTime Q U *
            (complexSmeared D h U - ∫ V, complexSmeared D h V ∂ν) *
            (c.timeShift 1).actOn P U ∂ρ‖ ≤
          CI * c.side ^ (-q) * sharpNormR4 M h *
            reflectionSeminorm ρ c.baseTime Q * reflectionSeminorm ρ c.baseTime P
namespace WindowInsertion
def Statement : Prop :=
  HoldsAtAdmissibleParameters fun T y => ∀ Bs : ℝ, 2 * T.B ≤ Bs → ForSmallCoupling fun g =>
    ∃ CI q : ℝ, 0 ≤ CI ∧ 0 ≤ q ∧ ∀ M : ℝ, 1 ≤ M → WindowInsertionBound (T.stepParameters y) Bs g CI q M
end WindowInsertion
end YangMills.Construction.TotalDensities
end

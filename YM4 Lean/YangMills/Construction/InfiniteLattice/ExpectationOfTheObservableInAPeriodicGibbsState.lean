import YangMills.Construction.Geometry.TorusCovering
import YangMills.Construction.InfiniteLattice.HypercubicMotionsOfTheLattice
import YangMills.Construction.InfiniteLattice.MeanOfSixRiemannSumsOfATestFunction
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAtOneCutoff
import YangMills.Construction.Lattice.ImagesOfBondsAndPlaquettesUnderLatticeIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def riemannSumErrorConst : ℝ := 16
def MotionsTransitiveOnPlaquettes (L K : ℕ) : Prop :=
  ∀ p q : LatticeCutoffPlaquette L K, ∃ r : latticeMotions (refinedSpacing L K),
    (latticeMotionSymmetry r).pointMap '' p.cornerSet = q.cornerSet
def ExpectObservableEqRiemannMultiple {L K : ℕ}
    (ν : Measure (RefinedGaugeField L K)) (F : AmbientSpace → ℝ) : Prop :=
  YangMills.Construction.PeriodicGibbsAtCutoff.expectation ν
      (fun U => ((YangMills.Construction.PeriodicGibbsAtCutoff.smearedObservable F U : ℝ) : ℂ)) =
      (meanFaceEnergy ν : ℂ) * ((∑ᶠ p : LatticeCutoffPlaquette L K, F p.center : ℝ) : ℂ) ∧
    (meanFaceEnergy ν : ℂ) * ((∑ᶠ p : LatticeCutoffPlaquette L K, F p.center : ℝ) : ℂ) =
      6 * ((refinedSpacing L K : ℂ) ^ 4)⁻¹ * (meanFaceEnergy ν : ℂ) *
        realRiemannSum L K F
def PeriodicGibbsObservableExpectation : Prop :=
  (∀ (L : ℕ) (K : ℕ+) (β : ℝ), YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    0 < β →
    ∀ ν ∈ periodicGibbsSet L K β,
      MotionsTransitiveOnPlaquettes L K ∧
      (∀ r : latticeMotions (refinedSpacing L K),
        IsSymmetricUnder ν (latticeMotionSymmetry r)) ∧
      (∀ p : LatticeCutoffPlaquette L K, ∫ U, faceEnergy U p ∂ν = meanFaceEnergy ν) ∧
      ∀ F ∈ compactTestFunctions, ExpectObservableEqRiemannMultiple ν F) ∧
  ∀ (L : ℕ), YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    ∀ (F : AmbientSpace → ℝ) (y : AmbientSpace) (R : ℝ), 0 < R →
      YangMills.Construction.TestFunctions.IsLipschitzFor
        YangMills.Construction.TestFunctions.euclidDistR4 F →
      YangMills.Construction.TorusCovering.IsSupportedIn F
        (YangMills.Construction.TestFunctions.closedBallR4 y R) →
        (∀ K : ℕ+,
          ‖realRiemannSum L K F - ((∫ x, F x : ℝ) : ℂ)‖ ≤
            riemannSumErrorConst * (R + 1) ^ 4 * refinedSpacing L K *
              YangMills.Construction.TestFunctions.lipConstR4 F) ∧
        Filter.Tendsto (fun J : ℕ => realRiemannSum L J F) Filter.atTop
          (nhds ((∫ x, F x : ℝ) : ℂ))
end YangMills.Construction.InfiniteLattice
end

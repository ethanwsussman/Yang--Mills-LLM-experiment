import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
open RenormalizationStepParameters TorusLumps TestFunctions
open InfiniteLattice (periodicGibbsSet smearedEnergyCumulant smearedEnergy)
structure WindowBounds (ℓ : StepParameters) (Bs g Ccum Ctr M : ℝ) : Prop where
  cumulant_bound : ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePoint ℓ Bs g K β →
    ∀ ν ∈ periodicGibbsSet ℓ.side K β, ∀ n : ℕ, 2 ≤ n → ∀ R d : ℝ, 0 < R → 0 < d →
      ∀ f : Fin n → InfiniteLattice.AmbientSpace → ℝ, (∀ i, IsLipschitzFor euclidDistR4 (f i)) →
        (∀ i, ∃ x, tsupport (f i) ⊆ closedBallR4 x R) → HasSeparatedSupportsR4 f d →
          ‖smearedEnergyCumulant ν f‖ ≤
            (n.factorial : ℝ) * (Ccum * (1 + R) ^ 4 * ((n : ℝ) / min d 1) ^ 5) ^ n *
              ∏ i, sharpNormR4 M (f i)
  onePoint_diff : ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePoint ℓ Bs g K β →
    ∀ ν ∈ periodicGibbsSet ℓ.side K β, ∀ ν' ∈ periodicGibbsSet ℓ.side K β, ∀ R : ℝ, 0 < R →
      ∀ f : InfiniteLattice.AmbientSpace → ℝ, IsLipschitzFor euclidDistR4 f →
        (∃ x, tsupport f ⊆ closedBallR4 x R) →
          |(∫ U, smearedEnergy f U ∂ν) - ∫ U, smearedEnergy f U ∂ν'| ≤
            Ctr * (1 + R) ^ 4 * sharpNormR4 M f
namespace WindowBoundsExist
def Statement : Prop :=
  HoldsAtAdmissibleParameters fun T y => ∀ Bs : ℝ, 2 * T.B ≤ Bs → ForSmallCoupling fun g =>
    ∃ Ccum Ctr : ℝ, 0 < Ccum ∧ 0 < Ctr ∧ ∀ M : ℝ, 1 ≤ M → WindowBounds (T.stepParameters y) Bs g Ccum Ctr M
end WindowBoundsExist
end YangMills.Construction.TotalDensities
end

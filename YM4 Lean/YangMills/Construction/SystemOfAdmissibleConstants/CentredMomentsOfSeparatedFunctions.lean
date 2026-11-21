import YangMills.Construction.ChessboardTori.StandingConventions
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace SeparatedMoments
open TestFunctions ChessboardTori
open InfiniteLattice (AmbientSpace periodicGibbsSet smearedEnergy)
def fineConstant (L : ℕ) (A b R : ℝ) (n : ℕ) (d : ℝ) : ℝ :=
  10 * 2 ^ 53 * (L : ℝ) ^ 5 * A * Real.exp (b + b ^ ((20 : ℝ) / 19)) * (1 + R) ^ 4 * ((n : ℝ) / d) ^ 5
def coarseConstant (L : ℕ) (R : ℝ) (n : ℕ) (d : ℝ) : ℝ :=
  24 * 2 ^ 40 * (L : ℝ) ^ 12 * ((n : ℝ) / d) ^ 4 * (1 + R) ^ 4
def IsMaximalScalePower (L : ℕ) (d l : ℝ) : Prop :=
  (∃ j : ℤ, l = (L : ℝ) ^ j) ∧ l ≤ d / 8 ∧ d / 8 < L * l
structure CentredMomentBound (D : ChessboardSetup) (M R d G : ℝ) (n : ℕ) : Prop where
  gibbs_bound : ∀ ν ∈ periodicGibbsSet D.L D.K D.β, ∀ f : Fin n → AmbientSpace → ℝ,
    (∀ i, IsLipschitzFor euclidDistR4 (f i)) → (∀ i, ∃ x, tsupport (f i) ⊆ closedBallR4 x R) →
    HasSeparatedSupportsR4 f d → ∀ J : Finset (Fin n), J.Nonempty →
      |∫ U, ∏ i ∈ J, (smearedEnergy (f i) U - ∫ V, smearedEnergy (f i) V ∂ν) ∂ν| ≤
        ∏ i ∈ J, G * sharpNormR4 M (f i)
  torus_bound : ∀ m : ℕ+, ∀ f : Fin n → PeriodicLattice.FourTorus D.L m → ℝ,
    (∀ i, IsLipschitzFor euclidDistTorus (f i)) → (∀ i, ∃ x, tsupport (f i) ⊆ closedBallTorus x R) →
    HasSeparatedSupportsTorus f d → ∀ J : Finset (Fin n), J.Nonempty →
      |∫ U, ∏ i ∈ J, (PeriodicLattice.smearedObservable (f i) U -
          ∫ V, PeriodicLattice.smearedObservable (f i) V ∂PeriodicLattice.wilsonGibbsMeasure D.L m D.K D.β)
        ∂PeriodicLattice.wilsonGibbsMeasure D.L m D.K D.β| ≤ ∏ i ∈ J, G * sharpNormTorus M (f i)
end SeparatedMoments
end YangMills.Construction
end

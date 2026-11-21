import YangMills.Construction.Continuum.CentredMomentsOfTheCumulantsAndOfTheirLimits
import YangMills.Construction.Continuum.GrowthConditionOfALimitFromABoundAtTheCutoffs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.BoundsOnEverySide
open AmbientPoints
open SeparatedBound
open LimitGrowthFromCutoffBound (restrictToTestTuples)
open TestSpaces (SepTupleOfCard)
structure GibbsStateSequence (L : ℕ) where
  K : ℕ+ → ℕ+
  β : ℕ+ → ℝ
  gibbs : ∀ k, Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (((K k : ℕ+) : ℕ) : ℤ)))
  gibbs_mem : ∀ k, gibbs k ∈ InfiniteLattice.periodicGibbsSet L (K k) (β k)
def GibbsStateSequence.CumulantsBoundedBy {L : ℕ} (Q : GibbsStateSequence L) (M : ℝ)
    (C : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ (k : ℕ+) (n : ℕ), 2 ≤ n → ∀ R δ : ℝ, 0 < R → 0 < δ → ∀ X : SepTupleOfCard n,
    SupportedSeparated R δ X →
      ‖InfiniteLattice.smearedEnergyCumulant (Q.gibbs k) X.1‖ ≤ C n δ R * sharpNormProd M X
structure GibbsStateSequence.HasSubsequentialLimit {L : ℕ} {s : Conventions.StandingParameters}
    (Q : GibbsStateSequence L) (M : ℝ)
    (C : ℕ → ℝ → ℝ → ℝ) (φ : ℕ+ → ℕ+) (S : TupleMapFamily s .euclidean) : Prop where
  strictMono : StrictMono φ
  tendsto : ∀ (n : ℕ) (hn : 2 ≤ n) (f : separatedTuples s .euclidean n),
    Tendsto (fun i => InfiniteLattice.smearedEnergyCumulant (Q.gibbs (φ i)) f.1) atTop
      (𝓝 (S n hn f : ℂ))
  isConnected : CumulantLimits.IsConnectedFamily S
  symm : ∀ (n : ℕ) (hn : 2 ≤ n), IsTupleSymmetric (S n hn)
  bound : ∀ (n : ℕ) (hn : 2 ≤ n) (R δ : ℝ), 0 < R → 0 < δ → ∀ X : SepTupleOfCard n,
    SupportedSeparated R δ X → |restrictToTestTuples S n hn X| ≤ C n δ R * sharpNormProd M X
def SeparatedLimitsExist : Prop :=
  ∀ (L : ℕ), Conventions.IsAdmissibleBlockingFactor L → ∀ (M : ℝ), 1 ≤ M →
    ∀ (Q : GibbsStateSequence L) (C : ℕ → ℝ → ℝ → ℝ), Q.CumulantsBoundedBy M C →
      ∀ s : Conventions.StandingParameters,
        ∃ (φ : ℕ+ → ℕ+) (S : TupleMapFamily s .euclidean), Q.HasSubsequentialLimit M C φ S
end YangMills.Construction.BoundsOnEverySide
end

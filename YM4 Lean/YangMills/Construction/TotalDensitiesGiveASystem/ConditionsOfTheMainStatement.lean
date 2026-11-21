import YangMills.Construction.TotalDensitiesGiveASystem.LawsOfTheTopStatement
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensitySystem
structure LimitRequirements (ϑ d₀ : ℝ) (ηBar : ℝ → ℝ) (C : SystemsWithFiveBounds.LimitConstants)
    (S : LimitTheorem.CumulantFamily) : Prop where
  symmetries : SystemsWithFiveBounds.LatticeSymmetries S
  axialPositive : LimitTheorem.IsReflectionPositiveAxial (LimitTheorem.centredOf S)
  distributions : SystemsWithFiveBounds.DistributionalExtension S
  conditions : SystemsWithFiveBounds.LimitConditions 1 ϑ d₀ ηBar C S
structure VolumeFirstExtras (p : TorusLumps.StepParameters) {IsPair : ℕ+ → ℝ → Prop}
    (Q : SystemsWithFiveBounds.PairSequence p.side IsPair) (S : LimitTheorem.CumulantFamily) : Prop where
  large_sides : ∀ b : ℕ+ → ℝ, ∃ m : ℕ+ → ℕ+, (∀ j, b j ≤ PeriodicLattice.torusSide p.side (m j)) ∧
    ∀ (n : ℕ) (hn : 2 ≤ n) (X : TestSpaces.SepTupleOfCard n),
      (∀ᶠ j in atTop, SchwingerFunctions.IsR4TestFamily (PeriodicLattice.torusSide p.side (m j)) X.1) ∧
      Tendsto (fun j => SchwingerFunctions.connectedSchwingerR4 p.side (m j) (Q.cutoff j) (Q.coupling j) X.1) atTop
        (𝓝 ((S n hn X : ℝ) : ℂ))
  spatialRotations : SystemsWithFiveBounds.SpatialRotationRep (LimitTheorem.centredOf S)
structure ShapeConditions (p : TorusLumps.StepParameters) (Bs c₅ lam g ϑ : ℝ) (room : ℕ → ℝ)
    (C : SystemsWithFiveBounds.LimitConstants) (d₀ : ℝ)
    (ηBar εBar : ℝ → ℝ) (ζ : ℕ+ → ℝ → ℝ → ℝ) (K₀ : ℝ → ℕ) (d₄ : ℝ) : Prop where
  twoPointLaw : TotalDensities.TwoPointLawAtShape p Bs c₅ lam g ϑ room d₀ ηBar εBar ζ K₀
  twoPointLawInLimits : TotalDensities.TwoPointLawInLimits p Bs g ϑ d₀ ηBar εBar
  everyLimit : ∀ S : LimitTheorem.CumulantFamily, IsContinuumLimit p Bs g S → LimitRequirements ϑ d₀ ηBar C S
  d₄_mem : d₄ ∈ Ioc (0 : ℝ) d₀
  fourPoint : FourPointCondition.FourPointConditionHolds (totalFlowValue p g Bs room ζ) p.side ϑ d₄ 1
  fourPointInLimits : TotalDensities.FourPointLawInLimits p Bs g ϑ d₄
  ergodic : ∀ (Q : SystemsWithFiveBounds.PairSequence p.side (IsFirstPassagePair p Bs g))
    (S : LimitTheorem.CumulantFamily), Q.Defines S →
    SystemsWithFiveBounds.ErgodicDecompositionConclusion 1 ϑ d₀ ηBar C Q S
def CouplingConstants (p : TorusLumps.StepParameters) (Bs c₅ lam g : ℝ) : Prop :=
  ∃ (cV : ℝ) (Cn : ℕ → ℝ → ℝ) (C : SystemsWithFiveBounds.LimitConstants), C.Valid ∧
    TorusCumulantBound p Bs g cV Cn ∧ LocalCumulantBounds p Bs g C ∧
    (∀ (s : Conventions.StandingParameters) (S : AmbientPoints.TupleMapFamily s .torus), s.L = p.side →
      IsTorusLimit p Bs g s S → IsTorusLimitFamily s cV Cn C S) ∧
    (∀ (Q : SystemsWithFiveBounds.PairSequence p.side (IsFirstPassagePair p Bs g))
      (S : LimitTheorem.CumulantFamily), Q.Defines S →
      VolumeFirstExtras p Q S ∧ TotalDensities.ShortDistanceAsymptotics S) ∧
    ∀ ϑ ∈ Ioc (0 : ℝ) 1, TotalDensities.ShortDistanceLimitNonGaussian ϑ ∧
      ∀ room : ℕ → ℝ, RoomFunctions.IsSubexpGrowth room →
        ∃ (d₀ : ℝ) (ηBar εBar : ℝ → ℝ) (ζ : ℕ+ → ℝ → ℝ → ℝ) (K₀ : ℝ → ℕ) (d₄ : ℝ),
          ShapeConditions p Bs c₅ lam g ϑ room C d₀ ηBar εBar ζ K₀ d₄
structure CouplingConditions (p : TorusLumps.StepParameters) (Bs c₅ lam : ℝ) (Nw : ℕ) (CT g : ℝ) : Prop where
  passage : FlowPassage p Bs c₅ lam Nw g
  tie : CouplingTie p Bs CT g
  torusLimits : HasTorusSubsequenceLimits p Bs g
  growingTorusLimits : HasGrowingTorusSubsequenceLimits p Bs g
  volumeFirstLimits : HasVolumeFirstLimits p Bs g
  constants : CouplingConstants p Bs c₅ lam g
end YangMills.Construction.TotalDensitySystem
end

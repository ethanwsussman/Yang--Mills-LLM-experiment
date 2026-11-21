import YangMills.Construction.InfiniteLattice.RegularConditionalProbabilityOfAPeriodicGibbsState
import YangMills.Construction.ReflectionsAndOneInsertion.OneInsertionAtOneCutoff
import YangMills.Construction.ReflectionsAndOneInsertion.ReflectionsObservablesAndCellData
import YangMills.Construction.TwoPoints.FourShapesAndTheShapeConstant
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open TestFunctions (IsLipschitzFor HasSeparatedSupportsR4 inverseEighthKernel closedBallR4
  euclidDistR4 sharpNormR4 separatedPairsR4)
open InfiniteLattice (GaugeField IsInfiniteVolumeLimit AmbientSpace localObsAbove
  periodicGibbsSet reflectionSeminorm smearedEnergyCumulant smearedEnergy timeConj)
open ChessboardTori (GridCell)
open ReflectionsAndOneInsertion (complexSmeared)
structure BoundConstants where
  aStar : ℝ
  sepExponent : ℕ
  ballConst : ℝ → ℝ
  factorialExponent : ℝ
  onePointConst : ℝ → ℝ
  insertionConst : ℝ
  insertionExponent : ℝ
  insertionRadiusRatio : ℝ
  lawScale : ℝ
  lawError : ℝ → ℝ
  cutoffThreshold : ℝ → ℕ
structure BoundConstants.Admissible (N : BoundConstants) : Prop where
  aStar_pos : 0 < N.aStar
  ballConst_pos : ∀ R : ℝ, 0 < R → 0 < N.ballConst R
  ballConst_monotoneOn : MonotoneOn N.ballConst (Ioi 0)
  factorialExponent_nonneg : 0 ≤ N.factorialExponent
  onePointConst_nonneg : ∀ R : ℝ, 0 < R → 0 ≤ N.onePointConst R
  onePointConst_monotoneOn : MonotoneOn N.onePointConst (Ioi 0)
  insertionConst_nonneg : 0 ≤ N.insertionConst
  insertionExponent_nonneg : 0 ≤ N.insertionExponent
  insertionRadiusRatio_mem : N.insertionRadiusRatio ∈ Ioc (0 : ℝ) (1 / 4)
  lawScale_mem : N.lawScale ∈ Ioo (0 : ℝ) 1
  lawError_monotoneOn : MonotoneOn N.lawError (Ioc 0 N.lawScale)
  lawError_mem : ∀ d ∈ Ioc 0 N.lawScale, N.lawError d ∈ Icc (0 : ℝ) (1 / 3)
  lawError_tendsto : Tendsto N.lawError (𝓝[>] 0) (𝓝 0)
def BoundConstants.cumulantBound (N : BoundConstants) (n : ℕ) (d R : ℝ) : ℝ :=
  (N.aStar * max 1 (d ^ (-(N.sepExponent : ℤ))) * N.ballConst R) ^ n *
    (n.factorial : ℝ) ^ N.factorialExponent
def asymptoticFreedomSlope : ℝ := 11 * 2 ^ 2 / (12 * Real.pi ^ 2)
def twoPointPrefactor : ℝ :=
  3 * (2 ^ 2 - 1) / Real.pi ^ 4 * (12 * Real.pi ^ 2 / (11 * 2 ^ 2)) ^ 2
def twoPointMainTerm (d : ℝ) (f h : AmbientSpace → ℝ) : ℝ :=
  twoPointPrefactor * inverseEighthKernel f h / Real.log (1 / d) ^ 2
def SatisfiesTwoPointLaw (err : ℝ → ℝ) (d value : ℝ) (f h : AmbientSpace → ℝ) : Prop :=
  ∃ η : ℝ, value = twoPointMainTerm d f h * (1 + η) ∧
    1 / 2 * (1 - err d) ^ 4 ≤ 1 + η ∧ 1 + η ≤ 3 / 2 * (1 + err d) ^ 4
def AEErgodicComponentsIn (D : LatticePhases.Setup)
    (ν : periodicGibbsSet D.L D.K D.β) (Z : Set (Measure (GaugeField D.mesh))) : Prop :=
  ∀ κ : GaugeField D.mesh → LatticePhases.ProbMeasure (GaugeField D.mesh),
    LatticePhases.IsInvariantConditionalFamily D ν κ →
      ∀ᵐ U ∂ν.1, (κ U).toMeasure ∈ Z
structure FiveBoundSystem where
  L : ℕ
  admissibleL : Conventions.IsAdmissibleBlockingFactor L
  M : ℝ
  one_le_M : 1 ≤ M
  ϑ : ℝ
  ϑ_mem : ϑ ∈ Ioc (0 : ℝ) 1
  ϑ_le : ϑ ≤ TwoPoints.Shapes.shapeConst
  top : ℝ
  top_pos : 0 < top
  IsPair : ℝ → ℕ+ → ℝ → Prop
  States : ∀ (L' : ℕ) (K : ℕ+) (β : ℝ),
    Set (Measure (GaugeField (PeriodicLattice.meshSize L' (((K : ℕ)) : ℤ))))
  consts : ℝ → BoundConstants
  consts_admissible : ∀ g ∈ Ioc 0 top, (consts g).Admissible
  β_pos : ∀ g ∈ Ioc 0 top, ∀ K β, IsPair g K β → 0 < β
  states_subset : ∀ g ∈ Ioc 0 top, ∀ K β, IsPair g K β → States L K β ⊆ periodicGibbsSet L K β
  limits_mem : ∀ g ∈ Ioc 0 top, ∀ K β, IsPair g K β → ∀ ν, IsInfiniteVolumeLimit L K β ν →
    ν ∈ States L K β
  components_mem : ∀ g ∈ Ioc 0 top, ∀ K β, IsPair g K β → ∀ (hβ : 0 < β)
    (ν : periodicGibbsSet L K β), IsInfiniteVolumeLimit L K β ν.1 →
      AEErgodicComponentsIn ⟨L, admissibleL, K, β, hβ⟩ ν (States L K β)
  infinite_cutoffs : ∀ g ∈ Ioc 0 top, {K : ℕ+ | ∃ β, IsPair g K β}.Infinite
  asymptotic_freedom : ∀ g ∈ Ioc 0 top, ∃ δ : ℕ+ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ K β, IsPair g K β →
    |β / Real.log (1 / PeriodicLattice.meshSize L (((K : ℕ)) : ℤ)) - asymptoticFreedomSlope| ≤ δ K
  cumulant_bound : ∀ g ∈ Ioc 0 top, ∀ K β, IsPair g K β →
    ∀ ν ∈ States L K β, ∀ n : ℕ, 2 ≤ n → ∀ R d : ℝ, 0 < R → 0 < d →
      ∀ f : Fin n → AmbientSpace → ℝ, (∀ i, IsLipschitzFor euclidDistR4 (f i)) →
        (∀ i, ∃ x, tsupport (f i) ⊆ closedBallR4 x R) → HasSeparatedSupportsR4 f d →
          ‖smearedEnergyCumulant ν f‖ ≤ (consts g).cumulantBound n d R * ∏ i, sharpNormR4 M (f i)
  onePoint_bound : ∀ g ∈ Ioc 0 top, ∀ K β, IsPair g K β →
    ∀ ν ∈ States L K β, ∀ ν' ∈ States L K β, ∀ R : ℝ, 0 < R →
      ∀ f : AmbientSpace → ℝ, IsLipschitzFor euclidDistR4 f → (∃ x, tsupport f ⊆ closedBallR4 x R) →
        |(∫ U, smearedEnergy f U ∂ν) - ∫ U, smearedEnergy f U ∂ν'| ≤
          (consts g).onePointConst R * sharpNormR4 M f
  twoPoint_law : ∀ g ∈ Ioc 0 top, ∀ d ∈ Ioc 0 (consts g).lawScale, ∀ K β, IsPair g K β →
    (consts g).cutoffThreshold d ≤ (K : ℕ) → ∀ ν ∈ States L K β,
      ∀ f h : AmbientSpace → ℝ, (f, h) ∈ separatedPairsR4 d ϑ → ContDiff ℝ 1 f → ContDiff ℝ 1 h →
        ∃ t : ℝ, smearedEnergyCumulant ν ![f, h] = (t : ℂ) ∧
          SatisfiesTwoPointLaw (consts g).lawError d t f h
  insertion_bound : ∀ g ∈ Ioc 0 top, ∀ (D : ChessboardTori.ChessboardSetup), D.L = L →
    IsPair g D.K D.β →
    ∀ (c : GridCell D) (h : AmbientSpace → ℝ), IsLipschitzFor euclidDistR4 h →
      tsupport h ⊆ closedBallR4 c.centre ((consts g).insertionRadiusRatio * c.side) → c.side ≤ 1 →
      ∀ ρ ∈ States D.L D.K D.β, ∀ ν ∈ States D.L D.K D.β,
      ∀ P ∈ localObsAbove c.baseTime, ∀ Q ∈ localObsAbove c.baseTime,
        ‖∫ U, timeConj c.baseTime Q U *
            (complexSmeared D h U - ∫ V, complexSmeared D h V ∂ν) *
            (c.timeShift 1).actOn P U ∂ρ‖ ≤
          (consts g).insertionConst * c.side ^ (-(consts g).insertionExponent) * sharpNormR4 M h *
            reflectionSeminorm ρ c.baseTime Q * reflectionSeminorm ρ c.baseTime P
end YangMills.Construction.SystemsWithFiveBounds
end

import YangMills.Construction.BoundsOnEverySide.TheBoundsOnEverySide
import YangMills.Construction.SystemsWithFiveBounds.SystemWithFiveBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open Filter MeasureTheory Set TestFunctions
open BoundsOnEverySide (SideFamily)
open InfiniteLattice (GaugeField IsInfiniteVolumeLimit AmbientSpace localObsAbove
  periodicGibbsSet reflectionSeminorm smearedEnergyCumulant smearedEnergy timeConj)
open ChessboardTori (GridCell)
open ReflectionsAndOneInsertion (complexSmeared)
structure StatedSideFamily extends SideFamily where
  stateSet : ∀ (L' : ℕ) (K : ℕ+) (β : ℝ),
    Set (Measure (GaugeField (PeriodicLattice.meshSize L' (((K : ℕ)) : ℤ))))
  stateSet_subset : ∀ K β, IsFirstPassage K β → stateSet L K β ⊆ periodicGibbsSet L K β
  volumeLimits_mem : ∀ K β, IsFirstPassage K β → ∀ ν, IsInfiniteVolumeLimit L K β ν →
    ν ∈ stateSet L K β
  ergodicComponents_mem : ∀ K β, IsFirstPassage K β → ∀ (hβ : 0 < β) (ν : periodicGibbsSet L K β),
    IsInfiniteVolumeLimit L K β ν.1 →
      AEErgodicComponentsIn ⟨L, admissible, K, β, hβ⟩ ν (stateSet L K β)
structure BoundsHoldAt (F : StatedSideFamily) (N : BoundConstants) : Prop where
  admissible_constants : N.Admissible
  cumulant_le : ∀ (K : ℕ+) (β : ℝ), F.IsFirstPassage K β →
    ∀ ν ∈ F.stateSet F.L K β, ∀ n : ℕ, 2 ≤ n → ∀ R d : ℝ, 0 < R → 0 < d →
      ∀ f : Fin n → AmbientSpace → ℝ, (∀ i, IsLipschitzFor euclidDistR4 (f i)) →
        (∀ i, ∃ x, tsupport (f i) ⊆ closedBallR4 x R) → HasSeparatedSupportsR4 f d →
          ‖smearedEnergyCumulant ν f‖ ≤ N.cumulantBound n d R * ∏ i, sharpNormR4 F.M (f i)
  mean_sub_le : ∀ (K : ℕ+) (β : ℝ), F.IsFirstPassage K β →
    ∀ ν ∈ F.stateSet F.L K β, ∀ ν' ∈ F.stateSet F.L K β, ∀ R : ℝ, 0 < R →
      ∀ f : AmbientSpace → ℝ, IsLipschitzFor euclidDistR4 f → (∃ x, tsupport f ⊆ closedBallR4 x R) →
        |(∫ U, smearedEnergy f U ∂ν) - ∫ U, smearedEnergy f U ∂ν'| ≤
          N.onePointConst R * sharpNormR4 F.M f
  insertion_le : ∀ (D : ChessboardTori.ChessboardSetup), D.L = F.L → F.IsFirstPassage D.K D.β →
    ∀ (c : GridCell D) (h : AmbientSpace → ℝ), IsLipschitzFor euclidDistR4 h →
      tsupport h ⊆ closedBallR4 c.centre (N.insertionRadiusRatio * c.side) → c.side ≤ 1 →
      ∀ ρ ∈ F.stateSet D.L D.K D.β, ∀ ν ∈ F.stateSet D.L D.K D.β,
      ∀ P ∈ localObsAbove c.baseTime, ∀ Q ∈ localObsAbove c.baseTime,
        ‖∫ U, timeConj c.baseTime Q U *
            (complexSmeared D h U - ∫ V, complexSmeared D h V ∂ν) *
            (c.timeShift 1).actOn P U ∂ρ‖ ≤
          N.insertionConst * c.side ^ (-N.insertionExponent) * sharpNormR4 F.M h *
            reflectionSeminorm ρ c.baseTime Q * reflectionSeminorm ρ c.baseTime P
def TwoPointLawAt (F : StatedSideFamily) (N : BoundConstants) (ϑ : ℝ) : Prop :=
  ∀ d ∈ Ioc 0 N.lawScale, ∀ K β, F.IsFirstPassage K β → N.cutoffThreshold d ≤ (K : ℕ) →
    ∀ ν ∈ F.stateSet F.L K β, ∀ f h : AmbientSpace → ℝ, (f, h) ∈ separatedPairsR4 d ϑ →
      ContDiff ℝ 1 f → ContDiff ℝ 1 h →
        ∃ t : ℝ, smearedEnergyCumulant ν ![f, h] = (t : ℂ) ∧ SatisfiesTwoPointLaw N.lawError d t f h
def FiveBoundSystem.statedSideFamily (Y : FiveBoundSystem) (g : ℝ) (hg : g ∈ Ioc 0 Y.top) :
    StatedSideFamily where
  L := Y.L
  admissible := Y.admissibleL
  M := Y.M
  one_le_M := Y.one_le_M
  sideSet := univ
  exists_side_ge l := by
    have hL : (1 : ℝ) < Y.L := by
      have := Y.admissibleL.2
      exact_mod_cast (by omega : 1 < Y.L)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt l hL
    refine ⟨⟨n + 1, Nat.succ_pos n⟩, mem_univ _, ?_⟩
    have h₁ : (Y.L : ℝ) ^ n ≤ (Y.L : ℝ) ^ (n + 1) :=
      pow_le_pow_right₀ hL.le (Nat.le_succ n)
    have h₀ : (0 : ℝ) < (Y.L : ℝ) ^ (n + 1) := by positivity
    show l ≤ 2 * (Y.L : ℝ) ^ (n + 1)
    linarith
  IsFirstPassage := Y.IsPair g
  pos_of_isFirstPassage := Y.β_pos g hg
  stateSet := Y.States
  stateSet_subset := Y.states_subset g hg
  volumeLimits_mem := Y.limits_mem g hg
  ergodicComponents_mem := Y.components_mem g hg
theorem FiveBoundSystem.boundsHoldAt_statedSideFamily (Y : FiveBoundSystem) {g : ℝ}
    (hg : g ∈ Ioc 0 Y.top) :
    BoundsHoldAt (Y.statedSideFamily g hg) (Y.consts g) where
  admissible_constants := Y.consts_admissible g hg
  cumulant_le := Y.cumulant_bound g hg
  mean_sub_le := Y.onePoint_bound g hg
  insertion_le := Y.insertion_bound g hg
theorem FiveBoundSystem.twoPointLawAt_statedSideFamily (Y : FiveBoundSystem) {g : ℝ}
    (hg : g ∈ Ioc 0 Y.top) :
    TwoPointLawAt (Y.statedSideFamily g hg) (Y.consts g) Y.ϑ :=
  fun d hd K β hp hK ν hν f h hfh hf hh => Y.twoPoint_law g hg d hd K β hp hK ν hν f h hfh hf hh
end YangMills.Construction.SystemsWithFiveBounds
end

import YangMills.Construction.InfiniteLattice.CubicToriAmongTheToriOfAnyShape
import YangMills.Construction.InfiniteLattice.CumulantsArePolynomialsInTheMomentsAndWeakLimits
import YangMills.Construction.InfiniteLattice.TorusConfigurationsAndMeasuresThroughTheCoveringMapOfACutoff
import YangMills.Construction.InfiniteLattice.WeakLimitPointsOfTheFamilyAreLimitsAlongSequences
import YangMills.Construction.LawInAState.FromSixteenCopiesToOneBoxProof
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
import YangMills.Construction.TotalDensitiesGiveASystem.TheStatesOfTheToriAreLimitsOfTheTori
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open InfiniteLattice GibbsAtFixedSpacing TestFunctions
private theorem continuous_of_isLipschitzFor {g : InfiniteLattice.AmbientSpace → ℝ}
    (h : IsLipschitzFor TestFunctions.euclidDistR4 g) : Continuous g := by apply _root_.YangMills.SharedProofs.p29528 <;> assumption
private theorem euclidNormVec_le_two_mul_norm (v : InfiniteLattice.AmbientSpace) :
    TorusMetric.euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.SharedProofs.p8643 <;> assumption
private theorem tendsto_torusSide {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) :
    Tendsto (fun m : ℕ => PeriodicLattice.torusSide L m) atTop atTop := by
  have h1 : (1 : ℝ) < L := by
    have : 1 < L := lt_of_lt_of_le (by norm_num) hL.2
    exact_mod_cast this
  have hp := tendsto_pow_atTop_atTop_of_one_lt h1
  refine Tendsto.congr (fun m => ?_) (hp.const_mul_atTop (show (0 : ℝ) < 2 by norm_num))
  simp [PeriodicLattice.torusSide]
private theorem tendsto_torusSide_of_strictMono {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    {n : ℕ → ℕ} (hs : StrictMono fun i => PeriodicLattice.torusSide L (n i)) :
    Tendsto (fun i => PeriodicLattice.torusSide L (n i)) atTop atTop := by
  have hinj : Function.Injective n := fun a b h => hs.injective (by simp only [h])
  have : Tendsto n atTop atTop := by
    simpa [Nat.cofinite_eq_atTop] using hinj.tendsto_cofinite
  exact (tendsto_torusSide hL).comp this
theorem torusStatesAreLimitsOfTori_proof
    (hCum : GibbsAtFixedSpacing.CumulantsPolynomialInMomentsAndWeakLimits)
    (hCub : InfiniteLattice.CubicTorusAsQuotient.Statement)
    (hP : InfiniteLattice.CutoffCovering.CoveringIdentification)
    (hW : InfiniteLattice.PeriodicLiftAtCutoff.ClusterPointsAreSequentialLimits) :
    TorusStatesAreLimitsOfTori := by
  intro L hL K β hβ ν hν
  have hmem : ν ∈ InfiniteLattice.weakLimitsAlongSides L K β := by
    rcases hν with ⟨hp, n, hn, hs, hc⟩ | hv
    · exact ⟨hp, n, hn, tendsto_torusSide_of_strictMono hL hs, hc⟩
    · have h₁ := (hP ⟨⟨L, hL, K, ⟨1, one_pos⟩⟩, β, hβ⟩).2.2.2
      have h₂ := (hW L K hL K.pos β hβ).2.1
      exact (Set.ext_iff.1 (h₁.trans h₂.symm) ν).1 hv
  obtain ⟨hp, n, hn, hside, hconv⟩ := hmem
  have hprob : ∀ i, IsProbabilityMeasure (InfiniteLattice.liftedWilsonMeasure L (n i) K β) :=
    fun i => (hP ⟨⟨L, hL, K, ⟨n i, hn i⟩⟩, β, hβ⟩).2.2.1.2.2.1
  refine ⟨n, hn, hside, fun k f hk hlip hcpt hdis => ?_⟩
  let ρ : ℕ → GibbsAtFixedSpacing.BorelProb (CutoffLattice.spacingAt L K) :=
    fun i => ⟨InfiniteLattice.liftedWilsonMeasure L (n i) K β, hprob i⟩
  let p : GibbsAtFixedSpacing.BorelProb (CutoffLattice.spacingAt L K) := ⟨ν, hp⟩
  have hρ : GibbsAtFixedSpacing.BorelProb.TendstoWeak ρ p := fun F hF => hconv F hF
  have ha : 0 < CutoffLattice.spacingAt L K := CutoffLattice.spacingAt_pos hL K
  have hcont : ∀ j, Continuous (f j) := fun j => continuous_of_isLipschitzFor (hlip j)
  have ht := hCum.2.2.1 L K ha ρ p hρ k f hk fun j => by
    obtain ⟨b, hb⟩ := (hcpt j).exists_bound_of_continuous (hcont j)
    exact ⟨(hcont j).measurable, ⟨b, hb⟩, hcpt j⟩
  obtain ⟨r, hr⟩ :=
    (isCompact_iUnion fun i => hcpt i).isBounded.subset_closedBall (0 : InfiniteLattice.AmbientSpace)
  have hsupp : ∀ i, tsupport (f i) ⊆ Metric.closedBall (0 : InfiniteLattice.AmbientSpace) r :=
    fun i => (Set.subset_iUnion (fun i => tsupport (f i)) i).trans hr
  refine Tendsto.congr' ?_ ht
  filter_upwards [hside.eventually_ge_atTop (8 * r)] with i hi
  have hdiam : HasDiameterLE (Metric.closedBall (0 : InfiniteLattice.AmbientSpace) r)
      (PeriodicLattice.torusSide L (n i) / 2) := fun x hx y hy => by
    have h₁ := euclidNormVec_le_two_mul_norm (x - y)
    have h₂ : ‖x‖ ≤ r := by simpa using hx
    have h₃ : ‖y‖ ≤ r := by simpa using hy
    have h₄ := norm_sub_le x y
    linarith
  exact ((hCub ⟨L, hL, K, ⟨n i, hn i⟩⟩ β hβ).2.2.2).ursellFunctionOfMeasure_eq f
    ⟨hk, hlip, hcpt, hdis, _, hdiam, hsupp⟩
end YangMills.Construction.TotalDensitiesGiveASystem
end

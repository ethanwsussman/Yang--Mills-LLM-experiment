import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.Probability.BoundedRealRandomVariable
import YangMills.Construction.SourcesAndGluing.StandingDataAndSigns
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace SourcesAndGluing
section Holomorphic
variable {P : Type*}
def relabelCoordinates {N : ℕ} (e : Fin N ≃ P) : Coordinates.ComplexCoordinates N ≃ (P → ℂ) :=
  e.arrowCongr (Equiv.refl ℂ)
def HolomorphicOnSet (U : Set (P → ℂ)) (F : (P → ℂ) → ℂ) : Prop :=
  ∀ (N : ℕ) (e : Fin N ≃ P),
    Coordinates.ComplexCoordinates.IsHolomorphicIn (relabelCoordinates e ⁻¹' U)
      ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F ∘ relabelCoordinates e)
def EntireFun (F : (P → ℂ) → ℂ) : Prop := HolomorphicOnSet univ F
theorem holomorphicOnSet_iff_complexCoordinates {n : ℕ} (U : Set (Coordinates.ComplexCoordinates n))
    (F : Coordinates.ComplexCoordinates n → ℂ) :
    HolomorphicOnSet U F ↔
      Coordinates.ComplexCoordinates.IsHolomorphicIn U ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F) := by
  constructor
  · intro h
    have e : (relabelCoordinates (Equiv.refl (Fin n)) :
        Coordinates.ComplexCoordinates n → Fin n → ℂ) = id := by
      funext z i
      simp [relabelCoordinates, Equiv.arrowCongr]
    have := h n (Equiv.refl _)
    rw [e] at this
    simpa using this
  · rintro ⟨hO, hc, hd⟩ N e
    have hΦ : Continuous (relabelCoordinates e) := by
      refine continuous_pi fun i => ?_
      simpa [relabelCoordinates, Equiv.arrowCongr] using continuous_apply (e.symm i)
    have key : ∀ (a : Coordinates.ComplexCoordinates N) (j : Fin N) (ζ : ℂ),
        relabelCoordinates e (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) =
          relabelCoordinates e a + ζ • Coordinates.ComplexCoordinates.stdBasisVector (e j) := by
      intro a j ζ
      funext i
      by_cases hi : i = e j
      · subst hi
        simp [relabelCoordinates, Equiv.arrowCongr, Coordinates.ComplexCoordinates.stdBasisVector]
      · have : e.symm i ≠ j := fun h => hi (by rw [← h]; simp)
        simp [relabelCoordinates, Equiv.arrowCongr, Coordinates.ComplexCoordinates.stdBasisVector,
          hi, this]
    refine ⟨hO.preimage hΦ, hc.comp hΦ.continuousOn (fun _ h => h), fun a ha j => ?_⟩
    filter_upwards [hd (relabelCoordinates e a) ha (e j)] with ζ hζ
    have : (fun ζ : ℂ => ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F ∘ relabelCoordinates e)
          (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) =
        fun ζ : ℂ => ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F)
          (relabelCoordinates e a + ζ • Coordinates.ComplexCoordinates.stdBasisVector (e j)) := by
      funext ζ'
      simp only [Function.comp_apply, key]
    rw [this]
    exact hζ
end Holomorphic
def unitDiscAtOne : Set ℂ := {w | ‖w - 1‖ < 1}
def principalLog (w : ℂ) : ℂ := -∑' q : ℕ+, (1 - w) ^ (q : ℕ) / ((q : ℕ) : ℂ)
theorem isOpen_unitDiscAtOne : IsOpen unitDiscAtOne :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
theorem unitDiscAtOne_subset_slitPlane : unitDiscAtOne ⊆ Complex.slitPlane := by
  intro w hw
  have h : ‖w - 1‖ < 1 := hw
  have := Complex.mem_slitPlane_of_norm_lt_one h
  simpa using this
theorem principalLog_eq_log {w : ℂ} (hw : w ∈ unitDiscAtOne) : principalLog w = Complex.log w := by
  have hz : ‖1 - w‖ < 1 := by
    have h : ‖w - 1‖ < 1 := hw
    rwa [norm_sub_rev]
  have h := Complex.hasSum_taylorSeries_neg_log hz
  have hs := (hasSum_nat_add_iff' 1).2 h
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_zero, div_zero,
    sub_zero] at hs
  have ht : ∑' q : ℕ+, (1 - w) ^ (q : ℕ) / ((q : ℕ) : ℂ) = -Complex.log w := by
    have := tsum_pnat_eq_tsum_succ (f := fun q : ℕ => (1 - w) ^ q / (q : ℂ))
    rw [this, hs.tsum_eq]
    simp
  rw [principalLog, ht, neg_neg]
theorem principalLog_one : principalLog 1 = 0 := by
  rw [principalLog_eq_log (by simp [unitDiscAtOne]), Complex.log_one]
theorem exp_principalLog {w : ℂ} (hw : w ∈ unitDiscAtOne) : Complex.exp (principalLog w) = w := by
  rw [principalLog_eq_log hw]
  exact Complex.exp_log (Complex.slitPlane_ne_zero (unitDiscAtOne_subset_slitPlane hw))
theorem hasDerivAt_principalLog {w : ℂ} (hw : w ∈ unitDiscAtOne) :
    HasDerivAt principalLog (1 / w) w := by
  have h := (Complex.hasStrictDerivAt_log (unitDiscAtOne_subset_slitPlane hw)).hasDerivAt
  rw [one_div]
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_unitDiscAtOne.mem_nhds hw] with v hv
  exact principalLog_eq_log hv
theorem differentiableOn_principalLog : DifferentiableOn ℂ principalLog unitDiscAtOne := fun _ hw =>
  (hasDerivAt_principalLog hw).differentiableAt.differentiableWithinAt
section Derivatives
variable {P : Type*}
abbrev firstIndices (n : ℕ) : Finset (Fin n) := Finset.univ
def coordVector [DecidableEq P] (i : P) : P → ℂ := Pi.single i 1
def partialDeriv [DecidableEq P] (i : P) (F : (P → ℂ) → ℂ) : (P → ℂ) → ℂ :=
  fun a => deriv (fun ζ : ℂ => F (a + ζ • coordVector i)) 0
def iteratedPartials [DecidableEq P] (l : List P) (F : (P → ℂ) → ℂ) : (P → ℂ) → ℂ :=
  l.foldr partialDeriv F
def setPartial [LinearOrder P] (J : Finset P) (F : (P → ℂ) → ℂ) : (P → ℂ) → ℂ :=
  iteratedPartials J.sort F
theorem setPartial_empty [LinearOrder P] (F : (P → ℂ) → ℂ) : setPartial ∅ F = F := by
  simp [setPartial, iteratedPartials]
end Derivatives
abbrev IndexPartition (n : ℕ) : Type := Finpartition (firstIndices n)
def blockCount {n : ℕ} (π : IndexPartition n) : ℕ := π.parts.card
def partitionsNoSingletons (n : ℕ) : Finset (IndexPartition n) :=
  Finset.univ.filter fun π => ∀ J ∈ π.parts, 2 ≤ J.card
section Cumulants
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
structure BoundedRVFamily (μ : Measure Ω) (X : Fin n → Ω → ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  one_le : 1 ≤ n
  isBounded : ∀ i, Probability.IsBoundedRealRV (X i)
def cumulant (μ : Measure Ω) (X : Fin n → Ω → ℝ) : ℂ :=
  setPartial (firstIndices n) (fun z => principalLog (Cumulants.momentGeneratingFunction μ X z)) 0
end Cumulants
namespace GluingSetup
variable (D : GluingSetup) {n : ℕ}
structure TorusTestFamily (f : Fin n → D.Torus → ℝ) : Prop where
  one_le : 1 ≤ n
  bounded : ∀ i, TestFunctions.IsBoundedFun (f i)
def wilsonOnGaugeFields : Measure D.gaugeFields :=
  D.gibbsMeasure.comap Subtype.val
def smearedOnGaugeFields (f : D.Torus → ℝ) (U : D.gaugeFields) : ℝ :=
  D.smeared f U.1
def torusConnected (f : Fin n → D.Torus → ℝ) : ℂ :=
  SourcesAndGluing.cumulant D.wilsonOnGaugeFields fun i => D.smearedOnGaugeFields (f i)
def gibbsConnected (ν : Measure D.GridField) (f : Fin n → (Fin 4 → ℝ) → ℝ) : ℂ :=
  SourcesAndGluing.cumulant ν fun i U => InfiniteLattice.smearedEnergy (f i) U
end GluingSetup
end SourcesAndGluing
end YangMills.Construction
end

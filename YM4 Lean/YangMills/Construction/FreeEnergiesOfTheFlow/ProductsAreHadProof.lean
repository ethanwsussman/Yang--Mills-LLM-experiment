import YangMills.Construction.FreeEnergiesOfTheFlow.CompletedObservablesAreBounded
import YangMills.Construction.FreeEnergiesOfTheFlow.FittedResponsesAreMeans
import YangMills.Construction.FreeEnergiesOfTheFlow.ProductsAreHad
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import YangMills.Construction.ResponseInTheExpansion.TwoPointFunctionByTotalCovariance
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.FreeEnergies
open WeightedResponses ResponseInTheExpansion TorusLumps RenormalizationStepParameters ColdStepAtMirrorFrames
theorem conditionalProductMeansStatement_holds (hSt : ResponseInTheExpansion.StageStatesMeasurableStatement)
    (hB : completedObservablesBounded) (hT : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement)
    (hFR : fittedResponseIsConditionalMeanStatement) :
    conditionalProductMeansStatement := by
  intro a ha
  obtain ⟨L₀, r₀, C₀, hr₀, H⟩ := hFR a ha
  refine ⟨L₀, r₀, C₀, hr₀, ?_⟩
  intro L hodd hL Tb hTa hTL hD hCS hOn hrt hCd K
  obtain ⟨y₀, Y₀⟩ := H L hodd hL Tb hTa hTL hD hCS hOn hrt hCd K
  refine ⟨max y₀ Tb.floorMin, fun y hy hRS => ?_⟩
  have hfit := hD.fits y ((le_max_right _ _).trans hy)
  intro β T S tp hSK hOR hRR k f I n _ hbs
  have Y₀' := fun g => Y₀ y ((le_max_left _ _).trans hy) hRS β T S tp hSK hOR hRR g 0 (Nat.zero_le _) n hbs
  have hbd : ∀ (s : ℕ) (i : Fin k), ∃ C : ℝ, 0 ≤ C ∧ Measurable (completedCentered S (f i) s n) ∧
      ∀ u, |completedCentered S (f i) s n u| ≤ C := by
    intro s i
    obtain ⟨hm, C, hC⟩ := (hB _ hfit T S.coeffs s n).1 (fineWeight (f i) _)
    exact ⟨|C| + |centering S (f i) s n|, by positivity, hm.sub_const _, fun u =>
      (abs_sub _ _).trans (add_le_add ((hC u).trans (le_abs_self C)) le_rfl)⟩
  have hprob : ∀ s : ℕ, IsProbabilityMeasure (markedSampleLaw T β s n) := fun s =>
    (hT _ hfit hfit.depth_lt T hOR.isCutoff_bottom hOR.marksMeasurable β (fun _ => 0) s n).1
  have hfield : ∀ s : ℕ, stageSigma T s n ≤ markedSampleMeasurableSpace (Tb.stepParameters y) s n := fun s =>
    (hSt _ hfit T s n).comap_le
  have hint : ∀ s : ℕ, Integrable (fun u => ∏ i ∈ I, completedCentered S (f i) s n u) (markedSampleLaw T β s n) := by
    intro s
    have := hprob s
    choose C hC0 hm hC using hbd s
    refine Integrable.of_bound (Finset.measurable_prod _ fun i _ => hm i).aestronglyMeasurable (∏ i ∈ I, C i)
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hC i u)
  refine ⟨fun s => ⟨hint s, hfield s⟩, ?_⟩
  have h0 := hprob 0
  have hsm : ∀ i, StronglyMeasurable[stageSigma T 0 n] (completedCentered S (f i) 0 n) := by
    intro i
    obtain ⟨C, -, hm, -⟩ := hbd 0 i
    have e : completedCentered S (f i) 0 n = fun a => completedCentered S (f i) 0 n (stageState T 0 n a).1 := rfl
    rw [e]
    exact ((hm.comp measurable_fst).comp (comap_measurable _)).stronglyMeasurable
  have hone : ∀ i, Integrable (completedCentered S (f i) 0 n) (markedSampleLaw T β 0 n) := by
    intro i
    obtain ⟨C, -, hm, hC⟩ := hbd 0 i
    exact Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]; exact hC u)
  have hmean : ∀ᵐ u ∂(markedSampleLaw T β 0 n), ∀ i,
      fittedResponse S (f i) 0 n (stageState T 0 n u) = completedCentered S (f i) 0 n u := by
    rw [ae_all_iff]
    intro i
    have h := (Y₀' (f i)).2.1
    rw [condExp_of_stronglyMeasurable (hfield 0) (hsm i) (hone i)] at h
    exact h
  have hprod : StronglyMeasurable[stageSigma T 0 n] (fun u => ∏ i ∈ I, completedCentered S (f i) 0 n u) :=
    Finset.stronglyMeasurable_fun_prod _ fun i _ => hsm i
  filter_upwards [hmean] with u hu
  unfold conditionalProduct
  rw [condExp_of_stronglyMeasurable (hfield 0) hprod (hint 0)]
  exact Finset.prod_congr rfl fun i _ => (hu i).symm
end YangMills.Construction.FreeEnergies
end

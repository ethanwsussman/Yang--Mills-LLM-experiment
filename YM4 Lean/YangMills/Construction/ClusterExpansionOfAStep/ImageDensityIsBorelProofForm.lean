import YangMills.Construction.ClusterExpansionOfAStep.GasDensityOfAGroundIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.ImageDensityIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.ImageFactorIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheHotLumps
import YangMills.Construction.ClusterExpansionOfAStep.ShareOfTheFieldAboveIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
theorem measurableSet_setOf_isHullState {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
    (hadm : ℓ.Admissible) (hside : ℓ.side ∣ n) (r : ℕ)
    (Y : Finset (TorusFields.TorusSite n)) :
    MeasurableSet {V : TorusFields.TorusField n | TorusLumps.IsHullState ℓ r V Y} := by
  classical
  have e : {V : TorusFields.TorusField n | TorusLumps.IsHullState ℓ r V Y} =
      ⋃ H ∈ {H : Finset (Finset (TorusFields.TorusSite n)) |
      TorusLumps.thickening (2 * r) (H.biUnion id) ⊆ Y ∧
        ∀ X ∈ TorusLumps.chainComponents r Y, ∃ l ∈ H, (l ∩ X).Nonempty},
      {V : TorusFields.TorusField n | TorusLumps.torusHotLumps ℓ V = H} := by
    ext V
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      exact ⟨TorusLumps.torusHotLumps ℓ V, h, rfl⟩
    · rintro ⟨H, h, rfl⟩
      exact h
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun H _ =>
    TorusLumps.measurableSet_torusHotLumps_eq hadm hside H
theorem imageStateDensityMeasurable_of_components
    (hF : StepGas.CoarseFactorExpansionMeasurable) (hZ : GroundBlockActivityMeasurable)
    (hG : GroundBlockDensityMeasurable) (hS : ShareMeasurability.LevelShareOffHotMeasurable) :
    ImageStateDensityMeasurable := by
  intro T hT
  obtain ⟨y₂, h₂⟩ := hF T hT
  obtain ⟨y₃, h₃⟩ := hZ T hT
  obtain ⟨y₄, h₄⟩ := hG T hT
  refine ⟨max y₂ (max y₃ y₄), fun y hy R htab hform n _ hB Y y' => ?_⟩
  classical
  have hy₂ : y₂ ≤ y := (le_max_left _ _).trans hy
  have hy₃ : y₃ ≤ y := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hy
  have hy₄ : y₄ ≤ y := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hy
  have hadm := hform.admissible
  have hside : R.params.side ∣ n := hB.1
  have hl := htab.params_eq
  have hch : ColdChain.ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam
      R.anchorRadius T.σA T.cg T.N := by
    have e1 : R.params.coupling = T.coupling := by rw [hl]; rfl
    have e2 : R.params.side = T.side := by rw [hl]; rfl
    rw [e1, e2, htab.anchorRadius_eq]
    exact hT.chain
  have hσ : R.params.threshold ≤ T.σA := by
    have e1 : R.params.threshold = T.threshold := by rw [hl]; rfl
    have h1 := hT.σ_le
    have h2 := hT.σ_pos
    rw [e1]
    linarith
  have hcond : MeasurableSet {q : TorusFields.TorusField n ×
      (Y → TorusLumps.CoarseLabel R.labels.Ω R.params.side) |
      TorusLumps.IsHullState R.params R.nextRange q.1 Y ∧
        ∀ X ∈ TorusLumps.chainComponents R.nextRange Y,
          StepSettings.coarseFactorExpansion R n q.1 Y q.2 X ≠ 0} := by
    have e : {q : TorusFields.TorusField n × (Y → TorusLumps.CoarseLabel R.labels.Ω R.params.side) |
        TorusLumps.IsHullState R.params R.nextRange q.1 Y ∧
          ∀ X ∈ TorusLumps.chainComponents R.nextRange Y,
            StepSettings.coarseFactorExpansion R n q.1 Y q.2 X ≠ 0} =
        (Prod.fst ⁻¹' {V | TorusLumps.IsHullState R.params R.nextRange V Y}) ∩
          ⋂ X ∈ TorusLumps.chainComponents R.nextRange Y,
            {q | StepSettings.coarseFactorExpansion R n q.1 Y q.2 X ≠ 0} := by
      ext q
      simp
    rw [e]
    refine (measurable_fst (measurableSet_setOf_isHullState hadm hside _ Y)).inter
      (Finset.measurableSet_biInter _ fun X _ => ?_)
    exact ((h₂ y hy₂ R htab hform n hB Y X) (measurableSet_singleton 0)).compl
  have hsh : Measurable fun q : TorusFields.TorusField n ×
      (Y → TorusLumps.CoarseLabel R.labels.Ω R.params.side) =>
      StepCosts.levelShare R.params.coupling R.params.side (R.depth + 1)
        (HoledShares.coldRegion R.params q.1) y' q.1 :=
    (hS R.params T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N hadm hch hσ R.depth n hB y').comp
      measurable_fst
  have e : (fun q : TorusFields.TorusField n × (Y → TorusLumps.CoarseLabel R.labels.Ω R.params.side) =>
      if TorusLumps.IsHullState R.params R.nextRange q.1 Y ∧
          ∀ X ∈ TorusLumps.chainComponents R.nextRange Y,
            StepSettings.coarseFactorExpansion R n q.1 Y q.2 X ≠ 0
      then R.stateDensity T.lam n y' q.1 Y q.2 else 0) = fun q =>
      (if TorusLumps.IsHullState R.params R.nextRange q.1 Y ∧
          ∀ X ∈ TorusLumps.chainComponents R.nextRange Y,
            StepSettings.coarseFactorExpansion R n q.1 Y q.2 X ≠ 0
        then (StepGas.hotCaseGround R q.1 ⟨Y, q.2⟩).groundSetting.blockActivity T.lam y' else 0) +
      (if TorusLumps.IsHullState R.params R.nextRange q.1 Y ∧
          ∀ X ∈ TorusLumps.chainComponents R.nextRange Y,
            StepSettings.coarseFactorExpansion R n q.1 Y q.2 X ≠ 0
        then (StepGas.hotCaseGround R q.1 ⟨Y, q.2⟩).blockDensity y' else 0) +
      (if TorusLumps.IsHullState R.params R.nextRange q.1 Y ∧
          ∀ X ∈ TorusLumps.chainComponents R.nextRange Y,
            StepSettings.coarseFactorExpansion R n q.1 Y q.2 X ≠ 0
        then R.nextCoupling * StepCosts.levelShare R.params.coupling R.params.side (R.depth + 1)
            (HoledShares.coldRegion R.params q.1) y' q.1 -
          (StepGas.coldCaseGround R (TorusFields.trivialField n)).totalDensity T.lam y' else 0) := by
    funext q
    by_cases h : TorusLumps.IsHullState R.params R.nextRange q.1 Y ∧
        ∀ X ∈ TorusLumps.chainComponents R.nextRange Y,
          StepSettings.coarseFactorExpansion R n q.1 Y q.2 X ≠ 0
    · simp only [if_pos h]
      have e1 : R.stateDensity T.lam n y' q.1 Y q.2 =
          ImageDensities.groundDensity R (StepGas.hotCaseGround R q.1 ⟨Y, q.2⟩) T.lam y' :=
        dif_neg (NeZero.ne n)
      rw [e1]
      unfold ImageDensities.groundDensity StepGas.GasGround.totalDensity
      show _ = _
      simp only [StepGas.hotCaseGround]
      ring
    · simp only [if_neg h, add_zero]
  rw [e]
  exact ((h₃ y hy₃ R htab hform n hB Y y').add (h₄ y hy₄ R htab hform n hB Y y')).add
    (Measurable.ite hcond ((hsh.const_mul _).sub measurable_const) measurable_const)
end ClusterExpansionOfAStep
end YangMills.Construction
end

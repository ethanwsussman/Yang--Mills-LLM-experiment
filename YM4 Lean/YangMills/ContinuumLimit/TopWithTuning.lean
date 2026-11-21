import Mathlib
import YangMills.ContinuumLimit.TopAtAPredicate
import YangMills.ContinuumLimit.TuningAtAdmissibleTables
set_option autoImplicit false

open Set

noncomputable section

namespace YangMills.ContinuumLimit

open YangMills.Construction YangMills.Construction.TotalDensities
  YangMills.Construction.RenormalizationStepParameters YangMills.Construction.TrajectoryData
  YangMills.Construction.CouplingFlow YangMills.Construction.TopAux

def TopWithTuning.Statement (Q' : ParameterAssignment → ℝ → Prop) : Prop :=
  ∃ J Lstar : ℕ, 1 ≤ J ∧ ∀ L : ℕ, Odd L → Lstar ≤ L →
    ∃ (ℓ : TorusLumps.StepParameters) (Bs c₅ γ : ℝ) (Nw : ℕ) (CT : ℝ)
      (T : ParameterAssignment) (y c M Cr : ℝ) (Kr : WeightedResponses.ResponseParameters) (lam cr : ℝ),
    ℓ.side = L ∧ ℓ.baseDepth = J ∧ TotalDensitySystem.IsUnitMeshStepParameters ℓ ∧ 2 ≤ Bs ∧ 0 ≤ c₅ ∧
      γ ∈ Ioo (0 : ℝ) 1 ∧ 0 < CT ∧ 1 ≤ Nw ∧
      T.Admissible ∧ T.stepParameters y = ℓ ∧ 0 ≤ Cr ∧
      HasAverageSlope (ReferenceDensity.oneLoopCoefficient T.coupling T.ρA T.lam T.side)
        (slopeConst L) c ∧
      (∀ t, |ScaledVariables.secondStepCoefficient T.coupling T.ρA T.lam T.side t| ≤ M) ∧
      Bs = 2 * T.B ∧ RunTable T y Kr lam cr ∧ Q' T y ∧ TunedAtEveryCutoff T y ∧
      (∀ g ∈ Ioc 0 γ,
        TotalDensitySystem.CouplingConditions ℓ Bs c₅ (3 / 4 * TotalDensitySystem.oneLoopShift L) Nw CT g ∧
          ReferenceFlowBound ℓ Bs T.coupling T.ρA T.lam Cr g) ∧
      (∀ g ∈ Ioc 0 γ, runFloor T y cr < SequencePassage.passageThreshold Bs g) ∧
      ∀ g ∈ Ioc 0 γ, ∀ K : ℕ, ∃! β : ℝ, IsTunedAt T y (SequencePassage.passageThreshold Bs g) K β

theorem top_with_tuning {Q' : ParameterAssignment → ℝ → Prop} (hQ' : HoldsAtAdmissibleParameters Q') :
    TopWithTuning.Statement Q' := by
  obtain ⟨J, L₀, hJ, hTop⟩ :=
    top_at_predicate (HoldsAtAdmissibleParameters.and run_table_at_admissible_tables hQ')
  refine ⟨J, L₀, hJ, fun L hodd hge => ?_⟩
  obtain ⟨ℓ, Bs, c₅, γ, Nw, CT, T, y, c, M, Cr, hside, hdepth, hunit, hBs2, hc₅, hγ, hCT, hNw, hT, hℓ,
    hCr, hS, hM, hBs, ⟨⟨Kr, lam, cr, hRun⟩, hQT⟩, hall⟩ := hTop L hodd hge
  obtain ⟨γ₁, hγ₁, hfl⟩ := exists_coupling_interval_above_floor (y + |cr| + 2)
  have hfloor : ∀ g ∈ Ioc 0 (min γ γ₁), runFloor T y cr < SequencePassage.passageThreshold Bs g := by
    intro g hg
    have h := hfl g ⟨hg.1, hg.2.trans (min_le_right _ _)⟩
    unfold runFloor SequencePassage.passageThreshold
    rw [hBs]
    linarith
  refine ⟨ℓ, Bs, c₅, min γ γ₁, Nw, CT, T, y, c, M, Cr, Kr, lam, cr, hside, hdepth, hunit, hBs2, hc₅,
    ⟨lt_min hγ.1 hγ₁.1, lt_of_le_of_lt (min_le_left _ _) hγ.2⟩, hCT, hNw, hT, hℓ, hCr, hS, hM, hBs,
    hRun, hQT, tuned_of_runTable_closed hRun,
    fun g hg => hall g ⟨hg.1, hg.2.trans (min_le_left _ _)⟩, hfloor, fun g hg K => ?_⟩
  exact ((tuned_at_runFloor_closed hRun K).2.2.2.1 _ (hfloor g hg).le).1

end YangMills.ContinuumLimit

end

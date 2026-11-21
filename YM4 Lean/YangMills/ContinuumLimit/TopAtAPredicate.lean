import Mathlib
import YangMills.Construction.QuaternionicWilsonModel.TheTopOfTheTrajectoryWithTheFlowProof
import YangMills.Construction.TheStatementsProvedTogether.FromTheTopOfTheTrajectoryProof
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
set_option autoImplicit false

open Set

noncomputable section

namespace YangMills.ContinuumLimit

open YangMills.Construction YangMills.Construction.TotalDensities
  YangMills.Construction.RenormalizationStepParameters YangMills.Construction.TrajectoryData
  YangMills.Construction.CouplingFlow YangMills.Construction.TopAux

def TopAtPredicate (Q : ParameterAssignment → ℝ → Prop) : Prop :=
  ∃ J Lstar : ℕ, 1 ≤ J ∧ ∀ L : ℕ, Odd L → Lstar ≤ L →
    ∃ (ℓ : TorusLumps.StepParameters) (Bs c₅ γ : ℝ) (Nw : ℕ) (CT : ℝ)
      (T : ParameterAssignment) (y c M Cr : ℝ),
    ℓ.side = L ∧ ℓ.baseDepth = J ∧ TotalDensitySystem.IsUnitMeshStepParameters ℓ ∧ 2 ≤ Bs ∧ 0 ≤ c₅ ∧
      γ ∈ Ioo (0 : ℝ) 1 ∧ 0 < CT ∧ 1 ≤ Nw ∧
      T.Admissible ∧ T.stepParameters y = ℓ ∧ 0 ≤ Cr ∧
      HasAverageSlope (ReferenceDensity.oneLoopCoefficient T.coupling T.ρA T.lam T.side)
        (slopeConst L) c ∧
      (∀ t, |ScaledVariables.secondStepCoefficient T.coupling T.ρA T.lam T.side t| ≤ M) ∧
      Bs = 2 * T.B ∧ Q T y ∧
      ∀ g ∈ Ioc 0 γ,
        TotalDensitySystem.CouplingConditions ℓ Bs c₅ (3 / 4 * TotalDensitySystem.oneLoopShift L) Nw CT g ∧
          ReferenceFlowBound ℓ Bs T.coupling T.ρA T.lam Cr g

private theorem admissibleParameters_at_unit_coupling
    (hChoose : ClusterExpansionOfAStep.ParametersCanBeChosen)
    {P : ParameterAssignment → ℝ → Prop} (h : HoldsAtAdmissibleParameters P) :
    ∃ J N₀ : ℕ, ∀ N : ℕ, Odd N → N₀ ≤ N → ∃ (T : ParameterAssignment) (y : ℝ), T.Admissible ∧ T.coupling = 1 ∧
      T.baseDepth = J ∧ T.side = N ∧ T.threshold ≤ 1 / 2 ∧ P T y := by
  obtain ⟨A, hA, hP⟩ := h
  obtain ⟨cK, κ, δ₁, J₀, hChosen⟩ := hChoose 1 le_rfl
  obtain ⟨N₀, hN₀⟩ := hChosen A.property hA.property_eventually
  refine ⟨J₀, max N₀ (A.sideFloor 1), fun N hodd hge => ?_⟩
  obtain ⟨T, hc, -, -, -, hJ, hs, hC, hrt, hσ, hn, hCs, hK, hadm, hprop⟩ :=
    hN₀ N hodd (le_trans (le_max_left _ _) hge) (A.derivBoundFloor 1) A.rateCeiling
      (fun D r => min (A.thresholdCeiling D r) (1 / 2))
      A.n₀Floor A.CsFloor A.NFloor hA.rateCeiling_pos
      (fun D r => lt_min (hA.thresholdCeiling_pos D r) (by norm_num))
  obtain ⟨y₀, hy⟩ := hP T hadm
    ⟨by rw [hc, hs]; exact le_trans (le_max_right _ _) hge, by rw [hc]; exact hC, hrt,
      le_trans hσ (min_le_left _ _), hn, hCs, hK, hprop⟩
  exact ⟨T, y₀, hadm, hc, hJ, hs, le_trans hσ (min_le_right _ _), hy y₀ le_rfl⟩

theorem exists_coupling_interval_above_floor (y₂ : ℝ) :
    ∃ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 ∧ ∀ g ∈ Ioc 0 γ, y₂ ≤ g ^ (-2 : ℤ) := by
  have hY : (0 : ℝ) < max 4 y₂ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hs : 0 < Real.sqrt (max 4 y₂) := Real.sqrt_pos.2 hY
  have h2 : (2 : ℝ) ≤ Real.sqrt (max 4 y₂) := by
    apply Real.le_sqrt_of_sq_le
    exact le_trans (by norm_num) (le_max_left _ _)
  refine ⟨(Real.sqrt (max 4 y₂))⁻¹, ⟨inv_pos.2 hs, ?_⟩, fun g hg => ?_⟩
  · exact inv_lt_one_of_one_lt₀ (by linarith)
  have hg0 : 0 < g := hg.1
  have h1 : g * Real.sqrt (max 4 y₂) ≤ 1 := by
    calc g * Real.sqrt (max 4 y₂) ≤ (Real.sqrt (max 4 y₂))⁻¹ * Real.sqrt (max 4 y₂) :=
          mul_le_mul_of_nonneg_right hg.2 hs.le
      _ = 1 := inv_mul_cancel₀ hs.ne'
  have h0 : 0 ≤ g * Real.sqrt (max 4 y₂) := by positivity
  have h3 : g ^ 2 * max 4 y₂ ≤ 1 := by
    have h3 : (g * Real.sqrt (max 4 y₂)) ^ 2 ≤ 1 := by nlinarith
    rwa [mul_pow, Real.sq_sqrt hY.le] at h3
  have hg2 : 0 < g ^ 2 := by positivity
  have h4 : max 4 y₂ ≤ (g ^ 2)⁻¹ := by
    rw [le_inv_comm₀ hY hg2]
    exact (le_div_iff₀ hY).2 (by simpa [one_div] using h3) |>.trans_eq (by simp [one_div])
  have h5 : g ^ (-2 : ℤ) = (g ^ 2)⁻¹ := by
    rw [zpow_neg]; norm_cast
  rw [h5]
  exact le_trans (le_max_right _ _) h4

private theorem firstPassageIndex_eq {B g : ℝ} {x : ℕ → ℝ} {K K' : ℕ}
    (h : SequencePassage.IsFirstPassageIndex B g x K)
    (h' : SequencePassage.IsFirstPassageIndex B g x K') : K' = K := by
  rcases lt_trichotomy K' K with hlt | heq | hgt
  · exact absurd h'.1 (not_le.2 (h.2 K' hlt))
  · exact heq
  · exact absurd h.1 (not_le.2 (h'.2 K hgt))

private theorem referenceFlowBound_of_data {T : ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y)
    (hAdm : D.Admissible) (hData : HasTrajectoryData D) {g : ℝ}
    (hg : 0 < g) (hy : D.floorStar ≤ g ^ (-2 : ℤ))
    (hEq : ExpansionFlowEqTotalFlowAt (T.stepParameters y) D.shift g) :
    ReferenceFlowBound (T.stepParameters y) D.shift T.coupling T.ρA T.lam D.Cr g := by
  intro K β hβ
  obtain ⟨hw, heq⟩ := hEq K
  have hwR : β ∈ SequencePassage.passageWindow D.shift g
      (ClusterExpansionOfAStep.flowCoupling (T.stepParameters y)) K := by
    rw [← hw]
    exact hβ
  have hwD : β ∈ D.passageWindow K g := hwR
  obtain ⟨hnear, hlast⟩ := hData.flow g hg hy K β hwD
  have hx : ∀ k ≤ K, TotalDensityFlow.coupling (T.stepParameters y) β k = D.coupling β k :=
    fun k hk => heq β hwR k hk
  obtain ⟨K', hp⟩ := hData.passage g hg hy β hwD.1
  have hK' : K' = K := firstPassageIndex_eq hwD.2 hp.isFirstPassageIndex
  subst hK'
  have hX : D.X₀ ≤ g ^ (-2 : ℤ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hstays : StaysAbove D.X₀ (couplingAt (T.stepParameters y) β) K' :=
    fun l hl => le_trans hX (hp.coupling_gt l hl).le
  have hb := (hAdm.errorMargin.bounds β).boundsUpTo K' hstays
  refine ⟨fun k hk => hb.flow_pos k hk, fun k hk => ?_, ?_⟩
  · rw [hx k hk]
    exact hnear k hk
  · rw [hx K' le_rfl]
    exact hlast

private theorem flowBound_at_admissible_parameters (hFlowData : trajectoryDataStatement)
    (hEq : expansionFlowEqTotalFlow) :
    HoldsAtAdmissibleParameters fun T y => ∃ c M Cr : ℝ, 0 ≤ Cr ∧
      HasAverageSlope (ReferenceDensity.oneLoopCoefficient T.coupling T.ρA T.lam T.side) (slopeConst T.side) c ∧
      (∀ t, |ScaledVariables.secondStepCoefficient T.coupling T.ρA T.lam T.side t| ≤ M) ∧
      ForSmallCoupling fun g => ReferenceFlowBound (T.stepParameters y) (2 * T.B) T.coupling T.ρA T.lam Cr g := by
  have hFlowDataAt : HoldsAtAdmissibleParameters fun T y => ∃ D : TrajectoryParameters T y, ∀ Bs lam : ℝ,
      2 * T.B ≤ Bs → 0 < lam → lam ≤ D.rateBound →
        (D.withShift Bs lam).Admissible ∧ HasTrajectoryData (D.withShift Bs lam) := by
    obtain ⟨Q, hQ, sideFloor, rateCeiling, thresholdCeiling, n₀Floor, CsFloor, C₀, h1, h2, hT'⟩ := hFlowData
    refine ⟨⟨Q, sideFloor, fun _ => C₀, rateCeiling, thresholdCeiling, n₀Floor, CsFloor, fun _ => 0⟩,
      ⟨hQ, h1, h2⟩, fun T hAdm hMet => ?_⟩
    exact hT' T hAdm hMet.side_ge hMet.rt_le hMet.threshold_le hMet.n₀_ge hMet.Cs_ge hMet.derivBound_ge
      hMet.holds
  refine HoldsAtAdmissibleParameters.mono (HoldsAtAdmissibleParameters.and hFlowDataAt hEq)
    fun T y hAdm hBoth => ?_
  obtain ⟨⟨D, hD⟩, hEqT⟩ := hBoth
  have hrate : 0 < D.rateBound := by
    have hside : (1 : ℝ) < T.side := by
      have h : 2 ^ 40 ≤ T.side := hAdm.L_ge
      have h' : 1 < T.side := lt_of_lt_of_le (by norm_num) h
      exact_mod_cast h'
    have hlog := Real.log_pos hside
    have hpi := Real.pi_pos
    show 0 < 3 / 4 * (11 / (3 * Real.pi ^ 2) * Real.log T.side)
    positivity
  obtain ⟨hH, hData⟩ := hD (2 * T.B) D.rateBound le_rfl hrate le_rfl
  obtain ⟨y₆, fR⟩ := hEqT (2 * T.B) le_rfl
  refine ⟨D.cH, D.Md, D.Cr, hH.errorMargin.Cr_nonneg, hH.errorMargin.slope, hH.errorMargin.secondStep_le,
    max (D.withShift (2 * T.B) D.rateBound).floorStar y₆, fun g hg hy => ?_⟩
  exact referenceFlowBound_of_data (D.withShift (2 * T.B) D.rateBound) hH hData hg
    (le_trans (le_max_left _ _) hy) (fR g hg (le_trans (le_max_right _ _) hy))

theorem top_at_predicate {Q : ParameterAssignment → ℝ → Prop} (hQ : HoldsAtAdmissibleParameters Q) :
    TopAtPredicate Q := by
  obtain ⟨J, L₀, hL₀⟩ := admissibleParameters_at_unit_coupling
    TheStatementsProvedTogether.step_parameters_exist
    (HoldsAtAdmissibleParameters.and
      (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and
        (HoldsAtAdmissibleParameters.and TheStatementsProvedTogether.flow_passes
          TheStatementsProvedTogether.pairs_tied_to_wilson_measure)
        TheStatementsProvedTogether.total_density_subseq_limit_exists)
        TheStatementsProvedTogether.exists_coupling_constants)
        (flowBound_at_admissible_parameters TheStatementsProvedTogether.firstPassagePath_data
          TheStatementsProvedTogether.expansionFlow_eq_totalFlow))
      hQ)
  have hJ1 : 1 ≤ J := by
    obtain ⟨k, hk⟩ : ∃ k, Odd k ∧ L₀ ≤ k := ⟨2 * L₀ + 1, ⟨L₀, rfl⟩, by omega⟩
    obtain ⟨T, -, hT', -, hJ, -, -, -⟩ := hL₀ k hk.1 hk.2
    have h := hT'.J₀_ge
    omega
  refine ⟨J, L₀, hJ1, fun L hodd hge => ?_⟩
  obtain ⟨T, y, hT', h1, hJ, h2, hσ, ⟨⟨⟨⟨⟨c, Nw, hc, hNw, fP⟩, CT, hCT, y₂, fT⟩, y₃, fL⟩, c', fN⟩,
    cH, Md, Cr, hCr, hS, hM, y₅, fW⟩, hQT⟩ := hL₀ L hodd hge
  subst h2
  obtain ⟨y₁, gP⟩ := fP (max c c') (le_max_left _ _)
  obtain ⟨y₄, gN⟩ := fN (max c c') (le_max_right _ _)
  obtain ⟨γ, hγ, hfl⟩ := exists_coupling_interval_above_floor (max y₁ (max y₂ (max y₃ (max y₄ y₅))))
  have hall : ∀ g ∈ Ioc 0 γ, y₁ ≤ g ^ (-2 : ℤ) ∧ y₂ ≤ g ^ (-2 : ℤ) ∧ y₃ ≤ g ^ (-2 : ℤ) ∧
      y₄ ≤ g ^ (-2 : ℤ) ∧ y₅ ≤ g ^ (-2 : ℤ) :=
    fun g hg => by simpa only [max_le_iff] using hfl g hg
  have hB' := hT'.B_ge
  refine ⟨T.stepParameters y, 2 * T.B, max c c', γ, Nw, CT, T, y, cH, Md, Cr, rfl, hJ,
    ⟨h1, hT'.L_odd, hT'.L_ge, ?_, hT'.L_gt, hT'.σ_pos, (by show T.threshold < 1; linarith)⟩,
    by linarith, le_trans hc (le_max_left _ _), hγ, hCT, hNw, hT', rfl, hCr, hS, hM, rfl, hQT,
    fun g hg => ?_⟩
  · show 1 ≤ T.baseDepth
    omega
  obtain ⟨a₁, a₂, a₃, a₄, a₅⟩ := hall g hg
  obtain ⟨l₁, l₂, l₃⟩ := fL g hg.1 a₃
  exact ⟨⟨gP g hg.1 a₁, fT g hg.1 a₂, l₁, l₂, l₃, gN g hg.1 a₄⟩, fW g hg.1 a₅⟩

end YangMills.ContinuumLimit

end

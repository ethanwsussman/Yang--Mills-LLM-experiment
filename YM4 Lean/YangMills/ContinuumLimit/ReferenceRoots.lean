import YangMills.ContinuumLimit.ReferenceTrial
set_option autoImplicit false
noncomputable section
namespace YangMills.BranchHot
open Filter Set Construction ContinuumLimit Formulation
open scoped Topology
open Construction.PeriodicLattice Construction.TheStatementsProvedTogether

theorem bare_root_with_window_data {Q : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (hQ : TotalDensities.HoldsAtAdmissibleParameters Q) :
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
      ∃ (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ)
        (Kr : WeightedResponses.ResponseParameters) (lam cr Bs γ c₅ speed CT c : ℝ) (Nw : ℕ),
        (T.stepParameters y).side = L ∧ CouplingFlow.HasAverageSlope (FamilyNorms.ParameterAssignment.oneLoop T) (CouplingFlow.slopeConst L) c ∧ RunTable T y Kr lam cr ∧ Q T y ∧ 0 < γ ∧ 2 ≤ Bs ∧
        (∀ g ∈ Ioc (0:ℝ) γ, TotalDensitySystem.CouplingConditions (T.stepParameters y) Bs c₅ speed Nw CT g) ∧
        ∀ H : ℝ, ∃ (M : ℕ+) (δ : ℝ), 8 ≤ torusSide L M ∧ 0 < δ ∧
          ∀ᶠ K : ℕ in atTop, ∀ g₀ ∈ Ioo (0:ℝ) δ,
            let g := renormalizedBareCoupling L M K g₀
            let b := (g ^ 2)⁻¹
            let P := TotalDensityFlow.coupling (T.stepParameters y) b K
            IsLeast {t : ℝ | 0 < t ∧ referenceResponse L M K (t ^ 2)⁻¹ = fixedPhysicalLevel g₀} g ∧
              b ∈ runDomain T y K ∧ IsTunedAt T y P K b ∧ H ≤ P := by
  obtain ⟨ϑ₀, hϑ₀, J, Lstar, _, top⟩ := tuned_top hQ
  refine ⟨max Lstar 13, fun L hodd hlarge => ?_⟩
  obtain ⟨p, Bs, c₅, γ, Nw, CT, T, y, c, U, Cr, Kr, lam, cr, hL, _, _, hBs, _, hγ, _, _, _, heq,
    _, hSlope, _, _, hRun, hQT, _, htop⟩ := top L hodd ((le_max_left ..).trans hlarge)
  refine ⟨T,y,Kr,lam,cr,Bs,γ,c₅,3/4*TotalDensitySystem.oneLoopShift L,CT,c,Nw,heq ▸ hL,hSlope,hRun,hQT,hγ.1,hBs,?_,fun H => ?_⟩
  · intro g hg
    rw [heq]
    exact (htop g hg).1
  obtain ⟨a, ha, habove⟩ := exists_coupling_interval_above_floor H
  let G := min a γ
  have hG : G ∈ Ioc (0:ℝ) γ := ⟨lt_min ha.1 hγ.1, min_le_right ..⟩
  obtain ⟨_, _, hfloor, _, hpos, htune, hlim⟩ := htop G hG
  let P := SequencePassage.passageThreshold Bs G
  have hH : H ≤ P := by
    have h := habove G ⟨hG.1,min_le_left ..⟩
    dsimp [P,SequencePassage.passageThreshold]
    linarith
  choose b hb using fun k => (htune k).exists
  have h13 : 13 ≤ L := (le_max_right ..).trans hlarge
  let s : Conventions.StandingParameters := ⟨L,⟨hodd,h13⟩,1,1⟩
  obtain ⟨R, hR, ρ, hρ, hhot⟩ := all_cutoff_trial hϑ₀ s hL.symm hpos hlim b hb (runDepth lam cr)
  let M : ℕ+ := ⟨(s.m:ℕ)+R, s.m.pos.trans_le (Nat.le_add_right ..)⟩
  let sM : Conventions.StandingParameters := ⟨L,s.isAdmissible,1,M⟩
  obtain ⟨δ,hδ,hsmall⟩ := fixedPhysicalLevel_small hρ
  refine ⟨M,δ,?_,hδ,?_⟩
  · change 8 ≤ 2 * (L:ℝ) ^ (1 + R)
    have hL1 : 1 ≤ (L:ℝ) := by exact_mod_cast (show 1 ≤ L by omega)
    have h8 : 8 ≤ (L:ℝ) := by exact_mod_cast (show 8 ≤ L by omega)
    have hp := one_le_pow₀ hL1 (n:=R)
    rw [pow_add,pow_one]
    nlinarith
  filter_upwards [hhot, eventually_ge_atTop 1] with k hcross hk
  intro g₀ hg₀
  let bk := b (k+R)
  let bp := TotalDensityFlow.coupling (T.stepParameters y) bk k
  have ht : IsTunedAt T y P (k+R) bk := hb (k+R)
  have hbp : IsTunedAt T y bp k bk := ⟨⟨ht.1.1, fun j hj => ht.1.2 j (by omega)⟩,rfl⟩
  have hx := (above_iff_total expansion_gives_total_flow total_density_flow_unique hRun).mp ht.1
  have hagree := (total_flow_of_above_total expansion_gives_total_flow total_density_flow_unique hRun ht.1).2
  have hdesc := hRun.descent bk hx.1 (k+R) hx.2 k (Nat.le_add_right ..)
  change lam * ((↑(k + R) : ℝ) - ↑k) - cr ≤ ResponseInTheExpansion.flowCouplings (T.stepParameters y) bk k - ResponseInTheExpansion.flowCouplings (T.stepParameters y) bk (k+R) at hdesc
  rw [← hagree k (Nat.le_add_right ..), ← hagree (k+R) le_rfl, ht.2, Nat.cast_add] at hdesc
  have hcr := FirstPassageOfATunedPair.lt_mul_runDepth (c₅ := cr) hRun.lam_pos
  have hmul := mul_le_mul_of_nonneg_left (show (runDepth lam cr : ℝ) ≤ R by exact_mod_cast hR) hRun.lam_pos.le
  have hf : P ≤ bp := by dsimp [bp]; linarith [le_abs_self cr]
  have hbk : 0 < bk := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (hRun.adm.fits y hRun.floor).y₁_ge) ht.1.1
  let f := referenceResponse L M k
  have hcov (z : ℝ) (hz : 0 < z) : f z =
      ReferenceCalibration.energyCovariance sM ⟨k,hk⟩ (fixedReferenceTests L M) z :=
    ReferenceCalibration.reference_covariance_eq sM ⟨k,hk⟩ (fixedReferenceTests L M) hz
  have hcont : ContinuousOn f (Ioi 0) :=
    (ReferenceCalibration.covariance_continuous sM ⟨k,hk⟩ (fixedReferenceTests L M)).continuousOn.congr
      (fun z hz => hcov z hz)
  have hcold : Tendsto f atTop (𝓝 0) :=
    (ReferenceCalibration.covariance_cold sM ⟨k,hk⟩ (fixedReferenceTests L M)).congr'
      ((eventually_gt_atTop (0:ℝ)).mono fun z hz => (hcov z hz).symm)
  have hr := hsmall g₀ hg₀
  obtain ⟨hmin, hm⟩ := leastBareAt_of_trial (F:=f) hbk hr.1 (hr.2.le.trans hcross.le) hcont hcold
  let g := renormalizedBareCoupling L M k g₀
  have hg : 0 < g := hmin.1.1
  have hlargeβ : bk ≤ (g^2)⁻¹ := by
    have hi := inv_anti₀ (sq_pos_of_pos hg) (pow_le_pow_left₀ hg.le hm 2)
    simpa [inv_pow,Real.sq_sqrt hbk.le] using hi
  obtain ⟨htuned, hlo, _⟩ := tuned_branch_of_le hRun k (hfloor.le.trans hf) hbp hlargeβ
  have hterm : bp ≤ TotalDensityFlow.coupling (T.stepParameters y) (g^2)⁻¹ k := by
    have hn := sub_nonneg.mpr hlargeβ
    linarith
  have hdom := (tuned_at_runFloor_closed hRun k).2.2.2.1 _ ((hfloor.le.trans hf).trans hterm)
  exact ⟨hmin, hdom.2 _ htuned, htuned, (hH.trans hf).trans hterm⟩

end YangMills.BranchHot
end





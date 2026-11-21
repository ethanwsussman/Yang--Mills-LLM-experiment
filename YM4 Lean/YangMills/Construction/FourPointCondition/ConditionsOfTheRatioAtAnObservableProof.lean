import YangMills.Construction.FourPointCondition.ConditionsOfTheRatioAtAnObservable
import YangMills.Construction.FourPointCondition.TransportsOfADilatedPair
import YangMills.Construction.SystemOfAdmissibleConstants.TheThresholdsAlongTheTrajectoryProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPair
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology
namespace YangMills.Construction.FourPointCondition
private theorem oneLoopCoeff_pos : 0 < oneLoopCoeff := by
  unfold oneLoopCoeff
  have := Real.pi_pos
  norm_num [ParameterChoice.colorNumber]
  positivity
abbrev _root_.YangMills.SharedProofs.p28620 := @oneLoopCoeff_pos
private theorem amplitudeConstant_pos : 0 < TwoPointFunction.amplitudeConstant := by
  unfold TwoPointFunction.amplitudeConstant
  have := Real.pi_pos
  norm_num [ParameterChoice.colorNumber]
  positivity
private theorem levelMesh_zero_eq (L K : ℕ) : levelMesh L K 0 = ((L : ℝ) ^ K)⁻¹ := by
  have : PeriodicLattice.meshSize L ((K : ℤ) - ((0 : ℕ) : ℤ)) = PeriodicLattice.meshSize L (K : ℤ) := by simp
  unfold levelMesh
  rw [this, RoomFunctions.meshSize_natCast_eq]
private theorem eventually_log_mul_sq_cube_le {A : ℝ} (hA : 0 < A) :
    ∀ᶠ u : ℝ in atTop, Real.log (A * u ^ 2) ^ 3 ≤ u := by
  have h1 : (fun x : ℝ => Real.log x ^ 3) =o[atTop] (id : ℝ → ℝ) := Real.isLittleO_pow_log_id_atTop
  have h2 := h1.def (c := 1 / 27) (by norm_num)
  filter_upwards [h2, eventually_gt_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log A), Real.tendsto_log_atTop.eventually_ge_atTop 0] with u hu hu1 hlA hl0
  have hu0 : 0 < u := by linarith
  have hlog : Real.log (A * u ^ 2) = Real.log A + 2 * Real.log u := by
    rw [Real.log_mul hA.ne' (by positivity), Real.log_pow]
    norm_num
  have h3 : Real.log (A * u ^ 2) ≤ 3 * Real.log u := by rw [hlog]; linarith
  have h4 : Real.log (A * u ^ 2) ^ 3 ≤ (3 * Real.log u) ^ 3 :=
    (Odd.strictMono_pow (by decide : Odd 3)).monotone h3
  have h5 : Real.log u ^ 3 ≤ 1 / 27 * u := by
    have := hu
    simp only [id, Real.norm_eq_abs, abs_of_pos hu0, abs_of_nonneg (pow_nonneg hl0 3)] at this
    exact this
  nlinarith
private theorem tendsto_log_one_div_nhdsGT_zero :
    Tendsto (fun d : ℝ => Real.log (1 / d)) (𝓝[>] 0) atTop := by apply _root_.YangMills.SharedProofs.p8376 <;> assumption
private theorem exists_cutoff_bound {C : ℕ → ℝ} (hC : RoomFunctions.IsSubexpGrowth C) {L : ℕ} (hL : 2 ≤ L)
    {lam B Ca βv : ℝ} (n₀ : ℕ) (hlam : 0 < lam) (hB : 0 < B) :
    ∃ K₁ : ℕ, ∀ K : ℕ, K₁ ≤ K →
      βv ≤ lam * K - Ca ∧ C K * (L : ℝ) ^ n₀ ≤ (L : ℝ) ^ ((lam * K - Ca) / (4 * B)) := by
  have hlL := RoomFunctions.log_base_pos hL
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  set ε : ℝ := lam * Real.log L / (8 * B) with hε
  have hε0 : 0 < ε := by positivity
  have h1 : Tendsto (fun K : ℕ => lam * (K : ℝ) - Ca) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop hlam)
  have h2 : Tendsto (fun K : ℕ => ε * (K : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hε0
  have h3 := hC.tendsto_log_div_nat.eventually (gt_mem_nhds hε0)
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.1 ((h1.eventually_ge_atTop βv).and
    ((h2.eventually_ge_atTop (n₀ * Real.log L + Ca * Real.log L / (4 * B))).and
      (h3.and (eventually_gt_atTop 0))))
  refine ⟨K₁, fun K hK => ?_⟩
  obtain ⟨ha, hb, hc, hd⟩ := hK₁ K hK
  refine ⟨ha, ?_⟩
  have hCK : 0 < C K := lt_of_lt_of_le one_pos (hC.one_le_apply K)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hd
  have hlogC : Real.log (C K) ≤ ε * K := by
    rw [div_lt_iff₀ hK0] at hc
    exact hc.le
  have hexp : Real.log (C K) + n₀ * Real.log L ≤ (lam * K - Ca) / (4 * B) * Real.log L := by
    have e : (lam * (K : ℝ) - Ca) / (4 * B) * Real.log L = 2 * (ε * K) - Ca * Real.log L / (4 * B) := by
      rw [hε]
      field_simp
      ring
    rw [e]
    linarith
  have hlhs : C K * (L : ℝ) ^ n₀ = Real.exp (Real.log (C K) + n₀ * Real.log L) := by
    rw [Real.exp_add, Real.exp_log hCK, ← Real.log_pow, Real.exp_log (by positivity)]
  rw [hlhs, Real.rpow_def_of_pos hL0, mul_comm (Real.log (L : ℝ))]
  exact Real.exp_le_exp.2 hexp
section LimsupBounds
variable {ℓ : TorusLumps.StepParameters} {vt lam Ca d₀ : ℝ} {n₀ : ℕ} {R : CouplingEvaluation}
  {φ ψ : (Fin 4 → ℝ) → ℝ}
private theorem inverseEighthKernel_pos (hG : TestPairs.GeometryAndKernelBounds) (hvt0 : 0 < vt) (hvt1 : vt ≤ 1)
    (hpair : (φ, ψ) ∈ TestFunctions.separatedPairsR4 1 vt) (hφ : TestFunctions.uniformNorm φ = 1)
    (hψ : TestFunctions.uniformNorm ψ = 1) : 0 < TestFunctions.inverseEighthKernel φ ψ := by
  obtain ⟨x₁, x₂, hb₁, hb₂, c₁, c₂⟩ := id hpair
  have hb := (hG.1 1 vt ⟨one_pos, hvt0, hvt1⟩ x₁ x₂ φ ψ hpair
    ⟨⟨hb₁.2.2.2.1, hb₁.2.2.2.2.1, hb₁.2.2.2.2.2⟩, ⟨hb₂.2.2.2.1, hb₂.2.2.2.2.1, hb₂.2.2.2.2.2⟩, c₁, c₂⟩).1
  obtain ⟨h1, h2, _, _⟩ := hb.2.2.2.2
  rw [hφ, hψ] at h1
  have : 0 < TestPairs.kernelLowerConst * vt ^ 2 * 1 * 1 := by
    unfold TestPairs.kernelLowerConst
    positivity
  linarith
private theorem twoPointLimsupAtScale_between (hT : dilatedPairPeriodizationStatement) (hfit : ℓ.Admissible)
    (hvt0 : 0 < vt) (hvt1 : vt ≤ 1)
    (hl : EvaluationLaws R ℓ.side vt lam Ca d₀ n₀) (hpair : (φ, ψ) ∈ TestFunctions.separatedPairsR4 1 vt)
    (hφ : TestFunctions.uniformNorm φ = 1) (hψ : TestFunctions.uniformNorm ψ = 1)
    (hK : 0 < TestFunctions.inverseEighthKernel φ ψ) {K : ℕ+} {β d : ℝ} (hdat : R.IsFirstPassage K β)
    (hd : d ∈ Ioc (0 : ℝ) d₀) (hdeep : R.IsDeepEnough ℓ.side K n₀ d) :
    ((2 / 9 * TwoPointFunction.amplitudeConstant * TestFunctions.inverseEighthKernel φ ψ *
        R.coupling K β d ^ 4 : ℝ) : EReal) ≤
        twoPointLimsupAtScale ℓ.side K β R.sides φ ψ d ∧
      twoPointLimsupAtScale ℓ.side K β R.sides φ ψ d ≤
        ((8 / 3 * TwoPointFunction.amplitudeConstant * TestFunctions.inverseEighthKernel φ ψ *
          R.coupling K β d ^ 4 : ℝ) : EReal) := by
  obtain ⟨M, hM⟩ := hT ℓ vt d φ ψ hfit hd.1 hvt0 hvt1 hpair hφ hψ
  have hne : (atTop ⊓ 𝓟 {m : ℕ | PeriodicLattice.torusSide ℓ.side m ∈ R.sides}).NeBot := by
    refine frequently_mem_iff_neBot.1 (frequently_atTop.2 fun a => ?_)
    obtain ⟨m, hm, hs⟩ := hl.sides_unbounded a
    exact ⟨m, hm, hs⟩
  have hg := hl.coupling_pos K β hdat d hd hdeep
  have hz := hl.fieldNorm_mem K β hdat d hd hdeep
  set g := R.coupling K β d
  set z := R.fieldNorm K β d
  set A := TwoPointFunction.amplitudeConstant with hA
  have hA0 : 0 < A := amplitudeConstant_pos
  set Y := A * TestFunctions.inverseEighthKernel φ ψ * g ^ 4 with hY
  have hY0 : 0 < Y := by positivity
  have key : ∀ᶠ m in atTop ⊓ 𝓟 {m : ℕ | PeriodicLattice.torusSide ℓ.side m ∈ R.sides},
      2 / 9 * Y ≤ (twoPointPeriodized ℓ.side K β (rescale d φ) (rescale d ψ) m).re ∧
        (twoPointPeriodized ℓ.side K β (rescale d φ) (rescale d ψ) m).re ≤ 8 / 3 * Y := by
    have e1 : ∀ᶠ m in atTop ⊓ 𝓟 {m : ℕ | PeriodicLattice.torusSide ℓ.side m ∈ R.sides}, M ≤ m :=
      (eventually_ge_atTop M).filter_mono inf_le_left
    have e2 : ∀ᶠ m in atTop ⊓ 𝓟 {m : ℕ | PeriodicLattice.torusSide ℓ.side m ∈ R.sides},
        PeriodicLattice.torusSide ℓ.side m ∈ R.sides :=
      eventually_inf_principal.2 (Eventually.of_forall fun _ h => h)
    filter_upwards [e1, e2] with m hm hs
    obtain ⟨hclass, -, hker⟩ := hM m hm
    obtain ⟨ε, hε, heq⟩ := hl.twoPoint K β hdat m hs d hd hdeep _ _ hclass
    have hre : (twoPointPeriodized ℓ.side K β (rescale d φ) (rescale d ψ) m).re =
        z ^ 2 * (1 + ε) * Y := by
      have : twoPointPeriodized ℓ.side K β (rescale d φ) (rescale d ψ) m =
          ((z ^ 2 * A * g ^ 4 * TestFunctions.inverseEighthKernelTorus (ℓ := PeriodicLattice.torusSide ℓ.side m)
            (TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side m) (fun x => φ (d⁻¹ • x)))
            (TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side m) (fun x => ψ (d⁻¹ • x))) *
              (1 + ε) : ℝ) : ℂ) := heq
      rw [this, hker, Complex.ofReal_re, hY]
      ring
    rw [hre]
    obtain ⟨hε1, hε2⟩ := abs_le.1 hε
    have hz2a : 4 / 9 ≤ z ^ 2 := by nlinarith [hz.1]
    have hz2b : z ^ 2 ≤ 16 / 9 := by nlinarith [hz.1, hz.2]
    have hw1 : 2 / 9 ≤ z ^ 2 * (1 + ε) := by nlinarith
    have hw2 : z ^ 2 * (1 + ε) ≤ 8 / 3 := by nlinarith
    exact ⟨mul_le_mul_of_nonneg_right hw1 hY0.le, mul_le_mul_of_nonneg_right hw2 hY0.le⟩
  have hlow : (((2 / 9 * Y : ℝ)) : EReal) ≤ twoPointLimsupAtScale ℓ.side K β R.sides φ ψ d := by
    refine le_limsup_of_frequently_le (Eventually.frequently (key.mono fun m h => ?_))
    exact EReal.coe_le_coe_iff.2 h.1
  have hup : twoPointLimsupAtScale ℓ.side K β R.sides φ ψ d ≤ (((8 / 3 * Y : ℝ)) : EReal) := by
    refine limsup_le_of_le (h := key.mono fun m h => ?_)
    exact EReal.coe_le_coe_iff.2 h.2
  have c1 : 2 / 9 * A * TestFunctions.inverseEighthKernel φ ψ * g ^ 4 = 2 / 9 * Y := by rw [hY]; ring
  have c2 : 8 / 3 * A * TestFunctions.inverseEighthKernel φ ψ * g ^ 4 = 8 / 3 * Y := by rw [hY]; ring
  rw [c1, c2]
  exact ⟨hlow, hup⟩
end LimsupBounds
set_option maxHeartbeats 1000000 in
theorem ratioConditionsEventually_holds (hT : dilatedPairPeriodizationStatement)
    (hG : TestPairs.GeometryAndKernelBounds) : ratioConditionsEventually := by
  intro ℓ vt lam Ca d₀ n₀ R φ ψ βv nv δv hfit hvt0 hvt1 hl hpair hφ hψ hδ
  have hK := inverseEighthKernel_pos hG hvt0 hvt1 hpair hφ hψ
  refine ⟨hK, ?_⟩
  have hL2 : 2 ≤ ℓ.side := le_trans (by norm_num) hfit.L_ge
  have hL1 : (1 : ℝ) ≤ ℓ.side := by exact_mod_cast (by omega : 1 ≤ ℓ.side)
  have hL0 : (0 : ℝ) < ℓ.side := by linarith
  have hB := hfit.B_pos
  have hd₀ := hl.d₀_mem
  have ha := oneLoopCoeff_pos
  have hA0 : 0 < TwoPointFunction.amplitudeConstant := amplitudeConstant_pos
  set a := oneLoopCoeff with ha_def
  set A := TwoPointFunction.amplitudeConstant with hA_def
  set X := A * TestFunctions.inverseEighthKernel φ ψ with hX
  have hX0 : 0 < X := by positivity
  obtain ⟨K₁, hK₁⟩ := exists_cutoff_bound (βv := βv) (Ca := Ca) hl.room hL2 n₀ hl.lam_pos hB
  set Ac : ℝ := 9 / 2 / X / (2 / 3 * a) ^ 2 with hAc
  have hAc0 : 0 < Ac := by positivity
  have hdep := RoomFunctions.tendsto_scaleDepth hl.room hL2
  have hu := tendsto_log_one_div_nhdsGT_zero
  have hu2 : Tendsto (fun d : ℝ => Real.log (1 / d) ^ 2) (𝓝[>] 0) atTop :=
    (tendsto_pow_atTop (by norm_num)).comp hu
  have hP : ∀ᶠ d : ℝ in 𝓝[>] 0, d < d₀ ∧ 8 / 3 * X * (4 / 3 * a) ^ 2 ≤ δv * Real.log (1 / d) ^ 2 ∧
      nv ≤ R.room (RoomFunctions.scaleDepth ℓ.side R.room d) ∧
      K₁ ≤ RoomFunctions.scaleDepth ℓ.side R.room d ∧
      Real.log (Ac * Real.log (1 / d) ^ 2) ^ 3 ≤ Real.log (1 / d) := by
    have e1 : ∀ᶠ d : ℝ in 𝓝[>] 0, d < d₀ := by
      filter_upwards [Ioo_mem_nhdsGT hd₀.1] with d h using h.2
    have e2 := (hu2.const_mul_atTop hδ).eventually_ge_atTop (8 / 3 * X * (4 / 3 * a) ^ 2)
    have e3 := (hl.room.tendsto_atTop_atTop.comp hdep).eventually_ge_atTop nv
    have e4 := hdep.eventually_ge_atTop K₁
    have e5 := hu.eventually (eventually_log_mul_sq_cube_le hAc0)
    filter_upwards [e1, e2, e3, e4, e5] with d h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨d₁, hd₁, hsub⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 hP
  have hd₁' : (0 : ℝ) < d₁ := hd₁
  refine ⟨min d₁ d₀, ⟨lt_min hd₁' hd₀.1, min_le_right _ _⟩, ?_⟩
  have hPd : ∀ d ∈ Ioc (0 : ℝ) (min d₁ d₀), _ := fun d (hd : d ∈ Ioc (0 : ℝ) (min d₁ d₀)) =>
    hsub ⟨hd.1, hd.2.trans (min_le_left _ _)⟩
  have hd₀' : ∀ d ∈ Ioc (0 : ℝ) (min d₁ d₀), d ∈ Ioc (0 : ℝ) d₀ := fun d hd =>
    ⟨hd.1, hd.2.trans (min_le_right _ _)⟩
  intro K β hdat d hd hdeep
  obtain ⟨-, -, hnvs, hK₁s, hcube⟩ := hPd d hd
  have hdpos : 0 < d := hd.1
  have hdepth : ((R.depthAt ℓ.side d : ℕ) : ℤ) + n₀ ≤ ((K : ℕ) : ℤ) := by
    have : (n₀ : ℤ) ≤ ((K : ℕ) : ℤ) - (R.depthAt ℓ.side d : ℤ) := hdeep
    omega
  have hdepth' : RoomFunctions.scaleDepth ℓ.side R.room d + n₀ ≤ (K : ℕ) := by exact_mod_cast hdepth
  have hKK : K₁ ≤ (K : ℕ) := by omega
  obtain ⟨hβK, hroomK⟩ := hK₁ K hKK
  have hslope : lam * ((K : ℕ) : ℝ) - Ca ≤ β := by
    have := hl.cutoff_le K β hdat
    rw [le_div_iff₀ hl.lam_pos] at this
    linarith
  have hsp : levelMesh ℓ.side K 0 = ((ℓ.side : ℝ) ^ (K : ℕ))⁻¹ := levelMesh_zero_eq _ _
  have hsp0 : 0 < levelMesh ℓ.side K 0 := by rw [hsp]; positivity
  refine ⟨hβK.trans hslope, ?_, ?_,
    (twoPointLimsupAtScale_between hT hfit hvt0 hvt1 hl hpair hφ hψ hK hdat (hd₀' d hd) hdeep).2,
    (twoPointLimsupAtScale_between hT hfit hvt0 hvt1 hl hpair hφ hψ hK hdat (hd₀' d hd) hdeep).1, ?_⟩
  · rw [le_div_iff₀ hsp0]
    have h1 := RoomFunctions.mul_meshSize_scaleDepth_le hl.room hL2 hdpos
    have h2 : PeriodicLattice.meshSize ℓ.side ((K : ℕ) : ℤ) ≤
        PeriodicLattice.meshSize ℓ.side (RoomFunctions.scaleDepth ℓ.side R.room d : ℕ) :=
      RoomFunctions.meshSize_natCast_anti hL2 (by omega)
    have h3 : levelMesh ℓ.side K 0 = PeriodicLattice.meshSize ℓ.side ((K : ℕ) : ℤ) := by
      rw [hsp, RoomFunctions.meshSize_natCast_eq]
    have hC0 : 0 < R.room (RoomFunctions.scaleDepth ℓ.side R.room d) :=
      lt_of_lt_of_le one_pos (hl.room.one_le_apply _)
    calc nv * levelMesh ℓ.side K 0 ≤ R.room (RoomFunctions.scaleDepth ℓ.side R.room d) * levelMesh ℓ.side K 0 :=
          mul_le_mul_of_nonneg_right hnvs hsp0.le
      _ ≤ R.room (RoomFunctions.scaleDepth ℓ.side R.room d) *
            PeriodicLattice.meshSize ℓ.side (RoomFunctions.scaleDepth ℓ.side R.room d : ℕ) := by
          rw [h3]
          exact mul_le_mul_of_nonneg_left h2 hC0.le
      _ ≤ d := h1
  · intro d' hd'
    have hfl : 0 < (ℓ.side : ℝ) ^ (β / (4 * ℓ.B)) * levelMesh ℓ.side K 0 :=
      mul_pos (Real.rpow_pos_of_pos hL0 _) hsp0
    have hd'pos : 0 < d' := lt_of_lt_of_le hfl hd'.1
    have hd'mem : d' ∈ Ioc (0 : ℝ) (min d₁ d₀) := ⟨hd'pos, hd'.2.trans hd.2⟩
    obtain ⟨hlt, hsm, -, -, -⟩ := hPd d' hd'mem
    have hKn : n₀ ≤ (K : ℕ) := by omega
    have hmem : R.room ((K : ℕ) - n₀) * PeriodicLattice.meshSize ℓ.side (((K : ℕ) - n₀ : ℕ) : ℤ) ≤ d' := by
      have hs1 : PeriodicLattice.meshSize ℓ.side (((K : ℕ) - n₀ : ℕ) : ℤ) =
          (ℓ.side : ℝ) ^ n₀ * levelMesh ℓ.side K 0 := by
        rw [hsp, RoomFunctions.meshSize_natCast_eq]
        have : (ℓ.side : ℝ) ^ (K : ℕ) = (ℓ.side : ℝ) ^ ((K : ℕ) - n₀) * (ℓ.side : ℝ) ^ n₀ := by
          rw [← pow_add, Nat.sub_add_cancel hKn]
        rw [this]
        field_simp
      have hC1 : R.room ((K : ℕ) - n₀) ≤ R.room (K : ℕ) := hl.room.mono (Nat.sub_le _ _)
      have hC0 : 0 < R.room (K : ℕ) := lt_of_lt_of_le one_pos (hl.room.one_le_apply _)
      have hpw : (ℓ.side : ℝ) ^ ((lam * ((K : ℕ) : ℝ) - Ca) / (4 * ℓ.B)) ≤ (ℓ.side : ℝ) ^ (β / (4 * ℓ.B)) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (div_le_div_of_nonneg_right hslope (by positivity))
      calc R.room ((K : ℕ) - n₀) * PeriodicLattice.meshSize ℓ.side (((K : ℕ) - n₀ : ℕ) : ℤ)
          ≤ R.room (K : ℕ) * ((ℓ.side : ℝ) ^ n₀ * levelMesh ℓ.side K 0) := by
            rw [hs1]
            exact mul_le_mul_of_nonneg_right hC1 (by positivity)
        _ = (R.room (K : ℕ) * (ℓ.side : ℝ) ^ n₀) * levelMesh ℓ.side K 0 := by ring
        _ ≤ (ℓ.side : ℝ) ^ (β / (4 * ℓ.B)) * levelMesh ℓ.side K 0 :=
            mul_le_mul_of_nonneg_right (hroomK.trans hpw) hsp0.le
        _ ≤ d' := hd'.1
    have hdeep' : R.IsDeepEnough ℓ.side K n₀ d' := by
      have h1 : RoomFunctions.scaleDepth ℓ.side R.room d' ≤ (K : ℕ) - n₀ := Nat.sInf_le hmem
      have h2 : ((R.depthAt ℓ.side d' : ℕ) : ℤ) ≤ ((K : ℕ) : ℤ) - n₀ := by
        have h3 : R.depthAt ℓ.side d' ≤ (K : ℕ) - n₀ := h1
        omega
      show (n₀ : ℤ) ≤ ((K : ℕ) : ℤ) - (R.depthAt ℓ.side d' : ℤ)
      omega
    have hmem₀ := hd₀' d' hd'mem
    have hsig := (twoPointLimsupAtScale_between hT hfit hvt0 hvt1 hl hpair hφ hψ hK hdat hmem₀ hdeep').2
    refine hsig.trans (EReal.coe_le_coe_iff.2 ?_)
    have hg := hl.coupling_pos K β hdat d' hmem₀ hdeep'
    have hlg := hl.log_mem K β hdat d' hmem₀ hdeep'
    set g := R.coupling K β d'
    set u := Real.log (1 / d') with hu_def
    have hu0 : 0 < u := by
      rw [hu_def, one_div, Real.log_inv]
      exact neg_pos.2 (Real.log_neg hd'pos (hlt.trans hd₀.2))
    have h1 : (g ^ 2 * u) ^ 2 ≤ (4 / 3 * a) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlg.2 2
    have h2 : 8 / 3 * X * (g ^ 4 * u ^ 2) ≤ δv * u ^ 2 := by
      have h3 : g ^ 4 * u ^ 2 ≤ (4 / 3 * a) ^ 2 := by nlinarith
      exact (mul_le_mul_of_nonneg_left h3 (by positivity)).trans hsm
    have h4 : (8 / 3 * X * g ^ 4) * u ^ 2 ≤ δv * u ^ 2 := by nlinarith
    have h5 := le_of_mul_le_mul_right h4 (by positivity)
    calc 8 / 3 * A * TestFunctions.inverseEighthKernel φ ψ * g ^ 4 = 8 / 3 * X * g ^ 4 := by rw [hX]; ring
      _ ≤ δv := h5
  · intro σ hσ m
    have hlow := (twoPointLimsupAtScale_between hT hfit hvt0 hvt1 hl hpair hφ hψ hK hdat (hd₀' d hd) hdeep).1
    rw [hσ] at hlow
    have hlow' := EReal.coe_le_coe_iff.1 hlow
    have hg := hl.coupling_pos K β hdat d (hd₀' d hd) hdeep
    have hlg := hl.log_mem K β hdat d (hd₀' d hd) hdeep
    set g := R.coupling K β d
    set u := Real.log (1 / d) with hu_def
    have hd1 : d < 1 := lt_of_le_of_lt (hd₀' d hd).2 hd₀.2
    have hu0 : 0 < u := by
      rw [hu_def, one_div, Real.log_inv]
      exact neg_pos.2 (Real.log_neg hdpos hd1)
    have h1 : (2 / 3 * a) ^ 2 ≤ (g ^ 2 * u) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlg.1 2
    have h2 : (2 / 3 * a) ^ 2 ≤ g ^ 4 * u ^ 2 := by nlinarith
    have hσ1 : 2 / 9 * X * g ^ 4 ≤ σ := by
      calc 2 / 9 * X * g ^ 4 = 2 / 9 * A * TestFunctions.inverseEighthKernel φ ψ * g ^ 4 := by rw [hX]; ring
        _ ≤ σ := hlow'
    have hσ0 : 0 < σ := lt_of_lt_of_le (by positivity) hσ1
    have hinv : 1 / σ ≤ Ac * u ^ 2 := by
      rw [div_le_iff₀ hσ0, hAc]
      have h3 : 2 / 9 * X * (2 / 3 * a) ^ 2 ≤ σ * u ^ 2 := by
        calc 2 / 9 * X * (2 / 3 * a) ^ 2 ≤ 2 / 9 * X * (g ^ 4 * u ^ 2) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = (2 / 9 * X * g ^ 4) * u ^ 2 := by ring
          _ ≤ σ * u ^ 2 := mul_le_mul_of_nonneg_right hσ1 (by positivity)
      have e : 9 / 2 / X / (2 / 3 * a) ^ 2 * u ^ 2 * σ = (σ * u ^ 2) / (2 / 9 * X * (2 / 3 * a) ^ 2) := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      linarith
    have hlog : Real.log (1 / σ) ≤ Real.log (Ac * u ^ 2) := Real.log_le_log (by positivity) hinv
    have hc : Real.log (1 / σ) ^ 3 ≤ u :=
      ((Odd.strictMono_pow (by decide : Odd 3)).monotone hlog).trans hcube
    have hside : 1 ≤ PeriodicLattice.torusSide ℓ.side m := by
      unfold PeriodicLattice.torusSide
      have : (1 : ℝ) ≤ (ℓ.side : ℝ) ^ m := one_le_pow₀ hL1
      linarith
    have e1 : Real.exp u = 1 / d := by
      rw [hu_def]
      exact Real.exp_log (by positivity)
    have e2 : 1 / d ≤ PeriodicLattice.torusSide ℓ.side m / d := div_le_div_of_nonneg_right hside hdpos.le
    exact (Real.exp_le_exp.2 hc).trans (e1.le.trans e2)
end YangMills.Construction.FourPointCondition
end

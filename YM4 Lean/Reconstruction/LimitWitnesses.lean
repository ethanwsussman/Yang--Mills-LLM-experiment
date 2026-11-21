import Reconstruction.Predicates
import YangMills.Construction.QuaternionicWilsonModel.WhatTheTopGivesAtEveryCouplingProof

set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.ModelSeams
def HasWightmanTheoryPositiveOnPair (C : SystemsWithFiveBounds.LimitConstants)
    (σ : SeparatedTuples.TupleFunctional) (X : TestSpaces.SepTupleOfCard 2) : Prop :=
  ∃ T : ConfigSpace.FlatSequence, SystemsWithFiveBounds.HasSchwingerSequence σ T ∧
    SystemsWithFiveBounds.OSAxioms C T ∧ SystemsWithFiveBounds.IsWightmanSchwingerSequence T ∧
    ∃ (Y : ConfigSpace.SepFamilyOfLength (1 + 1))
      (h : ConfigSpace.tensorRealFamily Y.1 ∈ ConfigSpace.schwartzFlatOffDiagonal (1 + 1)) (r : ℝ),
      Y.1 = X.1 ∧ 0 < r ∧ T.atSucc 1 ⟨_, h⟩ = (r : ℂ)
structure VolumeFirstLimitData (p : TorusLumps.StepParameters) (Bs g ϑ d₀ : ℝ) (ηBar : ℝ → ℝ)
    (C : SystemsWithFiveBounds.LimitConstants)
    (Q : SystemsWithFiveBounds.PairSequence p.side (TotalDensitySystem.IsFirstPassagePair p Bs g))
    (S : LimitTheorem.CumulantFamily) (A : SeparatedTuples.DecompositionData)
    (X₂ : TestSpaces.SepTupleOfCard 2) (X₄ : TestSpaces.SepTupleOfCard 4) : Prop where
  shape_mem : ϑ ∈ Ioc (0 : ℝ) 1
  scale_mem : d₀ ∈ Ioc (0 : ℝ) (1 / 40)
  constants_valid : C.Valid
  defines : Q.Defines S
  tendsto_cutoff : Tendsto (fun j => (Q.cutoff j : ℕ)) atTop atTop
  tendsto_coupling : Tendsto Q.coupling atTop atTop
  isCanonical : A.IsCanonical (LimitTheorem.centredOf S)
  componentProperties : ∀ ξ, SystemsWithFiveBounds.ComponentProperties 1 ϑ d₀ ηBar C (A.comp ξ)
  pair_contDiff : ∀ i, ContDiff ℝ ∞ (X₂.1 i)
  pair_mem : ∃ d ∈ Ioc (0 : ℝ) d₀, (X₂.1 0, X₂.1 1) ∈ TestFunctions.separatedPairsR4 d ϑ
  quad_contDiff : ∀ i, ContDiff ℝ ∞ (X₄.1 i)
  quad_mem : ∃ d ∈ Ioc (0 : ℝ) d₀, X₄.1 ∈ QuadrupleClasses.collinearQuadsR4 d ϑ
  twoPoint_pos : 0 < S 2 le_rfl X₂
  fourPoint_pos : 0 < S 4 (by norm_num) X₄
  connected_pos : ∀ ξ, 0 < LimitTheorem.connectedFn (A.comp ξ) X₂
  wightman : ∀ ξ, HasWightmanTheoryPositiveOnPair C (A.comp ξ) X₂
  ae_nonGaussian : ∀ᵐ ξ ∂A.law, IsNonGaussianOnSmoothQuadruple (A.comp ξ)
  exists_nonGaussian : ∃ ξ, IsNonGaussianOnSmoothQuadruple (A.comp ξ)
def everyCouplingStatement : Prop :=
  ∃ J Lstar : ℕ, 1 ≤ J ∧ ∀ L : ℕ, Odd L → Lstar ≤ L →
    ∃ (p : TorusLumps.StepParameters) (Bs c₅ γ : ℝ) (Nw : ℕ) (CT : ℝ),
    p.side = L ∧ p.baseDepth = J ∧ TotalDensitySystem.IsUnitMeshStepParameters p ∧ 2 ≤ Bs ∧ 0 ≤ c₅ ∧
      γ ∈ Ioo (0 : ℝ) 1 ∧ 0 < CT ∧ 1 ≤ Nw ∧
      ∀ g ∈ Ioc 0 γ, TotalDensitySystem.CouplingConditions p Bs c₅ (3 / 4 * TotalDensitySystem.oneLoopShift L) Nw CT g ∧
        ∃ (ϑ d₀ : ℝ) (ηBar : ℝ → ℝ) (C : SystemsWithFiveBounds.LimitConstants)
          (Q : SystemsWithFiveBounds.PairSequence p.side (TotalDensitySystem.IsFirstPassagePair p Bs g))
          (S : LimitTheorem.CumulantFamily) (A : SeparatedTuples.DecompositionData)
          (X₂ : TestSpaces.SepTupleOfCard 2) (X₄ : TestSpaces.SepTupleOfCard 4),
          VolumeFirstLimitData p Bs g ϑ d₀ ηBar C Q S A X₂ X₄
end YangMills.Construction.ModelSeams
end

set_option autoImplicit false
open Filter MeasureTheory Set YangMills.Construction.TestFunctions YangMills.Construction.TorusMetric
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.NonGaussianLimits
open YangMills.Construction.TotalDensitySystem YangMills.Construction.TotalDensities YangMills.Construction.TorusLumps
open YangMills.Construction.SystemsWithFiveBounds YangMills.Construction.LimitTheorem YangMills.Construction.QuadrupleClasses
open YangMills.Construction.FourPointCondition YangMills.Construction.ModelSeams
open YangMills.Construction.SeparatedTuples (DecompositionData TupleFunctional)
open YangMills.Construction.TestSpaces (SepTupleOfCard SepTuple sepRestrict)
open YangMills.Construction.ConfigSpace (SepFamilyOfLength tensorRealFamily schwartzFlatOffDiagonal)
theorem exists_volumeFirstLimitData (reconstruct : ∀ {σ T}, LimitTheorem.ComponentFieldData σ →
      SystemsWithFiveBounds.HasSchwingerSequence σ T → SystemsWithFiveBounds.IsWightmanSchwingerSequence T)
    (hTen : YangMills.Construction.ConfigSpace.FlatSpaceClosure)
    {ℓ : StepParameters} {Bs c₅ lam CT g : ℝ} {Nw : ℕ} (hL : 2 ≤ ℓ.side) (hc : CouplingConditions ℓ Bs c₅ lam Nw CT g) :
    ∃ (ϑ d₀ : ℝ) (ηBar : ℝ → ℝ) (C : LimitConstants)
      (Q : PairSequence ℓ.side (IsFirstPassagePair ℓ Bs g)) (S : CumulantFamily) (A : DecompositionData)
      (X₂ : SepTupleOfCard 2) (X₄ : SepTupleOfCard 4), VolumeFirstLimitData ℓ Bs g ϑ d₀ ηBar C Q S A X₂ X₄ := by
  obtain ⟨⟨Q, S, hS⟩, -⟩ := hc.volumeFirstLimits
  obtain ⟨cV, Cn, C, hC, -, -, -, hvf, hnum⟩ := hc.constants
  obtain ⟨Cb, hCb, hlip⟩ := radialProfile_lipschitz
  obtain ⟨ϑ, hϑ0, hϑ1, hϑ2⟩ : ∃ ϑ : ℝ, 0 < ϑ ∧ ϑ ≤ 1 / 16777216 ∧ 64 * Cb * ϑ ≤ 1 := by
    refine ⟨min (1 / 16777216) (1 / (64 * Cb)), lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
    have h1 : min (1 / 16777216 : ℝ) (1 / (64 * Cb)) ≤ 1 / (64 * Cb) := min_le_right _ _
    have h2 : 0 < 64 * Cb := by positivity
    calc 64 * Cb * min (1 / 16777216 : ℝ) (1 / (64 * Cb)) ≤ 64 * Cb * (1 / (64 * Cb)) := by gcongr
      _ = 1 := by field_simp
  have hϑm : ϑ ∈ Ioc (0 : ℝ) 1 := ⟨hϑ0, by linarith⟩
  obtain ⟨hnG, hroom⟩ := hnum ϑ hϑm
  obtain ⟨d₀, ηBar, εBar, ζ, K₀, d₄, hcl⟩ := hroom succGauge succGauge_isSubexpGrowth
  have hd := hcl.d₄_mem
  have hd₀ := hcl.twoPointLaw.cutoff_mem
  have hlim : IsContinuumLimit ℓ Bs g S := Or.inr ⟨Q, hS⟩
  have hAss := hcl.ergodic Q S hS
  obtain ⟨A, hA⟩ := hAss.decomposition.exists_canonical
  have hprob := hA.isProb
  have hqT := collinearBumps_mem_disjointSupportTuples hCb hlip hϑ0 hϑ1 hϑ2 hd.1
  have hqC := collinearBumps_mem_collinear hCb hlip hϑ0 hϑ1 hϑ2 hd.1
  let X₄ : SepTupleOfCard 4 := ⟨collinearBumps d₄, hqT⟩
  have hsm : ∀ i, ContDiff ℝ ∞ (collinearBumps d₄ i) := fun i => scaledBump_contDiff _ _
  have hC1 : ∀ i, ContDiff ℝ 1 (collinearBumps d₄ i) := fun i => (hsm i).of_le (by exact_mod_cast le_top)
  have hp01 : (collinearBumps d₄ 0, collinearBumps d₄ 1) ∈ separatedPairsR4 d₄ ϑ :=
    collinearBumps_pair_mem hCb hlip hϑ0 hϑ1 hϑ2 hd.1 (by decide)
  have hEvery := hcl.everyLimit S hlim
  obtain ⟨X, hX, e, hv, he1, -⟩ := hEvery.conditions.twoPointLaw d₄ hd _ _ hp01 (hC1 0) (hC1 1)
  have hX0 : X.1 0 = collinearBumps d₄ 0 := by rw [hX]; rfl
  have hX1 : X.1 1 = collinearBumps d₄ 1 := by rw [hX]; rfl
  have hpair : (X.1 0, X.1 1) ∈ separatedPairsR4 d₄ ϑ := by rw [hX0, hX1]; exact hp01
  have hXs : ∀ i, ContDiff ℝ ∞ (X.1 i) := by
    intro i
    fin_cases i
    · show ContDiff ℝ ∞ (X.1 0)
      rw [hX0]; exact hsm 0
    · show ContDiff ℝ ∞ (X.1 1)
      rw [hX1]; exact hsm 1
  have hS2 := hEvery.conditions.twoPoint_pos d₄ hd X hpair
  have hη : ∀ e : ℝ, 1 / 2 * (1 - ηBar d₄) ^ 4 ≤ 1 + e → 0 < 1 + e := by
    intro e he
    have h := hcl.twoPointLaw.sharp_on_tori.ηBar_mem d₄ hd
    have h1 : (0 : ℝ) < 1 - ηBar d₄ := by linarith [h.2]
    have h2 : 0 < 1 / 2 * (1 - ηBar d₄) ^ 4 := by positivity
    linarith
  have hmain : 0 < twoPointMainTerm d₄ (collinearBumps d₄ 0) (collinearBumps d₄ 1) := by
    have h1 := hS2
    rw [← hEvery.conditions.cumulants_eq 2 le_rfl X, hv] at h1
    exact (pos_iff_pos_of_mul_pos h1).2 (hη e he1)
  have hcomp : ∀ ξ, 0 < connectedFn (A.comp ξ) X := by
    intro ξ
    obtain ⟨X', hX', e', hv', he', -⟩ := (hAss.components A hA ξ).twoPointLaw d₄ hd _ _ hp01 (hC1 0) (hC1 1)
    have hXX : X' = X := Subtype.ext (hX'.trans hX.symm)
    rw [hXX] at hv'
    rw [hv']
    exact mul_pos hmain (hη e' he')
  obtain ⟨c, -, -, hconst⟩ := hAss.onePoint A hA
  have hval : ∀ ξ, 0 < evalOnMap (A.comp ξ) ⟨2, X⟩ := fun ξ =>
    evalOnMap_pos_of_connectedFn_pos (hconst ξ) (fun x => by rw [hX0]; exact scaledBump_nonneg _ _ _)
      (fun x => by rw [hX1]; exact scaledBump_nonneg _ _ _) (hcomp ξ)
  have htheory : ∀ ξ, HasWightmanTheoryPositiveOnPair C (A.comp ξ) X := by
    intro ξ
    obtain ⟨T, hT, -⟩ := (hAss.components A hA ξ).growth
    have h6 := (hAss.components A hA ξ).componentOS T hT
    have hW := reconstruct (hAss.components A hA ξ).fieldData hT
    let Y : SepFamilyOfLength (1 + 1) :=
      ⟨X.1, fun i => YangMills.Construction.ConfigSpace.mem_realC1CompactIn_iff.2
        ⟨isOpen_univ, (X.2.1 i).1, (X.2.1 i).2.1, Set.subset_univ _⟩, X.2.2⟩
    have hY : YangMills.Construction.ConfigSpace.AllSmoothCompact Y.1 := fun i =>
      YangMills.Construction.ConfigSpace.mem_realSmoothCompactIn_iff.2
        ⟨isOpen_univ, hXs i, (X.2.1 i).2.1, Set.subset_univ _⟩
    have hten := (hTen (1 + 1) (by norm_num)).2 Y hY
    refine ⟨T, hT, h6, hW, Y, hten, evalOnMap (A.comp ξ) ⟨2, X⟩, rfl, hval ξ, ?_⟩
    rw [(hT.2.2 1).2 Y hY hten]
    rfl
  have h4 : 0 < S 4 (by norm_num) X₄ := by
    have hlt1 : d₄ < 1 := by linarith [hd.2, hd₀.2]
    have hlog : 0 < Real.log (1 / d₄) := Real.log_pos (by rw [lt_div_iff₀ hd.1]; linarith)
    have hint := hcl.fourPointInLimits.on_space S hlim d₄ ⟨hd.1, le_rfl⟩ X₄ hqC
    have hprod : 0 < ∏ i, uniformNorm (X₄.1 i) := by
      refine Finset.prod_pos fun i _ => ?_
      show 0 < uniformNorm (scaledBump (d₄ / 32) (axisPoint d₄ i))
      rw [uniformNorm_scaledBump]
      norm_num
    have hmin : 0 < min ϑ (YangMills.Construction.TorusMeasure.omega4 * (16 : ℝ) ^ (-4 : ℤ)) := by
      refine lt_min hϑ0 ?_
      unfold YangMills.Construction.TorusMeasure.omega4
      positivity
    have hfloor : 0 < fourPointLowerConst ϑ := by
      unfold fourPointLowerConst
      positivity
    have hdim : 0 < gaugeGroupDim := by
      unfold gaugeGroupDim
      norm_num [YangMills.Construction.ParameterChoice.colorNumber]
    have hone : 0 < FourPointCondition.oneLoopCoeff := by
      unfold FourPointCondition.oneLoopCoeff
      have h : (0 : ℝ) < (YangMills.Construction.ParameterChoice.colorNumber : ℝ) := by
        norm_num [YangMills.Construction.ParameterChoice.colorNumber]
      positivity
    refine lt_of_lt_of_le ?_ hint.1
    exact mul_pos (mul_pos (mul_pos (mul_pos hfloor hdim) (pow_pos (by positivity) 4)) (zpow_pos hlog _)) hprod
  let X₁ : SepTupleOfCard 4 := ⟨collinearBumps 1, collinearBumps_mem_disjointSupportTuples hCb hlip hϑ0 hϑ1 hϑ2 one_pos⟩
  have hLpos : 0 < shortDistanceLimit X₁.1 :=
    hnG.four_pos X₁ (collinearBumps_mem_collinear hCb hlip hϑ0 hϑ1 hϑ2 one_pos)
  let Y : ℕ → SepTupleOfCard 4 := fun i => ⟨dyadicRescale i X₁.1, dyadicRescale_mem i X₁⟩
  have hae := (hvf Q S hS).2.ae_components A hA 4 (by norm_num) (by norm_num) X₁ Y (fun _ => rfl)
  have hng : ∀ᵐ ξ ∂A.law, IsNonGaussianOnSmoothQuadruple (A.comp ξ) := by
    filter_upwards [hae] with ξ hξ
    obtain ⟨i, hi⟩ := (hξ.eventually (lt_mem_nhds hLpos)).exists
    refine ⟨Y i, fun k => ?_, fun h0 => ?_⟩
    · exact (scaledBump_contDiff _ _).comp (by fun_prop)
    · rw [h0, mul_zero] at hi
      exact lt_irrefl _ hi
  exact ⟨ϑ, d₀, ηBar, C, Q, S, A, X, X₄,
    { shape_mem := hϑm
      scale_mem := hd₀
      constants_valid := hC
      defines := hS
      tendsto_cutoff := Q.tendsto_cutoff
      tendsto_coupling := tendsto_coupling_atTop hL hc Q.cutoff Q.coupling Q.pair Q.tendsto_cutoff
      isCanonical := hA
      componentProperties := hAss.components A hA
      pair_contDiff := hXs
      pair_mem := ⟨d₄, hd, hpair⟩
      quad_contDiff := hsm
      quad_mem := ⟨d₄, hd, hqC⟩
      twoPoint_pos := hS2
      fourPoint_pos := h4
      connected_pos := hcomp
      wightman := htheory
      ae_nonGaussian := hng
      exists_nonGaussian := hng.exists }⟩
theorem everyCouplingStatement_holds (reconstruct : ∀ {σ T}, LimitTheorem.ComponentFieldData σ →
      SystemsWithFiveBounds.HasSchwingerSequence σ T → SystemsWithFiveBounds.IsWightmanSchwingerSequence T)
    (hT : TrajectoryTopStatement)
    (hTen : YangMills.Construction.ConfigSpace.FlatSpaceClosure) : everyCouplingStatement := by
  obtain ⟨J, Ls, hJ, h⟩ := hT
  refine ⟨J, Ls, hJ, fun L hodd hge => ?_⟩
  obtain ⟨ℓ, Bs, c₅, γ, Nw, CT, hL, hJ₀, hdat, hB, hc₅, hγ, hCT, hNw, hall⟩ := h L hodd hge
  have hL2 : 2 ≤ ℓ.side := by
    have h40 := hdat.side_ge
    have h2 : (2 : ℕ) ≤ 2 ^ 40 := by norm_num
    omega
  exact ⟨ℓ, Bs, c₅, γ, Nw, CT, hL, hJ₀, hdat, hB, hc₅, hγ, hCT, hNw,
    fun g hg => ⟨hall g hg, exists_volumeFirstLimitData reconstruct hTen hL2 (hall g hg)⟩⟩
end YangMills.Construction.NonGaussianLimits
end

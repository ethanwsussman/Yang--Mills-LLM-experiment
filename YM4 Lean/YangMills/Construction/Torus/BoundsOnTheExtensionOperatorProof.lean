import YangMills.Construction.Torus.BoundsOnTheExtensionOperator
import YangMills.Construction.Torus.ColumnsOfTheGreenOperatorOnTheTori
import YangMills.Construction.Torus.FarApartLayersOfASeparatedSequenceProof
import YangMills.Construction.Torus.FloorOfTheInverseBounds
import YangMills.Construction.Torus.QuadraticFormsAndMatricesOfTheAverages
import YangMills.Construction.Torus.ScalarProductsTransposesAndProjectionsOfASettingProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.GeneralTorus.HarmonicExtBounds
theorem finite_coarseBond (G : GaugeSetting) : Finite G.CoarseBond := by apply _root_.YangMills.Construction.GeneralTorus.InnerProductsAdjointsProjections.finite_coarseBond <;> assumption
open SeparatedSequences GreenBounds
theorem eq_sum_smul_coarseDelta (G : GaugeSetting) [Fintype G.CoarseBond] (f : G.CoarseField) :
    f = ∑ c, f c • G.coarseDelta c := by
  classical
  funext c'
  simp [Finset.sum_apply, GaugeSetting.coarseDelta, Pi.single_apply]
theorem harmonicExt_eq_sum (G : GaugeSetting) [Fintype G.CoarseBond] (B : G.CoarseField) :
    G.harmonicExt B = ∑ c, B c • G.harmonicExt (G.coarseDelta c) := by
  have h := congrArg G.harmonicExt (eq_sum_smul_coarseDelta G B)
  rw [map_sum] at h
  simpa only [map_smul] using h
theorem harmonicExt_coarseDelta_eq_sum (G : GaugeSetting) [Fintype G.CoarseBond] (c : G.CoarseBond) :
    G.harmonicExt (G.coarseDelta c) =
      ∑ c₁, G.kernelEntry (Ring.inverse G.coarseGreen) c₁ c • G.greenColumn c₁ := by
  have h := congrArg (fun f => G.greenOp (G.meanOpAdjoint f))
    (eq_sum_smul_coarseDelta G (Ring.inverse G.coarseGreen (G.coarseDelta c)))
  simp only [map_sum, map_smul] at h
  exact h
theorem summand_le {δ e d d₁ d₂ k C x X Q : ℝ} (he0 : 0 < e) (he : e ≤ δ / 4)
    (hd₁ : 0 ≤ d₁) (htri : d ≤ d₁ + d₂) (hx : 0 < x) (hX : 0 < X)
    (hk : |k| ≤ C * x⁻¹ * Real.exp (-(1 / 2 * e) * d₂))
    (hT : X * x⁻¹ * Real.exp (-(1 / 2 * δ) * d₁) ≤ Q) :
    |k| * (X * Real.exp (-δ * d₁)) ≤
      C * Q * (Real.exp (-(1 / 2 * e) * d) * Real.exp (-(δ / 4) * d₁)) := by
  have hxi : 0 < x⁻¹ := inv_pos.2 hx
  have hC : 0 ≤ C := by
    have h0 : 0 ≤ C * (x⁻¹ * Real.exp (-(1 / 2 * e) * d₂)) := by
      rw [← mul_assoc]
      exact (abs_nonneg k).trans hk
    exact nonneg_of_mul_nonneg_left h0 (mul_pos hxi (Real.exp_pos _))
  have hQ : 0 ≤ Q :=
    (mul_pos (mul_pos hX hxi) (Real.exp_pos _)).le.trans hT
  have hsplit : Real.exp (-δ * d₁) =
      Real.exp (-(1 / 2 * δ) * d₁) * Real.exp (-(1 / 2 * δ) * d₁) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc |k| * (X * Real.exp (-δ * d₁))
      ≤ (C * x⁻¹ * Real.exp (-(1 / 2 * e) * d₂)) * (X * Real.exp (-δ * d₁)) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
    _ = C * (X * x⁻¹ * Real.exp (-(1 / 2 * δ) * d₁)) *
          (Real.exp (-(1 / 2 * e) * d₂) * Real.exp (-(1 / 2 * δ) * d₁)) := by
        rw [hsplit]
        ring
    _ ≤ C * Q * (Real.exp (-(1 / 2 * e) * d) * Real.exp (-(δ / 4) * d₁)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hT hC) ?_ (by positivity)
          (mul_nonneg hC hQ)
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith [mul_nonneg he0.le (sub_nonneg.2 htri),
          mul_nonneg (by linarith : (0 : ℝ) ≤ δ / 4 - e / 2) hd₁]
theorem levelSpacing_sq_div (D : ScaleData) (n n' : ℕ) :
    D.levelSpacing n ^ 2 * (D.levelSpacing n' ^ 2)⁻¹ =
      (D.L : ℝ) ^ ((-2 : ℝ) * ((n' : ℝ) - (n : ℝ))) := by
  have hL : (0 : ℝ) < D.L := by
    have := D.blocking.thirteen_le
    exact_mod_cast (by omega : 0 < D.L)
  have hb : D.baseSpacing ≠ 0 := D.baseSpacing_pos.ne'
  have he : (-2 : ℝ) * ((n' : ℝ) - (n : ℝ)) = ((2 * n : ℕ) : ℝ) - ((2 * n' : ℕ) : ℝ) := by
    push_cast
    ring
  rw [he, Real.rpow_sub hL, Real.rpow_natCast, Real.rpow_natCast, ScaleData.levelSpacing,
    ScaleData.levelSpacing, pow_mul, pow_mul]
  have h2 : (D.L : ℝ) ^ n' ≠ 0 := (pow_pos hL _).ne'
  field_simp
  ring
section Sites
variable {D : ScaleData} (B : SeparatedChain D)
theorem scaledDist_nonneg (hp : B.ScaledDistIsPseudometric) (x x' : D.Space) :
    0 ≤ B.scaledDist x x' := by apply _root_.YangMills.Construction.GeneralTorus.ShellSeparation.scaledDist_nonneg <;> assumption
theorem mem_augmentedShell (hl : B.ShellsAreCubeUnions) {n : ℕ} (hn : n ≤ D.lastLevel)
    {y : D.Space} (hy : y ∈ B.shellSites n) : y ∈ B.augmentedShell n := by
  cases n with
  | zero => exact (hl 0 hn).2.1 hy.2
  | succ k => exact hy.2
theorem exists_shell_level {y : D.Space} (hy : y ∈ B.shellSitesUnion) :
    ∃ n, n ≤ D.lastLevel ∧ y ∈ B.shellSites n ∧ B.localSpacing y = D.levelSpacing n := by
  obtain ⟨n, hn, hyn⟩ : ∃ n, n ≤ D.lastLevel ∧ y ∈ B.shellSites n := by
    simpa [SeparatedChain.shellSitesUnion] using hy
  have hne : {n | y ∈ B.shellSites n}.Nonempty := ⟨n, hyn⟩
  exact ⟨sInf {n | y ∈ B.shellSites n}, (Nat.sInf_le hyn).trans hn, Nat.sInf_mem hne, rfl⟩
theorem localSpacing_pos (y : D.Space) : 0 < B.localSpacing y := by
  have hL : (0 : ℝ) < D.L := by
    have := D.blocking.thirteen_le
    exact_mod_cast (by omega : 0 < D.L)
  unfold SeparatedChain.localSpacing ScaleData.levelSpacing
  exact mul_pos (pow_pos hL _) D.baseSpacing_pos
end Sites
section Sum
variable {L : ℕ} (s : LevelUnitChain L)
structure SumInputs : Prop where
  valid : (chosen L).Valid L
  inverse : CoarseGreenInverse.Conclusion (chosen L) s
  ordered : InverseBounds.RateThresholdOrdered L
  sums : InverseBounds.ExpSumsBounded s.setting
  trade : InverseBounds.PowerDistanceTrade s.setting
  pseudometric : s.chain.ScaledDistIsPseudometric
  shells : s.chain.ShellsAreCubeUnions
  anchors : ∀ c : s.setting.CoarseBond, GaugeSetting.coarseAnchor c ∈ s.chain.shellSites c.1
variable {s}
abbrev invEntry (s : LevelUnitChain L) (c₁ c : s.setting.CoarseBond) : ℝ :=
  s.setting.kernelEntry (Ring.inverse s.setting.coarseGreen) c₁ c
theorem abs_invEntry_mul_le (F : SumInputs s) {n : ℕ} (hn : n ≤ s.data.lastLevel)
    {y : s.data.Space} (hy : y ∈ s.chain.augmentedShell n)
    (hsp : s.chain.localSpacing y = s.data.levelSpacing n) (c c₁ : s.setting.CoarseBond) :
    |invEntry s c₁ c| * (s.chain.localSpacing y ^ 2 * GreenColumns.siteDecay (chosen L) s y c₁) ≤
      inverseKernelConstant 4 L * (L : ℝ) ^ 2 *
        (Real.exp (-(1 / 2 * inverseDecayRate 4 L (chosen L).rate (chosen L).bound) *
            GaugeSetting.siteCoarseDist (W := s.setting) y c) *
          Real.exp (-((chosen L).rate / 4) * GaugeSetting.siteCoarseDist (W := s.setting) y c₁)) := by
  obtain ⟨he0, he, -⟩ := F.ordered
  have he0' : 0 < inverseDecayRate 4 L (chosen L).rate (chosen L).bound := he0
  have he' : inverseDecayRate 4 L (chosen L).rate (chosen L).bound ≤ (chosen L).rate / 4 := he
  have hc₁ : (c₁.1 : ℕ) ≤ s.data.lastLevel := Nat.lt_succ_iff.1 c₁.1.2
  have hsite := mem_augmentedShell s.chain F.shells hc₁ (F.anchors c₁)
  have hrate : 1 / 2 * InverseBounds.decayRateOfInverse s.setting.data.L ≤
      1 / 2 * (chosen L).rate := by
    have h : InverseBounds.decayRateOfInverse s.setting.data.L ≤ (chosen L).rate / 4 := he
    linarith
  have htr := F.trade n c₁.1 hn hc₁ y hy _ hsite (-2) (1 / 2 * (chosen L).rate)
    (by rw [abs_neg, abs_two]; norm_num) hrate
  have hk := F.inverse.kernelEntry_bound c₁ c
  have hL : (0 : ℝ) < s.data.L := by
    have := s.data.blocking.thirteen_le
    exact_mod_cast (by omega : 0 < s.data.L)
  have hx : 0 < GaugeSetting.coarseSpacing c₁ := mul_pos (pow_pos hL _) s.data.baseSpacing_pos
  have hT : s.chain.localSpacing y ^ 2 * (GaugeSetting.coarseSpacing c₁ ^ 2)⁻¹ *
      Real.exp (-(1 / 2 * (chosen L).rate) * GaugeSetting.siteCoarseDist (W := s.setting) y c₁) ≤
        (L : ℝ) ^ 2 := by
    have hr := levelSpacing_sq_div s.data n c₁.1
    have hxe : GaugeSetting.coarseSpacing c₁ = s.data.levelSpacing c₁.1 := rfl
    rw [hsp, hxe, hr]
    have h2 : (s.data.L : ℝ) ^ |(-2 : ℝ)| = (L : ℝ) ^ 2 := by
      rw [abs_neg, abs_two]
      exact Real.rpow_two _
    exact htr.trans_eq h2
  exact summand_le he0' he' (scaledDist_nonneg s.chain F.pseudometric _ _)
    (F.pseudometric.2.2.2.2 y _ _) (pow_pos hx 2) (pow_pos (localSpacing_pos s.chain y) 2) hk hT
theorem sum_invEntry_le [Fintype s.setting.CoarseBond] (F : SumInputs s) {y : s.data.Space}
    (hy : y ∈ s.chain.shellSitesUnion) (c : s.setting.CoarseBond) :
    ∑ c₁, |invEntry s c₁ c| * (s.chain.localSpacing y ^ 2 *
        GreenColumns.siteDecay (chosen L) s y c₁) ≤
      inverseKernelConstant 4 L * (L : ℝ) ^ 2 *
        (2 * 4 * expSumConstant 4 L ((chosen L).rate / 4)) *
        coarseDecay (chosen L) s y c := by
  obtain ⟨n, hn, hyn, hsp⟩ := exists_shell_level s.chain hy
  have hyext := mem_augmentedShell s.chain F.shells hn hyn
  obtain ⟨he0, he, -⟩ := F.ordered
  have hsum := ((F.sums ((chosen L).rate / 4) (by
    have h1 : InverseBounds.decayRateOfInverse s.setting.data.L ≤ (chosen L).rate / 4 := he
    have h0 : 0 < InverseBounds.decayRateOfInverse s.setting.data.L := he0
    linarith)) y hy).2
  rw [finsum_eq_sum_of_fintype] at hsum
  have hC : 0 ≤ inverseKernelConstant 4 L * (L : ℝ) ^ 2 := by
    have hγ : 0 < compressedGreenLowerBound 4 1 := by
      unfold compressedGreenLowerBound testFormEnergyConstant
      positivity
    unfold inverseKernelConstant
    positivity
  set E := Real.exp (-(1 / 2 * inverseDecayRate 4 L (chosen L).rate (chosen L).bound) *
    GaugeSetting.siteCoarseDist (W := s.setting) y c) with hE
  have hD : coarseDecay (chosen L) s y c = E := by
    rw [hE]
    unfold coarseDecay halfInverseDecayRate
    rfl
  rw [hD]
  calc ∑ c₁, |invEntry s c₁ c| * (s.chain.localSpacing y ^ 2 *
          GreenColumns.siteDecay (chosen L) s y c₁)
      ≤ ∑ c₁, inverseKernelConstant 4 L * (L : ℝ) ^ 2 *
          (E * Real.exp (-((chosen L).rate / 4) *
            GaugeSetting.siteCoarseDist (W := s.setting) y c₁)) :=
        Finset.sum_le_sum fun c₁ _ => abs_invEntry_mul_le F hn hyext hsp c c₁
    _ = inverseKernelConstant 4 L * (L : ℝ) ^ 2 * E *
          ∑ c₁, Real.exp (-((chosen L).rate / 4) *
            GaugeSetting.siteCoarseDist (W := s.setting) y c₁) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ inverseKernelConstant 4 L * (L : ℝ) ^ 2 * E *
          (2 * 4 * expSumConstant 4 L ((chosen L).rate / 4)) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hC (Real.exp_pos _).le)
    _ = _ := by ring
end Sum
section Linear
variable {L : ℕ} (s : LevelUnitChain L) {ι : Type*}
theorem coe_finsetSum_smul (G : GaugeSetting) (t : Finset ι) (a : ι → ℝ)
    (A : ι → ↥G.formSubspace) :
    ((∑ i ∈ t, a i • A i : ↥G.formSubspace) : G.data.BondField) =
      ∑ i ∈ t, a i • (A i : G.data.BondField) := by
  simp
theorem grad_finsetSum (t : Finset ι) (a : ι → ℝ) (A : ι → s.data.BondField)
    (x : s.data.BaseSite) (μ ν : Fin 4) :
    s.grad (∑ i ∈ t, a i • A i) x μ ν = ∑ i ∈ t, a i * s.grad (A i) x μ ν := by
  unfold LevelUnitChain.grad
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
theorem cutoffGrad_finsetSum (t : Finset ι) (a : ι → ℝ) (A : ι → s.data.BondField)
    (ζ : s.data.Space → ℂ) (ν : Fin 4) :
    s.cutoffGrad ζ (∑ i ∈ t, a i • A i) ν =
      fun c => ∑ i ∈ t, (a i : ℂ) * s.cutoffGrad ζ (A i) ν c := by
  funext c
  unfold LevelUnitChain.cutoffGrad
  rw [grad_finsetSum]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
theorem toMatrixBondFun_finsetSum (t : Finset ι) (a : ι → ℂ) (f : ι → s.data.BaseBond → ℂ)
    (b : SeparatedSequences.FineBond L s.m s.scales) :
    s.toMatrixBondFun (fun c => ∑ i ∈ t, a i * f i c) b =
      ∑ i ∈ t, a i • s.toMatrixBondFun (f i) b := by
  unfold LevelUnitChain.toMatrixBondFun
  by_cases h : ∃ c, s.Corresponds c b
  · simp only [dif_pos h, Finset.sum_smul, smul_smul]
  · simp only [dif_neg h, smul_zero, Finset.sum_const_zero]
theorem conjugateBy_finsetSum (g : Matrices.ComplexMatrix2) (t : Finset ι) (a : ι → ℂ)
    (v : ι → Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.conjugateBy g (∑ i ∈ t, a i • v i) =
      ∑ i ∈ t, a i • Matrices.ComplexMatrix2.conjugateBy g (v i) := by
  unfold Matrices.ComplexMatrix2.conjugateBy
  rw [Finset.mul_sum, Finset.sum_mul]
  simp only [mul_smul_comm, smul_mul_assoc]
open scoped Matrix.Norms.L2Operator in
theorem cutoffGradSeminorm_finsetSum_le (t : Finset ι) (a : ι → ℝ) (A : ι → s.data.BondField)
    (α : ℝ) (ζ : s.data.Space → ℂ)
    (path : PeriodicLattice.SiteAtLevel L s.m s.scales.levels 0 →
      PeriodicLattice.SiteAtLevel L s.m s.scales.levels 0 →
      List (SeparatedSequences.FineBond L s.m s.scales)) :
    s.cutoffGradSeminorm α ζ (∑ i ∈ t, a i • A i) path ≤
      ∑ i ∈ t, ENNReal.ofReal |a i| * s.cutoffGradSeminorm α ζ (A i) path := by
  conv_lhs =>
    unfold LevelUnitChain.cutoffGradSeminorm SeparatedSequences.bondTransportHolderSeminorm
  refine iSup_le fun ν => iSup₂_le fun b hb => iSup₂_le fun b' hb' => iSup_le fun hcond => ?_
  have hterm : ∀ i, SeparatedSequences.holderTerm s.scales α PeriodicLattice.trivialGaugeField
      (path b.source b'.source) b.source b'.source
      (s.toMatrixBondFun (s.cutoffGrad ζ (A i) ν) b)
      (s.toMatrixBondFun (s.cutoffGrad ζ (A i) ν) b') ≤
      s.cutoffGradSeminorm α ζ (A i) path := by
    intro i
    unfold LevelUnitChain.cutoffGradSeminorm SeparatedSequences.bondTransportHolderSeminorm
    exact le_iSup_of_le ν (le_iSup₂_of_le b hb (le_iSup₂_of_le b' hb'
      (le_iSup_of_le hcond le_rfl)))
  refine le_trans ?_ (Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (hterm i))
  unfold SeparatedSequences.holderTerm
  rw [cutoffGrad_finsetSum, toMatrixBondFun_finsetSum, toMatrixBondFun_finsetSum,
    conjugateBy_finsetSum, ← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  set u := SeparatedSequences.unitL1Dist s.scales
      (b.source : PeriodicLattice.FourTorus L s.m) b'.source ^ (-α) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hcond.2.1.le _
  set w : ι → Matrices.ComplexMatrix2 := fun i =>
    Matrices.ComplexMatrix2.conjugateBy
      (PeriodicLattice.pathHolonomy PeriodicLattice.trivialGaugeField (path b.source b'.source))
      (s.toMatrixBondFun (s.cutoffGrad ζ (A i) ν) b') -
    s.toMatrixBondFun (s.cutoffGrad ζ (A i) ν) b with hw
  have hn : Matrices.ComplexMatrix2.operatorNorm (∑ i ∈ t, (a i : ℂ) • w i) ≤
      ∑ i ∈ t, |a i| * Matrices.ComplexMatrix2.operatorNorm (w i) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc ENNReal.ofReal (u * Matrices.ComplexMatrix2.operatorNorm (∑ i ∈ t, (a i : ℂ) • w i))
      ≤ ENNReal.ofReal (∑ i ∈ t, |a i| * (u * Matrices.ComplexMatrix2.operatorNorm (w i))) := by
        apply ENNReal.ofReal_le_ofReal
        calc u * Matrices.ComplexMatrix2.operatorNorm (∑ i ∈ t, (a i : ℂ) • w i)
            ≤ u * ∑ i ∈ t, |a i| * Matrices.ComplexMatrix2.operatorNorm (w i) :=
              mul_le_mul_of_nonneg_left hn hu0
          _ = _ := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ i ∈ t, ENNReal.ofReal |a i| *
          ENNReal.ofReal (u * Matrices.ComplexMatrix2.operatorNorm (w i)) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ =>
          mul_nonneg (abs_nonneg _) (mul_nonneg hu0 (norm_nonneg _))]
        exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_mul (abs_nonneg _)
end Linear
section Bounds
variable {L : ℕ} {s : LevelUnitChain L}
theorem fieldKernelConstant_eq (δ C R : ℝ) :
    greenColumnConstant 4 L δ C * (inverseKernelConstant 4 L * (L : ℝ) ^ 2 *
        (2 * 4 * expSumConstant 4 L (δ / 4)) * R) =
      fieldKernelConstant 4 L δ C * R := by
  unfold fieldKernelConstant
  push_cast
  ring
theorem greenColumnConstant_nonneg {δ C : ℝ} (hC : 1 ≤ C) : 0 ≤ greenColumnConstant 4 L δ C := by
  have : 0 ≤ C := by linarith
  unfold greenColumnConstant
  positivity
theorem harmonicExtKernel_le [Fintype s.setting.CoarseBond] (F : SumInputs s)
    (hcol : ∀ c, GreenColumns.ColumnEstimates (chosen L) s c)
    {y : s.data.Space} (hy : y ∈ s.chain.shellSitesUnion) (c : s.setting.CoarseBond)
    (b : ↥s.setting.bondSet) (hb : s.chain.LiesInCell b.1 y) :
    |s.setting.harmonicExtKernel b c| ≤
      fieldKernelConstant 4 L (chosen L).rate (chosen L).bound *
        coarseDecay (chosen L) s y c := by
  set nums := chosen L with hnums
  have hC := greenColumnConstant_nonneg (L := L) (δ := nums.rate) F.valid.one_le_bound
  have hx : s.setting.harmonicExtKernel b c =
      ∑ c₁, invEntry s c₁ c * (s.setting.greenColumn c₁).1 b.1 := by
    unfold GaugeSetting.harmonicExtKernel
    rw [harmonicExt_coarseDelta_eq_sum s.setting c, coe_finsetSum_smul, Finset.sum_apply]
    rfl
  rw [hx, ← fieldKernelConstant_eq]
  calc |∑ c₁, invEntry s c₁ c * (s.setting.greenColumn c₁).1 b.1|
      ≤ ∑ c₁, |invEntry s c₁ c * (s.setting.greenColumn c₁).1 b.1| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c₁, greenColumnConstant 4 L nums.rate nums.bound * (|invEntry s c₁ c| *
          (s.chain.localSpacing y ^ 2 * GreenColumns.siteDecay nums s y c₁)) := by
        refine Finset.sum_le_sum fun c₁ _ => ?_
        rw [abs_mul]
        have h1 := (hcol c₁).bond_le y hy b.1 b.2 hb
        calc |invEntry s c₁ c| * |(s.setting.greenColumn c₁).1 b.1|
            ≤ |invEntry s c₁ c| * (greenColumnConstant 4 L nums.rate nums.bound *
                s.chain.localSpacing y ^ 2 * GreenColumns.siteDecay nums s y c₁) :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ = _ := by ring
    _ = greenColumnConstant 4 L nums.rate nums.bound * ∑ c₁, |invEntry s c₁ c| *
          (s.chain.localSpacing y ^ 2 * GreenColumns.siteDecay nums s y c₁) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_invEntry_le F hy c) hC
theorem grad_harmonicExt_le [Fintype s.setting.CoarseBond] (F : SumInputs s)
    (hcol : ∀ c, GreenColumns.ColumnEstimates (chosen L) s c)
    {y : s.data.Space} (hy : y ∈ s.chain.shellSitesUnion) (c : s.setting.CoarseBond)
    (x : s.data.BaseSite) (hx : (x : s.data.Space) ∈ s.chain.localCube y) (μ ν : Fin 4) :
    |s.grad (s.setting.harmonicExt (s.setting.coarseDelta c)).1 x μ ν| ≤
      fieldKernelConstant 4 L (chosen L).rate (chosen L).bound *
        (s.chain.localSpacing y)⁻¹ * coarseDecay (chosen L) s y c := by
  set nums := chosen L with hnums
  have hC := greenColumnConstant_nonneg (L := L) (δ := nums.rate) F.valid.one_le_bound
  have hξ := localSpacing_pos s.chain y
  have hξi : 0 < (s.chain.localSpacing y)⁻¹ := inv_pos.2 hξ
  have hsum_eq : (s.setting.harmonicExt (s.setting.coarseDelta c)).1 =
      ∑ c₁, invEntry s c₁ c • (s.setting.greenColumn c₁).1 := by
    rw [harmonicExt_coarseDelta_eq_sum s.setting c, coe_finsetSum_smul]
  have hg : s.grad (s.setting.harmonicExt (s.setting.coarseDelta c)).1 x μ ν =
      ∑ c₁, invEntry s c₁ c * s.grad (s.setting.greenColumn c₁).1 x μ ν := by
    rw [hsum_eq]
    exact grad_finsetSum s Finset.univ _ (fun c₁ => (s.setting.greenColumn c₁).1) x μ ν
  rw [hg]
  have hR : fieldKernelConstant 4 L nums.rate nums.bound * (s.chain.localSpacing y)⁻¹ *
      coarseDecay nums s y c = (s.chain.localSpacing y)⁻¹ *
        (fieldKernelConstant 4 L nums.rate nums.bound * coarseDecay nums s y c) := by ring
  rw [hR, ← fieldKernelConstant_eq]
  calc |∑ c₁, invEntry s c₁ c * s.grad (s.setting.greenColumn c₁).1 x μ ν|
      ≤ ∑ c₁, |invEntry s c₁ c * s.grad (s.setting.greenColumn c₁).1 x μ ν| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c₁, (s.chain.localSpacing y)⁻¹ * (greenColumnConstant 4 L nums.rate nums.bound *
          (|invEntry s c₁ c| *
          (s.chain.localSpacing y ^ 2 * GreenColumns.siteDecay nums s y c₁))) := by
        refine Finset.sum_le_sum fun c₁ _ => ?_
        rw [abs_mul]
        have h1 := (hcol c₁).grad_le y hy x hx μ ν
        calc |invEntry s c₁ c| * |s.grad (s.setting.greenColumn c₁).1 x μ ν|
            ≤ |invEntry s c₁ c| * (greenColumnConstant 4 L nums.rate nums.bound *
                s.chain.localSpacing y * GreenColumns.siteDecay nums s y c₁) :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ = _ := by
            field_simp
    _ = (s.chain.localSpacing y)⁻¹ * (greenColumnConstant 4 L nums.rate nums.bound *
          ∑ c₁, |invEntry s c₁ c| *
          (s.chain.localSpacing y ^ 2 * GreenColumns.siteDecay nums s y c₁)) := by
        simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sum_invEntry_le F hy c) hC) hξi.le
theorem cutoffGradSeminorm_harmonicExt_le [Fintype s.setting.CoarseBond] (F : SumInputs s)
    (hcol : ∀ c, GreenColumns.ColumnEstimates (chosen L) s c)
    {y : s.data.Space} (hy : y ∈ s.chain.shellSitesUnion) (c : s.setting.CoarseBond) {α : ℝ}
    (h0 : 0 ≤ α) (h1 : α < 1) {ζ : s.data.Space → ℂ}
    (hζ : s.IsSmoothSupportedInDoubleCube y ζ)
    (path : PeriodicLattice.SiteAtLevel L s.m s.scales.levels 0 →
      PeriodicLattice.SiteAtLevel L s.m s.scales.levels 0 →
      List (SeparatedSequences.FineBond L s.m s.scales))
    (hpath : SeparatedSequences.IsGeodesicChoice s.scales path) :
    s.cutoffGradSeminorm α ζ (s.setting.harmonicExt (s.setting.coarseDelta c)).1 path ≤
      ENNReal.ofReal (fieldKernelConstant 4 L (chosen L).rate (chosen L).bound *
          ((chosen L).holderBound α / (chosen L).bound) *
          s.chain.localSpacing y ^ (-1 - α) * coarseDecay (chosen L) s y c) *
        s.cutoffSize α (s.chain.localSpacing y) ζ := by
  set nums := chosen L with hnums
  have hξ := localSpacing_pos s.chain y
  have hCne : nums.bound ≠ 0 := by
    have h1 := F.valid.one_le_bound
    have h2 : (0 : ℝ) < nums.bound := by linarith
    exact h2.ne'
  set S := s.cutoffSize α (s.chain.localSpacing y) ζ with hS
  set K : ℝ := (1 + (L : ℝ) ^ 4) * Real.exp (nums.rate * cellRadius 4 L) * nums.holderBound α
    with hK
  have hpow : s.chain.localSpacing y ^ (1 - α) =
      s.chain.localSpacing y ^ (-1 - α) * s.chain.localSpacing y ^ 2 := by
    have : (1 - α) = (-1 - α) + ((2 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [this, Real.rpow_add hξ, Real.rpow_natCast]
  have hsum_eq : (s.setting.harmonicExt (s.setting.coarseDelta c)).1 =
      ∑ c₁, invEntry s c₁ c • (s.setting.greenColumn c₁).1 := by
    rw [harmonicExt_coarseDelta_eq_sum s.setting c, coe_finsetSum_smul]
  rw [hsum_eq]
  refine (cutoffGradSeminorm_finsetSum_le s Finset.univ _ _ α ζ path).trans ?_
  have hterm : ∀ c₁ : s.setting.CoarseBond,
      ENNReal.ofReal |invEntry s c₁ c| *
          s.cutoffGradSeminorm α ζ (s.setting.greenColumn c₁).1 path ≤
        ENNReal.ofReal (|invEntry s c₁ c| * (K * s.chain.localSpacing y ^ (1 - α) *
            GreenColumns.siteDecay nums s y c₁)) * S := by
    intro c₁
    rw [ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]
    exact mul_le_mul' le_rfl ((hcol c₁).holder_le y hy α h0 h1 ζ hζ path hpath)
  refine (Finset.sum_le_sum fun c₁ _ => hterm c₁).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul' ?_ le_rfl
  by_cases hK0 : 0 ≤ K
  · have hnn : ∀ c₁ ∈ (Finset.univ : Finset s.setting.CoarseBond),
        0 ≤ |invEntry s c₁ c| * (K * s.chain.localSpacing y ^ (1 - α) *
          GreenColumns.siteDecay nums s y c₁) := fun c₁ _ =>
      mul_nonneg (abs_nonneg _)
        (mul_nonneg (mul_nonneg hK0 (Real.rpow_nonneg hξ.le _)) (Real.exp_pos _).le)
    rw [← ENNReal.ofReal_sum_of_nonneg hnn]
    apply ENNReal.ofReal_le_ofReal
    have hprod : 0 ≤ K * s.chain.localSpacing y ^ (-1 - α) :=
      mul_nonneg hK0 (Real.rpow_nonneg hξ.le _)
    calc ∑ c₁, |invEntry s c₁ c| * (K * s.chain.localSpacing y ^ (1 - α) *
            GreenColumns.siteDecay nums s y c₁)
        = K * s.chain.localSpacing y ^ (-1 - α) * ∑ c₁, |invEntry s c₁ c| *
            (s.chain.localSpacing y ^ 2 * GreenColumns.siteDecay nums s y c₁) := by
          rw [Finset.mul_sum, hpow]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ K * s.chain.localSpacing y ^ (-1 - α) * (inverseKernelConstant 4 L * (L : ℝ) ^ 2 *
            (2 * 4 * expSumConstant 4 L (nums.rate / 4)) * coarseDecay nums s y c) :=
          mul_le_mul_of_nonneg_left (sum_invEntry_le F hy c) hprod
      _ = _ := by
          rw [hK]
          unfold fieldKernelConstant greenColumnConstant
          push_cast
          field_simp
  · have hK' : K < 0 := not_le.1 hK0
    have hz : ∀ c₁ : s.setting.CoarseBond, ENNReal.ofReal (|invEntry s c₁ c| *
        (K * s.chain.localSpacing y ^ (1 - α) *
          GreenColumns.siteDecay nums s y c₁)) = 0 := by
      intro c₁
      apply ENNReal.ofReal_of_nonpos
      apply mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_pos _).le
      exact mul_nonpos_of_nonpos_of_nonneg hK'.le (Real.rpow_nonneg hξ.le _)
    simp only [hz, Finset.sum_const_zero]
    exact zero_le
end Bounds
theorem statement_holds (hG : GreenBoundsStatement)
    (hZ : CoarseGreenInverse.Statement)
    (hCol : GreenColumnsStatement)
    (hFl : InverseBoundsStatement)
    (hCells : SeparatedChainStructure)
    (hRows : CoarseBondFormsAndMatricesHold) :
    HarmonicExtBounds.Statement := by
  intro L hL s hs
  have hw := hG L hL
  have hH := hZ L hL s hs
  obtain ⟨hM, hP⟩ := hs
  have hblock : (chosen L).blockLower ≤ (s.data.blockCount : ℝ) :=
    (le_max_left _ _).trans hM
  have hLM : (L : ℝ) ≤ (s.data.blockCount : ℝ) := (le_max_right _ _).trans hM
  have hLM' : L ≤ s.data.blockCount := by exact_mod_cast hLM
  have hgap : (chosen L).gapLower ≤ (s.data.gapCount : ℝ) * (s.data.blockCount : ℝ) :=
    (le_max_left _ _).trans hP
  have hab : (chosen L).AboveLowerBounds s := ⟨hblock, hgap⟩
  have hGs := hw.holdsFor s hab
  obtain ⟨-, hcol, -, -⟩ := hCol L s hab hLM'
  obtain ⟨hord, hrest⟩ := hFl
  obtain ⟨hsums, htrade⟩ := hrest s.setting hLM' hP
  have hc := hCells s.data s.chain
  have F : SumInputs s :=
    { valid := hw
      inverse := hH
      ordered := hord L hL
      sums := hsums
      trade := htrade
      pseudometric := hc.2.2.2.2.2.2.2.2
      shells := hc.2.1
      anchors := fun c => ((hRows s.setting).1.1 c).2 }
  have := finite_coarseBond s.setting
  have := Fintype.ofFinite s.setting.CoarseBond
  refine
    { wellPosed := ⟨hGs.lap_pos, hH.isUnit⟩
      expansion := ?_
      kernel_le := fun y hy c b hb => harmonicExtKernel_le F hcol hy c b hb
      grad_le := fun y hy c x hx μ ν => grad_harmonicExt_le F hcol hy c x hx μ ν
      holder_le := fun y hy c α h0 h1 ζ hζ path hpath =>
        cutoffGradSeminorm_harmonicExt_le F hcol hy c h0 h1 hζ path hpath }
  intro B b
  rw [finsum_eq_sum_of_fintype, harmonicExt_eq_sum s.setting B, coe_finsetSum_smul,
    Finset.sum_apply]
  exact Finset.sum_congr rfl fun c _ => by
    change B c * _ = _
    rw [mul_comm]
    rfl
end YangMills.Construction.GeneralTorus.HarmonicExtBounds

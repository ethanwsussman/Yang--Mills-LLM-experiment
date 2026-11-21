import YangMills.Construction.InfiniteLattice.EquilibriumClassIsTheSetOfGibbsStates
import YangMills.Construction.Matrices.HaarPositivityOnOpenSets
import YangMills.Construction.Matrices.MapsPreservingTheProductOfHaarMeasures
import YangMills.Construction.TransferOperators.PeriodicStatesHaarMeasureCubicLatticesAndIntegralOperators
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.TransferOperators.GibbsHaarKernels
open YangMills.Construction.InfiniteLattice YangMills.Construction.Schatten
section Kernels
variable {X : Type} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
theorem integrable_of_memL2 (f : Lp ℂ 2 μ) : Integrable f μ :=
  (Lp.memLp f).integrable (by norm_num)
theorem integral_norm_le_L2norm (f : Lp ℂ 2 μ) : ∫ x, ‖f x‖ ∂μ ≤ ‖f‖ := by
  have h : eLpNorm f 1 μ ≤ eLpNorm f 2 μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable f)
  rw [Lp.norm_def, integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) ?_
  simpa [eLpNorm_one_eq_lintegral_enorm] using h
variable {μ}
variable {K L : X × X → ℂ}
theorem norm_le_kernelSup (hK : Continuous K) (z : X × X) : ‖K z‖ ≤ ⨆ z, ‖K z‖ :=
  le_ciSup (isCompact_range hK.norm).bddAbove z
theorem kernelSup_nonneg (K : X × X → ℂ) : 0 ≤ ⨆ z, ‖K z‖ :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem integrable_kernel_slice_mul (hK : Continuous K) (x : X) {g : X → ℂ}
    (hg : Integrable g μ) : Integrable (fun y => K (x, y) * g y) μ :=
  hg.bdd_mul (hK.comp (Continuous.prodMk_right x)).aestronglyMeasurable
    (ae_of_all _ fun _ => norm_le_kernelSup hK _)
theorem integrable_prod_kernel (hK : Continuous K) {f g : X → ℂ} (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (fun z : X × X => f z.1 * K z * g z.2) (μ.prod μ) := by
  have h := (hf.mul_prod hg).bdd_mul (f := K) hK.aestronglyMeasurable
    (ae_of_all _ (norm_le_kernelSup hK))
  refine h.congr (ae_of_all _ fun z => ?_)
  ring
theorem continuous_kernelApply (hK : Continuous K) (f : Lp ℂ 2 μ) :
    Continuous (kernelApply μ K f) := by
  have hf := integrable_of_memL2 μ f
  show Continuous fun x => ∫ y, K (x, y) * f y ∂μ
  refine continuous_of_dominated (bound := fun y => (⨆ z, ‖K z‖) * ‖f y‖)
    (fun x => (integrable_kernel_slice_mul hK x hf).aestronglyMeasurable)
    (fun x => ae_of_all _ fun y => ?_) (hf.norm.const_mul _) (ae_of_all _ fun y => ?_)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_le_kernelSup hK _) (norm_nonneg _)
  · exact (hK.comp (Continuous.prodMk_left y)).mul continuous_const
theorem norm_kernelApply_le (hK : Continuous K) (f : Lp ℂ 2 μ) (x : X) :
    ‖kernelApply μ K f x‖ ≤ (⨆ z, ‖K z‖) * ‖f‖ := by
  have hf := integrable_of_memL2 μ f
  calc ‖∫ y, K (x, y) * f y ∂μ‖ ≤ ∫ y, ‖K (x, y) * f y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (⨆ z, ‖K z‖) * ‖f y‖ ∂μ := by
        refine integral_mono (integrable_kernel_slice_mul hK x hf).norm (hf.norm.const_mul _) fun y => ?_
        show ‖K (x, y) * f y‖ ≤ (⨆ z, ‖K z‖) * ‖f y‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_le_kernelSup hK _) (norm_nonneg _)
    _ = (⨆ z, ‖K z‖) * ∫ y, ‖f y‖ ∂μ := integral_const_mul _ _
    _ ≤ (⨆ z, ‖K z‖) * ‖f‖ :=
        mul_le_mul_of_nonneg_left (integral_norm_le_L2norm μ f) (kernelSup_nonneg K)
variable (μ) in
def kernelLinearToCont (hK : Continuous K) : Lp ℂ 2 μ →ₗ[ℂ] C(X, ℂ) where
  toFun f := ⟨kernelApply μ K f, continuous_kernelApply hK f⟩
  map_add' f g := by
    ext x
    show ∫ y, K (x, y) * (f + g : Lp ℂ 2 μ) y ∂μ =
      (∫ y, K (x, y) * f y ∂μ) + ∫ y, K (x, y) * g y ∂μ
    rw [← integral_add (integrable_kernel_slice_mul hK x (integrable_of_memL2 μ f))
      (integrable_kernel_slice_mul hK x (integrable_of_memL2 μ g))]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy, Pi.add_apply, mul_add]
  map_smul' c f := by
    ext x
    show ∫ y, K (x, y) * (c • f : Lp ℂ 2 μ) y ∂μ = c • ∫ y, K (x, y) * f y ∂μ
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c f] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
variable (μ) in
def kernelOpOfContinuous (hK : Continuous K) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousMap.toLp 2 μ ℂ).comp ((kernelLinearToCont μ hK).mkContinuous (⨆ z, ‖K z‖) fun f =>
    (ContinuousMap.norm_le _
      (mul_nonneg (kernelSup_nonneg K) (norm_nonneg _))).2 fun x => norm_kernelApply_le hK f x)
theorem hasKernel_kernelOp (hK : Continuous K) :
    HasKernel μ K (kernelOp μ K) := by
  refine Classical.epsilon_spec (p := HasKernel μ K) ⟨kernelOpOfContinuous μ hK, fun f => ?_⟩
  exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (kernelLinearToCont μ hK f)
theorem norm_kernelOp_le (hK : Continuous K) :
    ‖kernelOp μ K‖ ≤ ⨆ z, ‖K z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (kernelSup_nonneg K) fun f => ?_
  have h := Lp.norm_le_of_ae_bound (f := kernelOp μ K f)
    (mul_nonneg (kernelSup_nonneg K) (norm_nonneg f)) (by
      filter_upwards [hasKernel_kernelOp hK f] with x hx
      rw [hx]
      exact norm_kernelApply_le hK f x)
  simpa [measureUnivNNReal] using h
theorem im_kernelOp_ae_eq_zero (hK : Continuous K) (hre : ∀ z, (K z).im = 0)
    (g : Lp ℂ 2 μ) (hg : ∀ᵐ y ∂μ, (g y).im = 0) :
    ∀ᵐ x ∂μ, (kernelOp μ K g x).im = 0 := by
  filter_upwards [hasKernel_kernelOp hK g] with x hx
  rw [hx]
  have h := Complex.imCLM.integral_comp_comm
    (integrable_kernel_slice_mul hK x (integrable_of_memL2 μ g))
  show Complex.imCLM (∫ y, K (x, y) * g y ∂μ) = 0
  rw [← h]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hg] with y hy
  simp [Complex.mul_im, hre, hy]
theorem inner_kernelOp_symm (hK : Continuous K) (hre : ∀ z, (K z).im = 0)
    (hsym : ∀ x x', K (x, x') = K (x', x)) (g f : Lp ℂ 2 μ) :
    inner ℂ g (kernelOp μ K f) = inner ℂ (kernelOp μ K g) f := by
  have hg := integrable_of_memL2 μ g
  have hf := integrable_of_memL2 μ f
  have hconj : Integrable (fun x => conj (g x)) μ :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hg
  have hint : Integrable (Function.uncurry fun x y => conj (g x) * K (x, y) * f y) (μ.prod μ) :=
    (integrable_prod_kernel hK hconj hf).congr (ae_of_all _ fun _ => rfl)
  have h1 : inner ℂ g (kernelOp μ K f) =
      ∫ x, ∫ y, conj (g x) * K (x, y) * f y ∂μ ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hasKernel_kernelOp hK f] with x hx
    rw [hx, RCLike.inner_apply']
    show conj (g x) * ∫ y, K (x, y) * f y ∂μ = _
    rw [← integral_const_mul]
    simp_rw [mul_assoc]
  have h2 : inner ℂ (kernelOp μ K g) f =
      ∫ x, ∫ y, conj (g y) * K (y, x) * f x ∂μ ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hasKernel_kernelOp hK g] with x hx
    rw [hx, RCLike.inner_apply']
    show conj (∫ y, K (x, y) * g y ∂μ) * f x = _
    rw [← integral_conj, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have hc : conj (K (x, y)) = K (y, x) := by
      rw [Complex.conj_eq_iff_im.2 (hre _), hsym]
    show conj (K (x, y) * g y) * f x = _
    rw [map_mul, hc]
    ring
  rw [h1, h2]
  exact integral_integral_swap hint
theorem continuous_kernel_comp (hK : Continuous K) (hL : Continuous L) :
    Continuous fun z : X × X => ∫ y, K (z.1, y) * L (y, z.2) ∂μ := by
  refine continuous_of_dominated (bound := fun _ => (⨆ z, ‖K z‖) * ⨆ z, ‖L z‖)
    (fun z => ?_) (fun z => ae_of_all _ fun y => ?_) (integrable_const _)
    (ae_of_all _ fun y => ?_)
  · exact ((hK.comp (Continuous.prodMk_right z.1)).mul
      (hL.comp (Continuous.prodMk_left z.2))).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul (norm_le_kernelSup hK _) (norm_le_kernelSup hL _) (norm_nonneg _)
      (kernelSup_nonneg K)
  · exact (hK.comp (continuous_fst.prodMk continuous_const)).mul
      (hL.comp (continuous_const.prodMk continuous_snd))
theorem kernelOp_comp (hK : Continuous K) (hL : Continuous L) :
    (kernelOp μ K).comp (kernelOp μ L) =
      kernelOp μ fun z : X × X => ∫ y, K (z.1, y) * L (y, z.2) ∂μ := by
  have hM := continuous_kernel_comp (μ := μ) hK hL
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  have h1 := hasKernel_kernelOp hK (kernelOp μ L f)
  have h3 := hasKernel_kernelOp hM f
  rw [ContinuousLinearMap.comp_apply]
  refine h1.trans (Filter.EventuallyEq.trans (ae_of_all _ fun x => ?_) h3.symm)
  show ∫ y, K (x, y) * (kernelOp μ L f) y ∂μ =
    ∫ v, (∫ y, K (x, y) * L (y, v) ∂μ) * f v ∂μ
  have e1 : ∫ y, K (x, y) * (kernelOp μ L f) y ∂μ =
      ∫ y, ∫ v, K (x, y) * L (y, v) * f v ∂μ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hasKernel_kernelOp hL f] with y hy
    rw [hy]
    show K (x, y) * ∫ v, L (y, v) * f v ∂μ = _
    rw [← integral_const_mul]
    simp_rw [mul_assoc]
  have e2 : ∫ v, (∫ y, K (x, y) * L (y, v) ∂μ) * f v ∂μ =
      ∫ v, ∫ y, K (x, y) * L (y, v) * f v ∂μ ∂μ :=
    integral_congr_ae (ae_of_all _ fun v => (integral_mul_const _ _).symm)
  rw [e1, e2]
  have hx : Integrable (fun y => K (x, y)) μ :=
    Integrable.of_bound (hK.comp (Continuous.prodMk_right x)).aestronglyMeasurable _
      (ae_of_all _ fun _ => norm_le_kernelSup hK _)
  exact integral_integral_swap (f := fun y v => K (x, y) * L (y, v) * f v)
    (integrable_prod_kernel hL hx (integrable_of_memL2 μ f))
theorem kernel_eq_of_kernelOp_eq [μ.IsOpenPosMeasure] (hK : Continuous K)
    (hL : Continuous L) (h : kernelOp μ K = kernelOp μ L) : K = L := by
  funext ⟨x, v⟩
  have hsK : Continuous fun y => K (x, y) := hK.comp (Continuous.prodMk_right x)
  have hsL : Continuous fun y => L (x, y) := hL.comp (Continuous.prodMk_right x)
  let D : C(X, ℂ) := ⟨fun y => conj (K (x, y) - L (x, y)),
    Complex.continuous_conj.comp (hsK.sub hsL)⟩
  let g : Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ D
  have hg : g =ᵐ[μ] D := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ D
  have hint := integrable_of_memL2 μ g
  have hae : kernelApply μ K g =ᵐ[μ] kernelApply μ L g := by
    have h1 := hasKernel_kernelOp hK g
    have h2 := hasKernel_kernelOp hL g
    rw [h] at h1
    exact h1.symm.trans h2
  have hx : ∫ y, K (x, y) * g y ∂μ = ∫ y, L (x, y) * g y ∂μ := congrFun
    ((Continuous.ae_eq_iff_eq μ (continuous_kernelApply hK g)
      (continuous_kernelApply hL g)).1 hae) x
  have hz : ∫ y, (((‖K (x, y) - L (x, y)‖ ^ 2 : ℝ)) : ℂ) ∂μ = 0 := by
    have h0 : ∫ y, (K (x, y) * g y - L (x, y) * g y) ∂μ = 0 := by
      rw [integral_sub (integrable_kernel_slice_mul hK x hint)
        (integrable_kernel_slice_mul hL x hint), hx, sub_self]
    rw [← h0]
    refine integral_congr_ae ?_
    filter_upwards [hg] with y hy
    rw [hy, ← sub_mul]
    show _ = (K (x, y) - L (x, y)) * conj (K (x, y) - L (x, y))
    rw [Complex.mul_conj']
    push_cast
    rfl
  have hcont : Continuous fun y => ‖K (x, y) - L (x, y)‖ ^ 2 := ((hsK.sub hsL).norm).pow 2
  have hz' : ∫ y, ‖K (x, y) - L (x, y)‖ ^ 2 ∂μ = 0 := by
    rw [integral_complex_ofReal] at hz
    exact_mod_cast hz
  have hi : Integrable (fun y => ‖K (x, y) - L (x, y)‖ ^ 2) μ := by
    obtain ⟨C, hC⟩ := (isCompact_range hcont).bddAbove
    refine Integrable.of_bound hcont.aestronglyMeasurable C (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hC ⟨y, rfl⟩
  have h0 := (integral_eq_zero_iff_of_nonneg (fun y => by positivity) hi).1 hz'
  have h1 := congrFun ((Continuous.ae_eq_iff_eq μ hcont continuous_const).1 h0) v
  have h2 : ‖K (x, v) - L (x, v)‖ ^ 2 = 0 := h1
  have h3 : K (x, v) - L (x, v) = 0 := by simpa using h2
  exact sub_eq_zero.1 h3
end Kernels
theorem gibbsStatesCharacterized_holds (hE : GibbsClassEqGibbsStates) (β : ℝ)
    (hβ : 0 < β) : GibbsStatesCharacterized β := by
  intro ν _
  obtain ⟨h1, h2⟩ := hE.2.1 1 zero_lt_one β hβ
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]
    rfl
  · rw [h2]
    rfl
  · simp only [periodicGibbsClass, Set.mem_iUnion, exists_prop]
theorem haarPiInvariance_holds (hMaps : Matrices.ComplexMatrix2.HaarPiInvariance.statement)
    (hOpen : Matrices.HaarPositivity.OpenPositiveStatement) (J : Type) [Finite J] :
    HaarPiInvariance J := by
  have preserving : ∀ j : J → Matrices.ComplexMatrix2.specialUnitary →
      Matrices.ComplexMatrix2.specialUnitary,
      (∀ b, Matrices.ComplexMatrix2.IsBiTranslateOrInvBiTranslate (j b)) →
      MeasurePreserving (fun (u : J → Matrices.ComplexMatrix2.specialUnitary) (b : J) => j b (u b))
        (Matrices.ComplexMatrix2.haarPi J) (Matrices.ComplexMatrix2.haarPi J) := by
    intro j hj
    obtain ⟨-, hm, hinv⟩ := hMaps J (Equiv.refl J) j hj
    refine ⟨hm, Measure.ext fun E hE => ?_⟩
    exact (Measure.map_apply hm hE).trans (hinv E hE)
  have hpos : (Matrices.ComplexMatrix2.haarPi J).IsOpenPosMeasure :=
    ⟨fun U hU hne => (hOpen J U hU hne).ne'⟩
  refine ⟨fun g g' => preserving (fun b x => g b * x * g' b) fun b => ⟨g b, g' b, Or.inl fun _ => rfl⟩,
    fun c => ?_, fun O hO hne => hOpen J O hO hne,
    fun f f' hf hf' h => (Continuous.ae_eq_iff_eq _ hf hf').1 h⟩
  classical
  have h := preserving (fun b x => if b = c then x⁻¹ else x) fun b => by
    by_cases hb : b = c
    · exact ⟨1, 1, Or.inr fun x => by simp [hb]⟩
    · exact ⟨1, 1, Or.inl fun x => by simp [hb]⟩
  convert h using 1
  funext u b
  simp only [invertAt]
theorem cubicPeriodSublatticeIffThreeLe_holds : CubicPeriodSublatticeIffThreeLe := by
  intro s hs
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have member : ∀ i : Fin 4, (Pi.single i (s : ℝ) : AmbientSpace) ∈ latticeSubgroup 1 := fun i =>
    ⟨Pi.single i (s : ℤ), fun k => by
      by_cases h : k = i
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]⟩
  have memberCubic : ∀ i : Fin 4,
      (Pi.single i (s : ℝ) : AmbientSpace) ∈ latticeSubgroup (s : ℝ) := fun i =>
    ⟨Pi.single i 1, fun k => by
      by_cases h : k = i
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]⟩
  have vector : ∀ i : Fin 4,
      (⟨Pi.single i (s : ℝ), member i⟩ : LatticePoint 1) ∈ cubicSublattice 1 (s : ℝ) := fun i => by
    rw [cubicSublattice, AddSubgroup.mem_addSubgroupOf]
    exact memberCubic i
  constructor
  · rintro ⟨Γ, hΓ⟩
    have hmem : (⟨Pi.single 0 (s : ℝ), member 0⟩ : LatticePoint 1) ∈ Γ.periods := hΓ ▸ vector 0
    have hne : (⟨Pi.single 0 (s : ℝ), member 0⟩ : LatticePoint 1) ≠ 0 := by
      intro h
      have h0 := congrFun (congrArg Subtype.val h) 0
      simp at h0
      omega
    have hn := Γ.le_norm_of_ne_zero _ hmem hne
    have hnorm : ‖(Pi.single 0 (s : ℝ) : AmbientSpace)‖ ≤ s :=
      (pi_norm_le_iff_of_nonneg hs0.le).2 fun i => by
        by_cases h : i = 0
        · subst h
          simp
        · simp [Pi.single_eq_of_ne h]
    have h3 : (3 : ℝ) ≤ s := by
      have := hn.trans hnorm
      simpa [minimalPeriodRatio] using this
    exact_mod_cast h3
  · intro h3
    have h3' : (3 : ℝ) ≤ s := by exact_mod_cast h3
    refine ⟨⟨cubicSublattice 1 (s : ℝ), ⟨fun i => ⟨Pi.single i (s : ℝ), member i⟩, vector, ?_⟩, ?_⟩, rfl⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hi := congrFun hg i
      simp [Finset.sum_apply, Pi.single_apply] at hi
      rcases hi with hi | hi
      · exact hi
      · omega
    · intro γ hγ hne
      rw [cubicSublattice, AddSubgroup.mem_addSubgroupOf] at hγ
      obtain ⟨n, hn⟩ := hγ
      have hex : ∃ k, n k ≠ 0 := by
        by_contra hall
        simp only [not_exists, not_not] at hall
        exact hne (Subtype.ext (funext fun k => by simp [hn, hall]))
      obtain ⟨k, hk⟩ := hex
      have h1 : (1 : ℝ) ≤ |(n k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
      calc minimalPeriodRatio * 1 = 3 := by simp [minimalPeriodRatio]
        _ ≤ s := h3'
        _ ≤ |(n k : ℝ)| * s := le_mul_of_one_le_left hs0.le h1
        _ = ‖(γ : AmbientSpace) k‖ := by rw [hn k, Real.norm_eq_abs, abs_mul, abs_of_pos hs0]
        _ ≤ ‖(γ : AmbientSpace)‖ := norm_le_pi_norm _ k
theorem statement_holds (hE : GibbsClassEqGibbsStates)
    (hMaps : Matrices.ComplexMatrix2.HaarPiInvariance.statement)
    (hOpen : Matrices.HaarPositivity.OpenPositiveStatement) : Statement := by
  refine ⟨gibbsStatesCharacterized_holds hE, fun J _ _ => haarPiInvariance_holds hMaps hOpen J,
    cubicPeriodSublatticeIffThreeLe_holds, fun J _ _ => ⟨fun K hK => ?_, ?_, ?_⟩⟩
  · exact ⟨fun g => continuous_kernelApply hK g, hasKernel_kernelOp hK,
      norm_kernelOp_le hK, fun hre g hg => im_kernelOp_ae_eq_zero hK hre g hg,
      fun hre hsym g f => inner_kernelOp_symm hK hre hsym g f⟩
  · intro K K' hK hK'
    exact ⟨continuous_kernel_comp hK hK', kernelOp_comp hK hK'⟩
  · intro K K' hK hK' h
    have hpos : (Matrices.ComplexMatrix2.haarPi J).IsOpenPosMeasure :=
      ⟨fun U hU hne => (hOpen J U hU hne).ne'⟩
    exact kernel_eq_of_kernelOp_eq hK hK' h
end YangMills.Construction.TransferOperators.GibbsHaarKernels
end

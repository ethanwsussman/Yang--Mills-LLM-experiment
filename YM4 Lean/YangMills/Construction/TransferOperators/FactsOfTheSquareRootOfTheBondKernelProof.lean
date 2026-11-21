import YangMills.Construction.Matrices.FactsOnFunctionsAndOperatorsOfSeveralVariablesOnG
import YangMills.Construction.TransferOperators.CharacterCoefficientsOfTheOneBondWeight
import YangMills.Construction.TransferOperators.FactsOfTheSquareRootOfTheBondKernel
import YangMills.Construction.TransferOperators.PeriodicStatesHaarMeasureCubicLatticesAndIntegralOperators
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology
open YangMills.Construction.SpinHarmonics YangMills.Construction.Schatten
open YangMills.Construction.SpinHarmonics.SeveralVariables YangMills.Construction.HilbertSpaceBasics
open YangMills.Construction.TransferOperators.GibbsHaarKernels
open YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.TransferOperators.SqrtLinkFacts
section Products
variable {B ι : Type*} [Fintype B]
theorem summable_pi_prod_of_nonneg (m : B → ι → ℝ) (hm : ∀ b i, 0 ≤ m b i)
    (hs : ∀ b, Summable (m b)) : Summable fun l : B → ι => ∏ b, m b (l b) := by
  classical
  refine summable_of_sum_le (c := ∏ b, ∑' i, m b i)
    (fun l => Finset.prod_nonneg fun b _ => hm b _) fun T => ?_
  let S : B → Finset ι := fun b => T.image fun l => l b
  have hT : T ⊆ Fintype.piFinset S := fun l hl =>
    Fintype.mem_piFinset.mpr fun b => Finset.mem_image_of_mem _ hl
  calc ∑ l ∈ T, ∏ b, m b (l b)
      ≤ ∑ l ∈ Fintype.piFinset S, ∏ b, m b (l b) :=
        Finset.sum_le_sum_of_subset_of_nonneg hT fun l _ _ =>
          Finset.prod_nonneg fun b _ => hm b _
    _ = ∏ b, ∑ i ∈ S b, m b i := (Finset.prod_univ_sum S fun b i => m b i).symm
    _ ≤ ∏ b, ∑' i, m b i :=
        Finset.prod_le_prod (fun b _ => Finset.sum_nonneg fun i _ => hm b i)
          fun b _ => (hs b).sum_le_tsum _ fun i _ => hm b i
theorem hasSum_pi_prod (f : B → ι → ℂ) (hs : ∀ b, Summable fun i => ‖f b i‖) :
    HasSum (fun l : B → ι => ∏ b, f b (l b)) (∏ b, ∑' i, f b i) := by
  classical
  have hn : Summable fun l : B → ι => ‖∏ b, f b (l b)‖ := by
    simpa only [norm_prod] using
      summable_pi_prod_of_nonneg (fun b i => ‖f b i‖) (fun _ _ => norm_nonneg _) hs
  have hg : Summable fun l : B → ι => ∏ b, f b (l b) := hn.of_norm
  have ht : Tendsto (fun S : Finset ι => Fintype.piFinset fun _ : B => S) atTop atTop := by
    refine tendsto_atTop.mpr fun T => ?_
    filter_upwards [eventually_ge_atTop (Finset.univ.biUnion fun b => T.image fun l => l b)]
      with S hS l hl
    refine Fintype.mem_piFinset.mpr fun b => hS ?_
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, Finset.mem_image_of_mem _ hl⟩
  have h₁ := hg.hasSum.comp ht
  have h₂ : Tendsto (fun S : Finset ι => ∏ b, ∑ i ∈ S, f b i) atTop (𝓝 (∏ b, ∑' i, f b i)) :=
    tendsto_finsetProd _ fun b _ => (hs b).of_norm.hasSum
  have he : (fun S : Finset ι => ∏ b, ∑ i ∈ S, f b i) =
      ((fun T : Finset (B → ι) => ∑ l ∈ T, ∏ b, f b (l b)) ∘
        fun S : Finset ι => Fintype.piFinset fun _ : B => S) := by
    funext S
    exact Finset.prod_univ_sum (fun _ => S) fun b i => f b i
  rw [he] at h₂
  have e := tendsto_nhds_unique h₂ h₁
  rw [e]
  exact hg.hasSum
end Products
theorem hasAbsUniformSum_of_dominated {ι X : Type*} (f : ι → X → ℂ) (F : X → ℂ) (M : ι → ℝ)
    (hM : Summable M) (hb : ∀ i x, ‖f i x‖ ≤ M i) (hF : ∀ x, HasSum (fun i => f i x) (F x)) :
    HasAbsUniformSum f F := by
  refine ⟨fun x => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hb i x) hM, ?_⟩
  have h := tendstoUniformly_tsum hM hb
  have hF' : (fun x => ∑' i, f i x) = F := funext fun x => (hF x).tsum_eq
  rwa [hF'] at h
section Hilbert
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
structure OrthogonalResolution (P : ι → H →L[ℂ] H) : Prop where
  inner_symm : ∀ l F G, inner ℂ (P l F) G = inner ℂ F (P l G)
  idem : ∀ l F, P l (P l F) = P l F
  orth : ∀ l l', l ≠ l' → ∀ F, P l (P l' F) = 0
  hasSum : ∀ F, HasSum (fun l => P l F) F
theorem hasSum_smul_apply_of_hasSum {P : ι → H →L[ℂ] H} {w : ι → ℝ} {A : H →L[ℂ] H}
    (h : HasSum (fun l => (w l : ℂ) • P l) A) (F : H) :
    HasSum (fun l => (w l : ℂ) • P l F) (A F) := by
  have h' : Tendsto (fun s : Finset ι => ∑ l ∈ s, (w l : ℂ) • P l) atTop (𝓝 A) := h
  have e : ∀ s : Finset ι, ∑ l ∈ s, (w l : ℂ) • P l F = (∑ l ∈ s, (w l : ℂ) • P l) F :=
    fun s => by simp
  show Tendsto (fun s : Finset ι => ∑ l ∈ s, (w l : ℂ) • P l F) atTop (𝓝 (A F))
  simp only [e]
  exact ((continuous_eval_const F).tendsto A).comp h'
variable {P : ι → H →L[ℂ] H} (hP : OrthogonalResolution P)
include hP
omit hP in
theorem re_inner_self_eq (F : H) : (inner ℂ F F : ℂ).re = ‖F‖ ^ 2 := by
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) F)
theorem OrthogonalResolution.inner_self_proj (l : ι) (F : H) :
    inner ℂ F (P l F) = ((‖P l F‖ ^ 2 : ℝ) : ℂ) := by
  rw [← hP.idem l F, ← hP.inner_symm, hP.idem l F]
  simp [inner_self_eq_norm_sq_to_K]
theorem OrthogonalResolution.hasSum_norm_sq (F : H) :
    HasSum (fun l => ‖P l F‖ ^ 2) (‖F‖ ^ 2) := by
  have h := ((innerSL ℂ F).hasSum (hP.hasSum F))
  simp only [innerSL_apply_apply, hP.inner_self_proj] at h
  have h' := Complex.reCLM.hasSum h
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at h'
  rwa [re_inner_self_eq] at h'
variable {w : ι → ℝ} {A : H →L[ℂ] H} (hA : ∀ F, HasSum (fun l => (w l : ℂ) • P l F) (A F))
include hA
theorem OrthogonalResolution.map_proj (l : ι) (F : H) : A (P l F) = (w l : ℂ) • P l F := by
  classical
  refine (hA (P l F)).unique ?_
  convert hasSum_single l ?_ using 1
  · rw [hP.idem]
  · intro l' hl'
    rw [hP.orth l' l hl', smul_zero]
theorem OrthogonalResolution.proj_map (l : ι) (F : H) : P l (A F) = (w l : ℂ) • P l F := by
  classical
  refine ((P l).hasSum (hA F)).unique ?_
  convert hasSum_single l ?_ using 1
  · simp [hP.idem]
  · intro l' hl'
    rw [map_smul, hP.orth l l' hl'.symm, smul_zero]
theorem OrthogonalResolution.hasSum_inner_map (F : H) :
    HasSum (fun l => w l * ‖P l F‖ ^ 2) (inner ℂ F (A F)).re ∧
      HasSum (fun _ : ι => (0 : ℝ)) (inner ℂ F (A F)).im := by
  have h := ((innerSL ℂ F).hasSum (hA F))
  simp only [innerSL_apply_apply, inner_smul_right, hP.inner_self_proj] at h
  constructor
  · have h' := Complex.reCLM.hasSum h
    simpa [← Complex.ofReal_pow] using h'
  · have h' := Complex.imCLM.hasSum h
    simpa [← Complex.ofReal_pow] using h'
theorem OrthogonalResolution.hasSum_norm_map_sq (F : H) :
    HasSum (fun l => w l ^ 2 * ‖P l F‖ ^ 2) (‖A F‖ ^ 2) := by
  have h := ((innerSL ℂ (A F)).hasSum (hA F))
  have e : ∀ l, inner ℂ (A F) ((w l : ℂ) • P l F) = ((w l ^ 2 * ‖P l F‖ ^ 2 : ℝ) : ℂ) := by
    intro l
    rw [inner_smul_right, ← hP.idem l F, ← hP.inner_symm, hP.proj_map hA, hP.idem l F,
      inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp
    ring
  simp only [innerSL_apply_apply, e] at h
  have h' := Complex.reCLM.hasSum h
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at h'
  rwa [re_inner_self_eq] at h'
theorem OrthogonalResolution.norm_map_le (hw : ∀ l, |w l| ≤ 1) (F : H) : ‖A F‖ ≤ ‖F‖ := by
  have h₁ := hP.hasSum_norm_map_sq hA F
  have h₂ := hP.hasSum_norm_sq F
  have h : ‖A F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    refine hasSum_le (fun l => ?_) h₁ h₂
    have : w l ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) (hw l)
    exact mul_le_of_le_one_left (by positivity) this
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
omit hA in
theorem OrthogonalResolution.hasSum_comp {w₁ w₂ : ι → ℝ} {A₁ A₂ : H →L[ℂ] H}
    (h₁ : ∀ F, HasSum (fun l => (w₁ l : ℂ) • P l F) (A₁ F))
    (h₂ : ∀ F, HasSum (fun l => (w₂ l : ℂ) • P l F) (A₂ F)) (F : H) :
    HasSum (fun l => ((w₁ l * w₂ l : ℝ) : ℂ) • P l F) (A₁ (A₂ F)) := by
  have h := A₁.hasSum (h₂ F)
  convert h using 2 with l
  rw [map_smul, hP.map_proj h₁, smul_smul, Complex.ofReal_mul, mul_comm]
end Hilbert
section Kernels
variable {J : Type} [Finite J] [Nonempty J]
abbrev KernelPoints (J : Type) : Type := (J → specialUnitary) × (J → specialUnitary)
omit [Nonempty J] in
theorem integrable_kernel_mul (A : KernelPoints J → ℂ) (hA : Continuous A) (ψ : HaarL2 J)
    (u : J → specialUnitary) : Integrable (fun w => A (u, w) * ψ w) (haarPi J) := by
  have hc : Continuous fun w => A (u, w) := hA.comp (by fun_prop)
  have h₁ : MemLp (fun w => A (u, w)) 2 (haarPi J) :=
    MemLp.of_bound hc.aestronglyMeasurable ‖(⟨_, hc⟩ : C(J → specialUnitary, ℂ))‖
      (ae_of_all _ fun w => (⟨_, hc⟩ : C(J → specialUnitary, ℂ)).norm_coe_le_norm w)
  exact h₁.integrable_mul (Lp.memLp ψ)
variable (hK : ∀ A : KernelPoints J → ℂ, Continuous A → ContinuousKernelOperatorProps J A)
include hK
theorem kernelOp_add (A A' : KernelPoints J → ℂ) (hA : Continuous A) (hA' : Continuous A') :
    kernelOp (haarPi J) (fun z => A z + A' z) =
      kernelOp (haarPi J) A + kernelOp (haarPi J) A' := by
  ext1 ψ
  apply Lp.ext
  filter_upwards [(hK _ (show Continuous fun z => A z + A' z from hA.add hA')).2.1 ψ, (hK A hA).2.1 ψ, (hK A' hA').2.1 ψ,
    Lp.coeFn_add (kernelOp (haarPi J) A ψ)
      (kernelOp (haarPi J) A' ψ)] with u h₀ h₁ h₂ h₃
  rw [add_apply, h₃, Pi.add_apply, h₀, h₁, h₂]
  simp only [kernelApply, add_mul]
  exact integral_add (integrable_kernel_mul A hA ψ u) (integrable_kernel_mul A' hA' ψ u)
theorem kernelOp_const_mul (c : ℂ) (A : KernelPoints J → ℂ) (hA : Continuous A) :
    kernelOp (haarPi J) (fun z => c * A z) =
      c • kernelOp (haarPi J) A := by
  ext1 ψ
  apply Lp.ext
  filter_upwards [(hK _ (show Continuous fun z => c * A z from continuous_const.mul hA)).2.1 ψ, (hK A hA).2.1 ψ,
    Lp.coeFn_smul c (kernelOp (haarPi J) A ψ)] with u h₀ h₁ h₃
  rw [smul_apply, h₃, Pi.smul_apply, h₀, h₁]
  simp only [kernelApply, mul_assoc, smul_eq_mul]
  exact integral_const_mul _ _
theorem kernelOp_zero :
    kernelOp (haarPi J) (fun _ : KernelPoints J => (0 : ℂ)) = 0 := by
  ext1 ψ
  apply Lp.ext
  filter_upwards [(hK _ continuous_const).2.1 ψ,
    Lp.coeFn_zero ℂ 2 (haarPi J)] with u h₀ h₁
  rw [zero_apply, h₁, h₀]
  simp [kernelApply]
theorem kernelOp_sum {ι : Type*} (s : Finset ι) (f : ι → KernelPoints J → ℂ)
    (hf : ∀ i, Continuous (f i)) :
    kernelOp (haarPi J) (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, kernelOp (haarPi J) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using kernelOp_zero hK
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [kernelOp_add hK _ _ (hf i) (continuous_finsetSum _ fun i _ => hf i), ih]
theorem norm_kernelOp_le (A : KernelPoints J → ℂ) (hA : Continuous A) (ε : ℝ)
    (h : ∀ z, ‖A z‖ ≤ ε) : ‖kernelOp (haarPi J) A‖ ≤ ε :=
  (hK A hA).2.2.1.trans (ciSup_le h)
theorem hasSum_kernelOp {ι : Type*} (f : ι → KernelPoints J → ℂ) (F : KernelPoints J → ℂ)
    (hf : ∀ i, Continuous (f i)) (hF : Continuous F)
    (h : HasAbsUniformSum f F) :
    HasSum (fun i => kernelOp (haarPi J) (f i))
      (kernelOp (haarPi J) F) := by
  show Tendsto (fun s : Finset ι => ∑ i ∈ s, kernelOp (haarPi J) (f i)) atTop
    (𝓝 (kernelOp (haarPi J) F))
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp h.2) (ε / 2) (half_pos hε)] with s hs
  have hc : Continuous fun z => ∑ i ∈ s, f i z := continuous_finsetSum _ fun i _ => hf i
  have hF' : Continuous fun z => (-1 : ℂ) * F z := continuous_const.mul hF
  have e : ∑ i ∈ s, kernelOp (haarPi J) (f i) -
      kernelOp (haarPi J) F =
      kernelOp (haarPi J) fun z => (∑ i ∈ s, f i z) + (-1) * F z := by
    rw [kernelOp_add hK _ _ hc hF', kernelOp_const_mul hK _ _ hF,
      kernelOp_sum hK s f hf]
    simp [sub_eq_add_neg]
  rw [dist_eq_norm, e]
  refine lt_of_le_of_lt (norm_kernelOp_le hK _ (hc.add hF') (ε / 2)
    fun z => ?_) (half_lt_self hε)
  have := (hs z).le
  rw [dist_comm, dist_eq_norm] at this
  simpa [sub_eq_add_neg] using this
end Kernels
section Projections
def spinDim {J : Type} (l : J → HalfNatural) : ℝ := ∏ᶠ b, (2 * (l b).toReal + 1)
theorem halfNatural_toReal_nonneg (l : HalfNatural) : 0 ≤ l.toReal :=
  div_nonneg (Nat.cast_nonneg _) zero_le_two
theorem finprod_sq_eq_spinDim_sq {J : Type} [Finite J] (l : J → HalfNatural) :
    (∏ᶠ b, (2 * (l b).toReal + 1) ^ 2 : ℝ) = spinDim l ^ 2 := by
  let _ := Fintype.ofFinite J
  simp only [spinDim, finprod_eq_prod_of_fintype, Finset.prod_pow]
theorem one_le_spinDim {J : Type} [Finite J] (l : J → HalfNatural) : 1 ≤ spinDim l := by
  let _ := Fintype.ofFinite J
  simp only [spinDim, finprod_eq_prod_of_fintype]
  calc (1 : ℝ) = ∏ _b : J, 1 := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun b _ => by
      linarith [halfNatural_toReal_nonneg (l b)]
variable (h₂ : SeveralVariablesFacts)
variable {J : Type} [Finite J] [Nonempty J]
include h₂
theorem isotypicProj_inner_symm (l : J → HalfNatural) (F G : HaarL2 J) :
    inner ℂ (isotypicProj l F) G = inner ℂ F (isotypicProj l G) := by
  have h := (h₂ J l ⟨0⟩).1.2.2.2.2.2.1.1.1
  have h' : star (isotypicProj l) = isotypicProj l := h.symm
  calc inner ℂ (isotypicProj l F) G = inner ℂ ((star (isotypicProj l)) F) G := by
        rw [h']
    _ = inner ℂ F (isotypicProj l G) := ContinuousLinearMap.adjoint_inner_left _ _ _
theorem isotypicProj_idem (l : J → HalfNatural) (F : HaarL2 J) :
    isotypicProj l (isotypicProj l F) = isotypicProj l F := by
  have h := (h₂ J l ⟨0⟩).1.2.2.2.2.2.1.1.2
  exact (congrArg (fun T : HaarL2 J →L[ℂ] HaarL2 J => T F) h).symm
theorem isotypicProj_mem (l : J → HalfNatural) (F : HaarL2 J) :
    isotypicProj l F ∈ prodCoeffSpanL2 l := by
  have h := (h₂ J l ⟨0⟩).1.2.2.2.2.2.1.2
  have h' : isotypicProj l F ∈ Set.range (isotypicProj l) := Set.mem_range_self F
  rw [h] at h'
  exact h'
theorem isotypicProj_of_mem (l : J → HalfNatural) (F : HaarL2 J)
    (hF : F ∈ prodCoeffSpanL2 l) : isotypicProj l F = F := by
  have h := (h₂ J l ⟨0⟩).1.2.2.2.2.2.1.2
  have h' : F ∈ Set.range (isotypicProj l) := by
    rw [h]
    exact hF
  obtain ⟨G, rfl⟩ := h'
  exact isotypicProj_idem h₂ l G
theorem isotypicProj_resolution :
    OrthogonalResolution (fun l : J → HalfNatural => isotypicProj l) where
  inner_symm := isotypicProj_inner_symm h₂
  idem := isotypicProj_idem h₂
  orth l l' hll F := by
    have hO := (h₂ J l ⟨0⟩).1.2.2.2.2.2.2.2 hll
    have h : inner ℂ (isotypicProj l (isotypicProj l' F))
        (isotypicProj l (isotypicProj l' F)) = (0 : ℂ) := by
      rw [← isotypicProj_inner_symm h₂ l _ (isotypicProj l' F)]
      exact Submodule.isOrtho_iff_inner_eq.mp hO _ (isotypicProj_mem h₂ l _) _
        (isotypicProj_mem h₂ l' F)
    exact inner_self_eq_zero.mp h
  hasSum F := ((h₂ J (fun _ => ⟨0⟩) ⟨0⟩).2.1 F).2.1
theorem isotypicKernel_eq_sum (l : J → HalfNatural) (u u' : J → specialUnitary) :
    isotypicKernel l u u' =
      ∑ α ∈ indicesWithSpins l, peterWeylFn α u * star (peterWeylFn α u') :=
  (h₂ J l ⟨0⟩).1.2.2.2.1 u u'
theorem isotypicKernel_im (l : J → HalfNatural) (u u' : J → specialUnitary) :
    (isotypicKernel l u u').im = 0 :=
  ((h₂ J l ⟨0⟩).1.2.2.2.2.1 u u').1
theorem isotypicKernel_comm (l : J → HalfNatural) (u u' : J → specialUnitary) :
    isotypicKernel l u u' = isotypicKernel l u' u :=
  ((h₂ J l ⟨0⟩).1.2.2.2.2.1 u u').2
theorem isotypicKernel_diag (l : J → HalfNatural) (u : J → specialUnitary) :
    isotypicKernel l u u = ((spinDim l ^ 2 : ℝ) : ℂ) := by
  rw [← finprod_sq_eq_spinDim_sq]
  exact ((h₂ J l ⟨0⟩).2.2.2.1.1 u).2.2
theorem sum_norm_peterWeylFn_sq (l : J → HalfNatural) (u : J → specialUnitary) :
    ∑ α ∈ indicesWithSpins l, ‖peterWeylFn α u‖ ^ 2 = spinDim l ^ 2 := by
  have h₁ := isotypicKernel_eq_sum h₂ l u u
  rw [isotypicKernel_diag h₂] at h₁
  have e : ∀ α : PeterWeylIndex J, peterWeylFn α u * star (peterWeylFn α u) =
      ((‖peterWeylFn α u‖ ^ 2 : ℝ) : ℂ) := fun α => by
    rw [← starRingEnd_apply, Complex.mul_conj']
    push_cast
    rfl
  simp only [e] at h₁
  exact_mod_cast h₁.symm
theorem norm_peterWeylFn_apply_le (α : PeterWeylIndex J) (u : J → specialUnitary) :
    ‖peterWeylFn α u‖ ≤ spinDim (spins α) := by
  have hm : α ∈ indicesWithSpins (spins α) := (Set.Finite.mem_toFinset _).mpr rfl
  have h := Finset.single_le_sum (f := fun α' => ‖peterWeylFn α' u‖ ^ 2)
    (fun _ _ => by positivity) hm
  simp only [sum_norm_peterWeylFn_sq h₂] at h
  exact (sq_le_sq₀ (norm_nonneg _) (zero_le_one.trans (one_le_spinDim _))).mp h
theorem norm_isotypicKernel_le (l : J → HalfNatural) (u u' : J → specialUnitary) :
    ‖isotypicKernel l u u'‖ ≤ spinDim l ^ 2 := by
  rw [isotypicKernel_eq_sum h₂]
  calc ‖∑ α ∈ indicesWithSpins l, peterWeylFn α u * star (peterWeylFn α u')‖
      ≤ ∑ α ∈ indicesWithSpins l, ‖peterWeylFn α u * star (peterWeylFn α u')‖ :=
        norm_sum_le _ _
    _ ≤ ∑ α ∈ indicesWithSpins l, (‖peterWeylFn α u‖ ^ 2 + ‖peterWeylFn α u'‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun α _ => ?_
        rw [norm_mul, norm_star]
        nlinarith [sq_nonneg (‖peterWeylFn α u‖ - ‖peterWeylFn α u'‖)]
    _ = spinDim l ^ 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, sum_norm_peterWeylFn_sq h₂,
          sum_norm_peterWeylFn_sq h₂]
        ring
theorem continuous_isotypicKernel (l : J → HalfNatural) :
    Continuous fun p : KernelPoints J => isotypicKernel l p.1 p.2 := by
  simp only [isotypicKernel_eq_sum h₂]
  exact continuous_finsetSum _ fun α _ =>
    ((peterWeylFn α).continuous.comp continuous_fst).mul
      (continuous_star.comp ((peterWeylFn α).continuous.comp continuous_snd))
omit [Finite J] [Nonempty J] in
theorem norm_dim_mul_spinCharacter_le (l : HalfNatural) (g : specialUnitary) :
    ‖((2 * l.toReal + 1 : ℝ) : ℂ) * spinCharacter l g‖ ≤ (2 * l.toReal + 1) ^ 2 := by
  have h := norm_isotypicKernel_le h₂ (J := Unit) (fun _ => l) (fun _ => g) (fun _ => 1)
  simpa [isotypicKernel, spinDim, finprod_unique] using h
end Projections
section Coefficients
variable {β : ℝ} (hv : ∀ l, WeightCharCoeffBounds β l)
variable {B : Type} [Finite B]
def charCoeffReal (β : ℝ) {B : Type} (l : B → HalfNatural) : ℝ :=
  ∏ᶠ b, (weightCharCoeff β (l b)).re
include hv
omit [Finite B] in
theorem weightCharCoeff_eq_ofReal (l : HalfNatural) :
    weightCharCoeff β l = (((weightCharCoeff β l).re : ℝ) : ℂ) := by
  have h := (hv l).1
  rw [h, Complex.ofReal_re]
theorem charCoeffProd_eq_ofReal (l : B → HalfNatural) :
    charCoeffProd β l = ((charCoeffReal β l : ℝ) : ℂ) := by
  let _ := Fintype.ofFinite B
  simp only [charCoeffProd, charCoeffReal, finprod_eq_prod_of_fintype]
  push_cast
  exact Finset.prod_congr rfl fun b _ => weightCharCoeff_eq_ofReal hv _
theorem charCoeffReal_pos (l : B → HalfNatural) : 0 < charCoeffReal β l := by
  let _ := Fintype.ofFinite B
  simp only [charCoeffReal, finprod_eq_prod_of_fintype]
  exact Finset.prod_pos fun b _ => (hv _).2.1
theorem charCoeffReal_le_one (l : B → HalfNatural) : charCoeffReal β l ≤ 1 := by
  let _ := Fintype.ofFinite B
  simp only [charCoeffReal, finprod_eq_prod_of_fintype]
  exact Finset.prod_le_one (fun b _ => (hv _).2.1.le) fun b _ => (hv _).2.2.1
theorem sqrtCharCoeffProd_eq_sqrt (l : B → HalfNatural) :
    sqrtCharCoeffProd β l = Real.sqrt (charCoeffReal β l) := by
  rw [sqrtCharCoeffProd, charCoeffProd_eq_ofReal hv, Complex.ofReal_re]
theorem sqrtCharCoeffProd_pos (l : B → HalfNatural) : 0 < sqrtCharCoeffProd β l := by
  rw [sqrtCharCoeffProd_eq_sqrt hv]
  exact Real.sqrt_pos.mpr (charCoeffReal_pos hv l)
theorem sqrtCharCoeffProd_le_one (l : B → HalfNatural) : sqrtCharCoeffProd β l ≤ 1 := by
  rw [sqrtCharCoeffProd_eq_sqrt hv]
  exact Real.sqrt_le_one.mpr (charCoeffReal_le_one hv l)
theorem sqrtCharCoeffProd_mul_self (l : B → HalfNatural) :
    sqrtCharCoeffProd β l * sqrtCharCoeffProd β l = charCoeffReal β l := by
  rw [sqrtCharCoeffProd_eq_sqrt hv]
  exact Real.mul_self_sqrt (charCoeffReal_pos hv l).le
theorem sqrtCharCoeffProd_eq_finprod (l : B → HalfNatural) :
    sqrtCharCoeffProd β l = ∏ᶠ b, sqrtCharCoeff β (l b) := by
  let _ := Fintype.ofFinite B
  rw [sqrtCharCoeffProd_eq_sqrt hv]
  simp only [charCoeffReal, sqrtCharCoeff, finprod_eq_prod_of_fintype, Real.sqrt_eq_rpow]
  exact (Real.finsetProd_rpow _ _ (fun b _ => (hv _).2.1.le) _).symm
end Coefficients
section Series
variable {β : ℝ} (h₂ : SeveralVariablesFacts)
  (hv : ∀ l, WeightCharCoeffBounds β l) (hs : WeightCharCoeffSummable β)
  (he : BondWeightCharExpansion β)
variable {B : Type} [Finite B] [Nonempty B]
include hs in
theorem summable_rpow_mul_dim_pow (ς : ℝ) (hς : 0 < ς) (k : ℕ) :
    Summable fun l : HalfNatural => (weightCharCoeff β l).re ^ ς * (2 * l.toReal + 1) ^ k := by
  refine (hs k ς (Nat.cast_nonneg k) hς).congr fun l => ?_
  rw [Real.rpow_natCast, mul_comm]
include hs in
theorem summable_sqrtCharCoeff_mul :
    Summable fun l : HalfNatural => sqrtCharCoeff β l * (2 * l.toReal + 1) ^ 2 := by
  refine (summable_rpow_mul_dim_pow hs (1 / 2) one_half_pos 2).congr fun l => ?_
  rw [sqrtCharCoeff, Real.sqrt_eq_rpow]
include hv hs in
theorem summable_sqrtCharCoeffProd_mul :
    Summable fun l : B → HalfNatural => sqrtCharCoeffProd β l * spinDim l ^ 2 := by
  let _ := Fintype.ofFinite B
  refine (summable_pi_prod_of_nonneg
    (fun (_ : B) (l : HalfNatural) => sqrtCharCoeff β l * (2 * l.toReal + 1) ^ 2)
    (fun _ l => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
    fun _ => summable_sqrtCharCoeff_mul hs).congr fun l => ?_
  rw [sqrtCharCoeffProd_eq_finprod hv, ← finprod_sq_eq_spinDim_sq]
  simp only [finprod_eq_prod_of_fintype, Finset.prod_mul_distrib]
include hv hs in
theorem summable_charCoeffReal_mul :
    Summable fun l : B → HalfNatural => charCoeffReal β l * spinDim l ^ 2 := by
  let _ := Fintype.ofFinite B
  refine (summable_pi_prod_of_nonneg
    (fun (_ : B) (l : HalfNatural) => (weightCharCoeff β l).re ^ (1 : ℝ) * (2 * l.toReal + 1) ^ 2)
    ?_ fun _ => summable_rpow_mul_dim_pow hs 1 one_pos 2).congr fun l => ?_
  · exact fun _ l => mul_nonneg (Real.rpow_nonneg (hv l).2.1.le _) (sq_nonneg _)
  · rw [← finprod_sq_eq_spinDim_sq]
    simp only [charCoeffReal, finprod_eq_prod_of_fintype, Finset.prod_mul_distrib,
      Real.rpow_one]
include h₂ hv hs in
theorem hasSum_sqrtLinkKernel (u u' : B → specialUnitary) :
    HasSum (fun l : B → HalfNatural => (sqrtCharCoeffProd β l : ℂ) * isotypicKernel l u u')
      (sqrtLinkKernel β u u') := by
  let _ := Fintype.ofFinite B
  let f : B → HalfNatural → ℂ := fun b l =>
    (sqrtCharCoeff β l : ℂ) * ((2 * l.toReal + 1 : ℝ) : ℂ) * spinCharacter l (u b * (u' b)⁻¹)
  have hsum : ∀ b, Summable fun l => ‖f b l‖ := fun b => by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_)
      (summable_sqrtCharCoeff_mul hs)
    have h := norm_dim_mul_spinCharacter_le h₂ l (u b * (u' b)⁻¹)
    have hr : 0 ≤ sqrtCharCoeff β l := Real.sqrt_nonneg _
    simp only [f]
    rw [mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left h hr
  have h := hasSum_pi_prod f hsum
  have e₁ : (fun l : B → HalfNatural => ∏ b, f b (l b)) =
      fun l => (sqrtCharCoeffProd β l : ℂ) * isotypicKernel l u u' := by
    funext l
    rw [sqrtCharCoeffProd_eq_finprod hv, isotypicKernel]
    simp only [finprod_eq_prod_of_fintype, Complex.ofReal_prod, ← Finset.prod_mul_distrib, f,
      mul_assoc]
  have e₂ : sqrtLinkKernel β u u' = ∏ b, ∑' l, f b l := by
    simp only [sqrtLinkKernel, finprod_eq_prod_of_fintype]
    rfl
  rw [e₂, ← e₁]
  exact h
include hv he in
theorem hasSum_linkProductKernel (u u' : B → specialUnitary) :
    HasSum (fun l : B → HalfNatural => charCoeffProd β l * isotypicKernel l u u')
      (linkProductKernel β u u') := by
  let _ := Fintype.ofFinite B
  let f : B → HalfNatural → ℂ := fun b l => bondWeightCharTerm β l (u b * (u' b)⁻¹)
  have hsum : ∀ b, Summable fun l => ‖f b l‖ := fun b => he.1 _
  have h := hasSum_pi_prod f hsum
  have e₀ : ∀ g : specialUnitary, ∑' l, bondWeightCharTerm β l g =
      InfiniteLattice.singleBondWeight β g := fun g => by
    have h₁ : HasSum (fun l => bondWeightCharTerm β l g) (InfiniteLattice.singleBondWeight β g) :=
      he.2.tendsto_at g
    exact h₁.tsum_eq
  have e₁ : (fun l : B → HalfNatural => ∏ b, f b (l b)) =
      fun l => charCoeffProd β l * isotypicKernel l u u' := by
    funext l
    simp only [charCoeffProd, isotypicKernel, finprod_eq_prod_of_fintype,
      ← Finset.prod_mul_distrib, f, bondWeightCharTerm]
    exact Finset.prod_congr rfl fun b _ => by ring
  have e₂ : linkProductKernel β u u' = ∏ b, ∑' l, f b l := by
    simp only [linkProductKernel, finprod_eq_prod_of_fintype, f, e₀]
  rw [e₂, ← e₁]
  exact h
include h₂ hv hs in
theorem sqrtLinkKernel_expansion : HasAbsUniformSum
    (fun (l : B → HalfNatural) (p : KernelPoints B) =>
      (sqrtCharCoeffProd β l : ℂ) * isotypicKernel l p.1 p.2)
    (fun p => sqrtLinkKernel β p.1 p.2) := by
  refine hasAbsUniformSum_of_dominated _ _ _ (summable_sqrtCharCoeffProd_mul hv hs)
    (fun l p => ?_) fun p => hasSum_sqrtLinkKernel h₂ hv hs p.1 p.2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sqrtCharCoeffProd_pos hv l)]
  exact mul_le_mul_of_nonneg_left (norm_isotypicKernel_le h₂ l p.1 p.2)
    (sqrtCharCoeffProd_pos hv l).le
include h₂ hv hs he in
theorem linkProductKernel_expansion : HasAbsUniformSum
    (fun (l : B → HalfNatural) (p : KernelPoints B) =>
      ((charCoeffReal β l : ℝ) : ℂ) * isotypicKernel l p.1 p.2)
    (fun p => linkProductKernel β p.1 p.2) := by
  refine hasAbsUniformSum_of_dominated _ _ _ (summable_charCoeffReal_mul hv hs) (fun l p => ?_)
    fun p => ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (charCoeffReal_pos hv l)]
    exact mul_le_mul_of_nonneg_left (norm_isotypicKernel_le h₂ l p.1 p.2)
      (charCoeffReal_pos hv l).le
  · have h := hasSum_linkProductKernel hv he p.1 p.2
    simpa only [charCoeffProd_eq_ofReal hv] using h
include hv hs in
theorem summable_over_labels (ς : ℝ) (hς : 0 < ς) :
    Summable fun e : PeterWeylLabel =>
      (weightCharCoeff β e.spin).re ^ ς * (2 * e.spin.toReal + 1) ^ 2 := by
  let E : (Σ l : HalfNatural, Fin (l.doubled + 1) × Fin (l.doubled + 1)) ≃ PeterWeylLabel :=
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2⟩
      invFun := fun e => ⟨e.spin, e.rowIdx, e.colIdx⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← E.summable_iff]
  have hn : ∀ l : HalfNatural, 0 ≤ (weightCharCoeff β l).re ^ ς * (2 * l.toReal + 1) ^ 2 :=
    fun l => mul_nonneg (Real.rpow_nonneg (hv l).2.1.le _) (sq_nonneg _)
  refine (summable_sigma_of_nonneg fun x => hn x.1).mpr ⟨fun l => (hasSum_fintype _).summable, ?_⟩
  refine (summable_rpow_mul_dim_pow hs ς hς 4).congr fun l => ?_
  have e : ((l.doubled : ℝ) + 1) = 2 * l.toReal + 1 := by
    simp only [HalfNatural.toReal]
    ring
  simp only [tsum_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [e]
  ring
include hv hs in
theorem summable_over_indices (ς : ℝ) (hς : 0 < ς) :
    Summable fun α : PeterWeylIndex B =>
      charCoeffReal β (spins α) ^ ς * spinDim (spins α) ^ 2 := by
  let _ := Fintype.ofFinite B
  refine (summable_pi_prod_of_nonneg
    (fun (_ : B) (e : PeterWeylLabel) =>
      (weightCharCoeff β e.spin).re ^ ς * (2 * e.spin.toReal + 1) ^ 2)
    (fun _ e => mul_nonneg (Real.rpow_nonneg (hv _).2.1.le _) (sq_nonneg _))
    fun _ => summable_over_labels hv hs ς hς).congr fun α => ?_
  rw [← finprod_sq_eq_spinDim_sq]
  simp only [charCoeffReal, finprod_eq_prod_of_fintype, Finset.prod_mul_distrib, spins]
  rw [Real.finsetProd_rpow _ _ fun b _ => (hv _).2.1.le]
include hv in
theorem peterWeylCoeff_re (α : PeterWeylIndex B) :
    (peterWeylCoeff β α).re = charCoeffReal β (spins α) := by
  rw [peterWeylCoeff, charCoeffProd_eq_ofReal hv, Complex.ofReal_re]
include h₂ in
theorem norm_peterWeylFn_le (α : PeterWeylIndex B) :
    ‖peterWeylFn α‖ ≤ spinDim (spins α) :=
  (ContinuousMap.norm_le _ (zero_le_one.trans (one_le_spinDim _))).mpr
    (norm_peterWeylFn_apply_le h₂ α)
include h₂ hv hs in
theorem peterWeylBounds : PeterWeylBounds β B := by
  refine ⟨norm_peterWeylFn_le h₂, fun ς hς => ?_⟩
  refine Summable.of_nonneg_of_le (fun α => ?_) (fun α => ?_) (summable_over_indices hv hs ς hς)
  · rw [peterWeylCoeff_re hv]
    exact mul_nonneg (Real.rpow_nonneg (charCoeffReal_pos hv _).le _) (sq_nonneg _)
  · rw [peterWeylCoeff_re hv]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_peterWeylFn_le h₂ α) 2)
      (Real.rpow_nonneg (charCoeffReal_pos hv _).le _)
include h₂ hv hs in
theorem sqrtLinkKernel_peterWeyl_expansion : HasAbsUniformSum
    (fun (α : PeterWeylIndex B) (p : KernelPoints B) =>
      (sqrtPeterWeylCoeff β α : ℂ) * peterWeylFn α p.1 * star (peterWeylFn α p.2))
    (fun p => sqrtLinkKernel β p.1 p.2) := by
  have hM := (peterWeylBounds h₂ hv hs (B := B)).2 (1 / 2) one_half_pos
  have hb : ∀ (α : PeterWeylIndex B) (p : KernelPoints B),
      ‖(sqrtPeterWeylCoeff β α : ℂ) * peterWeylFn α p.1 * star (peterWeylFn α p.2)‖ ≤
        (peterWeylCoeff β α).re ^ (1 / 2 : ℝ) * ‖peterWeylFn α‖ ^ 2 := fun α p => by
    have hr : 0 ≤ sqrtPeterWeylCoeff β α := Real.sqrt_nonneg _
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
      ← Real.sqrt_eq_rpow, mul_assoc, sq]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul ((peterWeylFn α).norm_coe_le_norm _) ((peterWeylFn α).norm_coe_le_norm _)
        (norm_nonneg _) (norm_nonneg _)) hr
  refine hasAbsUniformSum_of_dominated _ _ _ hM hb fun p => ?_
  have hg : Summable fun α : PeterWeylIndex B =>
      (sqrtPeterWeylCoeff β α : ℂ) * peterWeylFn α p.1 * star (peterWeylFn α p.2) :=
    Summable.of_norm_bounded hM fun α => hb α p
  have hf := hg.hasSum.tsum_fiberwise (spins : PeterWeylIndex B → B → HalfNatural)
  have e : ∀ l : B → HalfNatural, ∑' α : (spins ⁻¹' {l} : Set (PeterWeylIndex B)),
      (sqrtPeterWeylCoeff β α.1 : ℂ) * peterWeylFn α.1 p.1 * star (peterWeylFn α.1 p.2) =
      (sqrtCharCoeffProd β l : ℂ) * isotypicKernel l p.1 p.2 := fun l => by
    have hset : (spins ⁻¹' {l} : Set (PeterWeylIndex B)) = ↑(indicesWithSpins l) := by
      ext α
      simp [indicesWithSpins]
    rw [tsum_congr_set_coe (fun α : PeterWeylIndex B =>
      (sqrtPeterWeylCoeff β α : ℂ) * peterWeylFn α p.1 * star (peterWeylFn α p.2)) hset,
      Finset.tsum_subtype' (indicesWithSpins l) fun α : PeterWeylIndex B =>
      (sqrtPeterWeylCoeff β α : ℂ) * peterWeylFn α p.1 * star (peterWeylFn α p.2),
      isotypicKernel_eq_sum h₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    have hα' : spins α = l := (Set.Finite.mem_toFinset (finite_indicesWithSpins l)).mp hα
    rw [mul_assoc]
    congr 2
    simp only [sqrtPeterWeylCoeff, sqrtCharCoeffProd, peterWeylCoeff, hα']
  simp only [e] at hf
  have hu := hf.unique (hasSum_sqrtLinkKernel h₂ hv hs p.1 p.2)
  rw [← hu]
  exact hg.hasSum
end Series
section Operators
variable {B : Type} [Finite B] [Nonempty B]
  (hK : ∀ A : KernelPoints B → ℂ, Continuous A → ContinuousKernelOperatorProps B A)
  (h₂ : SeveralVariablesFacts)
variable {w : (B → HalfNatural) → ℝ} {K : KernelPoints B → ℂ}
  (hser : HasAbsUniformSum
    (fun (l : B → HalfNatural) (p : KernelPoints B) => (w l : ℂ) * isotypicKernel l p.1 p.2) K)
include h₂ hser
theorem continuous_of_expansion : Continuous K :=
  hser.2.continuous (Frequently.of_forall fun _ => continuous_finsetSum _ fun l _ =>
    continuous_const.mul (continuous_isotypicKernel h₂ l))
omit h₂ in
theorem hasSum_of_expansion (z : KernelPoints B) :
    HasSum (fun l : B → HalfNatural => (w l : ℂ) * isotypicKernel l z.1 z.2) (K z) :=
  hser.2.tendsto_at z
theorem im_of_expansion (z : KernelPoints B) : (K z).im = 0 := by
  have h := Complex.imCLM.hasSum (hasSum_of_expansion hser z)
  have e : ∀ l : B → HalfNatural, Complex.imCLM ((w l : ℂ) * isotypicKernel l z.1 z.2) = 0 :=
    fun l => by simp [isotypicKernel_im h₂]
  simp only [e] at h
  exact h.unique hasSum_zero
theorem comm_of_expansion (u u' : B → specialUnitary) : K (u, u') = K (u', u) := by
  have h := hasSum_of_expansion hser (u, u')
  simp only [isotypicKernel_comm h₂ _ u u'] at h
  exact h.unique (hasSum_of_expansion hser (u', u))
include hK
theorem hasSum_kernelOp_of_expansion :
    HasSum (fun l : B → HalfNatural => (w l : ℂ) • isotypicProj l)
      (kernelOp (haarPi B) K) := by
  have h := hasSum_kernelOp hK _ K
    (fun l => continuous_const.mul (continuous_isotypicKernel h₂ l))
    (continuous_of_expansion h₂ hser) hser
  convert h using 2 with l
  exact (kernelOp_const_mul hK _ _ (continuous_isotypicKernel h₂ l)).symm
theorem hasSum_apply_of_expansion (F : HaarL2 B) :
    HasSum (fun l : B → HalfNatural => (w l : ℂ) • isotypicProj l F)
      (kernelOp (haarPi B) K F) :=
  hasSum_smul_apply_of_hasSum (hasSum_kernelOp_of_expansion hK h₂ hser) F
theorem isRealSymmPosContraction_of_expansion (hw₀ : ∀ l, 0 ≤ w l) (hw₁ : ∀ l, w l ≤ 1) :
    IsRealSymmPosContraction B (kernelOp (haarPi B) K) := by
  have hc := continuous_of_expansion h₂ hser
  have hstrong := hasSum_apply_of_expansion hK h₂ hser
  have hP := isotypicProj_resolution h₂ (J := B)
  have hS := (hK K hc).2.2.2.2 (im_of_expansion h₂ hser) (comm_of_expansion h₂ hser)
  have h₁ : IsPositiveOp (kernelOp (haarPi B) K) := by
    refine ⟨hS, fun φ => ?_⟩
    have h := hP.hasSum_inner_map hstrong φ
    exact ⟨h.1.nonneg fun l => mul_nonneg (hw₀ l) (sq_nonneg _), h.2.unique hasSum_zero⟩
  have h₂' : ‖kernelOp (haarPi B) K‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun F => ?_
    rw [one_mul]
    exact hP.norm_map_le hstrong (fun l => by rw [abs_of_nonneg (hw₀ l)]; exact hw₁ l) F
  refine ⟨(hK K hc).2.2.2.1 (im_of_expansion h₂ hser), hS, h₁, h₂', fun l => ?_⟩
  ext1 F
  exact (hP.map_proj hstrong l F).trans (hP.proj_map hstrong l F).symm
end Operators
section Truncated
variable {ι : Type*} {J : Type} [Countable J]
theorem isRealPreserving_sum (s : Finset ι) (v : ι → ℝ)
    (P : ι → HaarL2 J →L[ℂ] HaarL2 J) (hP : ∀ i, IsRealPreserving (P i)) :
    IsRealPreserving (∑ i ∈ s, (v i : ℂ) • P i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro φ _
    filter_upwards [Lp.coeFn_zero ℂ 2 (haarPi J)] with u hu
    simp
  | insert i s hi ih =>
    intro φ hφ
    rw [Finset.sum_insert hi]
    filter_upwards [hP i φ hφ, ih φ hφ,
      Lp.coeFn_add (((v i : ℂ) • P i) φ) ((∑ i ∈ s, (v i : ℂ) • P i) φ),
      Lp.coeFn_smul (v i : ℂ) (P i φ)] with u a b c d
    rw [add_apply, c, Pi.add_apply, smul_apply, d, Pi.smul_apply, Complex.add_im, smul_eq_mul,
      Complex.mul_im, a, b]
    simp
end Truncated
section Requirements
variable {β : ℝ} (h₂ : SeveralVariablesFacts)
  (hv : ∀ l, WeightCharCoeffBounds β l) (hs : WeightCharCoeffSummable β)
  (he : BondWeightCharExpansion β)
variable {B : Type} [Finite B] [Nonempty B]
  (hK : ∀ A : KernelPoints B → ℂ, Continuous A → ContinuousKernelOperatorProps B A)
include h₂ hv hs in
theorem sqrtLinkOperator_hasSum (F : HaarL2 B)
    (hK : ∀ A : KernelPoints B → ℂ, Continuous A → ContinuousKernelOperatorProps B A) :
    HasSum (fun l : B → HalfNatural => (sqrtCharCoeffProd β l : ℂ) • isotypicProj l F)
      (sqrtLinkOperator β B F) :=
  hasSum_apply_of_expansion hK h₂ (sqrtLinkKernel_expansion h₂ hv hs) F
include h₂ hv hs he in
theorem linkProductOperator_hasSum (F : HaarL2 B)
    (hK : ∀ A : KernelPoints B → ℂ, Continuous A → ContinuousKernelOperatorProps B A) :
    HasSum (fun l : B → HalfNatural => ((charCoeffReal β l : ℝ) : ℂ) • isotypicProj l F)
      (linkProductOperator β B F) :=
  hasSum_apply_of_expansion hK h₂ (linkProductKernel_expansion h₂ hv hs he) F
include h₂ hv hs he hK
theorem sqrtLinkOperator_mul_self :
    sqrtLinkOperator β B * sqrtLinkOperator β B = linkProductOperator β B := by
  ext1 F
  have h := (isotypicProj_resolution h₂ (J := B)).hasSum_comp
    (fun F => sqrtLinkOperator_hasSum h₂ hv hs F hK)
    (fun F => sqrtLinkOperator_hasSum h₂ hv hs F hK) F
  simp only [sqrtCharCoeffProd_mul_self hv] at h
  exact h.unique (linkProductOperator_hasSum h₂ hv hs he F hK)
theorem isotypicEigenvalues : IsotypicEigenvalues β B := by
  intro l ψ hψ
  have hm : toHaarL2 ψ ∈ prodCoeffSpanL2 l :=
    Submodule.mem_map_of_mem hψ
  have hfix := isotypicProj_of_mem h₂ l _ hm
  have hP := isotypicProj_resolution h₂ (J := B)
  constructor
  · have h := hP.map_proj (fun F => sqrtLinkOperator_hasSum h₂ hv hs F hK) l (toHaarL2 ψ)
    simp only [hfix] at h
    exact h
  · have h := hP.map_proj (fun F => linkProductOperator_hasSum h₂ hv hs he F hK) l (toHaarL2 ψ)
    simp only [hfix] at h
    rw [charCoeffProd_eq_ofReal hv]
    exact h
theorem strongExpansions : StrongExpansions β B := fun F => by
  refine ⟨sqrtLinkOperator_hasSum h₂ hv hs F hK, ?_⟩
  simp only [charCoeffProd_eq_ofReal hv]
  exact linkProductOperator_hasSum h₂ hv hs he F hK
theorem sqrtSquared
    (hU : ContinuousKernelCompAndUniqueness B) : SqrtSquared β B := by
  refine ⟨sqrtLinkOperator_mul_self h₂ hv hs he hK, fun u u' => ?_⟩
  have hr := continuous_of_expansion h₂ (sqrtLinkKernel_expansion h₂ hv hs (B := B))
  have hb := continuous_of_expansion h₂ (linkProductKernel_expansion h₂ hv hs he (B := B))
  have h₁ := hU.1 _ _ hr hr
  have h₃ := hU.2 _ _ h₁.1 hb (h₁.2.symm.trans (sqrtLinkOperator_mul_self h₂ hv hs he hK))
  exact congrFun h₃ (u, u')
theorem hilbertSchmidtAndTraceClass : HilbertSchmidtAndTraceClass β B := by
  have hHS : IsHilbertSchmidtPW (sqrtLinkOperator β B) := by
    have hnorm : ∀ α : PeterWeylIndex B, ‖peterWeylVec α‖ = 1 :=
      fun α => (h₂ B (spins α) ⟨0⟩).1.1.1 α
    have hmem : ∀ α : PeterWeylIndex B, peterWeylFn α ∈ prodCoeffSpan (spins α) :=
      fun α => by
        rw [← (h₂ B (spins α) ⟨0⟩).1.2.2.1]
        exact Submodule.subset_span ⟨α, rfl, rfl⟩
    have heig : ∀ α : PeterWeylIndex B, ‖sqrtLinkOperator β B (peterWeylVec α)‖ ^ 2 =
        charCoeffReal β (spins α) := fun α => by
      have h := (isotypicEigenvalues h₂ hv hs he hK _ _ (hmem α)).1
      have h' : sqrtLinkOperator β B (peterWeylVec α) =
          (sqrtCharCoeffProd β (spins α) : ℂ) • peterWeylVec α := h
      rw [h', norm_smul, hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq,
        sqrtCharCoeffProd_mul_self hv]
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun α => ?_)
      (summable_over_indices hv hs (B := B) 1 one_pos)
    rw [heig, Real.rpow_one]
    exact le_mul_of_one_le_right (charCoeffReal_pos hv _).le
      (one_le_pow₀ (one_le_spinDim _))
  exact ⟨hHS, _, _, hHS, hHS, (sqrtLinkOperator_mul_self h₂ hv hs he hK).symm⟩
theorem truncInvSqrtProps : TruncInvSqrtProps β B := by
  intro ϰ
  have hP := isotypicProj_resolution h₂ (J := B)
  have hroot := fun F => sqrtLinkOperator_hasSum h₂ hv hs (B := B) F hK
  have hvr : ∀ l : B → HalfNatural, (invSqrtCharCoeffProd β l : ℂ) *
      (sqrtCharCoeffProd β l : ℂ) = 1 := fun l => by
    rw [invSqrtCharCoeffProd, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (sqrtCharCoeffProd_pos hv l).ne']
    simp
  have hcomm : ∀ (l l' : B → HalfNatural) (F : HaarL2 B),
      isotypicProj l (isotypicProj l' F) =
        isotypicProj l' (isotypicProj l F) := fun l l' F => by
    by_cases h : l = l'
    · rw [h]
    · rw [hP.orth l l' h, hP.orth l' l (Ne.symm h)]
  refine ⟨?_, ?_, fun l' => ?_, ?_, ?_⟩
  · exact isRealPreserving_sum _ _ _ fun l =>
      (hK _ (continuous_isotypicKernel h₂ l)).2.2.2.1 fun z => isotypicKernel_im h₂ l z.1 z.2
  · intro φ ψ
    simp only [truncInvSqrtLinkOperator, sum_apply, smul_apply, inner_sum, sum_inner,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal, isotypicProj_inner_symm h₂]
  · ext1 F
    simp only [truncInvSqrtLinkOperator, mul_apply_eq_comp, sum_apply, smul_apply,
      map_sum, map_smul]
    exact Finset.sum_congr rfl fun l _ => by rw [hcomm]
  · ext1 F
    simp only [truncInvSqrtLinkOperator, truncationProj, mul_apply_eq_comp,
      sum_apply, smul_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hP.map_proj hroot l F, smul_smul, hvr, one_smul]
  · ext1 F
    simp only [truncInvSqrtLinkOperator, truncationProj, mul_apply_eq_comp,
      sum_apply, smul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hP.proj_map hroot l F, smul_smul, hvr, one_smul]
end Requirements
section OneElement
variable (J : Type) [Unique J]
theorem liftToUnique_kernelOp (k : specialUnitary × specialUnitary → ℂ)
    (hK : ContinuousKernelOperatorProps J fun p => k (p.1 default, p.2 default)) :
    liftToUnique J (kernelOp haarProb k) =
      kernelOp (haarPi J) fun p => k (p.1 default, p.2 default) := by
  have he := measurePreserving_funUnique_haar J
  set e := MeasurableEquiv.funUnique J specialUnitary with hedef
  set K : KernelPoints J → ℂ := fun p => k (p.1 default, p.2 default) with hKdef
  set U : Lp ℂ 2 haarProb →L[ℂ] HaarL2 J :=
    (Lp.compMeasurePreservingₗᵢ ℂ _ he).toContinuousLinearMap with hUdef
  set V : HaarL2 J →L[ℂ] Lp ℂ 2 haarProb :=
    (Lp.compMeasurePreservingₗᵢ ℂ _ he.symm).toContinuousLinearMap with hVdef
  set T := kernelOp (haarPi J) K with hTdef
  have hU : ∀ ψ : Lp ℂ 2 haarProb, U ψ =ᵐ[haarPi J] ψ ∘ e :=
    fun ψ => Lp.coeFn_compMeasurePreserving ψ he
  have hV : ∀ φ : HaarL2 J, V φ =ᵐ[haarProb] φ ∘ e.symm :=
    fun φ => Lp.coeFn_compMeasurePreserving φ he.symm
  have hee : ∀ g, (e.symm g) default = g := fun g => e.apply_symm_apply g
  have hint : HasKernel haarProb k (V ∘L T ∘L U) := fun ψ => by
    have h₁ := hV (T (U ψ))
    have h₂ := he.symm.quasiMeasurePreserving.ae_eq_comp (hK.2.1 (U ψ))
    refine h₁.trans (h₂.trans (ae_of_all _ fun g => ?_))
    simp only [Function.comp, kernelApply]
    have h₃ : ∀ᵐ w ∂haarPi J, K (e.symm g, w) * (U ψ) w =
        (fun h => k (g, h) * ψ h) (e w) := by
      filter_upwards [hU ψ] with w hw
      rw [hw]
      simp only [hKdef, hee, Function.comp]
      rfl
    rw [integral_congr_ae h₃]
    exact he.integral_comp' fun h => k (g, h) * ψ h
  have hspec : HasKernel haarProb k (kernelOp haarProb k) :=
    Classical.epsilon_spec (p := HasKernel haarProb k) ⟨_, hint⟩
  have heq : kernelOp haarProb k = V ∘L T ∘L U := by
    ext1 ψ
    exact Lp.ext ((hspec ψ).trans (hint ψ).symm)
  have hUV : ∀ φ : HaarL2 J, U (V φ) = φ := fun φ =>
    Lp.ext ((hU (V φ)).trans ((he.quasiMeasurePreserving.ae_eq_comp (hV φ)).trans
      (ae_of_all _ fun u => by simp)))
  ext1 φ
  rw [heq]
  show U (V (T (U (V φ)))) = T φ
  rw [hUV, hUV]
theorem sqrtLinkKernel_of_unique (β : ℝ) (u u' : J → specialUnitary) :
    sqrtLinkKernel β u u' = sqrtKernel β (u default) (u' default) := by
  simp only [sqrtLinkKernel, finprod_unique]
theorem linkProductKernel_of_unique (β : ℝ) (u u' : J → specialUnitary) :
    linkProductKernel β u u' = InfiniteLattice.singleBondWeight β (u default * (u' default)⁻¹) := by
  simp only [linkProductKernel, finprod_unique]
end OneElement
theorem sqrtLinkKernelFacts_holds (h₁ : BondWeightCharCoeffStatement)
    (h₂ : SeveralVariablesFacts)
    (h₃ : GibbsHaarKernels.Statement) :
    SqrtLinkKernelFacts := by
  intro β hβ
  obtain ⟨-, hv, -, hs, he⟩ := h₁.2 β hβ
  have hK := fun (B : Type) [Finite B] [Nonempty B] => (h₃.2.2.2 B).1
  have hU := fun (B : Type) [Finite B] [Nonempty B] => (h₃.2.2.2 B).2
  have hroot := fun (B : Type) [Finite B] [Nonempty B] =>
    sqrtLinkKernel_expansion h₂ hv hs (B := B)
  have hbond := fun (B : Type) [Finite B] [Nonempty B] =>
    linkProductKernel_expansion h₂ hv hs he (B := B)
  refine ⟨fun B _ _ => ?_, ?_, fun J _ => ?_⟩
  · refine ⟨⟨fun u u' => im_of_expansion h₂ (hroot B) (u, u'), comm_of_expansion h₂ (hroot B),
      continuous_of_expansion h₂ (hroot B)⟩, ⟨hroot B, sqrtLinkKernel_peterWeyl_expansion h₂ hv hs, ?_⟩,
      peterWeylBounds h₂ hv hs, isotypicEigenvalues h₂ hv hs he (hK B),
      strongExpansions h₂ hv hs he (hK B),
      isRealSymmPosContraction_of_expansion (hK B) h₂ (hroot B)
        (fun l => (sqrtCharCoeffProd_pos hv l).le) (sqrtCharCoeffProd_le_one hv),
      isRealSymmPosContraction_of_expansion (hK B) h₂ (hbond B)
        (fun l => (charCoeffReal_pos hv l).le) (charCoeffReal_le_one hv),
      sqrtSquared h₂ hv hs he (hK B) (hU B), hilbertSchmidtAndTraceClass h₂ hv hs he (hK B),
      truncInvSqrtProps h₂ hv hs he (hK B)⟩
    simp only [charCoeffProd_eq_ofReal hv]
    exact hbond B
  · intro g g'
    have h := (sqrtSquared h₂ hv hs he (hK Unit) (hU Unit)).2 (fun _ => g) (fun _ => g')
    rw [← (measurePreserving_funUnique_haar Unit).integral_comp'
      (fun h => sqrtKernel β g h * sqrtKernel β h g')]
    simp only [sqrtLinkKernel_of_unique, linkProductKernel_of_unique] at h
    exact h
  · have er : sqrtOperator β = kernelOp haarProb fun p => sqrtKernel β p.1 p.2 := rfl
    have eb : singleLinkOperator β =
        kernelOp haarProb fun p => InfiniteLattice.singleBondWeight β (p.1 * p.2⁻¹) := rfl
    have hr : sqrtLinkOperator β J = liftToUnique J (sqrtOperator β) := by
      have hc := continuous_of_expansion h₂ (hroot J)
      have ek : (fun p : KernelPoints J => sqrtLinkKernel β p.1 p.2) =
          fun p => sqrtKernel β (p.1 default) (p.2 default) :=
        funext fun p => sqrtLinkKernel_of_unique J β p.1 p.2
      rw [er, liftToUnique_kernelOp J _ (ek ▸ hK J _ hc), sqrtLinkOperator, ek]
    have hb : linkProductOperator β J = liftToUnique J (singleLinkOperator β) := by
      have hc := continuous_of_expansion h₂ (hbond J)
      have ek : (fun p : KernelPoints J => linkProductKernel β p.1 p.2) =
          fun p => InfiniteLattice.singleBondWeight β (p.1 default * (p.2 default)⁻¹) :=
        funext fun p => linkProductKernel_of_unique J β p.1 p.2
      rw [eb, liftToUnique_kernelOp J _ (ek ▸ hK J _ hc), linkProductOperator, ek]
    rw [← hr, ← hb]
    exact hilbertSchmidtAndTraceClass h₂ hv hs he (hK J)
end YangMills.Construction.TransferOperators.SqrtLinkFacts
end

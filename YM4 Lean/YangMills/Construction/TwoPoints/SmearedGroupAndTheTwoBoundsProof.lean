import YangMills.Construction.Splines.CubicSplineBasicFactsProofs
import YangMills.Construction.HilbertSpace.BoundedSesqFormRepresentation
import YangMills.Construction.HilbertSpace.IteratedCauchySchwarz
import YangMills.Construction.SpectralCalculus.FormCompletionAndBoundedExtension
import YangMills.Construction.TwoPoints.SmearedGroupAndTheTwoBounds
import YangMills.Construction.TwoPoints.TransformsConvolutionPowersAndDensity
import Mathlib
set_option autoImplicit false
open Filter Topology MeasureTheory
open scoped NNReal ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.TwoPoints.LineTransforms
open YangMills.Construction.SpectralCalculus (IsCommutingSemigroupGroup
  IsSelfAdjointContractionSemigroup IsPositiveBounded IsSymmetricBounded
  IsStronglyContinuousUnitaryGroup)
namespace SmearedPairBoundsProof
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ≥0 → H →L[ℂ] H} {U : ℝ → H →L[ℂ] H}
theorem inner_unitary_apply_apply (hU : IsStronglyContinuousUnitaryGroup U) (s : ℝ) (u v : H) :
    inner ℂ (U s u) (U s v) = inner ℂ u v :=
  (LinearMap.norm_map_iff_inner_map_map (U s)).mp (hU.isUnitaryBounded s).2 u v
theorem unitary_apply_neg_apply (hU : IsStronglyContinuousUnitaryGroup U) (s : ℝ) (v : H) :
    U s (U (-s) v) = v := by
  have h := hU.map_add s (-s)
  rw [add_neg_cancel, hU.map_zero] at h
  exact congrArg (fun B : H →L[ℂ] H => B v) h
theorem inner_unitary_left (hU : IsStronglyContinuousUnitaryGroup U) (u v : H) (s : ℝ) :
    inner ℂ (U s u) v = inner ℂ u (U (-s) v) := by
  conv_lhs => rw [← unitary_apply_neg_apply hU s v]
  exact inner_unitary_apply_apply hU s u _
theorem continuous_unitary_orbit (hU : IsStronglyContinuousUnitaryGroup U) (v : H) :
    Continuous fun s => U s v := by
  have h0 : ContinuousAt (fun s => U s v) 0 := by
    rw [continuousAt_iff_punctured_nhds]
    simpa [hU.map_zero] using hU.tendsto v
  rw [continuous_iff_continuousAt]
  intro s
  have h1 : ContinuousAt (fun s' => U (s' - s) v) s := by
    have hc : ContinuousAt (fun s' : ℝ => s' - s) s :=
      (continuous_id.sub continuous_const).continuousAt
    refine ContinuousAt.comp (f := fun s' : ℝ => s' - s) (g := fun s => U s v) ?_ hc
    simpa using h0
  have h2 : (fun s' => U s' v) = fun s' => U s (U (s' - s) v) := by
    funext s'
    have h3 := congrArg (fun B : H →L[ℂ] H => B v) (hU.map_add s (s' - s))
    simpa using h3.symm
  rw [h2]
  exact (U s).continuous.continuousAt.comp h1
theorem continuous_semigroup_orbit (hT : IsSelfAdjointContractionSemigroup T) (v : H) :
    Continuous fun t => T t v := by
  have h0 : Tendsto (fun t => T t v) (𝓝 0) (𝓝 v) := by
    have h : ContinuousAt (fun t => T t v) 0 := by
      rw [continuousAt_iff_punctured_nhds]
      have hset : ({0}ᶜ : Set ℝ≥0) = Set.Ioi 0 := by
        ext x
        simp [pos_iff_ne_zero]
      rw [hset]
      simpa [hT.map_zero] using hT.tendsto v
    simpa [ContinuousAt, hT.map_zero] using h
  have hle : ∀ (B : H →L[ℂ] H), ‖B‖ ≤ 1 → ∀ w : H, ‖B w‖ ≤ ‖w‖ := fun B hB w => by
    simpa using B.le_of_opNorm_le hB w
  have key : ∀ t t₀ : ℝ≥0, ‖T t v - T t₀ v‖ ≤ ‖T ((t - t₀) + (t₀ - t)) v - v‖ := by
    intro t t₀
    rcases le_total t₀ t with h | h
    · have e : T t = T t₀ * T (t - t₀) := by rw [hT.map_add, add_tsub_cancel_of_le h]
      have e' : T t v - T t₀ v = T t₀ (T (t - t₀) v - v) := by
        rw [e]
        simp [map_sub]
      rw [e', tsub_eq_zero_of_le h, add_zero]
      exact hle _ (hT.isContractive t₀) _
    · have e : T t₀ = T t * T (t₀ - t) := by rw [hT.map_add, add_tsub_cancel_of_le h]
      have e' : T t v - T t₀ v = -T t (T (t₀ - t) v - v) := by
        rw [e]
        simp [map_sub]
      rw [e', norm_neg, tsub_eq_zero_of_le h, zero_add]
      exact hle _ (hT.isContractive t) _
  rw [continuous_iff_continuousAt]
  intro t₀
  change Tendsto (fun t => T t v) (𝓝 t₀) (𝓝 (T t₀ v))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hr : Tendsto (fun t : ℝ≥0 => (t - t₀) + (t₀ - t)) (𝓝 t₀) (𝓝 0) := by
    have hc : Continuous fun t : ℝ≥0 => (t - t₀) + (t₀ - t) :=
      (continuous_id.sub continuous_const).add (continuous_const.sub continuous_id)
    simpa using hc.tendsto t₀
  have hz : Tendsto (fun t : ℝ≥0 => ‖T ((t - t₀) + (t₀ - t)) v - v‖) (𝓝 t₀) (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp h0).comp hr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun t => key t t₀) hz
theorem matrixCoeffsContinuous_of_pair (h : IsCommutingSemigroupGroup T U) :
    MatrixCoeffsContinuous T U where
  inner_group_left u v s := inner_unitary_left h.group u v s
  continuous_semigroup := continuous_semigroup_orbit h.semigroup
  continuous_group := continuous_unitary_orbit h.group
  continuous_inner u v := by
    have hT := h.semigroup
    have e : (fun p : ℝ≥0 × ℝ => inner ℂ u (T p.1 (U p.2 v))) =
        fun p : ℝ≥0 × ℝ => inner ℂ (T p.1 u) (U p.2 v) := by
      funext p
      exact (hT.isSymmetricBounded p.1 u _).symm
    rw [e]
    exact ((continuous_semigroup_orbit hT u).comp continuous_fst).inner
      ((continuous_unitary_orbit h.group v).comp continuous_snd)
  norm_inner_le u v t s := by
    have hT := h.semigroup
    have h1 : ‖T t (U s v)‖ ≤ ‖v‖ := by
      have h2 := (T t).le_of_opNorm_le (hT.isContractive t) (U s v)
      rw [one_mul, (h.group.isUnitaryBounded s).2] at h2
      exact h2
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
theorem contDiff_of_mem_c1 {g : ℝ → ℂ} (hg : g ∈ c1Functions) : ContDiff ℝ 1 g := hg.1
theorem continuous_of_mem_c1 {g : ℝ → ℂ} (hg : g ∈ c1Functions) : Continuous g :=
  (contDiff_of_mem_c1 hg).continuous
theorem hasCompactSupport_of_mem_c1 {g : ℝ → ℂ} (hg : g ∈ c1Functions) :
    HasCompactSupport g := hg.2.1
theorem lebesgueIntegral_eq (F : ℝ → ℂ) : lebesgueIntegral F = ∫ s, F s := rfl
theorem integrable_c1_mul {g φ : ℝ → ℂ} (hg : g ∈ c1Functions) (hφ : Continuous φ) :
    Integrable fun s => g s * φ s :=
  ((continuous_of_mem_c1 hg).mul hφ).integrable_of_hasCompactSupport
    (hasCompactSupport_of_mem_c1 hg).mul_right
theorem integrable_of_mem_c1 {g : ℝ → ℂ} (hg : g ∈ c1Functions) : Integrable g :=
  (continuous_of_mem_c1 hg).integrable_of_hasCompactSupport (hasCompactSupport_of_mem_c1 hg)
theorem l1Norm_eq_integral {g : ℝ → ℂ} (hg : g ∈ c1Functions) :
    l1Norm g = ∫ s, ‖g s‖ := by
  rw [integral_norm_eq_lintegral_enorm (continuous_of_mem_c1 hg).aestronglyMeasurable]
  rfl
theorem continuous_matrixCoeff (hU : IsStronglyContinuousUnitaryGroup U) (u v : H) :
    Continuous fun s => inner ℂ u (U s v) :=
  continuous_const.inner (continuous_unitary_orbit hU v)
theorem norm_matrixCoeff_le (hU : IsStronglyContinuousUnitaryGroup U) (u v : H) (s : ℝ) :
    ‖inner ℂ u (U s v)‖ ≤ ‖u‖ * ‖v‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) u (U s v)
  rwa [(hU.isUnitaryBounded s).2] at h
theorem exists_smearing
    (hR : HilbertSpace.BoundedSesqRep.Claim) (hU : IsStronglyContinuousUnitaryGroup U)
    {g : ℝ → ℂ} (hg : g ∈ c1Functions) :
    ∃ B : H →L[ℂ] H, IsSmearing U g B ∧
      (∀ B' : H →L[ℂ] H, IsSmearing U g B' → B' = B) ∧ ‖B‖ ≤ l1Norm g := by
  have hi : ∀ u v : H, Integrable fun s => g s * inner ℂ u (U s v) := fun u v =>
    integrable_c1_mul hg (continuous_matrixCoeff hU u v)
  have hn : 0 ≤ l1Norm g := ENNReal.toReal_nonneg
  obtain ⟨B, h1, h2, h3, -⟩ := hR H (l1Norm g)
    (fun u v => lebesgueIntegral fun s => g s * inner ℂ u (U s v)) hn
    { add_left := fun u₁ u₂ v => by
        simp only [lebesgueIntegral_eq, inner_add_left, mul_add]
        exact integral_add (hi u₁ v) (hi u₂ v)
      smul_left := fun a u v => by
        simp only [lebesgueIntegral_eq, inner_smul_left]
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun s => by
          simp only
          ring)
      add_right := fun u v₁ v₂ => by
        simp only [lebesgueIntegral_eq, map_add, inner_add_right, mul_add]
        exact integral_add (hi u v₁) (hi u v₂)
      smul_right := fun a u v => by
        simp only [lebesgueIntegral_eq, map_smul, inner_smul_right]
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun s => by
          simp only
          ring) }
    (fun u v => by
      have hb : Integrable fun s => ‖g s‖ * (‖u‖ * ‖v‖) :=
        (integrable_of_mem_c1 hg).norm.mul_const _
      have h := norm_integral_le_of_norm_le hb
        (f := fun s => g s * inner ℂ u (U s v)) (Eventually.of_forall fun s => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_matrixCoeff_le hU u v s) (norm_nonneg _))
      rw [integral_mul_const, ← l1Norm_eq_integral hg] at h
      rw [lebesgueIntegral_eq]
      linarith [h])
  exact ⟨B, h1, h2, h3⟩
section Smearing
variable (hR : HilbertSpace.BoundedSesqRep.Claim)
  (hU : IsStronglyContinuousUnitaryGroup U)
include hR hU
theorem isSmearing_smear {g : ℝ → ℂ} (hg : g ∈ c1Functions) :
    IsSmearing U g (smear U g) := by
  obtain ⟨B, h1, -, -⟩ := exists_smearing hR hU hg
  exact Classical.epsilon_spec (p := IsSmearing U g) ⟨B, h1⟩
theorem eq_smear_of_isSmearing {g : ℝ → ℂ} (hg : g ∈ c1Functions) {B : H →L[ℂ] H}
    (hB : IsSmearing U g B) : B = smear U g := by
  obtain ⟨B₀, -, h2, -⟩ := exists_smearing hR hU hg
  rw [h2 B hB, h2 _ (isSmearing_smear hR hU hg)]
theorem norm_smear_le {g : ℝ → ℂ} (hg : g ∈ c1Functions) :
    ‖smear U g‖ ≤ l1Norm g := by
  obtain ⟨B₀, -, h2, h3⟩ := exists_smearing hR hU hg
  rw [h2 _ (isSmearing_smear hR hU hg)]
  exact h3
theorem smear_add_smul {g h : ℝ → ℂ} (hg : g ∈ c1Functions)
    (hh : h ∈ c1Functions) (a : ℂ) :
    smear U (g + a • h) = smear U g + a • smear U h := by
  symm
  apply eq_smear_of_isSmearing hR hU (Submodule.add_mem _ hg (Submodule.smul_mem _ a hh))
  intro u v
  have hm := continuous_matrixCoeff hU u v
  have hi1 := integrable_c1_mul hg hm
  have hi2 := integrable_c1_mul hh hm
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_right,
    inner_smul_right, isSmearing_smear hR hU hg u v, isSmearing_smear hR hU hh u v,
    lebesgueIntegral_eq]
  rw [← integral_const_mul, ← integral_add hi1 (hi2.const_mul a)]
  congr 1
  funext s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem smear_zero : smear U (0 : ℝ → ℂ) = 0 := by
  symm
  apply eq_smear_of_isSmearing hR hU (Submodule.zero_mem _)
  intro u v
  simp [lebesgueIntegral_eq]
theorem smear_finsetSum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (G : ι → ℝ → ℂ)
    (hG : ∀ j ∈ s, G j ∈ c1Functions) :
    smear U (∑ j ∈ s, c j • G j) = ∑ j ∈ s, c j • smear U (G j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using smear_zero hR hU
  | insert a s ha ih =>
    have hs : ∑ j ∈ s, c j • G j ∈ c1Functions :=
      Submodule.sum_mem _ fun j hj =>
        Submodule.smul_mem _ _ (hG j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm,
      smear_add_smul hR hU hs (hG a (Finset.mem_insert_self _ _)),
      ih fun j hj => hG j (Finset.mem_insert_of_mem hj), add_comm]
theorem inner_smear_left {g : ℝ → ℂ} (hg : g ∈ c1Functions)
    (hg' : reflectConj g ∈ c1Functions) (u v : H) :
    inner ℂ (smear U g u) v = inner ℂ u (smear U (reflectConj g) v) := by
  rw [isSmearing_smear hR hU hg', ← inner_conj_symm, isSmearing_smear hR hU hg,
    lebesgueIntegral_eq, lebesgueIntegral_eq, ← integral_conj,
    ← integral_neg_eq_self (fun s => reflectConj g s * inner ℂ u (U s v)) volume]
  congr 1
  funext s
  rw [map_mul, inner_conj_symm, inner_unitary_left hU u v s]
  simp [reflectConj]
theorem smear_mul_smear {g h : ℝ → ℂ} (hg : g ∈ c1Functions)
    (hh : h ∈ c1Functions) (hgh : convolve g h ∈ c1Functions) :
    smear U g * smear U h = smear U (convolve g h) := by
  apply eq_smear_of_isSmearing hR hU hgh
  intro u v
  set m : ℝ → ℂ := fun s => inner ℂ u (U s v) with hm
  have hmc : Continuous m := continuous_matrixCoeff hU u v
  have hf : Integrable (Function.uncurry fun s x : ℝ => g s * (h (x - s) * m x))
      (volume.prod volume) := by
    have hcg := continuous_of_mem_c1 hg
    have hch := continuous_of_mem_c1 hh
    have hc : Continuous (Function.uncurry fun s x : ℝ => g s * (h (x - s) * m x)) := by
      unfold Function.uncurry
      fun_prop
    refine hc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact
      (((hasCompactSupport_of_mem_c1 hg).isCompact).prod
        (((hasCompactSupport_of_mem_c1 hg).isCompact).add
          (hasCompactSupport_of_mem_c1 hh).isCompact)) ?_
    rintro ⟨s, x⟩ hsx
    have hsx' : g s * (h (x - s) * m x) ≠ 0 := hsx
    have h1 : g s ≠ 0 := left_ne_zero_of_mul hsx'
    have h2 : h (x - s) ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hsx')
    refine ⟨subset_tsupport _ h1, ?_⟩
    have : x = s + (x - s) := by ring
    change x ∈ _
    rw [this]
    exact Set.add_mem_add (subset_tsupport _ h1) (subset_tsupport _ h2)
  have hinner : ∀ s : ℝ, inner ℂ u (U s (smear U h v)) =
      ∫ x, h (x - s) * m x := by
    intro s
    have e1 : inner ℂ u (U s (smear U h v)) =
        inner ℂ (U (-s) u) (smear U h v) := by
      rw [inner_unitary_left hU u _ (-s), neg_neg]
    rw [e1, isSmearing_smear hR hU hh, lebesgueIntegral_eq,
      ← integral_sub_right_eq_self (fun x => h x * inner ℂ (U (-s) u) (U x v)) s]
    congr 1
    funext x
    have e2 : inner ℂ (U (-s) u) (U (x - s) v) = m x := by
      rw [inner_unitary_left hU u _ (-s), neg_neg, hm]
      have h3 := congrArg (fun B : H →L[ℂ] H => B v) (hU.map_add s (x - s))
      have h4 : U s (U (x - s) v) = U x v := by simpa using h3
      simp only [h4]
    rw [e2]
  change inner ℂ u (smear U g (smear U h v)) = _
  rw [isSmearing_smear hR hU hg, lebesgueIntegral_eq, lebesgueIntegral_eq]
  simp only [hinner]
  have e3 : (fun s => g s * ∫ x, h (x - s) * m x) =
      fun s => ∫ x, g s * (h (x - s) * m x) := by
    funext s
    rw [integral_const_mul]
  rw [e3, integral_integral_swap hf]
  congr 1
  funext x
  change _ = convolve g h x * m x
  simp only [convolve, lebesgueIntegral_eq]
  rw [← integral_mul_const]
  congr 1
  funext s
  ring
theorem commute_smear {g : ℝ → ℂ} (hg : g ∈ c1Functions) {B : H →L[ℂ] H}
    (hB : IsSymmetricBounded B) (hc : ∀ s, Commute B (U s)) :
    Commute B (smear U g) := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  change inner ℂ u (B (smear U g v)) = inner ℂ u (smear U g (B v))
  rw [← hB u, isSmearing_smear hR hU hg, isSmearing_smear hR hU hg, lebesgueIntegral_eq,
    lebesgueIntegral_eq]
  congr 1
  funext s
  have h := congrArg (fun C : H →L[ℂ] H => C v) (hc s).eq
  have h' : B (U s v) = U s (B v) := h
  rw [hB u, h']
theorem smearingCalculus_of_pair (hC : ConvTransformRules) : SmearingCalculus U where
  existsUnique g hg := by
    obtain ⟨B, h1, h2, -⟩ := exists_smearing hR hU hg
    exact ⟨B, h1, h2⟩
  isSmearing _ hg := isSmearing_smear hR hU hg
  linear _ hg _ hh a := smear_add_smul hR hU hg hh a
  norm_le _ hg := norm_smear_le hR hU hg
  inner_left g hg := inner_smear_left hR hU hg (hC g hg g hg).2.1
  mul g hg h hh := smear_mul_smear hR hU hg hh (hC g hg h hh).1
  commute _ hB hc _ hg := commute_smear hR hU hg hB hc
end Smearing
theorem norm_le_uniformNorm {X : Type*} {f : X → ℂ} (hb : BddAbove (Set.range fun x => ‖f x‖))
    (x : X) : ‖f x‖ ≤ TestFunctions.uniformNorm f :=
  le_ciSup hb x
theorem uniformNorm_le {X : Type*} [Nonempty X] {f : X → ℂ} {c : ℝ} (h : ∀ x, ‖f x‖ ≤ c) :
    TestFunctions.uniformNorm f ≤ c :=
  ciSup_le h
theorem uniformNorm_nonneg {X : Type*} (f : X → ℂ) : 0 ≤ TestFunctions.uniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem norm_lineTransform_le (hB : TransformDerivBound) {g : ℝ → ℂ}
    (hg : g ∈ c1Functions) (q : ℝ) : ‖lineTransform g q‖ ≤ l1Norm g :=
  (hB g ((mem_ccIn_iff _ g).mpr
    ⟨continuous_of_mem_c1 hg, hasCompactSupport_of_mem_c1 hg, Set.subset_univ _⟩)).2.2.2 q
theorem bddAbove_norm_lineTransform (hB : TransformDerivBound) {g : ℝ → ℂ}
    (hg : g ∈ c1Functions) : BddAbove (Set.range fun q => ‖lineTransform g q‖) :=
  ⟨l1Norm g, by
    rintro _ ⟨q, rfl⟩
    exact norm_lineTransform_le hB hg q⟩
def opForm (D : H →L[ℂ] H) (u v : H) : ℂ := inner ℂ u (D v)
theorem isPosHermitianForm_opForm {D : H →L[ℂ] H} (hD : IsPositiveBounded D) :
    SpectralCalculus.IsPosHermitianForm (opForm D) where
  add_left f₁ f₂ h := inner_add_left _ _ _
  smul_left a f h := inner_smul_left _ _ _
  add_right f h₁ h₂ := by simp [opForm]
  smul_right a f h := by simp [opForm]
  conj_symm f h := by
    unfold opForm
    rw [inner_conj_symm, hD.1 h f]
  nonneg f := hD.2 f
theorem re_inner_apply_nonneg {D : H →L[ℂ] H} (hD : IsPositiveBounded D) (v : H) :
    0 ≤ (inner ℂ v (D v)).re :=
  (Complex.le_def.mp (hD.2 v)).1
theorem formSeminorm_opForm_sq {D : H →L[ℂ] H} (hD : IsPositiveBounded D) (v : H) :
    SpectralCalculus.formSeminorm (opForm D) v ^ 2 = (inner ℂ v (D v)).re :=
  Real.sq_sqrt (re_inner_apply_nonneg hD v)
theorem formSeminorm_opForm_le {D : H →L[ℂ] H} (v : H) :
    SpectralCalculus.formSeminorm (opForm D) v ≤ Real.sqrt ‖D‖ * ‖v‖ := by
  have h1 : (inner ℂ v (D v)).re ≤ ‖D‖ * ‖v‖ ^ 2 := by
    have h2 := (Complex.re_le_norm (inner ℂ v (D v))).trans (norm_inner_le_norm _ _)
    have h3 := D.le_opNorm v
    nlinarith [norm_nonneg v, norm_nonneg (D v)]
  calc SpectralCalculus.formSeminorm (opForm D) v ≤ Real.sqrt (‖D‖ * ‖v‖ ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = Real.sqrt ‖D‖ * ‖v‖ := by
      rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
theorem reflectConj_reflectConj (g : ℝ → ℂ) : reflectConj (reflectConj g) = g := by
  funext s
  simp [reflectConj]
section TransformBound
variable (hR : HilbertSpace.BoundedSesqRep.Claim)
  (hU : IsStronglyContinuousUnitaryGroup U)
include hR hU
theorem smearBoundedByTransform_of_rep (hS : SpectralCalculus.FormCompletionAndBoundedExtension)
    (hI : HilbertSpace.IteratedCauchySchwarz.Claim)
    (hC : ConvTransformRules) (hB : TransformDerivBound)
    (hP : ConvPowBound) : SmearBoundedByTransform U := by
  intro D hD hDc g hg v
  set S := TestFunctions.uniformNorm (lineTransform g) with hSdef
  have hS0 : 0 ≤ S := uniformNorm_nonneg _
  set k := reflectConj g with hk
  have hkm : k ∈ c1Functions := (hC g hg g hg).2.1
  have hkk : reflectConj k = g := reflectConj_reflectConj g
  set h := convolve k g with hh
  have hhm : h ∈ c1Functions := (hC k hkm g hg).1
  have hAmul : smear U k * smear U g = smear U h :=
    smear_mul_smear hR hU hkm hg hhm
  have hAv : ∀ w, smear U h w = smear U k (smear U g w) := fun w => by
    rw [← hAmul]
    rfl
  have hDcomm : ∀ {x : ℝ → ℂ}, x ∈ c1Functions → ∀ w,
      D (smear U x w) = smear U x (D w) := fun hx w =>
    congrArg (fun C : H →L[ℂ] H => C w) (commute_smear hR hU hx hD.1 hDc).eq
  have hform := isPosHermitianForm_opForm hD
  let A : H → H := fun w => smear U h w
  have hsym : ∀ f w, opForm D (A f) w = opForm D f (A w) := by
    intro f w
    simp only [opForm, A]
    rw [hAv f, inner_smear_left hR hU hkm (by rw [hkk]; exact hg), hkk,
      inner_smear_left hR hU hg hkm, ← hDcomm hg, ← hDcomm hkm, hAv w, hDcomm hkm, hDcomm hg]
  have hpow : ∀ n, 1 ≤ n → convPow h n ∈ c1Functions := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simpa [convPow_one] using hhm
    | succ n hn ih =>
      rw [convPow_succ h hn]
      exact (hC _ ih h hhm).1
  have hiter : ∀ n, 1 ≤ n → ∀ w, A^[n] w = smear U (convPow h n) w := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro w
      simp [A, convPow_one]
    | succ n hn ih =>
      intro w
      rw [Function.iterate_succ_apply, ih (A w), convPow_succ h hn,
        ← smear_mul_smear hR hU (hpow n hn) hhm (by
          rw [← convPow_succ h hn]
          exact hpow _ (by omega))]
      rfl
  have hhat : TestFunctions.uniformNorm (lineTransform h) ≤ S ^ 2 := by
    refine uniformNorm_le fun q => ?_
    have e : lineTransform h q = conj (lineTransform g q) * lineTransform g q := by
      rw [hh, (hC k hkm g hg).2.2.2.1, (hC g hg g hg).2.2.2.2]
      rfl
    rw [e, norm_mul, RCLike.norm_conj, ← pow_two]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_le_uniformNorm (bddAbove_norm_lineTransform hB hg) q) 2
  have hch : 0 ≤ convPowConst h :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hbound : ∀ k' n : ℕ, 1 ≤ k' → n = 2 ^ k' →
      SpectralCalculus.formSeminorm (opForm D) (A^[n] v) ≤
        (Real.sqrt ‖D‖ * ‖v‖ * convPowConst h) * (n : ℝ) * (S ^ 2) ^ (n - 1) := by
    intro k' n _ hn
    have hn1 : 1 ≤ n := by
      rw [hn]
      exact Nat.one_le_two_pow
    rw [hiter n hn1]
    have h1 : ‖smear U (convPow h n) v‖ ≤ l1Norm (convPow h n) * ‖v‖ :=
      ((smear U (convPow h n)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (norm_smear_le hR hU (hpow n hn1)) (norm_nonneg _))
    have h2 := hP h hhm n hn1
    have h3 : TestFunctions.uniformNorm (lineTransform h) ^ (n - 1) ≤ (S ^ 2) ^ (n - 1) :=
      pow_le_pow_left₀ (uniformNorm_nonneg _) hhat _
    have h4 : l1Norm (convPow h n) ≤ convPowConst h * (n : ℝ) * (S ^ 2) ^ (n - 1) :=
      h2.trans (mul_le_mul_of_nonneg_left h3 (mul_nonneg hch (Nat.cast_nonneg _)))
    calc SpectralCalculus.formSeminorm (opForm D) (smear U (convPow h n) v)
        ≤ Real.sqrt ‖D‖ * ‖smear U (convPow h n) v‖ := formSeminorm_opForm_le _
      _ ≤ Real.sqrt ‖D‖ * ((convPowConst h * (n : ℝ) * (S ^ 2) ^ (n - 1)) * ‖v‖) :=
        mul_le_mul_of_nonneg_left
          (h1.trans (mul_le_mul_of_nonneg_right h4 (norm_nonneg _))) (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hAb : SpectralCalculus.formSeminorm (opForm D) (A v) ≤
      S ^ 2 * SpectralCalculus.formSeminorm (opForm D) v :=
    (hI H (opForm D) A hform hsym).2 v (S ^ 2) _ (sq_nonneg S)
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hch) hbound
  have hCS := ((hS.1 H (opForm D) hform).1).norm_le_mul
  set Nv := SpectralCalculus.formSeminorm (opForm D) v with hNv
  set Ng := SpectralCalculus.formSeminorm (opForm D) (smear U g v) with hNg
  have hNv0 : 0 ≤ Nv := Real.sqrt_nonneg _
  have hNg0 : 0 ≤ Ng := Real.sqrt_nonneg _
  have hsq : Ng ^ 2 = (opForm D v (A v)).re := by
    rw [hNg, formSeminorm_opForm_sq hD]
    simp only [opForm, A]
    rw [hAv v, inner_smear_left hR hU hg hkm, ← hDcomm hkm]
  have hle : Ng ^ 2 ≤ (S * Nv) ^ 2 := by
    rw [hsq]
    calc (opForm D v (A v)).re ≤ ‖opForm D v (A v)‖ := Complex.re_le_norm _
      _ ≤ Nv * SpectralCalculus.formSeminorm (opForm D) (A v) := hCS _ _
      _ ≤ Nv * (S ^ 2 * Nv) := mul_le_mul_of_nonneg_left hAb hNv0
      _ = (S * Nv) ^ 2 := by ring
  have hNgle : Ng ≤ S * Nv :=
    (pow_le_pow_iff_left₀ hNg0 (mul_nonneg hS0 hNv0) two_ne_zero).mp hle
  calc ‖inner ℂ v (D (smear U g v))‖ = ‖opForm D v (smear U g v)‖ := rfl
    _ ≤ Nv * Ng := hCS _ _
    _ ≤ Nv * (S * Nv) := mul_le_mul_of_nonneg_left hNgle hNv0
    _ = S * Nv ^ 2 := by ring
    _ = S * (inner ℂ v (D v)).re := by rw [hNv, formSeminorm_opForm_sq hD]
end TransformBound
def fallingRatio (n i j : ℕ) : ℝ :=
  ∏ p ∈ Finset.range j, (((i - p : ℕ) : ℝ) / ((n - p : ℕ) : ℝ))
theorem fallingRatio_zero (n i : ℕ) : fallingRatio n i 0 = 1 := by
  simp [fallingRatio]
theorem fallingRatio_zero_left (n j : ℕ) : fallingRatio n 0 (j + 1) = 0 := by
  simp [fallingRatio]
theorem fallingRatio_succ_mul_choose (m i j : ℕ) :
    fallingRatio (m + 1) (i + 1) (j + 1) * ((m + 1).choose (i + 1) : ℝ) =
      fallingRatio m i j * (m.choose i : ℝ) := by
  have h1 : fallingRatio (m + 1) (i + 1) (j + 1) =
      fallingRatio m i j * (((i : ℝ) + 1) / ((m : ℝ) + 1)) := by
    unfold fallingRatio
    rw [Finset.prod_range_succ']
    congr 1
    · refine Finset.prod_congr rfl fun p _ => ?_
      rw [Nat.add_sub_add_right, Nat.add_sub_add_right]
    · simp
  have h2 : ((m : ℝ) + 1) * (m.choose i : ℝ) = ((m + 1).choose (i + 1) : ℝ) * ((i : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq m i
  have h3 : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [h1]
  field_simp
  linear_combination (-fallingRatio m i j) * h2
theorem pow_eq_sum_fallingRatio {R : Type*} [Ring R] [Algebra ℂ R] (a b : R) (hab : Commute a b)
    (h1 : a + b = 1) (j : ℕ) : ∀ n, j ≤ n →
    a ^ j = ∑ i ∈ Finset.range (n + 1),
      ((fallingRatio n i j * (n.choose i : ℝ) : ℝ) : ℂ) • (a ^ i * b ^ (n - i)) := by
  induction j with
  | zero =>
    intro n _
    have h := hab.add_pow n
    rw [h1, one_pow] at h
    rw [pow_zero, h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fallingRatio_zero, one_mul, Complex.ofReal_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul,
      (Nat.cast_commute _ _).eq]
  | succ j ih =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ', pow_succ', ih m (by omega), Finset.mul_sum]
    simp only [fallingRatio_zero_left, zero_mul, Complex.ofReal_zero, zero_smul, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fallingRatio_succ_mul_choose, mul_smul_comm, Nat.add_sub_add_right, pow_succ', mul_assoc]
theorem abs_prod_sub_pow_le (x : ℕ → ℝ) {y δ : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (j : ℕ)
    (hx : ∀ p < j, 0 ≤ x p ∧ x p ≤ 1 ∧ |x p - y| ≤ δ) :
    |∏ p ∈ Finset.range j, x p - y ^ j| ≤ j * δ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ih' := ih fun p hp => hx p (by omega)
    obtain ⟨h0, h1, h2⟩ := hx j (by omega)
    rw [Finset.prod_range_succ, pow_succ]
    have e : (∏ p ∈ Finset.range j, x p) * x j - y ^ j * y =
        (∏ p ∈ Finset.range j, x p - y ^ j) * x j + y ^ j * (x j - y) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg (pow_nonneg hy0 j)]
    have h3 : y ^ j ≤ 1 := pow_le_one₀ hy0 hy1
    push_cast
    have h4 : |∏ p ∈ Finset.range j, x p - y ^ j| * x j ≤ j * δ :=
      (mul_le_of_le_one_right (abs_nonneg _) h1).trans ih'
    have h5 : y ^ j * |x j - y| ≤ δ :=
      (mul_le_of_le_one_left (abs_nonneg _) h3).trans h2
    linarith
theorem abs_fallingRatio_sub_le {n i j J : ℕ} (hj : j ≤ J) (hi : i ≤ n) (hn : J < n) :
    |fallingRatio n i j - ((i : ℝ) / n) ^ j| ≤ j * ((J : ℝ) / ((n : ℝ) - J)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnJ : (0 : ℝ) < (n : ℝ) - J := by
    have : (J : ℝ) < n := by exact_mod_cast hn
    linarith
  have hin : (i : ℝ) ≤ n := by exact_mod_cast hi
  refine abs_prod_sub_pow_le _ (div_nonneg (Nat.cast_nonneg _) hn0.le)
    ((div_le_one hn0).mpr hin) j ?_
  intro p hp
  have hpn : p < n := by omega
  have hnp : (0 : ℝ) < ((n - p : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - p)
  refine ⟨div_nonneg (Nat.cast_nonneg _) hnp.le, ?_, ?_⟩
  · rw [div_le_one hnp]
    exact_mod_cast (by omega : i - p ≤ n - p)
  · have hpJ : (p : ℝ) ≤ J := by exact_mod_cast (by omega : p ≤ J)
    have hcast : ((n - p : ℕ) : ℝ) = (n : ℝ) - p := by
      rw [Nat.cast_sub hpn.le]
    rcases le_or_gt p i with h | h
    · have hc : ((i - p : ℕ) : ℝ) = (i : ℝ) - p := by rw [Nat.cast_sub h]
      have hnpr : (0 : ℝ) < (n : ℝ) - p := by
        rw [← hcast]
        exact hnp
      rw [hc, hcast]
      have e : ((i : ℝ) - p) / ((n : ℝ) - p) - (i : ℝ) / n =
          -((p : ℝ) * ((n : ℝ) - i) / ((n : ℝ) * ((n : ℝ) - p))) := by
        field_simp
        ring
      rw [e, abs_neg, abs_of_nonneg (by
        have : (0 : ℝ) ≤ (n : ℝ) - i := by linarith
        positivity)]
      rw [div_le_div_iff₀ (by positivity) hnJ]
      have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
      have h1 : (p : ℝ) * ((n : ℝ) - i) * ((n : ℝ) - J) ≤ (J : ℝ) * (n : ℝ) * ((n : ℝ) - J) := by
        have : (p : ℝ) * ((n : ℝ) - i) ≤ (J : ℝ) * n :=
          mul_le_mul hpJ (by linarith) (by linarith) hJ0
        exact mul_le_mul_of_nonneg_right this hnJ.le
      have h2 : (J : ℝ) * (n : ℝ) * ((n : ℝ) - J) ≤ (J : ℝ) * ((n : ℝ) * ((n : ℝ) - p)) := by
        have : (n : ℝ) - J ≤ (n : ℝ) - p := by linarith
        have h3 : (0 : ℝ) ≤ (J : ℝ) * n := by positivity
        nlinarith
      linarith
    · have hc : ((i - p : ℕ) : ℝ) = 0 := by
        rw [Nat.sub_eq_zero_of_le h.le]
        simp
      rw [hc, zero_div, zero_sub, abs_neg, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hn0.le)]
      have hiJ : (i : ℝ) ≤ J := by exact_mod_cast (by omega : i ≤ J)
      have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
      have h1 : (i : ℝ) / n ≤ (J : ℝ) / n := div_le_div_of_nonneg_right hiJ hn0.le
      have h2 : (J : ℝ) / n ≤ (J : ℝ) / ((n : ℝ) - J) :=
        div_le_div_of_nonneg_left hJ0 hnJ (by linarith)
      exact h1.trans h2
theorem inner_self_eq_ofReal_sq (v : H) : inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem inner_self_nonneg' (v : H) : 0 ≤ inner ℂ v v := by
  rw [inner_self_eq_ofReal_sq]
  exact_mod_cast sq_nonneg ‖v‖
theorem isSymmetricBounded_mul {A B : H →L[ℂ] H} (hA : IsSymmetricBounded A)
    (hB : IsSymmetricBounded B) (hc : Commute A B) : IsSymmetricBounded (A * B) := by
  intro u v
  change inner ℂ (A (B u)) v = inner ℂ u ((A * B) v)
  rw [hA, hB, hc.eq]
  rfl
theorem isSymmetricBounded_one : IsSymmetricBounded (1 : H →L[ℂ] H) := fun _ _ => rfl
theorem isSymmetricBounded_pow {A : H →L[ℂ] H} (hA : IsSymmetricBounded A) (i : ℕ) :
    IsSymmetricBounded (A ^ i) := by
  induction i with
  | zero => simpa using isSymmetricBounded_one (H := H)
  | succ i ih =>
    rw [pow_succ]
    exact isSymmetricBounded_mul ih hA (Commute.pow_left (Commute.refl A) i)
theorem inner_conj_mul_nonneg {C E : H →L[ℂ] H} (hC : IsSymmetricBounded C)
    (hE : ∀ v, 0 ≤ inner ℂ v (E v)) (v : H) : 0 ≤ inner ℂ v ((C * E * C) v) := by
  change 0 ≤ inner ℂ v (C (E (C v)))
  rw [← hC]
  exact hE _
theorem inner_pow_mul_pow_nonneg {A B : H →L[ℂ] H} (hA : IsPositiveBounded A)
    (hB : IsPositiveBounded B) (h1 : A + B = 1) (hc : Commute A B) (N : ℕ) :
    ∀ i k, i + k ≤ N → ∀ v, 0 ≤ inner ℂ v ((A ^ i * B ^ k) v) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i k hik v
    rcases i with _ | _ | i
    · rcases k with _ | _ | k
      · simpa using inner_self_nonneg' v
      · simpa using hB.2 v
      · have e : A ^ 0 * B ^ (k + 2) = B * (A ^ 0 * B ^ k) * B := by
          simp only [pow_zero, one_mul]
          rw [pow_succ, pow_succ', mul_assoc]
        rw [e]
        exact inner_conj_mul_nonneg hB.1 (ih k (by omega) 0 k (by omega)) v
    · rcases k with _ | _ | k
      · simpa using hA.2 v
      · have e : A ^ (0 + 1) * B ^ (0 + 1) = A * B * A + B * A * B := by
          have h2 : A * B * (A + B) = A * B := by rw [h1, mul_one]
          rw [zero_add, pow_one, pow_one]
          conv_lhs => rw [← h2]
          rw [mul_add, hc.eq]
        rw [e]
        have h3 := inner_conj_mul_nonneg hA.1 hB.2 v
        have h4 := inner_conj_mul_nonneg hB.1 hA.2 v
        change 0 ≤ inner ℂ v ((A * B * A) v + (B * A * B) v)
        rw [inner_add_right]
        exact add_nonneg h3 h4
      · have e : A ^ (0 + 1) * B ^ (k + 2) = B * (A ^ (0 + 1) * B ^ k) * B := by
          rw [pow_succ B (k + 1), pow_succ' B k, zero_add, pow_one]
          rw [← mul_assoc, ← mul_assoc, hc.eq]
          simp only [mul_assoc]
        rw [e]
        exact inner_conj_mul_nonneg hB.1 (ih (k + 1) (by omega) (0 + 1) k (by omega)) v
    · have e : A ^ (i + 2) * B ^ k = A * (A ^ i * B ^ k) * A := by
        have hk : Commute A (B ^ k) := hc.pow_right k
        rw [pow_succ A (i + 1), pow_succ' A i, mul_assoc, mul_assoc, mul_assoc, mul_assoc,
          hk.eq]
      have e' : A ^ (i + 1 + 1) * B ^ k = A * (A ^ i * B ^ k) * A := e
      rw [e']
      exact inner_conj_mul_nonneg hA.1 (ih (i + k) (by omega) i k (by omega)) v
theorem isPositiveBounded_semigroup (hT : IsSelfAdjointContractionSemigroup T) (τ : ℝ≥0) :
    IsPositiveBounded (T τ) := by
  refine ⟨hT.isSymmetricBounded τ, fun v => ?_⟩
  have e : T τ = T (τ / 2) * T (τ / 2) := by rw [hT.map_add, add_halves]
  rw [e]
  change 0 ≤ inner ℂ v (T (τ / 2) (T (τ / 2) v))
  rw [← hT.isSymmetricBounded (τ / 2)]
  exact inner_self_nonneg' _
theorem isPositiveBounded_one_sub_semigroup (hT : IsSelfAdjointContractionSemigroup T)
    (τ : ℝ≥0) : IsPositiveBounded (1 - T τ) := by
  have hA := isPositiveBounded_semigroup hT τ
  refine ⟨fun u v => ?_, fun v => ?_⟩
  · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_left,
      inner_sub_right]
    rw [hA.1]
  · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right]
    have h1 := Complex.le_def.mp (hA.2 v)
    have h2 : (inner ℂ v (T τ v)).re ≤ ‖v‖ ^ 2 := by
      have h3 := (Complex.re_le_norm (inner ℂ v (T τ v))).trans (norm_inner_le_norm _ _)
      have h4 := (T τ).le_of_opNorm_le (hT.isContractive τ) v
      rw [one_mul] at h4
      nlinarith [norm_nonneg v, norm_nonneg (T τ v)]
    rw [Complex.le_def]
    have h7 : (inner ℂ v (T τ v)).im = 0 := by simpa using h1.2.symm
    rw [inner_self_eq_ofReal_sq]
    simp only [Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im,
      Complex.ofReal_re, Complex.ofReal_im, h7]
    exact ⟨by linarith, by simp⟩
theorem semigroup_pow (hT : IsSelfAdjointContractionSemigroup T) (τ : ℝ≥0) (j : ℕ) :
    T τ ^ j = T ((j : ℝ≥0) * τ) := by
  induction j with
  | zero => simp [hT.map_zero]
  | succ j ih =>
    rw [pow_succ, ih, hT.map_add]
    congr 1
    push_cast
    ring
theorem continuous_cexp_I_mul (q : ℝ) :
    Continuous fun s : ℝ => Complex.exp (Complex.I * (s : ℂ) * (q : ℂ)) := by apply _root_.YangMills.Construction.Splines.CubicSplineLemmas.continuous_fourierPhase <;> assumption
theorem lineTransform_finsetSum {ι : Type*} (t : Finset ι) (c : ι → ℂ) (G : ι → ℝ → ℂ)
    (hG : ∀ j ∈ t, G j ∈ c1Functions) (q : ℝ) :
    lineTransform (∑ j ∈ t, c j • G j) q = ∑ j ∈ t, c j * lineTransform (G j) q := by
  have key : ∀ E : ℝ → ℂ, Continuous E →
      lebesgueIntegral (fun s => (∑ j ∈ t, c j • G j) s * E s) =
        ∑ j ∈ t, c j * lebesgueIntegral fun s => G j s * E s := by
    intro E hE
    rw [lebesgueIntegral_eq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ fun j hj => (integrable_c1_mul (hG j hj) hE).const_mul (c j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [lebesgueIntegral_eq, integral_const_mul]
  exact key _ (continuous_cexp_I_mul q)
theorem intervalRpow_nonneg (t : ℝ≥0) (a : unitInterval) : 0 ≤ intervalRpow t a :=
  Real.rpow_nonneg a.2.1 _
theorem intervalRpow_le_one (t : ℝ≥0) (a : unitInterval) : intervalRpow t a ≤ 1 :=
  Real.rpow_le_one a.2.1 a.2.2 t.2
theorem norm_transformSum_le (hB : TransformDerivBound) {τ : ℝ≥0} {J : ℕ}
    {g : ℕ → ℝ → ℂ} (hg : ∀ j ≤ J, g j ∈ c1Functions) (p : UnitStrip) :
    ‖transformSum τ J g p‖ ≤ ∑ j ∈ Finset.range (J + 1), l1Norm (g j) := by
  refine norm_sum_le_of_le _ fun j hj => ?_
  have hj' : j ≤ J := by
    have := Finset.mem_range.mp hj
    omega
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (intervalRpow_nonneg _ _)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (intervalRpow_le_one _ _)).trans
    (norm_lineTransform_le hB (hg j hj') _)
theorem bddAbove_norm_transformSum (hB : TransformDerivBound) {τ : ℝ≥0} {J : ℕ}
    {g : ℕ → ℝ → ℂ} (hg : ∀ j ≤ J, g j ∈ c1Functions) :
    BddAbove (Set.range fun p => ‖transformSum τ J g p‖) :=
  ⟨_, by
    rintro _ ⟨p, rfl⟩
    exact norm_transformSum_le hB hg p⟩
theorem norm_lineTransform_fallingRatio_sum_le (hB : TransformDerivBound) {τ : ℝ≥0}
    (hτ : 0 < τ) {J n i : ℕ} {g : ℕ → ℝ → ℂ} (hg : ∀ j ≤ J, g j ∈ c1Functions)
    (hn : J < n) (hi : i ≤ n) (q : ℝ) :
    ‖lineTransform (∑ j ∈ Finset.range (J + 1), ((fallingRatio n i j : ℝ) : ℂ) • g j) q‖ ≤
      TestFunctions.uniformNorm (transformSum τ J g) +
        (J : ℝ) * ((J : ℝ) / ((n : ℝ) - J)) * ∑ j ∈ Finset.range (J + 1), l1Norm (g j) := by
  have hmem : ∀ j ∈ Finset.range (J + 1), j ≤ J := fun j hj => by
    have := Finset.mem_range.mp hj
    omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnJ : (0 : ℝ) < (n : ℝ) - J := by
    have : (J : ℝ) < n := by exact_mod_cast hn
    linarith
  have hin : (i : ℝ) ≤ n := by exact_mod_cast hi
  have hy0 : 0 ≤ (i : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hn0.le
  have hy1 : (i : ℝ) / n ≤ 1 := (div_le_one hn0).mpr hin
  have hτ' : (τ : ℝ) ≠ 0 := (NNReal.coe_pos.mpr hτ).ne'
  let a : unitInterval := ⟨((i : ℝ) / n) ^ (1 / (τ : ℝ)), Real.rpow_nonneg hy0 _,
    Real.rpow_le_one hy0 hy1 (by positivity)⟩
  have hpow : ∀ j : ℕ, intervalRpow ((j : ℝ≥0) * τ) a = ((i : ℝ) / n) ^ j := by
    intro j
    change (((i : ℝ) / n) ^ (1 / (τ : ℝ))) ^ (((j : ℝ≥0) * τ : ℝ≥0) : ℝ) = _
    rw [← Real.rpow_mul hy0]
    have e : 1 / (τ : ℝ) * (((j : ℝ≥0) * τ : ℝ≥0) : ℝ) = (j : ℝ) := by
      push_cast
      field_simp
    rw [e, Real.rpow_natCast]
  have hF : transformSum τ J g (a, q) =
      ∑ j ∈ Finset.range (J + 1), ((((i : ℝ) / n) ^ j : ℝ) : ℂ) * lineTransform (g j) q := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hpow]
  rw [lineTransform_finsetSum _ _ _ fun j hj => hg j (hmem j hj)]
  have hd : ∑ j ∈ Finset.range (J + 1), ((fallingRatio n i j : ℝ) : ℂ) * lineTransform (g j) q =
      transformSum τ J g (a, q) + ∑ j ∈ Finset.range (J + 1),
        ((fallingRatio n i j - ((i : ℝ) / n) ^ j : ℝ) : ℂ) * lineTransform (g j) q := by
    rw [hF, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [hd]
  refine (norm_add_le _ _).trans (add_le_add
    (norm_le_uniformNorm (bddAbove_norm_transformSum hB hg) _) ?_)
  rw [Finset.mul_sum]
  refine norm_sum_le_of_le _ fun j hj => ?_
  have hj' := hmem j hj
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := abs_fallingRatio_sub_le hj' hi hn
  have h2 : (j : ℝ) * ((J : ℝ) / ((n : ℝ) - J)) ≤ (J : ℝ) * ((J : ℝ) / ((n : ℝ) - J)) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hj') (div_nonneg (Nat.cast_nonneg _) hnJ.le)
  exact mul_le_mul (h1.trans h2) (norm_lineTransform_le hB (hg j hj') q) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg _) hnJ.le))
section Expansion
variable (hR : HilbertSpace.BoundedSesqRep.Claim)
include hR
theorem norm_inner_smearedSum_le_of_lt (hp : IsCommutingSemigroupGroup T U)
    (hB : TransformDerivBound) (hc : SmearBoundedByTransform U) {τ : ℝ≥0} (hτ : 0 < τ)
    {J n : ℕ} {g : ℕ → ℝ → ℂ} (hg : ∀ j ≤ J, g j ∈ c1Functions) (hn : J < n) (v : H) :
    ‖inner ℂ v (smearedSum T U τ J g v)‖ ≤
      (TestFunctions.uniformNorm (transformSum τ J g) +
        (J : ℝ) * ((J : ℝ) / ((n : ℝ) - J)) * ∑ j ∈ Finset.range (J + 1), l1Norm (g j)) *
        ‖v‖ ^ 2 := by
  have hU := hp.group
  have hT := hp.semigroup
  have hmem : ∀ j ∈ Finset.range (J + 1), j ≤ J := fun j hj => by
    have := Finset.mem_range.mp hj
    omega
  set A := T τ with hA
  set B : H →L[ℂ] H := 1 - A with hBdef
  have hAB : A + B = 1 := by
    rw [hBdef]
    abel
  have hcomm : Commute A B := (Commute.one_right A).sub_right (Commute.refl A)
  have hAnn : IsPositiveBounded A := isPositiveBounded_semigroup hT τ
  have hBnn : IsPositiveBounded B := isPositiveBounded_one_sub_semigroup hT τ
  let Dop : ℕ → H →L[ℂ] H := fun i => ((n.choose i : ℝ) : ℂ) • (A ^ i * B ^ (n - i))
  have hPsa : ∀ i, IsSymmetricBounded (A ^ i * B ^ (n - i)) := fun i =>
    isSymmetricBounded_mul (isSymmetricBounded_pow hAnn.1 _) (isSymmetricBounded_pow hBnn.1 _)
      (hcomm.pow_pow _ _)
  have hDnn : ∀ i, IsPositiveBounded (Dop i) := by
    intro i
    refine ⟨fun u w => ?_, fun w => ?_⟩
    · simp only [Dop]
      change inner ℂ (((n.choose i : ℝ) : ℂ) • (A ^ i * B ^ (n - i)) u) w =
        inner ℂ u (((n.choose i : ℝ) : ℂ) • (A ^ i * B ^ (n - i)) w)
      rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, hPsa i]
    · simp only [Dop]
      change 0 ≤ inner ℂ w (((n.choose i : ℝ) : ℂ) • (A ^ i * B ^ (n - i)) w)
      rw [inner_smul_right]
      refine mul_nonneg ?_ (inner_pow_mul_pow_nonneg hAnn hBnn hAB hcomm _ i (n - i) le_rfl w)
      exact_mod_cast Nat.cast_nonneg (n.choose i)
  have hAU : ∀ s, Commute A (U s) := fun s => hp.commute τ s
  have hDU : ∀ i s, Commute (Dop i) (U s) := by
    intro i s
    have hBU : Commute B (U s) := (Commute.one_left _).sub_left (hAU s)
    exact ((hAU s).pow_left i |>.mul_left (hBU.pow_left (n - i))).smul_left _
  have hexp : ∀ j, j ≤ n → A ^ j = ∑ i ∈ Finset.range (n + 1),
      ((fallingRatio n i j : ℝ) : ℂ) • Dop i := by
    intro j hj
    rw [pow_eq_sum_fallingRatio A B hcomm hAB j n hj]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Dop]
    rw [smul_smul]
    push_cast
    rfl
  have hsum : ∑ i ∈ Finset.range (n + 1), Dop i = 1 := by
    have h := hexp 0 (Nat.zero_le _)
    simp only [fallingRatio_zero, pow_zero, Complex.ofReal_one, one_smul] at h
    exact h.symm
  let G : ℕ → ℝ → ℂ := fun i =>
    ∑ j ∈ Finset.range (J + 1), ((fallingRatio n i j : ℝ) : ℂ) • g j
  have hG : ∀ i, G i ∈ c1Functions := fun i =>
    Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hg j (hmem j hj))
  have hPhi : smearedSum T U τ J g =
      ∑ i ∈ Finset.range (n + 1), Dop i * smear U (G i) := by
    unfold smearedSum
    have e1 : ∀ i, Dop i * smear U (G i) = ∑ j ∈ Finset.range (J + 1),
        ((fallingRatio n i j : ℝ) : ℂ) • (Dop i * smear U (g j)) := by
      intro i
      simp only [G]
      rw [smear_finsetSum hR hU _ _ _ fun j hj => hg j (hmem j hj), Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm]
    simp only [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← semigroup_pow hT, hexp j (by have := hmem j hj; omega), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc]
  set C := ∑ j ∈ Finset.range (J + 1), l1Norm (g j) with hC
  set M := TestFunctions.uniformNorm (transformSum τ J g) +
    (J : ℝ) * ((J : ℝ) / ((n : ℝ) - J)) * C with hM
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖inner ℂ v ((Dop i * smear U (G i)) v)‖ ≤ M * (inner ℂ v (Dop i v)).re := by
    intro i hi
    have hi' : i ≤ n := by
      have := Finset.mem_range.mp hi
      omega
    have h1 := hc (Dop i) (hDnn i) (hDU i) (G i) (hG i) v
    have h2 : TestFunctions.uniformNorm (lineTransform (G i)) ≤ M :=
      uniformNorm_le fun q => norm_lineTransform_fallingRatio_sum_le hB hτ hg hn hi' q
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (re_inner_apply_nonneg (hDnn i) v))
  have hre : ∑ i ∈ Finset.range (n + 1), (inner ℂ v (Dop i v)).re = ‖v‖ ^ 2 := by
    have h1 : ∑ i ∈ Finset.range (n + 1), inner ℂ v (Dop i v) = inner ℂ v v := by
      rw [← inner_sum]
      congr 1
      have h2 := congrArg (fun E : H →L[ℂ] H => E v) hsum
      simpa using h2
    rw [← Complex.re_sum, h1, inner_self_eq_ofReal_sq, Complex.ofReal_re]
  rw [hPhi]
  have e2 : inner ℂ v ((∑ i ∈ Finset.range (n + 1), Dop i * smear U (G i)) v) =
      ∑ i ∈ Finset.range (n + 1), inner ℂ v ((Dop i * smear U (G i)) v) := by
    rw [← inner_sum]
    congr 1
    simp
  rw [e2, ← hre, Finset.mul_sum]
  exact norm_sum_le_of_le _ hterm
theorem norm_inner_smearedSum_le (hp : IsCommutingSemigroupGroup T U) (hB : TransformDerivBound)
    (hc : SmearBoundedByTransform U) {τ : ℝ≥0} (hτ : 0 < τ) {J : ℕ} {g : ℕ → ℝ → ℂ}
    (hg : ∀ j ≤ J, g j ∈ c1Functions) (v : H) :
    ‖inner ℂ v (smearedSum T U τ J g v)‖ ≤
      TestFunctions.uniformNorm (transformSum τ J g) * ‖v‖ ^ 2 := by
  set S := TestFunctions.uniformNorm (transformSum τ J g) with hS
  set C := ∑ j ∈ Finset.range (J + 1), l1Norm (g j) with hC
  have hlim : Tendsto (fun m : ℕ => (S + ((J : ℝ) * J * C) * (1 / ((m : ℝ) + 1))) * ‖v‖ ^ 2)
      atTop (𝓝 (S * ‖v‖ ^ 2)) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      ((J : ℝ) * J * C)).const_add S
    simpa using h.mul_const (‖v‖ ^ 2)
  refine ge_of_tendsto' hlim fun m => ?_
  have h := norm_inner_smearedSum_le_of_lt hR hp hB hc hτ hg (show J < m + J + 1 by omega) v
  have e : (((m + J + 1 : ℕ) : ℝ) - J) = (m : ℝ) + 1 := by
    push_cast
    ring
  rw [e] at h
  have e' : (J : ℝ) * ((J : ℝ) / ((m : ℝ) + 1)) * C = (J : ℝ) * J * C * (1 / ((m : ℝ) + 1)) := by
    ring
  rw [e'] at h
  exact h
end Expansion
section SquareSums
variable (hR : HilbertSpace.BoundedSesqRep.Claim)
include hR
theorem commute_semigroup_smear (hp : IsCommutingSemigroupGroup T U) {g : ℝ → ℂ}
    (hg : g ∈ c1Functions) (t : ℝ≥0) :
    Commute (T t) (smear U g) :=
  commute_smear hR hp.group hg (hp.semigroup.isSymmetricBounded t) (hp.commute t)
theorem inner_smearedSum_left (hp : IsCommutingSemigroupGroup T U) (hC : ConvTransformRules)
    {τ : ℝ≥0} {J : ℕ} {g : ℕ → ℝ → ℂ} (hg : ∀ j ≤ J, g j ∈ c1Functions) (u v : H) :
    inner ℂ (smearedSum T U τ J g u) v =
      inner ℂ u (smearedSum T U τ J (fun j => reflectConj (g j)) v) := by
  have hU := hp.group
  have hT := hp.semigroup
  unfold smearedSum
  simp only [ContinuousLinearMap.sum_apply]
  rw [sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ J := by
    have := Finset.mem_range.mp hj
    omega
  have hgj := hg j hj'
  have hk := (hC _ hgj _ hgj).2.1
  change inner ℂ (T _ (smear U (g j) u)) v =
    inner ℂ u (T _ (smear U (reflectConj (g j)) v))
  rw [hT.isSymmetricBounded, inner_smear_left hR hU hgj hk]
  have h := congrArg (fun E : H →L[ℂ] H => E v)
    (commute_semigroup_smear hR hp hk ((j : ℝ≥0) * τ)).eq
  have h' : T ((j : ℝ≥0) * τ) (smear U (reflectConj (g j)) v) =
      smear U (reflectConj (g j)) (T ((j : ℝ≥0) * τ) v) := h
  rw [h']
omit hR in
theorem convSquare_mem (hC : ConvTransformRules) {J : ℕ} {g : ℕ → ℝ → ℂ}
    (hg : ∀ j ≤ J, g j ∈ c1Functions) (i : ℕ) :
    convSquare J g i ∈ c1Functions := by
  refine Submodule.sum_mem _ fun p hp => ?_
  have hp' := (Finset.mem_filter.mp hp).1
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp'
  have h1' : p.1 ≤ J := by
    have := Finset.mem_range.mp h1
    omega
  have h2' : p.2 ≤ J := by
    have := Finset.mem_range.mp h2
    omega
  exact (hC _ (hC _ (hg _ h1') _ (hg _ h1')).2.1 _ (hg _ h2')).1
theorem smearedSum_reflectConj_mul (hp : IsCommutingSemigroupGroup T U) (hC : ConvTransformRules)
    {τ : ℝ≥0} {J : ℕ} {g : ℕ → ℝ → ℂ} (hg : ∀ j ≤ J, g j ∈ c1Functions) :
    smearedSum T U τ J (fun j => reflectConj (g j)) * smearedSum T U τ J g =
      smearedSum T U τ (2 * J) (convSquare J g) := by
  classical
  have hU := hp.group
  have hT := hp.semigroup
  have hmem : ∀ j ∈ Finset.range (J + 1), j ≤ J := fun j hj => by
    have := Finset.mem_range.mp hj
    omega
  set S := Finset.range (J + 1) ×ˢ Finset.range (J + 1) with hS
  let f : ℕ × ℕ → H →L[ℂ] H := fun p => T (((p.1 + p.2 : ℕ) : ℝ≥0) * τ) *
    smear U (convolve (reflectConj (g p.1)) (g p.2))
  have hcm : ∀ p ∈ S, convolve (reflectConj (g p.1)) (g p.2) ∈ c1Functions := by
    intro p hp'
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp'
    exact (hC _ (hC _ (hg _ (hmem _ h1)) _ (hg _ (hmem _ h1))).2.1 _ (hg _ (hmem _ h2))).1
  have hleft : smearedSum T U τ J (fun j => reflectConj (g j)) *
      smearedSum T U τ J g = ∑ p ∈ S, f p := by
    unfold smearedSum
    rw [Finset.sum_mul_sum, hS, Finset.sum_product]
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun j' hj' => ?_
    have hgj := hg j (hmem j hj)
    have hgj' := hg j' (hmem j' hj')
    have hk := (hC _ hgj _ hgj).2.1
    have hcomm := (commute_semigroup_smear hR hp hk ((j' : ℝ≥0) * τ)).eq
    simp only [f]
    rw [← smear_mul_smear hR hU hk hgj' (hC _ hk _ hgj').1]
    have e : (((j + j' : ℕ) : ℝ≥0) * τ) = (j : ℝ≥0) * τ + (j' : ℝ≥0) * τ := by
      push_cast
      ring
    rw [e, ← hT.map_add]
    calc T ((j : ℝ≥0) * τ) * smear U (reflectConj (g j)) *
          (T ((j' : ℝ≥0) * τ) * smear U (g j'))
        = T ((j : ℝ≥0) * τ) * (smear U (reflectConj (g j)) * T ((j' : ℝ≥0) * τ)) *
            smear U (g j') := by simp only [mul_assoc]
      _ = T ((j : ℝ≥0) * τ) * (T ((j' : ℝ≥0) * τ) * smear U (reflectConj (g j))) *
            smear U (g j') := by rw [hcomm]
      _ = _ := by simp only [mul_assoc]
  have hright : smearedSum T U τ (2 * J) (convSquare J g) =
      ∑ i ∈ Finset.range (2 * J + 1), ∑ p ∈ S with p.1 + p.2 = i, f p := by
    unfold smearedSum
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : convSquare J g i = ∑ p ∈ S with p.1 + p.2 = i,
        (1 : ℂ) • convolve (reflectConj (g p.1)) (g p.2) := by
      simp [convSquare, hS]
    rw [e, smear_finsetSum hR hU _ _ _ fun p hp' => hcm p (Finset.mem_filter.mp hp').1,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp' => ?_
    simp only [f, one_smul]
    rw [(Finset.mem_filter.mp hp').2]
  rw [hleft, hright]
  refine (Finset.sum_fiberwise_of_maps_to (fun p hp' => ?_) f).symm
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp'
  have h1' := hmem _ h1
  have h2' := hmem _ h2
  exact Finset.mem_range.mpr (by omega)
end SquareSums
theorem intervalRpow_add (t t' : ℝ≥0) (a : unitInterval) :
    intervalRpow (t + t') a = intervalRpow t a * intervalRpow t' a := by
  simp only [intervalRpow, NNReal.coe_add]
  exact Real.rpow_add_of_nonneg a.2.1 t.2 t'.2
theorem transformSum_convSquare (hC : ConvTransformRules) {τ : ℝ≥0} {J : ℕ}
    {g : ℕ → ℝ → ℂ} (hg : ∀ j ≤ J, g j ∈ c1Functions) (p : UnitStrip) :
    transformSum τ (2 * J) (convSquare J g) p =
      ((‖transformSum τ J g p‖ ^ 2 : ℝ) : ℂ) := by
  classical
  obtain ⟨a, q⟩ := p
  have hmem : ∀ j ∈ Finset.range (J + 1), j ≤ J := fun j hj => by
    have := Finset.mem_range.mp hj
    omega
  set S := Finset.range (J + 1) ×ˢ Finset.range (J + 1) with hS
  let f : ℕ × ℕ → ℂ := fun r => (intervalRpow (((r.1 + r.2 : ℕ) : ℝ≥0) * τ) a : ℂ) *
    (conj (lineTransform (g r.1) q) * lineTransform (g r.2) q)
  have hcm : ∀ r ∈ S, convolve (reflectConj (g r.1)) (g r.2) ∈ c1Functions ∧
      lineTransform (convolve (reflectConj (g r.1)) (g r.2)) q =
        conj (lineTransform (g r.1) q) * lineTransform (g r.2) q := by
    intro r hr
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hr
    have hk := (hC _ (hg _ (hmem _ h1)) _ (hg _ (hmem _ h1))).2.1
    have hc := hC _ hk _ (hg _ (hmem _ h2))
    refine ⟨hc.1, ?_⟩
    rw [hc.2.2.2.1, (hC _ (hg _ (hmem _ h1)) _ (hg _ (hmem _ h1))).2.2.2.2]
    rfl
  have hleft : transformSum τ (2 * J) (convSquare J g) (a, q) =
      ∑ i ∈ Finset.range (2 * J + 1), ∑ r ∈ S with r.1 + r.2 = i, f r := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : convSquare J g i = ∑ r ∈ S with r.1 + r.2 = i,
        (1 : ℂ) • convolve (reflectConj (g r.1)) (g r.2) := by
      simp [convSquare, hS]
    rw [e, lineTransform_finsetSum _ _ _ fun r hr => (hcm r (Finset.mem_filter.mp hr).1).1,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    simp only [f, one_mul]
    rw [(hcm r (Finset.mem_filter.mp hr).1).2, (Finset.mem_filter.mp hr).2]
  have hfib : ∑ i ∈ Finset.range (2 * J + 1), ∑ r ∈ S with r.1 + r.2 = i, f r =
      ∑ r ∈ S, f r := by
    refine Finset.sum_fiberwise_of_maps_to (fun r hr => ?_) f
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hr
    have h1' := hmem _ h1
    have h2' := hmem _ h2
    exact Finset.mem_range.mpr (by omega)
  have hprod : conj (transformSum τ J g (a, q)) * transformSum τ J g (a, q) =
      ∑ r ∈ S, f r := by
    unfold transformSum
    rw [map_sum, Finset.sum_mul_sum, hS, Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    simp only [f, map_mul, Complex.conj_ofReal]
    have e : (((j + j' : ℕ) : ℝ≥0) * τ) = (j : ℝ≥0) * τ + (j' : ℝ≥0) * τ := by
      push_cast
      ring
    rw [e, intervalRpow_add]
    push_cast
    ring
  rw [hleft, hfib, ← hprod, Complex.conj_mul']
  push_cast
  rfl
section Bounds
variable (hR : HilbertSpace.BoundedSesqRep.Claim)
include hR
theorem smearedSumBounds_of_pair (hp : IsCommutingSemigroupGroup T U) (hC : ConvTransformRules)
    (hB : TransformDerivBound) (hc : SmearBoundedByTransform U) {τ : ℝ≥0} (hτ : 0 < τ)
    {J : ℕ} {g : ℕ → ℝ → ℂ} (hg : ∀ j ≤ J, g j ∈ c1Functions) :
    SmearedSumBounds T U τ J g := by
  have hsq : ∀ i ≤ 2 * J, convSquare J g i ∈ c1Functions := fun i _ =>
    convSquare_mem hC hg i
  have hnorm : ∀ v : H, ((‖smearedSum T U τ J g v‖ ^ 2 : ℝ) : ℂ) =
      inner ℂ v (smearedSum T U τ (2 * J) (convSquare J g) v) := by
    intro v
    rw [← smearedSum_reflectConj_mul hR hp hC hg, ← inner_self_eq_ofReal_sq,
      inner_smearedSum_left hR hp hC hg]
    rfl
  refine ⟨norm_inner_smearedSum_le hR hp hB hc hτ hg, fun v => ?_, hsq, hnorm,
    transformSum_convSquare hC hg⟩
  set S := TestFunctions.uniformNorm (transformSum τ J g) with hS
  have hS0 : 0 ≤ S := uniformNorm_nonneg _
  have h1 := norm_inner_smearedSum_le hR hp hB hc hτ hsq v
  rw [← hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
  have h2 : TestFunctions.uniformNorm (transformSum τ (2 * J) (convSquare J g)) ≤ S ^ 2 := by
    refine uniformNorm_le fun p => ?_
    rw [transformSum_convSquare hC hg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_le_uniformNorm (bddAbove_norm_transformSum hB hg) p) 2
  have h3 : ‖smearedSum T U τ J g v‖ ^ 2 ≤ (S * ‖v‖) ^ 2 := by
    rw [mul_pow]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hS0 (norm_nonneg _)) two_ne_zero).mp h3
end Bounds
end SmearedPairBoundsProof
theorem smearedPairBounds_holds
    (hS : SpectralCalculus.FormCompletionAndBoundedExtension)
    (hR : HilbertSpace.BoundedSesqRep.Claim)
    (hI : HilbertSpace.IteratedCauchySchwarz.Claim)
    (hF : ConvPowDensity.Statement) : SmearedPairBounds := by
  intro H _ _ _ T U hp
  obtain ⟨hC, hB, -, hP, -⟩ := hF
  have hU := hp.group
  have hc : SmearBoundedByTransform U :=
    SmearedPairBoundsProof.smearBoundedByTransform_of_rep hR hU hS hI hC hB hP
  exact ⟨SmearedPairBoundsProof.matrixCoeffsContinuous_of_pair hp,
    SmearedPairBoundsProof.smearingCalculus_of_pair hR hU hC, hc,
    fun τ J g hτ hg => SmearedPairBoundsProof.smearedSumBounds_of_pair hR hp hC hB hc hτ hg⟩
end YangMills.Construction.TwoPoints.LineTransforms

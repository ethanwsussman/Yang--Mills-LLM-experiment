import YangMills.Construction.TwoPoints.FirstConsequencesOfThreeProperties
import YangMills.Construction.TwoPoints.RiemannSumsInTheSharpNorm
import YangMills.Construction.TwoPoints.SharpNormOfASuperposition
import YangMills.Construction.TwoPoints.TermsOfARiemannSum
import YangMills.Construction.TwoPoints.TranslationModulusOfAFunction
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace CubeSums
theorem sharpNorm_nonneg (S : FixedScale) (f : AmbientSpace → ℂ) : 0 ≤ S.sharpNorm f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem euclidNorm_nonneg (x : AmbientSpace) : 0 ≤ euclidNorm x := Real.sqrt_nonneg _
theorem exists_finset_gridCube_cover {δ : ℝ} (hδ : 0 < δ) {C : Set AmbientSpace}
    (hC : IsCompact C) :
    ∃ J : Finset (Fin 4 → ℤ), C ⊆ ⋃ j ∈ J, gridCube δ j := by
  obtain ⟨R, hR⟩ := hC.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_ge (R / δ + 1)
  have hN' : R + δ ≤ δ * N := by
    have h1 : (R / δ + 1) * δ ≤ N * δ := mul_le_mul_of_nonneg_right hN hδ.le
    have h2 : (R / δ + 1) * δ = R + δ := by field_simp
    linarith
  refine ⟨Finset.Icc (fun _ => -(N : ℤ)) (fun _ => (N : ℤ)), fun z hz => ?_⟩
  obtain ⟨j, hj, -⟩ := existsUnique_mem_gridCube hδ z
  have hb : ∀ μ, -(N : ℤ) ≤ j μ ∧ j μ ≤ (N : ℤ) := by
    intro μ
    have hzμ : |z μ| ≤ R := (norm_le_pi_norm z μ).trans (hR z hz)
    obtain ⟨a, b⟩ := hj μ
    obtain ⟨c, d⟩ := abs_le.1 hzμ
    have h1 : -(N : ℝ) ≤ (j μ : ℝ) := by
      by_contra hc
      replace hc := not_le.1 hc
      nlinarith [mul_lt_mul_of_pos_left hc hδ]
    have h2 : (j μ : ℝ) ≤ (N : ℝ) := by
      by_contra hc
      replace hc := not_le.1 hc
      nlinarith [mul_lt_mul_of_pos_left hc hδ]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  exact mem_iUnion₂.2 ⟨j, Finset.mem_Icc.2 ⟨fun μ => (hb μ).1, fun μ => (hb μ).2⟩, hj⟩
theorem isBounded_gridCube (δ : ℝ) (j : Fin 4 → ℤ) : Bornology.IsBounded (gridCube δ j) := by
  refine (isCompact_Icc (a := fun μ => δ * (j μ : ℝ))
    (b := fun μ => δ * ((j μ : ℝ) + 1))).isBounded.subset ?_
  intro z hz
  exact ⟨fun μ => (hz μ).1, fun μ => (hz μ).2.le⟩
theorem gridCube_pairwiseDisjoint {δ : ℝ} (hδ : 0 < δ) (J : Finset (Fin 4 → ℤ)) :
    Set.Pairwise (↑J) (Function.onFun Disjoint (gridCube δ)) := by
  intro i _ j _ hij
  exact Set.disjoint_left.2 fun z hi hj => hij ((existsUnique_mem_gridCube hδ z).unique hi hj)
theorem integral_eq_sum_gridCube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {δ : ℝ}
    (hδ : 0 < δ) (hm : ∀ j, MeasurableSet (gridCube δ j)) (J : Finset (Fin 4 → ℤ))
    {g : AmbientSpace → E} (hg : Integrable g)
    (h0 : ∀ z, z ∉ ⋃ j ∈ J, gridCube δ j → g z = 0) :
    ∫ z, g z = ∑ j ∈ J, ∫ z in gridCube δ j, g z := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h0,
    integral_biUnion_finset J (fun j _ => hm j) (gridCube_pairwiseDisjoint hδ J)
      (fun j _ => hg.integrableOn)]
theorem cubeRiemannSum_eq_finset_sum {δ : ℝ} (hδ : 0 < δ) {k φ : AmbientSpace → ℂ}
    {J : Finset (Fin 4 → ℤ)} (hJ : tsupport k ⊆ ⋃ j ∈ J, gridCube δ j) :
    cubeRiemannSum δ k φ =
      ∑ j ∈ J, setIntegralOf (gridCube δ j) k • translateFun (gridCenter δ j) φ := by
  unfold cubeRiemannSum
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra hjJ
  apply hj
  have hz : setIntegralOf (gridCube δ j) k = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
    refine image_eq_zero_of_notMem_tsupport fun hzk => hjJ ?_
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 (hJ hzk)
    have : i = j := (existsUnique_mem_gridCube hδ z).unique hzi hz
    exact this ▸ hi
  change setIntegralOf (gridCube δ j) k • translateFun (gridCenter δ j) φ = 0
  rw [hz, zero_smul]
theorem finset_sum_isBddLipschitz_sharpNorm_le (hConv : SharpNormSuperpositionBound.Statement)
    (S : FixedScale) (h0 : IsBddLipschitz 0) {ι : Type*} (J : Finset ι)
    (G : ι → AmbientSpace → ℂ) (c : ι → ℝ)
    (h : ∀ j ∈ J, IsBddLipschitz (G j) ∧ S.sharpNorm (G j) ≤ c j) :
    IsBddLipschitz (∑ j ∈ J, G j) ∧ S.sharpNorm (∑ j ∈ J, G j) ≤ ∑ j ∈ J, c j := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    have h1 := ((hConv S).2.1 0 0 h0).2
    simp only [zero_smul, norm_zero, zero_mul] at h1
    simpa using ⟨h0, h1.le⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    obtain ⟨b, bb⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨ga, gb⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨r1, r2⟩ := (hConv S).1 _ _ ga b
    exact ⟨r1, r2.trans (add_le_add gb bb)⟩
end CubeSums
open CubeSums in
theorem ConvolutionRiemannSumSharpEstimates.holds
    (hMod : TranslationModulusProperties.Statement)
    (hConv : SharpNormSuperpositionBound.Statement)
    (hTerms : RiemannSumTermProperties.Statement)
    (hFirst : AdmissibleFormConsequences.Statement) :
    ConvolutionRiemannSumSharpEstimates.Statement := by
  intro S k hk φ hφ δ hδ
  obtain ⟨hkc, hkZ, -⟩ := (mem_ccIn_iff _ _).1 hk
  have hφc : Continuous φ := hφ.1.continuous
  have hks : HasCompactSupport k := hkZ
  obtain ⟨Ck, hCk⟩ := hkc.bounded_above_of_compact_support hks
  have hkm : Measurable k := hkc.measurable
  have hBL : ∀ f ∈ compactC1Complex, IsBddLipschitz f := hFirst.2.2.1
  have h0 : IsBddLipschitz 0 := hBL 0 (Submodule.zero_mem _)
  have hMaps := (hFirst.2.2.2.1 S).1 φ hφ
  have hτ : ∀ v, translateFun v φ ∈ compactC1Complex := fun v => (hMaps.1 v).1.mem
  have hτs : ∀ v, S.sharpNorm (translateFun v φ) = S.sharpNorm φ :=
    fun v => (hMaps.1 v).1.sharpNorm_eq
  have hmono := (hMod S φ hφ).2
  have hdiff := (hMod S φ hφ).1.2.2.2.2.1
  have hd : ∀ v v', euclidNorm (v - v') ≤ δ →
      S.sharpNorm (translateFun v φ - translateFun v' φ) ≤ S.translationModulus φ δ :=
    fun v v' h => (hdiff v v').trans
      (hmono (mem_Ici.2 (euclidNorm_nonneg _)) (mem_Ici.2 hδ.le) h)
  have hterm := hTerms k hk φ hφ δ hδ
  have hm := hterm.1
  have hnear := hterm.2.1
  have hkint : Integrable k := hkc.integrable_of_hasCompactSupport hks
  have hint : ∀ G : AmbientSpace → ℂ, Continuous G → Integrable fun z => k z * G z :=
    fun G hG => (hkc.mul hG).integrable_of_hasCompactSupport (hks.mul_right (f' := G))
  have hsup : ∀ (Z : Set AmbientSpace) (c : AmbientSpace), MeasurableSet Z →
      Bornology.IsBounded Z → (∀ z ∈ Z, euclidNorm (z - c) ≤ δ) →
      IsBddLipschitz
          (fun x => setIntegralOf Z fun z => k z * (translateFun z φ - translateFun c φ) x) ∧
        S.sharpNorm
            (fun x => setIntegralOf Z fun z => k z * (translateFun z φ - translateFun c φ) x) ≤
          (∫ z in Z, ‖k z‖) * S.translationModulus φ δ := by
    intro Z c hZm hZb hZc
    have hcont : Continuous
        (Function.uncurry fun z : AmbientSpace => translateFun z φ - translateFun c φ) := by
      have : (Function.uncurry fun z : AmbientSpace => translateFun z φ - translateFun c φ) =
          fun p : AmbientSpace × AmbientSpace => φ (p.2 - p.1) - φ (p.2 - c) := rfl
      rw [this]
      fun_prop
    exact (hConv S).2.2 Z k (fun z => translateFun z φ - translateFun c φ) _ hZm hZb hkm
      ⟨Ck, fun z _ => hCk z⟩ hcont (fun z _ => hBL _ (Submodule.sub_mem _ (hτ z) (hτ c)))
      (fun z hz => hd z c (hZc z hz))
  obtain ⟨J, hJ⟩ := exists_finset_gridCube_cover hδ hkZ
  have hvan : ∀ z, z ∉ ⋃ j ∈ J, gridCube δ j → k z = 0 :=
    fun z hz => image_eq_zero_of_notMem_tsupport fun h => hz (hJ h)
  have hone : l1Norm k = ∫ z, ‖k z‖ :=
    (integral_norm_eq_lintegral_enorm hkm.aestronglyMeasurable).symm
  have hsumk : ∑ j ∈ J, ∫ z in gridCube δ j, ‖k z‖ = l1Norm k := by
    rw [hone]
    exact (integral_eq_sum_gridCube hδ hm J hkint.norm fun z hz => by
      rw [hvan z hz, norm_zero]).symm
  have hZk : ∫ z in tsupport k, ‖k z‖ = l1Norm k := by
    rw [hone]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
  have hTm : MeasurableSet (tsupport k) := (isClosed_tsupport k).measurableSet
  have hTb : Bornology.IsBounded (tsupport k) := hkZ.isBounded
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hdecomp : convolve k φ - cubeRiemannSum δ k φ =
        ∑ j ∈ J, fun x => setIntegralOf (gridCube δ j) fun z =>
          k z * (translateFun z φ - translateFun (gridCenter δ j) φ) x := by
      funext x
      rw [Pi.sub_apply, cubeRiemannSum_eq_finset_sum hδ hJ, Finset.sum_apply, Finset.sum_apply]
      have hx : Continuous fun z : AmbientSpace => φ (x - z) := by fun_prop
      have hconv : convolve k φ x = ∑ j ∈ J, ∫ z in gridCube δ j, k z * φ (x - z) :=
        integral_eq_sum_gridCube hδ hm J (hint _ hx) fun z hz => by rw [hvan z hz, zero_mul]
      rw [hconv, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h1 : setIntegralOf (gridCube δ j)
            (fun z => k z * (translateFun z φ - translateFun (gridCenter δ j) φ) x) =
          ∫ z in gridCube δ j, (k z * φ (x - z) - k z * φ (x - gridCenter δ j)) := by
        simp only [setIntegralOf, integralWrt, Pi.sub_apply, translateFun, mul_sub]
      rw [h1, integral_sub (hint _ hx).integrableOn (hkint.mul_const _).integrableOn,
        integral_mul_const]
      rfl
    have hG := finset_sum_isBddLipschitz_sharpNorm_le hConv S h0 J
      (fun j x => setIntegralOf (gridCube δ j) fun z =>
        k z * (translateFun z φ - translateFun (gridCenter δ j) φ) x)
      (fun j => (∫ z in gridCube δ j, ‖k z‖) * S.translationModulus φ δ)
      (fun j _ => hsup _ _ (hm j) (isBounded_gridCube δ j) (hnear j))
    rw [hdecomp]
    refine hG.2.trans (le_of_eq ?_)
    rw [← Finset.sum_mul, hsumk]
  · have hG := finset_sum_isBddLipschitz_sharpNorm_le hConv S h0 J
      (fun j => setIntegralOf (gridCube δ j) k • translateFun (gridCenter δ j) φ)
      (fun j => (∫ z in gridCube δ j, ‖k z‖) * S.sharpNorm φ)
      (fun j _ => by
        obtain ⟨b, e⟩ := (hConv S).2.1 (setIntegralOf (gridCube δ j) k)
          (translateFun (gridCenter δ j) φ) (hBL _ (hτ _))
        refine ⟨b, ?_⟩
        rw [e, hτs]
        exact mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _)
          (sharpNorm_nonneg S φ))
    rw [cubeRiemannSum_eq_finset_sum hδ hJ]
    refine hG.2.trans (le_of_eq ?_)
    rw [← Finset.sum_mul, hsumk]
  · have hc3 : convolve k φ =
        fun x => setIntegralOf (tsupport k) fun z => k z * translateFun z φ x := by
      funext x
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]).symm
    have hcont : Continuous (Function.uncurry fun z : AmbientSpace => translateFun z φ) := by
      have : (Function.uncurry fun z : AmbientSpace => translateFun z φ) =
          fun p : AmbientSpace × AmbientSpace => φ (p.2 - p.1) := rfl
      rw [this]
      fun_prop
    have hr := (hConv S).2.2 (tsupport k) k (fun z => translateFun z φ) (S.sharpNorm φ) hTm hTb
      hkm ⟨Ck, fun z _ => hCk z⟩ hcont (fun z _ => hBL _ (hτ z)) (fun z _ => (hτs z).le)
    rw [hc3]
    rw [hZk] at hr
    exact hr.2
  · intro hnn hk1 hsupp
    have hkre : ∀ z, k z = ((‖k z‖ : ℝ) : ℂ) := by
      intro z
      have e : k z = (((k z).re : ℝ) : ℂ) := Complex.ext rfl (by simp [(hnn z).1])
      have hn : ‖k z‖ = (k z).re := by
        conv_lhs => rw [e]
        rw [Complex.norm_real, Real.norm_of_nonneg (hnn z).2]
      rw [hn]
      exact e
    have hn1 : l1Norm k = 1 := by
      rw [hone]
      have h2 : (((∫ z, ‖k z‖ : ℝ)) : ℂ) = 1 := by
        calc (((∫ z, ‖k z‖ : ℝ)) : ℂ) = ∫ z, ((‖k z‖ : ℝ) : ℂ) := integral_ofReal.symm
          _ = ∫ z, k z := integral_congr_ae (ae_of_all _ fun z => (hkre z).symm)
          _ = 1 := hk1
      exact_mod_cast h2
    have hT1 : ∫ z in tsupport k, k z = 1 := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
        image_eq_zero_of_notMem_tsupport hz]
      exact hk1
    have hc4 : convolve k φ - φ = fun x => setIntegralOf (tsupport k) fun z =>
        k z * (translateFun z φ - translateFun 0 φ) x := by
      funext x
      have hx : Continuous fun z : AmbientSpace => φ (x - z) := by fun_prop
      have h1 : setIntegralOf (tsupport k)
            (fun z => k z * (translateFun z φ - translateFun 0 φ) x) =
          ∫ z in tsupport k, (k z * φ (x - z) - k z * φ (x - 0)) := by
        simp only [setIntegralOf, integralWrt, Pi.sub_apply, translateFun, mul_sub]
      have h2 : convolve k φ x = ∫ z in tsupport k, k z * φ (x - z) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
          rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]).symm
      rw [h1, integral_sub (hint _ hx).integrableOn (hkint.mul_const _).integrableOn,
        integral_mul_const, hT1, Pi.sub_apply, h2, sub_zero, one_mul]
    have hr := hsup (tsupport k) 0 hTm hTb fun z hz => hsupp hz
    rw [hc4]
    rw [hZk, hn1, one_mul] at hr
    exact hr.2
end YangMills.Construction.TwoPoints
end

import YangMills.Construction.TransferOperators.ComponentFunctionsOfTheProjections
import YangMills.Construction.TransferOperators.ComponentsOfAProductWithAPolynomial
import YangMills.Construction.TransferOperators.HatIsLinearAndKeepsRealFunctionsProof
import YangMills.Construction.TransferOperators.PartProjectionOnProductCoefficientSpaces
import YangMills.Construction.TransferOperators.SmoothFunctionsDecayRapidly
import YangMills.Construction.TransferOperators.TermsOfTheOperatorHatAsSeriesOfDoubleTerms
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics
section ContinuousMaps
variable {J : Type} [Finite J]
theorem partIsotypicProjC_apply (B : Set J) (l : ↥B → HalfNatural)
    (F : C(J → specialUnitary, ℂ)) (u : J → specialUnitary) :
    partIsotypicProjC B l F u = ∫ w, isotypicKernel l (restrictTo B u) w *
      F (glue B w (restrictTo Bᶜ u)) ∂haarPi ↥B := rfl
theorem integrable_partKernelIntegrand (B : Set J) (l : ↥B → HalfNatural)
    (F : C(J → specialUnitary, ℂ)) (u : J → specialUnitary) :
    Integrable (fun w => isotypicKernel l (restrictTo B u) w *
      F (glue B w (restrictTo Bᶜ u))) (haarPi ↥B) := by apply _root_.YangMills.Construction.SpinHarmonics.HatLinearReal.integrable_isotypicIntegrand <;> assumption
theorem exists_clm_partIsotypicProjC (B : Set J) (l : ↥B → HalfNatural) :
    ∃ T : C(J → specialUnitary, ℂ) →L[ℂ] C(J → specialUnitary, ℂ),
      ∀ F, T F = partIsotypicProjC B l F := by
  let K : C((↥B → specialUnitary) × (↥B → specialUnitary), ℂ) :=
    ⟨_, continuous_isotypicKernel l⟩
  let L : C(J → specialUnitary, ℂ) →ₗ[ℂ] C(J → specialUnitary, ℂ) :=
    { toFun := partIsotypicProjC B l
      map_add' := fun F H => by
        ext u
        simp only [ContinuousMap.add_apply, partIsotypicProjC_apply, mul_add]
        exact integral_add (integrable_partKernelIntegrand B l F u)
          (integrable_partKernelIntegrand B l H u)
      map_smul' := fun a F => by
        ext u
        simp only [ContinuousMap.smul_apply, partIsotypicProjC_apply, RingHom.id_apply,
          smul_eq_mul]
        rw [← integral_const_mul]
        congr 1
        funext w
        ring }
  refine ⟨L.mkContinuous ‖K‖ fun F => ?_, fun F => rfl⟩
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun u => ?_
  have hbound : ∀ᵐ w ∂haarPi ↥B, ‖isotypicKernel l (restrictTo B u) w *
      F (glue B w (restrictTo Bᶜ u))‖ ≤ ‖K‖ * ‖F‖ := by
    refine Eventually.of_forall fun w => ?_
    rw [norm_mul]
    exact mul_le_mul (K.norm_coe_le_norm (restrictTo B u, w)) (F.norm_coe_le_norm _)
      (norm_nonneg _) (norm_nonneg _)
  exact show ‖∫ w, isotypicKernel l (restrictTo B u) w *
      F (glue B w (restrictTo Bᶜ u)) ∂haarPi ↥B‖ ≤ ‖K‖ * ‖F‖ from by
    simpa using norm_integral_le_of_norm_le_const hbound
omit [Finite J] in
theorem exists_clm_mulPullback (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) :
    ∃ T : C(J → specialUnitary, ℂ) →L[ℂ] C(J → specialUnitary, ℂ),
      ∀ F, T F = mulPullback B f hf F :=
  ⟨ContinuousLinearMap.mul ℂ C(J → specialUnitary, ℂ)
    ⟨pullFromPart B f, hf.1.continuous.comp (continuous_restrictTo B)⟩, fun _ => rfl⟩
omit [Finite J] in
theorem restrictTo_glue {A : Type*} (B : Set J) (v : ↥B → A) (z : ↥Bᶜ → A) :
    restrictTo B (glue B v z) = v :=
  congrArg Prod.fst ((splitEquiv B).right_inv (v, z))
omit [Finite J] in
theorem restrictTo_compl_glue {A : Type*} (B : Set J) (v : ↥B → A) (z : ↥Bᶜ → A) :
    restrictTo Bᶜ (glue B v z) = z :=
  congrArg Prod.snd ((splitEquiv B).right_inv (v, z))
end ContinuousMaps
theorem hatTermAsDoubleSeries
    (hC : IsotypicPartSums.Statement)
    (hS : SmoothToSobolevDecayStatement)
    (hP : PartProjOnProdCoeffSpanStatement)
    (hM : MulPullbackComponents.Statement) :
    HatTermAsDoubleSeriesStatement := by
  intro J _ _ β B f hf D F l l' _ hB hD hF
  classical
  obtain ⟨P, hPl⟩ := exists_clm_partIsotypicProjC B l
  obtain ⟨P', hPl'⟩ := exists_clm_partIsotypicProjC B l'
  obtain ⟨T, hT⟩ := exists_clm_mulPullback B f hf
  let c : (J → HalfNatural) → C(J → specialUnitary, ℂ) := fun lam =>
    isotypicPartSum lam (toHaarL2 (F : (J → specialUnitary) → ℂ))
  have hmem : ∀ lam, c lam ∈ prodCoeffSpan lam := fun lam => ((hC J).1 lam _).1
  have hsum : HasSum c F := by
    have h := ((hS J) F hF).2
    have hfun : ∀ lam, isotypicPart lam (toHaarL2 (F : (J → specialUnitary) → ℂ)) =
        ⇑(c lam) := fun lam => ((hC J).1 lam _).2.1.symm
    unfold HasUniformSum at h
    simp only [hfun] at h
    rw [HasSum, SummationFilter.unconditional_filter,
      ContinuousMap.tendsto_iff_tendstoUniformly]
    simpa only [ContinuousMap.coe_sum, Finset.sum_apply] using h
  have hsumB : HasSum (fun k : ↥Bᶜ → HalfNatural => c (glue B l k)) (P F) := by
    have h₁ := P.hasSum hsum
    have hinj : Function.Injective (glue (X := HalfNatural) B l) := fun k k' h => by
      have h₂ := congrArg (restrictTo Bᶜ) h
      rwa [restrictTo_compl_glue, restrictTo_compl_glue] at h₂
    have hz : ∀ lam, lam ∉ Set.range (glue (X := HalfNatural) B l) → P (c lam) = 0 := by
      intro lam hlam
      rw [hPl]
      refine (hP J B lam (c lam) l hB (hmem lam)).2 fun h => hlam ⟨restrictTo Bᶜ lam, ?_⟩
      rw [h]
      exact (splitEquiv B).left_inv lam
    have h₂ := (hinj.hasSum_iff hz).2 h₁
    have h₃ : ((fun lam => P (c lam)) ∘ glue (X := HalfNatural) B l) =
        fun k => c (glue B l k) := by
      funext k
      simp only [Function.comp_apply]
      rw [hPl]
      exact (hP J B _ _ l hB (hmem _)).1 (restrictTo_glue B l k).symm
    rwa [h₃] at h₂
  have hterm : ∀ k : ↥Bᶜ → HalfNatural, P' (T (c (glue B l k))) =
      isotypicPartSum (glue B l' k) (toHaarL2
        (mulPullback B f hf (c (glue B l k)) : (J → specialUnitary) → ℂ)) := by
    intro k
    obtain ⟨hfin, hnear, hpt⟩ := hM J B f hf D (glue B l k) _ hB hD (hmem _)
    rw [hT]
    generalize mulPullback B f hf (c (glue B l k)) = ψ at hfin hnear hpt
    have hψ : ψ = ∑ lam' ∈ hfin.toFinset, isotypicPartSum lam'
        (toHaarL2 (ψ : (J → specialUnitary) → ℂ)) := by
      ext u
      refine (hpt u).trans ?_
      rw [ContinuousMap.coe_sum, Finset.sum_apply]
      refine tsum_eq_sum fun lam' h => ?_
      have h₀ : isotypicPartSum lam' (toHaarL2 (ψ : (J → specialUnitary) → ℂ)) = 0 := by
        by_contra h'
        exact h (hfin.mem_toFinset.2 h')
      simp [h₀]
    have hcomp : ∀ lam', isotypicPartSum lam' (toHaarL2 (ψ : (J → specialUnitary) → ℂ)) ∈
        prodCoeffSpan lam' := fun lam' => ((hC J).1 lam' _).1
    have hone : P' (isotypicPartSum (glue B l' k)
        (toHaarL2 (ψ : (J → specialUnitary) → ℂ))) =
        isotypicPartSum (glue B l' k) (toHaarL2 (ψ : (J → specialUnitary) → ℂ)) := by
      rw [hPl']
      exact (hP J B _ _ l' hB (hcomp _)).1 (restrictTo_glue B l' k).symm
    have hsplit : P' ψ = ∑ lam' ∈ hfin.toFinset, P' (isotypicPartSum lam'
        (toHaarL2 (ψ : (J → specialUnitary) → ℂ))) := by
      conv_lhs => rw [hψ]
      exact map_sum P' _ _
    rw [hsplit, Finset.sum_eq_single (glue B l' k), hone]
    · intro lam' hlam' hne
      rw [hPl']
      refine (hP J B lam' _ l' hB (hcomp lam')).2 fun h => hne ?_
      have hout := (hnear lam' (hfin.mem_toFinset.1 hlam')).1
      funext b
      by_cases hb : b ∈ B
      · rw [show glue B l' k b = l' ⟨b, hb⟩ from glue_of_mem B l' k ⟨b, hb⟩, h]
        rfl
      · rw [hout b hb, show glue B l k b = k ⟨b, hb⟩ from
          glue_of_notMem B l k ⟨b, hb⟩, show glue B l' k b = k ⟨b, hb⟩ from
          glue_of_notMem B l' k ⟨b, hb⟩]
    · intro hnot
      have h₀ : isotypicPartSum (glue B l' k)
          (toHaarL2 (ψ : (J → specialUnitary) → ℂ)) = 0 := by
        by_contra h'
        exact hnot (hfin.mem_toFinset.2 h')
      rw [h₀, map_zero]
  have hfinal := (P'.hasSum (T.hasSum hsumB)).const_smul (charCoeffRatio β l l')
  have he : hatSeriesTerm β B f hf F (l, l') = charCoeffRatio β l l' • P' (T (P F)) := by
    simp only [hatSeriesTerm, hatSummand, hPl, hPl', hT]
  rw [he]
  have hk : (fun k : ↥Bᶜ → HalfNatural =>
      hatDoubleTerm β B f hf F (glue B l' k) (glue B l k)) =
      fun k => charCoeffRatio β l l' • P' (T (c (glue B l k))) := by
    funext k
    rw [hterm k, hatDoubleTerm, restrictTo_glue, restrictTo_glue]
  rw [hk]
  exact hfinal
end YangMills.Construction.SpinHarmonics
end

import YangMills.Construction.Continuum.PartitionOfUnityAndCutoffOfClassC1
import YangMills.Construction.EuclideanFunctionals.CalculusOfEnergyAndMomentumInMatrixElements
import YangMills.Construction.EuclideanFunctionals.RaisingContractsAnInsertionMovedInTimeAndThePlateBoundAtEveryFractionProof
import YangMills.Construction.RotationInvariance.PlaneDataAreDataOfTheTwoSettings
import YangMills.Construction.RotationInvariance.RulesOfTheTranslationsAndMotionsOfPlates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane MeasureTheory
open scoped ComplexConjugate
namespace EuclideanFunctionals.FractionChange
open ForwardTube
open AboveHeight (IsThinInsert)
open TranslationRules (MotionsOnPlaneFactor ProductFunctionsInC1c)
theorem finCombIn_mono {U U' : Set R4} (hsub : U ⊆ U') :
    finCombIn U ≤ finCombIn U' := by apply _root_.YangMills.Construction.EuclideanFunctionals.HeightTuples.finCombIn_mono <;> assumption
theorem transl_actFree_mem (hT : TupleRules.TupleSpanActionRules) {c : ℝ} (a : ℝ) {F : FreeSep}
    (hF : F ∈ finCombIn {x : R4 | c < x 3}) :
    (EuclidMotion.transl (a • timeVec)).actFree F ∈ finCombIn {x : R4 | c + a < x 3} := by apply _root_.YangMills.Construction.EuclideanFunctionals.TimeShiftAndFractions.actFree_transl_mem <;> assumption
theorem insertion_eq_transl (hT : TupleRules.TupleSpanActionRules) {S : ConnFamily}
    (hInv : MomentSymmetry.MotionInvariant S) {c : ℝ}
    (hc : 0 < c) {F A : FreeSep} (hF : F ∈ finCombIn {x : R4 | c < x 3})
    (hA : A ∈ finCombIn {x : R4 | c < x 3}) {h : R4 → ℂ} (hh : IsThinInsert c h)
    (a : ℝ) :
    insertion S F h A =
      insertion S ((EuclidMotion.transl (a • timeVec)).actFree F)
        ((EuclidMotion.transl ((-a) • timeVec)).actFn h)
        ((EuclidMotion.transl ((-a) • timeVec)).actFree A) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TimeShiftAndFractions.insertion_eq_transl <;> assumption
theorem heightNorm_nonneg {m : SharpScale} {S : ConnFamily}
    (σ : EuclidFunctionalWithRecon m S) (c : ℝ) (F : FreeSep) :
    0 ≤ heightNorm σ c F :=
  norm_nonneg _
theorem heightNorm_transl_le (hT : TupleRules.TupleSpanActionRules)
    (hCalc : HamMomMatrixCalculus) {m : SharpScale} {S : ConnFamily}
    (σ : EuclidFunctionalWithRecon m S) {a c c' t : ℝ} (ht : 0 ≤ t)
    (hat : a - c' = t - c) {F : FreeSep} (hF : F ∈ finCombIn {x : R4 | c < x 3}) :
    heightNorm σ c' ((EuclidMotion.transl (a • timeVec)).actFree F) ≤ heightNorm σ c F := by
  have hG : pullDown c F ∈ finCombIn upperHalf := by
    have h := transl_actFree_mem hT (-c) hF
    refine finCombIn_mono ?_ h
    intro x hx
    have hx' : c + -c < x 3 := hx
    show 0 < x 3
    linarith
  have hAct := hT.2.2.1
  have hEq : pullDown c' ((EuclidMotion.transl (a • timeVec)).actFree F) =
      (EuclidMotion.transl (t • timeVec)).actFree (pullDown c F) := by
    unfold pullDown
    rw [(hAct _ _ F).1, (hAct _ _ F).1]
    congr 2
    refine EuclidMotion.ext_of_apply fun x => ?_
    rw [EuclidMotion.mul_apply, EuclidMotion.mul_apply, EuclidMotion.transl_apply,
      EuclidMotion.transl_apply, EuclidMotion.transl_apply, EuclidMotion.transl_apply,
      add_assoc, add_assoc, ← add_smul, ← add_smul]
    congr 2
    linarith
  have hExp := σ.recon.expHam_cls t ht ⟨pullDown c F, hG⟩
  have hContr : ‖σ.heatSemigroup t‖ ≤ 1 :=
    ((hCalc m S σ 0 0).2.2 t ht 0 le_rfl 0).2.1
  have hClass : reconClass σ (pullDown c F) =
      σ.recon.cls ⟨pullDown c F, hG⟩ := dif_pos hG
  unfold heightNorm
  rw [hEq, hClass]
  show ‖readClass σ.recon.cls _‖ ≤ _
  rw [← hExp]
  calc ‖ResolvedOps.expComplex σ.recon.ham (t : ℂ)
          (σ.recon.cls ⟨pullDown c F, hG⟩)‖
      ≤ ‖σ.heatSemigroup t‖ * ‖σ.recon.cls ⟨pullDown c F, hG⟩‖ :=
        ContinuousLinearMap.le_opNorm (σ.heatSemigroup t) _
    _ ≤ 1 * ‖σ.recon.cls ⟨pullDown c F, hG⟩‖ :=
        mul_le_mul_of_nonneg_right hContr (norm_nonneg _)
    _ = _ := one_mul _
theorem mul_mem_complexProfiles {ψ : RealPlane → ℝ} (hψ : ContDiff ℝ 1 ψ) {α : RealPlane → ℂ}
    (hα : α ∈ complexProfiles) : (fun y => (ψ y : ℂ) * α y) ∈ complexProfiles :=
  ⟨(Complex.ofRealCLM.contDiff.comp hψ).mul hα.1, hα.2.mul_left⟩
theorem tsupport_mul_subset (ψ : RealPlane → ℝ) (α : RealPlane → ℂ) :
    tsupport (fun y => (ψ y : ℂ) * α y) ⊆ tsupport α :=
  closure_mono fun y hy => fun h0 => hy (by simp [h0])
theorem productFunction_isThinInsert
    (hProd : ProductFunctionsInC1c) {c' η : ℝ} (hc' : c' < 1 / 4) (hη : 0 < η)
    {β : RealPlane → ℂ} (hβ : β ∈ complexProfiles) (hs : tsupport β ⊆ planeStrip c' η)
    {φ : RealPlane → ℝ} (hφ : φ ∈ realLabels) : IsThinInsert (η / 4) (productFunction β φ) := by
  refine ⟨(hProd β hβ φ hφ).1, fun x hx => ?_⟩
  have h1 : |planeComponent x 0| < c' * η := hs ((hProd β hβ φ hφ).2 hx).1
  have h2 : planeComponent x 0 = x 3 := by simp [planeComponent]
  rw [h2] at h1
  show |x 3| < η / 4
  nlinarith
theorem insertion_finsetSum {ι : Type*} {S : ConnFamily} {c : ℝ}
    (hLin : AboveHeight.LinearInsert S c) {F A : FreeSep}
    (hF : F ∈ finCombIn {x : R4 | c < x 3}) (hA : A ∈ finCombIn {x : R4 | c < x 3})
    {α : RealPlane → ℂ} {φ : RealPlane → ℝ}
    (hentry : ∀ ψ : RealPlane → ℝ, ContDiff ℝ 1 ψ →
      IsThinInsert c (productFunction (fun y => (ψ y : ℂ) * α y) φ))
    (ψ : ι → RealPlane → ℝ) (hψ : ∀ k, ContDiff ℝ 1 (ψ k)) (J : Finset ι) :
    insertion S F (productFunction (fun y => ((∑ k ∈ J, ψ k y : ℝ) : ℂ) * α y) φ) A =
      ∑ k ∈ J, insertion S F (productFunction (fun y => (ψ k y : ℂ) * α y) φ) A := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    have h0 := hentry (fun _ => 0) contDiff_const
    have h := hLin F hF A hA _ h0 _ h0 0 0
    have hz : productFunction (fun y => ((∑ k ∈ (∅ : Finset ι), ψ k y : ℝ) : ℂ) * α y) φ = fun _ => 0 := by
      funext x
      simp [productFunction]
    rw [hz, Finset.sum_empty]
    simpa using h
  | insert a J ha ih =>
    have hJ : ContDiff ℝ 1 (fun y => ∑ k ∈ J, ψ k y) :=
      ContDiff.sum fun k _ => hψ k
    have h := hLin F hF A hA _ (hentry _ (hψ a)) _ (hentry _ hJ) 1 1
    rw [Finset.sum_insert ha, ← ih]
    simp only [one_mul] at h
    rw [← h]
    congr 1
    funext x
    simp only [productFunction, Finset.sum_insert ha]
    push_cast
    ring
section
variable {m : SharpScale} {S : ConnFamily} {σ : EuclidFunctionalWithRecon m S}
theorem insertion_piece_le (hT : TupleRules.TupleSpanActionRules)
    (hCalc : HamMomMatrixCalculus)
    (hMot : MotionsOnPlaneFactor)
    (hRule : TranslationRules.TranslationLaws)
    (hInv : MomentSymmetry.MotionInvariant S)
    {p c c' : ℝ} {C : (RealPlane → ℝ) → ℝ} (h : ProductBoundHolds σ p C c)
    (hc' : c' ∈ productBoundFractions) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {s b : ℝ}
    (hs : |s| < c' * η) (hb : b < c * ((1 - 4 * c') * η))
    {β : RealPlane → ℂ} (hβ : β ∈ complexProfiles)
    (hnear : ∀ y ∈ tsupport β, |y 0 - s| ≤ b)
    {φ : RealPlane → ℝ} (hφ : φ ∈ realLabels) (hentry : IsThinInsert (η / 4) (productFunction β φ))
    {F A : FreeSep} (hF : F ∈ finCombIn {y : R4 | η / 4 < y 3})
    (hA : A ∈ finCombIn {y : R4 | η / 4 < y 3}) :
    ‖insertion S F (productFunction β φ) A‖ ≤
      C φ * ((1 - 4 * c') * η) ^ (-p) * profileL1Norm β * heightNorm σ (η / 4) F *
        heightNorm σ (η / 4) A := by
  have hc'1 : c' < 1 / 4 := hc'.2
  have hp : 0 < p := h.pos_exponent
  have hc0 : 0 < c := h.pos_fraction
  have hη₁ : 0 < (1 - 4 * c') * η := mul_pos (by linarith) hη0
  set ηs : ℝ := η - 4 * |s| with hηs
  have hηs1 : (1 - 4 * c') * η < ηs := by rw [hηs]; nlinarith
  have hηs0 : 0 < ηs := hη₁.trans hηs1
  have hηsle : ηs ≤ 1 := by rw [hηs]; linarith [abs_nonneg s]
  set y' : RealPlane := (-s) • unitX with hy'
  obtain ⟨hτ, -, -, hprof, -, -⟩ := hMot β hβ φ hφ y' 0
  have hplane : planeShift y' = EuclidMotion.transl ((-s) • timeVec) :=
    (hRule.2.2.2 (-s)).1
  rw [hplane] at hτ
  have hy0 : ∀ y : RealPlane, (y - y') 0 = y 0 + s := fun y => by
    simp [hy', unitX]
  have hstrip : tsupport (translateProfile y' β) ⊆ planeStrip c ηs := by
    have hcl : IsClosed ((fun y : RealPlane => y - y') ⁻¹' tsupport β) :=
      (isClosed_tsupport β).preimage (continuous_id.sub continuous_const)
    have hsub : tsupport (translateProfile y' β) ⊆
        (fun y : RealPlane => y - y') ⁻¹' tsupport β :=
      closure_minimal (fun y hy => subset_tsupport β hy) hcl
    intro y hy
    have h1 := hnear _ (hsub hy)
    rw [hy0, add_sub_cancel_right] at h1
    show |y 0| < c * ηs
    have h2 : c * ((1 - 4 * c') * η) < c * ηs := mul_lt_mul_of_pos_left hηs1 hc0
    linarith
  have hs' : ηs / 4 = η / 4 - |s| := by rw [hηs]; ring
  have hF' : (EuclidMotion.transl (s • timeVec)).actFree F ∈ finCombIn {y : R4 | ηs / 4 < y 3} := by
    refine finCombIn_mono (fun x hx => ?_) (transl_actFree_mem hT s hF)
    have hx' : η / 4 + s < x 3 := hx
    show ηs / 4 < x 3
    linarith [neg_abs_le s]
  have hA' : (EuclidMotion.transl ((-s) • timeVec)).actFree A ∈
      finCombIn {y : R4 | ηs / 4 < y 3} := by
    refine finCombIn_mono (fun x hx => ?_) (transl_actFree_mem hT (-s) hA)
    have hx' : η / 4 + -s < x 3 := hx
    show ηs / 4 < x 3
    linarith [le_abs_self s]
  have hNF : heightNorm σ (ηs / 4) ((EuclidMotion.transl (s • timeVec)).actFree F) ≤
      heightNorm σ (η / 4) F :=
    heightNorm_transl_le hT hCalc σ (t := |s| + s) (by linarith [neg_abs_le s])
      (by rw [hs']; ring) hF
  have hNA : heightNorm σ (ηs / 4) ((EuclidMotion.transl ((-s) • timeVec)).actFree A) ≤
      heightNorm σ (η / 4) A :=
    heightNorm_transl_le hT hCalc σ (t := |s| - s) (by linarith [le_abs_self s])
      (by rw [hs']; ring) hA
  have hnorm : profileL1Norm (translateProfile y' β) = profileL1Norm β :=
    integral_sub_right_eq_self (fun y => ‖β y‖) y'
  have hbound := h.le_bound ηs hηs0 hηsle φ hφ _ hprof hstrip _ hF' _ hA'
  rw [insertion_eq_transl hT hInv (by linarith : (0 : ℝ) < η / 4) hF hA hentry s, hτ]
  refine hbound.trans ?_
  rw [hnorm]
  have hC : 0 ≤ C φ := h.nonneg_constant φ hφ
  have hpow : ηs ^ (-p) ≤ ((1 - 4 * c') * η) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hη₁ hηs1.le (by linarith)
  have hβn : 0 ≤ profileL1Norm β := integral_nonneg fun _ => norm_nonneg _
  have hN1 := heightNorm_nonneg σ (ηs / 4) ((EuclidMotion.transl (s • timeVec)).actFree F)
  have hN2 := heightNorm_nonneg σ (ηs / 4) ((EuclidMotion.transl ((-s) • timeVec)).actFree A)
  have hpos' : 0 ≤ ((1 - 4 * c') * η) ^ (-p) := Real.rpow_nonneg hη₁.le _
  have hb0 : 0 ≤ C φ * ((1 - 4 * c') * η) ^ (-p) * profileL1Norm β * heightNorm σ (η / 4) F :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hpos') hβn) (heightNorm_nonneg σ _ _)
  gcongr
end
theorem abs_apply_zero_le_sqrtSumSq (x : Fin 2 → ℝ) : |x 0| ≤ EuclideanCoords.sqrtSumSq x := by
  refine Real.abs_le_sqrt ?_
  rw [Fin.sum_univ_two]
  nlinarith [sq_nonneg (x 1)]
theorem sum_profileL1Norm {ι : Type*} (J : Finset ι) (ψ : ι → RealPlane → ℝ)
    (hψ : ∀ k, ContDiff ℝ 1 (ψ k)) (hψ0 : ∀ k y, 0 ≤ ψ k y) {α : RealPlane → ℂ}
    (hα : α ∈ complexProfiles) (hone : ∀ y, α y ≠ 0 → ∑ k ∈ J, ψ k y = 1) :
    ∑ k ∈ J, profileL1Norm (fun y => (ψ k y : ℂ) * α y) = profileL1Norm α := by
  have hint : ∀ k ∈ J, Integrable (fun y => ‖(ψ k y : ℂ) * α y‖) := fun k _ =>
    (integrable_of_mem_complexProfiles (mul_mem_complexProfiles (hψ k) hα)).norm
  unfold profileL1Norm
  rw [← integral_finsetSum J hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ∑ k ∈ J, ‖(ψ k y : ℂ) * α y‖ = ‖α y‖
  by_cases h0 : α y = 0
  · simp [h0]
  · have : ∀ k ∈ J, ‖(ψ k y : ℂ) * α y‖ = ψ k y * ‖α y‖ := fun k _ => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψ0 k y)]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, hone y h0, one_mul]
section
variable {m : SharpScale} {S : ConnFamily} {σ : EuclidFunctionalWithRecon m S}
theorem productBound_of_fraction
    (hCut : PartitionOfUnity.C1PartitionAndCutoffExist)
    (hT : TupleRules.TupleSpanActionRules)
    (hCalc : HamMomMatrixCalculus)
    (hRules : TranslationRules.TranslationAndMotionFacts)
    (hPull : AboveHeight.Holds)
    (hInv : MomentSymmetry.MotionInvariant S)
    {p c c' : ℝ} {C : (RealPlane → ℝ) → ℝ} (h : ProductBoundHolds σ p C c)
    (hc' : c' ∈ productBoundFractions) :
    ProductBoundHolds σ p (productConstantsAt p c' C) c' := by
  have hc'0 : 0 < c' := hc'.1
  have hc'1 : c' < 1 / 4 := hc'.2
  have hbase : 0 < 1 - 4 * c' := by linarith
  refine ⟨h.pos_exponent, fun φ hφ => ?_, hc'0, hc'1, ?_⟩
  · exact mul_nonneg (Real.rpow_nonneg hbase.le _) (h.nonneg_constant φ hφ)
  intro η hη0 hη1 φ hφ α hα hsupp F hF A hA
  have hc0 : 0 < c := h.pos_fraction
  have hη₁ : 0 < (1 - 4 * c') * η := mul_pos hbase hη0
  have hε : 0 < c * ((1 - 4 * c') * η) / 8 := by positivity
  obtain ⟨χ, hχC, hχI, hχD, hχF, hχS⟩ := hCut.1 2 (Or.inl rfl) _ hε
  let e := EuclideanSpace.equiv (Fin 2) ℝ
  let K : (Fin 2 → ℤ) → RealPlane → ℝ := fun k y => χ k (e y)
  have hK : ∀ k, ContDiff ℝ 1 (K k) := fun k => (hχC k).1.comp e.contDiff
  have hK0 : ∀ k y, 0 ≤ K k y := fun k y => (hχI k _).1
  have hB : Bornology.IsBounded (e '' tsupport α) :=
    (hα.2.image e.continuous).isBounded
  let J : Finset (Fin 2 → ℤ) := (hχF _ hB).toFinset
  have hJ : ∀ k, k ∈ J ↔ (tsupport (χ k) ∩ e '' tsupport α).Nonempty := fun k => by
    simp [J]
  have hone : ∀ y, α y ≠ 0 → ∑ k ∈ J, K k y = 1 := by
    intro y hy
    have hout : ∀ k ∉ J, χ k (e y) = 0 := by
      intro k hk
      by_contra hne
      exact hk ((hJ k).2 ⟨e y, subset_tsupport _ hne,
        ⟨y, subset_tsupport _ hy, rfl⟩⟩)
    exact (hasSum_sum_of_ne_finset_zero hout).unique (hχS (e y))
  have hsum : (fun y => ((∑ k ∈ J, K k y : ℝ) : ℂ) * α y) = α := by
    funext y
    by_cases h0 : α y = 0
    · simp [h0]
    · rw [hone y h0]
      simp
  have hpos : (0 : ℝ) < η / 4 := by linarith
  have hLin := (hPull m S σ (η / 4) hpos).2.2.1
  have hentry : ∀ ψ : RealPlane → ℝ, ContDiff ℝ 1 ψ →
      IsThinInsert (η / 4) (productFunction (fun y => (ψ y : ℂ) * α y) φ) := fun ψ hψ =>
    productFunction_isThinInsert hRules.2.2.1 hc'1 hη0 (mul_mem_complexProfiles hψ hα)
      ((tsupport_mul_subset ψ α).trans hsupp) hφ
  have hsplit := insertion_finsetSum hLin hF hA hentry K hK J
  rw [hsum] at hsplit
  have hpiece : ∀ k ∈ J,
      ‖insertion S F (productFunction (fun y => (K k y : ℂ) * α y) φ) A‖ ≤
        C φ * ((1 - 4 * c') * η) ^ (-p) * profileL1Norm (fun y => (K k y : ℂ) * α y) *
          heightNorm σ (η / 4) F * heightNorm σ (η / 4) A := by
    intro k hk
    obtain ⟨z, hz, y₀, hy₀, rfl⟩ := (hJ k).1 hk
    have hs : |y₀ 0| < c' * η := hsupp hy₀
    have hsub : tsupport (fun y => (K k y : ℂ) * α y) ⊆ e ⁻¹' tsupport (χ k) :=
      closure_minimal (fun y hy => subset_tsupport _ fun h0 => hy (by simp [K, h0]))
        ((isClosed_tsupport _).preimage e.continuous)
    refine insertion_piece_le hT hCalc hRules.2.1 hRules.1 hInv h hc' hη0 hη1 hs
      (b := 4 * (c * ((1 - 4 * c') * η) / 8)) (by nlinarith [mul_pos hc0 hη₁])
      (mul_mem_complexProfiles (hK k) hα) (fun y hy => ?_) hφ (hentry _ (hK k)) hF hA
    have h1 := hχD k _ (hsub hy) _ hz
    exact (abs_apply_zero_le_sqrtSumSq _).trans h1
  have hnorm := sum_profileL1Norm J K hK hK0 hα hone
  rw [hsplit]
  have hfac : ((1 - 4 * c') * η) ^ (-p) = (1 - 4 * c') ^ (-p) * η ^ (-p) :=
    Real.mul_rpow hbase.le hη0.le
  calc ‖∑ k ∈ J, insertion S F (productFunction (fun y => (K k y : ℂ) * α y) φ) A‖
      ≤ ∑ k ∈ J, ‖insertion S F (productFunction (fun y => (K k y : ℂ) * α y) φ) A‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ J, C φ * ((1 - 4 * c') * η) ^ (-p) * profileL1Norm (fun y => (K k y : ℂ) * α y) *
          heightNorm σ (η / 4) F * heightNorm σ (η / 4) A :=
        Finset.sum_le_sum hpiece
    _ = productConstantsAt p c' C φ * η ^ (-p) * profileL1Norm α *
          heightNorm σ (η / 4) F * heightNorm σ (η / 4) A := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, hnorm, hfac,
          productConstantsAt]
        ring
end
section
variable {m : SharpScale} {S : ConnFamily} {σ : EuclidFunctionalWithRecon m S}
theorem productBound_congr {p c : ℝ} {C C' : (RealPlane → ℝ) → ℝ}
    (h : ProductBoundHolds σ p C c) (hC : ∀ φ ∈ realLabels, C φ = C' φ) :
    ProductBoundHolds σ p C' c :=
  ⟨h.pos_exponent, fun φ hφ => hC φ hφ ▸ h.nonneg_constant φ hφ, h.pos_fraction, h.fraction_lt_quarter,
    fun η h0 h1 φ hφ α hα hs F hF A hA => hC φ hφ ▸ h.le_bound η h0 h1 φ hφ α hα hs F hF A hA⟩
theorem eq_labelConstants (C : (RealPlane → ℝ) → ℝ) :
    ∀ φ ∈ realLabels, C φ = labelConstants (fun ψ : realLabels => C ψ) φ :=
  fun φ hφ => by simp [labelConstants, hφ]
def toProductPlaneData (hcone : σ.ConeCondition) {p c : ℝ} {C : (RealPlane → ℝ) → ℝ}
    (h : ProductBoundHolds σ p C c) : ProductPlaneData m S where
  fnl := σ
  coneCond := hcone
  exponent := p
  labelBound := fun ψ => C ψ
  fraction := c
  productBound := productBound_congr h (eq_labelConstants C)
theorem boundsInTimePlane_of_productBound
    (hInv : ∀ (w : hyperoctahedral) (p c : ℝ) (hp : 0 < p) (hc : c ∈ productBoundFractions),
      MomentSymmetry.ImagePlaneBoundEquiv σ w hp hc)
    {p c' : ℝ} {C : (RealPlane → ℝ) → ℝ} (hp : 0 < p) (hc' : c' ∈ productBoundFractions)
    (h : ProductBoundHolds σ p C c') : BoundsInTimePlane σ hp hc' := by
  have hleft : ProductBoundWithExponent σ hp hc' := fun φ hφ =>
    ⟨C φ, fun η hη α hα hs F hF A hA => h.le_bound η hη.1 hη.2 φ hφ α hα hs F hF A hA⟩
  exact ⟨hleft, (hInv 1 p c' hp hc').2.2.2 hleft⟩
end
theorem isPlaneKernel_of_centeredFnFree_eq {S₁ S₂ : ConnFamily}
    (hσ : centeredFnFree S₁ = centeredFnFree S₂) {q : ℕ}
    {φ : Fin (q + 1) → realLabels} {K : (Fin q → ℂ × ℂ) → ℂ} (h : IsPlaneKernel S₁ φ K) :
    IsPlaneKernel S₂ φ K :=
  ⟨h.holomorphic, fun α hα ho => by
    rw [← h.integral_eq α hα ho]
    simp only [centeredFnAtProducts, hσ]⟩
theorem sameKernelsAndHarmonics_of_centered_eq
    (hKern : PlaneKernelProps.Holds) (hAngle : AngleFunctionOnPencil.Holds)
    {m : SharpScale} {S₁ S₂ : ConnFamily} (e₁ : PlaneDataWithAperture m S₁)
    (e₂ : PlaneDataWithAperture m S₂) (hap : e₂.angle = e₁.angle)
    (hσ : centeredFnFree S₁ = centeredFnFree S₂) :
    SameKernelsAndHarmonics S₁ S₂ e₁.angle := by
  have hker : ∀ (q : ℕ), 1 ≤ q → ∀ φ : Fin (q + 1) → realLabels, ∀ v ∈ forwardTubePow q,
      planeKernel S₁ φ v = planeKernel S₂ φ v := fun q hq φ v hv =>
    (hKern m S₂ e₂ q hq φ).2.1 _ (isPlaneKernel_of_centeredFnFree_eq hσ (hKern m S₁ e₁ q hq φ).1) v hv
  have hfun : ∀ (q : ℕ), 1 ≤ q → ∀ φ : Fin (q + 1) → realLabels,
      ∀ y ∈ pencilSet e₁.angle (q + 1),
        angleFunction S₁ e₁.angle y φ = angleFunction S₂ e₁.angle y φ := by
    intro q hq φ y hy
    have h₁ := hAngle m S₁ e₁ q hq y hy φ
    have h₂ := hAngle m S₂ e₂ q hq y (hap ▸ hy) φ
    rw [hap] at h₂
    refine h₂.2.2.1 _ ⟨h₁.2.1.entire, fun υ t s ht => ?_⟩
    rw [h₁.2.1.apply_eq_planeKernel υ t s ht]
    exact hker q hq φ _ (h₁.1 υ t s ht)
  have hharm : ∀ (q : ℕ), 1 ≤ q → ∀ φ : Fin (q + 1) → realLabels,
      ∀ y ∈ pencilSet e₁.angle (q + 1), ∀ ν : ℤ,
        angleHarmonic S₁ e₁.angle y φ ν = angleHarmonic S₂ e₁.angle y φ ν := by
    intro q hq φ y hy ν
    simp only [angleHarmonic, hfun q hq φ y hy]
  refine ⟨fun q hq φ => ⟨hker q hq φ, fun y hy => ⟨hfun q hq φ y hy, hharm q hq φ y hy⟩⟩,
    fun n => ?_⟩
  cases n with
  | zero => rfl
  | succ q =>
    by_cases hq : 1 ≤ q
    · have hset : harmonicFrequencies S₁ e₁.angle q =
          harmonicFrequencies S₂ e₁.angle q := by
        ext k
        simp only [harmonicFrequencies, Set.mem_union, Set.mem_ofPred_eq]
        refine or_congr Iff.rfl ⟨?_, ?_⟩
        · rintro ⟨ν, hν, y, hy, φ, hne⟩
          exact ⟨ν, hν, y, hy, φ, by rwa [← hharm q hq φ y hy ν]⟩
        · rintro ⟨ν, hν, y, hy, φ, hne⟩
          exact ⟨ν, hν, y, hy, φ, by rwa [hharm q hq φ y hy ν]⟩
      simp only [maxFrequency, if_pos hq, hset]
    · simp only [maxFrequency, if_neg hq]
theorem holds
    (hCut : PartitionOfUnity.C1PartitionAndCutoffExist)
    (hT : TupleRules.TupleSpanActionRules)
    (hCalc : HamMomMatrixCalculus)
    (hRules : TranslationRules.TranslationAndMotionFacts)
    (hPull : AboveHeight.Holds)
    (hInv : MomentSymmetry.ReductionHolds)
    (hSet : PlaneDataAsStandingData.ExistsStandingAndApertureData)
    (hKern : PlaneKernelProps.Holds)
    (hAngle : AngleFunctionOnPencil.Holds) :
    Holds := by
  refine ⟨fun m S σ p C c h => ?_, fun m S₁ S₂ d₁ d₂ hσ φ₀ => ?_⟩
  · have hI := hInv m S σ
    have ha : ∀ c' ∈ productBoundFractions,
        ProductBoundHolds σ p (productConstantsAt p c' C) c' := fun c' hc' =>
      productBound_of_fraction hCut hT hCalc hRules hPull hI.2.1 h hc'
    have hb : ∀ (c' : ℝ) (hc' : c' ∈ productBoundFractions),
        BoundsInTimePlane σ h.pos_exponent hc' := fun c' hc' =>
      boundsInTimePlane_of_productBound hI.2.2.1 h.pos_exponent hc' (ha c' hc')
    refine ⟨ha, hb, fun hcone => ⟨?_, fun c' hc' => ⟨fun φ₀ => ?_, hb c' hc', ha c' hc'⟩⟩⟩
    · exact ⟨toProductPlaneData hcone h, rfl, rfl, rfl, fun _ => rfl⟩
    · obtain ⟨e, ⟨hs, hf, hp, hl⟩, he⟩ := (hSet m S (toProductPlaneData hcone (ha c' hc'))).2 φ₀
      exact ⟨e, hf, hp, hs, he, fun φ => congrFun hl φ⟩
  · obtain ⟨e₁, -, h₁⟩ := (hSet m S₁ d₁).2 φ₀
    obtain ⟨e₂, -, h₂⟩ := (hSet m S₂ d₂).2 φ₀
    subst h₁
    exact sameKernelsAndHarmonics_of_centered_eq hKern hAngle e₁ e₂ h₂ hσ
end EuclideanFunctionals.FractionChange
end YangMills.Construction
end

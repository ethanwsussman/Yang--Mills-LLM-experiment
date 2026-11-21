import Reconstruction.MinkowskiSpace.TranslationOperatorsOfABoundedFieldFormProof
import Reconstruction.MinkowskiSpace.TranslationsAndMeasureOnTheTensorVectors
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.TensorTranslations
open MinkowskiSpace FieldForms RealPointVectors WightmanTheory FieldFormHilbert ProjectionMeasures
  FormsOperators OneLoopNotation ComplexHilbert PVMCalculus
theorem translateVal_tensorVal (a : RealVec4) {m : ℕ} (f : Fin m → (Fin 4 → ℝ) → ℂ) :
    translateVal a (tensorVal f) =
      tensorVal fun i => poincareActR4 (pureTranslation a) (f i) := by
  cases m with
  | zero => rfl
  | succ m =>
    funext x
    show poincarePullback (pureTranslation a).1 (TestSpaces.tensorProd f) x =
      TestSpaces.tensorProd (fun i => poincareActR4 (pureTranslation a) (f i)) x
    simp [TestSpaces.tensorProd, poincarePullback, poincareActR4, asOnePointFn]
theorem isBddMeasurableFun_minkowskiPhase (a : RealVec4) :
    IsBddMeasurableFun (minkowskiPhase a) := by apply _root_.YangMills.Construction.WightmanTheory.DomainFacts.minkowskiPhase_isBddMeasurable <;> assumption
theorem I_mul_minkowskiForm_imagTimeShift (t : ℝ) (p : RealVec4) :
    Complex.I * minkowskiForm (imagTimeShift t) (MinkowskiSpace.toComplex p) = -((t * p 0 : ℝ) : ℂ) := by
  have h : minkowskiForm (MinkowskiSpace.toComplex (t • timeUnit)) (MinkowskiSpace.toComplex p) =
      ((t * p 0 : ℝ) : ℂ) := by
    simp [minkowskiForm, MinkowskiSpace.toComplex, timeUnit, mkTimeSpace, spaceBilin, spacePart]
  rw [imagTimeShift, minkowskiForm_smul_left, h, ← mul_assoc, Complex.I_mul_I]
  ring
theorem isBddMeasurableFun_expDecay_indicator {t : ℝ} (ht : 0 ≤ t) :
    IsBddMeasurableFun
      (closedFutureCone.indicator fun p : RealVec4 => Complex.exp (-((t * p 0 : ℝ) : ℂ))) := by apply _root_.YangMills.Construction.WightmanTheory.DomainFacts.decay_indicator_isBddMeasurable <;> assumption
section PvmFacts
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem isBddMeasurableFun_indicator_one (Δ : FourBorelSet) :
    IsBddMeasurableFun (Δ.1.indicator fun _ => (1 : ℂ)) := by apply _root_.YangMills.Construction.FieldFormTranslations.isBddMeasurableFun_setIndicator <;> assumption
theorem eq_idOp_of_isSupportedOn {E : FourBorelSet → BddOp H} {Δ₀ : FourBorelSet}
    (hI : PvmIntegralBasic E Δ₀) (hR : PvmIntegralRules E)
    (hc : IsSupportedOn E Δ₀) : E Δ₀ = idOp H := by
  obtain ⟨-, -, hind, hone⟩ := hR
  have hlin := hI.2 1 1 _ _ (isBddMeasurableFun_indicator_one Δ₀)
    (isBddMeasurableFun_indicator_one Δ₀.compl)
  have hfun : (fun p => (1 : ℂ) * Δ₀.1.indicator (fun _ => (1 : ℂ)) p +
      1 * Δ₀.compl.1.indicator (fun _ => (1 : ℂ)) p) = fun _ => (1 : ℂ) := by
    funext p
    by_cases hp : p ∈ Δ₀.1
    · have hp' : p ∉ Δ₀.compl.1 := fun h => h hp
      simp [Set.indicator_of_mem hp, Set.indicator_of_notMem hp']
    · have hp' : p ∈ Δ₀.compl.1 := hp
      simp [Set.indicator_of_notMem hp, Set.indicator_of_mem hp']
  rw [hfun, hone, hind, hind, hc] at hlin
  simpa using hlin.symm
theorem pvmIntegral_indicator_of_isSupportedOn {E : FourBorelSet → BddOp H} {Δ₀ : FourBorelSet}
    (hI : PvmIntegralBasic E Δ₀) (hR : PvmIntegralRules E)
    (hc : IsSupportedOn E Δ₀) {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u) :
    pvmIntegral E (Δ₀.1.indicator u) = pvmIntegral E u := by
  have hmul := hR.1 u _ hu (isBddMeasurableFun_indicator_one Δ₀)
  have hfun : (fun p => u p * Δ₀.1.indicator (fun _ => (1 : ℂ)) p) = Δ₀.1.indicator u := by
    funext p
    by_cases hp : p ∈ Δ₀.1
    · simp [Set.indicator_of_mem hp]
    · simp [Set.indicator_of_notMem hp]
  rw [hfun, hR.2.2.1, eq_idOp_of_isSupportedOn hI hR hc] at hmul
  rw [hmul]
  rfl
end PvmFacts
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K} {℘ C : ℝ}
theorem eq_of_eqOn_tensorVec (B : BddOp K)
    (U : UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A))
    (h : ∀ (m : ℕ) (f : Fin m → TestFn),
      ((U (tensorVec E Ω A f) : tensorHilbert E Ω A) : K) = B (tensorVec E Ω A f))
    (χ : tensorHilbert E Ω A) :
    ((U χ : tensorHilbert E Ω A) : K) = B χ := by
  let Y := tensorHilbert E Ω A
  let L₁ : Y →L[ℂ] K := Y.subtypeL.comp (U.toContinuousLinearEquiv : Y →L[ℂ] Y)
  let L₂ : Y →L[ℂ] K := B.comp Y.subtypeL
  let M : Submodule ℂ Y := LinearMap.eqLocus (L₁ : Y →ₗ[ℂ] K) (L₂ : Y →ₗ[ℂ] K)
  have hclosed : IsClosed (M : Set Y) := isClosed_eq L₁.continuous L₂.continuous
  have hle : tensorDomain E Ω A ≤ M.map Y.subtype := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨m, f, hf, rfl⟩
    refine ⟨tensorVec E Ω A fun i => ⟨f i, hf i⟩, ?_, rfl⟩
    exact h m fun i => ⟨f i, hf i⟩
  have hχ : (χ : K) ∈ closure (tensorDomain E Ω A : Set K) := by
    have := χ.2
    rwa [← SetLike.mem_coe, show (Y : Set K) = _ from Submodule.topologicalClosure_coe _] at this
  have hmem : χ ∈ closure (M : Set Y) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    refine closure_mono ?_ hχ
    intro v hv
    obtain ⟨y, hy, rfl⟩ := hle hv
    exact ⟨y, hy, rfl⟩
  rw [hclosed.closure_eq] at hmem
  exact hmem
theorem properties_of_isBoundedFieldForm (hC : PVMCalculus.BoundedFunctionalCalculus)
    (hV : RealPointVectors.BoundaryVectorFacts E Ω A ℘ C)
    (hf : IsBoundedFieldForm E Ω A ℘ C) : Properties E Ω A := by
  obtain ⟨hMS, hI, hR, -, -, -, hRes, -, -, -⟩ :=
    (hC.2 K).2 E closedFutureConeBorel hf.isPVM hf.supportedOn
  have hT : ∀ a : RealVec4, spectralTranslation E (MinkowskiSpace.toComplex a) =
      pvmIntegral E (minkowskiPhase a) := fun a =>
    pvmIntegral_indicator_of_isSupportedOn hI hR hf.supportedOn (isBddMeasurableFun_minkowskiPhase a)
  refine ⟨?_, ?_⟩
  · intro a U hU χ
    refine eq_of_eqOn_tensorVec _ U (fun m f => ?_) χ
    rw [hU m f]
    show _ = spectralTranslation E (MinkowskiSpace.toComplex a)
      (testState E Ω A m (tensorVal fun i => (f i).1))
    rw [hV.spectralTranslation_testState m _ a (hV.tensorVal_mem m _ fun i => (f i).2),
      translateVal_tensorVal]
  · let Y := tensorHilbert E Ω A
    have hclosed : IsClosed (Y : Set K) := Submodule.isClosed_topologicalClosure _
    have hY : ∀ Δ, ∀ y ∈ Y, E Δ y ∈ Y := by
      intro Δ y hy
      have h₁ : y ∈ tensorDomainClosure E Ω A := by
        rw [← coe_tensorHilbert]
        exact hy
      have h₂ := hV.proj_mem Δ y h₁
      rw [← coe_tensorHilbert] at h₂
      exact h₂
    obtain ⟨hF, hcar, hint⟩ := (hRes Y hclosed hY).2
    let F : FourBorelSet → BddOp Y := fun Δ => restrictInvariant Y (E Δ) (hY Δ)
    obtain ⟨-, hIF, -, -, -, -, -, -, -, -⟩ :=
      (hC.2 Y).2 F closedFutureConeBorel hF hcar
    refine ⟨F, fun Δ χ => rfl, hF, hcar, ?_, ?_⟩
    · intro a V hVa
      have hu := isBddMeasurableFun_minkowskiPhase a
      have hEq : V = pvmIntegral F (minkowskiPhase a) := by
        ext χ
        rw [hVa χ, hint _ hu χ, hT a]
      rw [hEq]
      exact (hIF.1 _ hu).1
    · intro t ht χ
      have hu := isBddMeasurableFun_expDecay_indicator ht
      have hfun : (closedFutureCone.indicator fun p : RealVec4 =>
            Complex.exp (Complex.I * minkowskiForm (imagTimeShift t) (MinkowskiSpace.toComplex p))) =
          closedFutureCone.indicator fun p : RealVec4 => Complex.exp (-((t * p 0 : ℝ) : ℂ)) := by
        congr 1
        funext p
        rw [I_mul_minkowskiForm_imagTimeShift]
      show ((pvmIntegral F _ χ : Y) : K) = pvmIntegral E _ χ
      rw [hfun]
      exact hint _ hu χ
theorem holds (hC : PVMCalculus.BoundedFunctionalCalculus)
    (hV : RealPointVectors.BoundaryVectorsStatement) : Holds :=
  fun E Ω A ℘ C hf => properties_of_isBoundedFieldForm hC (hV E Ω A ℘ C hf) hf
end YangMills.Construction.TensorTranslations

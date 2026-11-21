import YangMills.Construction.EuclideanFunctionals.ReconstructionIsUniqueUpToUnitary
import YangMills.Construction.EuclideanFunctionals.TensorsWithComplexEntriesTranslationsAndTranslatedClasses
import YangMills.Construction.HilbertSpace.BasicHilbertSpaceFacts
import YangMills.Construction.SpectralTheory.MeasuresIntegralsProductsImagesAndTransportOfAProjectionValuedMeasure
import Mathlib
set_option autoImplicit false
open Set
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ReconUnique
open BorelSpectral
open OperatorTransport (IsUnitaryMap)
open SpectralTheorem (IsSpectralIntegralOf spectralIntegralOp)
open SpectralMeasureCalculus (UnboundedCalculusLaws)
open EuclidFunctionalWithRecon
open TensorTranslation (raise)
section Unitary
variable {𝒦 𝒦' : Type*} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦]
  [NormedAddCommGroup 𝒦'] [InnerProductSpace ℂ 𝒦']
theorem inv_apply_map {V : 𝒦 →ₗ[ℂ] 𝒦'} (hV : IsUnitaryMap V) (ψ : 𝒦) : hV.inv (V ψ) = ψ :=
  hV.toLinearEquiv.symm_apply_apply ψ
theorem map_inv_apply {V : 𝒦 →ₗ[ℂ] 𝒦'} (hV : IsUnitaryMap V) (χ : 𝒦') : V (hV.inv χ) = χ :=
  hV.toLinearEquiv.apply_symm_apply χ
theorem norm_eq_of_inner_self_eq {φ : 𝒦} {ψ : 𝒦'} (h : ⟪φ, φ⟫_ℂ = ⟪ψ, ψ⟫_ℂ) : ‖φ‖ = ‖ψ‖ := by
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖φ‖ ^ 2 = ‖ψ‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'
theorem norm_map_of_unitary {V : 𝒦 →ₗ[ℂ] 𝒦'} (hV : IsUnitaryMap V) (ψ : 𝒦) : ‖V ψ‖ = ‖ψ‖ :=
  norm_eq_of_inner_self_eq (hV.inner_map_map ψ ψ)
end Unitary
theorem eq_spectralIntegralOp {n : ℕ} {Y : Set (Fin n → ℝ)} {𝒦 : Type*} [NormedAddCommGroup 𝒦]
    [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦] {E : SpectralMeasure Y 𝒦}
    (hAll : UnboundedCalculusLaws E) {A : HilbertSpaceBasics.UnboundedOp 𝒦} {g : Y → ℂ}
    (hg : Measurable g) (hA : IsSpectralIntegralOf A E g) : A = spectralIntegralOp E g := by
  have h := hAll.isIntegralOf g hg
  refine LinearPMap.ext (Submodule.ext fun ψ => (hA.1 ψ).trans (h.1 ψ).symm) ?_
  intro x h₁ h₂
  exact (hA.2 ⟨x, h₁⟩).trans (h.2 ⟨x, h₂⟩).symm
theorem exists_unitary_of_denseRange (hFive : HilbertSpace.BasicFacts.BasicHilbertSpaceFacts)
    {M 𝒦 𝒦' : Type} [AddCommMonoid M] [Module ℂ M] [NormedAddCommGroup 𝒦]
    [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦] [NormedAddCommGroup 𝒦'] [InnerProductSpace ℂ 𝒦']
    [CompleteSpace 𝒦'] (f : M →ₗ[ℂ] 𝒦) (g : M →ₗ[ℂ] 𝒦')
    (hfg : ∀ x y, ⟪f x, f y⟫_ℂ = ⟪g x, g y⟫_ℂ) (hf : DenseRange f) (hg : DenseRange g) :
    ∃ B : 𝒦 →L[ℂ] 𝒦', IsUnitaryMap (B : 𝒦 →ₗ[ℂ] 𝒦') ∧ ∀ x, B (f x) = g x := by
  have hWell : ∀ x y, f x = f y → g x = g y := by
    intro x y h
    have h₀ : ⟪g x - g y, g x - g y⟫_ℂ = 0 := by
      simp only [inner_sub_left, inner_sub_right, ← hfg, h, sub_self]
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h₀)
  have hPre : ∀ ψ : LinearMap.range f, ∃ x, f x = ψ := fun ψ => ψ.2
  choose pre hPre using hPre
  let B₀ : LinearMap.range f →ₗ[ℂ] 𝒦' :=
    { toFun := fun ψ => g (pre ψ)
      map_add' := fun a b => by
        rw [← map_add]
        exact hWell _ _ (by rw [map_add, hPre, hPre, hPre]; rfl)
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← map_smul]
        exact hWell _ _ (by rw [map_smul, hPre, hPre]; rfl) }
  have hB₀ : ∀ x, B₀ ⟨f x, LinearMap.mem_range_self f x⟩ = g x :=
    fun x => hWell _ _ (hPre _)
  have hDense : Dense ((LinearMap.range f : Submodule ℂ 𝒦) : Set 𝒦) := by
    rw [LinearMap.coe_range]
    exact hf
  have hNorm : ∀ ψ : LinearMap.range f, ‖B₀ ψ‖ = ‖(ψ : 𝒦)‖ := by
    rintro ⟨_, x, rfl⟩
    rw [hB₀]
    exact norm_eq_of_inner_self_eq (hfg x x).symm
  obtain ⟨B, hB, -, -, hU⟩ := (hFive 𝒦 𝒦').1 _ 1 B₀ hDense zero_le_one
    (fun ψ => by rw [hNorm, one_mul])
  have hRange : Dense (Set.range B₀) := by
    refine hg.mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨_, LinearMap.mem_range_self f x⟩, hB₀ x⟩
  exact ⟨B, hU hNorm hRange, fun x => (hB ⟨_, LinearMap.mem_range_self f x⟩).trans (hB₀ x)⟩
variable {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
  {ℋ' : Type} [NormedAddCommGroup ℋ'] [InnerProductSpace ℂ ℋ'] [CompleteSpace ℋ']
  (R' : OSReconstruction ℋ' S)
theorem exists_unitary_extending (hFive : HilbertSpace.BasicFacts.BasicHilbertSpaceFacts) :
    ∃ B : σ.space →L[ℂ] ℋ', IsUnitaryMap (B : σ.space →ₗ[ℂ] ℋ') ∧
      ∀ F, B (σ.recon.cls F) = R'.cls F :=
  exists_unitary_of_denseRange hFive _ _
    (fun F A => (σ.recon.inner_cls F A).trans (R'.inner_cls F A).symm)
    σ.recon.denseRange_cls R'.denseRange_cls
theorem map_classOrZero (V : σ.space →ₗ[ℂ] ℋ') (hV : MapsClassesTo σ R' V)
    (G : FreeSep) :
    V (readClass σ.recon.cls G) = readClass R'.cls G := by
  unfold readClass
  split_ifs with h
  · exact hV _
  · exact map_zero V
theorem expComplex_intertwines (B : σ.space →L[ℂ] ℋ')
    (hB : MapsClassesTo σ R' (B : σ.space →ₗ[ℂ] ℋ')) {t : ℝ} (ht : 0 ≤ t)
    (ψ : σ.space) :
    B (ResolvedOps.expComplex σ.recon.ham (t : ℂ) ψ) =
      ResolvedOps.expComplex R'.ham (t : ℂ) (B ψ) := by
  have h : (fun ψ => B (ResolvedOps.expComplex σ.recon.ham (t : ℂ) ψ)) =
      fun ψ => ResolvedOps.expComplex R'.ham (t : ℂ) (B ψ) := by
    refine σ.recon.denseRange_cls.equalizer
      (B.continuous.comp (ContinuousLinearMap.continuous _))
      ((ContinuousLinearMap.continuous _).comp B.continuous) ?_
    funext F
    have h₁ := map_classOrZero σ R' _ hB ((EuclidMotion.transl (t • timeVec)).actFree F.1)
    have h₂ : B (σ.recon.cls F) = R'.cls F := hB F
    simp only [Function.comp_apply]
    rw [σ.recon.expHam_cls t ht F, h₂, R'.expHam_cls t ht F]
    exact h₁
  exact congrFun h ψ
theorem spatialTranslOp_intertwines (B : σ.space →L[ℂ] ℋ')
    (hB : MapsClassesTo σ R' (B : σ.space →ₗ[ℂ] ℋ')) {v : R4}
    (hv : v ∈ spatialVecs) (ψ : σ.space) :
    B (spatialTranslOp (hamMomMeasure σ.recon.ham σ.recon.mom) v ψ) =
      spatialTranslOp (hamMomMeasure R'.ham R'.mom) v (B ψ) := by
  have h : (fun ψ => B (spatialTranslOp (hamMomMeasure σ.recon.ham σ.recon.mom) v ψ)) =
      fun ψ => spatialTranslOp (hamMomMeasure R'.ham R'.mom) v (B ψ) := by
    refine σ.recon.denseRange_cls.equalizer
      (B.continuous.comp (ContinuousLinearMap.continuous _))
      ((ContinuousLinearMap.continuous _).comp B.continuous) ?_
    funext F
    have h₁ := map_classOrZero σ R' _ hB ((EuclidMotion.transl v).actFree F.1)
    have h₂ : B (σ.recon.cls F) = R'.cls F := hB F
    simp only [Function.comp_apply]
    rw [σ.recon.transl_cls v hv F, h₂, R'.transl_cls v hv F]
    exact h₁
  exact congrFun h ψ
theorem jointMeasure_conj (hFirst : ReconstructionBasicFacts)
    (B : σ.space →L[ℂ] ℋ') (hU : IsUnitaryMap (B : σ.space →ₗ[ℂ] ℋ'))
    (hB : MapsClassesTo σ R' (B : σ.space →ₗ[ℂ] ℋ'))
    (Δ : BorelSubsets SpectralPoint.EMPoints) :
    ((hamMomMeasure R'.ham R'.mom Δ : ℋ' →L[ℂ] ℋ') : ℋ' →ₗ[ℂ] ℋ') =
      σ.jointMeasure.unitaryPushforward hU Δ := by
  have hDet : σ.SpectralMeasureUniqueness :=
    (hFirst m S σ σ.space σ.recon).2.2.1
  obtain ⟨-, -, hCarried, hTransform⟩ := (hFirst m S σ ℋ' R').1
  refine hDet ℋ' _ hU (hamMomMeasure R'.ham R'.mom) hCarried ?_ Δ
  intro k v hv
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hOn := (hTransform k hk v hv).2
  refine LinearMap.ext fun χ => ?_
  have hχ : B (hU.inv χ) = χ := map_inv_apply hU χ
  have hLeft : (hamMomMeasure R'.ham R'.mom).integralOpOn
      SpectralPoint.nonnegEnergy (SpectralPoint.laplaceFourierKernel k v) χ =
        ResolvedOps.expComplex R'.ham ((k : ℝ) : ℂ)
          (spatialTranslOp (hamMomMeasure R'.ham R'.mom) v χ) :=
    (congrArg (fun T : ℋ' →L[ℂ] ℋ' => T χ) hOn).symm
  have hRight : B (σ.heatSemigroup k (σ.translOp v (hU.inv χ))) =
      ResolvedOps.expComplex R'.ham ((k : ℝ) : ℂ)
        (spatialTranslOp (hamMomMeasure R'.ham R'.mom) v χ) := by
    have e₁ := expComplex_intertwines σ R' B hB hk (σ.translOp v (hU.inv χ))
    have e₂ := spatialTranslOp_intertwines σ R' B hB hv (hU.inv χ)
    rw [hχ] at e₂
    exact e₁.trans (congrArg _ e₂)
  exact hLeft.trans hRight.symm
theorem hamMomMeasure_eq_zero_iff {V : σ.space →ₗ[ℂ] ℋ'} (hU : IsUnitaryMap V)
    (hP : ∀ Δ : BorelSubsets SpectralPoint.EMPoints,
      ((hamMomMeasure R'.ham R'.mom Δ : ℋ' →L[ℂ] ℋ') : ℋ' →ₗ[ℂ] ℋ') =
        σ.jointMeasure.unitaryPushforward hU Δ)
    (Δ : BorelSubsets SpectralPoint.EMPoints) :
    hamMomMeasure R'.ham R'.mom Δ = 0 ↔ σ.jointMeasure Δ = 0 := by
  have hApply : ∀ χ, hamMomMeasure R'.ham R'.mom Δ χ =
      V (σ.jointMeasure Δ (hU.inv χ)) :=
    fun χ => LinearMap.congr_fun (hP Δ) χ
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun ψ => ?_
    have h₁ := hApply (V ψ)
    rw [h, inv_apply_map hU] at h₁
    refine hU.bijective.1 ?_
    rw [← h₁]
    simp
  · intro h
    refine ContinuousLinearMap.ext fun χ => ?_
    rw [hApply, h]
    simp
theorem generator_conj (hCalc : SpectralMeasureCalculus.CalculusTheorem)
    {V : σ.space →ₗ[ℂ] ℋ'} (hU : IsUnitaryMap V)
    {P' : SpectralMeasure SpectralPoint.EMPoints ℋ'}
    (hP : ∀ Δ, ((P' Δ : ℋ' →L[ℂ] ℋ') : ℋ' →ₗ[ℂ] ℋ') = σ.jointMeasure.unitaryPushforward hU Δ)
    {g : SpectralPoint.EMPoints → ℂ} (hg : Measurable g)
    {A : HilbertSpaceBasics.UnboundedOp σ.space} {A' : HilbertSpaceBasics.UnboundedOp ℋ'}
    (hA : IsSpectralIntegralOf A σ.jointMeasure g) (hA' : IsSpectralIntegralOf A' P' g) :
    OperatorTransport.conjOp hU A = A' := by
  obtain ⟨E', hE', -, hInt⟩ :=
    (hCalc σ.space 4 SpectralPoint.EMPoints σ.jointMeasure).2.2.2.2.2.1 ℋ' V hU
  have hEq : E' = P' := SpectralMeasure.ext_apply fun Δ =>
    ContinuousLinearMap.coe_injective ((hE' Δ).trans (hP Δ).symm)
  subst hEq
  have hAll := (hCalc σ.space 4 SpectralPoint.EMPoints σ.jointMeasure).2.2.1
  have hAll' := (hCalc ℋ' 4 SpectralPoint.EMPoints E').2.2.1
  rw [eq_spectralIntegralOp hAll hg hA, eq_spectralIntegralOp hAll' hg hA', hInt g hg]
theorem uniqueUnitaryEquiv (hCalc : SpectralMeasureCalculus.CalculusTheorem)
    (hFive : HilbertSpace.BasicFacts.BasicHilbertSpaceFacts)
    (hFirst : ReconstructionBasicFacts) :
    UniqueUnitaryEquiv σ R' := by
  obtain ⟨B, hU, hB⟩ := exists_unitary_extending σ R' hFive
  have hCarries : MapsClassesTo σ R' (B : σ.space →ₗ[ℂ] ℋ') := hB
  have hP := jointMeasure_conj σ R' hFirst B hU hCarries
  obtain ⟨hGen, -⟩ := hFirst m S σ σ.space σ.recon
  obtain ⟨hGen', -⟩ := hFirst m S σ ℋ' R'
  have hE : Measurable fun p : SpectralPoint.EMPoints => ((SpectralPoint.energyOf p : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp SpectralPoint.measurable_energyOf
  have hQ : ∀ j : Fin 3,
      Measurable fun p : SpectralPoint.EMPoints => ((SpectralPoint.momentumOf p j : ℝ) : ℂ) :=
    fun j => Complex.measurable_ofReal.comp (SpectralPoint.measurable_momentumOf_apply j)
  refine ⟨B, hU, hCarries, ?_, ?_, ?_, hP⟩
  · intro V' hV' hCarries'
    obtain ⟨B', rfl⟩ := ((hFive σ.space ℋ').2.2.2.2.2.2.2.2.2.1 V' hV').1
    have hAgree := (hFive σ.space ℋ').2.1 (Set.range σ.recon.cls) B' B
      σ.recon.denseRange_cls (by
        rintro _ ⟨F, rfl⟩
        exact (hCarries' F).trans (hB F).symm)
    rw [hAgree]
  · exact generator_conj σ hCalc hU hP hE hGen.1 hGen'.1
  · exact fun j => generator_conj σ hCalc hU hP (hQ j) (hGen.2.1 j) (hGen'.2.1 j)
theorem sameSpectralNullSets (hFive : HilbertSpace.BasicFacts.BasicHilbertSpaceFacts)
    (hFirst : ReconstructionBasicFacts) : SameSpectralNullSets σ R' := by
  obtain ⟨B, hU, hB⟩ := exists_unitary_extending σ R' hFive
  have hZero := hamMomMeasure_eq_zero_iff σ R' hU (jointMeasure_conj σ R' hFirst B hU hB)
  exact ⟨hZero, fun n _ => hZero _, hZero _⟩
theorem heightNorm_withRecon (hFive : HilbertSpace.BasicFacts.BasicHilbertSpaceFacts) (c : ℝ)
    (F : FreeSep) : heightNorm (σ.withRecon R') c F = heightNorm σ c F := by
  obtain ⟨B, hU, hB⟩ := exists_unitary_extending σ R' hFive
  have h := map_classOrZero σ R' (B : σ.space →ₗ[ℂ] ℋ') hB (pullDown c F)
  have h' : heightNorm (σ.withRecon R') c F =
      ‖readClass R'.cls (pullDown c F)‖ := rfl
  rw [h', ← h]
  exact norm_map_of_unitary hU _
theorem heightNorm_eq_osForm (hTensors : TensorTranslation.AllFacts)
    {c : ℝ} (hc : 0 < c) {F : FreeSep} (hF : F ∈ finCombIn {y | c < y 3}) :
    heightNorm σ c F =
      (osForm S (pullDown c F) (pullDown c F)).re ^ (1 / 2 : ℝ) := by
  obtain ⟨hBij, hInv, -⟩ := (hTensors m S σ).2.2.1 c hc
  have hDown : pullDown c F ∈ finCombIn upperHalf := by
    obtain ⟨G, hG, rfl⟩ := hBij.surjOn hF
    rw [hInv.1 hG]
    exact hG
  have hClass : reconClass σ (pullDown c F) =
      σ.recon.cls ⟨pullDown c F, hDown⟩ := dif_pos hDown
  have hInner := σ.recon.inner_cls ⟨_, hDown⟩ ⟨_, hDown⟩
  have hSq : ‖reconClass σ (pullDown c F)‖ ^ 2 =
      (osForm S (pullDown c F) (pullDown c F)).re := by
    rw [hClass]
    have h := congrArg Complex.re hInner
    simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using h
  rw [← hSq, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  rfl
theorem sameHeightNormsAndProductBound (hFive : HilbertSpace.BasicFacts.BasicHilbertSpaceFacts)
    (hTensors : TensorTranslation.AllFacts) :
    SameHeightNormsAndProductBound σ R' := by
  have hNorm := heightNorm_withRecon σ R' hFive
  refine ⟨fun c hc F hF => ⟨hNorm c F, heightNorm_eq_osForm σ hTensors hc hF⟩, ?_⟩
  intro p c hp hc
  have hProd : ∀ (φ : RealPlane → ℝ) (C : ℝ), ProductBoundWith σ hp hc φ C ↔
      ProductBoundWith (σ.withRecon R') hp hc φ C := by
    intro φ C
    simp only [ProductBoundWith, hNorm]
  refine ⟨?_, fun φ _ C => hProd φ C⟩
  simp only [ProductBoundWithExponent, hProd]
theorem statement_holds (hCalc : SpectralMeasureCalculus.CalculusTheorem)
    (hFive : HilbertSpace.BasicFacts.BasicHilbertSpaceFacts) (hFirst : ReconstructionBasicFacts)
    (hTensors : TensorTranslation.AllFacts) : statement := by
  intro m S σ ℋ' _ _ _ R'
  exact ⟨uniqueUnitaryEquiv σ R' hCalc hFive hFirst, sameSpectralNullSets σ R' hFive hFirst,
    sameHeightNormsAndProductBound σ R' hFive hTensors⟩
end YangMills.Construction.EuclideanFunctionals.ReconUnique

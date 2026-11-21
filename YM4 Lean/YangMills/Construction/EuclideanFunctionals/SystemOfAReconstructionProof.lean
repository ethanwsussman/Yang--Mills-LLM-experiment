import YangMills.Construction.EuclideanFunctionals.MeasuresAndOperatorsOfTheReconstruction
import YangMills.Construction.EuclideanFunctionals.SystemOfAReconstruction
import YangMills.Construction.SpectralTheory.MeasuresOnABorelSetOfTheEarlierSettings
import YangMills.Construction.SpectralTheory.MeasuresOnRealSpaceOfTheEarlierSettings
import Mathlib
set_option autoImplicit false
open Set
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.OSDataOfReconProof
open YangMills.Construction.BorelSpectral
open YangMills.Construction.HilbertSpaceBasics (UnboundedOp)
open YangMills.Construction.SettingsComparison
  (IsSameMeasure euclideanToCoords liftToCoords valueFn FullSpaceMeasuresAgree
    IsProjValuedBorelMeasure)
open YangMills.Construction.SpectralTheorem (IsSpectralIntegralOf spectralIntegralOp)
open YangMills.Construction.EuclideanFunctionals.DefinitionComparison
theorem eq_spectralIntegralOp {n : ℕ} {Y : Set (Fin n → ℝ)} {𝒦 : Type*} [NormedAddCommGroup 𝒦]
    [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦] {E : SpectralMeasure Y 𝒦}
    {A : UnboundedOp 𝒦} {g : Y → ℂ} (hA : IsSpectralIntegralOf A E g) :
    A = spectralIntegralOp E g := by
  have h : IsSpectralIntegralOf (spectralIntegralOp E g) E g :=
    Classical.epsilon_spec (p := fun A => IsSpectralIntegralOf A E g) ⟨A, hA⟩
  refine LinearPMap.ext (Submodule.ext fun ψ => (hA.1 ψ).trans (h.1 ψ).symm) ?_
  intro x h₁ h₂
  exact (hA.2 ⟨x, h₁⟩).trans (h.2 ⟨x, h₂⟩).symm
theorem kernel_mem_of_eq {𝒦 : Type*} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦]
    {A : UnboundedOp 𝒦} {D : Submodule ℂ 𝒦} {T : D →ₗ[ℂ] 𝒦} (h : A = ⟨D, T⟩) {x : 𝒦}
    (hx : ∃ hm : x ∈ A.domain, A ⟨x, hm⟩ = 0) : ∃ hm : x ∈ D, T ⟨x, hm⟩ = 0 := by
  subst h
  exact hx
section Classes
variable {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
def clsOnSpan (cl : finCombIn upperHalf →ₗ[ℂ] ℋ) :
    freeSpanIn upperHalf →ₗ[ℂ] ℋ :=
  cl ∘ₗ Submodule.inclusion (finCombIn_eq_freeSpanIn upperHalf).ge
theorem classOrZero_clsOnSpan (cl : finCombIn upperHalf →ₗ[ℂ] ℋ) (F : FreeSep) :
    classOrZero (clsOnSpan cl) F = readClass cl F := by
  have hEq := finCombIn_eq_freeSpanIn upperHalf
  by_cases h : F ∈ freeSpanIn upperHalf
  · have h' : F ∈ finCombIn upperHalf := hEq.ge h
    rw [classOrZero_of_mem _ h]
    simp only [readClass, h', dite_true]
    rfl
  · have h' : F ∉ finCombIn upperHalf := fun hc => h (hEq.le hc)
    simp [classOrZero, readClass, h, h']
theorem denseRange_clsOnSpan {cl : finCombIn upperHalf →ₗ[ℂ] ℋ}
    (h : DenseRange cl) : DenseRange (clsOnSpan cl) := by
  have hEq := finCombIn_eq_freeSpanIn upperHalf
  have hr : range (clsOnSpan cl) = range cl := by
    ext x
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨F, rfl⟩
      exact ⟨⟨F.1, hEq.le F.2⟩, rfl⟩
  unfold DenseRange
  rw [hr]
  exact h
end Classes
section Unitaries
variable {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
theorem EuclideanSpectral_isUnitaryMap_of_isUnitaryMap {U : ℋ →ₗ[ℂ] ℋ}
    (h : YangMills.Construction.OperatorTransport.IsUnitaryMap U) :
    YangMills.Construction.EuclideanSpectral.IsUnitaryMap U := by
  refine ⟨h.bijective, fun ψ => ?_⟩
  have hi := h.inner_map_map ψ ψ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hi
  have h' : ‖U ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by exact_mod_cast hi
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'
theorem inv_eq_inv {U : ℋ →ₗ[ℂ] ℋ} (h : YangMills.Construction.OperatorTransport.IsUnitaryMap U)
    (h' : YangMills.Construction.EuclideanSpectral.IsUnitaryMap U) : h'.inv = h.inv := by
  ext x
  apply h.bijective.1
  have a : U (h'.inv x) = x := (LinearEquiv.ofBijective U h'.bijective).apply_symm_apply x
  have b : U (h.inv x) = x := h.toLinearEquiv.apply_symm_apply x
  rw [a, b]
end Unitaries
section BlockEvaluations
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  {F : SpectralMeasure (univ : Set (Fin 4 → ℝ)) ℋ}
  {G : YangMills.Construction.EuclideanSpectral.ProjMeasure ℋ 4}
theorem momCoord_measurable (j : Fin 3) : Measurable (momCoord j) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (j.succ : Fin 4)).continuous.measurable
theorem spatialDot_measurable (v : R4) : Measurable (spatialDot v) :=
  Finset.measurable_fun_sum _ fun j _ => (momCoord_measurable j).const_mul _
theorem eq_borelFnOp (hR : FullSpaceMeasuresAgree ℋ 4) (hFG : IsSameMeasure F G)
    {A : UnboundedOp ℋ} {f : EuclideanSpace ℝ (Fin 4) → ℂ} (hf : Measurable f)
    (hA : IsSpectralIntegralOf A F (liftToCoords f)) :
    A = ⟨G.fnDomain f, G.borelFnOp f⟩ :=
  (eq_spectralIntegralOp hA).trans (hR.spectralIntegralOp_eq F G hFG f hf)
theorem integralOpOn_eq_semigroupOp (hR : FullSpaceMeasuresAgree ℋ 4) (hFG : IsSameMeasure F G)
    {t : ℝ} (ht : 0 ≤ t) :
    ⇑(F.integralOpOn SpectralPoint.nonnegEnergy (SpectralPoint.laplaceFourierKernel t 0)) =
      ⇑(semigroupOp G t) := by
  set f : EuclideanSpace ℝ (Fin 4) → ℂ := fun p => (Real.exp (-t * energyCoord p) : ℂ) with hf
  have hmeas : Measurable (nonnegEnergySet.1.indicator f) := by
    refine Measurable.indicator ?_ nonnegEnergySet.2
    exact Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_energyCoord.const_mul _))
  have hbdd : YangMills.Construction.BorelCalculus.IsBoundedFn
      (nonnegEnergySet.1.indicator f) := by
    refine ⟨1, fun x => ?_⟩
    by_cases hx : x ∈ nonnegEnergySet.1
    · rw [indicator_of_mem hx]
      have hx' : 0 ≤ energyCoord x := hx
      simp only [hf, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by nlinarith)
    · rw [indicator_of_notMem hx]
      simp
  have h := hR.integralOp_eq F G hFG _ hmeas hbdd
  have hfun : zeroExtend SpectralPoint.nonnegEnergy.1
      (SpectralPoint.laplaceFourierKernel t 0) = liftToCoords (nonnegEnergySet.1.indicator f) := by
    funext y
    by_cases hy : 0 ≤ SpectralPoint.energyOf y
    · have hy' : (WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin 4)) ∈ nonnegEnergySet.1 := hy
      have hy'' : y ∈ SpectralPoint.nonnegEnergy.1 := hy
      simp only [zeroExtend, liftToCoords, dif_pos hy'', indicator_of_mem hy']
      simp [SpectralPoint.laplaceFourierKernel, SpectralPoint.dotR4, SpectralPoint.dot3, hf,
        energyCoord, SpectralPoint.energyOf]
    · have hy' : (WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin 4)) ∉ nonnegEnergySet.1 := hy
      have hy'' : y ∉ SpectralPoint.nonnegEnergy.1 := hy
      simp only [zeroExtend, liftToCoords, dif_neg hy'', indicator_of_notMem hy']
  unfold SpectralMeasure.integralOpOn semigroupOp
    YangMills.Construction.EuclideanSpectral.ProjMeasure.boundedIntegralOn
  rw [hfun]
  exact h
theorem spatialTranslOp_eq_spatialShiftOp (hR : FullSpaceMeasuresAgree ℋ 4)
    (hFG : IsSameMeasure F G) (v : R4) :
    ⇑(spatialTranslOp F v) = ⇑(spatialShiftOp G v) := by
  have hmeas : Measurable fun p : EuclideanSpace ℝ (Fin 4) =>
      Complex.exp (Complex.I * (spatialDot v p : ℂ)) :=
    Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (spatialDot_measurable v)).const_mul _)
  have hbdd : YangMills.Construction.BorelCalculus.IsBoundedFn
      fun p : EuclideanSpace ℝ (Fin 4) => Complex.exp (Complex.I * (spatialDot v p : ℂ)) :=
    ⟨1, fun x => (Complex.norm_exp_I_mul_ofReal _).le⟩
  exact hR.integralOp_eq F G hFG _ hmeas hbdd
end BlockEvaluations
theorem exists_isSameMeasure
    (hBorel : YangMills.Construction.SettingsComparison.BorelSetMeasuresAgreeForAllSpaces)
    (hReal : YangMills.Construction.SettingsComparison.FullSpaceMeasuresAgreeForAllSpaces)
    {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (F : SpectralMeasure (univ : Set (Fin 4 → ℝ)) ℋ) :
    ∃ G : YangMills.Construction.EuclideanSpectral.ProjMeasure ℋ 4, IsSameMeasure F G := by
  have hB := hBorel ℋ 4 univ (by norm_num) MeasurableSet.univ ⟨0, mem_univ _⟩
  have hmeas : IsProjValuedBorelMeasure (valueFn F) := (hB.isProjValued_iff _).2 ⟨F, rfl⟩
  exact ((hReal ℋ 4).isProjValued_iff _).1 hmeas
theorem osDataOfRecon_holds
    (hBorel : YangMills.Construction.SettingsComparison.BorelSetMeasuresAgreeForAllSpaces)
    (hReal : YangMills.Construction.SettingsComparison.FullSpaceMeasuresAgreeForAllSpaces)
    (hFirst : ReconstructionBasicFacts)
    (hLink : ReconstructionMeasureOperatorFacts) : OSDataOfRecon.Holds := by
  intro m S σ
  have hR := hReal σ.space 4
  have hFacts : σ.SpectralGeneratorsAndKernel ∧ σ.TranslUnitaryGroup ∧
      σ.SpectralMeasureUniqueness ∧ σ.VacuumInvariance ∧ σ.RotationCovariance :=
    hFirst m S σ σ.space σ.recon
  obtain ⟨⟨hH, hP, hCar, hTr⟩, ⟨-, hU0, -⟩, -, ⟨-, -, -, -, -, hΩ, -⟩, hCov₁, hCov₂, -⟩ := hFacts
  have hJoint := (hLink m S σ).1.isJoint
  obtain ⟨G, hFG⟩ := exists_isSameMeasure hBorel hReal σ.jointMeasure
  have hHam : σ.recon.ham =
      ⟨G.fnDomain energyFn, hamiltonianOp G⟩ :=
    eq_borelFnOp hR hFG (Complex.measurable_ofReal.comp measurable_energyCoord) hH
  have hMom : ∀ j, σ.recon.mom j =
      ⟨G.fnDomain (fun p => (momCoord j p : ℂ)), momentumOp G j⟩ := fun j =>
    eq_borelFnOp hR hFG (Complex.measurable_ofReal.comp (momCoord_measurable j)) (hP j)
  have hExp : ∀ t : ℝ, 0 ≤ t → ⇑(σ.heatSemigroup t) = ⇑(semigroupOp G t) := by
    intro t ht
    have h0 : (0 : R4) ∈ spatialVecs := by simp [spatialVecs]
    have h := (hTr t ht 0 h0).2
    rw [hU0, mul_one] at h
    rw [h]
    exact integralOpOn_eq_semigroupOp hR hFG ht
  have hSp : ∀ v, ⇑(σ.translOp v) = ⇑(spatialShiftOp G v) :=
    spatialTranslOp_eq_spatialShiftOp hR hFG
  have hExpL : ∀ t : ℝ, 0 ≤ t → semigroupOp G t =
      (σ.heatSemigroup t : σ.space →ₗ[ℂ] σ.space) := fun t ht =>
    LinearMap.ext fun x => (congrFun (hExp t ht) x).symm
  have hSpL : ∀ v, spatialShiftOp G v =
      (σ.translOp v : σ.space →ₗ[ℂ] σ.space) := fun v =>
    LinearMap.ext fun x => (congrFun (hSp v) x).symm
  have hCl := classOrZero_clsOnSpan σ.recon.cls
  have hU := fun w => EuclideanSpectral_isUnitaryMap_of_isUnitaryMap (σ.recon.rotOp_unitary w)
  refine ⟨{
    cls := clsOnSpan σ.recon.cls
    inner_cls := fun F F' => σ.recon.inner_cls _ _
    denseRange_cls := denseRange_clsOnSpan σ.recon.denseRange_cls
    pvm := G
    pvm_negEnergy := ?_
    hamiltonian_vac := kernel_mem_of_eq hHam hΩ
    semigroup_cls := fun t ht F =>
      (congrFun (hExp t ht) _).symm.trans
        ((σ.recon.expHam_cls t ht _).trans (hCl _).symm)
    shift_cls := fun v hv F =>
      (congrFun (hSp v) _).symm.trans
        ((σ.recon.transl_cls v hv _).trans (hCl _).symm)
    rotOp := σ.recon.rotOp
    rotOp_unitary := hU
    rotOp_cls := fun w F =>
      (σ.recon.rotOp_cls w _).trans (hCl _).symm
    rotOp_comm_semigroup := fun w t ht => by
      rw [hExpL t ht]
      exact hCov₁ t ht w
    rotOp_conj_shift := fun w v hv => by
      rw [hSpL, hSpL, inv_eq_inv (σ.recon.rotOp_unitary w)]
      exact hCov₂ w v hv }, ?_⟩
  · apply LinearMap.ext
    intro x
    have h := congrFun (hFG negEnergySet) x
    refine h.trans ?_
    have hset : euclideanToCoords negEnergySet =
        ⟨SpectralPoint.nonnegEnergy.1ᶜ, SpectralPoint.nonnegEnergy.2.compl⟩ := by
      apply Subtype.ext
      ext y
      simp [euclideanToCoords, negEnergySet, SpectralPoint.nonnegEnergy, energyCoord,
        SpectralPoint.energyOf]
    have hc : σ.jointMeasure
        ⟨SpectralPoint.nonnegEnergy.1ᶜ, SpectralPoint.nonnegEnergy.2.compl⟩ = 0 := hCar
    rw [hset, hc]
    rfl
  · exact {
      cls_eq := fun F => (hCl F).symm
      isJointSpectralMeasure := hJoint
      measure_eq := hFG
      rotOp_eq := fun _ => rfl
      vac_eq := rfl
      ham_eq := hHam
      mom_eq := hMom
      exp_eq := hExp
      spatial_eq := fun v _ => hSp v }
end YangMills.Construction.EuclideanFunctionals.OSDataOfReconProof

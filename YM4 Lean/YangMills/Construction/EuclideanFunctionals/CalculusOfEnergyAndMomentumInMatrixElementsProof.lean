import YangMills.Construction.EuclideanFunctionals.FirstFactsOnAReconstructionProof
import YangMills.Construction.EuclideanFunctionals.CalculusOfEnergyAndMomentumInMatrixElements
import YangMills.Construction.SpectralTheory.EverySelfAdjointOperatorIsResolved
import YangMills.Construction.SpectralTheory.MeasuresIntegralsProductsImagesAndTransportOfAProjectionValuedMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.HamMomMatrixCalculusProof
open YangMills.Construction.EuclideanFunctionals
open YangMills.Construction.EuclideanFunctionals.EuclidFunctionalWithRecon
open YangMills.Construction.EuclideanFunctionals.SpectralPoint
open YangMills.Construction.BorelSpectral
open YangMills.Construction.BorelSpectral.SpectralMeasure
open YangMills.Construction.SpectralMeasureCalculus (BoundedCalculusLaws MeasureLaws)
open YangMills.Construction.BorelCalculus (IsBoundedFn conjFn)
open YangMills.Construction.ResolvedOps (StronglyCommute IsDiagonalized)
theorem inner_apply_eq_polarization {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (x y : E) :
    ⟪x, T y⟫_ℂ = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4, (Complex.I ^ k)⁻¹ *
      ⟪x + Complex.I ^ k • y, T (x + Complex.I ^ k • y)⟫_ℂ := by
  have hsq : Complex.I ^ 2 = -1 := Complex.I_sq
  have hcube : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hsq]; ring
  have hinv : (-Complex.I)⁻¹ = Complex.I := by rw [inv_neg, Complex.inv_I, neg_neg]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero, pow_one, hsq,
    hcube, hinv, inv_one, Complex.inv_I, map_add, map_neg, map_smul, map_one, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_I, inv_neg, zero_add]
  generalize ⟪x, T x⟫_ℂ = a
  generalize ⟪x, T y⟫_ℂ = b
  generalize ⟪y, T x⟫_ℂ = c
  generalize ⟪y, T y⟫_ℂ = d
  ring_nf
  simp only [Complex.I_sq]
  ring
section
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
theorem isSelfAdjoint_hamAndMomenta (k : Fin 4) :
    OperatorTransport.IsSelfAdjointUnbounded (σ.hamAndMomenta k) := by
  induction k using Fin.cases with
  | zero => exact σ.recon.ham_selfAdjoint
  | succ j => exact σ.recon.mom_selfAdjoint j
theorem stronglyCommute_hamAndMomenta (i k : Fin 4) (hne : i ≠ k) :
    StronglyCommute (σ.hamAndMomenta i) (σ.hamAndMomenta k) := by apply _root_.YangMills.Construction.EuclideanFunctionals.ReconstructionFactsProof.stronglyCommute_hmFamily <;> assumption
theorem spatialEmbed_mem_spatialVecs (v : Fin 3 → ℝ) : spatialEmbed v ∈ spatialVecs := Fin.snoc_last (α := fun _ => ℝ) (0 : ℝ) v
theorem spatialShiftOp_eq_translOp (v : Fin 3 → ℝ) :
    σ.spatialShiftOp v = σ.translOp (spatialEmbed v) :=
  rfl
def kernelExt (t : ℝ) (v : R4) : EMPoints → ℂ :=
  zeroExtend SpectralPoint.nonnegEnergy.1 (laplaceFourierKernel t v)
theorem measurable_kernelExt (t : ℝ) (v : R4) :
    Measurable (kernelExt t v) := by apply _root_.YangMills.Construction.EuclideanFunctionals.ReconstructionFactsProof.measurable_zeroExtend_kernel <;> assumption
theorem kernelExt_of_mem (t : ℝ) (v : R4) {p : EMPoints}
    (hp : p ∈ SpectralPoint.nonnegEnergy.1) :
    kernelExt t v p =
      Complex.exp (-(t : ℂ) * (energyOf p : ℂ) + Complex.I * (dotR4 v (momentumOf p) : ℂ)) := by
  simp only [kernelExt, zeroExtend, dif_pos hp, laplaceFourierKernel]
theorem kernelExt_of_not_mem (t : ℝ) (v : R4) {p : EMPoints}
    (hp : p ∉ SpectralPoint.nonnegEnergy.1) : kernelExt t v p = 0 := by
  simp only [kernelExt, zeroExtend, dif_neg hp]
theorem norm_kernelExt_le {t : ℝ} (ht : 0 ≤ t) (v : R4) (p : EMPoints) :
    ‖kernelExt t v p‖ ≤ 1 := by
  by_cases hp : p ∈ SpectralPoint.nonnegEnergy.1
  · have hE : 0 ≤ energyOf p := hp
    rw [kernelExt_of_mem t v hp, Complex.norm_exp]
    have hre : (-(t : ℂ) * (energyOf p : ℂ) +
        Complex.I * (dotR4 v (momentumOf p) : ℂ)).re = -(t * energyOf p) := by
      simp
    rw [hre, Real.exp_le_one_iff]
    have := mul_nonneg ht hE
    linarith
  · rw [kernelExt_of_not_mem t v hp]
    simp
theorem isBoundedFn_kernelExt {t : ℝ} (ht : 0 ≤ t) (v : R4) :
    IsBoundedFn (kernelExt t v) := by apply _root_.YangMills.Construction.EuclideanFunctionals.ReconstructionFactsProof.isBoundedFn_zeroExtend_kernel <;> assumption
theorem dotR4_zero_left (q : Fin 3 → ℝ) : dotR4 0 q = 0 := by
  simp [dotR4, dot3]
theorem kernelExt_mul (t s : ℝ) :
    kernelExt t 0 * kernelExt s 0 = kernelExt (t + s) 0 := by
  funext p
  by_cases hp : p ∈ SpectralPoint.nonnegEnergy.1
  · simp only [Pi.mul_apply, kernelExt_of_mem _ _ hp, dotR4_zero_left, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp only [Pi.mul_apply, kernelExt_of_not_mem _ _ hp, mul_zero]
theorem conjFn_kernelExt (t : ℝ) :
    conjFn (kernelExt t 0) = kernelExt t 0 := by
  funext p
  by_cases hp : p ∈ SpectralPoint.nonnegEnergy.1
  · simp only [conjFn, kernelExt_of_mem _ _ hp, dotR4_zero_left, ← Complex.exp_conj]
    congr 1
    simp
  · simp only [conjFn, kernelExt_of_not_mem _ _ hp, map_zero]
theorem heatSemigroup_mul_translOp
    (hG : σ.SpectralGeneratorsAndKernel) {t : ℝ} (ht : 0 ≤ t) {v : R4}
    (hv : v ∈ spatialVecs) :
    σ.heatSemigroup t * σ.translOp v =
      σ.jointMeasure.integralOp (kernelExt t v) :=
  (hG.2.2.2 t ht v hv).2
theorem heatSemigroup_eq_integralOp
    (hG : σ.SpectralGeneratorsAndKernel) (hU : σ.TranslUnitaryGroup)
    {t : ℝ} (ht : 0 ≤ t) :
    σ.heatSemigroup t = σ.jointMeasure.integralOp (kernelExt t 0) := by
  have h := heatSemigroup_mul_translOp σ hG ht (v := 0) (by simp [spatialVecs])
  rwa [hU.2.1, mul_one] at h
theorem jointMeasureOfHamMom_holds
    (hGen : JointSpectralGenerators.JointMeasureGeneratorsCommutation)
    (hDiag : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hU : σ.TranslUnitaryGroup) (x y : σ.space) :
    σ.JointMeasureOfHamMom x y := by
  have hR : ∀ k, IsDiagonalized (σ.hamAndMomenta k) := fun k =>
    (hDiag.1 σ.space).2.2.2.1 _ (isSelfAdjoint_hamAndMomenta σ k)
  have hJ := ((hGen σ.space).1 4 (by norm_num) σ.hamAndMomenta hR
    (stronglyCommute_hamAndMomenta σ)).2.1
  refine ⟨hR, isSelfAdjoint_hamAndMomenta σ, stronglyCommute_hamAndMomenta σ, ?_, hJ, rfl, ?_⟩
  · intro v
    have h := hU.2.2.2.2.2.1 (spatialEmbed v) (spatialEmbed_mem_spatialVecs v)
    rw [spatialShiftOp_eq_translOp, h]
    rfl
  · exact ⟨⟨fun A => σ.jointMeasure.isStarProjection A, σ.jointMeasure.map_univ,
      fun z A hd => σ.jointMeasure.countablyAdditive z A hd⟩, fun _ => rfl⟩
theorem pairMeasurePolarization_holds
    (hM : MeasureLaws σ.jointMeasure)
    (hG : σ.SpectralGeneratorsAndKernel) (x y : σ.space) :
    σ.PairMeasurePolarization x y := by
  refine ⟨?_, fun k _ => hM.isFiniteMeasure _, ?_, ?_, ?_⟩
  · intro A
    have h := inner_apply_eq_polarization (σ.jointMeasure A) x y
    simp only [SpectralMeasure.inner_apply_self_eq_diagMeasure] at h
    exact h
  · rintro g hg ⟨b, hb⟩
    have hi : ∀ z : σ.space, Integrable g (σ.spectralMeasureAt z) := fun z => by
      have : IsFiniteMeasure (σ.spectralMeasureAt z) := hM.isFiniteMeasure z
      exact Integrable.of_bound hg.aestronglyMeasurable b (Filter.Eventually.of_forall hb)
    have h := hM.integral_eq g x y hg fun k _ => hi _
    refine h.trans ?_
    simp only [polarizedIntegral, ← Complex.inv_I, inv_pow]
    rfl
  · intro B hB A hsub
    have hz : σ.jointMeasure A = 0 := by
      refine ContinuousLinearMap.ext fun z => ?_
      have := hM.isFiniteMeasure z
      have hA := hM.real_apply z A
      have hBr := hM.real_apply z B
      rw [hB] at hBr
      have hmono : (σ.jointMeasure.diagMeasure z).real A.1 ≤
          (σ.jointMeasure.diagMeasure z).real B.1 :=
        measureReal_mono hsub (measure_ne_top _ _)
      have hsq : ‖σ.jointMeasure A z‖ ^ 2 ≤ 0 := by
        rw [← hA]
        refine hmono.trans (le_of_eq ?_)
        rw [hBr]
        simp
      have hn : ‖σ.jointMeasure A z‖ = 0 := by
        have := sq_nonneg ‖σ.jointMeasure A z‖
        exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm hsq this)
      simpa using hn
    refine ⟨hz, ?_⟩
    simp [pairSpectralMeasure, matrixCoeff, hz]
  · have hc := hG.2.2.1
    have hs : SpectralPoint.negEnergyBorel =
        ⟨SpectralPoint.nonnegEnergy.1ᶜ, SpectralPoint.nonnegEnergy.2.compl⟩ :=
      Subtype.ext (by
        ext p
        simp [SpectralPoint.negEnergyBorel, SpectralPoint.nonnegEnergy])
    rw [hs]
    exact hc
theorem heatMatrixElements_holds
    (hB : BoundedCalculusLaws σ.jointMeasure)
    (hG : σ.SpectralGeneratorsAndKernel) (hU : σ.TranslUnitaryGroup)
    (x y : σ.space) :
    σ.HeatMatrixElements x y := by
  intro t ht s hs v
  have hEt := heatSemigroup_eq_integralOp σ hG hU ht
  have hEs := heatSemigroup_eq_integralOp σ hG hU hs
  have hEts := heatSemigroup_eq_integralOp σ hG hU (add_nonneg ht hs)
  have hm := measurable_kernelExt t (0 : R4)
  have hb := isBoundedFn_kernelExt ht (0 : R4)
  have hvm := spatialEmbed_mem_spatialVecs v
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hEt]
    change star _ = _
    rw [← hB.conjugate _ hm hb, conjFn_kernelExt]
  · rw [hEt]
    refine (hB.norm_le _ SpectralPoint.nonnegEnergy hm hb hG.2.2.1).trans ?_
    exact Real.iSup_le (fun w => norm_kernelExt_le ht 0 w.1) zero_le_one
  · rw [hEt, hEs, hEts, ← hB.mul _ _ hm hb (measurable_kernelExt s 0)
      (isBoundedFn_kernelExt hs 0), kernelExt_mul]
  · exact (hG.2.2.2 t ht _ hvm).1
  · have h := heatSemigroup_mul_translOp σ hG ht hvm
    have happ : σ.heatSemigroup t (σ.spatialShiftOp v y) =
        σ.jointMeasure.integralOp (kernelExt t (spatialEmbed v)) y := by
      rw [← h]
      rfl
    rw [happ]
    exact hB.inner_eq _ (measurable_kernelExt t _)
      (isBoundedFn_kernelExt ht _) x y
end
theorem hamMomMatrixCalculus_holds (hBasic : ReconstructionBasicFacts)
    (hGen : JointSpectralGenerators.JointMeasureGeneratorsCommutation)
    (hDiag : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hCalc : SpectralMeasureCalculus.CalculusTheorem) :
    HamMomMatrixCalculus := by
  intro c S σ x y
  have hF := hBasic c S σ σ.space σ.recon
  have hG : σ.SpectralGeneratorsAndKernel := hF.1
  have hU : σ.TranslUnitaryGroup := hF.2.1
  have hC := hCalc σ.space 4 SpectralPoint.EMPoints σ.jointMeasure
  exact ⟨jointMeasureOfHamMom_holds σ hGen hDiag hU x y, pairMeasurePolarization_holds σ hC.1 hG x y,
    heatMatrixElements_holds σ hC.2.1 hG hU x y⟩
end YangMills.Construction.EuclideanFunctionals.HamMomMatrixCalculusProof

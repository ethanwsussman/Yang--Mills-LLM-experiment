import YangMills.Construction.TransferOperators.OperatorsOfATwistedActionOnAPowerOfG
import YangMills.Construction.TransferOperators.PeriodicStatesHaarMeasureCubicLatticesAndIntegralOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics YangMills.Construction.Schatten
open YangMills.Construction.TransferOperators.GibbsHaarKernels (HaarPiInvariance)
noncomputable section
namespace YangMills.Construction.TransferOperators.TwistedActionOperators
section Action
variable {J V : Type} (t h : J → V)
theorem twistedConjAction_twistedConjAction (g g' : V → Matrices.ComplexMatrix2.specialUnitary)
    (u : J → Matrices.ComplexMatrix2.specialUnitary) :
    twistedConjAction t h g (twistedConjAction t h g' u) = twistedConjAction t h (g * g') u := by
  funext b
  simp only [twistedConjAction, Pi.mul_apply, mul_inv_rev, mul_assoc]
theorem twistedConjAction_one (u : J → Matrices.ComplexMatrix2.specialUnitary) :
    twistedConjAction t h 1 u = u := by
  funext b
  simp [twistedConjAction]
end Action
section Operators
variable {J V : Type} [Finite J] {t h : J → V}
theorem measurePreserving_twistedConjAction (hH : HaarPiInvariance J)
    (g : V → Matrices.ComplexMatrix2.specialUnitary) :
    MeasurePreserving (twistedConjAction t h g) (Matrices.ComplexMatrix2.haarPi J)
      (Matrices.ComplexMatrix2.haarPi J) :=
  hH.1 (fun b => g (t b)) fun b => (g (h b))⁻¹
def compInvIsometry (t h : J → V) (hH : HaarPiInvariance J)
    (g : V → Matrices.ComplexMatrix2.specialUnitary) :
    HaarL2 J →ₗᵢ[ℂ] HaarL2 J :=
  Lp.compMeasurePreservingₗᵢ ℂ (twistedConjAction t h g⁻¹)
    (measurePreserving_twistedConjAction hH g⁻¹)
theorem isTwistedTranslation_compInvIsometry (hH : HaarPiInvariance J)
    (g : V → Matrices.ComplexMatrix2.specialUnitary) :
    IsTwistedTranslation t h g (compInvIsometry t h hH g).toContinuousLinearMap :=
  fun φ => Lp.coeFn_compMeasurePreserving φ (measurePreserving_twistedConjAction hH g⁻¹)
theorem eq_compInvIsometry (hH : HaarPiInvariance J)
    {g : V → Matrices.ComplexMatrix2.specialUnitary}
    {T : HaarL2 J →L[ℂ] HaarL2 J} (hT : IsTwistedTranslation t h g T) :
    T = (compInvIsometry t h hH g).toContinuousLinearMap :=
  ContinuousLinearMap.ext fun φ =>
    Lp.ext ((hT φ).trans (isTwistedTranslation_compInvIsometry hH g φ).symm)
theorem mul_eq_of_isTwistedTranslation (hH : HaarPiInvariance J)
    {g g' : V → Matrices.ComplexMatrix2.specialUnitary}
    {T T' T'' : HaarL2 J →L[ℂ] HaarL2 J}
    (hT : IsTwistedTranslation t h g T) (hT' : IsTwistedTranslation t h g' T')
    (hT'' : IsTwistedTranslation t h (g * g') T'') : T * T' = T'' := by
  refine ContinuousLinearMap.ext fun φ => Lp.ext ?_
  have h₁ := hT (T' φ)
  have h₂ := (measurePreserving_twistedConjAction (t := t) (h := h) hH
    g⁻¹).quasiMeasurePreserving.ae_eq_comp (hT' φ)
  refine (h₁.trans (h₂.trans ?_)).trans (hT'' φ).symm
  refine Filter.Eventually.of_forall fun u => ?_
  simp only [Function.comp_apply]
  rw [twistedConjAction_twistedConjAction, mul_inv_rev]
theorem eq_one_of_isTwistedTranslation {T : HaarL2 J →L[ℂ] HaarL2 J}
    (hT : IsTwistedTranslation t h (1 : V → Matrices.ComplexMatrix2.specialUnitary) T) :
    T = 1 := by
  refine ContinuousLinearMap.ext fun φ => Lp.ext ((hT φ).trans ?_)
  refine Filter.Eventually.of_forall fun u => ?_
  simp only [inv_one, twistedConjAction_one, one_apply_eq_self]
theorem kernelOperator_commute (hH : HaarPiInvariance J)
    {g : V → Matrices.ComplexMatrix2.specialUnitary}
    {T K : HaarL2 J →L[ℂ] HaarL2 J}
    {A : (J → Matrices.ComplexMatrix2.specialUnitary) × (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ}
    (hA : Continuous A)
    (hK : HasKernel (Matrices.ComplexMatrix2.haarPi J) A K)
    (hinv : ∀ u u' : J → Matrices.ComplexMatrix2.specialUnitary,
      A (twistedConjAction t h g⁻¹ u, twistedConjAction t h g⁻¹ u') = A (u, u'))
    (hT : IsTwistedTranslation t h g T) : K * T = T * K := by
  have hmp := measurePreserving_twistedConjAction (t := t) (h := h) hH g⁻¹
  refine ContinuousLinearMap.ext fun φ => Lp.ext ?_
  have hleft : (K (T φ) : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ)
      =ᵐ[Matrices.ComplexMatrix2.haarPi J]
      fun u => ∫ w, A (u, w) *
        (φ : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ) (twistedConjAction t h g⁻¹ w)
        ∂Matrices.ComplexMatrix2.haarPi J := by
    refine (hK (T φ)).trans (Filter.Eventually.of_forall fun u => ?_)
    refine integral_congr_ae ?_
    filter_upwards [hT φ] with w hw
    rw [hw]
  have hright : (T (K φ) : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ)
      =ᵐ[Matrices.ComplexMatrix2.haarPi J]
      fun u => ∫ w, A (u, w) *
        (φ : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ) (twistedConjAction t h g⁻¹ w)
        ∂Matrices.ComplexMatrix2.haarPi J := by
    refine (hT (K φ)).trans ((hmp.quasiMeasurePreserving.ae_eq_comp (hK φ)).trans
      (Filter.Eventually.of_forall fun u => ?_))
    show ∫ w, A (twistedConjAction t h g⁻¹ u, w) *
        (φ : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ) w
        ∂Matrices.ComplexMatrix2.haarPi J = _
    have hmeas : AEStronglyMeasurable
        (fun w => A (twistedConjAction t h g⁻¹ u, w) *
          (φ : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ) w)
        (Measure.map (twistedConjAction t h g⁻¹) (Matrices.ComplexMatrix2.haarPi J)) := by
      rw [hmp.map_eq]
      exact (hA.comp (Continuous.prodMk_right _)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable φ)
    calc ∫ w, A (twistedConjAction t h g⁻¹ u, w) *
          (φ : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ) w
          ∂Matrices.ComplexMatrix2.haarPi J
        = ∫ w, A (twistedConjAction t h g⁻¹ u, w) *
            (φ : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ) w
            ∂Measure.map (twistedConjAction t h g⁻¹) (Matrices.ComplexMatrix2.haarPi J) := by
          rw [hmp.map_eq]
      _ = ∫ w, A (twistedConjAction t h g⁻¹ u, twistedConjAction t h g⁻¹ w) *
            (φ : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ) (twistedConjAction t h g⁻¹ w)
            ∂Matrices.ComplexMatrix2.haarPi J :=
          integral_map hmp.aemeasurable hmeas
      _ = ∫ w, A (u, w) *
            (φ : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ) (twistedConjAction t h g⁻¹ w)
            ∂Matrices.ComplexMatrix2.haarPi J := by simp only [hinv]
  exact hleft.trans hright.symm
end Operators
theorem statement_holds (hS : GibbsHaarKernels.Statement) : Statement := by
  intro J V _ _ t h
  have hH : HaarPiInvariance J := hS.2.1 J
  refine ⟨fun g => ⟨_, isTwistedTranslation_compInvIsometry hH g⟩, fun ρ hρ => ?_⟩
  have hmul : ∀ g g', ρ g * ρ g' = ρ (g * g') :=
    fun g g' => mul_eq_of_isTwistedTranslation hH (hρ g) (hρ g') (hρ (g * g'))
  have hone : ρ 1 = 1 := eq_one_of_isTwistedTranslation (hρ 1)
  refine ⟨fun g => ?_, fun g φ ψ => ?_, hmul, hone, fun A hA hinv g => ?_⟩
  · have hl : ρ g⁻¹ * ρ g = 1 := by rw [hmul, inv_mul_cancel, hone]
    have hr : ρ g * ρ g⁻¹ = 1 := by rw [hmul, mul_inv_cancel, hone]
    exact Function.bijective_iff_has_inverse.2
      ⟨ρ g⁻¹, fun φ => DFunLike.congr_fun hl φ, fun φ => DFunLike.congr_fun hr φ⟩
  · rw [eq_compInvIsometry hH (hρ g)]
    exact (compInvIsometry t h hH g).inner_map_map φ ψ
  · exact kernelOperator_commute hH hA ((hS.2.2.2 J).1 A hA).2.1 (hinv g⁻¹) (hρ g)
end YangMills.Construction.TransferOperators.TwistedActionOperators
end

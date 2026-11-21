import YangMills.Construction.ReflectionPositivity.WeightsFormAndSeriesOfASplitTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def SplitTorusReflectionPositivity : Prop :=
  ∀ (β : ℝ), 0 < β → ∀ (Γ : PeriodSublattice 1) (v : AmbientSpace) (hv : v ∈ NormalFamilies.normalSet) (z : ℤ),
    Γ.SplitsAlongWithHalfPeriod v z → ∀ (c : ℝ) (hc : NormalFamilies.IsAllowedLevel 1 v c),
      let P : NormalFamilies.NormalLevelPair 1 := ⟨v, hv, c, hc⟩
      PeriodSublattice.PreservesFiniteMeasure (Γ.pullbackField P.reflectSymmetry)
        (Γ.gibbsMeasure β) ∧
      (∃ (X : Type) (_ : MeasurableSpace X) (m : Measure X)
        (Ψ : ↥(Γ.plusAlgebra v z c) →ₗ[ℂ] (X → ℂ)),
        IsFiniteMeasure m ∧ (∀ F, Measurable (Ψ F)) ∧
        (∀ F x, ‖Ψ F x‖ ≤ PeriodSublattice.supNorm F.1) ∧
        ∀ F G, Γ.reflectionPairing β P G.1 F.1 = ∫ x, conj (Ψ G x) * Ψ F x ∂m) ∧
      (∀ F ∈ Γ.plusAlgebra v z c, ∀ G ∈ Γ.plusAlgebra v z c,
        ∀ K ∈ Γ.plusAlgebra v z c, ∀ w : ℂ,
          Γ.reflectionPairing β P G (w • F + K) =
            w * Γ.reflectionPairing β P G F + Γ.reflectionPairing β P G K ∧
          Γ.reflectionPairing β P (w • F + K) G =
            conj w * Γ.reflectionPairing β P F G + Γ.reflectionPairing β P K G) ∧
      (∀ F ∈ Γ.plusAlgebra v z c, ∀ G ∈ Γ.plusAlgebra v z c,
        Γ.reflectionPairing β P G F = conj (Γ.reflectionPairing β P F G)) ∧
      (∀ F ∈ Γ.plusAlgebra v z c, 0 ≤ Γ.reflectionPairing β P F F) ∧
      (∃ (C : Type) (_ : Countable C) (α : C → ℝ) (H : C → Γ.QuotientField → ℂ),
        (∀ γ, 0 ≤ α γ) ∧
        HasSum α (Real.exp (β * (Γ.numSplitPlaquettes v z c : ℝ))) ∧
        (∀ γ, H γ ∈ Γ.plusAlgebra v z c) ∧
        (∀ γ, PeriodSublattice.supNorm (H γ) ≤ 1) ∧
        (∀ U, Summable fun γ => ‖(α γ : ℂ) * H γ U * Γ.conjReflect P (H γ) U‖) ∧
        TendstoUniformly
          (fun (s : Finset C) U => ∑ γ ∈ s, (α γ : ℂ) * H γ U * Γ.conjReflect P (H γ) U)
          (Γ.integrateOut (Γ.crossingLinks v z c)
            fun U => (Γ.splitFaceWeight β v z c U : ℂ))
          Filter.atTop) ∧
      (∀ E : Γ.QuotientField → ℝ, (fun U => (E U : ℂ)) ∈ Γ.plusAlgebra v z c →
        IsProbabilityMeasure (Γ.perturbedReflMeasure β P E) ∧
        PeriodSublattice.PreservesFiniteMeasure (Γ.pullbackField P.reflectSymmetry)
          (Γ.perturbedReflMeasure β P E) ∧
        ∀ F : Γ.QuotientField → ℂ, F ∈ Γ.plusAlgebra v z c ∨ F ∈ Γ.minusAlgebra v z c →
          0 ≤ ∫ U, Γ.conjReflect P F U * F U *
            (Γ.perturbedReflWeight β P E U : ℂ) ∂Γ.quotientHaar)
end YangMills.Construction.InfiniteLattice

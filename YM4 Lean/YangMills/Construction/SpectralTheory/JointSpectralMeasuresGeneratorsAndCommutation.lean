import YangMills.Construction.SpectralTheory.FunctionsOfSelfAdjointOperators
import YangMills.Construction.SpectralTheory.ResolvedOperatorsAndTheirJointSpectralMeasure
import Mathlib
set_option autoImplicit false
open Set
open scoped NNReal
noncomputable section
namespace YangMills.Construction.JointSpectralGenerators
open HilbertSpaceBasics (UnboundedOp ofBounded)
open OperatorTransport (IsContractionSemigroup IsNonnegUnbounded IsUnitaryGroup)
open BorelSpectral
open BorelSpectral.SpectralMeasure (OpCommutes)
open SpectralTheorem (spectralIntegralOp spectralMeasure)
open SelfAdjointFunctions (fnCalc expI)
open ResolvedOps
def JointMeasureGeneratorsCommutation : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    (∀ (r : ℕ) (hr : 1 ≤ r) (A : Fin r → UnboundedOp H), (∀ k, IsDiagonalized (A k)) →
      (∀ j k, j ≠ k → StronglyCommute (A j) (A k)) →
      (∃! E : SpectralMeasure (univ : Set (Fin r → ℝ)) H, IsJointSpectralMeasure A E) ∧
      IsJointSpectralMeasure A (jointSpectralMeasure hr A) ∧
      (∀ k, (jointSpectralMeasure hr A).coordMarginal k = spectralMeasure (A k)) ∧
      (∀ (k : Fin r) (u : ℝ → ℂ), Measurable u →
        fnCalc (A k) u = spectralIntegralOp (jointSpectralMeasure hr A) fun y => u (y.1 k)) ∧
      (∀ k, A k = spectralIntegralOp (jointSpectralMeasure hr A) fun y => ((y.1 k : ℝ) : ℂ)) ∧
      (∀ B : H →L[ℂ] H, (∀ k, OpCommutes B (spectralMeasure (A k))) →
        OpCommutes B (jointSpectralMeasure hr A)) ∧
      ∀ (C : BorelSubsets (univ : Set (Fin r → ℝ))) (Φ : C.1 → ℂ),
        (jointSpectralMeasure hr A).IsCarriedBy C → Measurable Φ → (∃ c : ℝ, ∀ y, ‖Φ y‖ ≤ c) →
          (jointSpectralMeasure hr A).setIntegralOp C Φ =
            ofBounded ((jointSpectralMeasure hr A).integralOpOn C Φ) ∧
          ‖(jointSpectralMeasure hr A).integralOpOn C Φ‖ ≤ ⨆ y, ‖Φ y‖) ∧
    (∀ T : ℝ≥0 → H →L[ℂ] H, IsContractionSemigroup T →
      ∃! A : UnboundedOp H, IsDiagonalized A ∧ IsNonnegUnbounded A ∧
        ∀ t : ℝ≥0, T t = expComplex A ((t : ℝ) : ℂ)) ∧
    (∀ U : ℝ → H →ₗ[ℂ] H, IsUnitaryGroup U →
      ∃! B : UnboundedOp H, IsDiagonalized B ∧
        ∀ s : ℝ, U s = (expI B s : H →ₗ[ℂ] H)) ∧
    (∀ A B : UnboundedOp H, IsDiagonalized A → IsNonnegUnbounded A → IsDiagonalized B →
      (∀ (t : ℝ≥0) (s : ℝ),
        Commute (expComplex A ((t : ℝ) : ℂ)) (expI B s)) →
      StronglyCommute A B) ∧
    (∀ B B' : UnboundedOp H, IsDiagonalized B → IsDiagonalized B' →
      (∀ s s' : ℝ, Commute (expI B s) (expI B' s')) →
      StronglyCommute B B') ∧
    ∀ A B : UnboundedOp H, IsDiagonalized A → IsNonnegUnbounded A → IsDiagonalized B →
      (∀ C : H →L[ℂ] H, (∀ t : ℝ≥0, Commute C (expComplex A ((t : ℝ) : ℂ))) →
        OpCommutes C (spectralMeasure A)) ∧
      ∀ C : H →L[ℂ] H, (∀ s : ℝ, Commute C (expI B s)) →
        OpCommutes C (spectralMeasure B)
end YangMills.Construction.JointSpectralGenerators

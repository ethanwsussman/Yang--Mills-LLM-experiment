import YangMills.Construction.EnergyMomentum.LatticeBasics
import YangMills.Construction.JointSpectrum.SpectralIntegral
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction
open JointSpectrum JointSpectrum.SpectralIntegral
namespace JointSpectrum.CalculusApplications
def CalculusApplicationsStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : Type) [Fintype J] [Nonempty J] (S : CommutingFamily H J),
    (∀ f : SpectralDomain J → ℝ, Measurable f → (∃ M : ℝ, ∀ p, |f p| ≤ M) →
      ∃ C : H →L[ℂ] H, ⇑C = spectralIntegral S (fun p => (f p : ℂ)) ∧ IsSelfAdjoint C ∧
        (0 ≤ C ↔ jointSpectralMeasure S {p | f p < 0} = 0)) ∧
    (∀ f : SpectralDomain J → ℂ, Measurable f → (∃ M : ℝ, ∀ p, ‖f p‖ ≤ M) →
      ∃ P C : H →L[ℂ] H, ⇑P = jointSpectralMeasure S {p | f p = 0} ∧ ⇑C = spectralIntegral S f ∧
        HilbertSpaceBasics.IsOrthProjOnto P (LatticeBasics.nullSet C)) ∧
    (∃ P : H →L[ℂ] H, ⇑P = jointSpectralMeasure S {p | (p.1 : ℝ) = 0} ∧
      HilbertSpaceBasics.IsOrthProjOnto P (LatticeBasics.nullSet S.A)) ∧
    (∃ P : H →L[ℂ] H, ⇑P = jointSpectralMeasure S {p | (p.1 : ℝ) = 1} ∧
      HilbertSpaceBasics.IsOrthProjOnto P (LatticeBasics.nullSet (1 - S.A))) ∧
    (∀ α : J, ∃ P : H →L[ℂ] H, ⇑P = jointSpectralMeasure S {p | p.2 α = 1} ∧
      HilbertSpaceBasics.IsOrthProjOnto P
        (LatticeBasics.nullSet (1 - (S.B α : H →L[ℂ] H)))) ∧
    (∀ (F : ℕ → SpectralDomain J → ℂ) (f : SpectralDomain J → ℂ),
      (∀ n, Measurable (F n)) → Measurable f → (∃ M : ℝ, ∀ n p, ‖F n p‖ ≤ M) →
      (∀ p, Tendsto (fun n => F n p) atTop (𝓝 (f p))) →
      ∃ (C : ℕ → H →L[ℂ] H) (D : H →L[ℂ] H), (∀ n, ⇑(C n) = spectralIntegral S (F n)) ∧
        ⇑D = spectralIntegral S f ∧ HilbertSpaceBasics.TendstoStrongly C atTop D) ∧
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (S' : CommutingFamily H' J) (Y : H →ₗ[ℂ] H'), LatticeBasics.IsIsometricMap Y →
      (∀ ψ, Y (S.A ψ) = S'.A (Y ψ)) →
      (∀ (α : J) (ψ : H), Y ((S.B α : H →L[ℂ] H) ψ) = (S'.B α : H' →L[ℂ] H') (Y ψ)) →
      (∀ ψ, ScalarSpectralMeasures.spectralMeasure S' (Y ψ) =
        ScalarSpectralMeasures.spectralMeasure S ψ) ∧
      (∀ f : SpectralDomain J → ℂ, Measurable f → ∀ ψ,
        (ψ ∈ integralDomain S f ↔ Y ψ ∈ integralDomain S' f) ∧
          (ψ ∈ integralDomain S f → spectralIntegral S' f (Y ψ) = Y (spectralIntegral S f ψ))) ∧
      (∀ Δ : Set (SpectralDomain J), MeasurableSet Δ → ∀ ψ,
        jointSpectralMeasure S' Δ (Y ψ) = Y (jointSpectralMeasure S Δ ψ)) ∧
      ∀ hY : LatticeBasics.IsUnitaryLinearMap Y, ∀ Δ : Set (SpectralDomain J), MeasurableSet Δ →
        jointSpectralMeasure S' Δ =
          Y ∘ jointSpectralMeasure S Δ ∘
            (LinearIsometryEquiv.ofSurjective (⟨Y, hY.1⟩ : H →ₗᵢ[ℂ] H') hY.2).symm ∧
        (jointSpectralMeasure S' Δ = 0 ↔ jointSpectralMeasure S Δ = 0)
end JointSpectrum.CalculusApplications
end YangMills.Construction

import YangMills.Construction.HilbertSpace.UnitaryConjugation
import YangMills.Construction.SpectralTheory.SelfAdjointSpectralMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.BorelSpectral.SpectralMeasure
open HilbertSpaceBasics (UnboundedOp)
open SpectralTheorem (spectralIntegralOp)
variable {n n' : ℕ} {Y : Set (Fin n → ℝ)} {Y' : Set (Fin n' → ℝ)} {H H' : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
def matrixCoeff (E : SpectralMeasure Y H) (φ ψ : H) (Δ : BorelSubsets Y) : ℂ :=
  ⟪φ, E Δ ψ⟫_ℂ
def setIntegralOp (E : SpectralMeasure Y H) (C : BorelSubsets Y) (g : C.1 → ℂ) : UnboundedOp H :=
  spectralIntegralOp E (zeroExtend C.1 g)
def unitaryPushforward (E : SpectralMeasure Y H) {V : H →ₗ[ℂ] H'}
    (hV : OperatorTransport.IsUnitaryMap V) (Δ : BorelSubsets Y) : H' →ₗ[ℂ] H' :=
  V ∘ₗ (E Δ : H →ₗ[ℂ] H) ∘ₗ hV.inv
def restrictTo (E : SpectralMeasure Y H) (C : BorelSubsets Y) (Δ : BorelSubsets C.1) : H →L[ℂ] H :=
  E ⟨Subtype.val '' Δ.1, C.2.subtype_image Δ.2⟩
def Commutes {Y₁ : Set (Fin n → ℝ)} {Y₂ : Set (Fin n' → ℝ)}
    (E₁ : SpectralMeasure Y₁ H) (E₂ : SpectralMeasure Y₂ H) : Prop :=
  ∀ Δ₁ Δ₂, Commute (E₁ Δ₁) (E₂ Δ₂)
def OpCommutes (B : H →L[ℂ] H) (E : SpectralMeasure Y H) : Prop :=
  ∀ Δ, Commute B (E Δ)
end YangMills.Construction.BorelSpectral.SpectralMeasure

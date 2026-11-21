import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
namespace YangMills.Construction.TorusLumps
def markAlongLog {k : ℕ} (ψ : ℍ[ℝ] → ℝ) (Ξ : (Fin k → ℝ) →L[ℝ] imaginaryQuaternions) (g : UnitQuaternion)
    (f : (Fin k → ℝ) → ℍ[ℝ]) (τ : Fin k → ℝ) : ℝ :=
  ψ (((minimalLog (g * (expUnit (Ξ τ))⁻¹) : imaginaryQuaternions) : ℍ[ℝ]) - f τ)
def LogMarkSmoothness : Prop :=
  ∀ (ψ : ℍ[ℝ] → ℝ) (ρ : ℝ), ρ ≤ 1 / 64 → ContDiff ℝ 40 ψ →
    (∀ j, ∃ B : ℝ, ∀ v, ‖iteratedFDeriv ℝ j ψ v‖ ≤ B) → (∀ v, ρ ≤ ‖v‖ → ψ v = 0) →
    ∃ q : ℝ → ℝ → ℝ, ∀ (k : ℕ) (U : Set (Fin k → ℝ)) (f : (Fin k → ℝ) → ℍ[ℝ]),
      IsOpen U → ContDiffOn ℝ 40 f U → (∀ τ ∈ U, ‖f τ‖ ≤ 1) →
      (∀ (Ξ : (Fin k → ℝ) →L[ℝ] imaginaryQuaternions) (g : UnitQuaternion),
        ContDiffOn ℝ 40 (markAlongLog ψ Ξ g f) U ∧
        ∀ τ ∈ U, ∀ F S : ℝ, ‖Ξ‖ ≤ S → (∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i f τ‖ ≤ F) →
          ∀ j, 1 ≤ j → j ≤ 40 → ‖iteratedFDeriv ℝ j (markAlongLog ψ Ξ g f) τ‖ ≤ q F S) ∧
      (∀ a₀ : ℍ[ℝ], ContDiffOn ℝ 40 (fun τ => ψ (a₀ - f τ)) U ∧
        ∀ τ ∈ U, ∀ F S : ℝ, (∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i f τ‖ ≤ F) →
          ∀ j, 1 ≤ j → j ≤ 40 → ‖iteratedFDeriv ℝ j (fun τ => ψ (a₀ - f τ)) τ‖ ≤ q F S)
end YangMills.Construction.TorusLumps
end

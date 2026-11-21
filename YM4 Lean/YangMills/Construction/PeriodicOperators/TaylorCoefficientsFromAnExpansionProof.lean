import YangMills.Construction.PeriodicOperators.TaylorCoefficientsFromAnExpansion
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfAProductOfLocalOperatorFunctionsProof
import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open YangMills.Construction.Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
open YangMills.Construction.TorusMetric (euclidNormVec)
namespace ExpansionCoefficients
section ExtensionByZero
variable {P : PeriodicData} {A : Set P.Carrier} {m : ℕ}
theorem norm_fieldExtend_le (σ : Fin m ≃ A)
    (w : YangMills.Construction.Coordinates.ComplexCoordinates m) (y : P.Carrier) :
    ‖fieldExtend σ w y‖ ≤ ‖w‖ := by apply _root_.YangMills.Construction.PeriodicOperators.LocalTorusMatrices.norm_fieldExtend_le <;> assumption
theorem fieldExtend_zero (σ : Fin m ≃ A) :
    fieldExtend σ (0 : YangMills.Construction.Coordinates.ComplexCoordinates m) = 0 := by apply _root_.YangMills.Construction.PeriodicOperators.LeibnizRuleProof.fieldExtend_zero <;> assumption
theorem fieldExtend_fieldValues (σ : Fin m ≃ A) (φ : P.Carrier → ℂ) {y : P.Carrier} (hy : y ∈ A) :
    fieldExtend σ (fieldValues σ φ) y = φ y := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.fieldExtend_fieldValues <;> assumption
def fieldExtendₗ (σ : Fin m ≃ A) :
    YangMills.Construction.Coordinates.ComplexCoordinates m →ₗ[ℂ] P.Carrier → ℂ :=
  Function.ExtendByZero.linearMap ℂ fun k => ((σ k : A) : P.Carrier)
theorem fieldExtendₗ_apply (σ : Fin m ≃ A)
    (w : YangMills.Construction.Coordinates.ComplexCoordinates m) :
    fieldExtendₗ σ w = fieldExtend σ w :=
  rfl
end ExtensionByZero
theorem claim_holds (hPar : ParameterIndependence.Claim) : Claim := by
  intro P Q Q' hP hQ hQ' A hA x' x D hD f B r K hr hsymm hread hbound φ φ'
  obtain ⟨ρ, L₀, hA₀⟩ := hA
  obtain ⟨c, hc⟩ := (hD.image fun y => euclidNormVec (P.pos y - Q'.pos x')).bddAbove
  have hDnear : ∀ y ∈ D, y ∈ nearIndices P (Q'.pos x') (max L₀ c) := fun y hy =>
    (hc (mem_image_of_mem _ hy)).trans (le_max_right _ _)
  have hAL : IsLocalWith P Q Q' A ρ (max L₀ c) :=
    (hPar P Q Q' hP hQ hQ' A ρ L₀ ρ L₀ hA₀ hA₀).1.1 ρ (max L₀ c) hA₀.radius_pos le_rfl
      (le_max_left _ _)
  obtain ⟨m, σ, -, -, -⟩ := hAL.holo_entry x' x
  have hexp : IsSecondOrderExpansion (entryFun A x' x σ) (f ∘ₗ fieldExtendₗ σ)
      (B.compl₁₂ (fieldExtendₗ σ) (fieldExtendₗ σ)) := by
    refine ⟨fun w w' => by simpa using hsymm (fieldExtendₗ σ w) (fieldExtendₗ σ w'), ?_⟩
    refine IsBigO.of_bound |K| ?_
    filter_upwards [Metric.ball_mem_nhds
      (0 : YangMills.Construction.Coordinates.ComplexCoordinates m) hr] with w hw
    have hw' : ‖w‖ ≤ r := by
      have hlt : ‖w‖ < r := by simpa using hw
      exact hlt.le
    have hb := hbound (fieldExtend σ w) ‖w‖ hw' fun y _ => norm_fieldExtend_le σ w y
    have hat0 : entryFun A x' x σ 0 = A 0 x' x := by
      show A (fieldExtend σ 0) x' x = A 0 x' x
      rw [fieldExtend_zero]
    have hsub : entryFun A x' x σ w - (entryFun A x' x σ 0 + (f ∘ₗ fieldExtendₗ σ) w +
        (1 / 2 : ℂ) * (B.compl₁₂ (fieldExtendₗ σ) (fieldExtendₗ σ)) w w) =
        A (fieldExtend σ w) x' x - A 0 x' x - f (fieldExtend σ w) -
          (1 / 2 : ℂ) * B (fieldExtend σ w) (fieldExtend σ w) := by
      rw [hat0]
      simp only [LinearMap.comp_apply, LinearMap.compl₁₂_apply, fieldExtendₗ_apply, entryFun]
      ring
    rw [hsub]
    have hcube : 0 ≤ ‖w‖ ^ 3 := pow_nonneg (norm_nonneg w) 3
    calc _ ≤ K * ‖w‖ ^ 3 := hb
      _ ≤ |K| * ‖w‖ ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self K) hcube
      _ = |K| * ‖‖w‖ ^ 3‖ := by simp
  have hInd := (hPar P Q Q' hP hQ hQ' A ρ (max L₀ c) ρ (max L₀ c) hAL hAL).2.1.1 φ φ' x' x
  have hagree : ∀ ψ : P.Carrier → ℂ, ∀ y ∈ D, fieldExtend σ (fieldValues σ ψ) y = ψ y :=
    fun ψ y hy => fieldExtend_fieldValues σ ψ (hDnear y hy)
  have hlin := hInd.1.2.2 ρ (max L₀ c) hAL m σ _ _ hexp
  have hquad := hInd.2.2.2 ρ (max L₀ c) hAL m σ _ _ hexp
  simp only [LinearMap.comp_apply, LinearMap.compl₁₂_apply, fieldExtendₗ_apply] at hlin hquad
  refine ⟨hlin.symm.trans (hread _ _ (hagree φ)).1, hquad.symm.trans ?_⟩
  calc B (fieldExtend σ (fieldValues σ φ)) (fieldExtend σ (fieldValues σ φ'))
      = B φ (fieldExtend σ (fieldValues σ φ')) := (hread _ _ (hagree φ)).2 _
    _ = B (fieldExtend σ (fieldValues σ φ')) φ := hsymm _ _
    _ = B φ' φ := (hread _ _ (hagree φ')).2 _
    _ = B φ φ' := hsymm _ _
end ExpansionCoefficients
end YangMills.Construction.PeriodicOperators
end

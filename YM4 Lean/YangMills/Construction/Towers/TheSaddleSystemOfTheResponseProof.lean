import YangMills.Construction.PeriodicOperators.CalculusOfSymbols
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.Towers.TheInversesThatFormTheResponse
import YangMills.Construction.Towers.TheSaddleSystemOfTheResponse
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseSaddle
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.SymbolCalculus
open YangMills.Construction.PeriodicOperators.StripSymbols
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
open YangMills.Construction.Tower.BackgroundFieldResponse (responseKernel responseDefect xiInv blockCovarianceInv)
theorem saddle_of_right_invs (hS : StripSymbols.Claim)
    (hC : SymbolCalculus.Claim) {I₀ I₁ : PeriodicData} (i₀ : IsPeriodic I₀)
    (i₁ : IsPeriodic I₁) {Q : I₁.Carrier → I₀.Carrier → ℂ} {Qt : I₀.Carrier → I₁.Carrier → ℂ}
    {Ξ Ξi : I₀.Carrier → I₀.Carrier → ℂ} {Ci : I₁.Carrier → I₁.Carrier → ℂ}
    (pQ : IsPeriodicKernel I₀ I₁ Q) (pQt : IsPeriodicKernel I₁ I₀ Qt)
    (pΞ : IsPeriodicKernel I₀ I₀ Ξ) (pΞi : IsPeriodicKernel I₀ I₀ Ξi)
    (pCi : IsPeriodicKernel I₁ I₁ Ci)
    (hΞ : compKernel Ξ Ξi = idKernel I₀)
    (hCi : compKernel (compKernel (compKernel Q Ξi) Qt) Ci = idKernel I₁) :
    ResponseProperties.CompSummableEverywhere Q (compKernel (compKernel Ξi Qt) Ci) ∧
      compKernel Q (compKernel (compKernel Ξi Qt) Ci) = idKernel I₁ ∧
      ResponseProperties.CompSummableEverywhere (Ξ - compKernel Qt Q) (compKernel (compKernel Ξi Qt) Ci) ∧
      ResponseProperties.CompSummableEverywhere Qt (fun a b => Ci a b - idKernel I₁ a b) ∧
      compKernel (Ξ - compKernel Qt Q) (compKernel (compKernel Ξi Qt) Ci) =
        compKernel Qt (fun a b => Ci a b - idKernel I₁ a b) := by
  have unit₀ := (hC I₁ I₀ i₁ i₀).2.2.2.2.2.2.2.1
  have law₀₀ := (hC I₀ I₀ i₀ i₀).2.2.2.2.2.2.2.2 I₁ i₁
  have law₁₀ := (hC I₁ I₀ i₁ i₀).2.2.2.2.2.2.2.2 I₁ i₁
  have law₀₁ := (hC I₀ I₁ i₀ i₁).2.2.2.2.2.2.2.2 I₁ i₁
  have law₁₀' := (hC I₁ I₀ i₁ i₀).2.2.2.2.2.2.2.2 I₀ i₀
  have pA := (law₀₀.1 Ξi Qt pΞi pQt).2
  have ph := (law₁₀.1 _ Ci pA pCi).2
  have pB := (law₁₀.1 Qt Ci pQt pCi).2
  have pQtQ := (law₁₀'.1 Qt Q pQt pQ).2
  have pId : IsPeriodicKernel I₁ I₁ (idKernel I₁) := (unit₀ Qt pQt).1
  have a₁ := ((hS.2.1 I₀ I₀ i₀ i₀).2.2.2 I₁ I₁ i₁ i₁ Ξi Qt Ci pΞi pQt pCi).2.2.2.2.2.2.2.2
  have a₂ := ((hS.2.1 I₀ I₁ i₀ i₁).2.2.2 I₁ I₁ i₁ i₁ Q _ Ci pQ pA pCi).2.2.2.2.2.2.2.2
  have a₃ := ((hS.2.1 I₀ I₁ i₀ i₁).2.2.2 I₀ I₁ i₀ i₁ Q Ξi Qt pQ pΞi pQt).2.2.2.2.2.2.2.2
  have a₄ := ((hS.2.1 I₀ I₀ i₀ i₀).2.2.2 I₀ I₁ i₀ i₁ Ξ Ξi _ pΞ pΞi pB).2.2.2.2.2.2.2.2
  have a₅ := ((hS.2.1 I₁ I₀ i₁ i₀).2.2.2 I₀ I₁ i₀ i₁ Qt Q _ pQt pQ ph).2.2.2.2.2.2.2.2
  have hQh : compKernel Q (compKernel (compKernel Ξi Qt) Ci) = idKernel I₁ := by
    rw [← a₂, ← a₃, hCi]
  have hΞh : compKernel Ξ (compKernel (compKernel Ξi Qt) Ci) = compKernel Qt Ci := by
    rw [a₁, ← a₄, hΞ]
    exact (unit₀ _ pB).2.2.2.2.2
  have hQt : compKernel Qt (idKernel I₁) = Qt := (unit₀ Qt pQt).2.2.2.2.1
  have hQtQh : compKernel (compKernel Qt Q) (compKernel (compKernel Ξi Qt) Ci) = Qt := by
    rw [a₅, hQh, hQt]
  have d₁ := law₀₀.2 Ξ (compKernel Qt Q) _ _ 1 (-1) pΞ pQtQ ph ph
  have d₂ := law₁₀.2 Qt Qt Ci (idKernel I₁) 1 (-1) pQt pQt pCi pId
  have hX : Ξ - compKernel Qt Q = fun a b => (1 : ℂ) * Ξ a b + -1 * compKernel Qt Q a b := by
    funext a b
    simp [sub_eq_add_neg]
  have hν : (fun a b => Ci a b - idKernel I₁ a b) =
      fun a b => (1 : ℂ) * Ci a b + -1 * idKernel I₁ a b := by
    funext a b
    simp [sub_eq_add_neg]
  refine ⟨(law₀₁.1 Q _ pQ ph).1, hQh, ?_, ?_, ?_⟩
  · rw [hX]
    exact d₁.2.2.2.2.2.1.1
  · rw [hν]
    exact d₂.2.2.2.2.2.2.1.1
  · rw [hX, hν]
    have e₁ : compKernel (fun a b => (1 : ℂ) * Ξ a b + -1 * compKernel Qt Q a b)
        (compKernel (compKernel Ξi Qt) Ci) =
        fun a b => (1 : ℂ) * compKernel Ξ (compKernel (compKernel Ξi Qt) Ci) a b +
          -1 * compKernel (compKernel Qt Q) (compKernel (compKernel Ξi Qt) Ci) a b :=
      d₁.2.2.2.2.2.2.2.2.2.1
    have e₂ : compKernel Qt (fun a b => (1 : ℂ) * Ci a b + -1 * idKernel I₁ a b) =
        fun a b => (1 : ℂ) * compKernel Qt Ci a b +
          -1 * compKernel Qt (idKernel I₁) a b :=
      d₂.2.2.2.2.2.2.2.2.2.2.1
    rw [e₁, e₂, hΞh, hQtQh, hQt]
theorem saddleEquations_holds (hInv : ResponseInverses.Claim) (hS : StripSymbols.Claim)
    (hC : SymbolCalculus.Claim) (hT : TowerIndexSets.Claim)
    (hFree : FreeOperators.FreeOperatorsArePeriodic) : SaddleEquations := by
  intro L hL k hk
  obtain ⟨δ₀, -, hall⟩ := hInv
  obtain ⟨-, -, hOps⟩ := hall L hL k hk
  obtain ⟨hMaps, hFin⟩ := hFree.2 L hL k hk
  obtain ⟨f₁, e₁, f₂, f₃, e₂⟩ := saddle_of_right_invs hS hC
    (hT L hL k 0 (Nat.zero_le k)).2.1 (hT L hL k k le_rfl).2.1
    (Q := (trivialRescaledOperators L k).Q) (Qt := (trivialRescaledOperators L k).Qt)
    (Ξ := (trivialRescaledOperators L k).Xi)
    (Ξi := xiInv L k) (Ci := blockCovarianceInv L k)
    hMaps.edgeAverage.finite_range.1 hFin.edgeAverage_transpose.1 hFin.Xi.1
    hOps.xi.periodic hOps.cov.periodic hOps.xi.right_inv hOps.cov.right_inv
  exact ⟨f₁, e₁, f₂, f₃, e₂⟩
end YangMills.Construction.Tower.ResponseSaddle
end

import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsWithTheirConstantsForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory BlockAverages ColdStepAtMirrorFrames Interpolation ConvexObservables Cumulants
namespace Cumulants
open Classical in
def summedObservableCumulantBound : Prop :=
  ∀ (N N' : ℕ) (κ lam : ℝ) (M : ℕ), 0 < κ → 0 < lam → 2 ≤ M → M ≤ 9 →
    ∃ B : (ℕ → ℝ) → ℝ, (∀ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) → 0 ≤ B Cq) ∧
      ∀ (F : BlockFrame) (ι : Type) [Fintype ι] [DecidableEq ι] (y : ι → F.Cell) (ρ x : ℝ) (p : ℝ → ℝ)
        (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (Qa : Type) [Fintype Qa] (za : Qa → F.Cell)
        (P : Fin M → Qa → Prop) (O : Fin M → Qa → BondField ι → ℝ) (e : Fin M → Qa → ℝ)
        (A : Fin M → ℝ) (Cq : ℕ → ℝ) (r₀ n : ℝ) (Y₀ : F.Cell) (i₀ : Fin M),
        0 < ρ → 0 < x → IsCutoff ρ p → (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ N) →
        IsUniformlyConvexDecaying ρ (x * lam / 4) κ (fun b b' => (cellSupDist (y b) (y b') : ℝ)) Ψ K →
        (∀ (b : ι) (u : BondVector), |bondPartialDeriv Ψ b 0 u| ≤ Real.sqrt (x * lam / 4) * ‖u‖) →
        Integrable (ballDensity (cutoffFactor ρ p) Ψ) →
        (∀ q, 0 ≤ Cq q) → (∀ i, 0 ≤ A i) → (∀ i q, 0 ≤ e i q) → κ / 16 ≤ r₀ →
        (∀ i, ∃ q, P i q) → (∀ u : F.Cell, (Finset.univ.filter fun q => za q = u).card ≤ N') →
        (∀ q, P i₀ q → za q = Y₀) →
        (∀ i q, P i q → ContDiffOn ℝ 1 (O i q) {η | ∀ b, ‖η b‖ < ρ}) →
        (∀ i q, P i q → ∀ m : ℕ, 1 ≤ m →
          Integrable fun η => |O i q η| ^ m * ballDensity (cutoffFactor ρ p) Ψ η) →
        (∀ i q, P i q → HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ (A i * Real.exp (-(r₀ * e i q)))
          (fun b => (cellSupDist (y b) (za q) : ℝ)) (O i q)) →
        (∀ s : Fin M → Qa, (∀ i, P i (s i)) →
          n ≤ (cellsDiameter fun i => za (s i)) + ∑ i, e i (s i)) →
        |cumulantFromMoments (cutoffFactor ρ p) Ψ fun i η => ∑ q ∈ Finset.univ.filter (P i), O i q η| ≤
          B Cq * (∏ i, A i) * Real.exp (-(κ / 16 * n))
end Cumulants
end YangMills.Construction
end

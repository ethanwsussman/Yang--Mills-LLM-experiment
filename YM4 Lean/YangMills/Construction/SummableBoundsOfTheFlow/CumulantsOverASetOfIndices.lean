import YangMills.Construction.SummableBoundsOfTheFlow.CumulantOfOneMore
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.Interpolation
namespace YangMills.Construction.Cumulants
open Classical in
def SetIndexedCumulantBound (N N' : ℕ) (κ lam : ℝ) (B : ℕ → (ℕ → ℝ) → ℝ) : Prop :=
  ∀ (α : Type) [DecidableEq α] (S : Finset α) (a₀ : α) (F : BlockFrame) (ι : Type) [Fintype ι] [DecidableEq ι]
    (y : ι → F.Cell) (ρ x : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (Qa : Type) [Fintype Qa]
    (za : Qa → F.Cell) (P : α → Qa → Prop) (O : α → Qa → BondField ι → ℝ) (e : α → Qa → ℝ) (A : α → ℝ)
    (Cq : ℕ → ℝ) (r₀ n : ℝ) (Y₀ : F.Cell),
    a₀ ∈ S → 2 ≤ S.card → S.card ≤ 9 → 0 < ρ → 0 < x → IsCutoff ρ p →
    (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ N) →
    IsUniformlyConvexDecaying ρ (x * lam / 4) κ (fun b b' => (cellSupDist (y b) (y b') : ℝ)) Ψ K →
    (∀ (b : ι) (u : BondVector), |bondPartialDeriv Ψ b 0 u| ≤ Real.sqrt (x * lam / 4) * ‖u‖) →
    Integrable (ballDensity (cutoffFactor ρ p) Ψ) → (∀ q, 0 ≤ Cq q) → (∀ a ∈ S, 0 ≤ A a) →
    (∀ a ∈ S, ∀ q, 0 ≤ e a q) →
    κ / 16 ≤ r₀ → (∀ a ∈ S, ∃ q, P a q) → (∀ u : F.Cell, (Finset.univ.filter fun q => za q = u).card ≤ N') →
    (∀ q, P a₀ q → za q = Y₀) → (∀ a ∈ S, ∀ q, P a q → ContDiffOn ℝ 1 (O a q) {η | ∀ b, ‖η b‖ < ρ}) →
    (∀ a ∈ S, ∀ q, P a q → ∀ m : ℕ, 1 ≤ m →
      Integrable fun η => |O a q η| ^ m * ballDensity (cutoffFactor ρ p) Ψ η) →
    (∀ a ∈ S, ∀ q, P a q → HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ (A a * Real.exp (-(r₀ * e a q)))
      (fun b => (cellSupDist (y b) (za q) : ℝ)) (O a q)) →
    (∀ (s : α → Qa) (D : ℕ), (∀ a ∈ S, P a (s a)) → (∀ a ∈ S, ∀ b ∈ S, cellSupDist (za (s a)) (za (s b)) ≤ D) →
      n ≤ D + ∑ a ∈ S, e a (s a)) →
    |jointCumulant (ballExpectation (cutoffFactor ρ p) Ψ) S fun a η => ∑ q ∈ Finset.univ.filter (P a), O a q η| ≤
      B S.card Cq * (∏ a ∈ S, A a) * Real.exp (-(κ / 16 * n))
def setIndexedCumulantBoundStatement : Prop :=
  ∀ (N N' : ℕ) (κ lam : ℝ), 0 < κ → 0 < lam → ∃ B : ℕ → (ℕ → ℝ) → ℝ,
    (∀ M, 2 ≤ M → M ≤ 9 → ∀ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) → 0 ≤ B M Cq) ∧ SetIndexedCumulantBound N N' κ lam B
end YangMills.Construction.Cumulants
end

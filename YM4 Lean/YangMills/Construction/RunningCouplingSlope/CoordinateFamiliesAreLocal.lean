import YangMills.Construction.RunningCouplingSlope.CoordinatesOfATriple
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def HolomorphicFamiliesAreLocal : Prop :=
  ∀ ρ C r : ℝ, 0 < ρ → 0 ≤ C → 0 ≤ r → ∃ M θ : ℝ, 0 < M ∧ 0 < θ ∧
    ∀ {L n k : ℕ} {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq ι] (e : I → Tower.Vertex L n k k)
      (c : ι → Tower.Vertex L n k k) (F : (I → ℂ) → Matrix ι ι ℂ) (T : ℝ → ℝ → Matrix ι ι ℂ)
      (x x' : I → ℝ) (y y' : Tower.Vertex L n k k),
      IsLocallyHolomorphicFamily e c c F ρ C r →
      (∀ i, |x i| ≤ 1) → (∀ i, |x' i| ≤ 1) →
      (∀ i, e i ≠ y → x i = 0) → (∀ i, e i ≠ y' → x' i = 0) →
      (∀ᶠ w : ℝ × ℝ in 𝓝 0, T w.1 w.2 = F (complexifyCoords (w.1 • x + w.2 • x'))) →
      IsLocalAlongCellPair c T y y' M θ
end YangMills.Construction.RunningCouplingSlope
end

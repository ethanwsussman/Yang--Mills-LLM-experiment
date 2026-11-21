import YangMills.Construction.Continuum.TransportRadiusAndTheGap
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
open YangMills.Construction.Conventions YangMills.Construction.TestFunctions YangMills.Construction.TorusMetric YangMills.Construction.TorusTransport
variable (s : StandingParameters)
def periodizationRadius : ℝ := TransportData.maxRadius ⟨s, 1, le_rfl⟩
theorem periodizationRadius_eq : periodizationRadius s = s.side / 4 - 1 := rfl
variable {s}
theorem le_periodizationRadius_iff {ρ : ℝ} :
    ρ ≤ periodizationRadius s ↔ 4 * ρ + 4 ≤ s.side := by
  rw [periodizationRadius_eq]
  constructor <;> intro h <;> linarith
theorem mem_closedBallR4_zero_iff {ρ : ℝ} {x : Fin 4 → ℝ} :
    x ∈ closedBallR4 0 ρ ↔ euclidNormVec x ≤ ρ := by
  simp [closedBallR4]
theorem euclidNormVec_sub_le_of_mem_closedBallR4 {ρ : ℝ} {x y : Fin 4 → ℝ}
    (hx : x ∈ closedBallR4 0 ρ) (hy : y ∈ closedBallR4 0 ρ) :
    euclidNormVec (x - y) ≤ 2 * ρ := by
  have hn (v : Fin 4 → ℝ) :
      euclidNormVec v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 4))‖ := by
    simp [euclidNormVec, EuclideanSpace.norm_eq]
  have hx' := mem_closedBallR4_zero_iff.mp hx
  have hy' := mem_closedBallR4_zero_iff.mp hy
  rw [hn] at hx' hy' ⊢
  rw [WithLp.toLp_sub]
  linarith [norm_sub_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 4)) (WithLp.toLp 2 y)]
section Periodize
variable {𝕜 : Type*} [RCLike 𝕜]
variable (s) in
def IsPeriodizableInBall (ρ : ℝ) (f : (Fin 4 → ℝ) → 𝕜) : Prop :=
  0 < ρ ∧ ρ ≤ periodizationRadius s ∧ IsBoundedFun f ∧ tsupport f ⊆ closedBallR4 0 ρ
variable (s) in
def torusPeriodize (f : (Fin 4 → ℝ) → 𝕜) : s.Torus → 𝕜 := periodize s.side f
end Periodize
end InfiniteLattice
end YangMills.Construction
end

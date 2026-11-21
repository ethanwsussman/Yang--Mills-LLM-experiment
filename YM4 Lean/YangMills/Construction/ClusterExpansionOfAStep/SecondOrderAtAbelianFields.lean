import YangMills.Construction.ClusterExpansionOfAStep.FamiliesAtConstantCurvature
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TorusLumps
open BlockAverages TorusFields
def offsetSupNorm (u : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (u i).natAbs
def offsetTriangleDiameter (u u' : Fin 4 → ℤ) : ℕ :=
  max (max (offsetSupNorm u) (offsetSupNorm u')) (offsetSupNorm (u - u'))
def HasPolynomialGrowth (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions) : Prop :=
  ∃ (K : ℝ) (p : ℕ), ∀ c, ‖B c‖ ≤ K * (1 + (offsetSupNorm c.1 : ℝ)) ^ p
def discreteGradient (φ : (Fin 4 → ℤ) → imaginaryQuaternions) (c : (Fin 4 → ℤ) × Fin 4) :
    imaginaryQuaternions :=
  φ (c.1 + Pi.single c.2 1) - φ c.1
def SecondOrderAtAbelianFields : Prop :=
  ∀ P : StepParameters, P.Admissible → ∀ (C : ℝ) (F : LocalDensity), IsCurvatureFamily P C F →
    (∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      Filter.Tendsto (fun n : ℕ => mixedDeriv (F n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'])
        Filter.atTop (nhds (secondDerivLimit F c c' X X'))) ∧
    (∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      |secondDerivLimit F c c' X X'| ≤ ‖X‖ * ‖X'‖ * (C / P.weight (offsetTriangleDiameter c.1 c'.1))) ∧
    (∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      secondDerivLimit F c c' X X' = secondDerivLimit F c' c X' X) ∧
    (∀ B B' : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions, HasPolynomialGrowth B → HasPolynomialGrowth B' →
      Summable fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        secondDerivLimit F cc.1 cc.2 (B cc.1) (B' cc.2)) ∧
    (∀ A A' : Fin 4 → Fin 4 → imaginaryQuaternions, (∀ i j, A i j = - A j i) → (∀ i j, A' i j = - A' j i) →
      Summable fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        secondDerivLimit F cc.1 cc.2 (linearPotential A cc.1) (linearPotential A' cc.2)) ∧
    (∀ (φ : (Fin 4 → ℤ) → imaginaryQuaternions) (B' : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
      (∃ (K : ℝ) (p : ℕ), ∀ z, ‖φ z‖ ≤ K * (1 + (offsetSupNorm z : ℝ)) ^ p) → HasPolynomialGrowth B' →
      HasSum (fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        secondDerivLimit F cc.1 cc.2 (discreteGradient φ cc.1) (B' cc.2)) 0) ∧
    (∀ ω : Fin 4 → Fin 4 → ℝ, (∀ i j, ω i j = - ω j i) → ∀ ε : ℝ, 0 < ε → ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ < γ₀ → ∀ (n : ℕ) [NeZero n], 4 * Real.log (1 / γ) ^ 2 + 4 < n →
        ∀ (X : imaginaryQuaternions) (V : TorusField n) (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
          ‖X‖ = 1 → IsAbelianWithCurvature X ω γ V →
          ColdStepAtMirrorFrames.IsLinearPotential (curvatureAlong X ω) B → ∀ Y : TorusSite n,
            |centered F n Y V - γ ^ 2 / 2 *
                ∑' cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4),
                  secondDerivLimit F cc.1 cc.2 (B cc.1) (B cc.2)| ≤ ε * γ ^ 2) ∧
    ∀ (ω : Fin 4 → Fin 4 → ℝ) (l : ℕ) (X : imaginaryQuaternions), (∀ i j, ω i j = - ω j i) → 0 < l →
      (∀ i j, ∃ k : ℤ, (l : ℝ) * ω i j = k) → ‖X‖ = 1 →
      ∃ v : ℝ,
        HasSum (fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
          secondDerivLimit F cc.1 cc.2 (linearPotential (curvatureAlong X ω) cc.1)
            (linearPotential (curvatureAlong X ω) cc.2)) v ∧
        ∀ ε : ℝ, 0 < ε → ∃ n₁ : ℕ, ∀ (n : ℕ) [NeZero n], n₁ ≤ n → ∀ V : TorusField n,
          IsAbelianWithCurvature X ω (2 * Real.pi * l / (n : ℝ) ^ 2) V → ∀ Y : TorusSite n,
            |centered F n Y V - (2 * Real.pi * l / (n : ℝ) ^ 2) ^ 2 / 2 * v| ≤
              ε * (2 * Real.pi * l / (n : ℝ) ^ 2) ^ 2
end TorusLumps
end YangMills.Construction
end

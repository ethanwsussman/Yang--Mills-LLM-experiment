import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Topology
namespace YangMills.Construction.GaussianMeans
open ColdStepAtMirrorFrames
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def quadraticForm (M : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (η : BondField ι) : ℝ :=
  ∑ i, ∑ j, M i j * (η i.1 i.2 * η j.1 j.2)
def gaussianExpectation (M : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (g : BondField ι → ℝ) : ℝ :=
  (∫ η, g η * Real.exp (-(1 / 2 * quadraticForm M η))) / ∫ η, Real.exp (-(1 / 2 * quadraticForm M η))
def familyPartialDeriv (H : (Fin 2 → ℝ) → Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (l : Fin 2) :
    Matrix (ι × Fin 3) (ι × Fin 3) ℝ :=
  fun i j => fderiv ℝ (fun τ => H τ i j) 0 (Pi.single l 1)
def familyMixedDeriv (H : (Fin 2 → ℝ) → Matrix (ι × Fin 3) (ι × Fin 3) ℝ) :
    Matrix (ι × Fin 3) (ι × Fin 3) ℝ :=
  fun i j => iteratedFDeriv ℝ 2 (fun τ => H τ i j) 0 fun l => Pi.single l 1
def LogDetMixedDerivGaussian : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (c : ℝ) (H : (Fin 2 → ℝ) → Matrix (ι × Fin 3) (ι × Fin 3) ℝ),
    0 < c → (∀ i j, ContDiffAt ℝ 3 (fun τ => H τ i j) 0) → (∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), (H τ).IsSymm) →
    (∀ η : BondField ι, c * ∑ b, ‖η b‖ ^ 2 ≤ quadraticForm (H 0) η) →
    ContDiffAt ℝ 2 (fun τ => Real.log (H τ).det) 0 ∧
      -(1 / 2) * iteratedFDeriv ℝ 2 (fun τ => Real.log (H τ).det) 0 (fun l => Pi.single l 1) =
        gaussianExpectation (H 0) (fun η => -(1 / 2 * quadraticForm (familyMixedDeriv H) η) +
            1 / 2 * quadraticForm (familyPartialDeriv H 0) η *
              (1 / 2 * quadraticForm (familyPartialDeriv H 1) η)) -
          gaussianExpectation (H 0) (fun η => 1 / 2 * quadraticForm (familyPartialDeriv H 0) η) *
            gaussianExpectation (H 0) (fun η => 1 / 2 * quadraticForm (familyPartialDeriv H 1) η)
end YangMills.Construction.GaussianMeans
end

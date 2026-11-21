import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSites
import YangMills.Construction.Towers.TwoStagesOfAConstraintOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def partialGaugedAction (L m k : ℕ) : ℕ → (Edge L m k 0 → Matrices.ComplexMatrix2) → ℝ
  | 0 => plaquetteAction L m k
  | i + 1 => fun U =>
      partialGaugedAction L m k i U + axialFunction L m k i (smoothingIter L m k i U)
def partialFibreHessian (L m k i : ℕ) (𝒰 : Set (Edge L m k 0 → Matrices.ComplexMatrix2))
    (W' : Edge L m k i → Matrices.ComplexMatrix2) (U : Edge L m k 0 → Matrices.ComplexMatrix2) :
    QuadraticForm ℝ (LinearMap.ker (smoothingIterDifferential L m k i U)) :=
  fibreHessianOnKernel (smoothingIterDifferential L m k i U)
    (fibreWithin 𝒰 (smoothingIter L m k i) W') (partialGaugedAction L m k i) U
structure PartialGaugedActionAt {L m k i : ℕ} (𝒰 : Set (Edge L m k 0 → Matrices.ComplexMatrix2))
    (W' : Edge L m k i → Matrices.ComplexMatrix2) : Prop where
  isCritical : (fieldCurveData L m k 0).IsCriticalOn (fibreWithin 𝒰 (smoothingIter L m k i) W')
    (partialGaugedAction L m k i) (chosenProlongComp L m k i W')
  hessian_posDef : (partialFibreHessian L m k i 𝒰 W' (chosenProlongComp L m k i W')).PosDef
  value_eq : partialGaugedAction L m k i (chosenProlongComp L m k i W') =
    chosenEnergy L m k i W'
  gaussian_eq : constrainedGaussianOnEdgeForms
      (smoothingIterDifferential L m k i (chosenProlongComp L m k i W'))
      (partialFibreHessian L m k i 𝒰 W' (chosenProlongComp L m k i W')) =
    ∏ j : Fin i, gaussianNormaliser L m k j
      ((chosenCriticalBranch L m k).prolongIter (Nat.succ_le_of_lt j.is_lt) W')
def PartialGaugedActionsHold : Prop :=
  ∀ L m k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 1 ≤ i → i ≤ k →
    ∀ 𝒰 : Set (Edge L m k 0 → Matrices.ComplexMatrix2), IsOpenNhdOfOne 𝒰 →
      EventuallyNearIdentity (fieldSpace L m k i) fun W' => PartialGaugedActionAt 𝒰 W'
end YangMills.Construction.Tower
end

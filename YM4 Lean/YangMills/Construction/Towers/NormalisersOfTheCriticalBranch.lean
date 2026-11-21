import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.ExpansionOfAStepInTheLeftChart
import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
variable {L n k i : ℕ}
def quadraticTerm (V : Edge L n k i → Matrices.ComplexMatrix2) : EdgeFormBilinear L n k i :=
  Classical.epsilon (IsQuadraticExpansion V)
def FibreGradientRelation (L n k i : ℕ) (W : Edge L n k (i + 1) → Matrices.ComplexMatrix2) : Prop :=
  ∃ g : edgeFormSpace L n k (i + 1),
    (g : Edge L n k (i + 1) → Matrices.ComplexMatrix2) = (chosenCriticalBranch L n k).energyGradient (i + 1) W ∧
      (PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L n k i) (S' := edgePairedSpace L n k (i + 1))
          (constraintDifferential L n k i W) g).1 =
        leftGradient (fieldSpace L n k i) (fun V => (chosenGaugeFixedEnergy L n k i V : ℂ))
          (chosenProlong L n k i W)
def FibreHessianRelation (L n k i : ℕ) (W : Edge L n k (i + 1) → Matrices.ComplexMatrix2) : Prop :=
  ∀ B : LinearMap.ker (constraintDifferential L n k i W),
    fibreHessianForm L n k i W B =
      leftSecondDeriv (chosenGaugeFixedEnergy L n k i) (chosenProlong L n k i W) B.1.1 B.1.1 -
        (traceFinsumPairing (restrictToPositiveEdges ((chosenCriticalBranch L n k).energyGradient (i + 1) W))
          (quadraticTerm (chosenProlong L n k i W) B.1 B.1)).re
structure ScalingCompatible (hL : 0 < L) {j : ℕ} (hj : j ≤ k) : Prop where
  energy_eq : ∀ l ≤ j, EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j l) fun W =>
    transportTotalScalar (scaleEdge (n := n) hL hj l) (chosenEnergy L n k l) W =
      chosenEnergy L (scaledExponent n k j) j l W
  prolong_eq : ∀ l < j, EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j (l + 1)) fun W =>
    transportTotalFunValued (scaleEdge (n := n) hL hj (l + 1))
        (scaleEdge (n := n) hL hj l) (chosenProlong L n k l) W =
      chosenProlong L (scaledExponent n k j) j l W
  normaliser_eq : ∀ l < j, EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j (l + 1)) fun W =>
    transportTotalScalar (scaleEdge (n := n) hL hj (l + 1)) (gaussianNormaliser L n k l) W =
      gaussianNormaliser L (scaledExponent n k j) j l W
  logRatio_eq : ∀ l < j, EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j (l + 1)) fun W =>
    transportTotalScalar (scaleEdge (n := n) hL hj (l + 1)) (logNormaliserRatio L n k l) W =
      logNormaliserRatio L (scaledExponent n k j) j l W
structure StepNormaliserProperties (L n k i : ℕ) (hL : 0 < L) (hi : i + 1 ≤ k) : Prop where
  gradient_rel : EventuallyNearIdentity (fieldSpace L n k (i + 1)) (FibreGradientRelation L n k i)
  hessian_rel : EventuallyNearIdentity (fieldSpace L n k (i + 1)) (FibreHessianRelation L n k i)
  normaliser_pos : EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W => 0 < gaussianNormaliser L n k i W
  normaliser_analytic : ∃ 𝒰 : Set (Edge L n k (i + 1) → Matrices.ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
    IsAnalyticFieldFunction 𝒰 (gaussianNormaliser L n k i)
  logRatio_analytic : ∃ 𝒰 : Set (Edge L n k (i + 1) → Matrices.ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
    IsAnalyticFieldFunction 𝒰 (logNormaliserRatio L n k i)
  logRatio_gauge_invariant : ForGaugesNearOneOrConstant fun v W =>
    logNormaliserRatio L n k i (PeriodicLattice.gaugeTransform v W) = logNormaliserRatio L n k i W
  logRatio_symmetry_invariant : EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
    ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n, IsLevelSymmetry k (i + 1) f →
      logNormaliserRatio L n k i (pushField f W) = logNormaliserRatio L n k i W
  energy_unique : ∀ b : CriticalBranchData L n k, b.IsCritical → ∀ l ≤ k,
    EventuallyNearIdentity (fieldSpace L n k l) fun V => b.energy l V = chosenEnergy L n k l V
  prolong_unique : ∀ b : CriticalBranchData L n k, b.IsCritical → ∀ l < k,
    EventuallyNearIdentity (fieldSpace L n k (l + 1)) fun W => b.prolong l W = chosenProlong L n k l W
  scaling : ScalingCompatible (n := n) hL hi
def NormalisersHold : Prop :=
  ∀ L n k : ℕ, ∀ h : Conventions.IsAdmissibleBlockingFactor L, 0 < n → ∀ (i : ℕ) (hi : i + 1 ≤ k),
    StepNormaliserProperties L n k i (lt_of_lt_of_le (by norm_num) h.2) hi
end YangMills.Construction.Tower
end

import YangMills.Construction.ColdStepAtMirrorFrames.ComponentsOfAFieldAlongAnElement
import YangMills.Construction.SummableBoundsOfTheFlow.MixtureAtTheFlatField
import YangMills.Construction.SummableBoundsOfTheFlow.MixtureEnergyIsAnalytic
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.MixtureDerivatives
section
variable {n : ℕ}
open Classical in
def coarseSingleBond (c : TorusFields.TorusBond n) (X : BlockAverages.imaginaryQuaternions) :
    TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions :=
  fun c' => if c' = c then X else 0
variable [NeZero n] (L : ℕ) [NeZero L]
def mixedBondCoordVector : MixtureJets.MixedBond L n → BlockAverages.imaginaryQuaternions →
    (TorusFields.TorusBond (n * L) → BlockAverages.imaginaryQuaternions) ×
      (TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions)
  | Sum.inl b, X => (TwoLevelMixtures.singleBondCoord L b X, 0)
  | Sum.inr c, X => (0, coarseSingleBond c X)
end
section Forms
variable {F : BlockAverages.BlockFrame} {j : ℕ}
theorem pathSum_add_fn (B D : ColdStepAtMirrorFrames.LevelForm F j) (x : F.Site j)
    (l : List BlockAverages.PathStep) :
    ColdStepAtMirrorFrames.pathSum (fun y i => B y i + D y i) x l =
      ColdStepAtMirrorFrames.pathSum B x l + ColdStepAtMirrorFrames.pathSum D x l := by
  induction l generalizing x with
  | nil => simp [ColdStepAtMirrorFrames.pathSum]
  | cons st r ih =>
    simp only [ColdStepAtMirrorFrames.pathSum, ih]
    split_ifs <;> ring
theorem pathSum_const_mul (r : ℝ) (B : ColdStepAtMirrorFrames.LevelForm F j) (x : F.Site j)
    (l : List BlockAverages.PathStep) :
    ColdStepAtMirrorFrames.pathSum (fun y i => r * B y i) x l = r * ColdStepAtMirrorFrames.pathSum B x l := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.pathSum_const_mul <;> assumption
variable {n : ℕ} (L : ℕ)
theorem contourMean_add (W W' : TorusFields.TorusBond (n * L) → ℝ) (c : TorusFields.TorusBond n) :
    TwoLevelMixtures.contourMean L (W + W') c =
      TwoLevelMixtures.contourMean L W c + TwoLevelMixtures.contourMean L W' c := by
  simp only [TwoLevelMixtures.contourMean, ColdStepAtMirrorFrames.contourAverage, Pi.add_apply, pathSum_add_fn,
    Finset.sum_add_distrib, mul_add]
theorem contourMean_smul (r : ℝ) (W : TorusFields.TorusBond (n * L) → ℝ) (c : TorusFields.TorusBond n) :
    TwoLevelMixtures.contourMean L (r • W) c = r * TwoLevelMixtures.contourMean L W c := by
  simp only [TwoLevelMixtures.contourMean, ColdStepAtMirrorFrames.contourAverage, Pi.smul_apply, smul_eq_mul,
    pathSum_const_mul, ← Finset.mul_sum]
  ring
variable [NeZero n] (a : ℝ) (t : ℕ) (θ : ℝ) [NeZero L]
section Maxwell
variable {m : ℕ} [NeZero m] (u : ℕ) (A B C : TorusFields.TorusBond m → ℝ) (r : ℝ)
omit [NeZero L] in
theorem maxwellForm_add_left :
    WeightedResponses.maxwellForm a L u (A + B) C =
      WeightedResponses.maxwellForm a L u A C + WeightedResponses.maxwellForm a L u B C := by
  simp only [WeightedResponses.maxwellForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
omit [NeZero L] in
theorem maxwellForm_add_right :
    WeightedResponses.maxwellForm a L u A (B + C) =
      WeightedResponses.maxwellForm a L u A B + WeightedResponses.maxwellForm a L u A C := by
  simp only [WeightedResponses.maxwellForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]
omit [NeZero L] in
theorem maxwellForm_smul_left :
    WeightedResponses.maxwellForm a L u (r • A) C = r * WeightedResponses.maxwellForm a L u A C := by
  simp only [WeightedResponses.maxwellForm, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
omit [NeZero L] in
theorem maxwellForm_smul_right :
    WeightedResponses.maxwellForm a L u A (r • C) = r * WeightedResponses.maxwellForm a L u A C := by
  simp only [WeightedResponses.maxwellForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  ring
end Maxwell
section Pairing
variable (A B C : TorusFields.TorusBond (n * L) → ℝ) (r : ℝ)
omit [NeZero L] in
theorem contourPairing_add_left :
    TwoLevelMixtures.contourPairing L (A + B) C =
      TwoLevelMixtures.contourPairing L A C + TwoLevelMixtures.contourPairing L B C := by
  simp only [TwoLevelMixtures.contourPairing, contourMean_add, add_mul, Finset.sum_add_distrib]
omit [NeZero L] in
theorem contourPairing_add_right :
    TwoLevelMixtures.contourPairing L A (B + C) =
      TwoLevelMixtures.contourPairing L A B + TwoLevelMixtures.contourPairing L A C := by
  simp only [TwoLevelMixtures.contourPairing, contourMean_add, mul_add, Finset.sum_add_distrib]
omit [NeZero L] in
theorem contourPairing_smul_left :
    TwoLevelMixtures.contourPairing L (r • A) C = r * TwoLevelMixtures.contourPairing L A C := by
  simp only [TwoLevelMixtures.contourPairing, contourMean_smul, mul_assoc, ← Finset.mul_sum]
omit [NeZero L] in
theorem contourPairing_smul_right :
    TwoLevelMixtures.contourPairing L A (r • C) = r * TwoLevelMixtures.contourPairing L A C := by
  simp only [TwoLevelMixtures.contourPairing, contourMean_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring
end Pairing
def interpBilinear :
    (TorusFields.TorusBond (n * L) → ℝ) →ₗ[ℝ] (TorusFields.TorusBond (n * L) → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (TwoLevelMixtures.interpForm a L t θ)
    (fun A B C => by
      simp only [TwoLevelMixtures.interpForm, TwoLevelMixtures.interpKinetic, maxwellForm_add_left,
        contourPairing_add_left]
      ring)
    (fun r A C => by
      simp only [TwoLevelMixtures.interpForm, TwoLevelMixtures.interpKinetic, maxwellForm_smul_left,
        contourPairing_smul_left, smul_eq_mul]
      ring)
    (fun A B C => by
      simp only [TwoLevelMixtures.interpForm, TwoLevelMixtures.interpKinetic, maxwellForm_add_right,
        contourPairing_add_right]
      ring)
    (fun r A C => by
      simp only [TwoLevelMixtures.interpForm, TwoLevelMixtures.interpKinetic, maxwellForm_smul_right,
        contourPairing_smul_right, smul_eq_mul]
      ring)
theorem interpBilinear_apply (A A' : TorusFields.TorusBond (n * L) → ℝ) :
    interpBilinear L a t θ A A' = TwoLevelMixtures.interpForm a L t θ A A' := rfl
theorem sum_smul_bondIndicator {m : ℕ} [NeZero m] (A : TorusFields.TorusBond m → ℝ) :
    ∑ b, A b • MixtureJets.bondIndicator b = A := by
  classical
  funext b'
  simp [Finset.sum_apply, MixtureJets.bondIndicator]
theorem interpForm_eq_sum (A A' : TorusFields.TorusBond (n * L) → ℝ) :
    TwoLevelMixtures.interpForm a L t θ A A' =
      ∑ b, ∑ b', A b * A' b' *
        TwoLevelMixtures.interpForm a L t θ (MixtureJets.bondIndicator b) (MixtureJets.bondIndicator b') := by
  have h : interpBilinear L a t θ (∑ b, A b • MixtureJets.bondIndicator b)
      (∑ b', A' b' • MixtureJets.bondIndicator b') =
      ∑ b, ∑ b', A b * A' b' *
        interpBilinear L a t θ (MixtureJets.bondIndicator b) (MixtureJets.bondIndicator b') := by
    have e1 : interpBilinear L a t θ (∑ b, A b • MixtureJets.bondIndicator b) =
        ∑ b, A b • interpBilinear L a t θ (MixtureJets.bondIndicator b) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun b _ => map_smul _ _ _
    rw [e1, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [LinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [map_smul, smul_eq_mul]
    ring
  rwa [sum_smul_bondIndicator, sum_smul_bondIndicator] at h
end Forms
def mixtureIteratedDerivCoordStatement : Prop :=
  ∀ (a : ℝ) (L t : ℕ) (θ : ℝ) (n : ℕ) [NeZero n] [NeZero L] (k : ℕ) (c : Fin k → MixtureJets.MixedBond L n)
    (X : Fin k → BlockAverages.imaginaryQuaternions),
    AnalyticAt ℝ (TwoLevelMixtures.interpEnergyLog (n := n) a L t θ) 0 →
    MixtureJets.mixtureIteratedDeriv a L t θ c X =
      iteratedFDeriv ℝ k (TwoLevelMixtures.interpEnergyLog (n := n) a L t θ) 0
        fun l => mixedBondCoordVector L (c l) (X l)
end YangMills.Construction.MixtureDerivatives
end

import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.TreeResponseOfTheLeastCoordinates
import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace WeightedResponses
def unitGenerator : BlockAverages.imaginaryQuaternions := ⟨(⟨0, 1, 0, 0⟩ : ℍ[ℝ]), rfl⟩
section Kernels
variable (a ρA : ℝ) (L u : ℕ) {n : ℕ}
def responseKernel [NeZero L] (b : TorusFields.TorusBond (n * L)) (c : TorusFields.TorusBond n) : ℝ :=
  ColdStepAtMirrorFrames.minimizerResponse (F := TorusFields.torusFrame L u n) a ρA
    (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top c.1, c.2) unitGenerator
    (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).depth b.1) b.2
variable [NeZero n] [NeZero L]
def responseMap (A : TorusFields.TorusBond n → ℝ) : TorusFields.TorusBond (n * L) → ℝ :=
  fun b => ∑ c : TorusFields.TorusBond n, responseKernel a ρA L u b c * A c
def responseAdjoint (h : TorusFields.TorusBond (n * L) → ℝ) : TorusFields.TorusBond n → ℝ :=
  fun c => ∑ b : TorusFields.TorusBond (n * L), h b * responseKernel a ρA L u b c
end Kernels
section QuadraticForms
variable {m : ℕ}
def curl (A : TorusFields.TorusBond m → ℝ) (p : TorusFields.TorusPlaquette m) : ℝ :=
  A (p.1, p.2.1) + A (p.1 + TorusFields.unitStep m p.2.1, p.2.2) - A (p.1 + TorusFields.unitStep m p.2.2, p.2.1) - A (p.1, p.2.2)
variable [NeZero m]
open Classical in
def curlFunctional (p : TorusFields.TorusPlaquette m) : TorusFields.TorusBond m → ℝ :=
  fun c => curl (fun c' => if c' = c then 1 else 0) p
def maxwellKernel (a : ℝ) (L u : ℕ) (b b' : TorusFields.TorusBond m) : ℝ :=
  TorusFields.mixedDeriv (TorusFields.actionAtLevel a L u Finset.univ) (TorusFields.trivialField m) ![b, b']
    ![unitGenerator, unitGenerator]
def maxwellForm (a : ℝ) (L u : ℕ) (A A' : TorusFields.TorusBond m → ℝ) : ℝ :=
  ∑ b : TorusFields.TorusBond m, ∑ b' : TorusFields.TorusBond m, A b * maxwellKernel a L u b b' * A' b'
def maxwellDefect (a : ℝ) (L u : ℕ) (h : TorusFields.TorusPlaquette m → ℝ) (A : TorusFields.TorusBond m → ℝ) : ℝ :=
  2 * ∑ p ∈ TorusFields.plaquettesIn Finset.univ, h p * curl A p - maxwellForm a L u A A
end QuadraticForms
section StepHessian
variable (a ρA : ℝ) (L u n : ℕ)
open Classical in
def pairCoordinates
    (b b' : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u n)))) (s s' : ℝ) :
    (TorusFields.torusFrame L u n).Site (TorusFields.torusFrame L u n).depth → Fin 4 → BlockAverages.imaginaryQuaternions :=
  fun x i => (if (x, i) = b.1 then s else 0) • unitGenerator + (if (x, i) = b'.1 then s' else 0) • unitGenerator
def trivialHessian :
    Matrix ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u n)))
      ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u n))) ℝ :=
  fun b b' => deriv (fun s => deriv (fun s' => ColdStepAtMirrorFrames.chartedEnergy a (pairCoordinates L u n b b' s s')
    (ColdStepAtMirrorFrames.uniformField (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top)) 0) 0
open Classical in
def stepCovariance [NeZero L] [NeZero n] (h h' : TorusFields.TorusBond (n * L) → ℝ) : ℝ :=
  let l := fun b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u n))) =>
    ∑ c : TorusFields.TorusBond (n * L),
      if (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).depth c.1, c.2) = b.1
      then h c else 0
  let l' := fun b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u n))) =>
    ∑ c : TorusFields.TorusBond (n * L),
      if (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).depth c.1, c.2) = b.1
      then h' c else 0
  l ⬝ᵥ (Matrix.mulVec (trivialHessian a L u n)⁻¹ l')
end StepHessian
def adjointTransport (a ρA : ℝ) (L : ℕ) [NeZero L] (k : ℕ) :
    (d n : ℕ) → [NeZero n] → (TorusFields.TorusBond (fineSide L d n) → ℝ) → TorusFields.TorusBond n → ℝ
  | 0, _, _, h => h
  | d + 1, n, _, h => responseAdjoint a ρA L (k + d) (adjointTransport a ρA L k d (n * L) h)
def accumulatedCovariance (a ρA : ℝ) (L : ℕ) [NeZero L] (k : ℕ) :
    (d n : ℕ) → [NeZero n] → (TorusFields.TorusBond (fineSide L d n) → ℝ) →
      (TorusFields.TorusBond (fineSide L d n) → ℝ) → ℝ
  | 0, _, _, _, _ => 0
  | d + 1, n, _, h, h' => accumulatedCovariance a ρA L k d (n * L) h h' +
      stepCovariance a L (k + d) n (adjointTransport a ρA L k d (n * L) h) (adjointTransport a ρA L k d (n * L) h')
end WeightedResponses
end YangMills.Construction
end

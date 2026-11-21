import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open Classical
variable {ℓ : TorusLumps.StepParameters}
def localBoxRadius (x : ℝ) : ℝ := ⌊x ^ ((1 : ℝ) / 20)⌋₊
def logCubeScale (x : ℝ) : ℝ := ⌊Real.log x ^ 3⌋₊
structure IsLocalChainAbove (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ)
    (T : WeightedResponses.StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) (nn x₀ : ℝ) : Prop where
  floor_le : x₀ ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1
  coupling_ge : ∀ j ≤ k + 2 * WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1,
    (Tb.stepParameters y).y₁ ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β j).1
  onFamily : IsTowerAtParameters Tb y T β
    (k + 2 * WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1)
  cutoff : ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn
  measurable : T.MarksMeasurable
  side_ge : 2 ^ 10 * localBoxRadius (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 ≤ N
  one_le : 1 ≤ nn
  le_rpow : nn ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 ^ ((1 : ℝ) / 90)
def sampledCurvature (T : WeightedResponses.StageTower ℓ) (k M : ℕ) (nn x : ℝ) (N : ℕ) [NeZero N]
    (u : WeightedResponses.MarkedSample ℓ (k + M + M) N)
    (o : TorusFields.TorusSite (WeightedResponses.fineSide ℓ.side M (WeightedResponses.fineSide ℓ.side M N)))
    (p : TorusFields.TorusPlaquette (WeightedResponses.fineSide ℓ.side M (WeightedResponses.fineSide ℓ.side M N))) :
    BlockAverages.imaginaryQuaternions :=
  descendedCurvature T k M nn (logCubeScale x) (x ^ (-(1 / 4 : ℝ))) (WeightedResponses.fineSide ℓ.side M N)
    (sampleBelow ℓ (k + M) M N u) o p
def IsGaugeSmallAlong (T : WeightedResponses.StageTower ℓ) (k : ℕ) (nn ρ₀ s : ℝ) :
    (d n : ℕ) → [NeZero n] → WeightedResponses.MarkedSample ℓ (k + d) n →
      TorusFields.TorusSite (WeightedResponses.fineSide ℓ.side d n) →
      (TorusFields.TorusSite n → BlockAverages.UnitQuaternion) → Prop
  | 0, n, _, u, o, g => ∀ b : TorusFields.TorusBond n, b.1 ∈ supBall o (ballRadius ℓ.side nn ρ₀ 0) →
      ‖(LumpContours.minimalLog (gaugeTransform g (WeightedResponses.topField ℓ k n u) b) : Quaternion ℝ)‖ ≤ s
  | d + 1, n, _, u, o, g =>
    (∀ b : TorusFields.TorusBond n, b.1 ∈ supBall (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1)) →
      ‖(LumpContours.minimalLog (gaugeTransform g u.2.2.1 b) : Quaternion ℝ)‖ ≤ s) ∧
    (∀ z ∈ supBall (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1)), ∀ μ ν : Fin 4,
      TorusFields.curvature u.2.2.1 z μ ν ≤ s) ∧
    IsGaugeSmallAlong T k nn ρ₀ s d (n * ℓ.side) u.1 o
      (fun x => g (TorusLumps.parentBlock ℓ.side x) *
        blockTreeGauge ℓ (WeightedResponses.topField ℓ (k + d) (n * ℓ.side) u.1) x)
structure IsLocalKernel {n : ℕ} [NeZero n] (ρ₀ δ size : ℝ)
    (κ : TorusFields.TorusSite n → TorusFields.TorusPlaquette n → TorusFields.TorusPlaquette n → ℝ) : Prop where
  support : ∀ y p p', ρ₀ < (TorusFields.supDist p.1 y : ℝ) ∨ ρ₀ < (TorusFields.supDist p'.1 y : ℝ) → κ y p p' = 0
  decay : ∀ y p p', |κ y p p'| ≤
    size * Real.exp (-(δ * max (TorusFields.supDist p.1 y : ℝ) (TorusFields.supDist p'.1 y : ℝ)))
def IsNormalizedShareForm {n : ℕ} [NeZero n] (err : ℝ)
    (κ : TorusFields.TorusSite n → TorusFields.TorusPlaquette n → TorusFields.TorusPlaquette n → ℝ) : Prop :=
  ∀ (y : TorusFields.TorusSite n) (μ ν ρ τ : Fin 4), μ < ν → ρ < τ →
    |∑ p ∈ (TorusFields.plaquettesIn Finset.univ).filter (fun p : TorusFields.TorusPlaquette n => p.2 = (μ, ν)),
      ∑ p' ∈ (TorusFields.plaquettesIn Finset.univ).filter (fun p' : TorusFields.TorusPlaquette n => p'.2 = (ρ, τ)),
        κ y p p' -
      (if (μ, ν) = (ρ, τ) then 1 else 0)| ≤ err
end YangMills.Construction.ResponseInTheExpansion
end

import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MomentLaw
variable {N : ℕ}
def minimalOffset (o z : TorusFields.TorusSite N) : Fin 4 → ℤ := fun i => ((z - o) i).valMinAbs
def latticePath (o z : TorusFields.TorusSite N) : List (TorusFields.TorusBond N) :=
  (BlockOffsets.pathBonds 0 (BlockAverages.axisPath (minimalOffset o z) 1)).map fun b =>
    (o + TorusFields.siteOfInt b.1, b.2)
def pathSum (f : TorusFields.TorusBond N → ℝ) (l : List (TorusFields.TorusBond N)) : ℝ := (l.map f).sum
def plaquetteLogSize (B : TorusFields.TorusBond N → BlockAverages.imaginaryQuaternions) (x : TorusFields.TorusSite N)
    (μ ν : Fin 4) : ℝ :=
  ‖B (x, μ)‖ + ‖B (x + TorusFields.unitStep N μ, ν)‖ + ‖B (x + TorusFields.unitStep N ν, μ)‖ + ‖B (x, ν)‖
def axialGaugePathBoundsStatement : Prop :=
  (∀ (ℓ : TorusLumps.StepParameters) (N : ℕ) [NeZero N] (o z : TorusFields.TorusSite N),
    (∀ W : TorusFields.TorusField N,
      ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ResponseInTheExpansion.axialGaugeAt ℓ W o z) ≤
        pathSum (fun c => ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W c.1 c.2)) (latticePath o z)) ∧
    (∀ W W' : TorusFields.TorusField N,
      ‖((ResponseInTheExpansion.axialGaugeAt ℓ W o z : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
          (ResponseInTheExpansion.axialGaugeAt ℓ W' o z : BlockAverages.UnitQuaternion)‖ ≤
        pathSum (fun c => ‖((W c.1 c.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
          (W' c.1 c.2 : BlockAverages.UnitQuaternion)‖) (latticePath o z)) ∧
    (∀ c ∈ latticePath o z, TorusFields.supDist c.1 o ≤ TorusFields.supDist z o) ∧
    (latticePath o z).length ≤ 4 * TorusFields.supDist z o) ∧
  (∀ (ℓ : TorusLumps.StepParameters) (N : ℕ) [NeZero N] (o : TorusFields.TorusSite N) (W : TorusFields.TorusField N)
      (r : ℕ) (s : ℝ), 2 * r + 2 < N → 0 ≤ s →
    (∀ (y : TorusFields.TorusSite N) (μ ν : Fin 4), μ < ν → TorusFields.supDist y o ≤ r →
      TorusFields.supDist (y + TorusFields.unitStep N μ) o ≤ r →
      TorusFields.supDist (y + TorusFields.unitStep N ν) o ≤ r →
      TorusFields.supDist (y + TorusFields.unitStep N μ + TorusFields.unitStep N ν) o ≤ r →
      TorusFields.curvature W y μ ν ≤ s) →
    ∀ b : TorusFields.TorusBond N, TorusFields.supDist b.1 o ≤ r →
      TorusFields.supDist (b.1 + TorusFields.unitStep N b.2) o ≤ r →
      ColdStepAtMirrorFrames.BlockOffsets.distFromOne
        (ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ W o) W b) ≤ 3 * r * s) ∧
  (∀ (N : ℕ) [NeZero N] (W : TorusFields.TorusField N) (g : TorusFields.TorusSite N → BlockAverages.UnitQuaternion)
      (B : TorusFields.TorusBond N → BlockAverages.imaginaryQuaternions) (x : TorusFields.TorusSite N) (μ ν : Fin 4),
    W x μ = BlockAverages.expUnit (B (x, μ)) →
    W (x + TorusFields.unitStep N μ) ν = BlockAverages.expUnit (B (x + TorusFields.unitStep N μ, ν)) →
    W (x + TorusFields.unitStep N ν) μ = BlockAverages.expUnit (B (x + TorusFields.unitStep N ν, μ)) →
    W x ν = BlockAverages.expUnit (B (x, ν)) →
    plaquetteLogSize B x μ ν ≤ 1 →
    plaquetteLogSize (fun b => LumpContours.minimalLog (ResponseInTheExpansion.gaugeTransform g W b)) x μ ν ≤ 1 →
    ‖((TorusFields.holonomy W x μ ν : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 -
        ((ResponseInTheExpansion.lieFormCurl B (x, μ, ν) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤
      3 * plaquetteLogSize B x μ ν ^ 2 ∧
    ‖((ResponseInTheExpansion.lieFormCurl (fun b => LumpContours.minimalLog (ResponseInTheExpansion.gaugeTransform g W b))
          (x, μ, ν) - ResponseInTheExpansion.lieFormCurl B (x, μ, ν) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤
      2 * ColdStepAtMirrorFrames.BlockOffsets.distFromOne (g x) * TorusFields.curvature W x μ ν +
        3 * plaquetteLogSize (fun b => LumpContours.minimalLog (ResponseInTheExpansion.gaugeTransform g W b)) x μ ν ^ 2 +
        3 * plaquetteLogSize B x μ ν ^ 2) ∧
  ∀ u : BlockAverages.UnitQuaternion, ‖LumpContours.minimalLog u‖ ≤ Real.pi
end YangMills.Construction.MomentLaw
end

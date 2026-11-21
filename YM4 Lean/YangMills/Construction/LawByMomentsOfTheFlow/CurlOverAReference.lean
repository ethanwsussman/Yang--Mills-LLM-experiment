import YangMills.Construction.LawByMomentsOfTheFlow.AxialGaugeAlongPaths
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MomentLaw
variable {N : ℕ}
def weightedBondSize [NeZero N] (o : TorusFields.TorusSite N) (v : ℝ) (c : TorusFields.TorusBond N) : ℝ :=
  (1 + (TorusFields.supDist c.1 o : ℝ)) * v
def plaquetteBonds [NeZero N] (x : TorusFields.TorusSite N) (μ ν : Fin 4) : List (TorusFields.TorusBond N) :=
  [(x, μ), (x + TorusFields.unitStep N μ, ν), (x + TorusFields.unitStep N ν, μ), (x, ν)]
def plaquettePathBonds [NeZero N] (o x : TorusFields.TorusSite N) (μ ν : Fin 4) : List (TorusFields.TorusBond N) :=
  latticePath o x ++ latticePath o (x + TorusFields.unitStep N μ) ++ latticePath o (x + TorusFields.unitStep N ν) ++
    latticePath o (x + TorusFields.unitStep N μ + TorusFields.unitStep N ν) ++ plaquetteBonds x μ ν
structure IsNearReference [NeZero N] (o : TorusFields.TorusSite N) (D : ℕ) (W W₀ : TorusFields.TorusField N)
    (M F : TorusFields.TorusBond N → BlockAverages.imaginaryQuaternions) (e : TorusFields.TorusBond N → ℝ)
    (v ω κ : ℝ) : Prop where
  size_nonneg : ∀ c, 0 ≤ e c
  distFromOne_field_le : ∀ c : TorusFields.TorusBond N, TorusFields.supDist c.1 o ≤ D →
    ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W c.1 c.2) ≤ κ * (weightedBondSize o v c + ω) + e c
  distFromOne_reference_le : ∀ c : TorusFields.TorusBond N, TorusFields.supDist c.1 o ≤ D →
    ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W₀ c.1 c.2) ≤ κ * (weightedBondSize o v c + ω)
  norm_sub_reference_le : ∀ c : TorusFields.TorusBond N, TorusFields.supDist c.1 o ≤ D →
    ‖((W c.1 c.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - (W₀ c.1 c.2 : BlockAverages.UnitQuaternion)‖ ≤ e c
  log_field_le : ∀ c : TorusFields.TorusBond N, TorusFields.supDist c.1 o ≤ D →
    ‖LumpContours.minimalLog (W c.1 c.2) - M c - F c‖ ≤ κ * (weightedBondSize o v c + ω + e c) ^ 2 + ω
  log_reference_le : ∀ c : TorusFields.TorusBond N, TorusFields.supDist c.1 o ≤ D →
    ‖LumpContours.minimalLog (W₀ c.1 c.2) - M c‖ ≤ κ * (weightedBondSize o v c + ω) ^ 2 + ω
  free_le : ∀ c, ‖F c‖ ≤ e c
  curl_le : ∀ (x : TorusFields.TorusSite N) (μ ν : Fin 4), μ < ν →
    ‖ResponseInTheExpansion.lieFormCurl M (x, μ, ν)‖ ≤ v / 16
def plaquetteSum [NeZero N] (e : TorusFields.TorusBond N → ℝ) (x : TorusFields.TorusSite N) (μ ν : Fin 4) : ℝ :=
  pathSum e (plaquetteBonds x μ ν)
def curlOverReferenceStatement : Prop :=
  ∀ (P : TorusLumps.StepParameters) (N : ℕ) [NeZero N] (o : TorusFields.TorusSite N) (D : ℕ)
    (W W₀ : TorusFields.TorusField N) (M F : TorusFields.TorusBond N → BlockAverages.imaginaryQuaternions)
    (e : TorusFields.TorusBond N → ℝ) (v ω κ ε : ℝ), IsNearReference o D W W₀ M F e v ω κ → 1 ≤ κ → 0 ≤ v → 0 ≤ ω →
    0 ≤ ε → 2 * D + 2 < N →
    10 ^ 4 * κ ^ 2 * ((D : ℝ) + 3) ^ 2 * (v + ω + 100 * ((D : ℝ) + 3) * ε) ≤ 1 →
    (∀ (x : TorusFields.TorusSite N) (μ ν : Fin 4), μ < ν → TorusFields.supDist x o + 1 ≤ D →
      (∀ c ∈ plaquetteBonds x μ ν, e c ≤ ε) →
      TorusFields.curvature W x μ ν ≤ v / 2 + 2 * plaquetteSum e x μ ν + 5 * ω) ∧
    ∀ (x : TorusFields.TorusSite N) (μ ν : Fin 4), μ < ν → TorusFields.supDist x o + 3 ≤ D →
      (∀ c ∈ plaquettePathBonds o x μ ν, e c ≤ ε) →
      ‖ResponseInTheExpansion.lieFormCurl (axialCoords P W o) (x, μ, ν) - ResponseInTheExpansion.lieFormCurl M (x, μ, ν) -
          ResponseInTheExpansion.lieFormCurl F (x, μ, ν)‖ ≤
        2 * 10 ^ 5 * κ ^ 2 * (((TorusFields.supDist x o : ℝ) + 2) * (v + ω + plaquetteSum e x μ ν) +
          pathSum e (plaquettePathBonds o x μ ν)) ^ 2 + 4 * ω ∧
      ∀ c ∈ plaquetteBonds x μ ν, ‖axialCoords P W o c‖ ≤
        62 * (((TorusFields.supDist x o : ℝ) + 2) * (v + ω + plaquetteSum e x μ ν) +
          pathSum e (plaquettePathBonds o x μ ν))
end YangMills.Construction.MomentLaw
end

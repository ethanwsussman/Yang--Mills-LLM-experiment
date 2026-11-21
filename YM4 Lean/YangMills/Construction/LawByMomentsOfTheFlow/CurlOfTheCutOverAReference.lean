import YangMills.Construction.LawByMomentsOfTheFlow.CurlOverAReference
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MomentLaw
def cutoffCurlOverReferenceStatement : Prop :=
  (∀ (ℓ : TorusLumps.StepParameters) (N : ℕ) [NeZero N] (o : TorusFields.TorusSite N) (D : ℕ)
    (W W₀ : TorusFields.TorusField N) (M Nf : TorusFields.TorusBond N → BlockAverages.imaginaryQuaternions)
    (e : TorusFields.TorusBond N → ℝ) (v ω κ ε : ℝ),
    IsNearReference o D W W₀ M Nf e v ω κ → 1 ≤ κ → 0 ≤ v → v ≤ 1 → 0 ≤ ω → 0 < ε → 2 * D + 2 < N →
    10 ^ 4 * κ ^ 2 * ((D : ℝ) + 3) ^ 2 * (v + ω + 100 * ((D : ℝ) + 3) * ε) ≤ 1 → (∀ c, e c ≤ 1 / 64) →
    ∀ (x : TorusFields.TorusSite N) (μ ν : Fin 4), μ < ν → TorusFields.supDist x o + 3 ≤ D →
      ‖ResponseInTheExpansion.lieFormCurl (axialCoords ℓ W o) (x, μ, ν) - ResponseInTheExpansion.lieFormCurl M (x, μ, ν) -
          ResponseInTheExpansion.lieFormCurl Nf (x, μ, ν)‖ ≤
        2 * 10 ^ 5 * κ ^ 2 * (((TorusFields.supDist x o : ℝ) + 2) * (v + ω + plaquetteSum e x μ ν) +
          pathSum e (plaquettePathBonds o x μ ν)) ^ 2 + 4 * ω +
          20 * pathSum (fun c => (e c / ε) ^ 20) (plaquettePathBonds o x μ ν)) ∧
  (∀ (ℓ : TorusLumps.StepParameters) (N : ℕ) [NeZero N] (o : TorusFields.TorusSite N) (D m : ℕ)
    (W W₀ : TorusFields.TorusField N) (M Nf : TorusFields.TorusBond N → BlockAverages.imaginaryQuaternions)
    (e : TorusFields.TorusBond N → ℝ) (v ω κ ε : ℝ),
    IsNearReference o D W W₀ M Nf e v ω κ → 1 ≤ κ → 0 ≤ v → 0 ≤ ω → 0 < ε → 2 * D + 2 < N → 2 ≤ m →
    10 ^ 4 * κ ^ 2 * ((D : ℝ) + 3) ^ 2 * (v + ω + 100 * ((D : ℝ) + 3) * ε) ≤ 1 →
    ∀ (x : TorusFields.TorusSite N) (μ ν : Fin 4), μ < ν → TorusFields.supDist x o + 3 ≤ D →
      ‖ResponseInTheExpansion.lieFormCurl (cutoffCoords ℓ W o m) (x, μ, ν)‖ ≤
        2 * 10 ^ 5 * κ ^ 2 * (((TorusFields.supDist x o : ℝ) + 2) * (v + ω + plaquetteSum e x μ ν) +
          pathSum e (plaquettePathBonds o x μ ν)) ^ 2 + (4 * ω + v / 16) +
          124 / ((m : ℝ) - 1) * (((TorusFields.supDist x o : ℝ) + 2) * (v + ω + plaquetteSum e x μ ν) +
            pathSum e (plaquettePathBonds o x μ ν)) +
          plaquetteSum e x μ ν + 20 * pathSum (fun c => (e c / ε) ^ 20) (plaquettePathBonds o x μ ν)) ∧
  ∀ (ℓ : TorusLumps.StepParameters) (N : ℕ) [NeZero N] (o : TorusFields.TorusSite N) (D m : ℕ)
    (W W₀ : TorusFields.TorusField N) (M Nf : TorusFields.TorusBond N → BlockAverages.imaginaryQuaternions)
    (e : TorusFields.TorusBond N → ℝ) (v ω κ ε X : ℝ),
    IsNearReference o D W W₀ M Nf e v ω κ → 1 ≤ κ → 0 ≤ v → 0 ≤ ω → 0 ≤ ε → 2 * D + 2 < N →
    10 ^ 4 * κ ^ 2 * ((D : ℝ) + 3) ^ 2 * (v + ω + 100 * ((D : ℝ) + 3) * ε) ≤ 1 → 2 * m + 1 ≤ D →
    v / 2 + 8 * ε + 5 * ω ≤ X → 0 ≤ X → (∀ c : TorusFields.TorusBond N, TorusFields.supDist c.1 o ≤ 2 * m → e c < ε) →
    boxCurvature o (2 * m) W ≤ X
end YangMills.Construction.MomentLaw
end

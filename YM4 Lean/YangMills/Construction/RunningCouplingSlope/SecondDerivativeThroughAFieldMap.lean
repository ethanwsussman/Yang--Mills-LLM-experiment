import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.TorusFields
structure HasFlatTangents {n m : ℕ} (p : TorusField n → TorusField m)
    (Z : TorusBond n → imaginaryQuaternions → TorusBond m → imaginaryQuaternions) : Prop where
  map_trivial : p (trivialField n) = trivialField m
  contDiff : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (b : TorusBond m),
    ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => ((p (perturb c X σ (trivialField n)) b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) 0
  hasDerivAt_tangent : ∀ (c : TorusBond n) (X : imaginaryQuaternions) (b : TorusBond m),
    HasDerivAt (fun s : ℝ => ((p (perturb ![c] ![X] ![s] (trivialField n)) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]))
      ((Z c X b : imaginaryQuaternions) : ℍ[ℝ]) 0
def SecondDerivativePullback : Prop :=
  ∀ (m : ℕ) [NeZero m] (g : TorusField m → ℝ),
    (∀ (k : ℕ) (c : Fin k → TorusBond m) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => g (perturb c X σ (trivialField m))) 0) →
    ∃ B : (TorusBond m → imaginaryQuaternions) →L[ℝ] (TorusBond m → imaginaryQuaternions) →L[ℝ] ℝ,
      (∀ (b b' : TorusBond m) (Y Y' : imaginaryQuaternions),
        mixedDeriv g (trivialField m) ![b, b'] ![Y, Y'] = B (Pi.single b Y) (Pi.single b' Y')) ∧
      ((∀ u : UnitQuaternion, ∀ᶠ V in 𝓝 (trivialField m), g (gaugeTransform (fun _ => u) V) = g V) →
        ∀ (n : ℕ) [NeZero n] (p : TorusField n → TorusField m)
          (Z : TorusBond n → imaginaryQuaternions → TorusBond m → imaginaryQuaternions), HasFlatTangents p Z →
          ∀ (c c' : TorusBond n) (X X' : imaginaryQuaternions),
            mixedDeriv (fun V => g (p V)) (trivialField n) ![c, c'] ![X, X'] =
              ∑ b, ∑ b', B (Pi.single b (Z c X b)) (Pi.single b' (Z c' X' b')))
end YangMills.Construction.TorusFields
end

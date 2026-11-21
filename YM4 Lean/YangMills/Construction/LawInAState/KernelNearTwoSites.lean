import YangMills.Construction.LawInAState.HatsSumToTheFreeKernel
import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open TorusFields
def siteWeight {N : ℕ} (y : TorusSite N) (p : TorusPlaquette N) : ℝ := (1 + (supDist p.1 y : ℝ)) ^ 5
def maxwellKernelNearSitesStatement : Prop :=
  ∀ {N : ℕ} [NeZero N] (T : TorusPlaquette N → TorusPlaquette N → ℝ) (Ck cT n : ℝ) (R : ℕ) (o : TorusSite N),
    64 ≤ n → 64 * n ≤ N →
    (∀ p ∈ plaquettesIn (ResponseInTheExpansion.supBall o ((R : ℝ) / 8)),
      ∀ p' ∈ plaquettesIn (ResponseInTheExpansion.supBall o ((R : ℝ) / 8)),
      ∀ z : Fin 4 → ℤ, (∀ i, z i = ((p.1 - p'.1) i).valMinAbs) → z ≠ 0 →
        |T p p' - LimitForms.maxwellKernel z p.2.1 p.2.2 p'.2.1 p'.2.2| ≤
          Ck * ((1 + Real.sqrt (LimitForms.intNormSq z)) ^ 5)⁻¹ + Ck * ((R : ℝ) ^ 4)⁻¹) →
    ∀ y w : TorusSite N, (supDist y o : ℝ) ≤ (R : ℝ) / 8 - n + 2 → (supDist w o : ℝ) ≤ (R : ℝ) / 8 - n + 2 →
    (∀ i, |(minimalSiteDiff y w i : ℝ)| ≤ 13 * n) →
    n ^ 2 / 4 ≤ (ReflectionKernel.normSq fun i => (minimalSiteDiff y w i : ℝ)) →
    ∀ p p' : TorusPlaquette N, p.2.1 < p.2.2 → p'.2.1 < p'.2.2 → |T p p'| ≤ cT →
      |T p p' - ReflectionKernel.kernel (fun i => (minimalSiteDiff y w i : ℝ)) p.2.1 p.2.2 p'.2.1 p'.2.2| ≤
        (1024 * |Ck| + 192000 + (|cT| + 1) * 16 ^ 5) *
          (((n ^ 5)⁻¹ + ((R : ℝ) ^ 4)⁻¹) * (siteWeight y p * siteWeight w p'))
end YangMills.Construction.StateLaws
end

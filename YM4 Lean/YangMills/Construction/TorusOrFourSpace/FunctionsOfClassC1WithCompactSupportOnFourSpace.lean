import YangMills.Construction.TorusOrFourSpace.MultilinearFormsOnGrowingDomainsDefs
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.GrowingDomains
open Kind
def CompactlySupportedC1Bounds : Prop :=
  ∀ D : Params, IsLatticePowerScale D →
    ∀ g : Kind.euclidean.Pt D → ℝ, g ∈ c1Set D Kind.euclidean →
      IsCompactQ D Kind.euclidean (supportQ D Kind.euclidean g) →
      vecSupNormQ D Kind.euclidean (gradVec D Kind.euclidean g) < ∞ ∧
      (∀ x y : Kind.euclidean.Pt D,
        ENNReal.ofReal |g x - g y| ≤
          vecSupNormQ D Kind.euclidean (gradVec D Kind.euclidean g) *
            ENNReal.ofReal (quotDist D Kind.euclidean x y)) ∧
      IsLipschitzQ D Kind.euclidean g ∧
      ENNReal.ofReal (lipConstQ D Kind.euclidean g) ≤
        vecSupNormQ D Kind.euclidean (gradVec D Kind.euclidean g) ∧
      sharpNormQ D Kind.euclidean g ≤
        ENNReal.ofReal (40 * D.M) * GrowingDomains.cOneNorm D Kind.euclidean g
end YangMills.Construction.PeriodicSpace.GrowingDomains

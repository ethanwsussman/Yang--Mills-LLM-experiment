import YangMills.Construction.ColdChainAtEveryLevel.TermsAndVariationsOfAFramedChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
def patchQuarticGaugeStatement : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide →
    IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m →
    ∀ (z : F.Cell) (X : F.GaugeField 0) (ε : ℝ), z ∈ S → 0 ≤ ε → ε ≤ c →
      ∑ p ∈ patchPlaquettes S z, ‖(plaquetteHolonomy X p : ℍ[ℝ]) - 1‖ ^ 2 ≤ ε ^ 2 →
      ∃ Γ : F.Site 0 → UnitQuaternion,
        ∑ b ∈ patchInnerBonds S z 0, ‖(gaugeTransform Γ X b.1 b.2 : ℍ[ℝ]) - 1‖ ^ 4 ≤ (C * ε) ^ 4
end BlockAverages
end YangMills.Construction
end

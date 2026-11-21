import YangMills.Construction.ColdStepAtMirrorFrames.LocalTermsOfAMeasureForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def AdmissiblePotentialStability : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ m r μ : ℝ) (d : ι → ι → ℝ), 0 < ρ → 0 < m → 0 ≤ r →
    IsPseudoMetricOnBonds d → 2 * m ≤ μ →
    (∀ (U W : BondField ι → ℝ) (t : ℝ), IsAdmissiblePotential ρ m r d U → IsAdmissiblePotential ρ m r d W →
      0 ≤ t → t ≤ 1 → IsAdmissiblePotential ρ m r d (segmentInterpolant U W t)) ∧
    (IsAdmissiblePotential ρ m r d (halfSqNormOn μ Finset.univ)) ∧
    (∀ (Φ : BondField ι → ℝ) (S : Finset ι), IsAdmissiblePotential ρ m r d Φ →
      IsAdmissiblePotential ρ m r d (frozenPotential S μ Φ)) ∧
    (∀ (κ : Type) [Fintype κ] [DecidableEq κ] (i : κ → ι) (Φ : BondField ι → ℝ),
      Function.Injective i → IsAdmissiblePotential ρ m r d Φ →
      IsAdmissiblePotential ρ m r (fun k k' => d (i k) (i k')) (fun ξ => Φ (pushforwardField i ξ)))
end YangMills.Construction.ColdStepAtMirrorFrames
end

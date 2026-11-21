import YangMills.Construction.HoleBesideASecondHole.MeanOfAProductOfGroupVariables
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace TurnedMeans
open BlockAverages GroupMeans
def OscillationAtMost {E : Type} (I : Finset E) (f : E → UnitQuaternion) (η : ℝ) : Prop :=
  ∀ e ∈ I, ∀ e' ∈ I, ‖(f e : ℍ[ℝ]) - f e'‖ ≤ η
open Classical in
def TurnedMeanEstimate : Prop :=
  ∀ (E : Type) (I G : Finset E) (A B P Pk : E → UnitQuaternion) (η δ τ : ℝ),
    G ⊆ I → G.Nonempty → 0 ≤ η → η ≤ 1 / 8 →
    OscillationAtMost I A η → OscillationAtMost I B η → OscillationAtMost I P η →
    (∀ e ∈ I, ‖(Pk e : ℍ[ℝ]) - P e‖ ≤ η) →
    average I (fun e => ‖(Pk e : ℍ[ℝ]) - P e‖) ≤ δ →
    ((I \ G).card : ℝ) ≤ τ * I.card →
    ‖((meanDirection I A)⁻¹ : UnitQuaternion).1 *
          quatAverage G (fun e => ((A e * Pk e * (B e)⁻¹ : UnitQuaternion) : ℍ[ℝ])) *
          (meanDirection I B : UnitQuaternion).1 - quatAverage I (fun e => (P e : ℍ[ℝ]))‖ ≤
        δ + 12 * η ^ 2 + 14 * η * τ ∧
      1 - ‖quatAverage I (fun e => (P e : ℍ[ℝ]))‖ ≤ η ^ 2
end TurnedMeans
end YangMills.Construction
end

import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetTraceShift
def shiftedTrace {I I' : PeriodicData} (p : Fin 4 → ℂ) (T : JetQuad I' I) (S : JetQuad I I')
    (κ : Fin 4 → ℂ) : ℂ :=
  LinearMap.trace ℂ (I.UnitQuot → ℂ) ((T.f10 (κ - p)).comp (S.f01 κ))
open JetQuad in
def Claim : Prop :=
  ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
    ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
      ∀ (T : JetQuad I' I) (S : JetQuad I I'), IsJet δ p T → IsJet δ p S →
        Continuous (fun κ => shiftedTrace p T S (toComplexVec κ)) ∧
        Continuous (fun κ => shiftedTrace p T S (toComplexVec κ + p)) ∧
        torusAverage (fun κ => shiftedTrace p T S (toComplexVec κ + p)) =
          torusAverage fun κ => shiftedTrace p T S (toComplexVec κ)
end YangMills.Construction.PeriodicOperators.JetTraceShift
end

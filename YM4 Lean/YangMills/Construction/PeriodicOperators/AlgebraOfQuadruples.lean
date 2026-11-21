import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.QuadAlgebra
open JetQuad
def MulBilinearUnital (p : Fin 4 → ℂ) (I J K : PeriodicData) : Prop :=
  (∀ (T T' : JetQuad I J) (S : JetQuad K I),
    mul p (add T T') S = add (mul p T S) (mul p T' S)) ∧
  (∀ (T : JetQuad I J) (S S' : JetQuad K I),
    mul p T (add S S') = add (mul p T S) (mul p T S')) ∧
  (∀ (a : ℂ) (T : JetQuad I J) (S : JetQuad K I),
    mul p (smul a T) S = smul a (mul p T S)) ∧
  (∀ (a : ℂ) (T : JetQuad I J) (S : JetQuad K I),
    mul p T (smul a S) = smul a (mul p T S)) ∧
  ∀ T : JetQuad I J, mul p (one J) T = T ∧ mul p T (one I) = T
def JetNormTrace (δ : ℝ) (p : Fin 4 → ℂ) (I J : PeriodicData) : Prop :=
  (∀ T S : JetQuad I J, IsJet δ p T → IsJet δ p S →
    jetNorm δ p (add T S) ≤ jetNorm δ p T + jetNorm δ p S) ∧
  (∀ (a : ℂ) (T : JetQuad I J), IsJet δ p T →
    jetNorm δ p (smul a T) ≤ ENNReal.ofReal ‖a‖ * jetNorm δ p T) ∧
  jetNorm δ p (one I) ≤ 1 ∧
  (∀ T S : JetQuad I I, IsJet δ p T → IsJet δ p S →
    traceNumber (add T S) = traceNumber T + traceNumber S) ∧
  ∀ (a : ℂ) (T : JetQuad I I), IsJet δ p T → traceNumber (smul a T) = a * traceNumber T
def Claim : Prop :=
  (∀ (p : Fin 4 → ℂ) (I J K : PeriodicData), MulBilinearUnital p I J K) ∧
  ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
    ∀ I J : PeriodicData, IsPeriodic I → IsPeriodic J → JetNormTrace δ p I J
end YangMills.Construction.PeriodicOperators.QuadAlgebra
end

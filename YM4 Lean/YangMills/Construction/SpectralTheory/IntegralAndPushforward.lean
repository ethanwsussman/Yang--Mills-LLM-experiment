import YangMills.Construction.SpectralTheory.IntegralConstruction
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.SpectralTheory
def extendByZero {n : ℕ} (S : BorelSets n) (g : S.1 → ℂ) : (Fin n → ℝ) → ℂ :=
  Function.extend Subtype.val g 0
theorem extendByZero_apply_of_mem {n : ℕ} (S : BorelSets n) (g : S.1 → ℂ) (x : S.1) :
    extendByZero S g x = g x :=
  Subtype.val_injective.extend_apply g 0 x
theorem extendByZero_apply_of_not_mem {n : ℕ} (S : BorelSets n) (g : S.1 → ℂ) {x : Fin n → ℝ}
    (hx : x ∉ S.1) : extendByZero S g x = 0 :=
  Function.extend_apply' g (0 : (Fin n → ℝ) → ℂ) x fun ⟨y, hy⟩ => hx (hy ▸ y.2)
theorem measurable_extendByZero {n : ℕ} (S : BorelSets n) {g : S.1 → ℂ} (hg : Measurable g) :
    Measurable (extendByZero S g) :=
  (MeasurableEmbedding.subtype_coe S.2).measurable_extend hg measurable_const
namespace ProjectionMeasure
variable {n : ℕ} [NeZero n] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
def functionalCalculus (P : ProjectionMeasure n H) (g : (Fin n → ℝ) → ℂ) : UnboundedOperator H :=
  Classical.epsilon (P.IsApproximantLimitOperator g)
theorem functionalCalculus_isApproximantLimitOperator (P : ProjectionMeasure n H)
    {g : (Fin n → ℝ) → ℂ} (hex : ∃ T : UnboundedOperator H, P.IsApproximantLimitOperator g T) :
    P.IsApproximantLimitOperator g (P.functionalCalculus g) :=
  Classical.epsilon_spec hex
def functionalCalculusOn (P : ProjectionMeasure n H) (S : BorelSets n) (g : S.1 → ℂ) :
    UnboundedOperator H :=
  P.functionalCalculus (extendByZero S g)
def pushforward {m : ℕ} (P : ProjectionMeasure n H) (φ : (Fin n → ℝ) → Fin m → ℝ)
    (hφ : Measurable φ) (B : BorelSets m) : H →L[ℂ] H :=
  P ⟨φ ⁻¹' B.1, hφ B.2⟩
end ProjectionMeasure
end YangMills.Construction.SpectralTheory

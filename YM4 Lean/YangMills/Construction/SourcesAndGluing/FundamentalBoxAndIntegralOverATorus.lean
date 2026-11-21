import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.TorusMetric
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.FundamentalDomain
def fundBox (ℓ : ℝ) : Set (Fin 4 → ℝ) := Set.pi univ fun _ => Ico (-ℓ / 2) (ℓ / 2)
def openBox (ℓ : ℝ) : Set (Fin 4 → ℝ) := Set.pi univ fun _ => Ioo (-ℓ / 2) (ℓ / 2)
theorem mem_fundBox {ℓ : ℝ} {y : Fin 4 → ℝ} : y ∈ fundBox ℓ ↔ ∀ μ, y μ ∈ Ico (-ℓ / 2) (ℓ / 2) := by
  simp [fundBox, Set.mem_pi]
theorem mem_openBox {ℓ : ℝ} {y : Fin 4 → ℝ} :
    y ∈ openBox ℓ ↔ ∀ μ, y μ ∈ Ioo (-ℓ / 2) (ℓ / 2) := by
  simp [openBox, Set.mem_pi]
section Integral
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ℓ : ℝ}
def IntegrableOnFundBox (h : Torus4 ℓ → V) : Prop :=
  IntegrableOn (fun y => h (torusProj ℓ y)) (fundBox ℓ)
def torusIntegral (h : Torus4 ℓ → V) : V := ∫ y in fundBox ℓ, h (torusProj ℓ y)
end Integral
end YangMills.Construction.FundamentalDomain
end

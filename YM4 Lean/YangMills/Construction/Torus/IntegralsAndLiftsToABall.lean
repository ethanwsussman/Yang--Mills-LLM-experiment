import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace TestFunctions
open YangMills.Construction.TorusMetric
def IsLiftOfTorusPoint (ℓ : ℝ) (u : Torus4 ℓ) (v : Fin 4 → ℝ) : Prop := torusProj ℓ v = u
def IsBoundedMeasurableOnTorus {ℓ : ℝ} (F : Torus4 ℓ → ℂ) : Prop :=
  IsBoundedFun F ∧ Measurable (F ∘ torusProj ℓ)
def torusIntegralComplex (ℓ : ℝ) (F : Torus4 ℓ → ℂ) : ℂ :=
  ∫ x in Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) ℓ, F (torusProj ℓ x)
def IsSupportedInBallImage (ℓ : ℝ) (c : Fin 4 → ℝ) (σ : ℝ) (F : Torus4 ℓ → ℂ) : Prop :=
  0 < σ ∧ σ ≤ ℓ / 4 ∧ ∀ u, u ∉ torusProj ℓ '' closedBallR4 c σ → F u = 0
theorem liftToBall_apply_of_mem {ℓ σ : ℝ} {c x : Fin 4 → ℝ} (F : Torus4 ℓ → ℂ)
    (hx : x ∈ closedBallR4 c σ) : liftToBall ℓ c σ F x = F (torusProj ℓ x) :=
  Set.indicator_of_mem hx _
theorem liftToBall_apply_of_notMem {ℓ σ : ℝ} {c x : Fin 4 → ℝ} (F : Torus4 ℓ → ℂ)
    (hx : x ∉ closedBallR4 c σ) : liftToBall ℓ c σ F x = 0 :=
  Set.indicator_of_notMem hx _
end TestFunctions
end YangMills.Construction
end

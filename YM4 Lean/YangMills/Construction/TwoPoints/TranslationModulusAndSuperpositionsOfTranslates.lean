import YangMills.Construction.TwoPoints.FormsOnPairsWithDisjointSupports
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def gradOscENNReal (f : AmbientSpace → ℂ) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ (x : AmbientSpace) (x' : AmbientSpace) (_ : euclidNorm (x - x') ≤ δ),
    ENNReal.ofReal (hermitianNorm (grad f x - grad f x'))
def gradOsc (f : AmbientSpace → ℂ) (δ : ℝ) : ℝ := (gradOscENNReal f δ).toReal
def FixedScale.translationModulus (S : FixedScale) (f : AmbientSpace → ℂ) (δ : ℝ) : ℝ :=
  max (gradSup f * δ) (40 * S.scale * gradOsc f δ)
def convolve {X : Type*} [MeasureTheory.MeasureSpace X] [Sub X] (k φ : X → ℂ) (x : X) : ℂ :=
  lebesgueIntegral fun z => k z * φ (x - z)
def gridCube (δ : ℝ) (j : Fin 4 → ℤ) : Set AmbientSpace :=
  {z | ∀ μ, δ * (j μ : ℝ) ≤ z μ ∧ z μ < δ * ((j μ : ℝ) + 1)}
def gridCenter (δ : ℝ) (j : Fin 4 → ℤ) : AmbientSpace := fun μ => δ * ((j μ : ℝ) + 1 / 2)
def setIntegralOf (Q : Set AmbientSpace) (k : AmbientSpace → ℂ) : ℂ :=
  integralWrt (MeasureTheory.volume.restrict Q) k
def cubeRiemannSum (δ : ℝ) (k φ : AmbientSpace → ℂ) : AmbientSpace → ℂ :=
  ∑ᶠ j : Fin 4 → ℤ, setIntegralOf (gridCube δ j) k • translateFun (gridCenter δ j) φ
theorem existsUnique_mem_gridCube {δ : ℝ} (hδ : 0 < δ) (z : AmbientSpace) :
    ∃! j : Fin 4 → ℤ, z ∈ gridCube δ j := by
  refine ⟨fun μ => ⌊z μ / δ⌋, fun μ => ?_, fun j hj => ?_⟩
  · have h1 := Int.floor_le (z μ / δ)
    have h2 := Int.lt_floor_add_one (z μ / δ)
    rw [le_div_iff₀ hδ] at h1
    rw [div_lt_iff₀ hδ] at h2
    constructor <;> linarith
  · funext μ
    obtain ⟨a, b⟩ := hj μ
    rw [eq_comm, Int.floor_eq_iff, le_div_iff₀ hδ, div_lt_iff₀ hδ]
    constructor <;> linarith
abbrev cc1NearZero (ε : ℝ) : Submodule ℂ (AmbientSpace → ℂ) :=
  cc1In (euclidOpenBall (0 : AmbientSpace) ε)
def farShifts (ε : ℝ) : Set AmbientSpace := {z | 2 * ε ≤ euclidNorm z}
def shiftPairing (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (φ₁ φ₂ : AmbientSpace → ℂ)
    (z : AmbientSpace) : ℂ :=
  complexifyForm S φ₁ (translateFun z φ₂)
def IsMollifierSeq (j : ℕ → AmbientSpace → ℂ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    j n ∈ realValuedPart (ccInfIn (euclidOpenBall (0 : AmbientSpace) (1 / (n : ℝ)))) ∧
      (∀ x, IsRealNonneg (j n x)) ∧ lebesgueIntegral (j n) = 1
end TwoPoints
end YangMills.Construction
end

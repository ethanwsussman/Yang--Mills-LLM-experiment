import YangMills.Construction.Towers.OperatorsDependingLocallyOnAField
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.AbelianFieldDensity
open YangMills.Construction.Tower.LocalFamilies YangMills.Construction.OneLoopNotation
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
variable {J B : Type}
def IsExpDecayKernel (pos : J → InfiniteLattice.AmbientSpace) (c s : ℝ) (S : J → J → ℂ) : Prop :=
  ∀ i' i, ‖S i' i‖ ≤ s * Real.exp (-(c * TorusMetric.euclidNormVec (pos i' - pos i)))
def HasRangeLeTwo (pos : J → InfiniteLattice.AmbientSpace) (X : J → J → ℂ) : Prop :=
  ∀ i' i, ¬ TorusMetric.euclidNormVec (pos i' - pos i) ≤ 2 → X i' i = 0
def IsCubicGrowthLocalKernel (pos : J → InfiniteLattice.AmbientSpace) (A : ℝ) (X : J → J → ℂ) :
    Prop :=
  HasRangeLeTwo pos X ∧
    ∀ i' i, ‖X i' i‖ ≤ A * (1 + TorusMetric.euclidNormVec (pos i')) ^ 3
def IsCubicGrowthLocalFamily {N : Type} (pos : J → InfiniteLattice.AmbientSpace) (A : ℝ)
    (X : N → J → J → ℂ) : Prop :=
  (∀ m, HasRangeLeTwo pos (X m)) ∧
    ∀ i' i, Summable (fun m => ‖X m i' i‖) ∧
      ∑' m, ‖X m i' i‖ ≤ A * (1 + TorusMetric.euclidNormVec (pos i')) ^ 3
abbrev OriginIndex (pos : J → InfiniteLattice.AmbientSpace) : Type := {i : J // pos i = 0}
def loopTermsOne (pos : J → InfiniteLattice.AmbientSpace) (S₀ X S₁ : J → J → ℂ) :
    OriginIndex pos × J × J → ℂ :=
  fun t => S₀ t.1 t.2.1 * X t.2.1 t.2.2 * S₁ t.2.2 t.1
def loopTermsTwo (pos : J → InfiniteLattice.AmbientSpace) (S₀ X S₁ Y S₂ : J → J → ℂ) :
    OriginIndex pos × J × J × J × J → ℂ :=
  fun t => S₀ t.1 t.2.1 * X t.2.1 t.2.2.1 * S₁ t.2.2.1 t.2.2.2.1 * Y t.2.2.2.1 t.2.2.2.2 *
    S₂ t.2.2.2.2 t.1
def loopTermsThree (pos : J → InfiniteLattice.AmbientSpace) (S₀ X S₁ Y S₂ W S₃ : J → J → ℂ) :
    OriginIndex pos × J × J × J × J × J × J → ℂ :=
  fun t => S₀ t.1 t.2.1 * X t.2.1 t.2.2.1 * S₁ t.2.2.1 t.2.2.2.1 * Y t.2.2.2.1 t.2.2.2.2.1 *
    S₂ t.2.2.2.2.1 t.2.2.2.2.2.1 * W t.2.2.2.2.2.1 t.2.2.2.2.2.2 * S₃ t.2.2.2.2.2.2 t.1
def loopSumOne (pos : J → InfiniteLattice.AmbientSpace) (S₀ X S₁ : J → J → ℂ) : ℂ :=
  ∑' t, loopTermsOne pos S₀ X S₁ t
def loopSumTwo (pos : J → InfiniteLattice.AmbientSpace) (S₀ X S₁ Y S₂ : J → J → ℂ) : ℂ :=
  ∑' t, loopTermsTwo pos S₀ X S₁ Y S₂ t
def loopSumThree (pos : J → InfiniteLattice.AmbientSpace) (S₀ X S₁ Y S₂ W S₃ : J → J → ℂ) : ℂ :=
  ∑' t, loopTermsThree pos S₀ X S₁ Y S₂ W S₃ t
def entryAlong (T : (B → ℝ) → BddOp (IndexL2 J)) (ξ : B → ℝ) (i' i : J) (f : ℝ) : ℂ :=
  matrixEntry (T fun b => f * ξ b) i' i
def firstVariationKernel (T : (B → ℝ) → BddOp (IndexL2 J)) (ξ : B → ℝ) : J → J → ℂ :=
  fun i' i => deriv (entryAlong T ξ i' i) 0
def secondVariationKernel (T : (B → ℝ) → BddOp (IndexL2 J)) (ξ : B → ℝ) : J → J → ℂ :=
  fun i' i => deriv (deriv (entryAlong T ξ i' i)) 0
def taylorRemainderKernel (T : (B → ℝ) → BddOp (IndexL2 J)) (ξ : B → ℝ) (f : ℝ) :
    J → J → ℂ :=
  fun i' i => entryAlong T ξ i' i f - entryAlong T ξ i' i 0 - (f : ℂ) * firstVariationKernel T ξ i' i -
    ((1 / 2 * f ^ 2 : ℝ) : ℂ) * secondVariationKernel T ξ i' i
def shiftedResolventAlong (T : (B → ℝ) → BddOp (IndexL2 J)) (ξ : B → ℝ) (z f w : ℝ) :
    BddOp (IndexL2 J) :=
  inverseOp (addScalar (addScalar (T fun b => f * ξ b) z) w)
def resolventFirstCoeff (pos : J → InfiniteLattice.AmbientSpace)
    (T : (B → ℝ) → BddOp (IndexL2 J)) (ξ : B → ℝ) (z w : ℝ) : ℂ :=
  loopSumOne pos (matrixEntry (baseResolvent T z w)) (firstVariationKernel T ξ)
    (matrixEntry (baseResolvent T z w))
def resolventSecondCoeff (pos : J → InfiniteLattice.AmbientSpace)
    (T : (B → ℝ) → BddOp (IndexL2 J)) (ξ : B → ℝ) (z w : ℝ) : ℂ :=
  loopSumOne pos (matrixEntry (baseResolvent T z w)) (secondVariationKernel T ξ)
      (matrixEntry (baseResolvent T z w)) -
    2 * loopSumTwo pos (matrixEntry (baseResolvent T z w)) (firstVariationKernel T ξ)
      (matrixEntry (baseResolvent T z w)) (firstVariationKernel T ξ) (matrixEntry (baseResolvent T z w))
end YangMills.Construction.Tower.LocalFamilies
end

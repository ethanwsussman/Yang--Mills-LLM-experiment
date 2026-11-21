import YangMills.Construction.InfiniteLattice.ColumnOverACell
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (IsBoundedObservable IsBoundedlyLocalizedIn IsLocalizedAbove IsLocalizedBelow
  AmbientSpace timeAxis)
namespace MultipleReflections
namespace Setup.Grid
variable {D : Setup} (G : D.Grid) (k : Fin 4 → ℤ)
def StackReflectionsCompose : Prop :=
  (∀ (n n' : ℤ) (A : D.GaugeField → ℂ), IsBoundedObservable A →
    G.stackReflect k n (G.stackReflect k n' A) =
      (G.stackShift (2 * (n - n'))).actOn A) ∧
  (∀ (n i : ℤ) (A : D.GaugeField → ℂ), IsBoundedObservable A →
    G.stackReflect k n ((G.stackShift i).actOn A) =
      (G.stackShift (-i)).actOn (G.stackReflect k n A)) ∧
  (∀ (n i : ℤ) (A : D.GaugeField → ℂ), IsBoundedObservable A →
    G.stackReflect k (n + i) ((G.stackShift i).actOn A) =
      (G.stackShift i).actOn (G.stackReflect k n A)) ∧
  (∀ (n : ℤ) (A A' : D.GaugeField → ℂ), IsBoundedObservable A → IsBoundedObservable A' →
    G.stackReflect k n (A * A') = G.stackReflect k n A * G.stackReflect k n A') ∧
  ∀ (i : ℤ) (A A' : D.GaugeField → ℂ), IsBoundedObservable A → IsBoundedObservable A' →
    (G.stackShift i).actOn (A * A') =
      (G.stackShift i).actOn A * (G.stackShift i).actOn A'
def StackReflectionsCrossWalls : Prop :=
  (∀ (n : ℤ) (Z : D.GaugeField → ℂ), IsLocalizedBelow (G.wallTimeHalf k n) Z →
    IsLocalizedAbove (G.wallTimeHalf k n) (G.stackReflect k n Z)) ∧
  (∀ (n : ℤ) (Z : D.GaugeField → ℂ), IsLocalizedAbove (G.wallTimeHalf k n) Z →
    IsLocalizedBelow (G.wallTimeHalf k n) (G.stackReflect k n Z)) ∧
  ∀ (i : ℤ) (A : D.GaugeField → ℂ), IsLocalizedAbove (G.wallTimeHalf k 0) A →
    IsLocalizedAbove (G.wallTimeHalf k i) ((G.stackShift i).actOn A)
def stackSlab (i₁ i₂ : ℤ) : Set AmbientSpace :=
  {x | G.wallTime k (i₁ - 1) < x timeAxis ∧ x timeAxis < G.wallTime k i₂}
def StackCopiesMove (F : D.GaugeField → ℂ) : Prop :=
  G.stackCopy k F 1 = F ∧
  (∀ n i : ℤ, G.stackReflect k n (G.stackCopy k F i) = G.stackCopy k F (2 * n + 1 - i)) ∧
  (∀ m i : ℤ, (G.stackShift (2 * m)).actOn (G.stackCopy k F i) =
    G.stackCopy k F (i + 2 * m)) ∧
  (∀ n i₁ i₂ : ℤ, i₁ ≤ i₂ + 1 → G.stackReflect k n (G.stackProd k F i₁ i₂) =
    G.stackProd k F (2 * n + 1 - i₂) (2 * n + 1 - i₁)) ∧
  (∀ m i₁ i₂ : ℤ, i₁ ≤ i₂ + 1 → (G.stackShift (2 * m)).actOn (G.stackProd k F i₁ i₂) =
    G.stackProd k F (i₁ + 2 * m) (i₂ + 2 * m)) ∧
  ∀ i₁ i₂ : ℤ, i₁ ≤ i₂ + 1 →
    IsBoundedlyLocalizedIn (G.stackSlab k i₁ i₂) (G.stackProd k F i₁ i₂)
end Setup.Grid
def StackMovesHold : Prop :=
  ∀ (D : Setup) (G : D.Grid) (k : Fin 4 → ℤ),
    G.StackReflectionsCompose k ∧ G.StackReflectionsCrossWalls k ∧
    ∀ F ∈ G.tileAlgebra k, G.StackCopiesMove k F
end MultipleReflections
end YangMills.Construction
end

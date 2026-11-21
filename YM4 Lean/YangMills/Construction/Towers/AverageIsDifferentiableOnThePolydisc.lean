import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfigurationDefs
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
variable {L k j : ℕ}
def nearIdentityValues (F : Finset (Edge L k j)) (ρ : ℝ) : Set (F → Matrices.ComplexMatrix2) :=
  {w | w ∈ Matrices.specialUnitaryPower F ∧
    ∀ b, Matrices.ComplexMatrix2.operatorNorm (w b - 1) < ρ}
def fieldOfValuesOn (F : Finset (Edge L k j)) (w : F → Matrices.ComplexMatrix2) :
    Edge L k j → Matrices.ComplexMatrix2 :=
  open Classical in
  fun b => if h : b ∈ F then w ⟨b, h⟩ else if h' : b.opposite ∈ F then (w ⟨b.opposite, h'⟩)⁻¹ else 1
def ComplexSmoothingDifferentiableOnPolydisc : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k → ∀ ρ : ℝ,
    IsAdmissiblePolydiscRadius L ρ → ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    ∀ F : Finset (Edge L k j),
      (∀ b, b ∈ F ↔ b ∈ doubleCubeLinks L (meshAt L k j) c ∧ b.IsPositivelyOriented) →
      Matrices.EmbeddedSubmanifold.DifferentiableOnOpen (Matrices.specialUnitaryPower F)
        (nearIdentityValues F ρ)
        fun w => complexSmoothing L (fieldOfValuesOn F w) c
end YangMills.Construction.Tower.FullSpace
end

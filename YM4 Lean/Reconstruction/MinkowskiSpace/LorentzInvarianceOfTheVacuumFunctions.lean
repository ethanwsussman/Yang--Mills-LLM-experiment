import Reconstruction.MinkowskiSpace.WightmanTheoriesOfOneHermitianScalarField
import Reconstruction.MinkowskiSpace.EuclideanFieldFormsAndWhatAFormRepresents
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.VacuumLorentzInvariance
open Matrix
def complexPartialDeriv {b : ℕ} (w : (Fin b → MinkowskiSpace.ComplexVec4) → ℂ) (k : Fin b)
    (μ : Fin 4) (z : Fin b → MinkowskiSpace.ComplexVec4) : ℂ :=
  deriv (fun t : ℂ => w (Function.update z k (Function.update (z k) μ t))) (z k μ)
def lieDerivative {b : ℕ} (X : MinkowskiSpace.ComplexMat4)
    (w : (Fin b → MinkowskiSpace.ComplexVec4) → ℂ) (z : Fin b → MinkowskiSpace.ComplexVec4) : ℂ :=
  ∑ k, ∑ μ, (X *ᵥ z k) μ * complexPartialDeriv w k μ z
def Statement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (Ω : H)
    (T : ℝ → OneLoopNotation.BddOp H) (p C : ℝ),
    FieldForms.IsBoundedFieldForm P Ω T p C → FieldForms.IsEuclidean P Ω T →
    ∀ b : ℕ, 1 ≤ b →
      (∀ X ∈ MinkowskiSpace.lorentzAlgebraC,
        WightmanTheory.IsHolomorphicOnTube
            (lieDerivative X (FieldForms.vacuumExpectation P Ω T (b + 1))) ∧
          ∀ z ∈ WightmanTheory.tubeTuples b,
            lieDerivative X (FieldForms.vacuumExpectation P Ω T (b + 1)) z = 0) ∧
      (∀ (L : ℝ → MinkowskiSpace.ComplexMat4) (z : Fin b → MinkowskiSpace.ComplexVec4),
        (∀ t ∈ Set.Icc (0 : ℝ) 1, L t ∈ MinkowskiSpace.lorentzGroupC) →
        (∀ i j, ContDiffOn ℝ 1 (fun t => L t i j) (Set.Icc (0 : ℝ) 1)) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          MinkowskiSpace.mulVecTuple (L t) z ∈ WightmanTheory.tubeTuples b) →
          FieldForms.vacuumExpectation P Ω T (b + 1) (MinkowskiSpace.mulVecTuple (L 1) z) =
            FieldForms.vacuumExpectation P Ω T (b + 1) (MinkowskiSpace.mulVecTuple (L 0) z)) ∧
      (∀ L ∈ MinkowskiSpace.restrictedLorentz, ∀ z ∈ WightmanTheory.tubeTuples b,
        FieldForms.vacuumExpectation P Ω T (b + 1)
            (MinkowskiSpace.mulVecTuple (MinkowskiSpace.toComplexMatrix L) z) =
          FieldForms.vacuumExpectation P Ω T (b + 1) z)
end YangMills.Construction.VacuumLorentzInvariance
end

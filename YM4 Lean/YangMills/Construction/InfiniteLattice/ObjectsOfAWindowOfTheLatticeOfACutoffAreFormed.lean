import YangMills.Construction.InfiniteLattice.RefinedLattices
import YangMills.Construction.InfiniteLattice.WindowsKernelDensitiesLeastSideAndThresholdOfACutoff
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.CutoffLattice
def WindowObjectsWellDefined : Prop :=
  ∀ (L K : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L), 0 < K → ∀ β : ℝ, 0 < β →
    ∀ W : WindowAt L K,
      (W.faces.Finite ∧ W.faces.encard = W.faceCount ∧ W.rim.Finite) ∧
      (∀ p ∈ W.faces, ∀ b, FaceHasLink p b →
        b ∈ (W.links : Set (InfiniteLattice.Link (InfiniteLattice.refinedSpacing L K))) ∪ W.rim) ∧
      (∀ (V : W.Assignments) (U U' : FieldsAt L K),
        W.restrictRim U = W.restrictRim U' →
          W.plaquetteActionSum hL V U = W.plaquetteActionSum hL V U') ∧
      (∀ ξ : InfiniteLattice.LinkVariables W.rim, ∃ U : FieldsAt L K, W.restrictRim U = ξ) ∧
      (∀ (V : W.Assignments) (U : FieldsAt L K),
        W.localEnergy hL V (W.restrictRim U) = W.plaquetteActionSum hL V U) ∧
      (∀ ξ : InfiniteLattice.LinkVariables W.rim,
        Integrable (fun V' : W.Assignments => Real.exp (β * W.localEnergy hL V' ξ)) W.haarProd ∧
          ∫ V', Real.exp (β * W.localEnergy hL V' ξ) ∂W.haarProd ≠ 0) ∧
      (∀ (V : W.Assignments) (U : FieldsAt L K),
        W.boltzmannKernel hL β V (W.restrictRim U) =
          Real.exp (β * W.plaquetteActionSum hL V U) /
            ∫ V', Real.exp (β * W.plaquetteActionSum hL V' U) ∂W.haarProd)
end YangMills.Construction.CutoffLattice
end

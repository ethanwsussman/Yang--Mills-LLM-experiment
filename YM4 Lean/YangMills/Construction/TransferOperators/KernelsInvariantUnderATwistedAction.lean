import YangMills.Construction.TransferOperators.BondKernelAndLayerEnergy
import YangMills.Construction.TransferOperators.SquareRootOfTheBondKernel
import YangMills.Construction.TransferOperators.TwistedActionOnAPowerOfG
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TransferOperators
open SpinHarmonics
def TwistInvariantKernelsStatement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (J : Type) [Finite J],
    (∀ (V : Type) (s r : J → V) (g : V → Matrices.ComplexMatrix2.specialUnitary)
      (u v : J → Matrices.ComplexMatrix2.specialUnitary),
      linkProductKernel β (twistedConjAction s r g u) (twistedConjAction s r g v) =
          linkProductKernel β u v ∧
      sqrtLinkKernel β (twistedConjAction s r g u) (twistedConjAction s r g v) =
          sqrtLinkKernel β u v ∧
      ∀ l : J → HalfNatural,
        isotypicKernel l (twistedConjAction s r g u) (twistedConjAction s r g v) =
          isotypicKernel l u v) ∧
    (Continuous fun q : (J → Matrices.ComplexMatrix2.specialUnitary) ×
        (J → Matrices.ComplexMatrix2.specialUnitary) => linkProductKernel β q.1 q.2) ∧
    ∀ l : J → HalfNatural,
      Continuous fun q : (J → Matrices.ComplexMatrix2.specialUnitary) ×
        (J → Matrices.ComplexMatrix2.specialUnitary) => isotypicKernel l q.1 q.2
end YangMills.Construction.TransferOperators
end

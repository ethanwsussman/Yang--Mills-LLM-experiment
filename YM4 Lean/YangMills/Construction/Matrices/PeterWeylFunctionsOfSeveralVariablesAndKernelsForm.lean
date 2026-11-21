import YangMills.Construction.Matrices.PropertiesOfFunctionsOfSeveralVariablesOnTheGroup
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MeasureTheory Matrices.ComplexMatrix2 HilbertSpaceBasics SeveralVariables
def PeterWeylOrthonormalAndKernel : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (l : J → HalfNatural),
    Orthonormal ℂ (peterWeylVec : PeterWeylIndex J → HaarL2 J) ∧
    LinearIndependent ℂ (fun α : {α : PeterWeylIndex J // spins α = l} => peterWeylFn α.1) ∧
    Submodule.span ℂ (peterWeylFn '' {α : PeterWeylIndex J | spins α = l}) =
      prodCoeffSpan l ∧
    (∀ u v : J → specialUnitary, isotypicKernel l u v =
      ∑ α ∈ indicesWithSpins l, peterWeylFn α u * star (peterWeylFn α v)) ∧
    ∀ u v : J → specialUnitary,
      (isotypicKernel l u v).im = 0 ∧ isotypicKernel l u v = isotypicKernel l v u
end YangMills.Construction.SpinHarmonics
end

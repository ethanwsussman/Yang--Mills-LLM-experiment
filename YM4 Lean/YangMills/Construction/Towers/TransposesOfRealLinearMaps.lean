import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open LeftChartFields
namespace PairedFunctionSpace
variable {S S' : PairedFunctionSpace}
def PreservesRealFiniteSupport (T : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) : Prop :=
  ∀ f : S.realSubmodule, S.IsFinitelySupported f → S'.IsFinitelySupported (T f)
def HasRealDecomposition (S : PairedFunctionSpace) : Prop :=
  ∀ f : S.complexSubmodule, ∃! p : S.realSubmodule × S.realSubmodule,
    (f : S.index → Matrices.ComplexMatrix2) =
      (p.1 : S.index → Matrices.ComplexMatrix2) + Complex.I • (p.2 : S.index → Matrices.ComplexMatrix2)
def RealTransposeProperties (T : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) : Prop :=
  IsComplexification T (complexification T) ∧
  PreservesFiniteSupport (complexification T) ∧
  (∀ g : S'.realSubmodule, ∃ u : S'.complexSubmodule,
    (u : S'.index → Matrices.ComplexMatrix2) = g ∧
    (transposeMap (complexification T) u : S.index → Matrices.ComplexMatrix2) ∈ S.realSubmodule) ∧
  IsRealTransposeMap T (realTransposeMap T) ∧
  (∀ (g : S'.realSubmodule) (f : S.realSubmodule), S.IsFinitelySupported f →
    S.pair (realTransposeMap T g) f = S'.pair g (T f)) ∧
  ∀ R : S'.realSubmodule → S.realSubmodule,
    (∀ (g : S'.realSubmodule) (f : S.realSubmodule), S.IsFinitelySupported f →
      S.pair (R g) f = S'.pair g (T f)) → R = realTransposeMap T
def AdmitsRealTransposes (S S' : PairedFunctionSpace) : Prop :=
  S.HasRealDecomposition ∧
  ∀ T : S.realSubmodule →ₗ[ℝ] S'.realSubmodule, PreservesRealFiniteSupport T →
    RealTransposeProperties T
end PairedFunctionSpace
def RealTransposesExist : Prop :=
  ∀ L k : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ n : ℕ, 0 < n → ∀ c c' : FiniteCarrier L n k,
      PairedFunctionSpace.AdmitsRealTransposes (pairedFunctions c.carrier)
        (pairedFunctions c'.carrier)) ∧
    ∀ c c' : FullCarrier L k,
      PairedFunctionSpace.AdmitsRealTransposes (pairedFunctions c.carrier)
        (pairedFunctions c'.carrier)
end YangMills.Construction.Tower
end

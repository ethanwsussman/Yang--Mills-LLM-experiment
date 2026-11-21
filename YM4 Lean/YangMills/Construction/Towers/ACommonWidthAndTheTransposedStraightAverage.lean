import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import YangMills.Construction.Towers.TheJetsOfTheTwoOperatorFunctions
import YangMills.Construction.Towers.TransposesOfRealLinearMaps
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
namespace PairedFunctionSpace
def realLinearMapOfValues (S S' : PairedFunctionSpace)
    (m : (S.index → Matrices.ComplexMatrix2) → S'.index → Matrices.ComplexMatrix2) :
    S.realSubmodule →ₗ[ℝ] S'.realSubmodule :=
  Classical.epsilon fun T : S.realSubmodule →ₗ[ℝ] S'.realSubmodule =>
    ∀ f : S.realSubmodule, (T f : S'.index → Matrices.ComplexMatrix2) = m f
end PairedFunctionSpace
namespace FullSpace
open YangMills.Construction.PeriodicOperators
def jointInvertibilityWidth (L k : ℕ) (hL : 0 < L) : ℝ :=
  Classical.epsilon (IsJointInvertibilityWidth L k hL)
abbrev fineFormSpace (L k : ℕ) : PairedFunctionSpace := (edgePauliCoordinates L k 0).space
abbrev coarseFormSpace (L k : ℕ) : PairedFunctionSpace := (edgePauliCoordinates L k k).space
def crossingSmoothingComplex (L k : ℕ) :
    (fineFormSpace L k).complexSubmodule →ₗ[ℂ] (coarseFormSpace L k).complexSubmodule :=
  PairedFunctionSpace.linearOfValues (fineFormSpace L k) (coarseFormSpace L k)
    (crossingSmoothingIter L k k)
def crossingSmoothingReal (L k : ℕ) :
    (fineFormSpace L k).realSubmodule →ₗ[ℝ] (coarseFormSpace L k).realSubmodule :=
  PairedFunctionSpace.realLinearMapOfValues (fineFormSpace L k) (coarseFormSpace L k)
    (crossingSmoothingIter L k k)
def crossingSmoothingTransposeKernel (L k : ℕ) :
    (colourEdges L k 0).Carrier → (colourEdges L k k).Carrier → ℂ :=
  kernelOfMap (crossingSmoothingTranspose L k)
structure CrossingSmoothingComplexProps (L k : ℕ) : Prop where
  values : ∀ f : (fineFormSpace L k).complexSubmodule,
    (crossingSmoothingComplex L k f : (coarseFormSpace L k).index → Matrices.ComplexMatrix2) =
      crossingSmoothingIter L k k f.1
  finite_support : PairedFunctionSpace.PreservesFiniteSupport (crossingSmoothingComplex L k)
  transpose_defined : PairedFunctionSpace.IsTransposeMap (crossingSmoothingComplex L k)
    (PairedFunctionSpace.transposeMap (crossingSmoothingComplex L k))
structure TransposeKernelProps (L k : ℕ) : Prop where
  represents : Represents (crossingSmoothingTransposeKernel L k) (crossingSmoothingTranspose L k)
  periodic : IsPeriodicKernel (colourEdges L k k) (colourEdges L k 0)
    (crossingSmoothingTransposeKernel L k)
  finite_range : IsFiniteRange (colourEdges L k k) (colourEdges L k 0)
    (crossingSmoothingTransposeKernel L k)
  entire : FourierSymbolIsEntire (colourEdges L k k) (colourEdges L k 0)
    (crossingSmoothingTransposeKernel L k)
  bounded : ∀ υ : ℝ, 0 < υ → QuotHomFamilyBoundedOn (imStrip υ)
    (symbolHom (colourEdges L k k) (colourEdges L k 0) (crossingSmoothingTransposeKernel L k))
  acts_on_blochWave : ∀ (κ : Fin 4 → ℂ) (φ : (colourEdges L k k).UnitQuot → ℂ)
    (ι' : (colourEdges L k 0).Carrier),
    ApplySummableAt (crossingSmoothingTransposeKernel L k) (blochWave (colourEdges L k k) κ φ) ι' ∧
      applyKernel (crossingSmoothingTransposeKernel L k) (blochWave (colourEdges L k k) κ φ) ι' =
        blochWave (colourEdges L k 0) κ
          (applyKernel (quotSymbol (colourEdges L k k) (colourEdges L k 0)
            (crossingSmoothingTransposeKernel L k) κ) φ) ι'
structure CrossingSmoothingRealProps (L k : ℕ) : Prop where
  values : ∀ f : (fineFormSpace L k).realSubmodule,
    (crossingSmoothingReal L k f : (coarseFormSpace L k).index → Matrices.ComplexMatrix2) =
      crossingSmoothingIter L k k f.1
  finite_support : PairedFunctionSpace.PreservesRealFiniteSupport (crossingSmoothingReal L k)
  transpose_defined : PairedFunctionSpace.IsRealTransposeMap (crossingSmoothingReal L k)
    (PairedFunctionSpace.realTransposeMap (crossingSmoothingReal L k))
  transpose_values : ∀ g : (coarseFormSpace L k).realSubmodule,
    PairedFunctionSpace.transposeOfValues (fineFormSpace L k) (coarseFormSpace L k)
        (crossingSmoothingIter L k k) g.1 =
      (PairedFunctionSpace.realTransposeMap (crossingSmoothingReal L k) g :
        (fineFormSpace L k).index → Matrices.ComplexMatrix2)
def JointWidthAndTransposeTheorem : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    IsJointInvertibilityWidth L k hL (jointInvertibilityWidth L k hL) ∧
    CrossingSmoothingComplexProps L k ∧
    TransposeKernelProps L k ∧
    CrossingSmoothingRealProps L k
end FullSpace
end YangMills.Construction.Tower
end

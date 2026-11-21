import YangMills.Construction.ReflectionPositivity.ReconstructionOfAFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity
namespace ContractionFunctionals
open YangMills.Construction.SeparatedTuples YangMills.Construction.ReflectionPositivity.Reconstruction
structure IsAdmissible (σ : TupleFunctional) : Prop where
  contraction : ∃ D₀ : Set ℝ, ContractionHypotheses σ D₀
  permInvariant : σ.IsPermInvariant
  timeReflect_invariant : σ.IsInvariant TimeAxis.timeReflection
end ContractionFunctionals
end ReflectionPositivity
end YangMills.Construction

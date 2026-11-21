import YangMills.Construction.Towers.TheFieldsAndTheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.KernelAtZeroSources
def TransposeExists (S S' : Tower.PairedFunctionSpace)
    (φ : (S.index → Matrices.ComplexMatrix2) → S'.index → Matrices.ComplexMatrix2) : Prop :=
  (∀ f : S.complexSubmodule,
      (Tower.PairedFunctionSpace.linearOfValues S S' φ f : S'.index → Matrices.ComplexMatrix2) =
        φ f) ∧
    Tower.PairedFunctionSpace.PreservesFiniteSupport
      (Tower.PairedFunctionSpace.linearOfValues S S' φ) ∧
    Tower.PairedFunctionSpace.IsTransposeMap (Tower.PairedFunctionSpace.linearOfValues S S' φ)
      (Tower.PairedFunctionSpace.transposeMap (Tower.PairedFunctionSpace.linearOfValues S S' φ))
def PairingFinite {ι : Type} (f f' : ι → Matrices.ComplexMatrix2) : Prop :=
  (Function.support fun i => Matrices.ComplexMatrix2.halfTrace (f i * f' i)).Finite
def HoldsAt (L k : ℕ) (U : Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) : Prop :=
  TransposeExists (Tower.pairedFunctions (Tower.FullSpace.Vertex L k 0))
      (Tower.FullSpace.edgePairedSpace (Tower.meshAt L k 0))
      (Tower.FullSpace.covDiff U) ∧
    TransposeExists (Tower.pairedFunctions (Tower.FullSpace.Vertex L k 0))
      (Tower.pairedFunctions (Tower.FullSpace.Vertex L k k))
      (Tower.FullSpace.iterAdjointCubeAverage L k U k) ∧
    (∀ A ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0),
      Tower.FullSpace.gaugeFixingTerm L k U A ∈
        (Tower.pairedFunctions (Tower.FullSpace.Vertex L k 0)).complexSubmodule) ∧
    (∀ A ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0),
      ∀ A' ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0),
      Tower.HasFiniteSupp (Tower.FullSpace.restrictToPositiveEdges A) →
        Tower.HasFiniteSupp (Tower.FullSpace.restrictToPositiveEdges A') →
          PairingFinite (Tower.FullSpace.gaugeFixingTerm L k U A)
            (Tower.FullSpace.gaugeFixingTerm L k U A')) ∧
    PeriodicOperators.IsSymmKernel (fun _ => 1) (Tower.FullSpace.backgroundKernel L k U) ∧
    Tower.FullSpace.IsHessianKernel U 0 0 (Tower.FullSpace.backgroundKernel L k U) ∧
    (∀ X, Tower.FullSpace.IsHessianKernel U 0 0 X → X = Tower.FullSpace.backgroundKernel L k U) ∧
    ∀ ζ : Tower.FullSpace.FullField L k,
      (ζ.2.1 : Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) = 0 →
      (ζ.2.2 : Tower.FullSpace.Edge L k k → Matrices.ComplexMatrix2) = 0 →
      ζ.gaugeField = U →
        Tower.FullSpace.hessianKernel ζ.gaugeField ζ.2.1 ζ.2.2 =
          Tower.FullSpace.backgroundKernel L k U
def ZeroSourceKernel : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ U ∈ Tower.FullSpace.smallIterateFields L k, HoldsAt L k U
end YangMills.Construction.Tower.FullSpace.KernelAtZeroSources
end

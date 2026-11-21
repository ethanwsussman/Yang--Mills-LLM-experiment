import YangMills.Construction.LimitTheorem.AssertionsAtGivenConstants
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.LimitTheorem.DecompositionTransfer
open SeparatedTuples ReflectionPositivity.TupleForm
open HilbertSpaceBasics (IsPosSemidef)
open ReflectionPositivity.Reconstruction (posClass)
open ReflectionPositivity.PairMeasureOperators (groundStateProjection)
open InfiniteLattice (AmbientSpace)
structure HasDecompositionConditions (σ : TupleFunctional) (B : DecompositionData) : Prop where
  isCanonical : B.IsCanonical σ
  isomorphic_of_canonical : ∀ A : DecompositionData, A.IsCanonical σ → A.Isomorphic B
  groundStates : GroundStatesAsL2 σ B
  permutes : ∀ r : AmbientSpace → AmbientSpace, IsEuclidIsometry r → σ.IsInvariant r →
    PermutesComponents B r
def UniqueComponentMap (A B : DecompositionData) : Prop :=
  (∃ e : A.space ≃ₜ B.space, A.law.map e = B.law ∧
    (∀ ξ, B.comp (e ξ) = A.comp ξ) ∧
    ∀ f : A.space → B.space, (∀ ξ, B.comp (f ξ) = A.comp ξ) → f = e) ∧
  Set.range A.comp = Set.range B.comp
def GroundStateDescription (σ : TupleFunctional) (A : DecompositionData) : Prop :=
  GroundStatesAsL2 σ A ∧
  ∀ hpos : IsPosSemidef (reflectionForm σ),
    (∀ F F' : PositiveSpan,
      ⟪groundStateProjection σ hpos (posClass σ hpos F),
        groundStateProjection σ hpos (posClass σ hpos F')⟫_ℂ =
      ∫ ξ, (starRingEnd ℂ) ((A.comp ξ).spanExtension F.1) *
        (A.comp ξ).spanExtension F'.1 ∂A.law) ∧
    ENat.card A.space = Cardinal.toENat (Module.rank ℂ (Lp ℂ 2 A.law)) ∧
    Module.rank ℂ (Lp ℂ 2 A.law) = Module.rank ℂ (hamiltonianKernel σ hpos)
def TransferStatement : Prop :=
  ∀ (σ : TupleFunctional) (B A : DecompositionData), HasDecompositionConditions σ B →
    A.IsCanonical σ →
    UniqueComponentMap A B ∧ GroundStateDescription σ A ∧
      (∀ r : AmbientSpace → AmbientSpace, IsEuclidIsometry r → σ.IsInvariant r →
        PermutesComponents A r) ∧
      TransportedCanonical σ A
end YangMills.Construction.LimitTheorem.DecompositionTransfer
end

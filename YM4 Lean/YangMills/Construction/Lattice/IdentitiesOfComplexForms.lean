import YangMills.Construction.Lattice.AveragingOnPart
import YangMills.Construction.Lattice.CurrentOnPart
import YangMills.Construction.Lattice.HessianOfTheActionOfARegion
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ComplexTransport
variable {L m : ℕ} {j : ℤ}
def gaugeFieldOfPositiveValues (ℬ : Set (Bond L m j))
    (v : PositiveBondOf ℬ → Matrices.ComplexMatrix2) :
    Bond L m j → Matrices.ComplexMatrix2 :=
  open Classical in
  fun b => if h : b ∈ ℬ ∧ b.IsPositivelyOriented then v ⟨b, h⟩
    else if h' : b.opposite ∈ ℬ ∧ b.opposite.IsPositivelyOriented then (v ⟨b.opposite, h'⟩)⁻¹
    else 1
def bondFormOfPositiveValues (ℬ : Set (Bond L m j))
    (a : PositiveBondOf ℬ → Matrices.ComplexMatrix2) : Bond L m j → Matrices.ComplexMatrix2 :=
  open Classical in
  fun b => if h : b ∈ ℬ ∧ b.IsPositivelyOriented then a ⟨b, h⟩
    else if h' : b.opposite ∈ ℬ ∧ b.opposite.IsPositivelyOriented then -a ⟨b.opposite, h'⟩
    else 0
def gaugeFieldOfPoint (ℬ : Set (Bond L m j)) {κ : Type}
    (p : PositiveBondOf ℬ ⊕ κ → Matrices.ComplexMatrix2) :
    Bond L m j → Matrices.ComplexMatrix2 :=
  gaugeFieldOfPositiveValues ℬ fun b => p (.inl b)
def algebraPartOfPoint {ι κ : Type} (p : ι ⊕ κ → Matrices.ComplexMatrix2) :
    κ → Matrices.ComplexMatrix2 := fun k => p (.inr k)
def firstAlgebraPart {ι κ κ' : Type} (p : ι ⊕ (κ ⊕ κ') → Matrices.ComplexMatrix2) :
    κ → Matrices.ComplexMatrix2 :=
  fun k => p (.inr (.inl k))
def secondAlgebraPart {ι κ κ' : Type} (p : ι ⊕ (κ ⊕ κ') → Matrices.ComplexMatrix2) :
    κ' → Matrices.ComplexMatrix2 :=
  fun k => p (.inr (.inr k))
def BothHolomorphicToUnimodular {ι κ : Type} (W : Set (ι ⊕ κ → Matrices.ComplexMatrix2))
    (f g : (ι ⊕ κ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) : Prop :=
  ∃ (_ : Fintype ι) (_ : Fintype κ),
    ∀ b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      Matrices.GroupLieProduct.IsHolomorphicToUnimodular b W f ∧
        Matrices.GroupLieProduct.IsHolomorphicToUnimodular b W g
def BothHolomorphicToTraceless {ι κ : Type} (W : Set (ι ⊕ κ → Matrices.ComplexMatrix2))
    (f g : (ι ⊕ κ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) : Prop :=
  ∃ (_ : Fintype ι) (_ : Fintype κ),
    ∀ b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      Matrices.GroupLieProduct.IsHolomorphicToTraceless b W f ∧
        Matrices.GroupLieProduct.IsHolomorphicToTraceless b W g
def BothHolomorphicScalar {ι κ : Type} (W : Set (ι ⊕ κ → Matrices.ComplexMatrix2))
    (f g : (ι ⊕ κ → Matrices.ComplexMatrix2) → ℂ) : Prop :=
  ∃ (_ : Fintype ι) (_ : Fintype κ),
    ∀ b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      Matrices.GroupLieProduct.IsHolomorphicToCoords b (Equiv.funUnique (Fin 1) ℂ).symm W f ∧
        Matrices.GroupLieProduct.IsHolomorphicToCoords b (Equiv.funUnique (Fin 1) ℂ).symm W g
def IsHolomorphicAtZero {α τ : Type}
    (f : (α → Matrices.ComplexMatrix2) → τ → Matrices.ComplexMatrix2) : Prop :=
  ∃ (_ : Fintype α) (_ : Fintype τ) (N : Set (α → Matrices.ComplexMatrix2)), 0 ∈ N ∧
    ∀ (b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
      (ν : τ ≃ Fin (Fintype.card τ)),
      Matrices.GroupLieProduct.IsHolomorphicOnTraceless b
        (Matrices.GroupLieProduct.matrixPiEquiv ν) N f
def IsComplexBondFormSupportedOn (ℬ : Set (Bond L m j))
    (A : Bond L m j → Matrices.ComplexMatrix2) : Prop :=
  IsBondForm complexLieAlgebra A ∧ ℬ.indicator A = A
structure ComplexTransportIdentities (σ : FourTorus L m ≃ FourTorus L m)
    (ℬ : Set (Bond L m j)) : Prop where
  exp_transport : ∀ V₀, IsGaugeField complexGaugeGroup ℬ V₀ →
    ∀ A, IsComplexBondFormSupportedOn ℬ A →
    ∀ b ∈ ℬ, transportGaugeField σ (expTwist A V₀) (bondImage σ b) =
      expTwist (twistedTransportForm σ V₀ A) (transportGaugeField σ V₀) (bondImage σ b)
  exp_transport_holomorphic : ∀ b ∈ ℬ,
    BothHolomorphicToUnimodular (Matrices.GroupLieProduct (PositiveBondOf ℬ) (PositiveBondOf ℬ))
      (fun p => transportGaugeField σ
        (expTwist (bondFormOfPositiveValues ℬ (algebraPartOfPoint p)) (gaugeFieldOfPoint ℬ p))
        (bondImage σ b))
      (fun p => expTwist (twistedTransportForm σ (gaugeFieldOfPoint ℬ p)
          (bondFormOfPositiveValues ℬ (algebraPartOfPoint p)))
        (transportGaugeField σ (gaugeFieldOfPoint ℬ p)) (bondImage σ b))
  inner_transport : ∀ ξ : ℝ, 0 < ξ → ∀ V₀, IsGaugeField complexGaugeGroup ℬ V₀ →
    ∀ A, IsComplexBondFormSupportedOn ℬ A → ∀ B, IsComplexBondFormSupportedOn ℬ B →
      bondFormInner ξ (twistedTransportForm σ V₀ A) (twistedTransportForm σ V₀ B) =
        bondFormInner ξ A B
  inner_transport_holomorphic : ∀ ξ : ℝ, 0 < ξ →
    BothHolomorphicScalar
      (Matrices.GroupLieProduct (PositiveBondOf ℬ) (PositiveBondOf ℬ ⊕ PositiveBondOf ℬ))
      (fun p => bondFormInner ξ
        (twistedTransportForm σ (gaugeFieldOfPoint ℬ p)
          (bondFormOfPositiveValues ℬ (firstAlgebraPart p)))
        (twistedTransportForm σ (gaugeFieldOfPoint ℬ p)
          (bondFormOfPositiveValues ℬ (secondAlgebraPart p))))
      (fun p => bondFormInner ξ (bondFormOfPositiveValues ℬ (firstAlgebraPart p))
        (bondFormOfPositiveValues ℬ (secondAlgebraPart p)))
  current_transport : ∀ ξ : ℝ, 0 < ξ → ∀ V₀, IsGaugeField complexGaugeGroup ℬ V₀ →
    ∀ b, (∀ q ∈ plaquettesThrough b, q.BondsWithin ℬ) →
      yangMillsCurrent ξ (transportGaugeField σ (extendByOne ℬ V₀)) (bondImage σ b) =
        twistedTransportForm σ V₀ (yangMillsCurrent ξ (extendByOne ℬ V₀)) (bondImage σ b)
  current_transport_holomorphic : ∀ ξ : ℝ, 0 < ξ →
    ∀ b, (∀ q ∈ plaquettesThrough b, q.BondsWithin ℬ) →
    BothHolomorphicToTraceless (Matrices.GroupLieProduct (PositiveBondOf ℬ) Empty)
      (fun p => yangMillsCurrent ξ (transportGaugeField σ (gaugeFieldOfPoint ℬ p))
        (bondImage σ b))
      (fun p => twistedTransportForm σ (gaugeFieldOfPoint ℬ p)
        (yangMillsCurrent ξ (gaugeFieldOfPoint ℬ p)) (bondImage σ b))
structure RegionHessianTransport (σ : FourTorus L m ≃ FourTorus L m) {K : ℕ} (k : ℕ)
    (Ω₀ : Set (FourTorus L m)) (ℬ : Set (BondAtLevel L m K 0)) : Prop where
  hessian_eq : ∀ U, IsGaugeField complexGaugeGroup ℬ U →
    ∀ A₁, IsComplexBondFormSupportedOn ℬ A₁ →
    ∀ A₂, IsComplexBondFormSupportedOn ℬ A₂ →
      regionEnergyHessian k (σ '' Ω₀) (transportGaugeField σ U)
          (twistedTransportForm σ U A₁) (twistedTransportForm σ U A₂) =
        regionEnergyHessian k Ω₀ U A₁ A₂
  holomorphic : BothHolomorphicScalar
    (Matrices.GroupLieProduct (PositiveBondOf ℬ) (PositiveBondOf ℬ ⊕ PositiveBondOf ℬ))
    (fun p => regionEnergyHessian k (σ '' Ω₀) (transportGaugeField σ (gaugeFieldOfPoint ℬ p))
      (twistedTransportForm σ (gaugeFieldOfPoint ℬ p)
        (bondFormOfPositiveValues ℬ (firstAlgebraPart p)))
      (twistedTransportForm σ (gaugeFieldOfPoint ℬ p)
        (bondFormOfPositiveValues ℬ (secondAlgebraPart p))))
    (fun p => regionEnergyHessian k Ω₀ (gaugeFieldOfPoint ℬ p)
      (bondFormOfPositiveValues ℬ (firstAlgebraPart p))
      (bondFormOfPositiveValues ℬ (secondAlgebraPart p)))
end YangMills.Construction.PeriodicLattice.ComplexTransport
end

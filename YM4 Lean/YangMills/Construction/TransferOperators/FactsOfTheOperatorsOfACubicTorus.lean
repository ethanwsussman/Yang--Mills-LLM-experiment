import YangMills.Construction.Matrices.HilbertSchmidtOperatorsTraceClassAndTraceOnG
import YangMills.Construction.TransferOperators.TransferOperatorOfACubicTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.TransferOperators
def IsUnitaryOp {J : Type} [Countable J]
    (T : HaarL2 J →L[ℂ] HaarL2 J) : Prop :=
  Function.Bijective T ∧ ∀ f h : HaarL2 J, inner ℂ (T f) (T h) = inner ℂ f h
namespace CubicPeriodSublattice
variable (Γ : CubicPeriodSublattice) (μ : Fin 4)
def invariantSubspace : Set (Γ.SliceL2 μ) :=
  {f | ∀ g : Γ.VertexOrbits μ → specialUnitary, Γ.gaugeRep g f = f}
variable {μ} in
def IsInvariantKernel
    (K : (Γ.LinkOrbits μ → specialUnitary) × (Γ.LinkOrbits μ → specialUnitary) → ℂ) : Prop :=
  ∀ (g : Γ.VertexOrbits μ → specialUnitary) (U U' : Γ.LinkOrbits μ → specialUnitary),
    K (Γ.orbitGaugeAct g U, Γ.orbitGaugeAct g U') = K (U, U')
structure GaugeRepProperties : Prop where
  rep_formula : ∀ g : Γ.VertexOrbits μ → specialUnitary,
    Γ.IsGaugeRep g (Γ.gaugeRep g)
  rep_unitary : ∀ g : Γ.VertexOrbits μ → specialUnitary, IsUnitaryOp (Γ.gaugeRep g)
  rep_mul : ∀ g g' : Γ.VertexOrbits μ → specialUnitary,
    Γ.gaugeRep g * Γ.gaugeRep g' = Γ.gaugeRep (g * g')
  proj_formula : Γ.IsGaugeProjection (Γ.gaugeProjection μ)
  proj_integrable : ∀ h f : Γ.SliceL2 μ,
    Integrable (fun g : Γ.VertexOrbits μ → specialUnitary => inner ℂ h (Γ.gaugeRep g f))
      (haarPi (Γ.VertexOrbits μ))
  proj_inner : ∀ h f : Γ.SliceL2 μ,
    inner ℂ h (Γ.gaugeProjection μ f) =
      ∫ g : Γ.VertexOrbits μ → specialUnitary, inner ℂ h (Γ.gaugeRep g f)
        ∂haarPi (Γ.VertexOrbits μ)
  proj_symm : IsSymmetricOp (Γ.gaugeProjection μ)
  proj_idempotent : Γ.gaugeProjection μ * Γ.gaugeProjection μ = Γ.gaugeProjection μ
  proj_range : Set.range (Γ.gaugeProjection μ) = Γ.invariantSubspace μ
  commute_proj : ∀ T : Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ, IsSymmetricOp T →
    (∀ g : Γ.VertexOrbits μ → specialUnitary,
      T * Γ.gaugeRep g = Γ.gaugeRep g * T) →
    T * Γ.gaugeProjection μ = Γ.gaugeProjection μ * T
  kernelOp_commute : ∀ K : (Γ.LinkOrbits μ → specialUnitary) × (Γ.LinkOrbits μ → specialUnitary) → ℂ,
    Continuous K → Γ.IsInvariantKernel K → ∀ g : Γ.VertexOrbits μ → specialUnitary,
      Schatten.kernelOp (haarPi (Γ.LinkOrbits μ)) K * Γ.gaugeRep g =
        Γ.gaugeRep g * Schatten.kernelOp (haarPi (Γ.LinkOrbits μ)) K
structure BoltzmannProperties (β : ℝ) : Prop where
  formula : Γ.IsBoltzmannMultiplier β (Γ.boltzmannMultiplier μ β)
  nonneg : IsPositiveOp (Γ.boltzmannMultiplier μ β)
  le_one : OpLE (Γ.boltzmannMultiplier μ β) 1
  commute : ∀ g : Γ.VertexOrbits μ → specialUnitary,
    Γ.boltzmannMultiplier μ β * Γ.gaugeRep g = Γ.gaugeRep g * Γ.boltzmannMultiplier μ β
structure LinkOperatorProperties (β : ℝ) : Prop where
  link_traceClass : IsTraceClassPW (linkProductOperator β (Γ.LinkOrbits μ))
  sqrt_hilbertSchmidt : IsHilbertSchmidtPW (sqrtLinkOperator β (Γ.LinkOrbits μ))
  link_symm : IsSymmetricOp (linkProductOperator β (Γ.LinkOrbits μ))
  sqrt_symm : IsSymmetricOp (sqrtLinkOperator β (Γ.LinkOrbits μ))
  link_nonneg : IsPositiveOp (linkProductOperator β (Γ.LinkOrbits μ))
  sqrt_nonneg : IsPositiveOp (sqrtLinkOperator β (Γ.LinkOrbits μ))
  link_real : IsRealPreserving (linkProductOperator β (Γ.LinkOrbits μ))
  sqrt_real : IsRealPreserving (sqrtLinkOperator β (Γ.LinkOrbits μ))
  link_continuous : Continuous fun p : (Γ.LinkOrbits μ → specialUnitary) ×
    (Γ.LinkOrbits μ → specialUnitary) => linkProductKernel β p.1 p.2
  sqrt_continuous : Continuous fun p : (Γ.LinkOrbits μ → specialUnitary) ×
    (Γ.LinkOrbits μ → specialUnitary) => sqrtLinkKernel β p.1 p.2
  link_commute : ∀ g : Γ.VertexOrbits μ → specialUnitary,
    linkProductOperator β (Γ.LinkOrbits μ) * Γ.gaugeRep g =
      Γ.gaugeRep g * linkProductOperator β (Γ.LinkOrbits μ)
  sqrt_commute : ∀ g : Γ.VertexOrbits μ → specialUnitary,
    sqrtLinkOperator β (Γ.LinkOrbits μ) * Γ.gaugeRep g =
      Γ.gaugeRep g * sqrtLinkOperator β (Γ.LinkOrbits μ)
  isotypic_commute : ∀ (l : Γ.LinkOrbits μ → HalfNatural) (g : Γ.VertexOrbits μ → specialUnitary),
    isotypicProj l * Γ.gaugeRep g = Γ.gaugeRep g * isotypicProj l
structure TransferProperties (β : ℝ) : Prop where
  sqrt_commute_proj : sqrtLinkOperator β (Γ.LinkOrbits μ) * Γ.gaugeProjection μ =
    Γ.gaugeProjection μ * sqrtLinkOperator β (Γ.LinkOrbits μ)
  half_symm : IsSymmetricOp (Γ.halfTransfer μ β)
  half_hilbertSchmidt : IsHilbertSchmidtPW (Γ.halfTransfer μ β)
  transfer_eq_sandwich : Γ.transfer μ β =
    Γ.gaugeProjection μ * sqrtLinkOperator β (Γ.LinkOrbits μ) * Γ.boltzmannMultiplier μ β *
      sqrtLinkOperator β (Γ.LinkOrbits μ) * Γ.gaugeProjection μ
  transfer_eq_factor : Γ.transfer μ β =
    sqrtLinkOperator β (Γ.LinkOrbits μ) * Γ.gaugeProjection μ * Γ.boltzmannMultiplier μ β *
      sqrtLinkOperator β (Γ.LinkOrbits μ)
  transfer_nonneg : IsPositiveOp (Γ.transfer μ β)
  transfer_symm : IsSymmetricOp (Γ.transfer μ β)
  transfer_traceClass : IsTraceClassPW (Γ.transfer μ β)
  entry_le : ∀ a a' : PeterWeylIndex (Γ.LinkOrbits μ),
    ‖peterWeylEntry (Γ.transfer μ β) a a'‖ ≤
      sqrtPeterWeylCoeff β a * sqrtPeterWeylCoeff β a'
  entry_summable : Summable fun p : PeterWeylIndex (Γ.LinkOrbits μ) ×
    PeterWeylIndex (Γ.LinkOrbits μ) => ‖peterWeylEntry (Γ.transfer μ β) p.1 p.2‖
end CubicPeriodSublattice
namespace Block
variable {μ : Fin 4} (B : Block μ)
abbrev LinkType : Type := ↥(B.links : Set (SliceLink μ))
def IsInvariantKernel (K : (B.LinkType → specialUnitary) × (B.LinkType → specialUnitary) → ℂ) : Prop :=
  ∀ (g : B.vertices → specialUnitary) (U U' : B.LinkType → specialUnitary),
    K (gaugeAct B.links_subset_linksWithin g U,
      gaugeAct B.links_subset_linksWithin g U') = K (U, U')
structure OperatorProperties (β : ℝ) : Prop where
  rep_formula : ∀ g : B.vertices → specialUnitary,
    IsBlockGaugeRep B g (blockGaugeRep B g)
  rep_unitary : ∀ g : B.vertices → specialUnitary, IsUnitaryOp (blockGaugeRep B g)
  rep_mul : ∀ g g' : B.vertices → specialUnitary,
    blockGaugeRep B g * blockGaugeRep B g' = blockGaugeRep B (g * g')
  kernelOp_commute : ∀ K : (B.LinkType → specialUnitary) × (B.LinkType → specialUnitary) → ℂ,
    Continuous K → B.IsInvariantKernel K → ∀ g : B.vertices → specialUnitary,
      Schatten.kernelOp (haarPi B.LinkType) K * blockGaugeRep B g =
        blockGaugeRep B g * Schatten.kernelOp (haarPi B.LinkType) K
  link_continuous : Continuous fun p : (B.LinkType → specialUnitary) × (B.LinkType → specialUnitary) =>
    linkProductKernel β p.1 p.2
  sqrt_continuous : Continuous fun p : (B.LinkType → specialUnitary) × (B.LinkType → specialUnitary) =>
    sqrtLinkKernel β p.1 p.2
  isotypic_continuous : ∀ l : B.LinkType → HalfNatural,
    Continuous fun p : (B.LinkType → specialUnitary) × (B.LinkType → specialUnitary) =>
      isotypicKernel l p.1 p.2
  link_invariant : B.IsInvariantKernel fun p => linkProductKernel β p.1 p.2
  sqrt_invariant : B.IsInvariantKernel fun p => sqrtLinkKernel β p.1 p.2
  isotypic_invariant : ∀ l : B.LinkType → HalfNatural,
    B.IsInvariantKernel fun p => isotypicKernel l p.1 p.2
  link_traceClass : IsTraceClassPW (linkProductOperator β B.LinkType)
  sqrt_hilbertSchmidt : IsHilbertSchmidtPW (sqrtLinkOperator β B.LinkType)
  link_symm : IsSymmetricOp (linkProductOperator β B.LinkType)
  sqrt_symm : IsSymmetricOp (sqrtLinkOperator β B.LinkType)
  link_nonneg : IsPositiveOp (linkProductOperator β B.LinkType)
  sqrt_nonneg : IsPositiveOp (sqrtLinkOperator β B.LinkType)
  link_real : IsRealPreserving (linkProductOperator β B.LinkType)
  sqrt_real : IsRealPreserving (sqrtLinkOperator β B.LinkType)
end Block
def CubicTorusOperators.Statement : Prop :=
  ∀ β : ℝ, 0 < β →
    (∀ (Γ : CubicPeriodSublattice) (μ : Fin 4),
      Γ.GaugeRepProperties μ ∧ Γ.BoltzmannProperties μ β ∧ Γ.LinkOperatorProperties μ β ∧
        Γ.TransferProperties μ β) ∧
    ∀ (μ : Fin 4) (B : Block μ), B.OperatorProperties β
end YangMills.Construction.TransferOperators
end

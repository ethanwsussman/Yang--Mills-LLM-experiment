import YangMills.Construction.PartitionCubes.LocalOperators
import YangMills.Construction.RegionSequence.FineLatticeNorms
import YangMills.Construction.RegionSequence.SeparatedNestedRegions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Propagator
open Set
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
structure PropagatorConstants where
  δ : ℝ
  γ : ℝ
  B : ℝ
  blockLower : ℝ
  gapLower : ℝ
  Bα : ℝ → ℝ
  Bε : ℝ → ℝ
  Bαε : ℝ → ℝ → ℝ
instance instInhabitedPropagatorConstants : Inhabited PropagatorConstants :=
  ⟨⟨0, 0, 0, 0, 0, fun _ => 0, fun _ => 0, fun _ _ => 0⟩⟩
structure IsUnitSeparated (𝒮 : NestedRegions) (K m M R₁ : ℕ) : Prop where
  K_pos : 0 < K
  m_pos : 0 < m
  s_le : 𝒮.s ≤ K
  ξ_eq : 𝒮.ξ = unitSpacing 𝒮.L 𝒮.s
  side_eq : 𝒮.side = unitSide 𝒮.L m K 𝒮.s
  chain : IsSeparatedChain 𝒮.L 𝒮.ξ M R₁ 𝒮.s 𝒮.Ω
abbrev BondOperator (𝒮 : NestedRegions) : Type := (𝒮.FineBond → ℝ) → 𝒮.FineBond → ℝ
abbrev OperatorFunctional (𝒮 : NestedRegions) : Type := (BondOperator 𝒮 → ℝ) → ℝ
variable {𝒮 : NestedRegions} {M : ℕ}
def kernelStep (Q' Q : LevelCube 𝒮 M) : BondOperator 𝒮 :=
  fun A => Q'.kernel Q (Q.system.inv (Q.system.pullBonds Q.partitionFn A))
def kernelChain : List (LevelCube 𝒮 M) → BondOperator 𝒮
  | Q' :: Q :: ω, A => kernelStep Q' Q (kernelChain ω A)
  | _, A => A
def chainTerm : List (LevelCube 𝒮 M) → BondOperator 𝒮
  | Q :: ω, A => Q.invTerm (kernelChain ω A)
  | [], _ => 0
variable (𝒮 M) in
def oddChains : Set (List (LevelCube 𝒮 M)) := {ω | (∀ Q ∈ ω, Q ∈ active 𝒮 M) ∧ Odd ω.length}
variable (𝒮 M) in
def chainsOfLength (i : ℕ) : Set (List (LevelCube 𝒮 M)) :=
  {ω | (∀ Q ∈ ω, Q ∈ active 𝒮 M) ∧ ω.length = 2 * i + 1}
variable (𝒮 M) in
def remainderAdj : BondOperator 𝒮 :=
  adjointValue (𝒮.oneForms : Set (𝒮.FineBond → ℝ)) bondInner bondInner (remainderOp 𝒮 M)
def neumannTerm (𝒮 : NestedRegions) (M i : ℕ) : BondOperator 𝒮 :=
  fun A => approxInverse 𝒮 M ((remainderOp 𝒮 M)^[i] A)
def adjNeumannTerm (𝒮 : NestedRegions) (M i : ℕ) : BondOperator 𝒮 :=
  fun A => (remainderAdj 𝒮 M)^[i] (approxInverse 𝒮 M A)
def evalAt (T : BondOperator 𝒮) : OperatorFunctional 𝒮 := fun p => p T
variable (𝒮 M) in
def sumOverChains (i : ℕ) : OperatorFunctional 𝒮 :=
  fun p => ∑ᶠ ω ∈ chainsOfLength 𝒮 M i, p (chainTerm ω)
def tensorAbs {r : ℕ} (J : 𝒮.Tensor r) (x : 𝒮.FineBond) : ℝ := ⨆ ν, |J ν x|
def wideCell (y : 𝒮.Point) : Set 𝒮.Point := cubeHalfSide y (𝒮.levelScale y)
def TensorAnchored {r : ℕ} (X : Set 𝒮.Point) (J : 𝒮.Tensor r) : Prop :=
  ∀ ν, AnchorSupported X (J ν)
def IsOneFormIn (X : Set 𝒮.Point) (J : 𝒮.FineBond → ℝ) : Prop :=
  J ∈ 𝒮.oneForms ∧ AnchorSupported X J
def cutoffNorm (α : ℝ) (y : 𝒮.Point) (ζ : 𝒮.FineSite → ℝ) : ℝ :=
  holderSite α (𝒮.levelScale y) ζ + supSite ζ
variable (𝒮 M) in
structure NeumannIdentities : Prop where
  baseOp_approxInverse : ∀ A ∈ 𝒮.oneForms,
    baseOp (approxInverse 𝒮 M A) = A - remainderOp 𝒮 M A
  remainderOp_eq : ∀ A ∈ 𝒮.oneForms, ∀ b, remainderOp 𝒮 M A b =
    ∑ᶠ p ∈ active 𝒮 M ×ˢ active 𝒮 M, kernelStep p.1 p.2 A b
  existsUnique_resolvent : ∀ A ∈ 𝒮.oneForms,
    ∃! g, g ∈ 𝒮.oneForms ∧ g - remainderOp 𝒮 M g = A
  baseGreen_eq : ∀ A ∈ 𝒮.oneForms, ∀ g ∈ 𝒮.oneForms, g - remainderOp 𝒮 M g = A →
    baseGreen A = approxInverse 𝒮 M g
  hasSum_neumann : ∀ A ∈ 𝒮.oneForms, ∀ b,
    HasSum (fun i : ℕ => neumannTerm 𝒮 M i A b) (baseGreen A b)
  hasSum_adjNeumann : ∀ A ∈ 𝒮.oneForms, ∀ b,
    HasSum (fun i : ℕ => adjNeumannTerm 𝒮 M i A b) (baseGreen A b)
  hasSum_chains : ∀ A ∈ 𝒮.oneForms, ∀ b,
    HasSum (fun ω : oddChains 𝒮 M => chainTerm ω.1 A b) (baseGreen A b)
variable (𝒮) in
structure BaseGreenExists : Prop where
  invertible : 𝒮.BaseOpInvertible
  symm : ∀ A ∈ 𝒮.oneForms, ∀ A' ∈ 𝒮.oneForms,
    bondInner (baseGreen A) A' = bondInner A (baseGreen A')
  pos : ∀ A ∈ 𝒮.oneForms, A ≠ 0 → 0 < bondInner A (baseGreen A)
namespace PropagatorConstants
variable (c : PropagatorConstants)
def decay (y y' : 𝒮.Point) : ℝ := Real.exp (-c.δ * 𝒮.weightedDist y y')
structure OneFormBounds (R : OperatorFunctional 𝒮) (ρ : ℝ) (y y' : 𝒮.Point) : Prop where
  abs_le : ∀ J, IsOneFormIn (𝒮.cellOf y') J → ∀ x, AnchoredIn (𝒮.cellOf y) x →
    R (fun T => |T J x|) ≤ ρ * (c.B * 𝒮.levelScale y ^ 2 * c.decay y y' * supBond J)
  nabla_le : ∀ J, IsOneFormIn (𝒮.cellOf y') J → ∀ x, AnchoredIn (𝒮.cellOf y) x →
    R (fun T => tensorAbs (nablaOne (T J)) x) ≤
      ρ * (c.B * 𝒮.levelScale y * c.decay y y' * supBond J)
  lap_le : ∀ J, IsOneFormIn (𝒮.cellOf y') J → ∀ x, AnchoredIn (𝒮.cellOf y) x →
    R (fun T => |bondLap (T J) x|) ≤ ρ * (c.B * c.decay y y' * supBond J)
  holder_nabla_le : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ : 𝒮.FineSite → ℝ,
    VanishesOff (wideCell y) ζ → ∀ J, IsOneFormIn (𝒮.cellOf y') J →
    R (fun T => holderTensorOne α (smulSiteTensor ζ (nablaOne (T J)))) ≤
      ρ * (c.Bα α * 𝒮.levelScale y ^ (1 - α) * cutoffNorm α y ζ * c.decay y y' * supBond J)
  ltwo_le : ∀ ζ : 𝒮.FineSite → ℝ, VanishesOff (𝒮.cellOf y) ζ → ∀ J,
    IsOneFormIn (𝒮.cellOf y') J →
    R (fun T => ltwoBond (smulSiteBond ζ (T J))) ≤
      ρ * (c.B * 𝒮.levelScale y ^ 2 * supSite ζ * c.decay y y' * ltwoBond J)
  ltwo_nabla_le : ∀ ζ : 𝒮.FineSite → ℝ, VanishesOff (𝒮.cellOf y) ζ → ∀ J,
    IsOneFormIn (𝒮.cellOf y') J →
    R (fun T => ltwoTensor (smulSiteTensor ζ (nablaOne (T J)))) ≤
      ρ * (c.B * 𝒮.levelScale y * supSite ζ * c.decay y y' * ltwoBond J)
  ltwo_nablaTwo_le : ∀ ζ : 𝒮.FineSite → ℝ, VanishesOff (𝒮.cellOf y) ζ → ∀ J,
    IsOneFormIn (𝒮.cellOf y') J →
    R (fun T => ltwoTensor (smulSiteTensor ζ (nablaTwo (nablaOne (T J))))) ≤
      ρ * (c.B * supSite ζ * c.decay y y' * ltwoBond J)
structure DivBounds (R : OperatorFunctional 𝒮) (ρ : ℝ) (y y' : 𝒮.Point) : Prop where
  nabla_div_le : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ J : 𝒮.Tensor 1,
    TensorAnchored (wideCell y') J → ∀ x, AnchoredIn (𝒮.cellOf y) x →
    R (fun T => tensorAbs (nablaOne (T (divOne J))) x) ≤
      ρ * (c.Bε ε * c.decay y y' *
        (holderTensor ε (𝒮.levelScale y') J + supTensor J))
  holder_nabla_div_le : ∀ α ε : ℝ, 0 ≤ α → α < 1 → 0 < ε → α + ε < 1 →
    ∀ ζ : 𝒮.FineSite → ℝ, VanishesOff (wideCell y) ζ → ∀ J : 𝒮.Tensor 1,
    TensorAnchored (wideCell y') J →
    R (fun T => holderTensorOne α (smulSiteTensor ζ (nablaOne (T (divOne J))))) ≤
      ρ * (c.Bαε α ε * 𝒮.levelScale y ^ (-α) * cutoffNorm α y ζ * c.decay y y' *
        (holderTensor (α + ε) (𝒮.levelScale y') J + supTensor J))
  ltwo_nabla_div_le : ∀ ζ : 𝒮.FineSite → ℝ, VanishesOff (𝒮.cellOf y) ζ →
    ∀ J : 𝒮.Tensor 1, TensorAnchored (𝒮.cellOf y') J →
    R (fun T => ltwoTensor (smulSiteTensor ζ (nablaOne (T (divOne J))))) ≤
      ρ * (c.B * supSite ζ * c.decay y y' * ltwoTensor J)
structure AllBounds (R : OperatorFunctional 𝒮) (ρ : ℝ) (y y' : 𝒮.Point) : Prop extends
    c.OneFormBounds R ρ y y', c.DivBounds R ρ y y'
structure DivSourceBounds (T : BondOperator 𝒮) (ρ : ℝ) (y y' : 𝒮.Point) : Prop where
  abs_le : ∀ J : 𝒮.Tensor 1, TensorAnchored (𝒮.cellOf y') J → ∀ x, AnchoredIn (𝒮.cellOf y) x →
    |T (divOne J) x| ≤ ρ * (c.B * 𝒮.levelScale y * c.decay y y' * supTensor J)
  holder_le : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ : 𝒮.FineSite → ℝ, VanishesOff (wideCell y) ζ →
    ∀ J : 𝒮.Tensor 1, TensorAnchored (𝒮.cellOf y') J →
    holderBondOne α (smulSiteBond ζ (T (divOne J))) ≤
      ρ * (c.Bα α * 𝒮.levelScale y ^ (1 - α) * cutoffNorm α y ζ * c.decay y y' * supTensor J)
  ltwo_le : ∀ ζ : 𝒮.FineSite → ℝ, VanishesOff (𝒮.cellOf y) ζ → ∀ J : 𝒮.Tensor 1,
    TensorAnchored (𝒮.cellOf y') J →
    ltwoBond (smulSiteBond ζ (T (divOne J))) ≤
      ρ * (c.B * 𝒮.levelScale y * supSite ζ * c.decay y y' * ltwoTensor J)
  ltwo_divTwo_le : ∀ ζ : 𝒮.FineSite → ℝ, VanishesOff (𝒮.cellOf y) ζ →
    ∀ J : 𝒮.Tensor 2, TensorAnchored (𝒮.cellOf y') J →
    ltwoBond (smulSiteBond ζ (T (divTwo J))) ≤
      ρ * (c.B * supSite ζ * c.decay y y' * ltwoTensor J)
variable (𝒮 M)
structure CoerciveBound : Prop extends BaseGreenExists 𝒮 where
  lower : ∀ A ∈ 𝒮.oneForms, c.γ * bondInner A A ≤ bondInner A (baseOp A)
structure NeumannExpansion : Prop extends NeumannIdentities 𝒮 M where
  neumann_bounds : ∀ i : ℕ, ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres,
    c.AllBounds (evalAt (neumannTerm 𝒮 M i)) ((2 : ℝ)⁻¹ ^ i) y y'
  chain_bounds : ∀ i : ℕ, ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres,
    c.AllBounds (sumOverChains 𝒮 M i) ((2 : ℝ)⁻¹ ^ i) y y'
  adjNeumann_bounds : ∀ i : ℕ, ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres,
    c.DivSourceBounds (adjNeumannTerm 𝒮 M i) ((2 : ℝ)⁻¹ ^ i) y y'
structure Conclusion : Prop where
  coercive : c.CoerciveBound 𝒮
  baseGreen_bounds : ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres,
    c.AllBounds (evalAt baseGreen) 1 y y'
  baseGreen_div_bounds : ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres,
    c.DivSourceBounds baseGreen 1 y y'
  expansion : c.NeumannExpansion 𝒮 M
end PropagatorConstants
end Propagator
end YangMills.Construction

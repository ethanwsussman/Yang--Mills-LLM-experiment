import YangMills.Construction.Dirichlet.GreenOperatorEstimates
import YangMills.Construction.Lattice.GreenOperatorsOfCubes
import YangMills.Construction.SeparatedSequences.FourGroupsOfInequalitiesForTheGreenOperator
import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import YangMills.Construction.SeparatedSequences.SupDistanceInLevelUnits
import YangMills.Construction.Torus.AveragedSquareExpansion
import YangMills.Construction.Torus.ExpansionOfTheInverseOverTheCubes
import YangMills.Construction.Torus.GeometryOfCovers
import YangMills.Construction.TorusForms.AxialLowerBound
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators TorusMetric
noncomputable section
namespace SeparatedClasses
structure OperatorConstants where
  zeroFormRate : ℝ
  avgSqRate : ℝ
  cubeRate : ℝ
  oneFormRate : ℝ
  coarseRate : ℝ
  extRate : ℝ
  coarseLowerBound : ℝ
  treeLowerBound : ℝ
  K : ℝ
  Kα : ℝ → ℝ
  Kε : ℝ → ℝ
  Kαε : ℝ → ℝ → ℝ
structure OperatorConstants.Pos (n : OperatorConstants) : Prop where
  zeroFormRate_pos : 0 < n.zeroFormRate
  avgSqRate_pos : 0 < n.avgSqRate
  cubeRate_pos : 0 < n.cubeRate
  oneFormRate_pos : 0 < n.oneFormRate
  coarseRate_pos : 0 < n.coarseRate
  extRate_pos : 0 < n.extRate
  coarseLowerBound_pos : 0 < n.coarseLowerBound
  treeLowerBound_pos : 0 < n.treeLowerBound
namespace ClassData
variable (C : ClassData) (Ω : ℕ → Set C.Point) (φ : BondFrame)
def oneGreenApply (g : C.BondFn) : C.BondFn :=
  (C.unitSpacingParameters.oneGreen Ω φ
    ⟨bondProjection C.cutoff (Ω 0) φ g, LinearMap.mem_range_self _ _⟩).1
def oneGreenDiv (J : C.Tensors 1) : C.BondFn :=
  C.oneGreenApply Ω φ (C.divOne Ω φ J)
def gradOneGreen (J : C.BondFn) : C.Tensors 1 :=
  C.gradOne (C.oneGreenApply Ω φ J)
def gradOneGreenDiv (J : C.Tensors 1) : C.Tensors 1 :=
  C.gradOne (C.oneGreenDiv Ω φ J)
abbrev CoarseSeriesExpansion : Type := ↥(C.unitSpacingParameters.principalBonds Ω φ)
variable {C Ω φ}
def tensorAbsAt {r : ℕ} (J : C.Tensors r) (x : C.BareBond) : ℝ := ⨆ ν, |J ν x|
def siteMulTensor {r : ℕ} (ζ : C.SiteFn) (J : C.Tensors r) : C.Tensors r :=
  fun ν => siteMulBond ζ (J ν)
theorem Apex.point_mem_allLayerPoints (y : C.Apex Ω) :
    y.point ∈ C.unitSpacingParameters.allLayerPoints Ω :=
  mem_iUnion₂.mpr ⟨y.1.1, y.2.1, y.1.2, y.2.2, rfl⟩
def apexKernel (T : Module.End ℝ (C.unitSpacingParameters.CoarseZeroForms Ω)) (y y' : C.Apex Ω) : ℝ :=
  countingKernel (fun f => T f) ⟨y.point, y.point_mem_allLayerPoints⟩
    ⟨y'.point, y'.point_mem_allLayerPoints⟩
def coarseKernel (T : Module.End ℝ (C.unitSpacingParameters.CoarseOneForms Ω φ))
    (c c' : C.CoarseSeriesExpansion Ω φ) : ℝ :=
  countingKernel (fun f => T f) c c'
def coarseFoot (c : C.CoarseSeriesExpansion Ω φ) : C.Point := (C.expansionSource c.1 : C.Point)
def coarseMesh (c : C.CoarseSeriesExpansion Ω φ) : ℝ := C.expansionMesh c.1
def pointDecay (Ω : ℕ → Set C.Point) (δ : ℝ) (p p' : C.Point) : ℝ :=
  Real.exp (-δ * (C.chainDist Ω p p').toReal)
def IsCutoffAt (y : C.Apex Ω) (ζ : C.SiteFn) : Prop :=
  ∀ x : C.BareSite, y.mesh ≤ C.supDist (x : C.Point) y.point → ζ x = 0
def cutoffNorm (α : ℝ) (y : C.Apex Ω) (ζ : C.SiteFn) : ℝ :=
  C.siteScaledHolder α y.mesh ζ + C.siteSupNorm ζ
structure ZeroGreenBounds (n : OperatorConstants) (y y' : C.Apex Ω) : Prop where
  abs_le : ∀ lam : C.SiteFn, SiteSupportedOn y'.block lam → ∀ x ∈ sitesWithin y.block,
    |C.greenOp Ω lam x| ≤ n.K * y.mesh ^ 2 * expDecay (n.zeroFormRate / 2) y y' * C.siteSupNorm lam
  grad_le : ∀ lam : C.SiteFn, SiteSupportedOn y'.block lam →
    ∀ x : C.BareBond, x.1 ∈ bondsWithin y.block →
      |C.siteGrad (C.greenOp Ω lam) x| ≤
        n.K * y.mesh * expDecay (n.zeroFormRate / 2) y y' * C.siteSupNorm lam
  div_le : ∀ lam : C.BondFn, BondSupportedOn y'.block lam → ∀ x ∈ sitesWithin y.block,
    |C.greenDiv Ω lam x| ≤ n.K * y.mesh * expDecay (n.zeroFormRate / 2) y y' * C.bondSupNorm lam
  lap_le : ∀ lam : C.SiteFn, SiteSupportedOn y'.block lam → ∀ x ∈ sitesWithin y.block,
    |C.siteLap (C.greenOp Ω lam) x| ≤ n.K * expDecay (n.zeroFormRate / 2) y y' * C.siteSupNorm lam
  grad_holder_le : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ, IsCutoffAt y ζ →
    ∀ lam : C.SiteFn, SiteSupportedOn y'.block lam →
      C.bondHolder α (siteMulBond ζ (C.siteGrad (C.greenOp Ω lam))) ≤
        n.Kα α * y.mesh ^ (1 - α) * cutoffNorm α y ζ * expDecay (n.zeroFormRate / 2) y y' *
          C.siteSupNorm lam
  div_holder_le : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ, IsCutoffAt y ζ →
    ∀ lam : C.BondFn, BondSupportedOn y'.block lam →
      C.siteHolder α (fun x => ζ x * C.greenDiv Ω lam x) ≤
        n.Kα α * y.mesh ^ (1 - α) * cutoffNorm α y ζ * expDecay (n.zeroFormRate / 2) y y' *
          C.bondSupNorm lam
structure OneGreenPointBounds (n : OperatorConstants) (φ : BondFrame) (y y' : C.Apex Ω) : Prop where
  abs_le : ∀ J ∈ C.forms Ω φ, BondSupportedOn y'.block J →
    ∀ x : C.BareBond, x.1 ∈ bondsWithin y.block →
      |C.oneGreenApply Ω φ J x| ≤ n.K * y.mesh ^ 2 * expDecay n.oneFormRate y y' * C.bondSupNorm J
  grad_le : ∀ J ∈ C.forms Ω φ, BondSupportedOn y'.block J →
    ∀ x : C.BareBond, x.1 ∈ bondsWithin y.block →
      tensorAbsAt (C.gradOneGreen Ω φ J) x ≤
        n.K * y.mesh * expDecay n.oneFormRate y y' * C.bondSupNorm J
  div_le : ∀ J : C.Tensors 1, (∀ ν, BondSupportedOn y'.block (J ν)) →
    ∀ x : C.BareBond, x.1 ∈ bondsWithin y.block →
      |C.oneGreenDiv Ω φ J x| ≤ n.K * y.mesh * expDecay n.oneFormRate y y' * C.tensorSupNorm J
  lap_le : ∀ J ∈ C.forms Ω φ, BondSupportedOn y'.block J →
    ∀ x : C.BareBond, x.1 ∈ bondsWithin y.block →
      |C.bondLap (C.oneGreenApply Ω φ J) x| ≤ n.K * expDecay n.oneFormRate y y' * C.bondSupNorm J
structure OneGreenHolderBounds (n : OperatorConstants) (φ : BondFrame) (y y' : C.Apex Ω) : Prop where
  grad_holder_le : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ, IsCutoffAt y ζ → ∀ J ∈ C.forms Ω φ,
    BondSupportedOn y'.block J →
      C.tensorHolder α (siteMulTensor ζ (C.gradOneGreen Ω φ J)) ≤
        n.Kα α * y.mesh ^ (1 - α) * cutoffNorm α y ζ * expDecay n.oneFormRate y y' *
          C.bondSupNorm J
  div_holder_le : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ, IsCutoffAt y ζ → ∀ J : C.Tensors 1,
    (∀ ν, BondSupportedOn y'.block (J ν)) →
      C.bondHolder α (siteMulBond ζ (C.oneGreenDiv Ω φ J)) ≤
        n.Kα α * y.mesh ^ (1 - α) * cutoffNorm α y ζ * expDecay n.oneFormRate y y' *
          C.tensorSupNorm J
structure OneGreenDivBounds (n : OperatorConstants) (φ : BondFrame) (y y' : C.Apex Ω) : Prop where
  abs_le : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ J : C.Tensors 1,
    (∀ ν, AnchorSupportedIn Ω y'.doubledBlock (J ν)) →
    ∀ x : C.BareBond, x.1 ∈ bondsWithin y.block →
      tensorAbsAt (C.gradOneGreenDiv Ω φ J) x ≤
        n.Kε ε * expDecay n.oneFormRate y y' *
          (C.tensorScaledHolder ε y'.mesh J + C.tensorSupNorm J)
  holder_le : ∀ α ε : ℝ, 0 ≤ α → α < 1 → 0 < ε → α + ε < 1 → ∀ ζ, IsCutoffAt y ζ →
    ∀ J : C.Tensors 1, (∀ ν, AnchorSupportedIn Ω y'.doubledBlock (J ν)) →
      C.tensorHolder α (siteMulTensor ζ (C.gradOneGreenDiv Ω φ J)) ≤
        n.Kαε α ε * y.mesh ^ (-α) * cutoffNorm α y ζ * expDecay n.oneFormRate y y' *
          (C.tensorScaledHolder (α + ε) y'.mesh J + C.tensorSupNorm J)
structure OneGreenL2Bounds (n : OperatorConstants) (φ : BondFrame) (y y' : C.Apex Ω) : Prop where
  l2_le : ∀ ζ, SiteSupportedOn y.block ζ → ∀ J ∈ C.forms Ω φ, BondSupportedOn y'.block J →
    C.bondL2 (siteMulBond ζ (C.oneGreenApply Ω φ J)) ≤
      n.K * y.mesh ^ 2 * C.siteSupNorm ζ * expDecay n.oneFormRate y y' * C.bondL2 J
  grad_l2_le : ∀ ζ, SiteSupportedOn y.block ζ → ∀ J ∈ C.forms Ω φ, BondSupportedOn y'.block J →
    C.tensorL2 (siteMulTensor ζ (C.gradOneGreen Ω φ J)) ≤
      n.K * y.mesh * C.siteSupNorm ζ * expDecay n.oneFormRate y y' * C.bondL2 J
  div_l2_le : ∀ ζ, SiteSupportedOn y.block ζ → ∀ J : C.Tensors 1,
    (∀ ν, BondSupportedOn y'.block (J ν)) →
      C.bondL2 (siteMulBond ζ (C.oneGreenDiv Ω φ J)) ≤
        n.K * y.mesh * C.siteSupNorm ζ * expDecay n.oneFormRate y y' * C.tensorL2 J
  grad_div_l2_le : ∀ ζ, SiteSupportedOn y.block ζ → ∀ J : C.Tensors 1,
    (∀ ν, BondSupportedOn y'.block (J ν)) →
      C.tensorL2 (siteMulTensor ζ (C.gradOneGreenDiv Ω φ J)) ≤
        n.K * C.siteSupNorm ζ * expDecay n.oneFormRate y y' * C.tensorL2 J
  grad_grad_l2_le : ∀ ζ, SiteSupportedOn y.block ζ → ∀ J ∈ C.forms Ω φ,
    BondSupportedOn y'.block J →
      C.tensorL2 (siteMulTensor ζ (C.gradTwo (C.gradOneGreen Ω φ J))) ≤
        n.K * C.siteSupNorm ζ * expDecay n.oneFormRate y y' * C.bondL2 J
  div_div_l2_le : ∀ ζ, SiteSupportedOn y.block ζ → ∀ J : C.Tensors 2,
    (∀ ν, BondSupportedOn y'.block (J ν)) →
      C.bondL2 (siteMulBond ζ (C.oneGreenApply Ω φ (C.divTwo Ω φ J))) ≤
        n.K * C.siteSupNorm ζ * expDecay n.oneFormRate y y' * C.tensorL2 J
variable (Ω φ)
def extKernel (b : C.BareBond) (c : C.CoarseSeriesExpansion Ω φ) : ℝ :=
  countingKernel (fun B b' => (C.unitSpacingParameters.oneExtension Ω φ B).1 b') b c
def extColumn (c : C.CoarseSeriesExpansion Ω φ) : C.BondFn := fun b => extKernel Ω φ b c
variable {Ω φ}
structure ExtBounds (n : OperatorConstants) (y : C.Apex Ω) (c : C.CoarseSeriesExpansion Ω φ) : Prop where
  abs_le : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ b : C.BareBond, b.1 ∈ bondsWithin y.block →
    |extKernel Ω φ b c| ≤
      n.Kα α * pointDecay Ω n.extRate y.point (coarseFoot c)
  grad_le : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ b : C.BareBond, b.1 ∈ bondsWithin y.block →
    (⨆ ν, |C.bondFwd ν (extColumn Ω φ c) b|) ≤
      n.Kα α * y.mesh⁻¹ * pointDecay Ω n.extRate y.point (coarseFoot c)
  holder_le : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ, IsCutoffAt y ζ →
    C.tensorHolder α (siteMulTensor ζ (C.gradOne (extColumn Ω φ c))) ≤
      n.Kα α * y.mesh ^ (-1 - α) * cutoffNorm α y ζ *
        pointDecay Ω n.extRate y.point (coarseFoot c)
variable (Ω φ)
def coarseWeightedSq (B : C.unitSpacingParameters.CoarseOneForms Ω φ) : ℝ :=
  ∑ᶠ c : C.CoarseSeriesExpansion Ω φ, coarseMesh c ^ (4 + 2) * |B c| ^ 2
structure AvgOneGreenLowerBound (n : OperatorConstants) : Prop where
  total : ∀ B : C.unitSpacingParameters.CoarseOneForms Ω φ,
    n.coarseLowerBound * coarseWeightedSq Ω φ B ≤
      C.unitSpacingParameters.coarseOneInner Ω φ B
        (C.unitSpacingParameters.averagedOneGreen Ω φ B)
  restricted : ∀ (X : Set (C.CoarseSeriesExpansion Ω φ)) (B : C.unitSpacingParameters.CoarseOneForms Ω φ),
    (∀ c, c ∉ X → B c = 0) →
      n.coarseLowerBound * coarseWeightedSq Ω φ B ≤
        C.unitSpacingParameters.coarseOneInner Ω φ B
          ((indicatorMul X ∘ₗ C.unitSpacingParameters.averagedOneGreen Ω φ ∘ₗ indicatorMul X) B)
end ClassData
namespace PeriodicExpansions
variable {L j N : ℕ} (S : PeriodicLattice.Scales 4 L j N) (Λ' : Set (GridPoint 4 S.coarseMesh))
abbrev CenteredCoarseIndex : Type :=
  ↥(linksAvoiding (S.centeredRegion Λ')) ⊕ ↥(linksMeeting Λ')
def centeredAvg : OneForm 4 S.fineMesh →ₗ[ℝ] (CenteredCoarseIndex S Λ' → ℝ) where
  toFun A := Sum.elim (fun b => S.centeredFineFormAvg A b.1)
    (fun c => S.centeredCoarseFormAvg (S.centeredFineFormAvg A) c.1)
  map_add' A A' := by
    funext r
    rcases r with b | c <;> simp
  map_smul' a A := by
    funext r
    rcases r with b | c <;> simp
def centeredInner (B B' : CenteredCoarseIndex S Λ' → ℝ) : ℝ :=
  (∑ᶠ b : ↥(linksAvoiding (S.centeredRegion Λ')), B (Sum.inl b) * B' (Sum.inl b)) +
    (L : ℝ) ^ 4 * ∑ᶠ c : ↥(linksMeeting Λ'), B (Sum.inr c) * B' (Sum.inr c)
def centeredCompress (G : Module.End ℝ (OneForm 4 S.fineMesh)) :
    Module.End ℝ (CenteredCoarseIndex S Λ' → ℝ) :=
  centeredAvg S Λ' ∘ₗ G ∘ₗ
    GeneralTorus.adjointFor (fun A A' => inner ℝ A A') (centeredInner S Λ')
      (centeredAvg S Λ')
end PeriodicExpansions
section Trees
open Construction.Lattice BlockSpin
variable (S : Lattice.LatticeParameters) {ℓ : Fin S.d → ℝ} [PeriodsMultipleOfBlock S ℓ]
def cornerTreeLinks (y : Lattice.LatticeSite ℓ (S.L : ℝ)) : Set (Lattice.Link ℓ 1) :=
  {b | ∃ σ : Fin S.d → ℤ, (∀ μ, 0 ≤ σ μ ∧ σ μ ≤ (S.L : ℤ) - 1) ∧
    ∃ t ∈ (axisPath
        ((PeriodsMultipleOfBlock.isBlockSpacing_one (S := S) (ℓ := ℓ)).toFineSite y -
          gridPoint ℓ 1 fun _ => (S.offset : ℤ)) σ).steps, t.link = b}
def VanishesOnCornerTrees (Λ' : Set (Lattice.LatticeSite ℓ (S.L : ℝ))) (B : Cochain1 ℓ 1) : Prop :=
  ∀ y ∈ Λ', ∀ b ∈ cornerTreeLinks S y, B b = 0
end Trees
namespace ClassData
variable (C : ClassData)
abbrev centeredBlockParams : Lattice.LatticeParameters :=
  ⟨4, C.L, (C.L - 1) / 2, by norm_num,
    by have := C.isAdmissible.2; omega,
    by have := C.isAdmissible.2; omega⟩
def levelPeriods (n : ℕ) : Fin C.centeredBlockParams.d → ℝ :=
  fun _ => 2 * (C.L : ℝ) ^ ((C.m : ℕ) + C.cutoff - n)
def IsLevelLift (n : ℕ) (p : C.Point) (x : Lattice.PeriodicTorus (C.levelPeriods n)) : Prop :=
  ∃ v : Fin 4 → ℝ, (p = fun μ => (v μ : AddCircle (PeriodicLattice.torusSide C.L C.m))) ∧
    x = Lattice.torusMk (C.levelPeriods n) fun μ => (C.L : ℝ) ^ (C.cutoff - n) * v μ
variable (Ω : ℕ → Set C.Point)
def TreeLowerBoundAt (n : ℕ)
    [BlockSpin.PeriodsMultipleOfBlock C.centeredBlockParams (C.levelPeriods n)] : Prop :=
  ∀ (Λ' : Set (Lattice.LatticeSite (C.levelPeriods n) (C.L : ℝ)))
    (B : Lattice.Cochain1 (C.levelPeriods n) 1),
    (∀ x ∈ BlockSpin.blockUnion C.centeredBlockParams 1 1 Λ', ∃ p ∈ Ω 0, C.IsLevelLift n p x) →
    B ∈ Lattice.supportedIn
      (Lattice.linksTouching (BlockSpin.blockUnion C.centeredBlockParams 1 1 Λ')) →
    (BlockSpin.VanishesOnBlockTrees C.centeredBlockParams Λ' B ∨
      VanishesOnCornerTrees C.centeredBlockParams Λ' B) →
    BlockSpin.AxialBound C.centeredBlockParams Λ' B
end ClassData
section Expansions
variable {D : Weighted.TorusData} {B : Weighted.SeparatedChain D} {ι : Type*}
  {𝒟 : ι → D.CoverPiece}
structure AvgSqInverseNeumann (δ : B.Localization 𝒟) (c : ℝ) : Prop where
  isUnit_one_sub : IsUnit (1 - δ.error)
  inverse_eq : Ring.inverse B.avgGreenSq = δ.approxInverse * Ring.inverse (1 - δ.error)
  hasSum_powers : ∀ y y' : ↥B.allSites,
    HasSum (fun n : ℕ => B.kernel (δ.approxInverse * δ.error ^ n) y y')
      (B.kernel (Ring.inverse B.avgGreenSq) y y')
  hasSum_terms : ∀ y y' : ↥B.allSites,
    HasSum (fun n : ℕ => B.kernel (∑ᶠ ϖ, δ.neumannTerm n ϖ) y y')
      (B.kernel (Ring.inverse B.avgGreenSq) y y')
  sum_terms_le : ∀ (n : ℕ) (y y' : ↥B.allSites),
    ∑ᶠ ϖ, |B.kernel (δ.neumannTerm n ϖ) y y'| ≤
      1 / 2 * Weighted.expansionConstBound 4 D.L c * (2 : ℝ)⁻¹ ^ n * B.siteScale y ^ (-4 : ℤ) *
        Real.exp (-(1 / 2 * Weighted.expansionDecayRate 4 D.L) * B.weightedDistance y y')
end Expansions
section OneFormExpansion
open RegionSequence RegionSequence.NestedRegions PartitionCubes Propagator Propagator.SequenceOfRegions
structure OneGreenExpansion (𝒮 : RegionSequence.NestedRegions) (M : ℕ) : Prop where
  existsUnique : ∀ A ∈ 𝒮.oneForms, ∃! g, g ∈ 𝒮.oneForms ∧ g - remainderOp 𝒮 M g = A
  green_eq : ∀ A ∈ 𝒮.oneForms, ∀ g ∈ 𝒮.oneForms, g - remainderOp 𝒮 M g = A →
    baseGreen A = approxInverse 𝒮 M g
  hasSum_neumann : ∀ A ∈ 𝒮.oneForms, ∀ b,
    HasSum (fun i : ℕ => neumannTerm 𝒮 M i A b) (baseGreen A b)
  hasSum_adj : ∀ A ∈ 𝒮.oneForms, ∀ b,
    HasSum (fun i : ℕ => adjNeumannTerm 𝒮 M i A b) (baseGreen A b)
  hasSum_chains : ∀ A ∈ 𝒮.oneForms, ∀ b,
    HasSum (fun ω : oddChains 𝒮 M => chainTerm ω.1 A b) (baseGreen A b)
  neumann_bounds : ∀ i : ℕ, ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres,
    (chosenConstants 𝒮.L).AllBounds (evalAt (neumannTerm 𝒮 M i)) ((2 : ℝ)⁻¹ ^ i) y y'
  adj_bounds : ∀ i : ℕ, ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres,
    (chosenConstants 𝒮.L).DivSourceBounds (adjNeumannTerm 𝒮 M i) ((2 : ℝ)⁻¹ ^ i) y y'
end OneFormExpansion
section CoarseExpansion
open GeneralTorus GeneralTorus.GaugeSetting GeneralTorus.CubeGaugeSetting
structure CoarseInverseExpansion (C : CubeGaugeSetting) : Prop where
  inverse_eq : Ring.inverse C.coarseGreen =
    C.approxInverse ∘ₗ Ring.inverse (1 - C.remainder)
  hasSum_powers : ∀ c c' : C.CoarseBond,
    HasSum (fun k : ℕ => C.matrixEntry (C.approxInverse ∘ₗ C.remainder ^ k) c c')
      (C.matrixEntry (Ring.inverse C.coarseGreen) c c')
  hasSum_words : ∀ c c' : C.CoarseBond,
    HasSum (fun p : (k : ℕ) × C.CubeWord k => C.matrixEntry (wordTerm p.2) c c')
      (C.matrixEntry (Ring.inverse C.coarseGreen) c c')
  words_le : ∀ (k : ℕ) (c c' : C.CoarseBond),
    ∑' ω : C.CubeWord k, |C.matrixEntry (wordTerm ω) c c'| ≤
      3 * 2 ^ 4 * (2 * (SeparatedSequences.compressedGreenLowerBound 4 1)⁻¹) * ((2 : ℝ) ^ k)⁻¹ *
        (coarseSpacing c)⁻¹ * (coarseSpacing c')⁻¹ *
        Real.exp (-(1 / 2 * InverseBounds.decayRateOfInverse C.data.L) * coarseDist c c')
end CoarseExpansion
namespace ClassData
variable (C : ClassData) (Ω : ℕ → Set C.Point) (φ : BondFrame)
open Construction.Lattice BlockSpin
def coarseHead (c : Σ j : ℕ, C.PosLatticeBond j) : C.LatticeSite c.1 := c.2.1.target
def curlExtSq (B : C.unitSpacingParameters.CoarseOneForms Ω φ) : ℝ :=
  latticeInner C.L C.t (DirichletOperators.curl C.t (C.unitSpacingParameters.oneExtension Ω φ B).1)
    (DirichletOperators.curl C.t (C.unitSpacingParameters.oneExtension Ω φ B).1)
variable {C Ω}
def blocksOfSites (Θ' : Set (Lattice.LatticeSite (C.levelPeriods C.t) (C.L : ℝ))) : Set C.Point :=
  {x | ∃ p, (∃ y ∈ Θ', C.IsLevelLift C.t p (y : Lattice.PeriodicTorus (C.levelPeriods C.t))) ∧
    C.supDist x p ≤ (C.L : ℝ) / 2}
variable (Ω) in
structure IsInteriorBlockSet (Θ' : Set (Lattice.LatticeSite (C.levelPeriods C.t) (C.L : ℝ))) :
    Prop where
  eq_sUnion : ∃ F ⊆ PeriodicLattice.standardCubePartition C.L C.m
      (C.scales.blockPartitionIndex (C.t + 1)),
    blocksOfSites Θ' = ⋃₀ F
  subset_member : blocksOfSites Θ' ⊆ C.memberAt Ω C.t
  dist_complement_gt : ENNReal.ofReal ((C.gapSize : ℝ) * (C.blockSize : ℝ)) <
    supDistInLevelUnits C.cutoff C.t
      (PeriodicLattice.complementRegion (C.scales.blockPartitionIndex C.t) (C.memberAt Ω C.t))
      (blocksOfSites Θ')
variable [PeriodsMultipleOfBlock C.centeredBlockParams (C.levelPeriods C.t)]
structure IsTreeConstrained (Θ' : Set (Lattice.LatticeSite (C.levelPeriods C.t) (C.L : ℝ)))
    (B : Cochain1 (C.levelPeriods C.t) 1) : Prop where
  mem_supportedIn : B ∈ supportedIn (linksTouching (blockUnion C.centeredBlockParams 1 1 Θ'))
  blockAverage_eq_zero : ∀ c, blockAverage1 C.centeredBlockParams 1 1 (C.L : ℝ) B c = 0
  vanishesOnTrees : VanishesOnBlockTrees C.centeredBlockParams Θ' B
structure IsParametrization (Θ' : Set (Lattice.LatticeSite (C.levelPeriods C.t) (C.L : ℝ)))
    (V : Set (Lattice.Link (C.levelPeriods C.t) 1))
    (P : (V → ℝ) →ₗ[ℝ] Cochain1 (C.levelPeriods C.t) 1) : Prop where
  constrained : ∀ B', IsTreeConstrained Θ' (P B')
  apply_eq : ∀ (B' : V → ℝ) (b : V), P B' b = B' b
  surjective : ∀ B, IsTreeConstrained Θ' B → ∃ B', P B' = B
variable (Ω)
def toCoarseField (B : Cochain1 (C.levelPeriods C.t) 1) : C.unitSpacingParameters.CoarseOneForms Ω φ :=
  fun c => ∑ᶠ b ∈ {b : Lattice.Link (C.levelPeriods C.t) 1 | c.1.1 = C.t ∧
    C.IsLevelLift C.t (C.expansionSource c.1 : C.Point) (b.1 : Lattice.PeriodicTorus (C.levelPeriods C.t)) ∧
    C.IsLevelLift C.t (C.coarseHead c.1 : C.Point)
      (b.head : Lattice.PeriodicTorus (C.levelPeriods C.t))}, B b
def ParametrizedLowerBound (n : OperatorConstants) : Prop :=
  ∀ Θ' : Set (Lattice.LatticeSite (C.levelPeriods C.t) (C.L : ℝ)), IsInteriorBlockSet Ω Θ' →
    ∀ (V : Set (Lattice.Link (C.levelPeriods C.t) 1))
      (P : (V → ℝ) →ₗ[ℝ] Cochain1 (C.levelPeriods C.t) 1), IsParametrization Θ' V P →
      ∀ B' : V → ℝ,
        n.treeLowerBound / (12 * 4 ^ 2) * ((C.L : ℝ) ^ (4 + 1))⁻¹ * latticeNorm 4 1 (P B') ^ 2 ≤
            C.curlExtSq Ω φ (toCoarseField Ω φ (P B')) ∧
          n.treeLowerBound / (12 * 4 ^ 2) * ((C.L : ℝ) ^ (4 + 1))⁻¹ * ∑ᶠ b : V, |B' b| ^ 2 ≤
            n.treeLowerBound / (12 * 4 ^ 2) * ((C.L : ℝ) ^ (4 + 1))⁻¹ *
              latticeNorm 4 1 (P B') ^ 2
end ClassData
structure OperatorSetting extends SingleSequence.SequenceData where
  twelve_L_le_blockSize : 12 * data.L ≤ data.blockSize
namespace OperatorSetting
variable (s : OperatorSetting) (n : OperatorConstants)
def walkConstants : DirichletGreen.GreenConstants :=
  ⟨n.zeroFormRate, 0, 0, n.K, (s.data.blockSize : ℝ) / 2, n.Kα⟩
def WalkExpansionHolds : Prop :=
  ∀ 𝒮 : s.BlockSettingType, s.IsBlockSetting 𝒮 →
    ∀ E : Dirichlet.CentredCube 4 s.unitTorusSide → Set (Dirichlet.LatticeBond 4 s.unitTorusSide 𝒮.ξ),
      𝒮.IsRuleFamily E →
      (∀ f : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.Ω 0) f →
        ∀ x, HasSum (fun ω : {ω : List (Dirichlet.CentredCube 4 s.unitTorusSide) // 𝒮.IsCubeWalk ω} =>
          𝒮.walkOperator E ω.1 f x) (𝒮.fullGreen f x)) ∧
      DirichletGreen.GreenConstants.WalkSumBounds 𝒮 (s.walkConstants n) E
def AvgSqInverseHolds : Prop :=
  ∀ (D : Weighted.TorusData) (B : Weighted.SeparatedChain D), s.IsWeightedTorus D B →
    ∀ (ι : Type) (𝒟 : ι → D.CoverPiece),
      B.IsCover (Weighted.coverConst 4 D.L) 𝒟 →
      (∀ i, B.CutoffVanishesOffLayers (𝒟 i)) →
      ∀ δ : B.Localization 𝒟,
        AvgSqInverseNeumann δ (Weighted.coverConst 4 D.L)
def MatchesConstants (k : PeriodicLattice.DecayConstants) : Prop :=
  k.base = n.K ∧ (∀ α, 0 ≤ α → α < 1 → k.holder α = n.Kα α) ∧
    (∀ ε, 0 < ε → ε < 1 → k.grad ε = n.Kε ε) ∧
    ∀ α ε, 0 ≤ α → 0 < ε → α + ε < 1 → k.gradHolder α ε = n.Kαε α ε
def IsCubeDataOf (E : CubeCovering.CubeData s.data.L s.data.m) : Prop :=
  E.scales = s.data.scales ∧ E.gapExp = s.data.gapExp ∧ E.seq = s.Ω
def CubeGreenConclusions : Prop :=
  ∀ E : CubeCovering.CubeData s.data.L s.data.m, s.IsCubeDataOf E →
    ∀ (Q : CubeCovering.Cube E) (o : Q.Origin),
      ∃ k : PeriodicLattice.DecayConstants, MatchesConstants n k ∧
        (Q.IsInterior →
          Q.meshes.CenteredTwoScaleConclusions (CubeCovering.Cube.coarseSiteSet o) n.cubeRate k) ∧
        ∀ (hQ : Q.IsBoundary) (B : Q.BoundaryData o), Q.BoundaryGreenConclusions hQ B n.cubeRate k
def CubeCoarseLowerBound : Prop :=
  ∀ E : CubeCovering.CubeData s.data.L s.data.m, s.IsCubeDataOf E →
    ∀ (Q : CubeCovering.Cube E) (o : Q.Origin),
      (∀ (hQ : Q.IsInterior) (h : IsUnit (Q.periodicOp o))
        (B : PeriodicExpansions.CenteredCoarseIndex Q.meshes (CubeCovering.Cube.coarseSiteSet o) → ℝ),
        n.coarseLowerBound * PeriodicExpansions.centeredInner Q.meshes _ B B ≤
          PeriodicExpansions.centeredInner Q.meshes _ B
            (PeriodicExpansions.centeredCompress Q.meshes _ (Q.periodicGreen hQ o h) B)) ∧
      ∀ (hQ : Q.IsBoundary) (Bc : Q.BoundaryData o) (A : DirichletLaplacian.supportedForms Bc.links),
        n.coarseLowerBound * ‖(A : PeriodicLattice.OneForm 4 E.unitMeshOf)‖ ^ 2 ≤
          inner ℝ (A : PeriodicLattice.OneForm 4 E.unitMeshOf) (Q.boundaryGreen hQ o Bc A)
def LocalCoarseLowerBound : Prop :=
  ∀ E : GeneralTorus.CubeGaugeSetting, s.IsGaugeSetting E.toGaugeSetting → ∀ Q ∈ E.chain.allCubes,
    ∀ B : (E.localSetting Q).CoarseField,
      (∀ c : (E.localSetting Q).CoarseBond,
        GeneralTorus.GaugeSetting.coarseAnchor c ∉ GeneralTorus.ScaleData.cubeSet Q → B c = 0) →
      n.coarseLowerBound * ∑ᶠ c : (E.localSetting Q).CoarseBond,
          GeneralTorus.GaugeSetting.coarseSpacing c ^ (4 + 2) * |B c| ^ 2 ≤
        (E.localSetting Q).coarseInner B ((E.localSetting Q).coarseGreen B)
structure OperatorBounds : Prop where
  zero_isUnit : IsUnit (s.data.unitSpacingParameters.massiveZeroOperator s.Ω)
  zeroSq_isUnit : IsUnit (s.data.unitSpacingParameters.averagedZeroGreenSq s.Ω)
  one_isUnit : IsUnit (s.data.unitSpacingParameters.massiveOneOperator s.Ω s.frame)
  avg_isUnit : IsUnit (s.data.unitSpacingParameters.averagedOneGreen s.Ω s.frame)
  zero_green : ∀ y y' : s.data.Apex s.Ω, ClassData.ZeroGreenBounds n y y'
  walk : s.WalkExpansionHolds n
  avgSq_inverse : s.AvgSqInverseHolds
  avgSq_inverse_kernel : ∀ y y' : s.data.Apex s.Ω,
    |ClassData.apexKernel (Ring.inverse (s.data.unitSpacingParameters.averagedZeroGreenSq s.Ω)) y y'| ≤
      n.K * y.mesh ^ (-4 : ℤ) * ClassData.expDecay (n.avgSqRate / 2) y y'
  trees : ∀ k, k < s.data.cutoff →
    ∀ [BlockSpin.PeriodsMultipleOfBlock s.data.centeredBlockParams (s.data.levelPeriods k)],
      s.data.TreeLowerBoundAt s.Ω k
  cubeGreens : s.CubeGreenConclusions n
  one_point : ∀ y y' : s.data.Apex s.Ω, ClassData.OneGreenPointBounds n s.frame y y'
  one_holder : ∀ y y' : s.data.Apex s.Ω, ClassData.OneGreenHolderBounds n s.frame y y'
  one_div : ∀ y y' : s.data.Apex s.Ω, ClassData.OneGreenDivBounds n s.frame y y'
  one_l2 : ∀ y y' : s.data.Apex s.Ω, ClassData.OneGreenL2Bounds n s.frame y y'
  one_expansion : ∀ 𝒮, s.IsNestedRegions 𝒮 → OneGreenExpansion 𝒮 s.data.blockSize
  coarse_inverse : ∀ E : GeneralTorus.CubeGaugeSetting, s.IsGaugeSetting E.toGaugeSetting →
    CoarseInverseExpansion E
  coarse_inverse_kernel : ∀ c c' : s.data.CoarseSeriesExpansion s.Ω s.frame,
    |ClassData.coarseKernel
        (Ring.inverse (s.data.unitSpacingParameters.averagedOneGreen s.Ω s.frame)) c c'| ≤
      n.K * ClassData.coarseMesh c ^ (-2 : ℤ) *
        ClassData.pointDecay s.Ω (n.coarseRate / 2) (ClassData.coarseFoot c) (ClassData.coarseFoot c')
  ext : ∀ (y : s.data.Apex s.Ω) (c : s.data.CoarseSeriesExpansion s.Ω s.frame), ClassData.ExtBounds n y c
  coarse_lower : ClassData.AvgOneGreenLowerBound s.Ω s.frame n
  cube_coarse_lower : s.CubeCoarseLowerBound n
  local_coarse_lower : s.LocalCoarseLowerBound n
  parametrized : s.data.t < s.data.cutoff →
    ∀ [BlockSpin.PeriodsMultipleOfBlock s.data.centeredBlockParams (s.data.levelPeriods s.data.t)],
      ClassData.ParametrizedLowerBound s.Ω s.frame n
end OperatorSetting
end SeparatedClasses
end
end YangMills.Construction

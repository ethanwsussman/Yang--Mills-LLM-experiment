import YangMills.Construction.Torus.OperatorsOfTheSequence
import YangMills.Construction.Weighted.GivenChain
import YangMills.Construction.Weighted.LayerOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
def matProd {ι : Type*} (M M' : ι → ι → ℝ) : ι → ι → ℝ :=
  fun i k => ∑ᶠ j, M i j * M' j k
def l2OpNorm {ι : Type*} (M : ι → ι → ℝ) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ u : ι → ℝ,
    Real.sqrt (∑ᶠ i, (∑ᶠ j, M i j * u j) ^ 2) ≤ C * Real.sqrt (∑ᶠ i, u i ^ 2)}
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def layerOpNorm (K : B.LayerOp) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ w, B.layerSpaceNorm (K w) ≤ C * B.layerSpaceNorm w}
def mulOp (m : ↥B.allSites → ℝ) : B.LayerOp where
  toFun w := fun y => m y * w y
  map_add' w w' := by
    ext y
    simp [mul_add]
  map_smul' c w := by
    ext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
open Classical in
def extendByZero (X : Set ↥B.allSites) (M : ↥X → ↥X → ℝ) : B.LayerMat :=
  fun y y' => if h : y ∈ X ∧ y' ∈ X then M ⟨y, h.1⟩ ⟨y', h.2⟩ else 0
def AvgRelations : Prop :=
  (∀ (f : ↥B.bareSpace) (w : B.LayerFn),
    B.layerInner (B.avgOp f) w = B.bareInner f (B.avgOpAdjoint w)) ∧
  (∀ (w : B.LayerFn), ∀ x ∈ D.bareSites (B.stage 0),
    (B.avgOpAdjoint w : D.BareSite → ℝ) x = B.layerEval w (B.blockCenter x)) ∧
  B.avgOp ∘ₗ B.avgOpAdjoint = LinearMap.id ∧
  (∀ y : ↥B.allSites, B.bareSpaceNorm (B.blockIndicator y) ^ 2 = B.siteScale y ^ 4) ∧
  (∀ (f : ↥B.bareSpace) (y : ↥B.allSites),
    |B.avgOp f y| ≤
      B.siteScale y ^ (-2 : ℤ) * TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ)) ∧
  ∀ (f : ↥B.bareSpace) (y : ↥B.allSites),
    TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ) ^ 2 =
      TorusData.siteNorm (B.block y) (fun x => (f : D.BareSite → ℝ) x - B.avgOp f y) ^ 2 +
        B.siteScale y ^ 4 * B.avgOp f y ^ 2
def WeightedAvgForm : Prop :=
  (∀ f f' : ↥B.bareSpace,
    B.bareInner f' (B.weightedAvg f) =
      ∑ᶠ y : ↥B.allSites, avgWeight D.L (B.level y) * B.siteScale y ^ 2 *
        (B.avgOp f' y * B.avgOp f y)) ∧
  ∀ f g : ↥B.bareSpace,
    B.bareInner (B.weightedAvg f) g = B.bareInner f (B.weightedAvg g)
def BasisRelations : Prop :=
  (∀ y : ↥B.allSites, B.layerInner (B.basisVec y) (B.basisVec y) = 1) ∧
  (∀ y y' : ↥B.allSites, y ≠ y' →
    B.layerInner (B.basisVec y) (B.basisVec y') = 0) ∧
  Submodule.span ℝ (range B.basisVec) = ⊤ ∧
  (∀ (K : B.LayerOp) (y y' : ↥B.allSites),
    B.matrixOf K y y' =
      B.siteScale y ^ 2 * B.kernel K y y' * B.siteScale y' ^ (-2 : ℤ)) ∧
  ∀ y : ↥B.allSites,
    (B.avgOpAdjoint (B.basisVec y) : D.BareSite → ℝ) =
      B.siteScale y ^ (-2 : ℤ) • B.blockIndicator y
def OpNormBounds : Prop :=
  ∀ (K K' : B.LayerOp) (δ : ℝ), 0 ≤ δ →
    B.expWeightedOpNorm δ (K ∘ₗ K') ≤ B.expWeightedOpNorm δ K * B.expWeightedOpNorm δ K' ∧
    (∀ y y' : ↥B.allSites,
      |B.matrixOf K y y'| ≤
        B.expWeightedOpNorm δ K * Real.exp (-δ * B.weightedDistance y y')) ∧
    l2OpNorm (B.matrixOf K) = B.layerOpNorm K ∧
    l2OpNorm (B.matrixOf K) ≤ B.expWeightedOpNorm 0 K ∧
    B.expWeightedOpNorm 0 K ≤ B.expWeightedOpNorm δ K
def MatNormBounds : Prop :=
  ∀ (M M' : B.LayerMat) (δ : ℝ), 0 ≤ δ →
    B.expWeightedMatrixNorm δ (matProd M M') ≤
      B.expWeightedMatrixNorm δ M * B.expWeightedMatrixNorm δ M' ∧
    (∀ y y' : ↥B.allSites,
      |M y y'| ≤ B.expWeightedMatrixNorm δ M * Real.exp (-δ * B.weightedDistance y y')) ∧
    l2OpNorm M ≤ B.expWeightedMatrixNorm 0 M ∧
    B.expWeightedMatrixNorm 0 M ≤ B.expWeightedMatrixNorm δ M
def SubsetMatNormBounds : Prop :=
  ∀ (X : Set ↥B.allSites) (M M' : ↥X → ↥X → ℝ) (δ : ℝ), 0 ≤ δ →
    B.expWeightedMatrixNorm δ (B.extendByZero X (matProd M M')) ≤
      B.expWeightedMatrixNorm δ (B.extendByZero X M) *
        B.expWeightedMatrixNorm δ (B.extendByZero X M') ∧
    (∀ y y' : ↥X,
      |M y y'| ≤ B.expWeightedMatrixNorm δ (B.extendByZero X M) *
        Real.exp (-δ * B.weightedDistance (y : ↥B.allSites) (y' : ↥B.allSites))) ∧
    l2OpNorm M ≤ B.expWeightedMatrixNorm 0 (B.extendByZero X M) ∧
    B.expWeightedMatrixNorm 0 (B.extendByZero X M) ≤
      B.expWeightedMatrixNorm δ (B.extendByZero X M)
def MulOpRelations : Prop :=
  ∀ m : ↥B.allSites → ℝ,
    (∀ y y' : ↥B.allSites, y ≠ y' → B.matrixOf (B.mulOp m) y y' = 0) ∧
    B.mulOp m ∘ₗ B.scaleOnLayer = B.scaleOnLayer ∘ₗ B.mulOp m
end SeparatedChain
def AvgAndMatrixFacts : Prop :=
  ∀ G : GivenChain,
    G.chain.AvgRelations ∧ G.chain.WeightedAvgForm ∧
      G.chain.BasisRelations ∧ G.chain.OpNormBounds ∧
      G.chain.MatNormBounds ∧ G.chain.SubsetMatNormBounds ∧
      G.chain.MulOpRelations
end YangMills.Construction.Weighted
end

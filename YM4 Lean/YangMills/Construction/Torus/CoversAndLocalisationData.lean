import YangMills.Construction.Torus.AdmissiblePairs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
namespace TorusData
variable (D : TorusData)
def blockSide (j : ℕ) : ℝ := (D.blockNumber : ℝ) * D.scale j
def cubeVertices (σ : ℝ) (y : D.Space) : Set D.Space :=
  {z | ∃ ε : Fin 4 → ℝ, (∀ μ, ε μ = 1 ∨ ε μ = -1) ∧
    z = y + TorusMetric.torusProj D.side fun μ => ε μ * (σ / 2)}
def levelVertices (j : ℕ) : Set D.Space :=
  ⋃ y ∈ D.latticeAt (D.blockSide j), D.cubeVertices (D.blockSide j) y
structure CoverPiece where
  index : ℕ
  index_le : index ≤ D.top
  center : D.Space
  center_mem : center ∈ D.levelVertices index
  cutoff : D.Space → ℝ
  cutoff_mem : ∀ x, cutoff x ∈ Icc (0 : ℝ) 1
namespace CoverPiece
variable {D} (p : D.CoverPiece)
def dilate (r : ℝ) : Set D.Space :=
  {x | TorusMetric.torusSupNorm (x - p.center) ≤ r * D.blockSide p.index}
def unitBox : Set D.Space := p.dilate 1
def doubledBox : Set D.Space := p.dilate 2
end CoverPiece
end TorusData
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def HasBoxInLayer (p : D.CoverPiece) : Prop :=
  ∃ y ∈ D.latticeAt (D.blockSide p.index),
    p.center ∈ D.cubeVertices (D.blockSide p.index) y ∧
      D.cubeAround (D.blockSide p.index) y ⊆ B.layer p.index
structure IsCover {ι : Type*} (c : ℝ) (P : ι → D.CoverPiece) : Prop where
  one_le : 1 ≤ c
  finite : Finite ι
  box_in_layer : ∀ i, B.HasBoxInLayer (P i)
  cutoff_eq_zero : ∀ i x, x ∉ (P i).dilate (2 / 3) → (P i).cutoff x = 0
  sum_sq : ∀ x ∈ B.stage 0, ∑ᶠ i, (P i).cutoff x ^ 2 = 1
  lipschitz : ∀ i x x', |(P i).cutoff x - (P i).cutoff x'| ≤
    c * (D.blockNumber : ℝ)⁻¹ * B.weightedDistance x x'
  overlap : ∀ x ∈ B.stage 0, ({i | (P i).cutoff x ≠ 0}.ncard : ℝ) ≤ c
def pieceSites (p : D.CoverPiece) : Set D.Space := B.allSites ∩ p.unitBox
def mulOnLayer (g : D.Space → ℝ) : Module.End ℝ B.LayerFn where
  toFun w := fun y => g y * w y
  map_add' w w' := by
    ext y
    simp [mul_add]
  map_smul' c w := by
    ext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def pieceIndicatorOp (p : D.CoverPiece) : Module.End ℝ B.LayerFn :=
  B.mulOnLayer ((B.pieceSites p).indicator 1)
def pieceCutoffOp (p : D.CoverPiece) : Module.End ℝ B.LayerFn :=
  B.mulOnLayer p.cutoff
structure Localization {ι : Type*} (P : ι → D.CoverPiece) where
  region : ι → Set D.Space
  bonds : ι → Set D.Bond
  admissible : ∀ i, B.IsAdmissiblePair (region i) (bonds i)
  siteCube_subset : ∀ i, ∀ y ∈ B.allSites ∩ (P i).doubledBox, B.siteCube y ⊆ region i
  bondsAtSite_subset : ∀ i, ∀ x ∈ D.bareSites (B.stage 0 ∩ (P i).dilate (5 / 3)),
    TorusData.bondsAtSite x ⊆ bonds i
namespace Localization
variable {B} {ι : Type*} {P : ι → D.CoverPiece} (δ : B.Localization P) (i : ι)
def localAvgGreenSq : Module.End ℝ ↥(B.layerSpaceOn (δ.region i)) :=
  B.admissibleAvgGreenSq (δ.region i) (δ.bonds i)
def localScaledGreenSq : Module.End ℝ ↥(B.layerSpaceOn (δ.region i)) :=
  Ring.inverse (B.scaleOnLayerOn (δ.region i)) ^ 2 * δ.localAvgGreenSq i *
    Ring.inverse (B.scaleOnLayerOn (δ.region i)) ^ 2
end Localization
end SeparatedChain
end YangMills.Construction.Weighted

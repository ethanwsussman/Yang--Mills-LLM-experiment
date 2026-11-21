import YangMills.Construction.Torus.CoversAndLocalisationData
import YangMills.Construction.Weighted.CoverConstant
import YangMills.Construction.Weighted.GivenChain
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def BlockConditionsOn (j : ℕ) (X : Set D.Space) : Prop :=
  ∀ x ∈ D.bareSites (B.stage 0),
    ((x : D.Space) ∈ X ↔ B.blockCenter x ∈ X) ∧
      (B.blockCenter x ∈ X ↔ B.siteCube (B.blockCenter x) ⊆ X) ∧
        ((x : D.Space) ∈ X → B.bareLevel x ≤ j + 1)
def PieceAvoidsStageTwoAbove (q : D.CoverPiece) : Prop :=
  q.doubledBox ∩ B.stage (q.index + 2) = ∅ ∧
    B.BlockConditionsOn q.index q.doubledBox ∧ B.BlockConditionsOn q.index q.unitBox
def WeightedDistanceBoundFromPiece (q : D.CoverPiece) : Prop :=
  ∀ r r' : ℝ, 0 < r → r < r' → r' ≤ 2 → ∀ x x' : D.Space, x ∈ q.dilate r →
    r' * D.blockSide q.index ≤ TorusMetric.torusSupNorm (x' - q.center) →
      (r' - r) * (D.blockNumber : ℝ) / (D.L : ℝ) ≤ B.weightedDistance x x'
def CutoffVanishesOffLayers (q : D.CoverPiece) : Prop :=
  (∀ x ∈ B.stage (q.index + 2), q.cutoff x = 0) ∧
    (1 ≤ q.index → ∀ x ∈ D.closedComplement (B.stage q.index), q.cutoff x = 0)
def doubledBoxBlocks (q : D.CoverPiece) : Set D.Space :=
  ⋃ y ∈ B.allSites ∩ q.doubledBox, B.siteCube y
def IsLocalizationPair {ι : Type*} (P : ι → D.CoverPiece) (W : ι → Set D.Space)
    (b : ι → Set D.Bond) : Prop :=
  ∃ δ : B.Localization P, δ.region = W ∧ δ.bonds = b
def ThreeLocalizations {ι : Type*} (P : ι → D.CoverPiece) : Prop :=
  B.IsLocalizationPair P (fun _ => B.stage 0)
      (fun _ => TorusData.bondsMeeting (D.bareSites (B.stage 0))) ∧
    B.IsLocalizationPair P (fun i => B.doubledBoxBlocks (P i))
      (fun i => TorusData.bondsMeeting (D.bareSites (B.doubledBoxBlocks (P i)))) ∧
    B.IsLocalizationPair P (fun i => B.doubledBoxBlocks (P i))
      (fun i => TorusData.bondsWithin (D.bareSites (B.doubledBoxBlocks (P i))) ∪
        (TorusData.bondsMeeting (D.bareSites (B.doubledBoxBlocks (P i))) \
          TorusData.bondsWithin (D.bareSites (B.stage 0))))
end SeparatedChain
def CoverGeometry : Prop :=
  ∀ G : GivenChain,
    (∀ (ι : Type) (c : ℝ) (P : ι → G.data.CoverPiece), G.chain.IsCover c P →
      ∀ i, G.chain.PieceAvoidsStageTwoAbove (P i)) ∧
    (∀ (ι : Type) (c : ℝ) (P : ι → G.data.CoverPiece), G.chain.IsCover c P →
      ∀ i, G.chain.WeightedDistanceBoundFromPiece (P i)) ∧
    (∃ (ι : Type) (P : ι → G.data.CoverPiece),
      G.chain.IsCover (coverConst 4 G.data.L) P ∧
        ∀ i, G.chain.CutoffVanishesOffLayers (P i)) ∧
    (∀ (ι : Type) (c : ℝ) (P : ι → G.data.CoverPiece), G.chain.IsCover c P →
      G.chain.ThreeLocalizations P)
end YangMills.Construction.Weighted

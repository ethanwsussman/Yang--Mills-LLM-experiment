import YangMills.Construction.HoleBesideASecondHole.OneTorusAtTwoFrames
import YangMills.Construction.HoleBesideASecondHole.TheInequalityOfAHoleOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusFrames
open BlockAverages TorusFields TorusLumps LumpContours FrameTransfer StepCosts HoleOnTori
def torusAtFrameStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (n : ℕ) [NeZero n] (F : BlockFrame), F.blockSide = L → (∀ i, F.extent i = n) →
    (∀ S : Finset (TorusSite n), sitesOfTorus F F.depth (sitesInBlocks L S) = cutBelow F.depth (cellsOfSites F S)) ∧
    (∀ y z : TorusSite n,
      cellSupDist (torusSiteInFrame F F.top y) (torusSiteInFrame F F.top z) = supDist y z) ∧
    (∀ x : TorusSite (n * L),
      enclosingCell (torusSiteInFrame F F.depth x) = torusSiteInFrame F F.top (parentBlock L x)) ∧
    (∀ (m : ℕ) (X : Finset (TorusSite n)), cellsOfSites F (thickening m X) = thicken m (cellsOfSites F X)) ∧
    (∀ (m : ℕ) (X : Finset (TorusSite (n * L))),
      sitesOfTorus F F.depth (thickening m X) = thicken m (sitesOfTorus F F.depth X)) ∧
    (∀ X : Finset (TorusSite n),
      cutBonds (cellsOfSites F X) = (bondsWithin X).image fun c => (torusSiteInFrame F F.top c.1, c.2)) ∧
    (∀ X : Finset (TorusSite (n * L)),
      cutBonds (sitesOfTorus F F.depth X) = (bondsWithin X).image fun c => (torusSiteInFrame F F.depth c.1, c.2)) ∧
    cellsOfSites F (Finset.univ : Finset (TorusSite n)) = torusCells F ∧
    levelSites F F.top = cellsOfSites F (Finset.univ : Finset (TorusSite n)) ∧
    levelSites F F.depth = sitesOfTorus F F.depth (Finset.univ : Finset (TorusSite (n * L))) ∧
    (∀ (s : ℝ) (V : TorusField n),
      BlockAverages.IsCold (torusCells F) F.top s (readAtLevel F F.top V) ↔ TorusFields.IsCold s V) ∧
    ∀ ℓ : StepParameters, ℓ.side = L → L ∣ n →
      (∀ l : Finset (TorusSite n), HoleOnTori.IsTopLump ℓ l ↔ LumpContours.IsLump ℓ.grid (cellsOfSites F l)) ∧
      ∀ (S₀ : Finset (TorusSite n)) (V : TorusField n),
        hotLumps ℓ.grid ℓ.threshold (cellsOfSites F S₀) (readAtLevel F F.top V) =
          (topHotLumps ℓ S₀ V).image (cellsOfSites F)
end YangMills.Construction.TorusFrames
end

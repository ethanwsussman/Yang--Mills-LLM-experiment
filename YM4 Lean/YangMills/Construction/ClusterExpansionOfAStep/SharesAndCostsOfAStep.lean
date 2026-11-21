import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.StepCosts
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open YangMills.Construction.ColdStepAtMirrorFrames
variable {n : ℕ}
def torusSiteInFrame (F : BlockFrame) (j : ℕ) (x : TorusSite n) : F.Site j :=
  siteOfCoords j fun i => ((x i).cast : ℤ)
def levelShare [NeZero n] (a : ℝ) (L : ℕ) :
    ℕ → Finset (TorusSite n) → TorusSite n → TorusField n → ℝ
  | 0, S, y, W => ∑ p ∈ plaquettesIn S,
      (((plaquetteVertices p.1 p.2.1 p.2.2).count y : ℕ) : ℝ) / 4 * plaquetteEnergy W p.1 p.2.1 p.2.2
  | t + 1, S, y, W =>
    minimalCellShare a (cellsOfSites (torusFrame L t n) S) (torusSiteInFrame (torusFrame L t n) (t + 1) y)
      (readAtLevel (torusFrame L t n) (t + 1) W)
abbrev BaseChoice (L n : ℕ) : Type := (stepBlockFrame L n).Cell → (stepBlockFrame L n).Site 0
def stepHotLumps (ℓ : StepParameters) (W : TorusField (n * ℓ.side)) :
    Finset (Finset ((stepBlockFrame ℓ.side n).Site 0)) :=
  hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0)
    (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
def bondFit (ℓ : StepParameters) (W : TorusField (n * ℓ.side)) (V : TorusField n)
    (b : BaseChoice ℓ.side n) (c : TorusBond n) : ℝ :=
  contourFit ℓ.baseDepth (stepHotLumps ℓ W) b (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
    (readAtLevel (stepBlockFrame ℓ.side n) 1 V)
    (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)
def meanNorm (ℓ : StepParameters) (W : TorusField (n * ℓ.side)) (b : BaseChoice ℓ.side n)
    (c : TorusBond n) : ℝ :=
  ‖contourMean ℓ.baseDepth (stepHotLumps ℓ W) b (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
    (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)‖
def chartCoord (ℓ : StepParameters) (V : TorusField n) (W : TorusField (n * ℓ.side))
    (b : TorusBond (n * ℓ.side)) : imaginaryQuaternions :=
  bondCoordinate 1 (readAtLevel (stepBlockFrame ℓ.side n) 1 V) (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
    (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1, b.2)
def frameCoord (ℓ : StepParameters) (ρA : ℝ) (t m₀ : ℕ) (V : TorusField n)
    (b : TorusBond (n * ℓ.side)) : imaginaryQuaternions :=
  bondFrameCoord ℓ.coupling ρA m₀
    (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2)
    (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)
open Classical in
def chartBonds (L : ℕ) (n : ℕ) [NeZero n] [NeZero L] : Finset (TorusBond (n * L)) :=
  Finset.univ.filter fun b =>
    ¬ IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 b.1, b.2)
def blockCost [NeZero n] (ℓ : StepParameters) (t : ℕ) (W : TorusField (n * ℓ.side)) (V : TorusField n)
    (b : BaseChoice ℓ.side n) (Y : TorusSite n) : ℝ :=
  ∑ y ∈ sitesInBlocks ℓ.side {Y},
      levelShare ℓ.coupling ℓ.side t (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) y W +
    ℓ.coupling / 2 * ∑ i : Fin 4, (bondFit ℓ W V b (Y, i) + bondFit ℓ W V b (Y - TorusFields.unitStep n i, i))
end YangMills.Construction.StepCosts
end

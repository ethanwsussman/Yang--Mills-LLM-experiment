import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import YangMills.Construction.HoleBesideASecondHole.TheInequalityOfAHoleAsRead
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours HoleBounds TorusFields TorusLumps StepCosts
namespace HoleOnTori
variable {n : ℕ}
def stepHotLumps (ℓ : StepParameters) (X : Finset (TorusSite (n * ℓ.side))) (W : TorusField (n * ℓ.side)) :
    Finset (Finset ((stepBlockFrame ℓ.side n).Site 0)) :=
  hotLumps ℓ.grid ℓ.threshold (X.image (torusSiteInFrame (stepBlockFrame ℓ.side n) 0))
    (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
def topHotLumps (ℓ : StepParameters) (S₀ : Finset (TorusSite n)) (V : TorusField n) :
    Finset (Finset (TorusSite n)) :=
  open Classical in
  (hotLumps ℓ.grid ℓ.threshold (S₀.image (torusSiteInFrame (stepBlockFrame ℓ.side (n / ℓ.side)) 0))
    (readAtLevel (stepBlockFrame ℓ.side (n / ℓ.side)) 0 V)).image fun l => l.image (toTorusSite n)
def IsTopLump (ℓ : StepParameters) (l : Finset (TorusSite n)) : Prop :=
  open Classical in
  ∃ x : (stepBlockFrame ℓ.side (n / ℓ.side)).Site 0, l = (lumpOf ℓ.grid x).image (toTorusSite n)
def bondFit (ℓ : StepParameters) (h : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0)))
    (W : TorusField (n * ℓ.side)) (V : TorusField n) (b : BaseChoice ℓ.side n) (c : TorusBond n) : ℝ :=
  contourFit ℓ.baseDepth h b (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
    (readAtLevel (stepBlockFrame ℓ.side n) 1 V)
    (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)
def stepLumpSites (ℓ : StepParameters) (h : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0))) :
    Finset (TorusSite (n * ℓ.side)) :=
  open Classical in h.biUnion fun l => l.image (toTorusSite (n * ℓ.side))
open Classical in
def bondsWithin [NeZero n] (X : Finset (TorusSite n)) : Finset (TorusBond n) :=
  Finset.univ.filter fun c => c.1 ∈ X ∧ c.1 + TorusFields.unitStep n c.2 ∈ X
open Classical in
def chartDeviationSites [NeZero n] (ℓ : StepParameters) (r : ℝ) (S : Finset (TorusSite n)) (V : TorusField n)
    (W Wl : TorusField (n * ℓ.side)) : Finset (TorusSite n) :=
  S.filter fun y => ∃ c ∈ bondsWithin (sitesInBlocks ℓ.side S), parentBlock ℓ.side c.1 = y ∧
    r ≤ ‖(chartCoord ℓ V W c : ℍ[ℝ]) - chartCoord ℓ V Wl c‖
open Classical in
def HoleSavingOnTorus [NeZero n] (ℓ : StepParameters) (cE : ℝ) (t : ℕ) (S₀ S : Finset (TorusSite n)) (m : ℕ)
    (V : TorusField n) (W Wl : TorusField (n * ℓ.side)) (b : BaseChoice ℓ.side n) : Prop :=
  actionAtLevel ℓ.coupling ℓ.side (t + 1) S V + 6 * ℓ.κ * ℓ.threshold ^ 2 * m +
      (ℓ.κ / 4) * ℓ.threshold ^ 2 * (stepHotLumps ℓ (sitesInBlocks ℓ.side S₀) W).card +
      cE * (chartDeviationSites ℓ (ℓ.threshold / 128) S V W Wl).card ≤
    actionAtLevel ℓ.coupling ℓ.side t (sitesInBlocks ℓ.side S₀ \
        thickening lumpRange (stepLumpSites ℓ (stepHotLumps ℓ (sitesInBlocks ℓ.side S₀) W))) W +
      ℓ.κ * ℓ.threshold ^ 2 * (stepHotLumps ℓ (sitesInBlocks ℓ.side S₀) W).card +
      ℓ.coupling * ∑ c ∈ bondsWithin S₀, bondFit ℓ (stepHotLumps ℓ (sitesInBlocks ℓ.side S₀) W) W V b c
open Classical in
def awayFromLumps [NeZero n] (H : Finset (Finset (TorusSite n))) : Finset (TorusSite n) :=
  Finset.univ \ thickening lumpRange (H.biUnion id)
open Classical in
structure HoleSavingBounds (ℓ : StepParameters) (cE : ℝ) : Prop where
  holed : ∀ (t n : ℕ) [NeZero n], ℓ.side ∣ n → 4096 ≤ n → ∀ H : Finset (Finset (TorusSite n)),
    (∀ l ∈ H, IsTopLump ℓ l) → ∀ (V : TorusField n) (W Wl : TorusField (n * ℓ.side)) (b : BaseChoice ℓ.side n),
      (∀ y ∈ thickening lumpRange ((topHotLumps ℓ (awayFromLumps H) V).biUnion id),
        ∀ z ∈ thickening lumpRange (H.biUnion id), 2 * wallMargin ≤ supDist y z) →
      IsMinimizingField ℓ.coupling
        (cellsOfSites (torusFrame ℓ.side t n) (awayFromLumps H \
          thickening lumpRange ((topHotLumps ℓ (awayFromLumps H) V).biUnion id)))
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth Wl) →
      (∀ c ∈ bondsWithin (sitesInBlocks ℓ.side (awayFromLumps H \
          thickening lumpRange ((topHotLumps ℓ (awayFromLumps H) V).biUnion id))),
        ∀ z ∈ thickening lumpRange (H.biUnion id), supDist (parentBlock ℓ.side c.1) z ≤ wallMargin →
        W c.1 c.2 = Wl c.1 c.2) →
      IsBaseChoice ℓ.baseDepth (stepHotLumps ℓ (sitesInBlocks ℓ.side (awayFromLumps H)) W) b →
      HoleSavingOnTorus ℓ cE t (awayFromLumps H)
        (awayFromLumps H \ thickening lumpRange ((topHotLumps ℓ (awayFromLumps H) V).biUnion id))
        (topHotLumps ℓ (awayFromLumps H) V).card V W Wl b
  cold : ∀ (t n : ℕ) [NeZero n], 4096 ≤ n → ∀ (V : TorusField n) (W Wl : TorusField (n * ℓ.side))
      (b : BaseChoice ℓ.side n),
      IsCold (9 / 8 * ℓ.threshold) V →
      IsMinimizingField ℓ.coupling (cellsOfSites (torusFrame ℓ.side t n) (Finset.univ : Finset (TorusSite n)))
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth Wl) →
      IsBaseChoice ℓ.baseDepth (stepHotLumps ℓ (sitesInBlocks ℓ.side Finset.univ) W) b →
      HoleSavingOnTorus ℓ cE t Finset.univ Finset.univ 0 V W Wl b
end HoleOnTori
end YangMills.Construction
end

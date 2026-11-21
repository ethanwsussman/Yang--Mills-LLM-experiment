import YangMills.Construction.Lattice.BlockAveraging
import YangMills.Construction.Lattice.BondsWithinSiteSets
import YangMills.Construction.Lattice.CoordinateCombs
import YangMills.Construction.Lattice.SiteBoxes
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ} {j j' : ℤ}
abbrev SignedFrame : Type := Equiv.Perm (Fin 4) × (Fin 4 → ℤˣ)
def signedFrameCount : ℕ := 2 ^ 4 * Nat.factorial 4
namespace SignedFrame
def actOnVector (r : SignedFrame) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun μ => ((r.2 μ : ℤ) : ℝ) * v (r.1 μ)
def torusEquiv (L m : ℕ) (r : SignedFrame) : FourTorus L m ≃ FourTorus L m :=
  signedCoordinatePerm L m r.1 r.2
def preimageSite (r : SignedFrame) (y : Site L m j) : Site L m j :=
  Classical.epsilon fun x : Site L m j => (x : FourTorus L m) = (torusEquiv L m r).symm y
def preimageSites (r : SignedFrame) (P : Set (Site L m j)) : Set (Site L m j) :=
  {x | ∃ y ∈ P, (x : FourTorus L m) = (torusEquiv L m r).symm y}
def preimageSet (r : SignedFrame) (X : Set (FourTorus L m)) : Set (FourTorus L m) :=
  (torusEquiv L m r).symm '' X
def mapBond (r : SignedFrame) (b : Bond L m j) : Bond L m j :=
  bondPreimage (torusEquiv L m r).symm b
end SignedFrame
def combToBlockSite (y : Site L m j) (x : Site L m j') : List (Bond L m j') :=
  coordinateComb (y.toSublattice j') x
def rotatedComb (r : SignedFrame) (y x : Site L m j) : List (Bond L m j) :=
  (coordinateComb (r.preimageSite y) (r.preimageSite x)).map r.mapBond
def HasChartFaces (j : ℤ) (P : Set (Site L m j)) (lo hi : Fin 4 → ℝ) : Prop :=
  ∃ (i : ℤ) (X : Set (FourTorus L m)) (c : TorusBox.BoxChart (torusSide L m) X), -(m : ℤ) ≤ i ∧ i ≤ j ∧
    IsPartitionBox i X ∧ (∀ μ, c.upper μ - c.lower μ < torusSide L m / 2) ∧ P = sitesIn X ∧
    c.lower = lo ∧ c.upper = hi
theorem isSiteBox_iff_hasChartFaces {P : Set (Site L m j)} :
    IsSiteBox j P ↔ ∃ lo hi, HasChartFaces j P lo hi := by
  constructor
  · rintro ⟨i, X, hi, hij, hX, ⟨c, hc⟩, hP⟩
    exact ⟨c.lower, c.upper, i, X, c, hi, hij, hX, hc, hP, rfl, rfl⟩
  · rintro ⟨_, _, i, X, c, hi, hij, hX, hc, hP, _, _⟩
    exact ⟨i, X, hi, hij, hX, ⟨c, hc⟩, hP⟩
def chartCoords (lo hi : Fin 4 → ℝ) (p : FourTorus L m) : Fin 4 → ℝ :=
  Classical.epsilon fun v => v ∈ TorusBox.boxOfIntervals lo hi ∧ torusProj (torusSide L m) v = p
def siteOfCoords (j : ℤ) (v : Fin 4 → ℝ) : Site L m j :=
  Classical.epsilon fun x : Site L m j => (x : FourTorus L m) = torusProj (torusSide L m) v
def cornerSite (j : ℤ) (lo : Fin 4 → ℝ) : Site L m j :=
  siteOfCoords j fun μ => lo μ + meshSize L j / 2
def boxBasePoint (j : ℤ) (P : Set (Site L m j)) : Site L m j :=
  Classical.epsilon fun y => ∃ lo hi, HasChartFaces j P lo hi ∧ y = cornerSite j lo
def axialBoxTree (j : ℤ) (P : Set (Site L m j)) : Set (Bond L m j) :=
  {b | ∃ x ∈ P, b ∈ coordinateComb (boxBasePoint j P) x}
def rotatedAxialBoxTree (r : SignedFrame) (j : ℤ) (P : Set (Site L m j)) : Set (Bond L m j) :=
  r.mapBond '' axialBoxTree j (r.preimageSites P)
abbrev IndexedBond (L m : ℕ) : Type := Σ j : ℤ, Bond L m j
def liftTree (j : ℤ) (T : Set (Bond L m j)) : Set (IndexedBond L m) :=
  (fun b => (⟨j, b⟩ : IndexedBond L m)) '' T
def positiveTreeBonds (T : Set (IndexedBond L m)) : Set (IndexedBond L m) :=
  {t | t.2.IsPositivelyOriented ∧ (t ∈ T ∨ (⟨t.1, t.2.opposite⟩ : IndexedBond L m) ∈ T)}
def axialPathThrough : List (Site L m j) → List (Bond L m j)
  | x :: x' :: l => axialPath x x' ++ axialPathThrough (x' :: l)
  | _ => []
def IsShellSetting (j : ℤ) (P₁ P₂ : Set (Site L m j)) (lo hi lo' hi' : Fin 4 → ℝ) (a : ℝ) :
    Prop :=
  HasChartFaces j P₁ lo hi ∧ HasChartFaces j P₂ lo' hi' ∧ P₂ ⊂ P₁ ∧
    (∀ μ, lo μ < lo' μ ∧ lo' μ < hi' μ ∧ hi' μ < hi μ) ∧ lo' 0 < a ∧ a < hi' 0
def shellPath (j : ℤ) (lo hi : Fin 4 → ℝ) (a : ℝ) (x : Site L m j) : List (Bond L m j) :=
  let y : Fin 4 → ℝ := fun μ => lo μ + meshSize L j / 2
  let u : Fin 4 → ℝ := chartCoords lo hi (x : FourTorus L m)
  let far : ℝ := hi 0 - meshSize L j / 2
  if u 0 ≤ a then coordinateComb (cornerSite j lo) x
  else axialPathThrough [cornerSite j lo, siteOfCoords j ![y 0, y 1, y 2, u 3],
    siteOfCoords j ![y 0, y 1, u 2, u 3], siteOfCoords j ![far, y 1, u 2, u 3],
    siteOfCoords j ![far, u 1, u 2, u 3], x]
def shellSpanningTree (j : ℤ) (lo hi : Fin 4 → ℝ) (P₁ P₂ : Set (Site L m j)) (a : ℝ) :
    Set (Bond L m j) :=
  {b | ∃ x ∈ P₁ \ P₂, b ∈ shellPath j lo hi a x}
def boxEntranceBond (j : ℤ) (P : Set (Site L m j)) : Bond L m j :=
  Bond.forwardFrom (boxBasePoint j P - unitStep L m j 0) 0
def rotatedBoxEntranceBond (r : SignedFrame) (j : ℤ) (P : Set (Site L m j)) : Bond L m j :=
  r.mapBond (boxEntranceBond j (r.preimageSites P))
def boxCenter (X : Set (FourTorus L m)) : FourTorus L m :=
  Classical.epsilon fun p => ∃ c : TorusBox.BoxChart (torusSide L m) X,
    p = torusProj (torusSide L m) fun μ => (c.lower μ + c.upper μ) / 2
def chartFacesOf (j : ℤ) (P : Set (Site L m j)) : (Fin 4 → ℝ) × (Fin 4 → ℝ) :=
  Classical.epsilon fun f => HasChartFaces j P f.1 f.2
def nestShellTree (q : ℕ) (P : ℕ → Set (FourTorus L m)) (J : ℕ → ℤ) (i : ℕ) :
    Set (Bond L m (J i)) :=
  let f := chartFacesOf (J i) (sitesIn (P (i - 1)))
  shellSpanningTree (J i) f.1 f.2 (sitesIn (P (i - 1))) (sitesIn (P i))
    (chartCoords f.1 f.2 (boxCenter (P q)) 0)
def nestGaugeTree (q : ℕ) (P : ℕ → Set (FourTorus L m)) (J : ℕ → ℤ) : Set (IndexedBond L m) :=
  {t | (∃ i, 1 ≤ i ∧ i ≤ q ∧ ∃ b ∈ nestShellTree q P J i, t = ⟨J i, b⟩) ∨
    (∃ i, 1 ≤ i ∧ i + 1 ≤ q ∧ t = ⟨J i, boxEntranceBond (J i) (sitesIn (P i))⟩) ∨
    t = ⟨J 1, boxEntranceBond (J 1) (sitesIn (P 0))⟩}
def rotatedNestGaugeTree (r : SignedFrame) (q : ℕ) (P : ℕ → Set (FourTorus L m)) (J : ℕ → ℤ) :
    Set (IndexedBond L m) :=
  (fun t : IndexedBond L m => (⟨t.1, r.mapBond t.2⟩ : IndexedBond L m)) ''
    nestGaugeTree q (fun i => r.preimageSet (P i)) J
def averageOverFrames {τ E : Type*} [AddCommMonoid E] [Module ℝ E] (T : SignedFrame → τ)
    (F : τ → E) : E :=
  ((signedFrameCount : ℝ)⁻¹) • ∑ r : SignedFrame, F (T r)
def blockBonds (j' : ℤ) (P'' : Set (Site L m j)) : Set (Bond L m j') :=
  {b | ∃ y ∈ P'', b.LiesIn (sitesInBlock j' y)}
def BlockAxialData (K k : ℕ) (P'' : Set (SiteAtLevel L m K (k + 1)))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop :=
  k < K ∧ IsGaugeField compactGaugeGroup (blockBonds (levelDepth K k) P'') V ∧
    ∀ y ∈ P'', ∀ x ∈ sitesInBlock (levelDepth K k) y, HasContourMean V y x
def IsBlockAxialGauge (K k : ℕ) (P'' : Set (SiteAtLevel L m K (k + 1)))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop :=
  BlockAxialData K k P'' V ∧
    ∀ y ∈ P'', ∀ x ∈ sitesInBlock (levelDepth K k) y, (x : FourTorus L m) ≠ y →
      meanContourHolonomy V y x = 1
end PeriodicLattice
end YangMills.Construction

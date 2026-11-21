import YangMills.Construction.Lattice.OneStepSchemes
import YangMills.Construction.Lattice.SiteBoxes
import YangMills.Construction.Lattice.SiteCoordinates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j k : ℤ}
abbrev blockAnchor (k : ℤ) (y : Site L m j) : Site L m k := schemeBaseSite .cornered k y
def blockTranslation (L m : ℕ) (k : ℤ) (ν : Fin 4) : Site L m k := (L : ℤ) • unitStep L m k ν
def blockIndexBox (L : ℕ) : Set (Fin 4 → ℤ) :=
  {q | ∀ ν, -centreToFaceSteps L ≤ q ν ∧ q ν ≤ centreToFaceSteps L}
def doubleBlockIndexBox (L : ℕ) (μ : Fin 4) : Set (Fin 4 → ℤ) :=
  {q | -centreToFaceSteps L ≤ q μ ∧ q μ ≤ centreToFaceSteps L + L ∧
    ∀ ν, ν ≠ μ → |q ν| ≤ centreToFaceSteps L}
def IsParametrizedBy (w : Site L m k) (Q : Set (Fin 4 → ℤ)) (R : Set (FourTorus L m)) : Prop :=
  InjOn (offsetSite w) Q ∧
    (fun q => (offsetSite w q : FourTorus L m)) '' Q = R
def BlockCoordinates (k : ℤ) (y : Site L m j) : Prop :=
  IsParametrizedBy (y.toSublattice k) (blockIndexBox L) (unitBlock y) ∧
  (unitBlock y).ncard = L ^ 4 ∧
  (blockAnchor k y : FourTorus L m) ∈ unitBlock y
def DoubleBlockCoordinates (k : ℤ) (c : Bond L m j) (μ : Fin 4) : Prop :=
  c.target.toSublattice k = c.source.toSublattice k + blockTranslation L m k μ ∧
  blockAnchor k c.target = blockAnchor k c.source + blockTranslation L m k μ ∧
  unitBlock c.target = (fun z => z + (blockTranslation L m k μ : FourTorus L m)) '' unitBlock c.source ∧
  (fun x => x + blockTranslation L m k μ) '' sitesInBlock k c.source = sitesInBlock k c.target ∧
  (∀ x ∈ sitesInBlock k c.source, shiftAcross c x = x + blockTranslation L m k μ) ∧
  IsParametrizedBy (c.source.toSublattice k) (doubleBlockIndexBox L μ) (bondDoubleBlock c)
def IsMonotoneSteps (s : List (Fin 4 → ℤ)) : Prop :=
  (∀ t ∈ s, ∃ ν : Fin 4, t = Pi.single ν 1 ∨ t = -Pi.single ν 1) ∧
  ∀ ν : Fin 4, ¬((Pi.single ν 1 : Fin 4 → ℤ) ∈ s ∧ (-Pi.single ν 1 : Fin 4 → ℤ) ∈ s)
def MonotonePathsRemainIn (w : Site L m k) (Q : Set (Fin 4 → ℤ)) (R : Set (FourTorus L m)) : Prop :=
  ∀ q ∈ Q, ∀ s : List (Fin 4 → ℤ), IsMonotoneSteps s → q + s.sum ∈ Q →
    ∀ i : ℕ, i ≤ s.length →
      (offsetSite (offsetSite w q) (s.take i).sum : FourTorus L m) ∈ R
def countSteps (Γ : List (Bond L m k)) (s : Site L m k) : ℕ :=
  open Classical in Γ.countP fun b => decide (b.target - b.source = s)
def sitesOfPath (x : Site L m k) (Γ : List (Bond L m k)) : List (Site L m k) :=
  x :: Γ.map Bond.target
def translatePath (Γ : List (Bond L m k)) (a : Site L m k) : List (Bond L m k) :=
  Γ.map fun b => ⟨b.source + a, b.target + a, by
    obtain ⟨μ, hμ⟩ := b.isNeighbour
    exact ⟨μ, by simpa only [add_sub_add_right_eq_sub] using hμ⟩⟩
def ContourCoordinates (y : Site L m j) (x : Site L m k) (q : Fin 4 → ℤ) : Prop :=
  ∀ Γ ∈ contourSet y x,
    IsBondPathFromTo Γ (y.toSublattice k) x ∧
    (∀ ν, q ν ≠ 0 → countSteps Γ ((q ν).sign • unitStep L m k ν) = (q ν).natAbs ∧
      |q ν| ≤ centreToFaceSteps L) ∧
    (∀ b ∈ Γ, ∃ ν, q ν ≠ 0 ∧ b.target - b.source = (q ν).sign • unitStep L m k ν) ∧
    (∀ z ∈ sitesOfPath (y.toSublattice k) Γ, (z : FourTorus L m) ∈ unitBlock y) ∧
    ∀ b ∈ Γ, b ∈ (bondsInside (unitBlock y) : Set (Bond L m k))
def CornerCombCoordinates (y : Site L m j) (x : Site L m k) (q : Fin 4 → ℤ) : Prop :=
  (∃ P : Set (Site L m k), IsSiteBox k P ∧ blockAnchor k y ∈ P ∧ x ∈ P) ∧
  IsChartOffset (blockAnchor k y) x (fun ν => q ν + centreToFaceSteps L) ∧
  IsBondPathFromTo (coordinateComb (blockAnchor k y) x) (blockAnchor k y) x ∧
  (∀ ν, countSteps (coordinateComb (blockAnchor k y) x) (unitStep L m k ν) =
      (q ν + centreToFaceSteps L).toNat ∧
    q ν + centreToFaceSteps L ≤ (L : ℤ) - 1) ∧
  (∀ b ∈ coordinateComb (blockAnchor k y) x, ∃ ν, b.target - b.source = unitStep L m k ν) ∧
  (∀ z ∈ sitesOfPath (blockAnchor k y) (coordinateComb (blockAnchor k y) x),
    (z : FourTorus L m) ∈ unitBlock y) ∧
  ∀ b ∈ coordinateComb (blockAnchor k y) x, b ∈ (bondsInside (unitBlock y) : Set (Bond L m k))
def ContoursAndCombsTranslate (k : ℤ) (c : Bond L m j) (μ : Fin 4) : Prop :=
  ∀ x ∈ sitesInBlock k c.source,
    (fun Γ => translatePath Γ (blockTranslation L m k μ)) '' contourSet c.source x =
      contourSet c.target (x + blockTranslation L m k μ) ∧
    translatePath (coordinateComb (blockAnchor k c.source) x) (blockTranslation L m k μ) =
      coordinateComb (blockAnchor k c.target) (x + blockTranslation L m k μ)
def DoubleBlockAxialPaths (k : ℤ) (c : Bond L m j) (μ : Fin 4) : Prop :=
  (∀ x ∈ sitesInBlock k c.source,
    IsAxialDisplacement x (x + blockTranslation L m k μ) μ (L : ℤ) ∧
    crossingPath c x = forwardAxisPath x μ L ∧
    (∀ z, z ∈ sitesOfPath x (crossingPath c x) ↔
      ∃ i : ℕ, i ≤ L ∧ z = x + (i : ℤ) • unitStep L m k μ) ∧
    ∀ i : ℕ, i ≤ L →
      ((x + (i : ℤ) • unitStep L m k μ : Site L m k) : FourTorus L m) ∈ bondDoubleBlock c) ∧
  axialPath (c.source.toSublattice k) (c.target.toSublattice k) =
    crossingPath c (c.source.toSublattice k) ∧
  axialPath (blockAnchor k c.source) (blockAnchor k c.target) =
    crossingPath c (blockAnchor k c.source)
def PathsInsideDoubleBlock (k : ℤ) (c : Bond L m j) : Prop :=
  (∀ y : Site L m j, (y = c.source ∨ y = c.target) → ∀ x ∈ sitesInBlock k y,
    (∀ Γ ∈ contourSet y x, ∀ b ∈ Γ,
      b ∈ (bondsInside (bondDoubleBlock c) : Set (Bond L m k))) ∧
    ∀ b ∈ coordinateComb (blockAnchor k y) x,
      b ∈ (bondsInside (bondDoubleBlock c) : Set (Bond L m k))) ∧
  ∀ x ∈ sitesInBlock k c.source, ∀ b ∈ crossingPath c x,
    b ∈ (bondsInside (bondDoubleBlock c) : Set (Bond L m k))
def BlockPaths.Statement : Prop :=
  ∀ L m K : ℕ, Odd L → 13 ≤ L → 0 < m → ∀ n : ℕ, n < K →
    (∀ y : SiteAtLevel L m K (n + 1),
      BlockCoordinates (levelDepth K n) y ∧
      MonotonePathsRemainIn (y.toSublattice (levelDepth K n)) (blockIndexBox L) (unitBlock y) ∧
      ∀ q ∈ blockIndexBox L,
        ContourCoordinates y (offsetSite (y.toSublattice (levelDepth K n)) q) q ∧
        CornerCombCoordinates y (offsetSite (y.toSublattice (levelDepth K n)) q) q) ∧
    ∀ (c : BondAtLevel L m K (n + 1)) (μ : Fin 4),
      c.target - c.source = unitStep L m (levelDepth K (n + 1)) μ →
      DoubleBlockCoordinates (levelDepth K n) c μ ∧
      MonotonePathsRemainIn (c.source.toSublattice (levelDepth K n)) (doubleBlockIndexBox L μ)
        (bondDoubleBlock c) ∧
      ContoursAndCombsTranslate (levelDepth K n) c μ ∧
      DoubleBlockAxialPaths (levelDepth K n) c μ ∧
      PathsInsideDoubleBlock (levelDepth K n) c
end YangMills.Construction.PeriodicLattice

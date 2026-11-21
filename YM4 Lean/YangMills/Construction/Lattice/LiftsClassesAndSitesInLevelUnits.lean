import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BlocksAndCorridors
import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def scaledIntLattice (a : ℝ) : Set (Fin 4 → ℝ) :=
  {w | ∃ z : Fin 4 → ℤ, ∀ μ, w μ = a * (z μ : ℝ)}
def cosetMod (N : ℝ) (w : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  {w' | w' - w ∈ scaledIntLattice N}
def liftSetAtLevel (L m K j : ℕ) (x : FourTorus L m) : Set (Fin 4 → ℝ) :=
  {w | IsLevelLift L m K j x w}
def LevelSideFacts (L m K j k : ℕ) : Prop :=
  (∃ a : ℤ, sideInLevelUnits L m K j = (a : ℝ)) ∧
  (∃ a : ℤ, sideInLevelUnits L m K k = (a : ℝ)) ∧
  sideInLevelUnits L m K j = (L : ℝ) ^ (K - j) * torusSide L m ∧
  sideInLevelUnits L m K j = (L : ℝ) ^ (k - j) * sideInLevelUnits L m K k ∧
  sideInLevelUnits L m K k ≤ sideInLevelUnits L m K j ∧
  2 * (L : ℝ) ≤ sideInLevelUnits L m K k ∧
  (6 : ℝ) ≤ 2 * (L : ℝ)
def LiftCosetFacts (L m K j : ℕ) : Prop :=
  (∀ x : FourTorus L m, ∃ w, liftSetAtLevel L m K j x = cosetMod (sideInLevelUnits L m K j) w) ∧
  (∀ w, ∃! x : FourTorus L m,
    liftSetAtLevel L m K j x = cosetMod (sideInLevelUnits L m K j) w) ∧
  (∀ (w : Fin 4 → ℝ) (x : FourTorus L m), IsLevelLift L m K j x w ↔ x = torusClassOf L m K j w) ∧
  (∀ (x x' : FourTorus L m) (w w' : Fin 4 → ℝ), IsLevelLift L m K j x w →
    IsLevelLift L m K j x' w' →
    IsLevelLift L m K j (x + x') (w + w') ∧ IsLevelLift L m K j (x - x') (w - w')) ∧
  (∀ (x : FourTorus L m) (r w : Fin 4 → ℝ), IsLevelLift L m K j x w →
    shiftBy L m K j x r = torusClassOf L m K j (w + r))
def SitesAndBondsRescaled (L m K j k : ℕ) : Prop :=
  (sublattice L m (levelDepth K j) : Set (FourTorus L m)) =
    torusClassOf L m K j '' scaledIntLattice 1 ∧
  (sublattice L m (levelDepth K k) : Set (FourTorus L m)) =
    torusClassOf L m K j '' scaledIntLattice ((L : ℝ) ^ (k - j)) ∧
  (∀ (y : SiteAtLevel L m K k) (w : Fin 4 → ℝ), IsLevelLift L m K j (y : FourTorus L m) w →
    w ∈ scaledIntLattice ((L : ℝ) ^ (k - j))) ∧
  sublattice L m (levelDepth K k) ≤ sublattice L m (levelDepth K j) ∧
  toLevelUnits L K j (meshSize L (levelDepth K j)) = 1 ∧
  toLevelUnits L K j (meshSize L (levelDepth K k)) = (L : ℝ) ^ (k - j) ∧
  (∀ x x' : SiteAtLevel L m K k, (∃ e : BondAtLevel L m K k, e.source = x ∧ e.target = x') ↔
    ∃ (σ : ℝ) (μ : Fin 4), (σ = 1 ∨ σ = -1) ∧
      (x' : FourTorus L m) =
        shiftBy L m K j (x : FourTorus L m) ((σ * (L : ℝ) ^ (k - j)) • coordVec μ)) ∧
  (∀ e : BondAtLevel L m K k, e.IsPositivelyOriented ↔ ∃ μ : Fin 4,
    (e.target : FourTorus L m) =
      shiftBy L m K j (e.source : FourTorus L m) ((L : ℝ) ^ (k - j) • coordVec μ))
def SupNormAndCubesRescaled (L m K j k : ℕ) : Prop :=
  (∀ x : FourTorus L m, IsLeast (supNormVec '' liftSetAtLevel L m K j x)
    (toLevelUnits L K j (TorusMetric.torusSupNorm x))) ∧
  ∀ y : SiteAtLevel L m K k, cubeAround y =
    {z : FourTorus L m | toLevelUnits L K j (TorusMetric.torusSupNorm (z - (y : FourTorus L m))) ≤
      (L : ℝ) ^ (k - j) / 2}
def HalfWidthProperties (L n : ℕ) : Prop :=
  (∃ a : ℤ, halfWidth L n = (a : ℝ)) ∧
  0 ≤ halfWidth L n ∧
  2 * halfWidth L n + 1 = (L : ℝ) ^ n ∧
  halfWidth L 0 = 0
def RescaledLatticeStatement : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
  ∀ j k : ℕ, j ≤ k → k ≤ K →
    LevelSideFacts L m K j k ∧
    LiftCosetFacts L m K j ∧
    SitesAndBondsRescaled L m K j k ∧
    SupNormAndCubesRescaled L m K j k ∧
    HalfWidthProperties L (k - j)
end YangMills.Construction.PeriodicLattice

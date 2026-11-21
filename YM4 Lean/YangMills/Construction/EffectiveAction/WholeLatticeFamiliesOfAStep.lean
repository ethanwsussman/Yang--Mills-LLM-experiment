import YangMills.Construction.EffectiveAction.Coefficient
import YangMills.Construction.Lattice.LevelCoordinates
import YangMills.Construction.PolymerActivities.LocalisedActivitiesAndTheirNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace EffectiveAction
open Set YangMills.Construction.PeriodicLattice
abbrev torusCover (L n K j : ℕ) : (Fin 4 → ℝ) → FourTorus L n := torusClassOf L n K j
def scaledTorusSide (L n K j : ℕ) : ℝ := toLevelUnits L K j (torusSide L n)
def IsHalfSideBox (L n K j : ℕ) (B : Set (Fin 4 → ℝ)) : Prop :=
  ∃ a b : Fin 4 → ℝ, a ≤ b ∧ B = Icc a b ∧ ∀ μ, b μ - a μ < scaledTorusSide L n K j / 2
abbrev stepRegions (L n K j m' : ℕ) : Set (Set (FourTorus L n)) :=
  connectedRegions L n (coarseCubeIndex K m' j)
def IsBoxLift (L n K j m' : ℕ) (Y : Set (Fin 4 → ℝ)) (X : Set (FourTorus L n)) : Prop :=
  X ∈ stepRegions L n K j m' ∧ ∃ B, IsHalfSideBox L n K j B ∧ X ⊆ torusCover L n K j '' B ∧
    Y = torusCover L n K j ⁻¹' X ∩ B
def IsComplexPairOn (L j M : ℕ) (Y : CubeDomain) (U J : BondField) : Prop :=
  ∀ b ∈ Y.touchingBonds L j M, U b ∈ complexGaugeGroup ∧ J b ∈ complexLieAlgebra
open Classical in
def pushConfiguration (L n K j M : ℕ) (Y : CubeDomain) (U : BondField) :
    BondAtLevel L n K 0 → Matrices.ComplexMatrix2 := fun b =>
  if h : ∃ q ∈ Y.touchingBonds L j M, projectBond L n K 0 q = b then U h.choose
  else if h' : ∃ q ∈ Y.touchingBonds L j M, projectBond L n K 0 q = b.opposite then
    (U h'.choose)⁻¹
  else 1
open Classical in
def pushCurrent (L n K j M : ℕ) (Y : CubeDomain) (J : BondField) :
    BondAtLevel L n K 0 → Matrices.ComplexMatrix2 := fun b =>
  if h : ∃ q ∈ Y.touchingBonds L j M, projectBond L n K 0 q = b then J h.choose
  else if h' : ∃ q ∈ Y.touchingBonds L j M, projectBond L n K 0 q = b.opposite then
    -J h'.choose
  else 0
def pushPair (L n K j M : ℕ) (Y : CubeDomain) (U J : BondField) : FieldCurrentPair L n K :=
  (pushConfiguration L n K j M Y U, pushCurrent L n K j M Y J)
def projectedRegion (L n K j M : ℕ) (Y : CubeDomain) : Set (FourTorus L n) :=
  torusCover L n K j '' Y.carrier M
structure TorusSizeData (m' : ℕ) where
  sizes : Set ℕ
  sizes_infinite : sizes.Infinite
  sizes_pos : ∀ n ∈ sizes, 0 < n
  constants : ℕ → AnalyticityConstants
  cubeExp_eq : ∀ n ∈ sizes, (constants n).cubeExp = m'
  innerRadius : ℕ → ℝ
  outerRadius : ℕ → ℝ
abbrev TorusActivityFamily (L K j : ℕ) : Type := ∀ n : ℕ, RootedLocalActivities L n K j
def activityOnTorus {L K j : ℕ} (M : ℕ) (F : TorusActivityFamily L K j) (n : ℕ) (Y : CubeDomain)
    (y : IntPoint) (p : BondField × BondField) : ℂ :=
  F n (projectedRegion L n K j M Y) (projectSite L n K j y) (pushPair L n K j M Y p.1 p.2)
namespace TorusSizeData
variable {m' : ℕ} (S : TorusSizeData m') (L K j : ℕ)
def Admits (n : ℕ) (Y : CubeDomain) : Prop :=
  n ∈ S.sizes ∧ ∃ X, IsBoxLift L n K j m' (Y.carrier (L ^ m')) X
def admissiblePairs (n : ℕ) (Y : CubeDomain) : Set (BondField × BondField) :=
  {p | IsComplexPairOn L j (L ^ m') Y p.1 p.2 ∧
    pushPair L n K j (L ^ m') Y p.1 p.2 ∈
      (S.constants n).singleScaleDomainEqualRadii K j (projectedRegion L n K j (L ^ m') Y)
        (S.innerRadius n) (S.outerRadius n)}
variable {L K j}
structure IsConsistent (F : TorusActivityFamily L K j) : Prop where
  admits_exists : ∀ Y, ∃ n, S.Admits L K j n Y
  pairs_eq : ∀ Y n n', S.Admits L K j n Y → S.Admits L K j n' Y →
    S.admissiblePairs L K j n Y = S.admissiblePairs L K j n' Y
  value_eq : ∀ (y : RootedDomain (L ^ m')) (n n' : ℕ), S.Admits L K j n y.1.1 →
    S.Admits L K j n' y.1.1 → ∀ p ∈ S.admissiblePairs L K j n y.1.1,
      activityOnTorus (L ^ m') F n y.1.1 y.1.2 p = activityOnTorus (L ^ m') F n' y.1.1 y.1.2 p
open Classical in
def infiniteVolumeFamily (F : TorusActivityFamily L K j) : LocalFamily := fun Y y U J =>
  if h : ∃ n, S.Admits L K j n Y ∧ (U, J) ∈ S.admissiblePairs L K j n Y then
    activityOnTorus (L ^ m') F h.choose Y y (U, J)
  else 0
def infiniteVolumeStiffness (ε : ℝ) (F : TorusActivityFamily L K j) : ℂ :=
  stiffness ε L K j (L ^ m') (S.infiniteVolumeFamily F)
end TorusSizeData
end EffectiveAction
end YangMills.Construction

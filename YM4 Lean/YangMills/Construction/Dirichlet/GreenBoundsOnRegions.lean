import YangMills.Construction.Dirichlet.BlockGapFloors
import YangMills.Construction.Dirichlet.LatticeCalculus
import YangMills.Construction.Dirichlet.Parameters
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
noncomputable section
namespace YangMills.Construction.Dirichlet.RegionBounds
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
structure IsRegionSourceData (W : Set (PeriodicTorus d S)) (E : Set (LatticeBond d S 𝒮.ξ))
    (y' : PeriodicTorus d S) (f : LatticeSite d S 𝒮.ξ → ℝ) (F : BondField d S 𝒮.ξ) : Prop where
  cellUnion : 𝒮.IsCellUnion W
  boundaryRule : IsBoundaryRule (𝒮.Ω 0) W E
  centre_mem : y' ∈ 𝒮.centres
  source_vanishesOff : VanishesOff W f
  source_supportedNear : 𝒮.IsSupportedNear y' f
  field_supportedNear : 𝒮.IsFieldSupportedNear y' F
  field_zero_at_boundary : ∀ b : LatticeBond d S 𝒮.ξ, IsBoundaryBond W b → b ∉ E →
    F b.dir b.source = 0
  field_zero_away : ∀ b : LatticeBond d S 𝒮.ξ, (b.source : PeriodicTorus d S) ∉ W →
    (b.target : PeriodicTorus d S) ∉ W → F b.dir b.source = 0
def regionSolution (W : Set (PeriodicTorus d S)) (E : Set (LatticeBond d S 𝒮.ξ))
    (f : LatticeSite d S 𝒮.ξ → ℝ) (F : BondField d S 𝒮.ξ) :
    LatticeSite d S 𝒮.ξ → ℝ :=
  𝒮.blockGreen W E (f + restrictTo W (latticeDiv F))
def IsCloseTo (y : PeriodicTorus d S) (x : LatticeSite d S 𝒮.ξ) : Prop :=
  supNorm ((x : PeriodicTorus d S) - y) ≤ 2 * 𝒮.centreSpacing y
def decayFactor (y y' : PeriodicTorus d S) : ℝ :=
  Real.exp (-(1 / 2 * YangMills.Construction.WeightedGreen.expDecayRate d L aMinus aPlus) *
    𝒮.blockDist y y')
def sourceScale (y : PeriodicTorus d S) (f : LatticeSite d S 𝒮.ξ → ℝ) (F : BondField d S 𝒮.ξ) : ℝ :=
  𝒮.centreSpacing y ^ 2 * supNormAll f + 𝒮.centreSpacing y * fieldSupNorm F
def holderFactor (α : ℝ) (y : PeriodicTorus d S) (x x' : LatticeSite d S 𝒮.ξ) : ℝ :=
  (siteLOneDist x x' / 𝒮.centreSpacing y) ^ α
def HasDecayBounds (d L : ℕ) (aMinus aPlus C : ℝ) : Prop :=
  ∀ (S : ℝ) (𝒮 : BlockSetting d L aMinus aPlus S),
    BlockGapFloors d L aMinus aPlus (𝒮.M : ℝ) (𝒮.R₁ : ℝ) →
    ∀ (W : Set (PeriodicTorus d S)) (E : Set (LatticeBond d S 𝒮.ξ)) (y' : PeriodicTorus d S)
      (f : LatticeSite d S 𝒮.ξ → ℝ) (F : BondField d S 𝒮.ξ),
      IsRegionSourceData 𝒮 W E y' f F →
      ∀ y : PeriodicTorus d S, 𝒮.IsInteriorCentre W y →
      ∀ x : LatticeSite d S 𝒮.ξ, IsCloseTo 𝒮 y x →
      ∀ ν : Fin d,
        |regionSolution 𝒮 W E f F x| ≤ C * sourceScale 𝒮 y f F * decayFactor 𝒮 y y' ∧
        (F = 0 →
          |forwardDiff ν (regionSolution 𝒮 W E f F) x| ≤
            C * (𝒮.centreSpacing y * supNormAll f) * decayFactor 𝒮 y y')
def HasHolderDecayBounds (d L : ℕ) (aMinus aPlus α C : ℝ) : Prop :=
  ∀ (S : ℝ) (𝒮 : BlockSetting d L aMinus aPlus S),
    BlockGapFloors d L aMinus aPlus (𝒮.M : ℝ) (𝒮.R₁ : ℝ) →
    ∀ (W : Set (PeriodicTorus d S)) (E : Set (LatticeBond d S 𝒮.ξ)) (y' : PeriodicTorus d S)
      (f : LatticeSite d S 𝒮.ξ → ℝ) (F : BondField d S 𝒮.ξ),
      IsRegionSourceData 𝒮 W E y' f F →
      ∀ y : PeriodicTorus d S, 𝒮.IsInteriorCentre W y →
      ∀ x x' : LatticeSite d S 𝒮.ξ, IsCloseTo 𝒮 y x → IsCloseTo 𝒮 y x' →
      ∀ ν : Fin d,
        |regionSolution 𝒮 W E f F x - regionSolution 𝒮 W E f F x'| ≤
          C * holderFactor 𝒮 α y x x' * sourceScale 𝒮 y f F * decayFactor 𝒮 y y' ∧
        (F = 0 →
          |forwardDiff ν (regionSolution 𝒮 W E f F) x - forwardDiff ν (regionSolution 𝒮 W E f F) x'| ≤
            C * holderFactor 𝒮 α y x x' * (𝒮.centreSpacing y * supNormAll f) * decayFactor 𝒮 y y')
def decayConstant (d L : ℕ) (aMinus aPlus : ℝ) : ℝ :=
  Classical.epsilon fun C : ℝ => 0 < C ∧ HasDecayBounds d L aMinus aPlus C
def holderDecayConstant (d L : ℕ) (aMinus aPlus α : ℝ) : ℝ :=
  Classical.epsilon fun C : ℝ => 0 < C ∧ HasHolderDecayBounds d L aMinus aPlus α C
def RegionBoundsStatement : Prop :=
  ∀ (d L : ℕ) (aMinus aPlus : ℝ), Parameters d L aMinus aPlus →
    (0 < decayConstant d L aMinus aPlus ∧
      HasDecayBounds d L aMinus aPlus (decayConstant d L aMinus aPlus)) ∧
    ∀ α : ℝ, 0 < α → α < 1 →
      0 < holderDecayConstant d L aMinus aPlus α ∧
        HasHolderDecayBounds d L aMinus aPlus α (holderDecayConstant d L aMinus aPlus α)
end YangMills.Construction.Dirichlet.RegionBounds

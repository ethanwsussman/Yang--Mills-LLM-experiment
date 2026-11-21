import YangMills.Construction.Dirichlet.CubeCoverAndWalks
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.DirichletGreen
variable {d L : ℕ} {S aMinus aPlus : ℝ}
structure GreenConstants where
  δ₀ : ℝ
  rStar : ℝ
  mStar : ℝ
  B : ℝ
  Cw : ℝ
  Bα : ℝ → ℝ
instance : Inhabited GreenConstants := ⟨⟨0, 0, 0, 0, 0, fun _ => 0⟩⟩
def fieldModulusAt {ξ : ℝ} (F : Dirichlet.BondField d S ξ) (x : Dirichlet.LatticeSite d S ξ) : ℝ :=
  ⨆ μ, |F μ x|
variable (𝒮 : Dirichlet.BlockSetting d L aMinus aPlus S)
structure GreenExists : Prop where
  lower_bound : ∀ f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.Ω 0) f →
    min 4 aMinus * ∑ n ∈ Finset.range (𝒮.t + 1),
        (𝒮.scaleAt n ^ 2)⁻¹ * Dirichlet.siteNormOn (Torus.shell 𝒮.Ω n) f ^ 2 ≤
      Dirichlet.innerSum f (𝒮.fullOperator f)
  operator_positive : ∀ f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.Ω 0) f →
    f ≠ 0 → 0 < Dirichlet.innerSum f (𝒮.fullOperator f)
  invertible : ∀ f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.Ω 0) f →
    ∃! g : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.Ω 0) g ∧ 𝒮.fullOperator g = f
  green_symmetric : ∀ f g : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.Ω 0) f →
    Dirichlet.VanishesOff (𝒮.Ω 0) g →
      Dirichlet.innerSum (𝒮.fullGreen f) g = Dirichlet.innerSum f (𝒮.fullGreen g)
  green_positive : ∀ f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.Ω 0) f →
    f ≠ 0 → 0 < Dirichlet.innerSum f (𝒮.fullGreen f)
structure IsAdmissibleData (y y' : Torus.PeriodicTorus d S) (f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ)
    (F : Dirichlet.BondField d S 𝒮.ξ) (ζ : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ) : Prop where
  first_mem : y ∈ 𝒮.centres
  second_mem : y' ∈ 𝒮.centres
  function_supported : Dirichlet.VanishesOff (𝒮.cell y') f
  field_attached : 𝒮.IsFieldSupportedNear y' F
  cutoff_vanishes : ∀ x : Dirichlet.LatticeSite d S 𝒮.ξ,
    𝒮.centreSpacing y ≤ Torus.supNorm ((x : Torus.PeriodicTorus d S) - y) → ζ x = 0
def divSource (F : Dirichlet.BondField d S 𝒮.ξ) : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ :=
  Dirichlet.restrictTo (𝒮.Ω 0) (Dirichlet.latticeDiv F)
def holderWeight (α : ℝ) (y : Torus.PeriodicTorus d S) (ζ : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ) : ℝ :=
  𝒮.centreSpacing y ^ (1 - α) *
    (Dirichlet.scaledHolderSeminorm α (𝒮.centreSpacing y) ζ + Dirichlet.supNormAll ζ)
def cutoffGrad (ζ g : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ) : Dirichlet.BondField d S 𝒮.ξ :=
  fun μ => Dirichlet.pointwiseMul ζ (Dirichlet.grad g μ)
namespace GreenConstants
variable (c : GreenConstants)
def LargeEnough : Prop :=
  c.mStar ≤ (𝒮.M : ℝ) ∧ c.rStar ≤ (𝒮.R₁ : ℝ) * (𝒮.M : ℝ)
def expDecay (κ : ℝ) (y y' : Torus.PeriodicTorus d S) : ℝ := Real.exp (-κ * 𝒮.blockDist y y')
structure PointBounds : Prop where
  at_sites : c.LargeEnough 𝒮 → ∀ (y y' : Torus.PeriodicTorus d S)
    (f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ)
    (F : Dirichlet.BondField d S 𝒮.ξ) (ζ : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ),
    IsAdmissibleData 𝒮 y y' f F ζ →
    ∀ x : Dirichlet.LatticeSite d S 𝒮.ξ,
      Torus.supNorm ((x : Torus.PeriodicTorus d S) - y) ≤ 2 * 𝒮.centreSpacing y →
      |𝒮.fullGreen f x| ≤
          c.B * 𝒮.centreSpacing y ^ 2 * expDecay 𝒮 (c.δ₀ / 2) y y' * Dirichlet.supNormAll f ∧
      fieldModulusAt (Dirichlet.grad (𝒮.fullGreen f)) x ≤
          c.B * 𝒮.centreSpacing y * expDecay 𝒮 (c.δ₀ / 2) y y' * Dirichlet.supNormAll f ∧
      |𝒮.fullGreen (divSource 𝒮 F) x| ≤
          c.B * 𝒮.centreSpacing y * expDecay 𝒮 (c.δ₀ / 2) y y' * Dirichlet.fieldSupNorm F
  laplacian : c.LargeEnough 𝒮 → ∀ (y y' : Torus.PeriodicTorus d S)
    (f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ)
    (F : Dirichlet.BondField d S 𝒮.ξ) (ζ : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ),
    IsAdmissibleData 𝒮 y y' f F ζ →
    ∀ x : Dirichlet.LatticeSite d S 𝒮.ξ, (x : Torus.PeriodicTorus d S) ∈ 𝒮.cell y →
      |Dirichlet.latticeLaplacian (𝒮.fullGreen f) x| ≤
        c.B * expDecay 𝒮 (c.δ₀ / 2) y y' * Dirichlet.supNormAll f
  holder : c.LargeEnough 𝒮 → ∀ (y y' : Torus.PeriodicTorus d S)
    (f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ)
    (F : Dirichlet.BondField d S 𝒮.ξ) (ζ : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ),
    IsAdmissibleData 𝒮 y y' f F ζ →
    ∀ α : ℝ, 0 < α → α < 1 →
      Dirichlet.fieldHolderSeminorm α (cutoffGrad 𝒮 ζ (𝒮.fullGreen f)) ≤
          c.Bα α * holderWeight 𝒮 α y ζ * expDecay 𝒮 (c.δ₀ / 2) y y' * Dirichlet.supNormAll f ∧
      Dirichlet.holderSeminorm α (Dirichlet.pointwiseMul ζ (𝒮.fullGreen (divSource 𝒮 F))) ≤
          c.Bα α * holderWeight 𝒮 α y ζ * expDecay 𝒮 (c.δ₀ / 2) y y' * Dirichlet.fieldSupNorm F
variable (E : Dirichlet.CentredCube d S → Set (Dirichlet.LatticeBond d S 𝒮.ξ))
def walkSum (m : ℕ) (v : List (Dirichlet.CentredCube d S) → ℝ) : ℝ :=
  ∑ᶠ ω ∈ {ω : List (Dirichlet.CentredCube d S) |
    𝒮.IsCubeWalk ω ∧ Dirichlet.BlockSetting.walkSteps ω = m}, v ω
def walkGain (m : ℕ) : ℝ := (c.Cw / (𝒮.M : ℝ)) ^ m
structure WalkSumBounds : Prop where
  at_sites : ∀ (m : ℕ) (y y' : Torus.PeriodicTorus d S) (f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ)
    (F : Dirichlet.BondField d S 𝒮.ξ) (ζ : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ),
    IsAdmissibleData 𝒮 y y' f F ζ →
    ∀ x : Dirichlet.LatticeSite d S 𝒮.ξ, (x : Torus.PeriodicTorus d S) ∈ 𝒮.cell y →
      walkSum 𝒮 m (fun ω => |𝒮.walkOperator E ω f x|) ≤
        walkGain 𝒮 c m * c.B * 𝒮.centreSpacing y ^ 2 * expDecay 𝒮 (c.δ₀ / 4) y y' *
          Dirichlet.supNormAll f ∧
      walkSum 𝒮 m (fun ω => fieldModulusAt (Dirichlet.grad (𝒮.walkOperator E ω f)) x) ≤
        walkGain 𝒮 c m * c.B * 𝒮.centreSpacing y * expDecay 𝒮 (c.δ₀ / 4) y y' *
          Dirichlet.supNormAll f ∧
      walkSum 𝒮 m (fun ω => |Dirichlet.latticeLaplacian (𝒮.walkOperator E ω f) x|) ≤
        walkGain 𝒮 c m * c.B * expDecay 𝒮 (c.δ₀ / 4) y y' * Dirichlet.supNormAll f ∧
      walkSum 𝒮 m (fun ω => |𝒮.walkOperator E ω (divSource 𝒮 F) x|) ≤
        walkGain 𝒮 c m * c.B * 𝒮.centreSpacing y * expDecay 𝒮 (c.δ₀ / 4) y y' *
          Dirichlet.fieldSupNorm F
  holder : ∀ (m : ℕ) (y y' : Torus.PeriodicTorus d S) (f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ)
    (F : Dirichlet.BondField d S 𝒮.ξ) (ζ : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ),
    IsAdmissibleData 𝒮 y y' f F ζ →
    ∀ α : ℝ, 0 < α → α < 1 →
      walkSum 𝒮 m
          (fun ω => Dirichlet.fieldHolderSeminorm α (cutoffGrad 𝒮 ζ (𝒮.walkOperator E ω f))) ≤
        walkGain 𝒮 c m * c.Bα α * holderWeight 𝒮 α y ζ * expDecay 𝒮 (c.δ₀ / 4) y y' *
          Dirichlet.supNormAll f ∧
      walkSum 𝒮 m
          (fun ω => Dirichlet.holderSeminorm α
            (Dirichlet.pointwiseMul ζ (𝒮.walkOperator E ω (divSource 𝒮 F)))) ≤
        walkGain 𝒮 c m * c.Bα α * holderWeight 𝒮 α y ζ * expDecay 𝒮 (c.δ₀ / 4) y y' *
          Dirichlet.fieldSupNorm F
structure WalkExpansion : Prop where
  squares_floor : ∀ p : Torus.PeriodicTorus d S,
    Torus.supSetDist {p} (𝒮.Ω 0) ≤ ENNReal.ofReal (4 * 𝒮.ξ) → 1 ≤ 𝒮.bumpSqSum p
  parametrix : ∀ f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.Ω 0) f →
    𝒮.fullOperator (𝒮.approxGreen E f) = f - 𝒮.totalRemainder E f
  local_remainder : ∀ Q ∈ 𝒮.coverCubes, ∀ y ∈ 𝒮.centres, ∀ y' ∈ 𝒮.centres,
    ∀ x : Dirichlet.LatticeSite d S 𝒮.ξ, (x : Torus.PeriodicTorus d S) ∈ 𝒮.cell y →
    ∀ f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.cell y') f →
      |𝒮.cubeRemainder E Q f x| ≤
        c.Cw * (𝒮.M : ℝ)⁻¹ * expDecay 𝒮 (c.δ₀ / 2) y y' * Dirichlet.supNormAll f
  remainder_bound : ∀ f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.Ω 0) f →
    Dirichlet.supNormAll (𝒮.totalRemainder E f) ≤ c.Cw * (𝒮.M : ℝ)⁻¹ * Dirichlet.supNormAll f ∧
      c.Cw * (𝒮.M : ℝ)⁻¹ * Dirichlet.supNormAll f ≤ 1 / 2 * Dirichlet.supNormAll f
  resolvent_exists : ∀ f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.Ω 0) f →
    ∃! g : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ,
      Dirichlet.VanishesOff (𝒮.Ω 0) g ∧ g - 𝒮.totalRemainder E g = f
  green_eq_resolvent : ∀ f g : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ,
    Dirichlet.VanishesOff (𝒮.Ω 0) f → Dirichlet.VanishesOff (𝒮.Ω 0) g →
      g - 𝒮.totalRemainder E g = f → 𝒮.fullGreen f = 𝒮.approxGreen E g
  neumann_series : ∀ f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.Ω 0) f →
    ∀ x, HasSum (fun m : ℕ => 𝒮.approxGreen E ((𝒮.totalRemainder E)^[m] f) x) (𝒮.fullGreen f x)
  walk_series : ∀ f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.Ω 0) f →
    ∀ x, HasSum (fun ω : {ω : List (Dirichlet.CentredCube d S) // 𝒮.IsCubeWalk ω} =>
      𝒮.walkOperator E ω.1 f x) (𝒮.fullGreen f x)
  walk_bounds : WalkSumBounds 𝒮 c E
structure Holds (d L : ℕ) (aMinus aPlus : ℝ) : Prop where
  rate_pos : 0 < c.δ₀
  rate_le_one : c.δ₀ ≤ 1
  existence : ∀ (S : ℝ) (𝒮 : Dirichlet.BlockSetting d L aMinus aPlus S), GreenExists 𝒮
  bounds : ∀ (S : ℝ) (𝒮 : Dirichlet.BlockSetting d L aMinus aPlus S), c.PointBounds 𝒮
  expansion : ∀ (S : ℝ) (𝒮 : Dirichlet.BlockSetting d L aMinus aPlus S), c.LargeEnough 𝒮 →
    ∀ E : Dirichlet.CentredCube d S → Set (Dirichlet.LatticeBond d S 𝒮.ξ),
      𝒮.IsRuleFamily E → c.WalkExpansion 𝒮 E
end GreenConstants
def GreenBoundsClaim : Prop :=
  ∀ (d L : ℕ) (aMinus aPlus : ℝ), Dirichlet.Parameters d L aMinus aPlus →
    ∃ c : GreenConstants, c.Holds d L aMinus aPlus
def chosenConstants (d L : ℕ) (aMinus aPlus : ℝ) : GreenConstants :=
  Classical.epsilon fun c : GreenConstants => c.Holds d L aMinus aPlus

namespace FourDimensional
def constants (L : ℕ) : GreenConstants :=
  chosenConstants 4 L (1 - ((L : ℝ) ^ 2)⁻¹) 1
def decayRate (L : ℕ) : ℝ := (constants L).δ₀
def boundConstant (L : ℕ) : ℝ := (constants L).B
def blockFloor (L : ℕ) : ℝ := (constants L).mStar
def gapFloor (L : ℕ) : ℝ := (constants L).rStar
end FourDimensional

end YangMills.Construction.DirichletGreen

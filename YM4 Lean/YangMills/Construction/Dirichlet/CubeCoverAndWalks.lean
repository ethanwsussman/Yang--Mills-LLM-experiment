import YangMills.Construction.Dirichlet.LatticeCalculus
import YangMills.Construction.Dirichlet.Parameters
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.Dirichlet
@[ext]
structure CentredCube (d : ℕ) (S : ℝ) where
  level : ℕ
  centre : PeriodicTorus d S
variable {d L : ℕ} {S aMinus aPlus : ℝ}
def circleRep (θ : AddCircle S) : ℝ :=
  Classical.epsilon fun v : ℝ => v ∈ Ioc (-(S / 2)) (S / 2) ∧ (v : AddCircle S) = θ
def IsCubeVertex (c : PeriodicTorus d S) (σ : ℝ) (z : PeriodicTorus d S) : Prop :=
  ∃ ε : Fin d → ℝ, (∀ μ, ε μ = 1 ∨ ε μ = -1) ∧ z = c + torusProj d S fun μ => ε μ * (σ / 2)
def pointwiseMul {ξ : ℝ} (h f : LatticeSite d S ξ → ℝ) : LatticeSite d S ξ → ℝ :=
  fun x => h x * f x
namespace BlockSetting
variable (𝒮 : BlockSetting d L aMinus aPlus S)
def blockWidth (n : ℕ) : ℝ := (𝒮.M : ℝ) * 𝒮.scaleAt n
def coverCubesAt (n : ℕ) : Set (CentredCube d S) :=
  {Q | Q.level = n ∧ n ≤ 𝒮.t ∧ ∃ c ∈ spacingLattice d S (𝒮.blockWidth n),
    cubeAt c (𝒮.blockWidth n) ⊆ shell 𝒮.Ω n ∧ IsCubeVertex c (𝒮.blockWidth n) Q.centre}
def coverCubes : Set (CentredCube d S) := {Q | ∃ n ≤ 𝒮.t, Q ∈ 𝒮.coverCubesAt n}
def cubePoints (Q : CentredCube d S) : Set (PeriodicTorus d S) :=
  {p | supNorm (p - Q.centre) ≤ 𝒮.blockWidth Q.level}
def innerRegion (Q : CentredCube d S) : Set (PeriodicTorus d S) :=
  ⋃ y ∈ {y | y ∈ 𝒮.centres ∧ 𝒮.cell y ⊆ 𝒮.cubePoints Q}, 𝒮.cell y
def cubeBump (Q : CentredCube d S) (p : PeriodicTorus d S) : ℝ :=
  ∏ μ, bumpProfile (circleRep (p μ - Q.centre μ) / 𝒮.blockWidth Q.level)
def bumpSqSum (p : PeriodicTorus d S) : ℝ := ∑ᶠ Q ∈ 𝒮.coverCubes, 𝒮.cubeBump Q p ^ 2
def partitionOfUnity (Q : CentredCube d S) (p : PeriodicTorus d S) : ℝ :=
  𝒮.cubeBump Q p * (√(𝒮.bumpSqSum p))⁻¹
def latticeCutoff (Q : CentredCube d S) : LatticeSite d S 𝒮.ξ → ℝ :=
  fun x => 𝒮.partitionOfUnity Q x
def commutatorOp (h ψ : LatticeSite d S 𝒮.ξ → ℝ) : LatticeSite d S 𝒮.ξ → ℝ :=
  restrictTo (𝒮.Ω 0) fun x =>
    (∑ᶠ x' ∈ {x' : LatticeSite d S 𝒮.ξ | IsNeighbor x x'}, (𝒮.ξ ^ 2)⁻¹ * (h x' - h x) * (ψ x' - ψ x)) -
      latticeLaplacian h x * ψ x -
      𝒮.a (𝒮.centreIndex (𝒮.centreOf x)) * (𝒮.centreSpacing (𝒮.centreOf x) ^ 2)⁻¹ *
        (𝒮.ξ / 𝒮.centreSpacing (𝒮.centreOf x)) ^ d *
        ∑ᶠ x' ∈ {x' : LatticeSite d S 𝒮.ξ | (x' : PeriodicTorus d S) ∈ 𝒮.cell (𝒮.centreOf x)},
          (h x' - h x) * ψ x'
def IsRuleFamily (E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ)) : Prop :=
  ∀ Q ∈ 𝒮.coverCubes, IsBoundaryRule (𝒮.Ω 0) (𝒮.innerRegion Q) (E Q)
variable (E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ))
def cubeGreen (Q : CentredCube d S) : (LatticeSite d S 𝒮.ξ → ℝ) → LatticeSite d S 𝒮.ξ → ℝ :=
  𝒮.blockGreen (𝒮.innerRegion Q) (E Q)
def sandwichedGreen (Q : CentredCube d S) (f : LatticeSite d S 𝒮.ξ → ℝ) : LatticeSite d S 𝒮.ξ → ℝ :=
  pointwiseMul (𝒮.latticeCutoff Q) (𝒮.cubeGreen E Q (pointwiseMul (𝒮.latticeCutoff Q) f))
def approxGreen (f : LatticeSite d S 𝒮.ξ → ℝ) : LatticeSite d S 𝒮.ξ → ℝ :=
  fun x => ∑ᶠ Q ∈ 𝒮.coverCubes, 𝒮.sandwichedGreen E Q f x
def cubeRemainder (Q : CentredCube d S) (f : LatticeSite d S 𝒮.ξ → ℝ) : LatticeSite d S 𝒮.ξ → ℝ :=
  restrictTo (𝒮.Ω 0)
    (𝒮.commutatorOp (𝒮.latticeCutoff Q) (𝒮.cubeGreen E Q (pointwiseMul (𝒮.latticeCutoff Q) f)))
def totalRemainder (f : LatticeSite d S 𝒮.ξ → ℝ) : LatticeSite d S 𝒮.ξ → ℝ :=
  fun x => ∑ᶠ Q ∈ 𝒮.coverCubes, 𝒮.cubeRemainder E Q f x
def IsCubeWalk (ω : List (CentredCube d S)) : Prop :=
  ω ≠ [] ∧ (∀ Q ∈ ω, Q ∈ 𝒮.coverCubes) ∧
    List.IsChain (fun A B => (𝒮.cubePoints A ∩ 𝒮.cubePoints B).Nonempty) ω
def walkSteps (ω : List (CentredCube d S)) : ℕ := ω.length - 1
def walkOperator : List (CentredCube d S) → (LatticeSite d S 𝒮.ξ → ℝ) → LatticeSite d S 𝒮.ξ → ℝ
  | [] => id
  | Q :: ω => 𝒮.sandwichedGreen E Q ∘ ω.foldr (fun Q' T => 𝒮.cubeRemainder E Q' ∘ T) id
end BlockSetting
end YangMills.Construction.Dirichlet

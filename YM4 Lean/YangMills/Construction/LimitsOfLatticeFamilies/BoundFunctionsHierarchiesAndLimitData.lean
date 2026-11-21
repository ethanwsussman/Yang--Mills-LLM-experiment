import YangMills.Construction.LimitsOfLatticeFamilies.SpacesOfFunctionsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
namespace ModelSpace
variable (s : Conventions.StandingParameters)
def sharpNormOfScale (M : ℕ) : (Y : ModelSpace) → (Y.Carrier s → ℝ) → ℝ
  | euclidean, g => TestFunctions.sharpNormR4 (M : ℝ) g
  | torus, g => TestFunctions.sharpNormTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (M : ℝ) g
end ModelSpace
open ModelSpace
structure SeparationBound where
  val : ℕ → ℝ → ℝ → ℝ
  val_nonneg : ∀ n, 2 ≤ n → ∀ d R, 0 < d → 0 < R → 0 ≤ val n d R
  val_antitoneOn : ∀ n, 2 ≤ n → ∀ R, 0 < R → AntitoneOn (fun d => val n d R) (Ioi 0)
def EventuallyIn (J : Set ℕ) (P : ℕ → Prop) : Prop := ∃ k, ∀ j ∈ J, k ≤ j → P j
variable (s : Conventions.StandingParameters) (Y : ModelSpace)
structure HierarchySequence where
  indices : Set ℕ
  indices_infinite : indices.Infinite
  rad : ℕ → ℝ≥0∞
  rad_pos : ∀ j ∈ indices, 0 < rad j
  rad_eventually_ge : ∀ ρ : ℝ, 0 < ρ → EventuallyIn indices fun j => ENNReal.ofReal ρ ≤ rad j
  rad_torus : Y = torus → ∀ j ∈ indices, rad j = ⊤
  phi : (j n : ℕ) → TupleFunctional (lipSepTuplesIn s Y n (rad j))
  phi_multilinear : ∀ j ∈ indices, ∀ n, 2 ≤ n → IsMultilinearLip (phi j n)
  phi_symm : ∀ j ∈ indices, ∀ n, 2 ≤ n → (phi j n).IsSymm
variable {s Y}
def HierarchySequence.definedAt (H : HierarchySequence s Y) {n : ℕ} (g : FunTuple s Y n) : Set ℕ :=
  {j | j ∈ H.indices ∧ ∀ i, supportIn s Y (g i) ⊆ ballAtBase s Y (H.rad j)}
variable (s Y)
variable {s Y}
end YangMills.Construction.LatticeLimits
end

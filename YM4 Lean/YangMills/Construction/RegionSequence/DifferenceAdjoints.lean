import YangMills.Construction.Dirichlet.RegionSequenceOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RegionSequence
open Dirichlet NestedRegions
variable (𝒮 : NestedRegions)
structure DifferenceAdjoints : Prop where
  site_inner_forwardDiff : ∀ (ν : Fin 4) (f g : 𝒮.FineSite → ℝ),
    innerSum (forwardDiff ν f) g = innerSum f (backwardDiff ν g)
  site_backwardDiff_eq : ∀ (ν : Fin 4) (f : 𝒮.FineSite → ℝ),
    backwardDiff ν f = 𝒮.ξ⁻¹ • (translateBackward ν f - f) ∧
      backwardDiff ν f = -translateBackward ν (forwardDiff ν f)
  site_comm : ∀ (ν ρ : Fin 4) (f : 𝒮.FineSite → ℝ),
    forwardDiff ν (forwardDiff ρ f) = forwardDiff ρ (forwardDiff ν f) ∧
      forwardDiff ν (backwardDiff ρ f) = backwardDiff ρ (forwardDiff ν f) ∧
      backwardDiff ν (backwardDiff ρ f) = backwardDiff ρ (backwardDiff ν f)
  bond_inner_fwdDiff : ∀ (ν : Fin 4) (A B : 𝒮.FineBond → ℝ),
    bondInner (NestedRegions.fwdDiff ν A) B = bondInner A (bwdDiff ν B)
  bond_bwdDiff_eq : ∀ (ν : Fin 4) (A : 𝒮.FineBond → ℝ) (b : 𝒮.FineBond),
    bwdDiff ν A b = 𝒮.ξ⁻¹ * (A (shiftDown ν b) - A b) ∧
      bwdDiff ν A b = -NestedRegions.fwdDiff ν A (shiftDown ν b)
  bond_comm : ∀ (ν ρ : Fin 4) (A : 𝒮.FineBond → ℝ),
    NestedRegions.fwdDiff ν (NestedRegions.fwdDiff ρ A) =
        NestedRegions.fwdDiff ρ (NestedRegions.fwdDiff ν A) ∧
      NestedRegions.fwdDiff ν (bwdDiff ρ A) = bwdDiff ρ (NestedRegions.fwdDiff ν A) ∧
      bwdDiff ν (bwdDiff ρ A) = bwdDiff ρ (bwdDiff ν A)
  tensor_inner_fwdDiff : ∀ r : ℕ, r = 1 ∨ r = 2 → ∀ (ν : Fin 4) (J J' : 𝒮.Tensor r),
    tensorInner (r := r) (fun κ => NestedRegions.fwdDiff ν (J κ)) J' =
      tensorInner (r := r) J (fun κ => bwdDiff ν (J' κ))
  tensor_bwdDiff_eq : ∀ r : ℕ, r = 1 ∨ r = 2 → ∀ (ν : Fin 4) (J : 𝒮.Tensor r)
    (κ : Fin r → Fin 4) (b : 𝒮.FineBond),
    bwdDiff ν (J κ) b = 𝒮.ξ⁻¹ * (J κ (shiftDown ν b) - J κ b) ∧
      bwdDiff ν (J κ) b = -NestedRegions.fwdDiff ν (J κ) (shiftDown ν b)
  tensor_comm : ∀ r : ℕ, r = 1 ∨ r = 2 → ∀ (ν ρ : Fin 4) (J : 𝒮.Tensor r),
    (fun κ : Fin r → Fin 4 => NestedRegions.fwdDiff ν (NestedRegions.fwdDiff ρ (J κ))) =
        (fun κ => NestedRegions.fwdDiff ρ (NestedRegions.fwdDiff ν (J κ))) ∧
      (fun κ : Fin r → Fin 4 => NestedRegions.fwdDiff ν (bwdDiff ρ (J κ))) =
        (fun κ => bwdDiff ρ (NestedRegions.fwdDiff ν (J κ))) ∧
      (fun κ : Fin r → Fin 4 => bwdDiff ν (bwdDiff ρ (J κ))) =
        (fun κ => bwdDiff ρ (bwdDiff ν (J κ)))
def DifferenceAdjointsHold : Prop := ∀ 𝒮 : NestedRegions, DifferenceAdjoints 𝒮
end YangMills.Construction.RegionSequence

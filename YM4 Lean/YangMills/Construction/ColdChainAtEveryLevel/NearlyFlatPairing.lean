import YangMills.Construction.ColdChainAtEveryLevel.BoundedDifferences
import YangMills.Construction.ColdChainAtEveryLevel.HomotopyFormula
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.LatticeFractionalIntegration YangMills.Construction.FiniteDifferences
namespace FlatPairing
def stepDisplacement (st : PathStep) : Lattice4 := if st.2 then basisVector st.1 else - basisVector st.1
def pathProduct (R : Lattice4 → Lattice4 → UnitQuaternion) : Lattice4 → List PathStep → UnitQuaternion
  | _, [] => 1
  | x, st :: r => R x (x + stepDisplacement st) * pathProduct R (x + stepDisplacement st) r
def scaledPairNorm (κ : ℝ) (a : Lattice4 × Lattice4) : ℝ := κ * ((supNorm a.1 : ℝ) + supNorm a.2)
def pairingValue (P0 : Lattice4 × Lattice4 → ℝ) (P1 : Lattice4 × Lattice4 → ℍ[ℝ]) (a b : Lattice4) : ℍ[ℝ] :=
  (P0 (a, b) : ℍ[ℝ]) + P1 (a, b)
def twoBlockHull (L : ℕ) (i : Fin 4) : Set Lattice4 :=
  {x | ∀ μ, -(((L : ℤ) - 1) / 2) ≤ x μ ∧ x μ ≤ ((L : ℤ) - 1) / 2 + if μ = i then (L : ℤ) else 0}
def closedBlockContour (R : Lattice4 → Lattice4 → UnitQuaternion) (L : ℕ) (h : Lattice4)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) : UnitQuaternion :=
  pathProduct R 0 (bondContour L h π i) * R ((L : ℤ) • basisVector i) 0
def nearlyFlatPairingStatement : Prop :=
  ∀ B : ℝ, 1 ≤ B → ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
    ∀ (κ ρ : ℝ) (D : Set Lattice4) (P0 : Lattice4 × Lattice4 → ℝ) (P1 : Lattice4 × Lattice4 → ℍ[ℝ]),
      0 ≤ κ → 0 ≤ ρ → ρ ≤ 1 →
      FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) B P0 →
      FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) ρ P1 →
      (∀ a b, pairingValue P0 P1 b a = star (pairingValue P0 P1 a b)) →
      (∀ a ∈ D, 1 ≤ (pairingValue P0 P1 a a).re) →
      (∀ a ∈ D, ∀ b ∈ D, κ * supNorm (b - a) ≤ r →
        ‖((polarUnit (pairingValue P0 P1 a b) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
          C * ρ * (κ * supNorm (b - a))) ∧
      (∀ y ∈ D, ∀ x ∈ D, ∀ t : Lattice4, x + t ∈ D → κ * supNorm (x - y) ≤ r → κ * supNorm t ≤ r →
        ‖((polarUnit (pairingValue P0 P1 y x) * polarUnit (pairingValue P0 P1 x (x + t)) *
            polarUnit (pairingValue P0 P1 (x + t) y) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
          C * ρ * (κ * supNorm (x - y)) * (κ * supNorm t)) ∧
      ∀ (L : ℕ) (i : Fin 4), Odd L → 3 ≤ L → κ * (3 * L) ≤ r → (∀ x ∈ twoBlockHull L i, x ∈ D) →
        (∀ h ∈ centredCube L, ∀ π : Equiv.Perm (Fin 4),
          ‖((closedBlockContour (fun a b => polarUnit (pairingValue P0 P1 a b)) L h π i : UnitQuaternion)
            : ℍ[ℝ]) - 1‖ ≤ C * ρ * (κ * L) ^ 2) ∧
        ‖(1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
          pureComponent ((closedBlockContour (fun a b => polarUnit (pairingValue P0 P1 a b)) L h π i
            : UnitQuaternion) : ℍ[ℝ])‖ ≤ C * ρ * (κ * L) ^ 3
end FlatPairing
end YangMills.Construction
end

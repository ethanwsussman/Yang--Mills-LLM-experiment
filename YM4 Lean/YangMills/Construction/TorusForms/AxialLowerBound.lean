import YangMills.Construction.TorusForms.FacesAndSumsOfBlocksAndCorridors
import YangMills.Construction.TorusForms.ObjectsOnTheIntegerLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace BlockSpin
open Finset
section Torus
variable (S : Lattice.LatticeParameters) {ℓ : Fin S.d → ℝ} [PeriodsMultipleOfBlock S ℓ]
def VanishesOnBlockTrees (Λ' : Set (Lattice.LatticeSite ℓ (S.L : ℝ)))
    (A : Lattice.Cochain1 ℓ 1) : Prop :=
  ∀ y ∈ Λ', ∀ e ∈ blockTree S
    (PeriodsMultipleOfBlock.isBlockSpacing_one (S := S) (ℓ := ℓ)) y, A e = 0
open Classical in
def SharpAxialBound (Λ' : Set (Lattice.LatticeSite ℓ (S.L : ℝ)))
    (𝒞 : Set (Lattice.Link ℓ (S.L : ℝ))) (A : Lattice.Cochain1 ℓ 1) : Prop :=
  (S.L : ℝ) ^ (S.d - 2) * (∑ c ∈ univ.filter (· ∈ 𝒞), |blockAverage1 S 1 1 (S.L : ℝ) A c| ^ 2)
      + (∑ y ∈ univ.filter (· ∈ Λ'), blockCurvatureEnergy S A y)
      + (∑ c ∈ univ.filter (· ∈ 𝒞), corridorCurvatureEnergy S A c)
    ≥ 1 / (12 * (S.d : ℝ) ^ 2) * ((S.L : ℝ) ^ (S.d + 1))⁻¹ * Lattice.latticeNorm S.d 1 A ^ 2
open Classical in
def AxialBound (Λ' : Set (Lattice.LatticeSite ℓ (S.L : ℝ))) (A : Lattice.Cochain1 ℓ 1) : Prop :=
  (S.L : ℝ) ^ (S.d - 2) *
        (∑ c ∈ univ.filter (· ∈ Lattice.linksTouching Λ'),
          |blockAverage1 S 1 1 (S.L : ℝ) A c| ^ 2)
      + (∑ p : Lattice.LatticePlaquette ℓ 1, |unitLatticeCurvature A p| ^ 2)
    ≥ 1 / (12 * (S.d : ℝ) ^ 2) * ((S.L : ℝ) ^ (S.d + 1))⁻¹ * Lattice.latticeNorm S.d 1 A ^ 2
end Torus
end BlockSpin
namespace IntegerLattice
section Scaled
variable (S : Lattice.LatticeParameters)
def corridorCurvatureEnergy (A : EdgeForm S.d 1) (c : Edge S.d S.L) : ℝ :=
  ∑ᶠ p ∈ {p : Face S.d 1 | FaceInEdgeCorridor S p c}, |discreteCurl S.d A p| ^ 2
def AxialBound (Λ' : Set (ScaledSite S.d S.L)) (A : EdgeForm S.d 1) : Prop :=
  (S.L : ℝ) ^ (S.d - 2) * (∑ᶠ c ∈ edgesMeeting Λ', |blockAverage S A c| ^ 2)
      + (∑ᶠ p : Face S.d 1, |discreteCurl S.d A p| ^ 2)
    ≥ 1 / (12 * (S.d : ℝ) ^ 2) * ((S.L : ℝ) ^ (S.d + 1))⁻¹ * edgeNormSq A
end Scaled
end IntegerLattice
namespace BlockSpin
end BlockSpin
end YangMills.Construction

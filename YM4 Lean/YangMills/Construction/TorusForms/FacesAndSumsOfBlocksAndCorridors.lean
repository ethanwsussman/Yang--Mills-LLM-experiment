import YangMills.Construction.TorusForms.UnitLatticeAndBlockLattice
import Mathlib
noncomputable section
namespace YangMills.Construction.BlockSpin
open Finset YangMills.Construction.Lattice
variable (P : LatticeParameters) {ℓ : Fin P.d → ℝ} [PeriodsMultipleOfBlock P ℓ]
open Classical in
def blockDirectionalEnergy (A : Cochain1 ℓ 1) (y : LatticeSite ℓ (P.L : ℝ)) (μ : Fin P.d) : ℝ :=
  ∑ x ∈ univ.filter (fun x : LatticeSite ℓ 1 => LinkInside P (x, μ) (blockOf P 1 1 y)),
    |linkComponent A μ x| ^ 2
def blockEnergy (A : Cochain1 ℓ 1) (y : LatticeSite ℓ (P.L : ℝ)) : ℝ :=
  ∑ μ, blockDirectionalEnergy P A y μ
open Classical in
def blockCurvatureEnergy (A : Cochain1 ℓ 1) (y : LatticeSite ℓ (P.L : ℝ)) : ℝ :=
  ∑ p ∈ univ.filter (fun p : LatticePlaquette ℓ 1 => PlaquetteWithin P p (blockOf P 1 1 y)),
    |unitLatticeCurvature A p| ^ 2
open Classical in
def faceEnergy (A : Cochain1 ℓ 1) (F : Set (LatticeSite ℓ 1)) : ℝ :=
  ∑ b ∈ univ.filter (· ∈ linksWithin F), |A b| ^ 2
open Classical in
def corridorCurvatureEnergy (A : Cochain1 ℓ 1) (c : Link ℓ (P.L : ℝ)) : ℝ :=
  ∑ p ∈ univ.filter (fun p : LatticePlaquette ℓ 1 => PlaquetteInLinkCorridor P 1 p c),
    |unitLatticeCurvature A p| ^ 2
end YangMills.Construction.BlockSpin

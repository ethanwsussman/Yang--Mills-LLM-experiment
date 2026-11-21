import YangMills.Construction.LatticeFields.BlockAveraging
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
def IsInvOnSet {E : Type} (W : Set E) (B G : E → E) : Prop :=
  Set.MapsTo B W W ∧ Set.MapsTo G W W ∧ Set.InvOn G B W W
def invOnSet {E : Type} [Nonempty E] (W : Set E) (B : E → E) : E → E :=
  Classical.epsilon (IsInvOnSet W B)
def blockLapConst (d : ℕ) : ℝ := 6 * (d : ℝ) * 30 ^ d * 16 ^ (1 - (d : ℤ))
def blockMomentLowerBound (d : ℕ) : ℝ := (blockLapConst d + 1) ^ (-2 : ℤ)
variable {d N : ℕ} {κ : LatticeShape d}
def blockUnion (N : ℕ) (Y : Set (LatticeSite 1 κ)) : Set (LatticeSite N κ) :=
  ⋃ y ∈ Y, coarseBlock N y
def fieldsSupportedIn (X : Set (LatticeSite N κ)) : Set (ScalarField N κ) :=
  {f | ∀ x, x ∉ X → ScalarField.eval f x = 0}
def blockAvgKerIn (X : Set (LatticeSite N κ)) : Set (ScalarField N κ) :=
  {u | u ∈ fieldsSupportedIn X ∧ siteBlockAvg u = 0}
def massiveBlockLaplacian (f : ScalarField N κ) : ScalarField N κ :=
  tensorLaplacian f + siteBlockAvgAdj (siteBlockAvg f)
def compressedMassiveBlockLaplacian (X : Set (LatticeSite N κ)) (f : ScalarField N κ) :
    ScalarField N κ :=
  restrictSites X (massiveBlockLaplacian (restrictSites X f))
def dirichletBlockGreen (X : Set (LatticeSite N κ)) : ScalarField N κ → ScalarField N κ :=
  invOnSet (fieldsSupportedIn X) (compressedMassiveBlockLaplacian X)
def blockGreenMoment (X : Set (LatticeSite N κ)) (ω : ScalarField 1 κ) : ScalarField 1 κ :=
  siteBlockAvg (dirichletBlockGreen X (dirichletBlockGreen X (siteBlockAvgAdj ω)))
def blockGreenMomentInv (X : Set (LatticeSite N κ)) (Y : Set (LatticeSite 1 κ)) :
    ScalarField 1 κ → ScalarField 1 κ :=
  invOnSet (fieldsSupportedIn Y) (blockGreenMoment X)
def dirichletProjCompl (X : Set (LatticeSite N κ)) (Y : Set (LatticeSite 1 κ))
    (f : ScalarField N κ) : ScalarField N κ :=
  dirichletBlockGreen X (siteBlockAvgAdj (blockGreenMomentInv X Y (siteBlockAvg (dirichletBlockGreen X f))))
structure DirichletBlockProps (X : Set (LatticeSite N κ)) (Y : Set (LatticeSite 1 κ)) : Prop where
  green_inv :
    IsInvOnSet (fieldsSupportedIn X) (compressedMassiveBlockLaplacian X) (dirichletBlockGreen X)
  green_norm_le : ∀ g ∈ fieldsSupportedIn X,
    fieldNorm (latticeGrad (dirichletBlockGreen X g)) ^ 2 + fieldNorm (dirichletBlockGreen X g) ^ 2 ≤
      (d : ℝ) ^ 2 * fieldNorm g ^ 2
  moment_symm : ∀ ω ∈ fieldsSupportedIn Y, ∀ ω' ∈ fieldsSupportedIn Y,
    fieldInner ω' (blockGreenMoment X ω) = fieldInner (blockGreenMoment X ω') ω
  moment_lower : ∀ ω ∈ fieldsSupportedIn Y,
    blockMomentLowerBound d * fieldNorm ω ^ 2 ≤ fieldInner ω (blockGreenMoment X ω)
  moment_upper : ∀ ω ∈ fieldsSupportedIn Y,
    fieldInner ω (blockGreenMoment X ω) ≤ (d : ℝ) ^ 2 * fieldNorm ω ^ 2
  moment_inv : IsInvOnSet (fieldsSupportedIn Y) (blockGreenMoment X) (blockGreenMomentInv X Y)
  range_eq : compressedMassiveBlockLaplacian X '' blockAvgKerIn X =
    (fun u => restrictSites X (tensorLaplacian u)) '' blockAvgKerIn X
  isOrthProj : ∀ f ∈ fieldsSupportedIn X,
    IsOrthProj (compressedMassiveBlockLaplacian X '' blockAvgKerIn X) f
      (f - dirichletProjCompl X Y f)
def DirichletBlockFacts : Prop :=
  ∀ (d L k : ℕ), 2 ≤ d → 2 ≤ L → ∀ (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ),
    (∀ f : ScalarField (L ^ k) (LatticeShape.torus ℓ hℓ),
      (d : ℝ)⁻¹ * (fieldNorm (latticeGrad f) ^ 2 + fieldNorm f ^ 2) ≤
        fieldInner f (massiveBlockLaplacian f)) ∧
    (∀ Y : Set (LatticeSite 1 (LatticeShape.torus ℓ hℓ)), Y.Nonempty →
      DirichletBlockProps (blockUnion (L ^ k) Y) Y) ∧
    (∀ f : ScalarField (L ^ k) (LatticeShape.torus ℓ hℓ),
      kerLaplacianProjCompl f = dirichletProjCompl Set.univ Set.univ f)
end YangMills.Construction.LatticeFields

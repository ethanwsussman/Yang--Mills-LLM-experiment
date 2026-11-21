import YangMills.Construction.LatticeFields.FieldsAndDifferences
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
variable {d : ℕ} {κ : LatticeShape d}
def coarseBlock (N : ℕ) (y : LatticeSite 1 κ) : Set (LatticeSite N κ) := unitCube N y
def blockExitFace (N : ℕ) (y : LatticeSite 1 κ) (μ : Fin d) : Set (LatticeSite N κ) :=
  {x | ∃ (w : scaledIntLattice d 1) (v : scaledIntLattice d N), toSite 1 κ w = y ∧ toSite N κ v = x ∧
    (∀ ν, (w : Fin d → ℝ) ν ≤ (v : Fin d → ℝ) ν ∧ (v : Fin d → ℝ) ν < (w : Fin d → ℝ) ν + 1) ∧
    (v : Fin d → ℝ) μ = (w : Fin d → ℝ) μ + 1 - latticeSpacing N}
variable {N : ℕ}
def siteBlockAvg (f : ScalarField N κ) : ScalarField 1 κ :=
  fun y _ => ∑ᶠ x ∈ coarseBlock N y, latticeSpacing N ^ d * ScalarField.eval f x
def bondBlockAvg (A : LatticeOneForm N κ) : LatticeOneForm 1 κ :=
  fun y i => ∑ᶠ x ∈ coarseBlock N y, latticeSpacing N ^ d *
    ∑ j ∈ Finset.range N, latticeSpacing N *
      LatticeOneForm.coord A (i 0) (x + j • unitStep N κ (i 0))
def exitFaceAvg (A : LatticeOneForm N κ) : LatticeOneForm 1 κ :=
  fun y i => ∑ᶠ x ∈ blockExitFace N y (i 0), latticeSpacing N ^ (d - 1) * LatticeOneForm.coord A (i 0) x
def deltaField {I : Type} (x : LatticeSite N κ) (i : I) : LatticeField N κ I :=
  fun x' i' => ({(x, i)} : Set (LatticeSite N κ × I)).indicator 1 (x', i')
def fieldAdjointAt {M : ℕ} {I J : Type} (T : LatticeField N κ I → LatticeField M κ J)
    (ω : LatticeField M κ J) : LatticeField N κ I :=
  fun x i => (latticeSpacing N ^ d)⁻¹ * fieldInner (T (deltaField x i)) ω
def siteBlockAvgAdj (ω : ScalarField 1 κ) : ScalarField N κ :=
  fieldAdjointAt siteBlockAvg ω
def bondBlockAvgAdj (B : LatticeOneForm 1 κ) : LatticeOneForm N κ :=
  fieldAdjointAt bondBlockAvg B
def IsOrthProj {I : Type} (W : Set (LatticeField N κ I)) (f g : LatticeField N κ I) : Prop :=
  g ∈ W ∧ ∀ h ∈ W, fieldInner (f - g) h = 0
section Torus
variable {ℓ : Fin d → ℕ} {hℓ : ∀ μ, 1 ≤ ℓ μ}
def siteBlockAvgKer (N : ℕ) (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Set (ScalarField N (LatticeShape.torus ℓ hℓ)) :=
  {l | siteBlockAvg l = 0}
def laplacianImageKer (N : ℕ) (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Set (ScalarField N (LatticeShape.torus ℓ hℓ)) :=
  tensorLaplacian '' siteBlockAvgKer N ℓ hℓ
def kerLaplacianProj (f : ScalarField N (LatticeShape.torus ℓ hℓ)) :
    ScalarField N (LatticeShape.torus ℓ hℓ) :=
  Classical.epsilon (IsOrthProj (laplacianImageKer N ℓ hℓ) f)
def kerLaplacianProjCompl (f : ScalarField N (LatticeShape.torus ℓ hℓ)) :
    ScalarField N (LatticeShape.torus ℓ hℓ) :=
  f - kerLaplacianProj f
def massiveLaplacian (a : ℝ) (A : LatticeOneForm N (LatticeShape.torus ℓ hℓ)) :
    LatticeOneForm N (LatticeShape.torus ℓ hℓ) :=
  latticeCurlAdjoint (latticeCurl A) + latticeGrad (kerLaplacianProj (latticeDiv A)) +
    a • bondBlockAvgAdj (bondBlockAvg A)
def massiveLaplacianAlt (a : ℝ) (A : LatticeOneForm N (LatticeShape.torus ℓ hℓ)) :
    LatticeOneForm N (LatticeShape.torus ℓ hℓ) :=
  tensorLaplacian A - latticeGrad (kerLaplacianProjCompl (latticeDiv A)) +
    a • bondBlockAvgAdj (bondBlockAvg A)
end Torus
def massiveLaplacianUnit (a : ℝ) (A : LatticeOneForm 1 κ) : LatticeOneForm 1 κ :=
  latticeCurlAdjoint (latticeCurl A) + a • A
end YangMills.Construction.LatticeFields

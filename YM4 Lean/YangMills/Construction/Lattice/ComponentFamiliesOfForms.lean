import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def gridSideLength (L m : ℕ) (j : ℤ) : ℕ := 2 * L ^ ((m : ℤ) + j).toNat
def shiftedPoint (x : Site L m j) (n : Fin 4 → ℤ) : FourTorus L m :=
  (x : FourTorus L m) + ∑ ρ : Fin 4, pointOnAxis L m ρ ((n ρ : ℝ) * meshSize L j)
def covDerivTranspose (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2) (ν : Fin 4)
    (f : Site L m j → Matrices.ComplexMatrix2) (x : Site L m j) : Matrices.ComplexMatrix2 :=
  ((ξ⁻¹ : ℝ) : ℂ) •
    ((U (Bond.forwardFrom (x - unitStep L m j ν) ν))⁻¹ * f (x - unitStep L m j ν) *
      U (Bond.forwardFrom (x - unitStep L m j ν) ν) - f x)
abbrev AxisSiteFamily (L m : ℕ) (j : ℤ) : Type := Fin 4 → Site L m j → Matrices.ComplexMatrix2
abbrev PlaquetteFamily (L m : ℕ) (j : ℤ) : Type := Plaquette L m j → Matrices.ComplexMatrix2
abbrev plaquetteFamilyComponent (F : PlaquetteFamily L m j) (μ ν : Fin 4) :
    Site L m j → Matrices.ComplexMatrix2 :=
  plaquetteFormOf F μ ν
def axisFamilyGradient (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2)
    (g : Site L m j → Matrices.ComplexMatrix2) : AxisSiteFamily L m j :=
  fun μ => covDeriv ξ U μ g
def plaquetteFamilyExteriorDeriv (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2)
    (A : AxisSiteFamily L m j) : PlaquetteFamily L m j :=
  fun p => covDeriv ξ U p.firstAxis (A p.secondAxis) p.origin -
    covDeriv ξ U p.secondAxis (A p.firstAxis) p.origin
def axisFamilyInner (ξ : ℝ) (A B : AxisSiteFamily L m j) : ℂ :=
  ((ξ ^ 4 : ℝ) : ℂ) *
    ∑ᶠ x : Site L m j, ∑ μ : Fin 4, Matrices.ComplexMatrix2.halfTrace (A μ x * B μ x)
def plaquetteFamilyInner (ξ : ℝ) (F H : PlaquetteFamily L m j) : ℂ :=
  plaquetteFormInner ξ (plaquetteFamilyComponent F) (plaquetteFamilyComponent H)
abbrev MatrixPlaquetteForm (L m : ℕ) (j : ℤ) : Type := PlaquetteFamily L m j
def plaquetteFamilyOfComponents (F : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2) :
    PlaquetteFamily L m j :=
  fun p => F p.firstAxis p.secondAxis p.origin
theorem bondFormInner_eq_axisFamilyInner (ξ : ℝ) (A B : Bond L m j → Matrices.ComplexMatrix2) :
    bondFormInner ξ A B = axisFamilyInner ξ (bondFormComponent A) (bondFormComponent B) := rfl
theorem plaquetteFormInner_eq_plaquetteFamilyInner (ξ : ℝ)
    (F H : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2) :
    plaquetteFormInner ξ F H =
      plaquetteFamilyInner ξ (plaquetteFamilyOfComponents F) (plaquetteFamilyOfComponents H) := by
  simp only [plaquetteFamilyInner, plaquetteFormInner]
  refine congrArg (_ * ·) (finsum_congr fun x =>
    Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν hν => ?_)
  have h : μ < ν := Finset.mem_Ioi.mp hν
  simp [plaquetteFamilyComponent, plaquetteFormOf, plaquetteFamilyOfComponents, h]
end PeriodicLattice
end YangMills.Construction

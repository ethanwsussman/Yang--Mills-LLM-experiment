import YangMills.Construction.Lattice.AxialGauges
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def toFourTorus (L m : ℕ) (x : Fin 4 → ℝ) : FourTorus L m :=
  fun μ => (x μ : AddCircle (torusSide L m))
def IsInducedByAffine (σ : FourTorus L m ≃ FourTorus L m) (r : SignedFrame) (v : Fin 4 → ℝ) :
    Prop :=
  ∀ x : Fin 4 → ℝ, σ (toFourTorus L m x) = toFourTorus L m (r.actOnVector x + v)
def meshVectors (L : ℕ) (i : ℤ) : Set (Fin 4 → ℝ) :=
  {v | ∃ n : Fin 4 → ℤ, ∀ μ, v μ = (n μ : ℝ) * meshSize L i}
def latticeIsometries (L m : ℕ) (i : ℤ) : Set (FourTorus L m ≃ FourTorus L m) :=
  {σ | ∃ r : SignedFrame, ∃ v ∈ meshVectors L i, IsInducedByAffine σ r v}
def HasLinearPart (σ : FourTorus L m ≃ FourTorus L m) (r : SignedFrame) : Prop :=
  ∃ v : Fin 4 → ℝ, IsInducedByAffine σ r v
def linearComponent (σ : FourTorus L m ≃ FourTorus L m) : SignedFrame :=
  open Classical in if h : ∃ r : SignedFrame, HasLinearPart σ r then h.choose else 1
def IsTorusTranslation (σ : FourTorus L m ≃ FourTorus L m) : Prop := HasLinearPart σ 1
def sitePreimage (σ : FourTorus L m ≃ FourTorus L m) (y : Site L m j) : Site L m j :=
  Classical.epsilon fun x : Site L m j => (x : FourTorus L m) = σ.symm y
def bondImage (σ : FourTorus L m ≃ FourTorus L m) (b : Bond L m j) : Bond L m j :=
  bondPreimage σ.symm b
def pathImage (σ : FourTorus L m ≃ FourTorus L m) (Γ : List (Bond L m j)) : List (Bond L m j) :=
  Γ.map (bondImage σ)
def plaquetteImage (σ : FourTorus L m ≃ FourTorus L m) (p : Plaquette L m j) : Plaquette L m j :=
  open Classical in
  if h : ∃ p' : Plaquette L m j, p'.face = σ '' p.face then h.choose else p
def transportSiteFunction {α : Type*} (σ : FourTorus L m ≃ FourTorus L m) (u : Site L m j → α) :
    Site L m j → α :=
  fun x => u (sitePreimage σ x)
def transportTorusFunction {α : Type*} (σ : FourTorus L m ≃ FourTorus L m)
    (f : FourTorus L m → α) : FourTorus L m → α :=
  fun x => f (σ.symm x)
def transportPlaquetteFunction {α : Type*} (σ : FourTorus L m ≃ FourTorus L m)
    (f : Plaquette L m j → α) : Plaquette L m j → α :=
  fun p => f (plaquetteImage σ.symm p)
def transportMeasure (σ : FourTorus L m ≃ FourTorus L m)
    (ν : Measure (Bond L m j → Matrices.ComplexMatrix2)) :
    Measure (Bond L m j → Matrices.ComplexMatrix2) :=
  ν.map (transportGaugeField σ)
def transportForm (σ : FourTorus L m ≃ FourTorus L m) (A : Bond L m j → Matrices.ComplexMatrix2) :
    Bond L m j → Matrices.ComplexMatrix2 :=
  fun b' => A (bondPreimage σ b')
def twistedFormValue (σ : FourTorus L m ≃ FourTorus L m)
    (V₀ A : Bond L m j → Matrices.ComplexMatrix2) (b' : Bond L m j) : Matrices.ComplexMatrix2 :=
  open Classical in
  if (bondPreimage σ b').IsPositivelyOriented then A (bondPreimage σ b')
  else -Matrices.ComplexMatrix2.conjugateBy (V₀ (bondPreimage σ b').opposite)⁻¹
    (A (bondPreimage σ b').opposite)
def twistedTransportForm (σ : FourTorus L m ≃ FourTorus L m)
    (V₀ A : Bond L m j → Matrices.ComplexMatrix2) : Bond L m j → Matrices.ComplexMatrix2 :=
  open Classical in
  fun b' => if b'.IsPositivelyOriented then twistedFormValue σ V₀ A b'
    else -twistedFormValue σ V₀ A b'.opposite
end PeriodicLattice
end YangMills.Construction

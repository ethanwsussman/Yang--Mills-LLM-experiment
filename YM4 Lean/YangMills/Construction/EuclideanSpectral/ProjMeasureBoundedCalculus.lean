import YangMills.Construction.EuclideanSpectral.ProjMeasureBoundedIntegral
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanSpectral
namespace ProjMeasure
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
  [NeZero n]
def IsBoundedBorelFn (f : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
def homeoImage
    (κ : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)) (B : BorelSubset n) : BorelSubset n :=
  ⟨κ '' B.1, κ.toMeasurableEquiv.measurableSet_image.2 B.2⟩
def fnDomainSet (E : ProjMeasure H n) (u : EuclideanSpace ℝ (Fin n) → ℂ) : Set H :=
  {ψ | ∫⁻ x, ‖u x‖ₑ ^ 2 ∂(E.diagMeasure ψ) < ⊤}
def fnDomain (E : ProjMeasure H n) (u : EuclideanSpace ℝ (Fin n) → ℂ) : Submodule ℂ H :=
  Classical.epsilon fun S : Submodule ℂ H => (S : Set H) = E.fnDomainSet u
def truncIntegral (E : ProjMeasure H n) (u : EuclideanSpace ℝ (Fin n) → ℂ)
    (k : ℕ) : H →ₗ[ℂ] H :=
  E.boundedIntegral ({x | ‖u x‖ ≤ (k : ℝ)}.indicator u)
def IsTruncLimit (E : ProjMeasure H n)
    (u : EuclideanSpace ℝ (Fin n) → ℂ) (A : E.fnDomain u →ₗ[ℂ] H) : Prop :=
  ∀ ψ : E.fnDomain u,
    Tendsto (fun k : ℕ => E.truncIntegral u (k + 1) (ψ : H)) atTop (𝓝 (A ψ))
def truncLimit (E : ProjMeasure H n)
    (u : EuclideanSpace ℝ (Fin n) → ℂ) : E.fnDomain u →ₗ[ℂ] H :=
  Classical.epsilon (E.IsTruncLimit u)
def LinearAndIndicator (E : ProjMeasure H n) : Prop :=
  (∀ (f g : EuclideanSpace ℝ (Fin n) → ℂ) (z : ℂ), IsBoundedBorelFn f → IsBoundedBorelFn g →
    E.boundedIntegral (f + z • g) = E.boundedIntegral f + z • E.boundedIntegral g) ∧
  (∀ B : BorelSubset n, E.boundedIntegral (B.1.indicator fun _ => 1) = E B) ∧
  E.boundedIntegral (fun _ => 1) = LinearMap.id
def NormBoundsNullSets (E : ProjMeasure H n) : Prop :=
  (∀ (f : EuclideanSpace ℝ (Fin n) → ℂ), IsBoundedBorelFn f → ∀ ψ : H,
    ‖E.boundedIntegral f ψ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(E.diagMeasure ψ)) ∧
  (∀ f g : EuclideanSpace ℝ (Fin n) → ℂ, IsBoundedBorelFn f → IsBoundedBorelFn g →
    (∃ N : BorelSubset n, E.IsNull N ∧ ∀ x, x ∉ N.1 → f x = g x) →
      E.boundedIntegral f = E.boundedIntegral g) ∧
  (∀ (f : EuclideanSpace ℝ (Fin n) → ℂ), IsBoundedBorelFn f → ∀ B : BorelSubset n, Supports B E →
    E.boundedIntegral f = E.boundedIntegralOn B f ∧
    ∃ T : H →L[ℂ] H, (T : H →ₗ[ℂ] H) = E.boundedIntegral f ∧ ‖T‖ ≤ sSup ((fun x => ‖f x‖) '' B.1))
def MulIntegral (E : ProjMeasure H n) : Prop :=
  ∀ f g : EuclideanSpace ℝ (Fin n) → ℂ, IsBoundedBorelFn f → IsBoundedBorelFn g →
    E.boundedIntegral (f * g) = E.boundedIntegral f ∘ₗ E.boundedIntegral g
def ConjIntegral (E : ProjMeasure H n) : Prop :=
  ∀ (f : EuclideanSpace ℝ (Fin n) → ℂ), IsBoundedBorelFn f → ∀ φ ψ : H,
    inner ℂ (E.boundedIntegral (fun x => conj (f x)) φ) ψ = inner ℂ φ (E.boundedIntegral f ψ)
def UnitaryIntegral (E : ProjMeasure H n) : Prop :=
  ∀ (f : EuclideanSpace ℝ (Fin n) → ℂ), IsBoundedBorelFn f → ∀ B : BorelSubset n, Supports B E →
    (∀ x ∈ B.1, ‖f x‖ = 1) →
      ∃ hU : IsUnitaryMap (E.boundedIntegral f), hU.inv = E.boundedIntegral fun x => conj (f x)
def HomeoUnitaryTransport (E : ProjMeasure H n) : Prop :=
  ∀ (U : H →ₗ[ℂ] H) (hU : IsUnitaryMap U)
    (κ : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)),
    ∃ E' : ProjMeasure H n,
      (∀ B : BorelSubset n, E' B = hU.inv ∘ₗ E (homeoImage κ B) ∘ₗ U) ∧
      (∀ (ψ : H) (B : BorelSubset n), E'.diag ψ B = E.diag (U ψ) (homeoImage κ B)) ∧
      ∀ (f : EuclideanSpace ℝ (Fin n) → ℂ), IsBoundedBorelFn f →
        E'.boundedIntegral f = hU.inv ∘ₗ E.boundedIntegral (f ∘ κ.symm) ∘ₗ U
def UnboundedFunctions (E : ProjMeasure H n) : Prop :=
  ∀ u : EuclideanSpace ℝ (Fin n) → ℂ, Measurable u →
    ((E.fnDomain u : Submodule ℂ H) : Set H) = E.fnDomainSet u ∧
    E.IsTruncLimit u (E.truncLimit u) ∧
    (∀ ψ : E.fnDomain u, ‖E.truncLimit u ψ‖ ^ 2 =
      ∫ x, ‖u x‖ ^ 2 ∂(E.diagMeasure (ψ : H))) ∧
    ∀ B : BorelSubset n, Supports B E → (∃ c : ℝ, ∀ x ∈ B.1, ‖u x‖ ≤ c) →
      E.fnDomainSet u = univ ∧
      ∀ ψ : E.fnDomain u, E.truncLimit u ψ = E.boundedIntegralOn B u (ψ : H)
end ProjMeasure
def ProjMeasureBoundedCalculus : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) [NeZero n]
    (E : ProjMeasure H n),
    E.LinearAndIndicator ∧ E.NormBoundsNullSets ∧ E.MulIntegral ∧
    E.ConjIntegral ∧ E.UnitaryIntegral ∧ E.HomeoUnitaryTransport ∧
    E.UnboundedFunctions
end YangMills.Construction.EuclideanSpectral

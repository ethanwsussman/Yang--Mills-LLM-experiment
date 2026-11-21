import YangMills.Construction.Continuum.FunctionsNormsBallsAndNeighbourhoods
import YangMills.Construction.Continuum.IsometriesOfFourSpaceAndOfATorusReflectionsAndInducedMaps
import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction.TorusTransport.AffineGroup
def integerPoints : Set (Fin 4 → ℝ) := Set.range fun (k : Fin 4 → ℤ) (μ : Fin 4) => (k μ : ℝ)
def IsOrthogonalLinear (w : (Fin 4 → ℝ) → Fin 4 → ℝ) : Prop :=
  ∃ R ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∀ x, w x = R *ᵥ x
def IsHyperoctahedralMotion (g : (Fin 4 → ℝ) → Fin 4 → ℝ) : Prop :=
  ∃ R ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∃ b : Fin 4 → ℝ,
    g = orthoAffine R b ∧ ∃ w : hyperoctahedral, ∀ x, w.1 x = R *ᵥ x
def IsCompositionGroup (G : Set ((Fin 4 → ℝ) → Fin 4 → ℝ)) : Prop :=
  id ∈ G ∧ (∀ g ∈ G, ∀ h ∈ G, g ∘ h ∈ G) ∧ ∀ g ∈ G, ∃ h ∈ G, g ∘ h = id ∧ h ∘ g = id
def HyperoctahedralPreservesLattices (D : TransportData) : Prop :=
  ∀ w : hyperoctahedral,
    IsOrthogonalLinear w.1 ∧
      w.1 '' integerPoints = integerPoints ∧
      w.1 '' (D.periods : Set (Fin 4 → ℝ)) = D.periods ∧
      ∀ r : ℝ, 0 < r → w.1 '' openBallZero r = openBallZero r
def AffineMotionsGroup : Prop :=
  (∀ g, g ∈ affineHyperoctahedral ↔ IsHyperoctahedralMotion g) ∧
    IsCompositionGroup affineHyperoctahedral ∧
    (∀ b, ⇑(translationEquiv b) ∈ affineHyperoctahedral) ∧
    (∀ w : hyperoctahedral, ⇑w.1 ∈ affineHyperoctahedral) ∧
    ∀ (μ : Fin 4) (c : ℝ), hyperplaneReflect μ c ∈ affineHyperoctahedral
def MotionsDescendToIsometries (D : TransportData) : Prop :=
  ∀ g ∈ affineHyperoctahedral, ∀ (R : hyperoctahedral) (b : Fin 4 → ℝ), g = affinePair b R →
    R.1 '' (D.periods : Set (Fin 4 → ℝ)) = D.periods ∧
      (∃! Φ : D.Torus → D.Torus, Φ ∘ D.projHom = D.projHom ∘ g) ∧
      D.torusMap g ∘ D.projHom = D.projHom ∘ g ∧
      D.IsTorusIsometry (D.torusMap g)
def DescendedGenerators (D : TransportData) : Prop :=
  (∀ b, D.torusMap (translationEquiv b) = fun ξ => ξ + D.projHom b) ∧
    (∀ w : hyperoctahedral, D.torusMap w.1 = D.hyperoctahedralOnTorus w ∧
      ∀ x, D.torusMap w.1 (D.projHom x) = D.projHom (w.1 x)) ∧
    ∀ (μ : Fin 4) (c : ℝ), D.torusMap (hyperplaneReflect μ c) = D.torusReflect μ c ∧
      ∀ x, D.torusMap (hyperplaneReflect μ c) (D.projHom x) = D.projHom (hyperplaneReflect μ c x)
def AffineGroupOnTori : Prop :=
  ∀ D : TransportData,
    HyperoctahedralPreservesLattices D ∧
      AffineMotionsGroup ∧
      MotionsDescendToIsometries D ∧
      DescendedGenerators D
end YangMills.Construction.TorusTransport.AffineGroup
end

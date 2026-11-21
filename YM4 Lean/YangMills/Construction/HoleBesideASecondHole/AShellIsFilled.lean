import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGauge
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace ShellFilling
open BlockAverages LatticeFractionalIntegration
def IsWithinSupDist (o : Fin 4 → ℝ) (r : ℝ) (x : LatticeFractionalIntegration.Lattice4) : Prop :=
  ∀ i, |(x i : ℝ) - o i| ≤ r
def IsBeyondSupDist (o : Fin 4 → ℝ) (r : ℝ) (x : LatticeFractionalIntegration.Lattice4) : Prop :=
  ∃ i, r ≤ |(x i : ℝ) - o i|
def plaquetteDefect (P : Finset LatticeFractionalIntegration.Lattice4)
    (X : LatticeFractionalIntegration.Lattice4 → Fin 4 → BlockAverages.UnitQuaternion) : ℝ :=
  ∑ p ∈ orientedPlaquettesOf P,
    ‖((latticePlaquette X p.1 p.2.1 p.2.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2
def shellFillingStatement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (l : ℝ) (o : Fin 4 → ℝ) (D Sh : Finset LatticeFractionalIntegration.Lattice4)
    (X : LatticeFractionalIntegration.Lattice4 → Fin 4 → BlockAverages.UnitQuaternion) (ε : ℝ),
    100 ≤ l → (∀ x, x ∈ D ↔ IsWithinSupDist o (1.95 * l) x) → (∀ x, x ∈ Sh ↔ x ∈ D ∧ IsBeyondSupDist o l x) →
    0 ≤ ε → ε ^ 2 ≤ c → plaquetteDefect Sh X ≤ ε ^ 2 →
    ∃ X' : LatticeFractionalIntegration.Lattice4 → Fin 4 → BlockAverages.UnitQuaternion,
      (∀ b ∈ bondsOf D, IsBeyondSupDist o (1.9 * l) b.1 → IsBeyondSupDist o (1.9 * l) (b.1 + basisVector b.2) →
        X' b.1 b.2 = X b.1 b.2) ∧
      plaquetteDefect D X' ≤ C * ε ^ 2
end ShellFilling
end YangMills.Construction
end

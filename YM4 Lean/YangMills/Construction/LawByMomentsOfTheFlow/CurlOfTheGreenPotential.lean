import YangMills.Construction.LawByMomentsOfTheFlow.PotentialOfAPlaquetteByAGreenFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open PeriodicLattice.ShortDistanceTwoPoint
open Classical in
def curlGreenPotentialStatement : Prop :=
  ∀ (A : Type) [CommRing A] (g : (Fin 4 → A) → ℝ) (y : Fin 4 → A) (q : CyclicFormula.OrderedDirectionPair),
    (∀ (x : Fin 4 → A) (r : CyclicFormula.OrderedDirectionPair),
      plaquetteCurlAt (greenPlaquettePotential g y q.1.1 q.1.2) x r.1.1 r.1.2 =
        planePairEntry (secondDiffMatrix g (x - y)) r q) ∧
    ∀ κ : ℝ, (∀ z : Fin 4 → A, discreteLaplacian g z = (if z = 0 then 1 else 0) - κ) →
      ∀ B : (Fin 4 → A) → Fin 4 → ℝ, (Function.support (Function.uncurry B)).Finite →
        ∑' x : Fin 4 → A, ∑ r : CyclicFormula.OrderedDirectionPair,
            plaquetteCurlAt (greenPlaquettePotential g y q.1.1 q.1.2) x r.1.1 r.1.2 *
              plaquetteCurlAt B x r.1.1 r.1.2 =
          plaquetteCurlAt B y q.1.1 q.1.2
end YangMills.Construction.MomentLaw
end

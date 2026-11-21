import YangMills.Construction.LawByMomentsOfTheFlow.PotentialOfAPlaquetteByAGreenFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint
def curvaturePairingSummationByParts : Prop :=
  ∀ (A : Type) [CommRing A] (F : (Fin 4 → A) → Fin 4 → Fin 4 → ℝ) (B : (Fin 4 → A) → Fin 4 → ℝ),
    (∀ x a b, F x a b = -F x b a) →
    (∀ (a b c : Fin 4) (u : Fin 4 → A), Summable fun x => F (x - u) a b * B x c) →
    ∑' x, ∑ r : YangMills.Construction.CyclicFormula.OrderedDirectionPair, F x r.1.1 r.1.2 * plaquetteCurlAt B x r.1.1 r.1.2 =
      ∑' x, ∑ μ, B x μ * ∑ ν, (F x μ ν - F (x - unitVector ν) μ ν)
end YangMills.Construction.MomentLaw
end

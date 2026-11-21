import YangMills.Construction.InfiniteLattice.FactsOfTheGaugeTransformationsAtEverySpacing
import YangMills.Construction.InfiniteLattice.TraceOnTheGroupAndOneBondWeightProof
import YangMills.Construction.ReflectionPositivity.CovarianceAlgebraAndLocalisationOfTheRepresentativesProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace GaugeTransformFacts
variable {a : ℝ}
def inv (g : GaugeTransform a) : GaugeTransform a where
  toFun x := (g.toFun x)⁻¹
  finite_ne_one := g.finite_ne_one.subset fun x hx hone => hx (by
    have hx₁ : g.toFun x = 1 := hone
    rw [hx₁, inv_one])
theorem act_apply (g : GaugeTransform a) (U : GaugeField a) (ℓ : Link a) :
    g.act U ℓ = g.toFun ℓ.initial * U ℓ * (g.toFun ℓ.terminal)⁻¹ := rfl
theorem continuous_eval (ℓ : Link a) : Continuous fun U : GaugeField a => U ℓ := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem continuous_act (g : GaugeTransform a) : Continuous g.act :=
  continuous_induced_rng.2 (continuous_pi fun ℓ =>
    (continuous_const.mul (continuous_eval ℓ)).mul continuous_const)
theorem mul_act (g g' : GaugeTransform a) (U : GaugeField a) :
    (g * g').act U = g.act (g'.act U) := by
  refine Subtype.ext (funext fun ℓ => ?_)
  change g.toFun ℓ.initial * g'.toFun ℓ.initial * U ℓ * (g.toFun ℓ.terminal * g'.toFun ℓ.terminal)⁻¹ =
    g.toFun ℓ.initial * (g'.toFun ℓ.initial * U ℓ * (g'.toFun ℓ.terminal)⁻¹) * (g.toFun ℓ.terminal)⁻¹
  simp only [mul_inv_rev, mul_assoc]
theorem inv_act_act (g : GaugeTransform a) (U : GaugeField a) :
    (inv g).act (g.act U) = U := by
  refine Subtype.ext (funext fun ℓ => ?_)
  change (g.toFun ℓ.initial)⁻¹ * (g.toFun ℓ.initial * U ℓ * (g.toFun ℓ.terminal)⁻¹) *
    ((g.toFun ℓ.terminal)⁻¹)⁻¹ = U ℓ
  group
theorem act_inv_act (g : GaugeTransform a) (U : GaugeField a) :
    g.act ((inv g).act U) = U := by
  refine Subtype.ext (funext fun ℓ => ?_)
  change g.toFun ℓ.initial * ((g.toFun ℓ.initial)⁻¹ * U ℓ * ((g.toFun ℓ.terminal)⁻¹)⁻¹) *
    (g.toFun ℓ.terminal)⁻¹ = U ℓ
  group
def actHomeomorph (g : GaugeTransform a) : GaugeField a ≃ₜ GaugeField a where
  toFun := g.act
  invFun := (inv g).act
  left_inv := inv_act_act g
  right_inv := act_inv_act g
  continuous_toFun := continuous_act g
  continuous_invFun := continuous_act (inv g)
theorem faceHolonomy_act (g : GaugeTransform a) (U : GaugeField a)
    (p : ElementaryPlaquette a) :
    faceHolonomy (g.act U) p =
      g.toFun p.corner * faceHolonomy U p * (g.toFun p.corner)⁻¹ := by
  have hc : g.toFun (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis) =
      g.toFun (p.corner + axisStep a p.highAxis + axisStep a p.lowAxis) :=
    congrArg g.toFun (add_right_comm _ _ _)
  simp only [faceHolonomy, act_apply, Link.forwardFrom]
  rw [hc]
  group
theorem fullTrace_conj (g X : Matrices.ComplexMatrix2.specialUnitary) :
    Matrices.ComplexMatrix2.fullTrace ((g * X * g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
      Matrices.ComplexMatrix2) = Matrices.ComplexMatrix2.fullTrace (X : Matrices.ComplexMatrix2) := by apply _root_.YangMills.Construction.InfiniteLattice.SUTwoTrace.fullTrace_conj <;> assumption
theorem faceEnergy_act (g : GaugeTransform a) (U : GaugeField a)
    (p : ElementaryPlaquette a) : faceEnergy (g.act U) p = faceEnergy U p := by
  simp only [faceEnergy, faceHolonomy_act, fullTrace_conj]
end GaugeTransformFacts
open GaugeTransformFacts in
theorem gaugeTransformPropertiesForAllSpacings_holds :
    GaugeTransformPropertiesForAllSpacings := by
  intro a _ g g'
  refine ⟨fun U ℓ => (g.act U).2 ℓ, faceHolonomy_act g, fun p => ?_, mul_act g g',
    (actHomeomorph g).isHomeomorph, fun F hF => ⟨?_, ?_⟩⟩
  · exact funext fun U => faceEnergy_act g U p
  · obtain ⟨hm, C, hC⟩ := hF
    exact ⟨hm.comp (continuous_act g).measurable, C, fun U => hC _⟩
  · exact funext fun U => congrArg F (mul_act g g' U)
end YangMills.Construction.InfiniteLattice

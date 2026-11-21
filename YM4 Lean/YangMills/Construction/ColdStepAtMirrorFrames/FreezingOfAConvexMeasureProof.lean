import YangMills.Construction.ColdStepAtMirrorFrames.FreezingOfAConvexMeasure
import YangMills.Construction.ColdStepAtMirrorFrames.FrozenMeasureSplits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem ballExpectationFreezingBound_holds (hTorus : FreezingBoundOnTorus)
    (hBlock : BlockComparisonBound) (hSplit : FrozenPotentialExpectationFactorizes) :
    BallExpectationFreezingBound := by
  intro ι ι' P P' _ _ _ _ _ _ _ _ ρ r S lam x c ε R p pos D Ψ H θ Y pos' D' Ψ' H' θ' Y' Λ Λ' e M M' φ
    hρ hr hlam hx hc hε hR hp hD hD' hΨ hΨ' hS hSp hS2 hSp2 hθ hsum hθ' hsum' hH hH' hΛ hΛ' hdist hY
    hfar hfar' hcomp hval
  have hLeft := hTorus ι P ρ r S lam x c R p pos D Ψ H θ Y Λ hρ hr hlam hx hc hR hp hD hΨ hS hSp hθ hsum
    hH hΛ
  have hRight := hTorus ι' P' ρ r S lam x c R p pos' D' Ψ' H' θ' Y' Λ' hρ hr hlam hx hc hR hp hD' hΨ'
    hS2 hSp2 hθ' hsum' hH' hΛ'
  have hΨcont : Continuous Ψ := by
    obtain ⟨K, hK, _⟩ := hΨ
    exact hK.smooth.continuous
  have hΨcont' : Continuous Ψ' := by
    obtain ⟨K, hK, _⟩ := hΨ'
    exact hK.smooth.continuous
  have hCoupling : 0 ≤ x * lam := by positivity
  have hSplitLeft := hSplit ι ↥Λ Λ (Equiv.refl _) ρ (x * lam) p Ψ H hρ hp hΨcont hCoupling
  have hSplitRight := hSplit ι' ↥Λ Λ' e ρ (x * lam) p Ψ' H' hρ hp hΨcont' hCoupling
  have hMiddle := hBlock ι ι' ↥Λ P P' ρ r S lam x c ε R p pos D Ψ H θ Y pos' D' Ψ' H' θ' Y'
    (fun k => k.1) (fun k => (e k).1) M M' φ hρ hr hlam hx hc hε hR hp hD hD' hΨ hΨ' hS hSp hS2 hSp2
    hθ hsum hθ' hsum' hH hH' Subtype.val_injective
    (fun a b h => e.injective (Subtype.ext h)) hdist hY hfar hfar' hcomp hval
  have hSplitLeft' : ballExpectation (cutoffFactor ρ p) (frozenPotential Λ (x * lam) Ψ)
      (fun η => H (restrictToBonds Λ η)) =
      ballExpectation (cutoffFactor ρ p) (fun ξ : BondField ↥Λ => Ψ (pushforwardField (fun k => k.1) ξ))
        (fun ξ => H (pushforwardField (fun k : ↥Λ => k.1) ξ)) := hSplitLeft
  rw [hSplitLeft'] at hLeft
  rw [hSplitRight] at hRight
  set a := ballExpectation (cutoffFactor ρ p) Ψ H
  set a' := ballExpectation (cutoffFactor ρ p) Ψ' H'
  set b := ballExpectation (cutoffFactor ρ p)
    (fun ξ : BondField ↥Λ => Ψ (pushforwardField (fun k => k.1) ξ))
    (fun ξ => H (pushforwardField (fun k : ↥Λ => k.1) ξ))
  set b' := ballExpectation (cutoffFactor ρ p)
    (fun ξ : BondField ↥Λ => Ψ' (pushforwardField (fun k => (e k).1) ξ))
    (fun ξ => H' (pushforwardField (fun k => (e k).1) ξ))
  have hTriangle : |a - a'| ≤ |a - b| + |b' - b| + |a' - b'| := by
    have hSplitDiff : a - a' = (a - b) - (b' - b) - (a' - b') := by ring
    rw [hSplitDiff]
    refine (abs_sub _ _).trans ?_
    exact add_le_add (abs_sub _ _) le_rfl
  refine hTriangle.trans ?_
  have hRegroup : c ^ 2 * (2 * freezingConstant lam S * Real.exp (-(r * R / 16)) +
      blockComparisonConstant lam S * (ε + Real.exp (-(r * R / 32)))) =
      c ^ 2 * freezingConstant lam S * Real.exp (-(r * R / 16)) +
        c ^ 2 * blockComparisonConstant lam S * (ε + Real.exp (-(r * R / 32))) +
        c ^ 2 * freezingConstant lam S * Real.exp (-(r * R / 16)) := by ring
  rw [hRegroup]
  exact add_le_add (add_le_add hLeft hMiddle) hRight
end YangMills.Construction.ColdStepAtMirrorFrames
end

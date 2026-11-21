import YangMills.Construction.ResponseInTheExpansion.TraceOfTheFourPointKernelProof
import YangMills.Construction.LawByMomentsOfTheFlow.PairingOfACurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint
private theorem sum_orderedDirectionPair (f : Fin 4 → Fin 4 → ℝ) :
    ∑ r : CyclicFormula.OrderedDirectionPair, f r.1.1 r.1.2 =
      f 0 1 + f 0 2 + f 0 3 + f 1 2 + f 1 3 + f 2 3 := by apply _root_.YangMills.DeltaSharedProofs.p501869 <;> assumption
theorem curvaturePairingSummationByParts_holds : curvaturePairingSummationByParts := by
  intro A _ F B hF hs
  have hs0 : ∀ a b c : Fin 4, Summable fun x => F x a b * B x c := fun a b c => by
    simpa using hs a b c 0
  set P : Fin 4 → Fin 4 → ℝ := fun μ ν => ∑' x, F x μ ν * B x μ with hP
  set Q : Fin 4 → Fin 4 → ℝ := fun μ ν => ∑' x, F (x - unitVector ν) μ ν * B x μ with hQ
  have sP : ∀ μ ν, HasSum (fun x => F x μ ν * B x μ) (P μ ν) := fun μ ν => (hs0 μ ν μ).hasSum
  have sQ : ∀ μ ν, HasSum (fun x => F (x - unitVector ν) μ ν * B x μ) (Q μ ν) := fun μ ν =>
    (hs μ ν μ _).hasSum
  have shift : ∀ μ ν : Fin 4, HasSum (fun x => F x μ ν * B (x + unitVector ν) μ) (Q μ ν) := by
    intro μ ν
    have h := ((Equiv.addRight (unitVector ν : Fin 4 → A)).hasSum_iff).2 (sQ μ ν)
    simpa [Function.comp_def] using h
  have term : ∀ a b : Fin 4, HasSum (fun x => F x a b * plaquetteCurlAt B x a b)
      (P a b + P b a - Q a b - Q b a) := by
    intro a b
    have s2 : HasSum (fun x => F x a b * B (x + unitVector a) b) (-Q b a) := by
      have h := (shift b a).neg
      have e : (fun x => -(F x b a * B (x + unitVector a) b)) =
          fun x => F x a b * B (x + unitVector a) b := by
        funext x
        rw [hF x a b]
        ring
      rwa [e] at h
    have s3 := shift a b
    have s4 : HasSum (fun x => F x a b * B x b) (-P b a) := by
      have h := (sP b a).neg
      have e : (fun x => -(F x b a * B x b)) = fun x => F x a b * B x b := by
        funext x
        rw [hF x a b]
        ring
      rwa [e] at h
    have h := (((sP a b).add s2).sub s3).sub s4
    have e : (fun x => F x a b * B x a + F x a b * B (x + unitVector a) b -
        F x a b * B (x + unitVector b) a - F x a b * B x b) = fun x => F x a b * plaquetteCurlAt B x a b := by
      funext x
      unfold plaquetteCurlAt
      ring
    rw [e] at h
    have e2 : P a b + P b a - Q a b - Q b a = P a b + -Q b a - Q a b - -P b a := by
      generalize P a b = p1
      generalize P b a = p2
      generalize Q a b = q1
      generalize Q b a = q2
      ring
    rw [e2]
    exact h
  have hL : HasSum (fun x => ∑ r : CyclicFormula.OrderedDirectionPair,
        F x r.1.1 r.1.2 * plaquetteCurlAt B x r.1.1 r.1.2)
      (∑ r : CyclicFormula.OrderedDirectionPair,
        (P r.1.1 r.1.2 + P r.1.2 r.1.1 - Q r.1.1 r.1.2 - Q r.1.2 r.1.1)) :=
    hasSum_sum fun r _ => term r.1.1 r.1.2
  have hR : HasSum (fun x => ∑ μ, B x μ * ∑ ν, (F x μ ν - F (x - unitVector ν) μ ν))
      (∑ μ, ∑ ν, (P μ ν - Q μ ν)) := by
    have h : HasSum (fun x => ∑ μ, ∑ ν, (F x μ ν * B x μ - F (x - unitVector ν) μ ν * B x μ))
        (∑ μ, ∑ ν, (P μ ν - Q μ ν)) :=
      hasSum_sum fun μ _ => hasSum_sum fun ν _ => (sP μ ν).sub (sQ μ ν)
    have e : (fun x => ∑ μ, ∑ ν, (F x μ ν * B x μ - F (x - unitVector ν) μ ν * B x μ)) =
        fun x => ∑ μ, B x μ * ∑ ν, (F x μ ν - F (x - unitVector ν) μ ν) := by
      funext x
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      ring
    rwa [e] at h
  have hd : ∀ x a, F x a a = 0 := fun x a => by
    have := hF x a a
    linarith
  have hP0 : ∀ a, P a a = 0 := fun a => by
    simp [hP, hd]
  have hQ0 : ∀ a, Q a a = 0 := fun a => by
    simp [hQ, hd]
  rw [hL.tsum_eq, hR.tsum_eq,
    sum_orderedDirectionPair (fun a b => P a b + P b a - Q a b - Q b a)]
  simp only [Fin.sum_univ_four, hP0, hQ0]
  ring
end YangMills.Construction.MomentLaw
end

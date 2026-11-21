import YangMills.Construction.SpectralTheory.FunctionsOfSelfAdjointOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.UnitaryGroups
open BorelSpectral HilbertSpaceBasics SpectralTheorem SelfAdjointFunctions
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def IsContinuousUnitaryGroup (U : ℝ → H →L[ℂ] H) : Prop :=
  IsUnitaryRep U ∧ TendstoStrongly U (𝓝 0) 1
def expDampedInner (U : ℝ → H →L[ℂ] H) (x y : H) (t : ℝ) : ℂ :=
  (Real.exp (-t) : ℂ) * ⟪x, U t y⟫_ℂ
def resolventForm (U : ℝ → H →L[ℂ] H) (x y : H) : ℂ :=
  ∫ t in Ioi (0 : ℝ), expDampedInner U x y t
def IsResolventOp (U : ℝ → H →L[ℂ] H) (R : H →L[ℂ] H) : Prop :=
  ∀ x y, ⟪x, R y⟫_ℂ = resolventForm U x y
def resolventOp (U : ℝ → H →L[ℂ] H) : H →L[ℂ] H :=
  Classical.epsilon (IsResolventOp U)
def circleSupport {n : ℕ} {Y : Set (Fin n → ℝ)} (g : Y → ℂ) (hg : Measurable g) :
    BorelSubsets Y :=
  ⟨{y | g y ≠ 0 ∧ ‖g y‖ ^ 2 = (g y).re},
    (hg (measurableSet_singleton 0)).compl.inter
      (measurableSet_eq_fun (hg.norm.pow_const 2) (Complex.measurable_re.comp hg))⟩
def IsStoneGenerator (A : UnboundedOp H) (U : ℝ → H →L[ℂ] H) : Prop :=
  IsSelfAdjointOp A ∧ ∀ t, U t = expI A t
def stoneGenerator (U : ℝ → H →L[ℂ] H) : UnboundedOp H :=
  Classical.epsilon fun A => IsStoneGenerator A U
def StoneTheoremHolds : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    (∀ U : ℝ → H →L[ℂ] H, IsContinuousUnitaryGroup U →
      IsStronglyCont U ∧
      (∀ t, star (U t) = U (-t)) ∧
      (∀ x y, IntegrableOn (expDampedInner U x y) (Ioi 0)) ∧
      IsSesquilinear (resolventForm U) ∧
      (∀ x y, ‖resolventForm U x y‖ ≤ ‖x‖ * ‖y‖) ∧
      (∃! R : H →L[ℂ] H, IsResolventOp U R) ∧
      IsResolventOp U (resolventOp U) ∧
      (∀ x y, ⟪x, star (resolventOp U) y⟫_ℂ = resolventForm (fun t => U (-t)) x y) ∧
      (∀ B : H →L[ℂ] H, (∀ t, Commute B (U t)) →
        Commute B (resolventOp U) ∧ Commute B (star (resolventOp U))) ∧
      star (resolventOp U) * resolventOp U =
        (1 / 2 : ℂ) • (resolventOp U + star (resolventOp U)) ∧
      resolventOp U * star (resolventOp U) =
        (1 / 2 : ℂ) • (resolventOp U + star (resolventOp U)) ∧
      (∀ y, resolventOp U y = 0 → y = 0) ∧
      DenseRange (resolventOp U) ∧
      (∀ (n : ℕ) (Y : Set (Fin n → ℝ)) (F : SpectralMeasure Y H) (g : Y → ℂ)
        (hg : Measurable g), (∃ c : ℝ, ∀ y, ‖g y‖ ≤ c) →
          resolventOp U = F.integralOp g →
          F.IsCarriedBy (circleSupport g hg) ∧
          ∀ t : ℝ, U t = F.integralOpOn (circleSupport g hg) fun y =>
            Complex.exp (Complex.I * t * (((g y.1).im / (g y.1).re : ℝ) : ℂ))) ∧
      (∀ (n : ℕ) (Y : Set (Fin n → ℝ)) (F : SpectralMeasure Y H) (f : Y → ℝ),
        Measurable f →
          (∀ t : ℝ, 0 ≤ t →
            U t = F.integralOp fun y => Complex.exp (Complex.I * t * (f y : ℝ))) →
          resolventOp U = F.integralOp fun y => (1 - Complex.I * (f y : ℝ))⁻¹) ∧
      (∃! A : UnboundedOp H, IsStoneGenerator A U) ∧
      IsStoneGenerator (stoneGenerator U) U ∧
      (opKernel (stoneGenerator U) : Set H) = {y | ∀ t, U t y = y} ∧
      ∀ B : H →L[ℂ] H, (∀ t, Commute B (U t)) →
        ∀ S : BorelSubsets ℝ, Commute B (spectralMeasure (stoneGenerator U) (realLineSet S))) ∧
    ∀ (n : ℕ) (E E' : SpectralMeasure (FullSpace n) H),
      (∀ (t : ℝ) (i : Fin n), 0 ≤ t →
        E.integralOp (fun y => Complex.exp (Complex.I * t * (y.1 i : ℝ))) =
          E'.integralOp fun y => Complex.exp (Complex.I * t * (y.1 i : ℝ))) →
      E = E'
end YangMills.Construction.UnitaryGroups

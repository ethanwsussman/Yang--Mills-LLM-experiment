import YangMills.Construction.ReflectionPositivity.HalvesOfASplitTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace PeriodSublattice
variable (Γ : PeriodSublattice 1)
def IsBoundedBorelFn (F : Γ.QuotientField → ℂ) : Prop :=
  Measurable F ∧ ∃ C : ℝ, ∀ U, ‖F U‖ ≤ C
def totalFaceEnergy (U : Γ.QuotientField) : ℝ :=
  ∑ᶠ q : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U q
end PeriodSublattice
open NormalFamilies
def SplitTorusPullbacks : Prop :=
  ∀ (β : ℝ), 0 < β → ∀ (Γ : PeriodSublattice 1) (e : AmbientSpace) (he : e ∈ normalSet) (h : ℤ),
    Γ.SplitsAlongWithHalfPeriod e h →
    (∀ (c : ℝ) (hc : IsAllowedLevel 1 e c),
      let P : NormalLevelPair 1 := ⟨e, he, c, hc⟩
      Function.Involutive (Γ.pullbackField P.reflectSymmetry) ∧
      (∀ F ∈ continuousLocalFunctions 1,
        Γ.periodize (P.conjReflectObservable F) = Γ.conjReflect P (Γ.periodize F)) ∧
      (∀ F G : Γ.QuotientField → ℂ, Γ.IsBoundedBorelFn F → Γ.IsBoundedBorelFn G →
        Γ.conjReflect P (F + G) = Γ.conjReflect P F + Γ.conjReflect P G ∧
        Γ.conjReflect P (F * G) = Γ.conjReflect P F * Γ.conjReflect P G) ∧
      (∀ (w : ℂ) (F : Γ.QuotientField → ℂ), Γ.IsBoundedBorelFn F →
        Γ.conjReflect P (w • F) = conj w • Γ.conjReflect P F) ∧
      (∀ F : Γ.QuotientField → ℂ, Γ.IsBoundedBorelFn F →
        Γ.conjReflect P (Γ.conjReflect P F) = F)) ∧
    (∀ g : LatticeSymmetry 1, IsClassIsometry e g.toFun →
      IsHomeomorph (Γ.pullbackField g) ∧
      PeriodSublattice.PreservesFiniteMeasure (Γ.pullbackField g) Γ.quotientHaar ∧
      (∀ (U : Γ.QuotientField) (b : Link 1),
        Γ.orientedValue (Γ.pullbackField g U) (Γ.orientedClass b) =
          Γ.orientedValue U (Γ.orientedClass (g.linkMap b))) ∧
      (∀ g' : LatticeSymmetry 1, IsClassIsometry e g'.toFun →
        Γ.descendOrientedLink g = Γ.descendOrientedLink g' →
          Γ.pullbackField g = Γ.pullbackField g') ∧
      (∀ U : Γ.QuotientField, Γ.lift (Γ.pullbackField g U) =
        g.pullbackField (Γ.lift U)) ∧
      (∀ F ∈ continuousLocalFunctions 1,
        Γ.periodize (g.actOn F) = Γ.compPullback g (Γ.periodize F)) ∧
      (∀ F : Γ.QuotientField → ℂ, Γ.IsBoundedBorelFn F →
        Γ.IsBoundedBorelFn (Γ.compPullback g F) ∧
        PeriodSublattice.supNorm (Γ.compPullback g F) = PeriodSublattice.supNorm F ∧
        Γ.compPullback g (fun U => conj (F U)) =
          (fun U => conj (Γ.compPullback g F U)) ∧
        ∀ S : Set Γ.QuotientLink, PeriodSublattice.DependsOnlyOn F S →
          PeriodSublattice.DependsOnlyOn (Γ.compPullback g F) (Γ.linkImage g '' S)) ∧
      (∀ F G : Γ.QuotientField → ℂ, Γ.IsBoundedBorelFn F → Γ.IsBoundedBorelFn G →
        Γ.compPullback g (F * G) = Γ.compPullback g F * Γ.compPullback g G) ∧
      (∀ g' g'' : LatticeSymmetry 1, IsClassIsometry e g'.toFun →
        g''.toFun = g.toFun ∘ g'.toFun → ∀ F : Γ.QuotientField → ℂ, Γ.IsBoundedBorelFn F →
          Γ.compPullback g (Γ.compPullback g' F) = Γ.compPullback g'' F) ∧
      (∀ q : Γ.QuotientPlaquette, Γ.compPullback g (fun U => Γ.quotientFaceEnergy U q) =
        fun U => Γ.quotientFaceEnergy U (Γ.descendFace g q)) ∧
      Γ.compPullback g Γ.totalFaceEnergy = Γ.totalFaceEnergy ∧
      PeriodSublattice.PreservesFiniteMeasure (Γ.pullbackField g)
        (Γ.quotientHaar.withDensity fun U => ENNReal.ofReal (Γ.boltzmannWeight β U)) ∧
      PeriodSublattice.PreservesFiniteMeasure (Γ.pullbackField g) (Γ.gibbsMeasure β)) ∧
    (∀ v ∈ Γ.periods, ∀ F ∈ continuousLocalFunctions 1,
      Γ.periodize ((shift v).actOn F) = Γ.periodize F) ∧
    (∀ F ∈ continuousLocalFunctions 1, ∀ G ∈ continuousLocalFunctions 1,
      Γ.periodize (F * G) = Γ.periodize F * Γ.periodize G ∧
      Γ.periodize (F + G) = Γ.periodize F + Γ.periodize G) ∧
    (∀ F ∈ continuousLocalFunctions 1,
      Γ.periodize (fun U => conj (F U)) = fun U => conj (Γ.periodize F U))
end YangMills.Construction.InfiniteLattice

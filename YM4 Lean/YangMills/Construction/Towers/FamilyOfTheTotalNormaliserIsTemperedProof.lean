import YangMills.Construction.PeriodicOperators.FunctionalDeterminesItsPolarisationSymbol
import YangMills.Construction.Towers.ACommonWidthAndTheTransposedStraightAverage
import YangMills.Construction.Towers.CoefficientOfTheFamilyOfTheTotalNormaliser
import YangMills.Construction.Towers.FamilyOfTheTotalNormaliserIsAFunctional
import YangMills.Construction.Towers.FamilyOfTheTotalNormaliserIsTempered
import YangMills.Construction.Towers.SymbolOfTheTotalNormaliserIsATemperingChoice
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperatorsAreAdmitted
import YangMills.Construction.Towers.TheSecondDifferentialAtTheResponseSymbolsNearZero
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.NormaliserTempered
open YangMills.Construction.PeriodicOperators (imStrip)
open YangMills.Construction.PeriodicOperators.Tempered (FieldFamily IsLatticeFunctional IsHessianSymbol
  IsTemperedFunctional IsTemperedWitness hessianSymbol symbolDomain)
open YangMills.Construction.Tower.FullSpace (IsJointInvertibilityWidth jointInvertibilityWidth)
theorem mem_imStrip_min {a b : ℝ} {z : Fin 4 → ℂ} (ha : z ∈ imStrip a) (hb : z ∈ imStrip b) :
    z ∈ imStrip (min a b) :=
  fun μ => le_min (ha μ) (hb μ)
theorem isHessianSymbol_hessianSymbol
    (hdet : YangMills.Construction.PeriodicOperators.Tempered.HessianSymbolDetermined.Claim)
    {L : ℕ} (hS : YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L)
    {F : FieldFamily L} (hF : IsTemperedFunctional L F) :
    IsHessianSymbol L F (hessianSymbol L F) := by
  obtain ⟨-, P, hP, -⟩ := hdet L hS F hF
  exact Classical.epsilon_spec (p := IsHessianSymbol L F) ⟨P, hP⟩
theorem temperedAndStiffness
    (hfun : YangMills.Construction.Tower.LogNormaliserIsFunctional.Claim)
    (hwit : YangMills.Construction.Tower.NormaliserSymbol.IsTemperedWitnessClaim)
    (hnear : YangMills.Construction.Tower.ResponseSecondVariation.NearZeroCubicBound)
    (hstiff : YangMills.Construction.Tower.NormaliserStiffness.StiffnessIsMixedPartial)
    (hjoint : YangMills.Construction.Tower.FullSpace.JointWidthAndTransposeTheorem)
    (hconst : YangMills.Construction.Tower.FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hdet : YangMills.Construction.PeriodicOperators.Tempered.HessianSymbolDetermined.Claim) :
    TemperedAndStiffness := by
  obtain ⟨-, -, δ₀, hδ₀, -⟩ := hconst
  refine ⟨δ₀, hδ₀, fun L hL hS k hk => ?_⟩
  have hw : IsJointInvertibilityWidth L k hL (jointInvertibilityWidth L k hL) := (hjoint L hL hS k hk).1
  have htemp : IsTemperedFunctional L (YangMills.Construction.Tower.logNormaliserFamily L k) := by
    obtain ⟨π, e, hc, -⟩ := hwit δ₀ hδ₀ L hL hS k hk _ hw
    exact ⟨hfun L hS k hk, _, π, e, hc⟩
  have hP := isHessianSymbol_hessianSymbol hdet hS htemp
  have hstrips : SymbolOnStrips δ₀ L k hL := by
    intro δ hδ z hz
    obtain ⟨π, e, hc, hval⟩ := hwit δ₀ hδ₀ L hL hS k hk δ hδ
    have hmin : z ∈ imStrip (min δ (2 * δ₀)) := mem_imStrip_min hz.1 hz.2
    refine ⟨⟨_, π, e, hc, hmin⟩, fun a a' μ ν => ?_⟩
    rw [hP _ π e hc μ ν hmin]
    exact hval z hz a a' μ ν
  refine ⟨htemp, hstrips, ?_, hstiff L hL hS k hk⟩
  obtain ⟨C, N, hN, hsub, hbd⟩ := hnear δ₀ hδ₀ L hL hS k hk _ hw
  refine ⟨C, N, hN, fun z hz => ⟨(hstrips _ hw z (hsub hz)).1, ?_⟩, fun z hz μ ν => ?_⟩
  · exact ⟨_, hw, (hsub hz).1, δ₀, hδ₀, (hsub hz).2⟩
  · have hval := (hstrips _ hw z (hsub hz)).2 2 2 μ ν
    rw [if_pos rfl] at hval
    rw [hval]
    exact hbd z hz μ ν
end YangMills.Construction.Tower.NormaliserTempered
end

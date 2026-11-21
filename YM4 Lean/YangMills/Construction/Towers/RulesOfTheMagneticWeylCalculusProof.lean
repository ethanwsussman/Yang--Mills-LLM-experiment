import YangMills.Construction.Towers.AdjointOfAQuantization
import YangMills.Construction.Towers.CoefficientsReadOffAQuantization
import YangMills.Construction.Towers.ExplicitFormOfTheWeylOperators
import YangMills.Construction.Towers.MoyalExpansionOfAStarProduct
import YangMills.Construction.Towers.QuantizationIsTheSumOfItsSeries
import YangMills.Construction.Towers.QuantizationOfAStarProduct
import YangMills.Construction.Towers.RelationsOfTheWeylOperators
import YangMills.Construction.Towers.RulesOfTheMagneticWeylCalculus
import YangMills.Construction.Towers.StarProductOfTwoSymbols
import YangMills.Construction.Towers.StarProductWithAConstantMatrix
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open UnitLatticeL2 UnitaryCombinations AbelianFieldDensity OneLoopNotation
open InfiniteLattice (AmbientSpace)
open MagneticWeyl
private theorem hasAbsSummableFourier_of_isWeylSymbol {p q : ℕ} [NeZero p] [NeZero q]
    {a : AmbientSpace → Matrix (Fin p) (Fin q) ℂ} (ha : IsWeylSymbol a) :
    HasAbsSummableFourier a := by
  obtain ⟨c, hc, hs⟩ := ha
  exact ⟨c, hc, by simpa using hs 0 (by norm_num)⟩
theorem magneticWeylCalculusRules_holds
    (hExp : WeylExplicitFormulas)
    (hRel : MagneticWeylRelations)
    (hSum : WeylQuantHasSum)
    (hAdj : WeylQuantAdjoint)
    (hCoef : FourierCoeffsFromQuantization)
    (hProd : MoyalProductBounds)
    (hConst : MoyalProductWithConstant)
    (hQuant : WeylQuantMoyalProduct)
    (hRem : MoyalRemainderBound) :
    MagneticWeylCalculusRules := by
  intro L φ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h₁, h₂, h₃, h₄, -⟩ := hExp L φ
    exact ⟨h₁, h₂, h₃, h₄⟩
  · intro k k'
    obtain ⟨hm, -, hi, ho⟩ := hRel L φ k k'
    refine ⟨hm, ?_, ?_⟩
    · refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun ψ χ => ?_).symm
      exact hi ψ χ
    · have h := congrArg (fun v : EuclideanSpace ℂ (Fin 1) => v 0)
        (ho (EuclideanSpace.single 0 (1 : ℂ)))
      simpa [matrixAtZero, boundedMagneticWeyl] using h
  · intro p q _ _ a ha
    obtain ⟨hr, hd⟩ := (hCoef L φ).1 p q a ha
    exact ⟨⟨(hSum L φ p q a (hasAbsSummableFourier_of_isWeylSymbol ha)).2,
      (hAdj L φ p q a ha).1, (hAdj L φ p q a ha).2, hr, hd⟩, hConst φ p q a ha⟩
  · intro p _ a ha
    exact (hCoef L φ).2 p a ha
  · intro p q r _ _ _ a b ha hb
    obtain ⟨h₁, -, h₃, -, h₅⟩ := hProd φ p q r a b ha hb
    exact ⟨⟨h₁, h₃, h₅, hQuant L φ p q r a b ha hb⟩,
      hRem φ p q r a b ha hb (moyalRemainder φ a b) fun _ => rfl⟩
end YangMills.Construction.Tower
end

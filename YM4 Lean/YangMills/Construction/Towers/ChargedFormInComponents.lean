import YangMills.Construction.Towers.ChargedFormOfTheConstantFieldDefs
import YangMills.Construction.Towers.PropertiesOfAbelianFields
import YangMills.Construction.Towers.TheCoefficientAsAResponseToAConstantField
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Tower.UnitLatticeL2
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
open YangMills.Construction.Tower.AbelianFieldDensity YangMills.Construction.Tower.AbelianFieldFacts
def ChargedPairsFormIdentity : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (f : ℝ) (w : VectorL2 L 4)
    (B : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2), (Function.support fun x => w x).Finite →
    IsLieFormOf w B →
    ((∑ᶠ p, AbelianFieldFacts.faceTerm (scaledLinearAngle L f) B p +
        ∑ᶠ x, AbelianFieldFacts.vertexTerm (scaledLinearAngle L f) B x : ℝ) : ℂ) =
      pairsForm chargedTermPair L (2 * f) w
end YangMills.Construction.Tower.ConstantFieldSymbols
end

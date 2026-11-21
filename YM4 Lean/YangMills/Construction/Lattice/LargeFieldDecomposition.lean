import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Lattice
inductive LargeFieldDecomposition where
  | regularityOfTheFirstBackground
  | regularityOfTheNextBackground (n : ℕ)
  | approximateFluctuationTest (n : ℕ)
  | completionOfTheFluctuationTests (n : ℕ)
  | smallFieldTestOfTheFluctuationField (n : ℕ)
  | extendibilityOfTheExteriorField
  | smallFieldTestOfTheMainStep
  | testAtTheLastShell
  | testOfTheDenominator
end YangMills.Construction.Lattice

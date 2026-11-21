import YangMills.Construction.Continuum.ConstantOfTheExtension
import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.Continuum.GrowthConditionOfSequencesOnFlatFunctions
import YangMills.Construction.Continuum.SeparatedTuplesWithSmoothEntriesAndTheirSeparation
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SeparatedBound
abbrev CorrelationFamily : Type := (n : ℕ) → 2 ≤ n → TestSpaces.SepTupleOfCard n → ℝ
def SupportedSeparated {n : ℕ} (R d : ℝ) (X : TestSpaces.SepTupleOfCard n) : Prop :=
  SmoothSepR4.SupportedInBalls R X.1 ∧ ENNReal.ofReal d ≤ SmoothSepR4.sepDist X.1
def sharpNormProd (M : ℝ) {n : ℕ} (X : TestSpaces.SepTupleOfCard n) : ℝ :=
  ∏ i, TestFunctions.sharpNormR4 M (X.1 i)
def ExtendsToFlat {n : ℕ} (Φ : TestSpaces.SepTupleOfCard n → ℝ)
    (T : ConfigurationSpace.flatSchwartzSet n → ℂ) : Prop :=
  T ∈ ConfigurationSpace.flatSchwartzDualSet n ∧
    ∀ (f : Fin n → (Fin 4 → ℝ) → ℝ) (hf : f ∈ SmoothSepR4.smoothSepR4 n)
      (h : ConfigurationSpace.ofRealFun (TestSpaces.tensorProd f) ∈
        ConfigurationSpace.flatSchwartzSet n),
      T ⟨_, h⟩ = (Φ ⟨f, hf.1⟩ : ℂ)
def IsMomentSequence (S : CorrelationFamily) (Q : GrowthSequences.FlatSeq) : Prop :=
  Q.zeroTerm = id ∧
    (∀ h : 1 ≤ 1, Q.posTerm 1 h = 0) ∧
    ∀ (n : ℕ) (hn : 2 ≤ n),
      ExtendsToFlat
        (fun X : TestSpaces.SepTupleOfCard n => TestSpaces.centredOfCumulants S ⟨n, X⟩)
        (Q.posTerm n (by omega))
def MatchesMembers (Q : GrowthSequences.FlatSeq)
    (T : (n : ℕ) → TestSpaces.flatSchwartzSet n → ℂ) : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (φ : TestSpaces.flatSchwartzSet n)
    (ψ : ConfigurationSpace.flatSchwartzSet n), φ.1 = ψ.1 → T n φ = Q.posTerm n hn ψ
def extFactorAbs : ℝ := |ExtensionConstants.extFactor|
def extBaseMax : ℝ := max 1 |ExtensionConstants.extBase|
end YangMills.Construction.SeparatedBound
end

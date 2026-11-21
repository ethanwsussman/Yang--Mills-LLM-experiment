import YangMills.Construction.Torus.CentredFunctionalOfAFamilyOfMaps
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.AmbientPoints
noncomputable section
namespace YangMills.Construction.FourSpaceGrowth
variable {s : Conventions.StandingParameters} {n : ℕ}
def ofTestSpaceTuple (X : TestSpaces.SepTuple) : allSeparatedTuples s .euclidean :=
  ⟨⟨X.1, X.2.1⟩, (mem_separatedTuples_r4_iff X.2.1).2 X.2.2⟩
def restrictToR4 (σ : allSeparatedTuples s .euclidean → ℝ) :
    TestSpaces.SepTuple → ℝ :=
  fun X => σ (ofTestSpaceTuple X)
def GrowthBoundOf (k : ℕ) (c C ϰ : ℝ)
    (σ : allSeparatedTuples s .euclidean → ℝ) : Prop :=
  TestSpaces.GrowthBound k c C ϰ (restrictToR4 σ)
end YangMills.Construction.FourSpaceGrowth

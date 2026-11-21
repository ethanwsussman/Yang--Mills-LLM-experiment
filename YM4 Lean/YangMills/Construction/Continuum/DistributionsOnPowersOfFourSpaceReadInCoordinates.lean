import YangMills.Construction.Continuum.OrderZeroTestFunctionsOnCoordinateSpacesAndGenerators
import YangMills.Construction.TorusOrFourSpace.TestFunctionsAndDistributionsOnASet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CoordinateRepresentation
open TopologicalSpace ReflectionSpaces PeriodicSpace PeriodicSpace.Kind
variable {D : Params} {p : ℕ+}
def IsCoordinateImageOfSet (Ω : Set (euclidean.Tuple D p))
    (W : Opens (Euclidean.Coord (4 * (p : ℕ)))) : Prop :=
  (W : Set (Euclidean.Coord (4 * (p : ℕ)))) = Tuple.proj D euclidean ⁻¹' Ω
def ReadsAs {Ω : Set (euclidean.Tuple D p)} {W : Opens (Euclidean.Coord (4 * (p : ℕ)))}
    (T : Tuple.testFns D euclidean Ω → ℂ) (V : Euclidean.Distribution W) : Prop :=
  IsCoordinateImageOfSet Ω W ∧
    ∀ (F : Tuple.testFns D euclidean Ω) (G : Euclidean.testFunctionSpace W),
      (G : Euclidean.Coord (4 * (p : ℕ)) → ℂ) = F.1 ∘ Tuple.proj D euclidean →
        V.form G = T F
def DistributionsReadInCoordinates : Prop :=
  ∀ (D : Params) (p : ℕ+) (Ω : Set (euclidean.Tuple D p))
    (W : Opens (Euclidean.Coord (4 * (p : ℕ)))),
    Tuple.IsOpenT D euclidean Ω → IsCoordinateImageOfSet Ω W →
      (∀ F ∈ Tuple.testFns D euclidean Ω,
        F ∘ Tuple.proj D euclidean ∈ Euclidean.testFunctionSpace W) ∧
      (∀ G ∈ Euclidean.testFunctionSpace W, ∃ F ∈ Tuple.testFns D euclidean Ω,
        F ∘ Tuple.proj D euclidean = G) ∧
      ∀ T : Tuple.testFns D euclidean Ω → ℂ, Tuple.IsDistrib T →
        ∃! V : Euclidean.Distribution W, ReadsAs T V
end YangMills.Construction.CoordinateRepresentation
end

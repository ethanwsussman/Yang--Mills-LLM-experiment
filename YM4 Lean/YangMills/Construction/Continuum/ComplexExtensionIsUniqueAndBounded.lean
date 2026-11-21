import YangMills.Construction.ConfigSpace.MultilinearComplexification
import YangMills.Construction.Continuum.FormsBoundedOnSeparatedBalls
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ConfigSpace
open TestFunctions
variable {n : ℕ}
theorem mem_smoothComplexTupleSet_of_real (f : smoothRealTupleSet n) :
    f.1 ∈ smoothComplexTupleSet n := by
  obtain ⟨f, ⟨hentries, hdisjoint⟩, hsmooth⟩ := f
  exact ⟨fun i => ⟨hsmooth i, (hentries i).2.2.1⟩, hdisjoint⟩
def AgreesOnRealTuples (T' : smoothComplexTupleSet n → ℂ) (T : smoothRealTupleSet n → ℝ) : Prop :=
  ∀ f : smoothRealTupleSet n, T' ⟨f.1, mem_smoothComplexTupleSet_of_real f⟩ = (T f : ℂ)
def complexifyUniqueAndBounded : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ T : smoothRealTupleSet n → ℝ, IsRealMultilinearSmooth T →
    ((∀ (φ : smoothComplexTupleSet n) (ε : Fin n → Fin 2),
        tupleComplexParts ε φ.1 ∈ smoothRealTupleSet n ∧
          ∀ i, tsupport (tupleComplexParts ε φ.1 i) ⊆ tsupport (φ.1 i)) ∧
      IsComplexMultilinearSmooth (complexify T) ∧
      AgreesOnRealTuples (complexify T) T ∧
      ∀ T' : smoothComplexTupleSet n → ℂ, IsComplexMultilinearSmooth T' →
        AgreesOnRealTuples T' T → T' = complexify T) ∧
    ∀ (c : ℝ) (a : ℕ) (G : ℝ), SeparatedBallBound c a G T →
      ∀ (d : ℝ), 0 < d → ∀ φ : smoothComplexTupleSet n,
        (∀ i, SupportInSmallBall (φ.1 i)) →
        (∀ i i', i ≠ i' →
          ENNReal.ofReal d ≤ setDistR4 (tsupport (φ.1 i)) (tsupport (φ.1 i'))) →
        ‖complexify T φ‖ ≤ 2 ^ n * G * max 1 (d ^ (-(a : ℤ))) *
          ∏ i, max (uniformNorm (φ.1 i)) (c * gradSupNorm (φ.1 i))
end YangMills.Construction.ConfigSpace

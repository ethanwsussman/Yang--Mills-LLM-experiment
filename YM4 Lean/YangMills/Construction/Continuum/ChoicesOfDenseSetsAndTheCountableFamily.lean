import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import YangMills.Construction.TestFunctions.RationalBoxFamilies
import YangMills.Construction.TorusOrFourSpace.BoxesStockOfSupportsAndFamilyOfTuples
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.EuclideanTuples
open TestFunctions PeriodicSpace
abbrev R4Fun : Type := (Fin 4 → ℝ) → ℝ
abbrev rationalUnions : Set (Set (Fin 4 → ℝ)) := ratBoxUnions
variable (S : Params)
theorem supportStock_euclidean :
    (Kind.supportStock S .euclidean : Set (Set (Fin 4 → ℝ))) = rationalUnions := by
  ext Q
  constructor
  · rintro ⟨r, b, -, rfl⟩
    refine ⟨range fun i => (b i).toSet, finite_range _, ?_, ?_⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨(b i).lo, (b i).hi, (b i).lo_lt_hi, rfl⟩
    · show (⋃ i, Kind.quotMap S .euclidean '' (b i).toSet : Set (Fin 4 → ℝ)) =
        ⋃₀ range fun i => (b i).toSet
      rw [sUnion_range]
      exact iUnion_congr fun i => image_id _
  · rintro ⟨𝓑, hfin, hbox, rfl⟩
    have hrep : ∀ B : 𝓑, ∃ b : RationalBox, b.toSet = B := fun B => by
      obtain ⟨s, t, hst, h⟩ := hbox B B.2
      exact ⟨⟨s, t, hst⟩, h.symm⟩
    choose c hc using hrep
    have := hfin.to_subtype
    let e := Finite.equivFin 𝓑
    refine ⟨Nat.card 𝓑, fun i => c (e.symm i), fun _ => trivial, ?_⟩
    show ⋃₀ 𝓑 = (⋃ i, Kind.quotMap S .euclidean '' (c (e.symm i)).toSet :
      Set (Fin 4 → ℝ))
    have himg : ∀ i, (Kind.quotMap S .euclidean '' (c (e.symm i)).toSet :
        Set (Fin 4 → ℝ)) = (e.symm i : Set (Fin 4 → ℝ)) :=
      fun i => (image_id _).trans (hc _)
    rw [iUnion_congr himg]
    ext x
    simp only [mem_iUnion, mem_sUnion]
    constructor
    · rintro ⟨B, hB, hx⟩
      exact ⟨e ⟨B, hB⟩, by rw [Equiv.symm_apply_apply]; exact hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨_, (e.symm i).2, hx⟩
theorem partialDeriv_euclidean (μ : Fin 4) (u : R4Fun) :
    (Kind.partialDeriv S .euclidean μ u : R4Fun) = partialDerivR4 μ u := by
  have h := Classical.epsilon_spec
    (p := fun v : Kind.Pt S .euclidean → ℝ =>
      v ∘ Kind.quotMap S .euclidean = partialDerivR4 μ (u ∘ Kind.quotMap S .euclidean))
    ⟨partialDerivR4 μ u, rfl⟩
  exact h
theorem partialDerivR4_eq_fderiv {f : R4Fun} (hf : IsC1R4 f) (μ : Fin 4)
    (x : Fin 4 → ℝ) : partialDerivR4 μ f x = fderiv ℝ f x (Pi.single μ 1) := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.partialDerivR4_eq_fderiv <;> assumption
theorem bounded_of_isC1R4 {f : R4Fun} (hf : IsC1R4 f) (hc : HasCompactSupport f) :
    (∃ C, ∀ x, ‖f x‖ ≤ C) ∧ ∀ μ, ∃ C, ∀ x, ‖partialDerivR4 μ f x‖ ≤ C := by
  refine ⟨hf.continuous.bounded_above_of_compact_support hc, fun μ => ?_⟩
  have h1 : Continuous fun x => fderiv ℝ f x (Pi.single μ 1) :=
    (ContDiff.continuous_fderiv hf (by norm_num)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := h1.bounded_above_of_compact_support (hc.fderiv_apply ℝ _)
  exact ⟨C, fun x => by rw [partialDerivR4_eq_fderiv hf]; exact hC x⟩
theorem uniformNorm_nonneg (f : R4Fun) : 0 ≤ TestFunctions.uniformNorm f := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.uniformNorm_nonneg <;> assumption
theorem c1NormR4_nonneg (f : R4Fun) : 0 ≤ c1NormR4 f := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.c1NormR4_nonneg <;> assumption
theorem partialDerivR4_neg (μ : Fin 4) (f : R4Fun) :
    partialDerivR4 μ (-f) = -partialDerivR4 μ f := by
  funext x
  exact deriv.fun_neg
theorem c1NormR4_neg (f : R4Fun) : c1NormR4 (-f) = c1NormR4 f := by
  unfold c1NormR4
  simp only [partialDerivR4_neg, TestFunctions.uniformNorm, Pi.neg_apply, norm_neg]
end YangMills.Construction.EuclideanTuples

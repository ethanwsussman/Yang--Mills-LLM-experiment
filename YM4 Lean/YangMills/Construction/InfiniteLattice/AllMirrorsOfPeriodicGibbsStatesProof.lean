import YangMills.Construction.InfiniteLattice.AllMirrorsOfPeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.FunctionsStatesSupportsClassesMirrorsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAtASpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexOrder
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicGibbsSymmetries
open BasicStructure
variable {a : ℝ}
theorem isBoundedObservable_actOn {r : LatticeSymmetry a} (hm : Measurable r.pullbackField)
    {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) : IsBoundedObservable (r.actOn A) := by
  obtain ⟨hAm, C, hC⟩ := hA
  exact ⟨hAm.comp hm, C, fun U => hC _⟩

theorem bijOn_signedUnitVectors {w : AmbientSpace →ₗ[ℝ] AmbientSpace} (hw : w ∈ hypercubicGroup) :
    BijOn w signedUnitVectors signedUnitVectors := by
  obtain ⟨ς, h⟩ := id hw
  have hs : ∀ κ, w (Pi.single κ 1) = Pi.single (ς κ) 1 ∨
      w (Pi.single κ 1) = -Pi.single (ς κ) 1 := h
  have hmaps : MapsTo w signedUnitVectors signedUnitVectors := by
    rintro x ⟨μ, rfl | rfl⟩
    · rcases hs μ with h1 | h1
      · exact ⟨ς μ, Or.inl h1⟩
      · exact ⟨ς μ, Or.inr h1⟩
    · rcases hs μ with h1 | h1
      · exact ⟨ς μ, Or.inr (by rw [map_neg, h1])⟩
      · exact ⟨ς μ, Or.inl (by rw [map_neg, h1, neg_neg])⟩
  have hsurjOn : SurjOn w signedUnitVectors signedUnitVectors := by
    rintro y ⟨κ, rfl | rfl⟩
    · obtain ⟨μ, rfl⟩ := ς.surjective κ
      rcases hs μ with h1 | h1
      · exact ⟨_, ⟨μ, Or.inl rfl⟩, h1⟩
      · exact ⟨_, ⟨μ, Or.inr rfl⟩, by rw [map_neg, h1, neg_neg]⟩
    · obtain ⟨μ, rfl⟩ := ς.surjective κ
      rcases hs μ with h1 | h1
      · exact ⟨_, ⟨μ, Or.inr rfl⟩, by rw [map_neg, h1]⟩
      · exact ⟨_, ⟨μ, Or.inl rfl⟩, h1⟩
  have hsurj : Function.Surjective w := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    intro x _
    have hx : x = ∑ i, x i • (Pi.single i 1 : AmbientSpace) := by
      funext μ
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    obtain ⟨y, -, hy⟩ :=
      hsurjOn (show (Pi.single i 1 : AmbientSpace) ∈ signedUnitVectors from ⟨i, Or.inl rfl⟩)
    exact ⟨y, hy⟩
  exact ⟨hmaps, (LinearMap.injective_iff_surjective.mpr hsurj).injOn, hsurjOn⟩

theorem isSymmetricUnder_latticeMotion
    (hmeas : ∀ r : LatticeSymmetry a, Measurable r.pullbackField)
    {ν : Measure (GaugeField a)}
    (hτ : ∀ v : LatticePoint a, IsSymmetricUnder ν (shift v))
    (hW : ∀ r : LatticeSymmetry a, ∀ w ∈ hyperoctahedralLinearGroup, (∀ x, r.toFun x = w x) →
      IsSymmetricUnder ν r)
    (r : latticeMotions a) : IsSymmetricUnder ν (latticeMotionSymmetry r) := by
  obtain ⟨f, hf⟩ := r
  obtain ⟨w, hw, v, hv, hfx⟩ := id hf
  have hlin : (⇑w : AmbientSpace → AmbientSpace) ∈ latticeMotions a :=
    ⟨w, hw, 0, zero_mem _, fun x => by simp⟩
  obtain ⟨w', hw', hww⟩ :=
    exists_mem_hyperoctahedralLinearGroup w (bijOn_signedUnitVectors hw)
  have hinv : IsSymmetricUnder ν (latticeMotionSymmetry ⟨⇑w, hlin⟩) :=
    hW _ w' hw' fun x => by
      show w x = w' x
      rw [hww]
  intro A hA
  have key : (latticeMotionSymmetry ⟨f, hf⟩).actOn A =
      (shift (⟨v, hv⟩ : LatticePoint a)).actOn
        ((latticeMotionSymmetry ⟨⇑w, hlin⟩).actOn A) := by
    funext U
    show A _ = A _
    congr 1
    apply Subtype.ext
    funext b
    show U ((latticeMotionSymmetry ⟨f, hf⟩).linkMap b) =
      U ((shift (⟨v, hv⟩ : LatticePoint a)).linkMap
        ((latticeMotionSymmetry ⟨⇑w, hlin⟩).linkMap b))
    refine congrArg U.1 ?_
    apply Link.ext <;> apply Subtype.ext
    · exact hfx _
    · exact hfx _
  rw [key, hτ _ _ (isBoundedObservable_actOn (hmeas _) hA), hinv A hA]

theorem statement_holds (h₁ : PeriodicGibbsAtSpacing.Statement)
    (h₂ : BasicStructure.Statement) : Statement := by
  intro a ha β hβ
  obtain ⟨hprop, -, -, hset, hne, -, -⟩ := h₁ a ha β hβ
  obtain ⟨-, hFi, -, -, -, -, -, -⟩ := h₂.1 a ha β hβ
  have hmeas : ∀ r : LatticeSymmetry a, Measurable r.pullbackField := fun r =>
    (hFi r r).1.continuous.measurable
  refine ⟨fun ν hν => ?_, hset, hne⟩
  have : IsProbabilityMeasure ν := hν.1.1
  obtain ⟨hτ, hW, hM⟩ := hprop ν hν
  refine ⟨isSymmetricUnder_latticeMotion hmeas hτ hW, fun Q hQ => ?_⟩
  obtain ⟨m1, m2, m3, -⟩ := hM Q hQ
  exact ⟨m1, fun F hF => m2 F hF, fun F hF => m3 F hF⟩



end YangMills.Construction.InfiniteLattice.PeriodicGibbsSymmetries

end

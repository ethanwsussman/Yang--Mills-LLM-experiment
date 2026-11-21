import YangMills.Construction.InfiniteLattice.FactsOfTheLocalFunctionsAtEverySpacing
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndDenseLocalObservables
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndLatticeIsometries
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open GibbsAtFixedSpacing
namespace InfiniteLattice.GaugeFieldSpaceDensity
variable {a : ℝ}
theorem supNorm_lt_of_norm_le {G : GaugeField a → ℂ} {c ε : ℝ} (hc : 0 ≤ c) (hcε : c < ε)
    (hG : ∀ U, ‖G U‖ ≤ c) : observableSupNorm G < ε :=
  lt_of_le_of_lt (Real.iSup_le hG hc) hcε
theorem exists_countable_supNormDense_subset [CompactSpace (GaugeField a)]
    [TopologicalSpace.MetrizableSpace (GaugeField a)]
    (hdense : ∀ (f : C(GaugeField a, ℂ)) (ε : ℝ), 0 < ε →
      ∃ F ∈ continuousLocalFunctions a, ∀ U, ‖f U - F U‖ < ε)
    (hcont : ∀ F ∈ continuousLocalFunctions a, Continuous F) :
    ∃ D : Set (GaugeField a → ℂ), D.Countable ∧ D ⊆ continuousLocalFunctions a ∧
      IsSupNormDenseIn D (continuousFns a) := by
  let := TopologicalSpace.metrizableSpaceMetric (GaugeField a)
  have : SecondCountableTopology (GaugeField a) := inferInstance
  let S : Set C(GaugeField a, ℂ) := {f | (f : GaugeField a → ℂ) ∈ continuousLocalFunctions a}
  obtain ⟨t, htS, htc, hcl⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have hsub : (fun f : C(GaugeField a, ℂ) => (f : GaugeField a → ℂ)) '' t ⊆
      continuousLocalFunctions a := by
    rintro _ ⟨f, hf, rfl⟩
    exact htS hf
  refine ⟨_, htc.image _, hsub, fun F hF => hcont F (hsub hF), fun F hF ε hε => ?_⟩
  obtain ⟨G, hG, hFG⟩ := hdense ⟨F, hF⟩ (ε / 3) (by positivity)
  have hGt : (⟨G, hcont G hG⟩ : C(GaugeField a, ℂ)) ∈ closure t := hcl hG
  obtain ⟨H, hHt, hGH⟩ := Metric.mem_closure_iff.1 hGt (ε / 3) (by positivity)
  refine ⟨H, ⟨H, hHt, rfl⟩, supNorm_lt_of_norm_le (c := 2 * (ε / 3)) (by positivity) (by linarith) ?_⟩
  intro U
  have h₁ : ‖F U - G U‖ < ε / 3 := hFG U
  have h₂ : ‖G U - H U‖ ≤ ε / 3 := by
    have := ContinuousMap.dist_apply_le_dist (f := (⟨G, hcont G hG⟩ : C(GaugeField a, ℂ)))
      (g := H) U
    rw [dist_eq_norm] at this
    exact this.trans hGH.le
  calc ‖(F - H) U‖ = ‖(F U - G U) + (G U - H U)‖ := by simp
    _ ≤ ‖F U - G U‖ + ‖G U - H U‖ := norm_add_le _ _
    _ ≤ 2 * (ε / 3) := by linarith
theorem gaugeFieldSpaceAndDenseLocal_holds
    (hsym : FieldSpace.SymmetryProperties)
    (hloc : LocalFunctionPropertiesForAllSpacings) :
    GaugeFieldSpaceAndDenseLocal := by
  intro a ha
  obtain ⟨⟨hcompact, hmetric, hsigma⟩, -⟩ := hsym a ha
  obtain ⟨hadd, hsmul, hconst, hconj, hdense, -⟩ := hloc a ha
  have hcont : ∀ F ∈ continuousLocalFunctions a, Continuous F := fun F hF => hF.2.2
  have hcount := exists_countable_supNormDense_subset hdense hcont
  have hdenseLoc : IsSupNormDenseIn (continuousLocalFunctions a) (continuousFns a) := by
    obtain ⟨D, -, hD, -, hd⟩ := hcount
    refine ⟨hcont, fun F hF ε hε => ?_⟩
    obtain ⟨H, hH, hn⟩ := hd F hF ε hε
    exact ⟨H, hD hH, hn⟩
  refine ⟨hcompact, hmetric, hsigma, hcont, hadd, hsmul, hconst, hconj, hcount, hdenseLoc, ?_, ?_⟩
  · exact fun F hF => hF.2
  · intro F hF ε hε
    obtain ⟨H, hH, hFH⟩ := hdense ⟨F, hF.1⟩ (ε / 2) (by positivity)
    have hR : (1 / 2 : ℂ) • (H + fun U => conj (H U)) ∈ continuousLocalFunctions a :=
      hsmul _ _ (hadd _ hH _ (hconj _ hH)).1
    have hval : ∀ U, ((1 / 2 : ℂ) • (H + fun U => conj (H U))) U = ((H U).re : ℂ) := by
      intro U
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.add_conj]
      push_cast
      ring
    refine ⟨_, ⟨hR, hcont _ hR, fun U => by rw [hval]; exact Complex.ofReal_im _⟩,
      supNorm_lt_of_norm_le (c := ε / 2) (by positivity) (by linarith) fun U => ?_⟩
    have hFU : F U = ((F U).re : ℂ) := by
      apply Complex.ext <;> simp [hF.2 U]
    have h₃ : ‖F U - H U‖ < ε / 2 := hFH U
    have h₄ : |(F U - H U).re| ≤ ‖F U - H U‖ := Complex.abs_re_le_norm _
    have h₅ : (F - (1 / 2 : ℂ) • (H + fun U => conj (H U))) U = (((F U - H U).re : ℝ) : ℂ) := by
      rw [Pi.sub_apply, hval U, Complex.sub_re, Complex.ofReal_sub, ← hFU]
    rw [h₅, Complex.norm_real, Real.norm_eq_abs]
    linarith
end InfiniteLattice.GaugeFieldSpaceDensity
end YangMills.Construction
end

import YangMills.Construction.ChessboardTori.BoxAgainstTheTorusThroughFreeBoundaryConditions
import YangMills.Construction.ChessboardTori.OuterConfigurationAgainstTheFreeBox
import YangMills.Construction.ChessboardTori.PeriodicRealizationOnARectangularTorus
import YangMills.Construction.ChessboardTori.SurfaceCountsOfABox
import YangMills.Construction.ChessboardTori.TorusAgainstTheFreeBox
import YangMills.Construction.ChessboardTori.TorusPartitionAtTheZeroSource
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction
open InfiniteLattice GibbsAtFixedSpacing
namespace ChessboardTori
namespace BoxVersusTorusViaFreeBoundary
theorem exists_real_eq_of_nonneg {z : ℂ} (hz : 0 ≤ z) : ∃ r : ℝ, 0 ≤ r ∧ z = r := by
  obtain ⟨hre, him⟩ := Complex.le_def.mp hz
  exact ⟨z.re, hre, Complex.ext (by simp) (by simpa using him.symm)⟩
theorem exists_real_eq_of_le_ofReal {z : ℂ} {r : ℝ} (hz : z ≤ r) : ∃ s : ℝ, s ≤ r ∧ z = s := by
  obtain ⟨hre, him⟩ := Complex.le_def.mp hz
  exact ⟨z.re, by simpa using hre, Complex.ext (by simp) (by simpa using him)⟩
theorem div_le_inv_mul_inv_mul_div {x x₁ t t₁ f f₁ c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hf : 0 ≤ f) (hf₁ : 0 < f₁) (hx : x ≤ f) (hx₁ : c₁ * f₁ ≤ x₁) (ht : c₂ * f ≤ t)
    (ht₁ : t₁ ≤ f₁) (ht₁' : c₂ * f₁ ≤ t₁) : x / x₁ ≤ c₁⁻¹ * c₂⁻¹ * (t / t₁) := by
  have hpos₁ : 0 < c₁ * f₁ := mul_pos hc₁ hf₁
  have hpos₂ : 0 < t₁ := lt_of_lt_of_le (mul_pos hc₂ hf₁) ht₁'
  have hle₁ : x / x₁ ≤ f / (c₁ * f₁) := div_le_div₀ hf hx hpos₁ hx₁
  have hle₂ : c₂ * f / f₁ ≤ t / t₁ := div_le_div₀ (le_trans (mul_nonneg hc₂.le hf) ht) ht hpos₂ ht₁
  have heq : f / (c₁ * f₁) = c₁⁻¹ * c₂⁻¹ * (c₂ * f / f₁) := by
    field_simp
  rw [heq] at hle₁
  exact hle₁.trans (mul_le_mul_of_nonneg_left hle₂ (by positivity))
variable (D : ChessboardSetup)
theorem isBoxLocalObservable_const_one (B : Set AmbientSpace) :
    D.IsBoxLocalObservable B (fun _ => (1 : ℂ)) :=
  ⟨⟨measurable_const, 1, fun _ => by simp⟩, fun _ _ _ => rfl⟩
theorem wilsonKernelAt_eq_div (B : Set AmbientSpace) {Φ : D.GaugeField → ℂ}
    (hΦ : DependsOnlyOnLinks (D.boxLinks B : Set D.Link) Φ) (η : D.GaugeField) :
    D.wilsonKernelAt (D.boxLinks B) (D.coe_boxLinks_subset_positive B) Φ η =
      D.boundaryConditionPartition B η Φ / D.boundaryConditionPartition B η (fun _ => 1) := by
  have hnum : D.boundaryConditionPartition B η Φ = ∫ U, Φ (D.overwriteBox B U η) *
      (Real.exp (-D.β * ∑ᶠ p ∈ plaquettesTouching (D.boxLinks B),
        faceEnergy (D.overwriteBox B U η) p) : ℂ) ∂D.boxHaar B := by
    simp only [ChessboardSetup.boundaryConditionPartition, ChessboardSetup.evalOnBox_eq_overwriteBox hΦ _ η]
  have hden : D.boundaryConditionPartition B η (fun _ => 1) =
      ((∫ U, Real.exp (-D.β * ∑ᶠ p ∈ plaquettesTouching (D.boxLinks B),
        faceEnergy (D.overwriteBox B U η) p) ∂D.boxHaar B : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp [ChessboardSetup.boundaryConditionPartition, ChessboardSetup.evalOnBox]
  rw [hnum, hden]
  exact wilsonLinkKernel_apply D.β _ _ Φ η
theorem liftedExpectation_eq_div (hform : D.LiftedExpectationFormula)
    (hzero : D.partitionFunction 0 = D.torusPartition (fun _ => 1))
    {Φ : D.GaugeField → ℂ} (hΦ : IsBoundedObservable Φ) :
    D.liftedExpectation Φ = D.torusPartition Φ / D.torusPartition (fun _ => 1) := by
  rw [hform Φ hΦ, hzero, div_eq_inv_mul]
  congr 1
  simp only [ChessboardSetup.torusPartition, PeriodicLattice.boltzmannWeight]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp
end BoxVersusTorusViaFreeBoundary
open BoxVersusTorusViaFreeBoundary in
theorem BoxVersusTorusViaFreeBoundary.proof
    (hfree : FreeBoxComparison.Statement)
    (htorus : TorusVersusFreeBox.Statement)
    (hcount : BoxBoundaryCount.Statement)
    (hzero : ZeroSourcePartition.Statement)
    (hquot : BoxTorusQuotient.Statement) :
    BoxVersusTorusViaFreeBoundary.Statement := by
  intro D g hg hside B hB Φ hΦ hΦ₀ η
  obtain ⟨hF₁, hout⟩ := hfree D g hg hside B hB
  have hone := isBoxLocalObservable_const_one D B
  obtain ⟨hF, hch⟩ := hout Φ hΦ hΦ₀
  obtain ⟨ha, hb⟩ := hch η
  obtain ⟨-, hch₁⟩ := hout _ hone (fun _ => zero_le_one)
  obtain ⟨ha₁, hb₁⟩ := hch₁ η
  obtain ⟨hc, hd⟩ := htorus D g hg hside B hB Φ hΦ hΦ₀
  obtain ⟨hc₁, hd₁⟩ := htorus D g hg hside B hB _ hone (fun _ => zero_le_one)
  have hn := hcount D g hg hside B hB
  have hform : D.LiftedExpectationFormula := ((hquot ⟨D, g, hg⟩).2 hside).2.2
  have hker := wilsonKernelAt_eq_div D B hΦ.2 η
  have hlift := liftedExpectation_eq_div D hform (hzero D) hΦ.1
  set c₁ := Real.exp (-2 * D.β * (D.boundaryPlaquetteCount B : ℝ)) with hc₁def
  set c₂ := Real.exp (-2 * D.β * (D.torusBoundaryPlaquetteCount B : ℝ)) with hc₂def
  have hc₁pos : 0 < c₁ := Real.exp_pos _
  have hc₂pos : 0 < c₂ := Real.exp_pos _
  have hprod : Real.exp (2 * D.β *
      ((D.boundaryPlaquetteCount B + D.torusBoundaryPlaquetteCount B : ℕ) : ℝ)) = c₁⁻¹ * c₂⁻¹ := by
    rw [hc₁def, hc₂def, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    push_cast
    ring
  refine ⟨ha, hb, hc, hd, hn, ?_, ?_⟩
  all_goals
    obtain ⟨f, hf, hfe⟩ := exists_real_eq_of_nonneg hF
    obtain ⟨f₁, hf₁, hfe₁⟩ := exists_real_eq_of_nonneg hF₁.le
    rw [hfe] at ha hb hc hd
    rw [hfe₁] at ha₁ hb₁ hc₁ hd₁ hF₁
    obtain ⟨x, hx, hxe⟩ := exists_real_eq_of_le_ofReal hb
    obtain ⟨x₁, hx₁, hxe₁⟩ := exists_real_eq_of_le_ofReal hb₁
    obtain ⟨t, ht, hte⟩ := exists_real_eq_of_le_ofReal hd
    obtain ⟨t₁, ht₁, hte₁⟩ := exists_real_eq_of_le_ofReal hd₁
    rw [hxe₁, ← Complex.ofReal_mul, Complex.real_le_real] at ha₁
    rw [hte, ← Complex.ofReal_mul, Complex.real_le_real] at hc
    rw [hte₁, ← Complex.ofReal_mul, Complex.real_le_real] at hc₁
    have hf₁pos : 0 < f₁ := by exact_mod_cast hF₁
    have ht₁pos : 0 < t₁ := lt_of_lt_of_le (mul_pos hc₂pos hf₁pos) hc₁
  · rw [hker, hlift, hxe, hxe₁, hte, hte₁, hprod, ← Complex.ofReal_div, ← Complex.ofReal_div,
      ← Complex.ofReal_mul, Complex.real_le_real]
    exact div_le_inv_mul_inv_mul_div hc₁pos hc₂pos hf hf₁pos hx ha₁ hc ht₁ hc₁
  · have ht₀ : 0 ≤ t := le_trans (mul_nonneg hc₂pos.le hf) hc
    have hle : Real.exp (2 * D.β *
        ((D.boundaryPlaquetteCount B + D.torusBoundaryPlaquetteCount B : ℕ) : ℝ)) ≤
        Real.exp (2 * (boxBoundaryConstant : ℝ) * D.β *
          (PeriodicLattice.torusSide D.L D.m / D.mesh) ^ 3) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hn (by linarith [D.beta_pos] : 0 ≤ 2 * D.β)
      linarith
    rw [hlift, hte, hte₁, ← Complex.ofReal_div, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.real_le_real]
    exact mul_le_mul_of_nonneg_right hle (div_nonneg ht₀ ht₁pos.le)
end ChessboardTori
end YangMills.Construction
end

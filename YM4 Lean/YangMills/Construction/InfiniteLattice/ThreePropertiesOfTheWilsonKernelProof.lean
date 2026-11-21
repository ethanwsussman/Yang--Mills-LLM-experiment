import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndWhatAnObservableReads
import YangMills.Construction.InfiniteLattice.ThreePropertiesOfTheWilsonKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory InfiniteLattice Matrices
namespace LatticePhases.WilsonKernelProperties
variable {a : ℝ}
theorem faceEnergy_bounds (U : GaugeField a) (p : ElementaryPlaquette a) :
    0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2 := by
  have hu : ((faceHolonomy U p : ComplexMatrix2.specialUnitary) : ComplexMatrix2) ∈
      Matrix.unitaryGroup (Fin 2) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup (faceHolonomy U p).2
  have h0 := entry_norm_bound_of_unitary hu 0 0
  have h1 := entry_norm_bound_of_unitary hu 1 1
  have hre : |(ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re| ≤ 2 := by
    rw [ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Complex.add_re]
    refine (abs_add_le _ _).trans ?_
    have e0 := Complex.abs_re_le_norm
      (((faceHolonomy U p : ComplexMatrix2.specialUnitary) : ComplexMatrix2) 0 0)
    have e1 := Complex.abs_re_le_norm
      (((faceHolonomy U p : ComplexMatrix2.specialUnitary) : ComplexMatrix2) 1 1)
    linarith
  have := abs_le.mp hre
  unfold faceEnergy
  constructor <;> linarith [this.1, this.2]
namespace HeatBath
variable (W : OrientedLinkSet a)
theorem energy_bounds (U : GaugeField a) :
    0 ≤ W.energy U ∧ W.energy U ≤ 2 * (W.faceCount : ℝ) := by
  have hn : W.faceCount = W.faces_finite.toFinset.card :=
    Set.ncard_eq_toFinset_card _ W.faces_finite
  constructor
  · exact Finset.sum_nonneg fun p _ => (faceEnergy_bounds U p).1
  · calc W.energy U ≤ ∑ _p ∈ W.faces_finite.toFinset, (2 : ℝ) :=
          Finset.sum_le_sum fun p _ => (faceEnergy_bounds U p).2
      _ = 2 * (W.faceCount : ℝ) := by
          rw [hn, Finset.sum_const, nsmul_eq_mul, mul_comm]
instance instSecondCountableSpecialUnitary :
    SecondCountableTopology ComplexMatrix2.specialUnitary :=
  haveI : SecondCountableTopology ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _
instance isProbabilityMeasure_resampleHaar : IsProbabilityMeasure W.resampleHaar := by
  unfold OrientedLinkSet.resampleHaar LinkVariables.haarMeasure ComplexMatrix2.haarPi
  infer_instance
theorem integrable_of_continuous {E : Type*} [NormedAddCommGroup E] {f : W.Resample → E}
    (hf : Continuous f) : Integrable f W.resampleHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
theorem continuous_glue_field (V : W.Resample) :
    Continuous fun U : GaugeField a => W.glue V U := by
  have key : Continuous fun U : GaugeField a =>
      ((W.glue V U : GaugeField a) : Link a → ComplexMatrix2.specialUnitary) := by
    refine continuous_pi fun b => ?_
    by_cases hb : b ∈ (W.links : Set (Link a))
    · have e : ∀ U : GaugeField a, W.glue V U b = V ⟨b, hb⟩ := fun U => dif_pos hb
      simp only [e]
      exact continuous_const
    · by_cases hr : b.opposite ∈ (W.links : Set (Link a))
      · have e : ∀ U : GaugeField a, W.glue V U b = (V ⟨b.opposite, hr⟩)⁻¹ := fun U =>
          (dif_neg hb).trans (dif_pos hr)
        simp only [e]
        exact continuous_const
      · have e : ∀ U : GaugeField a, W.glue V U b = U b := fun U =>
          (dif_neg hb).trans (dif_neg hr)
        simp only [e]
        exact continuous_gaugeField_eval b
  exact Continuous.subtype_mk key _
theorem glue_apply_of_not_mem (V : W.Resample) (U : GaugeField a) {b : Link a}
    (hb : b ∉ W.links) (hr : b.opposite ∉ W.links) : W.glue V U b = U b :=
  (dif_neg (by simpa using hb)).trans (dif_neg (by simpa using hr))
theorem glue_congr (V : W.Resample) {U U' : GaugeField a} {b : Link a} (h : U b = U' b) :
    W.glue V U b = W.glue V U' b := by
  by_cases hb : b ∈ (W.links : Set (Link a))
  · have e : ∀ U : GaugeField a, W.glue V U b = V ⟨b, hb⟩ := fun U => dif_pos hb
    rw [e, e]
  · by_cases hr : b.opposite ∈ (W.links : Set (Link a))
    · have e : ∀ U : GaugeField a, W.glue V U b = (V ⟨b.opposite, hr⟩)⁻¹ := fun U =>
        (dif_neg hb).trans (dif_pos hr)
      rw [e, e]
    · have e : ∀ U : GaugeField a, W.glue V U b = U b := fun U =>
        (dif_neg hb).trans (dif_neg hr)
      rw [e, e, h]
def unnormalizedWeight (x : ℝ) (U : GaugeField a) (V : W.Resample) : ℝ :=
  Real.exp (-x * W.energy (W.glue V U))
def partitionFunction (x : ℝ) (U : GaugeField a) : ℝ :=
  ∫ V, unnormalizedWeight W x U V ∂W.resampleHaar
theorem boltzmannDensity_eq (x : ℝ) (U : GaugeField a) (V : W.Resample) :
    W.boltzmannDensity x U V = unnormalizedWeight W x U V / partitionFunction W x U := rfl
theorem continuous_unnormalizedWeight (x : ℝ) (U : GaugeField a) :
    Continuous (unnormalizedWeight W x U) :=
  Real.continuous_exp.comp (continuous_const.mul (W.continuous_energy.comp (W.continuous_glue U)))
theorem continuous_unnormalizedWeight_field (x : ℝ) (V : W.Resample) :
    Continuous fun U : GaugeField a => unnormalizedWeight W x U V :=
  Real.continuous_exp.comp
    (continuous_const.mul (W.continuous_energy.comp (continuous_glue_field W V)))
theorem unnormalizedWeight_pos (x : ℝ) (U : GaugeField a) (V : W.Resample) :
    0 < unnormalizedWeight W x U V :=
  Real.exp_pos _
theorem unnormalizedWeight_le_one {x : ℝ} (hx : 0 < x) (U : GaugeField a) (V : W.Resample) :
    unnormalizedWeight W x U V ≤ 1 := by
  refine Real.exp_le_one_iff.mpr ?_
  have := (energy_bounds W (W.glue V U)).1
  nlinarith
theorem partitionFunction_pos {x : ℝ} (hx : 0 < x) (U : GaugeField a) :
    0 < partitionFunction W x U := by
  have hlow : ∀ V, Real.exp (-x * (2 * (W.faceCount : ℝ))) ≤ unnormalizedWeight W x U V :=
    fun V => by
      refine Real.exp_le_exp.mpr ?_
      have := (energy_bounds W (W.glue V U)).2
      nlinarith
  have hmono : ∫ _V : W.Resample, Real.exp (-x * (2 * (W.faceCount : ℝ))) ∂W.resampleHaar ≤
      partitionFunction W x U :=
    integral_mono (integrable_const _)
      (integrable_of_continuous W (continuous_unnormalizedWeight W x U)) hlow
  rw [integral_const, probReal_univ, one_smul] at hmono
  exact (Real.exp_pos _).trans_le hmono
theorem continuous_boltzmannDensity {x : ℝ} (U : GaugeField a) :
    Continuous (W.boltzmannDensity x U) :=
  (continuous_unnormalizedWeight W x U).div_const _
theorem boltzmannDensity_pos {x : ℝ} (hx : 0 < x) (U : GaugeField a) (V : W.Resample) :
    0 < W.boltzmannDensity x U V :=
  div_pos (unnormalizedWeight_pos W x U V) (partitionFunction_pos W hx U)
theorem integral_boltzmannDensity {x : ℝ} (hx : 0 < x) (U : GaugeField a) :
    ∫ V, W.boltzmannDensity x U V ∂W.resampleHaar = 1 := by
  simp only [boltzmannDensity_eq]
  rw [integral_div]
  exact div_self (partitionFunction_pos W hx U).ne'
theorem norm_le_supNorm {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (U : GaugeField a) : ‖F U‖ ≤ observableSupNorm F := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.norm_le_supNorm <;> assumption
theorem supNorm_nonneg (F : GaugeField a → ℂ) : 0 ≤ observableSupNorm F :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem continuous_comp_glue {F : GaugeField a → ℂ} (hF : Continuous F) (U : GaugeField a) :
    Continuous fun V : W.Resample => F (W.glue V U) :=
  hF.comp (W.continuous_glue U)
theorem integrable_heatBath_integrand {F : GaugeField a → ℂ} (hF : Continuous F) (x : ℝ)
    (U : GaugeField a) :
    Integrable (fun V : W.Resample => F (W.glue V U) * (W.boltzmannDensity x U V : ℂ))
      W.resampleHaar :=
  integrable_of_continuous W ((continuous_comp_glue W hF U).mul
    (Complex.continuous_ofReal.comp (continuous_boltzmannDensity W U)))
theorem continuous_parametric_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : GaugeField a → W.Resample → E) (C : ℝ) (hV : ∀ U, Continuous (Φ U))
    (hU : ∀ V, Continuous fun U => Φ U V) (hC : ∀ U V, ‖Φ U V‖ ≤ C) :
    Continuous fun U => ∫ V, Φ U V ∂W.resampleHaar := by
  have : FirstCountableTopology (GaugeField a) :=
    inferInstanceAs (FirstCountableTopology
      ({U : Link a → ComplexMatrix2.specialUnitary | ∀ b, U b.opposite = (U b)⁻¹} :
        Set (Link a → ComplexMatrix2.specialUnitary)))
  exact continuous_of_dominated (fun U => (hV U).aestronglyMeasurable)
    (fun U => Filter.Eventually.of_forall (hC U)) (integrable_const C)
    (Filter.Eventually.of_forall hU)
theorem heatBath_eq_div (x : ℝ) (F : GaugeField a → ℂ) (U : GaugeField a) :
    W.heatBath x F U = (∫ V, F (W.glue V U) * (unnormalizedWeight W x U V : ℂ) ∂W.resampleHaar) /
      (partitionFunction W x U : ℂ) := by
  rw [← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  simp only [boltzmannDensity_eq, Complex.ofReal_div, mul_div_assoc]
theorem continuous_partitionFunction {x : ℝ} (hx : 0 < x) :
    Continuous (partitionFunction W x) :=
  continuous_parametric_integral W (unnormalizedWeight W x) 1
    (continuous_unnormalizedWeight W x) (continuous_unnormalizedWeight_field W x)
    fun U V => by
      rw [Real.norm_of_nonneg (unnormalizedWeight_pos W x U V).le]
      exact unnormalizedWeight_le_one W hx U V
theorem continuous_heatBath {x : ℝ} (hx : 0 < x) {F : GaugeField a → ℂ} (hc : Continuous F)
    (hF : IsBoundedObservable F) : Continuous (W.heatBath x F) := by
  have e : W.heatBath x F = fun U =>
      (∫ V, F (W.glue V U) * (unnormalizedWeight W x U V : ℂ) ∂W.resampleHaar) /
        (partitionFunction W x U : ℂ) := funext (heatBath_eq_div W x F)
  rw [e]
  refine Continuous.div ?_
    (Complex.continuous_ofReal.comp (continuous_partitionFunction W hx)) ?_
  · refine continuous_parametric_integral W _ (observableSupNorm F) (fun U => ?_) (fun V => ?_)
      fun U V => ?_
    · exact (continuous_comp_glue W hc U).mul
        (Complex.continuous_ofReal.comp (continuous_unnormalizedWeight W x U))
    · exact (hc.comp (continuous_glue_field W V)).mul
        (Complex.continuous_ofReal.comp (continuous_unnormalizedWeight_field W x V))
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (unnormalizedWeight_pos W x U V).le]
      calc ‖F (W.glue V U)‖ * unnormalizedWeight W x U V ≤ observableSupNorm F * 1 :=
            mul_le_mul (norm_le_supNorm hF _) (unnormalizedWeight_le_one W hx U V)
              (unnormalizedWeight_pos W x U V).le (supNorm_nonneg F)
        _ = observableSupNorm F := mul_one _
  · intro U
    exact Complex.ofReal_ne_zero.mpr (partitionFunction_pos W hx U).ne'
theorem norm_heatBath_le {x : ℝ} (hx : 0 < x) {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) (U : GaugeField a) :
    ‖W.heatBath x F U‖ ≤ observableSupNorm F := by
  have hint : Integrable (fun V => observableSupNorm F * W.boltzmannDensity x U V)
      W.resampleHaar :=
    (integrable_of_continuous W (continuous_boltzmannDensity W U)).const_mul _
  calc ‖W.heatBath x F U‖ ≤ ∫ V, observableSupNorm F * W.boltzmannDensity x U V ∂W.resampleHaar :=
        norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun V => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (boltzmannDensity_pos W hx U V).le]
          exact mul_le_mul_of_nonneg_right (norm_le_supNorm hF _)
            (boltzmannDensity_pos W hx U V).le)
    _ = observableSupNorm F := by
        rw [integral_const_mul, integral_boltzmannDensity W hx, mul_one]
theorem heatBath_isLinear (x : ℝ) : IsLinearOnContinuousLocal W x := by
  intro c₁ c₂ F₁ F₂ h₁ h₂
  funext U
  have e : ∀ V : W.Resample,
      (c₁ * F₁ (W.glue V U) + c₂ * F₂ (W.glue V U)) * (W.boltzmannDensity x U V : ℂ) =
        c₁ * (F₁ (W.glue V U) * (W.boltzmannDensity x U V : ℂ)) +
          c₂ * (F₂ (W.glue V U) * (W.boltzmannDensity x U V : ℂ)) := fun V => by ring
  simp only [OrientedLinkSet.heatBath, e]
  rw [integral_add ((integrable_heatBath_integrand W h₁.2.2 x U).const_mul _)
    ((integrable_heatBath_integrand W h₂.2.2 x U).const_mul _), integral_const_mul,
    integral_const_mul]
def faceCorners : Set AmbientSpace :=
  ⋃ p ∈ W.faces, ⋃ b ∈ {b | b ∈ p.edges},
    {((b : Link a).initial : AmbientSpace), (b.terminal : AmbientSpace)}
theorem isBounded_faceCorners : Bornology.IsBounded (faceCorners W) :=
  (W.faces_finite.biUnion fun p _ => (List.finite_toSet p.edges).biUnion fun _ _ =>
    Set.toFinite _).isBounded
theorem heatBath_congr (x : ℝ) {F : GaugeField a → ℂ} {S : Set AmbientSpace}
    (hF : ∀ U U' : GaugeField a, (∀ b : Link a, b ∈ linksWithin S → U b = U' b) → F U = F U')
    {U U' : GaugeField a}
    (h : ∀ b : Link a, b ∈ linksWithin (S ∪ faceCorners W) → U b = U' b) :
    W.heatBath x F U = W.heatBath x F U' := by
  have hglue : ∀ (V : W.Resample) (b : Link a), b ∈ linksWithin (S ∪ faceCorners W) →
      W.glue V U b = W.glue V U' b := fun V b hb => glue_congr W V (h b hb)
  have hFV : ∀ V : W.Resample, F (W.glue V U) = F (W.glue V U') := fun V =>
    hF _ _ fun b hb => hglue V b ⟨Or.inl hb.1, Or.inl hb.2⟩
  have hE : ∀ V : W.Resample, W.energy (W.glue V U) = W.energy (W.glue V U') := fun V => by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p ∈ W.faces := W.faces_finite.mem_toFinset.mp hp
    refine WilsonOperator.faceEnergy_congr p fun b hb => hglue V b ?_
    have hmem : ∀ y ∈ ({((b : Link a).initial : AmbientSpace), (b.terminal : AmbientSpace)} :
        Set AmbientSpace), y ∈ faceCorners W := fun y hy =>
      Set.mem_biUnion hp' (Set.mem_biUnion (show b ∈ {b | b ∈ p.edges} from hb) hy)
    exact ⟨Or.inr (hmem _ (by simp)), Or.inr (hmem _ (by simp))⟩
  simp only [OrientedLinkSet.heatBath, OrientedLinkSet.boltzmannDensity, hE, hFV]
theorem div_bounds_of_sandwich {E w I Z m M : ℝ} (hE : 0 < E) (hZ : 0 < Z) (hI : 0 < I)
    (hm : 0 < m) (hM : 0 < M) (hmM : M * m = 1) (hw₁ : m ≤ w) (hw₂ : w ≤ M)
    (hI₁ : m * Z ≤ I) (hI₂ : I ≤ M * Z) :
    E * w / I ≤ M * M * (E / Z) ∧ m * m * (E / Z) ≤ E * w / I := by
  have hc : E / Z * Z = E := div_mul_cancel₀ _ hZ.ne'
  constructor
  · rw [div_le_iff₀ hI]
    calc E * w ≤ E * M := mul_le_mul_of_nonneg_left hw₂ hE.le
      _ = M * M * (E / Z) * (m * Z) := by
          calc E * M = (M * m) * M * (E / Z * Z) := by rw [hmM, hc]; ring
            _ = M * M * (E / Z) * (m * Z) := by ring
      _ ≤ M * M * (E / Z) * I := mul_le_mul_of_nonneg_left hI₁ (by positivity)
  · rw [le_div_iff₀ hI]
    calc m * m * (E / Z) * I ≤ m * m * (E / Z) * (M * Z) :=
          mul_le_mul_of_nonneg_left hI₂ (by positivity)
      _ = E * m := by
          calc m * m * (E / Z) * (M * Z) = (M * m) * m * (E / Z * Z) := by ring
            _ = E * m := by rw [hmM, hc]; ring
      _ ≤ E * w := mul_le_mul_of_nonneg_left hw₁ hE.le
theorem abs_boltzmannDensity_sub_le {x y : ℝ} (hy : 0 < y) (U : GaugeField a)
    (V : W.Resample) :
    |W.boltzmannDensity x U V - W.boltzmannDensity y U V| ≤
      (Real.exp (2 * |x - y| * (W.faceCount : ℝ)) - 1) * W.boltzmannDensity y U V := by
  set n : ℝ := (W.faceCount : ℝ) with hn
  set c : ℝ := |x - y| * n with hcdef
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  let A : W.Resample → ℝ := fun V => W.energy (W.glue V U)
  let w : W.Resample → ℝ := fun V => Real.exp (-(x - y) * (A V - n))
  let k : ℝ := Real.exp (-(x - y) * n)
  have hwc : Continuous w := Real.continuous_exp.comp (continuous_const.mul
    ((W.continuous_energy.comp (W.continuous_glue U)).sub continuous_const))
  have hsplit : ∀ V, unnormalizedWeight W x U V = unnormalizedWeight W y U V * w V * k :=
    fun V => by
      simp only [unnormalizedWeight, w, k, A]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
  have hdev : ∀ V, |(x - y) * (A V - n)| ≤ c := fun V => by
    have h := energy_bounds W (W.glue V U)
    have habs : |A V - n| ≤ n := abs_le.mpr ⟨by simp only [A]; linarith [h.1],
      by simp only [A]; linarith [h.2]⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  have hw₁ : ∀ V, Real.exp (-c) ≤ w V := fun V => by
    refine Real.exp_le_exp.mpr ?_
    have := (abs_le.mp (hdev V)).2
    linarith
  have hw₂ : ∀ V, w V ≤ Real.exp c := fun V => by
    refine Real.exp_le_exp.mpr ?_
    have := (abs_le.mp (hdev V)).1
    linarith
  have hZ : 0 < partitionFunction W y U := partitionFunction_pos W hy U
  have hwy : Integrable (unnormalizedWeight W y U) W.resampleHaar :=
    integrable_of_continuous W (continuous_unnormalizedWeight W y U)
  have hwyw : Integrable (fun V => unnormalizedWeight W y U V * w V) W.resampleHaar :=
    integrable_of_continuous W ((continuous_unnormalizedWeight W y U).mul hwc)
  set I : ℝ := ∫ V, unnormalizedWeight W y U V * w V ∂W.resampleHaar with hIdef
  have hI₁ : Real.exp (-c) * partitionFunction W y U ≤ I := by
    rw [partitionFunction, ← integral_const_mul]
    refine integral_mono (hwy.const_mul _) hwyw fun V => ?_
    have := mul_le_mul_of_nonneg_left (hw₁ V) (unnormalizedWeight_pos W y U V).le
    simpa [mul_comm] using this
  have hI₂ : I ≤ Real.exp c * partitionFunction W y U := by
    rw [partitionFunction, ← integral_const_mul]
    refine integral_mono hwyw (hwy.const_mul _) fun V => ?_
    have := mul_le_mul_of_nonneg_left (hw₂ V) (unnormalizedWeight_pos W y U V).le
    simpa [mul_comm] using this
  have hIpos : 0 < I := (mul_pos (Real.exp_pos _) hZ).trans_le hI₁
  have hk : 0 < k := Real.exp_pos _
  have hZx : partitionFunction W x U = I * k := by
    rw [hIdef, ← integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have hgx : W.boltzmannDensity x U V = unnormalizedWeight W y U V * w V / I := by
    rw [boltzmannDensity_eq, hZx, hsplit V]
    exact mul_div_mul_right _ _ hk.ne'
  have hgy : W.boltzmannDensity y U V = unnormalizedWeight W y U V / partitionFunction W y U :=
    rfl
  have hmM : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
  obtain ⟨hup, hlow⟩ := div_bounds_of_sandwich (unnormalizedWeight_pos W y U V) hZ hIpos
    (Real.exp_pos (-c)) (Real.exp_pos c) hmM (hw₁ V) (hw₂ V) hI₁ hI₂
  rw [← hgx, ← hgy] at hup hlow
  have hexp : Real.exp (2 * |x - y| * n) = Real.exp c * Real.exp c := by
    rw [← Real.exp_add]
    congr 1
    rw [hcdef]
    ring
  have hexp' : Real.exp (-c) * Real.exp (-c) + Real.exp c * Real.exp c ≥ 2 := by
    have h1 := Real.add_one_le_exp (-c + -c)
    have h2 := Real.add_one_le_exp (c + c)
    rw [Real.exp_add] at h1 h2
    linarith
  have hgpos := boltzmannDensity_pos W hy U V
  rw [hexp, abs_le]
  constructor
  · nlinarith
  · linarith
theorem norm_heatBath_sub_le {x y : ℝ} (hy : 0 < y) {F : GaugeField a → ℂ}
    (hc : Continuous F) (hF : IsBoundedObservable F) (U : GaugeField a) :
    ‖W.heatBath x F U - W.heatBath y F U‖ ≤
      observableSupNorm F * (Real.exp (2 * |x - y| * (W.faceCount : ℝ)) - 1) := by
  set t : ℝ := Real.exp (2 * |x - y| * (W.faceCount : ℝ)) - 1 with ht
  have hint : Integrable (fun V => observableSupNorm F * (t * W.boltzmannDensity y U V))
      W.resampleHaar :=
    ((integrable_of_continuous W (continuous_boltzmannDensity W U)).const_mul _).const_mul _
  have e : W.heatBath x F U - W.heatBath y F U =
      ∫ V, F (W.glue V U) *
        ((W.boltzmannDensity x U V - W.boltzmannDensity y U V : ℝ) : ℂ) ∂W.resampleHaar := by
    simp only [OrientedLinkSet.heatBath]
    rw [← integral_sub (integrable_heatBath_integrand W hc x U)
      (integrable_heatBath_integrand W hc y U)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
    simp only [Complex.ofReal_sub]
    ring
  rw [e]
  calc ‖∫ V, F (W.glue V U) *
        ((W.boltzmannDensity x U V - W.boltzmannDensity y U V : ℝ) : ℂ) ∂W.resampleHaar‖
      ≤ ∫ V, observableSupNorm F * (t * W.boltzmannDensity y U V) ∂W.resampleHaar :=
        norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun V => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul (norm_le_supNorm hF _) (abs_boltzmannDensity_sub_le W hy U V)
            (abs_nonneg _) (supNorm_nonneg F))
    _ = observableSupNorm F * t := by
        rw [integral_const_mul, integral_const_mul, integral_boltzmannDensity W hy, mul_one]
end HeatBath
open HeatBath in
theorem holds (reads : ObservableRegions.Statement) : Statement := by
  intro D W β' β'' hβ' hβ'' F hF
  obtain ⟨hFo, ⟨S₀, hS₀, hFS₀⟩, hFc⟩ := hF
  have hkc := continuous_heatBath W hβ' hFc hFo
  have hnorm : ∀ U, ‖W.heatBath β' F U‖ ≤ observableSupNorm F := norm_heatBath_le W hβ' hFo
  have hko : IsBoundedObservable (W.heatBath β' F) := ⟨hkc.measurable, _, hnorm⟩
  refine ⟨⟨energy_bounds W, fun U => ⟨(continuous_boltzmannDensity W U).measurable,
      fun V => (boltzmannDensity_pos W hβ' U V).le, integral_boltzmannDensity W hβ' U⟩⟩,
    ⟨heatBath_isLinear W β', Real.iSup_le hnorm (supNorm_nonneg F), hko, ?_, hkc⟩, ?_, ?_⟩
  · have hFmem : F ∈ regionObservables D.mesh S₀ := ⟨hFo, hFS₀⟩
    have hread : ∀ U U' : GaugeField D.mesh,
        (∀ b : Link D.mesh, b ∈ linksWithin S₀ → U b = U' b) → F U = F U' :=
      (((reads D S₀ S₀).2.1 F hFo).out 0 1).mp hFmem
    have hmem : W.heatBath β' F ∈ regionObservables D.mesh (S₀ ∪ faceCorners W) :=
      (((reads D (S₀ ∪ faceCorners W) (S₀ ∪ faceCorners W)).2.1 _ hko).out 0 1).mpr
        fun U U' h => heatBath_congr W β' hread h
    exact ⟨S₀ ∪ faceCorners W, hS₀.union (isBounded_faceCorners W), hmem.2⟩
  · intro S H _ hHS hS
    have hread : ∀ U U' : GaugeField D.mesh,
        (∀ b : Link D.mesh, b ∈ linksWithin S → U b = U' b) → H U = H U' :=
      (((reads D S S).2.1 H hHS.1).out 0 1).mp hHS
    funext U
    have hHV : ∀ V : W.Resample, H (W.glue V U) = H U := fun V => by
      refine hread _ _ fun b hb => glue_apply_of_not_mem W V U (fun hbW => ?_) fun hrW => ?_
      · exact (hS b hbW).1 hb.1
      · exact (hS _ hrW).1 hb.2
    simp only [OrientedLinkSet.heatBath, hHV, mul_assoc]
    rw [integral_const_mul]
  · refine Real.iSup_le (fun U => norm_heatBath_sub_le W hβ'' hFc hFo U)
      (mul_nonneg (supNorm_nonneg F) (sub_nonneg.mpr (Real.one_le_exp (by positivity))))
end LatticePhases.WilsonKernelProperties
end YangMills.Construction

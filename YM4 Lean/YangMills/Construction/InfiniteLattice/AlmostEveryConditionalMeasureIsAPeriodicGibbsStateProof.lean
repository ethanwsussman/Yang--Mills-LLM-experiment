import YangMills.Construction.InfiniteLattice.AlmostEveryConditionalMeasureIsAPeriodicGibbsState
import YangMills.Construction.InfiniteLattice.GibbsStatesReadThroughKernelsAndSymmetries
import YangMills.Construction.InfiniteLattice.GroupOfTheLatticeIsometriesAndItsAction
import YangMills.Construction.InfiniteLattice.InvarianceOfAMeasureUnderAMotion
import YangMills.Construction.InfiniteLattice.InvariantDensitiesOfAPeriodicGibbsState
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAreConvexAndWeaklyCompact
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.ThreePropertiesOfTheWilsonKernel
import YangMills.Construction.InfiniteLattice.TopologyAndDensityOnTheConfigurationsOfOneLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.LatticePhases.ConditionalGibbsProof
section General
variable {a : ℝ}
theorem integrable_of_isBoundedObservable (μ : Measure (GaugeField a)) [IsFiniteMeasure μ]
    {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) : Integrable A μ := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.integrable_of_isBoundedObservable <;> assumption
theorem isBoundedObservable_mul {A B : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (hB : IsBoundedObservable B) : IsBoundedObservable fun U => A U * B U := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.isBoundedObservable_mul <;> assumption
theorem isBoundedObservable_sub {A B : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (hB : IsBoundedObservable B) : IsBoundedObservable fun U => A U - B U := by
  obtain ⟨hm, C, hC⟩ := hA
  obtain ⟨hm', C', hC'⟩ := hB
  exact ⟨hm.sub hm', C + C', fun U => (norm_sub_le _ _).trans (add_le_add (hC U) (hC' U))⟩
theorem norm_eval_le (ρ : ProbMeasure (GaugeField a)) {G : GaugeField a → ℂ} {C : ℝ}
    (hC : ∀ U, ‖G U‖ ≤ C) : ‖ρ.eval G‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := ρ.toMeasure) (f := G) (C := C)
    (Filter.Eventually.of_forall hC)
  simpa [ProbMeasure.eval] using h
theorem eval_sub (ρ : ProbMeasure (GaugeField a)) {A B : GaugeField a → ℂ}
    (hA : IsBoundedObservable A) (hB : IsBoundedObservable B) :
    ρ.eval (fun U => A U - B U) = ρ.eval A - ρ.eval B :=
  integral_sub (integrable_of_isBoundedObservable _ hA) (integrable_of_isBoundedObservable _ hB)
theorem norm_le_uniformSup {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) (U : GaugeField a) :
    ‖A U‖ ≤ uniformSup A := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.norm_le_supNorm <;> assumption
theorem ae_eq_zero_of_integral_conj_mul_self (μ : Measure (GaugeField a)) [IsFiniteMeasure μ]
    {d : GaugeField a → ℂ} (hd : IsBoundedObservable d) (h : ∫ U, conj (d U) * d U ∂μ = 0) :
    ∀ᵐ U ∂μ, d U = 0 := by
  have e : ∀ U, conj (d U) * d U = ((‖d U‖ ^ 2 : ℝ) : ℂ) := fun U => by
    rw [Complex.conj_mul']
    push_cast
    rfl
  simp only [e] at h
  rw [integral_complex_ofReal] at h
  have h0 : ∫ U, ‖d U‖ ^ 2 ∂μ = 0 := by exact_mod_cast h
  have hi : Integrable (fun U => ‖d U‖ ^ 2) μ := by
    obtain ⟨hm, C, hC⟩ := hd
    refine Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
      (ae_of_all _ fun U => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC U) 2
  have hz := (integral_eq_zero_iff_of_nonneg (fun U => by positivity) hi).mp h0
  filter_upwards [hz] with U hU
  have : ‖d U‖ ^ 2 = 0 := hU
  simpa using this
theorem ae_eval_eq_of_condExp (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ]
    (κ : GaugeField a → ProbMeasure (GaugeField a)) {G G' : GaugeField a → ℂ}
    (hG : IsBoundedObservable G) (hG' : IsBoundedObservable G')
    (hκ : Measurable[shiftInvariantSigma a] (fun U => (κ U).eval G) ∧
      ∀ J : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] J → (∃ C : ℝ, ∀ U, ‖J U‖ ≤ C) →
        ∫ U, J U * (κ U).eval G ∂μ = ∫ U, J U * G U ∂μ)
    (hκ' : Measurable[shiftInvariantSigma a] (fun U => (κ U).eval G') ∧
      ∀ J : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] J → (∃ C : ℝ, ∀ U, ‖J U‖ ≤ C) →
        ∫ U, J U * (κ U).eval G' ∂μ = ∫ U, J U * G' U ∂μ)
    (h : ∀ J : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] J → (∃ C : ℝ, ∀ U, ‖J U‖ ≤ C) →
      ∫ U, J U * G U ∂μ = ∫ U, J U * G' U ∂μ) :
    ∀ᵐ U ∂μ, (κ U).eval G = (κ U).eval G' := by
  obtain ⟨-, C, hC⟩ := hG
  obtain ⟨-, C', hC'⟩ := hG'
  have hb : ∀ U, ‖(κ U).eval G‖ ≤ C := fun U => norm_eval_le _ hC
  have hb' : ∀ U, ‖(κ U).eval G'‖ ≤ C' := fun U => norm_eval_le _ hC'
  have borel : ∀ {f : GaugeField a → ℂ}, Measurable[shiftInvariantSigma a] f → Measurable f :=
    fun hf => hf.mono (fun _ hs => hs.1) le_rfl
  have oV : IsBoundedObservable fun U => (κ U).eval G := ⟨borel hκ.1, C, hb⟩
  have oV' : IsBoundedObservable fun U => (κ U).eval G' := ⟨borel hκ'.1, C', hb'⟩
  have hdm : Measurable[shiftInvariantSigma a] fun U => (κ U).eval G - (κ U).eval G' :=
    hκ.1.sub hκ'.1
  have od : IsBoundedObservable fun U => (κ U).eval G - (κ U).eval G' :=
    isBoundedObservable_sub oV oV'
  have hJm : Measurable[shiftInvariantSigma a] fun U => conj ((κ U).eval G - (κ U).eval G') :=
    Complex.continuous_conj.measurable.comp hdm
  have hJb : ∃ C₀ : ℝ, ∀ U, ‖conj ((κ U).eval G - (κ U).eval G')‖ ≤ C₀ :=
    ⟨C + C', fun U => by
      rw [Complex.norm_conj]
      exact (norm_sub_le _ _).trans (add_le_add (hb U) (hb' U))⟩
  have oJ : IsBoundedObservable fun U => conj ((κ U).eval G - (κ U).eval G') := ⟨borel hJm, hJb⟩
  have hz : ∫ U, conj ((κ U).eval G - (κ U).eval G') * ((κ U).eval G - (κ U).eval G') ∂μ = 0 := by
    have e : ∀ U, conj ((κ U).eval G - (κ U).eval G') * ((κ U).eval G - (κ U).eval G') =
        conj ((κ U).eval G - (κ U).eval G') * (κ U).eval G -
          conj ((κ U).eval G - (κ U).eval G') * (κ U).eval G' := fun U => mul_sub _ _ _
    simp only [e]
    rw [integral_sub (integrable_of_isBoundedObservable _ (isBoundedObservable_mul oJ oV))
      (integrable_of_isBoundedObservable _ (isBoundedObservable_mul oJ oV')), hκ.2 _ hJm hJb,
      hκ'.2 _ hJm hJb, h _ hJm hJb, sub_self]
  filter_upwards [ae_eq_zero_of_integral_conj_mul_self μ od hz] with U hU
  exact sub_eq_zero.mp hU
theorem measure_eq_one_of_ae_mem (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ]
    {s : Set (GaugeField a)} (hs : MeasurableSet s) (h : ∀ᵐ U ∂μ, U ∈ s) : μ s = 1 :=
  (prob_compl_eq_zero_iff hs).mp (mem_ae_iff.mp h)
theorem eval_eq_of_uniform_approx (ρ : ProbMeasure (GaugeField a)) {A : Set (GaugeField a → ℂ)}
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) (hA : ∀ H ∈ A, IsBoundedObservable H)
    (hd : ∀ ε : ℝ, 0 < ε → ∃ H ∈ A, uniformSup (F - H) < ε)
    (T : (GaugeField a → ℂ) → GaugeField a → ℂ)
    (hT : ∀ H ∈ A, ‖ρ.eval (T F) - ρ.eval (T H)‖ ≤ uniformSup (F - H))
    (he : ∀ H ∈ A, ρ.eval (T H) = ρ.eval H) : ρ.eval (T F) = ρ.eval F := by
  refine sub_eq_zero.mp (norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_))
  obtain ⟨H, hH, hlt⟩ := hd (ε / 2) (half_pos hε)
  have hs : ‖ρ.eval F - ρ.eval H‖ ≤ uniformSup (F - H) := by
    rw [← eval_sub ρ hF (hA H hH)]
    exact norm_eval_le ρ fun U =>
      norm_le_uniformSup (A := F - H) (isBoundedObservable_sub hF (hA H hH)) U
  have h1 := hT H hH
  have e : ρ.eval (T F) - ρ.eval F =
      (ρ.eval (T F) - ρ.eval (T H)) - (ρ.eval F - ρ.eval H) := by
    rw [he H hH]
    ring
  rw [e]
  have h2 := norm_sub_le (ρ.eval (T F) - ρ.eval (T H)) (ρ.eval F - ρ.eval H)
  linarith
end General
theorem denseLocalSet_isCountableDense (hT : TopologyDensityHolds) (D : Setup) :
    IsCountableDenseLocal D.mesh D.denseLocalSet := by
  obtain ⟨A, hc, hd, -⟩ := (hT D).countable_dense_local
  exact denseLocalSet_spec D.L D.K ⟨A, hd.1, hc, hd.2⟩
theorem countable_orientedLinkSet (hT : TopologyDensityHolds) (D : Setup) :
    Countable (OrientedLinkSet D.mesh) := by
  have : Countable {S : Set (Link D.mesh) | S.Finite} := (hT D).countable_finite_linkSets.to_subtype
  refine Function.Injective.countable
    (f := fun W : OrientedLinkSet D.mesh =>
      (⟨(W.links : Set (Link D.mesh)), W.links.finite_toSet⟩ : {S : Set (Link D.mesh) | S.Finite})) ?_
  intro W W' h
  cases W
  cases W'
  have : _ = _ := Finset.coe_injective (congrArg Subtype.val h)
  subst this
  rfl
theorem sub_mem_continuousLocalFunctions (hT : TopologyDensityHolds) (D : Setup)
    {F H : GaugeField D.mesh → ℂ} (hF : F ∈ continuousLocalFunctions D.mesh)
    (hH : H ∈ continuousLocalFunctions D.mesh) : F - H ∈ continuousLocalFunctions D.mesh := by
  obtain ⟨A, hA⟩ := (hT D).exists_nonUnitalSubalgebra
  have hF' : F ∈ A := by
    rw [← SetLike.mem_coe, hA]
    exact hF
  have hH' : H ∈ A := by
    rw [← SetLike.mem_coe, hA]
    exact hH
  have h : F + (-1 : ℂ) • H ∈ A := add_mem hF' (SMulMemClass.smul_mem (-1 : ℂ) hH')
  have e : F + (-1 : ℂ) • H = F - H := by
    funext U
    simp [sub_eq_add_neg]
  rw [e] at h
  rw [← hA]
  exact h
theorem norm_eval_heatBath_sub_le (hT : TopologyDensityHolds)
    (hK : WilsonKernelProperties.Statement) (D : Setup) (ρ : ProbMeasure (GaugeField D.mesh))
    (W : OrientedLinkSet D.mesh) {F H : GaugeField D.mesh → ℂ}
    (hF : F ∈ continuousLocalFunctions D.mesh) (hH : H ∈ continuousLocalFunctions D.mesh) :
    ‖ρ.eval (W.heatBath D.β F) - ρ.eval (W.heatBath D.β H)‖ ≤ uniformSup (F - H) := by
  have hE := sub_mem_continuousLocalFunctions hT D hF hH
  obtain ⟨-, ⟨hlin, -, -⟩, -, -⟩ := hK D W D.β D.β D.β_pos D.β_pos F hF
  obtain ⟨-, ⟨-, -, hγF⟩, -, -⟩ := hK D W D.β D.β D.β_pos D.β_pos F hF
  obtain ⟨-, ⟨-, -, hγH⟩, -, -⟩ := hK D W D.β D.β D.β_pos D.β_pos H hH
  obtain ⟨-, ⟨-, hnorm, hγE⟩, -, -⟩ := hK D W D.β D.β D.β_pos D.β_pos (F - H) hE
  have hl := hlin 1 (-1) F H hF hH
  have e₁ : (fun U => (1 : ℂ) * F U + (-1) * H U) = F - H := by
    funext U
    simp [sub_eq_add_neg]
  have e₂ : (fun U => (1 : ℂ) * W.heatBath D.β F U + (-1) * W.heatBath D.β H U) =
      fun U => W.heatBath D.β F U - W.heatBath D.β H U := by
    funext U
    simp [sub_eq_add_neg]
  rw [e₁, e₂] at hl
  rw [← eval_sub ρ hγF.1 hγH.1, ← hl]
  exact norm_eval_le ρ fun U =>
    (norm_le_uniformSup (A := W.heatBath D.β (F - H)) hγE.1 U).trans hnorm
theorem norm_eval_shift_sub_le {a : ℝ} (ρ : ProbMeasure (GaugeField a)) (v : LatticePoint a)
    {F H : GaugeField a → ℂ} (hF : IsBoundedObservable F) (hH : IsBoundedObservable H) :
    ‖ρ.eval ((shift v).actOn F) - ρ.eval ((shift v).actOn H)‖ ≤ uniformSup (F - H) := by
  have oF : IsBoundedObservable ((shift v).actOn F) := hF.latticeMotionAct (shiftMotion v)
  have oH : IsBoundedObservable ((shift v).actOn H) := hH.latticeMotionAct (shiftMotion v)
  rw [← eval_sub ρ oF oH]
  exact norm_eval_le ρ fun U =>
    norm_le_uniformSup (A := F - H) (isBoundedObservable_sub hF hH) ((shift v).pullbackField U)
theorem holds (hT : TopologyDensityHolds)
    (hK : WilsonKernelProperties.Statement)
    (hD : InvariantDensityLaws)
    (hI : GibbsKernelsAndSymmetries.Assertion)
    (hM : MotionInvariance.Holds)
    (hC : YangMills.Construction.InfiniteLattice.PeriodicGibbsConvexCompact.Statement) :
    AlmostEveryConditionalIsPeriodicGibbs := by
  intro D ν κ hκ
  have : IsProbabilityMeasure ν.1 := ν.2.1.1
  have := countable_orientedLinkSet hT D
  have : Countable (LatticePoint D.mesh) := (hT D).countable_points
  obtain ⟨hsub, hcount, hdense⟩ := denseLocalSet_isCountableDense hT D
  have γloc : ∀ (W : OrientedLinkSet D.mesh) {F : GaugeField D.mesh → ℂ},
      F ∈ continuousLocalFunctions D.mesh → W.heatBath D.β F ∈ continuousLocalFunctions D.mesh :=
    fun W {F} hF => (hK D W D.β D.β D.β_pos D.β_pos F hF).2.1.2.2
  have τobs : ∀ (v : LatticePoint D.mesh) {F : GaugeField D.mesh → ℂ}, IsBoundedObservable F →
      IsBoundedObservable ((shift v).actOn F) :=
    fun v {_} hF => hF.latticeMotionAct (shiftMotion v)
  have hset : MeasurableSet[shiftInvariantSigma D.mesh] (conditionalGibbsLocus D κ) := by
    have e : conditionalGibbsLocus D κ =
        ⋂ F ∈ D.denseLocalSet,
          ((⋂ W : OrientedLinkSet D.mesh,
              {U | (κ U).eval (W.heatBath D.β F) = (κ U).eval F}) ∩
            ⋂ v : LatticePoint D.mesh, {U | (κ U).eval ((shift v).actOn F) = (κ U).eval F}) := by
      ext U
      simp only [conditionalGibbsLocus, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [e]
    refine MeasurableSet.biInter hcount fun F hF => MeasurableSet.inter
      (MeasurableSet.iInter fun W => ?_) (MeasurableSet.iInter fun v => ?_)
    · exact measurableSet_eq_fun (hκ _ (γloc W (hsub hF)).1).1 (hκ F (hsub hF).1).1
    · exact measurableSet_eq_fun (hκ _ (τobs v (hsub hF).1)).1 (hκ F (hsub hF).1).1
  have hae : ∀ᵐ U ∂ν.1, U ∈ conditionalGibbsLocus D κ := by
    have h₁ : ∀ F ∈ D.denseLocalSet, ∀ᵐ U ∂ν.1,
        (∀ W : OrientedLinkSet D.mesh, (κ U).eval (W.heatBath D.β F) = (κ U).eval F) ∧
          ∀ v : LatticePoint D.mesh, (κ U).eval ((shift v).actOn F) = (κ U).eval F := by
      intro F hF
      have oF : IsBoundedObservable F := (hsub hF).1
      refine Filter.Eventually.and (ae_all_iff.mpr fun W => ?_) (ae_all_iff.mpr fun v => ?_)
      · exact ae_eval_eq_of_condExp ν.1 κ (γloc W (hsub hF)).1 oF (hκ _ (γloc W (hsub hF)).1)
          (hκ F oF) fun J hJm hJb => (hD D ν J hJm hJb).1 W F (hsub hF)
      · exact ae_eval_eq_of_condExp ν.1 κ (τobs v oF) oF (hκ _ (τobs v oF)) (hκ F oF)
          fun J hJm hJb => (hD D ν J hJm hJb).2.1 v F oF
    filter_upwards [(ae_ball_iff hcount).mpr h₁] with U hU F hF
    exact hU F hF
  refine ⟨hset, ?_, fun U hU => ?_⟩
  · have hb : MeasurableSet (conditionalGibbsLocus D κ) :=
      (show IsShiftInvariantSet _ from hset).1
    exact measure_eq_one_of_ae_mem ν.1 hb hae
  have approx : ∀ F ∈ continuousLocalFunctions D.mesh, ∀ ε : ℝ, 0 < ε →
      ∃ H ∈ D.denseLocalSet, uniformSup (F - H) < ε := hdense
  have hkeep : GibbsKernelsAndSymmetries.HeatBathInvariant D.β (κ U) := fun W F hF =>
    eval_eq_of_uniform_approx (κ U) hF.1 (fun H hH => (hsub hH).1) (approx F hF)
      (W.heatBath D.β) (fun H hH => norm_eval_heatBath_sub_le hT hK D (κ U) W hF (hsub hH))
      fun H hH => (hU H hH).1 W
  have htrans : ∀ (v : LatticePoint D.mesh), ∀ F ∈ continuousLocalFunctions D.mesh,
      (κ U).eval ((shift v).actOn F) = (κ U).eval F := fun v F hF =>
    eval_eq_of_uniform_approx (κ U) hF.1 (fun H hH => (hsub hH).1) (approx F hF)
      (shift v).actOn
      (fun H hH => norm_eval_shift_sub_le (κ U) v hF.1 (hsub hH).1)
      fun H hH => (hU H hH).2 v
  have hmem : (κ U).toMeasure ∈
      {ν : Measure (GaugeField D.mesh) | IsGibbs D.β ν ∧ IsShiftInvariant ν} := by
    refine ⟨((hI D D.β D.β_pos).1 (κ U)).mpr hkeep, fun v => ?_⟩
    have hd' : ∀ G : C(GaugeField D.mesh, ℂ), ∀ ε : ℝ, 0 < ε →
        ∃ F ∈ {F : C(GaugeField D.mesh, ℂ) | ⇑F ∈ continuousLocalFunctions D.mesh},
          uniformSup (⇑G - ⇑F) < ε := by
      intro G ε hε
      obtain ⟨H, hH, hlt⟩ := (hT D).dense_local.2 G G.continuous ε hε
      exact ⟨⟨H, hH.2.2⟩, hH, hlt⟩
    exact ((hM D (shiftMotion v) (κ U)).2.1 _ hd').mpr fun F hF => htrans v F hF
  exact (hC D).1 ▸ hmem
end YangMills.Construction.LatticePhases.ConditionalGibbsProof

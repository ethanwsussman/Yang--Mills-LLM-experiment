import YangMills.Construction.Cumulants.JointCumulantThroughMoments
import YangMills.Construction.InfiniteLattice.CumulantsArePolynomialsInTheMomentsAndWeakLimits
import YangMills.Construction.InfiniteLattice.FunctionsOfTheBondsOfASetAndSupports
import YangMills.Construction.InfiniteLattice.PlaquetteFunctionSeesNeitherCornerNorSense
import YangMills.Construction.InfiniteLattice.TheSpaceOfConfigurationsAndTheSpaceOfMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.InfiniteLattice
open scoped Topology Pointwise
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing.MomentPolynomials
open YangMills.Construction.Cumulants (mixedCumulant)
open YangMills.Construction.Probability (IsBoundedRealRV)
open YangMills.Construction.SetPartition (PartitionsFin blockCount)
abbrev NonemptyIndexSet (n : ℕ) : Type := {J : Finset (Fin n) // J.Nonempty}
open Classical in
def blockVar {n : ℕ} (J : Finset (Fin n)) : MvPolynomial (NonemptyIndexSet n) ℤ :=
  if h : J.Nonempty then MvPolynomial.X ⟨J, h⟩ else 1
def cumulantPoly (n : ℕ) : MvPolynomial (NonemptyIndexSet n) ℤ :=
  ∑ π : PartitionsFin n, (-1) ^ (blockCount π - 1) *
    ((blockCount π - 1).factorial : MvPolynomial (NonemptyIndexSet n) ℤ) *
      ∏ J ∈ π.parts, blockVar J
theorem aeval_cumulantPoly {n : ℕ} (M : Finset (Fin n) → ℂ) :
    MvPolynomial.aeval (fun J : NonemptyIndexSet n => M J.1) (cumulantPoly n) =
      ∑ π : PartitionsFin n, (-1 : ℂ) ^ (blockCount π - 1) *
        ((blockCount π - 1).factorial : ℂ) * ∏ J ∈ π.parts, M J := by
  simp only [cumulantPoly, map_sum, map_mul, map_prod, map_pow, map_neg, map_one, map_natCast]
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun J hJ => ?_
  have hne := π.nonempty_of_mem_parts hJ
  simp [blockVar, hne]
theorem mixedCumulant_eq_aeval_cumulantPoly
    (hM : YangMills.Construction.Cumulants.MixedCumulantMomentExpansion)
    {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] {n : ℕ} (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ) (hX : ∀ j, IsBoundedRealRV (X j)) :
    mixedCumulant ν X =
      MvPolynomial.aeval (fun J : NonemptyIndexSet n => ((∫ x, ∏ j ∈ J.1, X j x ∂ν : ℝ) : ℂ))
        (cumulantPoly n) := by
  rw [hM Ω ν n X hn hX]
  exact (aeval_cumulantPoly fun J => ((∫ x, ∏ j ∈ J, X j x ∂ν : ℝ) : ℂ)).symm
theorem finite_setOf_center_mem
    (hF : LinkFunctions.Assertion) {a : ℝ} (ha : 0 < a) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) : {p : ElementaryPlaquette a | p.center ∈ S}.Finite := by
  obtain ⟨-, -, ⟨hpts, -⟩, -⟩ := hF a ha
  let D : Set AmbientSpace := Set.range fun q : Fin 4 × Fin 4 =>
    -(Pi.single q.1 (a / 2) : AmbientSpace) - (Pi.single q.2 (a / 2) : AmbientSpace)
  have hD : Bornology.IsBounded D := (Set.finite_range _).isBounded
  have hT := hpts (S + D) (hS.add hD)
  have hinj : Function.Injective
      fun p : ElementaryPlaquette a => (p.corner, (p.lowAxis, p.highAxis)) := by
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    exact ElementaryPlaquette.ext hpq.1 hpq.2.1 hpq.2.2
  refine Set.Finite.of_finite_image
    (f := fun p : ElementaryPlaquette a => (p.corner, (p.lowAxis, p.highAxis))) ?_ hinj.injOn
  refine (hT.prod (Set.finite_univ (α := Fin 4 × Fin 4))).subset ?_
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨?_, Set.mem_univ _⟩
  refine Set.mem_add.2 ⟨p.center, hp, _, Set.mem_range_self (p.lowAxis, p.highAxis), ?_⟩
  simp only [ElementaryPlaquette.center]
  abel
theorem plaquetteSmearing_eq_finset_sum {a : ℝ} (f : AmbientSpace → ℂ)
    (T : Finset (ElementaryPlaquette a))
    (hT : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → p ∈ T) (U : GaugeField a) :
    plaquetteSmearing f U = ∑ p ∈ T, f p.center * (faceEnergy U p : ℂ) := by
  refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
  refine hT p fun h0 => ?_
  simp [h0] at hp
theorem finite_setOf_apply_center_ne_zero (hF : LinkFunctions.Assertion)
    {a : ℝ} (ha : 0 < a) {f : AmbientSpace → ℂ} (hf : IsBoundedOfBoundedSupport f) :
    {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite :=
  finite_setOf_center_mem hF ha hf.2
theorem plaquetteSmearing_mem_continuousLocal (hF : LinkFunctions.Assertion)
    (hP : FaceEnergyIndependentOfBasepointAndOrientation)
    (hS : SpacesOfFieldsAndMeasures.FieldAndMeasureSpaceProperties) {a : ℝ} (ha : 0 < a)
    {f : AmbientSpace → ℂ} (hf : IsBoundedOfBoundedSupport f) :
    plaquetteSmearing f ∈ GibbsAtFixedSpacing.continuousLocal a := by
  obtain ⟨-, ⟨-, ⟨A, hA⟩, -⟩, -⟩ := hS a ha
  obtain ⟨-, hP'⟩ := hP
  obtain ⟨-, hside, -⟩ := hP' a ha
  have hfin := finite_setOf_apply_center_ne_zero hF ha hf
  have heq : plaquetteSmearing f =
      ∑ p ∈ hfin.toFinset, f p.center •
        fun U : GaugeField a => ((faceEnergy U p : ℝ) : ℂ) := by
    funext U
    rw [plaquetteSmearing_eq_finset_sum f hfin.toFinset fun p hp => hfin.mem_toFinset.2 hp,
      Finset.sum_apply]
    rfl
  rw [heq, ← hA]
  refine A.sum_mem fun p _ => A.smul_mem ?_ _
  have hmem := (hside p).2.1
  rwa [← hA] at hmem
theorem isBoundedRealRV_of_continuous
    (hS : SpacesOfFieldsAndMeasures.FieldAndMeasureSpaceProperties) {a : ℝ} (ha : 0 < a)
    {X : GaugeField a → ℝ} (hX : Continuous X) : IsBoundedRealRV X := by
  obtain ⟨⟨-, hc, -⟩, -⟩ := hS a ha
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hX.continuousOn
  exact ⟨hX.measurable, C, fun U => by simpa using hC U (Set.mem_univ U)⟩
theorem tendsto_mixedCumulant (hM : YangMills.Construction.Cumulants.MixedCumulantMomentExpansion)
    (hS : SpacesOfFieldsAndMeasures.FieldAndMeasureSpaceProperties) {a : ℝ} (ha : 0 < a)
    {ν : ℕ → BorelProb a} {μ : BorelProb a} (hν : BorelProb.TendstoWeak ν μ) {n : ℕ} (hn : 1 ≤ n)
    {X : Fin n → GaugeField a → ℝ} (hX : ∀ j, Continuous (X j)) :
    Tendsto (fun i => mixedCumulant (ν i).1 X) atTop (𝓝 (mixedCumulant μ.1 X)) := by
  have hb := fun j => isBoundedRealRV_of_continuous hS ha (hX j)
  have e : ∀ ρ : BorelProb a, mixedCumulant ρ.1 X =
      MvPolynomial.eval (fun J : NonemptyIndexSet n => ((∫ U, ∏ j ∈ J.1, X j U ∂ρ.1 : ℝ) : ℂ))
        (MvPolynomial.map (algebraMap ℤ ℂ) (cumulantPoly n)) := by
    intro ρ
    have : IsProbabilityMeasure ρ.1 := ρ.2
    rw [mixedCumulant_eq_aeval_cumulantPoly hM ρ.1 hn X hb, MvPolynomial.aeval_def,
      MvPolynomial.eval_map]
  simp_rw [e]
  refine ((MvPolynomial.continuous_eval _).tendsto _).comp (tendsto_pi_nhds.2 fun J => ?_)
  have hc : Continuous fun U => ((∏ j ∈ J.1, X j U : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_finsetProd _ fun j _ => hX j)
  have hlim := hν _ hc
  simpa only [BorelProb.integral, GaugeFieldProbability.expect, integral_complex_ofReal] using hlim
theorem isBoundedOfBoundedSupport_ofReal {f : AmbientSpace → ℝ}
    (hf : IsBoundedBorelCompactlySupported f) :
    IsBoundedOfBoundedSupport fun x => (f x : ℂ) := by
  obtain ⟨-, ⟨C, hC⟩, hc⟩ := hf
  refine ⟨⟨C, fun x => by simpa using hC x⟩, hc.isCompact.isBounded.subset fun x hx => ?_⟩
  refine subset_tsupport f ?_
  intro h0
  exact hx (by simp [h0])
theorem cumulantsPolynomialInMomentsAndWeakLimits
    (hM : YangMills.Construction.Cumulants.MixedCumulantMomentExpansion)
    (hF : LinkFunctions.Assertion)
    (hP : FaceEnergyIndependentOfBasepointAndOrientation)
    (hS : SpacesOfFieldsAndMeasures.FieldAndMeasureSpaceProperties) :
    CumulantsPolynomialInMomentsAndWeakLimits := by
  refine ⟨fun n hn => ⟨cumulantPoly n, fun Ω _ ν _ X hX =>
      mixedCumulant_eq_aeval_cumulantPoly hM ν hn X hX⟩,
    fun a ha => ⟨fun f hf => ⟨?_, plaquetteSmearing_mem_continuousLocal hF hP hS ha hf, ?_⟩,
      fun ν μ hν => ⟨fun n X hn hX => tendsto_mixedCumulant hM hS ha hν hn hX, fun f hf => ?_⟩⟩,
    fun L K hp ν μ hν n f hn hf => ?_, fun Ω Ω' _ _ ν ν' _ φ hφ hνφ n X hn hX => ?_⟩
  · refine (finite_setOf_apply_center_ne_zero hF ha hf).subset fun p hp h0 => hp ?_
    funext U
    simp [h0]
  · intro him U
    rw [plaquetteSmearing_eq_finset_sum f (finite_setOf_apply_center_ne_zero hF ha hf).toFinset
      fun p hp => (finite_setOf_apply_center_ne_zero hF ha hf).mem_toFinset.2 hp, Complex.im_sum]
    exact Finset.sum_eq_zero fun p _ => by simp [Complex.mul_im, him]
  · exact hν _ (plaquetteSmearing_mem_continuousLocal hF hP hS ha hf).1
  · simp_rw [ursellFunctionOfMeasure_eq_mixedCumulant]
    exact tendsto_mixedCumulant hM hS hp hν (by omega) fun j => Complex.continuous_re.comp
      (plaquetteSmearing_mem_continuousLocal hF hP hS hp
        (isBoundedOfBoundedSupport_ofReal (hf j))).1
  · subst hνφ
    have : IsProbabilityMeasure (ν'.map φ) := Measure.isProbabilityMeasure_map hφ.aemeasurable
    have hY : ∀ j, IsBoundedRealRV (X j ∘ φ) := fun j => by
      obtain ⟨C, hC⟩ := (hX j).bounded
      exact ⟨(hX j).measurable.comp hφ, C, fun ω => hC (φ ω)⟩
    rw [hM _ _ n X hn hX, hM _ _ n _ hn hY]
    refine Finset.sum_congr rfl fun π _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun J _ => ?_
    have hm : Measurable fun x => ∏ j ∈ J, X j x :=
      Finset.measurable_fun_prod _ fun j _ => (hX j).measurable
    rw [integral_map hφ.aemeasurable hm.aestronglyMeasurable]
    rfl
end YangMills.Construction.GibbsAtFixedSpacing.MomentPolynomials

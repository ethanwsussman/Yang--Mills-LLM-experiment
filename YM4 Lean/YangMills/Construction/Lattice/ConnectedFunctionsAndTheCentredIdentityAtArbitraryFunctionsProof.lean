import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.Cumulants.CumulantsOfALinearMapIntoBoundedRandomVariables
import YangMills.Construction.Lattice.ConnectedFunctionsAndTheCentredIdentityAtArbitraryFunctions
import YangMills.Construction.Lattice.LatticeAsAProbabilitySpace
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open YangMills.Construction.Probability (IsBoundedRealRV IsBoundedComplexRV complexExpectation)
open YangMills.Construction.Cumulants (mixedCumulant linearMapCumulant)
noncomputable section
namespace YangMills.Construction.ConnectedFunctions
namespace CentredIdentityArgument
open CouplingData
section Generic
variable {Ω : Type*} [MeasurableSpace Ω]
theorem boundedRV_of_measurable {u : Ω → ℂ} (hu : Measurable u) (hB : ∃ C : ℝ, ∀ ω, ‖u ω‖ ≤ C) :
    IsBoundedComplexRV u :=
  ⟨Complex.measurable_re.comp hu, Complex.measurable_im.comp hu, hB⟩
theorem measurable_of_boundedRV {u : Ω → ℂ} (hu : IsBoundedComplexRV u) : Measurable u := by
  have hdec : u = fun ω => ((u ω).re : ℂ) + ((u ω).im : ℂ) * Complex.I := by
    funext ω
    exact (Complex.re_add_im _).symm
  rw [hdec]
  exact (Complex.measurable_ofReal.comp hu.measurable_re).add
    ((Complex.measurable_ofReal.comp hu.measurable_im).mul_const _)
theorem integrable_of_boundedRV (ν : Measure Ω) [IsFiniteMeasure ν] {u : Ω → ℂ}
    (hu : IsBoundedComplexRV u) : Integrable u ν := by
  obtain ⟨C, hC⟩ := hu.bounded
  exact Integrable.of_bound (measurable_of_boundedRV hu).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)
theorem boundedRV_prod {ι : Type*} (s : Finset ι) (u : ι → Ω → ℂ)
    (hu : ∀ i, IsBoundedComplexRV (u i)) :
    IsBoundedComplexRV fun ω => ∏ i ∈ s, u i ω := by
  refine boundedRV_of_measurable
    (Finset.measurable_fun_prod _ fun i _ => measurable_of_boundedRV (hu i)) ?_
  choose C hC using fun i => (hu i).bounded
  refine ⟨∏ i ∈ s, |C i|, fun ω => ?_⟩
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => (hC i ω).trans (le_abs_self _)
theorem boundedRV_sub_const {u : Ω → ℂ} (hu : IsBoundedComplexRV u) (z : ℂ) :
    IsBoundedComplexRV fun ω => u ω - z := by
  refine boundedRV_of_measurable ((measurable_of_boundedRV hu).sub_const z) ?_
  obtain ⟨C, hC⟩ := hu.bounded
  exact ⟨C + ‖z‖, fun ω => (norm_sub_le _ _).trans (by linarith [hC ω])⟩
theorem boundedRV_mul {u v : Ω → ℂ} (hu : IsBoundedComplexRV u)
    (hv : IsBoundedComplexRV v) : IsBoundedComplexRV fun ω => u ω * v ω := by
  refine boundedRV_of_measurable
    ((measurable_of_boundedRV hu).mul (measurable_of_boundedRV hv)) ?_
  obtain ⟨C, hC⟩ := hu.bounded
  obtain ⟨C', hC'⟩ := hv.bounded
  refine ⟨|C| * |C'|, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hC ω).trans (le_abs_self _)) ((hC' ω).trans (le_abs_self _)) (norm_nonneg _)
    (abs_nonneg _)
theorem measurable_of_measurableSpace_eq {α : Type*} {m₁ m₂ : MeasurableSpace α} (hm : m₁ = m₂)
    {x : α → ℝ} (hx : @Measurable α ℝ m₂ _ x) : @Measurable α ℝ m₁ _ x := by
  subst hm
  exact hx
end Generic
theorem norm_le_euclidNormVec (v : Fin 4 → ℝ) : ‖v‖ ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
theorem lipschitz_of_periodic_contDiff {ℓ : ℝ} (hℓ : 0 < ℓ) (g : (Fin 4 → ℝ) → ℝ)
    (hg : ContDiff ℝ 1 g)
    (hper : ∀ (k : Fin 4 → ℤ) x, g (x + TestFunctions.latticeTranslate ℓ k) = g x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖g x - g y‖ ≤ C * ‖x - y‖ := by
  have hder : ∀ (k : Fin 4 → ℤ) x,
      fderiv ℝ g (x + TestFunctions.latticeTranslate ℓ k) = fderiv ℝ g x := by
    intro k x
    have hshift : (fun y => g (y + TestFunctions.latticeTranslate ℓ k)) = g := funext (hper k)
    rw [← fderiv_comp_add_right, hshift]
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : Fin 4 → ℝ)) (b := fun _ => ℓ)).exists_bound_of_continuousOn
      (hg.continuous_fderiv one_ne_zero).continuousOn
  have hbound : ∀ x, ‖fderiv ℝ g x‖ ≤ C := by
    intro x
    let k : Fin 4 → ℤ := fun μ => ⌊x μ / ℓ⌋
    have hcube : x - TestFunctions.latticeTranslate ℓ k ∈ Icc (0 : Fin 4 → ℝ) (fun _ => ℓ) := by
      have hcancel : ∀ μ, ℓ * (x μ / ℓ) = x μ := fun μ => by field_simp
      constructor
      · intro μ
        have hlow := mul_le_mul_of_nonneg_left (Int.floor_le (x μ / ℓ)) hℓ.le
        have hμ := hcancel μ
        simp only [Pi.zero_apply, Pi.sub_apply, TestFunctions.latticeTranslate, k]
        linarith
      · intro μ
        have hup := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (x μ / ℓ)) hℓ
        have hμ := hcancel μ
        simp only [Pi.sub_apply, TestFunctions.latticeTranslate, k]
        linarith
    have hx := hC _ hcube
    rwa [← hder k, sub_add_cancel] at hx
  refine ⟨C, (norm_nonneg _).trans (hbound 0), fun x y => ?_⟩
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => (hg.differentiable (by simp)) z)
    (fun z _ => hbound z) convex_univ (mem_univ y) (mem_univ x)
section Topology
variable {L m : ℕ} {i : ℤ}
theorem compactGaugeField_topology_eq :
    (inferInstance : TopologicalSpace (PeriodicLattice.CompactGaugeField L m i)) =
      (instTopologicalSpaceSubtype :
        TopologicalSpace ↥(PeriodicLattice.compactGaugeFields L m i)) := by
  change (⨅ b : PeriodicLattice.Bond L m i, TopologicalSpace.induced
    (fun U : PeriodicLattice.CompactGaugeField L m i =>
      PeriodicLattice.CompactGaugeField.linkValue U b) inferInstance) =
        TopologicalSpace.induced Subtype.val Pi.topologicalSpace
  rw [Pi.topologicalSpace, induced_iInf]
  refine iInf_congr fun b => ?_
  rw [induced_compose]
  change TopologicalSpace.induced _ (TopologicalSpace.induced Subtype.val _) = _
  rw [induced_compose]
  rfl
end Topology
variable (D : CouplingData)
abbrev ConfigSpace : Type := LatticeProbability.GaugeConfig D.toStandingParameters
abbrev gibbsLaw : Measure (ConfigSpace D) :=
  LatticeProbability.gibbsMeasureOn D.toStandingParameters D.coupling
abbrev FaceCoeffs : Type := D.LatticePlaq → ℝ
def sampleAtBarycenters (f : D.Torus → ℝ) : FaceCoeffs D := fun p => f p.barycenter
theorem sampleAtBarycenters_add (f g : D.Torus → ℝ) :
    sampleAtBarycenters D (f + g) = sampleAtBarycenters D f + sampleAtBarycenters D g := rfl
theorem sampleAtBarycenters_smul (a : ℝ) (f : D.Torus → ℝ) :
    sampleAtBarycenters D (a • f) = a • sampleAtBarycenters D f := rfl
theorem gibbsLaw_isProbability (hP : LatticeProbability.ProbabilitySpaceTheorem.claim) :
    IsProbabilityMeasure (gibbsLaw D) :=
  (hP D.toStandingParameters D.coupling D.coupling_pos).1.2.2.1
theorem finite_faces (hP : LatticeProbability.ProbabilitySpaceTheorem.claim) :
    Finite D.LatticePlaq :=
  (hP D.toStandingParameters D.coupling D.coupling_pos).2.1.1
theorem faceEnergy_boundedRV (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (p : D.LatticePlaq) :
    IsBoundedRealRV fun U : ConfigSpace D => PeriodicLattice.plaquetteCost U.1 p :=
  ((hP D.toStandingParameters D.coupling D.coupling_pos).2.1.2 p).2.2
theorem expect_eq_complexExpectation (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (G : D.Config → ℂ)
    (hG : IsBoundedComplexRV fun U : ConfigSpace D => G U.1) :
    D.expect G = complexExpectation (gibbsLaw D) fun U => G U.1 :=
  (hP D.toStandingParameters D.coupling D.coupling_pos).1.2.2.2.2.2 G hG
theorem gibbsCumulant_eq_mixedCumulant (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    {n : ℕ} (X : Fin n → D.Config → ℝ)
    (hX : ∀ i, IsBoundedRealRV fun U : ConfigSpace D => X i U.1) :
    PeriodicLattice.gibbsCumulant D.L D.m D.K D.coupling X =
      mixedCumulant (gibbsLaw D) fun i U => X i U.1 := by
  have hmgf : ∀ t : Fin n → ℂ,
      Cumulants.momentGeneratingFunction
          (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling) X t =
        Cumulants.momentGeneratingFunction (gibbsLaw D) (fun i (U : ConfigSpace D) => X i U.1) t := by
    intro t
    have hexp : IsBoundedComplexRV fun U : ConfigSpace D =>
        Complex.exp (∑ i, t i * (X i U.1 : ℂ)) := by
      refine boundedRV_of_measurable ?_ ?_
      · refine Complex.measurable_exp.comp (Finset.measurable_fun_sum _ fun i _ => ?_)
        exact ((Complex.measurable_ofReal.comp (hX i).measurable).const_mul _)
      · choose C hC using fun i => (hX i).bounded
        refine ⟨Real.exp (∑ i, ‖t i‖ * |C i|), fun U => ?_⟩
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_))
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, Complex.norm_real]
        exact mul_le_mul_of_nonneg_left (((hC i U).trans (le_abs_self _))) (norm_nonneg _)
    exact expect_eq_complexExpectation D hP (fun U => Complex.exp (∑ i, t i * (X i U : ℂ))) hexp
  have hlog : (fun t => Complex.log
        (Cumulants.momentGeneratingFunction
          (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling) X t)) =
      fun t => Complex.log
        (Cumulants.momentGeneratingFunction (gibbsLaw D) (fun i (U : ConfigSpace D) => X i U.1) t) :=
    funext fun t => by rw [hmgf]
  simp only [PeriodicLattice.gibbsCumulant, Cumulants.mixedCumulant, hlog]
section Coefficients
variable [Fintype D.LatticePlaq]
def coeffMap : FaceCoeffs D →ₗ[ℝ] ConfigSpace D → ℝ where
  toFun c U := ∑ p, c p * PeriodicLattice.plaquetteCost U.1 p
  map_add' c c' := by
    funext U
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext U
    simp [Finset.mul_sum, mul_assoc]
theorem coeffMap_apply (c : FaceCoeffs D) (U : ConfigSpace D) :
    coeffMap D c U = ∑ p, c p * PeriodicLattice.plaquetteCost U.1 p := rfl
theorem coeffMap_boundedRV (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (c : FaceCoeffs D) : IsBoundedRealRV (coeffMap D c) := by
  refine ⟨?_, ?_⟩
  · have hfun : (coeffMap D c : ConfigSpace D → ℝ) =
        fun U => ∑ p, c p * PeriodicLattice.plaquetteCost U.1 p := rfl
    rw [hfun]
    exact Finset.measurable_fun_sum _ fun p _ => (faceEnergy_boundedRV D hP p).measurable.const_mul _
  · choose C hC using fun p => (faceEnergy_boundedRV D hP p).bounded
    refine ⟨∑ p, |c p| * |C p|, fun U => ?_⟩
    rw [coeffMap_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hC p U).trans (le_abs_self _)) (abs_nonneg _)
theorem smearedObservable_eq_sum (f : D.Torus → ℝ) (U : D.Config) :
    (PeriodicLattice.smearedObservable f U : ℝ) =
      ∑ p : D.LatticePlaq, sampleAtBarycenters D f p * PeriodicLattice.plaquetteCost U p := by
  unfold PeriodicLattice.smearedObservable
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun p _ => by simp [sampleAtBarycenters, mul_comm]
theorem obs_eq_sum (h : D.Torus → ℂ) (U : D.Config) :
    D.obs h U =
      ∑ p : D.LatticePlaq, (PeriodicLattice.plaquetteCost U p : ℂ) * h p.barycenter := by
  unfold CouplingData.obs PeriodicLattice.smearedObservable
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun p _ => by simp
theorem obs_ofRealFun (f : D.Torus → ℝ) (U : ConfigSpace D) :
    D.obs (D.ofRealFun f) U.1 = (coeffMap D (sampleAtBarycenters D f) U : ℂ) := by
  rw [obs_eq_sum, coeffMap_apply]
  push_cast
  exact Finset.sum_congr rfl fun p _ => by simp [ofRealFun, sampleAtBarycenters, mul_comm]
theorem obs_boundedRV (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (h : D.Torus → ℂ) : IsBoundedComplexRV fun U : ConfigSpace D => D.obs h U.1 := by
  simp only [obs_eq_sum]
  refine boundedRV_of_measurable ?_ ?_
  · refine Finset.measurable_fun_sum _ fun p _ => ?_
    exact (Complex.measurable_ofReal.comp (faceEnergy_boundedRV D hP p).measurable).mul_const _
  · choose C hC using fun p => (faceEnergy_boundedRV D hP p).bounded
    refine ⟨∑ p, |C p| * ‖h p.barycenter‖, fun U => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right ((hC p U).trans (le_abs_self _)) (norm_nonneg _)
theorem cumulantReal_eq_linearMapCumulant (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    {n : ℕ} (f : Fin n → D.Torus → ℝ) :
    D.cumulantReal f =
      linearMapCumulant (gibbsLaw D) (coeffMap D) fun i => sampleAtBarycenters D (f i) := by
  have hobs : ∀ i, (fun U : ConfigSpace D => (PeriodicLattice.smearedObservable (f i) U.1 : ℝ)) =
      coeffMap D (sampleAtBarycenters D (f i)) := fun i => by
    funext U
    rw [smearedObservable_eq_sum, coeffMap_apply]
  unfold CouplingData.cumulantReal linearMapCumulant
  rw [gibbsCumulant_eq_mixedCumulant D hP]
  · exact congrArg _ (funext hobs)
  · intro i
    rw [hobs i]
    exact coeffMap_boundedRV D hP _
theorem faceCumulant_eq_linearMapCumulant [DecidableEq D.LatticePlaq]
    (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    {n : ℕ} (r : Fin n → D.LatticePlaq) :
    D.faceCumulant r =
      linearMapCumulant (gibbsLaw D) (coeffMap D) fun l => Pi.single (r l) (1 : ℝ) := by
  have hface : ∀ l, (fun U : ConfigSpace D => PeriodicLattice.plaquetteCost U.1 (r l)) =
      coeffMap D (Pi.single (r l) (1 : ℝ)) := fun l => by
    funext U
    rw [coeffMap_apply, Finset.sum_eq_single (r l)]
    · simp
    · intro p _ hp
      simp [Pi.single_eq_of_ne hp]
    · simp
  unfold CouplingData.faceCumulant linearMapCumulant
  rw [gibbsCumulant_eq_mixedCumulant D hP _ fun l => faceEnergy_boundedRV D hP (r l)]
  exact congrArg _ (funext hface)
omit [Fintype D.LatticePlaq] in
theorem sum_markParts (h : D.Torus → ℂ) :
    ∑ b : Fin 2, Complex.I ^ (b : ℕ) • D.ofRealFun (markPart h b) = h := by
  funext x
  simp [Fin.sum_univ_two, ofRealFun, markPart, mul_comm Complex.I]
omit [Fintype D.LatticePlaq] in
theorem multilinear_expand_markParts {n : ℕ} (W : Submodule ℂ (D.Torus → ℂ))
    (Ψ : (Fin n → D.Torus → ℂ) → ℂ)
    (hΨ : D.ComplexMultilinearOn (W : Set (D.Torus → ℂ)) Ψ) (f : Fin n → D.Torus → ℂ)
    (hf : ∀ l b, D.ofRealFun (markPart (f l) b) ∈ W) :
    Ψ f = ∑ b : Fin n → Fin 2, Complex.I ^ markWeight b *
      Ψ fun l => D.ofRealFun (markPart (f l) (b l)) := by
  have coe_update : ∀ (c : Fin n → W) (i : Fin n) (x : W),
      (fun l => ((Function.update c i x l : W) : D.Torus → ℂ)) =
        Function.update (fun l => (c l : D.Torus → ℂ)) i x := by
    intro c i x
    funext l
    by_cases hl : l = i
    · subst hl
      simp
    · simp [Function.update_of_ne hl]
  let M : MultilinearMap ℂ (fun _ : Fin n => W) ℂ :=
    { toFun := fun c => Ψ fun l => (c l : D.Torus → ℂ)
      map_update_add' := by
        intro inst c i x y
        obtain rfl : inst = (fun a b => instDecidableEqFin n a b) := Subsingleton.elim _ _
        have hsum := hΨ.1 (fun l => (c l : D.Torus → ℂ)) (fun l => (c l).2) i x y x.2 y.2
        simpa only [coe_update, Submodule.coe_add] using hsum
      map_update_smul' := by
        intro inst c i a x
        obtain rfl : inst = (fun a b => instDecidableEqFin n a b) := Subsingleton.elim _ _
        have hsc := hΨ.2 (fun l => (c l : D.Torus → ℂ)) (fun l => (c l).2) i x a x.2
        simpa only [coe_update, Submodule.coe_smul, smul_eq_mul] using hsc }
  let v : Fin n → Fin 2 → W := fun l b => ⟨D.ofRealFun (markPart (f l) b), hf l b⟩
  have hM : Ψ f = M fun l => ∑ b : Fin 2, Complex.I ^ (b : ℕ) • v l b := by
    change Ψ f = Ψ fun l => ((∑ b : Fin 2, Complex.I ^ (b : ℕ) • v l b : W) : D.Torus → ℂ)
    congr 1
    funext l
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (sum_markParts D (f l)).symm
  rw [hM, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul, Finset.prod_pow_eq_pow_sum]
  rfl
omit [Fintype D.LatticePlaq] in
theorem prod_update_eq_mul_prod_erase {n : ℕ} {Z Y : Type*} [CommMonoid Y] (F : Fin n → Z → Y)
    (f : Fin n → Z) (i : Fin n) (w : Z) :
    ∏ l, F l (Function.update f i w l) = F i w * ∏ l ∈ Finset.univ.erase i, F l (f l) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
theorem faceSum_eq_sum {n : ℕ} (f : Fin n → D.Torus → ℂ) :
    D.faceSum f = ∑ r : Fin n → D.LatticePlaq,
      (∏ l, f l (r l).barycenter) * D.faceCumulant r :=
  finsum_eq_sum_of_fintype _
theorem faceSum_complexMultilinear {n : ℕ} :
    D.ComplexMultilinearOn univ (D.faceSum (n := n)) := by
  have hupd : ∀ (f : Fin n → D.Torus → ℂ) (i : Fin n) (r : Fin n → D.LatticePlaq)
      (w : D.Torus → ℂ), ∏ l, (Function.update f i w l) (r l).barycenter =
        w (r i).barycenter * ∏ l ∈ Finset.univ.erase i, f l (r l).barycenter :=
    fun f i r w =>
      prod_update_eq_mul_prod_erase (fun l (w : D.Torus → ℂ) => w (r l).barycenter) f i w
  refine ⟨fun f _ i g g' _ _ => ?_, fun f _ i g a _ => ?_⟩
  · simp only [faceSum_eq_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hupd, hupd, hupd, Pi.add_apply]
    ring
  · simp only [faceSum_eq_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hupd, hupd, Pi.smul_apply, smul_eq_mul]
    ring
theorem linearMapCumulant_expand_faces (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hlin : Cumulants.LinearMapCumulantProperties) {n : ℕ} (hn : 1 ≤ n)
    (c : Fin n → FaceCoeffs D) :
    linearMapCumulant (gibbsLaw D) (coeffMap D) c =
      ∑ r : Fin n → D.LatticePlaq, (∏ l, (c l (r l) : ℂ)) * D.faceCumulant r := by
  classical
  have := gibbsLaw_isProbability D hP
  obtain ⟨-, -, hadd, hsmul⟩ := (hlin (ConfigSpace D) (gibbsLaw D) (FaceCoeffs D) (coeffMap D)
    (coeffMap_boundedRV D hP)).1 n hn
  let M : MultilinearMap ℝ (fun _ : Fin n => FaceCoeffs D) ℂ :=
    { toFun := linearMapCumulant (gibbsLaw D) (coeffMap D)
      map_update_add' := by
        intro inst c i x y
        obtain rfl : inst = (fun a b => instDecidableEqFin n a b) := Subsingleton.elim _ _
        exact hadd c i x y
      map_update_smul' := by
        intro inst c i a x
        obtain rfl : inst = (fun a b => instDecidableEqFin n a b) := Subsingleton.elim _ _
        rw [hsmul c i a x, Complex.real_smul] }
  have hc : c = fun l => ∑ p, c l p • (Pi.single p (1 : ℝ) : FaceCoeffs D) := by
    funext l q
    simp [Finset.sum_apply, Pi.single_apply]
  change M c = _
  conv_lhs => rw [hc]
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ, Complex.real_smul, faceCumulant_eq_linearMapCumulant D hP]
  push_cast
  rfl
theorem cumulantReal_eq_faceSum
    (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hlin : Cumulants.LinearMapCumulantProperties) {n : ℕ} (hn : 1 ≤ n)
    (g : Fin n → D.Torus → ℝ) :
    D.cumulantReal g = D.faceSum (D.ofRealTuple g) := by
  rw [cumulantReal_eq_linearMapCumulant D hP, linearMapCumulant_expand_faces D hP hlin hn,
    faceSum_eq_sum]
  rfl
theorem markSum_eq_faceSum (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hlin : Cumulants.LinearMapCumulantProperties) {n : ℕ} (hn : 1 ≤ n)
    (f : Fin n → D.Torus → ℂ) : D.markSum f = D.faceSum f := by
  have hexp := multilinear_expand_markParts D ⊤ D.faceSum
    (by rw [Submodule.top_coe]; exact faceSum_complexMultilinear D) f fun _ _ => Submodule.mem_top
  rw [hexp]
  unfold CouplingData.markSum
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cumulantReal_eq_faceSum D hP hlin hn]
  rfl
theorem connected_eq_faceSum (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hlin : Cumulants.LinearMapCumulantProperties) {n : ℕ} (hn : 1 ≤ n)
    (f : Fin n → D.Torus → ℂ) : D.connected f = D.faceSum f := by
  by_cases hreal : ∀ i, IsRealValued (f i)
  · have hre : D.ofRealTuple (fun i x => (f i x).re) = f := by
      funext i x
      exact Complex.ext (by simp [ofRealTuple, ofRealFun])
        (by simp [ofRealTuple, ofRealFun, hreal i x])
    have hcon : D.connected f = D.cumulantReal fun i x => (f i x).re := by
      unfold CouplingData.connected
      rw [if_pos hreal]
    rw [hcon, cumulantReal_eq_faceSum D hP hlin hn, hre]
  · rw [connected_of_not_real D f hreal, markSum_eq_faceSum D hP hlin hn]
theorem connected_complexMultilinear
    (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hlin : Cumulants.LinearMapCumulantProperties) {n : ℕ} (hn : 1 ≤ n) :
    D.ComplexMultilinearOn univ (D.connected (n := n)) := by
  have hfs : D.connected (n := n) = D.faceSum :=
    funext (connected_eq_faceSum D hP hlin hn)
  rw [hfs]
  exact faceSum_complexMultilinear D
theorem connected_ofRealTuple_eq_linearMapCumulant
    (hP : LatticeProbability.ProbabilitySpaceTheorem.claim) {n : ℕ}
    (f : Fin n → D.Torus → ℝ) :
    D.connected (D.ofRealTuple f) =
      linearMapCumulant (gibbsLaw D) (coeffMap D) fun i => sampleAtBarycenters D (f i) := by
  rw [← cumulantReal_eq_linearMapCumulant D hP]
  exact connected_ofReal D f
theorem connected_realSymmMultilinear
    (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hlin : Cumulants.LinearMapCumulantProperties) {n : ℕ} (hn : 1 ≤ n)
    (R : Set (D.Torus → ℝ)) : D.RealSymmMultilinearOn n R := by
  have := gibbsLaw_isProbability D hP
  obtain ⟨him, hperm, hadd, hsmul⟩ := (hlin (ConfigSpace D) (gibbsLaw D) (FaceCoeffs D)
    (coeffMap D) (coeffMap_boundedRV D hP)).1 n hn
  have hupd : ∀ (f : Fin n → D.Torus → ℝ) (i : Fin n) (g : D.Torus → ℝ),
      (fun l => sampleAtBarycenters D (Function.update f i g l)) =
        Function.update (fun l => sampleAtBarycenters D (f l)) i (sampleAtBarycenters D g) :=
    fun f i g => by
      funext l
      exact Function.apply_update (fun _ => sampleAtBarycenters D) f i g l
  refine ⟨fun f _ => ?_, fun f _ σ => ?_, fun f _ i g g' _ _ => ?_, fun f _ i g a _ => ?_⟩
  · rw [connected_ofRealTuple_eq_linearMapCumulant D hP]
    exact him _
  · rw [connected_ofRealTuple_eq_linearMapCumulant D hP,
      connected_ofRealTuple_eq_linearMapCumulant D hP]
    exact hperm (fun i => sampleAtBarycenters D (f i)) σ
  · simp only [connected_ofRealTuple_eq_linearMapCumulant D hP, hupd, sampleAtBarycenters_add]
    exact hadd _ i _ _
  · simp only [connected_ofRealTuple_eq_linearMapCumulant D hP, hupd, sampleAtBarycenters_smul]
    exact hsmul _ i a _
theorem connectedProperties
    (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hlin : Cumulants.LinearMapCumulantProperties) {n : ℕ} (hn : 1 ≤ n)
    (R : Set (D.Torus → ℝ)) (C : Set (D.Torus → ℂ)) : D.ConnectedPropertiesOn n R C := by
  have hm := connected_complexMultilinear D hP hlin hn
  refine ⟨connected_realSymmMultilinear D hP hlin hn R,
    fun f _ => connected_eq_faceSum D hP hlin hn f, fun f _ => ?_,
    fun f _ i g g' _ _ => hm.1 f (fun _ => mem_univ _) i g g' (mem_univ _) (mem_univ _),
    fun f _ i g a _ => hm.2 f (fun _ => mem_univ _) i g a (mem_univ _)⟩
  rw [connected_eq_faceSum D hP hlin hn, markSum_eq_faceSum D hP hlin hn]
omit [Fintype D.LatticePlaq] in
theorem ofRealFun_mem_complexification (H : Submodule ℝ (D.Torus → ℝ)) {f : D.Torus → ℝ}
    (hf : f ∈ H) : D.ofRealFun f ∈ D.complexification H := by
  have h0 : markPart (D.ofRealFun f) 0 = f := by
    funext x
    simp [markPart, ofRealFun]
  have h1 : markPart (D.ofRealFun f) 1 = 0 := by
    funext x
    simp [markPart, ofRealFun]
  refine ⟨?_, ?_⟩
  · rw [h0]
    exact hf
  · rw [h1]
    exact H.zero_mem
def complexificationSubmodule (H : Submodule ℝ (D.Torus → ℝ)) :
    Submodule ℂ (D.Torus → ℂ) where
  carrier := D.complexification H
  add_mem' := by
    rintro f g ⟨hf0, hf1⟩ ⟨hg0, hg1⟩
    have h0 : markPart (f + g) 0 = markPart f 0 + markPart g 0 := by
      funext x
      simp [markPart]
    have h1 : markPart (f + g) 1 = markPart f 1 + markPart g 1 := by
      funext x
      simp [markPart]
    refine ⟨?_, ?_⟩
    · rw [h0]
      exact H.add_mem hf0 hg0
    · rw [h1]
      exact H.add_mem hf1 hg1
  zero_mem' := by
    have hz : ∀ b, markPart (0 : D.Torus → ℂ) b = 0 := by
      intro b
      funext x
      simp [markPart]
    refine ⟨?_, ?_⟩
    · rw [hz]
      exact H.zero_mem
    · rw [hz]
      exact H.zero_mem
  smul_mem' := by
    rintro a f ⟨hf0, hf1⟩
    have h0 : markPart (a • f) 0 = a.re • markPart f 0 - a.im • markPart f 1 := by
      funext x
      simp [markPart]
    have h1 : markPart (a • f) 1 = a.re • markPart f 1 + a.im • markPart f 0 := by
      funext x
      simp [markPart]
    refine ⟨?_, ?_⟩
    · rw [h0]
      exact H.sub_mem (H.smul_mem _ hf0) (H.smul_mem _ hf1)
    · rw [h1]
      exact H.add_mem (H.smul_mem _ hf1) (H.smul_mem _ hf0)
omit [Fintype D.LatticePlaq] in
theorem complexification_isSubspace (H : Submodule ℝ (D.Torus → ℝ)) :
    D.ComplexificationIsSubspace H :=
  ⟨⟨complexificationSubmodule D H, rfl⟩, fun _ hf => ofRealFun_mem_complexification D H hf⟩
theorem uniqueExtension_complexification (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hlin : Cumulants.LinearMapCumulantProperties) {n : ℕ} (hn : 1 ≤ n)
    (H : Submodule ℝ (D.Torus → ℝ)) : D.UniqueExtensionOnComplexification n H := by
  have hm := connected_complexMultilinear D hP hlin hn
  refine ⟨⟨fun f _ i g g' _ _ => hm.1 f (fun _ => mem_univ _) i g g' (mem_univ _) (mem_univ _),
    fun f _ i g a _ => hm.2 f (fun _ => mem_univ _) i g a (mem_univ _)⟩,
    fun Ψ hΨ hagree f hf => ?_⟩
  have hH : ∀ l b, markPart (f l) b ∈ H := by
    intro l b
    fin_cases b
    · exact (hf l).1
    · exact (hf l).2
  have hW : ∀ l b, D.ofRealFun (markPart (f l) b) ∈ complexificationSubmodule D H :=
    fun l b => ofRealFun_mem_complexification D H (hH l b)
  rw [multilinear_expand_markParts D (complexificationSubmodule D H) Ψ hΨ f hW,
    connected_eq_faceSum D hP hlin hn, ← markSum_eq_faceSum D hP hlin hn]
  unfold CouplingData.markSum
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact (hagree (fun l => markPart (f l) (b l)) fun l => hH l (b l)).trans
    (connected_ofReal D _)
theorem uniqueExtension_all
    (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hlin : Cumulants.LinearMapCumulantProperties) {n : ℕ} (hn : 1 ≤ n) :
    D.UniqueExtension n := by
  have hU : D.complexification ((⊤ : Submodule ℝ (D.Torus → ℝ)) : Set (D.Torus → ℝ)) = univ := by
    ext f
    simp [complexification]
  intro Ψ hΨ hagree
  funext f
  refine (uniqueExtension_complexification D hP hlin hn ⊤).2 Ψ ?_ ?_ f fun k => ?_
  · rw [hU]
    exact hΨ
  · rw [Submodule.top_coe]
    exact hagree
  · rw [hU]
    exact mem_univ _
def centredOnSpace (h : D.Torus → ℂ) (U : ConfigSpace D) : ℂ :=
  D.obs h U.1 - complexExpectation (gibbsLaw D) fun U' => D.obs h U'.1
theorem centred_eq_centredOnSpace (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (h : D.Torus → ℂ) (U : ConfigSpace D) : D.centred h U.1 = centredOnSpace D h U := by
  unfold CouplingData.centred centredOnSpace
  rw [expect_eq_complexExpectation D hP _ (obs_boundedRV D hP h)]
theorem centredOnSpace_boundedRV (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (h : D.Torus → ℂ) : IsBoundedComplexRV (centredOnSpace D h) :=
  boundedRV_sub_const (obs_boundedRV D hP h) _
theorem centredMomentFn_eq_expectation (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    {q : ℕ} (h : Fin q → D.Torus → ℂ) :
    D.centredMomentFn h =
      complexExpectation (gibbsLaw D) fun U => ∏ l, centredOnSpace D (h l) U := by
  have hB : IsBoundedComplexRV fun U : ConfigSpace D => ∏ l, D.centred (h l) U.1 := by
    simp only [centred_eq_centredOnSpace D hP]
    exact boundedRV_prod _ _ fun l => centredOnSpace_boundedRV D hP (h l)
  unfold CouplingData.centredMomentFn
  rw [expect_eq_complexExpectation D hP _ hB]
  simp only [centred_eq_centredOnSpace D hP]
theorem obs_add_fun (g g' : D.Torus → ℂ) (U : D.Config) :
    D.obs (g + g') U = D.obs g U + D.obs g' U := by
  simp only [obs_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
theorem obs_smul_fun (a : ℂ) (g : D.Torus → ℂ) (U : D.Config) :
    D.obs (a • g) U = a * D.obs g U := by
  simp only [obs_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring
theorem centredOnSpace_add (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (g g' : D.Torus → ℂ) (U : ConfigSpace D) :
    centredOnSpace D (g + g') U = centredOnSpace D g U + centredOnSpace D g' U := by
  have := gibbsLaw_isProbability D hP
  have hE : (complexExpectation (gibbsLaw D) fun U' : ConfigSpace D => D.obs (g + g') U'.1) =
      (complexExpectation (gibbsLaw D) fun U' : ConfigSpace D => D.obs g U'.1) +
        complexExpectation (gibbsLaw D) fun U' : ConfigSpace D => D.obs g' U'.1 := by
    simp only [obs_add_fun]
    exact integral_add (integrable_of_boundedRV _ (obs_boundedRV D hP g))
      (integrable_of_boundedRV _ (obs_boundedRV D hP g'))
  unfold centredOnSpace
  rw [hE, obs_add_fun]
  ring
theorem centredOnSpace_smul (a : ℂ) (g : D.Torus → ℂ) (U : ConfigSpace D) :
    centredOnSpace D (a • g) U = a * centredOnSpace D g U := by
  have hE : (complexExpectation (gibbsLaw D) fun U' : ConfigSpace D => D.obs (a • g) U'.1) =
      a * complexExpectation (gibbsLaw D) fun U' : ConfigSpace D => D.obs g U'.1 := by
    simp only [obs_smul_fun]
    exact integral_const_mul _ _
  unfold centredOnSpace
  rw [hE, obs_smul_fun]
  ring
theorem centredMomentFn_complexMultilinear
    (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    {q : ℕ} : D.ComplexMultilinearOn univ (D.centredMomentFn (q := q)) := by
  have := gibbsLaw_isProbability D hP
  have hupd : ∀ (f : Fin q → D.Torus → ℂ) (i : Fin q) (w : D.Torus → ℂ) (U : ConfigSpace D),
      ∏ l, centredOnSpace D (Function.update f i w l) U =
        centredOnSpace D w U * ∏ l ∈ Finset.univ.erase i, centredOnSpace D (f l) U :=
    fun f i w U =>
      prod_update_eq_mul_prod_erase (fun _ (w : D.Torus → ℂ) => centredOnSpace D w U) f i w
  have hint : ∀ (f : Fin q → D.Torus → ℂ) (i : Fin q) (w : D.Torus → ℂ),
      Integrable (fun U => centredOnSpace D w U *
        ∏ l ∈ Finset.univ.erase i, centredOnSpace D (f l) U) (gibbsLaw D) :=
    fun f i w => integrable_of_boundedRV _ (boundedRV_mul (centredOnSpace_boundedRV D hP w)
      (boundedRV_prod _ _ fun l => centredOnSpace_boundedRV D hP (f l)))
  refine ⟨fun f _ i g g' _ _ => ?_, fun f _ i g a _ => ?_⟩
  · simp only [centredMomentFn_eq_expectation D hP, hupd, centredOnSpace_add D hP, add_mul]
    exact integral_add (hint f i g) (hint f i g')
  · simp only [centredMomentFn_eq_expectation D hP, hupd, centredOnSpace_smul D, mul_assoc]
    exact integral_const_mul _ _
omit [Fintype D.LatticePlaq] in
theorem restrictTo_update_of_not_mem {q : ℕ} (h : Fin q → D.Torus → ℂ) (i : Fin q)
    (w : D.Torus → ℂ) (J : Finset (Fin q)) (hi : i ∉ J) :
    D.restrictTo (Function.update h i w) J = D.restrictTo h J := by
  funext k
  unfold CouplingData.restrictTo
  rw [Function.update_of_ne]
  intro hk
  exact hi (hk ▸ J.orderEmbOfFin_mem rfl k)
omit [Fintype D.LatticePlaq] in
theorem restrictTo_update_of_mem {q : ℕ} (h : Fin q → D.Torus → ℂ) (i : Fin q)
    (J : Finset (Fin q)) (hi : i ∈ J) :
    ∃ k, ∀ w, D.restrictTo (Function.update h i w) J = Function.update (D.restrictTo h J) k w := by
  obtain ⟨k, hk⟩ : ∃ k, J.orderEmbOfFin rfl k = i := by
    exact show i ∈ Set.range (J.orderEmbOfFin rfl) from by
      rw [Finset.range_orderEmbOfFin]
      exact hi
  refine ⟨k, fun w => ?_⟩
  funext k'
  by_cases hkk : k' = k
  · subst hkk
    simp [CouplingData.restrictTo, hk]
  · rw [Function.update_of_ne hkk]
    unfold CouplingData.restrictTo
    rw [Function.update_of_ne]
    intro hk'
    exact hkk ((J.orderEmbOfFin rfl).injective (hk'.trans hk.symm))
omit [Fintype D.LatticePlaq] in
theorem centredFunctionalFn_complexMultilinear
    (hm : ∀ n : ℕ, 1 ≤ n → D.ComplexMultilinearOn univ (D.connected (n := n))) {q : ℕ} :
    D.ComplexMultilinearOn univ (D.centredFunctionalFn (q := q)) := by
  have main : ∀ (π : SetPartition.PartitionsFin q) (f : Fin q → D.Torus → ℂ) (i : Fin q),
      ∃ (A : (D.Torus → ℂ) → ℂ) (P : ℂ),
        (∀ w, ∏ J ∈ π.parts, D.connected (D.restrictTo (Function.update f i w) J) = A w * P) ∧
        (∀ g g', A (g + g') = A g + A g') ∧ ∀ (a : ℂ) g, A (a • g) = a * A g := by
    intro π f i
    obtain ⟨J₀, hJ₀, hi⟩ := π.exists_mem (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := restrictTo_update_of_mem D f i J₀ hi
    have hcard : 1 ≤ J₀.card := Finset.card_pos.mpr ⟨i, hi⟩
    refine ⟨fun w => D.connected (D.restrictTo (Function.update f i w) J₀),
      ∏ J ∈ π.parts.erase J₀, D.connected (D.restrictTo f J), fun w => ?_, fun g g' => ?_,
      fun a g => ?_⟩
    · rw [← Finset.mul_prod_erase _ _ hJ₀]
      congr 1
      refine Finset.prod_congr rfl fun J hJ => ?_
      rw [restrictTo_update_of_not_mem]
      intro hiJ
      exact (Finset.mem_erase.1 hJ).1 (π.eq_of_mem_parts (Finset.mem_erase.1 hJ).2 hJ₀ hiJ hi)
    · simp only [hk]
      exact (hm _ hcard).1 _ (fun _ => mem_univ _) k g g' (mem_univ _) (mem_univ _)
    · simp only [hk]
      exact (hm _ hcard).2 _ (fun _ => mem_univ _) k g a (mem_univ _)
  refine ⟨fun f _ i g g' _ _ => ?_, fun f _ i g a _ => ?_⟩
  · unfold CouplingData.centredFunctionalFn
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun π _ => ?_
    obtain ⟨A, P, h1, h2, -⟩ := main π f i
    rw [h1, h1, h1, h2, add_mul]
  · unfold CouplingData.centredFunctionalFn
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    obtain ⟨A, P, h1, -, h3⟩ := main π f i
    rw [h1, h1, h3, mul_assoc]
theorem centred_identity_real (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hlin : Cumulants.LinearMapCumulantProperties) {q : ℕ}
    (g : Fin q → D.Torus → ℝ) :
    D.centredMomentFn (D.ofRealTuple g) = D.centredFunctionalFn (D.ofRealTuple g) := by
  have := gibbsLaw_isProbability D hP
  have hmom := (hlin (ConfigSpace D) (gibbsLaw D) (FaceCoeffs D) (coeffMap D)
    (coeffMap_boundedRV D hP)).2.2 q fun l => sampleAtBarycenters D (g l)
  have hc : ∀ (f : D.Torus → ℝ) (U : ConfigSpace D), centredOnSpace D (D.ofRealFun f) U =
      (coeffMap D (sampleAtBarycenters D f) U : ℂ) -
        complexExpectation (gibbsLaw D) fun U' => (coeffMap D (sampleAtBarycenters D f) U' : ℂ) := by
    intro f U
    unfold centredOnSpace
    simp only [obs_ofRealFun]
  have hlhs : (fun U => ∏ l, centredOnSpace D (D.ofRealTuple g l) U) = fun U =>
      ∏ l, ((coeffMap D (sampleAtBarycenters D (g l)) U : ℂ) -
        complexExpectation (gibbsLaw D) fun U' => (coeffMap D (sampleAtBarycenters D (g l)) U' : ℂ)) :=
    funext fun U => Finset.prod_congr rfl fun l _ => hc (g l) U
  rw [centredMomentFn_eq_expectation D hP, hlhs, hmom]
  unfold CouplingData.centredFunctionalFn
  refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ => ?_
  exact (connected_ofRealTuple_eq_linearMapCumulant D hP fun k => g (J.orderEmbOfFin rfl k)).symm
theorem centred_identity_complex (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hlin : Cumulants.LinearMapCumulantProperties) {q : ℕ}
    (h : Fin q → D.Torus → ℂ) : D.centredMomentFn h = D.centredFunctionalFn h := by
  have hm : ∀ n : ℕ, 1 ≤ n → D.ComplexMultilinearOn univ (D.connected (n := n)) :=
    fun n hn => connected_complexMultilinear D hP hlin hn
  rw [multilinear_expand_markParts D ⊤ D.centredMomentFn
      (by rw [Submodule.top_coe]; exact centredMomentFn_complexMultilinear D hP) h
      fun _ _ => Submodule.mem_top,
    multilinear_expand_markParts D ⊤ D.centredFunctionalFn
      (by rw [Submodule.top_coe]; exact centredFunctionalFn_complexMultilinear D hm) h
      fun _ _ => Submodule.mem_top]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact centred_identity_real D hP hlin fun l => markPart (h l) (b l)
theorem connected_one_eq_expect (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hlin : Cumulants.LinearMapCumulantProperties) (f : D.Torus → ℝ) :
    D.connected (fun _ : Fin 1 => D.ofRealFun f) =
      D.expect (D.obs (D.ofRealFun f)) := by
  have := gibbsLaw_isProbability D hP
  have hmean := (hlin (ConfigSpace D) (gibbsLaw D) (FaceCoeffs D) (coeffMap D)
    (coeffMap_boundedRV D hP)).2.1 (sampleAtBarycenters D f)
  have hone := connected_ofRealTuple_eq_linearMapCumulant D hP fun _ : Fin 1 => f
  rw [expect_eq_complexExpectation D hP _ (obs_boundedRV D hP _)]
  simp only [obs_ofRealFun]
  exact hone.trans hmean
theorem fieldObservable_eq_coeffMap (f : D.Torus → ℝ) :
    D.fieldObservable f = (coeffMap D (sampleAtBarycenters D f) : ConfigSpace D → ℝ) :=
  funext fun U => smearedObservable_eq_sum D f U.1
omit [Fintype D.LatticePlaq] in
theorem compactGaugeField_measurableSpace_eq
    (hP : LatticeProbability.ProbabilitySpaceTheorem.claim) :
    (inferInstance : MeasurableSpace
      (PeriodicLattice.CompactGaugeField D.L D.m ((D.K : ℕ) : ℤ))) =
      (inferInstance : MeasurableSpace (ConfigSpace D)) := by
  exact (congrArg (@borel (ConfigSpace D))
    (compactGaugeField_topology_eq (L := D.L) (m := D.m) (i := ((D.K : ℕ) : ℤ)))).trans
      (hP D.toStandingParameters D.coupling D.coupling_pos).1.1.symm
theorem observableLinearAtBarycenters (hP : LatticeProbability.ProbabilitySpaceTheorem.claim) :
    D.ObservableLinearAtBarycenters := by
  refine ⟨fun f => ?_, Set.finite_range _, fun f f' hff => ?_, ?_⟩
  · have hB := coeffMap_boundedRV D hP (sampleAtBarycenters D f)
    rw [fieldObservable_eq_coeffMap]
    exact ⟨measurable_of_measurableSpace_eq (compactGaugeField_measurableSpace_eq D hP)
      hB.measurable, hB.bounded⟩
  · have hs : sampleAtBarycenters D f = sampleAtBarycenters D f' := funext hff
    rw [fieldObservable_eq_coeffMap, fieldObservable_eq_coeffMap, hs]
  · refine ⟨fun f g => ?_, fun a f => ?_⟩
    · rw [fieldObservable_eq_coeffMap, fieldObservable_eq_coeffMap, fieldObservable_eq_coeffMap,
        sampleAtBarycenters_add, map_add]
      rfl
    · rw [fieldObservable_eq_coeffMap, fieldObservable_eq_coeffMap, sampleAtBarycenters_smul,
        map_smul]
      rfl
end Coefficients
def boundedRealSubmodule : Submodule ℝ (D.Torus → ℝ) where
  carrier := D.boundedRealFuns
  add_mem' := by
    rintro f g ⟨C, hC⟩ ⟨C', hC'⟩
    exact ⟨C + C', fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hC' x))⟩
  zero_mem' := ⟨0, fun x => by simp⟩
  smul_mem' := by
    rintro a f ⟨C, hC⟩
    refine ⟨‖a‖ * C, fun x => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
theorem complexification_boundedRealSubmodule :
    D.complexification (boundedRealSubmodule D) = D.boundedComplexFuns := by
  ext f
  constructor
  · rintro ⟨⟨C, hC⟩, ⟨C', hC'⟩⟩
    refine ⟨C + C', fun x => ?_⟩
    have hre : |(f x).re| ≤ C := by simpa [markPart] using hC x
    have him : |(f x).im| ≤ C' := by simpa [markPart] using hC' x
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hre him)
  · rintro ⟨C, hC⟩
    refine ⟨⟨C, fun x => ?_⟩, ⟨C, fun x => ?_⟩⟩
    · simpa [markPart] using (Complex.abs_re_le_norm _).trans (hC x)
    · simpa [markPart] using (Complex.abs_im_le_norm _).trans (hC x)
theorem isLipschitzFor_of_isC1
    (hT : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (h : D.Torus → ℝ) (hh : D.IsC1 h) :
    TestFunctions.IsLipschitzFor (D.withDir 0).torusDist h := by
  have hpos : 0 < PeriodicLattice.torusSide D.L D.m := by
    have hL : 0 < (D.L : ℝ) := by
      have hadm := D.isAdmissible.2
      exact_mod_cast (by omega : 0 < D.L)
    unfold PeriodicLattice.torusSide
    positivity
  obtain ⟨C, hC0, hC⟩ := lipschitz_of_periodic_contDiff hpos (h ∘ D.proj) hh fun k x =>
    congrArg h (TestFunctions.torusProj_add_latticeTranslate _ x k)
  refine ⟨C, hC0, fun u u' => ?_⟩
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  obtain ⟨y, rfl⟩ := TestFunctions.torusProj_surjective _ u'
  obtain ⟨⟨k, hk⟩, -⟩ := (hT (D.withDir 0)).1.1 x y
  have hk' : TorusMetric.euclidNormVec
      (x - y - TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k) =
      (D.withDir 0).torusDist
        (TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) x)
        (TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) y) := hk
  have hx : TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) x = TorusMetric.torusProj
      (PeriodicLattice.torusSide D.L D.m)
      (x - TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k) := by
    have hshift := TestFunctions.torusProj_add_latticeTranslate (PeriodicLattice.torusSide D.L D.m)
      (x - TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k) k
    rwa [sub_add_cancel] at hshift
  change ‖h (TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) x) -
      h (TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) y)‖ ≤
    C * (D.withDir 0).torusDist (TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) x)
      (TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) y)
  rw [← hk']
  conv_lhs => rw [hx]
  refine (hC (x - TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k) y).trans
    (mul_le_mul_of_nonneg_left ?_ hC0)
  rw [sub_right_comm]
  exact norm_le_euclidNormVec _
end CentredIdentityArgument
open CentredIdentityArgument in
theorem centredIdentityAtAllFunctions_holds
    (hspace : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hlin : Cumulants.LinearMapCumulantProperties)
    (hclasses : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts) :
    CentredIdentityAtAllFunctions := by
  intro D
  have := finite_faces D hspace
  obtain ⟨_⟩ := nonempty_fintype D.LatticePlaq
  refine ⟨observableLinearAtBarycenters D hspace, fun n hn => ⟨connectedProperties D hspace hlin
      (by omega) univ univ, fun H => ⟨complexification_isSubspace D H,
        uniqueExtension_complexification D hspace hlin (by omega) H⟩,
      uniqueExtension_all D hspace hlin (by omega)⟩,
    fun q h _ => centred_identity_complex D hspace hlin h, connected_one_eq_expect D hspace hlin,
    ⟨⟨boundedRealSubmodule D, rfl, complexification_boundedRealSubmodule D,
      complexification_isSubspace D _,
      fun n hn => uniqueExtension_complexification D hspace hlin (by omega) _⟩,
      fun n hn => connectedProperties D hspace hlin (by omega) _ _,
      fun q h _ => centred_identity_complex D hspace hlin h⟩,
    fun q h _ _ => centred_identity_complex D hspace hlin (D.ofRealTuple h),
    fun h hh => isLipschitzFor_of_isC1 D hclasses h hh⟩
end YangMills.Construction.ConnectedFunctions
end

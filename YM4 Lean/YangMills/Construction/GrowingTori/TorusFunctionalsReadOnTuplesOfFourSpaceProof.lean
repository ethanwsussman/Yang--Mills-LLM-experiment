import YangMills.Construction.Cumulants.GeneratingFunctionOfBoundedRandomVariables
import YangMills.Construction.Cumulants.MomentsAndCentredMomentsThroughCumulants
import YangMills.Construction.GrowingTori.MultilinearityOfTheConnectedFunctions
import YangMills.Construction.GrowingTori.TorusFunctionalsReadOnTuplesOfFourSpace
import YangMills.Construction.GrowingTori.TransportOfFunctionsAndTuplesThroughTheBall
import YangMills.Construction.Lattice.LatticeAsAProbabilitySpace
import YangMills.Construction.ReflectionPositivity.CovarianceOfTheCurvatureDensity
import YangMills.Construction.ReflectionPositivity.DoublingOfTheCrossingVariables
import YangMills.Construction.ReflectionPositivity.ObservablesOfOneSideOfALinkMirror
import YangMills.Construction.ReflectionPositivity.PositivityOfTheWilsonMeasureAtALinkMirror
import YangMills.Construction.ReflectionPositivity.ReflectionInALinkMirror
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.CentredTensorMoments
open TorusTransport TorusTransport.TestFunctionOrders
open BallTuples (FnTuple R4Fun fnSupport lipTuplesBall subTupleOn)
open SourcesAndGluing (ballR4)
open Probability (IsBoundedRealRV IsBoundedComplexRV)
open BallPeriodization (IsPeriodizableInBall)
namespace TorusFunctionals
section ProbabilityFacts
variable (D : MomentData)
abbrev cutoffParams : Conventions.StandingParameters := D.atCutoff.toStandingParameters
abbrev Field : Type := LatticeProbability.GaugeConfig (cutoffParams D)
abbrev gibbs : Measure (Field D) := LatticeProbability.gibbsMeasureOn (cutoffParams D) D.β
def IsBoundedObs (G : D.BondField → ℂ) : Prop :=
  IsBoundedComplexRV fun U : Field D => G U.1
variable {D}
theorem IsBoundedObs.measurable {G : D.BondField → ℂ} (h : IsBoundedObs D G) :
    Measurable fun U : Field D => G U.1 := by
  have e : (fun U : Field D => G U.1) =
      fun U => (((G U.1).re : ℝ) : ℂ) + (((G U.1).im : ℝ) : ℂ) * Complex.I :=
    funext fun U => (Complex.re_add_im _).symm
  rw [e]
  exact (Complex.measurable_ofReal.comp h.measurable_re).add
    ((Complex.measurable_ofReal.comp h.measurable_im).mul_const _)
theorem isBoundedObs_of {G : D.BondField → ℂ} (h : Measurable fun U : Field D => G U.1)
    (hb : ∃ C : ℝ, ∀ U : Field D, ‖G U.1‖ ≤ C) : IsBoundedObs D G :=
  ⟨Complex.measurable_re.comp h, Complex.measurable_im.comp h, hb⟩
theorem isBoundedObs_const (z : ℂ) : IsBoundedObs D fun _ => z :=
  isBoundedObs_of measurable_const ⟨‖z‖, fun _ => le_rfl⟩
theorem IsBoundedObs.add {G G' : D.BondField → ℂ} (h : IsBoundedObs D G)
    (h' : IsBoundedObs D G') : IsBoundedObs D fun U => G U + G' U := by
  obtain ⟨C, hC⟩ := h.bounded
  obtain ⟨C', hC'⟩ := h'.bounded
  exact isBoundedObs_of (h.measurable.add h'.measurable)
    ⟨C + C', fun U => (norm_add_le _ _).trans (add_le_add (hC U) (hC' U))⟩
theorem IsBoundedObs.mul {G G' : D.BondField → ℂ} (h : IsBoundedObs D G)
    (h' : IsBoundedObs D G') : IsBoundedObs D fun U => G U * G' U := by
  obtain ⟨C, hC⟩ := h.bounded
  obtain ⟨C', hC'⟩ := h'.bounded
  refine isBoundedObs_of (h.measurable.mul h'.measurable) ⟨|C| * |C'|, fun U => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hC U).trans (le_abs_self _)) ((hC' U).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)
theorem isBoundedObs_sum {ι : Type*} (s : Finset ι) {G : ι → D.BondField → ℂ}
    (h : ∀ i ∈ s, IsBoundedObs D (G i)) : IsBoundedObs D fun U => ∑ i ∈ s, G i U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isBoundedObs_const (D := D) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
theorem isBoundedObs_prod {ι : Type*} (s : Finset ι) {G : ι → D.BondField → ℂ}
    (h : ∀ i ∈ s, IsBoundedObs D (G i)) : IsBoundedObs D fun U => ∏ i ∈ s, G i U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isBoundedObs_const (D := D) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
theorem isBoundedObs_ofReal {x : D.BondField → ℝ}
    (h : IsBoundedRealRV fun U : Field D => x U.1) :
    IsBoundedObs D fun U => ((x U : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := h.bounded
  exact isBoundedObs_of (Complex.measurable_ofReal.comp h.measurable)
    ⟨C, fun U => by simpa using hC U⟩
variable (hS : LatticeProbability.ProbabilitySpaceTheorem.claim)
include hS
theorem isProbabilityMeasure_gibbs : IsProbabilityMeasure (gibbs D) :=
  (hS (cutoffParams D) D.β D.β_pos).1.2.2.1
theorem expectation_eq_integral {G : D.BondField → ℂ} (h : IsBoundedObs D G) :
    D.expectation G = ∫ U : Field D, G U.1 ∂gibbs D :=
  (hS (cutoffParams D) D.β D.β_pos).1.2.2.2.2.2 G h
theorem IsBoundedObs.integrable {G : D.BondField → ℂ} (h : IsBoundedObs D G) :
    Integrable (fun U : Field D => G U.1) (gibbs D) := by
  have := isProbabilityMeasure_gibbs (D := D) hS
  obtain ⟨C, hC⟩ := h.bounded
  exact Integrable.of_bound h.measurable.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
theorem expectation_congr {G G' : D.BondField → ℂ} (h : IsBoundedObs D G)
    (e : ∀ U : Field D, G U.1 = G' U.1) : D.expectation G = D.expectation G' := by
  have h' : IsBoundedObs D G' := by
    have : (fun U : Field D => G' U.1) = fun U : Field D => G U.1 := funext fun U => (e U).symm
    unfold IsBoundedObs
    rw [this]
    exact h
  rw [expectation_eq_integral hS h, expectation_eq_integral hS h']
  exact integral_congr_ae (Filter.Eventually.of_forall e)
theorem expectation_sum {ι : Type*} (s : Finset ι) {G : ι → D.BondField → ℂ}
    (h : ∀ i ∈ s, IsBoundedObs D (G i)) :
    D.expectation (fun U => ∑ i ∈ s, G i U) = ∑ i ∈ s, D.expectation (G i) := by
  rw [expectation_eq_integral hS (isBoundedObs_sum s h), Finset.sum_congr rfl fun i hi =>
    expectation_eq_integral hS (h i hi)]
  exact integral_finsetSum s fun i hi => (h i hi).integrable hS
theorem expectation_const_mul {G : D.BondField → ℂ} (z : ℂ) (h : IsBoundedObs D G) :
    D.expectation (fun U => z * G U) = z * D.expectation G := by
  rw [expectation_eq_integral hS ((isBoundedObs_const z).mul h), expectation_eq_integral hS h]
  exact integral_const_mul z _
omit hS in
theorem expectation_ofReal (x : D.BondField → ℝ) :
    D.expectation (fun U => ((x U : ℝ) : ℂ)) = ((D.expectation x : ℝ) : ℂ) :=
  integral_complex_ofReal
theorem expectation_real_eq_integral {x : D.BondField → ℝ}
    (h : IsBoundedRealRV fun U : Field D => x U.1) :
    D.expectation x = ∫ U : Field D, x U.1 ∂gibbs D := by
  apply Complex.ofReal_injective
  rw [← expectation_ofReal, expectation_eq_integral hS (isBoundedObs_ofReal h)]
  exact integral_complex_ofReal
end ProbabilityFacts
section ObservableFacts
variable {D : MomentData}
theorem smearedObservable_eq_sum {E : Type*} [AddCommMonoid E] [Module ℝ E]
    [Fintype D.Plaquette] (u : D.Torus → E) (U : D.BondField) :
    PeriodicLattice.smearedObservable u U =
      ∑ p : D.Plaquette, PeriodicLattice.plaquetteCost U p • u p.barycenter :=
  finsum_eq_sum_of_fintype _
variable (hS : LatticeProbability.ProbabilitySpaceTheorem.claim)
include hS
theorem finite_plaquette : Finite D.Plaquette := (hS (cutoffParams D) D.β D.β_pos).2.1.1
theorem plaquetteCost_boundedRV (p : D.Plaquette) :
    IsBoundedRealRV fun U : Field D => PeriodicLattice.plaquetteCost U.1 p :=
  ((hS (cutoffParams D) D.β D.β_pos).2.1.2 p).2.2
theorem centredPlaquetteCost_boundedRV (p : D.Plaquette) :
    IsBoundedRealRV fun U : Field D => D.centredPlaquetteCost p U.1 := by
  have h := plaquetteCost_boundedRV (D := D) hS p
  obtain ⟨C, hC⟩ := h.bounded
  refine ⟨h.measurable.sub_const _,
    C + |D.expectation fun U' => PeriodicLattice.plaquetteCost U' p|, fun U => ?_⟩
  exact (abs_sub _ _).trans (add_le_add (hC U) le_rfl)
theorem isBoundedObs_centredPlaquetteCost (p : D.Plaquette) :
    IsBoundedObs D fun U => ((D.centredPlaquetteCost p U : ℝ) : ℂ) :=
  isBoundedObs_ofReal (centredPlaquetteCost_boundedRV hS p)
theorem isBoundedObs_plaquetteCost (p : D.Plaquette) :
    IsBoundedObs D fun U => ((PeriodicLattice.plaquetteCost U p : ℝ) : ℂ) :=
  isBoundedObs_ofReal (plaquetteCost_boundedRV hS p)
theorem expectation_smearedObservable [Fintype D.Plaquette] (u : D.Torus → ℂ) :
    D.expectation (PeriodicLattice.smearedObservable u) =
      ∑ p : D.Plaquette,
        (((D.expectation fun U' => PeriodicLattice.plaquetteCost U' p) : ℝ) : ℂ) *
          u p.barycenter := by
  have e : (PeriodicLattice.smearedObservable u : D.BondField → ℂ) = fun U =>
      ∑ p : D.Plaquette, u p.barycenter * ((PeriodicLattice.plaquetteCost U p : ℝ) : ℂ) := by
    funext U
    rw [smearedObservable_eq_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.real_smul, mul_comm]
  rw [e, expectation_sum hS _ fun p _ =>
    (isBoundedObs_const _).mul (isBoundedObs_plaquetteCost hS p)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [expectation_const_mul hS _ (isBoundedObs_plaquetteCost hS p), expectation_ofReal, mul_comm]
theorem centredObservable_eq_sum [Fintype D.Plaquette] (u : D.Torus → ℂ) (U : D.BondField) :
    D.atCutoff.centredObservable u U =
      ∑ p : D.Plaquette, ((D.centredPlaquetteCost p U : ℝ) : ℂ) * u p.barycenter := by
  have e : PeriodicLattice.gibbsExpectation D.atCutoff.L D.atCutoff.m D.atCutoff.K
      D.atCutoff.coupling (PeriodicLattice.smearedObservable u) =
      ∑ p : D.Plaquette,
        (((D.expectation fun U' => PeriodicLattice.plaquetteCost U' p) : ℝ) : ℂ) *
          u p.barycenter := expectation_smearedObservable hS u
  rw [ReflectionPositivity.CutoffMirrors.MirrorData.centredObservable, e, smearedObservable_eq_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.real_smul, MomentData.centredPlaquetteCost]
  push_cast
  ring
omit hS in
theorem smearedObservable_ofReal [Fintype D.Plaquette] (g : D.Torus → ℝ) (U : D.BondField) :
    PeriodicLattice.smearedObservable (fun x => ((g x : ℝ) : ℂ)) U =
      ((PeriodicLattice.smearedObservable g U : ℝ) : ℂ) := by
  rw [smearedObservable_eq_sum, smearedObservable_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.real_smul, smul_eq_mul]
  push_cast
  rfl
omit hS in
theorem centredObservable_ofReal [Fintype D.Plaquette] (g : D.Torus → ℝ) (U : D.BondField) :
    D.atCutoff.centredObservable (fun x => ((g x : ℝ) : ℂ)) U =
      ((D.atCutoff.centredObservable g U : ℝ) : ℂ) := by
  have e : (PeriodicLattice.smearedObservable (fun x => ((g x : ℝ) : ℂ)) :
      D.BondField → ℂ) = fun U => ((PeriodicLattice.smearedObservable g U : ℝ) : ℂ) :=
    funext fun U => smearedObservable_ofReal g U
  have e' : PeriodicLattice.gibbsExpectation D.atCutoff.L D.atCutoff.m D.atCutoff.K
      D.atCutoff.coupling (PeriodicLattice.smearedObservable (fun x => ((g x : ℝ) : ℂ))) =
      (((PeriodicLattice.gibbsExpectation D.atCutoff.L D.atCutoff.m D.atCutoff.K
        D.atCutoff.coupling (PeriodicLattice.smearedObservable g)) : ℝ) : ℂ) := by
    rw [e]
    exact expectation_ofReal _
  rw [ReflectionPositivity.CutoffMirrors.MirrorData.centredObservable,
    ReflectionPositivity.CutoffMirrors.MirrorData.centredObservable, e',
    smearedObservable_ofReal]
  push_cast
  rfl
omit hS in
theorem suppR4_ofReal (f : R4Fun) :
    SourcesAndGluing.GluingSetup.suppR4 (fun x => ((f x : ℝ) : ℂ)) =
      SourcesAndGluing.GluingSetup.suppR4 f := by
  simp [SourcesAndGluing.GluingSetup.suppR4]
omit hS in
theorem periodizable_ofReal {ρ : ℝ} {f : R4Fun}
    (hf : IsPeriodizableInBall D.toParams ρ f) :
    IsPeriodizableInBall D.toParams ρ (fun x => ((f x : ℝ) : ℂ)) := by
  refine ⟨hf.1, hf.2.1, ?_, ?_⟩
  · rw [suppR4_ofReal]
    exact hf.2.2.1
  · rw [suppR4_ofReal]
    exact hf.2.2.2
omit hS in
theorem periodize_ofReal {ρ : ℝ} {f : R4Fun}
    (hf : IsPeriodizableInBall D.toParams ρ f) :
    TestFunctions.periodize D.side (fun x => ((f x : ℝ) : ℂ)) =
      fun u => ((TestFunctions.periodize D.side f u : ℝ) : ℂ) := by
  funext u
  by_cases hu : u ∈ TorusMetric.torusProj D.side '' ballR4 ρ
  · obtain ⟨x, hx, rfl⟩ := hu
    rw [(periodizable_ofReal hf).periodize_torusProj_of_mem hx, hf.periodize_torusProj_of_mem hx]
  · rw [(periodizable_ofReal hf).periodize_eq_zero hu, hf.periodize_eq_zero hu]
    simp
omit hS in
theorem tensorObservable_succ {ρ : ℝ} [Fintype (D.PlaquetteInBall ρ)] {q : ℕ}
    (F : OrderedTestFun (q + 1)) (U : D.BondField) :
    D.tensorObservable ρ F U = ∑ p : Fin (q + 1) → D.PlaquetteInBall ρ,
      F (fun l => MomentData.ballPoint (p l)) *
        ∏ l, ((D.centredPlaquetteCost (p l).1 U : ℝ) : ℂ) :=
  finsum_eq_sum_of_fintype _
theorem tensorObservable_tupleTensor {ρ : ℝ} {q : ℕ} (f : Fin q → ComplexFun (Fin 4 → ℝ))
    (hf : ∀ l, IsPeriodizableInBall D.toParams ρ (f l)) (U : D.BondField) :
    D.tensorObservable ρ (tupleTensor f) U =
      ∏ l, D.atCutoff.centredObservable (TestFunctions.periodize D.side (f l)) U := by
  classical
  have := finite_plaquette (D := D) hS
  let _ : Fintype D.Plaquette := Fintype.ofFinite _
  cases q with
  | zero => simp [tupleTensor, MomentData.tensorObservable]
  | succ q =>
    have key : ∀ l, D.atCutoff.centredObservable (TestFunctions.periodize D.side (f l)) U =
        ∑ p : D.PlaquetteInBall ρ, ((D.centredPlaquetteCost p.1 U : ℝ) : ℂ) *
          f l (MomentData.ballPoint p) := by
      intro l
      rw [centredObservable_eq_sum hS]
      symm
      refine Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _ (fun p hp => ?_)
        (fun p => ?_)
      · have hp' : p.barycenter ∉ D.projectedBall ρ := fun h => hp ⟨⟨p, h⟩, rfl⟩
        rw [(hf l).periodize_eq_zero hp', mul_zero]
      · rw [← MomentData.torusProj_ballPoint p,
          (hf l).periodize_torusProj_of_mem (MomentData.ballPoint_mem p)]
    simp only [key]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, tensorObservable_succ]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_mul_distrib, mul_comm]
    rfl
theorem tensorObservable_realTuple {ρ : ℝ} {q : ℕ} (X : FnTuple q)
    (hX : ∀ l, IsPeriodizableInBall D.toParams ρ (X l)) (U : D.BondField) :
    D.tensorObservable ρ (realTupleTensor X) U =
      ∏ l, ((D.atCutoff.centredObservable (TestFunctions.periodize D.side (X l)) U : ℝ) : ℂ) := by
  classical
  have := finite_plaquette (D := D) hS
  let _ : Fintype D.Plaquette := Fintype.ofFinite _
  rw [realTupleTensor, tensorObservable_tupleTensor hS _ fun l => periodizable_ofReal (hX l)]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [periodize_ofReal (hX l), centredObservable_ofReal]
theorem tensorObservable_linComb {ρ : ℝ} {q n : ℕ} (c : Fin n → ℂ)
    (T : Fin n → OrderedTestFun q) (U : D.BondField) :
    D.tensorObservable ρ (linComb c T) U = ∑ b, c b * D.tensorObservable ρ (T b) U := by
  classical
  have := finite_plaquette (D := D) hS
  let _ : Fintype D.Plaquette := Fintype.ofFinite _
  cases q with
  | zero => rfl
  | succ q =>
    simp only [tensorObservable_succ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show linComb c T (fun l => MomentData.ballPoint (p l)) =
      ∑ b, c b * T b (fun l => MomentData.ballPoint (p l)) from rfl, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => mul_assoc _ _ _
theorem isBoundedObs_tensorObservable (ρ : ℝ) {q : ℕ} (F : OrderedTestFun q) :
    IsBoundedObs D (D.tensorObservable ρ F) := by
  classical
  have := finite_plaquette (D := D) hS
  let _ : Fintype D.Plaquette := Fintype.ofFinite _
  cases q with
  | zero => exact isBoundedObs_const _
  | succ q =>
    have e : D.tensorObservable ρ F = fun U => ∑ p : Fin (q + 1) → D.PlaquetteInBall ρ,
        F (fun l => MomentData.ballPoint (p l)) *
          ∏ l, ((D.centredPlaquetteCost (p l).1 U : ℝ) : ℂ) :=
      funext fun U => tensorObservable_succ F U
    unfold IsBoundedObs
    rw [e]
    exact isBoundedObs_sum _ fun p _ => (isBoundedObs_const _).mul
      (isBoundedObs_prod _ fun l _ => isBoundedObs_centredPlaquetteCost hS _)
end ObservableFacts
section Connected
variable {D : MomentData}
variable (hS : LatticeProbability.ProbabilitySpaceTheorem.claim)
theorem exists_common_bound {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (x : Fin n → Ω → ℝ)
    (h : ∀ i, IsBoundedRealRV (x i)) : ∃ b : ℝ, 0 < b ∧ ∀ i ω, |x i ω| ≤ b := by
  choose C hC using fun i => (h i).bounded
  refine ⟨1 + ∑ i, |C i|, by positivity, fun i ω => ?_⟩
  have h₁ : |C i| ≤ ∑ i, |C i| :=
    Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h₂ := (hC i ω).trans (le_abs_self _)
  linarith
include hS in
theorem observableOn_boundedRV (u : D.Torus → ℝ) :
    IsBoundedRealRV (LatticeProbability.observableOn (cutoffParams D) u) :=
  (hS (cutoffParams D) D.β D.β_pos).2.2.2.1.1 u
include hS in
theorem connectedFn_eq_mixedCumulant {n : ℕ} (hn : 1 ≤ n) (X : FnTuple n) :
    BallTuples.connectedFn D.toParams D.K D.β X =
      Cumulants.mixedCumulant (gibbs D) (LatticeProbability.observableVector (cutoffParams D)
        (BallTuples.periodize D.toParams X)) :=
  ((hS (cutoffParams D) D.β D.β_pos).2.2.2.2.1 n
    (BallTuples.periodize D.toParams X) hn).1
theorem isBoundedRealRV_prod {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} (s : Finset ι)
    {x : ι → Ω → ℝ} (h : ∀ i ∈ s, IsBoundedRealRV (x i)) :
    IsBoundedRealRV fun ω => ∏ i ∈ s, x i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using measurable_const, 1, by simp⟩
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    obtain ⟨h₁, C, hC⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨h₂, C', hC'⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨h₁.mul h₂, |C| * |C'|, fun ω => ?_⟩
    rw [abs_mul]
    exact mul_le_mul ((hC ω).trans (le_abs_self _)) ((hC' ω).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
section ConnectedProps
variable (hG : Cumulants.BoundedVariables.BoundedGeneratingFunctionTheorem)
  (hMul : BallTuples.ConnectedMultilinearity.Statement)
  (hMom : Cumulants.MomentsViaCumulants)
include hS hG hMul in
theorem connectedProperties (ρ : ℝ) (hρ : D.IsRadius ρ) (n : ℕ) (hn : 2 ≤ n) :
    ConnectedProperties D ρ n := by
  have hs := (hMul.2 D.toParams D.K D.β D.β_pos n hn).2
  refine ⟨hs.im_eq_zero ρ hρ.1 hρ.2, ?_, ?_, fun ρ' _ X h h' => rfl⟩
  · rintro ⟨X, hX⟩ σ
    have hP := isProbabilityMeasure_gibbs (D := D) hS
    have h1 : 1 ≤ n := by omega
    have hx : ∀ i, IsBoundedRealRV (LatticeProbability.observableVector
        (cutoffParams D) (BallTuples.periodize D.toParams X) i) :=
      fun i => observableOn_boundedRV hS _
    obtain ⟨b, hb, hb'⟩ := exists_common_bound _ hx
    have := (hG (Field D) (gibbs D) n _ b h1 hx hb hb').2.2.2.1.symmetric σ
    simp only [connectedReal]
    rw [connectedFn_eq_mixedCumulant hS h1, connectedFn_eq_mixedCumulant hS h1, ← this]
    rfl
  · intro A hA hd X hX l f g a b hf hg hf' hg' hc
    simp only [connectedReal]
    rw [hs.map_update_add ρ hρ.1 hρ.2 X l f g a b hf' hg' hc]
    simp
include hS hMom in
theorem momentPartitionExpansion (ρ : ℝ) : MomentPartitionExpansion D ρ := by
  intro q X _
  have hP := isProbabilityMeasure_gibbs (D := D) hS
  set x := LatticeProbability.observableVector (cutoffParams D)
    (BallTuples.periodize D.toParams X) with hx
  have hb : ∀ l, IsBoundedRealRV (x l) := fun l => observableOn_boundedRV hS _
  have hm := (hMom (Field D) (gibbs D) q x hb).2
  have hc : ∀ l, D.atCutoff.centredObservable (BallTuples.periodize D.toParams X l) =
      fun U => PeriodicLattice.smearedObservable (BallTuples.periodize D.toParams X l) U -
        ∫ U' : Field D, x l U' ∂gibbs D := by
    intro l
    funext U
    rw [ReflectionPositivity.CutoffMirrors.MirrorData.centredObservable]
    congr 1
    exact expectation_real_eq_integral hS (hb l)
  have hrv : IsBoundedRealRV fun U : Field D =>
      ∏ l, D.atCutoff.centredObservable (BallTuples.periodize D.toParams X l) U.1 := by
    refine isBoundedRealRV_prod _ fun l _ => ?_
    simp only [hc]
    obtain ⟨h₁, C, hC⟩ := hb l
    exact ⟨h₁.sub_const _, C + |∫ U' : Field D, x l U' ∂gibbs D|,
      fun U => (abs_sub _ _).trans (add_le_add (hC U) le_rfl)⟩
  have e : D.functionalOfPeriodized X =
      ∫ ω, ∏ l, (x l ω - ∫ ω', x l ω' ∂gibbs D) ∂gibbs D := by
    rw [MomentData.functionalOfPeriodized, MomentData.gibbsFunctional_eq,
      expectation_real_eq_integral hS hrv]
    simp only [hc]
    rfl
  rw [e, hm]
  refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J hJ => ?_
  have hJ' : 1 ≤ J.card := Finset.card_pos.mpr (π.nonempty_of_mem_parts hJ)
  rw [connectedFn_eq_mixedCumulant hS hJ']
  rfl
end ConnectedProps
end Connected
section TensorCalculus
variable {D : MomentData}
variable (hS : LatticeProbability.ProbabilitySpaceTheorem.claim)
theorem IsBallTensorSum.apply_eq_zero {ρ : ℝ} {q : ℕ} {F : OrderedTestFun (q + 1)}
    (hF : IsBallTensorSum ρ (q + 1) F) {x : Configuration (q + 1)} {l : Fin (q + 1)}
    (hx : x l ∉ ballR4 ρ) : F x = 0 := by
  obtain ⟨n, f, hb, hE⟩ := hF
  have e : F x = ∑ b, prodTensor (f b) x := by
    rw [show F x = (F : ComplexFun (Configuration (q + 1))) x from rfl, hE, Finset.sum_apply]
  rw [e]
  refine Finset.sum_eq_zero fun b _ => Finset.prod_eq_zero (Finset.mem_univ l) ?_
  by_contra h
  exact hx ((hb b l).2.2 (subset_closure h))
theorem projectedBall_mono {ρ ρ' : ℝ} (hle : ρ ≤ ρ') : D.projectedBall ρ ⊆ D.projectedBall ρ' :=
  image_mono fun _ hx => lt_of_lt_of_le hx hle
theorem tensorObservable_eq_of_radius_le
    (hT : PeriodizationThroughBall.PeriodizationLemma) (hS' : Finite D.Plaquette)
    {ρ ρ' : ℝ} (hρ' : D.IsRadius ρ') (hle : ρ ≤ ρ') {q : ℕ} {F : OrderedTestFun q}
    (hF : IsBallTensorSum ρ q F) : D.tensorObservable ρ F = D.tensorObservable ρ' F := by
  classical
  let _ : Fintype D.Plaquette := Fintype.ofFinite _
  cases q with
  | zero => rfl
  | succ q =>
    funext U
    have hinj : InjOn (TorusMetric.torusProj D.side) (ballR4 ρ') :=
      (hT D.toParams ρ' hρ'.1 hρ'.2).1.2.2.2.1
    let ι : D.PlaquetteInBall ρ → D.PlaquetteInBall ρ' :=
      fun p => ⟨p.1, projectedBall_mono hle p.2⟩
    have hι : ∀ p, MomentData.ballPoint (ι p) = MomentData.ballPoint p := fun p =>
      hinj (MomentData.ballPoint_mem (ι p)) (lt_of_lt_of_le (MomentData.ballPoint_mem p) hle)
        ((MomentData.torusProj_ballPoint (ι p)).trans (MomentData.torusProj_ballPoint p).symm)
    rw [tensorObservable_succ, tensorObservable_succ]
    refine Fintype.sum_of_injective (fun p l => ι (p l)) (fun p p' h => funext fun l =>
      Subtype.ext (congrArg (fun r => (r l).1) h)) _ _ (fun r hr => ?_) (fun p => ?_)
    · have hl : ∃ l, (r l).1.barycenter ∉ D.projectedBall ρ := by
        by_contra h
        push_neg at h
        exact hr ⟨fun l => ⟨(r l).1, h l⟩, funext fun l => Subtype.ext rfl⟩
      obtain ⟨l, hl⟩ := hl
      have hx : MomentData.ballPoint (r l) ∉ ballR4 ρ := fun hb =>
        hl ⟨_, hb, MomentData.torusProj_ballPoint (r l)⟩
      rw [IsBallTensorSum.apply_eq_zero hF (x := fun l => MomentData.ballPoint (r l)) hx,
        zero_mul]
    · simp only [hι]
      rfl
theorem tensorObservable_radius_indep
    (hT : PeriodizationThroughBall.PeriodizationLemma) (hS' : Finite D.Plaquette)
    {ρ ρ' : ℝ} (hρ : D.IsRadius ρ) (hρ' : D.IsRadius ρ') {q : ℕ} {F : OrderedTestFun q}
    (hF : IsBallTensorSum ρ q F) (hF' : IsBallTensorSum ρ' q F) :
    D.tensorObservable ρ F = D.tensorObservable ρ' F := by
  rcases le_total ρ ρ' with h | h
  · exact tensorObservable_eq_of_radius_le hT hS' hρ' h hF
  · exact (tensorObservable_eq_of_radius_le hT hS' hρ h hF').symm
theorem tensorObservable_mul (hS' : Finite D.Plaquette) (ρ : ℝ) {q q' : ℕ}
    (F : OrderedTestFun q) (F' : OrderedTestFun q') (U : D.BondField) :
    D.tensorObservable ρ F U * D.tensorObservable ρ F' U =
      D.tensorObservable ρ (gradedTensor ⟨q, F⟩ ⟨q', F'⟩).2 U := by
  classical
  let _ : Fintype D.Plaquette := Fintype.ofFinite _
  cases q with
  | zero =>
    cases q' with
    | zero => rfl
    | succ q' =>
      change (F : ℂ) * D.tensorObservable ρ F' U =
        D.tensorObservable ρ (q := q' + 1) (fun x => (F : ℂ) * F' x) U
      rw [tensorObservable_succ, tensorObservable_succ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => (mul_assoc _ _ _).symm
  | succ q =>
    cases q' with
    | zero =>
      change D.tensorObservable ρ F U * (F' : ℂ) =
        D.tensorObservable ρ (q := q + 1) (fun x => (F' : ℂ) * F x) U
      rw [tensorObservable_succ, tensorObservable_succ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    | succ q' =>
      change D.tensorObservable ρ F U * D.tensorObservable ρ F' U =
        D.tensorObservable ρ (q := q + 1 + q' + 1) (tensor (p := q + 1) (q := q' + 1) F F') U
      rw [tensorObservable_succ, tensorObservable_succ,
        tensorObservable_succ (q := q + 1 + q'), Finset.sum_mul_sum, ← Fintype.sum_prod_type']
      refine Fintype.sum_equiv (Fin.appendEquiv (q + 1) (q' + 1)) _ _ fun r => ?_
      have e : (fun l => MomentData.ballPoint (Fin.append r.1 r.2 l)) =
          Fin.append (fun l => MomentData.ballPoint (r.1 l))
            (fun l => MomentData.ballPoint (r.2 l)) := by
        funext l
        refine Fin.addCases (fun i => ?_) (fun k => ?_) l
        · simp
        · simp
      have hp : ∏ l, ((D.centredPlaquetteCost (Fin.append r.1 r.2 l).1 U : ℝ) : ℂ) =
          (∏ l, ((D.centredPlaquetteCost (r.1 l).1 U : ℝ) : ℂ)) *
            ∏ l, ((D.centredPlaquetteCost (r.2 l).1 U : ℝ) : ℂ) := by
        rw [Fin.prod_univ_add]
        simp
      change _ = tensor (p := q + 1) (q := q' + 1) F F'
          (fun l => MomentData.ballPoint (Fin.append r.1 r.2 l)) *
        ∏ l, ((D.centredPlaquetteCost (Fin.append r.1 r.2 l).1 U : ℝ) : ℂ)
      rw [e, tensor_append, hp]
      ring
theorem tensorObservable_conj (hS' : Finite D.Plaquette) (ρ : ℝ) {q : ℕ}
    (F : OrderedTestFun q) (U : D.BondField) :
    conj (D.tensorObservable ρ F U) = D.tensorObservable ρ (conjFn F) U := by
  classical
  let _ : Fintype D.Plaquette := Fintype.ofFinite _
  cases q with
  | zero => rfl
  | succ q =>
    rw [tensorObservable_succ, tensorObservable_succ, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, map_prod]
    simp only [Complex.conj_ofReal]
    rfl
theorem centredTensorMoment_realTuple (hS : LatticeProbability.ProbabilitySpaceTheorem.claim)
    {ρ : ℝ} (hρ : D.IsRadius ρ) {q : ℕ} {X : FnTuple q}
    (hX : X ∈ lipTuplesBall q ρ) :
    D.centredTensorMoment ρ (realTupleTensor X) = ((D.functionalOfPeriodized X : ℝ) : ℂ) := by
  have e : D.tensorObservable ρ (realTupleTensor X) = fun U =>
      ((∏ l, D.atCutoff.centredObservable (BallTuples.periodize D.toParams X l) U : ℝ) :
        ℂ) := by
    funext U
    rw [tensorObservable_realTuple hS X fun l => ⟨hρ.1, hρ.2, hX.2 l⟩]
    push_cast
    rfl
  rw [MomentData.centredTensorMoment, e, expectation_ofReal, MomentData.functionalOfPeriodized,
    MomentData.gibbsFunctional_eq]
include hS in
theorem tensorObservableCalculus (hT : PeriodizationThroughBall.PeriodizationLemma) (ρ : ℝ)
    (hρ : D.IsRadius ρ) : TensorObservableCalculus D ρ := by
  have hfin := finite_plaquette (D := D) hS
  refine ⟨fun q n c T _ U => tensorObservable_linComb hS c T U,
    fun ρ' hρ' q F h h' => tensorObservable_radius_indep hT hfin hρ hρ' h h',
    fun q q' F F' _ _ U => tensorObservable_mul hfin ρ F F' U,
    fun q F _ U => tensorObservable_conj hfin ρ F U,
    fun q f hf U => tensorObservable_tupleTensor hS f (fun l => ⟨hρ.1, hρ.2, (hf l).2⟩) U,
    fun q X hX => centredTensorMoment_realTuple hS hρ hX, ?_⟩
  intro q n c X hX
  have e : D.tensorObservable ρ (linComb c fun b => realTupleTensor (X b)) = fun U =>
      ∑ b, c b * D.tensorObservable ρ (realTupleTensor (X b)) U :=
    funext fun U => tensorObservable_linComb hS c _ U
  rw [MomentData.centredTensorMoment, e, expectation_sum hS _ fun b _ =>
    (isBoundedObs_const _).mul (isBoundedObs_tensorObservable hS ρ _)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [expectation_const_mul hS _ (isBoundedObs_tensorObservable hS ρ _)]
  exact congrArg (c b * ·) (centredTensorMoment_realTuple hS hρ (hX b)).symm
end TensorCalculus
section Invariance
variable {D : MomentData}
theorem IsLatticeSymmetry.exists_affine {s : TorusPeriodization.euclideanMotions}
    (hs : IsLatticeSymmetry D s) :
    ∃ R : PeriodicLattice.SignedFrame, ∃ v ∈ PeriodicLattice.meshVectors D.L ((D.K : ℕ) : ℤ),
      ∀ x, (s : Equiv.Perm (Fin 4 → ℝ)) x = R.actOnVector x + v := by
  rcases hs with ⟨k, hk⟩ | ⟨π, σ, hσ⟩ | ⟨μ, c, k, hc, rfl⟩
  · refine ⟨(1, fun _ => 1), fun ν => D.atCutoff.spacing * (k ν : ℝ),
      ⟨k, fun ν => mul_comm _ _⟩, fun x => ?_⟩
    rw [hk]
    congr 1
    funext ν
    simp [PeriodicLattice.SignedFrame.actOnVector]
  · refine ⟨(π, σ), 0, ⟨0, fun ν => by simp⟩, fun x => ?_⟩
    rw [hσ, add_zero]
    rfl
  · refine ⟨(1, fun ν => if ν = μ then -1 else 1), Pi.single μ (D.atCutoff.spacing * (k : ℝ)),
      ⟨Pi.single μ k, fun ν => ?_⟩, fun x => ?_⟩
    · by_cases h : ν = μ
      · subst h
        simp only [Pi.single_eq_same]
        exact mul_comm _ _
      · simp [Pi.single_eq_of_ne h]
    · rw [BallPeriodization.hyperplaneReflection_apply]
      funext ν
      by_cases h : ν = μ
      · subst h
        simp [PeriodicLattice.SignedFrame.actOnVector, PeriodicLattice.coordVec, ← hc]
        ring
      · simp [PeriodicLattice.SignedFrame.actOnVector, PeriodicLattice.coordVec, h]
theorem exists_symmetry
    (hI : ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance)
    {s : TorusPeriodization.euclideanMotions} (hs : IsLatticeSymmetry D s) :
    ∃ t : D.atCutoff.Symmetry, t.toFun = BallPeriodization.torusMap D.toParams s := by
  obtain ⟨R, v, hv, h⟩ := IsLatticeSymmetry.exists_affine hs
  obtain ⟨t, ht⟩ := (hI D.atCutoff).1.1 R v hv
  refine ⟨t, funext fun u => ?_⟩
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective D.side u
  refine (ht x).trans ?_
  rw [← h]
  exact (congrFun (BallPeriodization.torusMap_comp_torusProj D.toParams s) x).symm
theorem connectedInvariance
    (hT : PeriodizationThroughBall.PeriodizationLemma)
    (hI : ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance)
    (hC : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (ρ : ℝ) (hρ : D.IsRadius ρ) (n : ℕ) (hn : 2 ≤ n) : ConnectedInvariance D ρ n := by
  intro s hs X hX hXs
  obtain ⟨t, ht⟩ := exists_symmetry hI hs
  have hTρ := hT D.toParams ρ hρ.1 hρ.2
  have hXt : BallTuples.IsPeriodizable D.toParams ρ X := ⟨hρ.1, hρ.2, hX.1, hX.2⟩
  have hcomp : BallTuples.periodize D.toParams (BallPeriodization.tupleComp X s) =
      fun l => BallTuples.periodize D.toParams X l ∘ t.toFun := by
    funext l
    rw [ht]
    exact (hTρ.2.1 ℝ).2.2.2.2.2 (X l) s ⟨hρ.1, hρ.2, hX.2 l⟩ ⟨hρ.1, hρ.2, hXs.2 l⟩
  obtain ⟨hLip, -, hDis, -⟩ := hTρ.2.2.2.2 n (by omega) X hXt
  have htest : SchwingerFunctions.IsTorusTestFamily (BallTuples.periodize D.toParams X) :=
    ((hC D.atCutoff).2.2.1.2 n _ hn
      (fun l l' hl => Set.disjoint_iff_inter_eq_empty.1 (hDis l l' hl)) hLip).1
  obtain ⟨hb, hm, d, hd⟩ := htest
  have hconn := ((hI D.atCutoff).2 t)
  obtain ⟨-, -, t', -, -, -, -, -, -, -, hOn, -⟩ := hconn
  rw [BallTuples.connectedFn_eq_connectedSchwinger,
    BallTuples.connectedFn_eq_connectedSchwinger, hcomp]
  exact (hOn n hn _ d hb hm hd).2.2.2
end Invariance
section AxisReflection
abbrev axisRefl (μ : Fin 4) (c : ℝ) : Equiv.Perm (Fin 4 → ℝ) :=
  (BallPeriodization.hyperplaneReflection μ c : Equiv.Perm (Fin 4 → ℝ))
theorem axisRefl_apply_self (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    axisRefl μ c x μ = 2 * c - x μ := by
  rw [BallPeriodization.hyperplaneReflection_apply]
  simp [PeriodicLattice.coordVec]
  ring
theorem axisRefl_apply_of_ne {μ ν : Fin 4} (h : ν ≠ μ) (c : ℝ) (x : Fin 4 → ℝ) :
    axisRefl μ c x ν = x ν := by
  rw [BallPeriodization.hyperplaneReflection_apply]
  simp [PeriodicLattice.coordVec, h]
theorem axisRefl_axisRefl (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    axisRefl μ c (axisRefl μ c x) = x := by
  funext ν
  by_cases h : ν = μ
  · subst h
    rw [axisRefl_apply_self, axisRefl_apply_self]
    ring
  · rw [axisRefl_apply_of_ne h, axisRefl_apply_of_ne h]
theorem continuous_axisRefl (μ : Fin 4) (c : ℝ) : Continuous (axisRefl μ c) := by
  have e : (axisRefl μ c : (Fin 4 → ℝ) → Fin 4 → ℝ) =
      fun x => x - (2 * (x μ - c)) • PeriodicLattice.coordVec μ :=
    funext fun x => BallPeriodization.hyperplaneReflection_apply μ c x
  rw [e]
  fun_prop
def axisReflHomeo (μ : Fin 4) (c : ℝ) : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toFun := axisRefl μ c
  invFun := axisRefl μ c
  left_inv := axisRefl_axisRefl μ c
  right_inv := axisRefl_axisRefl μ c
  continuous_toFun := continuous_axisRefl μ c
  continuous_invFun := continuous_axisRefl μ c
theorem fnSupport_comp_axisRefl (μ : Fin 4) (c : ℝ) (f : R4Fun) :
    fnSupport (f ∘ axisRefl μ c) = axisRefl μ c ⁻¹' fnSupport f :=
  ((axisReflHomeo μ c).preimage_closure {x | f x ≠ 0}).symm
theorem abs_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem euclidDistR4_axisRefl (μ : Fin 4) (c : ℝ) (x y : Fin 4 → ℝ) :
    TestFunctions.euclidDistR4 (axisRefl μ c x) (axisRefl μ c y) =
      TestFunctions.euclidDistR4 x y := by
  have h : ∀ ν, (axisRefl μ c x - axisRefl μ c y) ν ^ 2 = (x - y) ν ^ 2 := by
    intro ν
    by_cases h : ν = μ
    · subst h
      simp only [Pi.sub_apply, axisRefl_apply_self]
      ring
    · simp only [Pi.sub_apply, axisRefl_apply_of_ne h]
  simp only [TestFunctions.euclidDistR4, TorusMetric.euclidNormVec, h]
theorem isLipschitzFor_comp_axisRefl (μ : Fin 4) (c : ℝ) {f : R4Fun}
    (hf : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f) :
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 (f ∘ axisRefl μ c) := by
  obtain ⟨C, hC, h⟩ := hf
  refine ⟨C, hC, fun x y => ?_⟩
  rw [← euclidDistR4_axisRefl μ c x y]
  exact h _ _
theorem isCompact_fnSupport_comp_axisRefl (μ : Fin 4) (c : ℝ) {f : R4Fun}
    (hf : IsCompact (fnSupport f)) : IsCompact (fnSupport (f ∘ axisRefl μ c)) := by
  rw [fnSupport_comp_axisRefl]
  exact (axisReflHomeo μ c).isCompact_preimage.2 hf
theorem fnSupport_comp_axisRefl_subset {ρ : ℝ} {μ : Fin 4} {c : ℝ} {f : R4Fun}
    (hf : IsHalfSpaceComponent ρ μ c f) : fnSupport (f ∘ axisRefl μ c) ⊆ {x | x μ < c} := by
  intro x hx
  rw [fnSupport_comp_axisRefl] at hx
  have h := (hf.1 hx).2
  have h' : c < axisRefl μ c x μ := h
  rw [axisRefl_apply_self] at h'
  change x μ < c
  linarith
theorem tupleComp_mem {ρ : ℝ} {μ : Fin 4} {c : ℝ} {q : ℕ} {X : FnTuple q}
    (hX : BallTuples.IsSepLipschitz X)
    (hE : ∀ l, IsHalfSpaceComponent ρ μ c (X l)) :
    BallPeriodization.tupleComp X (BallPeriodization.hyperplaneReflection μ c) ∈
      lipTuplesBall q ρ := by
  refine ⟨⟨fun l => isLipschitzFor_comp_axisRefl μ c (hX.1 l),
    fun l => isCompact_fnSupport_comp_axisRefl μ c (hX.2.1 l), fun l l' hl => ?_⟩,
    fun l => ⟨isCompact_fnSupport_comp_axisRefl μ c (hX.2.1 l), (hE l).2⟩⟩
  change Disjoint (fnSupport (X l ∘ axisRefl μ c)) (fnSupport (X l' ∘ axisRefl μ c))
  rw [fnSupport_comp_axisRefl, fnSupport_comp_axisRefl]
  exact (hX.2.2 l l' hl).preimage _
theorem mem_lipTuplesBall {ρ : ℝ} {μ : Fin 4} {c : ℝ} {q : ℕ} {X : FnTuple q}
    (hX : BallTuples.IsSepLipschitz X)
    (hE : ∀ l, IsHalfSpaceComponent ρ μ c (X l)) : X ∈ lipTuplesBall q ρ :=
  ⟨hX, fun l => ⟨hX.2.1 l, (hE l).1.trans inter_subset_left⟩⟩
theorem append_mem {ρ : ℝ} {μ : Fin 4} {c : ℝ} {q q' : ℕ} {X : FnTuple q} {Y : FnTuple q'}
    (hX : BallTuples.IsSepLipschitz X)
    (hE : ∀ l, IsHalfSpaceComponent ρ μ c (X l))
    (hY : BallTuples.IsSepLipschitz Y)
    (hE' : ∀ l, IsHalfSpaceComponent ρ μ c (Y l)) :
    (Fin.append (BallPeriodization.tupleComp X (BallPeriodization.hyperplaneReflection μ c)) Y :
      FnTuple (q + q')) ∈ lipTuplesBall (q + q') ρ := by
  set Z := BallPeriodization.tupleComp X (BallPeriodization.hyperplaneReflection μ c) with hZ
  have hZm : Z ∈ lipTuplesBall q ρ := tupleComp_mem hX hE
  have hYm : Y ∈ lipTuplesBall q' ρ := mem_lipTuplesBall hY hE'
  have hcross : ∀ l l', Disjoint (fnSupport (Z l)) (fnSupport (Y l')) := by
    intro l l'
    refine Set.disjoint_left.2 fun x hx hy => ?_
    have h₁ : x μ < c := fnSupport_comp_axisRefl_subset (hE l) hx
    have h₂ : c < x μ := ((hE' l').1 hy).2
    linarith
  refine ⟨⟨fun l => ?_, fun l => ?_, fun l l' hl => ?_⟩, fun l => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) l
    · simpa using hZm.1.1 i
    · simpa using hYm.1.1 k
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) l
    · simpa using hZm.1.2.1 i
    · simpa using hYm.1.2.1 k
  · revert hl
    refine Fin.addCases (fun i => ?_) (fun k => ?_) l <;>
      refine Fin.addCases (fun i' => ?_) (fun k' => ?_) l' <;> intro hl
    · simpa using hZm.1.2.2 i i' fun e => hl (by rw [e])
    · simpa using hcross i k'
    · simpa using (hcross i' k).symm
    · simpa using hYm.1.2.2 k k' fun e => hl (by rw [e])
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) l
    · simpa using hZm.2 i
    · simpa using hYm.2 k
end AxisReflection
section Tensors
theorem conjReflectTest_linComb {q n : ℕ} (μ : Fin 4) (c : ℝ) (a : Fin n → ℂ)
    (X : Fin n → FnTuple (q + 1)) :
    conjReflectTest μ c (linComb a fun b => realTupleTensor (X b)) =
      linComb (fun b => conj (a b)) fun b => realTupleTensor
        (BallPeriodization.tupleComp (X b) (BallPeriodization.hyperplaneReflection μ c)) := by
  funext x
  change conj (∑ b, a b * ∏ l, ((X b l (axisRefl μ c (x l)) : ℝ) : ℂ)) =
    ∑ b, conj (a b) * ∏ l, ((X b l (axisRefl μ c (x l)) : ℝ) : ℂ)
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, map_prod]
  simp only [Complex.conj_ofReal]
theorem realTupleTensor_append {p q : ℕ} (Z : FnTuple (p + 1)) (W : FnTuple (q + 1)) :
    realTupleTensor (q := p + 1 + q + 1) (Fin.append Z W : FnTuple (p + 1 + (q + 1))) =
      tensor (p := p + 1) (q := q + 1) (realTupleTensor Z) (realTupleTensor W) := by
  change prodTensor (fun l x =>
      (((Fin.append Z W : FnTuple (p + 1 + (q + 1))) l x : ℝ) : ℂ)) =
    tensor (prodTensor fun l x => ((Z l x : ℝ) : ℂ))
      (prodTensor fun l x => ((W l x : ℝ) : ℂ))
  rw [tensor_prodTensor]
  congr 1
  funext l
  refine Fin.addCases (fun i => ?_) (fun k => ?_) l
  · simp
  · simp
theorem mem_lipTuplesBall_zero (ρ : ℝ) (X : FnTuple 0) : X ∈ lipTuplesBall 0 ρ :=
  ⟨(BallTuples.isSepLipschitz_zero X).1, fun l => l.elim0⟩
theorem gradedTensor_isBallTupleCombination {ρ : ℝ} {μ : Fin 4} {c : ℝ} {a b : ℕ}
    {A : OrderedTestFun a} {B : OrderedTestFun b} (hA : IsHalfSpaceCombination ρ μ c a A)
    (hB : IsHalfSpaceCombination ρ μ c b B) :
    IsBallTupleCombination ρ (gradedTensor ⟨a, conjReflectTest μ c A⟩ ⟨b, B⟩) := by
  cases a with
  | zero =>
    cases b with
    | zero =>
      refine ⟨1, fun _ => conj (A : ℂ) * (B : ℂ), fun _ l => l.elim0,
        fun _ => mem_lipTuplesBall_zero ρ _, ?_⟩
      change conj (A : ℂ) * (B : ℂ) = ∑ _ : Fin 1, conj (A : ℂ) * (B : ℂ) * (1 : ℂ)
      simp
    | succ b =>
      obtain ⟨n, a', Y, hY, hE, rfl⟩ := hB
      refine ⟨n, fun i => conj (A : ℂ) * a' i, Y, fun i => mem_lipTuplesBall (hY i) (hE i), ?_⟩
      funext x
      change conj (A : ℂ) * ∑ i, a' i * realTupleTensor (Y i) x =
        ∑ i, conj (A : ℂ) * a' i * realTupleTensor (Y i) x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  | succ a =>
    obtain ⟨n, a', X, hX, hE, rfl⟩ := hA
    cases b with
    | zero =>
      refine ⟨n, fun i => (B : ℂ) * conj (a' i), fun i => BallPeriodization.tupleComp (X i)
        (BallPeriodization.hyperplaneReflection μ c), fun i => tupleComp_mem (hX i) (hE i), ?_⟩
      change (fun x => (B : ℂ) * conjReflectTest μ c
        (linComb a' fun b => realTupleTensor (X b)) x) = _
      rw [conjReflectTest_linComb]
      funext x
      change (B : ℂ) * ∑ i, conj (a' i) * realTupleTensor (q := a + 1)
          (BallPeriodization.tupleComp (X i) (BallPeriodization.hyperplaneReflection μ c)) x =
        ∑ i, (B : ℂ) * conj (a' i) * realTupleTensor (q := a + 1)
          (BallPeriodization.tupleComp (X i) (BallPeriodization.hyperplaneReflection μ c)) x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
    | succ b =>
      obtain ⟨m, a'', Y, hY, hE', rfl⟩ := hB
      let e := (finProdFinEquiv (m := n) (n := m)).symm
      refine ⟨n * m, fun i => conj (a' (e i).1) * a'' (e i).2, fun i => Fin.append
        (BallPeriodization.tupleComp (X (e i).1) (BallPeriodization.hyperplaneReflection μ c))
        (Y (e i).2), fun i => append_mem (hX _) (hE _) (hY _) (hE' _), ?_⟩
      change tensor (p := a + 1) (q := b + 1) (conjReflectTest μ c
        (linComb a' fun b => realTupleTensor (X b)))
          (linComb a'' fun b => realTupleTensor (Y b)) = _
      rw [conjReflectTest_linComb]
      funext x
      let Z : Fin n → FnTuple (a + 1) := fun i =>
        BallPeriodization.tupleComp (X i) (BallPeriodization.hyperplaneReflection μ c)
      change (∑ i, conj (a' i) * realTupleTensor (q := a + 1) (Z i) (initPoints x)) *
          (∑ k, a'' k * realTupleTensor (Y k) (tailPoints x)) =
        ∑ i, conj (a' (e i).1) * a'' (e i).2 *
          realTupleTensor (q := a + 1 + b + 1)
            (Fin.append (Z (e i).1) (Y (e i).2) : FnTuple (a + 1 + (b + 1))) x
      rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
      refine (Fintype.sum_equiv e _ _ fun i => ?_).symm
      rw [realTupleTensor_append]
      change _ * (realTupleTensor (q := a + 1) (Z (e i).1) (initPoints x) *
        realTupleTensor (Y (e i).2) (tailPoints x)) = _
      ring
end Tensors
section HalfSpace
variable {D : MomentData}
abbrev withDir (D : MomentData) (μ : Fin 4) : ReflectionPositivity.CutoffMirrors.MirrorData :=
  { D.atCutoff with dir := μ }
variable {μ : Fin 4}
theorem refl_eq_torusMap (C : ReflectionPositivity.CutoffMirrors.LinkLevel (withDir D μ)) :
    C.refl = BallPeriodization.torusMap D.toParams
      (BallPeriodization.hyperplaneReflection μ C.pos) := by
  funext u
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective D.side u
  have h₁ := congrFun ((withDir D μ).induces_reflect C.pos) x
  have h₂ := congrFun (BallPeriodization.torusMap_comp_torusProj D.toParams
    (BallPeriodization.hyperplaneReflection μ C.pos)) x
  have h₃ := BallPeriodization.reflectVec_eq_hyperplaneReflection (withDir D μ) C.pos x
  simp only [Function.comp_apply] at h₁ h₂
  rw [h₃] at h₁
  exact h₁.trans h₂.symm
theorem IsHalfSpaceComponent.periodizable {ρ c : ℝ} {f : R4Fun} (hρ : D.IsRadius ρ)
    (hc : IsCompact (fnSupport f)) (hE : IsHalfSpaceComponent ρ μ c f) :
    IsPeriodizableInBall D.toParams ρ f :=
  ⟨hρ.1, hρ.2, hc, hE.1.trans inter_subset_left⟩
theorem IsHalfSpaceComponent.periodizable_axisRefl {ρ c : ℝ} {f : R4Fun} (hρ : D.IsRadius ρ)
    (hc : IsCompact (fnSupport f)) (hE : IsHalfSpaceComponent ρ μ c f) :
    IsPeriodizableInBall D.toParams ρ (f ∘ axisRefl μ c) :=
  ⟨hρ.1, hρ.2, isCompact_fnSupport_comp_axisRefl μ c hc, hE.2⟩
theorem supp_subset_openSlab (hT : PeriodizationThroughBall.PeriodizationLemma) {ρ : ℝ}
    (hρ : D.IsRadius ρ) (C : ReflectionPositivity.CutoffMirrors.LinkLevel (withDir D μ))
    {f : R4Fun} (hc : IsCompact (fnSupport f)) (hE : IsHalfSpaceComponent ρ μ C.pos f) :
    (withDir D μ).supp (TestFunctions.periodize D.side f) ⊆ C.openSlab .pos := by
  have hf := hE.periodizable (D := D) hρ hc
  have hs := (((hT D.toParams ρ hρ.1 hρ.2).2.1 ℝ).2.2.2.1 f hf).1
  intro u hu
  have hu' : u ∈ TorusMetric.torusProj D.side '' fnSupport f := hs ▸ hu
  obtain ⟨x, hx, rfl⟩ := hu'
  have hxc : C.pos < x μ := (hE.1 hx).2
  have hxb : TorusMetric.euclidNormVec x < ρ := (hE.1 hx).1
  have hrx : axisRefl μ C.pos x ∈ fnSupport (f ∘ axisRefl μ C.pos) := by
    rw [fnSupport_comp_axisRefl, mem_preimage, axisRefl_axisRefl]
    exact hx
  have hrb : TorusMetric.euclidNormVec (axisRefl μ C.pos x) < ρ := hE.2 hrx
  have a₁ := abs_le_euclidNormVec x μ
  have a₂ := abs_le_euclidNormVec (axisRefl μ C.pos x) μ
  rw [axisRefl_apply_self] at a₂
  have two := hf.two_mul_le
  have b₁ := abs_lt.1 (lt_of_le_of_lt a₁ hxb)
  have b₂ := abs_lt.1 (lt_of_le_of_lt a₂ hrb)
  refine ⟨x, ⟨?_, ?_⟩, rfl⟩
  · change 0 < 1 * (x μ - C.pos)
    linarith
  · change 1 * (x μ - C.pos) < D.side / 2
    linarith
theorem reflectFn_periodize (hT : PeriodizationThroughBall.PeriodizationLemma) {ρ : ℝ}
    (hρ : D.IsRadius ρ) (C : ReflectionPositivity.CutoffMirrors.LinkLevel (withDir D μ))
    {f : R4Fun} (hc : IsCompact (fnSupport f)) (hE : IsHalfSpaceComponent ρ μ C.pos f) :
    C.reflectFn (TestFunctions.periodize D.side f) =
      TestFunctions.periodize D.side (f ∘ axisRefl μ C.pos) := by
  rw [ReflectionPositivity.CutoffMirrors.LinkLevel.reflectFn, refl_eq_torusMap]
  exact (((hT D.toParams ρ hρ.1 hρ.2).2.1 ℝ).2.2.2.2.2 f
    (BallPeriodization.hyperplaneReflection μ C.pos) (hE.periodizable hρ hc)
      (hE.periodizable_axisRefl hρ hc)).symm
theorem centredObservable_halfAlgebra
    (hS : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hT : PeriodizationThroughBall.PeriodizationLemma)
    (hO : ReflectionPositivity.CutoffMirrors.OneSideObservables.HalfSpaceObservables) {ρ : ℝ}
    (hρ : D.IsRadius ρ) (C : ReflectionPositivity.CutoffMirrors.LinkLevel (withDir D μ))
    {f : R4Fun} (hl : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f)
    (hc : IsCompact (fnSupport f)) (hE : IsHalfSpaceComponent ρ μ C.pos f) :
    (fun U : (withDir D μ).FieldSpace =>
      ((D.atCutoff.centredObservable (TestFunctions.periodize D.side f) U.1 : ℝ) : ℂ)) ∈
        C.halfAlgebra .pos ∧
    ∀ U : (withDir D μ).FieldSpace,
      D.atCutoff.centredObservable (TestFunctions.periodize D.side f) (C.reflectField U).1 =
        D.atCutoff.centredObservable (TestFunctions.periodize D.side (f ∘ axisRefl μ C.pos))
          U.1 := by
  have hf := hE.periodizable (D := D) hρ hc
  have hLip := (((hT D.toParams ρ hρ.1 hρ.2).2.1 ℝ).2.2.1 f hf hl).1
  have hb := ((hS (cutoffParams D) D.β D.β_pos).2.2.1.2.1 _ hLip).1
  obtain ⟨-, -, hal, him⟩ := (hO _ C).1 (TestFunctions.periodize D.side f) hb
    (supp_subset_openSlab hT hρ C hc hE)
  refine ⟨hal.2, fun U => ?_⟩
  have h := him.2.2.2 U
  rw [reflectFn_periodize hT hρ C hc hE] at h
  exact h
theorem sum_mem_of {Ω ι : Type*} {𝔄 : Set (Ω → ℂ)} (h₀ : (fun _ => 0) ∈ 𝔄)
    (hadd : ∀ F ∈ 𝔄, ∀ F' ∈ 𝔄, F + F' ∈ 𝔄) (s : Finset ι) {G : ι → Ω → ℂ}
    (hG : ∀ i ∈ s, G i ∈ 𝔄) : (fun U => ∑ i ∈ s, G i U) ∈ 𝔄 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h₀
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact hadd _ (hG a (Finset.mem_insert_self _ _)) _
      (ih fun i hi => hG i (Finset.mem_insert_of_mem hi))
theorem prod_mem_of {Ω ι : Type*} {𝔄 : Set (Ω → ℂ)} (h₁ : (fun _ => 1) ∈ 𝔄)
    (hmul : ∀ F ∈ 𝔄, ∀ F' ∈ 𝔄, F * F' ∈ 𝔄) (s : Finset ι) {G : ι → Ω → ℂ}
    (hG : ∀ i ∈ s, G i ∈ 𝔄) : (fun U => ∏ i ∈ s, G i U) ∈ 𝔄 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h₁
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact hmul _ (hG a (Finset.mem_insert_self _ _)) _
      (ih fun i hi => hG i (Finset.mem_insert_of_mem hi))
section HalfSpaceAlgebra
variable (hS : LatticeProbability.ProbabilitySpaceTheorem.claim)
  (hT : PeriodizationThroughBall.PeriodizationLemma)
  (hO : ReflectionPositivity.CutoffMirrors.OneSideObservables.HalfSpaceObservables)
  (hDb : ReflectionPositivity.CutoffMirrors.DoubledTransversal.DoublingProperties)
  {ρ : ℝ} (hρ : D.IsRadius ρ) (C : ReflectionPositivity.CutoffMirrors.LinkLevel (withDir D μ))
include hS hT hO hDb hρ in
theorem tensorObservable_mem_halfAlgebra {q : ℕ} {A : OrderedTestFun q}
    (hA : IsHalfSpaceCombination ρ μ C.pos q A) :
    (fun U : (withDir D μ).FieldSpace => D.tensorObservable ρ A U.1) ∈
      C.halfAlgebra .pos := by
  obtain ⟨-, hconst, hadd, hsmul, hmul, -⟩ := ((hDb _ C).2.2.1 .pos).2.1
  cases q with
  | zero => exact hconst A
  | succ q =>
    obtain ⟨n, a, X, hX, hE, rfl⟩ := hA
    have e : (fun U : (withDir D μ).FieldSpace => D.tensorObservable ρ
        (linComb a fun b => realTupleTensor (X b)) U.1) = fun U => ∑ b, (a b • fun U :
          (withDir D μ).FieldSpace => ∏ l,
            ((D.atCutoff.centredObservable (TestFunctions.periodize D.side (X b l)) U.1 : ℝ) :
              ℂ)) U := by
      funext U
      rw [tensorObservable_linComb hS]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [tensorObservable_realTuple hS (X b) fun l =>
        (hE b l).periodizable hρ ((hX b).2.1 l)]
      rfl
    rw [e]
    refine sum_mem_of (hconst 0) hadd _ fun b _ => hsmul _ _ ?_
    exact prod_mem_of (hconst 1) hmul _ fun l _ =>
      (centredObservable_halfAlgebra hS hT hO hρ C ((hX b).1 l) ((hX b).2.1 l) (hE b l)).1
include hS hT hO hρ in
theorem conj_tensorObservable_reflectField {q : ℕ} {A : OrderedTestFun q}
    (hA : IsHalfSpaceCombination ρ μ C.pos q A) (U : (withDir D μ).FieldSpace) :
    conj (D.tensorObservable ρ A (C.reflectField U).1) =
      D.tensorObservable ρ (conjReflectTest μ C.pos A) U.1 := by
  cases q with
  | zero => rfl
  | succ q =>
    obtain ⟨n, a, X, hX, hE, rfl⟩ := hA
    rw [conjReflectTest_linComb, tensorObservable_linComb hS, tensorObservable_linComb hS,
      map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, tensorObservable_realTuple hS (X b) fun l =>
        (hE b l).periodizable hρ ((hX b).2.1 l),
      tensorObservable_realTuple hS (BallPeriodization.tupleComp (X b)
        (BallPeriodization.hyperplaneReflection μ C.pos)) fun l =>
        (hE b l).periodizable_axisRefl hρ ((hX b).2.1 l), map_prod]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Complex.conj_ofReal,
      (centredObservable_halfAlgebra hS hT hO hρ C ((hX b).1 l) ((hX b).2.1 l) (hE b l)).2 U]
    rfl
end HalfSpaceAlgebra
end HalfSpace
section Positivity
variable {D : MomentData}
open scoped ComplexOrder in
theorem reflectionPositivity
    (hS : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hT : PeriodizationThroughBall.PeriodizationLemma)
    (hO : ReflectionPositivity.CutoffMirrors.OneSideObservables.HalfSpaceObservables)
    (hDb : ReflectionPositivity.CutoffMirrors.DoubledTransversal.DoublingProperties)
    (hR : ReflectionPositivity.CutoffMirrors.LinkReflection.LinkReflectionProperties)
    (hP : ReflectionPositivity.CutoffMirrors.LinkPositivity.ReflectionPositivityAtLink)
    (ρ : ℝ) (hρ : D.IsRadius ρ) : ReflectionPositivity D ρ := by
  intro μ c hc q₀ F F' hF hF'
  let C : ReflectionPositivity.CutoffMirrors.LinkLevel (withDir D μ) := ⟨c, hc⟩
  obtain ⟨-, s, hsθ, -⟩ := hR _ C
  have hind : D.IsReflectionSymmetry μ c s := hsθ.trans (refl_eq_torusMap C)
  have h : D.ReflectionIsSymmetry μ c := ⟨s, hind⟩
  have hiso : h.toSymmetry.toFun = C.refl :=
    (h.choose_spec.trans hind.symm).trans hsθ
  have hpull : ∀ U : Field D,
      ReflectionPositivity.CutoffMirrors.MirrorData.Symmetry.pullback h.toSymmetry U.1 =
        (C.reflectField U).1 := fun U =>
    (C.reflectField_val h.toSymmetry hiso U).symm
  have hconj : ∀ (G : TestSeq q₀), (∀ q : Fin (q₀ + 1),
      IsHalfSpaceCombination ρ μ c q (G q)) → ∀ U : Field D,
      conj (D.compPullback h.toSymmetry (seqObservable D ρ G) U.1) =
        ∑ q, D.tensorObservable ρ (conjReflectSeq μ c G q) U.1 := by
    intro G hG U
    rw [MomentData.compPullback, hpull, seqObservable, map_sum]
    exact Finset.sum_congr rfl fun q _ =>
      conj_tensorObservable_reflectField hS hT hO hρ C (hG q) U
  have hterm : ∀ G G' : TestSeq q₀, (∀ q : Fin (q₀ + 1),
      IsHalfSpaceCombination ρ μ c q (G q)) → ∀ U : Field D,
      (fun U => ∑ q, ∑ q', D.tensorObservable ρ (reflectedTensorProd μ c G G' q q').2 U) U.1 =
        (fun U => conj (D.compPullback h.toSymmetry (seqObservable D ρ G) U) *
          seqObservable D ρ G' U) U.1 := by
    intro G G' hG U
    change _ = conj (D.compPullback h.toSymmetry (seqObservable D ρ G) U.1) *
      seqObservable D ρ G' U.1
    rw [hconj G hG U, seqObservable, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
    exact (tensorObservable_mul (finite_plaquette hS) ρ _ _ _).symm
  have hnice : ∀ G G' : TestSeq q₀, IsBoundedObs D fun U => ∑ q, ∑ q',
      D.tensorObservable ρ (reflectedTensorProd μ c G G' q q').2 U := fun G G' =>
    isBoundedObs_sum _ fun q _ => isBoundedObs_sum _ fun q' _ =>
      isBoundedObs_tensorObservable hS ρ _
  have hpair : ∀ G G' : TestSeq q₀, (∀ q : Fin (q₀ + 1),
      IsHalfSpaceCombination ρ μ c q (G q)) → reflectionPairing D ρ h G G' =
        ∑ q, ∑ q', D.centredTensorMoment ρ (reflectedTensorProd μ c G G' q q').2 := by
    intro G G' hG
    rw [reflectionPairing, ← expectation_congr hS (hnice G G') (hterm G G' hG),
      expectation_sum hS _ fun q _ => isBoundedObs_sum _ fun q' _ =>
        isBoundedObs_tensorObservable hS ρ _]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [expectation_sum hS _ fun q' _ => isBoundedObs_tensorObservable hS ρ _]
    rfl
  have hform : reflectionPairing D ρ h F F = C.thetaForm
      (fun U => seqObservable D ρ F U.1) (fun U => seqObservable D ρ F U.1) := by
    rw [reflectionPairing, ← expectation_congr hS (hnice F F) (hterm F F hF)]
    unfold ReflectionPositivity.CutoffMirrors.LinkLevel.thetaForm
      ReflectionPositivity.CutoffMirrors.MirrorData.fieldExpectation
    refine expectation_congr hS (hnice F F) fun U => ?_
    rw [dif_pos U.2]
    refine (hterm F F hF U).trans ?_
    change conj (D.compPullback h.toSymmetry (seqObservable D ρ F) U.1) *
      seqObservable D ρ F U.1 = _
    rw [MomentData.compPullback, hpull]
  have hmem : (fun U : (withDir D μ).FieldSpace => seqObservable D ρ F U.1) ∈
      C.halfAlgebra .pos := by
    obtain ⟨-, hconst, hadd, -, -, -⟩ := ((hDb _ C).2.2.1 .pos).2.1
    exact sum_mem_of (hconst 0) hadd _ fun q _ =>
      tensorObservable_mem_halfAlgebra hS hT hO hDb hρ C (hF q)
  have hpos : 0 ≤ reflectionPairing D ρ h F F := by
    rw [hform]
    exact (hP _ C).2.1.2.2.1 _ hmem
  obtain ⟨h₁, h₂⟩ := Complex.le_def.1 hpos
  exact ⟨h, fun q q' => gradedTensor_isBallTupleCombination (hF q) (hF' q'), hpair F F' hF,
    h₂.symm, h₁⟩
theorem statement_holds
    (hS : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hG : Cumulants.BoundedVariables.BoundedGeneratingFunctionTheorem)
    (hMom : Cumulants.MomentsViaCumulants)
    (hMul : BallTuples.ConnectedMultilinearity.Statement)
    (hT : PeriodizationThroughBall.PeriodizationLemma)
    (hI : ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance)
    (hC : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (hO : ReflectionPositivity.CutoffMirrors.OneSideObservables.HalfSpaceObservables)
    (hDb : ReflectionPositivity.CutoffMirrors.DoubledTransversal.DoublingProperties)
    (hR : ReflectionPositivity.CutoffMirrors.LinkReflection.LinkReflectionProperties)
    (hP : ReflectionPositivity.CutoffMirrors.LinkPositivity.ReflectionPositivityAtLink) :
    Statement := fun _ ρ hρ =>
  ⟨fun n hn => connectedProperties hS hG hMul ρ hρ n hn, momentPartitionExpansion hS hMom ρ,
    tensorObservableCalculus hS hT ρ hρ, fun n hn => connectedInvariance hT hI hC ρ hρ n hn,
    reflectionPositivity hS hT hO hDb hR hP ρ hρ⟩
end Positivity
end TorusFunctionals
end YangMills.Construction.CentredTensorMoments
end

import YangMills.Construction.Cumulants.JointCumulantThroughMoments
import YangMills.Construction.HullsInEveryVolume.TheTwoWilsonLawsAgree
import YangMills.Construction.HullsInEveryVolume.TwoPointLawDefs
import YangMills.Construction.HullsInEveryVolume.LimitDefs
import YangMills.Construction.LawByMomentsOfTheFlow.ComponentsOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
import YangMills.Construction.LawByMomentsOfTheFlow.LawOnEveryTorus
import YangMills.Construction.QuaternionicWilsonModel.TheQuaternionModelIsSUTwoWithWilsonsWeightProof
import YangMills.Construction.RunningCouplingSlope.LimitOfAChainFormKillsClosedFormsProof
set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open WeightedResponses TorusFields
def limitPointCumulantStatement : Prop :=
  ForAllHullPoints fun Λ C _ _ S =>
    ‖(S.scaleCoupling : ℂ) ^ Λ.k * S.torusCumulant - (S.latticeCycleSumAt S.data.scaleLevel : ℂ)‖ ≤
      C 0 * S.scaleCoupling ^ (-(1 / 10) : ℝ) ∧
    ∀ ν : Measure (InfiniteLattice.RefinedGaugeField Λ.stepParams.side S.data.windowLevel),
      (∃ ms, TorusLimits.IsTorusLimitAlong Λ.stepParams.side S.data.windowLevel S.β ν ms) →
      ‖(S.scaleCoupling : ℂ) ^ Λ.k * S.stateUrsell ν - (S.latticeCycleSumAt S.data.scaleLevel : ℂ)‖ ≤
        C 0 * S.scaleCoupling ^ (-(1 / 10) : ℝ)
end YangMills.Construction.MomentLaw
end

noncomputable section
open MeasureTheory Filter
open scoped Topology Quaternion
namespace YangMills.Construction
namespace WindowRestrictions
open TorusFields WeightedResponses BlockAverages TorusLimits TwoPointLaw Matrices
private def plaquetteProductOf (w : (Fin 4 → ℤ) × Fin 4 → ComplexMatrix2) (P : OrientedPlaquette) : ComplexMatrix2 :=
  w (P.1.1, P.1.2.1) * w (P.1.1 + Pi.single P.1.2.1 1, P.1.2.2) *
    (w (P.1.1 + Pi.single P.1.2.2 1, P.1.2.1)).conjTranspose * (w (P.1.1, P.1.2.2)).conjTranspose
private def halfTraceEnergy (M : ComplexMatrix2) : ℝ := 1 - (1 / 2) * (ComplexMatrix2.fullTrace M).re
open Classical in
private def extendByOne {R : ℕ} (v : WindowValuation R) (b : (Fin 4 → ℤ) × Fin 4) : ComplexMatrix2 :=
  if h : TorusFields.BondOffsetInBox R b then v ⟨b, h⟩ else 1
private def windowEnergySum {R : ℕ} (E : Finset OrientedPlaquette) (c : OrientedPlaquette → ℝ) (v : WindowValuation R) : ℝ :=
  ∑ P ∈ E, c P * halfTraceEnergy (plaquetteProductOf (extendByOne v) P)
private def specialUnitaryValues (R : ℕ) : Set (WindowValuation R) := {v | ∀ b, v b ∈ ComplexMatrix2.specialUnitary}
private def windowEnergyObservable {R : ℕ} (E : Finset OrientedPlaquette) (c : OrientedPlaquette → ℝ) : WindowValuation R → ℝ :=
  (specialUnitaryValues R).indicator (windowEnergySum E c)
private theorem continuous_halfTraceEnergy : Continuous halfTraceEnergy := by
  unfold halfTraceEnergy
  have h : Continuous fun M : ComplexMatrix2 => ComplexMatrix2.fullTrace M := continuous_id.matrix_trace
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp h))
private theorem continuous_plaquetteProductOf {X : Type*} [TopologicalSpace X] {w : X → (Fin 4 → ℤ) × Fin 4 → ComplexMatrix2}
    (hw : ∀ b, Continuous fun x => w x b) (P : OrientedPlaquette) : Continuous fun x => plaquetteProductOf (w x) P := by
  unfold plaquetteProductOf
  exact (((hw _).matrix_mul (hw _)).matrix_mul (hw _).matrix_conjTranspose).matrix_mul (hw _).matrix_conjTranspose
private theorem continuous_windowEnergySum {R : ℕ} (E : Finset OrientedPlaquette) (c : OrientedPlaquette → ℝ) :
    Continuous (windowEnergySum (R := R) E c) := by
  unfold windowEnergySum
  refine continuous_finsetSum _ fun P _ =>
    continuous_const.mul (continuous_halfTraceEnergy.comp (continuous_plaquetteProductOf (fun b => ?_) P))
  by_cases h : TorusFields.BondOffsetInBox R b
  · simp only [extendByOne, dif_pos h]
    exact continuous_apply _
  · simp only [extendByOne, dif_neg h]
    exact continuous_const
private theorem isClosed_specialUnitary : IsClosed (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by
  have h : (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) =
      {A : ComplexMatrix2 | A * star A = 1} ∩ {A : ComplexMatrix2 | A.det = 1} := by
    ext A
    simp only [SetLike.mem_coe, Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
  rw [h]
  refine (isClosed_eq ?_ continuous_const).inter (isClosed_eq ?_ continuous_const)
  · exact continuous_id.matrix_mul continuous_id.matrix_conjTranspose
  · exact continuous_id.matrix_det
private theorem isClosed_specialUnitaryValues (R : ℕ) : IsClosed (specialUnitaryValues R) := by
  have h : specialUnitaryValues R =
      ⋂ b, (fun v : WindowValuation R => v b) ⁻¹' (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by
    ext v
    simp [specialUnitaryValues]
  rw [h]
  exact isClosed_iInter fun b => isClosed_specialUnitary.preimage (continuous_apply b)
private theorem abs_halfTraceEnergy_le {M : ComplexMatrix2} (hM : M ∈ ComplexMatrix2.specialUnitary) :
    |halfTraceEnergy M| ≤ 2 := by
  have hU := (Matrix.mem_specialUnitaryGroup_iff.mp hM).1
  have h0 := entry_norm_bound_of_unitary hU 0 0
  have h1 := entry_norm_bound_of_unitary hU 1 1
  have ht : |(ComplexMatrix2.fullTrace M).re| ≤ 2 := by
    have h2 : ComplexMatrix2.fullTrace M = M 0 0 + M 1 1 := Matrix.trace_fin_two M
    rw [h2]
    calc |(M 0 0 + M 1 1).re| ≤ ‖M 0 0 + M 1 1‖ := Complex.abs_re_le_norm _
      _ ≤ ‖M 0 0‖ + ‖M 1 1‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  unfold halfTraceEnergy
  rw [abs_le] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]
private theorem conjTranspose_mem_specialUnitary {M : ComplexMatrix2} (h : M ∈ ComplexMatrix2.specialUnitary) :
    M.conjTranspose ∈ ComplexMatrix2.specialUnitary := by
  obtain ⟨h1, h2⟩ := Matrix.mem_specialUnitaryGroup_iff.mp h
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Unitary.star_mem h1, ?_⟩
  change (M.conjTranspose).det = 1
  rw [Matrix.det_conjTranspose, h2, star_one]
private theorem plaquetteProductOf_mem {w : (Fin 4 → ℤ) × Fin 4 → ComplexMatrix2}
    (hw : ∀ b, w b ∈ ComplexMatrix2.specialUnitary) (P : OrientedPlaquette) :
    plaquetteProductOf w P ∈ ComplexMatrix2.specialUnitary :=
  ComplexMatrix2.specialUnitary.mul_mem
    (ComplexMatrix2.specialUnitary.mul_mem (ComplexMatrix2.specialUnitary.mul_mem (hw _) (hw _))
      (conjTranspose_mem_specialUnitary (hw _)))
    (conjTranspose_mem_specialUnitary (hw _))
private theorem extendByOne_mem {R : ℕ} {v : WindowValuation R} (hv : v ∈ specialUnitaryValues R)
    (b : (Fin 4 → ℤ) × Fin 4) : extendByOne v b ∈ ComplexMatrix2.specialUnitary := by
  by_cases h : TorusFields.BondOffsetInBox R b
  · simp only [extendByOne, dif_pos h]
    exact hv _
  · simp only [extendByOne, dif_neg h]
    exact ComplexMatrix2.specialUnitary.one_mem
private theorem isBounded_windowEnergyObservable {R : ℕ} (E : Finset OrientedPlaquette) (c : OrientedPlaquette → ℝ) :
    IsBoundedWindowObservable (windowEnergyObservable (R := R) E c) := by
  refine ⟨?_, ∑ P ∈ E, |c P| * 2, fun v => ?_⟩
  · letI : MeasurableSpace (WindowValuation R) := borel _
    haveI : BorelSpace (WindowValuation R) := ⟨rfl⟩
    exact (continuous_windowEnergySum E c).measurable.indicator (isClosed_specialUnitaryValues R).measurableSet
  · unfold windowEnergyObservable
    by_cases hv : v ∈ specialUnitaryValues R
    · rw [Set.indicator_of_mem hv]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun P _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_halfTraceEnergy_le (plaquetteProductOf_mem (extendByOne_mem hv) P)) (abs_nonneg _)
    · rw [Set.indicator_of_notMem hv, abs_zero]
      exact Finset.sum_nonneg fun P _ => by positivity
private theorem abs_piSingle_le (κ i : Fin 4) : |(Pi.single κ (1 : ℤ) : Fin 4 → ℤ) i| ≤ 1 := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.abs_single_one_le <;> assumption
private theorem bondOffsetInBox_add {R : ℕ} {n d : Fin 4 → ℤ} (κ : Fin 4) (hn : TorusFields.OffsetInBox R n)
    (hd : ∀ i, |d i| ≤ 1) : TorusFields.BondOffsetInBox (R + 2) (n + d, κ) := by
  constructor
  · intro i
    have a := abs_le.mp (hn i)
    have b := abs_le.mp (hd i)
    refine abs_le.mpr ?_
    simp only [Pi.add_apply]
    push_cast
    omega
  · intro i
    have a := abs_le.mp (hn i)
    have b := abs_le.mp (hd i)
    have c := abs_le.mp (abs_piSingle_le κ i)
    refine abs_le.mpr ?_
    simp only [Pi.add_apply]
    push_cast
    omega
private theorem plaquetteProductOf_extendByOne {R₀ : ℕ} (w : (Fin 4 → ℤ) × Fin 4 → ComplexMatrix2) {P : OrientedPlaquette}
    (hP : TorusFields.OffsetInBox R₀ P.1.1) :
    plaquetteProductOf (extendByOne (R := R₀ + 2) fun b => w b.1) P = plaquetteProductOf w P := by
  have h : ∀ (d : Fin 4 → ℤ) (κ : Fin 4), (∀ i, |d i| ≤ 1) →
      extendByOne (R := R₀ + 2) (fun b => w b.1) (P.1.1 + d, κ) = w (P.1.1 + d, κ) := by
    intro d κ hd
    simp only [extendByOne, dif_pos (bondOffsetInBox_add κ hP hd)]
  have h0 : ∀ κ : Fin 4, extendByOne (R := R₀ + 2) (fun b => w b.1) (P.1.1, κ) = w (P.1.1, κ) := by
    intro κ
    simpa using h 0 κ (by simp)
  unfold plaquetteProductOf
  rw [h0, h0, h _ _ (abs_piSingle_le _), h _ _ (abs_piSingle_le _)]
private theorem windowEnergyObservable_eq_sum {R₀ : ℕ} {E : Finset OrientedPlaquette} (c : OrientedPlaquette → ℝ)
    (hE : ∀ P ∈ E, TorusFields.OffsetInBox R₀ P.1.1) {w : (Fin 4 → ℤ) × Fin 4 → ComplexMatrix2}
    (hw : ∀ b, w b ∈ ComplexMatrix2.specialUnitary) :
    windowEnergyObservable (R := R₀ + 2) E c (fun b => w b.1) =
      ∑ P ∈ E, c P * halfTraceEnergy (plaquetteProductOf w P) := by
  unfold windowEnergyObservable
  rw [Set.indicator_of_mem
    (show (fun b : WindowLink (R₀ + 2) => w b.1) ∈ specialUnitaryValues (R₀ + 2) from fun b => hw b.1)]
  exact Finset.sum_congr rfl fun P hP => by rw [plaquetteProductOf_extendByOne w (hE P hP)]
private def linkMatrices {a : ℝ} (U : InfiniteLattice.GaugeField a) (b : (Fin 4 → ℤ) × Fin 4) : ComplexMatrix2 :=
  ((U (InfiniteLattice.Link.forwardFrom (latticePointOfInt a b.1) b.2) : ComplexMatrix2.specialUnitary) : ComplexMatrix2)
private def toElementaryPlaquette (a : ℝ) (P : OrientedPlaquette) : InfiniteLattice.ElementaryPlaquette a :=
  ⟨latticePointOfInt a P.1.1, P.1.2.1, P.1.2.2, P.2⟩
private theorem latticePointOfInt_add_axisStep (a : ℝ) (n : Fin 4 → ℤ) (μ : Fin 4) :
    latticePointOfInt a n + InfiniteLattice.axisStep a μ = latticePointOfInt a (n + Pi.single μ 1) := by
  apply Subtype.ext
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [latticePointOfInt, InfiniteLattice.axisStep, add_mul]
  · simp [latticePointOfInt, InfiniteLattice.axisStep, Pi.single_eq_of_ne h]
abbrev _root_.YangMills.SharedProofs.p61591 := @latticePointOfInt_add_axisStep
private theorem coe_inv_eq_conjTranspose (x : ComplexMatrix2.specialUnitary) :
    ((x⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) = (x : ComplexMatrix2).conjTranspose := by
  rw [InfiniteLattice.specialUnitary_coe_inv]
  exact Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp x.2).1)
abbrev _root_.YangMills.SharedProofs.p1210 := @coe_inv_eq_conjTranspose
private theorem faceEnergy_toElementaryPlaquette {a : ℝ} (U : InfiniteLattice.GaugeField a) (P : OrientedPlaquette) :
    InfiniteLattice.faceEnergy U (toElementaryPlaquette a P) = halfTraceEnergy (plaquetteProductOf (linkMatrices U) P) := by
  have h : ((InfiniteLattice.faceHolonomy U (toElementaryPlaquette a P) : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      plaquetteProductOf (linkMatrices U) P := by
    simp only [InfiniteLattice.faceHolonomy, toElementaryPlaquette, plaquetteProductOf, linkMatrices,
      latticePointOfInt_add_axisStep, Submonoid.coe_mul, coe_inv_eq_conjTranspose]
  rw [InfiniteLattice.faceEnergy, h]
  rfl
private theorem continuous_linkMatrices {a : ℝ} (b : (Fin 4 → ℤ) × Fin 4) :
    Continuous fun U : InfiniteLattice.GaugeField a => linkMatrices U b := by
  unfold linkMatrices
  exact continuous_subtype_val.comp ((continuous_apply _).comp continuous_subtype_val)
private theorem plaquetteBarycenter_bounds (P : OrientedPlaquette) (i : Fin 4) :
    (P.1.1 i : ℝ) ≤ plaquetteBarycenter P i ∧ plaquetteBarycenter P i ≤ (P.1.1 i : ℝ) + 1 := by
  unfold plaquetteBarycenter
  split_ifs <;> constructor <;> linarith
private theorem finite_setOf_offsetInBox (R : ℕ) :
    {P : OrientedPlaquette | TorusFields.OffsetInBox R P.1.1}.Finite := by
  have h1 : {n : Fin 4 → ℤ | TorusFields.OffsetInBox R n}.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin 4 => Set.Icc (-(R : ℤ)) R) fun _ => Set.finite_Icc _ _).subset ?_
    intro n hn i _
    exact abs_le.mp (hn i)
  have h2 := h1.prod (Set.finite_univ (α := Fin 4 × Fin 4))
  exact (h2.preimage (Subtype.val_injective.injOn)).subset fun P hP => ⟨hP, trivial⟩
private def cubePlaquettes (R : ℕ) : Finset OrientedPlaquette := (finite_setOf_offsetInBox R).toFinset
private theorem mem_cubePlaquettes {R : ℕ} {P : OrientedPlaquette} :
    P ∈ cubePlaquettes R ↔ TorusFields.OffsetInBox R P.1.1 := by
  simp [cubePlaquettes]
private theorem bijective_toElementaryPlaquette {a : ℝ} (ha : a ≠ 0) :
    Function.Bijective (toElementaryPlaquette a) := by
  constructor
  · rintro ⟨⟨n, μ, ν⟩, h⟩ ⟨⟨n', μ', ν'⟩, h'⟩ e
    simp only [toElementaryPlaquette, InfiniteLattice.ElementaryPlaquette.mk.injEq] at e
    obtain ⟨e1, e2, e3⟩ := e
    subst e2 e3
    have hn : n = n' := by
      funext i
      have h3 := congrFun (congrArg Subtype.val e1) i
      simp only [latticePointOfInt] at h3
      exact_mod_cast mul_right_cancel₀ ha h3
    subst hn
    rfl
  · intro p
    obtain ⟨n, hn⟩ := p.corner.2
    refine ⟨⟨(n, p.lowAxis, p.highAxis), p.lowAxis_lt_highAxis⟩, ?_⟩
    apply InfiniteLattice.ElementaryPlaquette.ext
    · exact Subtype.ext (funext fun i => (hn i).symm)
    · rfl
    · rfl
private def torusLinkMatrices {N : ℕ} (W : TorusField N) (b : (Fin 4 → ℤ) × Fin 4) : ComplexMatrix2 :=
  SoftAverages.quaternionToMatrix ((W (siteOfInt b.1) b.2 : UnitQuaternion) : ℍ[ℝ])
private theorem quaternionToMatrix_star (q : ℍ[ℝ]) :
    SoftAverages.quaternionToMatrix (star q) = (SoftAverages.quaternionToMatrix q).conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SoftAverages.quaternionToMatrix, Matrix.conjTranspose_apply]
private theorem quaternionToMatrix_mem (q : UnitQuaternion) :
    SoftAverages.quaternionToMatrix (q : ℍ[ℝ]) ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.quaternionToMatrix_mem_specialUnitary <;> assumption
private theorem halfTraceEnergy_quaternionToMatrix (q : ℍ[ℝ]) :
    halfTraceEnergy (SoftAverages.quaternionToMatrix q) = 1 - q.re := by
  have h : ComplexMatrix2.fullTrace (SoftAverages.quaternionToMatrix q) = 2 * (q.re : ℂ) := by
    rw [ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
    simp only [SoftAverages.quaternionToMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  unfold halfTraceEnergy
  rw [h]
  simp
private theorem siteOfInt_add_piSingle {N : ℕ} (n : Fin 4 → ℤ) (μ : Fin 4) :
    (siteOfInt (n + Pi.single μ 1) : TorusSite N) = siteOfInt n + TorusFields.unitStep N μ := by apply _root_.YangMills.SharedProofs.p8359 <;> assumption
private theorem coe_inv_unitQuaternion (q : UnitQuaternion) : ((q⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (q : ℍ[ℝ]) := rfl
private theorem plaquetteProductOf_torus {N : ℕ} (W : TorusField N) (P : OrientedPlaquette) :
    plaquetteProductOf (torusLinkMatrices W) P =
      SoftAverages.quaternionToMatrix ((holonomy W (siteOfInt P.1.1) P.1.2.1 P.1.2.2 : UnitQuaternion) : ℍ[ℝ]) := by
  simp only [plaquetteProductOf, torusLinkMatrices, holonomy, siteOfInt_add_piSingle, Submonoid.coe_mul,
    coe_inv_unitQuaternion, SoftAverages.quaternionToMatrix_mul, quaternionToMatrix_star]
private theorem halfTraceEnergy_torus {N : ℕ} (W : TorusField N) (P : OrientedPlaquette) :
    halfTraceEnergy (plaquetteProductOf (torusLinkMatrices W) P) =
      plaquetteEnergy W (siteOfInt P.1.1) P.1.2.1 P.1.2.2 := by
  rw [plaquetteProductOf_torus, halfTraceEnergy_quaternionToMatrix]
  rfl
private theorem zmod_val_intCast_real {N : ℕ} [NeZero N] (z : ℤ) :
    (((z : ZMod N).val : ℕ) : ℝ) = (z : ℝ) - N * ((z / (N : ℤ) : ℤ) : ℝ) := by
  have h : (((z : ZMod N).val : ℕ) : ℤ) = z - N * (z / (N : ℤ)) := by
    rw [ZMod.val_intCast, Int.emod_def]
  exact_mod_cast congrArg (fun k : ℤ => (k : ℝ)) h
private theorem isBoundedWindowObservable_prod {R : ℕ} {ι : Type} (J : Finset ι) {G : ι → WindowValuation R → ℝ}
    (h : ∀ j ∈ J, IsBoundedWindowObservable (G j)) : IsBoundedWindowObservable fun v => ∏ j ∈ J, G j v := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    refine ⟨?_, 1, fun v => by simp⟩
    letI : MeasurableSpace (WindowValuation R) := borel _
    simp only [Finset.prod_empty]
    exact measurable_const
  | insert j J hj ih =>
    have h₁ := h j (Finset.mem_insert_self j J)
    have h₂ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨C₁, hC₁⟩ := h₁.bounded
    obtain ⟨C₂, hC₂⟩ := h₂.bounded
    refine ⟨?_, C₁ * C₂, fun v => ?_⟩
    · letI : MeasurableSpace (WindowValuation R) := borel _
      have m₁ : Measurable (G j) := h₁.measurable
      have m₂ : Measurable fun v => ∏ i ∈ J, G i v := h₂.measurable
      simp only [Finset.prod_insert hj]
      exact m₁.mul m₂
    · simp only [Finset.prod_insert hj, abs_mul]
      exact mul_le_mul (hC₁ v) (hC₂ v) (abs_nonneg _) ((abs_nonneg _).trans (hC₁ v))
private theorem smearedEnergy_eq_sum {a : ℝ} (ha : a ≠ 0) (f : (Fin 4 → ℝ) → ℝ) {R₀ : ℕ}
    (hc : ∀ P, f (toElementaryPlaquette a P).center ≠ 0 → TorusFields.OffsetInBox R₀ P.1.1)
    (U : InfiniteLattice.GaugeField a) :
    InfiniteLattice.smearedEnergy f U =
      ∑ P ∈ cubePlaquettes R₀,
        f (toElementaryPlaquette a P).center * halfTraceEnergy (plaquetteProductOf (linkMatrices U) P) := by
  unfold InfiniteLattice.smearedEnergy
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (bijective_toElementaryPlaquette ha))]
  simp only [Equiv.ofBijective_apply]
  rw [finsum_eq_sum_of_support_subset]
  · refine Finset.sum_congr rfl fun P _ => ?_
    rw [faceEnergy_toElementaryPlaquette, smul_eq_mul, mul_comm]
  · intro P hP
    have hP' : InfiniteLattice.faceEnergy U (toElementaryPlaquette _ P) • f (toElementaryPlaquette _ P).center ≠ 0 := hP
    rw [smul_eq_mul] at hP'
    exact Finset.mem_coe.mpr (mem_cubePlaquettes.mpr (hc P (right_ne_zero_of_mul hP')))
private theorem smearedEnergy_eq_evalOnField {a : ℝ} (ha : a ≠ 0) (f : (Fin 4 → ℝ) → ℝ) {R₀ : ℕ}
    (hc : ∀ P, f (toElementaryPlaquette a P).center ≠ 0 → TorusFields.OffsetInBox R₀ P.1.1)
    (U : InfiniteLattice.GaugeField a) :
    InfiniteLattice.smearedEnergy f U =
      evalOnField (windowEnergyObservable (R := R₀ + 2) (cubePlaquettes R₀)
        fun P => f (toElementaryPlaquette a P).center) U :=
  (smearedEnergy_eq_sum ha f hc U).trans
    (windowEnergyObservable_eq_sum _ (fun _ hP => mem_cubePlaquettes.mp hP) (w := linkMatrices U)
      (fun _ => (U _).2)).symm
private theorem continuous_smearedEnergy {a : ℝ} (ha : a ≠ 0) (f : (Fin 4 → ℝ) → ℝ) {R₀ : ℕ}
    (hc : ∀ P, f (toElementaryPlaquette a P).center ≠ 0 → TorusFields.OffsetInBox R₀ P.1.1) :
    Continuous (InfiniteLattice.smearedEnergy f : InfiniteLattice.GaugeField a → ℝ) := by
  have h : (InfiniteLattice.smearedEnergy f : InfiniteLattice.GaugeField a → ℝ) = fun U =>
      ∑ P ∈ cubePlaquettes R₀,
        f (toElementaryPlaquette a P).center * halfTraceEnergy (plaquetteProductOf (linkMatrices U) P) :=
    funext (smearedEnergy_eq_sum ha f hc)
  rw [h]
  exact continuous_finsetSum _ fun P _ => continuous_const.mul
    (continuous_halfTraceEnergy.comp (continuous_plaquetteProductOf continuous_linkMatrices P))
private def plaquetteOnTorus (N : ℕ) (P : OrientedPlaquette) : TorusPlaquette N := (siteOfInt P.1.1, P.1.2.1, P.1.2.2)
private theorem curvatureObservable_eq_sum {N R₀ : ℕ} [NeZero N] (h : PlaquetteWeight N) (c : OrientedPlaquette → ℝ)
    (hN : 2 * R₀ < N) (hval : ∀ P ∈ cubePlaquettes R₀, h (plaquetteOnTorus N P) = c P)
    (hlift : ∀ p : TorusPlaquette N, p.2.1 < p.2.2 → h p ≠ 0 → ∃ P ∈ cubePlaquettes R₀, plaquetteOnTorus N P = p)
    (W : TorusField N) :
    curvatureObservable h W =
      ∑ P ∈ cubePlaquettes R₀, c P * halfTraceEnergy (plaquetteProductOf (torusLinkMatrices W) P) := by
  classical
  have hinj : Set.InjOn (plaquetteOnTorus N) (cubePlaquettes R₀ : Set OrientedPlaquette) := by
    intro P hP P' hP' e
    have hb := mem_cubePlaquettes.mp (Finset.mem_coe.mp hP)
    have hb' := mem_cubePlaquettes.mp (Finset.mem_coe.mp hP')
    simp only [plaquetteOnTorus, Prod.mk.injEq] at e
    obtain ⟨e1, e2, e3⟩ := e
    apply Subtype.ext
    refine Prod.ext ?_ (Prod.ext e2 e3)
    funext i
    have h1 : ((P.1.1 i : ℤ) : ZMod N) = ((P'.1.1 i : ℤ) : ZMod N) := congrFun e1 i
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
    have a := abs_le.mp (hb i)
    have a' := abs_le.mp (hb' i)
    have h3 : |P'.1.1 i - P.1.1 i| < (N : ℤ) := by
      refine abs_lt.mpr ⟨?_, ?_⟩ <;> omega
    have h4 := Int.eq_zero_of_abs_lt_dvd h2 h3
    omega
  have hsub : (cubePlaquettes R₀).image (plaquetteOnTorus N) ⊆ plaquettesIn Finset.univ := by
    intro p hp
    obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp hp
    simp [plaquettesIn, plaquetteOnTorus, P.2]
  have hzero : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)),
      p ∉ (cubePlaquettes R₀).image (plaquetteOnTorus N) → h p * plaquetteEnergyOf W p = 0 := by
    intro p hp hnot
    by_contra hne
    have hw : h p ≠ 0 := left_ne_zero_of_mul hne
    have hlt : p.2.1 < p.2.2 := by
      simp only [plaquettesIn, Finset.mem_filter] at hp
      exact hp.2.1
    obtain ⟨P, hP, e⟩ := hlift p hlt hw
    exact hnot (Finset.mem_image.mpr ⟨P, hP, e⟩)
  unfold curvatureObservable
  rw [← Finset.sum_subset hsub hzero, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [hval P hP, halfTraceEnergy_torus]
  rfl
private theorem curvatureObservable_eq_evalOnTorus {N R₀ : ℕ} [NeZero N] (h : PlaquetteWeight N)
    (c : OrientedPlaquette → ℝ) (hN : 2 * R₀ < N) (hval : ∀ P ∈ cubePlaquettes R₀, h (plaquetteOnTorus N P) = c P)
    (hlift : ∀ p : TorusPlaquette N, p.2.1 < p.2.2 → h p ≠ 0 → ∃ P ∈ cubePlaquettes R₀, plaquetteOnTorus N P = p)
    (W : TorusField N) :
    curvatureObservable h W = evalOnTorus (windowEnergyObservable (R := R₀ + 2) (cubePlaquettes R₀) c) W :=
  (curvatureObservable_eq_sum h c hN hval hlift W).trans
    (windowEnergyObservable_eq_sum c (fun _ hP => mem_cubePlaquettes.mp hP) (w := torusLinkMatrices W)
      (fun _ => quaternionToMatrix_mem _)).symm
end WindowRestrictions
namespace MomentLaw
open TorusFields WeightedResponses BlockAverages TorusLimits TwoPointLaw Matrices LevelTestFunctions WindowRestrictions
open SetPartition (PartitionsFin blockCount)
section Wilson
variable {m : ℕ} [NeZero m]
private theorem isProbabilityMeasure_wilsonLaw (β : ℝ) : IsProbabilityMeasure (wilsonLaw β m) := by apply _root_.YangMills.SharedProofs.p2076 <;> assumption
private theorem isBoundedRealRV_curvatureObservable (h : PlaquetteWeight m) :
    Probability.IsBoundedRealRV (curvatureObservable h) := by
  have hc : Continuous (curvatureObservable h) :=
    continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_plaquetteEnergy p.1 p.2.1 p.2.2)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨hc.measurable, C, fun W => by simpa using hC W (Set.mem_univ _)⟩
abbrev _root_.YangMills.SharedProofs.p42321 := @isBoundedRealRV_curvatureObservable
end Wilson
section Levels
variable {k : ℕ}
private theorem circleRep_eq {c d b : ℝ} {t : ℤ} (hc : 0 < c) (hd : d = b + c * t) (hb : 2 * |b| < c) :
    circleRep c d = b := by
  have h1 : d / c = b / c + t := by
    rw [hd]
    field_simp
  have hbb := abs_le.mp (le_refl |b|)
  have h2 : round (b / c) = 0 := by
    rw [round_eq_zero_iff]
    constructor
    · rw [le_div_iff₀ hc]
      linarith [hbb.1]
    · rw [div_lt_iff₀ hc]
      linarith [hbb.2]
  unfold circleRep
  rw [h1, round_add_intCast, h2, hd]
  push_cast
  ring
abbrev _root_.YangMills.SharedProofs.p85907 := @circleRep_eq
private def scaledTestValue (P : LevelData k) (L : ℕ) (z : Fin 4 → ℤ) (i : Fin k) (Q : OrientedPlaquette) : ℝ :=
  P.fn i (WithLp.toLp 2 fun a => (plaquetteBarycenter Q a - (z a : ℝ)) / (L : ℝ) ^ P.scaleLevel)
private theorem period_pos (P : LevelData k) {L : ℕ} (hL : 0 < L) : (0 : ℝ) < (P.period L : ℝ) := by
  unfold LevelData.period
  have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  push_cast
  positivity
private theorem testWeight_plaquetteOnTorus (P : LevelData k) {L N : ℕ} [NeZero N] (hL : 0 < L) {z : Fin 4 → ℤ}
    (hz : ∀ a, P.center a = (z a : ℝ) / (L : ℝ) ^ P.windowLevel) (hN : N = P.period L * L ^ P.windowLevel)
    (i : Fin k) (Q : OrientedPlaquette) (hb : ∀ a, 2 * |plaquetteBarycenter Q a - (z a : ℝ)| < N) :
    P.testWeight L i N (plaquetteOnTorus N Q) = scaledTestValue P L z i Q := by
  unfold LevelData.testWeight scaledTestValue
  refine congrArg (fun x => P.fn i (WithLp.toLp 2 x)) (funext fun a => ?_)
  have hK : (0 : ℝ) < (L : ℝ) ^ P.windowLevel := by positivity
  have hNr : (N : ℝ) = (P.period L : ℝ) * (L : ℝ) ^ P.windowLevel := by exact_mod_cast hN
  have hbar : barycenterCoord (plaquetteOnTorus N Q) a =
      plaquetteBarycenter Q a - N * ((Q.1.1 a / (N : ℤ) : ℤ) : ℝ) := by
    have e : barycenterCoord (plaquetteOnTorus N Q) a = (((siteOfInt Q.1.1 : TorusSite N) a).val : ℝ) +
        (if a = Q.1.2.1 then 1 / 2 else 0) + (if a = Q.1.2.2 then 1 / 2 else 0) := rfl
    have v : (((siteOfInt Q.1.1 : TorusSite N) a).val : ℝ) = (Q.1.1 a : ℝ) - N * ((Q.1.1 a / (N : ℤ) : ℤ) : ℝ) :=
      WindowRestrictions.zmod_val_intCast_real _
    rw [e, v]
    unfold plaquetteBarycenter
    ring
  have hw : circleRep (P.period L : ℝ) (barycenterCoord (plaquetteOnTorus N Q) a / (L : ℝ) ^ P.windowLevel - P.center a) =
      (plaquetteBarycenter Q a - (z a : ℝ)) / (L : ℝ) ^ P.windowLevel := by
    refine circleRep_eq (t := -(Q.1.1 a / (N : ℤ))) (period_pos P hL) ?_ ?_
    · rw [hbar, hz, hNr]
      push_cast
      field_simp
      ring
    · rw [abs_div, abs_of_pos hK, ← mul_div_assoc, div_lt_iff₀ hK, ← hNr]
      exact hb a
  rw [hw]
  field_simp
private theorem exists_plaquette_lift (P : LevelData k) {L N : ℕ} [NeZero N] (hL : 0 < L) {z : Fin 4 → ℤ}
    (hz : ∀ a, P.center a = (z a : ℝ) / (L : ℝ) ^ P.windowLevel) (hN : N = P.period L * L ^ P.windowLevel)
    (i : Fin k) (p : TorusPlaquette N) (hp : p.2.1 < p.2.2) :
    ∃ Q : OrientedPlaquette, plaquetteOnTorus N Q = p ∧ scaledTestValue P L z i Q = P.testWeight L i N p := by
  let r : Fin 4 → ℤ := fun a => round ((barycenterCoord p a / (L : ℝ) ^ P.windowLevel - P.center a) / (P.period L : ℝ))
  let n : Fin 4 → ℤ := fun a => ((p.1 a).val : ℤ) - N * r a
  refine ⟨⟨(n, p.2.1, p.2.2), hp⟩, ?_, ?_⟩
  · have h1 : (siteOfInt n : TorusSite N) = p.1 := by
      funext a
      simp [siteOfInt, n]
    simp only [plaquetteOnTorus, h1]
  · unfold scaledTestValue LevelData.testWeight
    refine congrArg (fun x => P.fn i (WithLp.toLp 2 x)) (funext fun a => ?_)
    have hNr : (N : ℝ) = (P.period L : ℝ) * (L : ℝ) ^ P.windowLevel := by exact_mod_cast hN
    have hc : circleRep (P.period L : ℝ) (barycenterCoord p a / (L : ℝ) ^ P.windowLevel - P.center a) =
        barycenterCoord p a / (L : ℝ) ^ P.windowLevel - P.center a - (P.period L : ℝ) * (r a : ℝ) := rfl
    rw [hc, hz]
    have hn : ((n a : ℤ) : ℝ) = ((p.1 a).val : ℝ) - (N : ℝ) * (r a : ℝ) := by
      simp [n]
    simp only [plaquetteBarycenter, barycenterCoord]
    rw [hn, hNr]
    field_simp
    ring
private theorem offsetInBox_of_scaledTestValue_ne_zero (P : LevelData k) {L : ℕ} (hL : 0 < L) {R d : ℝ}
    (ht : IsSupTestFamily R d P.fn) {z : Fin 4 → ℤ} {Z Rc : ℕ} (hZ : ∀ a, |z a| ≤ (Z : ℤ))
    (hR : R * (L : ℝ) ^ P.scaleLevel ≤ Rc) (i : Fin k) (Q : OrientedPlaquette) (hne : scaledTestValue P L z i Q ≠ 0) :
    TorusFields.OffsetInBox (Rc + Z + 1) Q.1.1 := by
  intro a
  have hS : (0 : ℝ) < (L : ℝ) ^ P.scaleLevel := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    positivity
  have h := ht.abs_coord_le i _ (subset_tsupport _ hne) a
  have h' : |(plaquetteBarycenter Q a - (z a : ℝ)) / (L : ℝ) ^ P.scaleLevel| ≤ R := h
  rw [abs_div, abs_of_pos hS, div_le_iff₀ hS] at h'
  have hb := abs_le.mp (h'.trans hR)
  have hq : |(z a : ℝ)| ≤ Z := by exact_mod_cast hZ a
  have hq' := abs_le.mp hq
  obtain ⟨e1, e2⟩ := WindowRestrictions.plaquetteBarycenter_bounds Q a
  refine abs_le.mpr ⟨?_, ?_⟩
  · have : -((Rc : ℝ) + Z + 1) ≤ (Q.1.1 a : ℝ) := by linarith [hb.1, hq'.1]
    exact_mod_cast this
  · have : (Q.1.1 a : ℝ) ≤ (Rc : ℝ) + Z + 1 := by linarith [hb.2, hq'.2]
    exact_mod_cast this
private theorem two_mul_abs_barycenter_sub_lt {N R₀ Z : ℕ} {z : Fin 4 → ℤ} (hZ : ∀ a, |z a| ≤ (Z : ℤ))
    (hN : 2 * (R₀ + Z + 1) < N) (Q : OrientedPlaquette) (hQ : TorusFields.OffsetInBox R₀ Q.1.1) (a : Fin 4) :
    2 * |plaquetteBarycenter Q a - (z a : ℝ)| < N := by
  have hq : |(z a : ℝ)| ≤ Z := by exact_mod_cast hZ a
  have hq' := abs_le.mp hq
  have hn : |(Q.1.1 a : ℝ)| ≤ R₀ := by exact_mod_cast hQ a
  have hn' := abs_le.mp hn
  obtain ⟨e1, e2⟩ := WindowRestrictions.plaquetteBarycenter_bounds Q a
  have h : |plaquetteBarycenter Q a - (z a : ℝ)| ≤ (R₀ : ℝ) + Z + 1 :=
    abs_le.mpr ⟨by linarith [hq'.2, hn'.1], by linarith [hq'.1, hn'.2]⟩
  have hNr : (2 * ((R₀ : ℝ) + Z + 1)) < N := by exact_mod_cast hN
  linarith
private abbrev withSideExponent (P : LevelData k) (m' : ℕ) : LevelData k := { P with sideExponent := m' }
end Levels
namespace MomentPoint
variable {Λ : MomentParameters}
private def onTorusOfExponent (S : MomentPoint Λ) (m' : ℕ)
    (hp : (withSideExponent S.data m').SupAdmissible Λ.stepParams.side Λ.R Λ.d)
    (hs : Λ.stepParams.side * Λ.stepParams.n₀ ≤ (withSideExponent S.data m').period Λ.stepParams.side) :
    MomentPoint Λ :=
  { S with data := withSideExponent S.data m', supAdmissible := hp, side_le := hs }
private theorem rescaledTestFunction_center (S : MomentPoint Λ) {z : Fin 4 → ℤ}
    (hz : ∀ a, S.data.center a = (z a : ℝ) / (Λ.stepParams.side : ℝ) ^ S.data.windowLevel) (i : Fin Λ.k)
    (Q : OrientedPlaquette) :
    S.rescaledTestFunction i
        (toElementaryPlaquette (PeriodicLattice.meshSize Λ.stepParams.side (S.data.windowLevel : ℤ)) Q).center =
      scaledTestValue S.data Λ.stepParams.side z i Q := by
  unfold rescaledTestFunction scaledTestValue
  refine congrArg (fun x => S.data.fn i (WithLp.toLp 2 x)) (funext fun a => ?_)
  set a₀ := PeriodicLattice.meshSize Λ.stepParams.side (S.data.windowLevel : ℤ) with ha₀
  have hL' : (Λ.stepParams.side : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Λ.stepParams.side
  have hK : (Λ.stepParams.side : ℝ) ^ S.data.windowLevel ≠ 0 := pow_ne_zero _ hL'
  have hS : (Λ.stepParams.side : ℝ) ^ S.data.scaleLevel ≠ 0 := pow_ne_zero _ hL'
  have ha : a₀ = ((Λ.stepParams.side : ℝ) ^ S.data.windowLevel)⁻¹ := by
    simp [ha₀, PeriodicLattice.meshSize, zpow_neg]
  have hb : (toElementaryPlaquette a₀ Q).center a =
      (Q.1.1 a : ℝ) * a₀ + (if a = Q.1.2.1 then a₀ / 2 else 0) + (if a = Q.1.2.2 then a₀ / 2 else 0) := by
    simp [InfiniteLattice.ElementaryPlaquette.center, toElementaryPlaquette, latticePointOfInt, Pi.single_apply]
  rw [hb, ha, hz]
  unfold plaquetteBarycenter
  split_ifs <;> field_simp <;> ring
end MomentPoint
private def partitionMomentSum (k : ℕ) (M : Finset (Fin k) → ℝ) : ℂ :=
  ∑ π : PartitionsFin k, (-1 : ℂ) ^ (blockCount π - 1) * ((blockCount π - 1).factorial : ℂ) *
    ∏ J ∈ π.parts, ((M J : ℝ) : ℂ)
private theorem tendsto_partitionMomentSum {k : ℕ} {M : ℕ → Finset (Fin k) → ℝ} {M' : Finset (Fin k) → ℝ}
    (h : ∀ J, Tendsto (fun i => M i J) atTop (𝓝 (M' J))) :
    Tendsto (fun i => partitionMomentSum k (M i)) atTop (𝓝 (partitionMomentSum k M')) := by
  unfold partitionMomentSum
  refine tendsto_finsetSum _ fun π _ => Tendsto.const_mul _ (tendsto_finsetProd _ fun J _ => ?_)
  exact (Complex.continuous_ofReal.tendsto _).comp (h J)
private theorem cumulant_bound_at_limit (hW : HullsInEveryVolume.wilsonLawsAgreeStatement)
    (hM : Cumulants.MixedCumulantMomentExpansion) {Λ : MomentParameters} (S : MomentPoint Λ)
    (hodd : Odd Λ.stepParams.side) (hL : 1 < Λ.stepParams.side) (hβ : 0 < S.β) (b : ℝ)
    (hlaw : ∀ S' : MomentPoint Λ,
      ‖(S'.scaleCoupling : ℂ) ^ Λ.k * S'.torusCumulant - (S'.latticeCycleSumAt S'.data.scaleLevel : ℂ)‖ ≤
        b * S'.scaleCoupling ^ (-(1 / 10) : ℝ))
    {ν : Measure (FineField Λ.stepParams.side S.data.windowLevel)} {ms : ℕ → ℕ}
    (hlim : IsTorusLimitAlong Λ.stepParams.side S.data.windowLevel S.β ν ms) :
    ‖(S.scaleCoupling : ℂ) ^ Λ.k * S.stateUrsell ν - (S.latticeCycleSumAt S.data.scaleLevel : ℂ)‖ ≤
      b * S.scaleCoupling ^ (-(1 / 10) : ℝ) := by
  classical
  obtain ⟨hpos, hmono, hconv⟩ := hlim
  obtain ⟨z, hz⟩ := S.supAdmissible.center_mem_lattice
  let L := Λ.stepParams.side
  let w := S.data.windowLevel
  have hL0 : 0 < L := Nat.zero_lt_one.trans hL
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL.le
  have hk1 : 1 ≤ Λ.k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hsp : PeriodicLattice.meshSize L (w : ℤ) ≠ 0 := zpow_ne_zero _ (by positivity)
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ, ∀ a, |z a| ≤ (Z : ℤ) := by
    refine ⟨∑ a, (z a).natAbs, fun a => ?_⟩
    rw [Int.abs_eq_natAbs]
    exact_mod_cast Finset.single_le_sum (f := fun a => (z a).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  obtain ⟨Rc, hRc⟩ : ∃ Rc : ℕ, Λ.R * (L : ℝ) ^ S.data.scaleLevel ≤ Rc := ⟨_, Nat.le_ceil _⟩
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℕ, R₀ = Rc + Z + 1 := ⟨_, rfl⟩
  have hbox : ∀ i Q, scaledTestValue S.data L z i Q ≠ 0 → TorusFields.OffsetInBox R₀ Q.1.1 :=
    fun i Q h => by
      rw [hR₀]
      exact offsetInBox_of_scaledTestValue_ne_zero S.data hL0 S.supAdmissible.isSupTestFamily hZ hRc i Q h
  let c : Fin Λ.k → OrientedPlaquette → ℝ := fun i Q => scaledTestValue S.data L z i Q
  let G : Fin Λ.k → WindowValuation (R₀ + 2) → ℝ := fun i => windowEnergyObservable (cubePlaquettes R₀) (c i)
  have hGb : ∀ i, IsBoundedWindowObservable (G i) := fun i =>
    WindowRestrictions.isBounded_windowEnergyObservable _ _
  have hcoef : ∀ i Q, S.rescaledTestFunction i
      (toElementaryPlaquette (PeriodicLattice.meshSize L (w : ℤ)) Q).center ≠ 0 →
      TorusFields.OffsetInBox R₀ Q.1.1 := fun i Q h =>
    hbox i Q (by rwa [MomentPoint.rescaledTestFunction_center S hz] at h)
  let X : Fin Λ.k → FineField L w → ℝ := fun i U =>
    InfiniteLattice.cutoffSmearedEnergyRe (S.rescaledTestFunction i) U
  have hXs : ∀ i U, X i U = evalOnField (G i) U := by
    intro i U
    have e := WindowRestrictions.smearedEnergy_eq_evalOnField hsp (S.rescaledTestFunction i) (hcoef i) U
    have hc : (fun Q => S.rescaledTestFunction i
        (toElementaryPlaquette (PeriodicLattice.meshSize L (w : ℤ)) Q).center) = c i :=
      funext (MomentPoint.rescaledTestFunction_center S hz i)
    rw [hc] at e
    exact (InfiniteLattice.cutoffSmearedEnergyRe_eq_smearedEnergy _ U).trans e
  have hXc : ∀ i, Continuous (X i) := by
    intro i
    have e : X i = InfiniteLattice.smearedEnergy (S.rescaledTestFunction i) :=
      funext fun U => InfiniteLattice.cutoffSmearedEnergyRe_eq_smearedEnergy _ U
    rw [e]
    exact WindowRestrictions.continuous_smearedEnergy hsp _ (hcoef i)
  obtain ⟨M, hM1, hM2, hM3⟩ : ∃ M : ℕ, R₀ + Z + 1 ≤ M ∧ L * Λ.stepParams.n₀ ≤ M ∧
      4 * |Λ.R| * (L : ℝ) ^ S.data.scaleLevel ≤ M := by
    refine ⟨R₀ + Z + 1 + L * Λ.stepParams.n₀ + ⌈4 * |Λ.R| * (L : ℝ) ^ S.data.scaleLevel⌉₊, by omega, by omega, ?_⟩
    refine (Nat.le_ceil _).trans ?_
    push_cast
    have h0 : (0 : ℝ) ≤ ((R₀ : ℝ) + Z + 1 + (L : ℝ) * Λ.stepParams.n₀) := by positivity
    linarith
  have hgrow : ∀ m' : ℕ, m' ≤ L ^ m' := fun m' => (Nat.lt_pow_self hL).le
  have hNfar : ∀ m', M ≤ m' → 2 * (R₀ + Z + 1) <
      (withSideExponent S.data m').period L * L ^ (withSideExponent S.data m').windowLevel := by
    intro m' hm
    have h1 : m' < L ^ m' := Nat.lt_pow_self hL
    have h2 : 1 ≤ L ^ w := Nat.one_le_pow _ _ hL0
    have h3 : R₀ + Z + 1 < L ^ m' := by omega
    show 2 * (R₀ + Z + 1) < 2 * L ^ m' * L ^ w
    nlinarith
  have hpage : ∀ m', M ≤ m' → (withSideExponent S.data m').SupAdmissible L Λ.R Λ.d := by
    intro m' hm
    refine ⟨S.supAdmissible.isSupTestFamily, S.supAdmissible.scaleLevel_le, ?_, S.supAdmissible.center_mem_lattice,
      fun i => ?_⟩
    · have h1 : (m' : ℝ) ≤ (L : ℝ) ^ m' := by exact_mod_cast hgrow m'
      have h2 : 4 * |Λ.R| * (L : ℝ) ^ S.data.scaleLevel ≤ m' := hM3.trans (by exact_mod_cast hm)
      have h3 : (1 : ℝ) ≤ (L : ℝ) ^ w := one_le_pow₀ hLr
      have h4 : ((withSideExponent S.data m').period L : ℝ) = 2 * (L : ℝ) ^ m' := by
        simp [LevelData.period]
      have h5 : 0 ≤ (L : ℝ) ^ S.data.scaleLevel := by positivity
      have h6 : 2 * Λ.R * (L : ℝ) ^ S.data.scaleLevel ≤ 2 * |Λ.R| * (L : ℝ) ^ S.data.scaleLevel := by
        have := le_abs_self Λ.R
        nlinarith
      have h7 : 0 ≤ (L : ℝ) ^ m' := by positivity
      show 2 * Λ.R * (L : ℝ) ^ S.data.scaleLevel ≤ ((withSideExponent S.data m').period L : ℝ) / 4 * (L : ℝ) ^ w
      rw [h4]
      calc 2 * Λ.R * (L : ℝ) ^ S.data.scaleLevel ≤ 2 * |Λ.R| * (L : ℝ) ^ S.data.scaleLevel := h6
        _ ≤ 2 * (L : ℝ) ^ m' / 4 * 1 := by linarith
        _ ≤ 2 * (L : ℝ) ^ m' / 4 * (L : ℝ) ^ w := mul_le_mul_of_nonneg_left h3 (by positivity)
    · obtain ⟨p, hp⟩ := S.supAdmissible.exists_ne_zero i
      obtain ⟨Q, -, hQ⟩ := exists_plaquette_lift S.data hL0 hz rfl i p.1 p.2
      have hne : scaledTestValue S.data L z i Q ≠ 0 := by
        rw [hQ]
        exact hp
      have e := testWeight_plaquetteOnTorus (withSideExponent S.data m') hL0 hz rfl i Q
        (two_mul_abs_barycenter_sub_lt hZ (hNfar m' hm) Q (hbox i Q hne))
      refine ⟨⟨plaquetteOnTorus _ Q, Q.2⟩, ?_⟩
      show (withSideExponent S.data m').testWeight L i _ (plaquetteOnTorus _ Q) ≠ 0
      rw [e]
      exact hne
  have hside : ∀ m', M ≤ m' → L * Λ.stepParams.n₀ ≤ (withSideExponent S.data m').period L := by
    intro m' hm
    show _ ≤ 2 * L ^ m'
    have := hgrow m'
    omega
  have htorus : ∀ m', M ≤ m' → ∀ (i : Fin Λ.k) (W : TorusField (fineSide L w (2 * L ^ m'))),
      curvatureObservable ((withSideExponent S.data m').testWeight L i (fineSide L w (2 * L ^ m'))) W =
        evalOnTorus (G i) W := by
    intro m' hm i W
    have hN : fineSide L w (2 * L ^ m') =
        (withSideExponent S.data m').period L * L ^ (withSideExponent S.data m').windowLevel := fineSide_eq _ _ _
    have hfar : 2 * (R₀ + Z + 1) < fineSide L w (2 * L ^ m') := by
      rw [hN]
      exact hNfar m' hm
    refine WindowRestrictions.curvatureObservable_eq_evalOnTorus _ (c i) (by omega) (fun Q hQ => ?_)
      (fun p hlt hne => ?_) W
    · exact testWeight_plaquetteOnTorus (withSideExponent S.data m') hL0 hz hN i Q
        (two_mul_abs_barycenter_sub_lt hZ hfar Q (mem_cubePlaquettes.mp hQ))
    · obtain ⟨Q, e, hQ⟩ := exists_plaquette_lift (withSideExponent S.data m') hL0 hz hN i p hlt
      have hne' : scaledTestValue S.data L z i Q ≠ 0 := by
        have h' : scaledTestValue S.data L z i Q = (withSideExponent S.data m').testWeight L i _ p := hQ
        rw [h']
        exact hne
      exact ⟨Q, mem_cubePlaquettes.mpr (hbox i Q hne'), e⟩
  have hmoment : ∀ m', M ≤ m' → 0 < m' → ∀ J : Finset (Fin Λ.k),
      ∫ W, ∏ j ∈ J, curvatureObservable ((withSideExponent S.data m').testWeight L j (fineSide L w (2 * L ^ m'))) W
          ∂(wilsonLaw S.β (fineSide L w (2 * L ^ m'))) =
        ∫ U, ∏ j ∈ J, X j U ∂(InfiniteLattice.liftedWilsonMeasure L m' w S.β) := by
    intro m' hm hm0 J
    have hb : IsBoundedWindowObservable fun v => ∏ j ∈ J, G j v :=
      WindowRestrictions.isBoundedWindowObservable_prod J fun j _ => hGb j
    have e := hW L w m' _ S.β _ hodd hL hm0 hβ hb
    refine Eq.trans ?_ (e.trans ?_)
    · refine integral_congr_ae (Eventually.of_forall fun W => ?_)
      exact Finset.prod_congr rfl fun j _ => htorus m' hm j W
    · refine integral_congr_ae (Eventually.of_forall fun U => ?_)
      exact Finset.prod_congr rfl fun j _ => (hXs j U).symm
  have hreal : ∀ F : FineField L w → ℝ, Continuous F →
      Tendsto (fun i => ∫ U, F U ∂InfiniteLattice.liftedWilsonMeasure L (ms i) w S.β) atTop (𝓝 (∫ U, F U ∂ν)) := by
    intro F hF
    have h := hconv (fun ω => (F ω : ℂ)) (Complex.continuous_ofReal.comp hF)
    simp only [integral_complex_ofReal] at h
    simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp h
  have hmass : ∀ i, ∫ _U, (1 : ℝ) ∂InfiniteLattice.liftedWilsonMeasure L (ms i) w S.β = 1 := by
    intro i
    have := isProbabilityMeasure_wilsonLaw (m := fineSide L w (2 * L ^ ms i)) S.β
    have hb : IsBoundedWindowObservable (fun _ : WindowValuation 0 => (1 : ℝ)) :=
      ⟨measurable_const, 1, fun _ => by simp⟩
    have e := hW L w (ms i) 0 S.β _ hodd hL (hpos i) hβ hb
    have e' : ∫ _W, (1 : ℝ) ∂(wilsonLaw S.β (fineSide L w (2 * L ^ ms i))) =
        ∫ _U, (1 : ℝ) ∂InfiniteLattice.liftedWilsonMeasure L (ms i) w S.β := e
    rw [← e']
    simp
  have hνone : ∫ _U, (1 : ℝ) ∂ν = 1 :=
    tendsto_nhds_unique (hreal _ continuous_const) (by simp only [hmass]; exact tendsto_const_nhds)
  have hνp : IsProbabilityMeasure ν := ⟨by
    have h := hνone
    rw [integral_const, smul_eq_mul, mul_one] at h
    exact (ENNReal.toReal_eq_one_iff _).mp h⟩
  have hbdd : ∀ l, Probability.IsBoundedRealRV (X l) := by
    intro l
    obtain ⟨C, hC⟩ := (hGb l).bounded
    exact ⟨(hXc l).measurable, C, fun U => by
      rw [hXs l U]
      exact hC _⟩
  have hstate : S.stateUrsell ν = partitionMomentSum Λ.k fun J => ∫ U, ∏ l ∈ J, X l U ∂ν :=
    hM _ ν Λ.k X hk1 hbdd
  have htend : Tendsto (fun i => partitionMomentSum Λ.k fun J =>
      ∫ U, ∏ l ∈ J, X l U ∂InfiniteLattice.liftedWilsonMeasure L (ms i) w S.β) atTop (𝓝 (S.stateUrsell ν)) := by
    rw [hstate]
    exact tendsto_partitionMomentSum fun J => hreal _ (continuous_finsetProd _ fun l _ => hXc l)
  have hcum : ∀ m', M ≤ m' → 0 < m' →
      connectedCurvature S.β (fineSide L w (2 * L ^ m'))
          (fun j => (withSideExponent S.data m').testWeight L j (fineSide L w (2 * L ^ m'))) =
        partitionMomentSum Λ.k fun J => ∫ U, ∏ l ∈ J, X l U ∂InfiniteLattice.liftedWilsonMeasure L m' w S.β := by
    intro m' hm hm0
    have := isProbabilityMeasure_wilsonLaw (m := fineSide L w (2 * L ^ m')) S.β
    have e : connectedCurvature S.β (fineSide L w (2 * L ^ m'))
          (fun j => (withSideExponent S.data m').testWeight L j (fineSide L w (2 * L ^ m'))) =
        partitionMomentSum Λ.k fun J =>
          ∫ W, ∏ j ∈ J, curvatureObservable ((withSideExponent S.data m').testWeight L j (fineSide L w (2 * L ^ m'))) W
            ∂(wilsonLaw S.β (fineSide L w (2 * L ^ m'))) :=
      hM _ _ Λ.k _ hk1 fun l => isBoundedRealRV_curvatureObservable _
    rw [e]
    exact congrArg (partitionMomentSum Λ.k) (funext (hmoment m' hm hm0))
  have hfar : ∀ᶠ i in atTop, M ≤ ms i := hmono.tendsto_atTop.eventually (eventually_ge_atTop M)
  refine le_of_tendsto ((htend.const_mul ((S.scaleCoupling : ℂ) ^ Λ.k)).sub_const
    (S.latticeCycleSumAt S.data.scaleLevel : ℂ)).norm ?_
  filter_upwards [hfar] with i hi
  have h := hlaw (MomentPoint.onTorusOfExponent S (ms i) (hpage _ hi) (hside _ hi))
  rw [← hcum (ms i) hi (hpos i)]
  exact h
theorem limitPointCumulant_of_torusCumulant (hT : torusCumulantStatement)
    (hW : HullsInEveryVolume.wilsonLawsAgreeStatement) (hM : Cumulants.MixedCumulantMomentExpansion) :
    limitPointCumulantStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, h⟩ := hT a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hLo hLL Tb hTa hTL hD hCS hCH hrt' hC => ?_⟩
  obtain ⟨M, f⟩ := h L hLo hLL Tb hTa hTL hD hCS hCH hrt' hC
  refine ⟨M, fun Kr hKc hη hN hKr hRet => ?_⟩
  obtain ⟨y₀, h'⟩ := f Kr hKc hη hN hKr hRet
  refine ⟨y₀, fun y hy hret hrow g hg hgy k _ hk2 hk8 R d hd => ?_⟩
  obtain ⟨C, c, X₀, hc, hX, hS⟩ := h' y hy hret hrow g hg hgy k hk2 hk8 R d hd
  refine ⟨C, c, X₀, hc, hX, fun S => ⟨hS S, fun ν ⟨ms, hms⟩ => ?_⟩⟩
  have hβ : 0 < S.β := by
    have hab : (g ^ 2)⁻¹ + 2 * Tb.B ≤ S.β := S.window_le
    have hp : 0 < (g ^ 2)⁻¹ := by positivity
    linarith [hD.B_ge]
  exact cumulant_bound_at_limit hW hM S hD.L_odd (lt_of_lt_of_le (by norm_num) hD.L_ge) hβ (C 0) hS hms
end MomentLaw
end YangMills.Construction
end

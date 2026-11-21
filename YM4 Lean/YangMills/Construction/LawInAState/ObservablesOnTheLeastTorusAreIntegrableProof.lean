import YangMills.Construction.InfiniteLattice.TorusStatesAreTheVolumeLimitPointsProof
import YangMills.Construction.LawInAState.ObservablesOnTheLeastTorusAreIntegrable
import YangMills.Construction.LawInAState.WilsonsLawOnTheLeastTorusInTheExpansion
import YangMills.Construction.ReflectionPositivity.CovarianceAlgebraAndLocalisationOfTheRepresentativesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Quaternion
noncomputable section
namespace YangMills.Construction.StateLaws
open TorusFields WeightedResponses
open InfiniteLattice (AmbientSpace)
open BlockAverages (UnitQuaternion)
private instance : SecondCountableTopology UnitQuaternion :=
  TopologicalSpace.Subtype.secondCountableTopology (unitary ℍ[ℝ] : Set ℍ[ℝ])
private theorem continuous_boltzmannFactor (β : ℝ) (m : ℕ) [NeZero m] :
    Continuous fun W : TorusField m => Real.exp (-β * wilsonAction Finset.univ W) := by
  have hW : ∀ (x : TorusSite m) (i : Fin 4), Continuous fun W : TorusField m => W x i := fun x i =>
    (continuous_apply i).comp (continuous_apply x)
  have hp : ∀ p : TorusPlaquette m, Continuous fun W : TorusField m => holonomy W p.1 p.2.1 p.2.2 := fun p =>
    (((hW _ _).mul (hW _ _)).mul (hW _ _).inv).mul (hW _ _).inv
  have h : Continuous fun W : TorusField m => wilsonAction Finset.univ W :=
    continuous_finsetSum _ fun p _ =>
      continuous_const.sub (Quaternion.continuous_re.comp (continuous_subtype_val.comp (hp p)))
  exact Real.continuous_exp.comp (continuous_const.mul h)
private theorem integral_one_wilsonLaw (β : ℝ) (m : ℕ) [NeZero m] : ∫ _W, (1 : ℝ) ∂wilsonLaw β m = 1 := by
  have hc := continuous_boltzmannFactor β m
  have hi : Integrable (fun W : TorusField m => Real.exp (-β * wilsonAction Finset.univ W)) (fieldHaar m) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZ : 0 < ∫ W, Real.exp (-β * wilsonAction Finset.univ W) ∂fieldHaar m := integral_exp_pos hi
  have hm : Measurable fun W : TorusField m => ENNReal.ofReal (Real.exp (-β * wilsonAction Finset.univ W) /
      ∫ W', Real.exp (-β * wilsonAction Finset.univ W') ∂fieldHaar m) :=
    (hc.measurable.div_const _).ennreal_ofReal
  unfold wilsonLaw
  rw [integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have e : ∀ W : TorusField m, (ENNReal.ofReal (Real.exp (-β * wilsonAction Finset.univ W) /
      ∫ W', Real.exp (-β * wilsonAction Finset.univ W') ∂fieldHaar m)).toReal • (1 : ℝ) =
      Real.exp (-β * wilsonAction Finset.univ W) /
        ∫ W', Real.exp (-β * wilsonAction Finset.univ W') ∂fieldHaar m := fun W => by
    rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ.le), smul_eq_mul, mul_one]
  simp only [e]
  rw [integral_div, div_self hZ.ne']
private theorem compactSpace_gaugeField (a : ℝ) : CompactSpace (InfiniteLattice.GaugeField a) := by apply _root_.YangMills.SharedProofs.p823 <;> assumption
private theorem finite_plaquettes_of_hasCompactSupport {a : ℝ} (ha : 0 < a) {f : AmbientSpace → ℝ}
    (hf : HasCompactSupport f) :
    {P : InfiniteLattice.ElementaryPlaquette a | f P.center ≠ 0}.Finite := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.finite_center_support <;> assumption
private theorem continuous_smearedEnergy {a : ℝ} (ha : 0 < a) {f : AmbientSpace → ℝ} (hf : HasCompactSupport f) :
    Continuous fun U : InfiniteLattice.GaugeField a => InfiniteLattice.smearedEnergy f U := by
  have hfin := finite_plaquettes_of_hasCompactSupport ha hf
  have e : (fun U : InfiniteLattice.GaugeField a => InfiniteLattice.smearedEnergy f U) =
      fun U : InfiniteLattice.GaugeField a => ∑ P ∈ hfin.toFinset,
        InfiniteLattice.faceEnergy U P • f P.center := by
    funext U
    unfold InfiniteLattice.smearedEnergy
    refine finsum_eq_sum_of_support_subset _ ?_
    intro P hP
    have hP' : f P.center ≠ 0 := fun h0 => hP (by simp [h0])
    simpa using hP'
  rw [e]
  refine continuous_finsetSum _ fun P _ => ?_
  simp only [smul_eq_mul]
  refine Continuous.mul ?_ continuous_const
  have hU : ∀ b : InfiniteLattice.Link a,
      Continuous fun U : InfiniteLattice.GaugeField a => U b :=
    fun b => (continuous_apply b).comp continuous_induced_dom
  have hv : Continuous fun U : InfiniteLattice.GaugeField a =>
      InfiniteLattice.faceHolonomy U P :=
    (((hU _).mul (hU _)).mul (hU _).inv).mul (hU _).inv
  have hm : Continuous fun U : InfiniteLattice.GaugeField a =>
      ((InfiniteLattice.faceHolonomy U P : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) :=
    continuous_subtype_val.comp hv
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp hm.matrix_trace))
theorem unitTorusObservablesIntegrable (h : LawInAState.unitTorusMomentsViaWeightsStatement) :
    unitTorusObservablesIntegrableStatement := by
  intro L K _ hodd hL3 hK β p φ hφ
  have hL : 0 < L := by omega
  have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) := zpow_pos (by exact_mod_cast hL) _
  have hmass : ∫ _U, (1 : ℝ) ∂unitTorusMeasure L K β = 1 := by
    have h0 := h L K 0 hodd hL3 hK (Nat.zero_le K) β 0 Fin.elim0 (fun i => i.elim0)
    simp only [Finset.univ_eq_empty, Finset.prod_empty] at h0
    rw [h0]
    exact integral_one_wilsonLaw β _
  have hfin : IsFiniteMeasure (unitTorusMeasure L K β) := by
    refine ⟨lt_top_iff_ne_top.mpr fun htop => ?_⟩
    rw [integral_const, measureReal_def, htop] at hmass
    simp at hmass
  have := compactSpace_gaugeField (PeriodicLattice.meshSize L (K : ℤ))
  have hc : Continuous fun U : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)) =>
      ∏ i, smearedObservable L K (φ i) U :=
    continuous_finsetProd _ fun i _ => continuous_smearedEnergy ha (hφ i).2.2
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end YangMills.Construction.StateLaws
end

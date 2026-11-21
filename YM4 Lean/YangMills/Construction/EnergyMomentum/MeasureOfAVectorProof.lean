import YangMills.Construction.EnergyMomentum.LaplaceFourierDenseDetermining
import YangMills.Construction.EnergyMomentum.SemigroupGeneratorsProof
import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusTheorem
import YangMills.Construction.SpectralTheory.JointMeasureOfASemigroupAndARepresentation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace Matrix
noncomputable section
namespace YangMills.Construction.EnergyMomentum.SpectralMeasure
open YangMills.Construction.BorelSpectral YangMills.Construction.SemigroupRepresentation YangMills.Construction.BorelCalculus YangMills.Construction.EnergyMomentum
def halfSpaceToEnergyMomentum (y : nonnegHalfSpace 3) : EnergyMomentumSpace :=
  (⟨y.1 0, y.2⟩, WithLp.toLp 2 (spatialCoords y.1))
theorem measurable_halfSpaceToEnergyMomentum : Measurable halfSpaceToEnergyMomentum := by
  refine Measurable.prodMk ?_ ?_
  · exact Measurable.subtype_mk ((measurable_pi_apply 0).comp measurable_subtype_coe)
  · exact (WithLp.measurable_toLp 2 _).comp (measurable_spatialCoords.comp measurable_subtype_coe)
def halfSpaceExp (t : ℝ≥0) (a : Fin 3 → ℝ) (y : nonnegHalfSpace 3) : ℂ :=
  Complex.exp (((-(t : ℝ) * y.1 0 : ℝ) : ℂ) + Complex.I * ((a ⬝ᵥ spatialCoords y.1 : ℝ) : ℂ))
theorem halfSpaceExp_eq (t : ℝ≥0) (a : Fin 3 → ℝ) (y : nonnegHalfSpace 3) :
    halfSpaceExp t a y = laplaceFourierExp t (WithLp.toLp 2 a) (halfSpaceToEnergyMomentum y) := rfl
theorem measurable_halfSpaceExp (t : ℝ≥0) (a : Fin 3 → ℝ) :
    Measurable (halfSpaceExp t a) := by
  have hfun : halfSpaceExp t a =
      laplaceFourierExp t (WithLp.toLp 2 a) ∘ halfSpaceToEnergyMomentum :=
    funext (halfSpaceExp_eq t a)
  rw [hfun]
  exact (continuous_laplaceFourierExp t _).measurable.comp measurable_halfSpaceToEnergyMomentum
theorem isBoundedFn_halfSpaceExp (t : ℝ≥0) (a : Fin 3 → ℝ) :
    IsBoundedFn (halfSpaceExp t a) :=
  ⟨1, fun y => by
    rw [halfSpaceExp_eq]
    exact norm_laplaceFourierExp_le_one t _ _⟩
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem unitaryGroup_zero {S : ℝ≥0 → H →L[ℂ] H} {V : Momentum3 → H →L[ℂ] H}
    (hSV : IsContractionSemigroupWithUnitaryGroup S V) : V 0 = 1 := by apply _root_.YangMills.Construction.EnergyMomentum.GeneratorsProof.unitaryGroup_zero <;> assumption
def groupOnCoords (V : Momentum3 → H →L[ℂ] H) : (Fin 3 → ℝ) → H →L[ℂ] H :=
  fun a => V (WithLp.toLp 2 a)
theorem isCommutingSemigroupRep_groupOnCoords {S : ℝ≥0 → H →L[ℂ] H}
    {V : Momentum3 → H →L[ℂ] H} (hSV : IsContractionSemigroupWithUnitaryGroup S V) :
    IsCommutingSemigroupRep S (groupOnCoords V) := by
  have hV0 : groupOnCoords V 0 = 1 := by
    change V (WithLp.toLp 2 0) = 1
    rw [WithLp.toLp_zero]
    exact unitaryGroup_zero hSV
  refine ⟨⟨⟨hSV.semigroup_zero, hSV.semigroup_add⟩, hSV.isSelfAdjoint, hSV.norm_le_one, fun ψ => ?_⟩,
    ⟨fun a => ?_, hV0, fun a b => ?_⟩, fun ψ => ?_, fun a t => (hSV.semigroup_mul_group t _).symm⟩
  · have hlim := (hSV.continuous_semigroup ψ).tendsto 0
    rw [hSV.semigroup_zero] at hlim
    exact hlim.mono_left nhdsWithin_le_nhds
  · have hmem := (isUnitaryOperator_iff_mem_unitary _).mp (hSV.isUnitary (WithLp.toLp 2 a))
    exact Unitary.mem_iff.mp hmem
  · change V _ * V _ = V (WithLp.toLp 2 (a + b))
    rw [hSV.group_add, WithLp.toLp_add]
  · have hcont : Continuous fun a : Fin 3 → ℝ => groupOnCoords V a ψ :=
      (hSV.continuous_group ψ).comp (PiLp.continuous_toLp 2 _)
    have hlim := hcont.tendsto 0
    rw [hV0] at hlim
    exact hlim
theorem exists_isSpectralMeasure
    (hJ : JointSpectralTheoremForPair)
    (hC : BorelCalculusTheorem)
    {S : ℝ≥0 → H →L[ℂ] H} {V : Momentum3 → H →L[ℂ] H}
    (hSV : IsContractionSemigroupWithUnitaryGroup S V) (ψ : H) :
    ∃ m : Measure EnergyMomentumSpace, IsSpectralMeasure S V ψ m := by
  have hE : IsJointSpectralMeasure (jointSpectralMeasure S (groupOnCoords V)) S (groupOnCoords V) :=
    ((hJ H 3 (by norm_num)).1 S (groupOnCoords V) (isCommutingSemigroupRep_groupOnCoords hSV)).2.2.1
  set E := jointSpectralMeasure S (groupOnCoords V)
  have hB : BoundedFunctionalCalculus E := ((hC H (3 + 1)).1 (nonnegHalfSpace 3) E).1
  refine ⟨(E.diagMeasure ψ).map halfSpaceToEnergyMomentum, inferInstance, fun t y => ?_⟩
  have hD : E.IsDiagonalIntegral (halfSpaceExp t y.ofLp) (E.integralOp (halfSpaceExp t y.ofLp)) :=
    Classical.epsilon_spec (hB.existsUnique_op _ (measurable_halfSpaceExp t _)
      (isBoundedFn_halfSpaceExp t _)).exists
  have hop : S t * V y = E.integralOp (halfSpaceExp t y.ofLp) := hE t y.ofLp
  rw [hop, hD ψ, integral_map measurable_halfSpaceToEnergyMomentum.aemeasurable
    (continuous_laplaceFourierExp t y).aestronglyMeasurable]
  rfl
theorem statement_holds (hJ : JointSpectralTheoremForPair)
    (hC : BorelCalculusTheorem)
    (hT : LaplaceFourierDenseDetermining) : Statement := by
  intro H _ _ _ S V hSV ψ
  have hm : IsSpectralMeasure S V ψ (spectralMeasure S V ψ) :=
    Classical.epsilon_spec (exists_isSpectralMeasure hJ hC hSV ψ)
  have hfin := hm.isFiniteMeasure
  refine ⟨hm, fun m hm' => ?_, ?_⟩
  · have hfin' := hm'.isFiniteMeasure
    exact ((hT (spectralMeasure S V ψ)).2 m fun t y => by
      rw [← hm'.inner_eq_integral, ← hm.inner_eq_integral])
  · have hint := hm.inner_eq_integral 0 0
    have hone : ∀ p, laplaceFourierExp 0 0 p = 1 := fun p => by simp [laplaceFourierExp, spatialDot]
    have hnorm : ⟪ψ, ψ⟫_ℂ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    simp only [hone, hSV.semigroup_zero, unitaryGroup_zero hSV, mul_one, one_apply_eq_self] at hint
    rw [hnorm, integral_const, Complex.real_smul, mul_one] at hint
    exact (Complex.ofReal_injective hint).symm
end YangMills.Construction.EnergyMomentum.SpectralMeasure

import Formulation.WilsonDefinitions
import YangMills.Construction.ClusterExpansionOfAStep.UnitQuaternionsAreTheMatrixGroupProof

noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Wilson
open Construction Construction.ClusterExpansionOfAStep

/-- Quaternion coordinates used by the SU(2) construction. -/
def su2Model : GaugeModel where
  Carrier := BlockAverages.UnitQuaternion
  normalizedRealTrace u := (u : ℍ[ℝ]).re
  lieDim := 3
  adjointCasimir := 8

private abbrev matrixModel := specialUnitary 2
private abbrev matrixMap : su2Model.Carrier ≃ₜ* matrixModel.Carrier :=
  unitQuaternionEquivSpecialUnitary

private def linkEquiv : su2Model.Carrier ≃ᵐ matrixModel.Carrier :=
  matrixMap.toHomeomorph.toMeasurableEquiv

private def fieldEquiv (N : ℕ) : Field su2Model N ≃ᵐ Field matrixModel N :=
  MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.piCongrRight fun _ => linkEquiv

private theorem energy_fieldEquiv {N : ℕ} (U : Field su2Model N) (p : Face N) :
    energy matrixModel (fieldEquiv N U) p = energy su2Model U p := by
  obtain ⟨⟨x, μ, ν⟩, hμν⟩ := p
  let q := U x μ * U (x + Pi.single μ 1) ν * (U (x + Pi.single ν 1) μ)⁻¹ * (U x ν)⁻¹
  unfold energy
  dsimp only
  change 1 - matrixModel.normalizedRealTrace (matrixMap _ * matrixMap _ * (matrixMap _)⁻¹ * (matrixMap _)⁻¹) =
    1 - su2Model.normalizedRealTrace q
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  let u : BlockAverages.UnitQuaternion := q
  change (Matrices.ComplexMatrix2.fullTrace (unitQuaternionEquivSpecialUnitary u : Matrices.ComplexMatrix2)).re / 2 =
    (u : ℍ[ℝ]).re
  rw [(unitQuaternionHaarTraceNorm_holds.2.1 u).1]
  ring

private theorem action_fieldEquiv {N : ℕ} [NeZero N] (U : Field su2Model N) :
    action matrixModel (fieldEquiv N U) = action su2Model U := by
  unfold action
  simp only [energy_fieldEquiv]

private abbrev fieldMeasure (G : GaugeModel) (N : ℕ) [NeZero N] : Measure (Field G N) :=
  Measure.pi fun _ : Site N => Measure.pi fun _ : Fin 4 => haar G

private theorem fieldMeasure_map (N : ℕ) [NeZero N] :
    (fieldMeasure su2Model N).map (fieldEquiv N) = fieldMeasure matrixModel N := by
  have he : MeasurePreserving linkEquiv (haar su2Model) (haar matrixModel) :=
    ⟨linkEquiv.measurable, unitQuaternionHaarTraceNorm_holds.1⟩
  let : IsProbabilityMeasure (haar matrixModel) := ⟨Measure.haarMeasure_self⟩
  have h₁ := measurePreserving_pi (fun _ : Fin 4 => haar su2Model) (fun _ => haar matrixModel) (fun _ => he)
  exact (measurePreserving_pi (fun _ : Site N => Measure.pi fun _ : Fin 4 => haar su2Model)
    (fun _ => Measure.pi fun _ : Fin 4 => haar matrixModel) (fun _ => h₁)).map_eq

private theorem smear_fieldEquiv (L m K : ℕ) [NeZero L] (f : Point → ℝ)
    (U : Field su2Model (siteCount L m K)) :
    smear matrixModel L m K f (fieldEquiv _ U) = smear su2Model L m K f U := by
  unfold smear
  simp only [energy_fieldEquiv]

private theorem wilsonLaw_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (ν : Measure Y) (hμ : μ.map e = ν)
    (a : X → ℝ) (b : Y → ℝ) (ha : ∀ x, b (e x) = a x) (β : ℝ) :
    (μ.withDensity (fun x => ENNReal.ofReal
      (Real.exp (-β * a x) / ∫ z, Real.exp (-β * a z) ∂μ))).map e =
    ν.withDensity (fun y => ENNReal.ofReal
      (Real.exp (-β * b y) / ∫ z, Real.exp (-β * b z) ∂ν)) := by
  subst ν
  have hZ : (∫ z, Real.exp (-β * b z) ∂μ.map e) = ∫ x, Real.exp (-β * a x) ∂μ := by
    rw [integral_map_equiv]
    simp only [ha]
  rw [hZ]
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, e.restrict_map, lintegral_map_equiv]
  simp only [ha]

private theorem law_fieldEquiv (N : ℕ) [NeZero N] (β : ℝ) :
    (law su2Model N β).map (fieldEquiv N) = law matrixModel N β :=
  wilsonLaw_map (fieldEquiv N) _ _ (fieldMeasure_map N) _ _ action_fieldEquiv β
private theorem centeredMoment_matrix (L m K : ℕ) [NeZero L] (β : ℝ) {n : ℕ}
    (f : Fin n → Point → ℝ) :
    centeredMoment matrixModel L m K β f = centeredMoment su2Model L m K β f := by
  unfold centeredMoment
  let N := siteCount L m K
  have hμ := law_fieldEquiv N β
  change (∫ U, ∏ i, (smear matrixModel L m K (f i) U -
      ∫ V, smear matrixModel L m K (f i) V ∂law matrixModel N β) ∂law matrixModel N β) = _
  rw [← hμ]
  simp only [N, integral_map_equiv, smear_fieldEquiv]

/-- The matrix and quaternion coordinates give the same continuum proposition. -/
theorem continuum_matrix_iff_quaternion : ContinuumLimitFor (specialUnitary 2) ↔ ContinuumLimitFor su2Model := by
  have hdim : matrixModel.lieDim = su2Model.lieDim := by decide
  have hcas : matrixModel.adjointCasimir = su2Model.adjointCasimir := by
    change 2 * (2 : ℝ)^2 = 8
    norm_num
  change ContinuumLimitFor matrixModel ↔ _
  simp only [ContinuumLimitFor, bareCoupling, couplingsAt, referenceResponse, fixedPhysicalLevel,
    centeredMoment_matrix, hdim, hcas]

end YangMills.Wilson
end

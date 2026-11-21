import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.InfiniteLattice.CurvatureObservableOnTheInfiniteLattice
import YangMills.Construction.InfiniteLattice.SmearedDensityAndActionOfIsometries
import YangMills.Construction.LawInAState.LawsAreInvariantUnderTranslations
import YangMills.Construction.LawInAState.TheNumberOfAMovedPair
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.StateLaws
private theorem euclidNormVec_le_two_mul_norm (w : Fin 4 → ℝ) : TorusMetric.euclidNormVec w ≤ 2 * ‖w‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
private theorem norm_le_euclidNormVec (w : Fin 4 → ℝ) : ‖w‖ ≤ TorusMetric.euclidNormVec w := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
open InfiniteLattice
private theorem mem_compactTestFunctions_of_lipschitz_bump {d : ℝ} {f : AmbientSpace → ℝ} {b : AmbientSpace}
    (hl : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f)
    (hs : TestFunctions.uniformNorm f = 1) (hb : tsupport f ⊆ TestFunctions.closedBallR4 b d) :
    f ∈ compactTestFunctions := by
  obtain ⟨C, hC, hC'⟩ := hl
  have hcont : Continuous f := by
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (C * 2)) fun x y => ?_).continuous
    have e1 := hC' x y
    have e2 : TestFunctions.euclidDistR4 x y ≤ 2 * dist x y := by
      rw [dist_eq_norm]
      exact euclidNormVec_le_two_mul_norm _
    rw [Real.dist_eq]
    calc |f x - f y| ≤ C * TestFunctions.euclidDistR4 x y := e1
      _ ≤ C * (2 * dist x y) := mul_le_mul_of_nonneg_left e2 hC
      _ = _ := by
        rw [Real.coe_toNNReal _ (by positivity)]
        ring
  refine ⟨hcont.measurable, ⟨1, fun x => ?_⟩, ?_⟩
  · have hbd : BddAbove (Set.range fun x => ‖f x‖) := by
      by_contra hn
      have h0 : TestFunctions.uniformNorm f = 0 := Real.iSup_of_not_bddAbove hn
      rw [hs] at h0
      exact one_ne_zero h0
    rw [← hs]
    exact le_ciSup hbd x
  · refine IsCompact.of_isClosed_subset (isCompact_closedBall b d) (isClosed_tsupport f) fun x hx => ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (norm_le_euclidNormVec _).trans (hb hx)
theorem covarianceTranslationInvariant (hInv : translationInvarianceStatement)
    (hObs : FixedSpacing.CurvatureObservable.CurvatureConditions)
    (hSm : InfiniteLattice.SmearedEnergyAndSymmetryAction.Main) : covarianceTranslationInvariantStatement := by
  intro L K k β d vt v f h hodd h13 hK hk hβ hd h0 h1 hp
  obtain ⟨x₁, x₂, ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩, ⟨b₁, b₂, b₃, b₄, b₅, b₆⟩, c₁, c₂⟩ := hp.mem_class
  have hf := mem_compactTestFunctions_of_lipschitz_bump a₁ hp.norm_left a₄
  have hh := mem_compactTestFunctions_of_lipschitz_bump b₁ hp.norm_right b₄
  have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) := by
    unfold PeriodicLattice.meshSize
    positivity
  let D : ChessboardTori.ChessboardSetup := ⟨⟨L, ⟨hodd, h13⟩, ⟨K, hK⟩, 1⟩, β, hβ⟩
  let D' : FixedSpacing.Setup := ⟨L, ⟨hodd, h13⟩, K, 1, β, hβ⟩
  have hinv : ∀ w : LatticePoint (PeriodicLattice.meshSize L (K : ℤ)),
      IsSymmetricUnder (unitTorusMeasure L K β) (shift w) :=
    hInv D (unitTorusMeasure L K β) (Or.inr ⟨0, rfl⟩)
  have hw : latticeShift L K k v ∈ latticeSubgroup (PeriodicLattice.meshSize L (K : ℤ)) := by
    refine ⟨fun i => v i * (L : ℤ) ^ k, fun i => ?_⟩
    have e : (L : ℝ) ^ k / (L : ℝ) ^ K = (L : ℝ) ^ k * (L : ℝ) ^ (-(K : ℤ)) := by
      rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
    simp only [latticeShift, PeriodicLattice.meshSize]
    rw [e]
    push_cast
    ring
  let w : LatticePoint (PeriodicLattice.meshSize L (K : ℤ)) := ⟨latticeShift L K k v, hw⟩
  have hmove : ∀ g ∈ compactTestFunctions, ∀ U, smearedObservable L K (translateBy L K k v g) U =
      smearedObservable L K g ((shift w).pullbackField U) := by
    intro g hg U
    have e := ((hObs D').1 g hg).2.1.1 w
    exact (congrFun e U).symm
  have hreal : ∀ G : LatticeConfig L K → ℝ, Measurable G → (∃ C : ℝ, ∀ U, |G U| ≤ C) →
      ∫ U, G ((shift w).pullbackField U) ∂unitTorusMeasure L K β = ∫ U, G U ∂unitTorusMeasure L K β := by
    intro G hm ⟨C, hC⟩
    have e := hinv w (fun U => ((G U : ℝ) : ℂ))
      ⟨Complex.measurable_ofReal.comp hm, C, fun U => by simpa using hC U⟩
    have e2 : (((∫ U, G ((shift w).pullbackField U) ∂unitTorusMeasure L K β : ℝ)) : ℂ) =
        ((∫ U, G U ∂unitTorusMeasure L K β : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal, ← integral_complex_ofReal]
      exact e
    exact_mod_cast e2
  have hobs : ∀ g ∈ compactTestFunctions, Measurable (smearedObservable L K g) ∧
      ∃ C : ℝ, ∀ U, |smearedObservable L K g U| ≤ C := by
    intro g hg
    obtain ⟨-, -, ⟨hm, C, hC⟩, -⟩ := (hSm _ ha).1.2 g hg
    refine ⟨?_, C, fun U => ?_⟩
    swap
    · have e := hC U
      rw [Complex.norm_real, Real.norm_eq_abs] at e
      exact e
    have e : smearedObservable L K g = fun U => Complex.re ((smearedObservable L K g U : ℝ) : ℂ) := by
      funext U
      simp
    rw [e]
    exact Complex.measurable_re.comp hm
  obtain ⟨m₁, B₁, hB₁⟩ := hobs f hf
  obtain ⟨m₂, B₂, hB₂⟩ := hobs h hh
  have mean₁ : ∫ U, smearedObservable L K (translateBy L K k v f) U ∂unitTorusMeasure L K β =
      ∫ U, smearedObservable L K f U ∂unitTorusMeasure L K β := by
    simp only [hmove f hf]
    exact hreal _ m₁ ⟨B₁, hB₁⟩
  have mean₂ : ∫ U, smearedObservable L K (translateBy L K k v h) U ∂unitTorusMeasure L K β =
      ∫ U, smearedObservable L K h U ∂unitTorusMeasure L K β := by
    simp only [hmove h hh]
    exact hreal _ m₂ ⟨B₂, hB₂⟩
  have e₁ : unitTorusCovariance L K β (translateBy L K k v f) (translateBy L K k v h) =
      ∫ U, (smearedObservable L K (translateBy L K k v f) U -
          ∫ U', smearedObservable L K (translateBy L K k v f) U' ∂unitTorusMeasure L K β) *
        (smearedObservable L K (translateBy L K k v h) U -
          ∫ U', smearedObservable L K (translateBy L K k v h) U' ∂unitTorusMeasure L K β) ∂unitTorusMeasure L K β := rfl
  have e₂ : unitTorusCovariance L K β f h =
      ∫ U, (smearedObservable L K f U - ∫ U', smearedObservable L K f U' ∂unitTorusMeasure L K β) *
        (smearedObservable L K h U - ∫ U', smearedObservable L K h U' ∂unitTorusMeasure L K β) ∂unitTorusMeasure L K β := rfl
  rw [e₁, e₂, mean₁, mean₂]
  simp only [hmove f hf, hmove h hh]
  set c₁ := ∫ U', smearedObservable L K f U' ∂unitTorusMeasure L K β
  set c₂ := ∫ U', smearedObservable L K h U' ∂unitTorusMeasure L K β
  refine hreal (fun U => (smearedObservable L K f U - c₁) * (smearedObservable L K h U - c₂))
    ((m₁.sub_const c₁).mul (m₂.sub_const c₂)) ⟨(|B₁| + |c₁|) * (|B₂| + |c₂|), fun U => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((abs_sub _ _).trans (add_le_add ((hB₁ U).trans (le_abs_self _)) le_rfl))
    ((abs_sub _ _).trans (add_le_add ((hB₂ U).trans (le_abs_self _)) le_rfl)) (abs_nonneg _) (by positivity)
end YangMills.Construction.StateLaws
end

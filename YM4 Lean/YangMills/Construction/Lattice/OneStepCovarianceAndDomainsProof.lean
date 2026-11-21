import YangMills.Construction.Lattice.GaugeCovarianceOfTheOneStepObjects
import YangMills.Construction.Lattice.OneStepCovarianceAndDomains
import YangMills.Construction.Lattice.OneStepObjectsAtRealBondFunctions
import YangMills.Construction.Lattice.OneStepObjectsNearSmallPlaquettes
import YangMills.Construction.Lattice.OneStepObjectsOfFirstOrder
import YangMills.Construction.Lattice.OneStepObjectsReadInTheChart
import YangMills.Construction.Lattice.PolydiscOfTheOneStepObjectsExists
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
private theorem stepCovariance_of_objectsCovariance {s : AveragingScheme} {c : BondAtLevel L m K (n + 1)}
    {a : LieBondField (doubleBlockSymmetricSet c)} {W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    {g : SiteAtLevel L m K n → Matrices.ComplexMatrix2.specialUnitary}
    (H : StepObjectsCovariance s c a (conjugateBondField g a) W₀ (gaugeMatrixValues g)) :
    StepCovariance s c a W₀ g where
  configuration := H.twisted_eq
  logarithm := H.log_eq
  gauge := H.gauge_eq
  variable_eq := H.variable_eq
  operator := H.straightened_eq
private theorem polydiscRadius_of_stepRadius {r : ℝ} (h : IsStepRadius L r) :
    IsAdmissiblePolydiscRadius L r where
  radius_pos := h.pos
  radius_le := h.le
  bounds_on := fun m K n hm hn s c hc a₀ a h₀ h₁ =>
    have B := h.bounds m K n hm hn s c hc a₀ a h₀ h₁
    { quantities := ⟨B.logarithm, B.gauge, B.variable_le⟩
      average_bound := B.average
      conj_bound := B.adjoint }
  holomorphic_on := h.holomorphic
private theorem stepRadius_of_polydiscRadius {r : ℝ} (h : IsAdmissiblePolydiscRadius L r)
    (hu : StepObjectsChartInvariant) (hL : Conventions.IsAdmissibleBlockingFactor L) :
    IsStepRadius L r where
  pos := h.radius_pos
  le := h.radius_le
  bounds := fun m K n hm hn s c hc a₀ a h₀ h₁ =>
    have B := h.bounds_on m K n hm hn s c hc a₀ a h₀ h₁
    { logarithm := B.quantities.log_bound
      gauge := B.quantities.gauge_bound
      variable_le := B.quantities.variable_bound
      average := B.average_bound
      adjoint := B.conj_bound }
  holomorphic := h.holomorphic_on
  universal := fun m K n m' K' n' hm hn hm' hn' s μ c c' f hd hd' hf a₀ a a₀' a' h₀ h₁ e₀ e₁ =>
    have V := hu L hL r h m K n m' K' n' hm hn hm' hn' s μ c c' f hd hd'
      ⟨hf.bijOn_sites, hf.map_base, hf.map_add_unitStep⟩ a₀ a a₀' a' h₀ h₁ e₀ e₁
    { logarithm := V.log_eq
      gauge := V.gaugeLog_eq
      variable_eq := V.variable_eq
      average := V.averageLog_eq }
theorem stepCovarianceDomainsStatement_proof (hc : StepObjectsGaugeCovariance)
    (he : ExistsOneStepPolydiscRadius)
    (hu : StepObjectsChartInvariant)
    (hn : StepObjectsNearSmallCurvature)
    (hf : StepQuantitiesFirstOrder)
    (hr : RealBondFieldStepStatement) :
    stepCovarianceDomainsStatement := by
  intro L hL
  have hrad : IsStepRadius L (stepRadius L) := by
    obtain ⟨r, h⟩ := he L hL
    exact Classical.epsilon_spec (p := IsStepRadius L) ⟨r, stepRadius_of_polydiscRadius h hu hL⟩
  have hpoly : IsAdmissiblePolydiscRadius L (stepRadius L) := polydiscRadius_of_stepRadius hrad
  have hle : stepBondRadius L ≤ stepRadius L := min_le_left _ _
  refine ⟨?_, hrad, ?_⟩
  · intro m K n hm hn' s c hpos W₀ a g hW
    exact stepCovariance_of_objectsCovariance
      (hc L hL m K n hm hn' s c hpos W₀ a (conjugateBondField g a) (gaugeMatrixValues g)
        (fun x => (g x).2) (fun _ => rfl) hW)
  · intro m K n hm hn' s c hpos W₀ hW hϖ
    have hN := hn L hL _ hpoly m K n hm hn' s c hpos W₀ hW hϖ
    have hF := hf L hL _ hpoly m K n hm hn' s c hpos W₀ hW hϖ
    refine ⟨fun a ha => ?_, hN.2 _ hle, fun a ha hreal => ?_⟩
    · have hlt : supOperatorNorm a < stepRadius L := lt_of_lt_of_le ha hle
      have T := hN.1 a hlt
      have P := hF a hlt
      exact
        { logarithm := fun y hy x hx =>
            ⟨(T.log_bound y hy x hx).1, (T.log_bound y hy x hx).2, P.log_le y hy x hx⟩
          gauge := fun y hy =>
            ⟨(T.gauge_bound y hy).1, (T.gauge_bound y hy).2.1, (T.gauge_bound y hy).2.2,
              P.gaugeLog_le y hy⟩
          variable_le := ⟨T.variable_bound.1, T.variable_bound.2, P.variable_le⟩ }
    · have R := hr L hL _ hpoly m K n hm hn' s c hpos W₀ hW hϖ a ha hreal
      exact
        { logarithm := R.log_mem
          gaugeLogarithm := R.gaugeLog_mem
          variable_mem := R.variable_mem
          gauge := R.gauge_mem
          plaquettes := R.curvature_lt
          average := R.average_eq }
end YangMills.Construction.PeriodicLattice

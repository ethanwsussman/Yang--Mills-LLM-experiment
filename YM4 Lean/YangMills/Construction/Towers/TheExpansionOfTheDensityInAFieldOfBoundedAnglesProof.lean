import YangMills.Construction.RunningCouplingSlope.MixedDerivativeByCellsProof
import YangMills.Construction.Towers.ExpansionOfTheLogarithmicDensity
import YangMills.Construction.Towers.SecondDerivativesOfTheLogarithmicDensity
import YangMills.Construction.Towers.SymbolsOfTheAveragesOnPlaneWavesProof
import YangMills.Construction.Towers.TheAbelianOperatorsAreLocalFamilies
import YangMills.Construction.Towers.TheAbelianOperatorsAreShiftedPositive
import YangMills.Construction.Towers.TheDensityIsEvenInTheField
import YangMills.Construction.Towers.TheExpansionOfTheDensityInAFieldOfBoundedAngles
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
open OperatorCalculus UnitLatticeL2 LocalFamilies
namespace DensityExpansion
theorem eventually_differentiableAt_slice {F : ℝ × ℝ → ℂ} (hF : ContDiffAt ℝ 2 F 0) :
    ∀ᶠ s : ℝ in 𝓝 0, DifferentiableAt ℝ (fun t : ℝ => F (s, t)) 0 := by
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 0, ContDiffAt ℝ 2 F p := hF.eventually (by simp)
  have hcont : Tendsto (fun s : ℝ => ((s, 0) : ℝ × ℝ)) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun s : ℝ => ((s, 0) : ℝ × ℝ)) := by fun_prop
    exact this.tendsto 0
  filter_upwards [hcont.eventually hev] with s hs
  have hd : DifferentiableAt ℝ F (s, 0) := hs.differentiableAt (by simp)
  have hline : DifferentiableAt ℝ (fun t : ℝ => ((s, t) : ℝ × ℝ)) 0 := by fun_prop
  exact DifferentiableAt.comp (0 : ℝ) (f := fun t : ℝ => ((s, t) : ℝ × ℝ)) hd hline
theorem differentiableAt_deriv_slice {F : ℝ × ℝ → ℂ} (hF : ContDiffAt ℝ 2 F 0) :
    DifferentiableAt ℝ (fun s : ℝ => deriv (fun t : ℝ => F (s, t)) 0) 0 := by apply _root_.YangMills.SharedProofs.p42628 <;> assumption
theorem deriv_deriv_slice_sub_half {F G : ℝ × ℝ → ℂ} (hF : ContDiffAt ℝ 2 F 0)
    (hG : ContDiffAt ℝ 2 G 0) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => F (s, t) - (1 / 2 : ℂ) * G (s, t)) 0) 0 =
      deriv (fun s : ℝ => deriv (fun t : ℝ => F (s, t)) 0) 0 -
        (1 / 2 : ℂ) * deriv (fun s : ℝ => deriv (fun t : ℝ => G (s, t)) 0) 0 := by
  have hinner : (fun s : ℝ => deriv (fun t : ℝ => F (s, t) - (1 / 2 : ℂ) * G (s, t)) 0) =ᶠ[𝓝 0]
      fun s : ℝ => deriv (fun t : ℝ => F (s, t)) 0 -
        (1 / 2 : ℂ) * deriv (fun t : ℝ => G (s, t)) 0 := by
    filter_upwards [eventually_differentiableAt_slice hF, eventually_differentiableAt_slice hG]
      with s hFs hGs
    exact ((hFs.hasDerivAt).sub ((hGs.hasDerivAt).const_mul (1 / 2 : ℂ))).deriv
  rw [hinner.deriv_eq]
  exact (((differentiableAt_deriv_slice hF).hasDerivAt).sub
    (((differentiableAt_deriv_slice hG).hasDerivAt).const_mul (1 / 2 : ℂ))).deriv
theorem eq_zero_of_norm_mul_le_cube {a : ℂ} {K f₀ : ℝ} (hf₀ : 0 < f₀)
    (h : ∀ f : ℝ, 0 < f → f ≤ f₀ → ‖a‖ * f ≤ K * f ^ 3) : a = 0 := by
  have hle : ∀ f : ℝ, 0 < f → f ≤ f₀ → ‖a‖ ≤ K * f ^ 2 := by
    intro f hf hf'
    have h2 : ‖a‖ * f ≤ (K * f ^ 2) * f := by
      have := h f hf hf'
      calc ‖a‖ * f ≤ K * f ^ 3 := this
        _ = (K * f ^ 2) * f := by ring
    exact le_of_mul_le_mul_right h2 hf
  have hlim : Tendsto (fun f : ℝ => K * f ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun f : ℝ => K * f ^ 2) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ f in 𝓝[>] (0 : ℝ), ‖a‖ ≤ K * f ^ 2 := by
    filter_upwards [Ioc_mem_nhdsGT hf₀] with f hf
    exact hle f hf.1 hf.2
  exact norm_le_zero_iff.mp (ge_of_tendsto hlim hev)
theorem expansion_of_even_half_difference {D A₁ A₂ : ℝ → ℂ} {c₁ c₂ a₁ a₂ S₁ S₂ : ℂ}
    {K₁ K₂ f₀ : ℝ}
    (hf₀ : 0 < f₀) (hD : ∀ f, D f = A₁ f - (1 / 2 : ℂ) * A₂ f)
    (h₁ : ∀ f : ℝ, |f| ≤ f₀ →
      ‖A₁ f - c₁ - a₁ * (f : ℂ) - ((1 / 2 * f ^ 2 : ℝ) : ℂ) * S₁‖ ≤ K₁ * |f| ^ 3)
    (h₂ : ∀ f : ℝ, |f| ≤ f₀ →
      ‖A₂ f - c₂ - a₂ * (f : ℂ) - ((1 / 2 * f ^ 2 : ℝ) : ℂ) * S₂‖ ≤ K₂ * |f| ^ 3)
    (heven : ∀ f : ℝ, |f| ≤ f₀ → D (-f) = D f) :
    ∀ f : ℝ, |f| ≤ f₀ →
      ‖D f - (c₁ - (1 / 2 : ℂ) * c₂) - ((1 / 2 * f ^ 2 : ℝ) : ℂ) * (S₁ - (1 / 2 : ℂ) * S₂)‖ ≤
        (K₁ + 1 / 2 * K₂) * |f| ^ 3 := by
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ → ℂ, W = fun f =>
      (A₁ f - c₁ - a₁ * (f : ℂ) - ((1 / 2 * f ^ 2 : ℝ) : ℂ) * S₁) -
        (1 / 2 : ℂ) * (A₂ f - c₂ - a₂ * (f : ℂ) - ((1 / 2 * f ^ 2 : ℝ) : ℂ) * S₂) := ⟨_, rfl⟩
  have hWbound : ∀ f : ℝ, |f| ≤ f₀ → ‖W f‖ ≤ (K₁ + 1 / 2 * K₂) * |f| ^ 3 := by
    intro f hf
    rw [hWdef]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h2]
    have hb₁ := h₁ f hf
    have hb₂ := h₂ f hf
    linarith
  have hW : ∀ f : ℝ, D f - (c₁ - (1 / 2 : ℂ) * c₂) -
      ((1 / 2 * f ^ 2 : ℝ) : ℂ) * (S₁ - (1 / 2 : ℂ) * S₂) =
      (a₁ - (1 / 2 : ℂ) * a₂) * (f : ℂ) + W f := by
    intro f
    rw [hWdef, hD]
    ring
  have ha : a₁ - (1 / 2 : ℂ) * a₂ = 0 := by
    refine eq_zero_of_norm_mul_le_cube (K := K₁ + 1 / 2 * K₂) hf₀ fun f hf' hf'' => ?_
    have hfabs : |f| ≤ f₀ := by rwa [abs_of_pos hf']
    have hnegabs : |-f| ≤ f₀ := by rwa [abs_neg]
    have hplus := hW f
    have hminus := hW (-f)
    rw [heven f hfabs, neg_sq, hplus] at hminus
    have hkey : (2 : ℂ) * ((a₁ - (1 / 2 : ℂ) * a₂) * (f : ℂ)) = W (-f) - W f := by
      push_cast at hminus
      linear_combination hminus
    have hnorm : 2 * (‖a₁ - (1 / 2 : ℂ) * a₂‖ * f) = ‖W (-f) - W f‖ := by
      rw [← hkey, norm_mul, norm_mul]
      simp [abs_of_pos hf']
    have hbplus := hWbound f hfabs
    have hbminus := hWbound (-f) hnegabs
    rw [abs_neg] at hbminus
    rw [abs_of_pos hf'] at hbplus hbminus
    have htri := norm_sub_le (W (-f)) (W f)
    linarith
  intro f hf
  rw [hW f, ha]
  simpa using hWbound f hf
theorem laplacian_and_massive_local_settings (hUnit : UnitLatticeIndexedSpaces)
    (hPositive : ShiftedPositive) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) {z C : ℝ} (hz : 0 < z) (hC : 0 < C)
    (hfam : IsLocallySmoothFamily (vertexPos L) (positiveEdgeInitial (L := L)) C
        (laplacianOp (L := L)) ∧
      IsLocallySmoothFamily (edgePos L) (positiveEdgeInitial (L := L)) C (massiveOp (L := L))) :
    IsLocalExpansionSetting (vertexPos L) (positiveEdgeInitial (L := L)) 3 4 z C
        (laplacianOp (L := L)) ∧
      IsLocalExpansionSetting (edgePos L) (positiveEdgeInitial (L := L)) 12 4 z C
        (massiveOp (L := L)) := by
  obtain ⟨hlow, hangle, -⟩ := hPositive L hL
  obtain ⟨hsite, hbond, htail⟩ := hUnit L hL z C hz hC
  have hsmall : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      (∀ b, |θ b| ≤ min (Real.pi / 8) (z / 192)) →
      IsBoundedBelowBy (addScalar (laplacianOp θ) z) (z / 2) ∧
        IsBoundedBelowBy (addScalar (massiveOp θ) z) (z / 2) := by
    intro θ hθ
    refine hlow z hz θ fun p => (hangle θ _ hθ p).trans ?_
    rcases le_total (Real.pi / 8) (z / 192) with h | h
    · rw [min_eq_left h]
      refine le_min (by linarith) (by linarith)
    · rw [min_eq_right h]
      refine le_min (by linarith) (by linarith)
  have hr : 0 < min (Real.pi / 8) (z / 192) := lt_min (by positivity) (by positivity)
  exact ⟨⟨hsite, htail, hfam.1, _, hr, fun θ hθ => (hsmall θ hθ).1⟩,
    ⟨hbond, htail, hfam.2, _, hr, fun θ hθ => (hsmall θ hθ).2⟩⟩
theorem densityAt_eq_logTrace_sub {L : ℕ} (z : ℝ) (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (x : FullSpace.Vertex L 0 0) :
    densityAt z θ x = logTraceAt (vertexPos L) (laplacianOp (L := L)) z θ x -
      (1 / 2 : ℂ) * logTraceAt (edgePos L) (massiveOp (L := L)) z θ x := rfl
theorem secondDerivative_eq_logTraceHessian_sub (hHessian : LogTraceSecondDerivative.IntegralFormula)
    {L : ℕ} {z C : ℝ} (hz : 0 < z) (hC : 0 < C)
    (hS : IsLocalExpansionSetting (vertexPos L) (positiveEdgeInitial (L := L)) 3 4 z C
      (laplacianOp (L := L)))
    (hB : IsLocalExpansionSetting (edgePos L) (positiveEdgeInitial (L := L)) 12 4 z C
      (massiveOp (L := L)))
    (x : FullSpace.Vertex L 0 0) (m : Fin 4 → ℤ)
    (hm : (x : InfiniteLattice.AmbientSpace) = PeriodicOperators.castVec m)
    (b b' : FullSpace.PositiveEdge (meshAt L 0 0)) :
    secondDerivative z x b b' =
      logTraceHessian (vertexPos L) (laplacianOp (L := L)) z
          (PeriodicOperators.castVec m) b b' -
        (1 / 2 : ℂ) * logTraceHessian (edgePos L) (massiveOp (L := L)) z
          (PeriodicOperators.castVec m) b b' := by
  have h₁ := (hHessian _ _ _ _ _ _ z C _ hz hC hS m b b').1
  have h₂ := (hHessian _ _ _ _ _ _ z C _ hz hC hB m b b').1
  have key := deriv_deriv_slice_sub_half h₁ h₂
  have hfield : ∀ s t : ℝ, (fun c => s * edgeIndicator b c + t * edgeIndicator b' c) =
      twoBondField b b' s t := by
    intro s t
    funext c
    simp only [twoBondField, edgeIndicator, bondIndicator]
    congr!
  simp only [secondDerivative, hfield, densityAt_eq_logTrace_sub, hm]
  simp only [logTraceHessian] at key ⊢
  exact key
theorem vertex_zero_coe (L : ℕ) :
    ((0 : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace) = 0 := rfl
theorem castVec_zero : PeriodicOperators.castVec (0 : Fin 4 → ℤ) = 0 := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.castVec_zero <;> assumption
end DensityExpansion
open DensityExpansion in
theorem quadraticExpansionOfDensity_holds
    (hHessian : LogTraceSecondDerivative.IntegralFormula)
    (hExpansion : LogTraceQuadraticExpansion)
    (hUnit : UnitLatticeIndexedSpaces)
    (hFamily : AbelianOperatorsLocallySmooth)
    (hPositive : ShiftedPositive)
    (hEven : DensityEvenInField) :
    QuadraticExpansionOfDensity := by
  intro z hz
  obtain ⟨C, hC, hfam⟩ := hFamily
  obtain ⟨K₁, hK₁⟩ := hExpansion z C 3 4 hz hC
  obtain ⟨K₂, hK₂⟩ := hExpansion z C 12 4 hz hC
  refine ⟨K₁ + 1 / 2 * K₂, fun L hL ξ hξ f hf => ?_⟩
  obtain ⟨hS, hB⟩ := laplacian_and_massive_local_settings hUnit hPositive hL hz hC (hfam L hL)
  obtain ⟨hlow, -, hscale⟩ := hPositive L hL
  obtain ⟨f₀, hf₀def⟩ : ∃ f₀ : ℝ, f₀ = min (Real.pi / 2) (z / 48) / 4 := ⟨_, rfl⟩
  have hf₀ : 0 < f₀ := by
    rw [hf₀def]
    have : 0 < min (Real.pi / 2) (z / 48) := lt_min (by positivity) (by positivity)
    positivity
  have hf₀le : f₀ ≤ 1 := by
    rw [hf₀def]
    have h₁ : min (Real.pi / 2) (z / 48) ≤ Real.pi / 2 := min_le_left _ _
    have h₂ := Real.pi_lt_four
    linarith
  have hbound : ∀ f : ℝ, |f| ≤ f₀ →
      IsBoundedBelowBy (addScalar (laplacianOp fun b => f * ξ b) z) (z / 2) ∧
        IsBoundedBelowBy (addScalar (massiveOp fun b => f * ξ b) z) (z / 2) := by
    intro f hf'
    refine hlow z hz _ fun p => ?_
    rw [hscale ξ f p, abs_mul]
    have h₁ := hξ.abs_faceAngle_le p
    have h₂ : |f| * |FullSpace.faceAngle ξ p| ≤ |f| * 4 :=
      mul_le_mul_of_nonneg_left h₁ (abs_nonneg f)
    rw [hf₀def] at hf'
    linarith
  have hgrowth : ∀ b, |ξ b| ≤ 2 + TorusMetric.euclidNormVec (positiveEdgeInitial b) := hξ.abs_le
  obtain ⟨hsum₁, a₁, ha₁⟩ := hK₁ _ _ (vertexPos L) (positiveEdgeInitial (L := L))
    (laplacianOp (L := L)) hS ξ hgrowth f₀ hf₀ hf₀le fun f hf' => (hbound f hf').1
  obtain ⟨hsum₂, a₂, ha₂⟩ := hK₂ _ _ (edgePos L) (positiveEdgeInitial (L := L))
    (massiveOp (L := L)) hB ξ hgrowth f₀ hf₀ hf₀le fun f hf' => (hbound f hf').2
  have hsplit : ∀ b b' : FullSpace.PositiveEdge (meshAt L 0 0),
      secondDerivative z (0 : FullSpace.Vertex L 0 0) b b' =
        logTraceHessian (vertexPos L) (laplacianOp (L := L)) z 0 b b' -
          (1 / 2 : ℂ) * logTraceHessian (edgePos L) (massiveOp (L := L)) z 0 b b' := by
    intro b b'
    have h := secondDerivative_eq_logTraceHessian_sub hHessian hz hC hS hB
      (0 : FullSpace.Vertex L 0 0) 0 ((vertex_zero_coe L).trans castVec_zero.symm) b b'
    rwa [castVec_zero] at h
  have hterm : secondDerivativeTerm z ξ = fun p =>
      logTraceHessian (vertexPos L) (laplacianOp (L := L)) z 0 p.1 p.2 * (ξ p.1 : ℂ) *
          (ξ p.2 : ℂ) -
        (1 / 2 : ℂ) * (logTraceHessian (edgePos L) (massiveOp (L := L)) z 0 p.1 p.2 *
          (ξ p.1 : ℂ) * (ξ p.2 : ℂ)) := by
    funext p
    simp only [secondDerivativeTerm, hsplit]
    ring
  have hsummable : Summable (secondDerivativeTerm z ξ) := by
    rw [hterm]
    exact hsum₁.sub (hsum₂.mul_left _)
  have hform : secondDerivativeSum z ξ =
      (∑' p : FullSpace.PositiveEdge (meshAt L 0 0) × FullSpace.PositiveEdge (meshAt L 0 0),
        logTraceHessian (vertexPos L) (laplacianOp (L := L)) z 0 p.1 p.2 *
          (ξ p.1 : ℂ) * (ξ p.2 : ℂ)) -
      (1 / 2 : ℂ) *
        ∑' p : FullSpace.PositiveEdge (meshAt L 0 0) × FullSpace.PositiveEdge (meshAt L 0 0),
          logTraceHessian (edgePos L) (massiveOp (L := L)) z 0 p.1 p.2 *
            (ξ p.1 : ℂ) * (ξ p.2 : ℂ) := by
    rw [secondDerivativeSum, hterm, hsum₁.tsum_sub (hsum₂.mul_left _), tsum_mul_left]
  have hd : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      densityAt z θ (0 : FullSpace.Vertex L 0 0) =
        logTraceAt (vertexPos L) (laplacianOp (L := L)) z θ 0 -
          (1 / 2 : ℂ) * logTraceAt (edgePos L) (massiveOp (L := L)) z θ 0 := by
    intro θ
    have h := densityAt_eq_logTrace_sub z θ (0 : FullSpace.Vertex L 0 0)
    rwa [vertex_zero_coe] at h
  have hexp := expansion_of_even_half_difference
    (D := fun f => densityAt z (fun b => f * ξ b) (0 : FullSpace.Vertex L 0 0))
    (A₁ := fun f => logTraceAt (vertexPos L) (laplacianOp (L := L)) z
      (fun b => f * ξ b) 0)
    (A₂ := fun f => logTraceAt (edgePos L) (massiveOp (L := L)) z
      (fun b => f * ξ b) 0)
    hf₀ (fun f => hd _) ha₁ ha₂ (fun f hf' => by
      have he : (fun b => (-f) * ξ b) = fun b => -(f * ξ b) := funext fun b => neg_mul _ _
      show densityAt z (fun b => (-f) * ξ b) (0 : FullSpace.Vertex L 0 0) = _
      rw [he]
      exact (hEven L hL z hz _ (hbound f hf').2).2 0)
  have hf' : |f| ≤ f₀ := by
    rw [hf₀def]
    linarith
  refine ⟨(hbound f hf').2, hsummable, ?_⟩
  rw [hform, hd (fun _ => 0)]
  exact hexp f hf'
end YangMills.Construction.Tower.AbelianFieldDensity
end

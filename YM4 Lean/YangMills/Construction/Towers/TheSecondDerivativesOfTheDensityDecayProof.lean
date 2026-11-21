import YangMills.Construction.Towers.DecayOfTheResolventOfAKernelOfRangeAtMostTwoProof
import YangMills.Construction.Towers.DecayOfTheSecondDerivativesOfTheLogarithmicDensity
import YangMills.Construction.Towers.TheExpansionOfTheDensityInAFieldOfBoundedAnglesProof
import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensityDecay
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.LocalFamilies
open Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
namespace HessianExpDecay
theorem deriv_deriv_sub_half {F G : ℝ × ℝ → ℂ} (hF : ContDiffAt ℝ 2 F 0) (hG : ContDiffAt ℝ 2 G 0) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => F (s, t) - (1 / 2 : ℂ) * G (s, t)) 0) 0 =
      deriv (fun s : ℝ => deriv (fun t : ℝ => F (s, t)) 0) 0 -
        (1 / 2 : ℂ) * deriv (fun s : ℝ => deriv (fun t : ℝ => G (s, t)) 0) 0 := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.DensityExpansion.deriv_deriv_slice_sub_half <;> assumption
theorem resolventDecayRate_pos {z C : ℝ} (hz : 0 < z) (hC : 0 < C) :
    0 < ResolventDecay.resolventDecayRate z C := by apply _root_.YangMills.Construction.Tower.ResolventDecay.resolventDecayRate_pos <;> assumption
theorem vertex_eq_castVec {L : ℕ} (x : FullSpace.Vertex L 0 0) :
    ∃ m : Fin 4 → ℤ, (x : InfiniteLattice.AmbientSpace) = PeriodicOperators.castVec m := by
  obtain ⟨m, hm⟩ := x.2
  refine ⟨m, funext fun μ => ?_⟩
  rw [hm μ]
  simp [meshAt, PeriodicOperators.castVec]
end HessianExpDecay
open HessianExpDecay in
theorem secondDerivativeExpDecay_holds
    (hHess : LocalFamilies.LogTraceSecondDerivative.IntegralFormula)
    (hDecay : LocalFamilies.LogDensityHessianDecay)
    (hUnit : LocalFamilies.UnitLatticeIndexedSpaces)
    (hFamily : LocalFamilies.AbelianOperatorsLocallySmooth)
    (hPos : ShiftedPositive) :
    SecondDerivativeExpDecay := by
  intro z hz L hL
  obtain ⟨C, hC, hfam⟩ := hFamily
  obtain ⟨K₁, hK₁⟩ := hDecay z C 3 4 hz hC
  obtain ⟨K₂, hK₂⟩ := hDecay z C 12 4 hz hC
  obtain ⟨hlow, hangle, -⟩ := hPos L hL
  obtain ⟨hvert, hedge, hinit⟩ := hUnit L hL z C hz hC
  obtain ⟨hfv, hfe⟩ := hfam L hL
  have hsmall : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      (∀ b, |θ b| ≤ min (Real.pi / 8) (z / 192)) →
      IsBoundedBelowBy (addScalar (laplacianOp θ) z) (z / 2) ∧
        IsBoundedBelowBy (addScalar (massiveOp θ) z) (z / 2) := by
    intro θ hθ
    refine hlow z hz θ fun q => (hangle θ _ hθ q).trans ?_
    rcases le_total (Real.pi / 8) (z / 192) with h | h
    · rw [min_eq_left h]
      refine le_min (by linarith) (by linarith)
    · rw [min_eq_right h]
      refine le_min (by linarith) (by linarith)
  have hr : 0 < min (Real.pi / 8) (z / 192) := lt_min (by positivity) (by positivity)
  have hV : IsLocalExpansionSetting (vertexPos L) (positiveEdgeInitial (L := L)) 3 4 z C
      (laplacianOp (L := L)) :=
    ⟨hvert, hinit, hfv, _, hr, fun θ hθ => (hsmall θ hθ).1⟩
  have hE : IsLocalExpansionSetting (edgePos L) (positiveEdgeInitial (L := L)) 12 4 z C
      (massiveOp (L := L)) :=
    ⟨hedge, hinit, hfe, _, hr, fun θ hθ => (hsmall θ hθ).2⟩
  refine ⟨K₁ + (1 / 2) * K₂, ResolventDecay.resolventDecayRate z C,
    resolventDecayRate_pos hz hC, fun x b b' => ?_⟩
  obtain ⟨m, hm⟩ := vertex_eq_castVec x
  have hsplit : secondDerivative z x b b' =
      logTraceHessian (vertexPos L) (laplacianOp (L := L)) z
          (PeriodicOperators.castVec m) b b' -
        (1 / 2 : ℂ) * logTraceHessian (edgePos L) (massiveOp (L := L)) z
          (PeriodicOperators.castVec m) b b' := by
    have h₁ := (hHess _ _ _ _ _ _ z C _ hz hC hV m b b').1
    have h₂ := (hHess _ _ _ _ _ _ z C _ hz hC hE m b b').1
    have hdens : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, densityAt z θ x =
        logTraceAt (vertexPos L) (laplacianOp (L := L)) z θ (x : InfiniteLattice.AmbientSpace) -
          (1 / 2 : ℂ) * logTraceAt (edgePos L) (massiveOp (L := L)) z θ
            (x : InfiniteLattice.AmbientSpace) := fun _ => rfl
    have hfield : ∀ s t : ℝ, (fun c => s * edgeIndicator b c + t * edgeIndicator b' c) =
        twoBondField b b' s t := by
      intro s t
      funext c
      have hind : ∀ d, edgeIndicator d c = bondIndicator d c := by
        intro d
        by_cases h : c = d <;> simp [edgeIndicator, bondIndicator, h]
      simp only [twoBondField, hind]
    have key := deriv_deriv_sub_half h₁ h₂
    simp only [logTraceHessian]
    rw [← key]
    simp only [secondDerivative, hdens, hfield, hm]
  have hdist : ∀ c : FullSpace.PositiveEdge (meshAt L 0 0),
      TorusMetric.euclidNormVec ((x - c.1.initial : FullSpace.Vertex L 0 0) :
          InfiniteLattice.AmbientSpace) =
        TorusMetric.euclidNormVec (PeriodicOperators.castVec m - positiveEdgeInitial c) := by
    intro c
    rw [← hm]
    rfl
  rw [hsplit, hdist b, hdist b']
  have hb₁ := hK₁ _ _ (vertexPos L) (positiveEdgeInitial (L := L)) (laplacianOp (L := L)) hV m b b'
  have hb₂ := hK₂ _ _ (edgePos L) (positiveEdgeInitial (L := L)) (massiveOp (L := L)) hE m b b'
  set E := Real.exp (-(ResolventDecay.resolventDecayRate z C *
    (TorusMetric.euclidNormVec (PeriodicOperators.castVec m - positiveEdgeInitial b) +
      TorusMetric.euclidNormVec (PeriodicOperators.castVec m - positiveEdgeInitial b'))))
  have hexp : Real.exp (-ResolventDecay.resolventDecayRate z C *
      (TorusMetric.euclidNormVec (PeriodicOperators.castVec m - positiveEdgeInitial b) +
        TorusMetric.euclidNormVec (PeriodicOperators.castVec m - positiveEdgeInitial b'))) = E := by
    simp only [E, neg_mul]
  rw [hexp]
  calc _ ≤ ‖logTraceHessian (vertexPos L) (laplacianOp (L := L)) z
          (PeriodicOperators.castVec m) b b'‖ +
        ‖(1 / 2 : ℂ) * logTraceHessian (edgePos L) (massiveOp (L := L)) z
          (PeriodicOperators.castVec m) b b'‖ := norm_sub_le _ _
    _ ≤ K₁ * E + (1 / 2) * (K₂ * E) := by
        rw [norm_mul]
        have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
        rw [h2]
        linarith
    _ = (K₁ + (1 / 2) * K₂) * E := by ring
end YangMills.Construction.Tower.AbelianFieldDensity
end

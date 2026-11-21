import YangMills.Construction.FourPointCondition.ConditionOnTheStates
import YangMills.Construction.FourPointCondition.FourPointConditionForAnyChoice
import YangMills.Construction.InfiniteLattice.ConnectedFourPointOfAStateMomentsExtensionsAndLimitPoints
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Torus.OneBallLiftAndTransportOfQuadruples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FourPointCondition
open Filter Set TestFunctions PeriodicLattice ResponseInTheExpansion TorusLumps QuadrupleClasses Conventions
private theorem isCompact_closedBallR4 (c : Fin 4 → ℝ) (r : ℝ) : IsCompact (closedBallR4 c r) := by apply _root_.YangMills.SharedProofs.p20989 <;> assumption
open InfiniteLattice.FourPointMoments InfiniteLattice.PeriodicExtensions QuadrupleBalls
private theorem continuous_of_isLipschitzFor {g : (Fin 4 → ℝ) → ℝ} (h : IsLipschitzFor euclidDistR4 g) :
    Continuous g := by apply _root_.YangMills.Construction.TestPairs.continuous_of_isLipschitzFor_r4 <;> assumption
private theorem isBallQuadruple_of_oneBall {d θ : ℝ} (hd : 0 < d) {f : Fin 4 → (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ quadsR4 d θ) (hone : OneBallPropertyR4 d f) : IsBallQuadruple (9 * d) f := by
  obtain ⟨-, ⟨x, hx⟩, hall⟩ := hone
  obtain ⟨hsep, -, hin⟩ := hall x hx
  have hcont : ∀ k, Continuous (f k) := fun k => continuous_of_isLipschitzFor (hf.2.1 k).1
  refine ⟨fun k => (hcont k).measurable, fun k => ?_, ⟨x 0, hin⟩, ⟨d, hd, fun i k hik => (hsep i k hik).1⟩⟩
  have hcs : HasCompactSupport (f k) :=
    (isCompact_closedBallR4 (x 0) (9 * d)).of_isClosed_subset (isClosed_tsupport _) (hin k)
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous (hcont k)
  exact ⟨C, hC⟩
private theorem momentCumulantSum_im (M : Finset (Fin 4) → ℝ) : (momentCumulantSum M).im = 0 := by
  have : momentCumulantSum M =
      ((∑ P : SetPartition.PartitionsFin 4, (-1 : ℝ) ^ (SetPartition.blockCount P - 1) *
        ((SetPartition.blockCount P - 1).factorial : ℝ) * ∏ J ∈ P.parts, M J : ℝ) : ℂ) := by
    simp [momentCumulantSum]
  rw [this, Complex.ofReal_im]
theorem fourPointBoundsInTorusLimitStates_holds (hA : fourPointBoundAtEveryProfile)
    (hW : MomentsExtensionsAndLimits)
    (hB : BallLiftPeriodizationStatement) : fourPointBoundsInTorusLimitStates := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := hA a ha
  refine ⟨max L₀ 13, rt₀, C₀, hrt, fun L hodd hL T hTa hTL hD hC hO hr hCd => ?_⟩
  obtain ⟨y₀, Hy⟩ := H L hodd ((le_max_left _ _).trans hL) T hTa hTL hD hC hO hr hCd
  refine ⟨y₀, fun y hy hR hWil => ?_⟩
  intro θ hθ hθ1 R lam Ca d₀ n₀ hlaws
  obtain ⟨d₄, hd₄, hcl⟩ := Hy y hy hR hWil θ hθ hθ1 R lam Ca d₀ n₀ hlaws
  refine ⟨d₄, hd₄, fun K β hβ hdat ν hν d hd hdeep f hf => ?_⟩
  have hLs : IsAdmissibleBlockingFactor (T.stepParameters y).side := by
    have hLL : (T.stepParameters y).side = L := hTL
    rw [hLL]
    exact ⟨hodd, (le_max_right _ _).trans hL⟩
  have hd0 : 0 < d := hd.1
  obtain ⟨hspace, htori⟩ := hB d θ hd0 ⟨hθ, hθ1⟩
  have hfQ : f ∈ quadsR4 d θ := hspace.1 hf
  have hball : IsBallQuadruple (9 * d) f := isBallQuadruple_of_oneBall hd0 hfQ (hspace.2 f hfQ)
  obtain ⟨hform, -, -, hbounds⟩ := (hW (T.stepParameters y).side K hLs K.pos β hβ).2.2 (9 * d) f (by positivity) hball
  have hkey := hbounds
    (fourPointLowerConst θ * gaugeGroupDim * R.coupling K β d ^ 8 * ∏ i, uniformNorm (f i))
    (fourPointUpperConst * gaugeGroupDim * R.coupling K β d ^ 8 * ∏ i, uniformNorm (f i))
    (40 * d) (by positivity) (fun m hm hside => by
      let s : StandingParameters := ⟨(T.stepParameters y).side, hLs, K, ⟨m, hm⟩⟩
      have h40 : 40 * d ≤ PeriodicLattice.torusSide s.L s.m := (le_max_left _ _).trans hside
      obtain ⟨-, hT, hsup⟩ := (htori s h40).2.1 f hf
      obtain ⟨r, hr, -, hlo, hhi⟩ := hcl s β rfl hdat d hd hdeep _ hT
      have hprod : ∏ i, uniformNorm (TestFunctions.periodize (PeriodicLattice.torusSide s.L s.m) (f i)) =
          ∏ i, uniformNorm (f i) :=
        Finset.prod_congr rfl fun i _ => hsup i
      have hconn : SchwingerFunctions.connectedSchwingerR4 (T.stepParameters y).side m K β f = (r : ℂ) := hr
      rw [hconn, Complex.ofReal_re]
      rw [hprod] at hlo hhi
      exact ⟨hlo, hhi⟩) ν hν
  have him : (fourPointUrsell ν.measure f).im = 0 := by
    rw [hform ν]
    exact momentCumulantSum_im _
  exact ⟨(fourPointUrsell ν.measure f).re, Complex.ext (by simp) (by simpa using him), hkey⟩
end YangMills.Construction.FourPointCondition
end

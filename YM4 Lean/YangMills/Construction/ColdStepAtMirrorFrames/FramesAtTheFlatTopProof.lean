import YangMills.Construction.ColdStepAtMirrorFrames.FlatChainOfNoFlux
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAtTheFlatTop
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionOfTheCurvedChain
import YangMills.Construction.RunningCouplingSlope.LeastActionIsWellAtTheTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceGoesUpALevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
private theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem isSmallCurvature_uniformField {F : BlockFrame} {j : ℕ} {s : ℝ} (hs : 0 < s) :
    IsSmallCurvature s (uniformField F j) := by apply _root_.YangMills.SharedProofs.p8038 <;> assumption
private theorem chartedField_zero {F : BlockFrame} :
    chartedField (fun _ _ => (0 : imaginaryQuaternions)) (uniformField F F.top) = uniformField F F.depth := by apply _root_.YangMills.DeltaSharedProofs.p501102 <;> assumption
private theorem minimizingCoordinates_uniform_eq_zero (hcurved : ConstantCurvatureMinimalAction)
    (hno : ConstantCurvatureChainFlatOfZeroFlux) (hone : MinimizingChartUnique) {a : ℝ} {L : ℕ}
    {c : ColdChainParameters} (ha : 1 ≤ a) (hodd : Odd L) (hc : c.Admissible a L)
    (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (G : BlockFrame) (hG : IsBlockTorus L G) :
    minimizingCoordinates a (finiteCells G) (uniformField G G.top) c.ρA = fun _ _ => 0 := by
  classical
  obtain ⟨hGL, n, h64, hn⟩ := hG
  have hoddG : Odd G.blockSide := hGL ▸ hodd
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  have hρ : 0 < c.ρA := hc.classical.1.1
  have hρ1 : c.ρA ≤ 1 := hc.classical.1.2.1
  obtain ⟨γ₀, hγ₀, hmin₀⟩ := hcurved a L c ha hodd hc
  have hμν : (0 : Fin 4) < 1 := by decide
  have hchain := hmin₀ G X 0 1 n 0 hGL hn h64 hX hμν (by simpa using hγ₀.le)
  have hmin := (hchain.1 G.depth (by simp [BlockFrame.top])).1
  have e₁ : constantCurvatureChain G X 0 1 0 G.top = uniformField G G.top := by
    funext x i
    exact hno G X 0 1 G.top hoddG x i
  have e₂ : constantCurvatureChain G X 0 1 0 G.depth = uniformField G G.depth := by
    funext x i
    exact hno G X 0 1 G.depth hoddG x i
  rw [e₁, e₂] at hmin
  have hz : IsMinimizingChart a (finiteCells G) (uniformField G G.top) c.ρA (fun _ _ => 0) := by
    refine ⟨fun _ _ => rfl, fun _ _ => by simpa using hρ.le, fun W' => ?_⟩
    rw [chartedField_zero]
    exact hmin W'
  have hest := hc.estimates G c.σA (uniformField G G.top) ⟨hGL, n, h64, hn⟩ hσ le_rfl (isSmallCurvature_uniformField hσ)
  have hs2 : ∀ i, 2 ≤ G.extent i := fun i => by rw [hn]; omega
  have hall := (hone G a c.ρA (c.N 0) c.σA _ _ hoddG hs2 hρ1 hest.minimizer hz).1
  have hex : ∃ w', IsMinimizingChart a (finiteCells G) (uniformField G G.top) c.ρA w' := ⟨_, hz⟩
  apply hall
  unfold minimizingCoordinates
  rw [dif_pos hex]
  exact hex.choose_spec
private theorem stepCoordinates_zero {F : BlockFrame} {S : Finset F.Cell} (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable S) x i = 0 := by apply _root_.YangMills.SharedProofs.p7539 <;> assumption
private theorem reflectedField_uniform {F : BlockFrame} (m : ℕ) (y : F.Cell) :
    reflectedField m y (uniformField F F.top) = uniformField (reflectedFrame F m) (reflectedFrame F m).top := by
  funext z i
  unfold reflectedField
  dsimp only
  split_ifs
  · rfl
  · exact inv_one
theorem stepFramesAtUniformTop_holds (hcurved : ConstantCurvatureMinimalAction)
    (hno : ConstantCurvatureChainFlatOfZeroFlux) (hone : MinimizingChartUnique) : stepFramesAtUniformTop := by
  classical
  intro a L c m ha hodd hc hm F star hF
  have hX : ∃ X : imaginaryQuaternions, ‖X‖ = 1 := by
    obtain ⟨q, h0, h1, h2, h3⟩ : ∃ q : Quaternion ℝ, q.re = 0 ∧ q.imI = 1 ∧ q.imJ = 0 ∧ q.imK = 0 :=
      ⟨⟨0, 1, 0, 0⟩, rfl, rfl, rfl, rfl⟩
    refine ⟨⟨q, h0⟩, ?_⟩
    show ‖q‖ = 1
    have h4 : Quaternion.normSq q = 1 := by
      rw [Quaternion.normSq_def', h0, h1, h2, h3]
      norm_num
    have h5 := Quaternion.normSq_eq_norm_mul_self q
    rw [h4] at h5
    nlinarith [norm_nonneg q]
  obtain ⟨X, hX⟩ := hX
  have hz := minimizingCoordinates_uniform_eq_zero hcurved hno hone ha hodd hc X hX
  have hframe : ∀ b : F.Site F.depth × Fin 4, stepFrame star a c.ρA m b (uniformField F F.top) = 0 := by
    intro b
    unfold stepFrame
    split_ifs with hs
    · unfold minimizingBondCoordinate
      rw [hz F hF]
    · unfold bondFrameCoord
      split_ifs with hbig
      · unfold reflectedBondCoord minimizingBondCoordinate
        rw [reflectedField_uniform, hz (reflectedFrame F m) ⟨hF.1, 4 * m, by omega, fun _ => rfl⟩]
      · unfold minimizingBondCoordinate
        rw [hz F hF]
  refine ⟨hframe, ?_⟩
  unfold fieldAboveFrame
  have e : coordsAboveFrame star a c.ρA m (uniformField F F.top) (0 : StepVariable (finiteCells F)) =
      fun _ _ => (0 : imaginaryQuaternions) := by
    funext x i
    unfold coordsAboveFrame
    rw [stepCoordinates_zero, add_zero, hframe]
  rw [e, chartedField_zero]
end YangMills.Construction.ColdStepAtMirrorFrames
end

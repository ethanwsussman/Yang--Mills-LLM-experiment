import YangMills.Construction.PassageToTheLimit.MovingAMirrorIsTranslatingTheImageProof
import YangMills.Construction.TorusOrFourSpace.ClosedBallsAndCompactSetsInBalls
import YangMills.Construction.TorusOrFourSpace.CompactSetsHaveFiniteDiameters
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefined
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
open YangMills.Construction.TorusMetric (euclidNormVec)
namespace CompactSupportDiameters
theorem euclidNormVec_sub_le {a b : Fin 4 → ℝ} {r : ℝ} (hr : 0 ≤ r) (ha : euclidNormVec a ≤ r)
    (hb : euclidNormVec b ≤ r) : euclidNormVec (a - b) ≤ 2 * r := by apply _root_.YangMills.Construction.LimitSpaces.MirrorTranslation.euclidNormVec_sub_le_two_mul <;> assumption
theorem euclidNormVec_le_of_mem_cube {x : Fin 4 → ℝ} {s : ℝ}
    (h : ∀ μ, x μ ∈ Set.Icc (-(s / 2)) (s / 2)) : euclidNormVec x ≤ s := by
  have hs : 0 ≤ s := by
    have h0 := h 0
    linarith [h0.1, h0.2]
  refine Real.sqrt_le_iff.2 ⟨hs, ?_⟩
  have hsq : ∀ μ, x μ ^ 2 ≤ (s / 2) ^ 2 := fun μ => sq_le_sq' (h μ).1 (h μ).2
  rw [Fin.sum_univ_four]
  nlinarith [hsq 0, hsq 1, hsq 2, hsq 3]
end CompactSupportDiameters
open CompactSupportDiameters in
theorem CompactSupportDiameters.finiteDiameters_holds
    (hWell : WellPosedness.WellPosed)
    (hBalls : ClosedBallsCompactAndCover) :
    CompactSupportDiameters.FiniteDiameters := by
  intro P Y
  obtain ⟨-, ⟨hLift, -⟩, hExhaust, hInBall⟩ := hBalls P
  have hEuc : WellPosedness.EuclideanQuotDistEqNorm P :=
    (hWell P Y).2.2.2.2.2.2.2.1
  have hTor : WellPosedness.TorusQuotDistEqEuclid P :=
    (hWell P Y).2.2.2.2.2.2.2.2.1
  have hFin : ∀ S : Set (Y.Pt P), IsCompactQ P Y S → setDiam P Y S < ∞ := by
    intro S hS
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z ∈ S, ∀ z' ∈ S, quotDist P Y z z' ≤ C := by
      cases Y with
      | euclidean =>
        obtain ⟨ρ, -, hρ, hSub⟩ := hExhaust euclidean S hS
        have hNear : ∀ y ∈ S, euclidNormVec y ≤ ρ.toReal := by
          intro y hy
          have hy' := hSub hy
          rw [centredBall, if_neg hρ.ne] at hy'
          have hlt : quotDist P euclidean y (origin P euclidean) < ρ.toReal := hy'
          have heq : quotDist P euclidean y (origin P euclidean) = euclidNormVec y :=
            (hEuc y 0).trans (congrArg euclidNormVec (sub_zero (show Fin 4 → ℝ from y)))
          exact heq.symm.le.trans hlt.le
        refine ⟨2 * ρ.toReal, fun z hz z' hz' => ?_⟩
        exact (hEuc z z').le.trans
          (euclidNormVec_sub_le ENNReal.toReal_nonneg (hNear z hz) (hNear z' hz'))
      | torus =>
        refine ⟨P.side, fun z _ z' _ => ?_⟩
        obtain ⟨x, hx, hcube⟩ := hLift (z - z')
        exact ((hTor z z').2.2 ⟨x, hx, rfl⟩).trans (euclidNormVec_le_of_mem_cube hcube)
    exact lt_of_le_of_lt
      (iSup_le fun z => iSup_le fun hz => iSup_le fun z' => iSup_le fun hz' =>
        ENNReal.ofReal_le_ofReal (hC z hz z' hz'))
      ENNReal.ofReal_lt_top
  refine ⟨hFin, fun n hn f hf => ?_⟩
  have hSupp : ∀ i, IsCompactQ P Y (supportQ P Y (f i)) := hf.2.1
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => setDiam P Y (supportQ P Y (f i))
  have hOne : 1 ≤ supportRadius P Y f := le_max_left _ _
  have hTop : supportRadius P Y f < ∞ :=
    max_lt ENNReal.one_lt_top (lt_of_le_of_lt (iSup_le hi₀) (hFin _ (hSupp i₀)))
  refine ⟨⟨hOne, hTop⟩, fun i => ?_⟩
  have hPos : 0 < (supportRadius P Y f).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hOne)) hTop.ne
  refine hInBall Y _ _ (hSupp i) hPos ?_
  rw [ENNReal.ofReal_toReal hTop.ne]
  exact (le_iSup (fun i => setDiam P Y (supportQ P Y (f i))) i).trans (le_max_right _ _)
end YangMills.Construction.PeriodicSpace

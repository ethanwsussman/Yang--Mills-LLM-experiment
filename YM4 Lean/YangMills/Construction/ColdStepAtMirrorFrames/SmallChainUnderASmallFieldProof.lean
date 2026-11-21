import YangMills.Construction.ColdChainAtEveryLevel.LeastValuesOfAChain
import YangMills.Construction.ColdStepAtMirrorFrames.ComponentsOfAFieldAlongAnElement
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionAcrossFrames
import YangMills.Construction.ColdStepAtMirrorFrames.SmallChainUnderASmallField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
theorem exists_minimizer_near_one_of_succ (hA : MinimalActionTransfer)
    (hV : minimalChainExistenceStatement) {a : ℝ} (ha : 0 ≤ a)
    {L : ℕ} (hL : Odd L) {c : ColdChainParameters} (hc : c.Admissible a L) (hFL : F.blockSide = L)
    (hF : IsLargeCubicTorus F) {k : ℕ}
    (hk : k + 1 ≤ F.top) {m : ℝ} (hm : 0 < m) (hm1 : 5 * m ≤ c.σA) (Y : F.GaugeField (k + 1))
    (hY : ∀ x i, ‖(Y x i : ℍ[ℝ]) - 1‖ ≤ m) :
    ∃ W : F.GaugeField k, blockEnergy a (finiteCells F) k W Y = minimalAction a (finiteCells F) (k + 1) Y ∧
      ∀ x i, ‖(W x i : ℍ[ℝ]) - 1‖ ≤ (5 * c.N 0 + 1) * m := by
  obtain ⟨n, hn, hext⟩ := hF
  have hLpos : 0 < L := hL.pos
  set G : BlockFrame := ⟨L, k, fun i => F.extent i * L ^ (F.top - (k + 1))⟩ with hG
  have hsF : ∀ i, 0 < F.extent i := fun i => by rw [hext i]; omega
  have hsG : ∀ i, 0 < G.extent i := fun i => Nat.mul_pos (hsF i) (pow_pos hLpos _)
  have hP : SharePeriods F G (k + 1) := by
    refine ⟨hFL, hFL ▸ hL, hsF, hsG, hk, le_rfl, ?_⟩
    intro j hj i
    show F.extent i * F.blockSide ^ (F.top - j) = (F.extent i * L ^ (F.top - (k + 1))) * L ^ (k + 1 - j)
    rw [hFL, mul_assoc, ← pow_add]
    congr 2
    omega
  have hT : IsBlockTorus L G := by
    refine ⟨rfl, n * L ^ (F.top - (k + 1)), ?_, fun i => ?_⟩
    · have : 1 ≤ L ^ (F.top - (k + 1)) := Nat.one_le_pow _ _ hLpos
      nlinarith
    · show F.extent i * L ^ (F.top - (k + 1)) = _
      rw [hext i]
  obtain ⟨h1, h2, -, -, -, -, h7, -⟩ := hA F G (k + 1) a hP
  set Y' : G.GaugeField G.top := transferField G Y with hY'
  have hY'near : ∀ x i, ‖(Y' x i : ℍ[ℝ]) - 1‖ ≤ m := fun x i => hY _ _
  have hsmall : IsSmallCurvature (5 * m) Y' := isSmallCurvature_of_near_one Y' (by linarith) hY'near
  obtain ⟨w, hw, -, -⟩ := (hc.estimates G (5 * m) Y' hT (by linarith) hm1 hsmall).minimizer
  have hN : 0 < c.N 0 := hc.positivity.2.2.2.2.2.1 0
  have hwb : ∀ x i, ‖w x i‖ ≤ c.N 0 * (5 * m) := by
    intro x i
    by_cases hb : (x, i) ∈ chordBonds (finiteCells G)
    · exact (hw.2.1 (x, i) hb).trans (min_le_right _ _)
    · rw [hw.1 (x, i) hb, norm_zero]
      positivity
  set W' : G.GaugeField k := chartedField w Y' with hW'
  have hW'near : ∀ x i, ‖(W' x i : ℍ[ℝ]) - 1‖ ≤ (5 * c.N 0 + 1) * m := by
    intro x i
    have := norm_chartedField_sub_one_le w Y' (by positivity) hm.le hwb hY'near x i
    linarith
  refine ⟨transferField F W', ?_, fun x i => hW'near _ _⟩
  have eW : transferField G (transferField F W' : F.GaugeField k) = W' := by
    funext x i
    show W' (transferSite G (transferSite F x)) i = W' x i
    rw [h7 k x (by omega)]
  rw [h2 k (transferField F W') Y (by omega), eW, h1 (k + 1) Y le_rfl]
  obtain ⟨-, -, h3, -⟩ := hV G a (finiteCells G) ha
  obtain ⟨W0, e0, m0⟩ := h3 k Y'
  have l1 := hw.2.2 W0
  have l2 := m0 W'
  exact le_antisymm (by rw [← e0]; exact l1) (by rw [← e0]; exact l2)
theorem smallMinimizingChainExists_of_transfer (hA : MinimalActionTransfer)
    (hV : minimalChainExistenceStatement) : SmallMinimizingChainExists := by
  intro a ha L hL c hc F hFL hF k
  have hN : 0 < c.N 0 := hc.positivity.2.2.2.2.2.1 0
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  induction k with
  | zero =>
    intro _
    refine ⟨1, 1, le_rfl, one_pos, fun m _ _ Y hY => ?_⟩
    refine ⟨Function.update (fun _ _ _ => 1) 0 Y, by simp, ?_, ?_⟩
    · intro j hj x i
      have : j = 0 := by omega
      subst this
      simpa using hY x i
    · simp [minimalAction]
  | succ k ih =>
    intro hk
    obtain ⟨C, m₀, hC, hm₀, hz⟩ := ih (by omega)
    set D : ℝ := 5 * c.N 0 + 1 with hD
    have hD1 : 1 ≤ D := by rw [hD]; linarith
    have hDp : 0 < D := by linarith
    refine ⟨C * D, min (c.σA / 5) (m₀ / D), by nlinarith, lt_min (by positivity) (by positivity), ?_⟩
    intro m hm hm1 Y hY
    have hm2 : 5 * m ≤ c.σA := by
      have := hm1.trans (min_le_left _ _)
      linarith
    have hm3 : D * m ≤ m₀ := by
      have := hm1.trans (min_le_right _ _)
      rwa [le_div_iff₀ hDp, mul_comm] at this
    obtain ⟨W, hW1, hW2⟩ := exists_minimizer_near_one_of_succ hA hV ha hL hc hFL hF hk hm hm2 Y hY
    obtain ⟨Z, hZ1, hZ2, hZ3⟩ := hz (D * m) (by positivity) hm3 W hW2
    have hup : ∀ j, j ≤ k → Function.update Z (k + 1) Y j = Z j := fun j hj =>
      Function.update_of_ne (by omega) _ _
    refine ⟨Function.update Z (k + 1) Y, by simp, ?_, ?_⟩
    · intro j hj x i
      by_cases h : j = k + 1
      · subst h
        simp only [Function.update_self]
        refine (hY x i).trans ?_
        have hCD : 1 ≤ C * D := by nlinarith
        exact le_mul_of_one_le_left hm.le hCD
      · rw [hup j (by omega)]
        have := hZ2 j (by omega) x i
        rw [mul_assoc]
        exact this
    · rw [Finset.sum_range_succ, hup 0 (by omega), Function.update_self, hup k le_rfl, hZ1, ← hW1]
      have e : ∑ j ∈ Finset.range k, ∑ b ∈ innerBonds (finiteCells F) (j + 1),
          blockFit (Function.update Z (k + 1) Y j) (Function.update Z (k + 1) Y (j + 1)) b =
          ∑ j ∈ Finset.range k, ∑ b ∈ innerBonds (finiteCells F) (j + 1), blockFit (Z j) (Z (j + 1)) b := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have := Finset.mem_range.1 hj
        rw [hup j (by omega), hup (j + 1) (by omega)]
      rw [e]
      unfold blockEnergy
      rw [← hZ3]
      ring
end ColdStepAtMirrorFrames
end YangMills.Construction
end

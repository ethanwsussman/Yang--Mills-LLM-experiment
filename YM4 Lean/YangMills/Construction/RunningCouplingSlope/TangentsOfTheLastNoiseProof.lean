import YangMills.Construction.RunningCouplingSlope.MovementsOfAChainAreTriangular
import YangMills.Construction.RunningCouplingSlope.TangentsOfTheLastNoise
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FinalNoiseComplementProof
open Tower
variable {L n k : ℕ}
private theorem levelField_congr_lower {X Y : ChainPoint L n k} (hb : X.fine = Y.fine) :
    ∀ j : ℕ, (∀ i : Fin k, (i : ℕ) < j → X.noise i = Y.noise i) → levelField X j = levelField Y j
  | 0, _ => hb
  | j + 1, h => by
    have e := levelField_congr_lower hb j fun i hi => h i (Nat.lt_succ_of_lt hi)
    simp only [levelField]
    by_cases hj : j < k
    · rw [dif_pos hj, dif_pos hj, e, h ⟨j, hj⟩ (Nat.lt_succ_self j)]
    · rw [dif_neg hj, dif_neg hj, e]
private theorem fibreMove_add_final (X : ChainPoint L n k) (ξ τ : LevelForms L n k)
    (hτ : τ ∈ finalNoiseTangents L n k) : fibreMove X (ξ + τ) = fibreMove X ξ := by
  have hτ' : τ.1 = 0 ∧ ∀ i : Fin k, (i : ℕ) + 1 ≠ k → τ.2 i = 0 := hτ
  have hfine : (expMove (ξ + τ) X).fine = (expMove ξ X).fine := by
    simp [expMove, hτ'.1]
  have hnoise : ∀ i : Fin k, (i : ℕ) + 1 ≠ k →
      (expMove (ξ + τ) X).noise i = (expMove ξ X).noise i := by
    intro i hi
    simp [expMove, hτ'.2 i hi]
  unfold fibreMove
  refine congrArg₂ ChainPoint.mk hfine (funext fun i => funext fun c => ?_)
  split_ifs with h
  · rw [levelField_congr_lower hfine (i : ℕ) fun i' hi' => hnoise i' (by omega)]
  · rw [hnoise i h]
private theorem slotCoords_final_eq_zero {m : ℕ} {τ : LevelForms L n (m + 1)}
    (hτ : τ ∈ finalNoiseTangents L n (m + 1)) : slotCoords τ = 0 := by
  have hτ' : τ.1 = 0 ∧ ∀ i : Fin (m + 1), (i : ℕ) + 1 ≠ m + 1 → τ.2 i = 0 := hτ
  funext e
  obtain ⟨⟨j, hj⟩, x⟩ := e
  have hs : slotOfLevel τ ⟨j, hj⟩ = 0 := by
    cases j with
    | zero => simp [slotOfLevel, hτ'.1]
    | succ j =>
      have h0 := hτ'.2 ⟨j, Nat.lt_of_succ_lt hj⟩ (by simp only []; omega)
      simp only [slotOfLevel]
      rw [h0]
      rfl
  simp only [slotCoords]
  rw [hs]
  have hz : ∀ i, suTwoComponents (0 : Matrices.ComplexMatrix2) i = 0 := fun i => by
    fin_cases i <;> simp [suTwoComponents]
  rcases x with x | x <;> simp [levelCoords, hz]
theorem finalNoiseComplement_of_triangular (hT : TransportCoordsTriangular) :
    FinalNoiseComplement := by
  intro L hL k n hk hn
  refine ⟨fun X ξ τ hτ => fibreMove_add_final X ξ τ hτ, fun X hX => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨N, -, -, hN⟩ := hT L hL m n hn X hX
  have hQ : ∀ τ ∈ finalNoiseTangents L n (m + 1), topDeriv X τ = finalNoise τ :=
    fun τ hτ => hN τ (slotCoords_final_eq_zero hτ)
  refine ⟨fun τ hτ h0 => ?_, fun ξ => ?_⟩
  · have hτ' : τ.1 = 0 ∧ ∀ i : Fin (m + 1), (i : ℕ) + 1 ≠ m + 1 → τ.2 i = 0 := hτ
    have hl : finalNoise τ = 0 := by rw [← hQ τ hτ, h0]
    refine Prod.ext hτ'.1 (funext fun i => ?_)
    by_cases hi : i = Fin.last m
    · subst hi
      exact hl
    · exact hτ'.2 i fun h => hi (Fin.ext (by simpa using h))
  · let v : edgeFormSpace L n (m + 1) (m + 1) := -(topDeriv X ξ)
    let w : (i : Fin (m + 1)) → edgeFormSpace L n (m + 1) (i + 1) := Pi.single (Fin.last m) v
    have hw : w (Fin.last m) = v := Pi.single_eq_same _ _
    have hmem : ((0, w) : LevelForms L n (m + 1)) ∈ finalNoiseTangents L n (m + 1) := by
      refine ⟨rfl, fun i hi => ?_⟩
      exact Pi.single_eq_of_ne (fun h => hi (by rw [h]; simp)) _
    refine ⟨(0, w), hmem, ?_⟩
    rw [map_add, hQ _ hmem]
    have hl : finalNoise ((0, w) : LevelForms L n (m + 1)) = v := hw
    rw [hl]
    exact add_neg_cancel _
end YangMills.Construction.RunningCouplingSlope.FinalNoiseComplementProof
end

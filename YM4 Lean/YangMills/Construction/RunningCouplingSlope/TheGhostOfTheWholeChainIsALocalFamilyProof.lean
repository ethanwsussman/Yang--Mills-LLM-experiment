import YangMills.Construction.RunningCouplingSlope.TheGhostOfTheWholeChainIsALocalFamily
import YangMills.Construction.RunningCouplingSlope.TheGhostOperatorReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TheSaddleOfTheWholeChainIsALocalFamilyProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter Tower
open scoped Topology Matrix.Norms.L2Operator
namespace RunningCouplingSlope.GhostMatrixLocality
section CoordinateValues
variable {L n k : ℕ} [Fintype (LevelFormIndex L n k)]
  [Fintype (Fin 3 × PositiveEdge L n k k)] [Fintype (GhostCoordIndex L n k)]
  [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
private lemma pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private lemma formCoords_eq_zero_off_cell (P : PauliCoordinates L n k) {c : Vertex L n k k}
    {ξ : LevelForms L n k} (h : LevelFormsSupportedInCell c ξ) (p : LevelFormIndex L n k)
    (hp : levelFormIndexCell p ≠ c) : P.formCoords ξ p = 0 := by
  rcases p with p | ⟨i, p⟩
  · have h1 := P.formCoords_base ξ p
    have h2 : (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) p.2.1 = 0 := h.1 p.2 hp
    have h3 : toPauliCoeffs (restrictToPositiveEdges (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2)) p = 0 := by
      show pauliCoeff p.1 ((ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) p.2.1) = 0
      rw [h2, pauliCoeff_zero]
    rw [h3] at h1
    exact_mod_cast h1.symm
  · have h1 := P.formCoords_level ξ i p
    have h2 : (ξ.2 i : Edge L n k (i + 1) → Matrices.ComplexMatrix2) p.2.1 = 0 := h.2 i p.2 hp
    have h3 : toPauliCoeffs (restrictToPositiveEdges (ξ.2 i : Edge L n k (i + 1) → Matrices.ComplexMatrix2)) p = 0 := by
      show pauliCoeff p.1 ((ξ.2 i : Edge L n k (i + 1) → Matrices.ComplexMatrix2) p.2.1) = 0
      rw [h2, pauliCoeff_zero]
    rw [h3] at h1
    exact_mod_cast h1.symm
private lemma tripleCoords_eq_zero_off_cell (P : PauliCoordinates L n k) {c : Vertex L n k k}
    {τ : LevelTriple L n k} (h : TripleSupportedInCell c τ) (i : TripleCoordIndex L n k)
    (hi : tripleCoordIndexCell i ≠ c) : tripleCoords P τ i = 0 := by
  rcases i with p | p | p
  · exact formCoords_eq_zero_off_cell P h.1 p hi
  · exact formCoords_eq_zero_off_cell P h.2.1 p hi
  · have h1 := P.topFormCoords_apply τ.2.2 p
    have h2 : (τ.2.2 : Edge L n k k → Matrices.ComplexMatrix2) p.2.1 = 0 := h.2.2 p.2 hi
    have h3 : toPauliCoeffs (restrictToPositiveEdges (τ.2.2 : Edge L n k k → Matrices.ComplexMatrix2)) p = 0 := by
      show pauliCoeff p.1 ((τ.2.2 : Edge L n k k → Matrices.ComplexMatrix2) p.2.1) = 0
      rw [h2, pauliCoeff_zero]
    rw [h3] at h1
    exact_mod_cast h1.symm
private lemma abs_le_one_of_sum_mul_self_le {ι : Type} [Fintype ι] {f : ι → ℝ} {b : ℝ}
    (h : ∑ m, f m * f m ≤ b) (hb : b ≤ 1) (i : ι) : |f i| ≤ 1 := by apply _root_.YangMills.SharedProofs.p79073 <;> assumption
private lemma abs_tripleCoords_le_one (P : PauliCoordinates L n k) {τ : LevelTriple L n k}
    (h : tripleNormSq τ ≤ 1) (i : TripleCoordIndex L n k) : |tripleCoords P τ i| ≤ 1 := by
  have h1 : levelFormsNormSq τ.1 = ∑ ι, P.formCoords τ.1 ι * P.formCoords τ.1 ι :=
    P.formCoords_pairing _ _
  have h2 : levelFormsNormSq τ.2.1 = ∑ ι, P.formCoords τ.2.1 ι * P.formCoords τ.2.1 ι :=
    P.formCoords_pairing _ _
  have h3 : topFormNormSq τ.2.2 = ∑ ι, P.topFormCoords τ.2.2 ι * P.topFormCoords τ.2.2 ι :=
    P.topFormCoords_pairing _ _
  have n1 : 0 ≤ levelFormsNormSq τ.1 := h1 ▸ Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have n2 : 0 ≤ levelFormsNormSq τ.2.1 := h2 ▸ Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have n3 : 0 ≤ topFormNormSq τ.2.2 := h3 ▸ Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have ht : levelFormsNormSq τ.1 + levelFormsNormSq τ.2.1 + topFormNormSq τ.2.2 ≤ 1 := h
  rcases i with p | p | p
  · exact abs_le_one_of_sum_mul_self_le h1.symm.le (by linarith) p
  · exact abs_le_one_of_sum_mul_self_le h2.symm.le (by linarith) p
  · exact abs_le_one_of_sum_mul_self_le h3.symm.le (by linarith) p
private lemma tripleOfCoords_tripleCoords (P : PauliCoordinates L n k) (τ : LevelTriple L n k) :
    tripleOfCoords P (tripleCoords P τ) = τ := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact P.formCoords.symm_apply_apply _
  · exact P.formCoords.symm_apply_apply _
  · exact P.topFormCoords.symm_apply_apply _
private lemma tripleCoords_add_smul (P : PauliCoordinates L n k) (s t : ℝ) (τ τ' : LevelTriple L n k) :
    tripleCoords P (s • τ + t • τ') =
      s • tripleCoords P τ + t • tripleCoords P τ' := by
  funext i
  rcases i with p | p | p <;> simp [tripleCoords]
end CoordinateValues
theorem ghostOperatorMatrixIsLocal_holds (hloc : HolomorphicFamiliesAreLocal)
    (hghost : GhostOperatorLocallyHolomorphic) :
    GhostOperatorMatrixIsLocal := by
  intro L hL k hk
  obtain ⟨ρ, C, r, hρ, hC, hr, H⟩ := hghost L hL k hk
  obtain ⟨M, θ, hM, hθ, HL⟩ := hloc ρ C r hρ hC hr
  refine ⟨M, θ, hM, hθ, ?_⟩
  filter_upwards [H] with n H
  intro _ _ _ _ _ _ _ _ P c c' τ τ' hc hc' hq hq'
  obtain ⟨G, hF, tie⟩ := H P
  set x := tripleCoords P τ with hx
  set x' := tripleCoords P τ' with hx'
  have ht : Tendsto (fun w : ℝ × ℝ => w.1 • x + w.2 • x') (𝓝 0) (𝓝 0) := by
    have hcont : Continuous fun w : ℝ × ℝ => w.1 • x + w.2 • x' := by fun_prop
    simpa using hcont.tendsto 0
  refine HL tripleCoordIndexCell ghostCoordIndexCell G (fun s t => ghostOperatorMatrix P (s • τ + t • τ'))
    x x' c c' hF (abs_tripleCoords_le_one P hq) (abs_tripleCoords_le_one P hq')
    (tripleCoords_eq_zero_off_cell P hc) (tripleCoords_eq_zero_off_cell P hc') ?_
  filter_upwards [ht.eventually tie] with w hw
  have e : tripleOfCoords P (w.1 • x + w.2 • x') = w.1 • τ + w.2 • τ' := by
    rw [hx, hx', ← tripleCoords_add_smul, tripleOfCoords_tripleCoords]
  rw [e] at hw
  exact hw
end RunningCouplingSlope.GhostMatrixLocality
end YangMills.Construction
end

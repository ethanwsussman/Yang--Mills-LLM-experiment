import YangMills.Construction.PeriodicOperators.SchurTestOnWeightedFunctions
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.SiteAverageOnASide
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.SideVertexSmoothingBound
section
theorem pauliCoeff_pauliSum (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ e, c e • Matrices.ComplexMatrix2.pauliFamily e) = c a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem ofPauliCoeffs_single_apply {σ : Type} [DecidableEq (Fin 3 × σ)] (e : Fin 3) (p q : σ) :
    ofPauliCoeffs (Pi.single (e, p) (1 : ℂ)) q =
      open Classical in if q = p then Matrices.ComplexMatrix2.pauliFamily e else 0 := by
  classical
  unfold ofPauliCoeffs
  by_cases h : q = p
  · subst h
    simp [Pi.single_apply, ite_smul]
  · simp [h]
theorem finsum_ofPauliCoeffs_single {σ : Type} [DecidableEq (Fin 3 × σ)] (S : Set σ) (e : Fin 3)
    (p : σ) :
    ∑ᶠ q ∈ S, ofPauliCoeffs (Pi.single (e, p) (1 : ℂ)) q =
      open Classical in if p ∈ S then Matrices.ComplexMatrix2.pauliFamily e else 0 := by
  classical
  rw [finsum_eq_single _ p]
  · by_cases h : p ∈ S
    · simp [h, ofPauliCoeffs_single_apply]
    · simp [h]
  · intro q hq
    simp [ofPauliCoeffs_single_apply, hq]
end
section
variable {L m k i : ℕ}
theorem pauliCoeff_vertexSmoothing_single [DecidableEq (Fin 3 × Vertex L m k i)] (e' e : Fin 3)
    (y : Vertex L m k (i + 1)) (p : Vertex L m k i) :
    pauliCoeff e' (vertexSmoothing L m k i (ofPauliCoeffs (Pi.single (e, p) (1 : ℂ))) y) =
      open Classical in
      if p ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y ∧ e' = e then
        PeriodicLattice.inverseFourthPowerWeight L else 0 := by
  classical
  show pauliCoeff e' (PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ q ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
      ofPauliCoeffs (Pi.single (e, p) (1 : ℂ)) q) = _
  rw [finsum_ofPauliCoeffs_single]
  by_cases hp : p ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y
  · have h : PeriodicLattice.inverseFourthPowerWeight L • Matrices.ComplexMatrix2.pauliFamily e =
        ∑ a, (if a = e then PeriodicLattice.inverseFourthPowerWeight L else 0) •
          Matrices.ComplexMatrix2.pauliFamily a := by
      simp [ite_smul]
    rw [if_pos hp, h, pauliCoeff_pauliSum]
    simp [hp]
  · have h : PeriodicLattice.inverseFourthPowerWeight L • (0 : Matrices.ComplexMatrix2) =
        ∑ a : Fin 3, (0 : ℂ) • Matrices.ComplexMatrix2.pauliFamily a := by
      simp
    rw [if_neg hp, h, pauliCoeff_pauliSum]
    simp [hp]
theorem kernelOfBasisImages_eq_exists {σ σ' : Type} (f : (σ → Matrices.ComplexMatrix2) →
    σ' → Matrices.ComplexMatrix2) (r : Fin 3 × σ') (s : Fin 3 × σ) :
    ∃ d : DecidableEq (Fin 3 × σ),
      (vertexCoordinate σ).kernelOfBasisImages (vertexCoordinate σ') f r s =
        pauliCoeff r.1 (f (ofPauliCoeffs (@Pi.single _ _ _ d s (1 : ℂ))) r.2) :=
  ⟨_, rfl⟩
theorem smoothingKernel_apply (e' e : Fin 3) (y : Vertex L m k (i + 1)) (p : Vertex L m k i) :
    SideVertexSmoothing.smoothingKernel L m k i (e', y) (e, p) =
      open Classical in
      if p ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y ∧ e' = e then
        PeriodicLattice.inverseFourthPowerWeight L else 0 := by
  obtain ⟨d, h⟩ := kernelOfBasisImages_eq_exists (vertexSmoothing L m k i) (e', y) (e, p)
  exact h.trans (@pauliCoeff_vertexSmoothing_single L m k i d e' e y p)
end
section
variable {L m k i : ℕ}
def blockMajorant (L m k i : ℕ) (y : Vertex L m k (i + 1)) (p : Vertex L m k i) : ℝ :=
  open Classical in
  if p ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y then
    (L : ℝ) ^ (-4 : ℤ) else 0
theorem norm_inverseFourthPowerWeight :
    ‖PeriodicLattice.inverseFourthPowerWeight L‖ = (L : ℝ) ^ (-4 : ℤ) := by
  rw [PeriodicLattice.inverseFourthPowerWeight, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
theorem ncard_sitesInBlock (P : RefinedBlocksPartition L m k 1 (i + 1)) (y : Vertex L m k (i + 1)) :
    (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y).ncard = L ^ 4 := by
  have himage : (fun q : Vertex L m k i => (q : PeriodicLattice.FourTorus L m)) ''
      PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y =
        PeriodicLattice.refinedBlock 1 y := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hp
      exact ⟨⟨p, P.subset_sublattice y hp⟩, hp, rfl⟩
  have h := P.ncard_eq y
  rw [← himage, Set.ncard_image_of_injective _ Subtype.val_injective] at h
  simpa using h
theorem blockMajorant_row (hL : 0 < L) (P : RefinedBlocksPartition L m k 1 (i + 1))
    (y : Vertex L m k (i + 1)) :
    Summable (blockMajorant L m k i y) ∧ ∑' p, blockMajorant L m k i y p ≤ 1 := by
  classical
  have hc := ncard_sitesInBlock P y
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y).Finite :=
    Set.finite_of_ncard_pos (by rw [hc]; positivity)
  have hz : ∀ p ∉ hfin.toFinset, blockMajorant L m k i y p = 0 := by
    intro p hp
    have hp' : p ∉ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y := by
      simpa using hp
    simp [blockMajorant, hp']
  refine ⟨summable_of_ne_finset_zero hz, ?_⟩
  rw [tsum_eq_sum hz]
  have hs : ∀ p ∈ hfin.toFinset, blockMajorant L m k i y p = (L : ℝ) ^ (-4 : ℤ) := by
    intro p hp
    have hp' : p ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y := by
      simpa using hp
    simp [blockMajorant, hp']
  rw [Finset.sum_congr rfl hs, Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hfin, hc]
  apply le_of_eq
  rw [nsmul_eq_mul, zpow_neg]
  push_cast
  norm_cast
  field_simp
theorem blockMajorant_column (P : RefinedBlocksPartition L m k 1 (i + 1)) (p : Vertex L m k i) :
    Summable (fun y => blockMajorant L m k i y p) ∧
      ∑' y, blockMajorant L m k i y p ≤ (L : ℝ) ^ (-4 : ℤ) := by
  classical
  obtain ⟨y₀, hy₀, huniq⟩ : ∃! y : Vertex L m k (i + 1),
      (p : PeriodicLattice.FourTorus L m) ∈ PeriodicLattice.refinedBlock 1 y :=
    P.existsUnique_mem p
  have hz : ∀ y, y ≠ y₀ → blockMajorant L m k i y p = 0 := by
    intro y hy
    have hp : p ∉ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y :=
      fun h => hy (huniq y h)
    simp [blockMajorant, hp]
  refine ⟨summable_of_ne_finset_zero (s := {y₀}) fun y hy => hz y (by simpa using hy), ?_⟩
  rw [tsum_eq_single y₀ hz]
  have hp : p ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y₀ := hy₀
  simp [blockMajorant, hp]
theorem meshAt_weight_le (hL : 0 < L) :
    meshAt L k (i + 1) ^ 4 * (1 * (L : ℝ) ^ (-4 : ℤ)) ≤ (1 : ℝ) ^ 2 * meshAt L k i ^ 4 := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have h : meshAt L k (i + 1) = L * meshAt L k i := by
    unfold meshAt
    rw [show (((i + 1 : ℕ) : ℤ) - (k : ℤ)) = 1 + ((i : ℤ) - (k : ℤ)) by push_cast; ring,
      zpow_add₀ hL', zpow_one]
  have hw : (L : ℝ) ^ (-4 : ℤ) = ((L : ℝ) ^ 4)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  apply le_of_eq
  rw [h, hw, one_pow, one_mul, one_mul, mul_pow]
  field_simp
theorem meshAt_pow_four_pos (hL : 0 < L) (r : ℕ) : 0 < meshAt L k r ^ 4 := by
  unfold meshAt
  positivity
end
theorem claim (hSchur : PeriodicOperators.SchurTest.Holds)
    (hBlocks : BlockPathContourPivotStatement) : SideVertexSmoothing.Claim := by
  intro L hL m k i hm hi
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have P : RefinedBlocksPartition L m k 1 (i + 1) :=
    ((hBlocks L hL k 1 (i + 1) (by omega) (by omega) hi).1 m hm).1
  have h := hSchur.2 (Vertex L m k i) (Vertex L m k (i + 1))
    (SideVertexSmoothing.smoothingKernel L m k i) (blockMajorant L m k i)
    (meshWeight (meshAt L k i)) (meshWeight (meshAt L k (i + 1)))
    (meshAt L k i ^ 4) (meshAt L k (i + 1) ^ 4) 1 ((L : ℝ) ^ (-4 : ℤ)) 1
    (meshAt_pow_four_pos hL0 i) (meshAt_pow_four_pos hL0 (i + 1)) zero_le_one (fun _ => rfl)
    (fun _ => rfl)
    (fun e e' y p he => by
      rw [smoothingKernel_apply, if_neg fun h => he h.2])
    (fun e y p => by
      classical
      rw [smoothingKernel_apply]
      by_cases hp : p ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y
      · simp [blockMajorant, hp, norm_inverseFourthPowerWeight]
      · simp [blockMajorant, hp])
    (blockMajorant_row hL0 P) (blockMajorant_column P) (meshAt_weight_le hL0)
  exact h.2 Set.univ
end YangMills.Construction.Tower.SideVertexSmoothingBound
end

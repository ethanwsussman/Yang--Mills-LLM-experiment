import YangMills.Construction.Towers.CrossingAverageOnTheWholeProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.SiteAverageOnTheWhole
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullVertexSmoothing
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.Quotients (MapsFiniteNorm finiteNormSpace)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
theorem pauliCoeff_sum_smul (w : Fin 3 → ℂ) (c : Fin 3) :
    pauliCoeff c (∑ d, w d • ComplexMatrix2.pauliFamily d) = w c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliCoeff_smul_pauliFamily (z : ℂ) (c c' : Fin 3) :
    pauliCoeff c' (z • ComplexMatrix2.pauliFamily c) = if c' = c then z else 0 := by
  have h : z • ComplexMatrix2.pauliFamily c =
      ∑ d, (if d = c then z else 0) • ComplexMatrix2.pauliFamily d := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hdc
      simp [hdc]
    · simp
  rw [h, pauliCoeff_sum_smul]
theorem pauliCoeff_zero (c' : Fin 3) : pauliCoeff c' (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
section KernelEntries
variable {σ : Type}
theorem ofPauliCoeffs_single_self [DecidableEq (Fin 3 × σ)] (c : Fin 3) (p : σ) :
    ofPauliCoeffs (Pi.single (c, p) (1 : ℂ) : Fin 3 × σ → ℂ) p = ComplexMatrix2.pauliFamily c := by
  unfold ofPauliCoeffs
  rw [Finset.sum_eq_single c]
  · simp
  · intro d _ hdc
    have : (d, p) ≠ (c, p) := fun h => hdc (congrArg Prod.fst h)
    simp [Pi.single_eq_of_ne this]
  · simp
theorem ofPauliCoeffs_single_of_ne [DecidableEq (Fin 3 × σ)] (c : Fin 3) {p q : σ} (h : q ≠ p) :
    ofPauliCoeffs (Pi.single (c, p) (1 : ℂ) : Fin 3 × σ → ℂ) q = 0 := by
  unfold ofPauliCoeffs
  refine Finset.sum_eq_zero fun d _ => ?_
  have : (d, q) ≠ (c, p) := fun e => h (congrArg Prod.snd e)
  simp [Pi.single_eq_of_ne this]
theorem finsum_mem_eq_of_mem {S : Set σ} {p : σ} (hp : p ∈ S) {g : σ → ComplexMatrix2}
    (h : ∀ q, q ≠ p → g q = 0) : ∑ᶠ q ∈ S, g q = g p := by
  rw [finsum_eq_single (fun q => ∑ᶠ (_ : q ∈ S), g q) p]
  · simp [hp]
  · intro q hq
    simp [h q hq]
theorem finsum_mem_eq_zero_of_not_mem {S : Set σ} {p : σ} (hp : p ∉ S) {g : σ → ComplexMatrix2}
    (h : ∀ q, q ≠ p → g q = 0) : ∑ᶠ q ∈ S, g q = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
  by_cases e : q = p
  · subst e
    simp [hp]
  · simp [h q e]
end KernelEntries
variable (L : ℕ) {a a' : ℝ}
theorem pauliCoeff_vertexSmoothing_of_mem
    (inst : DecidableEq (Fin 3 × InfiniteLattice.LatticePoint a')) (c c' : Fin 3)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a')
    (hx : x ∈ FullSpace.cubeVertices L a' y) :
    pauliCoeff c' (FullSpace.vertexSmoothing L (a := a) (a' := a')
        (ofPauliCoeffs (Pi.single (c, x) (1 : ℂ))) y) =
      if c' = c then PeriodicLattice.inverseFourthPowerWeight L else 0 := by
  unfold FullSpace.vertexSmoothing
  rw [finsum_mem_eq_of_mem hx (fun q h => ofPauliCoeffs_single_of_ne c h),
    ofPauliCoeffs_single_self]
  exact pauliCoeff_smul_pauliFamily _ c c'
theorem pauliCoeff_vertexSmoothing_of_not_mem
    (inst : DecidableEq (Fin 3 × InfiniteLattice.LatticePoint a')) (c c' : Fin 3)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a')
    (hx : x ∉ FullSpace.cubeVertices L a' y) :
    pauliCoeff c' (FullSpace.vertexSmoothing L (a := a) (a' := a')
        (ofPauliCoeffs (Pi.single (c, x) (1 : ℂ))) y) = 0 := by
  unfold FullSpace.vertexSmoothing
  rw [finsum_mem_eq_zero_of_not_mem hx (fun q h => ofPauliCoeffs_single_of_ne c h), smul_zero]
  exact pauliCoeff_zero c'
theorem kernel_of_mem (c c' : Fin 3) (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') (hx : x ∈ FullSpace.cubeVertices L a' y) :
    (vertexCoordinate (InfiniteLattice.LatticePoint a')).kernelOfBasisImages
        (vertexCoordinate (InfiniteLattice.LatticePoint a))
        (FullSpace.vertexSmoothing L (a := a) (a' := a')) (c', y) (c, x) =
      if c' = c then PeriodicLattice.inverseFourthPowerWeight L else 0 := by
  unfold PauliComponentsOfSymmetricKernel.kernelOfBasisImages PauliComponentsOfSymmetricKernel.mapOnCoeffs
  dsimp only [vertexCoordinate, toPauliCoeffs]
  exact pauliCoeff_vertexSmoothing_of_mem L _ c c' y x hx
theorem kernel_of_not_mem (c c' : Fin 3) (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') (hx : x ∉ FullSpace.cubeVertices L a' y) :
    (vertexCoordinate (InfiniteLattice.LatticePoint a')).kernelOfBasisImages
        (vertexCoordinate (InfiniteLattice.LatticePoint a))
        (FullSpace.vertexSmoothing L (a := a) (a' := a')) (c', y) (c, x) = 0 := by
  unfold PauliComponentsOfSymmetricKernel.kernelOfBasisImages PauliComponentsOfSymmetricKernel.mapOnCoeffs
  dsimp only [vertexCoordinate, toPauliCoeffs]
  exact pauliCoeff_vertexSmoothing_of_not_mem L _ c c' y x hx
theorem conjugateKernel_of_mem (k i : ℕ) (θ : AmbientSpace) (c c' : Fin 3)
    (y : FullSpace.Vertex L k (i + 1)) (x : FullSpace.Vertex L k i)
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k i) y) :
    conjugateKernel L k i θ (c', y) (c, x) =
      Complex.exp (bilinDot (toComplexVec θ)
          (toComplexVec ((y : AmbientSpace) - (x : AmbientSpace)))) *
        if c' = c then PeriodicLattice.inverseFourthPowerWeight L else 0 := by
  rw [← kernel_of_mem L c c' y x hx]
  rfl
theorem conjugateKernel_of_not_mem (k i : ℕ) (θ : AmbientSpace) (c c' : Fin 3)
    (y : FullSpace.Vertex L k (i + 1)) (x : FullSpace.Vertex L k i)
    (hx : x ∉ FullSpace.cubeVertices L (meshAt L k i) y) :
    conjugateKernel L k i θ (c', y) (c, x) = 0 := by
  have h := kernel_of_not_mem L c c' y x hx
  show Complex.exp _ * (vertexCoordinate _).kernelOfBasisImages (vertexCoordinate _) _ (c', y) (c, x) = 0
  rw [h, mul_zero]
theorem norm_exp_bilinDot_le (θ v : AmbientSpace) {r : ℝ} (hv : ∀ μ, |v μ| ≤ r) :
    ‖Complex.exp (bilinDot (toComplexVec θ) (toComplexVec v))‖ ≤
      Real.exp (TorusMetric.l1NormVec θ * r) := by apply _root_.YangMills.Construction.Tower.CrossingSmoothingBound.norm_exp_bilinDot_le <;> assumption
theorem abs_sub_apply_le_of_mem_cubeVertices {a₀ a₁ : ℝ} (ha₁ : 0 < a₁)
    (y : InfiniteLattice.LatticePoint a₀) (x : InfiniteLattice.LatticePoint a₁)
    (hx : x ∈ FullSpace.cubeVertices L a₁ y) (μ : Fin 4) :
    |((y : AmbientSpace) - (x : AmbientSpace)) μ| ≤ (L : ℝ) * a₁ := by
  obtain ⟨n, hn, hxe⟩ := hx
  have e : ((y : AmbientSpace) - (x : AmbientSpace)) μ = -((n μ : ℝ) * a₁) := by
    rw [hxe]
    simp [Finset.sum_apply, Pi.single_apply]
  rw [e, abs_neg, abs_mul, abs_of_pos ha₁]
  have h1 := hn μ
  rw [pow_one] at h1
  have h2 : |n μ| ≤ (L : ℤ) := by
    have := abs_nonneg (n μ)
    linarith
  have h3 : |(n μ : ℝ)| ≤ (L : ℝ) := by exact_mod_cast h2
  exact mul_le_mul_of_nonneg_right h3 ha₁.le
theorem claim_holds (hS : SchurTest.Holds) (hB : BlockPathContourPivotStatement) : Claim := by
  classical
  intro L hL k i hi θ
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  have hmpos : ∀ m, 0 < meshAt L k m := fun m => zpow_pos hLr _
  have hscale : meshAt L k (i + 1) = (L : ℝ) * meshAt L k i := by
    unfold meshAt
    rw [show ((i + 1 : ℕ) : ℤ) - (k : ℤ) = 1 + ((i : ℤ) - (k : ℤ)) by push_cast; ring,
      zpow_add₀ hLr.ne', zpow_one]
  have hpart : FullSpace.RefinedCubesPartition L k 1 (i + 1) :=
    (hB L hL k 1 (i + 1) (by omega) (by omega) hi).2.1
  have hsub : ∀ y : FullSpace.Vertex L k (i + 1),
      FullSpace.cubeOfOrder L (meshAt L k i) 1 y ⊆
        (InfiniteLattice.latticeSubgroup (meshAt L k i) : Set AmbientSpace) :=
    hpart.subset_sublattice
  have hnc : ∀ y : FullSpace.Vertex L k (i + 1),
      (FullSpace.cubeOfOrder L (meshAt L k i) 1 y).ncard = L ^ (4 * 1) := hpart.ncard_eq
  have hex : ∀ x : FullSpace.Vertex L k i, ∃! y : FullSpace.Vertex L k (i + 1),
      (x : AmbientSpace) ∈ FullSpace.cubeOfOrder L (meshAt L k i) 1 y := hpart.existsUnique_mem
  have himg : ∀ y : FullSpace.Vertex L k (i + 1),
      Subtype.val '' FullSpace.cubeVertices L (meshAt L k i) y =
        FullSpace.cubeOfOrder L (meshAt L k i) 1 y := by
    intro y
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, hsub y hp⟩, hp, rfl⟩
  have hcard : ∀ y : FullSpace.Vertex L k (i + 1),
      (FullSpace.cubeVertices L (meshAt L k i) y).ncard = L ^ 4 := by
    intro y
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg y, hnc y]
  have hfin : ∀ y : FullSpace.Vertex L k (i + 1),
      (FullSpace.cubeVertices L (meshAt L k i) y).Finite := by
    intro y
    refine Set.finite_of_ncard_pos ?_
    rw [hcard y]
    positivity
  have hLW : (L : ℝ) ^ 4 * (L : ℝ) ^ (-4 : ℤ) = 1 := by
    rw [show (-4 : ℤ) = -((4 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
    exact mul_inv_cancel₀ (pow_ne_zero _ hLr.ne')
  have hW : 0 < (L : ℝ) ^ (-4 : ℤ) := zpow_pos hLr _
  obtain ⟨E, hE⟩ : ∃ E, E = TorusMetric.l1NormVec θ * meshAt L k (i + 1) := ⟨_, rfl⟩
  obtain ⟨N, hN1, hN0⟩ : ∃ N : FullSpace.Vertex L k (i + 1) → FullSpace.Vertex L k i → ℝ,
      (∀ y x, x ∈ FullSpace.cubeVertices L (meshAt L k i) y →
        N y x = (L : ℝ) ^ (-4 : ℤ) * Real.exp E) ∧
      (∀ y x, x ∉ FullSpace.cubeVertices L (meshAt L k i) y → N y x = 0) :=
    ⟨fun y x => if x ∈ FullSpace.cubeVertices L (meshAt L k i) y then
        (L : ℝ) ^ (-4 : ℤ) * Real.exp E else 0,
      fun y x hx => if_pos hx, fun y x hx => if_neg hx⟩
  have hoff : ∀ (c c' : Fin 3) (y : FullSpace.Vertex L k (i + 1)) (x : FullSpace.Vertex L k i),
      c' ≠ c → conjugateKernel L k i θ (c', y) (c, x) = 0 := by
    intro c c' y x hcc
    by_cases hx : x ∈ FullSpace.cubeVertices L (meshAt L k i) y
    · rw [conjugateKernel_of_mem L k i θ c c' y x hx, if_neg hcc, mul_zero]
    · exact conjugateKernel_of_not_mem L k i θ c c' y x hx
  have hdiag : ∀ (c : Fin 3) (y : FullSpace.Vertex L k (i + 1)) (x : FullSpace.Vertex L k i),
      ‖conjugateKernel L k i θ (c, y) (c, x)‖ ≤ N y x := by
    intro c y x
    by_cases hx : x ∈ FullSpace.cubeVertices L (meshAt L k i) y
    · rw [hN1 y x hx, conjugateKernel_of_mem L k i θ c c y x hx, if_pos rfl, norm_mul]
      have hw : ‖PeriodicLattice.inverseFourthPowerWeight L‖ = (L : ℝ) ^ (-4 : ℤ) := by
        unfold PeriodicLattice.inverseFourthPowerWeight
        rw [Complex.norm_real, Real.norm_of_nonneg hW.le]
      rw [hw, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ hW.le
      rw [hE]
      exact norm_exp_bilinDot_le θ _ fun μ =>
        (abs_sub_apply_le_of_mem_cubeVertices L (hmpos i) y x hx μ).trans_eq hscale.symm
    · rw [hN0 y x hx, conjugateKernel_of_not_mem L k i θ c c y x hx, norm_zero]
  have hrows : ∀ y, Summable (N y) ∧ ∑' x, N y x ≤ Real.exp E := by
    intro y
    have hs : HasSum (N y) (∑ x ∈ (hfin y).toFinset, N y x) :=
      hasSum_sum_of_ne_finset_zero fun x hx => hN0 y x (by simpa using hx)
    have hv : ∑ x ∈ (hfin y).toFinset, N y x = Real.exp E := by
      rw [Finset.sum_congr rfl fun x hx => hN1 y x (by simpa using hx), Finset.sum_const,
        nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ (hfin y), hcard y]
      push_cast
      rw [← mul_assoc, hLW, one_mul]
    exact ⟨hs.summable, by rw [hs.tsum_eq, hv]⟩
  have hcols : ∀ x, Summable (fun y => N y x) ∧
      ∑' y, N y x ≤ (L : ℝ) ^ (-4 : ℤ) * Real.exp E := by
    intro x
    obtain ⟨y₀, hy₀, huniq⟩ := hex x
    have hs : HasSum (fun y => N y x) (N y₀ x) :=
      hasSum_single y₀ fun y hy => hN0 y x fun h => hy (huniq y h)
    exact ⟨hs.summable, by rw [hs.tsum_eq, hN1 y₀ x hy₀]⟩
  have hprod : meshAt L k (i + 1) ^ 4 *
      (Real.exp E * ((L : ℝ) ^ (-4 : ℤ) * Real.exp E)) ≤
        Real.exp E ^ 2 * meshAt L k i ^ 4 := by
    rw [hscale]
    refine le_of_eq ?_
    calc ((L : ℝ) * meshAt L k i) ^ 4 *
          (Real.exp E * ((L : ℝ) ^ (-4 : ℤ) * Real.exp E))
        = ((L : ℝ) ^ 4 * (L : ℝ) ^ (-4 : ℤ)) * (Real.exp E ^ 2 * meshAt L k i ^ 4) := by ring
      _ = Real.exp E ^ 2 * meshAt L k i ^ 4 := by rw [hLW, one_mul]
  have key := hS.2 (FullSpace.Vertex L k i) (FullSpace.Vertex L k (i + 1)) (conjugateKernel L k i θ) N
    (colourVertices L k i).weightOf (colourVertices L k (i + 1)).weightOf
    (meshAt L k i ^ 4) (meshAt L k (i + 1) ^ 4) (Real.exp E)
    ((L : ℝ) ^ (-4 : ℤ) * Real.exp E) (Real.exp E)
    (pow_pos (hmpos i) 4) (pow_pos (hmpos (i + 1)) 4) (Real.exp_pos _).le
    (fun _ => rfl) (fun _ => rfl) hoff hdiag hrows hcols hprod
  refine ⟨fun f hf => key.1 f hf, (key.2 _).1, ?_⟩
  have h := (key.2 (finiteNormSpace (colourVertices L k i))).2
  rw [hE] at h
  exact h
end YangMills.Construction.Tower.FullVertexSmoothing
end

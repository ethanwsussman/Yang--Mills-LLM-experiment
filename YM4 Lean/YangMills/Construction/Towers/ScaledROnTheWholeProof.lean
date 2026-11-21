import YangMills.Construction.Towers.BlocksOfATowerProof
import YangMills.Construction.PeriodicOperators.SchurTestOnWeightedFunctions
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.ScaledROnTheWhole
import YangMills.Construction.Towers.TransposesOfTheIteratedAveragesOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators (colourVertices expConj applyKernel bilinDot toComplexVec)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace WholeLatticeR
open YangMills.Construction.Tower.FullSpace.TrivialLinearization (baseVerticesOfCube)
open YangMills.Construction.Tower.FullSpace.RescaledConditions (TrivialAverages)
theorem pauliFamily_mem_traceless (i : Fin 3) :
    ComplexMatrix2.pauliFamily i ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliCoeff_sum_smul (c : Fin 3 → ℂ) (i : Fin 3) :
    pauliCoeff i (∑ j, c j • ComplexMatrix2.pauliFamily j) = c i := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem sum_ite_smul_pauliFamily (i : Fin 3) (r : ℂ) :
    ∑ j, (if j = i then r else 0) • ComplexMatrix2.pauliFamily j =
      r • ComplexMatrix2.pauliFamily i := by
  simp [ite_smul]
theorem R_trivial_apply {L k : ℕ} (hM : TrivialAverages L k) (i j : Fin 3)
    (x : FullSpace.Vertex L k 0) (y : FullSpace.Vertex L k k) :
    (FullSpace.rescaledOperators L k fun _ => 1).R (j, y) (i, x) =
      open Classical in if j = i ∧ x ∈ baseVerticesOfCube L k k y then
        ((finestMesh L k ^ 4 : ℝ) : ℂ) else 0 := by
  classical
  set R := (FullSpace.rescaledOperators L k fun _ => 1).R with hR
  set C := baseVerticesOfCube L k k y with hC
  let f : FullSpace.Vertex L k 0 → ComplexMatrix2 := Pi.single x (ComplexMatrix2.pauliFamily i)
  have hf : f ∈ GroupLieProduct.tracelessFunctions (FullSpace.Vertex L k 0) := by
    intro z _
    by_cases h : z = x
    · subst h
      simpa [f] using pauliFamily_mem_traceless i
    · simp [f, h, Pi.single_eq_of_ne]
  have hcoeff : toPauliCoeffs f = Pi.single (i, x) 1 := by
    funext p
    obtain ⟨m, z⟩ := p
    by_cases h : z = x
    · subst h
      have h1 := pauliCoeff_sum_smul (fun j => if j = i then 1 else 0) m
      rw [sum_ite_smul_pauliFamily, one_smul] at h1
      simp only [toPauliCoeffs, f, Pi.single_eq_same]
      rw [h1]
      by_cases hmi : m = i
      · subst hmi
        simp
      · simp [hmi]
    · have h0 : pauliCoeff m (0 : ComplexMatrix2) = 0 := by
        have h1 := pauliCoeff_sum_smul (fun _ => 0) m
        simpa using h1
      simp [toPauliCoeffs, f, h, h0]
  have happly : ∀ m, applyKernel R (toPauliCoeffs f) (m, y) = R (m, y) (i, x) := by
    intro m
    rw [hcoeff]
    show ∑' p, R (m, y) p * (Pi.single (i, x) (1 : ℂ) : _ → ℂ) p = _
    rw [tsum_eq_single (i, x)]
    · simp
    · intro p hp
      simp [Pi.single_eq_of_ne hp]
  have hsum : ∑ᶠ z ∈ C, f z = if x ∈ C then ComplexMatrix2.pauliFamily i else 0 := by
    rw [finsum_eq_single _ x]
    · by_cases hx : x ∈ C <;> simp [hx, f]
    · intro z hz
      simp [f, Pi.single_eq_of_ne hz]
  have h1 := hM.1 f hf y
  rw [hsum] at h1
  have h2 : ∑ m, R (m, y) (i, x) • ComplexMatrix2.pauliFamily m =
      ∑ m, (if m = i ∧ x ∈ C then ((finestMesh L k ^ 4 : ℝ) : ℂ) else 0) •
        ComplexMatrix2.pauliFamily m := by
    have e : ∑ m, R (m, y) (i, x) • ComplexMatrix2.pauliFamily m =
        ofPauliCoeffs (applyKernel R (toPauliCoeffs f)) y := by
      simp only [ofPauliCoeffs, happly]
    rw [e, h1]
    by_cases hx : x ∈ C
    · simp only [hx, if_true, and_true]
      rw [sum_ite_smul_pauliFamily]
      ext p q
      simp
    · simp [hx]
  have h3 := congrArg (pauliCoeff j) h2
  rw [pauliCoeff_sum_smul (fun m => R (m, y) (i, x)),
    pauliCoeff_sum_smul (fun m => if m = i ∧ x ∈ C then _ else _)] at h3
  exact h3
theorem meshAt_pos {L : ℕ} (hL : 0 < L) (k n : ℕ) : 0 < meshAt L k n := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.meshAt_pos <;> assumption
theorem meshAt_self (L k : ℕ) : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
theorem pow_mul_finestMesh {L : ℕ} (hL : 0 < L) (k : ℕ) : (L : ℝ) ^ k * finestMesh L k = 1 := by
  have h : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simp [finestMesh, meshAt, zpow_neg, h]
theorem abs_sub_le_half_of_mem_cube {L k : ℕ} (hL : 0 < L) {x : FullSpace.Vertex L k 0}
    {y : FullSpace.Vertex L k k} (hx : x ∈ baseVerticesOfCube L k k y) (μ : Fin 4) :
    |(y : AmbientSpace) μ - (x : AmbientSpace) μ| ≤ 1 / 2 := by
  obtain ⟨n, hn, hx⟩ := hx
  have e : (x : AmbientSpace) μ = (y : AmbientSpace) μ + (n μ : ℝ) * meshAt L k 0 := by
    have := congrFun hx μ
    simpa [Finset.sum_apply, Pi.single_apply] using this
  have hb : 2 * |(n μ : ℝ)| ≤ (L : ℝ) ^ k - 1 := by
    exact_mod_cast hn μ
  have hη := meshAt_pos hL k 0
  have h1 := pow_mul_finestMesh hL k
  unfold finestMesh at h1
  rw [e, show (y : AmbientSpace) μ - ((y : AmbientSpace) μ + (n μ : ℝ) * meshAt L k 0) =
    -((n μ : ℝ) * meshAt L k 0) by ring, abs_neg, abs_mul, abs_of_pos hη]
  nlinarith
theorem re_bilinDot_le_half_l1NormVec (θ v : AmbientSpace) (hv : ∀ μ, |v μ| ≤ 1 / 2) :
    (bilinDot (toComplexVec θ) (toComplexVec v)).re ≤ TorusMetric.l1NormVec θ / 2 := by
  have e : (bilinDot (toComplexVec θ) (toComplexVec v)).re = ∑ μ, θ μ * v μ := by
    simp [bilinDot, toComplexVec, Complex.mul_re]
  rw [e]
  unfold TorusMetric.l1NormVec
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun μ _ => ?_
  calc θ μ * v μ ≤ |θ μ * v μ| := le_abs_self _
    _ = |θ μ| * |v μ| := abs_mul _ _
    _ ≤ |θ μ| * (1 / 2) := mul_le_mul_of_nonneg_left (hv μ) (abs_nonneg _)
    _ = |θ μ| / 2 := by ring
end WholeLatticeR
theorem WholeLatticeR.conjugateBound_of_schur (hSchur : PeriodicOperators.SchurTest.Holds)
    (hMeans : FullSpace.TrivialFieldMeansCondition)
    (hCubes : BlockPathContourPivotStatement) :
    WholeLatticeR.ConjugateBound := by
  classical
  intro L hL k hk θ
  have hLpos : 0 < L := by have := hL.2; omega
  have hM := hMeans L hL k hk
  have hU : ∀ x : FullSpace.Vertex L k 0, ∃! y : FullSpace.Vertex L k k,
      (x : AmbientSpace) ∈ FullSpace.cubeOfOrder L (meshAt L k 0) k y := by
    have h := (hCubes L hL k k k hk le_rfl le_rfl).2.1.existsUnique_mem
    rw [Nat.sub_self] at h
    exact h
  have hη : 0 < finestMesh L k := WholeLatticeR.meshAt_pos hLpos k 0
  set E : ℝ := TorusMetric.l1NormVec θ / 2 with hE
  have hθ : 0 ≤ TorusMetric.l1NormVec θ :=
    Finset.sum_nonneg fun μ _ => abs_nonneg _
  set C := FullSpace.TrivialLinearization.baseVerticesOfCube L k k with hC
  let K : FullSpace.Vertex L k k → FullSpace.Vertex L k 0 → ℝ := fun y x =>
    if x ∈ C y then finestMesh L k ^ 4 * Real.exp E else 0
  have hrow : ∀ y, HasSum (K y) (Real.exp E) := by
    intro y
    have hcard : ((C y).ncard : ℝ) = (finestMesh L k ^ 4)⁻¹ := hM.2.1 y
    have hfin : (C y).Finite := by
      refine Set.finite_of_ncard_ne_zero fun h0 => ?_
      rw [h0] at hcard
      have : (finestMesh L k ^ 4)⁻¹ ≠ 0 := by positivity
      exact this (by simpa using hcard.symm)
    have h : HasSum (K y) (∑ x ∈ hfin.toFinset, K y x) :=
      hasSum_sum_of_ne_finset_zero fun x hx => by
        have : x ∉ C y := by simpa using hx
        simp [K, this]
    have e : ∑ x ∈ hfin.toFinset, K y x = Real.exp E := by
      have e1 : ∀ x ∈ hfin.toFinset, K y x = finestMesh L k ^ 4 * Real.exp E := by
        intro x hx
        have : x ∈ C y := by simpa using hx
        simp [K, this]
      rw [Finset.sum_congr rfl e1, Finset.sum_const, nsmul_eq_mul,
        ← Set.ncard_eq_toFinset_card _ hfin, hcard]
      field_simp
    rwa [e] at h
  have hcol : ∀ x, HasSum (fun y => K y x) (finestMesh L k ^ 4 * Real.exp E) := by
    intro x
    obtain ⟨y₀, hy₀, huniq⟩ := hU x
    have h := hasSum_single (f := fun y => K y x) y₀ (fun y hy => by
      have : x ∉ C y := fun hxy => hy (huniq y hxy)
      simp [K, this])
    have e : K y₀ x = finestMesh L k ^ 4 * Real.exp E := by
      have : x ∈ C y₀ := hy₀
      simp [K, this]
    simpa [e] using h
  have hoff : ∀ (i i' : Fin 3) (y : FullSpace.Vertex L k k) (x : FullSpace.Vertex L k 0), i' ≠ i →
      WholeLatticeR.conjugatedKernel L k θ (i', y) (i, x) = 0 := by
    intro i i' y x hi
    have := WholeLatticeR.R_trivial_apply hM i i' x y
    simp only [hi, false_and, if_false] at this
    simp only [WholeLatticeR.conjugatedKernel, expConj]
    exact mul_eq_zero_of_right _ this
  have hdiag : ∀ (i : Fin 3) (y : FullSpace.Vertex L k k) (x : FullSpace.Vertex L k 0),
      ‖WholeLatticeR.conjugatedKernel L k θ (i, y) (i, x)‖ ≤ K y x := by
    intro i y x
    have hent := WholeLatticeR.R_trivial_apply hM i i x y
    by_cases hx : x ∈ C y
    · have hx' : x ∈ FullSpace.TrivialLinearization.baseVerticesOfCube L k k y := hx
      simp only [hx', true_and, if_true] at hent
      have hre := WholeLatticeR.re_bilinDot_le_half_l1NormVec θ
        ((y : AmbientSpace) - (x : AmbientSpace))
        (fun μ => WholeLatticeR.abs_sub_le_half_of_mem_cube hLpos hx' μ)
      simp only [WholeLatticeR.conjugatedKernel, expConj]
      rw [hent]
      show ‖Complex.exp (bilinDot (toComplexVec θ)
        (toComplexVec ((y : AmbientSpace) - (x : AmbientSpace)))) *
        ((finestMesh L k ^ 4 : ℝ) : ℂ)‖ ≤ _
      rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      simp only [K, hx, if_true]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre) (by positivity)
    · have hx' : x ∉ FullSpace.TrivialLinearization.baseVerticesOfCube L k k y := hx
      simp only [hx', and_false, if_false] at hent
      simp only [WholeLatticeR.conjugatedKernel, expConj]
      rw [hent]
      simp [K, hx]
  have hAB : meshAt L k k ^ 4 * (Real.exp E * (finestMesh L k ^ 4 * Real.exp E)) ≤
      Real.exp (TorusMetric.l1NormVec θ) ^ 2 * meshAt L k 0 ^ 4 := by
    rw [WholeLatticeR.meshAt_self]
    have e : Real.exp E * Real.exp E = Real.exp (TorusMetric.l1NormVec θ) := by
      rw [← Real.exp_add, hE]
      congr 1
      ring
    have h1 : 1 ≤ Real.exp (TorusMetric.l1NormVec θ) := Real.one_le_exp hθ
    have h4 : 0 < meshAt L k 0 ^ 4 := by
      have := WholeLatticeR.meshAt_pos hLpos k 0
      positivity
    have : finestMesh L k = meshAt L k 0 := rfl
    rw [this]
    calc (1 : ℝ) ^ 4 * (Real.exp E * (meshAt L k 0 ^ 4 * Real.exp E))
        = Real.exp (TorusMetric.l1NormVec θ) * meshAt L k 0 ^ 4 := by
          rw [← e]
          ring
      _ ≤ Real.exp (TorusMetric.l1NormVec θ) ^ 2 * meshAt L k 0 ^ 4 := by
          refine mul_le_mul_of_nonneg_right ?_ h4.le
          nlinarith
  have hT := hSchur.2 (FullSpace.Vertex L k 0) (FullSpace.Vertex L k k)
    (WholeLatticeR.conjugatedKernel L k θ) K
    (colourVertices L k 0).weightOf (colourVertices L k k).weightOf
    (meshAt L k 0 ^ 4) (meshAt L k k ^ 4) (Real.exp E)
    (finestMesh L k ^ 4 * Real.exp E) (Real.exp (TorusMetric.l1NormVec θ))
    (by have := WholeLatticeR.meshAt_pos hLpos k 0; positivity)
    (by have := WholeLatticeR.meshAt_pos hLpos k k; positivity)
    (Real.exp_pos _).le (fun _ => rfl) (fun _ => rfl) hoff hdiag
    (fun y => ⟨(hrow y).summable, (hrow y).tsum_eq.le⟩)
    (fun x => ⟨(hcol x).summable, (hcol x).tsum_eq.le⟩) hAB
  exact ⟨fun f hf => hT.1 f hf,
    (hT.2 _).1, (hT.2 _).2⟩
end YangMills.Construction.Tower
end

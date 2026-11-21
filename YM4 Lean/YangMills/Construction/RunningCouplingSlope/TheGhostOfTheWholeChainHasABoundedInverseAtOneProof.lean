import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreIsSmoothProof
import YangMills.Construction.RunningCouplingSlope.AveragesAlongTheBackgroundAreLocal
import YangMills.Construction.RunningCouplingSlope.BoundedInversesOfLocalMatricesAreLocal
import YangMills.Construction.RunningCouplingSlope.CoordinateFamiliesAreClosedProof
import YangMills.Construction.RunningCouplingSlope.FreeInversesOnASideAreLocal
import YangMills.Construction.RunningCouplingSlope.FreeRootsOnASideAreLocal
import YangMills.Construction.RunningCouplingSlope.MapsOfTheBackgroundGaugeInColours
import YangMills.Construction.RunningCouplingSlope.PlainKernelsGiveTheirMaps
import YangMills.Construction.RunningCouplingSlope.TheGhostOfTheWholeChainHasABoundedInverseAtOne
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
open Matrix Filter
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace GhostInverse
open Tower PeriodicOperators Matrices
section OperatorNorms
variable {ι ι' κ κ' : Type}
private lemma opNorm_transpose_le [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι κ ℂ) : ‖X.transpose‖ ≤ ‖X‖ := by apply _root_.YangMills.SharedProofs.p19594 <;> assumption
private def embeddingMatrix [DecidableEq ι'] (f : ι → ι') : Matrix ι' ι ℂ :=
  Matrix.of fun p i => if p = f i then 1 else 0
private lemma opNorm_embed_le [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'] [DecidableEq ι]
    [DecidableEq ι'] [DecidableEq κ] [DecidableEq κ'] {f : ι → ι'} {g : κ → κ'}
    (hf : Function.Injective f) (hg : Function.Injective g) (X : Matrix ι κ ℂ) :
    ‖embeddingMatrix f * X * (embeddingMatrix g).conjTranspose‖ ≤ ‖X‖ := by apply _root_.YangMills.DeltaSharedProofs.p501444 <;> assumption
private lemma opNorm_fromBlocks_le [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ'] (A : Matrix ι' ι ℂ)
    (B : Matrix ι' κ ℂ) (C : Matrix κ' ι ℂ) (D : Matrix κ' κ ℂ) :
    ‖Matrix.fromBlocks A B C D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
  have e : Matrix.fromBlocks A B C D =
      embeddingMatrix (Sum.inl : ι' → ι' ⊕ κ') * A * (embeddingMatrix (Sum.inl : ι → ι ⊕ κ)).conjTranspose +
      embeddingMatrix (Sum.inl : ι' → ι' ⊕ κ') * B * (embeddingMatrix (Sum.inr : κ → ι ⊕ κ)).conjTranspose +
      embeddingMatrix (Sum.inr : κ' → ι' ⊕ κ') * C * (embeddingMatrix (Sum.inl : ι → ι ⊕ κ)).conjTranspose +
      embeddingMatrix (Sum.inr : κ' → ι' ⊕ κ') * D * (embeddingMatrix (Sum.inr : κ → ι ⊕ κ)).conjTranspose := by
    ext p q
    rcases p with p | p <;> rcases q with q | q <;>
      simp [Matrix.mul_apply, embeddingMatrix, Matrix.conjTranspose_apply]
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
  · exact opNorm_embed_le Sum.inl_injective Sum.inl_injective A
  · exact opNorm_embed_le Sum.inl_injective Sum.inr_injective B
  · exact opNorm_embed_le Sum.inr_injective Sum.inl_injective C
  · exact opNorm_embed_le Sum.inr_injective Sum.inr_injective D
end OperatorNorms
section BlockInverse
variable {S T : Type} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
private def topLeftBlock (Rt : Matrix S T ℂ) (Ru : Matrix T S ℂ) (Yi : Matrix S S ℂ)
    (Ni : Matrix T T ℂ) : Matrix S S ℂ :=
  Yi - Yi * (Rt * (Ni * (Ru * Yi)))
private def topRightBlock (Rt : Matrix S T ℂ) (Yi : Matrix S S ℂ) (Ni : Matrix T T ℂ) : Matrix S T ℂ :=
  Yi * (Rt * Ni)
private def bottomLeftBlock (Rt : Matrix S T ℂ) (R Ru : Matrix T S ℂ) (Yi : Matrix S S ℂ)
    (Ni : Matrix T T ℂ) : Matrix T S ℂ :=
  Ni * (Ru * Yi) + R * topLeftBlock Rt Ru Yi Ni
private def bottomRightBlock (Rt : Matrix S T ℂ) (R : Matrix T S ℂ) (Yi : Matrix S S ℂ)
    (Ni : Matrix T T ℂ) : Matrix T T ℂ :=
  -Ni + R * topRightBlock Rt Yi Ni
private def saddleInverse (c : ℂ) (Rt : Matrix S T ℂ) (R Ru : Matrix T S ℂ) (Yi : Matrix S S ℂ)
    (Ni : Matrix T T ℂ) : Matrix (S ⊕ T) (S ⊕ T) ℂ :=
  fromBlocks (c⁻¹ • topLeftBlock Rt Ru Yi Ni) (topRightBlock Rt Yi Ni)
    ((c⁻¹ * c⁻¹) • bottomLeftBlock Rt R Ru Yi Ni) (c⁻¹ • bottomRightBlock Rt R Yi Ni)
private theorem saddle_mul_saddleInverse {c : ℂ} (hc : c ≠ 0) (Δ : Matrix S S ℂ) (Rt : Matrix S T ℂ)
    (R Ru : Matrix T S ℂ) (Yi : Matrix S S ℂ) (Ni : Matrix T T ℂ)
    (hY : (Δ + Rt * R) * Yi = 1) (hN : Ru * Yi * Rt * Ni = 1) :
    fromBlocks (c • Δ) ((c * c) • Rt) Ru 0 * saddleInverse c Rt R Ru Yi Ni = 1 := by
  have hN' : Ru * (Yi * (Rt * Ni)) = 1 := by simpa only [Matrix.mul_assoc] using hN
  have hY1 : Δ * Yi + Rt * (R * Yi) = 1 := by
    rw [← Matrix.mul_assoc Rt, ← Matrix.add_mul]
    exact hY
  have hY2 : ∀ {V : Type} [Fintype V] (X : Matrix S V ℂ),
      Δ * (Yi * X) + Rt * (R * (Yi * X)) = X := by
    intro V _ X
    rw [← Matrix.mul_assoc Δ, ← Matrix.mul_assoc R, ← Matrix.mul_assoc Rt, ← Matrix.mul_assoc Rt,
      Matrix.mul_assoc Rt R Yi, ← Matrix.add_mul, hY1, Matrix.one_mul]
  have e21 : Ru * topLeftBlock Rt Ru Yi Ni = 0 := by
    have h : Ru * (Yi * (Rt * (Ni * (Ru * Yi)))) = Ru * Yi := by
      calc Ru * (Yi * (Rt * (Ni * (Ru * Yi)))) = (Ru * (Yi * (Rt * Ni))) * (Ru * Yi) := by
            simp only [Matrix.mul_assoc]
        _ = Ru * Yi := by rw [hN', Matrix.one_mul]
    rw [topLeftBlock, Matrix.mul_sub, h, sub_self]
  have e22 : Ru * topRightBlock Rt Yi Ni = 1 := hN'
  have e11 : Δ * topLeftBlock Rt Ru Yi Ni + Rt * bottomLeftBlock Rt R Ru Yi Ni = 1 := by
    have h := hY2 (Rt * (Ni * (Ru * Yi)))
    simp only [bottomLeftBlock, topLeftBlock, Matrix.mul_sub, Matrix.mul_add]
    rw [show Δ * Yi - Δ * (Yi * (Rt * (Ni * (Ru * Yi)))) +
        (Rt * (Ni * (Ru * Yi)) + (Rt * (R * Yi) - Rt * (R * (Yi * (Rt * (Ni * (Ru * Yi))))))) =
        (Δ * Yi + Rt * (R * Yi)) + (Rt * (Ni * (Ru * Yi)) -
          (Δ * (Yi * (Rt * (Ni * (Ru * Yi)))) + Rt * (R * (Yi * (Rt * (Ni * (Ru * Yi))))))) by
      abel]
    rw [hY1, h, sub_self, add_zero]
  have e12 : Δ * topRightBlock Rt Yi Ni + Rt * bottomRightBlock Rt R Yi Ni = 0 := by
    have h := hY2 (Rt * Ni)
    simp only [bottomRightBlock, topRightBlock, Matrix.mul_add, Matrix.mul_neg]
    rw [show Δ * (Yi * (Rt * Ni)) + (-(Rt * Ni) + Rt * (R * (Yi * (Rt * Ni)))) =
        (Δ * (Yi * (Rt * Ni)) + Rt * (R * (Yi * (Rt * Ni)))) - Rt * Ni by abel]
    rw [h, sub_self]
  have c1 : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  have c2 : c⁻¹ * c⁻¹ * (c * c) = 1 := by field_simp
  have c3 : c⁻¹ * (c * c) = c := by field_simp
  rw [saddleInverse, fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [c1, c2, one_smul, one_smul]
    exact e11
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [c3, ← smul_add, e12, smul_zero]
  · simp only [Matrix.mul_smul, Matrix.zero_mul]
    rw [e21]
    simp
  · simp only [Matrix.zero_mul, add_zero]
    exact e22
private def saddleBound (y t d e f u : ℝ) : ℝ :=
  u * (y + y * (t * (d * (e * y)))) + y * (t * d) +
    u * u * (d * (e * y) + f * (y + y * (t * (d * (e * y))))) + u * (d + f * (y * (t * d)))
private theorem opNorm_saddleInverse_le {c : ℂ} {Rt : Matrix S T ℂ} {R Ru : Matrix T S ℂ}
    {Yi : Matrix S S ℂ} {Ni : Matrix T T ℂ} {y t d e f u : ℝ}
    (hy : ‖Yi‖ ≤ y) (ht : ‖Rt‖ ≤ t) (hd : ‖Ni‖ ≤ d) (he : ‖Ru‖ ≤ e) (hf : ‖R‖ ≤ f)
    (hu : ‖c⁻¹‖ ≤ u) : ‖saddleInverse c Rt R Ru Yi Ni‖ ≤ saddleBound y t d e f u := by
  have y0 : 0 ≤ y := (norm_nonneg _).trans hy
  have t0 : 0 ≤ t := (norm_nonneg _).trans ht
  have d0 : 0 ≤ d := (norm_nonneg _).trans hd
  have e0 : 0 ≤ e := (norm_nonneg _).trans he
  have f0 : 0 ≤ f := (norm_nonneg _).trans hf
  have u0 : 0 ≤ u := (norm_nonneg _).trans hu
  have n1 : ‖Ru * Yi‖ ≤ e * y :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul he hy (norm_nonneg _) e0)
  have n2 : ‖Ni * (Ru * Yi)‖ ≤ d * (e * y) :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hd n1 (norm_nonneg _) d0)
  have n3 : ‖Rt * (Ni * (Ru * Yi))‖ ≤ t * (d * (e * y)) :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul ht n2 (norm_nonneg _) t0)
  have n4 : ‖Yi * (Rt * (Ni * (Ru * Yi)))‖ ≤ y * (t * (d * (e * y))) :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hy n3 (norm_nonneg _) y0)
  have nA : ‖topLeftBlock Rt Ru Yi Ni‖ ≤ y + y * (t * (d * (e * y))) :=
    (norm_sub_le _ _).trans (add_le_add hy n4)
  have n5 : ‖Rt * Ni‖ ≤ t * d :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul ht hd (norm_nonneg _) t0)
  have nB : ‖topRightBlock Rt Yi Ni‖ ≤ y * (t * d) :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hy n5 (norm_nonneg _) y0)
  have nC : ‖bottomLeftBlock Rt R Ru Yi Ni‖ ≤ d * (e * y) + f * (y + y * (t * (d * (e * y)))) :=
    (norm_add_le _ _).trans (add_le_add n2 ((Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hf nA (norm_nonneg _) f0)))
  have nD : ‖bottomRightBlock Rt R Yi Ni‖ ≤ d + f * (y * (t * d)) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ((Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hf nB (norm_nonneg _) f0)))
    rwa [norm_neg]
  have hu2 : ‖c⁻¹ * c⁻¹‖ ≤ u * u := by
    rw [norm_mul]
    exact mul_le_mul hu hu (norm_nonneg _) u0
  refine (opNorm_fromBlocks_le _ _ _ _).trans ?_
  rw [saddleBound]
  refine add_le_add (add_le_add (add_le_add ?_ nB) ?_) ?_
  · rw [norm_smul]
    exact mul_le_mul hu nA (norm_nonneg _) u0
  · rw [norm_smul]
    exact mul_le_mul hu2 nC (norm_nonneg _) (mul_nonneg u0 u0)
  · rw [norm_smul]
    exact mul_le_mul hu nD (norm_nonneg _) u0
private theorem saddle_invertible_bounded {c : ℂ} (hc : c ≠ 0) {Δ : Matrix S S ℂ} {Rt : Matrix S T ℂ}
    {R Ru : Matrix T S ℂ} {g : Matrix S S ℂ} {r s t d e f u : ℝ}
    (ug : IsUnit g.det) (uS : IsUnit (g * (Δ + Rt * R) * g).det)
    (uN : IsUnit (Ru * (Δ + Rt * R)⁻¹ * Rt).det) (bg : ‖g‖ ≤ r)
    (bS : ‖(g * (Δ + Rt * R) * g)⁻¹‖ ≤ s) (bN : ‖(Ru * (Δ + Rt * R)⁻¹ * Rt)⁻¹‖ ≤ d)
    (ht : ‖Rt‖ ≤ t) (he : ‖Ru‖ ≤ e) (hf : ‖R‖ ≤ f) (hu : ‖c⁻¹‖ ≤ u) :
    IsUnit (fromBlocks (c • Δ) ((c * c) • Rt) Ru 0).det ∧
      ‖(fromBlocks (c • Δ) ((c * c) • Rt) Ru 0)⁻¹‖ ≤ saddleBound (r * s * r) t d e f u := by
  have r0 : 0 ≤ r := (norm_nonneg _).trans bg
  have s0 : 0 ≤ s := (norm_nonneg _).trans bS
  have uY : IsUnit (Δ + Rt * R).det := by
    have h := uS
    rw [Matrix.det_mul, Matrix.det_mul] at h
    exact (IsUnit.mul_iff.1 (IsUnit.mul_iff.1 h).1).2
  have eYi : (Δ + Rt * R)⁻¹ = g * (g * (Δ + Rt * R) * g)⁻¹ * g := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mul_assoc g,
      Matrix.mul_nonsing_inv _ ug, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ug, Matrix.mul_one]
  have nY : ‖(Δ + Rt * R)⁻¹‖ ≤ r * s * r := by
    rw [eYi]
    refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul ?_ bg (norm_nonneg _) (by positivity))
    exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul bg bS (norm_nonneg _) r0)
  have hm := saddle_mul_saddleInverse hc Δ Rt R Ru _ _ (Matrix.mul_nonsing_inv _ uY)
    (Matrix.mul_nonsing_inv _ uN)
  refine ⟨Matrix.isUnit_det_of_right_inverse hm, ?_⟩
  rw [Matrix.inv_eq_right_inv hm]
  exact opNorm_saddleInverse_le nY ht bN he hf hu
private theorem complexMatrixOfLinearMap_eq {V J : Type} [AddCommGroup V] [Module ℝ V] [Fintype J]
    [DecidableEq J] (Ψ : V ≃ₗ[ℝ] (J → ℝ)) (m : V →ₗ[ℝ] V) (F : Matrix J J ℂ)
    (h : ∀ x κ, ((Ψ (m x) κ : ℝ) : ℂ) = ∑ κ', F κ κ' * ((Ψ x κ' : ℝ) : ℂ)) :
    complexMatrixOfLinearMap Ψ Ψ m = F := by
  ext i j
  have h1 := h (Ψ.symm (Pi.single j 1)) i
  simp only [LinearEquiv.apply_symm_apply] at h1
  have hsum : ∑ x, F i x * (((Pi.single j (1 : ℝ) : J → ℝ) x : ℝ) : ℂ) = F i j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  rw [hsum] at h1
  rw [← h1]
  simp [complexMatrixOfLinearMap, LinearMap.toMatrix'_apply]
end BlockInverse
section UnitPoint
variable {L n k : ℕ}
private theorem ofPauliCoeffs_toPauliCoeffs {σ : Type} {l : σ → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) :
    ofPauliCoeffs (toPauliCoeffs l) = l := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofPauliCoeffs_toPauliCoeffs <;> assumption
private theorem expMove_zero [NeZero L] :
    expMove (0 : LevelForms L n k) (unitPoint L n k) = unitPoint L n k := by apply _root_.YangMills.SharedProofs.p62410 <;> assumption
private theorem twoSourceBackground_zero : twoSourceBackground L n k 0 0 0 = trivialField L n k 0 := by
  funext b
  unfold twoSourceBackground PeriodicLattice.expTwist
  simp [ComplexMatrix2.matExp]
private lemma of_compKernel {a b c : Type} [Fintype b] (T : KernelMatrix b a)
    (S : KernelMatrix c b) : Matrix.of (compKernel T S) = Matrix.of T * Matrix.of S := by
  ext i j
  simp [compKernel, Matrix.mul_apply, tsum_fintype]
abbrev _root_.YangMills.DeltaSharedProofs.p17742 := @of_compKernel
private lemma of_meshTranspose {σ σ' : Type} (K : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')) :
    Matrix.of (meshTranspose (finestMesh L k) (meshAt L k k) K) =
      (unitNormScale L k * unitNormScale L k) • (Matrix.of K).transpose := by
  ext ι ι'
  simp only [meshTranspose, PeriodicOperators.wTranspose, meshWeight, Matrix.of_apply,
    Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, unitNormScale, meshAt]
  simp only [sub_self, zpow_zero, one_pow]
  push_cast
  ring
abbrev _root_.YangMills.SharedProofs.p28483 := @of_meshTranspose
private theorem rescaledRAlong_zero :
    rescaledRAlong L n k 0 0 0 = unitNormScale L k •
      Matrix.of (rescaledOperators L n k (trivialField L n k 0)).R := by
  rw [rescaledRAlong, twoSourceBackground_zero]
private theorem meanRAlong_zero :
    meanRAlong L n k 0 0 0 = unitNormScale L k •
      Matrix.of (meanKernelR L n k (trivialField L n k 0)) := by
  rw [meanRAlong, twoSourceBackground_zero]
private theorem opNorm_le_of_scaled {a b : Type} [Fintype a] [Fintype b] [DecidableEq b]
    {X : Matrix a b ℂ} {w : ℂ} {u η f m : ℝ} (hu0 : 0 < u) (hu' : u * η ^ 2 = 1)
    (hf : f = η ^ 2 * m) (hw : ‖w‖ = u) (h : ‖w • X‖ ≤ m) : ‖X‖ ≤ f := by
  rw [norm_smul, hw] at h
  rw [hf]
  refine le_of_mul_le_mul_left ?_ hu0
  rw [← mul_assoc, hu', one_mul]
  exact h
private theorem yConjugated_zero [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)] :
    yConjugated L n k 0 0 0 = periodicVertexResolventSqrt L n k *
      (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Delta +
        Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Rt *
          Matrix.of (rescaledOperators L n k (trivialField L n k 0)).R) *
      periodicVertexResolventSqrt L n k := by
  rw [yConjugated, twoSourceBackground_zero, ← of_compKernel]
  rfl
private theorem yInv_zero [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
    [DecidableEq (Fin 3 × Vertex L n k 0)] :
    yInv (trivialField L n k 0) =
      (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Delta +
        Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Rt *
          Matrix.of (rescaledOperators L n k (trivialField L n k 0)).R)⁻¹ := by
  rw [← of_compKernel]
  rfl
variable [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
  [Fintype (Fin 3 × PositiveEdge L n k 0)]
  [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
  [DecidableEq (LevelFormIndex L n k)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
  [DecidableEq (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k k)]
private theorem ghostOperatorMatrix_at_unit [NeZero L] (h₅ : BackgroundGaugeMapsInColourCoeffs)
    (h₆ : MeanKernelsRepresent) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hn : 0 < n) (hone : (fun _ => (1 : ComplexMatrix2)) ∈ fieldSpace L n k 0)
    (P : PauliCoordinates L n k) :
    ghostOperatorMatrix P 0 =
      fromBlocks
        (((finestMesh L k ^ 2 : ℝ) : ℂ) •
          Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Delta)
        ((((finestMesh L k ^ 2 : ℝ) : ℂ) * ((finestMesh L k ^ 2 : ℝ) : ℂ)) •
          Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Rt)
        (Matrix.of (meanKernelR L n k (trivialField L n k 0))) 0 := by
  classical
  have e₂ := h₅ L hL k n hk hn
  have e₃ := h₆ L hL k n hk hn
  unfold EventuallyNearIdentity at e₂ e₃
  obtain ⟨-, -, fRt, fΔ⟩ := e₂.self_of_nhdsWithin hone
  obtain ⟨-, -, fR, -, fre, -, flin⟩ := e₃.self_of_nhdsWithin hone
  have hreal : ∀ l : vertexFunctionSpace L n k 0,
      composedCubeAverage (quietPoint (fun _ => 1)) k l ∈ vertexFunctionSpace L n k k :=
    fun l y _ => fre k le_rfl l (fun x => l.2 x (Set.mem_univ x)) y
  have hsl : ∀ l : vertexFunctionSpace L n k 0, ∀ x,
      (l : Vertex L n k 0 → ComplexMatrix2) x ∈ ComplexMatrix2.traceless := fun l x =>
    (l.2 x (Set.mem_univ x)).2
  let T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k :=
    { toFun := fun l => ⟨composedCubeAverage (quietPoint (fun _ => 1)) k l, hreal l⟩
      map_add' := fun l l' => by
        apply Subtype.ext
        have := flin l l' (hsl l) (hsl l') 1
        simpa using this
      map_smul' := fun r l => by
        apply Subtype.ext
        have h0 := flin 0 0 (fun _ => ComplexMatrix2.traceless.zero_mem)
          (fun _ => ComplexMatrix2.traceless.zero_mem) 1
        have hz : composedCubeAverage (quietPoint (fun _ => 1)) k
            (0 : Vertex L n k 0 → ComplexMatrix2) = 0 := by
          simpa using h0
        have := flin l 0 (hsl l) (fun _ => ComplexMatrix2.traceless.zero_mem) (r : ℂ)
        simp only [add_zero, hz] at this
        simpa [Complex.coe_smul] using this }
  have hT : ∀ l : vertexFunctionSpace L n k 0,
      (composedCubeAverageLinear (quietPoint (fun _ => 1)) l : Vertex L n k k → ComplexMatrix2) =
        composedCubeAverage (quietPoint (fun _ => 1)) k l :=
    Classical.epsilon_spec
      (p := fun T' : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k =>
      ∀ x : vertexFunctionSpace L n k 0,
        (T' x : Vertex L n k k → ComplexMatrix2) = composedCubeAverage (quietPoint (fun _ => 1)) k x)
      ⟨T, fun _ => rfl⟩
  have cRu : ∀ (l : vertexFunctionSpace L n k 0) y,
      toPauliCoeffs (composedCubeAverageLinear (quietPoint (fun _ => 1)) l :
          Vertex L n k k → ComplexMatrix2) y =
        ∑ x, meanKernelR L n k (fun _ => 1) y x *
          toPauliCoeffs (l : Vertex L n k 0 → ComplexMatrix2) x := by
    intro l y
    have g := congrFun (fR (toPauliCoeffs (l : Vertex L n k 0 → ComplexMatrix2))).2 y
    change applyKernel (meanKernelR L n k (fun _ => 1))
        (toPauliCoeffs (l : Vertex L n k 0 → ComplexMatrix2)) y =
      toPauliCoeffs (composedCubeAverage (quietPoint (fun _ => 1)) k
        (ofPauliCoeffs (toPauliCoeffs (l : Vertex L n k 0 → ComplexMatrix2)))) y at g
    rw [ofPauliCoeffs_toPauliCoeffs (hsl l), ← hT l] at g
    simp only [applyKernel, tsum_fintype] at g
    exact g.symm
  have add0 : ∀ (a b : vertexFunctionSpace L n k 0) ι,
      toPauliCoeffs ((a + b : vertexFunctionSpace L n k 0) : Vertex L n k 0 → ComplexMatrix2) ι =
        toPauliCoeffs (a : Vertex L n k 0 → ComplexMatrix2) ι +
          toPauliCoeffs (b : Vertex L n k 0 → ComplexMatrix2) ι := by
    intro a b ι
    have e : ((a + b, 0) : vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k) =
        (a, 0) + (b, 0) := by simp
    have h1 := P.ghostCoords_fst (a + b, 0) ι
    have h2 := P.ghostCoords_fst (a, 0) ι
    have h3 := P.ghostCoords_fst (b, 0) ι
    simp only at h1 h2 h3
    rw [h1, h2, h3, e, map_add, Pi.add_apply, Complex.ofReal_add]
  have hg : ghostOperatorMatrix P 0 =
      complexMatrixOfLinearMap P.ghostCoords P.ghostCoords (ghostBlockOperator (unitPoint L n k)) := by
    unfold ghostOperatorMatrix
    rw [Prod.fst_zero, expMove_zero]
  rw [hg]
  refine complexMatrixOfLinearMap_eq P.ghostCoords _ _ fun z κ => ?_
  rw [Fintype.sum_sum_type]
  rcases κ with x | y
  · have e : (ghostBlockOperator (unitPoint L n k) z).1 =
        covDiffRealTranspose L n k (fun _ => 1)
            (covDiffLinear L n k (fun _ => 1) z.1) +
          iterAverageRealTranspose L n k (fun _ => 1) z.2 := rfl
    rw [← P.ghostCoords_fst, e, add0, fΔ z.1 x, fRt z.2 x]
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [P.ghostCoords_fst z j]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [P.ghostCoords_snd z j]
      push_cast
      ring
  · have e : (ghostBlockOperator (unitPoint L n k) z).2 =
        composedCubeAverageLinear (quietPoint (fun _ => 1)) z.1 := rfl
    rw [← P.ghostCoords_snd, e, cRu z.1 y]
    simp only [fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.of_apply, Matrix.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [P.ghostCoords_fst z j]
end UnitPoint
end GhostInverse
open GhostInverse Tower PeriodicOperators Matrices in
theorem ghostOperatorMatrixInverseBounded_of_locality
    (h₁ : FreeInversesLocal) (h₂ : PeriodicResolventSqrtsLocal)
    (h₃ : BackgroundMeansAreLocal)
    (h₄ : LocalMatricesBoundedAndInverseLocal)
    (h₅ : BackgroundGaugeMapsInColourCoeffs) (h₆ : MeanKernelsRepresent)
    (h₇ : UnitPointIsMinimizer) :
    GhostOperatorMatrixInverseBounded := by
  intro L hL k hk
  classical
  have hLpos : 0 < L := by
    have := hL.2
    omega
  haveI : NeZero L := ⟨hLpos.ne'⟩
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  obtain ⟨M₁, θ₁, hM₁, hθ₁, H₁⟩ := h₁ L hL
  obtain ⟨M₂, θ₂, hM₂, hθ₂, H₂⟩ := h₂ L hL
  obtain ⟨M₃, θ₃, hM₃, hθ₃, H₃⟩ := h₃ 1 one_pos L hL
  obtain ⟨S₁, hS₁, B₁⟩ := h₄.1 θ₁ hθ₁
  obtain ⟨S₂, hS₂, B₂⟩ := h₄.1 θ₂ hθ₂
  obtain ⟨S₃, hS₃, B₃⟩ := h₄.1 θ₃ hθ₃
  obtain ⟨n₁, G₁⟩ := H₁ k hk
  obtain ⟨n₂, G₂⟩ := H₂ k hk
  obtain ⟨n₃, G₃⟩ := H₃ k hk
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = finestMesh L k := ⟨_, rfl⟩
  have heta : 0 < η := hη ▸ zpow_pos hLR _
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (η ^ 2)⁻¹ := ⟨_, rfl⟩
  have hu0 : 0 < u := hu ▸ inv_pos.2 (pow_pos heta 2)
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = S₂ * M₂ * (S₁ * M₁) * (S₂ * M₂) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℝ, f = η ^ 2 * (S₃ * M₃) := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; positivity
  have hf0 : 0 < f := by rw [hf]; positivity
  have hd0 : 0 < S₁ * M₁ := by positivity
  have hb : 0 ≤ saddleBound y (u * u * f) (S₁ * M₁) f f u := by
    unfold saddleBound
    positivity
  refine ⟨saddleBound y (u * u * f) (S₁ * M₁) f f u + 1, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop (max (max n₁ n₂) (max n₃ 1))] with n hn
  have hn₁ : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn₃ : n₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hpos : 0 < n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  intro iW dW iB dB iG dG iS iT P
  haveI : Fintype (Fin 3 × PositiveEdge L n k 0) :=
    Fintype.ofInjective (Sum.inl : _ → LevelFormIndex L n k) Sum.inl_injective
  haveI : Finite (Vertex L n k 0) :=
    Finite.of_injective (fun x : Vertex L n k 0 => ((0 : Fin 3), x)) fun _ _ h =>
      congrArg Prod.snd h
  haveI : Finite (Face L n k 0) :=
    Finite.of_injective
      (fun p : Face L n k 0 => (p.origin, p.firstAxis, p.secondAxis)) fun _ _ h =>
      PeriodicLattice.Plaquette.ext (congrArg Prod.fst h) (congrArg (fun y => y.2.1) h)
        (congrArg (fun y => y.2.2) h)
  haveI : Fintype (Fin 3 × Face L n k 0) := Fintype.ofFinite _
  obtain ⟨dS⟩ : Nonempty (DecidableEq (Fin 3 × Vertex L n k 0)) := ⟨Classical.decEq _⟩
  obtain ⟨dT⟩ : Nonempty (DecidableEq (Fin 3 × Vertex L n k k)) := ⟨Classical.decEq _⟩
  obtain rfl : iG = (by clear P iG; infer_instance) := Subsingleton.elim _ _
  obtain rfl : dG = (by clear dG; infer_instance) := Subsingleton.elim _ _
  have hone : (fun _ => (1 : ComplexMatrix2)) ∈ fieldSpace L n k 0 :=
    (h₇ 1 one_pos L hL k n hk hpos).2.compact.2 0 (Nat.zero_le _)
  have hF := ghostOperatorMatrix_at_unit h₅ h₆ hL hk hpos hone P
  obtain ⟨-, -, uS, lS, -, -, -, -, uN, lN⟩ := G₁ n hn₁ hpos
  obtain ⟨-, -, -, ug, -, lg, -⟩ := G₂ n hn₂ hpos
  obtain ⟨-, -, lR, lRu, -⟩ := G₃ n hn₃ hpos 0
  have bS := B₁ L n k _ _ _ _ _ M₁ hL hpos hM₁.le lS
  have bN := B₁ L n k _ _ _ _ _ M₁ hL hpos hM₁.le lN
  have bg := B₂ L n k _ _ _ _ _ M₂ hL hpos hM₂.le lg
  have bR := B₃ L n k _ _ _ _ _ M₃ hL hpos hM₃.le lR.value_local
  have bRu := B₃ L n k _ _ _ _ _ M₃ hL hpos hM₃.le lRu.value_local
  have hnu : ‖unitNormScale L k‖ = u := by
    rw [hu, hη, unitNormScale, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    exact inv_pos.2 (pow_pos (hη ▸ heta) 2)
  have hu' : u * η ^ 2 = 1 := by
    rw [hu]
    exact inv_mul_cancel₀ (pow_pos heta 2).ne'
  have nR := opNorm_le_of_scaled hu0 hu' hf hnu (rescaledRAlong_zero ▸ bR)
  have nRu := opNorm_le_of_scaled hu0 hu' hf hnu (meanRAlong_zero ▸ bRu)
  have nRt : ‖Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Rt‖ ≤ u * u * f := by
    have e : Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Rt =
        (unitNormScale L k * unitNormScale L k) •
          (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).R).transpose :=
      of_meshTranspose _
    rw [e, norm_smul, norm_mul, hnu]
    exact mul_le_mul_of_nonneg_left ((opNorm_transpose_le _).trans nR) (by positivity)
  have hc : (((finestMesh L k ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    rw [← hη]
    exact_mod_cast (pow_pos heta 2).ne'
  have hcn : ‖(((finestMesh L k ^ 2 : ℝ) : ℂ))⁻¹‖ ≤ u := by
    rw [hu, ← hη, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos heta 2)]
  rw [yConjugated_zero] at uS bS
  rw [yInv_zero] at uN bN
  have hB := saddle_invertible_bounded hc ug uS uN bg bS bN nRt nRu nR hcn
  rw [hF]
  exact ⟨hB.1, hB.2.trans (by rw [hy]; linarith)⟩
end YangMills.Construction.RunningCouplingSlope
end

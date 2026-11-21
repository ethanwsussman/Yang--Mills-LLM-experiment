import YangMills.Construction.PeriodicOperators.ActionAndProductsOnTheTorusProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.ProductOfPeriodicOperators
import YangMills.Construction.RunningCouplingSlope.FreePictureReadsOnASide
import YangMills.Construction.RunningCouplingSlope.FreeRootsOnASideAreLocal
import YangMills.Construction.RunningCouplingSlope.RootsReadOnASide
import YangMills.Construction.Towers.TheRootsOfTheFreePropagatorsOnTheStrip
import YangMills.Construction.Towers.TransposesAndRelationsOfTheScaledPicture
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
open Tower.CriticalBranchResponse
open Tower.FreeStrip
open Tower.FreeResolvents
open LocalKernels.Periodisation (periodSide)
private theorem exists_decayRate {I I' : PeriodicData} {T : I'.Carrier → I.Carrier → ℂ}
    (h : IsPeriodicKernel I I' T) : ∃ δ, IsDecayRate I I' T δ := by apply _root_.YangMills.Construction.PeriodicOperators.TorusAction.exists_decayRate <;> assumption
private theorem compKernel_periodic_of_finiteRange (hComp : CompClaim)
    {I I' I'' : PeriodicData} (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hI'' : IsPeriodic I'') {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : FreeOperators.HasFiniteRangeEveryRate I I' T) (hS : IsPeriodicKernel I'' I S) :
    IsPeriodicKernel I'' I' (compKernel T S) := by
  obtain ⟨δ, hδ⟩ := exists_decayRate hS
  exact (hComp I I' I'' hI hI' hI'' T S δ hT.1 (hT.2.2 δ hδ.1) hS hδ).comp_periodic.2
private theorem compKernel_matrix_eq_mul {J J' J'' : Type} [Fintype J] (A : Matrix J' J ℂ)
    (B : Matrix J J'' ℂ) : compKernel (fun u v => A u v) (fun u v => B u v) = A * B := by
  funext u v
  simp [compKernel, tsum_fintype, Matrix.mul_apply]
private theorem periodization_symm {I : PeriodicData} (hI : IsPeriodic I)
    (T : I.Carrier → I.Carrier → ℂ) (hinv : IsShiftInvariant I I T) (hsym : ∀ a b, T a b = T b a)
    (s : ℕ) (x' x : I.Carrier) : periodization I I T s x x' = periodization I I T s x' x := by
  unfold periodization
  rw [← (Equiv.neg (Fin 4 → ℤ)).tsum_eq]
  refine tsum_congr fun m => ?_
  have h := hinv (s • m) (I.translate (s • (-m)) x') x
  rw [← hI.translate_add] at h
  simp only [Equiv.neg_apply]
  rw [hsym, ← h]
  simp [hI.translate_zero]
private theorem matrix_transpose_eq_of_symm {I : PeriodicData} (hI : IsPeriodic I) {J : Type}
    {q : I.Carrier → J} (hq : Function.Surjective q) (T : I.Carrier → I.Carrier → ℂ)
    (hinv : IsShiftInvariant I I T) (hsym : ∀ a b, T a b = T b a) (s : ℕ) (M : Matrix J J ℂ)
    (hM : ∀ x' x, M (q x') (q x) = periodization I I T s x' x) : M.transpose = M := by
  ext u v
  obtain ⟨x', rfl⟩ := hq u
  obtain ⟨x, rfl⟩ := hq v
  rw [Matrix.transpose_apply, hM, hM, periodization_symm hI T hinv hsym]
private theorem symm_of_kernelTranspose_eq {I : PeriodicData} {w : ℝ} (hw : 0 < w)
    (hwI : ∀ x, I.weightOf x = w) (T : I.Carrier → I.Carrier → ℂ)
    (h : kernelTranspose I I T = T) (a b : I.Carrier) : T a b = T b a := by
  have e := congrFun (congrFun h a) b
  simp only [kernelTranspose, wTranspose, hwI] at e
  rw [div_self hw.ne'] at e
  simpa using e.symm
private theorem det_isUnit_of_left_inverse {I : PeriodicData} {J : Type} [Fintype J]
    [DecidableEq J] {q : I.Carrier → J} (hq : Function.Surjective q) (A B : Matrix J J ℂ)
    (h : ∀ x' x, compKernel (fun u v => A u v) (fun u v => B u v) (q x') (q x) =
      if q x' = q x then 1 else 0) : IsUnit (Matrix.det B) := by
  have e : A * B = 1 := by
    ext u v
    obtain ⟨x', rfl⟩ := hq u
    obtain ⟨x, rfl⟩ := hq v
    rw [← compKernel_matrix_eq_mul, h, Matrix.one_apply]
  have hd : Matrix.det A * Matrix.det B = 1 := by
    rw [← Matrix.det_mul, e, Matrix.det_one]
  exact isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hd
theorem periodicResolventSqrtsLocal_holds (hLocal : BoundedSymbolLocalMatrix)
    (hCells : CellQuotientsOfTower) (hRoots : ResolventRootsPeriodize)
    (hRead : KernelMatricesOnSide) (hPer : FreeOperatorsPeriodizeOnTorus)
    (hStrip : FreeStripEstimate)
    (hRS : ResolventRootsOnStrip.ResolventRootsHold)
    (hRes : FreeResolventRoots) (hSets : TowerIndexSets.Claim)
    (hOps : FreeOperators.FreeOperatorsArePeriodic) (hComp : CompClaim)
    (hFacts : RescaledConditions.Holds) :
    PeriodicResolventSqrtsLocal := by
  intro L hL
  obtain ⟨δ, hδ, C, hC, hA⟩ := hStrip
  have hδ0 : 0 < δ := hδ.1
  have hC0 : 0 < C := by linarith
  obtain ⟨K, θ, hK, hθ, hloc⟩ := hLocal (2 * δ) (by positivity)
  refine ⟨K * C, θ, by positivity, hθ, fun k hk => ⟨1, fun n _ hn => ?_⟩⟩
  intro _ _ _ _ _ _ _ _ _
  have hL0 : 0 < L := by have := hL.2; omega
  have hs : 0 < periodSide L n := by
    simp only [periodSide]
    positivity
  set s := periodSide L n with hsdef
  have bnd := (hA L hL k hk).1
  obtain ⟨fb, fs⟩ := hRS L hL k hk
  obtain ⟨qs, qb, qp, -, -⟩ := hCells L n k hL hn
  obtain ⟨rootE, rootV⟩ := hRoots L n k hL hn hk
  obtain ⟨iV, iE, iF⟩ := hSets L hL k 0 (Nat.zero_le _)
  have per := hPer L n k hL hn hk
  obtain ⟨-, -, -, pe, pv, -, -⟩ := hRes L hL k hk
  set w : ℝ := meshAt L k 0 ^ 4 with hw
  have hw0 : 0 < w := by
    have : 0 < meshAt L k 0 := by
      unfold meshAt
      positivity
    positivity
  have hone : K * C * Real.sqrt (w / w) = K * C := by
    rw [div_self hw0.ne', Real.sqrt_one, mul_one]
  have wV : ∀ x, (colourVertices L k 0).weightOf x = w := fun _ => rfl
  have wE : ∀ x, (colourEdges L k 0).weightOf x = w := fun _ => rfl
  have wF : ∀ x, (colourFaces L k 0).weightOf x = w := fun _ => rfl
  have ops := hOps.2 L hL k hk
  have hd := ops.1.edgeCoboundary 0 (Nat.zero_le k)
  have hsd := ops.1.vertexCoboundary 0 (Nat.zero_le k)
  have hsdt := ops.2.vertexCoboundary_transpose 0 (Nat.zero_le k)
  obtain ⟨-, -, -, -, -, hOne, -⟩ := (hFacts L hL k hk).2
  have eD : (trivialRescaledOperators L k).D = vertexDiff L k := hOne.D_eq
  have eDt : (trivialRescaledOperators L k).Dt = vertexDiffT L k := by
    simp only [vertexDiffT, ← eD]
    rfl
  have pV : IsPeriodicQuotient (colourVertices L k 0) (colouredVertexProj L n k 0) s :=
    ⟨qs.surjective, qs.image_eq_iff⟩
  have pE : IsPeriodicQuotient (colourEdges L k 0) (colouredEdgeProj L n k 0) s :=
    ⟨qb.surjective, qb.image_eq_iff⟩
  have pF : IsPeriodicQuotient (colourFaces L k 0) (colouredFaceProj L n k 0) s :=
    ⟨qp.surjective, qp.image_eq_iff⟩
  have RE := hRead _ _ _ iE iE iE _ _ _ s hs pE pE pE
  have RV := hRead _ _ _ iV iV iV _ _ _ s hs pV pV pV
  have readE : ReadsKernel (colouredEdgeProj L n k 0) (colouredEdgeProj L n k 0) s
      (edgeResolventSqrt L k) (periodicEdgeResolventSqrt L n k) := rootE
  have readV : ReadsKernel (colouredVertexProj L n k 0) (colouredVertexProj L n k 0) s
      (vertexResolventSqrt L k) (periodicVertexResolventSqrt L n k) := rootV
  have symE := symm_of_kernelTranspose_eq hw0 wE _
    (pe.transpose_eq (-(1 / 2)) (by simp [resolventExponents]))
  have symV := symm_of_kernelTranspose_eq hw0 wV _
    (pv.transpose_eq (-(1 / 2)) (by simp [resolventExponents]))
  have hD₁ : IsPeriodicKernel (colourEdges L k 0) (colourFaces L k 0)
      (compKernel (edgeDiff L k) (edgeResolventSqrt L k)) :=
    compKernel_periodic_of_finiteRange hComp iE iF iE hd.finite_range fb.sqrt_periodic
  have hD₂ : IsPeriodicKernel (colourEdges L k 0) (colourVertices L k 0)
      (compKernel (vertexDiffT L k) (edgeResolventSqrt L k)) :=
    compKernel_periodic_of_finiteRange hComp iE iV iE hsdt fb.sqrt_periodic
  have hD₃ : IsPeriodicKernel (colourVertices L k 0) (colourEdges L k 0)
      (compKernel (vertexDiff L k) (vertexResolventSqrt L k)) :=
    compKernel_periodic_of_finiteRange hComp iV iE iV hsd.finite_range fs.sqrt_periodic
  have r₁ := (hRead _ _ _ iE iF iE _ _ _ s hs pE pF pE).1 _ _ _ _ hd.finite_range.1
    fb.sqrt_periodic per.coboundary readE
  have r₂ := (hRead _ _ _ iE iV iE _ _ _ s hs pE pV pE).1 _ _ _ _ (eDt ▸ hsdt.1)
    fb.sqrt_periodic per.Dt readE
  have r₃ := (hRead _ _ _ iV iE iV _ _ _ s hs pV pE pV).1 _ _ _ _ (eD ▸ hsd.finite_range.1)
    fs.sqrt_periodic per.D readV
  rw [eDt] at r₂
  rw [eD] at r₃
  have eTr : (rescaledOperators L n k (trivialField L n k 0)).Dt =
      (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).D).transpose := by
    funext x y
    have hη : finestMesh L k ^ 4 ≠ 0 := by
      unfold finestMesh meshAt
      positivity
    simp only [RescaledOperators.Dt, meshTranspose, PeriodicOperators.wTranspose,
      Matrix.transpose_apply, Matrix.of_apply]
    have e : meshWeight (rescaledOperators L n k (trivialField L n k 0)).eta y /
        meshWeight (rescaledOperators L n k (trivialField L n k 0)).eta x = 1 :=
      div_self hη
    rw [e]
    simp
  refine ⟨matrix_transpose_eq_of_symm iE qb.surjective _ fb.sqrt_periodic.1 symE s _ readE,
    matrix_transpose_eq_of_symm iV qs.surjective _ fs.sqrt_periodic.1 symV s _ readV,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨Mi, hMi⟩ := RE.2.1 _ fb.invSqrt_periodic
    have hp := RE.1 _ _ _ _ fb.invSqrt_periodic fb.sqrt_periodic hMi readE
    have e : compKernel (edgeResolventInvSqrt L k) (edgeResolventSqrt L k) =
        idKernel (colourEdges L k 0) := pe.sqrt_comp_invSqrt.2
    have hid := RE.2.2
    refine det_isUnit_of_left_inverse qb.surjective (Matrix.of Mi) _ fun x' x => ?_
    have h1 := hp x' x
    rw [e] at h1
    exact h1.trans (hid x' x).symm
  · obtain ⟨Mi, hMi⟩ := RV.2.1 _ fs.invSqrt_periodic
    have hp := RV.1 _ _ _ _ fs.invSqrt_periodic fs.sqrt_periodic hMi readV
    have e : compKernel (vertexResolventInvSqrt L k) (vertexResolventSqrt L k) =
        idKernel (colourVertices L k 0) := pv.sqrt_comp_invSqrt.2
    have hid := RV.2.2
    refine det_isUnit_of_left_inverse qs.surjective (Matrix.of Mi) _ fun x' x => ?_
    have h1 := hp x' x
    rw [e] at h1
    exact h1.trans (hid x' x).symm
  · have := hloc L n k hL hn _ _ iE iE w w hw0 hw0 wE wE _ _ colouredEdgeCell colouredEdgeCell
      qb qb _ C hC0 fb.sqrt_periodic bnd.edge_sqrt (periodicEdgeResolventSqrt L n k) rootE
    rwa [hone] at this
  · have := hloc L n k hL hn _ _ iV iV w w hw0 hw0 wV wV _ _ colouredVertexCell
      colouredVertexCell qs qs _ C hC0 fs.sqrt_periodic bnd.vertex_sqrt
      (periodicVertexResolventSqrt L n k) rootV
    rwa [hone] at this
  · have := hloc L n k hL hn _ _ iE iF w w hw0 hw0 wE wF _ _ colouredEdgeCell colouredFaceCell
      qb qp _ C hC0 hD₁ bnd.diff_edge_sqrt.2
      (Matrix.of (scaledEdgeCoboundaryKernel L n k 0) * periodicEdgeResolventSqrt L n k)
      (by rw [← compKernel_matrix_eq_mul]; exact r₁)
    rwa [hone] at this
  · have := hloc L n k hL hn _ _ iE iV w w hw0 hw0 wE wV _ _ colouredEdgeCell colouredVertexCell
      qb qs _ C hC0 hD₂ bnd.diffT_edge_sqrt.2
      ((Matrix.of (rescaledOperators L n k (trivialField L n k 0)).D).transpose *
        periodicEdgeResolventSqrt L n k)
      (by rw [← compKernel_matrix_eq_mul, ← eTr]; exact r₂)
    rwa [hone] at this
  · have := hloc L n k hL hn _ _ iV iE w w hw0 hw0 wV wE _ _ colouredVertexCell colouredEdgeCell
      qs qb _ C hC0 hD₃ bnd.diff_vertex_sqrt.2
      (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).D *
        periodicVertexResolventSqrt L n k)
      (by rw [← compKernel_matrix_eq_mul]; exact r₃)
    rwa [hone] at this
end YangMills.Construction.RunningCouplingSlope
end

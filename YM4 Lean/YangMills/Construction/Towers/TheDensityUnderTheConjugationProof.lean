import YangMills.Construction.Towers.MultiplesOfTheSectorMatricesAndTheConjugation
import YangMills.Construction.Towers.TheDensityIsTheSumOverTheSectorsOnTheUnitLattice
import YangMills.Construction.Towers.TheDensityUnderTheConjugation
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open OperatorCalculus OneLoopNotation Tower.UnitLatticeL2
namespace Tower.AbelianFieldDensity
open SectorDecomposition
namespace StarConjugation
section Operators
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem toBddOp_apply {M : H → H} (hM : IsBddOpMap M) (ψ : H) :
    toBddOp M ψ = M ψ :=
  Classical.epsilon_spec (p := fun B : BddOp H => ∀ ψ : H, B ψ = M ψ) hM ψ
theorem conj_inner_apply_self [CompleteSpace H] {S : BddOp H}
    (hS : IsSelfAdjointOp S) (u : H) : conj (inner ℂ u (S u)) = inner ℂ u (S u) := by
  rw [inner_conj_symm]
  have hadj := ContinuousLinearMap.adjoint_inner_left S u u
  rwa [show ContinuousLinearMap.adjoint S = S from hS] at hadj
end Operators
theorem starRing_finsum_mem {J : Type} (s : Set J) (g : J → ℂ) :
    conj (∑ᶠ i ∈ s, g i) = ∑ᶠ i ∈ s, conj (g i) := by
  let e : ℂ ≃+ ℂ := (starRingAut (R := ℂ)).toAddEquiv
  exact (AddEquiv.map_finsum e _).trans (finsum_congr fun i => AddEquiv.map_finsum e _)
theorem matrixEntry_diag_eq_inner {J : Type}
    (S : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2) (ι : J) :
    matrixEntry S ι ι = inner ℂ (basisVec ι) (S (basisVec ι)) := by
  classical
  unfold matrixEntry basisVec
  rw [lp.inner_single_left]
  simp
section Conjugation
variable {σ : Type}
theorem starConj_isBddOpMap (F : StarInvolutionFacts σ)
    (S : BddOp (L2Field σ)) :
    IsBddOpMap (fun f => pointwiseStar (S (pointwiseStar f))) := by
  refine ⟨LinearMap.mkContinuous
    { toFun := fun f => pointwiseStar (S (pointwiseStar f))
      map_add' := fun f g => by
        have ha : ∀ u v : L2Field σ, pointwiseStar (u + v) = pointwiseStar u + pointwiseStar v :=
          F.isConjLinear.1
        rw [ha, map_add, ha]
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        have hs : ∀ (a : ℂ) (u : L2Field σ), pointwiseStar (a • u) = conj a • pointwiseStar u :=
          F.isConjLinear.2
        rw [hs, map_smul, hs, Complex.conj_conj] } ‖S‖ (fun f => ?_),
    fun ψ => rfl⟩
  change ‖pointwiseStar (S (pointwiseStar f))‖ ≤ ‖S‖ * ‖f‖
  rw [F.norm_eq, ← F.norm_eq f]
  exact S.le_opNorm _
theorem matrixEntry_starConj (F : StarInvolutionFacts σ)
    (S : BddOp (L2Field σ)) (ι : Fin 3 × σ) :
    matrixEntry (toBddOp fun f => pointwiseStar (S (pointwiseStar f))) ι ι =
      conj (matrixEntry S ι ι) := by
  unfold matrixEntry
  rw [toBddOp_apply (starConj_isBddOpMap F S), F.basisVec_fixed, F.apply_eq_conj]
theorem traceAt_starConj (F : StarInvolutionFacts σ)
    (pos : Fin 3 × σ → InfiniteLattice.AmbientSpace)
    (S : BddOp (L2Field σ)) (x : InfiniteLattice.AmbientSpace) :
    traceAt pos (toBddOp fun f => pointwiseStar (S (pointwiseStar f))) x =
      conj (traceAt pos S x) := by
  unfold traceAt
  rw [starRing_finsum_mem]
  exact finsum_congr fun ι => finsum_congr fun _ => matrixEntry_starConj F S ι
theorem conj_traceAt_of_selfAdjoint (pos : Fin 3 × σ → InfiniteLattice.AmbientSpace)
    {S : BddOp (L2Field σ)} (hS : IsSelfAdjointOp S)
    (x : InfiniteLattice.AmbientSpace) :
    conj (traceAt pos S x) = traceAt pos S x := by
  unfold traceAt
  rw [starRing_finsum_mem]
  refine finsum_congr fun ι => finsum_congr fun _ => ?_
  rw [matrixEntry_diag_eq_inner]
  exact conj_inner_apply_self hS _
end Conjugation
section Sectors
variable {L N' : ℕ} {σ : Type}
  {mult : VectorL2 L N' → Matrices.ComplexMatrix2 → L2Field σ}
theorem lowering_injective (M : WeightMultipleFacts mult)
    {a b : VectorL2 L N'} (hab : mult a loweringPauli = mult b loweringPauli) :
    a = b := by
  have ht : IsWeightMatrix loweringPauli := Or.inr (Or.inr rfl)
  have h0 : mult (a + (-1 : ℂ) • b) loweringPauli = 0 := by
    rw [M.map_add _ ht, M.map_smul _ ht, hab]
    simp
  have h1 := M.inner_lowering (a + (-1 : ℂ) • b) (a + (-1 : ℂ) • b)
  rw [h0, inner_zero_left] at h1
  have h2 : inner ℂ (a + (-1 : ℂ) • b) (a + (-1 : ℂ) • b) = 0 := by
    have h3 := h1.symm
    simpa using h3
  have h4 : a + (-1 : ℂ) • b = 0 := inner_self_eq_zero (𝕜 := ℂ).1 h2
  have h5 : a - b = 0 := by
    simpa [sub_eq_add_neg] using h4
  exact sub_eq_zero.1 h5
theorem negSector_conjVec (M : WeightMultipleFacts mult)
    {S : BddOp (L2Field σ)}
    {Szero Splus Sminus : VectorL2 L N' → VectorL2 L N'}
    (hS : IsSectorTriple mult S Szero Splus Sminus)
    (hc : ∀ f, S (pointwiseStar f) = pointwiseStar (S f)) (v : VectorL2 L N') :
    Sminus (conjVec v) = conjVec (Splus v) := by
  apply lowering_injective M
  rw [← hS.2.2, ← M.star_raising, hc, hS.2.1, M.star_raising]
theorem conjVec_vecDelta (M : WeightMultipleFacts mult)
    (ι : Fin N' × FullSpace.Vertex L 0 0) :
    conjVec (vecDelta ι : VectorL2 L N') = vecDelta ι := by
  classical
  ext x i
  rw [M.conjVec_apply]
  unfold vecDelta
  by_cases hx : x = ι.2
  · subst hx
    by_cases hi : i = ι.1
    · subst hi
      simp
    · simp [hi]
  · simp [hx]
theorem vecCoord_eq_inner (ι : Fin N' × FullSpace.Vertex L 0 0) (w : VectorL2 L N') :
    vecCoord w ι = inner ℂ (vecDelta ι : VectorL2 L N') w := by
  classical
  unfold vecCoord vecDelta
  rw [lp.inner_single_left, EuclideanSpace.inner_single_left]
  simp
theorem conj_vecCoord_posSector (M : WeightMultipleFacts mult)
    {S : BddOp (L2Field σ)}
    {Szero Splus Sminus : VectorL2 L N' → VectorL2 L N'}
    (hS : IsSectorTriple mult S Szero Splus Sminus) (hsa : IsSelfAdjointOp S)
    (ι : Fin N' × FullSpace.Vertex L 0 0) :
    conj (vecCoord (Splus (vecDelta ι)) ι) = vecCoord (Splus (vecDelta ι)) ι := by
  rw [vecCoord_eq_inner]
  have h1 := M.inner_raising (vecDelta ι) (Splus (vecDelta ι))
  rw [← hS.2.1] at h1
  have h2 := conj_inner_apply_self hsa (mult (vecDelta ι) raisingPauli)
  rw [h1, map_mul] at h2
  have h3 : conj (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [h3] at h2
  exact mul_left_cancel₀ (by norm_num) h2
theorem vecTraceAt_negSector_eq (M : WeightMultipleFacts mult)
    {S : BddOp (L2Field σ)}
    {Szero Splus Sminus : VectorL2 L N' → VectorL2 L N'}
    (hS : IsSectorTriple mult S Szero Splus Sminus) (hsa : IsSelfAdjointOp S)
    (hc : ∀ f, S (pointwiseStar f) = pointwiseStar (S f))
    (hp : IsBddOpMap Splus) (hn : IsBddOpMap Sminus) (x : FullSpace.Vertex L 0 0) :
    vecTraceAt (toBddOp Sminus) x = vecTraceAt (toBddOp Splus) x := by
  unfold vecTraceAt
  refine finsum_congr fun ι => finsum_congr fun _ => ?_
  rw [toBddOp_apply hp, toBddOp_apply hn]
  have h1 := negSector_conjVec M hS hc (vecDelta ι)
  rw [conjVec_vecDelta M] at h1
  rw [h1, ← conj_vecCoord_posSector M hS hsa ι]
  exact M.conjVec_apply _ _ _
theorem traceStarConj_of_splits (F : StarInvolutionFacts σ) (M : WeightMultipleFacts mult)
    {pos : Fin 3 × σ → InfiniteLattice.AmbientSpace}
    (hsum : TraceSplitsBySector mult pos) :
    TraceStarConj mult pos := by
  intro S
  refine ⟨starConj_isBddOpMap F S, fun x => traceAt_starConj F pos S _, fun hsa x => ⟨?_, ?_⟩,
    fun Szero Splus Sminus hS hsa hc x => ?_⟩
  · exact Complex.conj_eq_iff_im.1 (conj_traceAt_of_selfAdjoint pos hsa _)
  · rw [traceAt_starConj F pos S, conj_traceAt_of_selfAdjoint pos hsa]
  · obtain ⟨-, hp, hn, -⟩ := hsum S Szero Splus Sminus hS
    exact vecTraceAt_negSector_eq M hS hsa hc hp hn x
end Sectors
end StarConjugation
theorem UnitLatticeStarConj.holds
    (hM : WeightMultiplesAndStar)
    (hT : SectorDecomposition.UnitLatticeTraceSplits.Claim) :
    UnitLatticeStarConj.Claim := fun L hL =>
  ⟨StarConjugation.traceStarConj_of_splits (hM L hL).2.2.2.2.1
      (hM L hL).2.2.2.2.2.2.1 (hT L hL).1,
    StarConjugation.traceStarConj_of_splits (hM L hL).2.2.2.2.2.1
      (hM L hL).2.2.2.2.2.2.2 (hT L hL).2⟩
end Tower.AbelianFieldDensity
end YangMills.Construction
end

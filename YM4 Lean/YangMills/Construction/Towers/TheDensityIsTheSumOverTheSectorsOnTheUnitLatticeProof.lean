import YangMills.Construction.Towers.GaugeTransformationsKeepTheDensityProof
import YangMills.Construction.Towers.MultiplesOfTheSectorMatricesAndTheConjugation
import YangMills.Construction.Towers.TheDensityIsTheSumOverTheSectorsOnTheUnitLattice
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.OneLoopNotation YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
namespace UnitLatticeTraceSplitsProof
section Boundedness
variable {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E']
  [InnerProductSpace ℂ E']
theorem norm_sq_eq_of_inner_scaled (A : E → E') {c : ℝ}
    (hinner : ∀ u u' : E, inner ℂ (A u) (A u') = (c : ℂ) * inner ℂ u u') (u : E) :
    ‖A u‖ ^ 2 = c * ‖u‖ ^ 2 := by
  have h : ((‖A u‖ : ℝ) : ℂ) ^ 2 = (c : ℂ) * ((‖u‖ : ℝ) : ℂ) ^ 2 := by
    simpa [inner_self_eq_norm_sq_to_K] using hinner u u
  exact_mod_cast h
theorem isBddOpMap_of_intertwining (A : E → E') {c : ℝ} (hc : 0 < c)
    (hadd : ∀ u u' : E, A (u + u') = A u + A u')
    (hsmul : ∀ (z : ℂ) (u : E), A (z • u) = z • A u)
    (hinner : ∀ u u' : E, inner ℂ (A u) (A u') = (c : ℂ) * inner ℂ u u')
    (S : E' →L[ℂ] E') (T : E → E) (hT : ∀ u, S (A u) = A (T u)) : IsBddOpMap T := by
  have hinj : ∀ u u' : E, A u = A u' → u = u' := by
    intro u u' h
    have h0 : A (u - u') = 0 := by
      have h1 : A (u - u') = A u + (-1 : ℂ) • A u' := by
        rw [sub_eq_add_neg, hadd, ← neg_one_smul ℂ u', hsmul]
      rw [h1, h]
      simp
    have h2 := norm_sq_eq_of_inner_scaled A hinner (u - u')
    rw [h0, norm_zero] at h2
    have h3 : ‖u - u'‖ ^ 2 = 0 := by
      have h4 : c * ‖u - u'‖ ^ 2 = 0 := by rw [← h2]; norm_num
      exact (mul_eq_zero.1 h4).resolve_left hc.ne'
    have h5 : ‖u - u'‖ = 0 := by simpa using h3
    exact sub_eq_zero.1 (norm_eq_zero.1 h5)
  let l : E →ₗ[ℂ] E :=
    { toFun := T
      map_add' := fun a b => hinj _ _ (by rw [← hT, hadd, map_add, hT, hT, hadd])
      map_smul' := fun z a => hinj _ _ (by
        simp only [RingHom.id_apply]
        rw [← hT, hsmul, map_smul, hT, hsmul]) }
  have hb : ∀ u, ‖l u‖ ≤ ‖S‖ * ‖u‖ := by
    intro u
    have h1 := norm_sq_eq_of_inner_scaled A hinner (T u)
    have h2 := norm_sq_eq_of_inner_scaled A hinner u
    have h3 : ‖A (T u)‖ ≤ ‖S‖ * ‖A u‖ := by
      rw [← hT]
      exact S.le_opNorm _
    have h4 : ‖A (T u)‖ ^ 2 ≤ (‖S‖ * ‖A u‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    rw [mul_pow, h1, h2] at h4
    have h5 : ‖T u‖ ^ 2 ≤ (‖S‖ * ‖u‖) ^ 2 := by
      rw [mul_pow]
      have h6 : c * ‖T u‖ ^ 2 ≤ c * (‖S‖ ^ 2 * ‖u‖ ^ 2) := by linarith
      exact le_of_mul_le_mul_left h6 hc
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h5
  exact ⟨l.mkContinuous ‖S‖ hb, fun ψ => rfl⟩
theorem toBddOp_apply {A : E → E} (h : IsBddOpMap A) (ψ : E) :
    toBddOp A ψ = A ψ :=
  Classical.epsilon_spec h ψ
end Boundedness
section Coordinates
variable {ι : Type}
theorem coords_eq_of_ofCoords_eq (f : L2Field ι) (i : ι) (c : Fin 3 → ℂ)
    (h : ofCoords f i = ∑ a, c a • ComplexMatrix2.pauliFamily a) : ∀ a, f (a, i) = c a := by
  obtain ⟨p0, p1, p2⟩ := ComplexMatrix2.pauliFamily_apply
  simp only [ofCoords, Fin.sum_univ_three, p0, p1, p2] at h
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  simp [Matrix.add_apply] at e00 e01 e10
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h0 : f (0, i) = c 0 := by linear_combination (1 / 2 : ℂ) * e01 + (1 / 2 : ℂ) * e10
  have h1 : f (1, i) = c 1 := by
    have h2 : Complex.I * (f (1, i) - c 1) = 0 := by
      linear_combination (1 / 2 : ℂ) * e10 - (1 / 2 : ℂ) * e01
    have h3 := (mul_eq_zero.1 h2).resolve_left hI
    exact sub_eq_zero.1 h3
  intro a
  fin_cases a
  · exact h0
  · exact h1
  · exact e00
theorem raisingPauli_eq_sum : raisingPauli =
    ∑ a, (![(1 / 2 : ℂ), Complex.I / 2, 0] : Fin 3 → ℂ) a • ComplexMatrix2.pauliFamily a := by
  simp only [raisingPauli, Fin.sum_univ_three]
  simp [smul_add, smul_smul, div_eq_mul_inv, mul_comm]
theorem loweringPauli_eq_sum : loweringPauli =
    ∑ a, (![(1 / 2 : ℂ), -Complex.I / 2, 0] : Fin 3 → ℂ) a • ComplexMatrix2.pauliFamily a := by
  simp only [loweringPauli, Fin.sum_univ_three]
  simp [sub_eq_add_neg, smul_add, smul_smul, div_eq_mul_inv, mul_comm]
theorem pauliFamily_two_eq_sum : ComplexMatrix2.pauliFamily 2 =
    ∑ a, (![(0 : ℂ), 0, 1] : Fin 3 → ℂ) a • ComplexMatrix2.pauliFamily a := by
  simp [Fin.sum_univ_three]
end Coordinates
section Diagonal
theorem coords_eq_of_ofCoords_eq_smul {ι : Type} (f : L2Field ι) (i : ι) (w : ℂ)
    (X : ComplexMatrix2) (c : Fin 3 → ℂ) (hX : X = ∑ a, c a • ComplexMatrix2.pauliFamily a)
    (h : ofCoords f i = w • X) (a : Fin 3) : f (a, i) = w * c a := by
  refine coords_eq_of_ofCoords_eq f i (fun a => w * c a) ?_ a
  rw [h, hX, Finset.smul_sum]
  simp only [smul_smul]
open Classical in
theorem basisVec_apply {J : Type} (j j' : J) :
    basisVec j j' = if j' = j then 1 else 0 := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.GaugeConjugation.basisVec_apply <;> assumption
variable {L N' : ℕ} {ι : Type}
open Classical in
theorem vecDelta_apply (k k' : Fin N') (x x' : FullSpace.Vertex L 0 0) :
    vecDelta (k, x) x' k' = if x' = x ∧ k' = k then 1 else 0 := by
  by_cases hx : x' = x
  · subst hx
    by_cases hk : k' = k
    · subst hk
      simp [vecDelta, lp.single_apply]
    · simp [vecDelta, lp.single_apply, hk]
  · simp [vecDelta, lp.single_apply, hx]
variable {tensor : VectorL2 L N' → ComplexMatrix2 → L2Field ι}
  {pos : ι → FullSpace.Vertex L 0 0 × Fin N'}
theorem sum_diag_entries_eq (hpos : Function.Injective pos)
    (hval : ∀ t, IsWeightMatrix t → ∀ (v : VectorL2 L N') (i : ι),
      ofCoords (tensor v t) i = v (pos i).1 (pos i).2 • t)
    (S : BddOp (L2Field ι))
    (S₀ Sp Sm : VectorL2 L N' → VectorL2 L N')
    (h : IsSectorTriple tensor S S₀ Sp Sm) (i : ι) :
    ∑ a, matrixEntry S (a, i) (a, i) =
      S₀ (vecDelta ((pos i).2, (pos i).1)) (pos i).1 (pos i).2 +
        Sp (vecDelta ((pos i).2, (pos i).1)) (pos i).1 (pos i).2 +
        Sm (vecDelta ((pos i).2, (pos i).1)) (pos i).1 (pos i).2 := by
  classical
  have t3 : IsWeightMatrix (ComplexMatrix2.pauliFamily 2) := Or.inl rfl
  have tp : IsWeightMatrix raisingPauli := Or.inr (Or.inl rfl)
  have tm : IsWeightMatrix loweringPauli := Or.inr (Or.inr rfl)
  obtain ⟨δ, hδ⟩ : ∃ δ : VectorL2 L N', δ = vecDelta ((pos i).2, (pos i).1) := ⟨_, rfl⟩
  rw [← hδ]
  have hd : ∀ i' : ι, δ (pos i').1 (pos i').2 = if i' = i then 1 else 0 := by
    intro i'
    rw [hδ, vecDelta_apply]
    by_cases hi : i' = i
    · simp [hi]
    · have hne : ¬ ((pos i').1 = (pos i).1 ∧ (pos i').2 = (pos i).2) := fun hh =>
        hi (hpos (Prod.ext hh.1 hh.2))
      simp [hi, hne]
  have c3 : ∀ (v : VectorL2 L N') (i' : ι) (a : Fin 3),
      tensor v (ComplexMatrix2.pauliFamily 2) (a, i') =
      v (pos i').1 (pos i').2 * (![(0 : ℂ), 0, 1] : Fin 3 → ℂ) a := fun v i' a =>
    coords_eq_of_ofCoords_eq_smul _ i' _ _ _ pauliFamily_two_eq_sum (hval _ t3 v i') a
  have cp : ∀ (v : VectorL2 L N') (i' : ι) (a : Fin 3), tensor v raisingPauli (a, i') =
      v (pos i').1 (pos i').2 * (![(1 / 2 : ℂ), Complex.I / 2, 0] : Fin 3 → ℂ) a := fun v i' a =>
    coords_eq_of_ofCoords_eq_smul _ i' _ _ _ raisingPauli_eq_sum (hval _ tp v i') a
  have cm : ∀ (v : VectorL2 L N') (i' : ι) (a : Fin 3), tensor v loweringPauli (a, i') =
      v (pos i').1 (pos i').2 * (![(1 / 2 : ℂ), -Complex.I / 2, 0] : Fin 3 → ℂ) a := fun v i' a =>
    coords_eq_of_ofCoords_eq_smul _ i' _ _ _ loweringPauli_eq_sum (hval _ tm v i') a
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have u2 : basisVec ((2 : Fin 3), i) = tensor δ (ComplexMatrix2.pauliFamily 2) := by
    ext ⟨a, i'⟩
    rw [c3, hd, basisVec_apply]
    by_cases hi : i' = i <;> fin_cases a <;> simp [hi]
  have u0 : basisVec ((0 : Fin 3), i) = tensor δ raisingPauli + tensor δ loweringPauli := by
    ext ⟨a, i'⟩
    simp only [lp.coeFn_add, Pi.add_apply]
    rw [cp, cm, hd, basisVec_apply]
    by_cases hi : i' = i <;> fin_cases a <;> simp [hi]
    all_goals ring
  have u1 : basisVec ((1 : Fin 3), i) =
      (-Complex.I) • (tensor δ raisingPauli - tensor δ loweringPauli) := by
    ext ⟨a, i'⟩
    simp only [lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [cp, cm, hd, basisVec_apply]
    by_cases hi : i' = i <;> fin_cases a <;> simp [hi]
    linear_combination hI
  rw [Fin.sum_univ_three]
  simp only [matrixEntry]
  rw [u0, u1, u2, map_add, map_smul, map_sub, h.1, h.2.1, h.2.2]
  simp only [lp.coeFn_add, lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply, Pi.add_apply,
    smul_eq_mul]
  rw [cp, cm, cp, cm, c3]
  simp
  linear_combination (-(Sp δ (pos i).1 (pos i).2 + Sm δ (pos i).1 (pos i).2) / 2) * hI
theorem isBddOpMap_of_isSectorTriple (hF : WeightMultipleFacts tensor)
    (S : BddOp (L2Field ι))
    (S₀ Sp Sm : VectorL2 L N' → VectorL2 L N')
    (h : IsSectorTriple tensor S S₀ Sp Sm) :
    IsBddOpMap S₀ ∧ IsBddOpMap Sp ∧ IsBddOpMap Sm := by
  have t3 : IsWeightMatrix (ComplexMatrix2.pauliFamily 2) := Or.inl rfl
  have tp : IsWeightMatrix raisingPauli := Or.inr (Or.inl rfl)
  have tm : IsWeightMatrix loweringPauli := Or.inr (Or.inr rfl)
  refine ⟨isBddOpMap_of_intertwining (fun v => tensor v (ComplexMatrix2.pauliFamily 2)) (c := 1)
      one_pos (hF.map_add _ t3) (hF.map_smul _ t3) ?_ S _ h.1,
    isBddOpMap_of_intertwining (fun v => tensor v raisingPauli) (c := 1 / 2) (by norm_num)
      (hF.map_add _ tp) (hF.map_smul _ tp) ?_ S _ h.2.1,
    isBddOpMap_of_intertwining (fun v => tensor v loweringPauli) (c := 1 / 2) (by norm_num)
      (hF.map_add _ tm) (hF.map_smul _ tm) ?_ S _ h.2.2⟩
  · intro v v'
    simpa using hF.inner_third v v'
  · intro v v'
    simpa using hF.inner_raising v v'
  · intro v v'
    simpa using hF.inner_lowering v v'
end Diagonal
section Traces
variable {L N' : ℕ}
theorem finsum_mem_range_eq_sum {I J : Type} [Fintype I] (g : I → J) (hg : Function.Injective g)
    (f : J → ℂ) : ∑ᶠ j ∈ Set.range g, f j = ∑ i, f (g i) := by
  rw [finsum_mem_range hg, finsum_eq_sum_of_fintype]
theorem vecTraceAt_eq_sum (T : VectorL2 L N' →L[ℂ] VectorL2 L N')
    (x : FullSpace.Vertex L 0 0) : vecTraceAt T x = ∑ k, T (vecDelta (k, x)) x k := by
  have hset : {j : Fin N' × FullSpace.Vertex L 0 0 | j.2 = x} =
      Set.range (fun k : Fin N' => (k, x)) := by
    ext ⟨k, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_range, Prod.mk.injEq]
    constructor
    · rintro rfl
      exact ⟨k, rfl, rfl⟩
    · rintro ⟨_, _, rfl⟩
      rfl
  have hinj : Function.Injective
      (fun k : Fin N' => ((k, x) : Fin N' × FullSpace.Vertex L 0 0)) :=
    fun a b hab => (Prod.ext_iff.1 hab).1
  unfold vecTraceAt
  rw [hset, finsum_mem_range_eq_sum _ hinj]
  rfl
theorem traceSplits_vertices (hI : VertexIndexCount L)
    (hF : WeightMultipleFacts (vertexTensor (L := L)))
    (hval : ∀ t, IsWeightMatrix t → ∀ (v : VectorL2 L 1) (x : FullSpace.Vertex L 0 0),
      ofCoords (vertexTensor v t) x = v x 0 • t) :
    TraceSplitsBySector (vertexTensor (L := L)) (vertexPos L) := by
  intro S S₀ Sp Sm h
  obtain ⟨b3, bp, bm⟩ := isBddOpMap_of_isSectorTriple hF S S₀ Sp Sm h
  refine ⟨b3, bp, bm, fun x => ?_⟩
  have hinj : Function.Injective (fun a : Fin 3 => ((a, x) : VertexIndex L)) :=
    fun a b hab => (Prod.ext_iff.1 hab).1
  have htr : traceAt (vertexPos L) S x = ∑ a, matrixEntry S (a, x) (a, x) := by
    unfold traceAt
    rw [(hI.1 x).1, finsum_mem_range_eq_sum _ hinj]
  have hpos : Function.Injective
      (fun x : FullSpace.Vertex L 0 0 => ((x, 0) : FullSpace.Vertex L 0 0 × Fin 1)) :=
    fun a b hab => (Prod.ext_iff.1 hab).1
  rw [htr, sum_diag_entries_eq (tensor := vertexTensor (L := L)) hpos hval S S₀ Sp Sm h x,
    vecTraceAt_eq_sum, vecTraceAt_eq_sum, vecTraceAt_eq_sum]
  simp only [Fin.sum_univ_one, toBddOp_apply b3, toBddOp_apply bp, toBddOp_apply bm]
theorem traceSplits_edges (hI : EdgeIndexCount L)
    (hF : WeightMultipleFacts (edgeTensor (L := L)))
    (hb : ∀ e : PeriodicOperators.PosEdge L 0 0,
      ∃! p : FullSpace.Vertex L 0 0 × Fin 4, FullSpace.forwardEdge p.1 p.2 = e)
    (hval : ∀ t, IsWeightMatrix t → ∀ (v : VectorL2 L 4) (x : FullSpace.Vertex L 0 0)
      (μ : Fin 4), ofCoords (edgeTensor v t) (FullSpace.forwardEdge x μ) = v x μ • t) :
    TraceSplitsBySector (edgeTensor (L := L)) (edgePos L) := by
  intro S S₀ Sp Sm h
  obtain ⟨b3, bp, bm⟩ := isBddOpMap_of_isSectorTriple hF S S₀ Sp Sm h
  refine ⟨b3, bp, bm, fun x => ?_⟩
  obtain ⟨pos, hfe⟩ : ∃ pos : PeriodicOperators.PosEdge L 0 0 →
      FullSpace.Vertex L 0 0 × Fin 4, ∀ e, FullSpace.forwardEdge (pos e).1 (pos e).2 = e :=
    ⟨fun e => Classical.choose (hb e).exists, fun e => Classical.choose_spec (hb e).exists⟩
  have hpos : Function.Injective pos := by
    intro e e' hee
    rw [← hfe e, ← hfe e', hee]
  have hback : ∀ (y : FullSpace.Vertex L 0 0) (μ : Fin 4),
      pos (FullSpace.forwardEdge y μ) = (y, μ) :=
    fun y μ => (hb (FullSpace.forwardEdge y μ)).unique (hfe _) rfl
  have hval' : ∀ t, IsWeightMatrix t → ∀ (v : VectorL2 L 4)
      (e : PeriodicOperators.PosEdge L 0 0),
      ofCoords (edgeTensor v t) e = v (pos e).1 (pos e).2 • t := by
    intro t ht v e
    have h1 := hval t ht v (pos e).1 (pos e).2
    rwa [hfe e] at h1
  have hinj : Function.Injective (fun c : Fin 3 × Fin 4 =>
      ((c.1, FullSpace.forwardEdge x c.2) : EdgeIndex L)) := by
    rintro ⟨a, μ⟩ ⟨a', μ'⟩ hab
    have h1 := Prod.ext_iff.1 hab
    have h2 : pos (FullSpace.forwardEdge x μ) = pos (FullSpace.forwardEdge x μ') :=
      congrArg pos h1.2
    rw [hback, hback] at h2
    exact Prod.ext h1.1 (Prod.ext_iff.1 h2).2
  have htr : traceAt (edgePos L) S x =
      ∑ μ, ∑ a, matrixEntry S (a, FullSpace.forwardEdge x μ) (a, FullSpace.forwardEdge x μ) := by
    unfold traceAt
    rw [(hI.1 x).1, finsum_mem_range_eq_sum _ hinj, Fintype.sum_prod_type_right]
  rw [htr, vecTraceAt_eq_sum, vecTraceAt_eq_sum, vecTraceAt_eq_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [sum_diag_entries_eq (tensor := edgeTensor (L := L)) hpos hval' S S₀ Sp Sm h, hback]
  simp only [toBddOp_apply b3, toBddOp_apply bp, toBddOp_apply bm]
end Traces
end UnitLatticeTraceSplitsProof
theorem UnitLatticeTraceSplits.claim_holds
    (hM : WeightMultiplesAndStar)
    (hS : UnitLatticeL2Statement) :
    UnitLatticeTraceSplits.Claim := by
  intro L hL
  obtain ⟨hb, hsl, hvert, hedge, -, -, hFv, hFe⟩ := hM L hL
  obtain ⟨-, ⟨-, -, -, hIv, -, -⟩, ⟨-, -, -, hIe, -, -⟩⟩ := hS.2 L
  exact ⟨UnitLatticeTraceSplitsProof.traceSplits_vertices hIv hFv
      fun t ht v x => hvert t (hsl t ht) v x,
    UnitLatticeTraceSplitsProof.traceSplits_edges hIe hFe hb
      fun t ht v x μ => hedge t (hsl t ht) v x μ⟩
end YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
end

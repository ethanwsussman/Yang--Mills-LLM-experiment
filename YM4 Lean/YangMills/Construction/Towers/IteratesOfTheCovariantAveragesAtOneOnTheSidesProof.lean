import YangMills.Construction.Matrices.ExponentialOfLieElements
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSites
import YangMills.Construction.Towers.RealAndCovariantDifferentialsOfTheChain
import YangMills.Construction.Towers.SecondOrderOfACompositeAtOneProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.TrivialFieldIterates
open YangMills.Construction.Matrices YangMills.Construction.Conventions
variable {L n k : ℕ}
theorem isPositivelyOriented_or_opposite {j : ℕ} (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem trivialField_mem_fieldSpace (j : ℕ) :
    trivialField L n k j ∈ fieldSpace L n k j := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.trivialField_mem <;> assumption
theorem holds_at_identity {ι : Type*} {D : Set (ι → ComplexMatrix2)} {P : (ι → ComplexMatrix2) → Prop}
    (h : EventuallyNearIdentity D P) (h1 : (fun _ => (1 : ComplexMatrix2)) ∈ D) : P fun _ => 1 :=
  Filter.Eventually.self_of_nhdsWithin h h1
theorem exists_fine_vertex_mem_block (hZ : BlockStructure) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {i : ℕ} (hi : i < k) (y : Vertex L n k (i + 1)) :
    ∃ x : Vertex L n k i, (x : PeriodicLattice.FourTorus L n) = y ∧
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y := by
  obtain ⟨hD, hS, -⟩ := (hZ L k (i + 1) hL (by omega) (by omega) hi).1 n hn
  have h1 := hS.1 y
  have hm : (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
    have : (y : PeriodicLattice.FourTorus L n) ∈
        PeriodicLattice.unitBlock y ∩ (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1)) :
          Set (PeriodicLattice.FourTorus L n)) := by
      rw [h1]
      exact rfl
    exact this.1
  exact ⟨⟨y, (hD y).2.2.2 hm⟩, rfl, hm⟩
theorem complexBlockAverageStep_trivialField (hF : LevelwiseMeans.LevelwiseMeansHold)
    (hT : TrivialFieldAtStep) (hZ : BlockStructure)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {i : ℕ} (hi : i < k) :
    PeriodicLattice.complexBlockAverageStep i (trivialField L n k i) =
      trivialField L n k (i + 1) := by
  have hpos : ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
      PeriodicLattice.complexBlockAverage (trivialField L n k i) c = 1 := by
    intro c hc
    obtain ⟨x, -, hx⟩ := exists_fine_vertex_mem_block hZ hL hn hi c.source
    have h := holds_at_identity
      (((hF L hL k hk).1 n hn).agree_near_identity i hi c hc c.source (Or.inl rfl) x hx)
      (trivialField_mem_fieldSpace i)
    rw [h.2.1]
    exact congrFun (hT L n k i hL hn hi).2.1 c
  funext c
  by_cases hc : c.IsPositivelyOriented
  · exact hpos c hc
  · have hr := (isPositivelyOriented_or_opposite c).resolve_left hc
    have h := hpos _ hr
    have h3 : PeriodicLattice.complexBlockAverage (trivialField L n k i) c.opposite =
        PeriodicLattice.complexBlockAverageOnPositive (trivialField L n k i) c.opposite :=
      if_pos hr
    have h4 : PeriodicLattice.complexBlockAverage (trivialField L n k i) c =
        (PeriodicLattice.complexBlockAverageOnPositive (trivialField L n k i) c.opposite)⁻¹ :=
      if_neg hc
    show PeriodicLattice.complexBlockAverage (trivialField L n k i) c = 1
    rw [h4, ← h3, h, inv_one]
theorem complexBlockFieldAtLevel_trivialField (hF : LevelwiseMeans.LevelwiseMeansHold)
    (hT : TrivialFieldAtStep) (hZ : BlockStructure)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k) :
    PeriodicLattice.complexBlockFieldAtLevel j (trivialField L n k 0) =
      trivialField L n k j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have e := ih (by omega)
    show PeriodicLattice.complexBlockAverageStep j
      (PeriodicLattice.complexBlockFieldAtLevel j (trivialField L n k 0)) = _
    rw [e]
    exact complexBlockAverageStep_trivialField hF hT hZ hL hn hk (by omega)
theorem restrictVertexFunction_self {j : ℕ} (f : Vertex L n k j → ComplexMatrix2) :
    restrictVertexFunction j f = f := by
  funext x
  have h : ((x.toSublattice (PeriodicLattice.levelDepth k j) : Vertex L n k j) :
      PeriodicLattice.FourTorus L n) = x :=
    Classical.epsilon_spec (p := fun z : Vertex L n k j =>
      (z : PeriodicLattice.FourTorus L n) = (x : PeriodicLattice.FourTorus L n)) ⟨x, rfl⟩
  show f (x.toSublattice (PeriodicLattice.levelDepth k j)) = f x
  rw [Subtype.ext h]
theorem restrictVertexFunction_restrictVertexFunction (hZ : BlockStructure)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {i j : ℕ} (hj : j < k)
    (f : Vertex L n k i → ComplexMatrix2) :
    restrictVertexFunction (j + 1) (restrictVertexFunction j f) = restrictVertexFunction (j + 1) f := by
  funext y
  obtain ⟨x, hx, -⟩ := exists_fine_vertex_mem_block hZ hL hn hj y
  have h : ((y.toSublattice (PeriodicLattice.levelDepth k j) : Vertex L n k j) :
      PeriodicLattice.FourTorus L n) = y :=
    Classical.epsilon_spec (p := fun z : Vertex L n k j =>
      (z : PeriodicLattice.FourTorus L n) = (y : PeriodicLattice.FourTorus L n)) ⟨x, hx⟩
  show f ((y.toSublattice (PeriodicLattice.levelDepth k j)).toSublattice (PeriodicLattice.levelDepth k i)) =
    f (y.toSublattice (PeriodicLattice.levelDepth k i))
  simp only [PeriodicLattice.Site.toSublattice]
  simp only [PeriodicLattice.Site.toSublattice] at h
  rw [h]
theorem logDirectionalDeriv_trivialField (hA : LeftChartFields.Claim)
    (hX : ComplexMatrix2.ExpImaginaryLieMem)
    {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0) {c : Edge L n k 0}
    (hc : c.IsPositivelyOriented) :
    logDirectionalDeriv ℂ (fun X => PeriodicLattice.complexBlockFieldAtLevel 0
        (PeriodicLattice.expTwist X (trivialField L n k 0)) c)
      (PeriodicLattice.complexBlockFieldAtLevel 0 (trivialField L n k 0) c) B = B c := by
  have hBc : B c ∈ PeriodicLattice.complexLieAlgebra := (hB.1 c hc).2
  let W : ℂ → ComplexMatrix2 := fun t => ComplexMatrix2.matExp (t • (Complex.I • B c))
  have hW0 : W 0 = 1 := by simp [W, ComplexMatrix2.matExp, NormedSpace.exp_zero]
  have hd : HasDerivAt W (Complex.I • B c) 0 := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) (Complex.I • B c) (0 : ℂ)
    simpa [NormedSpace.exp_zero] using h
  have hmaps : MapsTo W (Metric.ball 0 1) PeriodicLattice.complexGaugeGroup := fun t _ => by
    have e : W t = ComplexMatrix2.matExp (Complex.I • (t • B c)) := by
      simp only [W, smul_comm t Complex.I]
    rw [e]
    exact hX.2 _ (ComplexMatrix2.traceless.smul_mem t hBc)
  have h := (hA.2.1 1 one_pos W hmaps hd.differentiableAt).2.2.1
  have hf : (fun t : ℂ => ComplexMatrix2.logSeries (PeriodicLattice.complexBlockFieldAtLevel 0
        (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • B) (trivialField L n k 0)) c *
          (PeriodicLattice.complexBlockFieldAtLevel 0 (trivialField L n k 0) c)⁻¹)) =
      fun t => ComplexMatrix2.logSeries (W t * (W 0)⁻¹) := by
    funext t
    have e : PeriodicLattice.complexBlockFieldAtLevel 0
        (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • B) (trivialField L n k 0)) c =
        ComplexMatrix2.matExp (Complex.I • (algebraMap ℂ ℂ t • B) c) * 1 := if_pos hc
    have e' : PeriodicLattice.complexBlockFieldAtLevel 0 (trivialField L n k 0) c = 1 := rfl
    rw [e, e', hW0]
    simp only [W, Pi.smul_apply, Algebra.algebraMap_self, RingHom.id_apply, mul_one, inv_one,
      smul_comm t Complex.I]
  rw [logDirectionalDeriv, hf, h, hd.deriv, hW0, inv_one, mul_one, smul_smul,
    inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
theorem complexIterDeriv_zero_trivialField (hA : LeftChartFields.Claim)
    (hX : ComplexMatrix2.ExpImaginaryLieMem)
    {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0) :
    complexIterDeriv L n k 0 (trivialField L n k 0) B = B := by
  funext c
  by_cases hc : c.IsPositivelyOriented
  · simp only [complexIterDeriv, holLeftDifferential, extendOddly, if_pos hc]
    exact logDirectionalDeriv_trivialField hA hX hB hc
  · have hr := (isPositivelyOriented_or_opposite c).resolve_left hc
    simp only [complexIterDeriv, holLeftDifferential, extendOddly, if_neg hc]
    rw [logDirectionalDeriv_trivialField hA hX hB hr, hB.2 c, neg_neg]
theorem chainBottom_trivialField (hC : YangMills.Construction.ProlongCompositesAndVertexLayers.Statement)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    chainBottom (trivialField L n k k) = trivialField L n k 0 := by
  obtain ⟨hcomp, -, -⟩ := hC.1 L n k hL hn hk
  have h0 := holds_at_identity hcomp.comp_zero_eq (trivialField_mem_fieldSpace k)
  have hp : pure (trivialField L n k k) ≤
      𝓝[fieldSpace L n k k] trivialField L n k k :=
    pure_le_nhdsWithin (trivialField_mem_fieldSpace k)
  have ht := ((hcomp.tendsto 0 (Nat.zero_le k)).mono_left hp).mono_right nhdsWithin_le_nhds
  have e := tendsto_nhds_unique (tendsto_pure_nhds _ _) ht
  rw [chainBottom_eq, ← h0]
  exact e
theorem complexIterDeriv_trivialField (hA : LeftChartFields.Claim)
    (hX : ComplexMatrix2.ExpImaginaryLieMem)
    (hC : YangMills.Construction.ProlongCompositesAndVertexLayers.Statement)
    (hR : RealDerivEqComplexAtChainBottom)
    (hI : SmoothingIterAnalyticNearOne)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0) :
    complexIterDeriv L n k j (trivialField L n k 0) B =
      linearSmoothingIter L n k j B := by
  cases j with
  | zero => exact complexIterDeriv_zero_trivialField hA hX hB
  | succ i =>
    obtain ⟨-, hobj, -⟩ := hC.1 L n k hL hn hk
    have h := holds_at_identity (hR L n k hL hn hk) (trivialField_mem_fieldSpace k) (i + 1) hj ⟨B, hB⟩
    rw [chainBottom_trivialField hC hL hn hk] at h
    have hex := holds_at_identity (hobj.iterDifferential_linear (i + 1) hj)
      (trivialField_mem_fieldSpace 0)
    have hsp := Classical.epsilon_spec hex
    obtain ⟨U, -, -, hd⟩ := hI L n k i hL hn (by omega)
    refine h.symm.trans ?_
    show ((leftDifferentialLinear (smoothingIter L n k (i + 1)) _ ⟨B, hB⟩ :
      edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) = _
    rw [leftDifferentialLinear]
    exact (hsp ⟨B, hB⟩).trans (hd B hB)
theorem covariantIteratesAtTrivialField (hStep : TrivialFieldSmoothingStep.Statement)
    (hRel : TrivialLinearization.AllRelationsStatement)
    (hY : RealLinearMaps.RealLinearMapsStatement)
    (hI : SmoothingIterAnalyticNearOne)
    (hR : RealDerivEqComplexAtChainBottom)
    (hC : YangMills.Construction.ProlongCompositesAndVertexLayers.Statement)
    (hF : LevelwiseMeans.LevelwiseMeansHold)
    (hT : TrivialFieldAtStep)
    (hZ : BlockStructure)
    (hA : LeftChartFields.Claim)
    (hX : ComplexMatrix2.ExpImaginaryLieMem) : CovariantIteratesAtTrivialField := by
  intro L hL n k j hn hk hj
  have hk1 : 1 ≤ k := hk
  have cbf := fun (i : ℕ) (hi : i ≤ k) =>
    complexBlockFieldAtLevel_trivialField (n := n) hF hT hZ hL hn hk1 i hi
  have cid := fun (i : ℕ) (hi : i ≤ k) (B : Edge L n k 0 → ComplexMatrix2)
      (hB : B ∈ edgeFormSpace L n k 0) =>
    complexIterDeriv_trivialField hA hX hC hR hI hL hn hk1 i hi hB
  have st := fun (i : ℕ) (hi : i < k) => hStep L hL n k i hn hi
  have Y := fun (i : ℕ) (hi : i < k) => (hY L n k hL hn hk1).1 i hi
  have crossMem : ∀ i, i < k → ∀ B ∈ edgeFormSpace L n k i,
      crossingSmoothing L n k i B ∈ edgeFormSpace L n k (i + 1) := by
    intro i hi B hB
    obtain ⟨T, hT'⟩ := holds_at_identity (Y i hi).covariantSmoothingDeriv_isLinear
      (trivialField_mem_fieldSpace i)
    have e := hT' ⟨B, hB⟩
    rw [← ((st i hi).1 B hB).2.2]
    exact e ▸ (T ⟨B, hB⟩).2
  have vertexMem : ∀ i, i < k → ∀ l ∈ vertexFunctionSpace L n k i,
      vertexSmoothing L n k i l ∈ vertexFunctionSpace L n k (i + 1) := by
    intro i hi l hl
    obtain ⟨T, hT'⟩ := holds_at_identity (Y i hi).adjointCubeAverage_isLinear
      (trivialField_mem_fieldSpace i)
    have e := hT' ⟨l, hl⟩
    rw [← (st i hi).2 l hl]
    exact e ▸ (T ⟨l, hl⟩).2
  have crossIterMem : ∀ i, i ≤ k → ∀ B ∈ edgeFormSpace L n k 0,
      crossingSmoothingIter L n k i B ∈ edgeFormSpace L n k i := by
    intro i
    induction i with
    | zero => exact fun _ B hB => hB
    | succ i ih => exact fun hi B hB => crossMem i (by omega) _ (ih (by omega) B hB)
  have vertexIterMem : ∀ i, i ≤ k → ∀ l ∈ vertexFunctionSpace L n k 0,
      vertexSmoothingIter L n k i l ∈ vertexFunctionSpace L n k i := by
    intro i
    induction i with
    | zero => exact fun _ l hl => hl
    | succ i ih => exact fun hi l hl => vertexMem i (by omega) _ (ih (by omega) l hl)
  have linIterMem : ∀ i, i ≤ k → ∀ B ∈ edgeFormSpace L n k 0,
      linearSmoothingIter L n k i B ∈ edgeFormSpace L n k i := by
    intro i hi B hB
    cases i with
    | zero => exact hB
    | succ i =>
      obtain ⟨T, hT'⟩ := holds_at_identity (Y i (by omega)).complexIterDeriv_isLinear
        (trivialField_mem_fieldSpace 0)
      have e := hT' ⟨B, hB⟩
      rw [← cid (i + 1) hi B hB]
      exact e ▸ (T ⟨B, hB⟩).2
  have covEq : ∀ i, i ≤ k → ∀ B ∈ edgeFormSpace L n k 0,
      iterCovariantDeriv L n k (trivialField L n k 0) i B =
        crossingSmoothingIter L n k i B := by
    intro i
    induction i with
    | zero => exact fun _ B _ => rfl
    | succ i ih =>
      intro hi B hB
      show covariantSmoothingDeriv
        (PeriodicLattice.complexBlockFieldAtLevel i (trivialField L n k 0))
        (iterCovariantDeriv L n k (trivialField L n k 0) i B) = _
      rw [cbf i (by omega), ih (by omega) B hB]
      exact ((st i (by omega)).1 _ (crossIterMem i (by omega) B hB)).2.2
  have vertexEq : ∀ i, i ≤ k → ∀ l ∈ vertexFunctionSpace L n k 0,
      iterAdjointCubeAverage L n k (trivialField L n k 0) i l =
        vertexSmoothingIter L n k i l := by
    intro i
    induction i with
    | zero => exact fun _ l _ => rfl
    | succ i ih =>
      intro hi l hl
      show adjointCubeAverage
        (PeriodicLattice.complexBlockFieldAtLevel i (trivialField L n k 0))
        (iterAdjointCubeAverage L n k (trivialField L n k 0) i l) = _
      rw [cbf i (by omega), ih (by omega) l hl]
      exact (st i (by omega)).2 _ (vertexIterMem i (by omega) l hl)
  have driftEq : ∀ i, i ≤ k → ∀ B ∈ edgeFormSpace L n k 0,
      iterContourLogDrift L n k (trivialField L n k 0) i B =
        cubeContourAverageIter L n k i B := by
    intro i
    induction i with
    | zero =>
      intro _ B _
      simp [iterContourLogDrift, cubeContourAverageIter]
    | succ i ih =>
      intro hi B hB
      have hi' : i < k := by omega
      have hile : i ≤ k := by omega
      have e := ih hile B hB
      have nMem : cubeContourAverageIter L n k i B ∈ vertexFunctionSpace L n k i := by
        cases i with
        | zero => simp [cubeContourAverageIter]
        | succ i =>
          obtain ⟨T, hT'⟩ := holds_at_identity (Y i (by omega)).iterContourLogDrift_isLinear
            (trivialField_mem_fieldSpace 0)
          have e' := hT' ⟨B, hB⟩
          rw [← e]
          exact e' ▸ (T ⟨B, hB⟩).2
      have hrel := (hRel L hL).1 n k i i hn hi' hile
      have hlin := (hrel.2.2.2.2.1 B hB).1
      have hdN := ((hrel.1.2 _ nMem).2.2).1
      have dMem : vertexCoboundary (cubeContourAverageIter L n k i B) ∈ edgeFormSpace L n k i := by
        have e' : vertexCoboundary (cubeContourAverageIter L n k i B) =
            crossingSmoothingIter L n k i B - linearSmoothingIter L n k i B := by
          rw [hlin, sub_sub_cancel]
        rw [e']
        exact sub_mem (crossIterMem i hile B hB) (linIterMem i hile B hB)
      have hsplit : cubeContourAverage L n k i (linearSmoothingIter L n k i B) =
          cubeContourAverage L n k i (crossingSmoothingIter L n k i B) -
            cubeContourAverage L n k i
              (vertexCoboundary (cubeContourAverageIter L n k i B)) := by
        obtain ⟨T, hT'⟩ := holds_at_identity (Y i hi').contourLogDrift_isLinear
          (trivialField_mem_fieldSpace i)
        have val : ∀ C (hC' : C ∈ edgeFormSpace L n k i), cubeContourAverage L n k i C =
            (T ⟨C, hC'⟩ : Vertex L n k (i + 1) → ComplexMatrix2) := fun C hC' =>
          (((st i hi').1 C hC').2.1).symm.trans (hT' ⟨C, hC'⟩).symm
        have hsub : (⟨linearSmoothingIter L n k i B, linIterMem i hile B hB⟩ :
              edgeFormSpace L n k i) =
            ⟨crossingSmoothingIter L n k i B, crossIterMem i hile B hB⟩ -
              ⟨vertexCoboundary (cubeContourAverageIter L n k i B), dMem⟩ := Subtype.ext hlin
        rw [val _ (linIterMem i hile B hB), val _ (crossIterMem i hile B hB), val _ dMem, hsub,
          map_sub]
        rfl
      show adjointCubeAverage
          (PeriodicLattice.complexBlockFieldAtLevel i (trivialField L n k 0))
          (iterContourLogDrift L n k (trivialField L n k 0) i B) +
        contourLogDrift (PeriodicLattice.complexBlockFieldAtLevel i (trivialField L n k 0))
          (complexIterDeriv L n k i (trivialField L n k 0) B) = _
      rw [cbf i hile, e, cid i hile B hB, (st i hi').2 _ nMem,
        ((st i hi').1 _ (linIterMem i hile B hB)).2.1, hsplit, hdN]
      have hr : restrictVertexFunction (i + 1) (cubeContourAverageIter L n k i B) =
          ∑ m ∈ Finset.range i, restrictVertexFunction (i + 1)
            (cubeContourAverage L n k m (crossingSmoothingIter L n k m B)) := by
        funext y
        rw [Finset.sum_apply]
        show cubeContourAverageIter L n k i B _ = _
        simp only [cubeContourAverageIter, Finset.sum_apply]
        refine Finset.sum_congr rfl fun m _ => ?_
        exact congrFun (restrictVertexFunction_restrictVertexFunction hZ hL hn hi'
          (cubeContourAverage L n k m (crossingSmoothingIter L n k m B))) y
      have hs : cubeContourAverageIter L n k (i + 1) B =
          restrictVertexFunction (i + 1) (cubeContourAverageIter L n k i B) +
            cubeContourAverage L n k i (crossingSmoothingIter L n k i B) := by
        rw [hr]
        simp only [cubeContourAverageIter]
        rw [Finset.sum_range_succ, restrictVertexFunction_self]
      rw [hs]
      abel
  refine ⟨fun B hB => ⟨(cid j hj B hB), covEq j hj B hB, driftEq j hj B hB⟩,
    fun l hl => vertexEq j hj l hl⟩
end YangMills.Construction.Tower.TrivialFieldIterates
end

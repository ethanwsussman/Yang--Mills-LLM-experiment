import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Towers.EntriesOfTheActionAndOfTheCovariantDifferenceProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.RunningCouplingSlope.CoordinateFamiliesAreClosed
import YangMills.Construction.RunningCouplingSlope.TheCommutatorOfTheChainReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheLaplacianOfTheFineLatticeReadsNearCells
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FineLaplacian
open YangMills.Construction.Tower
open YangMills.Construction.Matrices
section RowColumnBound
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq b]
private theorem matrix_norm_le_sqrt_of_row_col (A : Matrix a b ℂ) {R S : ℝ} (hR : 0 ≤ R)
    (hS : 0 ≤ S) (hrow : ∀ p, ∑ q, ‖A p q‖ ≤ R) (hcol : ∀ q, ∑ p, ‖A p q‖ ≤ S) :
    ‖A‖ ≤ Real.sqrt (R * S) := by apply _root_.YangMills.SharedProofs.p34885 <;> assumption
private theorem sum_le_card_mul_of_code {α β : Type} [Fintype α] [Fintype β] {f : α → ℝ}
    {T : α → Prop} {M : ℝ} (hM : 0 ≤ M) (code : α → β) (hf : ∀ x, ¬T x → f x = 0)
    (hb : ∀ x, f x ≤ M) (hinj : ∀ x y, T x → T y → code x = code y → x = y) :
    ∑ x, f x ≤ Fintype.card β * M := by apply _root_.YangMills.SharedProofs.p48454 <;> assumption
end RowColumnBound
private def lieOfCoords (u : Fin 3 → ℂ) : ComplexMatrix2 :=
  ∑ a, u a • ComplexMatrix2.pauliFamily a
private def expConj (A T : ComplexMatrix2) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (Complex.I • A) * T * ComplexMatrix2.matExp (-(Complex.I • A))
private def pauliCoordFn (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ :=
  (1 / 2 : ℂ) • (Matrix.traceLinearMap (Fin 2) ℂ ℂ ∘ₗ
    LinearMap.mulLeft ℂ (ComplexMatrix2.pauliFamily a))
private lemma pauliCoordFn_apply (a : Fin 3) (X : ComplexMatrix2) :
    pauliCoordFn a X = (1 / 2 : ℂ) * Matrix.trace (ComplexMatrix2.pauliFamily a * X) := by
  simp [pauliCoordFn]
private lemma pauliCoordFn_pauli (a c : Fin 3) :
    pauliCoordFn a (ComplexMatrix2.pauliFamily c) = if a = c then 1 else 0 := by
  rw [pauliCoordFn_apply]
  fin_cases a <;> fin_cases c <;>
    simp [ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
      OneLoop.pauliZ, Matrix.trace_fin_two] <;> norm_num
private lemma pauliCoordFn_lieOfCoords (a : Fin 3) (u : Fin 3 → ℂ) :
    pauliCoordFn a (lieOfCoords u) = u a := by
  simp only [lieOfCoords, map_sum, map_smul, pauliCoordFn_pauli, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
private lemma lieOfCoords_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    lieOfCoords (fun a => pauliCoeff a X) = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private lemma pauliCoeff_eq_pauliCoordFn {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a X = pauliCoordFn a X := by
  conv_rhs => rw [← lieOfCoords_pauliCoeff hX]
  rw [pauliCoordFn_lieOfCoords]
private lemma pauli_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private lemma lieOfCoords_mem (u : Fin 3 → ℂ) : lieOfCoords u ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.LieInnerProductProof.pauliCombination_mem_traceless <;> assumption
private lemma conjugateBy_matExp (A T : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy (ComplexMatrix2.matExp (Complex.I • A)) T = expConj A T := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValueFunctions.LocalComponents.conjugateBy_expI <;> assumption
private lemma expConj_mem (A : ComplexMatrix2) {T : ComplexMatrix2}
    (hT : T ∈ ComplexMatrix2.traceless) : expConj A T ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValueFunctions.LocalComponents.expConj_mem <;> assumption
private def expConjEntry (a c : Fin 3) (u : Fin 3 → ℂ) : ℂ :=
  pauliCoordFn a (expConj (lieOfCoords u) (ComplexMatrix2.pauliFamily c))
private lemma pauliCoordFn_expConj (a : Fin 3) (u v : Fin 3 → ℂ) :
    pauliCoordFn a (expConj (lieOfCoords u) (lieOfCoords v)) = ∑ c, v c * expConjEntry a c u := by
  let T : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 :=
    { toFun := expConj (lieOfCoords u)
      map_add' := fun X Y => by simp only [expConj, mul_add, add_mul]
      map_smul' := fun x X => by
        simp only [expConj, mul_smul_comm, smul_mul_assoc, RingHom.id_apply] }
  change pauliCoordFn a (T (lieOfCoords v)) = _
  simp only [lieOfCoords, map_sum, map_smul, smul_eq_mul]
  rfl
private def lieOfCoordsCLM : (Fin 3 → ℂ) →L[ℂ] ComplexMatrix2 :=
  ∑ a, (ContinuousLinearMap.proj a : (Fin 3 → ℂ) →L[ℂ] ℂ).smulRight (ComplexMatrix2.pauliFamily a)
private lemma lieOfCoordsCLM_apply (u : Fin 3 → ℂ) : lieOfCoordsCLM u = lieOfCoords u := by
  simp [lieOfCoordsCLM, lieOfCoords]
private lemma analyticAt_expConjEntry (a c : Fin 3) (u : Fin 3 → ℂ) :
    AnalyticAt ℂ (expConjEntry a c) u := by
  have h0 : AnalyticAt ℂ (fun u : Fin 3 → ℂ => lieOfCoords u) u :=
    (lieOfCoordsCLM.analyticAt u).congr (Eventually.of_forall lieOfCoordsCLM_apply)
  have hs : AnalyticAt ℂ (fun u : Fin 3 → ℂ => Complex.I • lieOfCoords u) u :=
    show AnalyticAt ℂ ((Complex.I : ℂ) • fun u : Fin 3 → ℂ => lieOfCoords u) u from h0.const_smul
  have e1 : AnalyticAt ℂ
      (fun u : Fin 3 → ℂ => ComplexMatrix2.matExp (Complex.I • lieOfCoords u)) u :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) (𝔸 := ComplexMatrix2) _).comp_of_eq hs rfl
  have e2 : AnalyticAt ℂ
      (fun u : Fin 3 → ℂ => ComplexMatrix2.matExp (-(Complex.I • lieOfCoords u))) u :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) (𝔸 := ComplexMatrix2) _).comp_of_eq hs.neg rfl
  have h1 : AnalyticAt ℂ
      (fun u : Fin 3 → ℂ => expConj (lieOfCoords u) (ComplexMatrix2.pauliFamily c)) u :=
    (e1.mul analyticAt_const).mul e2
  exact (LinearMap.toContinuousLinearMap (pauliCoordFn a)).analyticAt _ |>.comp h1
private lemma expConjEntry_bounded : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a c : Fin 3) (u : Fin 3 → ℂ), ‖u‖ ≤ 1 →
    ‖expConjEntry a c u‖ ≤ K := by
  let F : (Fin 3 → ℂ) → (Fin 3 × Fin 3 → ℂ) := fun u p => expConjEntry p.1 p.2 u
  have c1 : ∀ p : Fin 3 × Fin 3, Continuous (expConjEntry p.1 p.2) := fun p =>
    continuous_iff_continuousAt.2 fun u => (analyticAt_expConjEntry p.1 p.2 u).continuousAt
  have hF : Continuous F := continuous_pi c1
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Fin 3 → ℂ) 1).exists_bound_of_continuousOn
    hF.continuousOn
  have h0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (by simp))
  refine ⟨K, h0, fun a c u hu => ?_⟩
  exact (norm_le_pi_norm (F u) (a, c)).trans (hK u (by simpa using hu))
section Incidence
variable {L n k : ℕ}
private abbrev toFineVertex {m : ℕ} (y : Vertex L n k m) : Vertex L n k 0 :=
  y.toSublattice (PeriodicLattice.levelDepth k 0)
private lemma toFineVertex_self (x : Vertex L n k 0) : toFineVertex x = x := by apply _root_.YangMills.DeltaSharedProofs.p39288 <;> assumption
private def edgeAxis (b : PositiveEdge L n k 0) : Fin 4 := b.2.choose
private lemma target_eq (b : PositiveEdge L n k 0) :
    b.1.target = b.1.source + PeriodicLattice.unitStep L n _ (edgeAxis b) := by
  have h : b.1.target - b.1.source = PeriodicLattice.unitStep L n _ (edgeAxis b) := b.2.choose_spec
  rw [← h]
  abel
private lemma edge_ext_source {b b' : PositiveEdge L n k 0} (h : b.1.source = b'.1.source)
    (hd : edgeAxis b = edgeAxis b') : b = b' := by
  apply Subtype.ext
  apply PeriodicLattice.Bond.ext h
  rw [target_eq b, target_eq b', h, hd]
private lemma edge_ext_target {b b' : PositiveEdge L n k 0} (h : b.1.target = b'.1.target)
    (hd : edgeAxis b = edgeAxis b') : b = b' := by
  apply Subtype.ext
  refine PeriodicLattice.Bond.ext ?_ h
  have e := target_eq b
  have e' := target_eq b'
  rw [h, hd] at e
  exact add_right_cancel (e.symm.trans e')
private def IsEndpoint (s : Vertex L n k 0) (b : PositiveEdge L n k 0) : Prop :=
  s = b.1.source ∨ s = b.1.target
private def edgeCoords (z : TripleCoordIndex L n k → ℂ) (b : PositiveEdge L n k 0) : Fin 3 → ℂ :=
  fun e => z (.inl (.inl (e, b)))
private def incidence (z : TripleCoordIndex L n k → ℂ) :
    Matrix (Fin 3 × Vertex L n k 0) (Fin 3 × PositiveEdge L n k 0) ℂ :=
  open Classical in
  fun p q =>
    (if p.2 = q.2.1.target then expConjEntry q.1 p.1 (edgeCoords z q.2) else 0) -
      (if p.2 = q.2.1.source then (if q.1 = p.1 then 1 else 0) else 0)
private lemma incidence_eq_zero (z : TripleCoordIndex L n k → ℂ) (p : Fin 3 × Vertex L n k 0)
    (q : Fin 3 × PositiveEdge L n k 0) (h : ¬IsEndpoint p.2 q.2) : incidence z p q = 0 := by
  simp only [IsEndpoint, not_or] at h
  simp [incidence, h.1, h.2]
private lemma norm_edgeCoords_le [Fintype (TripleCoordIndex L n k)]
    (z : TripleCoordIndex L n k → ℂ) (b : PositiveEdge L n k 0) : ‖edgeCoords z b‖ ≤ ‖z‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => norm_le_pi_norm z _
private lemma norm_ite_le {c : Prop} [Decidable c] {x : ℂ} {K : ℝ} (hK : 0 ≤ K) (h : ‖x‖ ≤ K) :
    ‖(if c then x else 0 : ℂ)‖ ≤ K := by
  split_ifs
  · exact h
  · simpa using hK
private lemma norm_incidence_le [Fintype (TripleCoordIndex L n k)] {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ (a c : Fin 3) (u : Fin 3 → ℂ), ‖u‖ ≤ 1 → ‖expConjEntry a c u‖ ≤ K)
    {z : TripleCoordIndex L n k → ℂ} (hz : ‖z‖ ≤ 1) (p : Fin 3 × Vertex L n k 0)
    (q : Fin 3 × PositiveEdge L n k 0) : ‖incidence z p q‖ ≤ K + 1 := by
  classical
  have h1 := norm_ite_le (c := p.2 = q.2.1.target) hK
    (hb q.1 p.1 _ ((norm_edgeCoords_le z q.2).trans hz))
  have h2 : ‖(if p.2 = q.2.1.source then (if q.1 = p.1 then 1 else 0) else 0 : ℂ)‖ ≤ 1 := by
    split_ifs <;> simp
  refine (norm_sub_le _ _).trans ?_
  convert add_le_add h1 h2
private def rowLabel (s : Vertex L n k 0) (q : Fin 3 × PositiveEdge L n k 0) :
    Fin 3 × Bool × Fin 4 :=
  open Classical in (q.1, decide (s = q.2.1.source), edgeAxis q.2)
private lemma rowLabel_inj (s : Vertex L n k 0) (q q' : Fin 3 × PositiveEdge L n k 0)
    (h : IsEndpoint s q.2) (h' : IsEndpoint s q'.2) (e : rowLabel s q = rowLabel s q') :
    q = q' := by
  obtain ⟨d, b⟩ := q
  obtain ⟨d', b'⟩ := q'
  simp only [rowLabel, Prod.mk.injEq, decide_eq_decide] at e
  obtain ⟨rfl, e1, e2⟩ := e
  simp only [IsEndpoint] at h h'
  have : b = b' := by
    by_cases ht : s = b.1.source
    · exact edge_ext_source (ht.symm.trans (e1.1 ht)) e2
    · have ht' : ¬s = b'.1.source := fun x => ht (e1.2 x)
      exact edge_ext_target ((h.resolve_left ht).symm.trans (h'.resolve_left ht')) e2
  rw [this]
private def columnLabel (b : PositiveEdge L n k 0) (p : Fin 3 × Vertex L n k 0) : Fin 3 × Bool :=
  open Classical in (p.1, decide (p.2 = b.1.source))
private lemma columnLabel_inj (b : PositiveEdge L n k 0) (p p' : Fin 3 × Vertex L n k 0)
    (h : IsEndpoint p.2 b) (h' : IsEndpoint p'.2 b) (e : columnLabel b p = columnLabel b p') :
    p = p' := by
  simp only [columnLabel, Prod.mk.injEq, decide_eq_decide] at e
  refine Prod.ext e.1 ?_
  by_cases ht : p.2 = b.1.source
  · exact ht.trans (e.2.1 ht).symm
  · have ht' : ¬p'.2 = b.1.source := fun x => ht (e.2.2 x)
    simp only [IsEndpoint] at h h'
    exact (h.resolve_left ht).trans (h'.resolve_left ht').symm
private lemma cellDist_le_of_endpoint
    (hc : (∀ y y' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k),
      cellDist y y' = cellDist y' y) ∧
    (∀ y y' y'' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k),
      cellDist y y'' ≤ cellDist y y' + cellDist y' y'') ∧
    (∀ (x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0)) (μ : Fin 4),
      cellDist (fineVertexCell (L := L) (n := n) (k := k) x)
        (fineVertexCell (L := L) (n := n) (k := k) (x + PeriodicLattice.unitStep L n _ μ)) ≤ 4))
    {s : Vertex L n k 0} {b : PositiveEdge L n k 0} (h : IsEndpoint s b) :
    cellDist (levelVertexCell b.1.source) (levelVertexCell s) ≤ 8 ∧
      cellDist (levelVertexCell s) (levelVertexCell b.1.source) ≤ 8 := by
  obtain ⟨sym, tri, near⟩ := hc
  have self_near : ∀ x : Vertex L n k 0,
      cellDist (fineVertexCell (L := L) (n := n) (k := k) x) (fineVertexCell x) ≤ 8 := by
    intro x
    have h1 := near x 0
    have h2 := tri (fineVertexCell x) (fineVertexCell (x + PeriodicLattice.unitStep L n _ 0))
      (fineVertexCell x)
    rw [sym (fineVertexCell (x + PeriodicLattice.unitStep L n _ 0))] at h2
    linarith
  have cell0 : ∀ x : Vertex L n k 0, levelVertexCell x = fineVertexCell x := fun x => by
    rw [levelVertexCell]
    exact congrArg _ (toFineVertex_self x)
  suffices H : cellDist (levelVertexCell b.1.source) (levelVertexCell s) ≤ 8 from
    ⟨H, by rw [sym]; exact H⟩
  rw [cell0, cell0]
  rcases h with rfl | rfl
  · exact self_near _
  · rw [target_eq b]
    exact (near _ _).trans (by norm_num)
private def edgeCoordsCLM [Fintype (TripleCoordIndex L n k)] (b : PositiveEdge L n k 0) :
    (TripleCoordIndex L n k → ℂ) →L[ℂ] (Fin 3 → ℂ) :=
  ContinuousLinearMap.pi fun e => ContinuousLinearMap.proj (.inl (.inl (e, b)))
private lemma analyticAt_ite {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : Prop}
    [Decidable c] {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun w => if c then f w else 0) x := by
  by_cases h : c
  · simpa [h] using hf
  · simpa [h] using analyticAt_const
private def edgeIndexCell (q : Fin 3 × PositiveEdge L n k 0) : Vertex L n k k :=
  levelVertexCell q.2.1.source
private theorem incidence_isLocallyHolomorphic
    (hc : (∀ y y' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k),
      cellDist y y' = cellDist y' y) ∧
    (∀ y y' y'' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k),
      cellDist y y'' ≤ cellDist y y' + cellDist y' y'') ∧
    (∀ (x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0)) (μ : Fin 4),
      cellDist (fineVertexCell (L := L) (n := n) (k := k) x)
        (fineVertexCell (L := L) (n := n) (k := k) (x + PeriodicLattice.unitStep L n _ μ)) ≤ 4))
    {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ (a c : Fin 3) (u : Fin 3 → ℂ), ‖u‖ ≤ 1 → ‖expConjEntry a c u‖ ≤ K)
    [Fintype (TripleCoordIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k 0)]
    [DecidableEq (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × Vertex L n k 0)] :
    IsLocallyHolomorphicFamily tripleCoordIndexCell edgeIndexCell fineIndexCell
      (incidence (L := L) (n := n) (k := k)) 1
      (Real.sqrt ((Fintype.card (Fin 3 × Bool × Fin 4) * (K + 1)) *
        (Fintype.card (Fin 3 × Bool) * (K + 1)))) 8 where
  holomorphic := by
    classical
    intro p q z _
    have h : AnalyticAt ℂ
        (fun z : TripleCoordIndex L n k → ℂ => expConjEntry q.1 p.1 (edgeCoords z q.2)) z :=
      (analyticAt_expConjEntry _ _ _).comp_of_eq ((edgeCoordsCLM q.2).analyticAt z) rfl
    exact (analyticAt_ite h).sub analyticAt_const
  norm_le := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 hz).le
    refine matrix_norm_le_sqrt_of_row_col _ (by positivity) (by positivity)
      (fun p => ?_) (fun q => ?_)
    · exact sum_le_card_mul_of_code (by positivity) (rowLabel p.2)
        (T := fun q => IsEndpoint p.2 q.2)
        (fun q h => by rw [incidence_eq_zero z p q h, norm_zero])
        (fun q => norm_incidence_le hK hb hz1 p q) (rowLabel_inj p.2)
    · exact sum_le_card_mul_of_code (by positivity) (columnLabel q.2)
        (T := fun p => IsEndpoint p.2 q.2)
        (fun p h => by rw [incidence_eq_zero z p q h, norm_zero])
        (fun p => norm_incidence_le hK hb hz1 p q) (columnLabel_inj q.2)
  depends_near := by
    intro p q z _ z' _ hz
    by_cases h : IsEndpoint p.2 q.2
    · have near := (cellDist_le_of_endpoint hc h).1
      have e : edgeCoords z q.2 = edgeCoords z' q.2 := funext fun e => hz _ near
      simp only [incidence, e]
    · rw [incidence_eq_zero z p q h, incidence_eq_zero z' p q h]
  eq_zero_of_far := by
    intro z _ p q h
    refine incidence_eq_zero z p q fun ht => ?_
    exact absurd (cellDist_le_of_endpoint hc ht).2 (not_le.2 h)
private lemma complexChainPoint_fine_edge (z : TripleCoordIndex L n k → ℂ)
    (b : PositiveEdge L n k 0) :
    (complexChainPoint z).fine b.1 =
      ComplexMatrix2.matExp (Complex.I • lieOfCoords (edgeCoords z b)) := by
  have e : complexFineValues z b.1 = lieOfCoords (edgeCoords z b) := by
    simp only [complexFineValues, edgeFormOfPositiveValues, dif_pos b.2]
    rfl
  simp only [complexChainPoint, PeriodicLattice.expTwist, if_pos b.2, unitPoint, mul_one, e]
private lemma pauliCoeffs_covDiff (z : TripleCoordIndex L n k → ℂ)
    (f : Fin 3 × Vertex L n k 0 → ℂ) (a : Fin 3) (b : PositiveEdge L n k 0) :
    toPauliCoeffs (restrictToPositiveEdges ((finestMesh L k)⁻¹ •
        covDiff (complexChainPoint z).fine (ofPauliCoeffs f))) (a, b) =
      (((finestMesh L k)⁻¹ : ℝ) : ℂ) *
        ((∑ c, f (c, b.1.target) * expConjEntry a c (edgeCoords z b)) - f (a, b.1.source)) := by
  have e1 : covDiff (complexChainPoint z).fine (ofPauliCoeffs f) b.1 =
      expConj (lieOfCoords (edgeCoords z b)) (lieOfCoords fun c => f (c, b.1.target)) -
        lieOfCoords fun c => f (c, b.1.source) := by
    simp only [covDiff, extendOddly, if_pos b.2]
    rw [complexChainPoint_fine_edge, conjugateBy_matExp]
    rfl
  have hm : expConj (lieOfCoords (edgeCoords z b)) (lieOfCoords fun c => f (c, b.1.target)) -
      (lieOfCoords fun c => f (c, b.1.source)) ∈ ComplexMatrix2.traceless :=
    Submodule.sub_mem _ (expConj_mem _ (lieOfCoords_mem _)) (lieOfCoords_mem _)
  change pauliCoeff a ((finestMesh L k)⁻¹ •
    covDiff (complexChainPoint z).fine (ofPauliCoeffs f) b.1) = _
  rw [e1, ← Complex.coe_smul, pauliCoeff_eq_pauliCoordFn (Submodule.smul_mem _ _ hm), map_smul,
    map_sub, pauliCoordFn_expConj, pauliCoordFn_lieOfCoords, smul_eq_mul]
private theorem kernelOfMap_eq {N N' : Type} [Fintype N] (M : (N → ℂ) → N' → ℂ)
    (T : PeriodicOperators.KernelMatrix N N') (h : ∀ f ι', M f ι' = ∑ ι, T ι' ι * f ι) :
    PeriodicOperators.kernelOfMap M = T := by
  classical
  have hT : PeriodicOperators.Represents T M := fun f =>
    ⟨fun ι' => (hasSum_fintype _).summable, funext fun ι' => by
      rw [h, PeriodicOperators.applyKernel, tsum_fintype]⟩
  have h0 : PeriodicOperators.Represents (PeriodicOperators.kernelOfMap M) M :=
    Classical.epsilon_spec (p := fun T => PeriodicOperators.Represents T M) ⟨T, hT⟩
  funext ι' ι
  have h1 := congrFun (h0 (Pi.single ι 1)).2 ι'
  rw [PeriodicOperators.applyKernel, tsum_fintype, h] at h1
  simpa [Pi.single_apply] using h1
abbrev _root_.YangMills.SharedProofs.p41761 := @kernelOfMap_eq
private lemma finsum_pairs [Fintype (Vertex L n k 0)] (f : Fin 3 × Vertex L n k 0 → ℂ) :
    ∑ᶠ p, f p = ∑ a : Fin 3, ∑ s : Vertex L n k 0, f (a, s) := by
  rw [finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
private lemma sum_pairs [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Vertex L n k 0)]
    (f : Fin 3 × Vertex L n k 0 → ℂ) :
    ∑ p, f p = ∑ a : Fin 3, ∑ s : Vertex L n k 0, f (a, s) := by
  rw [← finsum_eq_sum_of_fintype f]
  exact finsum_pairs f
private lemma rescaled_D_eq [Fintype (Fin 3 × Vertex L n k 0)] (z : TripleCoordIndex L n k → ℂ) :
    (rescaledOperators L n k (complexChainPoint z).fine).D =
      fun q p => (((finestMesh L k)⁻¹ : ℝ) : ℂ) * incidence z p q := by
  classical
  have : Finite (Vertex L n k 0) :=
    Finite.of_injective (fun s => ((0 : Fin 3), s)) fun s s' h => by simpa using h
  let _ : Fintype (Vertex L n k 0) := Fintype.ofFinite _
  refine kernelOfMap_eq (N := Fin 3 × Vertex L n k 0) (N' := Fin 3 × PositiveEdge L n k 0) _ _
    fun f q => ?_
  obtain ⟨a, b⟩ := q
  refine (pauliCoeffs_covDiff z f a b).trans ?_
  rw [sum_pairs]
  have col : ∀ c : Fin 3, ∑ s : Vertex L n k 0,
      (((finestMesh L k)⁻¹ : ℝ) : ℂ) * incidence z (c, s) (a, b) * f (c, s) =
      (((finestMesh L k)⁻¹ : ℝ) : ℂ) * (f (c, b.1.target) * expConjEntry a c (edgeCoords z b) -
        if a = c then f (c, b.1.source) else 0) := by
    intro c
    have t : ∀ s : Vertex L n k 0, incidence z (c, s) (a, b) * f (c, s) =
        (if s = b.1.target then expConjEntry a c (edgeCoords z b) * f (c, s) else 0) -
          (if s = b.1.source then (if a = c then f (c, s) else 0) else 0) := by
      intro s
      simp only [incidence, sub_mul, ite_mul, zero_mul, one_mul]
    simp only [mul_assoc, t, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [mul_comm (f _)]
  simp only [col, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
private lemma rescaled_Delta_eq (hL : 0 < L) [Fintype (Fin 3 × PositiveEdge L n k 0)]
    [Fintype (Fin 3 × Vertex L n k 0)] (z : TripleCoordIndex L n k → ℂ) :
    ((finestMesh L k ^ 2 : ℝ) : ℂ) •
      (Matrix.of (rescaledOperators L n k (complexChainPoint z).fine).Delta :
        Matrix (Fin 3 × Vertex L n k 0) (Fin 3 × Vertex L n k 0) ℂ) =
      incidence z * (incidence z).transpose := by
  have hη : finestMesh L k ≠ 0 := by
    unfold finestMesh meshAt
    exact (zpow_pos (by exact_mod_cast hL) _).ne'
  have hηc : ((finestMesh L k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hη
  have heta : (rescaledOperators L n k (complexChainPoint z).fine).eta = finestMesh L k := rfl
  ext p p'
  have e : (rescaledOperators L n k (complexChainPoint z).fine).Delta p p' =
      ∑ q, (((finestMesh L k)⁻¹ : ℝ) : ℂ) * incidence z p q *
        ((((finestMesh L k)⁻¹ : ℝ) : ℂ) * incidence z p' q) := by
    simp only [RescaledOperators.Delta, RescaledOperators.Dt, PeriodicOperators.compKernel,
      meshTranspose, PeriodicOperators.wTranspose, meshWeight, heta, rescaled_D_eq z]
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun q _ => ?_
    have h1 : finestMesh L k ^ 4 / finestMesh L k ^ 4 = 1 := div_self (pow_ne_zero _ hη)
    rw [h1]
    simp
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  push_cast
  field_simp
end Incidence
theorem fineLaplacianIsLocallyHolomorphic_holds (hcl : LocallyHolomorphicFamiliesClosed)
    (hcells : NeighbouringFineVertexCells) :
    FineLaplacianIsLocallyHolomorphic := by
  intro L hL k _
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨K, hK, hb⟩ := expConjEntry_bounded
  refine ⟨1, Real.sqrt ((Fintype.card (Fin 3 × Bool × Fin 4) * (K + 1)) *
      (Fintype.card (Fin 3 × Bool) * (K + 1))) *
      Real.sqrt ((Fintype.card (Fin 3 × Bool × Fin 4) * (K + 1)) *
      (Fintype.card (Fin 3 × Bool) * (K + 1))), 8 + 2 * 8, one_pos,
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), by norm_num,
    Eventually.of_forall fun n => ?_⟩
  intro iW iT iS dS
  obtain ⟨sym, tri, _, near⟩ := hcells L hL n k
  let _ : Fintype (Fin 3 × PositiveEdge L n k 0) :=
    Fintype.ofInjective (Sum.inl : _ → LevelFormIndex L n k) Sum.inl_injective
  let _ : DecidableEq (Fin 3 × PositiveEdge L n k 0) := Classical.decEq _
  have A := incidence_isLocallyHolomorphic (L := L) (n := n) (k := k) ⟨sym, tri, near⟩ hK hb
  have B := (hcl L n k).transpose (by norm_num) A
  have P := (hcl L n k).mul (by norm_num) (by norm_num) A B
  have e : (fun z : TripleCoordIndex L n k → ℂ => ((finestMesh L k ^ 2 : ℝ) : ℂ) •
      (Matrix.of (rescaledOperators L n k (complexChainPoint z).fine).Delta :
        Matrix (Fin 3 × Vertex L n k 0) (Fin 3 × Vertex L n k 0) ℂ)) =
      fun z => incidence z * (incidence z).transpose :=
    funext fun z => rescaled_Delta_eq hL0 z
  rw [e]
  exact P
end YangMills.Construction.RunningCouplingSlope.FineLaplacian
end

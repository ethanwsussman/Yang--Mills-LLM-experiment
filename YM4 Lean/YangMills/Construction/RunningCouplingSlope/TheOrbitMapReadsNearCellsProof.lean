import YangMills.Construction.RunningCouplingSlope.TheGaugeShiftReadsNearCellsProof
import YangMills.Construction.Towers.StepOfACriticalBranchInTheChartProof
import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG
import YangMills.Construction.RunningCouplingSlope.CellsOfNeighbouringFineSites
import YangMills.Construction.RunningCouplingSlope.TheOrbitMapReadsNearCells
import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChartProof
import YangMills.Construction.Towers.StepKernelsNearOneOnASideProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.GaugeOrbitLocality
open Tower Matrices
section PauliComponents
private def pauliLinearForm (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
  map_add' X Y := by
    fin_cases a <;> simp <;> ring
  map_smul' c X := by
    fin_cases a <;> simp <;> ring
private theorem pauliCoeff_eq_pauliLinearForm {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a X = pauliLinearForm a X := by
  simp only [pauliCoeff, dif_pos h]
  rfl
private theorem eq_sum_pauliCoeff {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    X = ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.NearIdentityStepKernels.eq_sum_pauliCoeff_smul <;> assumption
private def pauliSum (w : Fin 3 → ℂ) : ComplexMatrix2 := ∑ c, w c • ComplexMatrix2.pauliFamily c
private theorem matExp_mul_matExp_neg (Z : ComplexMatrix2) :
    ComplexMatrix2.matExp Z * ComplexMatrix2.matExp (-Z) = 1 := by apply _root_.YangMills.Construction.SpinHarmonics.matExp_mul_matExp_neg <;> assumption
private theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
private def adjointEntry (w : Fin 3 → ℂ) (a a' : Fin 3) : ℂ :=
  pauliLinearForm a (ComplexMatrix2.matExp (Complex.I • pauliSum w) * ComplexMatrix2.pauliFamily a' *
    ComplexMatrix2.matExp (-(Complex.I • pauliSum w)))
private def adjointArgument : (Fin 3 → ℂ) →ₗ[ℂ] ComplexMatrix2 where
  toFun w := Complex.I • pauliSum w
  map_add' w w' := by
    simp [pauliSum, add_smul, Finset.sum_add_distrib, smul_add]
  map_smul' c w := by
    simp [pauliSum, Finset.smul_sum, mul_smul, smul_comm c Complex.I]
private theorem analyticAt_adjointEntry (a a' : Fin 3) (w₀ : Fin 3 → ℂ) :
    AnalyticAt ℂ (fun w => adjointEntry w a a') w₀ := by
  have hS : AnalyticAt ℂ (fun w => Complex.I • pauliSum w) w₀ :=
    (LinearMap.toContinuousLinearMap adjointArgument).analyticAt w₀
  have hE : AnalyticAt ℂ (fun w => ComplexMatrix2.matExp (Complex.I • pauliSum w)) w₀ :=
    AnalyticAt.comp (g := NormedSpace.exp) (NormedSpace.exp_analytic (𝕂 := ℂ) _) hS
  have hE' : AnalyticAt ℂ (fun w => ComplexMatrix2.matExp (-(Complex.I • pauliSum w))) w₀ :=
    AnalyticAt.comp (g := NormedSpace.exp) (NormedSpace.exp_analytic (𝕂 := ℂ) _) hS.neg
  have hP : AnalyticAt ℂ (fun w => ComplexMatrix2.matExp (Complex.I • pauliSum w) *
      ComplexMatrix2.pauliFamily a' * ComplexMatrix2.matExp (-(Complex.I • pauliSum w))) w₀ :=
    (hE.mul analyticAt_const).mul hE'
  exact AnalyticAt.comp (g := pauliLinearForm a)
    ((LinearMap.toContinuousLinearMap (pauliLinearForm a)).analyticAt _) hP
private theorem exists_adjointEntry_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Fin 3 → ℂ, ‖w‖ ≤ 1 → ∀ a a', ‖adjointEntry w a a'‖ ≤ K := by
  have hc : Continuous fun w : Fin 3 → ℂ =>
      (fun a a' => adjointEntry w a a' : Fin 3 → Fin 3 → ℂ) :=
    continuous_pi fun a => continuous_pi fun a' =>
      continuous_iff_continuousAt.2 fun w => (analyticAt_adjointEntry a a' w).continuousAt
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Fin 3 → ℂ) 1).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun w hw a a' => ?_⟩
  have h := hK w (by simpa using hw)
  exact ((norm_le_pi_norm (fun a' => adjointEntry w a a') a').trans
    (norm_le_pi_norm (fun a a' => adjointEntry w a a') a)).trans (h.trans (le_max_left _ _))
private theorem pauliCoeff_conjugateBy_sub (w : Fin 3 → ℂ) {A B : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.traceless) (hB : B ∈ ComplexMatrix2.traceless)
    (hD : ComplexMatrix2.conjugateBy (ComplexMatrix2.matExp (Complex.I • pauliSum w)) A - B ∈
      ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (ComplexMatrix2.conjugateBy (ComplexMatrix2.matExp (Complex.I • pauliSum w)) A - B) =
      ∑ a', adjointEntry w a a' * pauliCoeff a' A - pauliCoeff a B := by
  rw [pauliCoeff_eq_pauliLinearForm hD, map_sub, pauliCoeff_eq_pauliLinearForm hB]
  congr 1
  rw [ComplexMatrix2.conjugateBy, matExp_inv]
  conv_lhs => rw [eq_sum_pauliCoeff hA]
  rw [Finset.mul_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [adjointEntry, mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
private theorem conjugateBy_mem_hermitianTraceless {A B : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) (hB : B ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy (ComplexMatrix2.matExp (Complex.I • A)) B ∈
      ComplexMatrix2.hermitianTraceless := by
  obtain ⟨h1, h2⟩ := hA
  obtain ⟨h3, h4⟩ := hB
  have e : star (Complex.I • A) = -(Complex.I • A) := by
    rw [star_smul, Matrix.star_eq_conjTranspose, ← h1]
    simp
  have hst : (ComplexMatrix2.matExp (Complex.I • A)).conjTranspose =
      ComplexMatrix2.matExp (-(Complex.I • A)) := by
    rw [← Matrix.star_eq_conjTranspose, ComplexMatrix2.matExp, NormedSpace.star_exp, e]
  have hst' : (ComplexMatrix2.matExp (-(Complex.I • A))).conjTranspose =
      ComplexMatrix2.matExp (Complex.I • A) := by
    rw [← hst, Matrix.conjTranspose_conjTranspose]
  refine ⟨?_, ?_⟩
  · rw [ComplexMatrix2.conjugateBy, matExp_inv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hst', hst, ← h3, mul_assoc]
  · change Matrix.trace _ = 0
    have h5 := matExp_mul_matExp_neg (-(Complex.I • A))
    rw [neg_neg] at h5
    rw [ComplexMatrix2.conjugateBy, matExp_inv, Matrix.trace_mul_comm, ← mul_assoc, h5, one_mul]
    exact h4
end PauliComponents
section SchurTest
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
private def euclidNorm (x : ι → ℂ) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖
private theorem euclidNorm_nonneg (x : ι → ℂ) : 0 ≤ euclidNorm x := norm_nonneg _
private theorem euclidNorm_sq (x : ι → ℂ) : euclidNorm x ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  unfold euclidNorm
  rw [EuclideanSpace.norm_sq_eq]
variable [DecidableEq ι]
private theorem opNorm_le_of_euclidNorm (A : Matrix ι' ι ℂ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ x, euclidNorm (A.mulVec x) ≤ K * euclidNorm x) : ‖A‖ ≤ K := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  exact h x.ofLp
private theorem schurTest (A : Matrix ι' ι ℂ) {R : ℝ} (hR : 0 ≤ R) (hrow : ∀ p, ∑ q, ‖A p q‖ ≤ R)
    (hcol : ∀ q, ∑ p, ‖A p q‖ ≤ R) : ‖A‖ ≤ R := by
  refine opNorm_le_of_euclidNorm _ hR fun x => ?_
  have hv : ∀ p, ‖A.mulVec x p‖ ≤ ∑ q, ‖A p q‖ * ‖x q‖ := by
    intro p
    simp only [Matrix.mulVec, dotProduct]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => (norm_mul _ _).le)
  have hcs : ∀ p, (∑ q, ‖A p q‖ * ‖x q‖) ^ 2 ≤ R * ∑ q, ‖A p q‖ * ‖x q‖ ^ 2 := by
    intro p
    have h1 := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι)
      (r := fun q => ‖A p q‖ * ‖x q‖) (f := fun q => ‖A p q‖) (g := fun q => ‖A p q‖ * ‖x q‖ ^ 2)
      (fun q _ => norm_nonneg _) (fun q _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun q _ => le_of_eq (by ring))
    exact h1.trans (mul_le_mul_of_nonneg_right (hrow p)
      (Finset.sum_nonneg fun q _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))
  have hmain : euclidNorm (A.mulVec x) ^ 2 ≤ (R * euclidNorm x) ^ 2 := by
    calc euclidNorm (A.mulVec x) ^ 2 = ∑ p, ‖A.mulVec x p‖ ^ 2 := euclidNorm_sq _
      _ ≤ ∑ p, (∑ q, ‖A p q‖ * ‖x q‖) ^ 2 :=
          Finset.sum_le_sum fun p _ => pow_le_pow_left₀ (norm_nonneg _) (hv p) 2
      _ ≤ ∑ p, R * ∑ q, ‖A p q‖ * ‖x q‖ ^ 2 := Finset.sum_le_sum fun p _ => hcs p
      _ = R * ∑ q, (∑ p, ‖A p q‖) * ‖x q‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ ≤ R * ∑ q, R * ‖x q‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => ?_) hR
          exact mul_le_mul_of_nonneg_right (hcol q) (sq_nonneg _)
      _ = (R * euclidNorm x) ^ 2 := by
          rw [← Finset.mul_sum, mul_pow, euclidNorm_sq]
          ring
  exact (sq_le_sq₀ (euclidNorm_nonneg _) (mul_nonneg hR (euclidNorm_nonneg _))).1 hmain
end SchurTest
section OrbitMatrix
variable {P S I : Type}
open Classical in
private def orbitMatrix (col : P → Fin 3) (hd tl : P → S) (idx : P → Fin 3 → I) (z : I → ℂ) :
    Matrix P (Fin 3 × S) ℂ :=
  fun p q => (if q.2 = hd p then adjointEntry (fun c => z (idx p c)) (col p) q.1 else 0) -
    if q.2 = tl p ∧ q.1 = col p then 1 else 0
variable (col : P → Fin 3) (hd tl : P → S) (idx : P → Fin 3 → I)
open Classical in
private theorem sum_ite_snd_eq [Fintype (Fin 3 × S)] {E : Type} [AddCommMonoid E] (f : Fin 3 → E)
    (h : S) : ∑ q : Fin 3 × S, (if q.2 = h then f q.1 else 0) = ∑ a, f a := by
  have e : (Finset.univ.filter fun q : Fin 3 × S => q.2 = h) =
      Finset.univ.map ⟨fun a => (a, h), fun a b e => (Prod.ext_iff.1 e).1⟩ := by
    ext ⟨a, x⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro h0
      refine ⟨a, ?_⟩
      change (a, h) = (a, x)
      rw [h0]
    · rintro ⟨a', e⟩
      exact (congrArg Prod.snd e).symm
  rw [← Finset.sum_filter, e, Finset.sum_map]
  rfl
open Classical in
private theorem sum_ite_point [Fintype (Fin 3 × S)] (h : S) (a : Fin 3) :
    ∑ q : Fin 3 × S, (if q.2 = h ∧ q.1 = a then (1 : ℝ) else 0) = 1 := by
  have e : ∀ q : Fin 3 × S, (if q.2 = h ∧ q.1 = a then (1 : ℝ) else 0) =
      if q.2 = h then (if q.1 = a then (1 : ℝ) else 0) else 0 := by
    intro q
    by_cases h1 : q.2 = h <;> simp [h1]
  simp only [e]
  rw [sum_ite_snd_eq (fun a' => if a' = a then (1 : ℝ) else 0) h]
  simp
private theorem orbitMatrix_analytic [Fintype I] (p : P) (q : Fin 3 × S) (s : Set (I → ℂ)) :
    AnalyticOnNhd ℂ (fun z => orbitMatrix col hd tl idx z p q) s := by
  intro z₀ _
  have hw : AnalyticAt ℂ (fun z : I → ℂ => fun c => z (idx p c)) z₀ :=
    (ContinuousLinearMap.pi fun c => ContinuousLinearMap.proj (idx p c) :
      (I → ℂ) →L[ℂ] Fin 3 → ℂ).analyticAt z₀
  have ht : AnalyticAt ℂ (fun z : I → ℂ => adjointEntry (fun c => z (idx p c)) (col p) q.1) z₀ :=
    AnalyticAt.comp (g := fun w => adjointEntry w (col p) q.1) (analyticAt_adjointEntry _ _ _) hw
  by_cases h : q.2 = hd p
  · simp only [orbitMatrix, if_pos h]
    exact ht.sub analyticAt_const
  · simp only [orbitMatrix, if_neg h]
    exact analyticAt_const.sub analyticAt_const
open Classical in
private theorem norm_orbitMatrix_entry_le [Fintype I] {K : ℝ}
    (hb : ∀ w : Fin 3 → ℂ, ‖w‖ ≤ 1 → ∀ a a', ‖adjointEntry w a a'‖ ≤ K) {z : I → ℂ} (hz : ‖z‖ ≤ 1)
    (p : P) (q : Fin 3 × S) :
    ‖orbitMatrix col hd tl idx z p q‖ ≤
      (if q.2 = hd p then K else 0) + if q.2 = tl p ∧ q.1 = col p then 1 else 0 := by
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · split_ifs
    · refine hb _ ?_ _ _
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun c => (norm_le_pi_norm z _).trans hz
    · simp
  · split_ifs <;> simp
open Classical in
private theorem norm_orbitMatrix_le [Fintype I] [Fintype P] [Fintype (Fin 3 × S)]
    [DecidableEq (Fin 3 × S)] {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ w : Fin 3 → ℂ, ‖w‖ ≤ 1 → ∀ a a', ‖adjointEntry w a a'‖ ≤ K) {N : ℕ}
    (hh : ∀ x : S, (Finset.univ.filter fun p => x = hd p).card ≤ N)
    (ht : ∀ x : S, (Finset.univ.filter fun p => x = tl p).card ≤ N) {z : I → ℂ} (hz : ‖z‖ ≤ 1) :
    ‖orbitMatrix col hd tl idx z‖ ≤ (K + 1) * (N + 3) := by
  refine schurTest _ (by positivity) (fun p => ?_) fun q => ?_
  · calc ∑ q, ‖orbitMatrix col hd tl idx z p q‖
        ≤ ∑ q : Fin 3 × S, ((if q.2 = hd p then K else 0) +
            if q.2 = tl p ∧ q.1 = col p then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun q _ => norm_orbitMatrix_entry_le col hd tl idx hb hz p q
      _ = 3 * K + 1 := by
          rw [Finset.sum_add_distrib, sum_ite_snd_eq (fun _ => K) (hd p), sum_ite_point]
          simp
      _ ≤ (K + 1) * (N + 3) := by nlinarith
  · calc ∑ p, ‖orbitMatrix col hd tl idx z p q‖
        ≤ ∑ p, ((if q.2 = hd p then K else 0) + if q.2 = tl p then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum fun p _ => (norm_orbitMatrix_entry_le col hd tl idx hb hz p q).trans ?_
          refine add_le_add le_rfl ?_
          by_cases h : q.2 = tl p
          · rw [if_pos h]
            split_ifs <;> norm_num
          · rw [if_neg h, if_neg fun e => h e.1]
      _ = (Finset.univ.filter fun p => q.2 = hd p).card * K +
            (Finset.univ.filter fun p => q.2 = tl p).card := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const,
            Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
      _ ≤ N * K + N := by
          have h1 : ((Finset.univ.filter fun p => q.2 = hd p).card : ℝ) ≤ N := by
            exact_mod_cast hh q.2
          have h2 : ((Finset.univ.filter fun p => q.2 = tl p).card : ℝ) ≤ N := by
            exact_mod_cast ht q.2
          have := mul_le_mul_of_nonneg_right h1 hK
          linarith
      _ ≤ (K + 1) * (N + 3) := by nlinarith
private theorem orbitMatrix_mulVec [Fintype (Fin 3 × S)] (z : I → ℂ) (v : Fin 3 × S → ℂ) (p : P) :
    (orbitMatrix col hd tl idx z).mulVec v p =
      ∑ a', adjointEntry (fun c => z (idx p c)) (col p) a' * v (a', hd p) - v (col p, tl p) := by
  classical
  simp only [Matrix.mulVec, dotProduct, orbitMatrix, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · have e : ∀ q : Fin 3 × S,
        (if q.2 = hd p then adjointEntry (fun c => z (idx p c)) (col p) q.1 else 0) * v q =
          if q.2 = hd p then adjointEntry (fun c => z (idx p c)) (col p) q.1 * v (q.1, hd p)
          else 0 := by
      rintro ⟨a, x⟩
      by_cases h : x = hd p
      · subst h
        simp
      · simp [h]
    simp only [e]
    exact sum_ite_snd_eq (fun a => adjointEntry (fun c => z (idx p c)) (col p) a * v (a, hd p)) _
  · rw [Finset.sum_eq_single (col p, tl p)]
    · simp
    · rintro ⟨a, x⟩ _ hne
      rw [if_neg, zero_mul]
      rintro ⟨h1, h2⟩
      exact hne (Prod.ext h2 h1)
    · simp
end OrbitMatrix
section OrbitExpansions
variable {L n k : ℕ}
private def rowColour : LevelFormIndex L n k → Fin 3
  | .inl p => p.1
  | .inr p => p.2.1
private def rowTurnedVertex : LevelFormIndex L n k → Vertex L n k 0
  | .inl p => p.2.1.target
  | .inr p => p.2.2.1.source.toSublattice (PeriodicLattice.levelDepth k 0)
private def rowSubtractedVertex : LevelFormIndex L n k → Vertex L n k 0
  | .inl p => p.2.1.source
  | .inr p => p.2.2.1.source.toSublattice (PeriodicLattice.levelDepth k 0)
private def rowCoords : LevelFormIndex L n k → Fin 3 → TripleCoordIndex L n k
  | .inl p, c => .inl (.inl (c, p.2))
  | .inr p, c => .inl (.inr ⟨p.1, (c, p.2.2)⟩)
private def bondAxis {m : ℤ} (b : PeriodicLattice.PositivelyOrientedBond L n m) : Fin 4 :=
  Classical.choose b.2
private def rowCode : LevelFormIndex L n k → Fin 3 × Option (Fin k) × Fin 4
  | .inl p => (p.1, none, bondAxis p.2)
  | .inr p => (p.2.1, some p.1, bondAxis p.2.2)
private theorem bondAxis_spec {m : ℤ} (b : PeriodicLattice.PositivelyOrientedBond L n m) :
    b.1.target - b.1.source = PeriodicLattice.unitStep L n m (bondAxis b) :=
  Classical.choose_spec b.2
private theorem bond_eq_of_endpoints {m : ℤ} {c c' : PeriodicLattice.Bond L n m}
    (h : c.source = c'.source) (h' : c.target = c'.target) : c = c' := by
  cases c
  cases c'
  simp only at h h'
  subst h h'
  rfl
abbrev _root_.YangMills.SharedProofs.p29034 := @bond_eq_of_endpoints
private theorem positiveBond_eq_of_source {m : ℤ} {b b' : PeriodicLattice.PositivelyOrientedBond L n m}
    (hd : bondAxis b = bondAxis b') (h : b.1.source = b'.1.source) : b = b' := by
  refine Subtype.ext (bond_eq_of_endpoints h ?_)
  have e := bondAxis_spec b
  rw [hd, ← bondAxis_spec b', h] at e
  exact sub_left_injective e
private theorem positiveBond_eq_of_target {m : ℤ} {b b' : PeriodicLattice.PositivelyOrientedBond L n m}
    (hd : bondAxis b = bondAxis b') (h : b.1.target = b'.1.target) : b = b' := by
  refine Subtype.ext (bond_eq_of_endpoints ?_ h)
  have e := bondAxis_spec b
  rw [hd, ← bondAxis_spec b', h] at e
  exact sub_right_injective e
private theorem coe_toSublattice [NeZero L] {i i' : ℤ} (h : i ≤ i') (y : PeriodicLattice.Site L n i) :
    ((y.toSublattice i' : PeriodicLattice.Site L n i') : PeriodicLattice.FourTorus L n) = y :=
  Classical.epsilon_spec (p := fun x : PeriodicLattice.Site L n i' =>
    (x : PeriodicLattice.FourTorus L n) = y)
    ⟨⟨y.1, PeriodicLattice.sublattice_mono (Nat.pos_of_ne_zero (NeZero.ne L)) n h y.2⟩, rfl⟩
private theorem toSublattice_self [NeZero L] {i : ℤ} (y : PeriodicLattice.Site L n i) :
    y.toSublattice i = y :=
  Subtype.ext (coe_toSublattice le_rfl y)
private theorem toSublattice_injective [NeZero L] {i i' : ℤ} (h : i ≤ i')
    {y y' : PeriodicLattice.Site L n i} (e : y.toSublattice i' = y'.toSublattice i') : y = y' :=
  Subtype.ext ((coe_toSublattice h y).symm.trans
    ((congrArg (fun u : PeriodicLattice.Site L n i' => (u : PeriodicLattice.FourTorus L n)) e).trans
      (coe_toSublattice h y')))
private theorem levelDepth_succ_le (i : Fin k) :
    PeriodicLattice.levelDepth k ((i : ℕ) + 1) ≤ PeriodicLattice.levelDepth k 0 := by
  simp only [PeriodicLattice.levelDepth]
  push_cast
  omega
private theorem rowCode_injective_of_shared [NeZero L] (p p' : LevelFormIndex L n k)
    (e : rowCode p = rowCode p')
    (h : rowTurnedVertex p = rowTurnedVertex p' ∨ rowSubtractedVertex p = rowSubtractedVertex p') :
    p = p' := by
  rcases p with ⟨a, b⟩ | ⟨i, a, c⟩ <;> rcases p' with ⟨a', b'⟩ | ⟨i', a', c'⟩
  · simp only [rowCode, Prod.mk.injEq] at e
    obtain ⟨rfl, -, e⟩ := e
    rcases h with h | h
    · rw [positiveBond_eq_of_target e h]
    · rw [positiveBond_eq_of_source e h]
  · simp [rowCode] at e
  · simp [rowCode] at e
  · simp only [rowCode, Prod.mk.injEq, Option.some.injEq] at e
    obtain ⟨rfl, rfl, e⟩ := e
    have h' : c.1.source = c'.1.source := by
      refine toSublattice_injective (levelDepth_succ_le i) ?_
      rcases h with h | h <;> exact h
    rw [positiveBond_eq_of_source e h']
private theorem card_rows_le [NeZero L] [Fintype (LevelFormIndex L n k)]
    (r : LevelFormIndex L n k → Vertex L n k 0)
    (hr : ∀ p p', r p = r p' →
      rowTurnedVertex p = rowTurnedVertex p' ∨ rowSubtractedVertex p = rowSubtractedVertex p')
    (x : Vertex L n k 0) {_ : DecidablePred fun p => x = r p} :
    (Finset.univ.filter fun p => x = r p).card ≤ 12 * (k + 1) := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun p => x = r p)
    (t := Finset.univ) rowCode (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    (fun p hp p' hp' e => rowCode_injective_of_shared p p' e
      (hr p p' (((Finset.mem_filter.1 hp).2).symm.trans (Finset.mem_filter.1 hp').2)))
  refine h.trans (le_of_eq ?_)
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_option]
  ring
private theorem cellDist_self (u : Vertex L n k k) : cellDist u u = 0 := by
  have h : ((u : PeriodicLattice.FourTorus L n) - (u : PeriodicLattice.FourTorus L n)) = 0 :=
    sub_self _
  unfold cellDist
  rw [h]
  refine le_antisymm ?_ (Real.sInf_nonneg (by rintro _ ⟨v, _, rfl⟩; exact Real.sqrt_nonneg _))
  refine csInf_le ⟨0, by rintro _ ⟨v, _, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨0, ?_, ?_⟩
  · funext μ
    simp [TorusMetric.torusProj]
  · simp [TorusMetric.euclidNormVec]
abbrev _root_.YangMills.SharedProofs.p28613 := @cellDist_self
private theorem levelVertexCell_eq_fineVertexCell [NeZero L] (x : Vertex L n k 0) :
    levelVertexCell x = fineVertexCell x := by
  rw [levelVertexCell, toSublattice_self]
private theorem cellDist_le_of_row [NeZero L] (hN : ∀ (x : Vertex L n k 0) (μ : Fin 4),
      cellDist (fineVertexCell (L := L) (n := n) (k := k) x)
        (fineVertexCell (L := L) (n := n) (k := k) (x + PeriodicLattice.unitStep L n _ μ)) ≤ 4)
    (p : LevelFormIndex L n k) (q : Fin 3 × Vertex L n k 0)
    (h : q.2 = rowTurnedVertex p ∨ q.2 = rowSubtractedVertex p) :
    cellDist (levelFormIndexCell p) (fineIndexCell q) ≤ 4 := by
  obtain ⟨a, x⟩ := q
  rcases p with ⟨c, b⟩ | ⟨i, c, b⟩
  · have e : levelFormIndexCell (.inl (c, b) : LevelFormIndex L n k) =
        fineVertexCell b.1.source := levelVertexCell_eq_fineVertexCell _
    have e' : fineIndexCell ((a, x) : Fin 3 × Vertex L n k 0) = fineVertexCell x :=
      levelVertexCell_eq_fineVertexCell _
    rw [e, e']
    rcases h with h | h
    · have h' : x = b.1.source + PeriodicLattice.unitStep L n _ (bondAxis b) := by
        have := bondAxis_spec b
        change x = b.1.target at h
        rw [h, ← this]
        abel
      rw [h']
      exact hN _ _
    · change x = b.1.source at h
      rw [h, cellDist_self]
      norm_num
  · have h' : x = b.1.source.toSublattice (PeriodicLattice.levelDepth k 0) := by
      rcases h with h | h <;> exact h
    have e : levelFormIndexCell (.inr ⟨i, c, b⟩ : LevelFormIndex L n k) = fineVertexCell x := by
      rw [h']
      rfl
    have e' : fineIndexCell ((a, x) : Fin 3 × Vertex L n k 0) = fineVertexCell x :=
      levelVertexCell_eq_fineVertexCell _
    rw [e, e', cellDist_self]
    norm_num
private theorem tripleCoordIndexCell_expansionCoords (p : LevelFormIndex L n k) (c : Fin 3) :
    tripleCoordIndexCell (rowCoords p c) = levelFormIndexCell p := by
  rcases p with p | p <;> rfl
private theorem extendOddly_mem {m : ℕ}
    (hx : ∀ b : Edge L n k m, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Edge L n k m → ComplexMatrix2)
    (h : ∀ b : Edge L n k m, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace L n k m := by apply _root_.YangMills.Construction.Tower.CriticalStepProof.extendOddly_mem <;> assumption
abbrev _root_.YangMills.SharedProofs.p1442 := @extendOddly_mem
private theorem expMove_fine (ζ : LevelForms L n k) (b : PositiveEdge L n k 0) :
    (expMove ζ (unitPoint L n k)).fine b.1 =
      ComplexMatrix2.matExp (Complex.I • (ζ.1 : Edge L n k 0 → ComplexMatrix2) b.1) := by
  simp [expMove, unitPoint, PeriodicLattice.expTwist, b.2]
private theorem expMove_noise (ζ : LevelForms L n k) (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    (expMove ζ (unitPoint L n k)).noise i c =
      ComplexMatrix2.matExp (Complex.I • (ζ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1) := by
  simp [expMove, unitPoint]
private theorem exists_formValues_eq (hxor : ∀ m, m ≤ k → ∀ b : Edge L n k m,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) (ζ : LevelForms L n k)
    (l : Vertex L n k 0 → ComplexMatrix2) (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) :
    ∃ ξ : LevelForms L n k, formValues ξ = gaugeOrbitValues (expMove ζ (unitPoint L n k)) l := by
  have m0 : (gaugeOrbitValues (expMove ζ (unitPoint L n k)) l).1 ∈ edgeFormSpace L n k 0 := by
    refine extendOddly_mem (hxor 0 (Nat.zero_le _))
      (fun b => ComplexMatrix2.conjugateBy ((expMove ζ (unitPoint L n k)).fine b) (l b.target) -
        l b.source) fun b hb => ?_
    · have e := expMove_fine ζ ⟨b, hb⟩
      change ComplexMatrix2.conjugateBy ((expMove ζ (unitPoint L n k)).fine b) (l b.target) -
        l b.source ∈ ComplexMatrix2.hermitianTraceless
      rw [show (expMove ζ (unitPoint L n k)).fine b = _ from e]
      exact ComplexMatrix2.hermitianTraceless.sub_mem
        (conjugateBy_mem_hermitianTraceless (ζ.1.2.1 b hb) (hl _)) (hl _)
  have m1 : ∀ i : Fin k,
      (gaugeOrbitValues (expMove ζ (unitPoint L n k)) l).2 i ∈ edgeFormSpace L n k (i + 1) := by
    intro i
    simp only [gaugeOrbitValues]
    refine extendOddly_mem (hxor ((i : ℕ) + 1) i.2) _ fun c hc => ?_
    simp only [dif_pos hc]
    rw [expMove_noise]
    exact ComplexMatrix2.hermitianTraceless.sub_mem
      (conjugateBy_mem_hermitianTraceless ((ζ.2 i).2.1 c hc) (hl _)) (hl _)
  exact ⟨(⟨_, m0⟩, fun i => ⟨_, m1 i⟩), rfl⟩
private theorem vertexFunction_mem (l : vertexFunctionSpace L n k 0) :
    ∀ y, (l : Vertex L n k 0 → ComplexMatrix2) y ∈ ComplexMatrix2.hermitianTraceless :=
  fun y => l.2 y (Set.mem_univ y)
section Coordinates
variable [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [Fintype (Fin 3 × Vertex L n k 0)]
  [Fintype (Fin 3 × Vertex L n k k)]
private theorem base_eq_pauliSum (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ)
    (b : PositiveEdge L n k 0) :
    ((tripleOfCoords P x).1.1 : Edge L n k 0 → ComplexMatrix2) b.1 =
      pauliSum fun c => complexifyCoords x (.inl (.inl (c, b))) := by apply _root_.YangMills.DeltaSharedProofs.p502055 <;> assumption
private theorem level_eq_pauliSum (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ)
    (i : Fin k) (b : PositiveEdge L n k (i + 1)) :
    ((tripleOfCoords P x).1.2 i : Edge L n k (i + 1) → ComplexMatrix2) b.1 =
      pauliSum fun c => complexifyCoords x (.inl (.inr ⟨i, (c, b)⟩)) := by apply _root_.YangMills.DeltaSharedProofs.p502402 <;> assumption
private theorem complexifyCoords_fineVertexCoords (P : PauliCoordinates L n k)
    (l : vertexFunctionSpace L n k 0) (q : Fin 3 × Vertex L n k 0) :
    complexifyCoords (fineVertexCoords P l) q =
      pauliCoeff q.1 ((l : Vertex L n k 0 → ComplexMatrix2) q.2) :=
  (P.ghostCoords_fst (l, 0) q).symm
omit [Fintype (GhostCoordIndex L n k)] [Fintype (Fin 3 × Vertex L n k k)] in
private theorem orbitMatrix_isLocallyHolomorphic [DecidableEq (Fin 3 × Vertex L n k 0)] [NeZero L]
    (hnear : ∀ (x : Vertex L n k 0) (μ : Fin 4),
      cellDist (fineVertexCell (L := L) (n := n) (k := k) x)
        (fineVertexCell (L := L) (n := n) (k := k) (x + PeriodicLattice.unitStep L n _ μ)) ≤ 4)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ w : Fin 3 → ℂ, ‖w‖ ≤ 1 → ∀ a a', ‖adjointEntry w a a'‖ ≤ K) :
    IsLocallyHolomorphicFamily (tripleCoordIndexCell (L := L) (n := n) (k := k)) fineIndexCell
      levelFormIndexCell (orbitMatrix rowColour rowTurnedVertex rowSubtractedVertex rowCoords) 1
      ((K + 1) * (((12 * (k + 1) : ℕ) : ℝ) + 3)) 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun p q => orbitMatrix_analytic _ _ _ _ p q _
  · intro z hz
    exact norm_orbitMatrix_le (N := 12 * (k + 1)) _ _ _ _ hK hb
      (fun x => card_rows_le rowTurnedVertex (fun _ _ h => Or.inl h) x)
      (fun x => card_rows_le rowSubtractedVertex (fun _ _ h => Or.inr h) x) (mem_ball_zero_iff.1 hz).le
  · intro p q z _ z' _ h
    have e : ∀ c, z (rowCoords p c) = z' (rowCoords p c) := fun c =>
      h _ (by rw [tripleCoordIndexCell_expansionCoords, cellDist_self]; norm_num)
    unfold orbitMatrix
    rw [show (fun c => z (rowCoords p c)) = fun c => z' (rowCoords p c) from funext e]
  · intro z _ p q h
    have h1 : q.2 ≠ rowTurnedVertex p := fun e =>
      absurd (cellDist_le_of_row hnear p q (Or.inl e)) (not_le.2 h)
    have h2 : q.2 ≠ rowSubtractedVertex p := fun e =>
      absurd (cellDist_le_of_row hnear p q (Or.inr e)) (not_le.2 h)
    simp [orbitMatrix, h1, h2]
private theorem complexify_formCoords_eq_mulVec (P : PauliCoordinates L n k)
    (x : TripleCoordIndex L n k → ℝ) (l : vertexFunctionSpace L n k 0) (ξ : LevelForms L n k)
    (hξ : formValues ξ = gaugeOrbitValues (pointOfCoords P x) (l : Vertex L n k 0 → ComplexMatrix2)) :
    complexifyCoords (P.formCoords ξ) =
      (orbitMatrix rowColour rowTurnedVertex rowSubtractedVertex rowCoords
        (complexifyCoords x)).mulVec (complexifyCoords (fineVertexCoords P l)) := by
  have hl := vertexFunction_mem l
  funext p
  rw [orbitMatrix_mulVec]
  rcases p with ⟨a, b⟩ | ⟨i, a, c⟩
  · have e1 : complexifyCoords (P.formCoords ξ) (.inl (a, b)) =
        pauliCoeff a ((ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1) := (P.formCoords_base ξ (a, b)).symm
    have e2 : (ξ.1 : Edge L n k 0 → ComplexMatrix2) =
        covDiff (pointOfCoords P x).fine (l : Vertex L n k 0 → ComplexMatrix2) :=
      congrArg Prod.fst hξ
    have e3 : (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1 =
        ComplexMatrix2.conjugateBy (ComplexMatrix2.matExp
            (Complex.I • pauliSum fun c => complexifyCoords x (.inl (.inl (c, b)))))
          ((l : Vertex L n k 0 → ComplexMatrix2) b.1.target) -
          (l : Vertex L n k 0 → ComplexMatrix2) b.1.source := by
      rw [e2, covDiff]
      simp only [extendOddly, if_pos b.2]
      rw [show (pointOfCoords P x).fine b.1 = _ from expMove_fine _ b, base_eq_pauliSum]
    have hm : (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1 ∈ ComplexMatrix2.traceless :=
      (ξ.1.2.1 b.1 b.2).2
    rw [e1, e3, pauliCoeff_conjugateBy_sub _ (hl _).2 (hl _).2 (e3 ▸ hm)]
    simp only [complexifyCoords_fineVertexCoords]
    rfl
  · have e1 : complexifyCoords (P.formCoords ξ) (.inr ⟨i, (a, c)⟩) =
        pauliCoeff a ((ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1) :=
      (P.formCoords_level ξ i (a, c)).symm
    have e2 : (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) = (gaugeOrbitValues (pointOfCoords P x)
        (l : Vertex L n k 0 → ComplexMatrix2)).2 i := congrFun (congrArg Prod.snd hξ) i
    have e3 : (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
        ComplexMatrix2.conjugateBy (ComplexMatrix2.matExp
            (Complex.I • pauliSum fun e => complexifyCoords x (.inl (.inr ⟨i, (e, c)⟩))))
          ((l : Vertex L n k 0 → ComplexMatrix2)
            (c.1.source.toSublattice (PeriodicLattice.levelDepth k 0))) -
          (l : Vertex L n k 0 → ComplexMatrix2)
            (c.1.source.toSublattice (PeriodicLattice.levelDepth k 0)) := by
      rw [e2]
      simp only [gaugeOrbitValues, extendOddly, if_pos c.2, dif_pos c.2]
      rw [show (pointOfCoords P x).noise i c = _ from expMove_noise _ i c, level_eq_pauliSum]
      rfl
    have hm : (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 ∈ ComplexMatrix2.traceless :=
      ((ξ.2 i).2.1 c.1 c.2).2
    rw [e1, e3, pauliCoeff_conjugateBy_sub _ (hl _).2 (hl _).2 (e3 ▸ hm)]
    simp only [complexifyCoords_fineVertexCoords]
    rfl
end Coordinates
end OrbitExpansions
theorem gaugeOrbitMapIsLocal_of_neighbouringVertexCells (hN : NeighbouringFineVertexCells) :
    GaugeOrbitMapIsLocal := by
  intro L hL k _
  have : NeZero L := ⟨by have := hL.2; omega⟩
  have hL2 : 2 ≤ L := by have := hL.2; omega
  obtain ⟨K, hK, hb⟩ := exists_adjointEntry_bound
  refine ⟨1, (K + 1) * (((12 * (k + 1) : ℕ) : ℝ) + 3), 4, one_pos, by positivity, by norm_num, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro _ _ _ _ _ _ _ _ _ P
  have hxor : ∀ m, m ≤ k → ∀ b : Edge L n k m,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun i hi b =>
    PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  refine ⟨orbitMatrix rowColour rowTurnedVertex rowSubtractedVertex rowCoords,
    orbitMatrix_isLocallyHolomorphic (hN L hL n k).2.2.2 hK hb, Eventually.of_forall fun x l => ?_⟩
  obtain ⟨ξ, hξ⟩ := exists_formValues_eq hxor (tripleOfCoords P x).1
    (l : Vertex L n k 0 → ComplexMatrix2) (vertexFunction_mem l)
  exact ⟨ξ, hξ, complexify_formCoords_eq_mulVec P x l ξ hξ⟩
end YangMills.Construction.RunningCouplingSlope.GaugeOrbitLocality
end

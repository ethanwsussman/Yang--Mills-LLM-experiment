import YangMills.Construction.HessianOfTheMainTerm.SumsOverTheSitesOfATorus
import YangMills.Construction.RunningCouplingSlope.KernelsNearTheCellsAreBounded
import YangMills.Construction.Torus.BoundsOnTheWeightedDistanceProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace CellKernelBound
section TorusNorms
open TorusMetric
private lemma supNormVec_le_euclidNormVec (v : Fin 4 → ℝ) : supNormVec v ≤ euclidNormVec v := by
  refine Finset.sup'_le _ _ fun μ _ => ?_
  refine Real.abs_le_sqrt ?_
  exact Finset.single_le_sum (f := fun i => v i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ μ)
abbrev _root_.YangMills.DeltaSharedProofs.p501598 := @supNormVec_le_euclidNormVec
abbrev _root_.YangMills.SharedProofs.p37493 := @supNormVec_le_euclidNormVec
private lemma supNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ supNormVec v :=
  (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
variable {S : ℝ}
private lemma torusProj_exists_lift (x : Torus4 S) : ∃ v, torusProj S v = x := by apply _root_.YangMills.Construction.Weighted.DistBounds.torusProj_surjective <;> assumption
private lemma torusEuclidNorm_nonneg (x : Torus4 S) : 0 ≤ torusEuclidNorm x := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
private lemma torusEuclidNorm_neg (x : Torus4 S) : torusEuclidNorm (-x) = torusEuclidNorm x := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.torusEuclidNorm_neg <;> assumption
private lemma torusSupNorm_le_torusEuclidNorm (x : Torus4 S) : torusSupNorm x ≤ torusEuclidNorm x := by
  obtain ⟨v₀, hv₀⟩ := torusProj_exists_lift x
  refine le_csInf ⟨_, v₀, hv₀, rfl⟩ ?_
  rintro _ ⟨v, hv, rfl⟩
  have hb : BddBelow (supNormVec '' (torusProj S ⁻¹' {x})) :=
    ⟨0, by rintro _ ⟨u, _, rfl⟩; exact supNormVec_nonneg u⟩
  have h1 : torusSupNorm x ≤ supNormVec v := csInf_le hb ⟨v, hv, rfl⟩
  exact h1.trans (supNormVec_le_euclidNormVec v)
abbrev _root_.YangMills.SharedProofs.p76601 := @torusSupNorm_le_torusEuclidNorm
end TorusNorms
variable {L n k : ℕ}
private structure CellGeometry (L n k : ℕ) (ε S : ℝ) : Prop where
  symm : ∀ y y' : Tower.Vertex L n k k, cellDist y y' = cellDist y' y
  nonneg : ∀ y y' : Tower.Vertex L n k k, 0 ≤ cellDist y y'
  sum : ∃ _ : Fintype (Tower.Vertex L n k k), ∀ y : Tower.Vertex L n k k,
    ∑ y', Real.exp (-(ε * cellDist y y')) ≤ S
private lemma cellGeometry_exists (hs : HessianOfTheMainTerm.SiteSums.BallDoublingAndWeightBound)
    (hl : HessianOfTheMainTerm.SiteLengthFacts) {ε : ℝ} (hε : 0 < ε) :
    ∃ S₀ : ℝ, 1 ≤ S₀ ∧ ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
      CellGeometry L n k ε S₀ := by
  obtain ⟨T, -, hT⟩ := hs.2 ε hε
  refine ⟨max T 1, le_max_right _ _, fun L n k hL hn => ?_⟩
  have hL1 : 1 < L := by have := hL.2; omega
  have hj : 0 ≤ (n : ℤ) + PeriodicLattice.levelDepth k k := by
    simp [PeriodicLattice.levelDepth]
  obtain ⟨hfin, -⟩ := hl L n (PeriodicLattice.levelDepth k k) hL1 hj
  have hsp : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) = 1 := by
    simp [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
  refine ⟨fun y y' => ?_, fun y y' => torusEuclidNorm_nonneg _, ?_⟩
  · unfold cellDist
    rw [← neg_sub, torusEuclidNorm_neg]
  · let _ : Fintype (Tower.Vertex L n k k) := Fintype.ofFinite _
    refine ⟨inferInstance, fun y => ?_⟩
    have h1 := hT L n (PeriodicLattice.levelDepth k k) inferInstance hL1 hj y
    refine le_trans (Finset.sum_le_sum fun y' _ => ?_) (h1.trans (le_max_left _ _))
    set u := HessianOfTheMainTerm.supLengthInMesh (y' - y) with hu
    have hu0 : 0 ≤ u := by
      rw [hu]
      unfold HessianOfTheMainTerm.supLengthInMesh
      rw [hsp, div_one]
      exact (Real.sInf_nonneg (by rintro _ ⟨v, _, rfl⟩; exact supNormVec_nonneg v))
    have hud : u ≤ cellDist y y' := by
      rw [hu]
      unfold HessianOfTheMainTerm.supLengthInMesh cellDist
      rw [hsp, div_one]
      have e : ((y' - y : Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) =
          -((y : PeriodicLattice.FourTorus L n) - y') := by
        push_cast
        abel
      rw [e]
      exact (torusSupNorm_le_torusEuclidNorm _).trans_eq (torusEuclidNorm_neg _)
    have h2 : Real.exp (-(ε * cellDist y y')) ≤ Real.exp (-ε * u) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h3 : (1 : ℝ) ≤ (1 + u) ^ 2 := by nlinarith
    calc Real.exp (-(ε * cellDist y y')) ≤ Real.exp (-ε * u) := h2
      _ = 1 * Real.exp (-ε * u) := by ring
      _ ≤ (1 + u) ^ 2 * Real.exp (-ε * u) := by gcongr
private theorem matrix_opNorm_le_sqrt_rowSum_mul_colSum {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    (A : Matrix ι' ι ℂ) (P Q : ℝ) (hP : ∀ p, ∑ q, ‖A p q‖ ≤ P) (hQ : ∀ q, ∑ p, ‖A p q‖ ≤ Q)
    (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q) : ‖A‖ ≤ Real.sqrt (P * Q) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have key : ∀ p, ‖∑ q, A p q * x q‖ ^ 2 ≤ P * ∑ q, ‖A p q‖ * ‖x q‖ ^ 2 := by
    intro p
    have h1 : ‖∑ q, A p q * x q‖ ≤ ∑ q, ‖A p q‖ * ‖x q‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun q _ => norm_mul _ _
    have h2 : (∑ q, ‖A p q‖ * ‖x q‖) ^ 2 ≤
        (∑ q, ‖A p q‖) * ∑ q, ‖A p q‖ * ‖x q‖ ^ 2 := by
      have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun q => Real.sqrt ‖A p q‖) (fun q => Real.sqrt ‖A p q‖ * ‖x q‖)
      have e1 : ∀ q, Real.sqrt ‖A p q‖ * (Real.sqrt ‖A p q‖ * ‖x q‖) = ‖A p q‖ * ‖x q‖ := by
        intro q
        rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
      have e2 : ∀ q, Real.sqrt ‖A p q‖ ^ 2 = ‖A p q‖ := fun q => Real.sq_sqrt (norm_nonneg _)
      have e3 : ∀ q, (Real.sqrt ‖A p q‖ * ‖x q‖) ^ 2 = ‖A p q‖ * ‖x q‖ ^ 2 := by
        intro q
        rw [mul_pow, e2]
      simpa only [e1, e2, e3] using h3
    calc ‖∑ q, A p q * x q‖ ^ 2 ≤ (∑ q, ‖A p q‖ * ‖x q‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ ≤ P * ∑ q, ‖A p q‖ * ‖x q‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hP p)
            (Finset.sum_nonneg fun q _ => by positivity)
  have hx : ‖x‖ ^ 2 = ∑ q, ‖x q‖ ^ 2 := EuclideanSpace.norm_sq_eq x
  have hsq : ‖(Matrix.toEuclideanLin A).toContinuousLinearMap x‖ ^ 2 ≤ P * Q * ‖x‖ ^ 2 := by
    have e0 : ‖(Matrix.toEuclideanLin A).toContinuousLinearMap x‖ ^ 2 =
        ∑ p, ‖∑ q, A p q * x q‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
    rw [e0, hx]
    calc ∑ p, ‖∑ q, A p q * x q‖ ^ 2 ≤ ∑ p, P * ∑ q, ‖A p q‖ * ‖x q‖ ^ 2 :=
          Finset.sum_le_sum fun p _ => key p
      _ = P * ∑ q, (∑ p, ‖A p q‖) * ‖x q‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ ≤ P * ∑ q, Q * ‖x q‖ ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right (hQ q) (by positivity)) hP0
      _ = P * Q * ∑ q, ‖x q‖ ^ 2 := by rw [← Finset.mul_sum]; ring
  have hs : Real.sqrt (P * Q) * ‖x‖ = Real.sqrt (P * Q * ‖x‖ ^ 2) := by
    rw [Real.sqrt_mul (mul_nonneg hP0 hQ0) (‖x‖ ^ 2), Real.sqrt_sq (norm_nonneg _)]
  rw [hs]
  exact Real.le_sqrt_of_sq_le hsq
abbrev _root_.YangMills.SharedProofs.p56120 := @matrix_opNorm_le_sqrt_rowSum_mul_colSum
private theorem sum_comp_le_mul_sum_of_fiber_card_le {κ Y : Type} [Fintype κ] [Fintype Y] (c : κ → Y)
    {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ y, (Nat.card {q // c q = y} : ℝ) ≤ m) (w : Y → ℝ) (hw : ∀ y, 0 ≤ w y) :
    ∑ q, w (c q) ≤ m * ∑ y, w y := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ c, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  have e : ∑ q ∈ Finset.univ.filter (fun q => c q = y), w (c q) =
      ((Finset.univ.filter fun q => c q = y).card : ℝ) * w y := by
    rw [Finset.sum_congr rfl fun q hq => by rw [(Finset.mem_filter.1 hq).2]]
    simp
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (hw y)
  have h := hm y
  rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
end CellKernelBound
open CellKernelBound in
theorem cellLocalKernelNormBound_holds
    (hs : HessianOfTheMainTerm.SiteSums.BallDoublingAndWeightBound)
    (hl : HessianOfTheMainTerm.SiteLengthFacts) :
    CellLocalKernelNormBound := by
  intro R
  obtain ⟨S₀, hS₀, hG⟩ := cellGeometry_exists hs hl (ε := 1) one_pos
  refine ⟨Real.exp R * S₀, by positivity, ?_⟩
  intro L n k hL hn ι ι' _ _ _ c c' m m' E A hm hm' hE hc hc' hA h0
  have G := hG L n k hL hn
  obtain ⟨inst, hsum⟩ := G.sum
  have entry : ∀ p q, ‖A p q‖ ≤ E * Real.exp R * Real.exp (-(1 * cellDist (c' p) (c q))) := by
    intro p q
    by_cases hd : R < cellDist (c' p) (c q)
    · rw [h0 p q hd, norm_zero]
      positivity
    · have h1 : 1 ≤ Real.exp R * Real.exp (-(1 * cellDist (c' p) (c q))) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith [not_lt.1 hd])
      calc ‖A p q‖ ≤ E := hA p q
        _ = E * 1 := (mul_one E).symm
        _ ≤ E * (Real.exp R * Real.exp (-(1 * cellDist (c' p) (c q)))) :=
          mul_le_mul_of_nonneg_left h1 hE
        _ = _ := by ring
  have hw : ∀ y y' : Tower.Vertex L n k k, 0 ≤ Real.exp (-(1 * cellDist y y')) := fun _ _ =>
    (Real.exp_pos _).le
  have hP : ∀ p, ∑ q, ‖A p q‖ ≤ E * Real.exp R * (m * S₀) := by
    intro p
    calc ∑ q, ‖A p q‖ ≤ ∑ q, E * Real.exp R * Real.exp (-(1 * cellDist (c' p) (c q))) :=
          Finset.sum_le_sum fun q _ => entry p q
      _ = E * Real.exp R * ∑ q, Real.exp (-(1 * cellDist (c' p) (c q))) := by
          rw [Finset.mul_sum]
      _ ≤ E * Real.exp R * (m * S₀) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (sum_comp_le_mul_sum_of_fiber_card_le c hm hc
            (fun y => Real.exp (-(1 * cellDist (c' p) y))) (hw _)).trans ?_
          exact mul_le_mul_of_nonneg_left (hsum _) hm
  have hQ : ∀ q, ∑ p, ‖A p q‖ ≤ E * Real.exp R * (m' * S₀) := by
    intro q
    calc ∑ p, ‖A p q‖ ≤ ∑ p, E * Real.exp R * Real.exp (-(1 * cellDist (c q) (c' p))) :=
          Finset.sum_le_sum fun p _ => by
            rw [G.symm (c q)]
            exact entry p q
      _ = E * Real.exp R * ∑ p, Real.exp (-(1 * cellDist (c q) (c' p))) := by
          rw [Finset.mul_sum]
      _ ≤ E * Real.exp R * (m' * S₀) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (sum_comp_le_mul_sum_of_fiber_card_le c' hm' hc'
            (fun y => Real.exp (-(1 * cellDist (c q) y))) (hw _)).trans ?_
          exact mul_le_mul_of_nonneg_left (hsum _) hm'
  refine (matrix_opNorm_le_sqrt_rowSum_mul_colSum A _ _ hP hQ (by positivity) (by positivity)).trans
    (le_of_eq ?_)
  have e : E * Real.exp R * (m * S₀) * (E * Real.exp R * (m' * S₀)) =
      (Real.exp R * S₀ * E) ^ 2 * (m * m') := by ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring
end YangMills.Construction.RunningCouplingSlope
end

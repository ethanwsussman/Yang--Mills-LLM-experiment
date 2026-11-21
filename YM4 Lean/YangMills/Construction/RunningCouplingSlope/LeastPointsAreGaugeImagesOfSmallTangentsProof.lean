import YangMills.Construction.Lattice.OppositeBondsAndPositiveValues
import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreIsSmoothProof
import YangMills.Construction.RunningCouplingSlope.FieldsAtALeastPointAreSmall
import YangMills.Construction.RunningCouplingSlope.LeastPointsAreGaugeImagesOfSmallTangents
import YangMills.Construction.RunningCouplingSlope.PointsOfSmallActionAreNearTheOrbit
import YangMills.Construction.Towers.GaugeCovarianceOfTheLiftProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open Filter
open scoped Topology Matrix.Norms.L2Operator Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MinimizerGaugeEquivalence
open Tower Matrices
section Group
private theorem su2_entry_one_one {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g 1 1 = star (g 0 0) := by
  have hu : g * star g = 1 := by
    have := (Matrix.mem_specialUnitaryGroup_iff.1 hg).1
    exact Matrix.mem_unitaryGroup_iff.1 this
  have hd : g.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.1 hg).2
  have hadj : Matrix.adjugate g = star g := by
    calc Matrix.adjugate g = Matrix.adjugate g * (g * star g) := by rw [hu, mul_one]
      _ = star g := by rw [← mul_assoc, Matrix.adjugate_mul, hd]; simp
  have h00 := congrFun (congrFun hadj 0) 0
  simp only [Matrix.adjugate_fin_two, Matrix.star_apply] at h00
  simpa using h00
private theorem inv_mem_compact {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem det_isUnit_of_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit g.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem traceDefect_eq_one_sub_re {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    traceDefect g = 1 - (g 0 0).re := by
  have h11 := su2_entry_one_one hg
  have htr : ComplexMatrix2.fullTrace g = g 0 0 + g 1 1 := Matrix.trace_fin_two g
  simp only [traceDefect, ComplexMatrix2.halfTrace, htr, h11, Complex.star_def]
  simp [Complex.add_re, Complex.mul_re]
  ring
private theorem add_star_eq_smul_one {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g + star g = ((2 * (g 0 0).re : ℝ) : ℂ) • (1 : ComplexMatrix2) := by
  have h11 := su2_entry_one_one hg
  have hu : g * star g = 1 := by
    have := (Matrix.mem_specialUnitaryGroup_iff.1 hg).1
    exact Matrix.mem_unitaryGroup_iff.1 this
  have hd : g.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.1 hg).2
  have hadj : Matrix.adjugate g = star g := by
    calc Matrix.adjugate g = Matrix.adjugate g * (g * star g) := by rw [hu, mul_one]
      _ = star g := by rw [← mul_assoc, Matrix.adjugate_mul, hd]; simp
  have h10 := congrFun (congrFun hadj 1) 0
  have h01 := congrFun (congrFun hadj 0) 1
  simp only [Matrix.adjugate_fin_two, Matrix.star_apply] at h10 h01
  simp at h10 h01
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.star_apply, Complex.ext_iff]
    ring
  · simp [Matrix.star_apply]
    rw [← h01]
    ring
  · simp [Matrix.star_apply]
    rw [← h10]
    ring
  · simp [Matrix.star_apply, h11, Complex.ext_iff]
    ring
private theorem norm_sub_one_sq {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    ‖g - 1‖ ^ 2 = 2 * traceDefect g := by
  have hu : star g * g = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 (Matrix.mem_specialUnitaryGroup_iff.1 hg).1
  have hstar : star (g - 1) * (g - 1) = ((2 - 2 * (g 0 0).re : ℝ) : ℂ) • (1 : ComplexMatrix2) := by
    have hexp : star (g - 1) * (g - 1) = (1 + 1) - (g + star g) := by
      rw [star_sub, star_one, sub_mul, mul_sub, mul_sub, hu]
      noncomm_ring
    rw [hexp, add_star_eq_smul_one hg]
    have htwo : (1 + 1 : ComplexMatrix2) = ((2 : ℝ) : ℂ) • (1 : ComplexMatrix2) := by
      rw [Complex.coe_smul, two_smul]
    rw [htwo, ← sub_smul]
    congr 1
    push_cast
    ring
  have hre : (g 0 0).re ≤ 1 := by
    have hU := (Matrix.mem_specialUnitaryGroup_iff.1 hg).1
    have h0 : ‖g 0 0‖ ≤ 1 := entry_norm_bound_of_unitary hU 0 0
    exact (Complex.re_le_norm _).trans h0
  have hcstar := CStarRing.norm_star_mul_self (x := g - 1)
  rw [hstar, norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)] at hcstar
  rw [traceDefect_eq_one_sub_re hg, pow_two, ← hcstar]
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p501476 := @norm_sub_one_sq
abbrev _root_.YangMills.SharedProofs.p32894 := @norm_sub_one_sq
private theorem traceDefect_nonneg {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    0 ≤ traceDefect g := by
  have := norm_sub_one_sq hg
  nlinarith [sq_nonneg ‖g - 1‖]
abbrev _root_.YangMills.SharedProofs.p3544 := @traceDefect_nonneg
private theorem traceDefect_inv {g : ComplexMatrix2} (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    traceDefect g⁻¹ = traceDefect g := by
  have hmem := (Matrix.mem_specialUnitaryGroup_iff.mp h).1
  have hu : g * star g = 1 := Matrix.mem_unitaryGroup_iff.mp hmem
  rw [Matrix.inv_eq_right_inv hu]
  simp only [traceDefect, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
  simp [Complex.mul_re]
abbrev _root_.YangMills.SharedProofs.p3992 := @traceDefect_inv
private theorem traceDefect_le_of_norm_lt {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (h : ‖g - 1‖ < ε) : traceDefect g ≤ ε := by
  have hsq := norm_sub_one_sq hg
  have hle : ‖g - 1‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h.le 2
  nlinarith
abbrev _root_.YangMills.DeltaSharedProofs.p501672 := @traceDefect_le_of_norm_lt
private theorem traceDefect_quaternionToMatrix (q : ℍ[ℝ]) :
    traceDefect (SoftAverages.quaternionToMatrix q) = 1 - q.re := by
  simp [traceDefect, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two,
    SoftAverages.quaternionToMatrix, Complex.mul_re]
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p500863 := @traceDefect_quaternionToMatrix
abbrev _root_.YangMills.SharedProofs.p14120 := @traceDefect_quaternionToMatrix
private theorem pathHolonomy_mem {L n k j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup)
    (γ : List (Edge L n k j)) : PeriodicLattice.pathHolonomy V γ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p6330 <;> assumption
private theorem exists_hermitian_log (hEL : ComplexMatrix2.ExpLogEstimates) {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) (h1 : ComplexMatrix2.operatorNorm (g - 1) < 1) :
    ∃ H ∈ ComplexMatrix2.hermitianTraceless, ComplexMatrix2.matExp (Complex.I • H) = g ∧
      ComplexMatrix2.operatorNorm H ≤ 2 * ComplexMatrix2.operatorNorm (g - 1) := by
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hg
  obtain ⟨H, -, -, h2, h3, h4, h5⟩ := hEL.2.2.2.2.2.2.2.1 g hu h1
  refine ⟨H, (h5 hd).2.1, h3, ?_⟩
  have hx0 : 0 ≤ ComplexMatrix2.operatorNorm H / 2 := by
    have := norm_nonneg H
    simp only [ComplexMatrix2.operatorNorm]
    positivity
  have hx1 : ComplexMatrix2.operatorNorm H / 2 ≤ Real.pi / 2 := by
    have := Real.pi_pos
    linarith
  have hsin := Real.mul_le_sin hx0 hx1
  rw [h4]
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hp := Real.pi_pos
  have hdiv : 2 / Real.pi * (ComplexMatrix2.operatorNorm H / 2) =
      ComplexMatrix2.operatorNorm H / Real.pi := by
    field_simp
  rw [hdiv] at hsin
  have hq : ComplexMatrix2.operatorNorm H / 4 ≤ ComplexMatrix2.operatorNorm H / Real.pi :=
    div_le_div_of_nonneg_left (by simp [ComplexMatrix2.operatorNorm]) hp hpi4
  nlinarith
abbrev _root_.YangMills.SharedProofs.p26564 := @exists_hermitian_log
end Group
section Edges
variable {L n k j : ℕ}
private theorem edge_opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
private theorem positive_or_opposite_positive (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem xor_positive_opposite
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
  intro j hj b
  have h := (hb ⟨L, hL, 1, ⟨n, hn⟩⟩ (PeriodicLattice.levelDepth k j) (by
    change -(n : ℤ) < PeriodicLattice.levelDepth k j
    simp only [PeriodicLattice.levelDepth]
    omega)).1 b
  exact h.2.2.2.2.2
private theorem extendOddly_opposite (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) (hj : j ≤ k)
    (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    extendOddly f b.opposite = -extendOddly f b := by
  by_cases hb : b.IsPositivelyOriented
  · have hb' : ¬ b.opposite.IsPositivelyOriented :=
      (hxor j hj b).elim (fun h => h.2) fun h => absurd hb h.2
    simp only [extendOddly, if_pos hb, if_neg hb', edge_opposite_opposite]
  · have hb' : b.opposite.IsPositivelyOriented := (positive_or_opposite_positive b).resolve_left hb
    simp only [extendOddly, if_pos hb', if_neg hb, neg_neg]
private theorem top_edge_eq_forward (hlat : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (c : PositiveEdge L n k k) :
    ∃ (z : TorusFields.TorusSite (2 * L ^ n)) (μ : Fin 4),
      c.1 = PeriodicLattice.Bond.forwardFrom (topVertexOf z) μ := by
  have hd : PeriodicLattice.levelDepth k k = 0 := by simp [PeriodicLattice.levelDepth]
  have hlc := (hlat L n hL.1 hL.2 hn).1 (PeriodicLattice.levelDepth k k) (by rw [hd]; omega)
  obtain ⟨-, -, -, hex, hiff, -⟩ := hlc
  obtain ⟨μ, hμ⟩ := c.2
  obtain ⟨m, hm⟩ := hex 0 c.1.source
  have hN : 2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k k) = 2 * L ^ n := by
    simp [PeriodicLattice.halfPeriod, hd]
  let z : TorusFields.TorusSite (2 * L ^ n) := fun ν => ((m ν : ℤ) : ZMod (2 * L ^ n))
  have hz : topVertexOf z = c.1.source := by
    rw [hm]
    refine (hiff 0 _ _).2 fun ν => ?_
    rw [hN]
    refine (ZMod.intCast_eq_intCast_iff _ _ _).1 ?_
    simp [z]
  refine ⟨z, μ, ?_⟩
  rw [hz]
  refine PeriodicLattice.Bond.ext rfl ?_
  change c.1.target = c.1.source + PeriodicLattice.unitStep L n _ μ
  rw [← hμ]
  abel
abbrev _root_.YangMills.SharedProofs.p10565 := @top_edge_eq_forward
private theorem gaugeTransform_mem_fieldSpace {w : Vertex L n k j → ComplexMatrix2}
    {V : Edge L n k j → ComplexMatrix2}
    (hw : ∀ x, w x ∈ PeriodicLattice.compactGaugeGroup) (hV : V ∈ fieldSpace L n k j) :
    PeriodicLattice.gaugeTransform w V ∈ fieldSpace L n k j := by apply _root_.YangMills.SharedProofs.p8548 <;> assumption
end Edges
section Chart
variable {L n k : ℕ}
private theorem exists_tangent_of_near_one (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    {X : ChainPoint L n k} (hU : X.fine ∈ fieldSpace L n k 0)
    (hN : ∀ i c, X.noise i c ∈ PeriodicLattice.compactGaugeGroup) {τ : ℝ} (hτ : τ ≤ 1 / 2)
    (hb : ∀ b, ComplexMatrix2.operatorNorm (X.fine b - 1) ≤ τ)
    (hn : ∀ i c, ComplexMatrix2.operatorNorm (X.noise i c - 1) ≤ τ) :
    ∃ ξ : LevelForms L n k, expMove ξ (unitPoint L n k) = X ∧
      (∀ b, ComplexMatrix2.operatorNorm ((ξ.1 : Edge L n k 0 → ComplexMatrix2) b) ≤ 2 * τ) ∧
      ∀ (i : Fin k) (b : Edge L n k ((i : ℕ) + 1)),
        ComplexMatrix2.operatorNorm ((ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) b) ≤
          2 * τ := by
  have hlog : ∀ g : ComplexMatrix2, ∃ H : ComplexMatrix2, g ∈ PeriodicLattice.compactGaugeGroup →
      ComplexMatrix2.operatorNorm (g - 1) ≤ τ →
      H ∈ ComplexMatrix2.hermitianTraceless ∧ ComplexMatrix2.matExp (Complex.I • H) = g ∧
        ComplexMatrix2.operatorNorm H ≤ 2 * τ := by
    intro g
    by_cases h : g ∈ PeriodicLattice.compactGaugeGroup ∧ ComplexMatrix2.operatorNorm (g - 1) ≤ τ
    · obtain ⟨H, h1, h2, h3⟩ := exists_hermitian_log hEL h.1 (by linarith [h.2])
      exact ⟨H, fun _ _ => ⟨h1, h2, h3.trans (by linarith [h.2])⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Hf hHf using hlog
  have hτ0 : 0 ≤ τ := by
    have := hb (PeriodicLattice.Bond.forwardFrom 0 0)
    exact (norm_nonneg _).trans this
  have hsu : ∀ {j : ℕ} (hj : j ≤ k) (f : Edge L n k j → ComplexMatrix2),
      (∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) →
      extendOddly f ∈ edgeFormSpace L n k j := by
    intro j hj f hf
    refine ⟨fun b hb' => ?_, fun b => extendOddly_opposite hxor hj f b⟩
    simp only [extendOddly, if_pos hb']
    exact hf b hb'
  let A : edgeFormSpace L n k 0 := ⟨extendOddly fun b => Hf (X.fine b),
    hsu (Nat.zero_le _) _ fun b _ => (hHf _ (hU.1 b (Set.mem_univ b)) (hb b)).1⟩
  let fN : (i : Fin k) → Edge L n k ((i : ℕ) + 1) → ComplexMatrix2 := fun i c =>
    open Classical in if hc : c.IsPositivelyOriented then Hf (X.noise i ⟨c, hc⟩) else 0
  let Nf : (i : Fin k) → edgeFormSpace L n k ((i : ℕ) + 1) := fun i =>
    ⟨extendOddly (fN i), hsu i.2 _ fun c hc => by
      simp only [fN, dif_pos hc]
      exact (hHf _ (hN i _) (hn i _)).1⟩
  refine ⟨(A, Nf), ?_, fun b => ?_, fun i b => ?_⟩
  · have hfine : (expMove ((A, Nf) : LevelForms L n k) (unitPoint L n k)).fine = X.fine := by
      funext b
      by_cases hbp : b.IsPositivelyOriented
      · simp only [expMove, unitPoint, PeriodicLattice.expTwist, if_pos hbp, mul_one, A, extendOddly]
        exact (hHf _ (hU.1 b (Set.mem_univ b)) (hb b)).2.1
      · have hbr := (positive_or_opposite_positive b).resolve_left hbp
        simp only [expMove, unitPoint, PeriodicLattice.expTwist, if_neg hbp, if_pos hbr, mul_one, A,
          extendOddly]
        rw [(hHf _ (hU.1 _ (Set.mem_univ _)) (hb _)).2.1, hU.2 b (Set.mem_univ _)]
        exact Matrix.nonsing_inv_nonsing_inv _ (det_isUnit_of_mem (hU.1 b (Set.mem_univ _)))
    have hnoise : (expMove ((A, Nf) : LevelForms L n k) (unitPoint L n k)).noise = X.noise := by
      funext i c
      simp only [expMove, unitPoint, mul_one, Nf, extendOddly, if_pos c.2, fN, dif_pos c.2]
      exact (hHf _ (hN i _) (hn i _)).2.1
    calc expMove ((A, Nf) : LevelForms L n k) (unitPoint L n k) =
        ⟨(expMove ((A, Nf) : LevelForms L n k) (unitPoint L n k)).fine,
          (expMove ((A, Nf) : LevelForms L n k) (unitPoint L n k)).noise⟩ := rfl
      _ = ⟨X.fine, X.noise⟩ := by rw [hfine, hnoise]
      _ = X := rfl
  · show ComplexMatrix2.operatorNorm ((extendOddly fun b => Hf (X.fine b)) b) ≤ _
    by_cases hbp : b.IsPositivelyOriented
    · simp only [extendOddly, if_pos hbp]
      exact (hHf _ (hU.1 b (Set.mem_univ b)) (hb b)).2.2
    · simp only [extendOddly, if_neg hbp, ComplexMatrix2.operatorNorm, norm_neg]
      exact (hHf _ (hU.1 _ (Set.mem_univ _)) (hb _)).2.2
  · show ComplexMatrix2.operatorNorm (extendOddly (fN i) b) ≤ _
    have hbd : ∀ c : Edge L n k ((i : ℕ) + 1), ComplexMatrix2.operatorNorm (fN i c) ≤ 2 * τ := by
      intro c
      by_cases hc : c.IsPositivelyOriented
      · simp only [fN, dif_pos hc]
        exact (hHf _ (hN i _) (hn i _)).2.2
      · simp only [fN, dif_neg hc]
        simp only [ComplexMatrix2.operatorNorm, norm_zero]
        linarith
    by_cases hbp : b.IsPositivelyOriented
    · simp only [extendOddly, if_pos hbp]
      exact hbd b
    · simp only [extendOddly, if_neg hbp, ComplexMatrix2.operatorNorm, norm_neg]
      exact hbd _
private theorem coords_le_of_values_le [NeZero L] {N : ℕ}
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelForms L n k) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ξ : LevelForms L n k) (t : ℝ), 0 ≤ t →
      (∀ b, ‖(ξ.1 : Edge L n k 0 → ComplexMatrix2) b‖ ≤ t) →
      (∀ (i : Fin k) (b : Edge L n k ((i : ℕ) + 1)),
        ‖(ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) b‖ ≤ t) → ‖e.symm ξ‖ ≤ K * t := by
  letI : ∀ j : ℕ, Fintype (Edge L n k j) := fun j => Fintype.ofFinite _
  let T : (Fin N → ℝ) →ₗ[ℝ]
      (Edge L n k 0 → ComplexMatrix2) × ((i : Fin k) → Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) :=
    { toFun := fun w => formValues (e w)
      map_add' := fun x y => by
        simp only [formValues, map_add]
        rfl
      map_smul' := fun r x => by
        simp only [formValues, map_smul, RingHom.id_apply]
        rfl }
  have hT : LinearMap.ker T = ⊥ := by
    refine LinearMap.ker_eq_bot.2 fun x y h => ?_
    refine e.injective (Prod.ext (Subtype.ext (congrArg Prod.fst h)) (funext fun i =>
      Subtype.ext (congrFun (congrArg Prod.snd h) i)))
  obtain ⟨K, hK0, hK⟩ := T.exists_antilipschitzWith hT
  refine ⟨K, by exact_mod_cast hK0, fun ξ t ht h1 h2 => ?_⟩
  have hdist := hK.le_mul_dist (e.symm ξ) 0
  have hTle : ‖T (e.symm ξ)‖ ≤ t := by
    have hTeq : T (e.symm ξ) = formValues ξ := by
      show formValues (e (e.symm ξ)) = _
      rw [e.apply_symm_apply]
    rw [hTeq, Prod.norm_def]
    refine max_le ((pi_norm_le_iff_of_nonneg ht).2 h1) ((pi_norm_le_iff_of_nonneg ht).2 fun i => ?_)
    exact (pi_norm_le_iff_of_nonneg ht).2 (h2 i)
  simp only [dist_zero_right, map_zero] at hdist
  exact hdist.trans (by gcongr)
end Chart
section Action
variable {L n k : ℕ} [NeZero L]
private theorem finite_face (j : ℕ) : Finite (Face L n k j) := by apply _root_.YangMills.SharedProofs.p23234 <;> assumption
private instance {j : ℕ} : Fintype (Face L n k j) :=
  haveI := finite_face (L := L) (n := n) (k := k) j
  Fintype.ofFinite _
private instance {j : ℕ} : Fintype (PositiveEdge L n k j) := Fintype.ofFinite _
private theorem plaquetteCost_eq_traceDefect (U : Edge L n k 0 → ComplexMatrix2) (p : Face L n k 0) :
    PeriodicLattice.plaquetteCost U p = traceDefect (PeriodicLattice.plaquetteHolonomy U p) := by
  simp only [PeriodicLattice.plaquetteCost, traceDefect, ComplexMatrix2.halfTrace]
  simp [Complex.mul_re]
abbrev _root_.YangMills.SharedProofs.p12545 := @plaquetteCost_eq_traceDefect
private theorem plaquetteAction_eq_sum (U : Edge L n k 0 → ComplexMatrix2) :
    plaquetteAction L n k U =
      ∑ p : Face L n k 0, traceDefect (PeriodicLattice.plaquetteHolonomy U p) := by
  simp only [plaquetteAction, PeriodicLattice.wilsonAction, finsum_eq_sum_of_fintype,
    plaquetteCost_eq_traceDefect]
private theorem plaquetteHolonomy_mem {j : ℕ} {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k j) (p : Face L n k j) :
    PeriodicLattice.plaquetteHolonomy U p ∈ PeriodicLattice.compactGaugeGroup :=
  pathHolonomy_mem (fun b => hU.1 b (Set.mem_univ _)) _
private def actionBoundConstant (a : ℝ) (L n k : ℕ) [NeZero L] : ℝ :=
  (Fintype.card (Face L n k 0) : ℝ) +
    a * (2 * ∑ i : Fin k, (Fintype.card (PositiveEdge L n k ((i : ℕ) + 1)) : ℝ))
private theorem actionBoundConstant_nonneg {a : ℝ} (ha : 0 < a) :
    0 ≤ actionBoundConstant a L n k := by
  unfold actionBoundConstant
  positivity
private theorem chainAction_le {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {X : ChainPoint L n k} (hX : IsCompactValued X)
    (h1 : ∀ p : Face L n k 0, ‖PeriodicLattice.plaquetteHolonomy X.fine p - 1‖ < ε)
    (h2 : ∀ (i : Fin k) (c : PositiveEdge L n k ((i : ℕ) + 1)), ‖X.noise i c - 1‖ < ε)
    (h3 : ∀ (i : Fin k) (c : PositiveEdge L n k ((i : ℕ) + 1)),
      ‖meanRadius (levelField X i) c.1 - 1‖ < ε) :
    chainAction a X ≤ actionBoundConstant a L n k * ε := by
  have hU : X.fine ∈ fieldSpace L n k 0 := hX.2 0 (Nat.zero_le _)
  have hA : plaquetteAction L n k X.fine ≤ (Fintype.card (Face L n k 0) : ℝ) * ε := by
    rw [plaquetteAction_eq_sum]
    have := Finset.sum_le_card_nsmul Finset.univ
      (fun p : Face L n k 0 => traceDefect (PeriodicLattice.plaquetteHolonomy X.fine p)) ε
      (fun p _ => traceDefect_le_of_norm_lt (plaquetteHolonomy_mem hU p) hε hε1 (h1 p))
    simpa using this
  have hterm : ∀ (i : Fin k) (c : PositiveEdge L n k ((i : ℕ) + 1)),
      (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c) ≤ 2 * ε := by
    intro i c
    have hr : (meanRadius (levelField X i) c.1).re ≤ 2 := by
      have hre : (meanRadius (levelField X i) c.1).re - 1 =
          (meanRadius (levelField X i) c.1 - 1).re := by simp
      have hnorm := Complex.re_le_norm (meanRadius (levelField X i) c.1 - 1)
      have hlt := h3 i c
      linarith
    have he0 := traceDefect_nonneg (hX.1 i c)
    have he1 := traceDefect_le_of_norm_lt (hX.1 i c) hε hε1 (h2 i c)
    calc _ ≤ 2 * traceDefect (X.noise i c) := mul_le_mul_of_nonneg_right hr he0
      _ ≤ 2 * ε := by linarith
  have hS : ∑ i : Fin k, ∑ᶠ c : PositiveEdge L n k ((i : ℕ) + 1),
      (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c) ≤
      ∑ i : Fin k, (Fintype.card (PositiveEdge L n k ((i : ℕ) + 1)) : ℝ) * (2 * ε) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [finsum_eq_sum_of_fintype]
    have := Finset.sum_le_card_nsmul Finset.univ
      (fun c : PositiveEdge L n k ((i : ℕ) + 1) =>
        (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c)) (2 * ε)
      (fun c _ => hterm i c)
    simpa using this
  have hS' := mul_le_mul_of_nonneg_left hS ha.le
  rw [← Finset.sum_mul] at hS'
  simp only [chainAction, actionBoundConstant]
  nlinarith
end Action
theorem minimizerGaugeEquivalentToSmallMove_holds (hO : SmallActionNearGaugeOrbit)
    (hF : MinimizerFieldsNearOne)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    (hor : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (hlat : PeriodicLattice.CoordinateDescription) :
    MinimizerGaugeEquivalentToSmallMove := by
  intro a ha L hL k n hk hn N e O hOn
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  haveI : NeZero (2 * L ^ n) := ⟨by
    have := hL.2
    positivity⟩
  have hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    xor_positive_opposite hor hL hn
  obtain ⟨K, hK0, hK⟩ := coords_le_of_values_le (L := L) (n := n) (k := k) e
  obtain ⟨r, hr0, hr⟩ := Metric.mem_nhds_iff.1 hOn
  set τ : ℝ := min (1 / 2) (r / (4 * K)) with hτ
  have hτ0 : 0 < τ := lt_min (by norm_num) (by positivity)
  obtain ⟨δ, hδ0, hδ⟩ := hO a ha L hL k n hk hn τ hτ0
  set M : ℝ := actionBoundConstant a L n k + 1 with hM
  have hM0 : 0 < M := by
    have := actionBoundConstant_nonneg (L := L) (n := n) (k := k) ha
    linarith
  set ε : ℝ := min 1 (δ / M) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hev : ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
      ∀ (z : TorusFields.TorusSite (2 * L ^ n)) (μ : Fin 4),
        1 - ((V z μ : BlockAverages.UnitQuaternion) : Quaternion ℝ).re < δ ^ 2 / 2 := by
    refine eventually_all.2 fun z => eventually_all.2 fun μ => ?_
    have hc : Continuous fun V : TorusFields.TorusField (2 * L ^ n) =>
        1 - ((V z μ : BlockAverages.UnitQuaternion) : Quaternion ℝ).re :=
      continuous_const.sub (Quaternion.continuous_re.comp (continuous_subtype_val.comp
        ((continuous_apply μ).comp (continuous_apply z))))
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    have hone : ((TorusFields.trivialField (2 * L ^ n) z μ : BlockAverages.UnitQuaternion) :
        Quaternion ℝ) = 1 := rfl
    have hre : (1 : Quaternion ℝ).re = 1 := rfl
    simp only [hone, hre, sub_self]
    positivity
  filter_upwards [hF a ha L hL k n hk hn ε hε0, hev] with V hV₁ hV₂ W hW X hX
  obtain ⟨s1, s2, s3⟩ := hV₁ W hW X hX
  have hact : chainAction a X < δ := by
    have h1 := chainAction_le ha hε0 (min_le_left _ _) hX.compact
      (fun p => s1 0 (Nat.zero_le _) p) s2 s3
    have h2 : ε ≤ δ / M := min_le_right _ _
    have h3 : 0 ≤ actionBoundConstant a L n k := actionBoundConstant_nonneg ha
    have h4 : actionBoundConstant a L n k * ε ≤ actionBoundConstant a L n k * (δ / M) :=
      mul_le_mul_of_nonneg_left h2 h3
    have h5 : actionBoundConstant a L n k * (δ / M) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ hM0, hM]
      nlinarith
    linarith
  have hWr : W ∈ fieldSpace L n k k := hW.1
  have hpos : ∀ c : PositiveEdge L n k k, traceDefect (W c.1) < δ ^ 2 / 2 := by
    intro c
    obtain ⟨z, μ, hz⟩ := top_edge_eq_forward hlat hL hn c
    rw [hz, hW.2 z μ, traceDefect_quaternionToMatrix]
    exact hV₂ z μ
  have htop : ∀ b, ComplexMatrix2.operatorNorm (levelField X k b - 1) < δ := by
    rw [hX.top_eq]
    intro b
    have hb : traceDefect (W b) < δ ^ 2 / 2 := by
      by_cases h : b.IsPositivelyOriented
      · exact hpos ⟨b, h⟩
      · have hr' := (positive_or_opposite_positive b).resolve_left h
        have h2 : traceDefect (W b.opposite) < δ ^ 2 / 2 := hpos ⟨b.opposite, hr'⟩
        rwa [hWr.2 b (Set.mem_univ _), traceDefect_inv (hWr.1 b (Set.mem_univ _))] at h2
    have h1 := norm_sub_one_sq (hWr.1 b (Set.mem_univ _))
    have h2 : ‖W b - 1‖ ^ 2 < δ ^ 2 := by linarith
    exact lt_of_pow_lt_pow_left₀ 2 hδ0.le h2
  obtain ⟨v, hv, hv1, hb, hnz⟩ := hδ X hX.compact htop hact
  have hU : (gaugeTransformPoint v X).fine ∈ fieldSpace L n k 0 :=
    gaugeTransform_mem_fieldSpace hv (hX.compact.2 0 (Nat.zero_le _))
  have hNr : ∀ i c, (gaugeTransformPoint v X).noise i c ∈ PeriodicLattice.compactGaugeGroup :=
    fun i c => ComplexMatrix2.specialUnitary.mul_mem
      (ComplexMatrix2.specialUnitary.mul_mem (hv _) (hX.compact.1 i c)) (inv_mem_compact (hv _))
  obtain ⟨ξ, hξ, hξ1, hξ2⟩ := exists_tangent_of_near_one hxor hEL hU hNr (min_le_left _ _)
    (fun b => (hb b).le) (fun i c => (hnz i c).le)
  refine ⟨v, e.symm ξ, hv, hv1, hr ?_, ?_⟩
  · have h1 := hK ξ (2 * τ) (by positivity) hξ1 hξ2
    have h2 : τ ≤ r / (4 * K) := min_le_right _ _
    have h3 : K * (2 * τ) ≤ r / 2 := by
      have h4 : K * (2 * τ) ≤ K * (2 * (r / (4 * K))) := by gcongr
      have h5 : K * (2 * (r / (4 * K))) = r / 2 := by
        field_simp
        ring
      linarith
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  · rw [e.apply_symm_apply, hξ]
end YangMills.Construction.RunningCouplingSlope.MinimizerGaugeEquivalence
end

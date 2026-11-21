import YangMills.Construction.Lattice.AveragingMapIsABorelMapProof
import YangMills.Construction.Matrices.ExponentialOfLieElements
import YangMills.Construction.Towers.PathsDifferentiableAtZero
import YangMills.Construction.Towers.PropertiesOfTheGaugeFixingFunctionsProof
import YangMills.Construction.Towers.WritingsOfAChainInTheLeftChartProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.DiffAtZeroPaths
open YangMills.Construction.Matrices
variable {L n k j : ℕ}
theorem isPositivelyOriented_or_opposite (e : Edge L n k j) :
    e.IsPositivelyOriented ∨ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem not_isPositivelyOriented_opposite (hQ : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (e : Edge L n k j)
    (he : e.IsPositivelyOriented) : ¬ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
theorem opposite_opposite (e : Edge L n k j) : e.opposite.opposite = e := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
theorem inv_eq_star {V : ComplexMatrix2} (hV : V ∈ ComplexMatrix2.specialUnitary) : V⁻¹ = star V := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.inv_eq_star_of_mem_specialUnitary <;> assumption
theorem star_mem_specialUnitary {V : ComplexMatrix2} (hV : V ∈ ComplexMatrix2.specialUnitary) :
    star V ∈ ComplexMatrix2.specialUnitary := by
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.1 hV
  refine Matrix.mem_specialUnitaryGroup_iff.2 ⟨Unitary.star_mem hu, ?_⟩
  rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hd, star_one]
theorem inv_inv_of_mem {V : ComplexMatrix2} (hV : V ∈ ComplexMatrix2.specialUnitary) : V⁻¹⁻¹ = V := by apply _root_.YangMills.SharedProofs.p318 <;> assumption
theorem hasDerivAt_entry {W : ℝ → ComplexMatrix2} {d : ComplexMatrix2} (h : HasDerivAt W d 0)
    (a c : Fin 2) : HasDerivAt (fun t => W t a c) (d a c) 0 := by
  let p : ComplexMatrix2 →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a c)
  exact (p.hasFDerivAt (x := W 0)).comp_hasDerivAt 0 h
theorem inv_I_smul_logDeriv_mem {W : ℝ → ComplexMatrix2}
    (hev : ∀ᶠ t in 𝓝 (0 : ℝ), W t ∈ ComplexMatrix2.specialUnitary)
    (hd : DifferentiableAt ℝ W 0) :
    Complex.I⁻¹ • (deriv W 0 * (W 0)⁻¹) ∈ ComplexMatrix2.hermitianTraceless := by
  have h0 : W 0 ∈ ComplexMatrix2.specialUnitary := hev.self_of_nhds
  have hW : HasDerivAt W (deriv W 0) 0 := hd.hasDerivAt
  set d := deriv W 0 with hdef
  obtain ⟨hu0, hdet0⟩ := Matrix.mem_specialUnitaryGroup_iff.1 h0
  have hprod : HasDerivAt (fun t => W t * star (W t)) (d * star (W 0) + W 0 * star d) 0 :=
    hW.mul hW.star
  have hone : HasDerivAt (fun t => W t * star (W t)) (0 : ComplexMatrix2) 0 :=
    (hasDerivAt_const (0 : ℝ) (1 : ComplexMatrix2)).congr_of_eventuallyEq (hev.mono fun t ht =>
      Matrix.mem_unitaryGroup_iff.1 (Matrix.mem_specialUnitaryGroup_iff.1 ht).1)
  have hzero : d * star (W 0) + W 0 * star d = 0 := hprod.unique hone
  have hkey : W 0 * star d = -(d * star (W 0)) := eq_neg_of_add_eq_zero_right hzero
  have hdetd : HasDerivAt (fun t => W t 0 0 * W t 1 1 - W t 0 1 * W t 1 0)
      ((d 0 0 * W 0 1 1 + W 0 0 0 * d 1 1) - (d 0 1 * W 0 1 0 + W 0 0 1 * d 1 0)) 0 :=
    ((hasDerivAt_entry hW 0 0).mul (hasDerivAt_entry hW 1 1)).sub
      ((hasDerivAt_entry hW 0 1).mul (hasDerivAt_entry hW 1 0))
  have hdetc : HasDerivAt (fun t => W t 0 0 * W t 1 1 - W t 0 1 * W t 1 0) (0 : ℂ) 0 :=
    (hasDerivAt_const (0 : ℝ) (1 : ℂ)).congr_of_eventuallyEq (hev.mono fun t ht => by
      have h := (Matrix.mem_specialUnitaryGroup_iff.1 ht).2
      rwa [Matrix.det_fin_two] at h)
  have htr : (d 0 0 * W 0 1 1 + W 0 0 0 * d 1 1) - (d 0 1 * W 0 1 0 + W 0 0 1 * d 1 0) = 0 :=
    hdetd.unique hdetc
  have hinv : (W 0)⁻¹ = star (W 0) := inv_eq_star h0
  have hadj : (W 0)⁻¹ = (W 0).adjugate := by
    rw [Matrix.inv_def, hdet0, Ring.inverse_one, one_smul]
  refine ⟨?_, ?_⟩
  · rw [hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose,
      ← Matrix.star_eq_conjTranspose, star_star, hkey, star_inv₀, Complex.star_def, Complex.conj_I,
      inv_neg, neg_smul, smul_neg, neg_neg]
  · have h : ComplexMatrix2.fullTrace (d * (W 0)⁻¹) = 0 := by
      rw [hadj, Matrix.adjugate_fin_two]
      simp only [ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp
      linear_combination htr
    simp only [ComplexMatrix2.fullTrace] at h ⊢
    rw [Matrix.trace_smul, h, smul_zero]
theorem hasDerivAt_matExp_mul (X V : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • X)) * V)
      (Complex.I • X * V) 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.ChainRule.hasDerivAt_expMul_zero <;> assumption
theorem eq_inv_opposite {𝒢 : Set ComplexMatrix2} {V : Edge L n k j → ComplexMatrix2}
    (hV : PeriodicLattice.IsGaugeField 𝒢 univ V) (e : Edge L n k j) : V e = (V e.opposite)⁻¹ := by
  have h := hV.2 e.opposite (mem_univ _)
  rwa [opposite_opposite] at h
theorem curveTangent_mem (hQ : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsDiffAtZeroPath γ) : curveTangent γ ∈ edgeFormSpace L n k j := by
  have hval : ∀ e : Edge L n k j, e.IsPositivelyOriented →
      Complex.I⁻¹ • (deriv (fun t => γ t e) 0 * (γ 0 e)⁻¹) ∈ PeriodicLattice.compactLieAlgebra :=
    fun e he => inv_I_smul_logDeriv_mem (hγ.1.mono fun t ht => ht.1 e (mem_univ e)) (hγ.2 e he)
  refine ⟨fun e he => ?_, fun e => ?_⟩
  · simp only [curveTangent, extendOddly, if_pos he]
    exact hval e he
  · by_cases he : e.IsPositivelyOriented
    · have h' := not_isPositivelyOriented_opposite hQ hL hn hj e he
      simp only [curveTangent, extendOddly, if_neg h', if_pos he, opposite_opposite]
    · have h' := (isPositivelyOriented_or_opposite e).resolve_left he
      simp only [curveTangent, extendOddly, if_neg he, if_pos h', neg_neg]
theorem tendsto_nhdsWithin_fieldSpace {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsDiffAtZeroPath γ) : Tendsto γ (𝓝 0) (𝓝[fieldSpace L n k j] γ 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun e => ?_, hγ.1⟩
  by_cases he : e.IsPositivelyOriented
  · exact (hγ.2 e he).continuousAt
  · have hr := (isPositivelyOriented_or_opposite e).resolve_left he
    have hstar : ∀ V ∈ fieldSpace L n k j, V e = star (V e.opposite) := fun V hV => by
      rw [eq_inv_opposite hV e]
      exact inv_eq_star (hV.1 _ (mem_univ _))
    have hc : Tendsto (fun t => star (γ t e.opposite)) (𝓝 0) (𝓝 (star (γ 0 e.opposite))) :=
      ((continuous_id.matrix_conjTranspose).tendsto _).comp (hγ.2 _ hr).continuousAt
    rw [hstar _ hγ.1.self_of_nhds]
    exact hc.congr' (hγ.1.mono fun t ht => (hstar _ ht).symm)
theorem mem_nhdsWithin_of_isOpenFieldSet {𝒪 : Set (Edge L n k j → ComplexMatrix2)}
    (h𝒪 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒪) {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ 𝒪) : 𝒪 ∈ 𝓝[fieldSpace L n k j] U := by apply _root_.YangMills.SharedProofs.p46903 <;> assumption
theorem expTwist_of_pos {e : Edge L n k j} (he : e.IsPositivelyOriented)
    (X U : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist X U e = ComplexMatrix2.matExp (Complex.I • X e) * U e := by
  simp only [PeriodicLattice.expTwist, if_pos he]
theorem expTwist_of_not_pos {e : Edge L n k j} (he : ¬ e.IsPositivelyOriented)
    (X U : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist X U e =
      (ComplexMatrix2.matExp (Complex.I • X e.opposite) * U e.opposite)⁻¹ := by
  simp only [PeriodicLattice.expTwist, if_neg he]
theorem expTwist_mem_fieldSpace (hQ : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {X U : Edge L n k j → ComplexMatrix2}
    (hG : ∀ e : Edge L n k j, e.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • X e) * U e ∈ ComplexMatrix2.specialUnitary) :
    PeriodicLattice.expTwist X U ∈ fieldSpace L n k j := by
  refine ⟨fun e _ => ?_, fun e _ => ?_⟩
  · by_cases he : e.IsPositivelyOriented
    · rw [expTwist_of_pos he]
      exact hG e he
    · have hr := (isPositivelyOriented_or_opposite e).resolve_left he
      rw [expTwist_of_not_pos he, inv_eq_star (hG _ hr)]
      exact star_mem_specialUnitary (hG _ hr)
  · by_cases he : e.IsPositivelyOriented
    · rw [expTwist_of_not_pos (not_isPositivelyOriented_opposite hQ hL hn hj e he), opposite_opposite,
        expTwist_of_pos he]
    · have hr := (isPositivelyOriented_or_opposite e).resolve_left he
      rw [expTwist_of_pos hr, expTwist_of_not_pos he, inv_inv_of_mem (hG _ hr)]
theorem expTwist_zero_smul {U : Edge L n k j → ComplexMatrix2} (hU : U ∈ fieldSpace L n k j)
    (B : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B) U = U := by
  funext e
  by_cases he : e.IsPositivelyOriented
  · rw [expTwist_of_pos he]
    simp
  · rw [expTwist_of_not_pos he, eq_inv_opposite hU e]
    simp
theorem expTwist_path (hE : ComplexMatrix2.ExpImaginaryLieMem)
    (hQ : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) {U B : Edge L n k j → ComplexMatrix2} (hU : U ∈ fieldSpace L n k j)
    (hB : B ∈ edgeFormSpace L n k j) :
    IsDiffAtZeroPath (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) U) ∧
      PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B) U = U ∧
      curveTangent (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) U) = B := by
  have hG : ∀ e : Edge L n k j, e.IsPositivelyOriented → ∀ t : ℝ,
      ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B e)) * U e ∈ ComplexMatrix2.specialUnitary :=
    fun e he t => by
      have hmem : (t : ℂ) • B e ∈ ComplexMatrix2.hermitianTraceless := by
        rw [Complex.coe_smul]
        exact ComplexMatrix2.hermitianTraceless.smul_mem t (hB.1 e he)
      exact ComplexMatrix2.specialUnitary.mul_mem (hE.1 _ hmem) (hU.1 e (mem_univ e))
  have hfun : ∀ e : Edge L n k j, e.IsPositivelyOriented →
      (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) U e) =
        fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B e)) * U e := fun e he => by
    funext t
    rw [expTwist_of_pos he]
    rfl
  have hder : ∀ e : Edge L n k j, e.IsPositivelyOriented →
      HasDerivAt (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) U e)
        (Complex.I • B e * U e) 0 := fun e he => by
    rw [hfun e he]
    exact hasDerivAt_matExp_mul (B e) (U e)
  have hzero := expTwist_zero_smul hU B
  refine ⟨⟨Eventually.of_forall fun t => expTwist_mem_fieldSpace hQ hL hn hj fun e he =>
      hG e he t, fun e he => (hder e he).differentiableAt⟩, hzero, ?_⟩
  have hpos : ∀ e : Edge L n k j, e.IsPositivelyOriented →
      Complex.I⁻¹ • (deriv (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) U e) 0 *
        (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B) U e)⁻¹) = B e := fun e he => by
    have hUe : U e ∈ ComplexMatrix2.specialUnitary := hU.1 e (mem_univ e)
    have hone : U e * (U e)⁻¹ = 1 := by
      rw [inv_eq_star hUe]
      exact Matrix.mem_unitaryGroup_iff.1 (Matrix.mem_specialUnitaryGroup_iff.1 hUe).1
    rw [(hder e he).deriv, hzero, Matrix.smul_mul, Matrix.smul_mul, mul_assoc, hone, mul_one,
      smul_smul,
      inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  funext e
  by_cases he : e.IsPositivelyOriented
  · simp only [curveTangent, extendOddly, if_pos he]
    exact hpos e he
  · have hr := (isPositivelyOriented_or_opposite e).resolve_left he
    simp only [curveTangent, extendOddly, if_neg he]
    rw [hpos _ hr, hB.2 e, neg_neg]
end YangMills.Construction.Tower.DiffAtZeroPaths
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices
theorem diffAtZeroPathsStatement_holds (hE : ComplexMatrix2.ExpImaginaryLieMem)
    (hQ : QuotientLattices.TorusAndSpaceLatticeProperties) : diffAtZeroPathsStatement := by
  intro L n k j hL hn hj
  exact ⟨fun γ hγ => ⟨DiffAtZeroPaths.curveTangent_mem hQ hL hn hj hγ,
      DiffAtZeroPaths.tendsto_nhdsWithin_fieldSpace hγ⟩,
    fun 𝒪 h𝒪 U hU => DiffAtZeroPaths.mem_nhdsWithin_of_isOpenFieldSet h𝒪 hU,
    fun U hU B hB => DiffAtZeroPaths.expTwist_path hE hQ hL hn hj hU hB⟩
end YangMills.Construction.Tower
end

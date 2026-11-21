import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Towers.CriticalBranchAtTheBottomLevel
import YangMills.Construction.Towers.TheActionOnATower
import YangMills.Construction.Towers.WilsonActionIsRealAnalyticOnTheConfigurationsProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
namespace Tower.BottomLevel
theorem contDiffAt_matrix_inv {M : ComplexMatrix2} (hM : IsUnit M) :
    ContDiffAt ℝ 2 (fun A : ComplexMatrix2 => A⁻¹) M := by
  obtain ⟨u, rfl⟩ := hM
  have e : (fun A : ComplexMatrix2 => A⁻¹) = Ring.inverse :=
    funext Matrix.nonsing_inv_eq_ringInverse
  rw [e]
  exact contDiffAt_ringInverse ℝ u
theorem contDiff_re_fullTrace :
    ContDiff ℝ 2 (fun M : ComplexMatrix2 => (ComplexMatrix2.fullTrace M).re) := by
  let T : ComplexMatrix2 →ₗ[ℝ] ℝ :=
    { toFun := fun M => (ComplexMatrix2.fullTrace M).re
      map_add' := fun M N => by simp [ComplexMatrix2.fullTrace, Matrix.trace_add]
      map_smul' := fun c M => by simp [ComplexMatrix2.fullTrace, Matrix.trace_smul] }
  exact T.toContinuousLinearMap.contDiff
theorem det_eq_one_of_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.specialUnitary) :
    X.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.mp hX).2
theorem re_halfTrace_mul_conjTranspose (X : ComplexMatrix2) :
    (ComplexMatrix2.halfTrace (X * X.conjTranspose)).re =
      1 / 2 * (Complex.normSq (X 0 0) + Complex.normSq (X 0 1) + Complex.normSq (X 1 0) +
        Complex.normSq (X 1 1)) := by
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.normSq_apply]
  ring
theorem re_halfTrace_mul_conjTranspose_nonneg (X : ComplexMatrix2) :
    0 ≤ (ComplexMatrix2.halfTrace (X * X.conjTranspose)).re := by
  rw [re_halfTrace_mul_conjTranspose]
  have := Complex.normSq_nonneg (X 0 0)
  have := Complex.normSq_nonneg (X 0 1)
  have := Complex.normSq_nonneg (X 1 0)
  have := Complex.normSq_nonneg (X 1 1)
  positivity
theorem eq_zero_of_re_halfTrace_mul_conjTranspose {X : ComplexMatrix2}
    (h : (ComplexMatrix2.halfTrace (X * X.conjTranspose)).re = 0) : X = 0 := by
  rw [re_halfTrace_mul_conjTranspose] at h
  have h0 := Complex.normSq_nonneg (X 0 0)
  have h1 := Complex.normSq_nonneg (X 0 1)
  have h2 := Complex.normSq_nonneg (X 1 0)
  have h3 := Complex.normSq_nonneg (X 1 1)
  have e0 : X 0 0 = 0 := Complex.normSq_eq_zero.1 (by linarith)
  have e1 : X 0 1 = 0 := Complex.normSq_eq_zero.1 (by linarith)
  have e2 : X 1 0 = 0 := Complex.normSq_eq_zero.1 (by linarith)
  have e3 : X 1 1 = 0 := Complex.normSq_eq_zero.1 (by linarith)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e0, e1, e2, e3]
theorem eq_zero_of_traceFinsumNorm_eq_zero {ι : Type*} [Fintype ι] {f : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless) (h : traceFinsumNorm f = 0) : f = 0 := by
  have hterm : ∀ i, ComplexMatrix2.halfTrace (f i * f i) =
      ComplexMatrix2.halfTrace (f i * (f i).conjTranspose) := fun i => by
    rw [← (hf i).1]
  have hre : (traceFinsumPairing f f).re =
      ∑ i, (ComplexMatrix2.halfTrace (f i * (f i).conjTranspose)).re := by
    simp only [traceFinsumPairing, finsum_eq_sum_of_fintype, Complex.re_sum, hterm]
  have hnn : ∀ i ∈ (Finset.univ : Finset ι),
      0 ≤ (ComplexMatrix2.halfTrace (f i * (f i).conjTranspose)).re :=
    fun i _ => re_halfTrace_mul_conjTranspose_nonneg _
  have h0 : (traceFinsumPairing f f).re ≤ 0 := Real.sqrt_eq_zero'.1 h
  have h1 : ∑ i, (ComplexMatrix2.halfTrace (f i * (f i).conjTranspose)).re = 0 :=
    le_antisymm (hre ▸ h0) (Finset.sum_nonneg hnn)
  funext i
  exact eq_zero_of_re_halfTrace_mul_conjTranspose
    ((Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1 i (Finset.mem_univ i))
theorem traceFinsumNorm_neg {ι : Type*} (f : ι → ComplexMatrix2) :
    traceFinsumNorm (-f) = traceFinsumNorm f := by
  simp [traceFinsumNorm, traceFinsumPairing]
theorem hasDerivAt_fderiv_smul_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : E → ℝ} (h2 : ContDiffAt ℝ 2 G 0) (v w : E) :
    HasDerivAt (fun s : ℝ => fderiv ℝ G (s • v) w) (fderiv ℝ (fderiv ℝ G) 0 v w) 0 := by
  have hdd : DifferentiableAt ℝ (fderiv ℝ G) ((0 : ℝ) • v) := by
    rw [zero_smul]
    exact (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hh : HasDerivAt (fun s : ℝ => s • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hc : HasDerivAt (fun s : ℝ => fderiv ℝ G (s • v)) (fderiv ℝ (fderiv ℝ G) 0 v) 0 := by
    have h := hdd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hh
    rw [zero_smul] at h
    exact h
  simpa using hc.clm_apply (hasDerivAt_const (0 : ℝ) w)
section Edges
variable {L n k : ℕ}
theorem isPositivelyOriented_or_opposite (b : Edge L n k 0) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.isPositivelyOriented_or_opposite <;> assumption
theorem not_isPositivelyOriented_opposite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (b : Edge L n k 0)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.not_opposite_isPositivelyOriented <;> assumption
theorem opposite_opposite (b : Edge L n k 0) : b.opposite.opposite = b :=
  PeriodicLattice.Bond.ext rfl rfl
theorem edgeFormOfPositiveValues_of_pos (w : PositiveEdge L n k 0 → ComplexMatrix2)
    {b : Edge L n k 0} (h : b.IsPositivelyOriented) :
    edgeFormOfPositiveValues w b = w ⟨b, h⟩ := by
  simp [edgeFormOfPositiveValues, h]
theorem expTwist_restrict (X U : Edge L n k 0 → ComplexMatrix2) :
    PeriodicLattice.expTwist (edgeFormOfPositiveValues (restrictToPositiveEdges X)) U =
      PeriodicLattice.expTwist X U := by
  funext b
  by_cases h : b.IsPositivelyOriented
  · simp only [PeriodicLattice.expTwist, if_pos h, edgeFormOfPositiveValues_of_pos _ h]
    rfl
  · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
    simp only [PeriodicLattice.expTwist, if_neg h, edgeFormOfPositiveValues_of_pos _ h']
    rfl
theorem isOpenNhdOfOne_fieldSpace (hE : Tower.BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    IsOpenNhdOfOne (fieldSpace L n k 0) := by
  have A := ((hE L hL k 0 (Nat.zero_le k)).1 n hn).2.2.2.2.2.2.2.2.1
  refine ⟨⟨subset_rfl, (A _ subset_rfl).1 ⟨univ, isOpen_univ, by simp⟩⟩, ?_⟩
  exact ⟨fun _ _ => one_mem _, fun _ _ => by simp [trivialField]⟩
end Edges
section Analyticity
variable {L n k : ℕ} [Fintype (PositiveEdge L n k 0)] [Fintype (Face L n k 0)]
theorem isAnalytic_plaquetteAction (hH : HolomorphyClosureStatement)
    (hO : IsOpenFieldSet PeriodicLattice.compactGaugeGroup (fieldSpace L n k 0))
    (hnb : ∀ b : Edge L n k 0, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented) :
    IsAnalyticFieldFunction (fieldSpace L n k 0) (plaquetteAction L n k) := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.isAnalyticFieldFunction_plaquetteAction <;> assumption
end Analyticity
section LeftChart
variable {L n k : ℕ}
def twisted (U : Edge L n k 0 → ComplexMatrix2) (y : PositiveEdge L n k 0 → ComplexMatrix2) :
    Edge L n k 0 → ComplexMatrix2 :=
  PeriodicLattice.expTwist (edgeFormOfPositiveValues y) U
def positivePart (L n k : ℕ) : edgeFormSpace L n k 0 →ₗ[ℝ] PositiveEdge L n k 0 → ComplexMatrix2 where
  toFun B := restrictToPositiveEdges (B : Edge L n k 0 → ComplexMatrix2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
variable [Fintype (PositiveEdge L n k 0)]
theorem contDiff_matExp_mul (c : PositiveEdge L n k 0) (V : ComplexMatrix2) :
    ContDiff ℝ 2 (fun y : PositiveEdge L n k 0 → ComplexMatrix2 =>
      ComplexMatrix2.matExp (Complex.I • y c) * V) := by
  have hE : ContDiff ℝ 2 (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2) :=
    contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact (hE.comp ((contDiff_apply ℝ ComplexMatrix2 c).const_smul Complex.I)).mul contDiff_const
theorem contDiffAt_twisted {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0)
    (b : Edge L n k 0) : ContDiffAt ℝ 2 (fun y => twisted U y b) 0 := by
  by_cases h : b.IsPositivelyOriented
  · have e : (fun y => twisted U y b) =
        fun y => ComplexMatrix2.matExp (Complex.I • y ⟨b, h⟩) * U b := by
      funext y
      simp only [twisted, PeriodicLattice.expTwist, if_pos h, edgeFormOfPositiveValues_of_pos _ h]
    rw [e]
    exact (contDiff_matExp_mul _ _).contDiffAt
  · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
    have e : (fun y => twisted U y b) =
        fun y => (ComplexMatrix2.matExp (Complex.I • y ⟨b.opposite, h'⟩) * U b.opposite)⁻¹ := by
      funext y
      simp only [twisted, PeriodicLattice.expTwist, if_neg h, edgeFormOfPositiveValues_of_pos _ h']
    rw [e]
    have hS : U b.opposite ∈ ComplexMatrix2.specialUnitary := hU.1 b.opposite (mem_univ _)
    have hM : IsUnit ((fun y : PositiveEdge L n k 0 → ComplexMatrix2 =>
        ComplexMatrix2.matExp (Complex.I • y ⟨b.opposite, h'⟩) * U b.opposite) 0) := by
      have h1 : (U b.opposite).det = 1 := det_eq_one_of_mem hS
      simp only [Pi.zero_apply, smul_zero, NormedSpace.exp_zero, one_mul]
      exact (Matrix.isUnit_iff_isUnit_det _).2 (by rw [h1]; exact isUnit_one)
    exact (contDiffAt_matrix_inv hM).comp (0 : PositiveEdge L n k 0 → ComplexMatrix2)
      (contDiff_matExp_mul _ _).contDiffAt
theorem contDiffAt_list_prod_twisted {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k 0) (l : List (Edge L n k 0)) :
    ContDiffAt ℝ 2 (fun y => (l.map (twisted U y)).prod) 0 := by
  induction l with
  | nil => simpa using contDiffAt_const
  | cons b l ih =>
    simpa only [List.map_cons, List.prod_cons] using (contDiffAt_twisted hU b).mul ih
theorem contDiffAt_plaquetteAction_twisted [Fintype (Face L n k 0)]
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0) :
    ContDiffAt ℝ 2 (fun y => plaquetteAction L n k (twisted U y)) 0 := by
  have e : (fun y => plaquetteAction L n k (twisted U y)) = fun y => ∑ p : Face L n k 0,
      (1 - (1 / 2) * (ComplexMatrix2.fullTrace
        (((PeriodicLattice.Plaquette.boundaryBonds p).map (twisted U y)).prod)).re) := by
    funext y
    simp only [plaquetteAction, PeriodicLattice.wilsonAction, finsum_eq_sum_of_fintype,
      PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteHolonomy,
      PeriodicLattice.pathHolonomy]
  rw [e]
  refine ContDiffAt.sum fun p _ => ?_
  exact contDiffAt_const.sub (contDiffAt_const.mul
    (contDiff_re_fullTrace.contDiffAt.comp _ (contDiffAt_list_prod_twisted hU _)))
omit [Fintype (PositiveEdge L n k 0)] in
theorem plaquetteAction_expTwist_line (U B B' : Edge L n k 0 → ComplexMatrix2) (s t : ℝ) :
    plaquetteAction L n k
        (PeriodicLattice.expTwist (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B') U) =
      plaquetteAction L n k
        (twisted U (s • restrictToPositiveEdges B + t • restrictToPositiveEdges B')) := by
  show _ = plaquetteAction L n k (PeriodicLattice.expTwist
    (edgeFormOfPositiveValues (s • restrictToPositiveEdges B + t • restrictToPositiveEdges B')) U)
  rw [← expTwist_restrict (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B') U]
  congr 3
variable [Fintype (Face L n k 0)]
theorem leftDeriv_plaquetteAction {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k 0) (B : Edge L n k 0 → ComplexMatrix2) :
    leftDeriv (fun V => (plaquetteAction L n k V : ℂ)) U B =
      ((fderiv ℝ (fun y => plaquetteAction L n k (twisted U y)) 0
        (restrictToPositiveEdges B) : ℝ) : ℂ) := by
  set ψ : (PositiveEdge L n k 0 → ComplexMatrix2) → ℝ :=
    fun y => plaquetteAction L n k (twisted U y) with hψ
  have hd : DifferentiableAt ℝ ψ 0 :=
    (contDiffAt_plaquetteAction_twisted hU).differentiableAt (by norm_num)
  have hh : HasDerivAt (fun u : ℝ => u • restrictToPositiveEdges B) (restrictToPositiveEdges B) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (restrictToPositiveEdges B)
  have hc : HasDerivAt (ψ ∘ fun u : ℝ => u • restrictToPositiveEdges B)
      (fderiv ℝ ψ 0 (restrictToPositiveEdges B)) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hh (by simp)
  have e : (fun t : ℝ => (plaquetteAction L n k (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ t • B) U) : ℂ)) =
      fun t => ((ψ ∘ fun u : ℝ => u • restrictToPositiveEdges B) t : ℂ) := by
    funext t
    have h := plaquetteAction_expTwist_line U B 0 0 t
    simp only [hψ, Function.comp_apply]
    have h := plaquetteAction_expTwist_line U 0 B 0 t
    simpa using congrArg (fun x : ℝ => (x : ℂ)) h
  simp only [leftDeriv, directionalDeriv]
  rw [e]
  exact hc.ofReal_comp.deriv
omit [Fintype (PositiveEdge L n k 0)] [Fintype (Face L n k 0)] in
theorem exists_inner_eq {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (c : InnerProductSpace.Core ℝ V) (l : V →ₗ[ℝ] ℝ) : ∃ g : V, ∀ v, c.inner g v = l v := by
  let _ : NormedAddCommGroup V := c.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ V := InnerProductSpace.ofCore c.toCore
  have : CompleteSpace V := FiniteDimensional.complete ℝ V
  refine ⟨(InnerProductSpace.toDual ℝ V).symm (LinearMap.toContinuousLinearMap l), fun v => ?_⟩
  exact InnerProductSpace.toDual_symm_apply
theorem leftGradient_mem (hF : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0) :
    leftGradient (fieldSpace L n k 0) (fun V => (plaquetteAction L n k V : ℂ)) U ∈
      edgeFormSpace L n k 0 := by
  obtain ⟨-, hfd, -, c, hc⟩ := hF L n k 0 hL hn (Nat.zero_le k)
  let l : edgeFormSpace L n k 0 →ₗ[ℝ] ℝ :=
    (fderiv ℝ (fun y => plaquetteAction L n k (twisted U y)) 0).toLinearMap ∘ₗ positivePart L n k
  obtain ⟨g, hg⟩ := exists_inner_eq c l
  have hex : ∃ X, IsLeftGradient (fieldSpace L n k 0)
      (fun V => (plaquetteAction L n k V : ℂ)) U X := by
    refine ⟨(g : Edge L n k 0 → ComplexMatrix2), ⟨fun b hb => (g.2.1 b hb).2, g.2.2⟩,
      fun _ => g.2, fun B hB _ => ?_⟩
    rw [leftDeriv_plaquetteAction hU, hc g ⟨B, hB⟩, hg]
    rfl
  exact (Classical.epsilon_spec hex).2.1 fun V _ => Complex.ofReal_im _
theorem leftSecondDeriv_eq_fderiv_fderiv {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k 0) (B B' : Edge L n k 0 → ComplexMatrix2) :
    leftSecondDeriv (plaquetteAction L n k) U B B' =
      fderiv ℝ (fderiv ℝ fun y => plaquetteAction L n k (twisted U y)) 0
        (restrictToPositiveEdges B) (restrictToPositiveEdges B') := by
  set ψ : (PositiveEdge L n k 0 → ComplexMatrix2) → ℝ :=
    fun y => plaquetteAction L n k (twisted U y) with hψ
  set v := restrictToPositiveEdges B with hv
  set w := restrictToPositiveEdges B' with hw
  have h2 : ContDiffAt ℝ 2 ψ 0 := contDiffAt_plaquetteAction_twisted hU
  have hnear : ∀ᶠ x in 𝓝 (0 : PositiveEdge L n k 0 → ComplexMatrix2), DifferentiableAt ℝ ψ x :=
    (h2.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have hline : Tendsto (fun s : ℝ => s • v) (𝓝 0) (𝓝 0) := by
    have : Continuous fun s : ℝ => s • v := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have hs : (fun s : ℝ => deriv (fun t : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B') U)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℝ ψ (s • v) w := by
    filter_upwards [hline.eventually hnear] with s hs
    have e : (fun t : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B') U)) =
        ψ ∘ fun t : ℝ => s • v + t • w := funext fun t => plaquetteAction_expTwist_line U B B' s t
    have hh : HasDerivAt (fun t : ℝ => s • v + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add (s • v)
    rw [e]
    exact (hs.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hh (by simp)).deriv
  simp only [leftSecondDeriv, mixedDirectionalDeriv]
  exact hs.deriv_eq.trans (hasDerivAt_fderiv_smul_line h2 v w).deriv
theorem leftSecondDeriv_polarization {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k 0) (B B' : Edge L n k 0 → ComplexMatrix2) :
    leftSecondDeriv (plaquetteAction L n k) U (B + B') (B + B') -
        leftSecondDeriv (plaquetteAction L n k) U (B - B') (B - B') =
      4 * leftSecondDeriv (plaquetteAction L n k) U B B' := by
  have hsym : IsSymmSndFDerivAt ℝ (fun y => plaquetteAction L n k (twisted U y)) 0 :=
    (contDiffAt_plaquetteAction_twisted hU).isSymmSndFDerivAt (by simp)
  have h := hsym.eq (restrictToPositiveEdges B') (restrictToPositiveEdges B)
  have e1 : restrictToPositiveEdges (B + B') =
      restrictToPositiveEdges B + restrictToPositiveEdges B' := rfl
  have e2 : restrictToPositiveEdges (B - B') =
      restrictToPositiveEdges B - restrictToPositiveEdges B' := rfl
  simp only [leftSecondDeriv_eq_fderiv_fderiv hU, e1, e2, map_add, map_sub, add_apply, sub_apply]
  rw [h]
  ring
end LeftChart
section NullSpace
variable {L n k : ℕ} [Fintype (PositiveEdge L n k 0)] [Fintype (Face L n k 0)]
omit [Fintype (PositiveEdge L n k 0)] [Fintype (Face L n k 0)] in
theorem edgeCoboundary_add (B B' : Edge L n k 0 → ComplexMatrix2) :
    edgeCoboundary (B + B') = edgeCoboundary B + edgeCoboundary B' := by
  funext p
  simp only [edgeCoboundary, Pi.add_apply]
  abel
omit [Fintype (PositiveEdge L n k 0)] [Fintype (Face L n k 0)] in
theorem edgeCoboundary_sub (B B' : Edge L n k 0 → ComplexMatrix2) :
    edgeCoboundary (B - B') = edgeCoboundary B - edgeCoboundary B' := by
  funext p
  simp only [edgeCoboundary, Pi.sub_apply]
  abel
omit [Fintype (PositiveEdge L n k 0)] [Fintype (Face L n k 0)] in
theorem edgeCoboundary_mem {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0)
    (p : Face L n k 0) : edgeCoboundary B p ∈ ComplexMatrix2.hermitianTraceless := by
  have h : ∀ (x : Vertex L n k 0) (μ : Fin 4),
      B (PeriodicLattice.Bond.forwardFrom x μ) ∈ ComplexMatrix2.hermitianTraceless :=
    fun x μ => hB.1 _ ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
  exact ComplexMatrix2.hermitianTraceless.sub_mem (ComplexMatrix2.hermitianTraceless.sub_mem
    (ComplexMatrix2.hermitianTraceless.add_mem (h _ _) (h _ _)) (h _ _)) (h _ _)
theorem hessian_null_iff_closed
    (hsq : ∀ B ∈ edgeFormSpace L n k 0, leftSecondDeriv (plaquetteAction L n k)
      (trivialField L n k 0) B B = traceFinsumNorm (edgeCoboundary B) ^ 2)
    {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0) :
    (∀ B' ∈ edgeFormSpace L n k 0,
      leftSecondDeriv (plaquetteAction L n k) (trivialField L n k 0) B B' = 0) ↔
    IsClosedEdgeForm B := by
  have hone : trivialField L n k 0 ∈ fieldSpace L n k 0 :=
    ⟨fun _ _ => one_mem _, fun _ _ => by simp [trivialField]⟩
  constructor
  · intro h
    have h0 := h B hB
    rw [hsq B hB] at h0
    exact eq_zero_of_traceFinsumNorm_eq_zero (edgeCoboundary_mem hB)
      (pow_eq_zero_iff (two_ne_zero)|>.1 h0)
  · intro hc B' hB'
    have hc' : edgeCoboundary B = 0 := hc
    have h := leftSecondDeriv_polarization hone B B'
    rw [hsq _ ((edgeFormSpace L n k 0).add_mem hB hB'), hsq _ ((edgeFormSpace L n k 0).sub_mem hB hB'),
      edgeCoboundary_add, edgeCoboundary_sub, hc', zero_add, zero_sub, traceFinsumNorm_neg,
      sub_self] at h
    linarith
end NullSpace
section Smoothing
variable {L n k : ℕ}
theorem logDirectionalDeriv_smoothingIter_zero (hExp : ComplexMatrix2.ExpLogEstimates)
    {W B : Edge L n k 0 → ComplexMatrix2} (hW : W ∈ fieldSpace L n k 0) {c : Edge L n k 0}
    (h : c.IsPositivelyOriented) :
    logDirectionalDeriv ℝ (fun X => smoothingIter L n k 0 (PeriodicLattice.expTwist X W) c)
      (smoothingIter L n k 0 W c) B = B c := by
  have hdet : IsUnit (W c).det := by
    rw [det_eq_one_of_mem (hW.1 c (mem_univ c))]
    exact isUnit_one
  set Z : ComplexMatrix2 := Complex.I • B c with hZ
  have hlog := hExp.2.2.2.2.1
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |t| * ‖Z‖ < Real.log 2 := by
    have hc : Continuous fun t : ℝ => |t| * ‖Z‖ := continuous_abs.mul continuous_const
    refine (hc.tendsto 0).eventually (gt_mem_nhds ?_)
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hev : (fun t : ℝ => ComplexMatrix2.logSeries (smoothingIter L n k 0
      (PeriodicLattice.expTwist (algebraMap ℝ ℂ t • B) W) c *
        (smoothingIter L n k 0 W c)⁻¹)) =ᶠ[𝓝 0] fun t => t • Z := by
    filter_upwards [hsmall] with t ht
    have e : Complex.I • (algebraMap ℝ ℂ t • B) c = t • Z := by
      ext i j
      simp [hZ]
      ring
    have e2 : smoothingIter L n k 0 (PeriodicLattice.expTwist (algebraMap ℝ ℂ t • B) W) c =
        ComplexMatrix2.matExp (t • Z) * W c := by
      show PeriodicLattice.expTwist (algebraMap ℝ ℂ t • B) W c = _
      simp only [PeriodicLattice.expTwist, if_pos h, e]
    have e3 : smoothingIter L n k 0 W c = W c := rfl
    rw [e2, e3, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
    refine (hlog _ ?_).2
    show ‖t • Z‖ < _
    rwa [norm_smul, Real.norm_eq_abs]
  have hd : HasDerivAt (fun t : ℝ => t • Z) Z 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const Z
  show Complex.I⁻¹ • deriv (fun t : ℝ => ComplexMatrix2.logSeries (smoothingIter L n k 0
    (PeriodicLattice.expTwist (algebraMap ℝ ℂ t • B) W) c * (smoothingIter L n k 0 W c)⁻¹)) 0 = _
  rw [hev.deriv_eq, hd.deriv, hZ, inv_smul_smul₀ Complex.I_ne_zero]
theorem leftDifferential_smoothingIter_zero (hExp : ComplexMatrix2.ExpLogEstimates)
    {W B : Edge L n k 0 → ComplexMatrix2} (hW : W ∈ fieldSpace L n k 0)
    (hB : B ∈ edgeFormSpace L n k 0) :
    leftDifferential (smoothingIter L n k 0) W B = B := by
  funext b
  by_cases h : b.IsPositivelyOriented
  · simp only [leftDifferential, extendOddly, if_pos h]
    exact logDirectionalDeriv_smoothingIter_zero hExp hW h
  · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
    simp only [leftDifferential, extendOddly, if_neg h]
    rw [logDirectionalDeriv_smoothingIter_zero hExp hW h', hB.2 b, neg_neg]
theorem leftDifferentialLinear_smoothingIter_zero (hExp : ComplexMatrix2.ExpLogEstimates)
    {W : Edge L n k 0 → ComplexMatrix2} (hW : W ∈ fieldSpace L n k 0) :
    leftDifferentialLinear (smoothingIter L n k 0) W = LinearMap.id := by
  have h : ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0, ∀ B : edgeFormSpace L n k 0,
      (T B : Edge L n k 0 → ComplexMatrix2) = leftDifferential (smoothingIter L n k 0) W B :=
    ⟨LinearMap.id, fun B => (leftDifferential_smoothingIter_zero hExp hW B.2).symm⟩
  have hs : ∀ B : edgeFormSpace L n k 0,
      (leftDifferentialLinear (smoothingIter L n k 0) W B : Edge L n k 0 → ComplexMatrix2) =
        leftDifferential (smoothingIter L n k 0) W B :=
    Classical.epsilon_spec (p := fun T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0 =>
      ∀ B : edgeFormSpace L n k 0,
        (T B : Edge L n k 0 → ComplexMatrix2) = leftDifferential (smoothingIter L n k 0) W B) h
  refine LinearMap.ext fun B => Subtype.ext ?_
  exact (hs B).trans (leftDifferential_smoothingIter_zero hExp hW B.2)
theorem hermitianPart_mem {X : ComplexMatrix2} (hX : ComplexMatrix2.fullTrace X = 0) :
    (1 / 2 : ℂ) • (X + X.conjTranspose) ∈ ComplexMatrix2.hermitianTraceless := by
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      hs, add_comm X.conjTranspose X]
  · have hX' : Matrix.trace X = 0 := hX
    simp [ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_add,
      Matrix.trace_conjTranspose, hX']
theorem skewPart_mem {X : ComplexMatrix2} (hX : ComplexMatrix2.fullTrace X = 0) :
    (-(Complex.I / 2)) • (X - X.conjTranspose) ∈ ComplexMatrix2.hermitianTraceless := by
  have hs : star (-(Complex.I / 2)) = Complex.I / 2 := by
    simp
    ring
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      hs, neg_smul, ← smul_neg, neg_sub]
  · have hX' : Matrix.trace X = 0 := hX
    simp [ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_sub,
      Matrix.trace_conjTranspose, hX']
theorem exists_real_imaginary_parts {h : Edge L n k 0 → ComplexMatrix2}
    (hh : h ∈ complexEdgeForms L n k 0) :
    ∃ f f' : edgeFormSpace L n k 0,
      h = (f : Edge L n k 0 → ComplexMatrix2) + Complex.I • (f' : Edge L n k 0 → ComplexMatrix2) := by
  have m1 : (fun b => (1 / 2 : ℂ) • (h b + (h b).conjTranspose)) ∈ edgeFormSpace L n k 0 := by
    refine ⟨fun b hb => hermitianPart_mem (hh.1 b hb), fun b => ?_⟩
    simp only [hh.2 b, Matrix.conjTranspose_neg]
    rw [← neg_add, smul_neg]
  have m2 : (fun b => (-(Complex.I / 2)) • (h b - (h b).conjTranspose)) ∈
      edgeFormSpace L n k 0 := by
    refine ⟨fun b hb => skewPart_mem (hh.1 b hb), fun b => ?_⟩
    simp only [hh.2 b, Matrix.conjTranspose_neg]
    rw [show -h b - -(h b).conjTranspose = -(h b - (h b).conjTranspose) by abel, smul_neg]
  refine ⟨⟨_, m1⟩, ⟨_, m2⟩, ?_⟩
  funext b
  show h b = (1 / 2 : ℂ) • (h b + (h b).conjTranspose) +
    Complex.I • (-(Complex.I / 2)) • (h b - (h b).conjTranspose)
  have hI : Complex.I * -(Complex.I / 2) = 1 / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
  rw [smul_smul, hI]
  module
variable [Fintype (PositiveEdge L n k 0)]
theorem edgeFormPairing_eq_sum (x y : Edge L n k 0 → ComplexMatrix2) : edgeFormPairing x y =
    ∑ b : PositiveEdge L n k 0, ComplexMatrix2.halfTrace (x b.1 * y b.1) := by
  simp only [edgeFormPairing, traceFinsumPairing, restrictToPositiveEdges, finsum_eq_sum_of_fintype]
theorem complexEdgeForm_ext
    (hnb : ∀ b : Edge L n k 0, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    {x y : Edge L n k 0 → ComplexMatrix2} (hx : x ∈ complexEdgeForms L n k 0)
    (hy : y ∈ complexEdgeForms L n k 0)
    (h : ∀ f ∈ complexEdgeForms L n k 0, edgeFormPairing x f = edgeFormPairing y f) : x = y := by
  have hz : x - y ∈ complexEdgeForms L n k 0 := (complexEdgeForms L n k 0).sub_mem hx hy
  set z := x - y with hzdef
  let f : Edge L n k 0 → ComplexMatrix2 := extendOddly fun b => (z b).conjTranspose
  have hfp : ∀ {b : Edge L n k 0}, b.IsPositivelyOriented → f b = (z b).conjTranspose :=
    fun hb => by simp [f, extendOddly, hb]
  have hfn : ∀ {b : Edge L n k 0}, ¬ b.IsPositivelyOriented →
      f b = -(z b.opposite).conjTranspose :=
    fun hb => by simp [f, extendOddly, hb]
  have hf : f ∈ complexEdgeForms L n k 0 := by
    refine ⟨fun b hb => ?_, fun b => ?_⟩
    · rw [hfp hb]
      have h0 : Matrix.trace (z b) = 0 := hz.1 b hb
      show Matrix.trace (z b).conjTranspose = 0
      simp [Matrix.trace_conjTranspose, h0]
    · by_cases hb : b.IsPositivelyOriented
      · rw [hfn (hnb b hb), hfp hb, opposite_opposite]
      · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
        rw [hfp hr, hfn hb, neg_neg]
  have hsum : ∑ b : PositiveEdge L n k 0,
      ComplexMatrix2.halfTrace (z b.1 * (z b.1).conjTranspose) = 0 := by
    have h1 := h f hf
    rw [edgeFormPairing_eq_sum, edgeFormPairing_eq_sum] at h1
    have h2 : ∑ b : PositiveEdge L n k 0, (ComplexMatrix2.halfTrace (x b.1 * f b.1) -
        ComplexMatrix2.halfTrace (y b.1 * f b.1)) = 0 := by
      rw [Finset.sum_sub_distrib, h1, sub_self]
    rw [← h2]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hfp b.2, hzdef, Pi.sub_apply, sub_mul]
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_sub, mul_sub]
  have hnn : ∀ b ∈ (Finset.univ : Finset (PositiveEdge L n k 0)),
      0 ≤ (ComplexMatrix2.halfTrace (z b.1 * (z b.1).conjTranspose)).re :=
    fun b _ => re_halfTrace_mul_conjTranspose_nonneg _
  have hre : ∑ b : PositiveEdge L n k 0,
      (ComplexMatrix2.halfTrace (z b.1 * (z b.1).conjTranspose)).re = 0 := by
    rw [← Complex.re_sum, hsum]
    rfl
  have hzero : ∀ b : Edge L n k 0, b.IsPositivelyOriented → z b = 0 := fun b hb =>
    eq_zero_of_re_halfTrace_mul_conjTranspose
      ((Finset.sum_eq_zero_iff_of_nonneg hnn).1 hre ⟨b, hb⟩ (Finset.mem_univ _))
  have hall : z = 0 := by
    funext b
    by_cases hb : b.IsPositivelyOriented
    · exact hzero b hb
    · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
      have h3 := hz.2 b
      rw [hzero _ hr] at h3
      simpa using h3.symm
  exact sub_eq_zero.1 hall
theorem realTransposeMap_id
    (hnb : ∀ b : Edge L n k 0, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (g : edgeFormSpace L n k 0) :
    (PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L n k 0)
      (S' := edgePairedSpace L n k 0) LinearMap.id g).1 = g.1 := by
  let T₀ : (edgePairedSpace L n k 0).realSubmodule →ₗ[ℝ] (edgePairedSpace L n k 0).realSubmodule :=
    LinearMap.id
  have hreal : ∀ x : edgeFormSpace L n k 0,
      (x : Edge L n k 0 → ComplexMatrix2) ∈ complexEdgeForms L n k 0 :=
    fun x => ⟨fun b hb => (x.2.1 b hb).2, x.2.2⟩
  have hC₁ : PairedFunctionSpace.IsComplexification T₀ LinearMap.id := fun _ _ _ hh => hh
  have hC : PairedFunctionSpace.IsComplexification T₀ (PairedFunctionSpace.complexification T₀) :=
    Classical.epsilon_spec ⟨_, hC₁⟩
  have hCid : PairedFunctionSpace.complexification T₀ = LinearMap.id := by
    refine LinearMap.ext fun h => Subtype.ext ?_
    obtain ⟨f, f', hs⟩ := exists_real_imaginary_parts h.2
    exact (hC f f' h hs).trans hs.symm
  have hD : PairedFunctionSpace.IsTransposeMap (PairedFunctionSpace.complexification T₀)
      (PairedFunctionSpace.transposeMap (PairedFunctionSpace.complexification T₀)) :=
    Classical.epsilon_spec ⟨LinearMap.id, by
      rw [hCid]
      intro _ _ _
      rfl⟩
  have hDid : ∀ h : (edgePairedSpace L n k 0).complexSubmodule,
      (PairedFunctionSpace.transposeMap (PairedFunctionSpace.complexification T₀) h).1 = h.1 := by
    intro h
    refine complexEdgeForm_ext hnb (Subtype.property _) h.2 fun f hf => ?_
    have h1 := hD h ⟨f, hf⟩ (Set.toFinite _)
    have h2 : PairedFunctionSpace.complexification T₀ ⟨f, hf⟩ = ⟨f, hf⟩ := by
      rw [hCid]
      rfl
    rw [h2] at h1
    exact h1
  have hR₁ : PairedFunctionSpace.IsRealTransposeMap T₀ LinearMap.id := fun _ h hh =>
    ((hDid h).trans hh).symm
  have hR : PairedFunctionSpace.IsRealTransposeMap T₀ (PairedFunctionSpace.realTransposeMap T₀) :=
    Classical.epsilon_spec ⟨_, hR₁⟩
  exact (hR g ⟨g.1, hreal g⟩ rfl).trans (hDid _)
end Smoothing
def bottomEnergy (L n k : ℕ) : ∀ j : ℕ, (Edge L n k j → ComplexMatrix2) → ℝ
  | 0 => plaquetteAction L n k
  | _ + 1 => fun _ => 0
def bottomData (L n k : ℕ) : CriticalBranchData L n k := ⟨bottomEnergy L n k, fun _ _ _ => 1⟩
theorem eventuallyNearIdentity_of_forall {L n k : ℕ} {P : (Edge L n k 0 → ComplexMatrix2) → Prop}
    (h : ∀ V ∈ fieldSpace L n k 0, P V) : EventuallyNearIdentity (fieldSpace L n k 0) P :=
  Filter.Eventually.mono self_mem_nhdsWithin h
end Tower.BottomLevel
open Tower Tower.BottomLevel in
theorem Tower.bottomLevelCriticalBranch_holds (hAct : Tower.ActionFacts.Statement)
    (hForms : Tower.FiniteSideFormSpaces)
    (hLat : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hFin : Tower.BondSetFields.ProductStructureHolds)
    (hExp : ComplexMatrix2.ExpLogEstimates)
    (hHol : GroupLieProduct.HolomorphyClosureStatement) :
    Tower.BottomLevelCriticalBranch := by
  intro L n k hL hn
  obtain ⟨hfin, -⟩ := hForms L n k 0 hL hn (Nat.zero_le k)
  let _ : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
  have hplaq : Finite (Face L n k 0) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h⟩ := (hLat L hL n 0 k hn (Nat.zero_le k)).2.1
    exact h
  let _ : Fintype (Face L n k 0) := Fintype.ofFinite _
  have hnb := not_isPositivelyOriented_opposite (k := k) hLat hL hn
  obtain ⟨⟨-, hnn, h1⟩, hgauge, hiso, -, -, hgrad, hsq⟩ := hAct L k n hL hn
  have hsq' : ∀ B ∈ edgeFormSpace L n k 0, leftSecondDeriv (plaquetteAction L n k)
      (trivialField L n k 0) B B = traceFinsumNorm (edgeCoboundary B) ^ 2 := hsq
  have hop := isOpenNhdOfOne_fieldSpace (k := k) hFin hL hn
  refine ⟨bottomData L n k, ?_⟩
  exact
    { analytic_energy := fun j hj => by
        obtain rfl := Nat.le_zero.1 hj
        exact ⟨_, hop, isAnalytic_plaquetteAction hHol hop.1 hnb⟩
      energy_nonneg := fun j hj => by
        obtain rfl := Nat.le_zero.1 hj
        exact eventuallyNearIdentity_of_forall hnn
      energy_bottom := eventuallyNearIdentity_of_forall fun _ _ => rfl
      analytic_prolong := fun i hi => absurd hi (Nat.not_lt_zero i)
      prolong_trivial := fun i hi => absurd hi (Nat.not_lt_zero i)
      prolong_section := fun i hi => absurd hi (Nat.not_lt_zero i)
      fibre_structure := fun i hi => absurd hi (Nat.not_lt_zero i)
      energy_gauge_invariant := fun j hj => by
        obtain rfl := Nat.le_zero.1 hj
        refine ⟨?_, eventuallyNearIdentity_of_forall fun W hW v hv _ => hgauge W hW v hv⟩
        filter_upwards [Filter.prod_mem_prod self_mem_nhdsWithin self_mem_nhdsWithin] with q hq
        exact hgauge q.2 hq.2 q.1 hq.1
      prolong_gauge_equivariant := fun i hi => absurd hi (Nat.not_lt_zero i)
      energy_symmetry_invariant := fun j hj => by
        obtain rfl := Nat.le_zero.1 hj
        exact eventuallyNearIdentity_of_forall fun W hW f hf => hiso W hW f hf.1 hf.2
      prolong_symmetry_equivariant := fun i hi => absurd hi (Nat.not_lt_zero i)
      energy_trivial := fun j hj => by
        obtain rfl := Nat.le_zero.1 hj
        exact h1
      gradient_trivial := fun j hj => by
        obtain rfl := Nat.le_zero.1 hj
        exact hgrad
      hessianAtOne_nonneg := fun j hj B hB => by
        obtain rfl := Nat.le_zero.1 hj
        show 0 ≤ leftSecondDeriv (plaquetteAction L n k) (trivialField L n k 0) B B
        rw [hsq' B hB]
        exact sq_nonneg _
      hessianAtOne_null_iff := fun j hj B hB => by
        obtain rfl := Nat.le_zero.1 hj
        exact hessian_null_iff_closed hsq' hB
      hessianAtOne_bottom := hsq'
      hessianAtOne_isLeast := fun i hi => absurd hi (Nat.not_lt_zero i)
      hessianAtOne_minimizer_iff := fun i hi => absurd hi (Nat.not_lt_zero i)
      prolongComp_section := fun j hj => by
        obtain rfl := Nat.le_zero.1 hj
        refine eventuallyNearIdentity_of_forall fun W hW => ⟨rfl, rfl, ?_⟩
        refine ⟨⟨leftGradient (fieldSpace L n k 0) (fun V => (plaquetteAction L n k V : ℂ)) W,
          leftGradient_mem hForms hL hn hW⟩, rfl, ?_⟩
        have e : leftDifferentialLinear (smoothingIter L n k 0)
            ((bottomData L n k).prolongComp 0 W) = LinearMap.id :=
          leftDifferentialLinear_smoothingIter_zero hExp hW
        rw [e]
        exact realTransposeMap_id hnb _
      prolongComp_lift := fun i hi => absurd hi (Nat.not_lt_zero i)
      prolongComp_critical := fun j hj => by
        obtain rfl := Nat.le_zero.1 hj
        refine ⟨_, hop, eventuallyNearIdentity_of_forall fun W hW => ⟨⟨hW, rfl⟩, fun I γ hγ hm h0 => ?_⟩⟩
        have hI : I ∈ 𝓝 (0 : ℝ) := hγ.1.1.mem_nhds hγ.1.2.2
        have hconst : (fun t => plaquetteAction L n k (γ t)) =ᶠ[𝓝 0]
            fun _ => plaquetteAction L n k W :=
          Filter.eventually_of_mem hI fun t ht => by
            have h2 : γ t = W := (hm ht).2
            show plaquetteAction L n k (γ t) = _
            rw [h2]
        rw [hconst.deriv_eq]
        simp }
end YangMills.Construction
end

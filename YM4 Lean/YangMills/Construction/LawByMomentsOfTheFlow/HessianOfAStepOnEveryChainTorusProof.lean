import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames
namespace MomentLaw
namespace TrivialHessian
open TorusFields WeightedResponses
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
theorem deriv_fderiv_smul_line (hf : ContDiffAt ℝ 2 f 0) (u v : E) :
    deriv (fun s : ℝ => fderiv ℝ f (s • u) v) 0 = fderiv ℝ (fderiv ℝ f) 0 u v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hline : HasDerivAt (fun s : ℝ => s • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have hF : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) ((0 : ℝ) • u) := by
    simpa using hd.hasFDerivAt
  have hcomp := hF.comp_hasDerivAt (0 : ℝ) hline
  have happ := hcomp.clm_apply (hasDerivAt_const (0 : ℝ) v)
  simpa using happ.deriv
theorem eventually_differentiableAt_smul (hf : ContDiffAt ℝ 2 f 0) (u : E) :
    ∀ᶠ s : ℝ in 𝓝 0, DifferentiableAt ℝ f (s • u) := by
  have hev : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℝ f x :=
    (hf.eventually (by simp)).mono fun x hx => hx.differentiableAt two_ne_zero
  have hc : Filter.Tendsto (fun s : ℝ => s • u) (𝓝 0) (𝓝 0) := by
    have : Continuous fun s : ℝ => s • u := by fun_prop
    simpa using this.tendsto 0
  exact hc.eventually hev
theorem deriv_deriv_two_param (hf : ContDiffAt ℝ 2 f 0) (u v : E) :
    deriv (fun s : ℝ => deriv (fun s' : ℝ => f (s • u + s' • v)) 0) 0 = fderiv ℝ (fderiv ℝ f) 0 u v := by
  have heq : (fun s : ℝ => deriv (fun s' : ℝ => f (s • u + s' • v)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℝ f (s • u) v := by
    filter_upwards [eventually_differentiableAt_smul hf u] with s hs
    have hline : HasDerivAt (fun s' : ℝ => s • u + s' • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (s • u)
    have hF : HasFDerivAt f (fderiv ℝ f (s • u)) (s • u + (0 : ℝ) • v) := by
      simpa using hs.hasFDerivAt
    exact (hF.comp_hasDerivAt (0 : ℝ) hline).deriv
  rw [heq.deriv_eq]
  exact deriv_fderiv_smul_line hf u v
theorem deriv_deriv_line (hf : ContDiffAt ℝ 2 f 0) (v : E) :
    deriv (deriv fun τ : ℝ => f (τ • v)) 0 = fderiv ℝ (fderiv ℝ f) 0 v v := by
  have heq : (deriv fun τ : ℝ => f (τ • v)) =ᶠ[𝓝 0] fun s => fderiv ℝ f (s • v) v := by
    filter_upwards [eventually_differentiableAt_smul hf v] with s hs
    have hline : HasDerivAt (fun τ : ℝ => τ • v) v s := by
      simpa using (hasDerivAt_id s).smul_const v
    exact (hs.hasFDerivAt.comp_hasDerivAt s hline).deriv
  rw [heq.deriv_eq]
  exact deriv_fderiv_smul_line hf v v
end Calculus
section Chart
variable (L u n : ℕ)
abbrev ChartLinks : Type := ↥(chordBonds (finiteCells (torusFrame L u n)))
def chartIndex : ChartLinks L u n ≃ Fin (Fintype.card (ChartLinks L u n)) := Fintype.equivFin _
def chartDirections (l : Fin (Fintype.card (ChartLinks L u n))) : ChartDirection (torusFrame L u n) :=
  Sum.inl (((chartIndex L u n).symm l).1.1, ((chartIndex L u n).symm l).1.2, unitGenerator)
open Classical in
def chartCoordinates (σ : Fin (Fintype.card (ChartLinks L u n)) → ℝ) :
    (torusFrame L u n).Site (torusFrame L u n).depth → Fin 4 → imaginaryQuaternions :=
  fun x i => (∑ c : ChartLinks L u n, if c.1 = (x, i) then σ (chartIndex L u n c) else 0) • unitGenerator
def chartBasis (b : ChartLinks L u n) : Fin (Fintype.card (ChartLinks L u n)) → ℝ :=
  Pi.single (chartIndex L u n b) 1
variable {L u n}
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem chartRestriction_uniform (a : ℝ) (σ : Fin (Fintype.card (ChartLinks L u n)) → ℝ) :
    chartRestriction a (fun _ _ => 0) (uniformField (torusFrame L u n) (torusFrame L u n).top)
        (chartDirections L u n) σ =
      chartedEnergy a (chartCoordinates L u n σ) (uniformField (torusFrame L u n) (torusFrame L u n).top) := by
  classical
  unfold chartRestriction
  have hbase : leftTranslate (fun y i => ∑ l, σ l • directionMove (chartDirections L u n l) y i)
      (uniformField (torusFrame L u n) (torusFrame L u n).top) =
        uniformField (torusFrame L u n) (torusFrame L u n).top := by
    funext y i
    simp [leftTranslate, directionMove, chartDirections, expUnit_zero]
  have hcoord : (fun x i => (0 : imaginaryQuaternions) +
      ∑ l, σ l • directionCoordinate (chartDirections L u n l) x i) = chartCoordinates L u n σ := by
    funext x i
    unfold chartCoordinates
    rw [zero_add, Finset.sum_smul, ← (chartIndex L u n).sum_comp]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [chartDirections, directionCoordinate, Equiv.symm_apply_apply]
    by_cases h : c.1 = (x, i)
    · have h' : c.1.1 = x ∧ c.1.2 = i := by simp [h]
      rw [if_pos h', if_pos h]
    · have h' : ¬ (c.1.1 = x ∧ c.1.2 = i) := fun hh => h (Prod.ext hh.1 hh.2)
      rw [if_neg h', if_neg h]
      simp
  rw [hbase, hcoord]
theorem pairCoordinates_eq (b b' : ChartLinks L u n) (s s' : ℝ) :
    pairCoordinates L u n b b' s s' =
      chartCoordinates L u n (s • chartBasis L u n b + s' • chartBasis L u n b') := by
  classical
  funext x i
  unfold pairCoordinates chartCoordinates
  rw [← add_smul]
  congr 1
  have h : ∀ c : ChartLinks L u n, (s • chartBasis L u n b + s' • chartBasis L u n b') (chartIndex L u n c) =
      (if c = b then s else 0) + (if c = b' then s' else 0) := by
    intro c
    simp [chartBasis, Pi.single_apply]
  simp only [h]
  have hs : ∀ (b₀ : ChartLinks L u n) (t : ℝ), (if (x, i) = b₀.1 then t else 0) =
      ∑ c : ChartLinks L u n, if c.1 = (x, i) then (if c = b₀ then t else 0) else 0 := by
    intro b₀ t
    rw [Finset.sum_eq_single b₀]
    · simp [eq_comm]
    · intro c _ hc
      simp [hc]
    · simp
  rw [hs b s, hs b' s', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp
theorem chartCoordinates_smul (τ : ℝ) (σ : Fin (Fintype.card (ChartLinks L u n)) → ℝ) :
    chartCoordinates L u n (τ • σ) =
      fun x i => (0 : imaginaryQuaternions) + τ • chartCoordinates L u n σ x i := by
  classical
  funext x i
  unfold chartCoordinates
  rw [zero_add, smul_smul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp
theorem chartCoordinates_mem (σ : Fin (Fintype.card (ChartLinks L u n)) → ℝ) (b : ChartLinks L u n) :
    chartCoordinates L u n σ b.1.1 b.1.2 = σ (chartIndex L u n b) • unitGenerator := by
  classical
  unfold chartCoordinates
  congr 1
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    rw [if_neg]
    intro h
    exact hc (Subtype.ext h)
  · simp
theorem chartCoordinates_not_mem (σ : Fin (Fintype.card (ChartLinks L u n)) → ℝ)
    (b : (torusFrame L u n).Site (torusFrame L u n).depth × Fin 4)
    (hb : b ∉ chordBonds (finiteCells (torusFrame L u n))) :
    chartCoordinates L u n σ b.1 b.2 = 0 := by
  classical
  unfold chartCoordinates
  have hzero : (∑ c : ChartLinks L u n, if c.1 = (b.1, b.2) then σ (chartIndex L u n c) else 0) = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]
    intro h
    apply hb
    have e : b = c.1 := Prod.ext (congrArg Prod.fst h).symm (congrArg Prod.snd h).symm
    rw [e]
    exact c.2
  rw [hzero, zero_smul]
theorem norm_unitGenerator : ‖(unitGenerator : imaginaryQuaternions)‖ = 1 := by
  have h : ‖((unitGenerator : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2 = 1 := by
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    simp [unitGenerator]
  have h0 : 0 ≤ ‖((unitGenerator : imaginaryQuaternions) : ℍ[ℝ])‖ := norm_nonneg _
  have : ‖((unitGenerator : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by nlinarith
  exact this
theorem chartedField_zero_uniform : chartedField (F := torusFrame L u n) (fun _ _ => 0)
    (uniformField (torusFrame L u n) (torusFrame L u n).top) =
      uniformField (torusFrame L u n) (torusFrame L u n).depth := by
  classical
  funext x i
  unfold chartedField uniformField
  split_ifs <;> simp [expUnit_zero]
theorem plaquetteDefect_uniform {j : ℕ} (p : (torusFrame L u n).Site j × Fin 4 × Fin 4) :
    plaquetteDefect (uniformField (torusFrame L u n) j) p = 0 := by
  simp [plaquetteDefect, plaquetteHolonomy, BlockAverages.pathHolonomy, BlockAverages.linkValue,
    uniformField]
end Chart
section Main
variable {a : ℝ} {L u n : ℕ}
theorem trivialHessian_posDef_of_admissible (c : ColdChainParameters) (hc : c.Admissible a L)
    (hρ : 0 < c.ρA) (h64 : 64 ≤ n)
    (hA : AnalyticAt ℝ (chartRestriction a (fun _ _ => 0)
      (uniformField (torusFrame L u n) (torusFrame L u n).top) (chartDirections L u n)) 0) :
    (trivialHessian a L u n).PosDef ∧ ∀ v : ChartLinks L u n → ℝ,
      c.lam * ∑ b, v b ^ 2 ≤ v ⬝ᵥ (trivialHessian a L u n).mulVec v := by
  classical
  have hf : ContDiffAt ℝ 2 (chartRestriction a (fun _ _ => 0)
      (uniformField (torusFrame L u n) (torusFrame L u n).top) (chartDirections L u n)) 0 :=
    hA.contDiffAt.of_le (by exact_mod_cast le_top)
  have hent : ∀ b b' : ChartLinks L u n, trivialHessian a L u n b b' =
      fderiv ℝ (fderiv ℝ (chartRestriction a (fun _ _ => 0)
        (uniformField (torusFrame L u n) (torusFrame L u n).top) (chartDirections L u n))) 0
        (chartBasis L u n b) (chartBasis L u n b') := by
    intro b b'
    rw [← deriv_deriv_two_param hf]
    unfold trivialHessian
    simp only [pairCoordinates_eq, chartRestriction_uniform]
  have hsym := hf.isSymmSndFDerivAt (by simp)
  have hlow : ∀ v : ChartLinks L u n → ℝ,
      c.lam * ∑ b, v b ^ 2 ≤ v ⬝ᵥ (trivialHessian a L u n).mulVec v := by
    intro v
    obtain ⟨σ, hσ⟩ : ∃ σ, σ = ∑ b : ChartLinks L u n, v b • chartBasis L u n b := ⟨_, rfl⟩
    have hσb : ∀ b : ChartLinks L u n, σ (chartIndex L u n b) = v b := by
      intro b
      rw [hσ, Finset.sum_apply, Finset.sum_eq_single b]
      · simp [chartBasis]
      · intro c _ hc
        simp [chartBasis, Pi.single_apply, hc.symm]
      · simp
    have hquad : v ⬝ᵥ (trivialHessian a L u n).mulVec v =
        fderiv ℝ (fderiv ℝ (chartRestriction a (fun _ _ => 0)
          (uniformField (torusFrame L u n) (torusFrame L u n).top) (chartDirections L u n))) 0 σ σ := by
      rw [hσ]
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      unfold dotProduct Matrix.mulVec
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 1
      unfold dotProduct
      refine Finset.sum_congr rfl fun b' _ => ?_
      show trivialHessian a L u n b b' * v b' = _
      rw [hent, hsym.eq]
      ring
    have hs := hc.positivity.2.2.2.1
    have hsmall : IsSmallCurvature c.σA (uniformField (torusFrame L u n) (torusFrame L u n).top) :=
      fun p _ => by
        rw [plaquetteDefect_uniform]
        exact hs
    have hhess := (hc.estimates (torusFrame L u n) c.σA _ ⟨rfl, n, h64, fun _ => rfl⟩ hs le_rfl
      hsmall).hessian
    have h := hhess (fun _ _ => 0) (chartCoordinates L u n σ) (fun _ _ => rfl)
      (fun b hb => chartCoordinates_not_mem σ b hb) (fun b _ => by simpa using hρ.le)
      (fun p _ => by
        rw [chartedField_zero_uniform, plaquetteDefect_uniform]
        exact hs)
    have e : (fun τ : ℝ => blockEnergy a (finiteCells (torusFrame L u n)) (torusFrame L u n).depth
        (chartedField (fun x i => (fun _ _ => (0 : imaginaryQuaternions)) x i + τ • chartCoordinates L u n σ x i)
          (uniformField (torusFrame L u n) (torusFrame L u n).top))
          (uniformField (torusFrame L u n) (torusFrame L u n).top)) =
        fun τ : ℝ => chartRestriction a (fun _ _ => 0)
          (uniformField (torusFrame L u n) (torusFrame L u n).top) (chartDirections L u n) (τ • σ) := by
      funext τ
      rw [chartRestriction_uniform, chartCoordinates_smul]
      rfl
    rw [e, deriv_deriv_line hf σ, ← hquad] at h
    have hsum : ∑ b ∈ chordBonds (finiteCells (torusFrame L u n)), ‖chartCoordinates L u n σ b.1 b.2‖ ^ 2 =
        ∑ b : ChartLinks L u n, v b ^ 2 := by
      rw [← Finset.sum_coe_sort (chordBonds (finiteCells (torusFrame L u n)))
        (fun b => ‖chartCoordinates L u n σ b.1 b.2‖ ^ 2)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [chartCoordinates_mem, hσb, norm_smul, norm_unitGenerator, mul_one, Real.norm_eq_abs, sq_abs]
    rw [hsum] at h
    exact h
  refine ⟨Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_, hlow⟩
  · refine Matrix.IsHermitian.ext fun b b' => ?_
    rw [star_trivial, hent, hent]
    exact hsym.eq _ _
  · intro v hv
    rw [star_trivial]
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hv
    have hpos : 0 < ∑ b : ChartLinks L u n, v b ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨b, Finset.mem_univ _, by
        have : v b ≠ 0 := hb
        positivity⟩
    exact (mul_pos hc.positivity.2.2.1 hpos).trans_le (hlow v)
end Main
end TrivialHessian
open TorusFields WeightedResponses
theorem trivialHessianPosDef (hK : ChartEnergyKernelBound) : trivialHessianPosDefStatement := by
  intro a L c ha hodd hL hc hρ u n _ h64
  obtain ⟨Ck, _, hCk⟩ := hK a L c ha hodd hL hc
  refine TrivialHessian.trivialHessian_posDef_of_admissible c hc hρ h64 ?_
  refine (hCk (torusFrame L u n) (fun _ _ => 0) _ ⟨rfl, n, h64, fun _ => rfl⟩
    ⟨fun b _ => ?_, fun p _ => ?_⟩ _ (TrivialHessian.chartDirections L u n)).1
  · have : (0 : ℝ) ≤ 1 / (64 * (L : ℝ)) := by positivity
    simpa using this
  · rw [TrivialHessian.chartedField_zero_uniform, TrivialHessian.plaquetteDefect_uniform]
    exact hc.positivity.2.2.2.1
end MomentLaw
end YangMills.Construction
end

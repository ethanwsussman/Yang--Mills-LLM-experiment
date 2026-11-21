import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorusProof
import YangMills.Construction.ResponseInTheExpansion.TheHessianOfAStepIsDefinite
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames WeightedResponses TorusFields RenormalizationStepParameters StepSettings
namespace ResponseInTheExpansion
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
private theorem deriv_deriv_two_param (hf : ContDiffAt ℝ 2 f 0) (u v : E) :
    deriv (fun s : ℝ => deriv (fun s' : ℝ => f (s • u + s' • v)) 0) 0 = fderiv ℝ (fderiv ℝ f) 0 u v := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.deriv_deriv_two_param <;> assumption
private theorem deriv_deriv_line (hf : ContDiffAt ℝ 2 f 0) (v : E) :
    deriv (deriv fun τ : ℝ => f (τ • v)) 0 = fderiv ℝ (fderiv ℝ f) 0 v v := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.deriv_deriv_line <;> assumption
end Calculus
section Chart
variable (L u n : ℕ)
private abbrev ChartBond : Type := ↥(chordBonds (finiteCells (torusFrame L u n)))
private def chartEnum : ChartBond L u n ≃ Fin (Fintype.card (ChartBond L u n)) := Fintype.equivFin _
private def chartDirections (l : Fin (Fintype.card (ChartBond L u n))) : ChartDirection (torusFrame L u n) :=
  Sum.inl (((chartEnum L u n).symm l).1.1, ((chartEnum L u n).symm l).1.2, unitGenerator)
open Classical in
private def chartCoords (σ : Fin (Fintype.card (ChartBond L u n)) → ℝ) :
    (torusFrame L u n).Site (torusFrame L u n).depth → Fin 4 → imaginaryQuaternions :=
  fun x i => (∑ c : ChartBond L u n, if c.1 = (x, i) then σ (chartEnum L u n c) else 0) • unitGenerator
private def chartBasis (b : ChartBond L u n) : Fin (Fintype.card (ChartBond L u n)) → ℝ :=
  Pi.single (chartEnum L u n b) 1
variable {L u n}
private theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem chartRestriction_eq (a : ℝ) (σ : Fin (Fintype.card (ChartBond L u n)) → ℝ) :
    chartRestriction a (fun _ _ => 0) (uniformField (torusFrame L u n) (torusFrame L u n).top)
        (chartDirections L u n) σ =
      chartedEnergy a (chartCoords L u n σ) (uniformField (torusFrame L u n) (torusFrame L u n).top) := by
  classical
  unfold chartRestriction
  have hbase : leftTranslate (fun y i => ∑ l, σ l • directionMove (chartDirections L u n l) y i)
      (uniformField (torusFrame L u n) (torusFrame L u n).top) =
        uniformField (torusFrame L u n) (torusFrame L u n).top := by
    funext y i
    simp [leftTranslate, directionMove, chartDirections, expUnit_zero]
  have hcoord : (fun x i => (0 : imaginaryQuaternions) +
      ∑ l, σ l • directionCoordinate (chartDirections L u n l) x i) = chartCoords L u n σ := by
    funext x i
    unfold chartCoords
    rw [zero_add, Finset.sum_smul, ← (chartEnum L u n).sum_comp]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [chartDirections, directionCoordinate, Equiv.symm_apply_apply]
    by_cases h : c.1 = (x, i)
    · have h' : c.1.1 = x ∧ c.1.2 = i := by simp [h]
      rw [if_pos h', if_pos h]
    · have h' : ¬ (c.1.1 = x ∧ c.1.2 = i) := fun hh => h (Prod.ext hh.1 hh.2)
      rw [if_neg h', if_neg h]
      simp
  rw [hbase, hcoord]
private theorem pairCoordinates_eq (b b' : ChartBond L u n) (s s' : ℝ) :
    pairCoordinates L u n b b' s s' =
      chartCoords L u n (s • chartBasis L u n b + s' • chartBasis L u n b') := by
  classical
  funext x i
  unfold pairCoordinates chartCoords
  rw [← add_smul]
  congr 1
  have hval : ∀ c : ChartBond L u n,
      (s • chartBasis L u n b + s' • chartBasis L u n b') (chartEnum L u n c) =
        (if c = b then s else 0) + (if c = b' then s' else 0) := by
    intro c
    simp [chartBasis, Pi.single_apply]
  simp only [hval]
  have hsingle : ∀ (b₀ : ChartBond L u n) (t : ℝ), (if (x, i) = b₀.1 then t else 0) =
      ∑ c : ChartBond L u n, if c.1 = (x, i) then (if c = b₀ then t else 0) else 0 := by
    intro b₀ t
    rw [Finset.sum_eq_single b₀]
    · simp [eq_comm]
    · intro c _ hc
      simp [hc]
    · simp
  rw [hsingle b s, hsingle b' s', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp
private theorem chartCoords_smul (τ : ℝ) (σ : Fin (Fintype.card (ChartBond L u n)) → ℝ) :
    chartCoords L u n (τ • σ) = fun x i => (0 : imaginaryQuaternions) + τ • chartCoords L u n σ x i := by
  classical
  funext x i
  unfold chartCoords
  rw [zero_add, smul_smul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp
private theorem chartCoords_mem (σ : Fin (Fintype.card (ChartBond L u n)) → ℝ) (b : ChartBond L u n) :
    chartCoords L u n σ b.1.1 b.1.2 = σ (chartEnum L u n b) • unitGenerator := by
  classical
  unfold chartCoords
  congr 1
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    rw [if_neg]
    intro h
    exact hc (Subtype.ext h)
  · simp
private theorem chartCoords_not_mem (σ : Fin (Fintype.card (ChartBond L u n)) → ℝ)
    (b : (torusFrame L u n).Site (torusFrame L u n).depth × Fin 4)
    (hb : b ∉ chordBonds (finiteCells (torusFrame L u n))) :
    chartCoords L u n σ b.1 b.2 = 0 := by
  classical
  unfold chartCoords
  have hzero : (∑ c : ChartBond L u n, if c.1 = (b.1, b.2) then σ (chartEnum L u n c) else 0) = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]
    intro h
    apply hb
    have e : b = c.1 := Prod.ext (congrArg Prod.fst h).symm (congrArg Prod.snd h).symm
    rw [e]
    exact c.2
  rw [hzero, zero_smul]
private theorem norm_unitGenerator : ‖(unitGenerator : imaginaryQuaternions)‖ = 1 := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.norm_unitGenerator <;> assumption
private theorem chartedField_zero_uniform : chartedField (F := torusFrame L u n) (fun _ _ => 0)
    (uniformField (torusFrame L u n) (torusFrame L u n).top) =
      uniformField (torusFrame L u n) (torusFrame L u n).depth := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.chartedField_zero_uniform <;> assumption
private theorem plaquetteDefect_uniform {j : ℕ} (p : (torusFrame L u n).Site j × Fin 4 × Fin 4) :
    plaquetteDefect (uniformField (torusFrame L u n) j) p = 0 := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.plaquetteDefect_uniform <;> assumption
end Chart
section Main
variable {a : ℝ} {L u n : ℕ}
private theorem trivialHessian_posDef_of_admissible (c : ColdChainParameters) (hc : c.Admissible a L)
    (hρ : 0 < c.ρA) (h64 : 64 ≤ n)
    (hA : AnalyticAt ℝ (chartRestriction a (fun _ _ => 0)
      (uniformField (torusFrame L u n) (torusFrame L u n).top) (chartDirections L u n)) 0) :
    (trivialHessian a L u n).PosDef := by
  classical
  have hf : ContDiffAt ℝ 2 (chartRestriction a (fun _ _ => 0)
      (uniformField (torusFrame L u n) (torusFrame L u n).top) (chartDirections L u n)) 0 :=
    hA.contDiffAt.of_le (by exact_mod_cast le_top)
  have hent : ∀ b b' : ChartBond L u n, trivialHessian a L u n b b' =
      fderiv ℝ (fderiv ℝ (chartRestriction a (fun _ _ => 0)
        (uniformField (torusFrame L u n) (torusFrame L u n).top) (chartDirections L u n))) 0
        (chartBasis L u n b) (chartBasis L u n b') := by
    intro b b'
    rw [← deriv_deriv_two_param hf]
    unfold trivialHessian
    simp only [pairCoordinates_eq, chartRestriction_eq]
  have hsym := hf.isSymmSndFDerivAt (by simp)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext fun b b' => ?_
    rw [star_trivial, hent, hent]
    exact hsym.eq _ _
  · intro v hv
    rw [star_trivial]
    obtain ⟨σ, hσ⟩ : ∃ σ, σ = ∑ b : ChartBond L u n, v b • chartBasis L u n b := ⟨_, rfl⟩
    have hσb : ∀ b : ChartBond L u n, σ (chartEnum L u n b) = v b := by
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
    have hlam := hc.positivity.2.2.1
    have hsmall : IsSmallCurvature c.σA (uniformField (torusFrame L u n) (torusFrame L u n).top) :=
      fun p _ => by
        rw [plaquetteDefect_uniform]
        exact hs
    have hhess := (hc.estimates (torusFrame L u n) c.σA _ ⟨rfl, n, h64, fun _ => rfl⟩ hs le_rfl
      hsmall).hessian
    have h := hhess (fun _ _ => 0) (chartCoords L u n σ) (fun _ _ => rfl)
      (fun b hb => chartCoords_not_mem σ b hb) (fun b _ => by simpa using hρ.le)
      (fun p _ => by
        rw [chartedField_zero_uniform, plaquetteDefect_uniform]
        exact hs)
    have e : (fun τ : ℝ => blockEnergy a (finiteCells (torusFrame L u n)) (torusFrame L u n).depth
        (chartedField (fun x i => (fun _ _ => (0 : imaginaryQuaternions)) x i + τ • chartCoords L u n σ x i)
          (uniformField (torusFrame L u n) (torusFrame L u n).top))
        (uniformField (torusFrame L u n) (torusFrame L u n).top)) =
        fun τ : ℝ => chartRestriction a (fun _ _ => 0)
          (uniformField (torusFrame L u n) (torusFrame L u n).top) (chartDirections L u n) (τ • σ) := by
      funext τ
      rw [chartRestriction_eq, chartCoords_smul]
      rfl
    rw [e, deriv_deriv_line hf σ, ← hquad] at h
    have hsum : ∑ b ∈ chordBonds (finiteCells (torusFrame L u n)), ‖chartCoords L u n σ b.1 b.2‖ ^ 2 =
        ∑ b : ChartBond L u n, v b ^ 2 := by
      rw [← Finset.sum_coe_sort (chordBonds (finiteCells (torusFrame L u n)))
        (fun b => ‖chartCoords L u n σ b.1 b.2‖ ^ 2)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [chartCoords_mem, hσb, norm_smul, norm_unitGenerator, mul_one, Real.norm_eq_abs, sq_abs]
    rw [hsum] at h
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hv
    have hpos : 0 < ∑ b : ChartBond L u n, v b ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨b, Finset.mem_univ _, by
        have : v b ≠ 0 := hb
        positivity⟩
    exact (mul_pos hlam hpos).trans_le h
end Main
theorem stepHessian_posDef (hK : ChartEnergyKernelBound) : stepHessianPosDefStatement := by
  intro a ha
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L hodd _ T hTa hTL hD hCS _ _ _ => ⟨0, fun y _ _ _ => ?_⟩⟩
  obtain ⟨c, _, hT, _⟩ := hCS
  have hc : c.Admissible T.coupling T.side := hT.2.2.2.2.2.2.2
  have hρ : 0 < c.ρA := by
    rw [hT.2.2.1]
    exact hD.chain.2.2.2.1
  have hodd' : Odd T.side := hD.L_odd
  obtain ⟨Ck, _, hCk⟩ := hK T.coupling T.side c hD.a_ge hodd' hD.L_ge hc
  intro u n _ hn
  have h64 : 64 ≤ n := by
    have := hD.n₀_ge
    omega
  show (trivialHessian T.coupling T.side u n).PosDef
  refine trivialHessian_posDef_of_admissible c hc hρ h64 ?_
  refine (hCk (torusFrame T.side u n) (fun _ _ => 0) _ ⟨rfl, n, h64, fun _ => rfl⟩
    ⟨fun b _ => ?_, fun p _ => ?_⟩ _ (chartDirections T.side u n)).1
  · have : (0 : ℝ) ≤ 1 / (64 * (T.side : ℝ)) := by positivity
    simpa using this
  · rw [chartedField_zero_uniform, plaquetteDefect_uniform]
    exact hc.positivity.2.2.2.1
end ResponseInTheExpansion
end YangMills.Construction
end

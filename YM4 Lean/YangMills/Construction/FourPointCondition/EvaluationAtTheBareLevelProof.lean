import YangMills.Construction.FreeEnergiesOfTheFlow.MeansGivenAStateReadTheCasesProof
import YangMills.Construction.ResponseInTheExpansion.RemainderOfTheResponseReturnsProof
import YangMills.Construction.FourPointCondition.BareObservableIsAQuadraticForm
import YangMills.Construction.FourPointCondition.EvaluationAtTheBareLevel
import YangMills.Construction.FourPointCondition.LawsAtALevelOfTheWindowProof
import YangMills.Construction.FourPointCondition.RiemannSumOfTheBareTraces
import YangMills.Construction.LawInAState.ConcentrationInOneBoxProof
import YangMills.Construction.LawOnABoxOfTheFlow.DrawsBelowATopHaveTheirLaw
import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheCurvatureOfALevel
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheLocalChain
import YangMills.Construction.ResponseInTheExpansion.TheHessianOfAStepIsDefinite
import YangMills.Construction.ResponseInTheExpansion.TheLocalEventIsLikely
import YangMills.Construction.ResponseInTheExpansion.TheMaxwellCovarianceAtLongDistance
import YangMills.Construction.ResponseInTheExpansion.TheWeightsOfATupleAreLocal
import YangMills.Construction.ResponseInTheExpansion.TheWindowHasATower
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames PeriodicLattice TorusFields TorusLumps RenormalizationStepParameters StepReturn
  WeightedResponses ResponseInTheExpansion LinearResponse
namespace FourPointCondition
section HoldsOnFamilies
private theorem holdsOnParameters_of_holdsAtAdmissible {P : ParameterAssignment → ℝ → Prop}
    (h : HoldsAtAdmissibleParameters P) : HoldsOnParameterFamilies P := by apply _root_.YangMills.SharedProofs.p23606 <;> assumption
private theorem holdsOnParams_and {P Q : ParameterAssignment → ℝ → Prop} (hP : HoldsOnParameterFamilies P)
    (hQ : HoldsOnParameterFamilies Q) : HoldsOnParameterFamilies fun Tb y => P Tb y ∧ Q Tb y := by apply _root_.YangMills.SharedProofs.p24215 <;> assumption
end HoldsOnFamilies
section Flow
private theorem abs_couplingFlow_succ_sub_le {ℓ : TorusLumps.StepParameters} (hR : ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) (t : ℕ)
    (h : ∀ j ≤ t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) :
    |(couplingFlow ℓ β (t + 1)).1 - (couplingFlow ℓ β t).1| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p4489 <;> assumption
private theorem couplingFlow_ge_of_bound {ℓ : TorusLumps.StepParameters} (hR : ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) (J : ℕ)
    (hJ : ℓ.y₁ ≤ β - 2 * |ℓ.B| * J) : ∀ j ≤ J, ℓ.y₁ ≤ (couplingFlow ℓ β j).1 := by
  have key : ∀ j, j ≤ J → ∀ i ≤ j, β - 2 * |ℓ.B| * i ≤ (couplingFlow ℓ β i).1 := by
    intro j
    induction j with
    | zero =>
      intro _ i hi
      have : i = 0 := by omega
      subst this
      simp [couplingFlow]
    | succ j ih =>
      intro hj i hi
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact ih (by omega) i (by omega)
      · have e : i = j + 1 := by omega
        subst e
        have hup : ∀ i ≤ j, ℓ.y₁ ≤ (couplingFlow ℓ β i).1 := by
          intro i hi
          refine hJ.trans (le_trans ?_ (ih (by omega) i hi))
          have : (i : ℝ) ≤ J := by exact_mod_cast (by omega : i ≤ J)
          have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * |ℓ.B|)
          linarith
        have h1 := abs_couplingFlow_succ_sub_le hR h0 j hup
        have h2 := (abs_le.1 h1).1
        have h3 := ih (by omega) j le_rfl
        have h4 := le_abs_self ℓ.B
        push_cast
        nlinarith
  intro j hj
  refine hJ.trans (le_trans ?_ (key j hj j le_rfl))
  have : (j : ℝ) ≤ J := by exact_mod_cast hj
  have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * |ℓ.B|)
  linarith
end Flow
section MeasurableRepresentative
private theorem imaginaryComponent_toImaginary (v : EuclideanSpace ℝ (Fin 3)) (e : Fin 3) :
    imaginaryComponent e (toImaginary v) = v e := by
  fin_cases e <;> rfl
private def clampSym (C t : ℝ) : ℝ := max (-C) (min C t)
private theorem abs_clampSym_le {C : ℝ} (hC : 0 ≤ C) (t : ℝ) : |clampSym C t| ≤ C := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.abs_clamp_le <;> assumption
private theorem clampSym_of_abs_le {C t : ℝ} (h : |t| ≤ C) : clampSym C t = t := by apply _root_.YangMills.DeltaSharedProofs.p15858 <;> assumption
private theorem exists_measurable_bounded_representative {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {I : Type}
    [Finite I] (raw : I → Fin 3 → Ω → ℝ) (A : Set Ω) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hm : ∀ a e, AEStronglyMeasurable (A.indicator (raw a e)) μ)
    (hb : ∀ a e, ∀ᵐ ω ∂μ, ω ∈ A → |raw a e ω| ≤ Cb) :
    ∃ G : Ω → I → imaginaryQuaternions, (∀ a e, Measurable fun ω => imaginaryComponent e (G ω a)) ∧
      (∀ ω a e, |imaginaryComponent e (G ω a)| ≤ Cb) ∧
      ∀ᵐ ω ∂μ, ω ∈ A → ∀ a e, imaginaryComponent e (G ω a) = raw a e ω := by
  refine ⟨fun ω a => toImaginary (WithLp.toLp 2 fun e => clampSym Cb ((hm a e).mk _ ω)), ?_, ?_, ?_⟩
  · intro a e
    simp only [imaginaryComponent_toImaginary]
    have h1 : Measurable ((hm a e).mk _) := (hm a e).stronglyMeasurable_mk.measurable
    exact (measurable_const.max (measurable_const.min h1))
  · intro ω a e
    simp only [imaginaryComponent_toImaginary]
    exact abs_clampSym_le hCb _
  · have h1 : ∀ᵐ ω ∂μ, ∀ a e, A.indicator (raw a e) ω = (hm a e).mk _ ω :=
      ae_all_iff.2 fun a => ae_all_iff.2 fun e => (hm a e).ae_eq_mk
    have h2 : ∀ᵐ ω ∂μ, ∀ a e, ω ∈ A → |raw a e ω| ≤ Cb := ae_all_iff.2 fun a => ae_all_iff.2 fun e => hb a e
    filter_upwards [h1, h2] with ω e1 e2 hω a e
    simp only [imaginaryComponent_toImaginary]
    have e3 : (hm a e).mk _ ω = raw a e ω := by
      rw [← e1 a e, Set.indicator_of_mem hω]
    show clampSym Cb ((hm a e).mk _ ω) = _
    rw [e3]
    exact clampSym_of_abs_le (e2 a e hω)
end MeasurableRepresentative
section Cycles
variable {I : Type} [Fintype I]
private theorem sum_fin_succ_fun {n : ℕ} (F : (Fin (n + 1) → I) → ℝ) :
    ∑ r, F r = ∑ a, ∑ r : Fin n → I, F (Fin.cons a r) := by
  rw [← Fintype.sum_prod_type']
  exact (Equiv.sum_comp (Fin.consEquiv (fun _ => I)) F).symm
private theorem finRotate_two_vals : finRotate 2 0 = 1 ∧ finRotate 2 1 = 0 := by decide
private theorem finRotate_four_vals :
    finRotate 4 0 = 1 ∧ finRotate 4 1 = 2 ∧ finRotate 4 2 = 3 ∧ finRotate 4 3 = 0 := by decide
private theorem trace_prod_ofFn_two [DecidableEq I] (M : Fin 2 → Matrix I I ℝ) :
    Matrix.trace (List.ofFn M).prod = ∑ r : Fin 2 → I, ∏ i, M i (r i) (r (finRotate 2 i)) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rw [sum_fin_succ_fun]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_fin_succ_fun, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_unique, Fin.prod_univ_two, finRotate_two_vals.1, finRotate_two_vals.2]
  rfl
private theorem trace_prod_ofFn_four [DecidableEq I] (M : Fin 4 → Matrix I I ℝ) :
    Matrix.trace (List.ofFn M).prod = ∑ r : Fin 4 → I, ∏ i, M i (r i) (r (finRotate 4 i)) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rw [sum_fin_succ_fun]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_fin_succ_fun, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum_fin_succ_fun, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum_fin_succ_fun, Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fintype.sum_unique, Fin.prod_univ_four, finRotate_four_vals.1, finRotate_four_vals.2.1,
    finRotate_four_vals.2.2.1, finRotate_four_vals.2.2.2]
  show M 0 a b * (M 1 b c * (M 2 c d * M 3 d a)) = M 0 a b * M 1 b c * M 2 c d * M 3 d a
  ring
private theorem trace_prod_ofFn_cycle [DecidableEq I] {q : ℕ} (hq : q = 1 ∨ q = 3) (M : Fin (q + 1) → Matrix I I ℝ) :
    Matrix.trace (List.ofFn M).prod = ∑ r : Fin (q + 1) → I, ∏ i, M i (r i) (r (finRotate (q + 1) i)) := by
  rcases hq with rfl | rfl
  · exact trace_prod_ofFn_two M
  · exact trace_prod_ofFn_four M
private theorem cyclicTraceSum_diagonal {n : ℕ} [NeZero n] {q : ℕ} (hq : q = 1 ∨ q = 3)
    (h : Fin (q + 1) → PlaquetteWeight n) (Tt : TorusPlaquette n → TorusPlaquette n → ℝ)
    (S : Finset (TorusPlaquette n)) (hS : S ⊆ plaquettesIn Finset.univ)
    (hz : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), p ∉ S → ∀ i, h i p = 0) :
    cyclicTraceSum (fun i => Matrix.diagonal fun a : S => h i a.1) (Matrix.of fun a b : S => Tt a.1 b.1) =
      3 / 2 * kernelCycleSum h Tt := by
  classical
  unfold cyclicTraceSum kernelCycleSum
  congr 1
  refine Finset.sum_congr (by ext; simp) fun s _ => ?_
  unfold kernelCycleTrace
  rw [@trace_prod_ofFn_cycle _ _ (fun a b => Classical.propDecidable (a = b)) q hq]
  have e1 : ∀ (i : Fin (q + 1)) (a b : S),
      (Matrix.diagonal (fun a : S => h (s i) a.1) * Matrix.of fun a b : S => Tt a.1 b.1) a b =
        h (s i) a.1 * Tt a.1 b.1 := by
    intro i a b
    rw [Matrix.diagonal_mul]
    rfl
  simp only [e1]
  have hsub : Fintype.piFinset (fun _ : Fin (q + 1) => S) ⊆
      Fintype.piFinset (fun _ : Fin (q + 1) => plaquettesIn (Finset.univ : Finset (TorusSite n))) :=
    fun p hp => Fintype.mem_piFinset.2 fun i => hS (Fintype.mem_piFinset.1 hp i)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_bij (fun r _ j => (r (s.symm j)).1) ?_ ?_ ?_ ?_
    · intro r _
      exact Fintype.mem_piFinset.2 fun i => (r _).2
    · intro r _ r' _ hr
      funext i
      have := congrFun hr (s i)
      simp only [Equiv.symm_apply_apply] at this
      exact Subtype.ext this
    · intro p hp
      refine ⟨fun i => ⟨p (s i), Fintype.mem_piFinset.1 hp _⟩, Finset.mem_univ _, ?_⟩
      funext j
      simp
    · intro r _
      rw [Finset.prod_mul_distrib]
      congr 1
      · have := Equiv.prod_comp s (fun j => h j (r (s.symm j)).1)
        simpa using this
      · simp
  · intro p hp hnot
    obtain ⟨j, hj⟩ : ∃ j, p j ∉ S := by
      by_contra hc
      push Not at hc
      exact hnot (Fintype.mem_piFinset.2 hc)
    have h0 := hz (p j) (Fintype.mem_piFinset.1 hp j) hj j
    rw [Finset.prod_eq_zero (Finset.mem_univ j) h0, zero_mul]
end Cycles
section Counting
variable {n : ℕ} [NeZero n]
private theorem card_supBall_le (o : TorusSite n) (t : ℝ) (r : ℕ) (h : t ≤ r) :
    (supBall o t).card ≤ (2 * r + 1) ^ 4 := by
  classical
  set F : TorusSite n → Fin 4 → ℤ := fun z i => (z i - o i).valMinAbs with hF
  have hsub : (supBall o t).image F ⊆ Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(r : ℤ)) r := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hw
    have hz' : (supDist z o : ℝ) ≤ t := (Finset.mem_filter.1 hz).2
    have hzr : supDist z o ≤ r := by exact_mod_cast hz'.trans h
    refine Fintype.mem_piFinset.2 fun i => ?_
    have hi : ((z i - o i).valMinAbs).natAbs ≤ supDist z o :=
      Finset.le_sup (f := fun i => ((z i - o i).valMinAbs).natAbs) (Finset.mem_univ i)
    have hir := hi.trans hzr
    rw [Finset.mem_Icc]
    simp only [hF]
    omega
  have hinj : Set.InjOn F (supBall o t : Set (TorusSite n)) := by
    intro z _ z' _ hzz
    funext i
    have h1 := congrFun hzz i
    have h2 : z i - o i = z' i - o i := by
      have e1 := ZMod.coe_valMinAbs (z i - o i)
      have e2 := ZMod.coe_valMinAbs (z' i - o i)
      simp only [hF] at h1
      rw [← e1, ← e2, h1]
    exact sub_left_injective h2
  calc (supBall o t).card = ((supBall o t).image F).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(r : ℤ)) r).card := Finset.card_le_card hsub
    _ = (2 * r + 1) ^ 4 := by
      rw [Fintype.card_piFinset]
      simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have : ((r : ℤ) + 1 - -(r : ℤ)).toNat = 2 * r + 1 := by omega
      rw [this]
abbrev _root_.YangMills.SharedProofs.p104098 := @card_supBall_le
private def ballPlaquettes (o : TorusSite n) (nn : ℝ) : Finset (TorusPlaquette n) :=
  open Classical in (plaquettesIn Finset.univ).filter fun p => p.1 ∈ supBall o (19 * nn)
private theorem card_ballPlaquettes_le (o : TorusSite n) {nn : ℝ} (hn : 1 ≤ nn) :
    ((ballPlaquettes o nn).card : ℝ) ≤ 16 * 41 ^ 4 * nn ^ 4 := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = ⌈19 * nn⌉₊ := ⟨_, rfl⟩
  have hr1 : 19 * nn ≤ r := hr ▸ Nat.le_ceil _
  have hr2 : (r : ℝ) ≤ 19 * nn + 1 := by
    rw [hr]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hb := card_supBall_le o (19 * nn) r hr1
  have hsub : ballPlaquettes o nn ⊆
      supBall o (19 * nn) ×ˢ ((Finset.univ : Finset (Fin 4)) ×ˢ (Finset.univ : Finset (Fin 4))) := by
    intro p hp
    have h1 := (Finset.mem_filter.1 hp).2
    simp [h1]
  have hc : (ballPlaquettes o nn).card ≤ 16 * (2 * r + 1) ^ 4 := by
    calc _ ≤ _ := Finset.card_le_card hsub
      _ = (supBall o (19 * nn)).card * 16 := by
        simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      _ ≤ (2 * r + 1) ^ 4 * 16 := Nat.mul_le_mul_right _ hb
      _ = _ := by ring
  have h3 : (2 * (r : ℝ) + 1) ≤ 41 * nn := by linarith
  calc ((ballPlaquettes o nn).card : ℝ) ≤ ((16 * (2 * r + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast hc
    _ = 16 * (2 * (r : ℝ) + 1) ^ 4 := by push_cast; ring
    _ ≤ 16 * (41 * nn) ^ 4 := by
      have := pow_le_pow_left₀ (by positivity) h3 4
      linarith
    _ = _ := by ring
omit [NeZero n] in
private theorem abs_plaquetteEnergyOf_le (W : TorusField n) (p : TorusPlaquette n) : |plaquetteEnergyOf W p| ≤ 2 := by
  have h0 : 0 ≤ plaquetteEnergyOf W p := plaquetteEnergy_nonneg _ _ _ _
  rw [abs_of_nonneg h0]
  unfold plaquetteEnergyOf _root_.YangMills.Construction.TorusFields.plaquetteEnergy
  set q : UnitQuaternion := holonomy W p.1 p.2.1 p.2.2
  have h := normSq_unitQuaternion q
  rw [Quaternion.normSq_def'] at h
  have h2 : ((q : Quaternion ℝ).re) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg ((q : Quaternion ℝ).imI), sq_nonneg ((q : Quaternion ℝ).imJ),
      sq_nonneg ((q : Quaternion ℝ).imK)]
  have h3 := abs_le.mp ((sq_le_one_iff_abs_le_one _).mp h2)
  linarith [h3.1]
private theorem abs_weight_le_of_weightSup {h : PlaquetteWeight n} (hs : weightSup h ≤ 1) {p : TorusPlaquette n}
    (hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n))) : |h p| ≤ 1 := by
  have ho : p.2.1 < p.2.2 := (Finset.mem_filter.1 hp).2.1
  have hb : BddAbove (Set.range fun p : OrientedPlaquette n => |h p.1|) := (Set.finite_range _).bddAbove
  exact (le_ciSup hb (⟨p, ho⟩ : OrientedPlaquette n)).trans hs
private theorem sum_abs_weight_ballPlaquettes_le {h : PlaquetteWeight n} (hs : weightSup h ≤ 1) (o : TorusSite n)
    {nn : ℝ} (hn : 1 ≤ nn) : ∑ a : ballPlaquettes o nn, |h a.1| ≤ 16 * 41 ^ 4 * nn ^ 4 := by
  have h1 : ∀ a : ballPlaquettes o nn, |h a.1| ≤ 1 := fun a =>
    abs_weight_le_of_weightSup hs (Finset.mem_filter.1 a.2).1
  calc _ ≤ ∑ _a : ballPlaquettes o nn, (1 : ℝ) := Finset.sum_le_sum fun a _ => h1 a
    _ = ((ballPlaquettes o nn).card : ℝ) := by simp
    _ ≤ _ := card_ballPlaquettes_le o hn
private theorem abs_curvatureObservable_le {h : PlaquetteWeight n} (hs : weightSup h ≤ 1) (o : TorusSite n)
    {nn : ℝ} (hn : 1 ≤ nn)
    (hz : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), p ∉ ballPlaquettes o nn → h p = 0)
    (W : TorusField n) : |curvatureObservable h W| ≤ 32 * 41 ^ 4 * nn ^ 4 := by
  have hsub : ballPlaquettes o nn ⊆ plaquettesIn (Finset.univ : Finset (TorusSite n)) := by
    classical
    exact Finset.filter_subset _ _
  have e : curvatureObservable h W = ∑ p ∈ ballPlaquettes o nn, h p * plaquetteEnergyOf W p := by
    unfold curvatureObservable
    refine (Finset.sum_subset hsub fun p hp hq => ?_).symm
    rw [hz p hp hq, zero_mul]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h2 : ∀ p ∈ ballPlaquettes o nn, |h p * plaquetteEnergyOf W p| ≤ 2 := by
    intro p hp
    rw [abs_mul]
    have h3 := abs_weight_le_of_weightSup hs (hsub hp)
    have h4 := abs_plaquetteEnergyOf_le W p
    nlinarith [abs_nonneg (h p), abs_nonneg (plaquetteEnergyOf W p)]
  calc _ ≤ ∑ _p ∈ ballPlaquettes o nn, (2 : ℝ) := Finset.sum_le_sum h2
    _ = ((ballPlaquettes o nn).card : ℝ) * 2 := by simp
    _ ≤ (16 * 41 ^ 4 * nn ^ 4) * 2 := mul_le_mul_of_nonneg_right (card_ballPlaquettes_le o hn) (by norm_num)
    _ = _ := by ring
end Counting
section Symmetry
variable (a ρA : ℝ) (L : ℕ) [NeZero L]
private theorem stepCovariance_comm (u n : ℕ) [NeZero n] (hP : (trivialHessian a L u n).PosDef)
    (h h' : TorusBond (n * L) → ℝ) :
    stepCovariance a L u n h h' = stepCovariance a L u n h' h := by
  classical
  unfold stepCovariance
  have hs : Matrix.transpose (trivialHessian a L u n)⁻¹ = (trivialHessian a L u n)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv]
    have := hP.isHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    rw [this]
  dsimp only
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, dotProduct_comm]
private theorem accumulatedCovariance_comm (n₀ k : ℕ)
    (hP : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → (trivialHessian a L u n).PosDef) :
    ∀ (d n : ℕ) [NeZero n], n₀ ≤ n → ∀ h h' : TorusBond (fineSide L d n) → ℝ,
      accumulatedCovariance a ρA L k d n h h' = accumulatedCovariance a ρA L k d n h' h
  | 0, _, _, _, _, _ => rfl
  | d + 1, n, _, hn, h, h' => by
    have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    have hnL : n₀ ≤ n * L := hn.trans (Nat.le_mul_of_pos_right n hL)
    show accumulatedCovariance a ρA L k d (n * L) h h' + _ = accumulatedCovariance a ρA L k d (n * L) h' h + _
    rw [accumulatedCovariance_comm n₀ k hP d (n * L) hnL h h', stepCovariance_comm a L (k + d) n (hP (k + d) n hn)]
end Symmetry
section Forms
private theorem quadraticForm_diagonal {n : ℕ} [NeZero n] (S : Finset (TorusPlaquette n))
    (hS : S ⊆ plaquettesIn Finset.univ) (h : PlaquetteWeight n)
    (hz : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), p ∉ S → h p = 0) (Gv : S → imaginaryQuaternions)
    (Gq : TorusPlaquette n → imaginaryQuaternions)
    (hG : ∀ (a : S) (e : Fin 3), imaginaryComponent e (Gv a) = imaginaryComponent e (Gq a.1)) :
    quadraticForm (Matrix.diagonal fun a : S => h a.1) Gv =
      (1 / 2) * ∑ p ∈ plaquettesIn Finset.univ, h p * ∑ e : Fin 3, imaginaryComponent e (Gq p) ^ 2 := by
  classical
  unfold quadraticForm
  congr 1
  have e1 : ∀ a : S, ∑ b, Matrix.diagonal (fun a : S => h a.1) a b *
      ∑ e : Fin 3, imaginaryComponent e (Gv a) * imaginaryComponent e (Gv b) =
      h a.1 * ∑ e : Fin 3, imaginaryComponent e (Gq a.1) ^ 2 := by
    intro a
    rw [Finset.sum_eq_single a]
    · rw [Matrix.diagonal_apply_eq]
      congr 1
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [hG a e]
      ring
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_mul]
    · intro hc
      exact absurd (Finset.mem_univ a) hc
  simp only [e1]
  rw [Finset.sum_coe_sort S fun p => h p * ∑ e : Fin 3, imaginaryComponent e (Gq p) ^ 2]
  refine Finset.sum_subset hS fun p hp hq => ?_
  rw [hz p hp hq, zero_mul]
private theorem sum_abs_diagonal {n : ℕ} (S : Finset (TorusPlaquette n)) (h : PlaquetteWeight n) :
    ∑ a : S, ∑ b : S, |(Matrix.diagonal fun a : S => h a.1) a b| = ∑ a : S, |h a.1| := by
  classical
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · rw [Matrix.diagonal_apply_eq]
  · intro b _ hb
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), abs_zero]
  · intro hc
    exact absurd (Finset.mem_univ a) hc
end Forms
section Markov
private theorem measureReal_inter_compl_le_of_moment {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (A B : Set Ω) (Wf : Ω → ℝ) {s D : ℝ} (hs : 0 < s) (q : ℕ) (hq : Even q)
    (hsm : ∀ᵐ u ∂μ, u ∈ A → Wf u ≤ s → u ∈ B) (hi : Integrable (A.indicator fun u => Wf u ^ q) μ)
    (hb : ∫ u, A.indicator (fun u => Wf u ^ q) u ∂μ ≤ D) : μ.real (A ∩ Bᶜ) ≤ D / s ^ q := by
  have hsq : 0 < s ^ q := pow_pos hs q
  have h0 : 0 ≤ᵐ[μ] A.indicator fun u => Wf u ^ q :=
    ae_of_all _ fun u => Set.indicator_nonneg (fun u _ => hq.pow_nonneg _) u
  have h1 := mul_meas_ge_le_integral_of_nonneg h0 hi (s ^ q)
  have hsub : (A ∩ Bᶜ : Set Ω) ≤ᵐ[μ] ({x | s ^ q ≤ A.indicator (fun u => Wf u ^ q) x} : Set Ω) := by
    filter_upwards [hsm] with u hu hmem
    have hmem' : u ∈ A ∩ Bᶜ := hmem
    have hlt : s < Wf u := by
      by_contra hc
      exact hmem'.2 (hu hmem'.1 (not_lt.1 hc))
    show s ^ q ≤ A.indicator (fun u => Wf u ^ q) u
    rw [Set.indicator_of_mem hmem'.1]
    exact pow_le_pow_left₀ hs.le hlt.le q
  have h2 : μ.real (A ∩ Bᶜ) ≤ μ.real {x | s ^ q ≤ A.indicator (fun u => Wf u ^ q) x} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  rw [le_div_iff₀ hsq]
  calc μ.real (A ∩ Bᶜ) * s ^ q ≤ μ.real {x | s ^ q ≤ A.indicator (fun u => Wf u ^ q) x} * s ^ q :=
        mul_le_mul_of_nonneg_right h2 hsq.le
    _ = s ^ q * μ.real {x | s ^ q ≤ A.indicator (fun u => Wf u ^ q) x} := mul_comm _ _
    _ ≤ _ := h1.trans hb
private theorem rpow_ratio_pow_le {β : ℝ} (hβ : 1 ≤ β) (Cs : ℝ) :
    (Cs * β ^ (-(1 / 2 : ℝ) + 2 / 1000)) ^ 200 / (β ^ (-(1 / 4 : ℝ))) ^ 200 ≤ |Cs| ^ 200 * β ^ (-(40 : ℝ)) := by
  have hβ0 : 0 < β := by linarith
  have e1 : (β ^ (-(1 / 2 : ℝ) + 2 / 1000)) ^ 200 = β ^ ((-(1 / 2 : ℝ) + 2 / 1000) * 200) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hβ0.le]
    norm_num
  have e2 : (β ^ (-(1 / 4 : ℝ))) ^ 200 = β ^ (-(1 / 4 : ℝ) * 200) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hβ0.le]
    norm_num
  have e3 : Cs ^ 200 = |Cs| ^ 200 := (Even.pow_abs (Nat.even_iff.2 (by norm_num)) Cs).symm
  rw [mul_pow, e1, e2, e3, mul_div_assoc, ← Real.rpow_sub hβ0]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (abs_nonneg _) _)
  exact Real.rpow_le_rpow_of_exponent_le hβ (by norm_num)
end Markov
section Thresholds
private theorem exists_le_of_log_sq (y b : ℝ) (hb : 0 ≤ b) :
    ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → y + b * (2 * Real.log x ^ 2) ≤ x := by apply _root_.YangMills.SharedProofs.p47765 <;> assumption
private theorem exists_large_coupling_threshold (Lr : ℝ) (n₀ : ℕ) {c : ℝ} (hc : 0 < c) (y b : ℝ) (hb : 0 ≤ b) :
    ∃ x₀ : ℝ, ∀ β, x₀ ≤ β → 25 ≤ β ∧ 2 * Real.log Lr + 3 ≤ Real.log β ∧ y + b * (2 * Real.log β ^ 2) ≤ β ∧
      β ^ 40 ≤ Real.exp (c * β) ∧ (n₀ : ℝ) ≤ β ^ ((1 : ℝ) / 20) := by
  obtain ⟨x₃, h₃⟩ := exists_le_of_log_sq y b hb
  have e2 := Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log Lr + 3)
  have e4 := (isLittleO_pow_exp_pos_mul_atTop 40 hc).def (c := 1) (by norm_num)
  have e5 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).eventually_ge_atTop (n₀ : ℝ)
  have e := (eventually_ge_atTop (25 : ℝ)).and (e2.and (e4.and (e5.and (eventually_ge_atTop x₃))))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 e
  refine ⟨x₀, fun β hβ => ?_⟩
  obtain ⟨a1, a2, a4, a5, a3⟩ := hx₀ β hβ
  refine ⟨a1, a2, h₃ β a3, ?_, a5⟩
  have hp : 0 ≤ β ^ 40 := by
    have : 0 ≤ β := by linarith
    positivity
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp, abs_of_pos (Real.exp_pos _)] at a4
  exact a4
private theorem exists_top_exponent {L m M : ℕ} (hL : 2 ≤ L) {β : ℝ} (hlam : 2 * Real.log L + 3 ≤ Real.log β)
    (hM : (M : ℝ) ≤ Real.log β ^ 2) (hβ : 0 < β) (hs : Real.exp (Real.log β ^ 3) ≤ 2 * (L : ℝ) ^ m) :
    ∃ e : ℕ, 1 ≤ e ∧ m = e + M + M ∧ 2 ^ 10 * β ^ ((1 : ℝ) / 20) ≤ 2 * (L : ℝ) ^ e := by
  have hlL : 0 < Real.log L := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = Real.log β := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = Real.log L := ⟨_, rfl⟩
  rw [← hl, ← hw] at hlam
  rw [← hl] at hM hs
  rw [← hw] at hlL
  have hl3 : 3 ≤ l := by linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : l ^ 3 ≤ Real.log 2 + m * w := by
    have := Real.log_le_log (Real.exp_pos _) hs
    rw [Real.log_exp, Real.log_mul (by norm_num) (by positivity), Real.log_pow, ← hw] at this
    exact this
  have hsq : 0 ≤ l ^ 2 := by positivity
  have h2 : (2 * w + 3) * l ^ 2 ≤ l ^ 3 := by
    have := mul_le_mul_of_nonneg_right hlam hsq
    nlinarith
  have h3 : 2 * (M : ℝ) * w ≤ 2 * l ^ 2 * w := by
    have := mul_le_mul_of_nonneg_right hM hlL.le
    linarith
  have h4 : 3 * l ^ 2 ≤ Real.log 2 + ((m : ℝ) - 2 * M) * w := by nlinarith
  have h5 : 27 ≤ 3 * l ^ 2 := by nlinarith
  have hlt : 2 * M < m := by
    by_contra hc
    have hc' : (m : ℝ) ≤ 2 * M := by exact_mod_cast not_lt.1 hc
    have : ((m : ℝ) - 2 * M) * w ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hlL.le
    linarith
  obtain ⟨e, rfl⟩ : ∃ e, m = e + M + M := ⟨m - 2 * M, by omega⟩
  refine ⟨e, by omega, rfl, ?_⟩
  have hbe : (0 : ℝ) < β ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hβ _
  have hpos : (0 : ℝ) < 2 ^ 10 * β ^ ((1 : ℝ) / 20) := by positivity
  have hpos2 : (0 : ℝ) < 2 * (L : ℝ) ^ e := by positivity
  rw [← Real.log_le_log_iff hpos hpos2, Real.log_mul (by norm_num) hbe.ne', Real.log_pow, Real.log_rpow hβ,
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, ← hl, ← hw]
  push_cast at h4 ⊢
  have h6 : (((e : ℝ) + M + M) - 2 * M) * w = e * w := by ring
  rw [h6] at h4
  nlinarith
end Thresholds
section Estimates
private theorem integral_prod_indicator_congr {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) {r : ℕ}
    (Gc Rw : Fin r → Ω → ℝ) (h : ∀ᵐ ω ∂μ, ω ∈ A → ∀ i, Gc i ω = Rw i ω) {c D : ℝ}
    (hI : Integrable (A.indicator fun ω => ∏ i, Rw i ω) μ)
    (hB : |∫ ω, A.indicator (fun ω => ∏ i, Rw i ω) ω ∂μ - c| ≤ D) :
    Integrable (A.indicator fun ω => ∏ i, Gc i ω) μ ∧
      |∫ ω, A.indicator (fun ω => ∏ i, Gc i ω) ω ∂μ - c| ≤ D := by
  have hcg : (A.indicator fun ω => ∏ i, Gc i ω) =ᵐ[μ] A.indicator fun ω => ∏ i, Rw i ω := by
    filter_upwards [h] with ω hω
    by_cases hm : ω ∈ A
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm]
      exact Finset.prod_congr rfl fun i _ => hω hm i
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]
  refine ⟨hI.congr hcg.symm, ?_⟩
  rw [integral_congr_ae hcg]
  exact hB
private theorem lintegral_indicator_congr_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {S S' : Set Ω}
    (hS : S = S') {f g : Ω → ℝ} (h : ∀ᵐ ω ∂μ, ω ∈ S → f ω = g ω) {D : ENNReal}
    (hb : ∫⁻ ω, ENNReal.ofReal (S'.indicator g ω) ∂μ ≤ D) :
    ∫⁻ ω, ENNReal.ofReal (S.indicator f ω) ∂μ ≤ D := by
  subst hS
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hb
  filter_upwards [h] with ω hω
  by_cases hm : ω ∈ S
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, hω hm]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]
private theorem abs_sub_le_of_two_steps {a b c u v w Cs Cx : ℝ} (h1 : |a - b| ≤ Cs * w)
    (h2 : |b - c| ≤ Cx * (u + v)) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    |a - c| ≤ (|Cs| + |Cx|) * (u + (v + w)) := by
  have e : a - c = (a - b) + (b - c) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h3 : Cs * w ≤ |Cs| * (u + (v + w)) :=
    mul_le_mul (le_abs_self _) (by linarith) hw (abs_nonneg _)
  have h4 : Cx * (u + v) ≤ |Cx| * (u + (v + w)) :=
    mul_le_mul (le_abs_self _) (by linarith) (by linarith) (abs_nonneg _)
  nlinarith
private theorem torus_and_depth_error_le {β Nr : ℝ} (hl : 3 ≤ Real.log β) (hβ : 0 < β)
    (hN : Real.exp (Real.log β ^ 3) ≤ Nr) :
    Nr ^ (-(4 : ℤ)) + (4 : ℝ) ^ (-((chainDepth β : ℕ) : ℤ)) ≤ 5 / β := by
  obtain ⟨l, hlb⟩ : ∃ l : ℝ, l = Real.log β := ⟨_, rfl⟩
  rw [← hlb] at hl hN
  have hexp : Real.exp l = β := by rw [hlb, Real.exp_log hβ]
  have hl3 : l ≤ l ^ 3 := by nlinarith [sq_nonneg l]
  have hβN : β ≤ Nr := by
    rw [← hexp]
    exact (Real.exp_le_exp.2 hl3).trans hN
  have hβ1 : 1 ≤ β := by
    rw [← hexp]
    exact Real.one_le_exp (by linarith)
  have hN1 : 1 ≤ Nr := hβ1.trans hβN
  have t1 : Nr ^ (-(4 : ℤ)) ≤ 1 / β := by
    rw [zpow_neg, one_div]
    refine inv_anti₀ hβ ?_
    have : (Nr : ℝ) ^ (4 : ℤ) = Nr ^ (4 : ℕ) := by norm_cast
    rw [this]
    exact hβN.trans (le_self_pow₀ hN1 (by norm_num))
  have hM : Real.log β ^ 2 < (chainDepth β : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [← hlb] at hM
  have hlog4 : 1 ≤ Real.log 4 := by
    have e : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [e, Real.log_pow]
    have := Real.log_two_gt_d9
    push_cast
    linarith
  have h4 : β ≤ (4 : ℝ) ^ (chainDepth β + 1) := by
    have e4 : (4 : ℝ) ^ (chainDepth β + 1) = Real.exp (((chainDepth β : ℝ) + 1) * Real.log 4) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), mul_comm]
      push_cast
      rfl
    rw [e4]
    have hM0 : (0 : ℝ) ≤ (chainDepth β : ℝ) + 1 := by positivity
    have a1 : (chainDepth β : ℝ) + 1 ≤ ((chainDepth β : ℝ) + 1) * Real.log 4 := le_mul_of_one_le_right hM0 hlog4
    have a2 : l ≤ l ^ 2 := by nlinarith
    calc β = Real.exp l := hexp.symm
      _ ≤ _ := Real.exp_le_exp.2 (by linarith)
  have t2 : (4 : ℝ) ^ (-((chainDepth β : ℕ) : ℤ)) ≤ 4 / β := by
    rw [zpow_neg, zpow_natCast, le_div_iff₀ hβ, inv_mul_le_iff₀ (by positivity)]
    calc β ≤ (4 : ℝ) ^ (chainDepth β + 1) := h4
      _ = _ := by rw [pow_succ]
  calc _ ≤ 1 / β + 4 / β := add_le_add t1 t2
    _ = 5 / β := by ring
private theorem error_le_of_rpow_bound {β n ε : ℝ} (h25 : 25 ≤ β) (hn1 : 1 ≤ n) (hn2 : n ≤ β ^ ((1 : ℝ) / 90))
    (hε0 : 0 ≤ ε) (hε : ε ≤ 5 / β) : ε ≤ n ^ (-(4 : ℤ)) ∧ n ^ 4 * ε ≤ 5 * β ^ (-(1 / 100 : ℝ)) := by
  have hβ1 : 1 ≤ β := by linarith
  have hβ0 : 0 < β := by linarith
  have hn0 : 0 < n := by linarith
  have hn4 : n ^ 4 ≤ β ^ ((4 : ℝ) / 90) := by
    have h2 : n ^ 4 ≤ (β ^ ((1 : ℝ) / 90)) ^ 4 := pow_le_pow_left₀ hn0.le hn2 4
    refine h2.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hβ0.le]
    norm_num
  have h1 : n ^ 4 * ε ≤ 5 * β ^ ((4 : ℝ) / 90 - 1) := by
    have e : β ^ ((4 : ℝ) / 90 - 1) = β ^ ((4 : ℝ) / 90) / β := by
      rw [Real.rpow_sub hβ0, Real.rpow_one]
    rw [e]
    calc n ^ 4 * ε ≤ β ^ ((4 : ℝ) / 90) * (5 / β) :=
          mul_le_mul hn4 hε hε0 (Real.rpow_nonneg hβ0.le _)
      _ = _ := by ring
  have h2 : β ^ ((4 : ℝ) / 90 - 1) ≤ β ^ (-(1 / 100 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hβ1 (by norm_num)
  refine ⟨?_, by linarith⟩
  have h3 : β ^ ((4 : ℝ) / 90 - 1) ≤ β ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hβ1 (by norm_num)
  have h4 : (5 : ℝ) ≤ β ^ ((1 : ℝ) / 2) := by
    have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 25) h25 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have e : (25 : ℝ) ^ ((1 : ℝ) / 2) = 5 := by
      rw [show (25 : ℝ) = 5 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [e] at this
  have h5 : 5 * β ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hβ0.le]
    have hp : 0 < β ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hβ0 _
    rw [← div_eq_mul_inv, div_le_one hp]
    exact h4
  rw [zpow_neg, show (n : ℝ) ^ (4 : ℤ) = n ^ (4 : ℕ) by norm_cast, ← one_div, le_div_iff₀ (by positivity)]
  linarith
private theorem mul_sum_le_of_abs_le {CR q1 p v C : ℝ} (hq1 : 0 ≤ q1) (hp : 0 ≤ p) (hv0 : 0 ≤ v) (hv : v ≤ 5 * p)
    (hC : 6 * |CR| ≤ C) : CR * (q1 + v) ≤ C * (p + q1) := by
  have h0 := abs_nonneg CR
  calc CR * (q1 + v) ≤ |CR| * (q1 + 5 * p) := mul_le_mul (le_abs_self _) (by linarith) (by linarith) h0
    _ ≤ 6 * |CR| * (p + q1) := by nlinarith [mul_nonneg h0 hq1, mul_nonneg h0 hp]
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (by linarith)
private theorem eighty_mul_le_of_chain {n b1 b2 P Q : ℝ} (h1 : n ≤ b1) (h2 : b1 ≤ b2) (h3 : 0 ≤ b2)
    (h4 : 2 ^ 10 * b2 ≤ 2 * P) (h5 : P ≤ Q) : 80 * n ≤ 2 * Q := by
  norm_num at h4
  linarith
end Estimates
section Samples
variable {ℓ : TorusLumps.StepParameters}
private theorem measurable_sampleBelow (s : ℕ) : ∀ d n : ℕ, Measurable (sampleBelow ℓ s d n)
  | 0, _ => measurable_id
  | d + 1, n => (measurable_sampleBelow s d (n * ℓ.side)).comp measurable_fst
private def localEventSet (T : StageTower ℓ) (x : ℝ) (N : ℕ) [NeZero N]
    (o : TorusSite (fineSide ℓ.side (chainDepth x) (fineSide ℓ.side (chainDepth x) N))) :
    Set (MarkedSample ℓ (0 + chainDepth x + chainDepth x) N) :=
  {u | IsLocalEvent T 0 (chainDepth x) (localBoxRadius x) N u o}
private def gaugeSmallSet (T : StageTower ℓ) (x nn : ℝ) (N : ℕ) [NeZero N]
    (o : TorusSite (fineSide ℓ.side (chainDepth x) (fineSide ℓ.side (chainDepth x) N))) :
    Set (MarkedSample ℓ (0 + chainDepth x + chainDepth x) N) :=
  {u | IsGaugeSmallAlong T 0 nn (logCubeScale x) (x ^ (-(1 / 4 : ℝ))) (chainDepth x) (fineSide ℓ.side (chainDepth x) N)
    (sampleBelow ℓ (0 + chainDepth x) (chainDepth x) N u) o
    (axialGaugeAt ℓ (topField ℓ (0 + chainDepth x) (fineSide ℓ.side (chainDepth x) N)
      (sampleBelow ℓ (0 + chainDepth x) (chainDepth x) N u))
      (siteAbove ℓ.side (chainDepth x) (fineSide ℓ.side (chainDepth x) N) o))}
private def fineField (ℓ : TorusLumps.StepParameters) (x : ℝ) (N : ℕ)
    (u : MarkedSample ℓ (0 + chainDepth x + chainDepth x) N) :
    TorusField (fineSide ℓ.side (chainDepth x) (fineSide ℓ.side (chainDepth x) N)) :=
  sampleBelow ℓ 0 (chainDepth x) (fineSide ℓ.side (chainDepth x) N) (sampleBelow ℓ (0 + chainDepth x) (chainDepth x) N u)
private def accumulatedCurlKernel (a ρA : ℝ) (L : ℕ) [NeZero L] (d n : ℕ) [NeZero n]
    (p p' : TorusPlaquette (fineSide L d n)) : ℝ :=
  accumulatedCovariance a ρA L 0 d n (curlFunctional p) (curlFunctional p')
end Samples
set_option maxHeartbeats 8000000 in
theorem fineLevelQuadraticApproxStatement_holds (hW : windowTowerExistsStatement)
    (hMo : levelCurvatureMomentsStatement) (hLE : localEventLikelyStatement) (hSz : localChainSizeStatement)
    (hBO : bareObservableQuadraticFormStatement) (hDB : BoxEvents.sampleBelowLawStatement)
    (hSt : StepCovariancesSumToMaxwellStatement) (hMx : maxwellCovarianceLongDistanceStatement)
    (hHs : stepHessianPosDefStatement) (hRs : fineTraceRiemannSumStatement)
    (hWt : testWeightsLocalStatement) : fineLevelQuadraticApproxStatement := by
  have Hall := holdsOnParams_and hW (holdsOnParams_and hMo (holdsOnParams_and hLE (holdsOnParams_and hSz
    (holdsOnParams_and hBO (holdsOnParams_and (holdsOnParameters_of_holdsAtAdmissible hDB)
      (holdsOnParams_and hSt (holdsOnParams_and hMx hHs)))))))
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hr, H⟩ := Hall a ha
  refine ⟨L₀, rt₀, C₀, hr, fun L hodd hL Tb hTa hTL hD hC hHf hrt hc => ?_⟩
  obtain ⟨y₀, Hy⟩ := H L hodd hL Tb hTa hTL hD hC hHf hrt hc
  refine ⟨y₀, fun y hy hR hW₀ => ?_⟩
  obtain ⟨⟨hfit, hJ, xw, hxw⟩, hMoT, ⟨cl, xl, hcl, hlE⟩, ⟨C₁, cS, hC₁, hcS, hSq⟩, ⟨Cq, xb, hBq⟩, hDBt,
    ⟨CSt, hStT⟩, ⟨CMx, hMxT⟩, hHsT⟩ := Hy y hy hR hW₀
  refine ⟨hfit, fun vt hv0 hv1 => ?_⟩
  choose Cm xm hmo using hMoT
  obtain ⟨Cs, xs, hsz⟩ := hSq 200
  obtain ⟨CR, hRm⟩ := hRs (Tb.stepParameters y) vt (|CSt| + |CMx|) hfit hv0 hv1 (by positivity)
  obtain ⟨xf, hxf⟩ := exists_large_coupling_threshold ((Tb.stepParameters y).side : ℝ) Tb.n₀ hcl
    (Tb.stepParameters y).y₁ (2 * |(Tb.stepParameters y).B|) (by positivity)
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = (∑ r ∈ Finset.range 17, |Cm r|) + 32 * 41 ^ 4 + 1 + |Cs| ^ 200 + 6 * |CR| :=
    ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = ∑ r ∈ Finset.range 17, |xm r| := ⟨_, rfl⟩
  have hCs0 : 0 ≤ |Cs| ^ 200 := pow_nonneg (abs_nonneg _) _
  have hCR0 := abs_nonneg CR
  have hsum0 : 0 ≤ ∑ r ∈ Finset.range 17, |Cm r| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCr : ∀ r ≤ 16, |Cm r| ≤ C := by
    intro r hr
    have := Finset.single_le_sum (f := fun r => |Cm r|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega : r < 17))
    rw [hCdef]
    linarith
  have hXr : ∀ r ≤ 16, xm r ≤ X := by
    intro r hr
    have := Finset.single_le_sum (f := fun r => |xm r|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega : r < 17))
    rw [hXdef]
    exact (le_abs_self _).trans this
  have hC32 : (32 : ℝ) * 41 ^ 4 ≤ C := by rw [hCdef]; linarith
  have hC1 : 1 ≤ C := by rw [hCdef]; norm_num at hsum0 ⊢; linarith
  have hCCs : |Cs| ^ 200 ≤ C := by rw [hCdef]; linarith
  have hCCR : 6 * |CR| ≤ C := by rw [hCdef]; linarith
  refine ⟨Cq, C, max (max (max X xw) (max xl (max xb xs))) xf, ?_⟩
  intro q β m n hq hβ hside hn1 hn2 f hf
  have hX' : X ≤ β := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hβ
  have hxw' : xw ≤ β := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hβ
  have hxl' : xl ≤ β := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hβ
  have hxb' : xb ≤ β :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))).trans hβ
  have hxs' : xs ≤ β :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))).trans hβ
  have hxf' : xf ≤ β := (le_max_right _ _).trans hβ
  obtain ⟨h25, hlam, hyb, hexp, hn0β⟩ := hxf β hxf'
  have hβ1 : 1 ≤ β := by linarith
  have hβ0 : 0 < β := by linarith
  have hlog3 : 3 ≤ Real.log β := by
    have := Real.log_nonneg (by
      have := hfit.L_ge
      have h2 : (1 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by
        have : 1 ≤ (Tb.stepParameters y).side := by omega
        exact_mod_cast this
      exact h2 : (1 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ))
    linarith
  have hfL : 2 ≤ (Tb.stepParameters y).side := by
    have := hfit.L_ge
    omega
  have hMle : ((chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 : ℕ) : ℝ) ≤ Real.log β ^ 2 :=
    Nat.floor_le (by positivity)
  obtain ⟨e, he1, hme, hNside⟩ := exists_top_exponent hfL hlam hMle hβ0 hside
  obtain ⟨N, hNe⟩ : ∃ N : ℕ, N = 2 * (Tb.stepParameters y).side ^ e := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, e = w + 1 := ⟨e - 1, by omega⟩
  have hNw : N = 2 * (Tb.stepParameters y).side ^ (w + 1) := by rw [hNe, hw]
  have hNz : NeZero N := ⟨by
    rw [hNe]
    have : (Tb.stepParameters y).side ≠ 0 := by omega
    positivity⟩
  have hNr : (2 : ℝ) ^ 10 * β ^ ((1 : ℝ) / 20) ≤ (N : ℝ) := by
    rw [hNe]
    push_cast
    exact hNside
  have hLN : (Tb.stepParameters y).side ∣ N := by
    rw [hNe]
    exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) 2
  have hLpos : 0 < (Tb.stepParameters y).side := by omega
  have hn0N : Tb.n₀ ≤ N := by
    have hp : 0 ≤ β ^ ((1 : ℝ) / 20) := Real.rpow_nonneg hβ0.le _
    have : (Tb.n₀ : ℝ) ≤ (N : ℝ) := by
      exact hn0β.trans ((le_mul_of_one_le_left hp (by norm_num)).trans hNr)
    exact_mod_cast this
  have hn0N1 : Tb.n₀ ≤ fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N := by
    rw [fineSide_eq]
    exact hn0N.trans (Nat.le_mul_of_pos_right N (pow_pos hLpos _))
  have hn0N2 : Tb.n₀ ≤ fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1)
      (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N) := by
    rw [fineSide_eq]
    exact hn0N1.trans (Nat.le_mul_of_pos_right _ (pow_pos hLpos _))
  have hyβ : (Tb.stepParameters y).y₁ ≤ β := by
    have h2 : 0 ≤ 2 * |(Tb.stepParameters y).B| * (2 * Real.log β ^ 2) := by positivity
    linarith
  have h0 : HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β) := hW₀ β hyβ
  have hJ2 : (Tb.stepParameters y).y₁ ≤ β - 2 * |(Tb.stepParameters y).B| *
      ((2 * chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 : ℕ) : ℝ) := by
    push_cast
    have h2 : 2 * |(Tb.stepParameters y).B| * (2 * (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 : ℝ)) ≤
        2 * |(Tb.stepParameters y).B| * (2 * Real.log β ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hrun := couplingFlow_ge_of_bound hR h0 (2 * chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) hJ2
  obtain ⟨T, hst, hcut, hcoin⟩ := hxw β 0 hxw' (fun j hj => hrun j (by rw [Nat.zero_add] at hj; exact hj))
  have hloc : ∀ x' : ℝ, x' ≤ β → IsLocalChainAbove Tb y T β 0 N n x' := by
    intro x' hx'
    refine ⟨hx', fun j hj => hrun j (by rw [Nat.zero_add] at hj; exact hj), hst, hcut, hcoin, ?_, hn1, hn2⟩
    show (2 : ℝ) ^ 10 * ((⌊β ^ ((1 : ℝ) / 20)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ)
    exact (mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg hβ0.le _)) (by norm_num)).trans hNr
  have key : ∀ (n₁ : ℕ) [NeZero n₁],
      n₁ = fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N) →
      ∀ (h : Fin (q + 1) → PlaquetteWeight n₁) (o : TorusSite n₁), (∀ i, weightSup (h i) ≤ 1) →
      (∀ (i : Fin (q + 1)) (z : TorusSite n₁) (p : TorusPlaquette (fineSide (Tb.stepParameters y).side 0 n₁)),
        z ∉ supBall o (12 * n) → IsPlaquetteAt (Tb.stepParameters y).side 0 z p → h i p = 0) →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (Φ : Ω → TorusField n₁) (I : Type) (_ : Fintype I) (G : Ω → I → imaginaryQuaternions) (A B : Set Ω)
        (κ : Fin (q + 1) → Matrix I I ℝ) (Tc : Matrix I I ℝ) (Bg : ℝ) (Tt : TorusPlaquette n₁ → TorusPlaquette n₁ → ℝ),
        Measurable Φ ∧ Measure.map Φ μ = wilsonLaw β n₁ ∧
        QuadraticFormApproximation μ (fun i ω => curvatureObservable (h i) (Φ ω)) G A B κ Tc 0
          (couplingFlow (Tb.stepParameters y) β 0).1 n C 40 Bg Cq ∧
        (∀ i ω, |curvatureObservable (h i) (Φ ω)| ≤ C * n ^ 4) ∧
        cyclicTraceSum κ Tc = 3 / 2 * kernelCycleSum h Tt ∧
        ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n₁)), ∀ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n₁)),
          1 ≤ sqNorm (plaquetteCentreDisplacement p p') →
          sqNorm (plaquetteCentreDisplacement p p') ≤ ((n₁ : ℝ) / 8) ^ 2 →
          |Tt p p' - continuumCurvatureKernel (plaquetteCentreDisplacement p p') p.2.1 p.2.2 p'.2.1 p'.2.2| ≤
            (|CSt| + |CMx|) * (sqNorm (plaquetteCentreDisplacement p p') ^ (-(5 / 2 : ℝ)) +
              ((n₁ : ℝ) ^ (-(4 : ℤ)) +
                (4 : ℝ) ^ (-((chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 : ℕ) : ℤ)))) := by
    intro n₁ _ en h o hsup hzero
    subst en
    have hS' : ballPlaquettes o n ⊆ plaquettesIn Finset.univ := by
      unfold ballPlaquettes
      exact Finset.filter_subset _ _
    have hzS : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite _)), p ∉ ballPlaquettes o n → ∀ i, h i p = 0 := by
      intro p hp hq i
      have hnb : p.1 ∉ supBall o (19 * n) := fun hb => hq (Finset.mem_filter.2 ⟨hp, hb⟩)
      refine hzero i p.1 p (fun hb => hnb ?_) ?_
      · have h12 := (Finset.mem_filter.1 hb).2
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h12.trans (by linarith)⟩
      · exact ⟨(Finset.mem_filter.1 hp).2.1, p.1, List.mem_cons.2 (Or.inl rfl), Finset.mem_singleton.2 rfl⟩
    have hmoR := fun (r : ℕ) (a : Fin r → ballPlaquettes o n) (e : Fin r → Fin 3) (hr : r ≤ 16) =>
      hmo r T β 0 N n o (fun j => (a j).1) e w hNw (hloc _ ((hXr r hr).trans hX'))
        (fun j => ⟨hS' (a j).2, (Finset.mem_filter.1 (a j).2).2⟩)
    have hm0 := hmo 0 T β 0 N n o Fin.elim0 Fin.elim0 w hNw (hloc _ ((hXr 0 (by norm_num)).trans hX'))
      (fun j => j.elim0)
    obtain ⟨G, hGm, hGb, hGa⟩ := exists_measurable_bounded_representative
      (markedSampleLaw T β (0 + chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N)
      (fun (a : ballPlaquettes o n) (e : Fin 3) u => imaginaryComponent e (sampledCurvature T 0
        (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) n (couplingFlow (Tb.stepParameters y) β 0).1 N u o a.1))
      (localEventSet T (couplingFlow (Tb.stepParameters y) β 0).1 N o) (abs_nonneg (Cm 1))
      (fun a e => (hmoR 1 (fun _ => a) (fun _ => e) (by norm_num)).2.1 0)
      (fun a e => (hmoR 1 (fun _ => a) (fun _ => e) (by norm_num)).2.2.1.mono
        fun u hu hA => (hu hA 0).trans (le_abs_self _))
    have e2 : 0 + chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 + chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 =
        0 + 2 * chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 := by omega
    have hst2 : IsTowerAtParameters Tb y T β (0 + chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) := by
      rw [e2]
      exact hst
    have hst1 : IsTowerAtParameters Tb y T β (0 + chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) :=
      ⟨hst2.startsAtWilson, fun j hj => hst2.coupling_eq j (by omega), fun j hj => hst2.onFamily j (by omega)⟩
    obtain ⟨hprob, hmap1⟩ := hDBt T β (0 + chainDepth (couplingFlow (Tb.stepParameters y) β 0).1)
      (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N hst2 hcoin (fun j hj => hrun j (by omega))
    obtain ⟨-, hmap2⟩ := hDBt T β 0 (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1)
      (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N) hst1 hcoin
      (fun j hj => hrun j (by omega))
    have := hprob
    have hS3 := hsz T β 0 N n 0 (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1)
      (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) o (hloc _ hxs') hLN le_rfl rfl rfl
    have en0 : n / ((Tb.stepParameters y).side : ℝ) ^ (0 - 0) = n := by simp
    rw [en0] at hS3
    obtain ⟨hsm, ⟨hint, hbd⟩, -⟩ := hS3
    have hs1 : β ^ (-(1 / 4 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
    have hs0 : 0 < β ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hβ0 _
    have hrw := measureReal_inter_compl_le_of_moment
      (markedSampleLaw T β (0 + chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N)
      (localEventSet T (couplingFlow (Tb.stepParameters y) β 0).1 N o)
      (gaugeSmallSet T (couplingFlow (Tb.stepParameters y) β 0).1 n N o)
      (fun u => widenedChainSize T C₁ cS (localChainDepth (Tb.stepParameters y) β 0) 0 n
        (localLogScale (Tb.stepParameters y) β 0) (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N)
        (sampleBelow (Tb.stepParameters y) (0 + chainDepth (couplingFlow (Tb.stepParameters y) β 0).1)
          (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N u) o)
      hs0 200 (Nat.even_iff.2 (by norm_num)) (hsm _ hs1) hint hbd
    refine ⟨MarkedSample (Tb.stepParameters y) (0 + chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N, inferInstance,
      markedSampleLaw T β (0 + chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N, hprob,
      fineField (Tb.stepParameters y) (couplingFlow (Tb.stepParameters y) β 0).1 N,
      {x // x ∈ ballPlaquettes o n}, inferInstance, G, localEventSet T (couplingFlow (Tb.stepParameters y) β 0).1 N o,
      gaugeSmallSet T (couplingFlow (Tb.stepParameters y) β 0).1 n N o,
      fun i => Matrix.diagonal fun a : ballPlaquettes o n => h i a.1,
      Matrix.of fun a b : ballPlaquettes o n => accumulatedCurlKernel Tb.coupling Tb.ρA (Tb.stepParameters y).side
        (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N) a.1 b.1,
      |Cm 1|, accumulatedCurlKernel Tb.coupling Tb.ρA (Tb.stepParameters y).side
        (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (measurable_sampleBelow 0 _ _).comp (measurable_sampleBelow _ _ _)
    · have hd1 := measurable_sampleBelow (ℓ := Tb.stepParameters y)
        (0 + chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N
      have hd2 := measurable_sampleBelow (ℓ := Tb.stepParameters y) 0 (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N)
      have hmm := Measure.map_map (μ := markedSampleLaw T β (0 + chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N) hd2 hd1
      rw [hmap1, hmap2] at hmm
      exact hmm.symm
    · refine ⟨hm0.1, hGm, hGb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro r a e hr
        obtain ⟨-, -, -, -, hI, hB⟩ := hmoR r a e hr
        have ht := integral_prod_indicator_congr
          (markedSampleLaw T β (0 + chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 +
            chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N)
          (localEventSet T (couplingFlow (Tb.stepParameters y) β 0).1 N o)
          (fun i ω => imaginaryComponent (e i) (G ω (a i)))
          (fun i ω => imaginaryComponent (e i) (sampledCurvature T 0 (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) n
            (couplingFlow (Tb.stepParameters y) β 0).1 N ω o (a i).1))
          (hGa.mono fun ω hω hA i => hω hA (a i) (e i)) hI hB
        refine ⟨ht.1, ht.2.trans ?_⟩
        exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hCr r hr)) (Real.rpow_nonneg hβ0.le _)
      · refine Matrix.IsSymm.ext fun a b => ?_
        exact accumulatedCovariance_comm Tb.coupling Tb.ρA (Tb.stepParameters y).side Tb.n₀ 0 hHsT
          (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) _ hn0N1 _ _
      · intro a b
        have hb2 := (hmoR 2 ![a, b] ![0, 0] (by norm_num)).2.2.2.1 0 1 rfl
        exact hb2.trans ((le_abs_self _).trans (hCr 2 (by norm_num)))
      · intro i
        exact Matrix.isSymm_diagonal _
      · intro i
        rw [sum_abs_diagonal]
        refine (sum_abs_weight_ballPlaquettes_le (hsup i) o hn1).trans ?_
        have hlg : 1 ≤ Real.log β ^ 24 := one_le_pow₀ (by linarith)
        have hn4 : 0 ≤ n ^ 4 := by positivity
        have hC16 : (16 : ℝ) * 41 ^ 4 ≤ C := by
          norm_num at hC32 ⊢
          linarith
        have hCn : 0 ≤ C * n ^ 4 := mul_nonneg (by linarith) hn4
        calc (16 : ℝ) * 41 ^ 4 * n ^ 4 ≤ C * n ^ 4 := mul_le_mul_of_nonneg_right hC16 hn4
          _ ≤ C * n ^ 4 * Real.log β ^ 24 := le_mul_of_one_le_right hCn hlg
      · intro i r hr
        have hb := hBq T β N n o (h i) (hloc _ hxb') hLN (hsup i) (hzero i) r hr
        refine lintegral_indicator_congr_le rfl ?_ hb
        filter_upwards [hGa] with ω hω hmem
        have hq' := quadraticForm_diagonal (ballPlaquettes o n) hS' (h i) (fun p hp hq => hzS p hp hq i) (G ω)
          (fun p => sampledCurvature T 0 (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) n
            (couplingFlow (Tb.stepParameters y) β 0).1 N ω o p) (fun a e => hω hmem.1 a e)
        show |curvatureObservable (h i) (fineField (Tb.stepParameters y) (couplingFlow (Tb.stepParameters y) β 0).1 N ω) -
            (0 : Fin (q + 1) → ℝ) i -
            quadraticForm (Matrix.diagonal fun a : ballPlaquettes o n => h i a.1) (G ω)| ^ (2 * r) = _
        rw [hq', Pi.zero_apply, sub_zero]
        rfl
      · have h1 := hlE T β 0 e N n o hNe (hloc _ hxl')
        have hex : Real.exp (-(cl * β)) ≤ C * β ^ (-(40 : ℝ)) := by
          have hp : 0 < β ^ (-(40 : ℝ)) := Real.rpow_pos_of_pos hβ0 _
          have h2 : Real.exp (-(cl * β)) ≤ β ^ (-(40 : ℝ)) := by
            rw [Real.exp_neg, Real.rpow_neg hβ0.le]
            refine inv_anti₀ (by positivity) ?_
            have e40 : β ^ (40 : ℝ) = β ^ (40 : ℕ) := by norm_cast
            rw [e40]
            exact hexp
          calc _ ≤ 1 * β ^ (-(40 : ℝ)) := by linarith
            _ ≤ _ := mul_le_mul_of_nonneg_right hC1 hp.le
        exact h1.trans hex
      · have hfin : (Cs * β ^ (-(1 / 2 : ℝ) + 2 / 1000)) ^ 200 / (β ^ (-(1 / 4 : ℝ))) ^ 200 ≤
            C * β ^ (-(40 : ℝ)) :=
          (rpow_ratio_pow_le hβ1 Cs).trans (mul_le_mul_of_nonneg_right hCCs (Real.rpow_nonneg hβ0.le _))
        exact hrw.trans hfin
    · intro i ω
      refine (abs_curvatureObservable_le (hsup i) o hn1 (fun p hp hq => hzS p hp hq i) _).trans ?_
      exact mul_le_mul_of_nonneg_right hC32 (by positivity)
    · exact cyclicTraceSum_diagonal hq h (accumulatedCurlKernel Tb.coupling Tb.ρA (Tb.stepParameters y).side
        (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N))
        (ballPlaquettes o n) hS' hzS
    · intro p hp p' hp' h1 h2
      obtain ⟨TtM, hMax, hclose⟩ := hStT 0 (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N) hn0N1
      have a1 := hclose p hp p' hp'
      have a2 := hMxT 0 _ hn0N2 TtM hMax p hp p' hp' h1 h2
      have hsq : 0 ≤ sqNorm (plaquetteCentreDisplacement p p') := Finset.sum_nonneg fun _ _ => sq_nonneg _
      exact abs_sub_le_of_two_steps a1 a2 (Real.rpow_nonneg hsq _) (zpow_nonneg (by positivity) _)
        (zpow_nonneg (by norm_num) _)
  obtain ⟨hsup, -, o, hzero⟩ := hWt (Tb.stepParameters y) hfit.L_odd m 0 q n vt f hn1 hv0 hf
  have heq : 2 * (Tb.stepParameters y).side ^ m =
      fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β 0).1) N) := by
    rw [fineSide_eq, fineSide_eq, hNe, hme]
    ring
  obtain ⟨Ω, i1, μ, i2, Φ, I, i3, G, A, B, κ, Tc, Bg, Tt, hΦ, hmap, R, hF, hcyc, hTt⟩ :=
    key (2 * (Tb.stepParameters y).side ^ m) heq (fun i => testWeight (Tb.stepParameters y).side 0 m (f i)) o hsup hzero
  refine ⟨Ω, i1, μ, i2, Φ, I, i3, G, A, B, κ, Tc, Bg, hΦ, hmap, R, hF, ?_⟩
  rw [hcyc]
  have hcast : (((2 * (Tb.stepParameters y).side ^ m : ℕ)) : ℝ) = torusSide (Tb.stepParameters y).side m := by
    unfold torusSide
    push_cast
    ring
  have hside' : Real.exp (Real.log β ^ 3) ≤ (((2 * (Tb.stepParameters y).side ^ m : ℕ)) : ℝ) := by
    rw [hcast]
    exact hside
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (((2 * (Tb.stepParameters y).side ^ m : ℕ)) : ℝ) ^ (-(4 : ℤ)) +
      (4 : ℝ) ^ (-((chainDepth (couplingFlow (Tb.stepParameters y) β 0).1 : ℕ) : ℤ)) := ⟨_, rfl⟩
  have hεle : ε ≤ 5 / β := by
    rw [hε]
    exact torus_and_depth_error_le hlog3 hβ0 hside'
  have hε0 : 0 ≤ ε := by
    rw [hε]
    exact add_nonneg (zpow_nonneg (by positivity) _) (zpow_nonneg (by norm_num) _)
  obtain ⟨hεn, hn4⟩ := error_le_of_rpow_bound h25 hn1 hn2 hε0 hεle
  have h80 : 80 * n ≤ torusSide (Tb.stepParameters y).side m := by
    have hb1 : β ^ ((1 : ℝ) / 90) ≤ β ^ ((1 : ℝ) / 20) := Real.rpow_le_rpow_of_exponent_le hβ1 (by norm_num)
    have hL1 : (1 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by exact_mod_cast hLpos
    have hem : e ≤ m := by omega
    have hpw : ((Tb.stepParameters y).side : ℝ) ^ e ≤ ((Tb.stepParameters y).side : ℝ) ^ m := pow_le_pow_right₀ hL1 hem
    have hp : 0 ≤ β ^ ((1 : ℝ) / 20) := Real.rpow_nonneg hβ0.le _
    unfold torusSide
    exact eighty_mul_le_of_chain hn2 hb1 hp hNside hpw
  have hRr := hRm m q n ε Tt hq hn1 h80 hε0 hεn (fun p hp p' hp' h1 h2 => by
    have hh := hTt p hp p' hp' h1 (by rw [hcast]; exact h2)
    rw [hε]
    exact hh) f hf
  refine hRr.trans ?_
  have hn0 : 0 < n := by linarith
  have hq1 : 0 ≤ 1 / n := by positivity
  have hp : 0 ≤ β ^ (-(1 / 100 : ℝ)) := Real.rpow_nonneg hβ0.le _
  have hnn : 0 ≤ n ^ 4 * ε := mul_nonneg (by positivity) hε0
  exact mul_sum_le_of_abs_le hq1 hp hnn hn4 hCCR
end FourPointCondition
end YangMills.Construction
end

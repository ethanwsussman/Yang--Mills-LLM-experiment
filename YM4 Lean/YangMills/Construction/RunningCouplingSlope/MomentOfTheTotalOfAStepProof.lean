import YangMills.Construction.ColdChainAtEveryLevel.KernelsOnCellsProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.LawInAState.DecayOverATorusProof
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.RunningCouplingSlope.MomentOfAnExpansionProof
import YangMills.Construction.RunningCouplingSlope.MomentOfTheLeastActionProof
import YangMills.Construction.RunningCouplingSlope.MomentOfTheTotalOfAStep
import YangMills.Construction.RunningCouplingSlope.NumberOfAStepIsTheNumberOfItsDensity
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
noncomputable section
open scoped Topology Quaternion
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps RenormalizationStepParameters SlopeCoefficient Filter
namespace RunningCouplingSlope
namespace GaugeTotalMoment
variable {n : ℕ}
private def expAbsDecay (u : ℝ) (k : ℤ) : ℝ := Real.exp (-(u * |(k : ℝ)|))
private theorem expAbsDecay_nonneg (u : ℝ) (k : ℤ) : 0 ≤ expAbsDecay u k := (Real.exp_pos _).le
private theorem summable_expAbsDecay {u : ℝ} (hu : 0 < u) : Summable (expAbsDecay u) := by apply _root_.YangMills.DeltaSharedProofs.p3646 <;> assumption
private def latticeExpSum (u : ℝ) : ℝ := (∑' k : ℤ, expAbsDecay (u / 4) k) ^ 4
private theorem latticeExpSum_nonneg (u : ℝ) : 0 ≤ latticeExpSum u :=
  pow_nonneg (tsum_nonneg (expAbsDecay_nonneg _)) 4
private theorem abs_le_offsetNorm (z : Fin 4 → ℤ) (i : Fin 4) : |((z i : ℤ) : ℝ)| ≤ (offsetNorm z : ℝ) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.abs_coord_le_offsetNorm <;> assumption
private theorem exp_neg_mul_offsetNorm_le_prod {u : ℝ} (hu : 0 < u) (z : Fin 4 → ℤ) :
    Real.exp (-(u * (offsetNorm z : ℝ))) ≤ ∏ i, expAbsDecay (u / 4) (z i) := by
  unfold expAbsDecay
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have h : ∀ i, u / 4 * |((z i : ℤ) : ℝ)| ≤ u / 4 * (offsetNorm z : ℝ) := fun i =>
    mul_le_mul_of_nonneg_left (abs_le_offsetNorm z i) (by positivity)
  have h2 : ∑ i : Fin 4, u / 4 * |((z i : ℤ) : ℝ)| ≤ ∑ _i : Fin 4, u / 4 * (offsetNorm z : ℝ) :=
    Finset.sum_le_sum fun i _ => h i
  have h3 : ∑ _i : Fin 4, u / 4 * (offsetNorm z : ℝ) = u * (offsetNorm z : ℝ) := by
    simp
    ring
  rw [Finset.sum_neg_distrib]
  linarith
private theorem sum_exp_neg_offsetNorm_le {u : ℝ} (hu : 0 < u) (s : Finset (Fin 4 → ℤ)) :
    ∑ z ∈ s, Real.exp (-(u * (offsetNorm z : ℝ))) ≤ latticeExpSum u := by
  classical
  have hu4 : 0 < u / 4 := by positivity
  let S : Finset ℤ := s.biUnion fun z => Finset.univ.image z
  have hsub : s ⊆ Fintype.piFinset fun _ : Fin 4 => S := by
    intro z hz
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_image_of_mem z (Finset.mem_univ i)⟩
  calc ∑ z ∈ s, Real.exp (-(u * (offsetNorm z : ℝ)))
      ≤ ∑ z ∈ s, ∏ i, expAbsDecay (u / 4) (z i) := Finset.sum_le_sum fun z _ => exp_neg_mul_offsetNorm_le_prod hu z
    _ ≤ ∑ z ∈ Fintype.piFinset (fun _ : Fin 4 => S), ∏ i, expAbsDecay (u / 4) (z i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ =>
          Finset.prod_nonneg fun i _ => expAbsDecay_nonneg _ _
    _ = ∏ _i : Fin 4, ∑ k ∈ S, expAbsDecay (u / 4) k :=
        (Finset.prod_univ_sum (fun _ : Fin 4 => S) fun _ k => expAbsDecay (u / 4) k).symm
    _ = (∑ k ∈ S, expAbsDecay (u / 4) k) ^ 4 := by simp
    _ ≤ latticeExpSum u := by
        unfold latticeExpSum
        exact pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => expAbsDecay_nonneg _ _)
          ((summable_expAbsDecay hu4).sum_le_tsum S fun k _ => expAbsDecay_nonneg _ _) 4
private def leastOffset (Y : TorusSite n) : Fin 4 → ℤ := fun i => (Y i).valMinAbs
private theorem siteOfInt_leastOffset [NeZero n] (Y : TorusSite n) : siteOfInt (leastOffset Y) = Y := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.siteOfInt_minimalCoords <;> assumption
private theorem leastOffset_injective [NeZero n] : Function.Injective (leastOffset (n := n)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.siteCoords_injective <;> assumption
private theorem supDist_zero_right (Y : TorusSite n) : _root_.YangMills.Construction.TorusFields.supDist Y 0 = offsetNorm (leastOffset Y) := by
  simp [_root_.YangMills.Construction.TorusFields.supDist, offsetNorm, leastOffset]
private theorem supDist_zero_left (Y : TorusSite n) : _root_.YangMills.Construction.TorusFields.supDist 0 Y = offsetNorm (leastOffset Y) := by
  simp only [_root_.YangMills.Construction.TorusFields.supDist, offsetNorm, leastOffset, Pi.zero_apply, zero_sub]
  congr 1
  funext i
  exact ZMod.natAbs_valMinAbs_neg (Y i)
private theorem natAbs_le_offsetNorm (z : Fin 4 → ℤ) (i : Fin 4) : (z i).natAbs ≤ offsetNorm z := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
private theorem leastOffset_siteOfInt [NeZero n] (z : Fin 4 → ℤ) (hz : 2 * offsetNorm z < n) :
    leastOffset (siteOfInt z : TorusSite n) = z := by
  funext i
  have h := natAbs_le_offsetNorm z i
  refine (ZMod.valMinAbs_spec (n := n) _ _).2 ⟨rfl, ?_⟩
  rw [Set.mem_Ioc]
  omega
private theorem sum_exp_neg_supDist_le [NeZero n] {u : ℝ} (hu : 0 < u) :
    ∑ Y : TorusSite n, Real.exp (-(u * (_root_.YangMills.Construction.TorusFields.supDist Y 0 : ℝ))) ≤ latticeExpSum u := by
  classical
  have h := sum_exp_neg_offsetNorm_le hu (Finset.univ.image (leastOffset (n := n)))
  rw [Finset.sum_image fun a _ b _ e => leastOffset_injective e] at h
  simpa only [supDist_zero_right] using h
private def offsetBox (R : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R
private theorem mem_offsetBox {R : ℕ} {z : Fin 4 → ℤ} : z ∈ offsetBox R ↔ offsetNorm z ≤ R := by apply _root_.YangMills.Construction.CellKernels.mem_centredBox_iff_supNorm <;> assumption
private theorem card_offsetBox (R : ℕ) : (offsetBox R).card = (2 * R + 1) ^ 4 := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.card_cubeBox <;> assumption
private theorem sum_eq_offsetBox_add_far [NeZero n] {R : ℕ} (hR : 2 * R < n) (f : TorusSite n → ℝ) :
    ∑ Y : TorusSite n, f Y =
      ∑ w ∈ offsetBox R, f (siteOfInt w) + ∑ Y ∈ Finset.univ.filter (fun Y : TorusSite n => R < _root_.YangMills.Construction.TorusFields.supDist Y 0), f Y := by
  classical
  have e1 : ∑ Y ∈ Finset.univ.filter (fun Y : TorusSite n => ¬ R < _root_.YangMills.Construction.TorusFields.supDist Y 0), f Y = ∑ w ∈ offsetBox R, f (siteOfInt w) := by
    refine Finset.sum_nbij' leastOffset siteOfInt ?_ ?_ ?_ ?_ ?_
    · intro Y hY
      have := (Finset.mem_filter.mp hY).2
      rw [mem_offsetBox, ← supDist_zero_right]
      omega
    · intro w hw
      have hw' := mem_offsetBox.mp hw
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [supDist_zero_right, leastOffset_siteOfInt w (by omega)]
      omega
    · intro Y _
      exact siteOfInt_leastOffset Y
    · intro w hw
      exact leastOffset_siteOfInt w (by have := mem_offsetBox.mp hw; omega)
    · intro Y _
      rw [siteOfInt_leastOffset]
  rw [← e1, add_comm]
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ f).symm
private theorem trivialField_isCold {s : ℝ} (hs : 0 < s) (n : ℕ) : IsCold s (trivialField n) := by apply _root_.YangMills.SharedProofs.p4747 <;> assumption
private theorem eventually_isCold [NeZero n] {s : ℝ} (hs : 0 < s) : ∀ᶠ W in 𝓝 (trivialField n), IsCold s W := by apply _root_.YangMills.SharedProofs.p23383 <;> assumption
private theorem areUnitVectors_pair {X : imaginaryQuaternions} (h : ‖X‖ = 1) : AreUnitVectors ![X, X] := by apply _root_.YangMills.Construction.RunningCouplingSlope.CenteredDensityMoment.areUnitVectors_pair <;> assumption
private def pairHessian (h : LocalDensity) (N : ℕ) (Y : TorusSite N) (e e' : TorusBond N) (X : imaginaryQuaternions) : ℝ :=
  mixedDeriv (h N Y) (trivialField N) ![e, e'] ![X, X]
private theorem iteratedFDeriv_two_finset_sum {ι : Type} (u : Finset ι) (g : ι → (Fin 2 → ℝ) → ℝ)
    (hg : ∀ i ∈ u, ContDiffAt ℝ (2 : ℕ) (g i) 0) :
    iteratedFDeriv ℝ 2 (fun σ => ∑ i ∈ u, g i σ) 0 = ∑ i ∈ u, iteratedFDeriv ℝ 2 (g i) 0 := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [iteratedFDeriv_const_of_ne (by norm_num) (0 : ℝ)]
    rfl
  | insert a s ha ih =>
    have h1 := hg a (Finset.mem_insert_self a s)
    have h2 : ∀ i ∈ s, ContDiffAt ℝ (2 : ℕ) (g i) 0 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have h3 : ContDiffAt ℝ (2 : ℕ) (fun σ => ∑ i ∈ s, g i σ) 0 := ContDiffAt.sum h2
    have e : (fun σ => ∑ i ∈ insert a s, g i σ) = g a + fun σ => ∑ i ∈ s, g i σ := by
      funext σ
      simp [Finset.sum_insert ha]
    rw [e, iteratedFDeriv_add_apply h1 h3, ih h2, Finset.sum_insert ha]
private theorem hessianAtTrivial_eq_sum {s s' c C : ℝ} {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {h : LocalDensity} {Hs : GaugeTotal}
    (hs : 0 < s) (hs' : 0 < s') (hB : HasStepDensityBounds s ℓ c C h) {N : ℕ} [NeZero N] (hN : 64 ≤ N)
    (hEq : ∀ V : TorusField N, IsCold s' V → centeredDensityTotal h N V = Hs N V)
    (e e' : TorusBond N) (X : imaginaryQuaternions) :
    hessianAtTrivial Hs N e e' X X = ∑ Y : TorusSite N, pairHessian h N Y e e' X := by
  have hc : ∀ Y : TorusSite N, ContDiffAt ℝ (2 : ℕ)
      (fun σ : Fin 2 → ℝ => h N Y (perturb ![e, e'] ![X, X] σ (trivialField N))) 0 := fun Y =>
    (hB.analyticAt N hN Y (trivialField N) (trivialField_isCold hs N) 2 _ _).contDiffAt
  have hne : NeZero N := inferInstance
  have ht : Tendsto (fun σ : Fin 2 → ℝ => perturb ![e, e'] ![X, X] σ (trivialField N)) (𝓝 0) (𝓝 (trivialField N)) := by
    have := (continuous_perturb ![e, e'] ![X, X] (trivialField N)).tendsto 0
    rwa [perturb_zero] at this
  have germ : (fun σ : Fin 2 → ℝ => Hs N (perturb ![e, e'] ![X, X] σ (trivialField N))) =ᶠ[𝓝 0]
      fun σ => ∑ Y : TorusSite N, (h N Y (perturb ![e, e'] ![X, X] σ (trivialField N)) - h N Y (trivialField N)) := by
    filter_upwards [ht.eventually (eventually_isCold hs')] with σ hσ
    rw [← hEq _ hσ]
    simp [centeredDensityTotal, NeZero.ne N, centered]
  unfold hessianAtTrivial mixedDeriv
  rw [(germ.iteratedFDeriv ℝ 2).eq_of_nhds, iteratedFDeriv_two_finset_sum _ _ fun Y _ => (hc Y).sub contDiffAt_const]
  rw [sum_apply]
  refine Finset.sum_congr rfl fun Y _ => ?_
  have e2 := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := 2) (x := (0 : Fin 2 → ℝ)) (hc Y)
    (contDiffAt_const (c := h N Y (trivialField N)))
  have e3 : (fun σ : Fin 2 → ℝ => h N Y (perturb ![e, e'] ![X, X] σ (trivialField N)) - h N Y (trivialField N)) =
      (fun σ : Fin 2 → ℝ => h N Y (perturb ![e, e'] ![X, X] σ (trivialField N))) -
        fun _ : Fin 2 → ℝ => h N Y (trivialField N) := rfl
  have e0 : iteratedFDeriv ℝ 2 (fun _ : Fin 2 → ℝ => h N Y (trivialField N)) = 0 :=
    iteratedFDeriv_const_of_ne (by norm_num) _
  rw [e3, e2, e0]
  simp [pairHessian, mixedDeriv]
private theorem abs_pairHessian_le {s c C : ℝ} {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {h : LocalDensity} (hs : 0 < s)
    (hB : HasStepDensityBounds s ℓ c C h) {N : ℕ} [NeZero N] (hN : 64 ≤ N) (Y : TorusSite N) (e e' : TorusBond N)
    {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    |pairHessian h N Y e e' X| ≤ C * Real.exp (-(c * (supportDiam Y ![e, e'] : ℝ))) :=
  hB.decay N hN Y (trivialField N) (trivialField_isCold hs N) 2 ![e, e'] ![X, X] (by norm_num) (by norm_num)
    (areUnitVectors_pair hX)
private theorem supDist_le_supportDiam {N : ℕ} (Y : TorusSite N) (e e' : TorusBond N) :
    _root_.YangMills.Construction.TorusFields.supDist Y e.1 ≤ supportDiam Y ![e, e'] := by
  refine le_max_of_le_left ?_
  exact Finset.le_sup (f := fun l : Fin 2 => _root_.YangMills.Construction.TorusFields.supDist Y ((![e, e'] : Fin 2 → TorusBond N) l).1) (Finset.mem_univ 0)
private theorem supDist_le_supportDiam' {N : ℕ} (Y : TorusSite N) (e e' : TorusBond N) :
    _root_.YangMills.Construction.TorusFields.supDist e'.1 e.1 ≤ supportDiam Y ![e, e'] := by
  refine le_max_of_le_right ?_
  refine le_trans ?_ (Finset.le_sup (f := fun l : Fin 2 => Finset.univ.sup fun l' : Fin 2 =>
    _root_.YangMills.Construction.TorusFields.supDist ((![e, e'] : Fin 2 → TorusBond N) l).1 ((![e, e'] : Fin 2 → TorusBond N) l').1) (Finset.mem_univ 1))
  exact Finset.le_sup (f := fun l' : Fin 2 => _root_.YangMills.Construction.TorusFields.supDist ((![e, e'] : Fin 2 → TorusBond N) 1).1
    ((![e, e'] : Fin 2 → TorusBond N) l').1) (Finset.mem_univ 0)
private theorem bondOffsetInBox_sub (z w : Fin 4 → ℤ) (d : Fin 4) {m : ℕ}
    (hm : offsetNorm z + offsetNorm w + 1 ≤ m) : TorusFields.BondOffsetInBox m (z - w, d) := by
  have hz := natAbs_le_offsetNorm z
  have hw := natAbs_le_offsetNorm w
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h1 := hz i
    have h2 := hw i
    rw [abs_le]
    simp only [Pi.sub_apply]
    omega
  · have h1 := hz i
    have h2 := hw i
    have h3 : |(Pi.single d (1 : ℤ) : Fin 4 → ℤ) i| ≤ 1 := by
      by_cases h : i = d
      · subst h
        simp
      · simp [h]
    rw [abs_le] at h3 ⊢
    simp only [Pi.add_apply, Pi.sub_apply]
    omega
private theorem bondFrom_shift {N : ℕ} (w z : Fin 4 → ℤ) (d : Fin 4) :
    bondFrom (siteOfInt w : TorusSite N) (z - w, d) = bondFrom (0 : TorusSite N) (z, d) := by
  simp only [bondFrom, zero_add, Prod.mk.injEq, and_true]
  funext i
  show ((w i : ℤ) : ZMod N) + (((z - w) i : ℤ) : ZMod N) = ((z i : ℤ) : ZMod N)
  simp
private theorem abs_pairHessian_sub_le {s c C : ℝ} {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {h : LocalDensity} (hs : 0 < s)
    (hB : HasStepDensityBounds s ℓ c C h) {N N' : ℕ} [NeZero N] [NeZero N'] (hN : 64 ≤ N) (hN' : 64 ≤ N')
    {m : ℕ} (hm : 2 * m + 2 < N) (hm' : 2 * m + 2 < N') (z w : Fin 4 → ℤ) (d : Fin 4)
    (hzw : offsetNorm z + offsetNorm w + 1 ≤ m) {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    |pairHessian h N (siteOfInt w) (bondFrom 0 (0, d)) (bondFrom 0 (z, d)) X -
        pairHessian h N' (siteOfInt w) (bondFrom 0 (0, d)) (bondFrom 0 (z, d)) X| ≤ C * Real.exp (-(c * (m : ℝ))) := by
  have h0 : offsetNorm (0 : Fin 4 → ℤ) = 0 := by simp [offsetNorm]
  have key := hB.local_comparison N N' hN hN' (siteOfInt w) (siteOfInt w) (trivialField N) (trivialField N') m hm hm'
    (trivialField_isCold hs N) (trivialField_isCold hs N') (fun _ _ => rfl) 2 ![(0 - w, d), (z - w, d)] ![X, X] le_rfl
    (by
      intro l
      fin_cases l
      · exact bondOffsetInBox_sub 0 w d (by omega)
      · exact bondOffsetInBox_sub z w d hzw)
    (areUnitVectors_pair hX)
  have e : ∀ {M : ℕ}, (fun l => bondFrom (siteOfInt w : TorusSite M)
      ((![(0 - w, d), (z - w, d)] : Fin 2 → (Fin 4 → ℤ) × Fin 4) l)) =
        ![bondFrom (0 : TorusSite M) (0, d), bondFrom (0 : TorusSite M) (z, d)] := by
    intro M
    funext l
    fin_cases l
    · exact bondFrom_shift w 0 d
    · exact bondFrom_shift w z d
  rw [e, e] at key
  exact key
private def torusKernel (h : LocalDensity) (N : ℕ) [NeZero N] (z : Fin 4 → ℤ) (X : imaginaryQuaternions) : ℝ :=
  ∑ Y : TorusSite N, pairHessian h N Y (bondFrom 0 (0, secondAxis)) (bondFrom 0 (z, secondAxis)) X
private theorem bondFrom_zero_fst {N : ℕ} (z : Fin 4 → ℤ) (d : Fin 4) :
    (bondFrom (0 : TorusSite N) (z, d)).1 = siteOfInt z := by
  simp [bondFrom]
private theorem bondFrom_zero_zero {N : ℕ} (d : Fin 4) : bondFrom (0 : TorusSite N) (0, d) = (0, d) := by
  simp only [bondFrom, zero_add, Prod.mk.injEq, and_true]
  funext i
  show (((0 : Fin 4 → ℤ) i : ℤ) : ZMod N) = 0
  simp
private theorem abs_far_sum_le {s c C : ℝ} {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {h : LocalDensity} (hs : 0 < s) (hc : 0 < c)
    (hC : 0 < C) (hB : HasStepDensityBounds s ℓ c C h) {N : ℕ} [NeZero N] (hN : 64 ≤ N) (R : ℕ) (z : Fin 4 → ℤ)
    {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    |∑ Y ∈ Finset.univ.filter (fun Y : TorusSite N => R < _root_.YangMills.Construction.TorusFields.supDist Y 0),
        pairHessian h N Y (bondFrom 0 (0, secondAxis)) (bondFrom 0 (z, secondAxis)) X| ≤
      C * Real.exp (-(c / 2 * (R : ℝ))) * latticeExpSum (c / 2) := by
  have hc2 : 0 < c / 2 := by positivity
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ Y ∈ Finset.univ.filter (fun Y : TorusSite N => R < _root_.YangMills.Construction.TorusFields.supDist Y 0),
      |pairHessian h N Y (bondFrom 0 (0, secondAxis)) (bondFrom 0 (z, secondAxis)) X| ≤
        C * Real.exp (-(c / 2 * (R : ℝ))) * Real.exp (-(c / 2 * (_root_.YangMills.Construction.TorusFields.supDist Y 0 : ℝ))) := by
    intro Y hY
    have hR : R < _root_.YangMills.Construction.TorusFields.supDist Y 0 := (Finset.mem_filter.mp hY).2
    have h1 := abs_pairHessian_le hs hB hN Y (bondFrom 0 (0, secondAxis)) (bondFrom 0 (z, secondAxis)) hX
    have h2 := supDist_le_supportDiam Y (bondFrom 0 (0, secondAxis)) (bondFrom 0 (z, secondAxis))
    rw [bondFrom_zero_zero] at h2
    have h2' : (supDist Y 0 : ℝ) ≤ (supportDiam Y ![bondFrom 0 (0, secondAxis),
        bondFrom 0 (z, secondAxis)] : ℝ) := by
      rw [bondFrom_zero_zero]
      exact_mod_cast h2
    have hR' : (R : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist Y 0 : ℝ) := by exact_mod_cast hR.le
    refine h1.trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun _ _ _ => (Real.exp_pos _).le).trans (sum_exp_neg_supDist_le hc2)
private theorem abs_torusKernel_sub_le {s c C : ℝ} {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {h : LocalDensity} (hs : 0 < s) (hc : 0 < c)
    (hC : 0 < C) (hB : HasStepDensityBounds s ℓ c C h) {N N' : ℕ} [NeZero N] [NeZero N'] (hN : 64 ≤ N)
    (hN' : 64 ≤ N') {R m : ℕ} (hR : 2 * R < N) (hR' : 2 * R < N') (hm : 2 * m + 2 < N) (hm' : 2 * m + 2 < N')
    (z : Fin 4 → ℤ) (hz : offsetNorm z + R + 1 ≤ m) {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    |torusKernel h N z X - torusKernel h N' z X| ≤
      ((2 * R + 1 : ℕ) : ℝ) ^ 4 * (C * Real.exp (-(c * (m : ℝ)))) +
        2 * (C * Real.exp (-(c / 2 * (R : ℝ))) * latticeExpSum (c / 2)) := by
  unfold torusKernel
  rw [sum_eq_offsetBox_add_far hR, sum_eq_offsetBox_add_far hR']
  have f1 := abs_far_sum_le hs hc hC hB hN R z hX
  have f2 := abs_far_sum_le hs hc hC hB hN' R z hX
  have near : |∑ w ∈ offsetBox R, pairHessian h N (siteOfInt w) (bondFrom 0 (0, secondAxis))
        (bondFrom 0 (z, secondAxis)) X - ∑ w ∈ offsetBox R, pairHessian h N' (siteOfInt w)
        (bondFrom 0 (0, secondAxis)) (bondFrom 0 (z, secondAxis)) X| ≤
      ((2 * R + 1 : ℕ) : ℝ) ^ 4 * (C * Real.exp (-(c * (m : ℝ)))) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (C * Real.exp (-(c * (m : ℝ)))) fun w hw => ?_).trans ?_
    · have hw' := mem_offsetBox.mp hw
      exact abs_pairHessian_sub_le hs hB hN hN' hm hm' z w secondAxis (by omega) hX
    · rw [card_offsetBox, nsmul_eq_mul]
      push_cast
      exact le_rfl
  rw [abs_le] at f1 f2 near ⊢
  constructor <;> linarith [f1.1, f1.2, f2.1, f2.2, near.1, near.2]
private theorem abs_torusKernel_le {s c C : ℝ} {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {h : LocalDensity} (hs : 0 < s) (hc : 0 < c)
    (hC : 0 < C) (hB : HasStepDensityBounds s ℓ c C h) {N : ℕ} [NeZero N] (hN : 64 ≤ N) (z : Fin 4 → ℤ)
    (hz : 2 * offsetNorm z < N) {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    |torusKernel h N z X| ≤ C * Real.exp (-(c / 2 * (offsetNorm z : ℝ))) * latticeExpSum (c / 2) := by
  have hc2 : 0 < c / 2 := by positivity
  unfold torusKernel
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ Y : TorusSite N,
      |pairHessian h N Y (bondFrom 0 (0, secondAxis)) (bondFrom 0 (z, secondAxis)) X| ≤
        C * Real.exp (-(c / 2 * (offsetNorm z : ℝ))) * Real.exp (-(c / 2 * (_root_.YangMills.Construction.TorusFields.supDist Y 0 : ℝ))) := by
    intro Y
    have h1 := abs_pairHessian_le hs hB hN Y (bondFrom 0 (0, secondAxis)) (bondFrom 0 (z, secondAxis)) hX
    have h2 := supDist_le_supportDiam Y (bondFrom 0 (0, secondAxis)) (bondFrom 0 (z, secondAxis))
    have h3 := supDist_le_supportDiam' Y (bondFrom 0 (0, secondAxis)) (bondFrom 0 (z, secondAxis))
    have e0 : (bondFrom (0 : TorusSite N) (0, secondAxis)).1 = 0 := by rw [bondFrom_zero_zero]
    rw [bondFrom_zero_fst, e0, supDist_zero_right, leastOffset_siteOfInt z hz] at h3
    rw [e0] at h2
    have h2' : (supDist Y 0 : ℝ) ≤ (supportDiam Y ![bondFrom 0 (0, secondAxis),
        bondFrom 0 (z, secondAxis)] : ℝ) := by exact_mod_cast h2
    have h3'' : (offsetNorm z : ℝ) ≤ (supportDiam Y ![bondFrom 0 (0, secondAxis),
        bondFrom 0 (z, secondAxis)] : ℝ) := by exact_mod_cast h3
    refine h1.trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
    nlinarith
  refine (Finset.sum_le_sum fun Y _ => hterm Y).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_exp_neg_supDist_le hc2) (by positivity)
private theorem inner_self_of_norm_eq_one {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    inner ℝ (X : ℍ[ℝ]) (X : ℍ[ℝ]) = 1 := by apply _root_.YangMills.SharedProofs.p81345 <;> assumption
private structure KernelData (s s' c C : ℝ) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (h : LocalDensity) (Hs : GaugeTotal)
    (K : LatticeBond → LatticeBond → ℝ) : Prop where
  hs : 0 < s
  hs' : 0 < s'
  hc : 0 < c
  hC : 0 < C
  hB : HasStepDensityBounds s ℓ c C h
  hEq : ∀ (N : ℕ) [NeZero N], 64 ≤ N → ∀ V : TorusField N, IsCold s' V → centeredDensityTotal h N V = Hs N V
  hlim : ∀ (b b' : LatticeBond) (X X' : imaginaryQuaternions),
    Tendsto (fun N => hessianAtTrivial Hs N (bondFrom 0 b) (bondFrom 0 b') X X') atTop
      (𝓝 (inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * K b b'))
variable {s s' c C : ℝ} {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {h : LocalDensity} {Hs : GaugeTotal} {K : LatticeBond → LatticeBond → ℝ}
private theorem KernelData.hessian_eq (S : KernelData s s' c C ℓ h Hs K) {N : ℕ} [NeZero N] (hN : 64 ≤ N)
    (z : Fin 4 → ℤ) (X : imaginaryQuaternions) :
    hessianAtTrivial Hs N (bondFrom 0 (0, secondAxis)) (bondFrom 0 (z, secondAxis)) X X =
      torusKernel h N z X :=
  hessianAtTrivial_eq_sum S.hs S.hs' S.hB hN (S.hEq N hN) _ _ X
private theorem KernelData.tendsto (S : KernelData s s' c C ℓ h Hs K) (z : Fin 4 → ℤ) {X : imaginaryQuaternions}
    (hX : ‖X‖ = 1) :
    Tendsto (fun N => hessianAtTrivial Hs N (bondFrom 0 (0, secondAxis)) (bondFrom 0 (z, secondAxis)) X X)
      atTop (𝓝 (K (0, secondAxis) (z, secondAxis))) := by
  have t := S.hlim (0, secondAxis) (z, secondAxis) X X
  rwa [inner_self_of_norm_eq_one hX, one_mul] at t
private theorem KernelData.abs_limit_le (S : KernelData s s' c C ℓ h Hs K) (z : Fin 4 → ℤ)
    {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    |K (0, secondAxis) (z, secondAxis)| ≤
      C * Real.exp (-(c / 2 * (offsetNorm z : ℝ))) * latticeExpSum (c / 2) := by
  refine le_of_tendsto (S.tendsto z hX).abs ?_
  filter_upwards [eventually_ge_atTop (max 64 (2 * offsetNorm z + 1))] with N hN
  have a1 := le_max_left 64 (2 * offsetNorm z + 1)
  have a2 := le_max_right 64 (2 * offsetNorm z + 1)
  haveI : NeZero N := ⟨by omega⟩
  rw [S.hessian_eq (by omega)]
  exact abs_torusKernel_le S.hs S.hc S.hC S.hB (by omega) z (by omega) hX
private theorem KernelData.abs_torusKernel_sub_limit_le (S : KernelData s s' c C ℓ h Hs K) {N : ℕ} [NeZero N]
    (hN : 64 ≤ N) {R m : ℕ} (hR : 2 * R < N) (hm : 2 * m + 2 < N) (z : Fin 4 → ℤ) (hz : offsetNorm z + R + 1 ≤ m)
    {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    |torusKernel h N z X - K (0, secondAxis) (z, secondAxis)| ≤
      ((2 * R + 1 : ℕ) : ℝ) ^ 4 * (C * Real.exp (-(c * (m : ℝ)))) +
        2 * (C * Real.exp (-(c / 2 * (R : ℝ))) * latticeExpSum (c / 2)) := by
  refine le_of_tendsto ((tendsto_const_nhds (x := torusKernel h N z X)).sub (S.tendsto z hX)).abs ?_
  filter_upwards [eventually_ge_atTop (max 64 (2 * m + 3 + 2 * R))] with N' hN'
  have a1 := le_max_left 64 (2 * m + 3 + 2 * R)
  have a2 := le_max_right 64 (2 * m + 3 + 2 * R)
  haveI : NeZero N' := ⟨by omega⟩
  rw [S.hessian_eq (by omega)]
  exact abs_torusKernel_sub_le S.hs S.hc S.hC S.hB hN (by omega) hR (by omega) hm (by omega) z hz hX
private theorem bondFrom_leastOffset [NeZero n] (y : TorusSite n) (d : Fin 4) :
    bondFrom (0 : TorusSite n) (leastOffset y, d) = (y, d) := by
  simp only [bondFrom, zero_add, siteOfInt_leastOffset]
private theorem KernelData.gaugeTotalMoment_eq (S : KernelData s s' c C ℓ h Hs K) [NeZero n] (hn : 64 ≤ n)
    (X : imaginaryQuaternions) :
    gaugeTotalMoment Hs n X = ∑ z ∈ offsetBox (2 * momentCutoff n),
      -(1 / 2) * torusKernel h n z X * ((z 0 : ℤ) : ℝ) ^ 2 := by
  classical
  have hr : 4 * momentCutoff n < n := by
    unfold momentCutoff
    omega
  unfold gaugeTotalMoment kernelSecondMoment
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_nbij' leastOffset siteOfInt ?_ ?_ ?_ ?_ ?_
  · intro y hy
    have := (Finset.mem_filter.mp hy).2
    rw [mem_offsetBox, ← supDist_zero_left]
    exact this
  · intro w hw
    have hw' := mem_offsetBox.mp hw
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [supDist_zero_left, leastOffset_siteOfInt w (by omega)]
    exact hw'
  · intro y _
    exact siteOfInt_leastOffset y
  · intro w hw
    exact leastOffset_siteOfInt w (by have := mem_offsetBox.mp hw; omega)
  · intro y _
    have e := S.hessian_eq hn (leastOffset y) X
    rw [bondFrom_leastOffset, bondFrom_zero_zero] at e
    beta_reduce
    rw [e]
    have e2 : firstCoordDiff 0 y = leastOffset y 0 := by
      simp [firstCoordDiff, leastOffset]
    rw [e2]
    ring
private def momentConst (c : ℝ) : ℝ :=
  32 * (160 / c) ^ 10 * (1 + 2 * latticeExpSum (c / 2)) + 64 / c ^ 2 * latticeExpSum (c / 2) * latticeExpSum (c / 4)
private theorem momentConst_pos {c : ℝ} (hc : 0 < c) : 0 < momentConst c := by
  unfold momentConst
  have h1 := latticeExpSum_nonneg (c / 2)
  have h2 := latticeExpSum_nonneg (c / 4)
  positivity
private theorem pow_ten_le_exp {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    x ^ 10 ≤ 32 * (160 / c) ^ 10 * Real.exp (c / 32 * x) := by
  have hy : 0 ≤ c / 160 * x := by positivity
  have h1 := Real.quadratic_le_exp_of_nonneg hy
  have h2 : (c / 160 * x) ^ 2 / 2 ≤ Real.exp (c / 160 * x) := by nlinarith
  have h3 : ((c / 160 * x) ^ 2 / 2) ^ 5 ≤ Real.exp (c / 160 * x) ^ 5 :=
    pow_le_pow_left₀ (by positivity) h2 5
  have h4 : Real.exp (c / 160 * x) ^ 5 = Real.exp (c / 32 * x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h4] at h3
  have h5 : x ^ 10 = 32 * (160 / c) ^ 10 * ((c / 160 * x) ^ 2 / 2) ^ 5 := by
    field_simp
    ring
  rw [h5]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)
private theorem sq_le_exp {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) : t ^ 2 ≤ 128 / c ^ 2 * Real.exp (c / 8 * t) := by
  have hy : 0 ≤ c / 8 * t := by positivity
  have h1 := Real.quadratic_le_exp_of_nonneg hy
  have h2 : (c / 8 * t) ^ 2 / 2 ≤ Real.exp (c / 8 * t) := by nlinarith
  have h5 : t ^ 2 = 128 / c ^ 2 * ((c / 8 * t) ^ 2 / 2) := by
    field_simp
    ring
  rw [h5]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)
private theorem KernelData.abs_box_sum_sub_le (S : KernelData s s' c C ℓ h Hs K) {b : ℝ}
    (hsum : HasSum (secondMomentTerm K) b) (r : ℕ) {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    |∑ z ∈ offsetBox (2 * r), secondMomentTerm K z - b| ≤
      64 / c ^ 2 * latticeExpSum (c / 2) * latticeExpSum (c / 4) * C * Real.exp (-(c / 4 * (r : ℝ))) := by
  classical
  have hc := S.hc
  have hC := S.hC
  have hc4 : 0 < c / 4 := by positivity
  have ht : Tendsto (fun u : Finset (Fin 4 → ℤ) => ∑ z ∈ u, secondMomentTerm K z) atTop (𝓝 b) := by
    have := hsum
    unfold HasSum at this
    rwa [SummationFilter.unconditional_filter] at this
  have ht' := (tendsto_const_nhds (x := ∑ z ∈ offsetBox (2 * r), secondMomentTerm K z)).sub ht
  refine le_of_tendsto ht'.abs ?_
  have G₁ := latticeExpSum_nonneg (c / 2)
  filter_upwards [eventually_ge_atTop (offsetBox (2 * r))] with u hu
  have hterm : ∀ z ∈ u \ offsetBox (2 * r), |secondMomentTerm K z| ≤
      64 / c ^ 2 * latticeExpSum (c / 2) * C * Real.exp (-(c / 4 * (r : ℝ))) *
        Real.exp (-(c / 4 * (offsetNorm z : ℝ))) := by
    intro z hz
    have hz' : ¬ offsetNorm z ≤ 2 * r := fun hh => (Finset.mem_sdiff.mp hz).2 (mem_offsetBox.mpr hh)
    have hz2 : 2 * (r : ℝ) ≤ (offsetNorm z : ℝ) := by
      have : 2 * r ≤ offsetNorm z := by omega
      exact_mod_cast this
    set t : ℝ := (offsetNorm z : ℝ) with htdef
    have t0 : 0 ≤ t := Nat.cast_nonneg _
    have hk := S.abs_limit_le z hX
    have h0 : ((z 0 : ℤ) : ℝ) ^ 2 ≤ t ^ 2 := by
      have := abs_le_offsetNorm z 0
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have hq := sq_le_exp hc t0
    have hm : |secondMomentTerm K z| =
        1 / 2 * |K (0, secondAxis) (z, secondAxis)| * ((z 0 : ℤ) : ℝ) ^ 2 := by
      unfold secondMomentTerm
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (((z 0 : ℤ) : ℝ)))]
      norm_num
    rw [hm]
    calc 1 / 2 * |K (0, secondAxis) (z, secondAxis)| * ((z 0 : ℤ) : ℝ) ^ 2
        ≤ 1 / 2 * (C * Real.exp (-(c / 2 * t)) * latticeExpSum (c / 2)) *
            (128 / c ^ 2 * Real.exp (c / 8 * t)) := by
          refine mul_le_mul ?_ (h0.trans hq) (sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hk (by norm_num)
      _ = 64 / c ^ 2 * latticeExpSum (c / 2) * C * (Real.exp (-(c / 2 * t)) * Real.exp (c / 8 * t)) := by ring
      _ ≤ 64 / c ^ 2 * latticeExpSum (c / 2) * C *
            (Real.exp (-(c / 4 * (r : ℝ))) * Real.exp (-(c / 4 * t))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith
      _ = 64 / c ^ 2 * latticeExpSum (c / 2) * C * Real.exp (-(c / 4 * (r : ℝ))) *
            Real.exp (-(c / 4 * t)) := by ring
  have hsplit : ∑ z ∈ offsetBox (2 * r), secondMomentTerm K z - ∑ z ∈ u, secondMomentTerm K z =
      - ∑ z ∈ u \ offsetBox (2 * r), secondMomentTerm K z := by
    have := Finset.sum_sdiff (f := secondMomentTerm K) hu
    linarith
  rw [hsplit, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.mul_sum]
  have hs := sum_exp_neg_offsetNorm_le hc4 (u \ offsetBox (2 * r))
  calc 64 / c ^ 2 * latticeExpSum (c / 2) * C * Real.exp (-(c / 4 * (r : ℝ))) *
        ∑ z ∈ u \ offsetBox (2 * r), Real.exp (-(c / 4 * (offsetNorm z : ℝ)))
      ≤ 64 / c ^ 2 * latticeExpSum (c / 2) * C * Real.exp (-(c / 4 * (r : ℝ))) * latticeExpSum (c / 4) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring
private theorem KernelData.abs_gaugeTotalMoment_sub_box_le (S : KernelData s s' c C ℓ h Hs K) [NeZero n]
    (hn : 64 ≤ n) {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    |gaugeTotalMoment Hs n X - ∑ z ∈ offsetBox (2 * momentCutoff n), secondMomentTerm K z| ≤
      32 * (160 / c) ^ 10 * (1 + 2 * latticeExpSum (c / 2)) * C * Real.exp (-(c / 32 * (n : ℝ))) := by
  have hc := S.hc
  have hC := S.hC
  set r := momentCutoff n with hr
  have hr' : r = n / 16 := rfl
  set R := n / 4 with hRdef
  set m := R + 2 * r + 1 with hmdef
  have G₁ := latticeExpSum_nonneg (c / 2)
  set E : ℝ := ((2 * R + 1 : ℕ) : ℝ) ^ 4 * (C * Real.exp (-(c * (m : ℝ)))) +
      2 * (C * Real.exp (-(c / 2 * (R : ℝ))) * latticeExpSum (c / 2)) with hE
  have hnn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have n0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  rw [S.gaugeTotalMoment_eq hn X, ← Finset.sum_sub_distrib]
  have hterm : ∀ z ∈ offsetBox (2 * r),
      |-(1 / 2) * torusKernel h n z X * ((z 0 : ℤ) : ℝ) ^ 2 - secondMomentTerm K z| ≤ (n : ℝ) ^ 2 * E := by
    intro z hz
    have hz' := mem_offsetBox.mp hz
    have hk := S.abs_torusKernel_sub_limit_le hn (R := R) (m := m) (by omega) (by omega) z (by omega) hX
    have e : -(1 / 2) * torusKernel h n z X * ((z 0 : ℤ) : ℝ) ^ 2 - secondMomentTerm K z =
        -(1 / 2) * ((z 0 : ℤ) : ℝ) ^ 2 * (torusKernel h n z X - K (0, secondAxis) (z, secondAxis)) := by
      unfold secondMomentTerm
      ring
    have h0 : ((z 0 : ℤ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have h1 := abs_le_offsetNorm z 0
      have h2 : (offsetNorm z : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (by omega : offsetNorm z ≤ n)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
    rw [e, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (((z 0 : ℤ) : ℝ)))]
    have hh : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
    rw [hh]
    have hnsq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    nlinarith [abs_nonneg (torusKernel h n z X - K (0, secondAxis) (z, secondAxis)),
      sq_nonneg (((z 0 : ℤ) : ℝ)),
      mul_le_mul h0 hk (abs_nonneg _) hnsq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ((n : ℝ) ^ 2 * E) hterm).trans ?_
  rw [card_offsetBox, nsmul_eq_mul]
  have hc1 : (((2 * (2 * r) + 1) ^ 4 : ℕ) : ℝ) ≤ (n : ℝ) ^ 4 := by
    have : 2 * (2 * r) + 1 ≤ n := by omega
    have h2 : (((2 * (2 * r) + 1 : ℕ)) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    push_cast at h2 ⊢
    exact pow_le_pow_left₀ (by positivity) h2 4
  have hR1 : (((2 * R + 1 : ℕ)) : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := by
    have h2 : (((2 * R + 1 : ℕ)) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 * R + 1 ≤ n)
    exact pow_le_pow_left₀ (by positivity) h2 4
  set e1 : ℝ := Real.exp (-(c / 2 * (R : ℝ))) with he1
  have e1pos : 0 < e1 := Real.exp_pos _
  have hmR : Real.exp (-(c * (m : ℝ))) ≤ e1 := by
    apply Real.exp_le_exp.mpr
    have : (R : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : R ≤ m)
    nlinarith
  have hEle : E ≤ (n : ℝ) ^ 4 * ((1 + 2 * latticeExpSum (c / 2)) * C * e1) := by
    have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hnn
    have a1 : ((2 * R + 1 : ℕ) : ℝ) ^ 4 * (C * Real.exp (-(c * (m : ℝ)))) ≤ (n : ℝ) ^ 4 * (C * e1) :=
      mul_le_mul hR1 (mul_le_mul_of_nonneg_left hmR hC.le) (by positivity) (by positivity)
    have a2 : 2 * (C * e1 * latticeExpSum (c / 2)) ≤ (n : ℝ) ^ 4 * (2 * (C * e1 * latticeExpSum (c / 2))) :=
      le_mul_of_one_le_left (by positivity) hn4
    have : (n : ℝ) ^ 4 * ((1 + 2 * latticeExpSum (c / 2)) * C * e1) =
        (n : ℝ) ^ 4 * (C * e1) + (n : ℝ) ^ 4 * (2 * (C * e1 * latticeExpSum (c / 2))) := by ring
    rw [this, hE]
    exact add_le_add a1 a2
  have hexp : e1 ≤ Real.exp (-(c / 16 * (n : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have : (n : ℝ) ≤ 8 * (R : ℝ) := by exact_mod_cast (by omega : n ≤ 8 * R)
    nlinarith
  have hpow := pow_ten_le_exp hc n0
  have hA : 0 ≤ (1 + 2 * latticeExpSum (c / 2)) * C := by positivity
  calc (((2 * (2 * r) + 1) ^ 4 : ℕ) : ℝ) * ((n : ℝ) ^ 2 * E)
      ≤ (n : ℝ) ^ 4 * ((n : ℝ) ^ 2 * ((n : ℝ) ^ 4 * ((1 + 2 * latticeExpSum (c / 2)) * C * e1))) := by
        refine mul_le_mul hc1 (mul_le_mul_of_nonneg_left hEle (by positivity)) (by positivity) (by positivity)
    _ = (n : ℝ) ^ 10 * ((1 + 2 * latticeExpSum (c / 2)) * C) * e1 := by ring
    _ ≤ (32 * (160 / c) ^ 10 * Real.exp (c / 32 * (n : ℝ))) * ((1 + 2 * latticeExpSum (c / 2)) * C) *
          Real.exp (-(c / 16 * (n : ℝ))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hpow hA) hexp e1pos.le (by positivity)
    _ = 32 * (160 / c) ^ 10 * (1 + 2 * latticeExpSum (c / 2)) * C *
          (Real.exp (c / 32 * (n : ℝ)) * Real.exp (-(c / 16 * (n : ℝ)))) := by ring
    _ = 32 * (160 / c) ^ 10 * (1 + 2 * latticeExpSum (c / 2)) * C * Real.exp (-(c / 32 * (n : ℝ))) := by
        rw [← Real.exp_add]
        congr 2
        ring
private theorem KernelData.abs_gaugeTotalMoment_sub_le (S : KernelData s s' c C ℓ h Hs K) {b : ℝ}
    (hsum : HasSum (secondMomentTerm K) b) [NeZero n] (hn : 64 ≤ n) {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    |gaugeTotalMoment Hs n X - b| ≤ momentConst c * C * Real.exp (-(c / 128 * (n : ℝ))) := by
  have hc := S.hc
  have hC := S.hC
  have h1 := S.abs_gaugeTotalMoment_sub_box_le hn hX
  have h2 := S.abs_box_sum_sub_le hsum (momentCutoff n) hX
  have G₁ := latticeExpSum_nonneg (c / 2)
  have G₂ := latticeExpSum_nonneg (c / 4)
  have e1 : Real.exp (-(c / 32 * (n : ℝ))) ≤ Real.exp (-(c / 128 * (n : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have e2 : Real.exp (-(c / 4 * (momentCutoff n : ℝ))) ≤ Real.exp (-(c / 128 * (n : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have : (n : ℝ) ≤ 32 * (momentCutoff n : ℝ) := by
      have : n ≤ 32 * momentCutoff n := by
        unfold momentCutoff
        omega
      exact_mod_cast this
    nlinarith
  have e3 := mul_le_mul_of_nonneg_left e1
    (show 0 ≤ 32 * (160 / c) ^ 10 * (1 + 2 * latticeExpSum (c / 2)) * C by positivity)
  have e4 := mul_le_mul_of_nonneg_left e2
    (show 0 ≤ 64 / c ^ 2 * latticeExpSum (c / 2) * latticeExpSum (c / 4) * C by positivity)
  have e5 : momentConst c * C * Real.exp (-(c / 128 * (n : ℝ))) =
      32 * (160 / c) ^ 10 * (1 + 2 * latticeExpSum (c / 2)) * C * Real.exp (-(c / 128 * (n : ℝ))) +
        64 / c ^ 2 * latticeExpSum (c / 2) * latticeExpSum (c / 4) * C * Real.exp (-(c / 128 * (n : ℝ))) := by
    unfold momentConst
    ring
  rw [e5]
  have tri : |gaugeTotalMoment Hs n X - b| ≤
      |gaugeTotalMoment Hs n X - ∑ z ∈ offsetBox (2 * momentCutoff n), secondMomentTerm K z| +
      |∑ z ∈ offsetBox (2 * momentCutoff n), secondMomentTerm K z - b| := abs_sub_le _ _ _
  linarith
private theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
end GaugeTotalMoment
open GaugeTotalMoment in
private theorem abs_gaugeTotalMoment_sub_le_of_densitySum (hS : StepTotalEqDensitySum)
    (hL : StepDensityIsLocal.Claim) (hT : StepGaugeTotalIsGaugeTotal) (hCo : LocalDensityCoefficient.Claim)
    (hN : CoefficientFromDensity.Claim) (hU : StepCoefficientEqualsDensityValue)
    {T : ParameterAssignment} (hD : T.Admissible) {c C : ℝ} (hc : 0 < c) (hC : 0 < C) (t : ℕ)
    (hB : HasStepDensityBounds T.threshold (T.stepParameters T.floorMin) c C (paramStepDensity T t)) {b : ℝ}
    (hb : IsStepCoefficient T.coupling T.side t b) (n : ℕ) [NeZero n] (X : imaginaryQuaternions) (hn : 64 ≤ n)
    (hX : ‖X‖ = 1) :
    |gaugeTotalMoment (stepGaugeTotal T.coupling T.ρA T.side t) n X - b| ≤
      momentConst c * C * Real.exp (-(c / 128 * (n : ℝ))) := by
  obtain ⟨hloc, hev⟩ := hL T hD t
  have hρ0 : 0 < T.ρA := hD.chain.2.2.2.1
  have hρ1 : T.ρA ≤ 1 := hD.chain.2.2.2.2.1
  have htot := hT T.coupling (by linarith [hD.a_ge]) T.side ⟨hD.L_odd, by
    have := hD.L_ge
    have h40 : (13 : ℕ) ≤ 2 ^ 40 := by norm_num
    omega⟩ t T.ρA hρ0 hρ1
  obtain ⟨b', hb'⟩ := hCo _ _ hloc htot hev
  have hs1 := hN _ _ b' hloc hb' hev
  obtain ⟨b₀, hb₀, -, hs2⟩ := hU T hD t
  have e1 : b' = b₀ := hs1.unique hs2
  have e2 : b = b₀ := tendsto_nhds_unique (hb 1 1 quaternionI one_pos le_rfl le_rfl norm_quaternionI)
    (hb₀ 1 1 quaternionI one_pos le_rfl le_rfl norm_quaternionI)
  obtain ⟨K, hK, hsum⟩ := hb'
  have hσ := hD.σ_pos
  have S : KernelData T.threshold (9 / 8 * T.threshold) c C (T.stepParameters T.floorMin) (paramStepDensity T t)
      (stepGaugeTotal T.coupling T.ρA T.side t) K :=
    { hs := hσ
      hs' := by positivity
      hc := hc
      hC := hC
      hB := hB
      hEq := fun N _ hN' V hV => hS T hD t N V hN' hV
      hlim := hK.tendsto_kernel }
  rw [e2, ← e1]
  exact S.abs_gaugeTotalMoment_sub_le hsum hn hX
open GaugeTotalMoment in
theorem GaugeTotalMoment.gaugeTotalMomentNearStepCoefficient_of_parts (hD : StepDensityBoundsAtFixedParameters)
    (hS : StepTotalEqDensitySum) (hL : StepDensityIsLocal.Claim)
    (hT : StepGaugeTotalIsGaugeTotal) (hCo : LocalDensityCoefficient.Claim)
    (hN : CoefficientFromDensity.Claim) (hU : StepCoefficientEqualsDensityValue) :
    GaugeTotalMomentNearStepCoefficient := by
  classical
  obtain ⟨rt₀, cD, -, hcD, H⟩ := hD
  choose! Cf hCf using H
  let Cof : ChainParameters → ℝ := fun l =>
    if e : ∃ T : ParameterAssignment, T.Admissible ∧ T.toChainParameters = l then momentConst (cD l) * Cf e.choose else 1
  refine ⟨fun _ => 1, Cof, fun l => cD l / 128, fun _ => one_pos, fun l => ?_, fun l => ?_, ?_⟩
  · by_cases e : ∃ T : ParameterAssignment, T.Admissible ∧ T.toChainParameters = l
    · simp only [Cof, dif_pos e]
      exact mul_pos (momentConst_pos (hcD l)) (hCf _ e.choose_spec.1).1
    · simp only [Cof, dif_neg e]
      exact one_pos
  · have := hcD l
    positivity
  · intro T hDr _ t b hb n _ X hn hX
    have e : ∃ T' : ParameterAssignment, T'.Admissible ∧ T'.toChainParameters = T.toChainParameters := ⟨T, hDr, rfl⟩
    obtain ⟨hD₀, e₀⟩ := e.choose_spec
    have hC₀ := hCf _ hD₀
    have ea : e.choose.coupling = T.coupling := congrArg ChainParameters.coupling e₀
    have eρ : e.choose.ρA = T.ρA := congrArg ChainParameters.ρA e₀
    have eL : e.choose.side = T.side := congrArg ChainParameters.side e₀
    have key := abs_gaugeTotalMoment_sub_le_of_densitySum hS hL hT hCo hN hU hD₀ (hcD T.toChainParameters) hC₀.1 t
      (by
        have := hC₀.2.1 e.choose.floorMin t le_rfl
        rwa [e₀] at this)
      (by rwa [ea, eL]) n X hn hX
    rw [ea, eρ, eL] at key
    simp only [Cof, dif_pos e]
    exact key
end RunningCouplingSlope
end YangMills.Construction
end

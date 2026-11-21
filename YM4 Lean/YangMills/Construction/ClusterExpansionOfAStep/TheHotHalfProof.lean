import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionNearAFlatTopProof
import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheMarkedIntegralOfAllBlocks
import YangMills.Construction.ClusterExpansionOfAStep.DerivativesOfAMarkedIntegral
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParametersProof
import YangMills.Construction.ClusterExpansionOfAStep.GasAtColdTops
import YangMills.Construction.ClusterExpansionOfAStep.GasDensityOfAGroundIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreCarried
import YangMills.Construction.ClusterExpansionOfAStep.RandomOrderOfBlocks
import YangMills.Construction.ClusterExpansionOfAStep.TheHotHalf
import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import YangMills.Construction.ColdStepAtMirrorFrames.FirstDerivativeOfAnExpansionAtOneProof
import YangMills.Construction.ColdStepAtMirrorFrames.MixedDerivativeBetweenSizes
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep.BlockDensities
open BlockAverages TorusFields TorusLumps StepSettings RenormalizationStepParameters MarkedIntegrals BlockOrder ColdStepAtMirrorFrames
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem iteratedFDeriv_two_swap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F}
    (hg : ContDiff ℝ 2 g) (z : E) (m : Fin 2 → E) :
    iteratedFDeriv ℝ 2 g z (m ∘ Equiv.swap 0 1) = iteratedFDeriv ℝ 2 g z m := by
  have hs : IsSymmSndFDerivAt ℝ g z :=
    hg.contDiffAt.isSymmSndFDerivAt (by simp)
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simpa using hs (m 1) (m 0)
theorem iteratedFDeriv_three_perm {f : E → ℝ} (hf : ContDiff ℝ 3 f) (z : E) (σ : Equiv.Perm (Fin 3))
    (m : Fin 3 → E) : iteratedFDeriv ℝ 3 f z (m ∘ σ) = iteratedFDeriv ℝ 3 f z m := by
  have h01 : ∀ m : Fin 3 → E, iteratedFDeriv ℝ 3 f z (m ∘ Equiv.swap 0 1) = iteratedFDeriv ℝ 3 f z m := by
    intro m
    have hd2 : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (m := 2) (by norm_num)
    have a : ∀ m : Fin 3 → E, iteratedFDeriv ℝ 3 f z m =
        iteratedFDeriv ℝ 2 (fderiv ℝ f) z (Fin.init m) (m (Fin.last 2)) :=
      fun m => iteratedFDeriv_succ_apply_right m
    have := iteratedFDeriv_two_swap hd2 z (Fin.init m)
    have e : Fin.init (m ∘ Equiv.swap (0 : Fin 3) 1) = (Fin.init m) ∘ Equiv.swap (0 : Fin 2) 1 := by
      funext i
      fin_cases i <;> simp [Fin.init]
    have l : (m ∘ Equiv.swap (0 : Fin 3) 1) (Fin.last 2) = m (Fin.last 2) := by
      simp [Equiv.swap_apply_def, Fin.last]
    rw [a, a m, e, l, this]
  have h12 : ∀ m : Fin 3 → E, iteratedFDeriv ℝ 3 f z (m ∘ Equiv.swap 1 2) = iteratedFDeriv ℝ 3 f z m := by
    intro m
    have h2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 f) z :=
      ((hf.differentiable_iteratedFDeriv (m := 2) (by norm_num)) z)
    have a : ∀ m : Fin 3 → E, iteratedFDeriv ℝ 3 f z m =
        (fderiv ℝ (iteratedFDeriv ℝ 2 f) z (m 0)) (Fin.tail m) :=
      fun m => iteratedFDeriv_succ_apply_left m
    have key : ∀ w : Fin 2 → E, (fderiv ℝ (iteratedFDeriv ℝ 2 f) z (m 0)) w =
        fderiv ℝ (fun y => iteratedFDeriv ℝ 2 f y w) z (m 0) := by
      intro w
      have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ w).hasFDerivAt.comp z hd.hasFDerivAt
      have h' : fderiv ℝ (fun y => iteratedFDeriv ℝ 2 f y w) z = _ := this.fderiv
      rw [h']
      rfl
    have e : Fin.tail (m ∘ Equiv.swap (1 : Fin 3) 2) = (Fin.tail m) ∘ Equiv.swap (0 : Fin 2) 1 := by
      funext i
      fin_cases i <;> simp [Fin.tail]
    have l : (m ∘ Equiv.swap (1 : Fin 3) 2) 0 = m 0 := by simp [Equiv.swap_apply_def]
    have hfun : (fun y => iteratedFDeriv ℝ 2 f y (Fin.tail m ∘ Equiv.swap (0 : Fin 2) 1)) =
        fun y => iteratedFDeriv ℝ 2 f y (Fin.tail m) :=
      funext fun y => iteratedFDeriv_two_swap h2 y (Fin.tail m)
    rw [a, a m, l, key, key, e, hfun]
  have hP : ∀ σ : Equiv.Perm (Fin 3), ∀ m : Fin 3 → E,
      iteratedFDeriv ℝ 3 f z (m ∘ σ) = iteratedFDeriv ℝ 3 f z m := by
    intro σ
    have hmem : σ ∈ Submonoid.closure (Set.range fun i : Fin 2 => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hmem using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro m
      fin_cases i
      · exact h01 m
      · exact h12 m
    | one => intro m; rfl
    | mul x y _ _ ihx ihy =>
      intro m
      have : m ∘ ⇑(x * y) = (m ∘ x) ∘ y := by funext i; simp
      rw [this, ihy, ihx]
  exact hP σ m
theorem iteratedFDeriv_perm_of_le_three {f : E → ℝ} (hf : ContDiff ℝ 3 f) (z : E) (j : ℕ) (hj : j ≤ 3)
    (σ : Equiv.Perm (Fin j)) (m : Fin j → E) :
    iteratedFDeriv ℝ j f z (m ∘ σ) = iteratedFDeriv ℝ j f z m := by
  interval_cases j
  · congr 1; funext i; exact i.elim0
  · have : σ = 1 := Subsingleton.elim _ _
    simp [this]
  · have h2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
    rcases (by
      have : ∀ τ : Equiv.Perm (Fin 2), τ = 1 ∨ τ = Equiv.swap 0 1 := by decide
      exact this σ) with rfl | rfl
    · simp
    · exact iteratedFDeriv_two_swap h2 z m
  · exact iteratedFDeriv_three_perm hf z σ m
end
section
variable {n : ℕ} [NeZero n]
instance isProbabilityMeasure_randomOrderLaw : IsProbabilityMeasure (randomOrderLaw n) := by
  unfold randomOrderLaw
  have : ∀ _ : TorusSite n, IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := fun _ =>
    ⟨by simp⟩
  infer_instance
theorem randomOrderLaw_tie (i j : TorusSite n) (hij : i ≠ j) : randomOrderLaw n {u | u i = u j} = 0 := by
  have hle : randomOrderLaw n ≤ (volume : Measure (TorusSite n → ℝ)) := by
    unfold randomOrderLaw
    rw [volume_pi]
    have : (Measure.pi fun _ : TorusSite n => (volume.restrict (Set.Icc (0 : ℝ) 1))) =
        (Measure.pi fun _ : TorusSite n => (volume : Measure ℝ)).restrict
          (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1) :=
      (Measure.restrict_pi_pi _ _).symm
    rw [this]
    exact Measure.restrict_le_self
  refine le_antisymm ((hle _).trans ?_) zero_le
  let f : (TorusSite n → ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.proj (R := ℝ) (φ := fun _ : TorusSite n => ℝ) i -
      LinearMap.proj (R := ℝ) (φ := fun _ : TorusSite n => ℝ) j
  have hset : {u : TorusSite n → ℝ | u i = u j} = (LinearMap.ker f : Set (TorusSite n → ℝ)) := by
    ext u
    simp [f, sub_eq_zero]
  rw [hset]
  refine le_of_eq (Measure.addHaar_submodule _ _ ?_)
  intro htop
  have : (Pi.single i 1 : TorusSite n → ℝ) ∈ LinearMap.ker f := by rw [htop]; trivial
  simp [f, hij.symm] at this
theorem ae_injective_randomOrderLaw : ∀ᵐ u ∂(randomOrderLaw n), Function.Injective u := by
  have h : ∀ i j : TorusSite n, i ≠ j → ∀ᵐ u ∂(randomOrderLaw n), u i ≠ u j := by
    intro i j hij
    exact measure_eq_zero_iff_ae_notMem.mp (randomOrderLaw_tie i j hij)
  have h2 : ∀ᵐ u ∂(randomOrderLaw n), ∀ i j : TorusSite n, i ≠ j → u i ≠ u j := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · filter_upwards [h i j hij] with u hu _ using hu
  filter_upwards [h2] with u hu i j hij
  by_contra hne
  exact hu i j hne hij
theorem measurableSet_precedingBlocks_eq (Y : TorusSite n) (A : Finset (TorusSite n)) :
    MeasurableSet {u : TorusSite n → ℝ | MarkedIntegrals.precedingBlocks u Y = A} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GroundDensityMeasurability.measurableSet_precedingBlocks_eq <;> assumption
def precedingWeight (Y : TorusSite n) (A : Finset (TorusSite n)) : ℝ :=
  (randomOrderLaw n).real {u | MarkedIntegrals.precedingBlocks u Y = A}
theorem precedingWeight_nonneg (Y : TorusSite n) (A : Finset (TorusSite n)) : 0 ≤ precedingWeight Y A :=
  measureReal_nonneg
theorem integral_precedingBlocks (Y : TorusSite n) (F : Finset (TorusSite n) → ℝ) :
    ∫ u, F (MarkedIntegrals.precedingBlocks u Y) ∂(randomOrderLaw n) = ∑ A, precedingWeight Y A * F A := by
  have hdec : ∀ u : TorusSite n → ℝ, F (MarkedIntegrals.precedingBlocks u Y) =
      ∑ A, Set.indicator {u | MarkedIntegrals.precedingBlocks u Y = A} (fun _ => F A) u := by
    intro u
    rw [Finset.sum_eq_single (MarkedIntegrals.precedingBlocks u Y)]
    · simp [Set.indicator]
    · intro A _ hA
      simp [Set.indicator, Ne.symm hA]
    · simp
  simp_rw [hdec]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun A _ => ?_
    rw [integral_indicator (measurableSet_precedingBlocks_eq Y A)]
    simp [precedingWeight, mul_comm, Measure.real]
  · intro A _
    exact (integrable_const (F A)).indicator (measurableSet_precedingBlocks_eq Y A)
theorem sum_precedingWeight (Y : TorusSite n) : ∑ A, precedingWeight Y A = 1 := by
  have := integral_precedingBlocks (n := n) Y (fun _ => 1)
  simpa using this.symm
theorem blockDensityAt_eq_sum (R : StepSetup) (Y : TorusSite n) (V : TorusField n) :
    R.blockDensityAt Y V = ∑ A, precedingWeight Y A *
      (Real.log (R.markedIntegral A V) - Real.log (R.markedIntegral (insert Y A) V)) :=
  integral_precedingBlocks Y fun A =>
    Real.log (R.markedIntegral A V) - Real.log (R.markedIntegral (insert Y A) V)
theorem sum_blockDensityAt (hT : SumIncrementsAlongOrder) (R : StepSetup) (V : TorusField n) :
    ∑ Y, R.blockDensityAt Y V =
      Real.log (R.markedIntegral ∅ V) - Real.log (R.markedIntegral Finset.univ V) := by
  let F : Finset (TorusSite n) → ℝ := fun A => Real.log (R.markedIntegral A V)
  let lo : LinearOrder (TorusSite n) :=
    LinearOrder.lift' (Fintype.equivFin (TorusSite n)) (Fintype.equivFin (TorusSite n)).injective
  have hint : ∀ Y, Integrable (fun u => F (MarkedIntegrals.precedingBlocks u Y) -
      F (insert Y (MarkedIntegrals.precedingBlocks u Y))) (randomOrderLaw n) := by
    intro Y
    have hdec : (fun u => F (MarkedIntegrals.precedingBlocks u Y) -
        F (insert Y (MarkedIntegrals.precedingBlocks u Y))) = fun u =>
        ∑ A, Set.indicator {u | MarkedIntegrals.precedingBlocks u Y = A}
          (fun _ => F A - F (insert Y A)) u := by
      funext u
      rw [Finset.sum_eq_single (MarkedIntegrals.precedingBlocks u Y)]
      · simp [Set.indicator]
      · intro A _ hA
        simp [Set.indicator, Ne.symm hA]
      · simp
    rw [hdec]
    exact integrable_finsetSum _ fun A _ =>
      (integrable_const _).indicator (measurableSet_precedingBlocks_eq Y A)
  have : ∑ Y, R.blockDensityAt Y V =
      ∫ u, ∑ Y, (F (MarkedIntegrals.precedingBlocks u Y) -
        F (insert Y (MarkedIntegrals.precedingBlocks u Y))) ∂(randomOrderLaw n) := by
    rw [integral_finsetSum _ fun Y _ => hint Y]
    rfl
  rw [this]
  have hae : (fun u => ∑ Y, (F (MarkedIntegrals.precedingBlocks u Y) -
      F (insert Y (MarkedIntegrals.precedingBlocks u Y)))) =ᵐ[randomOrderLaw n]
      fun _ => F ∅ - F Finset.univ := by
    filter_upwards [ae_injective_randomOrderLaw] with u hu
    have hb : ∀ Y, MarkedIntegrals.precedingBlocks u Y = BlockOrder.precedingBlocks u Y := by
      intro Y
      ext i
      simp only [MarkedIntegrals.precedingBlocks, BlockOrder.precedingBlocks, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · exact Or.inl
      · rintro (h | ⟨h1, h2⟩)
        · exact h
        · exact absurd (hu h1) (ne_of_lt h2)
    have := hT (TorusSite n) F u
    simp_rw [hb]
    have e : ∑ Y, (F (BlockOrder.precedingBlocks u Y) - F (insert Y (BlockOrder.precedingBlocks u Y))) =
        - ∑ Y, (F (insert Y (BlockOrder.precedingBlocks u Y)) - F (BlockOrder.precedingBlocks u Y)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    have h3 := this
    have hconv : ∑ Y, (F (insert Y (BlockOrder.precedingBlocks u Y)) - F (BlockOrder.precedingBlocks u Y)) =
        F Finset.univ - F ∅ := by
      convert h3
    rw [hconv]
    ring
  rw [integral_congr_ae hae]
  simp [F]
end
section
variable {n : ℕ}
theorem norm_expUnit_sub_one_le (w : imaginaryQuaternions) :
    ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖w‖ := by apply _root_.YangMills.SharedProofs.p28543 <;> assumption
theorem norm_mul_sub_mul_le (a b a' b' : UnitQuaternion) :
    ‖((a' * b' : UnitQuaternion) : ℍ[ℝ]) - ((a * b : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(a' : ℍ[ℝ]) - a‖ + ‖(b' : ℍ[ℝ]) - b‖ := by
  have e : ((a' * b' : UnitQuaternion) : ℍ[ℝ]) - ((a * b : UnitQuaternion) : ℍ[ℝ]) =
      ((a' : ℍ[ℝ]) - a) * b' + a * ((b' : ℍ[ℝ]) - b) := by
    simp only [Submonoid.coe_mul]
    noncomm_ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_unitQuaternion, norm_unitQuaternion]
  simp
theorem norm_inv_sub_inv (a a' : UnitQuaternion) :
    ‖((a'⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((a⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(a' : ℍ[ℝ]) - a‖ := by
  rw [coe_inv_unitQuaternion, coe_inv_unitQuaternion, ← star_sub, norm_star]
theorem norm_expUnit_mul_sub_le (w : imaginaryQuaternions) (g : UnitQuaternion) :
    ‖((expUnit w * g : UnitQuaternion) : ℍ[ℝ]) - g‖ ≤ ‖w‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearFlatExpansion.unitDist_expUnit_mul_le <;> assumption
theorem norm_perturbSum_le {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (τ : Fin k → ℝ) (b : TorusBond n) :
    ‖∑ l, if c l = b then τ l • X l else 0‖ ≤ k * ‖τ‖ := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ Finset.univ, ‖if c l = b then τ l • X l else (0 : imaginaryQuaternions)‖ ≤ ‖τ‖ := by
    intro l _
    split_ifs
    · rw [norm_smul, hX l, mul_one]
      exact norm_le_pi_norm τ l
    · simpa using norm_nonneg τ
  simpa using Finset.sum_le_card_nsmul _ _ _ this
theorem curvature_perturb_le {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (τ : Fin k → ℝ) (V : TorusField n) (x : TorusSite n) (μ ν : Fin 4) :
    curvature (perturb c X τ V) x μ ν ≤ curvature V x μ ν + 4 * (k * ‖τ‖) := by
  have hb : ∀ (y : TorusSite n) (i : Fin 4),
      ‖((perturb c X τ V y i : UnitQuaternion) : ℍ[ℝ]) - V y i‖ ≤ k * ‖τ‖ := fun y i =>
    (norm_expUnit_mul_sub_le _ _).trans (norm_perturbSum_le c X hX τ (y, i))
  have h := (norm_mul_sub_mul_le
    (V x μ * V (x + TorusFields.unitStep n μ) ν * (V (x + TorusFields.unitStep n ν) μ)⁻¹) (V x ν)⁻¹
    (perturb c X τ V x μ * perturb c X τ V (x + TorusFields.unitStep n μ) ν *
      (perturb c X τ V (x + TorusFields.unitStep n ν) μ)⁻¹)
    (perturb c X τ V x ν)⁻¹)
  have h2 := (norm_mul_sub_mul_le (V x μ * V (x + TorusFields.unitStep n μ) ν)
    (V (x + TorusFields.unitStep n ν) μ)⁻¹
    (perturb c X τ V x μ * perturb c X τ V (x + TorusFields.unitStep n μ) ν)
    (perturb c X τ V (x + TorusFields.unitStep n ν) μ)⁻¹)
  have h3 := (norm_mul_sub_mul_le (V x μ) (V (x + TorusFields.unitStep n μ) ν) (perturb c X τ V x μ)
    (perturb c X τ V (x + TorusFields.unitStep n μ) ν))
  rw [norm_inv_sub_inv] at h h2
  have h4 : ‖((holonomy (perturb c X τ V) x μ ν : UnitQuaternion) : ℍ[ℝ]) -
      ((holonomy V x μ ν : UnitQuaternion) : ℍ[ℝ])‖ ≤ 4 * (k * ‖τ‖) := by
    have := hb x μ
    have := hb (x + TorusFields.unitStep n μ) ν
    have := hb (x + TorusFields.unitStep n ν) μ
    have := hb x ν
    unfold holonomy
    linarith
  unfold curvature
  calc ‖((holonomy (perturb c X τ V) x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1‖
      = ‖(((holonomy (perturb c X τ V) x μ ν : UnitQuaternion) : ℍ[ℝ]) -
            ((holonomy V x μ ν : UnitQuaternion) : ℍ[ℝ])) +
          (((holonomy V x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1)‖ := by congr 1; abel
    _ ≤ _ := (norm_add_le _ _).trans (by linarith)
theorem isCold_perturb {k : ℕ} (hk : k ≤ 3) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (τ : Fin k → ℝ) (V : TorusField n) (s : ℝ) (hs : 0 < s) (hV : IsCold s V)
    (hτ : ‖τ‖ ≤ s / 2 ^ 10) : IsCold (9 / 8 * s) (perturb c X τ V) := by
  intro x μ ν h
  have h1 := curvature_perturb_le c X hX τ V x μ ν
  have h2 := hV x μ ν h
  have hk' : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have h3 : (k : ℝ) * ‖τ‖ ≤ 3 * (s / 2 ^ 10) :=
    mul_le_mul hk' hτ (norm_nonneg _) (by norm_num)
  linarith
theorem two_mul_supDist_le [NeZero n] (x y : TorusSite n) : 2 * supDist x y ≤ n := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.two_mul_supDist_le <;> assumption
end
section
theorem weight_le_of_le (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (hn1 : 0 < ℓ.n₁) (hrt : 0 < ℓ.rt) (m N : ℕ) (hN : N ≤ 2 * m + 4)
    (p : ℕ) (hw : ℓ.weight N = max 1 (((N : ℝ) / ℓ.n₁) ^ p) * Real.exp (ℓ.weightRate * N)) :
    ℓ.weight N ≤ (2 + 4 / ℓ.n₁) ^ p * (1 + m / ℓ.n₁) ^ p *
      (Real.exp (ℓ.rt / 2 ^ 8) * Real.exp (ℓ.rt * m / 2 ^ 9)) := by
  have hQ : max 1 (((N : ℝ) / ℓ.n₁) ^ p) ≤ (2 + 4 / ℓ.n₁) ^ p * (1 + m / ℓ.n₁) ^ p := by
    rw [← mul_pow]
    have hm0 : (0 : ℝ) ≤ m / ℓ.n₁ := by positivity
    have h4 : (0 : ℝ) ≤ 4 / ℓ.n₁ := by positivity
    have hbig : 1 ≤ (2 + 4 / ℓ.n₁) * (1 + m / ℓ.n₁) := by nlinarith
    refine max_le (one_le_pow₀ hbig) (pow_le_pow_left₀ (by positivity) ?_ _)
    have hNr : (N : ℝ) ≤ 2 * m + 4 := by exact_mod_cast hN
    have : (N : ℝ) / ℓ.n₁ ≤ (2 * m + 4) / ℓ.n₁ := div_le_div_of_nonneg_right hNr hn1.le
    have h5 : (2 * (m : ℝ) + 4) / ℓ.n₁ = 2 * (m / ℓ.n₁) + 4 / ℓ.n₁ := by ring
    nlinarith
  have hR : Real.exp (ℓ.weightRate * N) ≤ Real.exp (ℓ.rt / 2 ^ 8) * Real.exp (ℓ.rt * m / 2 ^ 9) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hNr : (N : ℝ) ≤ 2 * m + 4 := by exact_mod_cast hN
    unfold StepParameters.weightRate
    have : ℓ.rt / 2 ^ 10 * N ≤ ℓ.rt / 2 ^ 10 * (2 * m + 4) :=
      mul_le_mul_of_nonneg_left hNr (by positivity)
    linarith
  rw [hw]
  exact mul_le_mul hQ hR (Real.exp_pos _).le (by positivity)
theorem weight_pos (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (N : ℕ) : 0 < ℓ.weight N := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
theorem interpolation_le_decay_aux (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (hrt : 0 < ℓ.rt) (ch x C Ck τ₀ P Q : ℝ)
    (hch : 0 < ch) (hx1 : 1 ≤ x) (hC : 0 ≤ C) (hCk : 0 < Ck) (hτ0 : 0 < τ₀) (hτ1 : τ₀ ≤ 1) (hP0 : 0 ≤ P)
    (hQ0 : 0 ≤ Q) (hK : Ck * (2 / τ₀ ^ 3 + 8) * Q * Real.exp (ℓ.rt / 2 ^ 8) ≤ x) (m N k : ℕ)
    (hy : x ^ (C + 1) * P * Real.exp (-(1 / 4) * (ch * x + ℓ.rt * m / 2 ^ 8)) ≤ 1)
    (hWle : ℓ.weight N ≤ Q * P * (Real.exp (ℓ.rt / 2 ^ 8) * Real.exp (ℓ.rt * m / 2 ^ 9))) (hk : k ≤ 3) :
    Ck * ((2 * Real.exp (-(ch * x) - ℓ.rt * m / 2 ^ 8)) / τ₀ ^ k +
        (2 * Real.exp (-(ch * x) - ℓ.rt * m / 2 ^ 8)) ^ (1 - (k : ℝ) / (40 : ℕ)) *
          (4 * x ^ C) ^ ((k : ℝ) / (40 : ℕ))) ≤
      Real.exp (-(ch * x) / 2) / ℓ.weight N := by
  have hx0 : 0 < x := by linarith
  set u : ℝ := ch * x + ℓ.rt * m / 2 ^ 8 with hu_def
  have hu : 0 ≤ u := by positivity
  have he : -(ch * x) - ℓ.rt * m / 2 ^ 8 = -u := by rw [hu_def]; ring
  rw [he]
  set E : ℝ := Real.exp (-(37 / 40) * u) with hE_def
  have hE0 : 0 < E := Real.exp_pos _
  have hxC : 1 ≤ x ^ C := Real.one_le_rpow hx1 hC
  have hkr : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have t1 : 2 * Real.exp (-u) / τ₀ ^ k ≤ 2 * E / τ₀ ^ 3 := by
    have h1 : Real.exp (-u) ≤ E := Real.exp_le_exp.mpr (by nlinarith)
    have h2 : τ₀ ^ 3 ≤ τ₀ ^ k := pow_le_pow_of_le_one hτ0.le hτ1 hk
    have h3 : 0 < τ₀ ^ 3 := by positivity
    exact div_le_div₀ (by positivity) (by linarith) h3 h2
  have ha2 : 1 - (k : ℝ) / (40 : ℕ) ≤ 1 := by
    push_cast
    have : 0 ≤ (k : ℝ) / 40 := by positivity
    linarith
  have t2 : (2 * Real.exp (-u)) ^ (1 - (k : ℝ) / (40 : ℕ)) ≤ 2 * E := by
    rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
    have h1 : (2 : ℝ) ^ (1 - (k : ℝ) / (40 : ℕ)) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - (k : ℝ) / (40 : ℕ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) ha2
        _ = 2 := Real.rpow_one 2
    have h2 : Real.exp (-u * (1 - (k : ℝ) / (40 : ℕ))) ≤ E := Real.exp_le_exp.mpr (by nlinarith)
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
  have hb4 : 1 ≤ 4 * x ^ C := by linarith
  have t3 : (4 * x ^ C) ^ ((k : ℝ) / (40 : ℕ)) ≤ 4 * x ^ C := by
    have hb : (k : ℝ) / (40 : ℕ) ≤ 1 := by
      push_cast
      linarith
    calc (4 * x ^ C) ^ ((k : ℝ) / (40 : ℕ)) ≤ (4 * x ^ C) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb4 hb
      _ = 4 * x ^ C := Real.rpow_one _
  have step1 : Ck * ((2 * Real.exp (-u)) / τ₀ ^ k + (2 * Real.exp (-u)) ^ (1 - (k : ℝ) / (40 : ℕ)) *
      (4 * x ^ C) ^ ((k : ℝ) / (40 : ℕ))) ≤ Ck * (2 / τ₀ ^ 3 + 8) * x ^ C * E := by
    have h1 : (2 * Real.exp (-u)) ^ (1 - (k : ℝ) / (40 : ℕ)) * (4 * x ^ C) ^ ((k : ℝ) / (40 : ℕ)) ≤
        2 * E * (4 * x ^ C) :=
      mul_le_mul t2 t3 (Real.rpow_nonneg (by positivity) _) (by positivity)
    have h2 : 2 * E / τ₀ ^ 3 ≤ 2 / τ₀ ^ 3 * x ^ C * E := by
      have : 2 * E / τ₀ ^ 3 = 2 / τ₀ ^ 3 * 1 * E := by ring
      rw [this]
      have h20 : 0 ≤ 2 / τ₀ ^ 3 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxC h20) hE0.le
    have h3 : Ck * (2 / τ₀ ^ 3 + 8) * x ^ C * E =
        Ck * (2 / τ₀ ^ 3 * x ^ C * E + 2 * E * (4 * x ^ C)) := by
      ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left (by linarith) hCk.le
  have hW0 : 0 < ℓ.weight N := weight_pos ℓ N
  refine step1.trans ?_
  rw [le_div_iff₀ hW0]
  have hpow : x ^ (C + 1) = x ^ C * x := Real.rpow_add_one hx0.ne' C
  have hyy := hy
  rw [hpow] at hyy
  set S := Real.exp (ℓ.rt / 2 ^ 8) with hS
  set T := Real.exp (ℓ.rt * m / 2 ^ 9) with hT
  calc Ck * (2 / τ₀ ^ 3 + 8) * x ^ C * E * ℓ.weight N
      ≤ Ck * (2 / τ₀ ^ 3 + 8) * x ^ C * E * (Q * P * (S * T)) :=
        mul_le_mul_of_nonneg_left hWle (by positivity)
    _ = (Ck * (2 / τ₀ ^ 3 + 8) * Q * S) * (x ^ C * P * E * T) := by ring
    _ ≤ x * (x ^ C * P * E * T) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = (x ^ C * x * P * Real.exp (-(1 / 4) * u)) * (Real.exp (-(27 / 40) * u) * T) := by
        have : E = Real.exp (-(1 / 4) * u) * Real.exp (-(27 / 40) * u) := by
          rw [← Real.exp_add, hE_def]
          congr 1
          ring
        rw [this]
        ring
    _ ≤ 1 * (Real.exp (-(27 / 40) * u) * T) :=
        mul_le_mul_of_nonneg_right hyy (by positivity)
    _ = Real.exp (-(27 / 40) * u + ℓ.rt * m / 2 ^ 9) := by rw [one_mul, hT, ← Real.exp_add]
    _ ≤ Real.exp (-(ch * x) / 2) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : 0 ≤ ch * x := by positivity
        have h2 : 0 ≤ ℓ.rt * m / 2 ^ 8 := by positivity
        have e : ℓ.rt * (m : ℝ) / 2 ^ 9 = (ℓ.rt * m / 2 ^ 8) / 2 := by ring
        rw [hu_def, e]
        nlinarith
theorem interpolation_le_decay (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (hrt : 0 < ℓ.rt) (hn1 : 0 < ℓ.n₁) (ch x C Ck τ₀ : ℝ)
    (hch : 0 < ch) (hx1 : 1 ≤ x) (hC : 0 ≤ C) (hCk : 0 < Ck) (hτ0 : 0 < τ₀) (hτ1 : τ₀ ≤ 1)
    (hK : Ck * (2 / τ₀ ^ 3 + 8) * (2 + 4 / ℓ.n₁) ^ 16000 * Real.exp (ℓ.rt / 2 ^ 8) ≤ x)
    (hy : ∀ m : ℕ, x ^ (C + 1) * (1 + m / ℓ.n₁) ^ 16000 *
      Real.exp (-(1 / 4) * (ch * x + ℓ.rt * m / 2 ^ 8)) ≤ 1)
    (m N k : ℕ) (hN : N ≤ 2 * m + 4) (hk : k ≤ 3) :
    Ck * ((2 * Real.exp (-(ch * x) - ℓ.rt * m / 2 ^ 8)) / τ₀ ^ k +
        (2 * Real.exp (-(ch * x) - ℓ.rt * m / 2 ^ 8)) ^ (1 - (k : ℝ) / (40 : ℕ)) *
          (4 * x ^ C) ^ ((k : ℝ) / (40 : ℕ))) ≤
      Real.exp (-(ch * x) / 2) / ℓ.weight N :=
  interpolation_le_decay_aux ℓ hrt ch x C Ck τ₀ _ _ hch hx1 hC hCk hτ0 hτ1 (pow_nonneg (by positivity) _)
    (pow_nonneg (by positivity) _) hK m N k (hy m)
    (weight_le_of_le ℓ hn1 hrt m N hN 16000 rfl) hk
end
section
variable {n : ℕ}
theorem blockDensity_eq (R : StepSetup) [NeZero n] (y : TorusSite n) (V : TorusField n) :
    R.blockDensity n y V = R.blockDensityAt y V := by
  unfold StepSettings.StepSetup.blockDensity
  rw [dif_neg (NeZero.ne n)]
def SmallOrderInterpolation (Cm : ℝ) : Prop :=
  ∀ k ≤ 3, ∀ (u : (Fin k → ℝ) → ℝ) (τ₀ M₀ Mp : ℝ), 0 < τ₀ → 0 < M₀ → 0 ≤ Mp → ContDiff ℝ 40 u →
    (∀ τ, ‖τ‖ ≤ τ₀ → |u τ| ≤ M₀) → (∀ τ, ‖τ‖ ≤ τ₀ → ‖iteratedFDeriv ℝ 40 u τ‖ ≤ Mp) →
    ∀ v : Fin k → (Fin k → ℝ), (∀ l, ‖v l‖ ≤ 1) →
      |iteratedFDeriv ℝ k u 0 v| ≤
        Cm * (M₀ / τ₀ ^ k + M₀ ^ (1 - (k : ℝ) / (40 : ℕ)) * Mp ^ ((k : ℝ) / (40 : ℕ)))
theorem exists_smallOrderInterpolation (hI : LandauKolmogorovMultivariateAtZero) :
    ∃ Cm : ℝ, 0 < Cm ∧ SmallOrderInterpolation Cm := by
  choose! C hC hmain using fun k : ℕ => fun _ : k < 4 => hI k 40 k (by omega)
  refine ⟨C 0 + C 1 + C 2 + C 3, ?_, ?_⟩
  · have := hC 0 (by norm_num); have := hC 1 (by norm_num); have := hC 2 (by norm_num)
    have := hC 3 (by norm_num)
    linarith
  · intro k hk u τ₀ M₀ Mp hτ hM hMp hu h1 h2 v hv
    have hk4 : k < 4 := by omega
    have h3 := hmain k hk4 u τ₀ M₀ Mp hτ hM hMp hu h1 h2
      (fun σ m => iteratedFDeriv_perm_of_le_three (hu.of_le (by norm_num)) 0 k hk σ m) v hv
    refine h3.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h0 := (hC 0 (by norm_num)).le
    have h1' := (hC 1 (by norm_num)).le
    have h2' := (hC 2 (by norm_num)).le
    have h3' := (hC 3 (by norm_num)).le
    interval_cases k <;> linarith
theorem exists_contDiff_eventuallyEq {k : ℕ} (G : (Fin k → ℝ) → ℝ) (τ₀ : ℝ) (hτ : 0 < τ₀)
    (hG : ∀ τ, ‖τ‖ < 2 * τ₀ → ContDiffAt ℝ 40 G τ) :
    ∃ Gb : (Fin k → ℝ) → ℝ, ContDiff ℝ 40 Gb ∧ ∀ τ, ‖τ‖ < 3 / 2 * τ₀ → Gb =ᶠ[nhds τ] G := by
  let χ : ContDiffBump (0 : Fin k → ℝ) :=
    ⟨3 / 2 * τ₀, 7 / 4 * τ₀, by positivity, by linarith⟩
  have hχ : ContDiff ℝ 40 (fun τ => χ τ) := χ.contDiff
  refine ⟨fun τ => χ τ * G τ, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro τ
    by_cases ht : ‖τ‖ < 2 * τ₀
    · exact hχ.contDiffAt.mul (hG τ ht)
    · have hfar : ∀ᶠ z in nhds τ, χ z * G z = 0 := by
        have hmem : (Metric.closedBall (0 : Fin k → ℝ) (7 / 4 * τ₀))ᶜ ∈ nhds τ := by
          refine (Metric.isClosed_closedBall.isOpen_compl).mem_nhds ?_
          simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
          nlinarith
        filter_upwards [hmem] with z hz
        have : χ z = 0 := by
          apply χ.zero_of_le_dist
          simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
          have : χ.rOut = 7 / 4 * τ₀ := rfl
          rw [this, dist_zero_right]
          exact hz.le
        simp [this]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hfar
  · intro τ hτ'
    have : Metric.ball (0 : Fin k → ℝ) (3 / 2 * τ₀) ∈ nhds τ :=
      Metric.isOpen_ball.mem_nhds (by simpa using hτ')
    filter_upwards [this] with z hz
    have : χ z = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
    simp [this]
variable {R : StepSetup} {ch C : ℝ}
theorem blockDensity_perturb_eq [NeZero n] (y : TorusSite n) (V : TorusField n) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    (fun τ => R.blockDensity n y (perturb c X τ V)) = fun τ => ∑ A, precedingWeight y A •
      (Real.log (R.markedIntegral A (perturb c X τ V)) -
        Real.log (R.markedIntegral (insert y A) (perturb c X τ V))) := by
  funext τ
  rw [blockDensity_eq, blockDensityAt_eq_sum]
  simp
theorem contDiffAt_blockDensity_perturb (hS : R.LogMarkedIntegralSmooth C) [NeZero n] (hn : R.params.n₀ ≤ n)
    (y : TorusSite n) (V : TorusField n) {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) (hc : IsCold (9 / 8 * R.params.threshold) (perturb c X τ V)) :
    ContDiffAt ℝ 40 (fun τ' => R.blockDensity n y (perturb c X τ' V)) τ := by
  rw [blockDensity_perturb_eq]
  refine ContDiffAt.sum fun A _ => ContDiffAt.const_smul _ ?_
  exact (hS n hn A V k c X τ hc).1.sub (hS n hn (insert y A) V k c X τ hc).1
theorem norm_iteratedFDeriv_blockDensity_le (hS : R.LogMarkedIntegralSmooth C) [NeZero n]
    (hn : R.params.n₀ ≤ n) (y : TorusSite n) (V : TorusField n) {k : ℕ} (hk : k ≤ 3)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) (τ : Fin k → ℝ)
    (hc : IsCold (9 / 8 * R.params.threshold) (perturb c X τ V)) :
    ‖iteratedFDeriv ℝ 40 (fun τ' => R.blockDensity n y (perturb c X τ' V)) τ‖ ≤ 2 * R.coupling ^ C := by
  rw [blockDensity_perturb_eq]
  have hterm : ∀ A : Finset (TorusSite n), ContDiffAt ℝ 40 (fun τ' =>
      Real.log (R.markedIntegral A (perturb c X τ' V)) -
        Real.log (R.markedIntegral (insert y A) (perturb c X τ' V))) τ := fun A =>
    (hS n hn A V k c X τ hc).1.sub (hS n hn (insert y A) V k c X τ hc).1
  rw [iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := 40)
    (f := fun A τ' => precedingWeight y A • (Real.log (R.markedIntegral A (perturb c X τ' V)) -
        Real.log (R.markedIntegral (insert y A) (perturb c X τ' V))))
    (fun A _ => (hterm A).const_smul _)]
  refine (norm_sum_le _ _).trans ?_
  have hone : ∀ A ∈ (Finset.univ : Finset (Finset (TorusSite n))),
      ‖iteratedFDeriv ℝ 40 (fun τ' => precedingWeight y A •
        (Real.log (R.markedIntegral A (perturb c X τ' V)) -
          Real.log (R.markedIntegral (insert y A) (perturb c X τ' V)))) τ‖ ≤
        precedingWeight y A * (2 * R.coupling ^ C) := by
    intro A _
    rw [iteratedFDeriv_const_smul_apply' (hterm A), norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (precedingWeight_nonneg y A)]
    refine mul_le_mul_of_nonneg_left ?_ (precedingWeight_nonneg y A)
    rw [fun_iteratedFDeriv_sub_apply (hS n hn A V k c X τ hc).1 (hS n hn (insert y A) V k c X τ hc).1]
    refine (norm_sub_le _ _).trans ?_
    have h1 := (hS n hn A V k c X τ hc).2 hk hX
    have h2 := (hS n hn (insert y A) V k c X τ hc).2 hk hX
    linarith
  refine (Finset.sum_le_sum hone).trans ?_
  rw [← Finset.sum_mul, sum_precedingWeight, one_mul]
theorem abs_blockDensity_le (hA : R.MarkedIntegralStable ch) [NeZero n] (hn : R.params.n₀ ≤ n)
    (y : TorusSite n) (V : TorusField n) (hV : IsCold (9 / 8 * R.params.threshold) V)
    (he : Real.exp (-(7 * ch * R.coupling)) ≤ 1 / 2) :
    |R.blockDensity n y V| ≤ 2 * Real.exp (-(7 * ch * R.coupling)) := by
  set e := Real.exp (-(7 * ch * R.coupling)) with he_def
  have he0 : 0 < e := Real.exp_pos _
  have hterm : ∀ A : Finset (TorusSite n),
      0 ≤ Real.log (R.markedIntegral A V) - Real.log (R.markedIntegral (insert y A) V) ∧
      Real.log (R.markedIntegral A V) - Real.log (R.markedIntegral (insert y A) V) ≤ 2 * e := by
    intro A
    obtain ⟨h0, h1, h2⟩ := hA n hn V hV A y
    set Z := R.markedIntegral A V
    set Z' := R.markedIntegral (insert y A) V
    have hZ' : 0 < Z' := lt_of_lt_of_le (mul_pos (by linarith) h0) h1
    refine ⟨sub_nonneg.mpr (Real.log_le_log hZ' h2), ?_⟩
    rw [← Real.log_div h0.ne' hZ'.ne']
    have hq : Z / Z' ≤ 1 + 2 * e := by
      rw [div_le_iff₀ hZ']
      have : (1 + 2 * e) * ((1 - e) * Z) ≤ (1 + 2 * e) * Z' :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : Z ≤ (1 + 2 * e) * ((1 - e) * Z) := by
        have : (1 + 2 * e) * (1 - e) = 1 + e * (1 - 2 * e) := by ring
        nlinarith [mul_nonneg (mul_nonneg he0.le (by linarith : (0 : ℝ) ≤ 1 - 2 * e)) h0.le]
      linarith
    have := Real.log_le_sub_one_of_pos (div_pos h0 hZ')
    linarith
  rw [blockDensity_eq, blockDensityAt_eq_sum]
  have hlow : 0 ≤ ∑ A, precedingWeight y A * (Real.log (R.markedIntegral A V) -
      Real.log (R.markedIntegral (insert y A) V)) :=
    Finset.sum_nonneg fun A _ => mul_nonneg (precedingWeight_nonneg y A) (hterm A).1
  rw [abs_of_nonneg hlow]
  calc _ ≤ ∑ A, precedingWeight y A * (2 * e) :=
        Finset.sum_le_sum fun A _ => mul_le_mul_of_nonneg_left (hterm A).2 (precedingWeight_nonneg y A)
    _ = 2 * e := by rw [← Finset.sum_mul, sum_precedingWeight, one_mul]
end
section
variable {n : ℕ}
structure CouplingBounds (R : StepSetup) (ch C Cm : ℝ) : Prop where
  threshold_pos : 0 < R.params.threshold
  threshold_le_one : R.params.threshold ≤ 1
  rt_pos : 0 < R.params.rt
  n₁_pos : 0 < R.params.n₁
  gasRate_pos : 0 < ch
  one_le_coupling : 1 ≤ R.coupling
  C_nonneg : 0 ≤ C
  Cm_pos : 0 < Cm
  large_coupling : Cm * (2 / (R.params.threshold / 2 ^ 11) ^ 3 + 8) * (2 + 4 / R.params.n₁) ^ 16000 *
    Real.exp (R.params.rt / 2 ^ 8) ≤ R.coupling
  decay_floor : ∀ m : ℕ, R.coupling ^ (C + 1) * (1 + m / R.params.n₁) ^ 16000 *
    Real.exp (-(1 / 4) * (ch * R.coupling + R.params.rt * m / 2 ^ 8)) ≤ 1
  one_le_gasRate_mul : 1 ≤ ch * R.coupling
  rt_le_gasRate_mul : R.params.rt ≤ ch * R.coupling
variable {R : StepSetup} {ch C Cm : ℝ}
theorem CouplingBounds.interpolation_bound (N : CouplingBounds R ch C Cm) (hI : SmallOrderInterpolation Cm)
    {k : ℕ} (hk : k ≤ 3) (u : (Fin k → ℝ) → ℝ) (hu : ContDiff ℝ 40 u) (m M : ℕ) (hM : M ≤ 2 * m + 4)
    (hs : ∀ τ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 →
      |u τ| ≤ 2 * Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8))
    (hd : ∀ τ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 → ‖iteratedFDeriv ℝ 40 u τ‖ ≤ 4 * R.coupling ^ C) :
    |iteratedFDeriv ℝ k u 0 (fun l => Pi.single l 1)| ≤
      Real.exp (-(ch * R.coupling) / 2) / R.params.weight M := by
  have hτ : 0 < R.params.threshold / 2 ^ 11 := by have := N.threshold_pos; positivity
  have hτ1 : R.params.threshold / 2 ^ 11 ≤ 1 := by
    have := N.threshold_le_one
    have := N.threshold_pos
    linarith
  have hxC : 0 < R.coupling ^ C := Real.rpow_pos_of_pos (by linarith [N.one_le_coupling]) _
  refine (hI k hk u _ _ _ hτ (by positivity) (by positivity) hu hs hd _ ?_).trans
    (interpolation_le_decay R.params N.rt_pos N.n₁_pos ch R.coupling C Cm _ N.gasRate_pos N.one_le_coupling
      N.C_nonneg N.Cm_pos hτ hτ1 N.large_coupling N.decay_floor m M k hM hk)
  intro l
  simp [Pi.norm_single]
theorem CouplingBounds.exp_le_half (N : CouplingBounds R ch C Cm) :
    Real.exp (-(7 * ch * R.coupling)) ≤ 1 / 2 := by
  have h1 := N.one_le_gasRate_mul
  have h3 : Real.exp (-(7 * ch * R.coupling)) ≤ Real.exp (-7) := Real.exp_le_exp.mpr (by linarith)
  have h4 : (2 : ℝ) ≤ Real.exp 7 := by
    have := Real.add_one_le_exp (7 : ℝ)
    linarith
  have h5 : Real.exp (-7) ≤ 1 / 2 := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h4
  linarith
theorem CouplingBounds.size_le (N : CouplingBounds R ch C Cm) (m : ℕ) (hm : m ≤ 1) :
    2 * Real.exp (-(7 * ch * R.coupling)) ≤ 2 * Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8) := by
  have h1 := N.rt_le_gasRate_mul
  have h0 := N.rt_pos
  have hm' : (m : ℝ) ≤ 1 := by exact_mod_cast hm
  have h2 : R.params.rt * m / 2 ^ 8 ≤ R.params.rt := by nlinarith
  have : Real.exp (-(7 * ch * R.coupling)) ≤ Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8) :=
    Real.exp_le_exp.mpr (by nlinarith)
  linarith
theorem fieldsAgreeNear_perturb_drop {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (τ τ' : Fin k → ℝ) (V : TorusField n) (y : TorusSite n) (m : ℕ) (l₀ : Fin k)
    (hτ : ∀ l, l ≠ l₀ → τ' l = τ l) (hfar : ∀ b, BondOffsetInBox m b → c l₀ ≠ bondFrom y b) :
    FieldsAgreeNear (perturb c X τ V) (perturb c X τ' V) y y m := by
  intro b hb
  unfold perturb
  congr 2
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l = l₀
  · subst hl
    have : c l ≠ ((bondFrom y b).1, (bondFrom y b).2) := hfar b hb
    simp [this]
  · rw [hτ l hl]
theorem bondFrom_eq_iff [NeZero n] (y : TorusSite n) (m : ℕ) (hn : 2 * m + 2 < n) (a b : (Fin 4 → ℤ) × Fin 4)
    (ha : BondOffsetInBox m a) (hb : BondOffsetInBox m b) : bondFrom y a = bondFrom y b ↔ a = b := by
  constructor
  · intro h
    have h1 : y + siteOfInt a.1 = y + siteOfInt b.1 := congrArg Prod.fst h
    have h2 : a.2 = b.2 := (congrArg Prod.snd h : (bondFrom y a).2 = (bondFrom y b).2)
    have h3 : (siteOfInt a.1 : TorusSite n) = siteOfInt b.1 := add_left_cancel h1
    refine Prod.ext (funext fun i => ?_) h2
    have h4 : ((a.1 i : ℤ) : ZMod n) = ((b.1 i : ℤ) : ZMod n) := congrFun h3 i
    have h5 : ((n : ℤ)) ∣ b.1 i - a.1 i := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h4
    have h6 := ha.1 i
    have h7 := hb.1 i
    have h8 : |b.1 i - a.1 i| < (n : ℤ) := by
      have := abs_sub (b.1 i) (a.1 i)
      linarith
    have h9 := Int.eq_zero_of_abs_lt_dvd h5 h8
    linarith
  · rintro rfl
    rfl
theorem fieldsAgreeNear_perturb {n' : ℕ} [NeZero n] [NeZero n'] {k : ℕ} (h : Fin k → (Fin 4 → ℤ) × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) (V : TorusField n) (V' : TorusField n')
    (y : TorusSite n) (y' : TorusSite n') (m : ℕ) (hn : 2 * m + 2 < n) (hn' : 2 * m + 2 < n')
    (hh : ∀ l, BondOffsetInBox m (h l)) (hag : FieldsAgreeNear V V' y y' m) :
    FieldsAgreeNear (perturb (fun l => bondFrom y (h l)) X τ V)
      (perturb (fun l => bondFrom y' (h l)) X τ V') y y' m := by
  intro b hb
  unfold perturb
  rw [hag b hb]
  congr 2
  refine Finset.sum_congr rfl fun l _ => ?_
  have e1 : (bondFrom y (h l) = ((bondFrom y b).1, (bondFrom y b).2)) ↔ h l = b :=
    bondFrom_eq_iff y m hn _ _ (hh l) hb
  have e2 : (bondFrom y' (h l) = ((bondFrom y' b).1, (bondFrom y' b).2)) ↔ h l = b :=
    bondFrom_eq_iff y' m hn' _ _ (hh l) hb
  by_cases hl : h l = b
  · rw [if_pos (e1.mpr hl), if_pos (e2.mpr hl)]
  · rw [if_neg (fun q => hl (e1.mp q)), if_neg (fun q => hl (e2.mp q))]
theorem ne_bondFrom_of_lt [NeZero n] (y : TorusSite n) (z : TorusBond n) (m : ℕ) (hz : m < supDist y z.1)
    (b : (Fin 4 → ℤ) × Fin 4) (hb : BondOffsetInBox m b) : z ≠ bondFrom y b := by
  intro h
  have h1 : z.1 = y + siteOfInt b.1 := congrArg Prod.fst h
  have h2 : supDist y (y + siteOfInt b.1) ≤ m :=
    supDist_add_siteOfInt_le y b.1 m (fun i => by
      have := hb.1 i
      rw [Int.abs_eq_natAbs] at this
      exact_mod_cast this)
  rw [h1] at hz
  omega
end
section
variable {n : ℕ} {R : StepSetup} {ch C Cm : ℝ}
theorem exists_smooth_blockDensity (N : CouplingBounds R ch C Cm) (hS : R.LogMarkedIntegralSmooth C) [NeZero n]
    (hn : R.params.n₀ ≤ n) (y : TorusSite n) (V : TorusField n) (hV : IsCold R.params.threshold V) {k : ℕ}
    (hk : k ≤ 3) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) :
    ∃ Gb : (Fin k → ℝ) → ℝ, ContDiff ℝ 40 Gb ∧
      (∀ τ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 → Gb τ = R.blockDensity n y (perturb c X τ V)) ∧
      (∀ τ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 → ‖iteratedFDeriv ℝ 40 Gb τ‖ ≤ 2 * R.coupling ^ C) ∧
      (∀ j : ℕ, iteratedFDeriv ℝ j Gb 0 =
        iteratedFDeriv ℝ j (fun τ => R.blockDensity n y (perturb c X τ V)) 0) := by
  have hσ := N.threshold_pos
  have hτ0 : 0 < R.params.threshold / 2 ^ 11 := by positivity
  have hcold : ∀ τ : Fin k → ℝ, ‖τ‖ < 2 * (R.params.threshold / 2 ^ 11) →
      IsCold (9 / 8 * R.params.threshold) (perturb c X τ V) := fun τ ht =>
    isCold_perturb hk c X hX τ V R.params.threshold hσ hV (by linarith)
  obtain ⟨Gb, hGb, hGe⟩ := exists_contDiff_eventuallyEq (fun τ => R.blockDensity n y (perturb c X τ V))
    (R.params.threshold / 2 ^ 11) hτ0
    (fun τ ht => contDiffAt_blockDensity_perturb hS hn y V c X τ (hcold τ ht))
  have hin : ∀ τ : Fin k → ℝ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 →
      ‖τ‖ < 3 / 2 * (R.params.threshold / 2 ^ 11) := fun τ ht => by
    linarith
  refine ⟨Gb, hGb, fun τ ht => (hGe τ (hin τ ht)).self_of_nhds, fun τ ht => ?_, fun j => ?_⟩
  · rw [((hGe τ (hin τ ht)).iteratedFDeriv (𝕜 := ℝ) 40).self_of_nhds]
    exact norm_iteratedFDeriv_blockDensity_le hS hn y V hk c X hX τ (hcold τ (by linarith))
  · exact ((hGe 0 (by simpa using hτ0)).iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds
def zeroCoord {k : ℕ} (l₀ : Fin k) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun l => if l = l₀ then 0 else ContinuousLinearMap.proj l
theorem zeroCoord_apply {k : ℕ} (l₀ l : Fin k) (τ : Fin k → ℝ) :
    zeroCoord l₀ τ l = if l = l₀ then 0 else τ l := by
  unfold zeroCoord
  by_cases h : l = l₀ <;> simp [h]
theorem norm_zeroCoord_apply_le {k : ℕ} (l₀ : Fin k) (τ : Fin k → ℝ) : ‖zeroCoord l₀ τ‖ ≤ ‖τ‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun l => ?_
  rw [zeroCoord_apply]
  split_ifs
  · simpa using norm_nonneg τ
  · exact norm_le_pi_norm τ l
theorem norm_zeroCoord_le {k : ℕ} (l₀ : Fin k) : ‖zeroCoord l₀‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun τ => by
    simpa using norm_zeroCoord_apply_le l₀ τ
theorem norm_iteratedFDeriv_comp_zeroCoord_le {k j : ℕ} (Gb : (Fin k → ℝ) → ℝ) (hGb : ContDiff ℝ 40 Gb)
    (hj : j ≤ 40) (l₀ : Fin k) (τ : Fin k → ℝ) :
    ‖iteratedFDeriv ℝ j (fun z => Gb (zeroCoord l₀ z)) τ‖ ≤ ‖iteratedFDeriv ℝ j Gb (zeroCoord l₀ τ)‖ := by
  have h := (zeroCoord l₀).iteratedFDeriv_comp_right hGb τ (i := j) (by exact_mod_cast hj)
  have e : (fun z => Gb (zeroCoord l₀ z)) = Gb ∘ (zeroCoord l₀) := rfl
  rw [e, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin j, ‖zeroCoord l₀‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_zeroCoord_le l₀
  exact mul_le_of_le_one_right (norm_nonneg _) this
theorem iteratedFDeriv_comp_zeroCoord_eq_zero {k : ℕ} (Gb : (Fin k → ℝ) → ℝ) (hGb : ContDiff ℝ 40 Gb)
    (hk : k ≤ 40) (l₀ : Fin k) :
    iteratedFDeriv ℝ k (fun z => Gb (zeroCoord l₀ z)) 0 (fun l => Pi.single l 1) = 0 := by
  have h := (zeroCoord l₀).iteratedFDeriv_comp_right hGb 0 (i := k) (by exact_mod_cast hk)
  have e : (fun z => Gb (zeroCoord l₀ z)) = Gb ∘ (zeroCoord l₀) := rfl
  rw [e, h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine ContinuousMultilinearMap.map_coord_zero _ l₀ ?_
  funext l
  simp [zeroCoord_apply, Pi.single_apply]
theorem blockDensity_decay (N : CouplingBounds R ch C Cm) (hI : SmallOrderInterpolation Cm)
    (hA : R.MarkedIntegralStable ch) (hB : R.DensitiesLocal ch) (hS : R.LogMarkedIntegralSmooth C) [NeZero n]
    (hn : R.params.n₀ ≤ n) (y : TorusSite n) (V : TorusField n) (hV : IsCold R.params.threshold V) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (h1 : 1 ≤ k) (hk : k ≤ 3)
    (hX : AreUnitVectors X) :
    |mixedDeriv (R.blockDensity n y) V c X| ≤
      Real.exp (-(ch * R.coupling) / 2) / R.params.weight (supportDiam y c) := by
  have hσ := N.threshold_pos
  obtain ⟨Gb, hGb, hval, hder, hzero⟩ := exists_smooth_blockDensity N hS hn y V hV hk c X hX
  have hxC : 0 < R.coupling ^ C := Real.rpow_pos_of_pos (by linarith [N.one_le_coupling]) _
  have hcold : ∀ τ : Fin k → ℝ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 →
      IsCold (9 / 8 * R.params.threshold) (perturb c X τ V) :=
    fun τ ht => isCold_perturb hk c X hX τ V R.params.threshold hσ hV (by linarith)
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨l₀, -, hl₀⟩ := Finset.exists_mem_eq_sup Finset.univ hne fun l : Fin k => supDist y (c l).1
  set D : ℕ := Finset.univ.sup fun l : Fin k => supDist y (c l).1 with hD
  have hle : ∀ l, supDist y (c l).1 ≤ D := fun l =>
    Finset.le_sup (f := fun l : Fin k => supDist y (c l).1) (Finset.mem_univ l)
  have hspan : supportDiam y c ≤ 2 * (D - 2) + 4 := by
    have h2 : supportDiam y c ≤ 2 * D := by
      unfold supportDiam
      refine max_le (by omega) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
      have := supDist_triangle (c l).1 y (c l').1
      have h3 := hle l
      have h4 := hle l'
      rw [supDist_comm (c l).1 y] at this
      omega
    omega
  have hdM : mixedDeriv (R.blockDensity n y) V c X =
      iteratedFDeriv ℝ k (fun τ => R.blockDensity n y (perturb c X τ V)) 0 (fun l => Pi.single l 1) := rfl
  by_cases h4 : 4 ≤ D
  · have hfar := hB n n hn hn
    set u : (Fin k → ℝ) → ℝ := fun τ => Gb τ - Gb (zeroCoord l₀ τ) with hu_def
    have hP : ContDiff ℝ 40 (fun τ => Gb (zeroCoord l₀ τ)) := hGb.comp (zeroCoord l₀).contDiff
    have hu : ContDiff ℝ 40 u := hGb.sub hP
    have hb := N.interpolation_bound hI hk u hu (D - 2) (supportDiam y c) hspan ?_ ?_
    · have e0 : iteratedFDeriv ℝ k u 0 (fun l => Pi.single l 1) =
          iteratedFDeriv ℝ k (fun τ => R.blockDensity n y (perturb c X τ V)) 0 (fun l => Pi.single l 1) := by
        rw [hu_def, fun_iteratedFDeriv_sub_apply (hGb.of_le (by exact_mod_cast (by omega : k ≤ 40))).contDiffAt
          (hP.of_le (by exact_mod_cast (by omega : k ≤ 40))).contDiffAt, ContinuousMultilinearMap.sub_apply,
          iteratedFDeriv_comp_zeroCoord_eq_zero Gb hGb (by omega) l₀, hzero k, sub_zero]
      rw [hdM, ← e0]
      exact hb
    · intro τ ht
      have hPτ : ‖zeroCoord l₀ τ‖ ≤ R.params.threshold / 2 ^ 11 := (norm_zeroCoord_apply_le l₀ τ).trans ht
      have hm1 : 1 ≤ D - 2 := by omega
      have hside : 2 * (D - 2) + 2 < n := by
        have := two_mul_supDist_le y (c l₀).1
        rw [← hl₀] at this
        omega
      have hag : FieldsAgreeNear (perturb c X τ V) (perturb c X (zeroCoord l₀ τ) V) y y (D - 2) :=
        fieldsAgreeNear_perturb_drop c X τ _ V y (D - 2) l₀
          (fun l hl => by rw [zeroCoord_apply, if_neg hl])
          (fun b hb => ne_bondFrom_of_lt y (c l₀) (D - 2) (by rw [← hl₀]; omega) b hb)
      have hf := hfar (perturb c X τ V) (perturb c X (zeroCoord l₀ τ) V) y y (D - 2) hm1 hside hside
        (hcold τ ht) (hcold _ hPτ) hag
      have hpos := Real.exp_pos (-(ch * R.coupling) - R.params.rt * ((D - 2 : ℕ) : ℝ) / 2 ^ 8)
      simp only [hu_def]
      rw [hval τ ht, hval _ hPτ]
      linarith
    · intro τ ht
      have hPτ : ‖zeroCoord l₀ τ‖ ≤ R.params.threshold / 2 ^ 11 := (norm_zeroCoord_apply_le l₀ τ).trans ht
      rw [hu_def, fun_iteratedFDeriv_sub_apply hGb.contDiffAt hP.contDiffAt]
      refine (norm_sub_le _ _).trans ?_
      have h5 := hder τ ht
      have h6 := (norm_iteratedFDeriv_comp_zeroCoord_le Gb hGb (le_refl 40) l₀ τ).trans (hder _ hPτ)
      linarith
  · have hb := N.interpolation_bound hI hk Gb hGb (D - 2) (supportDiam y c) hspan
      (fun τ ht => by
        rw [hval τ ht]
        exact (abs_blockDensity_le hA hn y _ (hcold τ ht) N.exp_le_half).trans (N.size_le (D - 2) (by omega)))
      (fun τ ht => (hder τ ht).trans (by linarith))
    rw [hdM, ← hzero k]
    exact hb
theorem CouplingBounds.four_mul_exp_le (N : CouplingBounds R ch C Cm) :
    4 * Real.exp (-(7 * ch * R.coupling)) ≤
      2 * Real.exp (-(ch * R.coupling) - R.params.rt * ((0 : ℕ) : ℝ) / 2 ^ 8) := by
  have h1 := N.one_le_gasRate_mul
  have e : -(7 * ch * R.coupling) = -(ch * R.coupling) + -(6 * ch * R.coupling) := by ring
  have e2 : -(ch * R.coupling) - R.params.rt * ((0 : ℕ) : ℝ) / 2 ^ 8 = -(ch * R.coupling) := by simp
  rw [e, Real.exp_add, e2]
  have h2 : Real.exp (-(6 * ch * R.coupling)) ≤ 1 / 2 := by
    have h3 : (6 : ℝ) ≤ 6 * ch * R.coupling := by nlinarith
    have h4 : Real.exp (-(6 * ch * R.coupling)) ≤ Real.exp (-6) := Real.exp_le_exp.mpr (by linarith)
    have h5 : (2 : ℝ) ≤ Real.exp 6 := by
      have := Real.add_one_le_exp (6 : ℝ)
      linarith
    have h6 : Real.exp (-6) ≤ 1 / 2 := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by norm_num) h5
    linarith
  have h7 := Real.exp_pos (-(ch * R.coupling))
  nlinarith
theorem blockDensity_local (N : CouplingBounds R ch C Cm) (hI : SmallOrderInterpolation Cm)
    (hA : R.MarkedIntegralStable ch) (hB : R.DensitiesLocal ch) (hS : R.LogMarkedIntegralSmooth C) {n' : ℕ}
    [NeZero n] [NeZero n'] (hn : R.params.n₀ ≤ n) (hn' : R.params.n₀ ≤ n') (y : TorusSite n)
    (y' : TorusSite n') (V : TorusField n) (V' : TorusField n') (m : ℕ) (hs : 2 * m + 2 < n)
    (hs' : 2 * m + 2 < n') (hV : IsCold R.params.threshold V) (hV' : IsCold R.params.threshold V')
    (hag : FieldsAgreeNear V V' y y' m) {k : ℕ} (h : Fin k → (Fin 4 → ℤ) × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hk : k ≤ 2) (hh : ∀ l, BondOffsetInBox m (h l))
    (hX : AreUnitVectors X) :
    |mixedDeriv (R.blockDensity n y) V (fun l => bondFrom y (h l)) X -
        mixedDeriv (R.blockDensity n' y') V' (fun l => bondFrom y' (h l)) X| ≤
      Real.exp (-(ch * R.coupling) / 2) / R.params.weight m := by
  have hσ := N.threshold_pos
  have hk3 : k ≤ 3 := by omega
  obtain ⟨Gb, hGb, hval, hder, hzero⟩ :=
    exists_smooth_blockDensity N hS hn y V hV hk3 (fun l => bondFrom y (h l)) X hX
  obtain ⟨Gb', hGb', hval', hder', hzero'⟩ :=
    exists_smooth_blockDensity N hS hn' y' V' hV' hk3 (fun l => bondFrom y' (h l)) X hX
  have hxC : 0 < R.coupling ^ C := Real.rpow_pos_of_pos (by linarith [N.one_le_coupling]) _
  have hcold : ∀ τ : Fin k → ℝ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 →
      IsCold (9 / 8 * R.params.threshold) (perturb (fun l => bondFrom y (h l)) X τ V) :=
    fun τ ht => isCold_perturb hk3 _ X hX τ V R.params.threshold hσ hV (by linarith)
  have hcold' : ∀ τ : Fin k → ℝ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 →
      IsCold (9 / 8 * R.params.threshold) (perturb (fun l => bondFrom y' (h l)) X τ V') :=
    fun τ ht => isCold_perturb hk3 _ X hX τ V' R.params.threshold hσ hV' (by linarith)
  set u : (Fin k → ℝ) → ℝ := fun τ => Gb τ - Gb' τ with hu_def
  have hu : ContDiff ℝ 40 u := hGb.sub hGb'
  have hb := N.interpolation_bound hI hk3 u hu m m (by omega) ?_ ?_
  · have e0 : iteratedFDeriv ℝ k u 0 (fun l => Pi.single l 1) =
        mixedDeriv (R.blockDensity n y) V (fun l => bondFrom y (h l)) X -
          mixedDeriv (R.blockDensity n' y') V' (fun l => bondFrom y' (h l)) X := by
      rw [hu_def, fun_iteratedFDeriv_sub_apply (hGb.of_le (by exact_mod_cast (by omega : k ≤ 40))).contDiffAt
        (hGb'.of_le (by exact_mod_cast (by omega : k ≤ 40))).contDiffAt,
        ContinuousMultilinearMap.sub_apply, hzero k, hzero' k]
      rfl
    rw [← e0]
    exact hb
  · intro τ ht
    simp only [hu_def]
    rw [hval τ ht, hval' τ ht]
    by_cases hm : 1 ≤ m
    · have hf := hB n n' hn hn' _ _ y y' m hm hs hs' (hcold τ ht) (hcold' τ ht)
        (fieldsAgreeNear_perturb h X τ V V' y y' m hs hs' hh hag)
      have hpos := Real.exp_pos (-(ch * R.coupling) - R.params.rt * (m : ℝ) / 2 ^ 8)
      linarith
    · have hm0 : m = 0 := by omega
      subst hm0
      have h1 := abs_blockDensity_le hA hn y _ (hcold τ ht) N.exp_le_half
      have h2 := abs_blockDensity_le hA hn' y' _ (hcold' τ ht) N.exp_le_half
      have h3 := N.four_mul_exp_le
      have h4 := abs_sub (R.blockDensity n y (perturb (fun l => bondFrom y (h l)) X τ V))
        (R.blockDensity n' y' (perturb (fun l => bondFrom y' (h l)) X τ V'))
      linarith
  · intro τ ht
    rw [hu_def, fun_iteratedFDeriv_sub_apply hGb.contDiffAt hGb'.contDiffAt]
    refine (norm_sub_le _ _).trans ?_
    have h5 := hder τ ht
    have h6 := hder' τ ht
    linarith
end
section
variable {n : ℕ} {R : StepSetup} {ch C Cm : ℝ}
theorem isCold_nine_eighths (hσ : 0 < R.params.threshold) (V : TorusField n) (hV : IsCold R.params.threshold V) :
    IsCold (9 / 8 * R.params.threshold) V := fun x μ ν h => by
  have := hV x μ ν h
  linarith
theorem blockDensity_gauge (hσ : 0 < R.params.threshold) (hG : R.MarkedIntegralInvariant) [NeZero n]
    (hn : R.params.n₀ ≤ n) (y : TorusSite n) (γ : TorusSite n → UnitQuaternion) (V : TorusField n)
    (hV : IsCold R.params.threshold V) :
    R.blockDensity n y (gaugeTransform γ V) = R.blockDensity n y V := by
  rw [blockDensity_eq, blockDensity_eq, blockDensityAt_eq_sum, blockDensityAt_eq_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [(hG n hn V A (isCold_nine_eighths hσ V hV)).1 γ, (hG n hn V _ (isCold_nine_eighths hσ V hV)).1 γ]
theorem blockDensity_translate (hσ : 0 < R.params.threshold) (hG : R.MarkedIntegralInvariant) [NeZero n]
    (hn : R.params.n₀ ≤ n) (y u : TorusSite n) (V : TorusField n) (hV : IsCold R.params.threshold V) :
    R.blockDensity n y (TorusFields.translate u V) = R.blockDensity n (y + u) V := by
  rw [blockDensity_eq, blockDensity_eq]
  unfold StepSettings.StepSetup.blockDensityAt
  let e : TorusSite n ≃ TorusSite n := Equiv.addRight u
  let Φ : (TorusSite n → ℝ) ≃ᵐ (TorusSite n → ℝ) := MeasurableEquiv.piCongrLeft (fun _ => ℝ) e
  have hmp : MeasurePreserving Φ (randomOrderLaw n) (randomOrderLaw n) :=
    measurePreserving_piCongrLeft (fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)) e
  have hΦ : ∀ (w : TorusSite n → ℝ) (i : TorusSite n), Φ w (i + u) = w i := by
    intro w i
    exact Equiv.piCongrLeft_apply_apply (fun _ => ℝ) e w i
  have hE : ∀ w : TorusSite n → ℝ, MarkedIntegrals.precedingBlocks (Φ w) (y + u) =
      (MarkedIntegrals.precedingBlocks w y).image (· + u) := by
    intro w
    ext j
    simp only [MarkedIntegrals.precedingBlocks, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro h
      refine ⟨j - u, ?_, by abel⟩
      have e1 := hΦ w (j - u)
      have e2 := hΦ w y
      rw [sub_add_cancel] at e1
      rw [← e1, ← e2]
      exact h
    · rintro ⟨i, hi, rfl⟩
      rw [hΦ, hΦ]
      exact hi
  have hc := isCold_nine_eighths hσ V hV
  rw [← hmp.integral_comp Φ.measurableEmbedding (fun w' =>
    Real.log (R.markedIntegral (MarkedIntegrals.precedingBlocks w' (y + u)) V) -
      Real.log (R.markedIntegral (insert (y + u) (MarkedIntegrals.precedingBlocks w' (y + u))) V))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [hE, (hG n hn V (MarkedIntegrals.precedingBlocks w y) hc).2 u,
    (hG n hn V (insert y (MarkedIntegrals.precedingBlocks w y)) hc).2 u, Finset.image_insert]
theorem markedIntegral_empty (hArr : R.IsSymmetricWeight) (hrow : R.HasExpansions) (hL : 0 < R.params.side)
    [NeZero n] (hn : R.params.n₀ ≤ n) (V : TorusField n) :
    R.markedIntegral ∅ V = kernelImage R.params R.coupling R.functional n V := by
  have hle : n ≤ n * R.params.side := Nat.le_mul_of_pos_right n hL
  have hbs : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hlow : ∀ W, R.avoidingPart ∅ W = R.functional (n * R.params.side) W := by
    intro W
    unfold StepSettings.StepSetup.avoidingPart
    have hs := hrow.2.sum (n * R.params.side) hbs W
    have hD := (hArr (n * R.params.side) (hn.trans hle)).2.1 W
    have hb : sitesInBlocks R.params.side (∅ : Finset (TorusSite n)) = ∅ := by
      unfold sitesInBlocks
      simp
    refine (congrArg ENNReal.toReal (?_ : _ = ENNReal.ofReal (R.functional _ W))).trans
      (ENNReal.toReal_ofReal hD)
    rw [← hs]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext Y
    classical
    constructor
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2.1⟩
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2, by
        rw [hb]
        exact Finset.disjoint_empty_right _⟩
  unfold StepSettings.StepSetup.markedIntegral kernelImage
  rw [dif_neg (NeZero.ne n)]
  have hb0 : MarkedIntegrals.chartBondsInBlocks R.params.side (∅ : Finset (TorusSite n)) = ∅ := by
    unfold MarkedIntegrals.chartBondsInBlocks
    simp
  simp only [hb0, Finset.prod_empty, mul_one, hlow]
end
section
variable {R : StepSetup} {ch C Cm : ℝ}
theorem blockDensity_small_and_factorization (N : CouplingBounds R ch C Cm) (hI : SmallOrderInterpolation Cm)
    (hA : R.MarkedIntegralStable ch) (hB : R.DensitiesLocal ch) (hS : R.LogMarkedIntegralSmooth C)
    (hG : R.MarkedIntegralInvariant) (hT : SumIncrementsAlongOrder) (hArr : R.IsSymmetricWeight)
    (hrow : R.HasExpansions) (hL : 0 < R.params.side) :
    IsSmallDensity R.params (Real.exp (-(ch * R.coupling / 2))) R.blockDensity ∧
      ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold R.params.threshold V →
        0 < R.markedIntegral Finset.univ V ∧ 0 < kernelImage R.params R.coupling R.functional n V ∧
        Real.log (kernelImage R.params R.coupling R.functional n V) =
          Real.log (R.markedIntegral Finset.univ V) + ∑ Y, R.blockDensity n Y V := by
  have hσ := N.threshold_pos
  have e : -(ch * R.coupling / 2) = -(ch * R.coupling) / 2 := by ring
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n _ hn y V hV k c X
    have h0 : IsCold (9 / 8 * R.params.threshold) (perturb c X (0 : Fin k → ℝ) V) := by
      rw [perturb_zero]
      exact isCold_nine_eighths hσ V hV
    exact (contDiffAt_blockDensity_perturb hS hn y V c X 0 h0).of_le (by norm_num)
  · intro n _ hn y γ V hV
    exact blockDensity_gauge hσ hG hn y γ V hV
  · intro n _ hn y u V hV
    exact blockDensity_translate hσ hG hn y u V hV
  · intro n _ hn y V hV k c X h1 hk hX
    rw [e]
    exact blockDensity_decay N hI hA hB hS hn y V hV c X h1 hk hX
  · intro n n' _ _ hn hn' y y' V V' m hs hs' hV hV' hag k h X hk hh hX
    rw [e]
    exact blockDensity_local N hI hA hB hS hn hn' y y' V V' m hs hs' hV hV' hag h X hk hh hX
  · intro n _ hn V hV
    have hc := isCold_nine_eighths hσ V hV
    have y0 : TorusSite n := 0
    have h1 := (hA n hn V hc Finset.univ y0).1
    have h2 := (hA n hn V hc ∅ y0).1
    rw [markedIntegral_empty hArr hrow hL hn V] at h2
    refine ⟨h1, h2, ?_⟩
    have h3 := sum_blockDensityAt hT R V
    rw [markedIntegral_empty hArr hrow hL hn V] at h3
    have h4 : ∑ Y, R.blockDensity n Y V = ∑ Y, R.blockDensityAt Y V :=
      Finset.sum_congr rfl fun Y _ => blockDensity_eq R Y V
    rw [h4, h3]
    ring
theorem gasRate_pos (T : ParameterAssignment) (hT : T.Admissible) : 0 < T.gasRate := by apply _root_.YangMills.Construction.StepFloors.gasRate_pos <;> assumption
theorem n₁_pos_of_admissible (T : ParameterAssignment) (hT : T.Admissible) : 0 < T.n₁ := by apply _root_.YangMills.Construction.StepFloors.n₁_pos <;> assumption
theorem couplingBounds_of_admissible (T : ParameterAssignment) (hT : T.Admissible) (R : StepSetup) (y : ℝ)
    (hℓ : R.params = T.stepParameters y) (C Cm : ℝ) (hC : 0 ≤ C) (hCm : 0 < Cm)
    (hx1 : 1 ≤ R.coupling)
    (hbig : Cm * (2 / (T.threshold / 2 ^ 11) ^ 3 + 8) * (2 + 4 / T.n₁) ^ 16000 *
      Real.exp (T.rt / 2 ^ 8) ≤ R.coupling)
    (hF : T.FloorConditions (C + 1) 1 R.coupling) : CouplingBounds R T.gasRate C Cm := by
  have eσ : R.params.threshold = T.threshold := by rw [hℓ]; rfl
  have ert : R.params.rt = T.rt := by rw [hℓ]; rfl
  have en : R.params.n₁ = T.n₁ := by rw [hℓ]; rfl
  have hch := gasRate_pos T hT
  obtain ⟨y1, y2, y3⟩ := hF.gas_powers
  have hrt0 := hT.rt_pos
  have hp : 1 ≤ R.coupling ^ (1 / 90 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hm : (0 : ℝ) ≤ 16 * T.rt * boxRadius R.coupling := by positivity
  refine ⟨?_, ?_, ?_, ?_, hch, hx1, hC, hCm, ?_, ?_, ?_, ?_⟩
  · rw [eσ]; exact hT.σ_pos
  · rw [eσ]; exact hT.σ_one
  · rw [ert]; exact hrt0
  · rw [en]; exact n₁_pos_of_admissible T hT
  · rw [eσ, ert, en]; exact hbig
  · intro m
    rw [ert, en]
    have := y3 m
    have e : -(1 / 4) * (T.gasRate * R.coupling + T.rt * m / 2 ^ 8) =
        -(1 / 4 * (T.gasRate * R.coupling + T.rt * m / 2 ^ 8)) := by
      ring
    rw [e]
    exact this
  · clear hbig
    linarith
  · clear hbig
    rw [ert]
    linarith
end
theorem _root_.YangMills.Construction.ClusterExpansionOfAStep.hotFactorization_of (hGas : StepGas.ColdGasBounds)
    (hDer : ClusterExpansionOfAStep.LogMarkedIntegralDerivativesBounded)
    (hCar : StepInvariance.MarkedIntegralInvariance)
    (hTie : StepSettings.FullMarkedIntegralIsColdImage)
    (hI : LandauKolmogorovMultivariateAtZero) (hRO : SumIncrementsAlongOrder)
    (hFl : StepFloors.EventuallyFloorConditions) : ClusterExpansionOfAStep.HotFactorization := by
  obtain ⟨r1, p1, h1⟩ := hGas
  obtain ⟨r2, p2, h2⟩ := hDer
  obtain ⟨r3, p3, h3⟩ := hCar
  obtain ⟨Cm, hCm, hInt⟩ := exists_smallOrderInterpolation hI
  refine ⟨fun c => min (r1 c) (min (r2 c) (r3 c)), fun c => lt_min (p1 c) (lt_min (p2 c) (p3 c)), ?_⟩
  intro T hT hrt
  obtain ⟨ya, ha⟩ := h1 T hT (hrt.trans (min_le_left _ _))
  obtain ⟨C, yb, hC, hb⟩ := h2 T hT (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨yc, hc⟩ := h3 T hT (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨yd, hd⟩ := hTie T hT
  obtain ⟨yf, hf⟩ := hFl T hT (C + 1) 1 (by linarith) one_pos
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Cm * (2 / (T.threshold / 2 ^ 11) ^ 3 + 8) * (2 + 4 / T.n₁) ^ 16000 *
      Real.exp (T.rt / 2 ^ 8) := ⟨_, rfl⟩
  refine ⟨max (max (max ya yb) (max yc yd)) (max yf (max K 1)), ?_⟩
  intro y hy R hOn hArr
  have hy1 := (le_max_left _ _).trans hy
  have hy2 := (le_max_right _ _).trans hy
  have hya : ya ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy1
  have hyb : yb ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy1
  have hyc : yc ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy1
  have hyd : yd ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy1
  have hyf : yf ≤ y := (le_max_left _ _).trans hy2
  have hyK : K ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy2
  have hy1' : (1 : ℝ) ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy2
  have hx := hOn.le_coupling
  have N : CouplingBounds R T.gasRate C Cm :=
    couplingBounds_of_admissible T hT R y hOn.params_eq C Cm hC hCm (hy1'.trans hx) (hK ▸ hyK.trans hx)
      (hf R.coupling (hyf.trans hx))
  obtain ⟨hA, hB⟩ := ha y hya R hOn hArr
  have hS := hb y hyb R hOn hArr
  have hG := hc y hyc R hOn hArr
  have hL : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne R.params.side)
  obtain ⟨s1, s2⟩ := blockDensity_small_and_factorization N hInt hA hB hS hG hRO hArr hOn.isStep.1 hL
  have eσ : R.params.threshold = T.threshold := by rw [hOn.params_eq]; rfl
  have en : R.params.n₀ = T.n₀ := by rw [hOn.params_eq]; rfl
  refine ⟨s1, fun n _ hn V hV => ?_⟩
  have hV' : IsCold R.params.threshold V := by rw [eσ]; exact hV
  obtain ⟨t1, t2, t3⟩ := s2 n (by rw [en]; exact hn) V hV'
  have tie := hd y hyd R hOn hArr n hn V (by
    have := isCold_nine_eighths N.threshold_pos V hV'
    rw [eσ] at this
    exact this)
  rw [← tie]
  exact ⟨t1, t2, t3⟩
end YangMills.Construction.ClusterExpansionOfAStep.BlockDensities
end

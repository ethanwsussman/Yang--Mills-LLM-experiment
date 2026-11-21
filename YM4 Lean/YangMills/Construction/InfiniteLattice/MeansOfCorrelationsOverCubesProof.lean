import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.InfiniteLattice.ConditionalExpectationGivenTheInvariantField
import YangMills.Construction.InfiniteLattice.FunctionsFixedByTheTranslations
import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.InvariantFunctionsLongRangeOrderAndErgodicMeasures
import YangMills.Construction.InfiniteLattice.MeansOfCorrelationsOverCubes
import YangMills.Construction.InfiniteLattice.ReflectionsOfOneFamilyProof
import YangMills.Construction.Towers.SumsOverThePointsOfThePlaneWavesProof
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory YangMills.Construction.InfiniteLattice
open scoped Topology ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.LatticePhases
namespace CubeErgodic
section MeanErgodic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def intCube (n : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) n
theorem mem_intCube {n : ℕ} {k : Fin 4 → ℤ} :
    k ∈ intCube n ↔ ∀ μ, -(n : ℤ) ≤ k μ ∧ k μ ≤ n := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.mem_cubeBox <;> assumption
theorem card_Icc_neg_natCast (n : ℕ) : (Finset.Icc (-(n : ℤ)) n).card = 2 * n + 1 := by apply _root_.YangMills.Construction.Tower.PlaneWaveSums.card_Icc_neg_self <;> assumption
theorem card_intCube (n : ℕ) : (intCube n).card = (2 * n + 1) ^ 4 := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.card_cubeBox <;> assumption
theorem card_intCube_face (n : ℕ) (μ : Fin 4) :
    ((intCube n).filter fun k => k μ = -(n : ℤ)).card = (2 * n + 1) ^ 3 := by
  have hface : ((intCube n).filter fun k => k μ = -(n : ℤ)) =
      Fintype.piFinset (Function.update (fun _ : Fin 4 => Finset.Icc (-(n : ℤ)) n) μ
        {-(n : ℤ)}) := by
    ext k
    simp only [Finset.mem_filter, mem_intCube, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hk, hkμ⟩ ν
      by_cases hν : ν = μ
      · subst hν
        simpa using hkμ
      · simpa [Function.update_of_ne hν] using hk ν
    · intro hk
      have hμ : k μ = -(n : ℤ) := by simpa using hk μ
      refine ⟨fun ν => ?_, hμ⟩
      by_cases hν : ν = μ
      · subst hν
        omega
      · simpa [Function.update_of_ne hν] using hk ν
  rw [hface, Fintype.card_piFinset]
  fin_cases μ <;> simp [Fin.prod_univ_four, Function.update, -Int.card_Icc, card_Icc_neg_natCast] <;> ring
variable (T : (Fin 4 → ℤ) → H →ₗᵢ[ℂ] H)
def cubeAverage (n : ℕ) (x : H) : H :=
  ((intCube n).card : ℂ)⁻¹ • ∑ k ∈ intCube n, T k x
theorem cubeAverage_add (n : ℕ) (x y : H) :
    cubeAverage T n (x + y) = cubeAverage T n x + cubeAverage T n y := by
  simp [cubeAverage, Finset.sum_add_distrib, smul_add]
theorem cubeAverage_sub (n : ℕ) (x y : H) :
    cubeAverage T n (x - y) = cubeAverage T n x - cubeAverage T n y := by
  simp [cubeAverage, Finset.sum_sub_distrib, smul_sub]
theorem cubeAverage_smul (n : ℕ) (c : ℂ) (x : H) :
    cubeAverage T n (c • x) = c • cubeAverage T n x := by
  simp [cubeAverage, Finset.smul_sum, smul_comm c]
theorem card_intCube_pos (n : ℕ) : 0 < (intCube n).card := by
  rw [card_intCube]
  positivity
theorem norm_cubeAverage_le (n : ℕ) (x : H) : ‖cubeAverage T n x‖ ≤ ‖x‖ := by
  have hc : (0 : ℝ) < (intCube n).card := by exact_mod_cast card_intCube_pos n
  have hs : ‖∑ k ∈ intCube n, T k x‖ ≤ (intCube n).card * ‖x‖ := by
    refine (norm_sum_le _ _).trans ?_
    simp
  rw [cubeAverage, norm_smul, norm_inv, Complex.norm_natCast]
  calc ((intCube n).card : ℝ)⁻¹ * ‖∑ k ∈ intCube n, T k x‖
      ≤ ((intCube n).card : ℝ)⁻¹ * ((intCube n).card * ‖x‖) := by gcongr
    _ = ‖x‖ := by field_simp
def coordVector (μ : Fin 4) : Fin 4 → ℤ := Pi.single μ 1
theorem norm_cubeAverage_sub_le (hadd : ∀ k l x, T (k + l) x = T k (T l x)) (n : ℕ) (μ : Fin 4)
    (y : H) :
    ‖cubeAverage T n (y - T (coordVector μ) y)‖ ≤ 2 / (2 * n + 1) * ‖y‖ := by
  set e := coordVector μ with he
  set C := intCube n with hC
  set C' := C.map (addRightEmbedding e) with hC'
  have hshifted : ∑ k ∈ C, T k (T e y) = ∑ k ∈ C', T k y := by
    rw [hC', Finset.sum_map]
    exact Finset.sum_congr rfl fun k _ => by simp [hadd]
  have hcard : C'.card = C.card := Finset.card_map _
  have hsub : C \ C' ⊆ C.filter fun k => k μ = -(n : ℤ) := by
    intro k hk
    obtain ⟨hkC, hkC'⟩ := Finset.mem_sdiff.mp hk
    refine Finset.mem_filter.mpr ⟨hkC, ?_⟩
    by_contra hne
    apply hkC'
    have hm := mem_intCube.mp hkC
    refine Finset.mem_map.mpr ⟨k - e, mem_intCube.mpr fun ν => ?_, by simp⟩
    by_cases hν : ν = μ
    · subst hν
      have := hm ν
      have he1 : e ν = 1 := by simp [he, coordVector]
      simp only [Pi.sub_apply, he1]
      omega
    · have he0 : e ν = 0 := by simp [he, coordVector, Pi.single_eq_of_ne hν]
      simpa [he0] using hm ν
  have hleft : (C \ C').card ≤ (2 * n + 1) ^ 3 := by
    rw [← card_intCube_face n μ]
    exact Finset.card_le_card hsub
  have hright : (C' \ C).card ≤ (2 * n + 1) ^ 3 := by
    have := Finset.card_sdiff_comm hcard.symm
    omega
  have hbound : ∀ S : Finset (Fin 4 → ℤ), ‖∑ k ∈ S, T k y‖ ≤ S.card * ‖y‖ := fun S => by
    refine (norm_sum_le _ _).trans ?_
    simp
  have hdiff : ‖∑ k ∈ C, T k (y - T e y)‖ ≤ 2 * ((2 * n + 1 : ℝ) ^ 3) * ‖y‖ := by
    have hsplit : ∑ k ∈ C, T k (y - T e y) =
        ∑ k ∈ C \ C', T k y - ∑ k ∈ C' \ C, T k y := by
      rw [Finset.sum_sdiff_sub_sum_sdiff]
      simp only [map_sub, Finset.sum_sub_distrib, hshifted]
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    have hl : ((C \ C').card : ℝ) ≤ (2 * n + 1 : ℝ) ^ 3 := by exact_mod_cast hleft
    have hr : ((C' \ C).card : ℝ) ≤ (2 * n + 1 : ℝ) ^ 3 := by exact_mod_cast hright
    have hy := norm_nonneg y
    have := hbound (C \ C')
    have := hbound (C' \ C)
    nlinarith
  have hcc : (C.card : ℝ) = (2 * (n : ℝ) + 1) ^ 4 := by
    rw [hC, card_intCube]
    push_cast
    ring
  rw [cubeAverage, norm_smul, norm_inv, Complex.norm_natCast, ← hC, hcc]
  calc ((2 * (n : ℝ) + 1) ^ 4)⁻¹ * ‖∑ k ∈ C, T k (y - T e y)‖
      ≤ ((2 * (n : ℝ) + 1) ^ 4)⁻¹ * (2 * ((2 * n + 1 : ℝ) ^ 3) * ‖y‖) := by gcongr
    _ = 2 / (2 * n + 1) * ‖y‖ := by field_simp
theorem tendsto_cubeAverage_sub (hadd : ∀ k l x, T (k + l) x = T k (T l x)) (μ : Fin 4) (y : H) :
    Tendsto (fun n => cubeAverage T n (y - T (coordVector μ) y)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => 2 / (2 * (n : ℝ) + 1) * ‖y‖) atTop (𝓝 0) := by
    have hgrow : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    simpa using (hgrow.const_div_atTop 2).mul_const ‖y‖
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => norm_cubeAverage_sub_le T hadd n μ y) hlim
def invariantSubspace : Submodule ℂ H where
  carrier := {x | ∀ k, T k x = x}
  add_mem' hx hy k := by simp [hx k, hy k]
  zero_mem' k := by simp
  smul_mem' c x hx k := by simp [hx k]
theorem mem_invariantSubspace {x : H} : x ∈ invariantSubspace T ↔ ∀ k, T k x = x := Iff.rfl
theorem isClosed_invariantSubspace : IsClosed (invariantSubspace T : Set H) := by
  have : (invariantSubspace T : Set H) = ⋂ k, {x | T k x = x} := by
    ext x
    simp [mem_invariantSubspace]
  rw [this]
  exact isClosed_iInter fun k => isClosed_eq (T k).continuous continuous_id
theorem map_coordVector_eq_of_inner_eq_zero (μ : Fin 4) {x : H}
    (h : ⟪x - T (coordVector μ) x, x⟫_ℂ = 0) : T (coordVector μ) x = x := by
  set t := T (coordVector μ) x with ht
  have hn : ‖t‖ = ‖x‖ := (T (coordVector μ)).norm_map x
  have hxt : ⟪x, x⟫_ℂ = ⟪t, x⟫_ℂ := by
    rw [inner_sub_left, sub_eq_zero] at h
    exact h
  have hsq : ‖t - x‖ ^ 2 = 0 := by
    have hre : RCLike.re ⟪t, x⟫_ℂ = ‖x‖ ^ 2 := by
      rw [← hxt]
      exact inner_self_eq_norm_sq x
    rw [@norm_sub_sq ℂ, hre, hn]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq))
theorem mem_invariantSubspace_of_coordVector (h0 : ∀ x, T 0 x = x)
    (hadd : ∀ k l x, T (k + l) x = T k (T l x)) {x : H}
    (h : ∀ μ, T (coordVector μ) x = x) : x ∈ invariantSubspace T := by
  let G : AddSubgroup (Fin 4 → ℤ) :=
    { carrier := {k | T k x = x}
      add_mem' := fun {k l} hk hl => by
        change T k x = x at hk
        change T l x = x at hl
        change T (k + l) x = x
        rw [hadd, hl, hk]
      zero_mem' := h0 x
      neg_mem' := fun {k} hk => by
        change T k x = x at hk
        change T (-k) x = x
        have := hadd (-k) k x
        rw [neg_add_cancel, h0, hk] at this
        exact this.symm }
  intro k
  have hk : k = ∑ μ, k μ • coordVector μ := by
    ext ν
    simp [Finset.sum_apply, coordVector, Pi.single_apply]
  exact show k ∈ G from by
    rw [hk]
    exact G.sum_mem fun μ _ => G.zsmul_mem (h μ) _
variable [CompleteSpace H]
instance : CompleteSpace (invariantSubspace T) :=
  (isClosed_invariantSubspace T).completeSpace_coe
theorem tendsto_cubeAverage (h0 : ∀ x, T 0 x = x) (hadd : ∀ k l x, T (k + l) x = T k (T l x)) (x : H) :
    Tendsto (fun n => cubeAverage T n x) atTop (𝓝 ((invariantSubspace T).starProjection x)) := by
  set K := invariantSubspace T with hK
  let S : Submodule ℂ H := Submodule.span ℂ (⋃ μ, Set.range fun y => y - T (coordVector μ) y)
  have hS : ∀ z ∈ S, Tendsto (fun n => cubeAverage T n z) atTop (𝓝 0) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨μ, y, rfl⟩ := Set.mem_iUnion.mp hz
      exact tendsto_cubeAverage_sub T hadd μ y
    | zero => simp [cubeAverage]
    | add u v _ _ hu hv => simpa [cubeAverage_add] using hu.add hv
    | smul c u _ hu => simpa [cubeAverage_smul] using hu.const_smul c
  have hperp : Sᗮ ≤ K := by
    intro v hv
    refine mem_invariantSubspace_of_coordVector T h0 hadd fun μ => ?_
    refine map_coordVector_eq_of_inner_eq_zero T μ ?_
    exact (Submodule.mem_orthogonal _ _).mp hv _
      (Submodule.subset_span (Set.mem_iUnion.mpr ⟨μ, v, rfl⟩))
  have hclosure : Kᗮ ≤ S.topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    exact Submodule.orthogonal_le hperp
  have hz : ∀ z ∈ S.topologicalClosure, Tendsto (fun n => cubeAverage T n z) atTop (𝓝 0) := by
    intro z hz
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.mp hz (ε / 2) (half_pos hε)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hS w hw) (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have hwn := hN n hn
    rw [dist_zero_right] at hwn ⊢
    have hzwn : ‖cubeAverage T n (z - w)‖ < ε / 2 :=
      (norm_cubeAverage_le T n _).trans_lt (by rwa [← dist_eq_norm])
    have hdecomp : cubeAverage T n z = cubeAverage T n (z - w) + cubeAverage T n w := by
      rw [← cubeAverage_add, sub_add_cancel]
    rw [hdecomp]
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hfix : ∀ n, cubeAverage T n (K.starProjection x) = K.starProjection x := by
    intro n
    have hc : ((intCube n).card : ℂ) ≠ 0 := by
      exact_mod_cast (card_intCube_pos n).ne'
    have hf : ∀ k, T k (K.starProjection x) = K.starProjection x :=
      (mem_invariantSubspace T).mp (K.starProjection_apply_mem x)
    simp only [cubeAverage, hf, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    rw [inv_mul_cancel₀ hc, one_smul]
  have hsplit : ∀ n, cubeAverage T n x =
      K.starProjection x + cubeAverage T n (x - K.starProjection x) := by
    intro n
    rw [cubeAverage_sub, hfix]
    abel
  simp only [hsplit]
  simpa using tendsto_const_nhds.add
    (hz _ (hclosure (K.sub_starProjection_mem_orthogonal x)))
end MeanErgodic
section Shifts
variable {a : ℝ}
def latticePointOf (a : ℝ) (k : Fin 4 → ℤ) : LatticePoint a :=
  ⟨fun μ => (k μ : ℝ) * a, k, fun _ => rfl⟩
theorem latticePointOf_add (k l : Fin 4 → ℤ) :
    latticePointOf a (k + l) = latticePointOf a k + latticePointOf a l :=
  Subtype.ext (funext fun μ => by simp [latticePointOf, add_mul])
theorem latticePointOf_zero : latticePointOf a 0 = 0 :=
  Subtype.ext (funext fun μ => by simp [latticePointOf])
theorem exists_latticePointOf (v : LatticePoint a) : ∃ k, latticePointOf a k = v := by
  obtain ⟨x, m, hm⟩ := v
  exact ⟨m, Subtype.ext (funext fun μ => (hm μ).symm)⟩
theorem latticePointOf_injective (ha : a ≠ 0) : Function.Injective (latticePointOf a) := by
  intro k l h
  funext μ
  have hkl : (k μ : ℝ) * a = (l μ : ℝ) * a := congrFun (congrArg Subtype.val h) μ
  exact_mod_cast mul_right_cancel₀ ha hkl
theorem latticePointOf_mem_iff (ha : 0 < a) (n : ℕ+) (k : Fin 4 → ℤ) :
    latticePointOf a k ∈ centredCubePoints a n ↔ k ∈ intCube n := by
  simp only [centredCubePoints, Set.mem_ofPred_eq, PeriodicLattice.supNormVec, Finset.sup'_le_iff,
    Finset.mem_univ, forall_const, mem_intCube]
  refine forall_congr' fun μ => ?_
  have hcoord : ((latticePointOf a k : LatticePoint a) : AmbientSpace) μ = (k μ : ℝ) * a := rfl
  rw [hcoord, abs_mul, abs_of_pos ha]
  have habs : |(k μ : ℝ)| ≤ ((n : ℕ) : ℝ) ↔ -(((n : ℕ)) : ℤ) ≤ k μ ∧ k μ ≤ ((n : ℕ) : ℤ) := by
    rw [abs_le]
    exact_mod_cast Iff.rfl
  rw [← habs]
  constructor
  · exact fun h => le_of_mul_le_mul_right h ha
  · exact fun h => mul_le_mul_of_nonneg_right h ha.le
theorem centredCubePoints_eq_image (ha : 0 < a) (n : ℕ+) :
    centredCubePoints a n = latticePointOf a '' (intCube n : Set (Fin 4 → ℤ)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := exists_latticePointOf y
    exact ⟨k, (latticePointOf_mem_iff ha n k).mp hy, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact (latticePointOf_mem_iff ha n k).mpr hk
variable {ν : Measure (GaugeField a)} [IsProbabilityMeasure ν]
theorem measurePreserving_shift (h : IsShiftInvariant ν) (v : LatticePoint a) :
    MeasurePreserving (shift v).pullbackField ν ν := by
  have hm := (shift v).continuous_pullbackField.measurable
  refine ⟨hm, Measure.ext fun E hE => ?_⟩
  rw [Measure.map_apply hm hE]
  have hobs : IsBoundedObservable (E.indicator fun _ => (1 : ℂ)) := by
    refine ⟨measurable_const.indicator hE, 1, fun U => ?_⟩
    by_cases hU : U ∈ E <;> simp [hU]
  have hI := h v _ hobs
  have hpre : ∀ U, (shift v).actOn (E.indicator fun _ => (1 : ℂ)) U =
      ((shift v).pullbackField ⁻¹' E).indicator (fun _ => (1 : ℂ)) U := fun U => rfl
  simp only [hpre] at hI
  rw [integral_indicator_const _ (hm hE), integral_indicator_const _ hE] at hI
  have hR : ν.real ((shift v).pullbackField ⁻¹' E) = ν.real E := by
    simpa using hI
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hR
def l2Shift (h : IsShiftInvariant ν) (k : Fin 4 → ℤ) : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 ν :=
  Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_shift h (latticePointOf a k))
theorem coeFn_l2Shift (h : IsShiftInvariant ν) (k : Fin 4 → ℤ) (X : Lp ℂ 2 ν) :
    l2Shift h k X =ᵐ[ν] fun U => X ((shift (latticePointOf a k)).pullbackField U) :=
  Lp.coeFn_compMeasurePreserving X (measurePreserving_shift h (latticePointOf a k))
theorem l2Shift_zero (h : IsShiftInvariant ν) (X : Lp ℂ 2 ν) : l2Shift h 0 X = X := by
  refine Lp.ext ((coeFn_l2Shift h 0 X).trans (ae_of_all _ fun U => ?_))
  simp only [latticePointOf_zero, shift_zero_pullbackField]
theorem l2Shift_add (h : IsShiftInvariant ν) (k l : Fin 4 → ℤ) (X : Lp ℂ 2 ν) :
    l2Shift h (k + l) X = l2Shift h k (l2Shift h l X) := by
  have hcomp := (measurePreserving_shift h
    (latticePointOf a k)).quasiMeasurePreserving.ae_eq_comp (coeFn_l2Shift h l X)
  refine Lp.ext ?_
  filter_upwards [coeFn_l2Shift h (k + l) X, coeFn_l2Shift h k (l2Shift h l X), hcomp] with U h2 h3 h4
  rw [h2, h3]
  simp only [Function.comp_apply] at h4
  rw [h4, latticePointOf_add, shift_pullbackField_add]
omit [IsProbabilityMeasure ν] in
theorem inner_eq_integral_conj_mul {X Y : Lp ℂ 2 ν} {X' Y' : GaugeField a → ℂ} (hX : X =ᵐ[ν] X')
    (hY : Y =ᵐ[ν] Y') : ⟪X, Y⟫_ℂ = ∫ U, conj (X' U) * Y' U ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with U h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]
theorem memLp_two_of_isBoundedObservable {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) :
    MemLp A 2 ν := by
  obtain ⟨hm, C, hC⟩ := hA
  exact MemLp.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
theorem isBoundedObservable_conj {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) :
    IsBoundedObservable fun U => conj (A U) := by apply _root_.YangMills.Construction.NormalFamilies.ReflectionIdentities.isBoundedObservable_conj <;> assumption
theorem l2Shift_toLp_ae (h : IsShiftInvariant ν) (k : Fin 4 → ℤ) {A : GaugeField a → ℂ}
    (hA : MemLp A 2 ν) :
    l2Shift h k (hA.toLp A) =ᵐ[ν] (shift (latticePointOf a k)).actOn A := by
  have hcomp := (measurePreserving_shift h
    (latticePointOf a k)).quasiMeasurePreserving.ae_eq_comp hA.coeFn_toLp
  exact (coeFn_l2Shift h k _).trans hcomp
end Shifts
section Averages
variable {a : ℝ}
theorem cubeCorrelationMean_eq_inner (ha : 0 < a) (ρ : ProbMeasure (GaugeField a))
    (hinv : IsShiftInvariant ρ.toMeasure) {A : GaugeField a → ℂ}
    (hA : MemLp A 2 ρ.toMeasure) (n : ℕ+) :
    cubeCorrelationMean ρ A n = ⟪hA.toLp A, cubeAverage (l2Shift hinv) n (hA.toLp A)⟫_ℂ := by
  have hinj := latticePointOf_injective ha.ne'
  rw [cubeAverage, inner_smul_right, inner_sum, cubeCorrelationMean, centredCubePoints_eq_image ha n,
    Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset,
    finsum_mem_image hinj.injOn, finsum_mem_coe_finset]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_eq_integral_conj_mul hA.coeFn_toLp (l2Shift_toLp_ae hinv k hA)]
  rfl
theorem exists_condExpRepresentative_of_starProjection (D : Setup)
    (hfixed : ShiftFixedFunctions.Assertion)
    (hinvariant : InvariantFunctionsAndErgodicity)
    (ρ : ProbMeasure (GaugeField D.mesh)) (hinv : IsShiftInvariant ρ.toMeasure)
    {A : GaugeField D.mesh → ℂ} (hA : IsBoundedObservable A) :
    ∃ Y, IsIntegrableCondExpRepresentative ρ.toMeasure A Y ∧
      (invariantSubspace (l2Shift hinv)).starProjection
        ((memLp_two_of_isBoundedObservable hA).toLp A) =ᵐ[ρ.toMeasure] Y := by
  set K := invariantSubspace (l2Shift hinv) with hK
  have hAL := memLp_two_of_isBoundedObservable (ν := ρ.toMeasure) hA
  set P : Lp ℂ 2 ρ.toMeasure := K.starProjection (hAL.toLp A) with hP
  have hPfix : ∀ k, l2Shift hinv k P = P :=
    (mem_invariantSubspace _).mp (K.starProjection_apply_mem _)
  have hmeas : Measurable (P : GaugeField D.mesh → ℂ) := (Lp.stronglyMeasurable P).measurable
  have hae : ∀ v : LatticePoint D.mesh, ρ.HoldsAS fun U =>
      (shift v).actOn (P : GaugeField D.mesh → ℂ) U = P U := by
    intro v
    obtain ⟨k, rfl⟩ := exists_latticePointOf v
    rw [ProbMeasure.holdsAS_iff]
    have hk := coeFn_l2Shift hinv k P
    rw [hPfix k] at hk
    filter_upwards [hk] with U hU
    exact hU.symm
  obtain ⟨-, -, hYm, hYae⟩ := (hfixed D).2 ρ P hmeas hae
  rw [ProbMeasure.holdsAS_iff] at hYae
  set Y := (shiftFixedSet (P : GaugeField D.mesh → ℂ)).indicator
    (P : GaugeField D.mesh → ℂ) with hY
  have hYP : (P : GaugeField D.mesh → ℂ) =ᵐ[ρ.toMeasure] Y :=
    hYae.mono fun U hU => hU.symm
  refine ⟨Y, ⟨hYm, ?_, ?_⟩, hYP⟩
  · exact (((Lp.memLp P).integrable one_le_two).congr hYP).hasFiniteIntegral
  · rintro J hJ ⟨C, hC⟩
    have hJm : Measurable J := hJ.mono (fun I hI => hI.1) le_rfl
    have hJobs : IsBoundedObservable J := ⟨hJm, C, hC⟩
    have hJc := isBoundedObservable_conj hJobs
    have hJL := memLp_two_of_isBoundedObservable (ν := ρ.toMeasure) hJc
    have hJfix : hJL.toLp (fun U => conj (J U)) ∈ K := by
      intro k
      refine Lp.ext ((l2Shift_toLp_ae hinv k hJL).trans ?_)
      refine EventuallyEq.trans (ae_of_all _ fun U => ?_) hJL.coeFn_toLp.symm
      have hJk := congrFun ((hinvariant D).1 J hJ (latticePointOf D.mesh k)) U
      exact congrArg conj hJk
    have hinner : ⟪hJL.toLp (fun U => conj (J U)), P⟫_ℂ =
        ⟪hJL.toLp (fun U => conj (J U)), hAL.toLp A⟫_ℂ := by
      rw [hP, ← Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr hJfix]
    rw [inner_eq_integral_conj_mul hJL.coeFn_toLp hYP,
      inner_eq_integral_conj_mul hJL.coeFn_toLp hAL.coeFn_toLp] at hinner
    simpa using hinner
end Averages
end CubeErgodic
open CubeErgodic in
theorem correlationMeansConverge_holds
    (hfixed : ShiftFixedFunctions.Assertion)
    (hexpectation : CondExpInvariant.Claim)
    (hinvariant : InvariantFunctionsAndErgodicity) :
    CorrelationMeansConverge := by
  intro D ρ A hinv hA
  have hplateau : ∀ Y, IsIntegrableCondExpRepresentative ρ.toMeasure A Y →
      plateauPairing ρ.toMeasure A A = ∫ U, conj (A U) * Y U ∂ρ.toMeasure := fun Y hY =>
    ((hexpectation D ρ.toMeasure hinv A A hA hA).2.2.2.2.2.2.2 Y hY).2
  refine ⟨?_, fun Y hY => (hplateau Y hY).symm⟩
  obtain ⟨Y, hY, hPY⟩ := exists_condExpRepresentative_of_starProjection D hfixed hinvariant ρ hinv hA
  have hAL := memLp_two_of_isBoundedObservable (ν := ρ.toMeasure) hA
  have hlim := (tendsto_cubeAverage (l2Shift hinv) (l2Shift_zero hinv) (l2Shift_add hinv)
    (hAL.toLp A)).comp tendsto_PNat_val_atTop_atTop
  have hin := (tendsto_const_nhds (x := hAL.toLp A)).inner hlim (𝕜 := ℂ)
  rw [inner_eq_integral_conj_mul hAL.coeFn_toLp hPY, ← hplateau Y hY] at hin
  refine hin.congr fun n => ?_
  exact (cubeCorrelationMean_eq_inner D.mesh_pos ρ hinv hAL n).symm
end YangMills.Construction.LatticePhases
end

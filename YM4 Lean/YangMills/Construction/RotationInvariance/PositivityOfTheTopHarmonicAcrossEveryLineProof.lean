import YangMills.Construction.PositiveDefinite.KernelSesquilinearForm
import YangMills.Construction.RotationInvariance.GramKernelStaysPositiveAtImaginaryAngles
import YangMills.Construction.RotationInvariance.InvariantTwoPointFunctionHasTopFrequencyZeroProof
import YangMills.Construction.RotationInvariance.LineSidesAndReflectionByRotations
import YangMills.Construction.RotationInvariance.PositivityOfTheTopHarmonicAcrossEveryLine
import YangMills.Construction.RotationInvariance.RulesOfTheRotationsTheForwardTubeAndTheSector
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane ForwardTube Filter Topology
open scoped ComplexOrder ComplexConjugate
namespace EuclideanFunctionals.TopCoeffLinePositivity
variable {m : SharpScale} {S : ConnFamily}
theorem planeKernel_imagBoost_eq_sum
    (hP : DistinctHarmonics.Holds) (hH : TubeUnionHarmonics.Holds)
    (hO : UnionKernel.Holds)
    (hR : ForwardTube.RotationRules.Holds)
    (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q)
    (φ : Fin (q + 1) → realLabels) (y : Fin (q + 1) → RealPlane)
    (hy : StrictMono fun i => y i 0) (s : ℝ) :
    planeKernel S φ (fun k : Fin q => imagBoost s (embedPlaneTuple (successiveDifferences y) k)) =
      ∑ h ∈ Finset.Icc (-(maxFrequency S d.angle (q + 1) : ℤ))
          (maxFrequency S d.angle (q + 1) : ℤ),
        distinctHarmonic S d.angle φ h y * Complex.exp (-(4 * (h : ℂ) * (s : ℂ))) := by
  obtain ⟨hLC, hRP, -, -, hFT, -⟩ := hR
  obtain ⟨-, -, -, hrot0, -⟩ := hLC
  obtain ⟨-, hreal, -, hturn0⟩ := hFT
  have hdiff : ∀ i : Fin q, embedPlane (y i.succ - y i.castSucc) ∈ forwardTube := by
    intro i
    have hmem : y i.succ - y i.castSucc ∈ openRightHalf := by
      show 0 < (y i.succ - y i.castSucc) 0
      have h1 : y i.castSucc 0 < y i.succ 0 := hy (Fin.castSucc_lt_succ)
      simpa using sub_pos.mpr h1
    have h2 : embedPlane (y i.succ - y i.castSucc) ∈ forwardTube ∩ realVectors := by
      rw [hreal]
      exact ⟨_, hmem, rfl⟩
    exact h2.1
  have hz : embedPlaneTuple y ∈ orderedTube rightAngleZero (1 : Equiv.Perm (Fin (q + 1))) := by
    show ∀ i : Fin q, _ ∈ rotatedForwardTube rightAngleZero
    intro i
    rw [hturn0]
    have h3 : embedPlaneTuple y ((1 : Equiv.Perm (Fin (q + 1))) i.succ) -
        embedPlaneTuple y ((1 : Equiv.Perm (Fin (q + 1))) i.castSucc) =
        embedPlane (y i.succ - y i.castSucc) := by
      simp [embedPlaneTuple, embedPlane]
    rw [h3]
    exact hdiff i
  have hU : embedPlaneTuple y ∈ orderedTubeUnion q :=
    Set.mem_iUnion₂.mpr ⟨rightAngleZero, 1, hz⟩
  have hOk := hO m S d q hq φ rightAngleZero rightAngleZero 1 1
  obtain ⟨-, hcone, -, -, -, hone, -, -⟩ := hOk
  have hsz : imagBoostTuple s (embedPlaneTuple y) ∈
      orderedTube rightAngleZero (1 : Equiv.Perm (Fin (q + 1))) :=
    ((hcone.2.2.2 _ hz).2.1) s
  have hK := hone.1 rightAngleZero 1 _ hsz
  rw [orderedFrameKernel_eq] at hK
  have hexp := (hH m S d q hq φ).1.1 _ hU s
  have hlist : unrotate rightAngleZero
      (complexDifferences (permuteTuple (1 : Equiv.Perm (Fin (q + 1)))
        (imagBoostTuple s (embedPlaneTuple y)))) =
      fun k : Fin q => imagBoost s (embedPlaneTuple (successiveDifferences y) k) := by
    have h4 := (hRP q hq (Complex.I * (s : ℂ)) (embedPlaneTuple y) 0 1 1 φ).2.1
    have h5 : permuteTuple (1 : Equiv.Perm (Fin (q + 1)))
        (imagBoostTuple s (embedPlaneTuple y)) =
        complexBoostTuple (Complex.I * (s : ℂ)) (embedPlaneTuple y) := rfl
    rw [h5, h4, complexDifferences_embedPlaneTuple]
    funext k
    have h6 : ((-((rightAngleZero : rightAngleMultiples) : ℝ) : ℝ) : ℂ) = 0 := by
      simp [rightAngleZero]
    show complexBoost ((-((rightAngleZero : rightAngleMultiples) : ℝ) : ℝ) : ℂ) _ = _
    rw [h6, hrot0]
    rfl
  have hφ1 : permuteTuple (1 : Equiv.Perm (Fin (q + 1))) φ = φ := rfl
  rw [hφ1, hlist] at hK
  rw [← hK]
  show _ = _
  have hexp' : unionKernel S φ (imagBoostTuple s (embedPlaneTuple y)) = _ := hexp
  rw [hexp']
  refine Finset.sum_congr rfl fun h hh => ?_
  have habs : |h| ≤ (maxFrequency S d.angle (q + 1) : ℤ) :=
    abs_le.mpr (Finset.mem_Icc.mp hh)
  have h7 := (((hP m S d q hq h φ).1).1).2 y hU
  rw [h7]
  show _ = (if |h| ≤ (maxFrequency S d.angle (q + 1) : ℤ) then _ else _) * _
  rw [if_pos habs]
def harmonicSum (S : ConnFamily) (φ₀ : openingAngles) (s : ℝ) (N : ℕ) (φ : Fin N → realLabels)
    (y : Fin N → RealPlane) : ℂ :=
  ∑ h ∈ Finset.Icc (-(maxFrequency S φ₀ N : ℤ)) (maxFrequency S φ₀ N : ℤ),
    pointHarmonic S φ₀ h N φ y * Complex.exp (-(4 * (h : ℂ) * (s : ℂ)))
theorem harmonicGramKernel_eq_harmonicSum (φ₀ : openingAngles) (s : ℝ) {n n' : ℕ}
    (x : LabelledPoints n) (y : LabelledPoints n') :
    harmonicGramKernel S φ₀ s x y =
      harmonicSum S φ₀ s (n + n') (Fin.append x.labelVec y.labelVec)
        (mapAppend RealPlane.reflectFirst x.points y.points) :=
  rfl
theorem planeKernel_imagBoost_eq_harmonicSum
    (hP : DistinctHarmonics.Holds) (hH : TubeUnionHarmonics.Holds)
    (hO : UnionKernel.Holds)
    (hR : ForwardTube.RotationRules.Holds)
    (d : PlaneDataWithAperture m S) {N : ℕ} (hN : 2 ≤ N)
    (φ : Fin N → realLabels) (y : Fin N → RealPlane)
    (hy : StrictMono fun i => y i 0) (s : ℝ) :
    planeKernel S (q := N - 1) (fun k => φ (Fin.cast (by omega) k))
        (fun k => imagBoost s (embedPlane (successiveDifferences y k))) =
      harmonicSum S d.angle s N φ y := by
  obtain ⟨q, rfl⟩ : ∃ q, N = q + 2 := ⟨N - 2, by omega⟩
  exact planeKernel_imagBoost_eq_sum hP hH hO hR d (q := q + 1) (by omega) φ y hy s
theorem harmonicSum_zero (φ₀ : openingAngles) (s : ℝ) (φ : Fin 0 → realLabels)
    (y : Fin 0 → RealPlane) : harmonicSum S φ₀ s 0 φ y = 1 := by
  simp [harmonicSum, maxFrequency, pointHarmonic, vacuumHarmonic]
theorem harmonicSum_one (φ₀ : openingAngles) (s : ℝ) (φ : Fin 1 → realLabels)
    (y : Fin 1 → RealPlane) : harmonicSum S φ₀ s 1 φ y = 0 := by
  simp [harmonicSum, pointHarmonic]
theorem pointHarmonic_permuteTuple (hP : DistinctHarmonics.Holds)
    (d : PlaneDataWithAperture m S) {N : ℕ} (hN : 2 ≤ N) (h : ℤ)
    (ς : Equiv.Perm (Fin N)) (φ : Fin N → realLabels) {y : Fin N → RealPlane}
    (hy : y ∈ injectivePointTuples N) :
    pointHarmonic S d.angle h N (permuteTuple ς φ) (permuteTuple ς y) =
      pointHarmonic S d.angle h N φ y := by
  obtain ⟨q, rfl⟩ : ∃ q, N = q + 2 := ⟨N - 2, by omega⟩
  exact (hP m S d (q + 1) (by omega) h φ).2.2.1 ς y hy
def sumPerm {n n' : ℕ} (α : Equiv.Perm (Fin n)) (β : Equiv.Perm (Fin n')) :
    Equiv.Perm (Fin (n + n')) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr α β).trans finSumFinEquiv)
theorem permuteTuple_sumPerm_append {γ : Type*} {n n' : ℕ} (α : Equiv.Perm (Fin n))
    (β : Equiv.Perm (Fin n')) (u : Fin n → γ) (v : Fin n' → γ) :
    permuteTuple (sumPerm α β) (Fin.append u v) =
      Fin.append (permuteTuple α u) (permuteTuple β v) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [permuteTuple, sumPerm]
  · simp [permuteTuple, sumPerm]
theorem exists_perm_strictMono_time (hA : ForwardTube.GramKernelArgsFacts) {n : ℕ}
    (x : Fin n → RealPlane) (hpos : ∀ i, x i ∈ openRightHalf)
    (hinj : Function.Injective fun i => x i 0) :
    ∃ σ : Equiv.Perm (Fin n), (StrictMono fun i => x (σ i) 0) ∧
      realTuple (fun i => x (σ i)) ∈ successiveDomain n := by
  have hs : StrictMono fun i => x (Tuple.sort (fun i => x i 0) i) 0 := by
    have hm := Tuple.monotone_sort (fun i => x i 0)
    exact hm.strictMono_of_injective (hinj.comp (Equiv.injective _))
  refine ⟨Tuple.sort (fun i => x i 0), hs, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun h => absurd h (lt_irrefl 0), fun i h => absurd h (by omega)⟩
  · have h1 := (hA.1 n hn).2
    have h2 : realTuple (fun i => x (Tuple.sort (fun i => x i 0) i)) ∈
        successiveDomain n ∩ Set.range (realTuple (n := n)) := by
      rw [h1]
      exact ⟨_, ⟨fun i => hpos _, hs⟩, rfl⟩
    exact h2.1
theorem harmonicGramKernel_eq_gramKernelImag
    (hP : DistinctHarmonics.Holds) (hH : TubeUnionHarmonics.Holds)
    (hO : UnionKernel.Holds)
    (hR : ForwardTube.RotationRules.Holds)
    (hG : GramKernelImagPosSemidef.Holds)
    (hA : ForwardTube.GramKernelArgsFacts)
    (d : PlaneDataWithAperture m S) (s : ℝ) {n n' : ℕ}
    (x : LabelledPoints n) (y : LabelledPoints n')
    (hx : x.IsInjectiveIn openRightHalf) (hy : y.IsInjectiveIn openRightHalf)
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin n'))
    (hσ : realTuple (fun i => x.points (σ i)) ∈ successiveDomain n)
    (hτ : realTuple (fun i => y.points (τ i)) ∈ successiveDomain n') :
    harmonicGramKernel S d.angle s x y =
      gramKernelImag S s
        (ForwardTube.LabelledTuple.mk ⟨_, hσ⟩ fun i => x.labelVec (σ i))
        (ForwardTube.LabelledTuple.mk ⟨_, hτ⟩ fun i => y.labelVec (τ i)) := by
  rw [harmonicGramKernel_eq_harmonicSum]
  have hGs := ((hG m S d).2 s).2
  by_cases hN : 2 ≤ n + n'
  · have h1 := hGs.1 (ForwardTube.LabelledTuple.mk ⟨_, hσ⟩ fun i => x.labelVec (σ i))
      (ForwardTube.LabelledTuple.mk ⟨_, hτ⟩ fun i => y.labelVec (τ i)) hN
    rw [h1]
    obtain ⟨hlist, -, -, hmono, -, -⟩ := hA.2.2.1 n n' hN _ _ hσ hτ
    have h2 := planeKernel_imagBoost_eq_harmonicSum hP hH hO hR d hN
      (gramLabelOrder (fun i => x.labelVec (σ i)) (fun i => y.labelVec (τ i)))
      (reflectAppend (fun i => x.points (σ i)) (fun i => y.points (τ i))) hmono s
    have h3 : (fun k => imagBoost s (gramKernelArgs
        (realTuple fun i => x.points (σ i)) (realTuple fun i => y.points (τ i)) k)) =
        fun k => imagBoost s (embedPlane (successiveDifferences
          (reflectAppend (fun i => x.points (σ i)) (fun i => y.points (τ i))) k)) := by
      funext k
      rw [hlist k]
    refine Eq.trans ?_ (Eq.symm (h3 ▸ h2))
    have hdist := (mapAppend_reflectFirst_injective hx hy).1
    set ς : Equiv.Perm (Fin (n + n')) := sumPerm (Fin.revPerm.trans σ) τ with hς
    have h4 : gramLabelOrder (fun i => x.labelVec (σ i)) (fun i => y.labelVec (τ i)) =
        permuteTuple ς (Fin.append x.labelVec y.labelVec) := by
      rw [hς, permuteTuple_sumPerm_append]
      rfl
    have h5 : reflectAppend (fun i => x.points (σ i)) (fun i => y.points (τ i)) =
        permuteTuple ς (mapAppend RealPlane.reflectFirst x.points
          y.points) := by
      rw [hς, mapAppend, permuteTuple_sumPerm_append]
      rfl
    rw [h4, h5]
    unfold harmonicSum
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [pointHarmonic_permuteTuple hP d hN h ς _ hdist]
  · have hn2 : n + n' = 0 ∨ n + n' = 1 := by omega
    rcases hn2 with h0 | h1
    · obtain ⟨rfl, rfl⟩ : n = 0 ∧ n' = 0 := by omega
      rw [hGs.2.1 _ _ rfl rfl]
      exact harmonicSum_zero _ _ _ _
    · rw [hGs.2.2 (ForwardTube.LabelledTuple.mk ⟨_, hσ⟩ fun i => x.labelVec (σ i))
        (ForwardTube.LabelledTuple.mk ⟨_, hτ⟩ fun i => y.labelVec (τ i)) h1]
      generalize Fin.append x.labelVec y.labelVec = a
      generalize mapAppend RealPlane.reflectFirst x.points y.points = b
      revert a b
      rw [h1]
      exact fun a b => harmonicSum_one _ _ _ _
theorem harmonicGramKernel_form_nonneg_of_injective_time
    (hP : DistinctHarmonics.Holds) (hH : TubeUnionHarmonics.Holds)
    (hO : UnionKernel.Holds)
    (hR : ForwardTube.RotationRules.Holds)
    (hG : GramKernelImagPosSemidef.Holds)
    (hA : ForwardTube.GramKernelArgsFacts)
    (d : PlaneDataWithAperture m S) (s : ℝ) {p : ℕ}
    (u : Fin p → AllInjectiveConfigs openRightHalf) (c : Fin p → ℂ)
    (hu : ∀ a, Function.Injective fun i => (u a).2.1.points i 0) :
    0 ≤ ∑ a, ∑ b, conj (c a) * c b *
      harmonicGramKernel S d.angle s (u a).2.1 (u b).2.1 := by
  have hex := fun a => exists_perm_strictMono_time hA (u a).2.1.points ((u a).2.2.2) (hu a)
  choose σ _ hσ using hex
  have hpsd := ((hG m S d).2 s).1 p
    (fun a => ForwardTube.LabelledTuple.mk ⟨_, hσ a⟩ fun i => (u a).2.1.labelVec (σ a i)) c
  refine hpsd.trans_eq ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [harmonicGramKernel_eq_gramKernelImag hP hH hO hR hG hA d s
    (u a).2.1 (u b).2.1 (u a).2.2 (u b).2.2 (σ a) (σ b) (hσ a) (hσ b)]
theorem eventually_add_mul_ne_zero (A B : ℝ) (hB : B ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), A + B * ε ≠ 0 := by
  by_cases hA : A = 0
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have h1 : ε ≠ 0 := ne_of_gt hε
    simp [hA, hB, h1]
  · have hc : Continuous fun ε : ℝ => A + B * ε := by fun_prop
    have h0 : (fun ε : ℝ => A + B * ε) 0 ≠ 0 := by simpa using hA
    exact (hc.continuousAt.eventually_ne h0).filter_mono nhdsWithin_le_nhds
def timeStagger {n : ℕ} (ε : ℝ) (c : LabelledPoints n) :
    LabelledPoints n where
  points := fun i => c.points i + ((((i : ℕ) : ℝ) + 1) * ε) • unitX
  labels := c.labels
  labels_mem := c.labels_mem
theorem timeStagger_time {n : ℕ} (ε : ℝ) (c : LabelledPoints n) (i : Fin n) :
    (timeStagger ε c).points i 0 = c.points i 0 + (((i : ℕ) : ℝ) + 1) * ε := by
  simp [timeStagger, unitX]
theorem eventually_timeStagger_injective {n : ℕ} (c : LabelledPoints n)
    (hc : c.IsInjectiveIn openRightHalf) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (timeStagger ε c).IsInjectiveIn openRightHalf ∧
      Function.Injective fun i => (timeStagger ε c).points i 0 := by
  have hpair : ∀ i j : Fin n, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (timeStagger ε c).points i 0 = (timeStagger ε c).points j 0 →
        i = j := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ _ => hij
    · have hB : (((i : ℕ) : ℝ) + 1) - (((j : ℕ) : ℝ) + 1) ≠ 0 := by
        intro h
        apply hij
        ext
        have h1 : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by linarith
        exact_mod_cast h1
      filter_upwards [eventually_add_mul_ne_zero (c.points i 0 - c.points j 0) _ hB]
        with ε hε h
      exfalso
      apply hε
      rw [timeStagger_time, timeStagger_time] at h
      linear_combination h
  have hall := eventually_all.mpr fun i => eventually_all.mpr (hpair i)
  filter_upwards [hall, self_mem_nhdsWithin] with ε h1 h2
  have hinj : Function.Injective fun i => (timeStagger ε c).points i 0 :=
    fun i j hij => h1 i j hij
  refine ⟨⟨?_, fun i => ?_⟩, hinj⟩
  · show Function.Injective _
    intro i j hij
    exact hinj (congrArg (fun v : RealPlane => v 0) hij)
  · show 0 < (timeStagger ε c).points i 0
    rw [timeStagger_time]
    have h3 : 0 < c.points i 0 := hc.2 i
    have h4 : (0 : ℝ) < ε := h2
    positivity
theorem pointHarmonic_tendsto (hP : DistinctHarmonics.Holds)
    (d : PlaneDataWithAperture m S) {N : ℕ} (h : ℤ) (φ : Fin N → realLabels)
    {F : Filter ℝ} {g : ℝ → Fin N → RealPlane} {y₀ : Fin N → RealPlane}
    (hy₀ : y₀ ∈ injectivePointTuples N) (hg : Tendsto g F (𝓝 y₀))
    (hgd : ∀ᶠ ε in F, g ε ∈ injectivePointTuples N) :
    Tendsto (fun ε => pointHarmonic S d.angle h N φ (g ε)) F
      (𝓝 (pointHarmonic S d.angle h N φ y₀)) := by
  match N, φ, g, y₀, hy₀, hg, hgd with
  | 0, _, _, _, _, _, _ => exact tendsto_const_nhds
  | 1, _, _, _, _, _, _ => exact tendsto_const_nhds
  | q + 2, φ, g, y₀, hy₀, hg, hgd =>
    have hc := (((hP m S d (q + 1) (by omega) h φ).1).1).1
    exact (hc y₀ hy₀).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hg, hgd⟩)
theorem harmonicGramKernel_timeStagger_tendsto (hP : DistinctHarmonics.Holds)
    (hR : ForwardTube.RotationRules.Holds)
    (d : PlaneDataWithAperture m S) (s : ℝ) {n n' : ℕ}
    (x : LabelledPoints n) (y : LabelledPoints n')
    (hx : x.IsInjectiveIn openRightHalf) (hy : y.IsInjectiveIn openRightHalf) :
    Tendsto (fun ε => harmonicGramKernel S d.angle s (timeStagger ε x)
        (timeStagger ε y)) (𝓝[>] 0)
      (𝓝 (harmonicGramKernel S d.angle s x y)) := by
  have hlin : IsLinearMap ℝ RealPlane.reflectFirst := hR.2.2.1.2.1
  have hrefl : Continuous RealPlane.reflectFirst :=
    (IsLinearMap.mk' _ hlin).continuous_of_finiteDimensional
  have hpos : ∀ {k : ℕ} (c : LabelledPoints k) (i : Fin k),
      Continuous fun ε => (timeStagger ε c).points i := by
    intro k c i
    show Continuous fun ε : ℝ => c.points i + ((((i : ℕ) : ℝ) + 1) * ε) • unitX
    fun_prop
  have hcont : Continuous fun ε => mapAppend RealPlane.reflectFirst
      (timeStagger ε x).points (timeStagger ε y).points := by
    refine continuous_pi fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [mapAppend, Fin.append_left, mapPoints]
      exact hrefl.comp (hpos x j)
    · simp only [mapAppend, Fin.append_right]
      exact hpos y j
  have hzero : ∀ {k : ℕ} (c : LabelledPoints k),
      (timeStagger 0 c).points = c.points := by
    intro k c
    funext i
    simp [timeStagger]
  have hg : Tendsto (fun ε => mapAppend RealPlane.reflectFirst
      (timeStagger ε x).points (timeStagger ε y).points) (𝓝[>] 0)
      (𝓝 (mapAppend RealPlane.reflectFirst x.points y.points)) := by
    have h1 := hcont.tendsto 0
    simp only [hzero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hgd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), mapAppend RealPlane.reflectFirst
      (timeStagger ε x).points (timeStagger ε y).points ∈
        injectivePointTuples (n + n') := by
    filter_upwards [eventually_timeStagger_injective x hx, eventually_timeStagger_injective y hy]
      with ε h1 h2
    exact (mapAppend_reflectFirst_injective h1.1 h2.1).1
  refine tendsto_finsetSum _ fun h _ => Tendsto.mul_const _ ?_
  exact pointHarmonic_tendsto hP d h _ (mapAppend_reflectFirst_injective hx hy).1 hg hgd
theorem harmonicGramKernel_form_nonneg
    (hP : DistinctHarmonics.Holds) (hH : TubeUnionHarmonics.Holds)
    (hO : UnionKernel.Holds)
    (hR : ForwardTube.RotationRules.Holds)
    (hG : GramKernelImagPosSemidef.Holds)
    (hA : ForwardTube.GramKernelArgsFacts)
    (d : PlaneDataWithAperture m S) (s : ℝ) {p : ℕ}
    (u : Fin p → AllInjectiveConfigs openRightHalf) (c : Fin p → ℂ) :
    0 ≤ ∑ a, ∑ b, conj (c a) * c b *
      harmonicGramKernel S d.angle s (u a).2.1 (u b).2.1 := by
  have hlim : Tendsto (fun ε => ∑ a, ∑ b, conj (c a) * c b *
      harmonicGramKernel S d.angle s (timeStagger ε (u a).2.1)
        (timeStagger ε (u b).2.1)) (𝓝[>] 0)
      (𝓝 (∑ a, ∑ b, conj (c a) * c b *
        harmonicGramKernel S d.angle s (u a).2.1 (u b).2.1)) :=
    tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
      (harmonicGramKernel_timeStagger_tendsto hP hR d s _ _ (u a).2.2 (u b).2.2).const_mul _
  have hev := eventually_all.mpr fun a => eventually_timeStagger_injective (u a).2.1 (u a).2.2
  refine ge_of_tendsto hlim ?_
  filter_upwards [hev] with ε hε
  exact harmonicGramKernel_form_nonneg_of_injective_time hP hH hO hR hG hA d s
    (fun a => ⟨(u a).1, ⟨timeStagger ε (u a).2.1, (hε a).1⟩⟩) c fun a => (hε a).2
theorem tendsto_exp_mul_sum_lowest (T : ℕ) (c : ℤ → ℂ) :
    Tendsto (fun s : ℝ => ((Real.exp (-(4 * (T : ℝ) * s)) : ℝ) : ℂ) *
        ∑ h ∈ Finset.Icc (-(T : ℤ)) (T : ℤ), c h * Complex.exp (-(4 * (h : ℂ) * (s : ℂ))))
      atTop (𝓝 (c (-(T : ℤ)))) := by
  have hterm : ∀ h ∈ Finset.Icc (-(T : ℤ)) (T : ℤ),
      Tendsto (fun s : ℝ => c h * ((Real.exp (-(4 * (((h + T : ℤ)) : ℝ) * s)) : ℝ) : ℂ)) atTop
        (𝓝 (if h = -(T : ℤ) then c h else 0)) := by
    intro h hh
    by_cases he : h = -(T : ℤ)
    · subst he
      simp
    · have hlow := (Finset.mem_Icc.mp hh).1
      have hpos : 0 < ((h + T : ℤ) : ℝ) := by
        have h0 : 0 < h + T := by omega
        exact_mod_cast h0
      have h1 : Tendsto (fun s : ℝ => -(4 * ((h + T : ℤ) : ℝ) * s)) atTop atBot := by
        have h2 : Tendsto (fun s : ℝ => (4 * ((h + T : ℤ) : ℝ)) * s) atTop atTop :=
          tendsto_id.const_mul_atTop (by positivity)
        exact tendsto_neg_atTop_atBot.comp h2
      have h3 := Real.tendsto_exp_atBot.comp h1
      have h4 := (Complex.continuous_ofReal.tendsto 0).comp h3
      rw [if_neg he]
      simpa [Function.comp_def] using h4.const_mul (c h)
  have hs := tendsto_finsetSum _ hterm
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)] at hs
  refine hs.congr fun s => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [mul_left_comm]
  congr 1
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem pointHarmonic_tupleTwoMul (φ₀ : openingAngles) (h : ℤ) (k : ℕ)
    (φ : Fin (k + k) → realLabels) (y : Fin (k + k) → RealPlane) :
    pointHarmonic S φ₀ h (2 * k) (tupleTwoMul φ) (tupleTwoMul y) =
      pointHarmonic S φ₀ h (k + k) φ y := by
  have key : ∀ {N M : ℕ} (e : N = M) (φ : Fin M → realLabels) (y : Fin M → RealPlane),
      pointHarmonic S φ₀ h N (fun i => φ (Fin.cast e i)) (fun i => y (Fin.cast e i)) =
        pointHarmonic S φ₀ h M φ y := by
    intro N M e
    subst e
    intro φ y
    rfl
  exact key (two_mul k) φ y
theorem topCoeffMapAppend_eq (φ₀ : openingAngles) {k : ℕ}
    (a : RealPlane → RealPlane) (x y : LabelledPoints k) :
    topCoeffMapAppend S φ₀ a x y =
      pointHarmonic S φ₀ (-(maxFrequency S φ₀ (k + k) : ℤ)) (k + k)
        (Fin.append x.labelVec y.labelVec)
        (mapAppend a x.points y.points) := by
  rw [topCoeffMapAppend, topCoeff, pointHarmonic_tupleTwoMul,
    topIndex, two_mul]
theorem topCoeffMapAppend_form_nonneg
    (hP : DistinctHarmonics.Holds) (hH : TubeUnionHarmonics.Holds)
    (hO : UnionKernel.Holds)
    (hR : ForwardTube.RotationRules.Holds)
    (hG : GramKernelImagPosSemidef.Holds)
    (hA : ForwardTube.GramKernelArgsFacts)
    (d : PlaneDataWithAperture m S) (k : ℕ) {p : ℕ}
    (u : Fin p → InjectiveConfigs openRightHalf k) (c : Fin p → ℂ) :
    0 ≤ ∑ a, ∑ b, conj (c a) * c b *
      topCoeffMapAppend S d.angle RealPlane.reflectFirst (u a).1 (u b).1 := by
  have hlim : Tendsto (fun s : ℝ => ∑ a, ∑ b, conj (c a) * c b *
      (((Real.exp (-(4 * ((maxFrequency S d.angle (k + k) : ℕ) : ℝ) * s)) : ℝ) : ℂ) *
        harmonicGramKernel S d.angle s (u a).1 (u b).1)) atTop
      (𝓝 (∑ a, ∑ b, conj (c a) * c b *
        topCoeffMapAppend S d.angle RealPlane.reflectFirst
          (u a).1 (u b).1)) := by
    refine tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => Tendsto.const_mul _ ?_
    rw [topCoeffMapAppend_eq]
    exact tendsto_exp_mul_sum_lowest (maxFrequency S d.angle (k + k)) fun h =>
      pointHarmonic S d.angle h (k + k) _ _
  refine ge_of_tendsto hlim (Eventually.of_forall fun s => ?_)
  have h0 := harmonicGramKernel_form_nonneg hP hH hO hR hG hA d s (fun a => ⟨k, u a⟩) c
  have h1 : ∑ a, ∑ b, conj (c a) * c b *
      (((Real.exp (-(4 * ((maxFrequency S d.angle (k + k) : ℕ) : ℝ) * s)) : ℝ) : ℂ) *
        harmonicGramKernel S d.angle s (u a).1 (u b).1) =
      ((Real.exp (-(4 * ((maxFrequency S d.angle (k + k) : ℕ) : ℝ) * s)) : ℝ) : ℂ) *
        ∑ a, ∑ b, conj (c a) * c b *
          harmonicGramKernel S d.angle s (u a).1 (u b).1 := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h1]
  exact mul_nonneg (Complex.zero_le_real.mpr (Real.exp_pos _).le) h0
theorem rotate_rotate_neg (t : ℝ) (v : RealPlane) :
    RealPlane.rotate t (RealPlane.rotate (-t) v) = v := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.rotate_rotate_neg <;> assumption
theorem rotate_neg_rotate (t : ℝ) (v : RealPlane) :
    RealPlane.rotate (-t) (RealPlane.rotate t v) = v := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.rotate_neg_rotate <;> assumption
theorem pointHarmonic_translate_rotate (hP : DistinctHarmonics.Holds)
    (d : PlaneDataWithAperture m S) {N : ℕ} (hN : 2 ≤ N) (h : ℤ)
    (φ : Fin N → realLabels) {w : Fin N → RealPlane} (hw : w ∈ injectivePointTuples N)
    (t : ℝ) (u : RealPlane) :
    pointHarmonic S d.angle h N φ (translateTuple (mapPoints (RealPlane.rotate t) w) u) =
      Complex.exp (4 * Complex.I * (h : ℂ) * (t : ℂ)) * pointHarmonic S d.angle h N φ w := by
  obtain ⟨q, rfl⟩ : ∃ q, N = q + 2 := ⟨N - 2, by omega⟩
  have hq := hP m S d (q + 1) (by omega) h φ
  have hrot : mapPoints (RealPlane.rotate t) w ∈ injectivePointTuples (q + 2) := by
    show Function.Injective _
    intro i j hij
    have h1 : RealPlane.rotate t (w i) = RealPlane.rotate t (w j) := hij
    have h2 := congrArg (RealPlane.rotate (-t)) h1
    rw [rotate_neg_rotate, rotate_neg_rotate] at h2
    exact hw h2
  exact (hq.2.2.2.1 u _ hrot).trans (hq.2.2.2.2.1 w hw t)
def rotateBack {k : ℕ} (ϑ : ℝ) (u : RealPlane) (c : LabelledPoints k) :
    LabelledPoints k where
  points := fun i => RealPlane.rotate (-ϑ) (c.points i - u)
  labels := c.labels
  labels_mem := c.labels_mem
theorem rotateBack_isInjectiveIn {k : ℕ} {ϑ : ℝ} {u : RealPlane}
    {P : Set RealPlane} (hmem : ∀ y ∈ P, RealPlane.rotate (-ϑ) (y - u) ∈ openRightHalf)
    {c : LabelledPoints k} (hc : c.IsInjectiveIn P) :
    (rotateBack ϑ u c).IsInjectiveIn openRightHalf := by
  refine ⟨?_, fun i => hmem _ (hc.2 i)⟩
  show Function.Injective _
  intro i j hij
  have h1 : RealPlane.rotate (-ϑ) (c.points i - u) = RealPlane.rotate (-ϑ) (c.points j - u) := hij
  have h2 := congrArg (RealPlane.rotate ϑ) h1
  rw [rotate_rotate_neg, rotate_rotate_neg] at h2
  exact hc.1 (sub_left_injective h2)
theorem topCoeffMapAppend_lineReflection_eq (hP : DistinctHarmonics.Holds)
    (d : PlaneDataWithAperture m S) {k : ℕ} (hk : 1 ≤ k) {l : Set RealPlane} {ϑ : ℝ}
    {u : RealPlane}
    (hrefl : ∀ y, lineReflection l y =
      u + RealPlane.rotate ϑ (RealPlane.reflectFirst (RealPlane.rotate (-ϑ) (y - u))))
    (x y : LabelledPoints k)
    (hx : (rotateBack ϑ u x).IsInjectiveIn openRightHalf)
    (hy : (rotateBack ϑ u y).IsInjectiveIn openRightHalf) :
    Complex.exp (4 * Complex.I * (topIndex S d.angle k : ℂ) * (ϑ : ℂ)) *
        topCoeffMapAppend S d.angle (lineReflection l) x y =
      topCoeffMapAppend S d.angle RealPlane.reflectFirst
        (rotateBack ϑ u x) (rotateBack ϑ u y) := by
  have hdist := (mapAppend_reflectFirst_injective hx hy).1
  have hw : tupleTwoMul (mapAppend RealPlane.reflectFirst
      (rotateBack ϑ u x).points (rotateBack ϑ u y).points) ∈
      injectivePointTuples (2 * k) := by
    show Function.Injective _
    intro i j hij
    have h1 := hdist hij
    exact Fin.cast_injective _ h1
  have hpos : tupleTwoMul (mapAppend (lineReflection l)
      x.points y.points) =
      translateTuple (mapPoints (RealPlane.rotate ϑ) (tupleTwoMul
        (mapAppend RealPlane.reflectFirst
          (rotateBack ϑ u x).points (rotateBack ϑ u y).points))) u := by
    funext i
    simp only [tupleTwoMul, translateTuple, mapPoints]
    generalize Fin.cast (two_mul k) i = j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · simp only [mapAppend, Fin.append_left, mapPoints]
      rw [hrefl, add_comm]
      rfl
    · simp only [mapAppend, Fin.append_right]
      show y.points a = RealPlane.rotate ϑ (RealPlane.rotate (-ϑ) (y.points a - u)) + u
      rw [rotate_rotate_neg, sub_add_cancel]
  have hlab : ∀ c : LabelledPoints k, (rotateBack ϑ u c).labelVec = c.labelVec :=
    fun _ => rfl
  rw [topCoeffMapAppend, topCoeffMapAppend, topCoeff, hpos, hlab, hlab]
  rw [pointHarmonic_translate_rotate hP d (by omega) _ _ hw, ← mul_assoc, ← Complex.exp_add]
  have hz : 4 * Complex.I * (topIndex S d.angle k : ℂ) * (ϑ : ℂ) +
      4 * Complex.I * ((-(topIndex S d.angle k : ℤ) : ℤ) : ℂ) * (ϑ : ℂ) = 0 := by
    push_cast
    ring
  rw [hz, Complex.exp_zero, one_mul]
theorem lineReflectionPosSemidef_holds
    (hP : DistinctHarmonics.Holds) (hH : TubeUnionHarmonics.Holds)
    (hO : UnionKernel.Holds)
    (hR : ForwardTube.RotationRules.Holds)
    (hG : GramKernelImagPosSemidef.Holds)
    (hA : ForwardTube.GramKernelArgsFacts)
    (hL : LineSidesViaRotations.Holds)
    (d : PlaneDataWithAperture m S) :
    LineReflectionPosSemidef S d.angle := by
  intro k hk l hl P _ ϑ hϑ p w c
  obtain ⟨hν, u, hu, hPeq⟩ := id hϑ
  have hLs := hL l P (negSide (RealPlane.rotate ϑ unitX) u) u hl
    ⟨u, hu, _, hν, hPeq, rfl⟩ hu
  have hb := hLs.2.1 ϑ hϑ
  have hmem : ∀ y ∈ P, RealPlane.rotate (-ϑ) (y - u) ∈ openRightHalf := fun y hy => ((hb y).1).mp hy
  have hrefl := fun y => (hb y).2.2
  have h0 := topCoeffMapAppend_form_nonneg hP hH hO hR hG hA d k
    (fun a => ⟨rotateBack ϑ u (w a).1,
      rotateBack_isInjectiveIn hmem (w a).2⟩) c
  refine h0.trans_eq ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact congrArg (fun z => conj (c a) * c b * z)
    (topCoeffMapAppend_lineReflection_eq hP d hk hrefl (w a).1 (w b).1
      (rotateBack_isInjectiveIn hmem (w a).2)
      (rotateBack_isInjectiveIn hmem (w b).2)).symm
theorem allPositivity_holds (hK : PositiveDefinite.KernelSesqForm.SesqFormProperties)
    (hA : ForwardTube.GramKernelArgsFacts)
    (hG : GramKernelImagPosSemidef.Holds)
    (hH : TubeUnionHarmonics.Holds)
    (hL : LineSidesViaRotations.Holds)
    (hO : UnionKernel.Holds)
    (hP : DistinctHarmonics.Holds)
    (hR : ForwardTube.RotationRules.Holds) : AllPositivity := by
  intro m S d
  have hline := lineReflectionPosSemidef_holds hP hH hO hR hG hA hL d
  refine ⟨fun s p u c => harmonicGramKernel_form_nonneg hP hH hO hR hG hA d s u c,
    fun k _ p u c => topCoeffMapAppend_form_nonneg hP hH hO hR hG hA d k u c, hline, ?_⟩
  intro k hk l hl P hside x hx y
  obtain ⟨u, hu, ν, hν, hPeq⟩ := id hside
  obtain ⟨⟨ϑ, hϑ⟩, -⟩ := (hL l P (negSide ν u) u hl
    ⟨u, hu, ν, hν, hPeq, rfl⟩ hu).1
  have hpsd := hline k hk l hl P hside ϑ hϑ
  have h1 := ((hK _ _ hpsd).2 x y).2.2
  simp only [hx, mul_zero, zero_mul] at h1
  have h2 : ‖Complex.exp (4 * Complex.I * (topIndex S d.angle k : ℂ) * (ϑ : ℂ)) *
      topCoeffMapAppend S d.angle (lineReflection l) x.1 y.1‖ ^ 2 ≤ 0 := by
    have h3 : ((‖Complex.exp (4 * Complex.I * (topIndex S d.angle k : ℂ) * (ϑ : ℂ)) *
        topCoeffMapAppend S d.angle (lineReflection l) x.1 y.1‖ ^ 2 : ℝ) : ℂ) ≤
        ((0 : ℝ) : ℂ) := by
      simpa using h1
    exact Complex.real_le_real.mp h3
  have h4 := pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h2 (by positivity))
  rcases mul_eq_zero.mp (norm_eq_zero.mp h4) with h5 | h5
  · exact absurd h5 (Complex.exp_ne_zero _)
  · exact h5
end EuclideanFunctionals.TopCoeffLinePositivity
end YangMills.Construction
end

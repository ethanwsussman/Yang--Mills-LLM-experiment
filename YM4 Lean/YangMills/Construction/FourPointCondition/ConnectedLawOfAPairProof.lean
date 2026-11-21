import YangMills.Construction.Lattice.LatticesOfATorusAndOfFourSpaceProof
import YangMills.Construction.FourPointCondition.ConnectedLawOfAPair
import YangMills.Construction.ResponseInTheExpansion.TraceOfTheSquareOfTheKernelOfTheCurvature
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace YangMills.Construction.FourPointCondition
namespace GaussianPairProof
open TorusMetric TestFunctions ResponseInTheExpansion LinearResponse
variable {S : ℝ}
private theorem abs_coord_le_norm (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem torusProj_sub (v w : Fin 4 → ℝ) : torusProj S (v - w) = torusProj S v - torusProj S w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
private theorem torusNorm_nonneg (x : Torus4 S) : 0 ≤ torusEuclidNorm x := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
private theorem exists_minimal_lift (x : Torus4 S) :
    ∃ b : Fin 4 → ℝ, torusProj S b = x ∧ euclidNormVec b = torusEuclidNorm x := by apply _root_.YangMills.Construction.AmbientPoints.exists_torusProj_eq_euclidNormVec_eq <;> assumption
private theorem torusNorm_add_le (x y : Torus4 S) :
    torusEuclidNorm (x + y) ≤ torusEuclidNorm x + torusEuclidNorm y := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_add_le <;> assumption
private theorem torusNorm_sub_comm (x y : Torus4 S) : torusEuclidNorm (x - y) = torusEuclidNorm (y - x) := by apply _root_.YangMills.Construction.AmbientPoints.torusEuclidNorm_sub_comm <;> assumption
private theorem torusNorm_sub_le_sub_add_sub (a b c : Torus4 S) :
    torusEuclidNorm (a - c) ≤ torusEuclidNorm (a - b) + torusEuclidNorm (b - c) := by
  simpa using torusNorm_add_le (a - b) (b - c)
private theorem torusNorm_proj_eq (hS : 0 < S) {v : Fin 4 → ℝ} (hv : ∀ μ, |v μ| ≤ S / 2) :
    torusEuclidNorm (torusProj S v) = euclidNormVec v := by apply _root_.YangMills.Construction.QuotientLattices.torusEuclidNorm_torusProj_of_abs_le <;> assumption
abbrev _root_.YangMills.SharedProofs.p44320 := @torusNorm_proj_eq
private theorem round_neg_of_abs_sub_lt {x : ℝ} (h : |x - round x| < 1 / 2) : round (-x) = -round x := by
  have h' := abs_lt.mp h
  rw [round_eq, Int.floor_eq_iff]
  push_cast
  constructor <;> linarith [h'.1, h'.2]
private theorem circleSub_comm_of_lt (hS : 0 < S) {a b : ℝ} (h : |circleSub S a b| < S / 2) :
    circleSub S b a = -circleSub S a b := by
  set x : ℝ := (a - b) / S with hx
  have hab : a - b = S * x := by
    rw [hx]
    field_simp
  have hba : (b - a) / S = -x := by
    rw [hx]
    ring
  have hz : circleSub S a b = S * (x - round x) := by
    unfold circleSub
    rw [← hx, hab]
    ring
  have hnear : |x - round x| < 1 / 2 := by
    rw [hz, abs_mul, abs_of_pos hS] at h
    have : S * |x - round x| < S * (1 / 2) := by linarith
    exact lt_of_mul_lt_mul_left this hS.le
  have hr := round_neg_of_abs_sub_lt hnear
  have hba' : b - a = -(S * x) := by linarith
  unfold circleSub at hz ⊢
  rw [hba, hr, hz, hba']
  push_cast
  ring
private theorem abs_circleSub_le (hS : 0 < S) (a b : ℝ) : |circleSub S a b| ≤ S / 2 := by
  set x : ℝ := (a - b) / S with hx
  have hab : a - b = S * x := by
    rw [hx]
    field_simp
  have hz : circleSub S a b = S * (x - round x) := by
    unfold circleSub
    rw [← hx, hab]
    ring
  rw [hz, abs_mul, abs_of_pos hS]
  have := abs_sub_round x
  nlinarith
abbrev _root_.YangMills.SharedProofs.p20068 := @abs_circleSub_le
private theorem torusProj_periodicDisplacement (x y : Fin 4 → ℝ) :
    torusProj S (periodicDisplacement S y x) = torusProj S x - torusProj S y := by
  funext μ
  have h : ((S * (round ((x μ - y μ) / S) : ℝ) : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨round ((x μ - y μ) / S), by simp [mul_comm]⟩
  simp only [torusProj, periodicDisplacement, circleSub, Pi.sub_apply, AddCircle.coe_sub, h, sub_zero]
private theorem sqNorm_eq_normVec_sq (z : Fin 4 → ℝ) : sqNorm z = euclidNormVec z ^ 2 := by
  unfold sqNorm euclidNormVec
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
private theorem sum_orderedPlane (g : Fin 4 → Fin 4 → ℝ) :
    ∑ P : OrderedPlane, g P.1.1 P.1.2 = ∑ μ, ∑ ν, if μ < ν then g μ ν else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun e : Fin 4 × Fin 4 => e.1 < e.2) (by simp)
    (fun e => g e.1 e.2), Finset.sum_filter, Fintype.sum_prod_type]
private theorem planeKernelMatrix_neg (z : Fin 4 → ℝ) : planeKernelMatrix (-z) = planeKernelMatrix z := by
  funext P P'
  simp [planeKernelMatrix, continuumCurvatureKernel, hyperplaneReflection, sqNorm]
private theorem hyperplaneReflection_comm (z : Fin 4 → ℝ) (i j : Fin 4) :
    hyperplaneReflection z i j = hyperplaneReflection z j i := by
  unfold hyperplaneReflection
  by_cases h : i = j
  · subst h
    rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    ring
private theorem planeKernelMatrix_comm (z : Fin 4 → ℝ) (P P' : OrderedPlane) :
    planeKernelMatrix z P' P = planeKernelMatrix z P P' := by
  unfold planeKernelMatrix continuumCurvatureKernel
  rw [hyperplaneReflection_comm z P'.1.1 P.1.1, hyperplaneReflection_comm z P'.1.2 P.1.2,
    hyperplaneReflection_comm z P'.1.1 P.1.2, hyperplaneReflection_comm z P'.1.2 P.1.1]
  ring
private theorem trace_kernel_mul_kernel_neg (htr : CurvatureKernelSqTraceFormula)
    {z : Fin 4 → ℝ} (hz : 0 < sqNorm z) :
    Matrix.trace (planeKernelMatrix z * planeKernelMatrix (-z)) = 6 / (Real.pi ^ 4 * sqNorm z ^ 4) := by
  rw [planeKernelMatrix_neg, ← htr z hz]
  have h1 : Matrix.trace (planeKernelMatrix z * planeKernelMatrix z) =
      ∑ P : OrderedPlane, ∑ P' : OrderedPlane, planeKernelMatrix z P P' ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun P' _ => ?_
    rw [planeKernelMatrix_comm z P P', sq]
  rw [h1]
  have h2 : ∀ P : OrderedPlane, ∑ P' : OrderedPlane, planeKernelMatrix z P P' ^ 2 =
      ∑ ρ, ∑ τ, if ρ < τ then continuumCurvatureKernel z P.1.1 P.1.2 ρ τ ^ 2 else 0 := fun P =>
    sum_orderedPlane (fun ρ τ => continuumCurvatureKernel z P.1.1 P.1.2 ρ τ ^ 2)
  simp only [h2]
  rw [sum_orderedPlane (fun μ ν => ∑ ρ, ∑ τ, if ρ < τ then continuumCurvatureKernel z μ ν ρ τ ^ 2 else 0)]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  by_cases h : μ < ν
  · simp [h]
  · simp [h]
abbrev _root_.YangMills.SharedProofs.p793 := @trace_kernel_mul_kernel_neg
private theorem traceAlongCycle_one (u : Fin 2 → Fin 4 → ℝ) :
    traceAlongCycle S u (1 : Equiv.Perm (Fin 2)) =
      Matrix.trace (planeKernelMatrix (periodicDisplacement S (u 1) (u 0)) *
        planeKernelMatrix (periodicDisplacement S (u 0) (u 1))) := by
  simp [traceAlongCycle, List.ofFn_succ]
private def pairTranslateHom (S : ℝ) : (Fin 2 → Fin 4 → ℤ) →+ (Fin 2 → Fin 4 → ℝ) where
  toFun k := fun i => latticeTranslate S (k i)
  map_zero' := by
    funext i μ
    simp [latticeTranslate]
  map_add' k k' := by
    funext i μ
    simp [latticeTranslate, mul_add]
private abbrev pairPeriods (S : ℝ) : AddSubgroup (Fin 2 → Fin 4 → ℝ) := (pairTranslateHom S).range
private instance (S : ℝ) : Countable (pairPeriods S) :=
  (pairTranslateHom S).rangeRestrict_surjective.countable
private def cornerCube (S : ℝ) (a : Fin 4 → ℝ) : Set (Fin 4 → ℝ) := Set.pi univ fun μ => Ico (a μ) (a μ + S)
private def pairCube (S : ℝ) (a : Fin 4 → ℝ) : Set (Fin 2 → Fin 4 → ℝ) := Set.pi univ fun _ => cornerCube S a
private theorem measurableSet_pairCube (a : Fin 4 → ℝ) : MeasurableSet (pairCube S a) :=
  MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Ico
private theorem isAddFundamentalDomain_pairCube (hS : 0 < S) (a : Fin 4 → ℝ) :
    IsAddFundamentalDomain (pairPeriods S) (pairCube S a) volume := by
  refine IsAddFundamentalDomain.mk' (measurableSet_pairCube a).nullMeasurableSet ?_
  intro x
  have hex := fun (i : Fin 2) (μ : Fin 4) => existsUnique_add_zsmul_mem_Ico hS (x i μ) (a μ)
  choose k hk using fun i μ => (hex i μ).exists
  refine ⟨⟨pairTranslateHom S k, k, rfl⟩, ?_, ?_⟩
  · intro i _ μ _
    have h := hk i μ
    have e : (k i μ) • S = S * (k i μ : ℝ) := by simp [mul_comm]
    rw [e] at h
    simpa [pairTranslateHom, latticeTranslate, AddSubgroup.vadd_def, add_comm] using h
  · rintro ⟨_, k', rfl⟩ h
    have hk' : k' = k := by
      funext i μ
      refine (hex i μ).unique ?_ (hk i μ)
      have h1 := h i (mem_univ i) μ (mem_univ μ)
      have e : (k' i μ) • S = S * (k' i μ : ℝ) := by simp [mul_comm]
      rw [e]
      simpa [pairTranslateHom, latticeTranslate, AddSubgroup.vadd_def, add_comm] using h1
    subst hk'
    rfl
private theorem setIntegral_pairCube_eq (hS : 0 < S) (a b : Fin 4 → ℝ) {g : (Fin 2 → Fin 4 → ℝ) → ℝ}
    (hg : ∀ k v, g (pairTranslateHom S k + v) = g v) :
    ∫ v in pairCube S a, g v = ∫ v in pairCube S b, g v := by
  refine (isAddFundamentalDomain_pairCube hS a).setIntegral_eq (isAddFundamentalDomain_pairCube hS b) ?_
  rintro ⟨_, k, rfl⟩ x
  exact hg k x
private def pairIntegrand (f h : Torus4 S → ℝ) (u : Fin 2 → Fin 4 → ℝ) : ℝ :=
  f (torusProj S (u 0)) * h (torusProj S (u 1)) * torusEuclidNorm (torusProj S (u 0) - torusProj S (u 1)) ^ (-8 : ℤ)
private theorem pairIntegrand_periodic (f h : Torus4 S → ℝ) (k : Fin 2 → Fin 4 → ℤ)
    (v : Fin 2 → Fin 4 → ℝ) : pairIntegrand f h (pairTranslateHom S k + v) = pairIntegrand f h v := by
  have e : ∀ i, torusProj S ((pairTranslateHom S k + v) i) = torusProj S (v i) := by
    intro i
    have : (pairTranslateHom S k + v) i = v i + latticeTranslate S (k i) := by
      simp [pairTranslateHom, add_comm]
    rw [this, torusProj_add_latticeTranslate]
  simp only [pairIntegrand, e]
private theorem closedBallR4_subset_cornerCube (hS : 0 < S) {c : Fin 4 → ℝ} {r : ℝ} (hr : r ≤ S / 4) :
    closedBallR4 c r ⊆ cornerCube S (fun μ => c μ - S / 2) := by
  intro v hv μ _
  have h1 : |(v - c) μ| ≤ r := (abs_coord_le_norm (v - c) μ).trans hv
  have h2 := abs_le.mp h1
  simp only [Pi.sub_apply] at h2
  constructor <;> linarith [h2.1, h2.2]
private theorem liftToBall_eq_of_mem (hS : 0 < S) {c : Fin 4 → ℝ} {r : ℝ} {f : Torus4 S → ℝ}
    (hf : tsupport f ⊆ closedBallTorus (torusProj S c) r) {v : Fin 4 → ℝ}
    (hv : v ∈ cornerCube S (fun μ => c μ - S / 2)) : liftToBall S c r f v = f (torusProj S v) := by
  unfold liftToBall
  by_cases hB : v ∈ closedBallR4 c r
  · rw [indicator_of_mem hB]
    rfl
  · rw [indicator_of_notMem hB]
    by_contra hne
    refine hB ?_
    have hm : torusProj S v ∈ closedBallTorus (torusProj S c) r := hf (subset_tsupport _ (Ne.symm hne))
    have hm' : torusEuclidNorm (torusProj S v - torusProj S c) ≤ r := hm
    rw [← torusProj_sub, torusNorm_proj_eq hS] at hm'
    · exact hm'
    · intro μ
      have h2 := hv μ (mem_univ μ)
      simp only [Pi.sub_apply]
      rw [abs_le]
      constructor <;> linarith [h2.1, h2.2]
private theorem mem_closedBallR4_of_liftToBall_ne {c : Fin 4 → ℝ} {r : ℝ} {f : Torus4 S → ℝ} {v : Fin 4 → ℝ}
    (hv : liftToBall S c r f v ≠ 0) : v ∈ closedBallR4 c r := by
  by_contra hb
  exact hv (indicator_of_notMem hb _)
private theorem setIntegral_pairIntegrand (hS : 0 < S) {c : Fin 4 → ℝ} {r : ℝ} (hr : r ≤ S / 4)
    {f h : Torus4 S → ℝ} (hsf : tsupport f ⊆ closedBallTorus (torusProj S c) r)
    (hsh : tsupport h ⊆ closedBallTorus (torusProj S c) r) :
    ∫ u in pairCube S (fun μ => c μ - S / 2), pairIntegrand f h u =
      inverseEighthKernel (liftToBall S c r f) (liftToBall S c r h) := by
  set F : (Fin 4 → ℝ) → ℝ := liftToBall S c r f with hF
  set G : (Fin 4 → ℝ) → ℝ := liftToBall S c r h with hG
  set Ψ : (Fin 2 → Fin 4 → ℝ) → ℝ :=
    fun u => F (u 0) * G (u 1) * euclidNormVec (u 0 - u 1) ^ (-8 : ℤ) with hΨ
  have hker : inverseEighthKernel F G = ∫ u, Ψ u := by
    have h1 := (volume_preserving_finTwoArrow (Fin 4 → ℝ)).integral_comp'
      (fun z : (Fin 4 → ℝ) × (Fin 4 → ℝ) => F z.1 * G z.2 * euclidNormVec (z.1 - z.2) ^ (-8 : ℤ))
    simp only [inverseEighthKernel, RCLike.ofReal_real_eq_id, id]
    exact h1.symm
  have hout : ∀ u, u ∉ pairCube S (fun μ => c μ - S / 2) → Ψ u = 0 := by
    intro u hu
    by_contra hne
    have h1 : F (u 0) ≠ 0 := fun h0 => hne (by simp [hΨ, h0])
    have h2 : G (u 1) ≠ 0 := fun h0 => hne (by simp [hΨ, h0])
    refine hu ?_
    intro i _
    fin_cases i
    · exact closedBallR4_subset_cornerCube hS hr (mem_closedBallR4_of_liftToBall_ne h1)
    · exact closedBallR4_subset_cornerCube hS hr (mem_closedBallR4_of_liftToBall_ne h2)
  rw [hker, ← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  refine setIntegral_congr_fun (measurableSet_pairCube _) ?_
  intro u hu
  have hu0 : u 0 ∈ cornerCube S (fun μ => c μ - S / 2) := hu 0 (mem_univ _)
  have hu1 : u 1 ∈ cornerCube S (fun μ => c μ - S / 2) := hu 1 (mem_univ _)
  have e0 : F (u 0) = f (torusProj S (u 0)) := liftToBall_eq_of_mem hS hsf hu0
  have e1 : G (u 1) = h (torusProj S (u 1)) := liftToBall_eq_of_mem hS hsh hu1
  simp only [pairIntegrand, hΨ, e0, e1]
  by_cases hf0 : f (torusProj S (u 0)) = 0
  · simp [hf0]
  by_cases hh0 : h (torusProj S (u 1)) = 0
  · simp [hh0]
  have hb0 : u 0 ∈ closedBallR4 c r := mem_closedBallR4_of_liftToBall_ne (f := f) (by rw [← hF, e0]; exact hf0)
  have hb1 : u 1 ∈ closedBallR4 c r := mem_closedBallR4_of_liftToBall_ne (f := h) (by rw [← hG, e1]; exact hh0)
  have hcoord : ∀ μ, |(u 0 - u 1) μ| ≤ S / 2 := by
    intro μ
    have h1 := abs_le.mp ((abs_coord_le_norm (u 0 - c) μ).trans hb0)
    have h2 := abs_le.mp ((abs_coord_le_norm (u 1 - c) μ).trans hb1)
    simp only [Pi.sub_apply] at h1 h2 ⊢
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  rw [← torusProj_sub, torusNorm_proj_eq hS hcoord]
private theorem cycle_integrand_eq (htr : CurvatureKernelSqTraceFormula) {n : ℝ}
    (hn : 0 < n) (hS : 40 * n ≤ S) {f h : Torus4 S → ℝ}
    (hsep : ∀ p ∈ tsupport f, ∀ q ∈ tsupport h, n ≤ torusEuclidNorm (p - q))
    (hfar : ∀ p ∈ tsupport f, ∀ q ∈ tsupport h, torusEuclidNorm (p - q) ≤ 10 * n)
    (u : Fin 2 → Fin 4 → ℝ) :
    f (torusProj S (u 0)) * h (torusProj S (u 1)) * traceAlongCycle S u (1 : Equiv.Perm (Fin 2)) =
      6 / Real.pi ^ 4 * pairIntegrand f h u := by
  have hS0 : 0 < S := by linarith
  unfold pairIntegrand
  by_cases hf0 : f (torusProj S (u 0)) = 0
  · simp [hf0]
  by_cases hh0 : h (torusProj S (u 1)) = 0
  · simp [hh0]
  have hlo := hsep _ (subset_tsupport _ hf0) _ (subset_tsupport _ hh0)
  have hhi := hfar _ (subset_tsupport _ hf0) _ (subset_tsupport _ hh0)
  set z : Fin 4 → ℝ := periodicDisplacement S (u 1) (u 0) with hz
  have hcov : torusProj S z = torusProj S (u 0) - torusProj S (u 1) := torusProj_periodicDisplacement (u 0) (u 1)
  have hhalf : ∀ μ, |z μ| ≤ S / 2 := fun μ => abs_circleSub_le hS0 _ _
  have hnum : torusEuclidNorm (torusProj S (u 0) - torusProj S (u 1)) = euclidNormVec z := by
    rw [← hcov]
    exact torusNorm_proj_eq hS0 hhalf
  rw [hnum] at hlo hhi ⊢
  have hneg : periodicDisplacement S (u 0) (u 1) = -z := by
    funext μ
    have hlt : |z μ| < S / 2 := by
      have := abs_coord_le_norm z μ
      linarith
    exact circleSub_comm_of_lt hS0 hlt
  have hpos : 0 < euclidNormVec z := by linarith
  have hsq : 0 < sqNorm z := by
    rw [sqNorm_eq_normVec_sq]
    positivity
  rw [traceAlongCycle_one, ← hz, hneg, trace_kernel_mul_kernel_neg htr hsq, sqNorm_eq_normVec_sq]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hv : euclidNormVec z ≠ 0 := hpos.ne'
  have e8 : euclidNormVec z ^ (-8 : ℤ) = (euclidNormVec z ^ 8)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  rw [e8]
  field_simp
private theorem cumulant_eq_setIntegral (htr : CurvatureKernelSqTraceFormula)
    {n : ℝ} (hn : 0 < n) (hS : 40 * n ≤ S) {f h : Torus4 S → ℝ}
    (hsep : ∀ p ∈ tsupport f, ∀ q ∈ tsupport h, n ≤ torusEuclidNorm (p - q))
    (hfar : ∀ p ∈ tsupport f, ∀ q ∈ tsupport h, torusEuclidNorm (p - q) ≤ 10 * n) :
    gaussianCumulantLimit (q := 1) S ![f, h] =
      9 / Real.pi ^ 4 * ∫ u in pairCube S (fun _ => 0), pairIntegrand f h u := by
  have hone : ∀ s : Equiv.Perm (Fin 2), s 0 = 0 → s = 1 := by
    intro s hs
    refine Equiv.ext fun i => ?_
    fin_cases i
    · simpa using hs
    · have h1 : s 1 ≠ 0 := fun h0 => by
        have := s.injective (h0.trans hs.symm)
        exact absurd this (by decide)
      apply Fin.ext
      have hlt := (s 1).isLt
      have hne : (s 1).val ≠ 0 := fun h0 => h1 (Fin.ext h0)
      simp only [Equiv.Perm.coe_one, id, Fin.isValue, Fin.mk_one, Fin.val_one]
      omega
  unfold gaussianCumulantLimit
  rw [Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin (1 + 1))) (by simp)
    (fun s hs hne => absurd (hone s (Finset.mem_filter.mp hs).2) hne)]
  have hcube : (Set.pi univ fun _ : Fin (1 + 1) => Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) S) =
      pairCube S (fun _ => 0) := by
    simp [pairCube, cornerCube]
  rw [hcube]
  have hint : ∀ u : Fin (1 + 1) → Fin 4 → ℝ,
      (∏ i, (![f, h] : Fin (1 + 1) → Torus4 S → ℝ) i (torusProj S (u i))) * traceAlongCycle S u 1 =
        6 / Real.pi ^ 4 * pairIntegrand f h u := by
    intro u
    rw [← cycle_integrand_eq htr hn hS hsep hfar u, Fin.prod_univ_two]
    rfl
  simp only [hint]
  rw [integral_const_mul]
  ring
private theorem cumulant_eq_kernel_torus (htr : CurvatureKernelSqTraceFormula) {n vt : ℝ}
    (hn : 0 < n) (hS : 40 * n ≤ S) {f h : Torus4 S → ℝ} (hp : (f, h) ∈ separatedPairsTorus S n vt) :
    gaussianCumulantLimit (q := 1) S ![f, h] = 9 / Real.pi ^ 4 * inverseEighthKernelTorus (ℓ := S) f h := by
  have hS0 : 0 < S := by linarith
  obtain ⟨x₁, x₂, hbf, hbh, hlo, hhi⟩ := hp
  obtain ⟨-, -, -, hsf, -, -⟩ := hbf
  obtain ⟨-, -, -, hsh, -, -⟩ := hbh
  simp only at hsf hsh hlo hhi
  have hsep : ∀ p ∈ tsupport f, ∀ q ∈ tsupport h, n ≤ torusEuclidNorm (p - q) := by
    intro p hp q hq
    have h1 : setEuclidDist (tsupport f) (tsupport h) ≤ ENNReal.ofReal (torusEuclidNorm (p - q)) :=
      iInf₂_le_of_le p hp (iInf₂_le q hq)
    exact (ENNReal.ofReal_le_ofReal_iff (torusNorm_nonneg _)).mp (hlo.trans h1)
  have hnear : ∀ ε, 0 < ε → ∃ p ∈ tsupport f, ∃ q ∈ tsupport h,
      torusEuclidNorm (p - q) ≤ 6 * n + ε := by
    intro ε hε
    by_contra hno
    push Not at hno
    have h1 : ENNReal.ofReal (6 * n + ε) ≤ setEuclidDist (tsupport f) (tsupport h) :=
      le_iInf₂ fun p hp => le_iInf₂ fun q hq =>
        ENNReal.ofReal_le_ofReal (hno p hp q hq).le
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (h1.trans hhi)
    linarith
  have hinf : ∀ u ∈ tsupport f, torusEuclidNorm (u - x₁) ≤ n := fun u hu => hsf hu
  have hinh : ∀ w ∈ tsupport h, torusEuclidNorm (w - x₂) ≤ n := fun w hw => hsh hw
  have hfar : ∀ u ∈ tsupport f, ∀ w ∈ tsupport h, torusEuclidNorm (u - w) ≤ 10 * n := by
    intro u hu w hw
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨p, hp, q, hq, hpq⟩ := hnear ε hε
    have t1 := torusNorm_sub_le_sub_add_sub u x₁ w
    have t2 := torusNorm_sub_le_sub_add_sub x₁ p w
    have t3 := torusNorm_sub_le_sub_add_sub p q w
    have t4 := torusNorm_sub_le_sub_add_sub q x₂ w
    have e1 := hinf u hu
    have e2 := hinf p hp
    have e3 := hinh q hq
    have e4 := hinh w hw
    rw [torusNorm_sub_comm x₁ p] at t2
    rw [torusNorm_sub_comm x₂ w] at t4
    linarith
  have hwx : ∀ w ∈ tsupport h, torusEuclidNorm (w - x₁) ≤ 10 * n := by
    intro w hw
    obtain ⟨p, hp, q, hq, hpq⟩ := hnear n hn
    have t1 := torusNorm_sub_le_sub_add_sub w x₂ x₁
    have t2 := torusNorm_sub_le_sub_add_sub x₂ q x₁
    have t3 := torusNorm_sub_le_sub_add_sub q p x₁
    have e2 := hinf p hp
    have e3 := hinh q hq
    have e4 := hinh w hw
    rw [torusNorm_sub_comm x₂ q] at t2
    rw [torusNorm_sub_comm q p] at t3
    linarith
  have hpos : 0 < setEuclidDist (tsupport f) (tsupport h) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hn) hlo
  have H : ∃ q : (Fin 4 → ℝ) × ℝ, IsKernelBallTorus f h q.1 q.2 := by
    refine ⟨(liftPoint x₁, 10 * n), hpos, by simpa using hn, ?_, ?_, ?_⟩
    · simp only
      linarith
    · intro u hu
      change torusEuclidNorm (u - torusProj S (liftPoint x₁)) ≤ 10 * n
      rw [torusProj_liftPoint]
      linarith [hinf u hu]
    · intro w hw
      change torusEuclidNorm (w - torusProj S (liftPoint x₁)) ≤ 10 * n
      rw [torusProj_liftPoint]
      exact hwx w hw
  unfold inverseEighthKernelTorus
  rw [dif_pos H]
  obtain ⟨-, -, hr, hbf', hbh'⟩ := H.choose_spec
  rw [cumulant_eq_setIntegral htr hn hS hsep hfar,
    setIntegral_pairCube_eq hS0 (fun _ => 0) (fun μ => H.choose.1 μ - S / 2) (pairIntegrand_periodic f h),
    setIntegral_pairIntegrand hS0 hr hbf' hbh']
end GaussianPairProof
theorem gaussianTwoPointPair_holds (htr : LinearResponse.CurvatureKernelSqTraceFormula) :
    gaussianTwoPointPair := by
  intro L m d ϑ _ hd hside f h hp
  exact GaussianPairProof.cumulant_eq_kernel_torus htr hd hside hp
end YangMills.Construction.FourPointCondition
end

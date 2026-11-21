import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.LawInAState.ReflectionKernelAtADistanceProof
import YangMills.Construction.SourcesAndGluing.LatticeIsometriesAndTheirAction
import YangMills.Construction.FourPointCondition.ConnectedLawOfACollinearQuadrupleProof
import YangMills.Construction.FourPointCondition.ConnectedLawOfAPairProof
import YangMills.Construction.FourPointCondition.RiemannSumOfTheBareTraces
import YangMills.Construction.Torus.TorusLengthsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FourPointCondition
section KernelEstimates
open TestFunctions PeriodicLattice ResponseInTheExpansion TorusFields LinearResponse
private def vecNorm (z : Fin 4 → ℝ) : ℝ := Real.sqrt (sqNorm z)
private lemma sqNorm_nonneg_aux (z : Fin 4 → ℝ) : 0 ≤ sqNorm z := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.sumSq_nonneg <;> assumption
private lemma abs_coord_le_vecNorm (z : Fin 4 → ℝ) (i : Fin 4) : |z i| ≤ vecNorm z := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private lemma vecNorm_nonneg (z : Fin 4 → ℝ) : 0 ≤ vecNorm z := Real.sqrt_nonneg _
private lemma vecNorm_sq (z : Fin 4 → ℝ) : vecNorm z ^ 2 = sqNorm z := Real.sq_sqrt (sqNorm_nonneg_aux z)
private lemma abs_coord_mul_le_sqNorm (z : Fin 4 → ℝ) (i j : Fin 4) : |z i * z j| ≤ sqNorm z := by apply _root_.YangMills.Construction.ReflectionKernel.abs_mul_apply_le_normSq <;> assumption
private lemma abs_reflection_le_three {z : Fin 4 → ℝ} (hz : 0 < sqNorm z) (i j : Fin 4) :
    |hyperplaneReflection z i j| ≤ 3 := by
  unfold hyperplaneReflection
  have h1 : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  have h2 : |2 * z i * z j / sqNorm z| ≤ 2 := by
    rw [abs_div, abs_of_pos hz, div_le_iff₀ hz, mul_assoc, abs_mul]
    have := abs_coord_mul_le_sqNorm z i j
    simp only [abs_two]
    linarith
  calc _ ≤ |(if i = j then (1 : ℝ) else 0)| + |2 * z i * z j / sqNorm z| := abs_sub _ _
    _ ≤ 3 := by linarith
abbrev _root_.YangMills.SharedProofs.p8496 := @abs_reflection_le_three
private lemma nine_le_pi_sq : (9 : ℝ) ≤ Real.pi ^ 2 := by
  have := Real.pi_gt_three
  nlinarith
private lemma abs_reflection_minor_le {z : Fin 4 → ℝ} (hz : 0 < sqNorm z) (μ ν ρ τ : Fin 4) :
    |hyperplaneReflection z μ ρ * hyperplaneReflection z ν τ - hyperplaneReflection z μ τ * hyperplaneReflection z ν ρ| ≤ 18 := by
  have h1 := abs_reflection_le_three hz μ ρ
  have h2 := abs_reflection_le_three hz ν τ
  have h3 := abs_reflection_le_three hz μ τ
  have h4 := abs_reflection_le_three hz ν ρ
  calc _ ≤ |hyperplaneReflection z μ ρ * hyperplaneReflection z ν τ| + |hyperplaneReflection z μ τ * hyperplaneReflection z ν ρ| := abs_sub _ _
    _ ≤ 3 * 3 + 3 * 3 := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) (mul_le_mul h3 h4 (abs_nonneg _) (by norm_num))
    _ = 18 := by norm_num
abbrev _root_.YangMills.DeltaSharedProofs.p500912 := @abs_reflection_minor_le
private lemma abs_kernel_le_of_sq_le {z : Fin 4 → ℝ} {r : ℝ} (hr : 0 < r) (hz : r ^ 2 ≤ sqNorm z) (μ ν ρ τ : Fin 4) :
    |_root_.YangMills.Construction.LinearResponse.continuumCurvatureKernel z μ ν ρ τ| ≤ 2 / r ^ 4 := by
  have hz0 : 0 < sqNorm z := lt_of_lt_of_le (by positivity) hz
  unfold _root_.YangMills.Construction.LinearResponse.continuumCurvatureKernel
  have hd : 0 < Real.pi ^ 2 * sqNorm z ^ 2 := by positivity
  rw [abs_div, abs_of_pos hd, div_le_div_iff₀ hd (by positivity)]
  have h1 := abs_reflection_minor_le hz0 μ ν ρ τ
  have h2 : r ^ 4 ≤ sqNorm z ^ 2 := by
    calc r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hz 2
  have h3 := nine_le_pi_sq
  have h4 : 9 * r ^ 4 ≤ Real.pi ^ 2 * sqNorm z ^ 2 :=
    mul_le_mul h3 h2 (by positivity) (by positivity)
  calc _ ≤ 18 * r ^ 4 := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ _ := by linarith
private lemma abs_sqNorm_sub_le {z w : Fin 4 → ℝ} {δ : ℝ} (h : ∀ k, |z k - w k| ≤ δ) :
    |sqNorm z - sqNorm w| ≤ 4 * δ * (vecNorm z + vecNorm w) := by
  unfold sqNorm
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ k : Fin 4, |z k ^ 2 - w k ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 4, δ * (vecNorm z + vecNorm w) := by
      refine Finset.sum_le_sum fun k _ => ?_
      rw [show z k ^ 2 - w k ^ 2 = (z k - w k) * (z k + w k) by ring, abs_mul]
      refine mul_le_mul (h k) ?_ (abs_nonneg _) ((abs_nonneg _).trans (h k))
      exact (abs_add_le _ _).trans (add_le_add (abs_coord_le_vecNorm z k) (abs_coord_le_vecNorm w k))
    _ = _ := by simp; ring
private lemma abs_coord_mul_sub_le {z w : Fin 4 → ℝ} {δ : ℝ} (h : ∀ k, |z k - w k| ≤ δ) (i j : Fin 4) :
    |z i * z j - w i * w j| ≤ δ * (vecNorm z + vecNorm w) := by
  rw [show z i * z j - w i * w j = z i * (z j - w j) + w j * (z i - w i) by ring]
  calc _ ≤ |z i * (z j - w j)| + |w j * (z i - w i)| := abs_add_le _ _
    _ ≤ vecNorm z * δ + vecNorm w * δ := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul (abs_coord_le_vecNorm z i) (h j) (abs_nonneg _) (vecNorm_nonneg z))
        (mul_le_mul (abs_coord_le_vecNorm w j) (h i) (abs_nonneg _) (vecNorm_nonneg w))
    _ = _ := by ring
private lemma vecNorm_mono {z w : Fin 4 → ℝ} (h : sqNorm w ≤ sqNorm z) : vecNorm w ≤ vecNorm z :=
  Real.sqrt_le_sqrt h
private lemma le_vecNorm_of_sq_le {z : Fin 4 → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : r ^ 2 ≤ sqNorm z) : r ≤ vecNorm z :=
  Real.le_sqrt_of_sq_le h
private lemma reflection_lipschitz_of_le {z w : Fin 4 → ℝ} {δ r : ℝ} (hr : 0 < r) (hw : r ^ 2 ≤ sqNorm w)
    (hab : sqNorm w ≤ sqNorm z) (h : ∀ k, |z k - w k| ≤ δ) (i j : Fin 4) :
    |hyperplaneReflection z i j - hyperplaneReflection w i j| ≤ 20 * δ / r := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (h 0)
  have hb : 0 < sqNorm w := lt_of_lt_of_le (by positivity) hw
  have ha : 0 < sqNorm z := lt_of_lt_of_le hb hab
  have hsb : r ≤ vecNorm w := le_vecNorm_of_sq_le hr.le hw
  have hsab : vecNorm w ≤ vecNorm z := vecNorm_mono hab
  have hsa : 0 < vecNorm z := lt_of_lt_of_le hr (hsb.trans hsab)
  have hXY := abs_coord_mul_sub_le h i j
  have hab' := abs_sqNorm_sub_le h
  have hY := abs_coord_mul_le_sqNorm w i j
  set a := sqNorm z with ha_def
  set b := sqNorm w with hb_def
  set sa := vecNorm z
  have hsq : sa ^ 2 = a := vecNorm_sq z
  have key : |z i * z j / a - w i * w j / b| ≤ 10 * δ / sa := by
    rw [show z i * z j / a - w i * w j / b =
      ((z i * z j - w i * w j) * b + (w i * w j) * (b - a)) / (a * b) by field_simp; ring]
    rw [abs_div, abs_of_pos (mul_pos ha hb), div_le_iff₀ (mul_pos ha hb)]
    have e1 : |z i * z j - w i * w j| ≤ 2 * δ * sa := by nlinarith
    have e2 : |b - a| ≤ 8 * δ * sa := by
      rw [abs_sub_comm]; nlinarith
    calc _ ≤ |(z i * z j - w i * w j) * b| + |(w i * w j) * (b - a)| := abs_add_le _ _
      _ ≤ (2 * δ * sa) * b + b * (8 * δ * sa) := by
        rw [abs_mul, abs_mul, abs_of_pos hb]
        exact add_le_add (mul_le_mul_of_nonneg_right e1 hb.le)
          (mul_le_mul hY e2 (abs_nonneg _) hb.le)
      _ = 10 * δ / sa * (a * b) := by
        rw [← hsq]; field_simp; ring
  have e3 : 10 * δ / sa ≤ 10 * δ / r :=
    div_le_div_of_nonneg_left (by positivity) hr (hsb.trans hsab)
  unfold hyperplaneReflection
  rw [show (if i = j then (1 : ℝ) else 0) - 2 * z i * z j / a - ((if i = j then (1 : ℝ) else 0) - 2 * w i * w j / b)
      = -2 * (z i * z j / a - w i * w j / b) by ring, abs_mul]
  have e4 : |(-2 : ℝ)| = 2 := by norm_num
  rw [e4]
  calc _ ≤ 2 * (10 * δ / r) := by
        exact mul_le_mul_of_nonneg_left (key.trans e3) (by norm_num)
    _ = _ := by ring
private lemma kernel_lipschitz_of_le {z w : Fin 4 → ℝ} {δ r : ℝ} (hr : 0 < r) (hw : r ^ 2 ≤ sqNorm w)
    (hab : sqNorm w ≤ sqNorm z) (h : ∀ k, |z k - w k| ≤ δ) (μ ν ρ τ : Fin 4) :
    |_root_.YangMills.Construction.LinearResponse.continuumCurvatureKernel z μ ν ρ τ - _root_.YangMills.Construction.LinearResponse.continuumCurvatureKernel w μ ν ρ τ| ≤ 60 * δ / r ^ 5 := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (h 0)
  have hb : 0 < sqNorm w := lt_of_lt_of_le (by positivity) hw
  have ha : 0 < sqNorm z := lt_of_lt_of_le hb hab
  have hsb : r ≤ vecNorm w := le_vecNorm_of_sq_le hr.le hw
  have hsab : vecNorm w ≤ vecNorm z := vecNorm_mono hab
  have hsa : 0 < vecNorm z := lt_of_lt_of_le hr (hsb.trans hsab)
  have hab' := abs_sqNorm_sub_le h
  have hnw := abs_reflection_minor_le hb μ ν ρ τ
  have e : ∀ i j, |hyperplaneReflection z i j - hyperplaneReflection w i j| ≤ 20 * δ / r :=
    reflection_lipschitz_of_le hr hw hab h
  have bz := abs_reflection_le_three ha
  have bw := abs_reflection_le_three hb
  set e0 := 20 * δ / r with he0
  have he00 : 0 ≤ e0 := by positivity
  have prod_lip : ∀ i j k l, |hyperplaneReflection z i j * hyperplaneReflection z k l -
      hyperplaneReflection w i j * hyperplaneReflection w k l| ≤ 6 * e0 := by
    intro i j k l
    rw [show hyperplaneReflection z i j * hyperplaneReflection z k l - hyperplaneReflection w i j * hyperplaneReflection w k l =
      (hyperplaneReflection z i j - hyperplaneReflection w i j) * hyperplaneReflection z k l +
        hyperplaneReflection w i j * (hyperplaneReflection z k l - hyperplaneReflection w k l) by ring]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ e0 * 3 + 3 * e0 := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul (e i j) (bz k l) (abs_nonneg _) he00)
          (mul_le_mul (bw i j) (e k l) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have hnum : |(hyperplaneReflection z μ ρ * hyperplaneReflection z ν τ - hyperplaneReflection z μ τ * hyperplaneReflection z ν ρ) -
      (hyperplaneReflection w μ ρ * hyperplaneReflection w ν τ - hyperplaneReflection w μ τ * hyperplaneReflection w ν ρ)| ≤ 12 * e0 := by
    rw [sub_sub_sub_comm]
    calc _ ≤ _ := abs_sub _ _
      _ ≤ 6 * e0 + 6 * e0 := add_le_add (prod_lip _ _ _ _) (prod_lip _ _ _ _)
      _ = _ := by ring
  unfold _root_.YangMills.Construction.LinearResponse.continuumCurvatureKernel
  set Az := hyperplaneReflection z μ ρ * hyperplaneReflection z ν τ - hyperplaneReflection z μ τ * hyperplaneReflection z ν ρ
  set Aw := hyperplaneReflection w μ ρ * hyperplaneReflection w ν τ - hyperplaneReflection w μ τ * hyperplaneReflection w ν ρ
  set a := sqNorm z with ha_def
  set b := sqNorm w with hb_def
  set sa := vecNorm z
  have hsq : sa ^ 2 = a := vecNorm_sq z
  have hpi : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hr2 : r ^ 2 ≤ a := hw.trans hab
  have hb4 : r ^ 4 ≤ b ^ 2 := by
    calc r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hw 2
  have ha4 : r ^ 4 ≤ a ^ 2 := by
    calc r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hr2 2
  have e2 : |b - a| ≤ 8 * δ * sa := by
    rw [abs_sub_comm]; nlinarith
  have t1 : |(Az - Aw) / a ^ 2| ≤ 240 * δ / r ^ 5 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < a ^ 2)]
    calc _ ≤ (12 * e0) / r ^ 4 := div_le_div₀ (by positivity) hnum (by positivity) ha4
      _ = _ := by rw [he0]; field_simp; ring
  have t2 : |Aw * (b ^ 2 - a ^ 2) / (a ^ 2 * b ^ 2)| ≤ 288 * δ / r ^ 5 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < a ^ 2 * b ^ 2), abs_mul]
    have e3 : |b ^ 2 - a ^ 2| ≤ (8 * δ * sa) * (2 * a) := by
      rw [show b ^ 2 - a ^ 2 = (b - a) * (b + a) by ring, abs_mul, abs_of_pos (by positivity : 0 < b + a)]
      exact mul_le_mul e2 (by linarith) (by positivity) (by positivity)
    calc _ ≤ (18 * ((8 * δ * sa) * (2 * a))) / (a ^ 2 * b ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul hnw e3 (abs_nonneg _) (by norm_num)) (by positivity)
      _ = 288 * δ / (sa * b ^ 2) := by rw [← hsq]; field_simp; ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        calc r ^ 5 = r * r ^ 4 := by ring
          _ ≤ sa * b ^ 2 := mul_le_mul (hsb.trans hsab) hb4 (by positivity) hsa.le
  rw [show Az / (Real.pi ^ 2 * a ^ 2) - Aw / (Real.pi ^ 2 * b ^ 2) =
      ((Az - Aw) / a ^ 2 + Aw * (b ^ 2 - a ^ 2) / (a ^ 2 * b ^ 2)) / Real.pi ^ 2 by field_simp; ring]
  rw [abs_div, abs_of_pos hpi]
  have t3 : |(Az - Aw) / a ^ 2 + Aw * (b ^ 2 - a ^ 2) / (a ^ 2 * b ^ 2)| ≤ 528 * δ / r ^ 5 := by
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ 240 * δ / r ^ 5 + 288 * δ / r ^ 5 := add_le_add t1 t2
      _ = _ := by ring
  calc _ ≤ (528 * δ / r ^ 5) / 9 := div_le_div₀ (by positivity) t3 (by norm_num) nine_le_pi_sq
    _ ≤ _ := by
      have : 0 ≤ δ / r ^ 5 := by positivity
      have e : 528 * δ / r ^ 5 / 9 = (528 / 9) * (δ / r ^ 5) := by ring
      have e' : 60 * δ / r ^ 5 = 60 * (δ / r ^ 5) := by ring
      rw [e, e']
      nlinarith
private lemma kernel_lipschitz {z w : Fin 4 → ℝ} {δ r : ℝ} (hr : 0 < r) (hz : r ^ 2 ≤ sqNorm z)
    (hw : r ^ 2 ≤ sqNorm w) (h : ∀ k, |z k - w k| ≤ δ) (μ ν ρ τ : Fin 4) :
    |_root_.YangMills.Construction.LinearResponse.continuumCurvatureKernel z μ ν ρ τ - _root_.YangMills.Construction.LinearResponse.continuumCurvatureKernel w μ ν ρ τ| ≤ 60 * δ / r ^ 5 := by
  rcases le_total (sqNorm w) (sqNorm z) with hab | hab
  · exact kernel_lipschitz_of_le hr hw hab h μ ν ρ τ
  · rw [abs_sub_comm]
    exact kernel_lipschitz_of_le hr hz hab (fun k => by rw [abs_sub_comm]; exact h k) μ ν ρ τ
private lemma kernel_neg (z : Fin 4 → ℝ) (μ ν ρ τ : Fin 4) :
    _root_.YangMills.Construction.LinearResponse.continuumCurvatureKernel (-z) μ ν ρ τ = _root_.YangMills.Construction.LinearResponse.continuumCurvatureKernel z μ ν ρ τ := by
  have h : sqNorm (-z) = sqNorm z := by simp [sqNorm]
  simp [_root_.YangMills.Construction.LinearResponse.continuumCurvatureKernel, hyperplaneReflection, h]
abbrev _root_.YangMills.SharedProofs.p14816 := @kernel_neg
private lemma abs_prod_sub_prod_mul_le {ι : Type*} [DecidableEq ι] (t : Finset ι) (a b : ι → ℝ) {M η : ℝ} (hM : 0 < M) (hη : 0 ≤ η)
    (ha : ∀ i ∈ t, |a i| ≤ M) (hb : ∀ i ∈ t, |b i| ≤ M) (hab : ∀ i ∈ t, |a i - b i| ≤ η) :
    |∏ i ∈ t, a i - ∏ i ∈ t, b i| * M ≤ t.card * M ^ t.card * η := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have ih' := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)) (fun j hj => hb j (Finset.mem_insert_of_mem hj))
      (fun j hj => hab j (Finset.mem_insert_of_mem hj))
    have hbound : |∏ j ∈ t, a j| ≤ M ^ t.card := by
      rw [Finset.abs_prod]
      calc _ ≤ ∏ _j ∈ t, M := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
            (fun j hj => ha j (Finset.mem_insert_of_mem hj))
        _ = _ := by simp
    have e : a i * ∏ j ∈ t, a j - b i * ∏ j ∈ t, b j =
        (a i - b i) * ∏ j ∈ t, a j + b i * (∏ j ∈ t, a j - ∏ j ∈ t, b j) := by ring
    rw [e]
    have h1 : |(a i - b i) * ∏ j ∈ t, a j| ≤ η * M ^ t.card := by
      rw [abs_mul]
      exact mul_le_mul (hab i (Finset.mem_insert_self _ _)) hbound (abs_nonneg _) hη
    have h2 : |b i * (∏ j ∈ t, a j - ∏ j ∈ t, b j)| * M ≤ M * (t.card * M ^ t.card * η) := by
      rw [abs_mul, mul_assoc]
      exact mul_le_mul (hb i (Finset.mem_insert_self _ _)) ih' (by positivity) hM.le
    calc _ ≤ (|(a i - b i) * ∏ j ∈ t, a j| + |b i * (∏ j ∈ t, a j - ∏ j ∈ t, b j)|) * M :=
          mul_le_mul_of_nonneg_right (abs_add_le _ _) hM.le
      _ = |(a i - b i) * ∏ j ∈ t, a j| * M + |b i * (∏ j ∈ t, a j - ∏ j ∈ t, b j)| * M := by ring
      _ ≤ (η * M ^ t.card) * M + M * (t.card * M ^ t.card * η) :=
          add_le_add (mul_le_mul_of_nonneg_right h1 hM.le) h2
      _ = _ := by push_cast; ring
end KernelEstimates
section PeriodicGeometry
open TestFunctions PeriodicLattice ResponseInTheExpansion TorusFields LinearResponse TorusMetric
private lemma abs_circleSub_le {S : ℝ} (hS : 0 < S) (u v : ℝ) : |circleSub S u v| ≤ S / 2 := by apply _root_.YangMills.SharedProofs.p20068 <;> assumption
private lemma abs_circleSub_le_lift {S : ℝ} (hS : 0 < S) (u v : ℝ) (k : ℤ) :
    |circleSub S u v| ≤ |u - v - k * S| := by
  unfold circleSub
  have h := round_le ((u - v) / S) k
  have e : (u - v) - S * round ((u - v) / S) = S * ((u - v) / S - round ((u - v) / S)) := by
    field_simp
  have e' : u - v - k * S = S * ((u - v) / S - k) := by
    field_simp
  rw [e, e', abs_mul, abs_mul, abs_of_pos hS]
  exact mul_le_mul_of_nonneg_left h hS.le
private lemma coe_int_mul_period_eq_zero (S : ℝ) (k : ℤ) : ((k * S : ℝ) : AddCircle S) = 0 := by apply _root_.YangMills.Construction.Torus.coe_int_mul_period <;> assumption
private lemma torusProj_displacement {S : ℝ} (v w : Fin 4 → ℝ) :
    torusProj S (periodicDisplacement S v w) = torusProj S w - torusProj S v := by
  funext μ
  simp only [torusProj, periodicDisplacement, circleSub, Pi.sub_apply]
  rw [mul_comm S, AddCircle.coe_sub, coe_int_mul_period_eq_zero, sub_zero, AddCircle.coe_sub]
private lemma euclidNorm_nonneg {S : ℝ} (x : Torus4 S) : 0 ≤ torusEuclidNorm x := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
private lemma euclidNorm_proj_le {S : ℝ} (v : Fin 4 → ℝ) : torusEuclidNorm (torusProj S v) ≤ vecNorm v := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
private lemma euclidNorm_proj_sub {S : ℝ} (hS : 0 < S) (v w : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj S w - torusProj S v) = vecNorm (periodicDisplacement S v w) := by
  apply le_antisymm
  · rw [← torusProj_displacement]
    exact euclidNorm_proj_le _
  · refine le_csInf ⟨_, periodicDisplacement S v w, torusProj_displacement v w, rfl⟩ ?_
    rintro _ ⟨l, hl, rfl⟩
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    have hl' : torusProj S l = torusProj S w - torusProj S v := hl
    have h1 : ((l i : ℝ) : AddCircle S) = ((w i - v i : ℝ) : AddCircle S) := by
      have := congrFun hl' i
      simpa [torusProj, AddCircle.coe_sub] using this
    have h2 : ((l i - (w i - v i) : ℝ) : AddCircle S) = 0 := by
      rw [AddCircle.coe_sub, h1, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff S).1 h2
    have hk' : l i = w i - v i - ((-k : ℤ) : ℝ) * S := by
      have : (k : ℝ) * S = l i - (w i - v i) := by simpa using hk
      push_cast
      linarith
    have h3 := abs_circleSub_le_lift hS (w i) (v i) (-k)
    rw [← hk'] at h3
    exact sq_le_sq.2 h3
private lemma abs_le_one_of_uniformNorm {X : Type*} {f : X → ℝ} (h : uniformNorm f = 1) (x : X) : |f x| ≤ 1 := by
  by_cases hb : BddAbove (Set.range fun x => ‖f x‖)
  · have h1 := le_ciSup hb x
    unfold uniformNorm at h
    rw [h] at h1
    simpa using h1
  · exfalso
    unfold uniformNorm at h
    rw [Real.iSup_of_not_bddAbove hb] at h
    norm_num at h
private lemma abs_sub_le_lipConst {S : ℝ} {f : Torus4 S → ℝ} (hl : IsLipschitzFor euclidDistTorus f) (x y : Torus4 S) :
    |f x - f y| ≤ lipConstTorus f * euclidDistTorus x y := by
  have hd : 0 ≤ euclidDistTorus x y := euclidNorm_nonneg _
  obtain ⟨C, hC0, hC⟩ := hl
  rcases hd.eq_or_lt with hd0 | hd0
  · have := hC x y
    rw [← hd0] at this ⊢
    simpa using this
  · have h1 : |f x - f y| / euclidDistTorus x y ≤ lipConstTorus f := by
      unfold lipConstTorus bestLipschitzConstant
      refine le_csInf ⟨C, hC0, hC⟩ ?_
      rintro D ⟨_, hD⟩
      exact div_le_of_le_mul₀ hd ‹_› (hD x y)
    calc _ = |f x - f y| / euclidDistTorus x y * euclidDistTorus x y := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hd
abbrev _root_.YangMills.SharedProofs.p26625 := @abs_sub_le_lipConst
private lemma dist_proj_le_two {S : ℝ} {v w : Fin 4 → ℝ} (h : ∀ μ, |v μ - w μ| ≤ 1) :
    euclidDistTorus (torusProj S v) (torusProj S w) ≤ 2 := by
  have e : torusProj S v - torusProj S w = torusProj S (v - w) := by
    funext μ
    simp [torusProj, AddCircle.coe_sub]
  unfold euclidDistTorus
  rw [e]
  refine (euclidNorm_proj_le _).trans ?_
  refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
  have : ∀ i : Fin 4, (v - w) i ^ 2 ≤ 1 := fun i => by
    have := h i
    have : |(v - w) i| ≤ 1 := this
    exact (sq_le_one_iff_abs_le_one _).2 this
  unfold sqNorm
  calc _ ≤ ∑ _i : Fin 4, (1 : ℝ) := Finset.sum_le_sum fun i _ => this i
    _ = _ := by norm_num
private lemma le_vecNorm_of_separated {S : ℝ} (hS : 0 < S) {p : ℕ} {f : Fin p → Torus4 S → ℝ} {n : ℝ}
    (hap : HasSeparatedSupportsTorus f n) {i j : Fin p} (hij : i ≠ j) {v w : Fin 4 → ℝ}
    (hv : f i (torusProj S v) ≠ 0) (hw : f j (torusProj S w) ≠ 0) : n ≤ vecNorm (periodicDisplacement S v w) := by
  have h1 := hap.2 j i hij.symm
  have h2 : setEuclidDist (tsupport (f j)) (tsupport (f i)) ≤
      ENNReal.ofReal (torusEuclidNorm (torusProj S w - torusProj S v)) :=
    (iInf₂_le (torusProj S w) (subset_tsupport _ hw)).trans (iInf₂_le (torusProj S v) (subset_tsupport _ hv))
  have h3 := h1.trans h2
  rw [ENNReal.ofReal_le_ofReal_iff (euclidNorm_nonneg _), euclidNorm_proj_sub hS] at h3
  exact h3
private lemma vecNorm_le_of_near {S : ℝ} (hS : 0 < S) {f g : Torus4 S → ℝ} {n : ℝ}
    (hnear : ∀ x ∈ tsupport g, ∀ z ∈ tsupport f, euclidDistTorus x z ≤ 10 * n) {v w : Fin 4 → ℝ}
    (hv : f (torusProj S v) ≠ 0) (hw : g (torusProj S w) ≠ 0) : vecNorm (periodicDisplacement S v w) ≤ 10 * n := by
  have := hnear _ (subset_tsupport _ hw) _ (subset_tsupport _ hv)
  unfold euclidDistTorus at this
  rwa [euclidNorm_proj_sub hS] at this
private lemma eq_of_sub_eq_int_mul_period {x y S : ℝ} {k : ℤ} (hS : 0 < S) (h : x - y = k * S) (hxy : |x| + |y| < S) : x = y := by
  have h1 : |(k : ℝ)| * S < S := by
    rw [← abs_of_pos hS, ← abs_mul, abs_of_pos hS, ← h]
    exact (abs_sub _ _).trans_lt hxy
  have h2 : |(k : ℝ)| < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have h3 : k = 0 := by
    have : |k| < 1 := by exact_mod_cast h2
    exact Int.abs_lt_one_iff.1 this
  rw [h3] at h
  simp at h
  linarith
private def barycenterVec {N : ℕ} (p : TorusPlaquette N) : Fin 4 → ℝ := fun i =>
  ((p.1 i).val : ℝ) + (if i = p.2.1 then 1 / 2 else 0) + (if i = p.2.2 then 1 / 2 else 0)
private lemma centreDisplacement_eq_neg {N : ℕ} {S : ℝ} (hSN : S = N) (hS : 8 ≤ S) (p p' : TorusPlaquette N)
    (hsmall : vecNorm (periodicDisplacement S (barycenterVec p') (barycenterVec p)) ≤ S / 8) :
    plaquetteCentreDisplacement p p' = -periodicDisplacement S (barycenterVec p') (barycenterVec p) := by
  have hS0 : 0 < S := by linarith
  funext i
  have hY := (abs_coord_le_vecNorm (periodicDisplacement S (barycenterVec p') (barycenterVec p)) i).trans hsmall
  have hsite : |LinearResponse.torusDisplacement p.1 p'.1 i| ≤ S / 2 := by
    unfold LinearResponse.torusDisplacement
    rw [← hSN]
    exact abs_circleSub_le hS0 _ _
  set e : ℝ := ((if i = p'.2.1 then 1 else 0) + (if i = p'.2.2 then 1 else 0) -
    (if i = p.2.1 then 1 else 0) - (if i = p.2.2 then 1 else 0)) / 2 with he
  have heb : |e| ≤ 1 := by
    rw [he]
    split_ifs <;> norm_num
  have hc : plaquetteCentreDisplacement p p' i = LinearResponse.torusDisplacement p.1 p'.1 i + e := rfl
  rw [hc]
  have hk : ∃ k : ℤ, (LinearResponse.torusDisplacement p.1 p'.1 i + e) - (-periodicDisplacement S (barycenterVec p') (barycenterVec p)) i = k * S := by
    refine ⟨-round ((((p'.1 i).val : ℝ) - ((p.1 i).val : ℝ)) / (N : ℝ)) - round ((barycenterVec p i - barycenterVec p' i) / S), ?_⟩
    have hh : ∀ (c : Prop) [Decidable c], (if c then (1 / 2 : ℝ) else 0) = (if c then 1 else 0) / 2 := by
      intro c _
      split_ifs <;> norm_num
    simp only [LinearResponse.torusDisplacement, periodicDisplacement, circleSub, Pi.neg_apply, he, barycenterVec, hh]
    rw [← hSN]
    generalize round ((((p'.1 i).val : ℝ) - ((p.1 i).val : ℝ)) / S) = k₁
    generalize round (((((p.1 i).val : ℝ) + (if i = p.2.1 then 1 else 0) / 2 + (if i = p.2.2 then 1 else 0) / 2) -
      (((p'.1 i).val : ℝ) + (if i = p'.2.1 then 1 else 0) / 2 + (if i = p'.2.2 then 1 else 0) / 2)) / S) = k₂
    push_cast
    ring
  obtain ⟨k, hk⟩ := hk
  refine eq_of_sub_eq_int_mul_period hS0 hk ?_
  have h1 : |LinearResponse.torusDisplacement p.1 p'.1 i + e| ≤ S / 2 + 1 := (abs_add_le _ _).trans (add_le_add hsite heb)
  have h2 : |(-periodicDisplacement S (barycenterVec p') (barycenterVec p)) i| ≤ S / 8 := by
    rw [Pi.neg_apply, abs_neg]; exact hY
  linarith
private lemma abs_displacement_sub_le_two {S : ℝ} (hS : 8 ≤ S) {u u' b b' : Fin 4 → ℝ} (h : ∀ μ, |u μ - b μ| ≤ 1)
    (h' : ∀ μ, |u' μ - b' μ| ≤ 1) (hu : vecNorm (periodicDisplacement S u u') ≤ S / 8)
    (hb : vecNorm (periodicDisplacement S b b') ≤ S / 8) (μ : Fin 4) :
    |periodicDisplacement S u u' μ - periodicDisplacement S b b' μ| ≤ 2 := by
  have hS0 : 0 < S := by linarith
  have h1 := (abs_coord_le_vecNorm _ μ).trans hu
  have h2 := (abs_coord_le_vecNorm _ μ).trans hb
  set g := (u' μ - b' μ) - (u μ - b μ) with hg
  have hgb : |g| ≤ 2 := by
    calc _ ≤ _ := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (h' μ) (h μ)
      _ = 2 := by norm_num
  have hk : ∃ k : ℤ, (periodicDisplacement S u u' μ - periodicDisplacement S b b' μ) - g = k * S := by
    refine ⟨round ((b' μ - b μ) / S) - round ((u' μ - u μ) / S), ?_⟩
    simp only [periodicDisplacement, circleSub, hg]
    push_cast
    ring
  obtain ⟨k, hk⟩ := hk
  have h3 : |periodicDisplacement S u u' μ - periodicDisplacement S b b' μ| ≤ S / 8 + S / 8 :=
    (abs_sub _ _).trans (add_le_add h1 h2)
  have := eq_of_sub_eq_int_mul_period hS0 hk (by linarith)
  rw [this]
  exact hgb
end PeriodicGeometry
section MatrixTrace
open Matrix
section Walks
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private def pathThrough {k : ℕ} (a : ι) (P : Fin k → ι) (b : ι) : Fin (k + 2) → ι :=
  Fin.snoc (α := fun _ => ι) (Fin.cons (α := fun _ => ι) a P) b
private lemma pathThrough_zero {k : ℕ} (a : ι) (P : Fin k → ι) (b : ι) : pathThrough a P b 0 = a := by
  have : (0 : Fin (k + 2)) = Fin.castSucc (0 : Fin (k + 1)) := rfl
  rw [this, pathThrough, Fin.snoc_castSucc, Fin.cons_zero]
private lemma pathThrough_cons {k : ℕ} (a d : ι) (P : Fin k → ι) (b : ι) :
    pathThrough a (Fin.cons (α := fun _ => ι) d P) b = Fin.cons (α := fun _ => ι) a (pathThrough d P b) := by
  unfold pathThrough
  rw [Fin.cons_snoc_eq_snoc_cons]
private lemma list_prod_entry : ∀ (k : ℕ) (M : Fin (k + 1) → Matrix ι ι ℝ) (a b : ι),
    (List.ofFn M).prod a b =
      ∑ P : Fin k → ι, ∏ i : Fin (k + 1), M i (pathThrough a P b i.castSucc) (pathThrough a P b i.succ) := by
  intro k
  induction k with
  | zero =>
    intro M a b
    have h : pathThrough a (Fin.elim0 : Fin 0 → ι) b 1 = b := by
      have : (1 : Fin 2) = Fin.last 1 := rfl
      rw [this, pathThrough, Fin.snoc_last]
    simp [List.ofFn_succ, Fintype.sum_unique]
    have e : ∀ P : Fin 0 → ι, P = Fin.elim0 := fun P => Subsingleton.elim _ _
    rw [e default, pathThrough_zero, h]
  | succ k ih =>
    intro M a b
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    rw [← (Fin.consEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    change _ = ∏ i : Fin (k + 2), M i (pathThrough a (Fin.cons (α := fun _ => ι) d P) b i.castSucc)
      (pathThrough a (Fin.cons (α := fun _ => ι) d P) b i.succ)
    rw [pathThrough_cons]
    conv_rhs => rw [Fin.prod_univ_succ]
    have h0 : Fin.castSucc (0 : Fin (k + 2)) = 0 := rfl
    rw [h0, Fin.cons_zero, Fin.cons_succ, pathThrough_zero]
    congr 1
private lemma trace_list_prod_eq (k : ℕ) (M : Fin (k + 1) → Matrix ι ι ℝ) :
    Matrix.trace (List.ofFn M).prod =
      ∑ Q : Fin (k + 1) → ι, ∏ j, M j (Q j) (Q (finRotate (k + 1) j)) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  rw [← (Fin.consEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [list_prod_entry]
  refine Finset.sum_congr rfl fun P _ => ?_
  change _ = ∏ j, M j (Fin.cons (α := fun _ => ι) a P j)
    (Fin.cons (α := fun _ => ι) a P (finRotate (k + 1) j))
  refine Finset.prod_congr rfl fun j _ => ?_
  have h1 : pathThrough a P a j.castSucc = Fin.cons (α := fun _ => ι) a P j := by
    rw [pathThrough, Fin.snoc_castSucc]
  have h2 : pathThrough a P a j.succ = Fin.cons (α := fun _ => ι) a P (finRotate (k + 1) j) := by
    induction j using Fin.lastCases with
    | last =>
      rw [finRotate_last, Fin.succ_last, pathThrough, Fin.snoc_last, Fin.cons_zero]
    | cast i =>
      have e : finRotate (k + 1) i.castSucc = i.succ := by
        rw [finRotate_apply]
        exact Fin.coeSucc_eq_succ
      rw [e, Fin.succ_castSucc, pathThrough, Fin.snoc_castSucc]
  rw [h1, h2]
end Walks
end MatrixTrace
section CycleIntegrand
open TestFunctions PeriodicLattice ResponseInTheExpansion TorusFields LinearResponse TorusMetric
private structure TupleBounds (S n vt : ℝ) {p : ℕ} (f : Fin p → Torus4 S → ℝ) : Prop where
  bound : ∀ i x, |f i x| ≤ 1
  lipschitz : ∀ i x y, |f i x - f i y| ≤ 1 / (vt * n) * euclidDistTorus x y
  separated : ∀ i j, i ≠ j → ∀ v w, f i (torusProj S v) ≠ 0 → f j (torusProj S w) ≠ 0 → n ≤ vecNorm (periodicDisplacement S v w)
  close : ∀ i j v w, f i (torusProj S v) ≠ 0 → f j (torusProj S w) ≠ 0 → vecNorm (periodicDisplacement S v w) ≤ 10 * n
  continuous : ∀ i, Continuous fun v : Fin 4 → ℝ => f i (torusProj S v)
private def plaquetteAt {N : ℕ} (x : TorusSite N) (P : OrderedPlane) : TorusPlaquette N := (x, P.1.1, P.1.2)
private lemma plaquetteAt_mem {N : ℕ} [NeZero N] (x : TorusSite N) (P : OrderedPlane) :
    plaquetteAt x P ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)) := by
  simp [plaquettesIn, plaquetteAt, P.2]
variable {S : ℝ} {q : ℕ}
private def supportProduct (f : Fin (q + 1) → Torus4 S → ℝ) (u : Fin (q + 1) → Fin 4 → ℝ) : ℝ :=
  ∏ i, f i (torusProj S (u i))
private def cycleKernelFactor (S : ℝ) (s : Equiv.Perm (Fin (q + 1))) (R : Fin (q + 1) → OrderedPlane) (u : Fin (q + 1) → Fin 4 → ℝ)
    (j : Fin (q + 1)) : ℝ :=
  planeKernelMatrix (periodicDisplacement S (u (s (finRotate (q + 1) j))) (u (s j))) (R (s j)) (R (s (finRotate (q + 1) j)))
private def cycleIntegrand (f : Fin (q + 1) → Torus4 S → ℝ) (s : Equiv.Perm (Fin (q + 1))) (R : Fin (q + 1) → OrderedPlane)
    (u : Fin (q + 1) → Fin 4 → ℝ) : ℝ :=
  supportProduct f u * ∏ j, cycleKernelFactor S s R u j
private def NonvanishingAt (f : Fin (q + 1) → Torus4 S → ℝ) (u : Fin (q + 1) → Fin 4 → ℝ) : Prop :=
  ∀ i, f i (torusProj S (u i)) ≠ 0
private lemma finRotate_ne_self (hq : 1 ≤ q) (j : Fin (q + 1)) : finRotate (q + 1) j ≠ j := by
  intro h
  rw [finRotate_apply] at h
  have h1 : (1 : Fin (q + 1)) = 0 := by simpa using h
  rw [Fin.one_eq_zero_iff] at h1
  omega
abbrev _root_.YangMills.SharedProofs.p60146 := @finRotate_ne_self
private lemma supportProduct_eq_zero {f : Fin (q + 1) → Torus4 S → ℝ} {u : Fin (q + 1) → Fin 4 → ℝ} (h : ¬ NonvanishingAt f u) :
    supportProduct f u = 0 := by
  unfold NonvanishingAt at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi
private lemma abs_supportProduct_le {n vt : ℝ} {f : Fin (q + 1) → Torus4 S → ℝ} (hT : TupleBounds S n vt f)
    (u : Fin (q + 1) → Fin 4 → ℝ) : |supportProduct f u| ≤ 1 := by
  unfold supportProduct
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hT.bound i _)
private lemma displacement_in_range {n vt : ℝ} {f : Fin (q + 1) → Torus4 S → ℝ} (hT : TupleBounds S n vt f) (hq : 1 ≤ q)
    {u : Fin (q + 1) → Fin 4 → ℝ} (hg : NonvanishingAt f u) (s : Equiv.Perm (Fin (q + 1))) (j : Fin (q + 1)) :
    n ≤ vecNorm (periodicDisplacement S (u (s (finRotate (q + 1) j))) (u (s j))) ∧
      vecNorm (periodicDisplacement S (u (s (finRotate (q + 1) j))) (u (s j))) ≤ 10 * n :=
  ⟨hT.separated _ _ (s.injective.ne (finRotate_ne_self hq j)) _ _ (hg _) (hg _), hT.close _ _ _ _ (hg _) (hg _)⟩
private lemma sq_le_sqNorm_of_le {n : ℝ} (hn : 0 ≤ n) {z : Fin 4 → ℝ} (h : n ≤ vecNorm z) : n ^ 2 ≤ sqNorm z := by
  rw [← vecNorm_sq z]
  exact pow_le_pow_left₀ hn h 2
private lemma abs_cycleKernelFactor_le {n vt : ℝ} (hn : 0 < n) {f : Fin (q + 1) → Torus4 S → ℝ} (hT : TupleBounds S n vt f) (hq : 1 ≤ q)
    {u : Fin (q + 1) → Fin 4 → ℝ} (hg : NonvanishingAt f u) (s : Equiv.Perm (Fin (q + 1)))
    (R : Fin (q + 1) → OrderedPlane) (j : Fin (q + 1)) : |cycleKernelFactor S s R u j| ≤ 2 / n ^ 4 :=
  abs_kernel_le_of_sq_le hn (sq_le_sqNorm_of_le hn.le (displacement_in_range hT hq hg s j).1) _ _ _ _
private lemma abs_kernelProduct_le {n vt : ℝ} (hn : 0 < n) {f : Fin (q + 1) → Torus4 S → ℝ} (hT : TupleBounds S n vt f) (hq : 1 ≤ q)
    {u : Fin (q + 1) → Fin 4 → ℝ} (hg : NonvanishingAt f u) (s : Equiv.Perm (Fin (q + 1)))
    (R : Fin (q + 1) → OrderedPlane) : |∏ j, cycleKernelFactor S s R u j| ≤ (2 / n ^ 4) ^ (q + 1) := by
  rw [Finset.abs_prod]
  calc _ ≤ ∏ _j : Fin (q + 1), (2 / n ^ 4) :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => abs_cycleKernelFactor_le hn hT hq hg s R j)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
private lemma abs_cycleIntegrand_le {n vt : ℝ} (hn : 0 < n) {f : Fin (q + 1) → Torus4 S → ℝ} (hT : TupleBounds S n vt f) (hq : 1 ≤ q)
    (s : Equiv.Perm (Fin (q + 1))) (R : Fin (q + 1) → OrderedPlane) (u : Fin (q + 1) → Fin 4 → ℝ) :
    |cycleIntegrand f s R u| ≤ (2 / n ^ 4) ^ (q + 1) := by
  unfold cycleIntegrand
  by_cases hg : NonvanishingAt f u
  · rw [abs_mul]
    calc _ ≤ 1 * (2 / n ^ 4) ^ (q + 1) :=
          mul_le_mul (abs_supportProduct_le hT u) (abs_kernelProduct_le hn hT hq hg s R) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [supportProduct_eq_zero hg]
    simp only [zero_mul, abs_zero]
    positivity
private lemma supportProduct_cell_gap {n vt : ℝ} (hn : 0 < n) (hvt : 0 < vt) {f : Fin (q + 1) → Torus4 S → ℝ}
    (hT : TupleBounds S n vt f) {u b : Fin (q + 1) → Fin 4 → ℝ} (h : ∀ i μ, |u i μ - b i μ| ≤ 1) :
    |supportProduct f u - supportProduct f b| ≤ (q + 1) * (2 / (vt * n)) := by
  have h1 := abs_prod_sub_prod_mul_le (Finset.univ : Finset (Fin (q + 1))) (fun i => f i (torusProj S (u i)))
    (fun i => f i (torusProj S (b i))) (M := 1) (η := 2 / (vt * n)) one_pos (by positivity)
    (fun i _ => hT.bound i _) (fun i _ => hT.bound i _) (fun i _ => by
      calc _ ≤ 1 / (vt * n) * euclidDistTorus (torusProj S (u i)) (torusProj S (b i)) := hT.lipschitz i _ _
        _ ≤ 1 / (vt * n) * 2 := mul_le_mul_of_nonneg_left (dist_proj_le_two (h i)) (by positivity)
        _ = _ := by ring)
  simpa [supportProduct] using h1
private lemma kernelProduct_cell_gap {n vt : ℝ} (hS : 8 ≤ S) (hn : 0 < n) (h10 : 10 * n ≤ S / 8)
    {f : Fin (q + 1) → Torus4 S → ℝ} (hT : TupleBounds S n vt f) (hq : 1 ≤ q)
    {u b : Fin (q + 1) → Fin 4 → ℝ} (hgu : NonvanishingAt f u) (hgb : NonvanishingAt f b) (h : ∀ i μ, |u i μ - b i μ| ≤ 1)
    (s : Equiv.Perm (Fin (q + 1))) (R : Fin (q + 1) → OrderedPlane) :
    |∏ j, cycleKernelFactor S s R u j - ∏ j, cycleKernelFactor S s R b j| ≤ (q + 1) * (2 / n ^ 4) ^ q * (120 / n ^ 5) := by
  have hM : 0 < 2 / n ^ 4 := by positivity
  have h1 := abs_prod_sub_prod_mul_le (Finset.univ : Finset (Fin (q + 1))) (cycleKernelFactor S s R u) (cycleKernelFactor S s R b)
    (M := 2 / n ^ 4) (η := 120 / n ^ 5) hM (by positivity)
    (fun j _ => abs_cycleKernelFactor_le hn hT hq hgu s R j) (fun j _ => abs_cycleKernelFactor_le hn hT hq hgb s R j) (fun j _ => by
      have ru := displacement_in_range hT hq hgu s j
      have rb := displacement_in_range hT hq hgb s j
      have := kernel_lipschitz (δ := 2) hn (sq_le_sqNorm_of_le hn.le ru.1) (sq_le_sqNorm_of_le hn.le rb.1)
        (abs_displacement_sub_le_two hS (h _) (h _) (ru.2.trans h10) (rb.2.trans h10))
        (R (s j)).1.1 (R (s j)).1.2 (R (s (finRotate (q + 1) j))).1.1 (R (s (finRotate (q + 1) j))).1.2
      calc _ ≤ 60 * 2 / n ^ 5 := this
        _ = _ := by ring)
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  refine le_of_mul_le_mul_right ?_ hM
  calc _ ≤ _ := h1
    _ = _ := by push_cast; ring
private def unitCellGap (q : ℕ) (n vt : ℝ) : ℝ :=
  (q + 1) * (2 / (vt * n)) * (2 / n ^ 4) ^ (q + 1) + (q + 1) * (2 / n ^ 4) ^ q * (120 / n ^ 5)
private lemma cycleIntegrand_cell_gap {n vt : ℝ} (hS : 8 ≤ S) (hn : 0 < n) (hvt : 0 < vt) (h10 : 10 * n ≤ S / 8)
    {f : Fin (q + 1) → Torus4 S → ℝ} (hT : TupleBounds S n vt f) (hq : 1 ≤ q)
    {u b : Fin (q + 1) → Fin 4 → ℝ} (h : ∀ i μ, |u i μ - b i μ| ≤ 1)
    (s : Equiv.Perm (Fin (q + 1))) (R : Fin (q + 1) → OrderedPlane) :
    |cycleIntegrand f s R u - cycleIntegrand f s R b| ≤ unitCellGap q n vt := by
  have hF := supportProduct_cell_gap hn hvt hT h
  have p1 : 0 ≤ ((q : ℝ) + 1) * (2 / (vt * n)) * (2 / n ^ 4) ^ (q + 1) := by positivity
  have p2 : 0 ≤ ((q : ℝ) + 1) * (2 / n ^ 4) ^ q * (120 / n ^ 5) := by positivity
  unfold unitCellGap cycleIntegrand
  by_cases hgu : NonvanishingAt f u
  · by_cases hgb : NonvanishingAt f b
    · have hK := kernelProduct_cell_gap hS hn h10 hT hq hgu hgb h s R
      rw [show supportProduct f u * ∏ j, cycleKernelFactor S s R u j - supportProduct f b * ∏ j, cycleKernelFactor S s R b j =
        (supportProduct f u - supportProduct f b) * ∏ j, cycleKernelFactor S s R u j +
          supportProduct f b * (∏ j, cycleKernelFactor S s R u j - ∏ j, cycleKernelFactor S s R b j) by ring]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul hF (abs_kernelProduct_le hn hT hq hgu s R) (abs_nonneg _) (by positivity)
      · rw [abs_mul]
        calc _ ≤ 1 * ((q + 1) * (2 / n ^ 4) ^ q * (120 / n ^ 5)) :=
              mul_le_mul (abs_supportProduct_le hT b) hK (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
    · have e : supportProduct f b = 0 := supportProduct_eq_zero hgb
      rw [show supportProduct f u * ∏ j, cycleKernelFactor S s R u j - supportProduct f b * ∏ j, cycleKernelFactor S s R b j =
        (supportProduct f u - supportProduct f b) * ∏ j, cycleKernelFactor S s R u j by rw [e]; ring]
      rw [abs_mul]
      have := mul_le_mul hF (abs_kernelProduct_le hn hT hq hgu s R) (abs_nonneg _) (by positivity)
      linarith
  · have e : supportProduct f u = 0 := supportProduct_eq_zero hgu
    by_cases hgb : NonvanishingAt f b
    · rw [show supportProduct f u * ∏ j, cycleKernelFactor S s R u j - supportProduct f b * ∏ j, cycleKernelFactor S s R b j =
        (supportProduct f u - supportProduct f b) * ∏ j, cycleKernelFactor S s R b j by rw [e]; ring]
      rw [abs_mul]
      have := mul_le_mul hF (abs_kernelProduct_le hn hT hq hgb s R) (abs_nonneg _) (by positivity)
      linarith
    · have e' : supportProduct f b = 0 := supportProduct_eq_zero hgb
      rw [e, e']
      simp only [zero_mul, sub_zero, abs_zero]
      linarith
private lemma rpow_neg_five_halves_le {a n : ℝ} (hn : 0 < n) (h : n ^ 2 ≤ a) : a ^ (-(5 / 2 : ℝ)) ≤ 1 / n ^ 5 := by
  have h1 : a ^ (-(5 / 2 : ℝ)) ≤ (n ^ 2) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h (by norm_num)
  have h2 : (n ^ 2) ^ (-(5 / 2 : ℝ)) = 1 / n ^ 5 := by
    rw [← Real.rpow_natCast n 2, ← Real.rpow_mul hn.le]
    rw [show ((2 : ℕ) : ℝ) * (-(5 / 2 : ℝ)) = -((5 : ℕ) : ℝ) by norm_num]
    rw [Real.rpow_neg hn.le, Real.rpow_natCast, one_div]
  rw [← h2]
  exact h1
variable {N : ℕ} [NeZero N]
private def barycenters (x : Fin (q + 1) → TorusSite N) (R : Fin (q + 1) → OrderedPlane) : Fin (q + 1) → Fin 4 → ℝ :=
  fun i => barycenterVec (plaquetteAt (x i) (R i))
private def latticeTerm (f : Fin (q + 1) → Torus4 S → ℝ) (Tt : TorusPlaquette N → TorusPlaquette N → ℝ) (s : Equiv.Perm (Fin (q + 1)))
    (R : Fin (q + 1) → OrderedPlane) (x : Fin (q + 1) → TorusSite N) : ℝ :=
  supportProduct f (barycenters x R) * ∏ j, Tt (plaquetteAt (x (s j)) (R (s j)))
    (plaquetteAt (x (s (finRotate (q + 1) j))) (R (s (finRotate (q + 1) j))))
private def IsNearMaxwellKernel (S A ε : ℝ) (Tt : TorusPlaquette N → TorusPlaquette N → ℝ) : Prop :=
  ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)), ∀ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)),
    1 ≤ sqNorm (plaquetteCentreDisplacement p p') →
    sqNorm (plaquetteCentreDisplacement p p') ≤ (S / 8) ^ 2 →
    |Tt p p' - _root_.YangMills.Construction.LinearResponse.continuumCurvatureKernel (plaquetteCentreDisplacement p p') p.2.1 p.2.2 p'.2.1 p'.2.2| ≤
      A * (sqNorm (plaquetteCentreDisplacement p p') ^ (-(5 / 2 : ℝ)) + ε)
private lemma latticeTerm_sub_le {n vt A ε : ℝ} (hSN : S = N) (hS : 8 ≤ S) (hn : 1 ≤ n) (h10 : 10 * n ≤ S / 8) (hA : 0 ≤ A)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1 / n ^ 4) {f : Fin (q + 1) → Torus4 S → ℝ} (hT : TupleBounds S n vt f) (hq : 1 ≤ q)
    {Tt : TorusPlaquette N → TorusPlaquette N → ℝ} (hTt : IsNearMaxwellKernel S A ε Tt) (s : Equiv.Perm (Fin (q + 1)))
    (R : Fin (q + 1) → OrderedPlane) (x : Fin (q + 1) → TorusSite N) :
    |latticeTerm f Tt s R x - cycleIntegrand f s R (barycenters x R)| ≤ (q + 1) * ((2 + 2 * A) / n ^ 4) ^ q * (A * (1 / n ^ 5 + ε)) := by
  have hn0 : 0 < n := by linarith
  have hη : 0 ≤ A * (1 / n ^ 5 + ε) := by positivity
  have hM : 0 < (2 + 2 * A) / n ^ 4 := by positivity
  unfold latticeTerm cycleIntegrand
  by_cases hg : NonvanishingAt f (barycenters x R)
  · rw [← mul_sub, abs_mul]
    refine (mul_le_of_le_one_left (abs_nonneg _) (abs_supportProduct_le hT _)).trans ?_
    have hstep : ∀ j, |Tt (plaquetteAt (x (s j)) (R (s j))) (plaquetteAt (x (s (finRotate (q + 1) j))) (R (s (finRotate (q + 1) j))))
        - cycleKernelFactor S s R (barycenters x R) j| ≤ A * (1 / n ^ 5 + ε) := by
      intro j
      have hr := displacement_in_range hT hq hg s j
      set p := plaquetteAt (x (s j)) (R (s j)) with hp
      set p' := plaquetteAt (x (s (finRotate (q + 1) j))) (R (s (finRotate (q + 1) j))) with hp'
      have hz : plaquetteCentreDisplacement p p' = -periodicDisplacement S (barycenterVec p') (barycenterVec p) :=
        centreDisplacement_eq_neg hSN hS p p' (hr.2.trans h10)
      have hsq : sqNorm (plaquetteCentreDisplacement p p') =
          sqNorm (periodicDisplacement S (barycenterVec p') (barycenterVec p)) := by
        rw [hz]; simp [sqNorm]
      have hlow : n ^ 2 ≤ sqNorm (periodicDisplacement S (barycenterVec p') (barycenterVec p)) :=
        sq_le_sqNorm_of_le hn0.le hr.1
      have hup : sqNorm (periodicDisplacement S (barycenterVec p') (barycenterVec p)) ≤ (S / 8) ^ 2 := by
        rw [← vecNorm_sq]
        exact pow_le_pow_left₀ (vecNorm_nonneg _) (hr.2.trans h10) 2
      have h1 := hTt p (plaquetteAt_mem _ _) p' (plaquetteAt_mem _ _)
        (by rw [hsq]; nlinarith) (by rw [hsq]; exact hup)
      rw [hsq, hz, kernel_neg] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hA)
      have := rpow_neg_five_halves_le hn0 hlow
      linarith
    have hKabs := fun j => abs_cycleKernelFactor_le hn0 hT hq hg s R j
    have hle : ∀ j, |cycleKernelFactor S s R (barycenters x R) j| ≤ (2 + 2 * A) / n ^ 4 := fun j =>
      (hKabs j).trans (by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith)
    have hηle : A * (1 / n ^ 5 + ε) ≤ 2 * A / n ^ 4 := by
      have h5 : 1 / n ^ 5 ≤ 1 / n ^ 4 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hn (by norm_num))
      calc _ ≤ A * (1 / n ^ 4 + 1 / n ^ 4) :=
            mul_le_mul_of_nonneg_left (by linarith) hA
        _ = _ := by ring
    have hTabs : ∀ j, |Tt (plaquetteAt (x (s j)) (R (s j))) (plaquetteAt (x (s (finRotate (q + 1) j))) (R (s (finRotate (q + 1) j))))|
        ≤ (2 + 2 * A) / n ^ 4 := by
      intro j
      have h1 := abs_sub_abs_le_abs_sub (Tt (plaquetteAt (x (s j)) (R (s j))) (plaquetteAt (x (s (finRotate (q + 1) j))) (R (s (finRotate (q + 1) j)))))
        (cycleKernelFactor S s R (barycenters x R) j)
      have h2 := hstep j
      have h3 := hKabs j
      have e : (2 + 2 * A) / n ^ 4 = 2 / n ^ 4 + 2 * A / n ^ 4 := by ring
      rw [e]
      linarith
    have h1 := abs_prod_sub_prod_mul_le (Finset.univ : Finset (Fin (q + 1)))
      (fun j => Tt (plaquetteAt (x (s j)) (R (s j))) (plaquetteAt (x (s (finRotate (q + 1) j))) (R (s (finRotate (q + 1) j)))))
      (cycleKernelFactor S s R (barycenters x R)) hM hη (fun j _ => hTabs j) (fun j _ => hle j) (fun j _ => hstep j)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    refine le_of_mul_le_mul_right ?_ hM
    calc _ ≤ _ := h1
      _ = _ := by push_cast; ring
  · rw [supportProduct_eq_zero hg]
    simp only [zero_mul, sub_zero, abs_zero]
    positivity
end CycleIntegrand
section CellDecomposition
open TestFunctions PeriodicLattice ResponseInTheExpansion TorusFields LinearResponse TorusMetric MeasureTheory
variable {N : ℕ} [NeZero N] {S : ℝ} {q : ℕ}
private def unitCell (x : Fin (q + 1) → TorusSite N) : Set (Fin (q + 1) → Fin 4 → ℝ) :=
  Set.pi Set.univ fun i => Set.pi Set.univ fun μ => Set.Ico (((x i μ).val : ℝ)) (((x i μ).val : ℝ) + 1)
private def periodBox (S : ℝ) (q : ℕ) : Set (Fin (q + 1) → Fin 4 → ℝ) :=
  Set.pi Set.univ (fun _ : Fin (q + 1) => Set.pi Set.univ fun _ : Fin 4 => Set.Ico (0 : ℝ) S)
private lemma unitCell_measurable (x : Fin (q + 1) → TorusSite N) : MeasurableSet (unitCell x) :=
  MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Ico
private lemma unitCell_volume (x : Fin (q + 1) → TorusSite N) : volume (unitCell x) = 1 := by
  unfold unitCell
  rw [volume_pi_pi]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [volume_pi_pi]
  refine Finset.prod_eq_one fun μ _ => ?_
  simp [Real.volume_Ico]
private lemma barycenters_mem_closedCell (x : Fin (q + 1) → TorusSite N) (R : Fin (q + 1) → OrderedPlane) (i : Fin (q + 1)) (μ : Fin 4) :
    ((x i μ).val : ℝ) ≤ barycenters x R i μ ∧ barycenters x R i μ ≤ ((x i μ).val : ℝ) + 1 := by
  have hh : ∀ (c : Prop) [Decidable c], (0 : ℝ) ≤ (if c then (1 / 2 : ℝ) else 0) ∧ (if c then (1 / 2 : ℝ) else 0) ≤ 1 / 2 := by
    intro c _
    split_ifs <;> norm_num
  simp only [barycenters, barycenterVec, plaquetteAt]
  have h1 := hh (μ = (R i).1.1)
  have h2 := hh (μ = (R i).1.2)
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
private lemma abs_sub_barycenters_le {x : Fin (q + 1) → TorusSite N} {u : Fin (q + 1) → Fin 4 → ℝ} (hu : u ∈ unitCell x)
    (R : Fin (q + 1) → OrderedPlane) (i : Fin (q + 1)) (μ : Fin 4) : |u i μ - barycenters x R i μ| ≤ 1 := by
  obtain ⟨h1, h2⟩ := hu i (Set.mem_univ i) μ (Set.mem_univ μ)
  obtain ⟨h3, h4⟩ := barycenters_mem_closedCell x R i μ
  rw [abs_le]
  constructor <;> linarith
private lemma periodBox_eq_iUnion (hSN : S = N) :
    periodBox S q = ⋃ x ∈ (Finset.univ : Finset (Fin (q + 1) → TorusSite N)), unitCell x := by
  ext u
  simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
  constructor
  · intro hu
    refine ⟨fun i μ => ((⌊u i μ⌋₊ : ℕ) : ZMod N), fun i _ μ _ => ?_⟩
    obtain ⟨h1, h2⟩ := hu i (Set.mem_univ i) μ (Set.mem_univ μ)
    have hlt : ⌊u i μ⌋₊ < N := by
      rw [Nat.floor_lt h1, ← hSN]
      exact h2
    have hv : (((⌊u i μ⌋₊ : ℕ) : ZMod N)).val = ⌊u i μ⌋₊ := ZMod.val_cast_of_lt hlt
    show u i μ ∈ Set.Ico ((((⌊u i μ⌋₊ : ℕ) : ZMod N).val : ℝ)) ((((⌊u i μ⌋₊ : ℕ) : ZMod N).val : ℝ) + 1)
    rw [hv]
    exact ⟨Nat.floor_le h1, Nat.lt_floor_add_one _⟩
  · rintro ⟨x, hx⟩ i _ μ _
    obtain ⟨h1, h2⟩ := hx i (Set.mem_univ i) μ (Set.mem_univ μ)
    refine ⟨le_trans (Nat.cast_nonneg _) h1, lt_of_lt_of_le h2 ?_⟩
    rw [hSN]
    exact_mod_cast ZMod.val_lt (x i μ)
private lemma unitCell_disjoint {x y : Fin (q + 1) → TorusSite N} (hxy : x ≠ y) : Disjoint (unitCell x) (unitCell y) := by
  rw [Set.disjoint_left]
  intro u hx hy
  apply hxy
  funext i μ
  obtain ⟨h1, h2⟩ := hx i (Set.mem_univ i) μ (Set.mem_univ μ)
  obtain ⟨h3, h4⟩ := hy i (Set.mem_univ i) μ (Set.mem_univ μ)
  apply ZMod.val_injective
  have e1 : ((x i μ).val : ℝ) < ((y i μ).val : ℝ) + 1 := lt_of_le_of_lt h1 h4
  have e2 : ((y i μ).val : ℝ) < ((x i μ).val : ℝ) + 1 := lt_of_le_of_lt h3 h2
  have e1' : (x i μ).val < (y i μ).val + 1 := by exact_mod_cast e1
  have e2' : (y i μ).val < (x i μ).val + 1 := by exact_mod_cast e2
  omega
private lemma measurable_round_real : Measurable fun t : ℝ => ((round t : ℤ) : ℝ) := by apply _root_.YangMills.SharedProofs.p15817 <;> assumption
private lemma measurable_kernel (μ ν ρ τ : Fin 4) :
    Measurable fun z : Fin 4 → ℝ => _root_.YangMills.Construction.LinearResponse.continuumCurvatureKernel z μ ν ρ τ := by
  unfold _root_.YangMills.Construction.LinearResponse.continuumCurvatureKernel hyperplaneReflection sqNorm
  fun_prop
abbrev _root_.YangMills.SharedProofs.p18031 := @measurable_kernel
private lemma measurable_periodicDisplacement (a b : Fin (q + 1)) :
    Measurable fun u : Fin (q + 1) → Fin 4 → ℝ => periodicDisplacement S (u a) (u b) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [periodicDisplacement, circleSub]
  have h : Measurable fun u : Fin (q + 1) → Fin 4 → ℝ => u b i - u a i := by fun_prop
  exact h.sub (measurable_const.mul (measurable_round_real.comp (h.div_const _)))
private lemma cycleIntegrand_measurable {n vt : ℝ} {f : Fin (q + 1) → Torus4 S → ℝ} (hT : TupleBounds S n vt f)
    (s : Equiv.Perm (Fin (q + 1))) (R : Fin (q + 1) → OrderedPlane) : Measurable (cycleIntegrand f s R) := by
  unfold cycleIntegrand supportProduct
  refine Measurable.mul ?_ ?_
  · exact Finset.measurable_fun_prod _ fun i _ => (hT.continuous i).measurable.comp (measurable_pi_apply i)
  · refine Finset.measurable_fun_prod _ fun j _ => ?_
    exact (measurable_kernel _ _ _ _).comp (measurable_periodicDisplacement _ _)
private lemma cycleIntegrand_integrableOn {n vt : ℝ} (hn : 0 < n) {f : Fin (q + 1) → Torus4 S → ℝ} (hT : TupleBounds S n vt f)
    (hq : 1 ≤ q) (s : Equiv.Perm (Fin (q + 1))) (R : Fin (q + 1) → OrderedPlane)
    (x : Fin (q + 1) → TorusSite N) : IntegrableOn (cycleIntegrand f s R) (unitCell x) :=
  Measure.integrableOn_of_bounded (by rw [unitCell_volume]; simp) (cycleIntegrand_measurable hT s R).aestronglyMeasurable
    (M := (2 / n ^ 4) ^ (q + 1)) (Filter.Eventually.of_forall fun u => abs_cycleIntegrand_le hn hT hq s R u)
private def siteTermGap (q : ℕ) (n vt A ε : ℝ) : ℝ :=
  (q + 1) * ((2 + 2 * A) / n ^ 4) ^ q * (A * (1 / n ^ 5 + ε)) + unitCellGap q n vt
private lemma latticeTerm_sub_integral_le {n vt A ε : ℝ} (hSN : S = N) (hS : 8 ≤ S) (hn : 1 ≤ n) (hvt : 0 < vt) (h10 : 10 * n ≤ S / 8)
    (hA : 0 ≤ A) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / n ^ 4) {f : Fin (q + 1) → Torus4 S → ℝ} (hT : TupleBounds S n vt f)
    (hq : 1 ≤ q) {Tt : TorusPlaquette N → TorusPlaquette N → ℝ} (hTt : IsNearMaxwellKernel S A ε Tt) (s : Equiv.Perm (Fin (q + 1)))
    (R : Fin (q + 1) → OrderedPlane) (x : Fin (q + 1) → TorusSite N) :
    |latticeTerm f Tt s R x - ∫ u in unitCell x, cycleIntegrand f s R u| ≤ siteTermGap q n vt A ε := by
  have hn0 : 0 < n := by linarith
  have hint := cycleIntegrand_integrableOn hn0 hT hq s R x
  have hvol : volume.real (unitCell x) = 1 := by simp [Measure.real, unitCell_volume]
  have hfin : volume (unitCell x) < ⊤ := by rw [unitCell_volume]; simp
  have hconst : IntegrableOn (fun _ : Fin (q + 1) → Fin 4 → ℝ => cycleIntegrand f s R (barycenters x R)) (unitCell x) :=
    integrableOn_const hfin.ne
  have e : ∫ u in unitCell x, cycleIntegrand f s R u =
      cycleIntegrand f s R (barycenters x R) + ∫ u in unitCell x, (cycleIntegrand f s R u - cycleIntegrand f s R (barycenters x R)) := by
    rw [integral_sub hint hconst, setIntegral_const, hvol]
    simp
  have h2 : |∫ u in unitCell x, (cycleIntegrand f s R u - cycleIntegrand f s R (barycenters x R))| ≤ unitCellGap q n vt := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := unitCell x)
      (f := fun u => cycleIntegrand f s R u - cycleIntegrand f s R (barycenters x R)) (C := unitCellGap q n vt) hfin
      (fun u hu => cycleIntegrand_cell_gap hS hn0 hvt h10 hT hq (fun i μ => abs_sub_barycenters_le hu R i μ) s R)
    rw [hvol, mul_one] at this
    exact this
  have h1 := latticeTerm_sub_le hSN hS hn h10 hA hε hε' hT hq hTt s R x
  rw [e, show latticeTerm f Tt s R x - (cycleIntegrand f s R (barycenters x R) + ∫ u in unitCell x, (cycleIntegrand f s R u - cycleIntegrand f s R (barycenters x R))) =
    (latticeTerm f Tt s R x - cycleIntegrand f s R (barycenters x R)) - ∫ u in unitCell x, (cycleIntegrand f s R u - cycleIntegrand f s R (barycenters x R)) by ring]
  exact (abs_sub _ _).trans (add_le_add h1 h2)
open Classical in
private def supportSites (f : Torus4 S → ℝ) : Finset (TorusSite N) :=
  Finset.univ.filter fun a => ∃ v : Fin 4 → ℝ,
    (∀ μ, ((a μ).val : ℝ) ≤ v μ ∧ v μ ≤ ((a μ).val : ℝ) + 1) ∧ f (torusProj S v) ≠ 0
private lemma latticeTerm_sub_integral_eq_zero_off {f : Fin (q + 1) → Torus4 S → ℝ} {Tt : TorusPlaquette N → TorusPlaquette N → ℝ}
    (s : Equiv.Perm (Fin (q + 1))) (R : Fin (q + 1) → OrderedPlane) {x : Fin (q + 1) → TorusSite N}
    (hx : x ∉ Fintype.piFinset fun i => supportSites (N := N) (f i)) :
    latticeTerm f Tt s R x - ∫ u in unitCell x, cycleIntegrand f s R u = 0 := by
  rw [Fintype.mem_piFinset] at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  have hoff : ∀ v : Fin 4 → ℝ, (∀ μ, ((x i μ).val : ℝ) ≤ v μ ∧ v μ ≤ ((x i μ).val : ℝ) + 1) →
      f i (torusProj S v) = 0 := by
    intro v hv
    by_contra hc
    apply hi
    simp only [supportSites, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hv, hc⟩
  have hF : ∀ u : Fin (q + 1) → Fin 4 → ℝ, (∀ μ, ((x i μ).val : ℝ) ≤ u i μ ∧ u i μ ≤ ((x i μ).val : ℝ) + 1) →
      supportProduct f u = 0 := fun u hu => Finset.prod_eq_zero (Finset.mem_univ i) (hoff _ hu)
  have h1 : latticeTerm f Tt s R x = 0 := by
    unfold latticeTerm
    rw [hF _ fun μ => barycenters_mem_closedCell x R i μ, zero_mul]
  have h2 : ∫ u in unitCell x, cycleIntegrand f s R u = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    unfold cycleIntegrand
    rw [hF u fun μ => ?_, zero_mul]
    obtain ⟨e1, e2⟩ := hu i (Set.mem_univ i) μ (Set.mem_univ μ)
    exact ⟨e1, e2.le⟩
  rw [h1, h2, sub_zero]
private lemma supportSites_card_le {n vt : ℝ} (hSN : S = N) (hS : 0 < S) (hn : 1 ≤ n) {f : Fin (q + 1) → Torus4 S → ℝ}
    (hT : TupleBounds S n vt f) (i : Fin (q + 1)) : ((supportSites (N := N) (f i)).card : ℝ) ≤ (25 * n) ^ 4 := by
  classical
  rcases (supportSites (N := N) (f i)).eq_empty_or_nonempty with he | ⟨a₀, ha₀⟩
  · rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  simp only [supportSites, Finset.mem_filter, Finset.mem_univ, true_and] at ha₀
  obtain ⟨v₀, hv₀, hf₀⟩ := ha₀
  set B : ℤ := ⌊12 * n⌋ with hB
  have hB0 : 0 ≤ B := Int.floor_nonneg.2 (by linarith)
  have hBle : (B : ℝ) ≤ 12 * n := Int.floor_le _
  set T : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-B) B with hTdef
  have hsub : supportSites (N := N) (f i) ⊆ T.image fun w => a₀ + siteOfInt w := by
    intro a ha
    simp only [supportSites, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨v, hv, hf⟩ := ha
    have hr := hT.close i i v₀ v hf₀ hf
    refine Finset.mem_image.2 ⟨fun μ => ((a μ).val : ℤ) - ((a₀ μ).val : ℤ) -
      (N : ℤ) * round ((v μ - v₀ μ) / S), ?_, ?_⟩
    · refine Fintype.mem_piFinset.2 fun μ => ?_
      have hz := (abs_coord_le_vecNorm _ μ).trans hr
      have hzv : periodicDisplacement S v₀ v μ = v μ - v₀ μ - S * round ((v μ - v₀ μ) / S) := rfl
      obtain ⟨h1, h2⟩ := hv μ
      obtain ⟨h3, h4⟩ := hv₀ μ
      have hw : (((((a μ).val : ℤ) - ((a₀ μ).val : ℤ) - (N : ℤ) * round ((v μ - v₀ μ) / S) : ℤ)) : ℝ) =
          periodicDisplacement S v₀ v μ + (((a μ).val : ℝ) - v μ) - (((a₀ μ).val : ℝ) - v₀ μ) := by
        rw [hzv, hSN]
        push_cast
        ring
      have habs := abs_le.1 hz
      rw [Finset.mem_Icc]
      constructor
      · have h7 : (-(B + 1) : ℝ) < (((((a μ).val : ℤ) - ((a₀ μ).val : ℤ) - (N : ℤ) * round ((v μ - v₀ μ) / S) : ℤ)) : ℝ) := by
          have h5 : (12 * n : ℝ) < B + 1 := Int.lt_floor_add_one _
          rw [hw]
          linarith [habs.1]
        have h6 : -(B + 1) < (((a μ).val : ℤ) - ((a₀ μ).val : ℤ) - (N : ℤ) * round ((v μ - v₀ μ) / S)) := by
          exact_mod_cast h7
        omega
      · apply Int.le_floor.2
        rw [hw]
        linarith [habs.2]
    · funext μ
      simp only [Pi.add_apply, siteOfInt]
      push_cast
      simp
  have hcard : (T.card : ℝ) ≤ (25 * n) ^ 4 := by
    have e : T.card = (2 * B + 1).toNat ^ 4 := by
      rw [hTdef, Fintype.card_piFinset]
      simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 2
      ring
    have e2 : (((2 * B + 1).toNat : ℕ) : ℝ) = 2 * (B : ℝ) + 1 := by
      have : (((2 * B + 1).toNat : ℕ) : ℤ) = 2 * B + 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [e]
    push_cast
    rw [e2]
    refine pow_le_pow_left₀ (by have : (0 : ℝ) ≤ B := by exact_mod_cast hB0
                                linarith) ?_ 4
    linarith
  calc ((supportSites (N := N) (f i)).card : ℝ) ≤ ((T.image fun w => a₀ + (siteOfInt w : TorusSite N)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (T.card : ℝ) := by exact_mod_cast Finset.card_image_le
    _ ≤ _ := hcard
private lemma siteTermGap_nonneg {n vt A ε : ℝ} (hn : 0 < n) (hvt : 0 < vt) (hA : 0 ≤ A) (hε : 0 ≤ ε) :
    0 ≤ siteTermGap q n vt A ε := by
  unfold siteTermGap unitCellGap
  positivity
private lemma abs_latticeSum_sub_integral_le {n vt A ε : ℝ} (hSN : S = N) (hS : 8 ≤ S) (hn : 1 ≤ n) (hvt : 0 < vt) (h10 : 10 * n ≤ S / 8)
    (hA : 0 ≤ A) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / n ^ 4) {f : Fin (q + 1) → Torus4 S → ℝ} (hT : TupleBounds S n vt f)
    (hq : 1 ≤ q) {Tt : TorusPlaquette N → TorusPlaquette N → ℝ} (hTt : IsNearMaxwellKernel S A ε Tt) (s : Equiv.Perm (Fin (q + 1)))
    (R : Fin (q + 1) → OrderedPlane) :
    |∑ x : Fin (q + 1) → TorusSite N, latticeTerm f Tt s R x - ∫ u in periodBox S q, cycleIntegrand f s R u| ≤
      ((25 * n) ^ 4) ^ (q + 1) * siteTermGap q n vt A ε := by
  classical
  have hn0 : 0 < n := by linarith
  have hS0 : 0 < S := by linarith
  rw [periodBox_eq_iUnion (N := N) hSN, integral_biUnion_finset _ (fun x _ => unitCell_measurable x)
    (fun x _ y _ hxy => unitCell_disjoint hxy) (fun x _ => cycleIntegrand_integrableOn hn0 hT hq s R x),
    ← Finset.sum_sub_distrib]
  set W := Fintype.piFinset fun i => supportSites (N := N) (f i) with hW
  have hsum : ∑ x : Fin (q + 1) → TorusSite N, (latticeTerm f Tt s R x - ∫ u in unitCell x, cycleIntegrand f s R u) =
      ∑ x ∈ W, (latticeTerm f Tt s R x - ∫ u in unitCell x, cycleIntegrand f s R u) :=
    (Finset.sum_subset (Finset.subset_univ W) fun x _ hx => latticeTerm_sub_integral_eq_zero_off s R hx).symm
  rw [hsum]
  have hWcard : (W.card : ℝ) ≤ ((25 * n) ^ 4) ^ (q + 1) := by
    rw [hW, Fintype.card_piFinset]
    push_cast
    calc _ ≤ ∏ _i : Fin (q + 1), ((25 * n) ^ 4 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => supportSites_card_le hSN hS0 hn hT i
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc _ ≤ ∑ x ∈ W, |latticeTerm f Tt s R x - ∫ u in unitCell x, cycleIntegrand f s R u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ W, siteTermGap q n vt A ε :=
        Finset.sum_le_sum fun x _ => latticeTerm_sub_integral_le hSN hS hn hvt h10 hA hε hε' hT hq hTt s R x
    _ = W.card * siteTermGap q n vt A ε := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hWcard (siteTermGap_nonneg hn0 hvt hA hε)
end CellDecomposition
section Assembly
open TestFunctions PeriodicLattice ResponseInTheExpansion TorusFields LinearResponse TorusMetric MeasureTheory
section ErrorBound
variable {N : ℕ} [NeZero N] {S : ℝ} {q : ℕ}
private lemma sum_over_plaquette_tuples (g : (Fin (q + 1) → TorusPlaquette N) → ℝ) :
    ∑ p ∈ Fintype.piFinset (fun _ : Fin (q + 1) => plaquettesIn (Finset.univ : Finset (TorusSite N))), g p =
      ∑ R : Fin (q + 1) → OrderedPlane, ∑ x : Fin (q + 1) → TorusSite N, g fun i => plaquetteAt (x i) (R i) := by
  rw [← Fintype.sum_prod_type' (f := fun (R : Fin (q + 1) → OrderedPlane) (x : Fin (q + 1) → TorusSite N) =>
    g fun i => plaquetteAt (x i) (R i))]
  symm
  refine Finset.sum_bij (fun y _ i => plaquetteAt (y.2 i) (y.1 i)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro y _
    exact Fintype.mem_piFinset.2 fun i => plaquetteAt_mem _ _
  · rintro ⟨R, x⟩ _ ⟨R', x'⟩ _ h
    have h' : ∀ i, plaquetteAt (x i) (R i) = plaquetteAt (x' i) (R' i) := fun i => congrFun h i
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · have := h' i
      simp only [plaquetteAt, Prod.mk.injEq] at this
      exact Subtype.ext (Prod.ext this.2.1 this.2.2)
    · have := h' i
      simp only [plaquetteAt, Prod.mk.injEq] at this
      exact this.1
  · intro p hp
    have hp' := Fintype.mem_piFinset.1 hp
    have h : ∀ i, (p i).2.1 < (p i).2.2 := fun i => by
      have := hp' i
      simp only [plaquettesIn, Finset.mem_filter] at this
      exact this.2.1
    exact ⟨(fun i => ⟨((p i).2.1, (p i).2.2), h i⟩, fun i => (p i).1), Finset.mem_univ _, rfl⟩
open Classical in
private lemma kernelCycleSum_eq (f : Fin (q + 1) → Torus4 S → ℝ) (Tt : TorusPlaquette N → TorusPlaquette N → ℝ) :
    kernelCycleSum (fun i p => f i (torusProj S (barycenterVec p))) Tt =
      ∑ s ∈ (Finset.univ : Finset (Equiv.Perm (Fin (q + 1)))).filter (fun s => s 0 = 0),
        ∑ R : Fin (q + 1) → OrderedPlane, ∑ x : Fin (q + 1) → TorusSite N, latticeTerm f Tt s R x := by
  unfold kernelCycleSum
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_over_plaquette_tuples]
  rfl
private lemma traceAlongCycle_eq (u : Fin (q + 1) → Fin 4 → ℝ) (s : Equiv.Perm (Fin (q + 1))) :
    traceAlongCycle S u s = ∑ R : Fin (q + 1) → OrderedPlane, ∏ j, cycleKernelFactor S s R u j := by
  unfold traceAlongCycle
  rw [trace_list_prod_eq, ← (s.symm.arrowCongr (Equiv.refl OrderedPlane)).sum_comp]
  rfl
private lemma cycleIntegrand_integrableOn_periodBox {n vt : ℝ} (hSN : S = N) (hn : 0 < n) {f : Fin (q + 1) → Torus4 S → ℝ}
    (hT : TupleBounds S n vt f) (hq : 1 ≤ q) (s : Equiv.Perm (Fin (q + 1))) (R : Fin (q + 1) → OrderedPlane) :
    IntegrableOn (cycleIntegrand f s R) (periodBox S q) := by
  rw [periodBox_eq_iUnion (N := N) hSN, integrableOn_finset_iUnion]
  exact fun x _ => cycleIntegrand_integrableOn hn hT hq s R x
private lemma cumulant_term_eq {n vt : ℝ} (hSN : S = N) (hn : 0 < n) {f : Fin (q + 1) → Torus4 S → ℝ}
    (hT : TupleBounds S n vt f) (hq : 1 ≤ q) (s : Equiv.Perm (Fin (q + 1))) :
    ∫ u in periodBox S q, (∏ i, f i (torusProj S (u i))) * traceAlongCycle S u s =
      ∑ R : Fin (q + 1) → OrderedPlane, ∫ u in periodBox S q, cycleIntegrand f s R u := by
  have e : (fun u : Fin (q + 1) → Fin 4 → ℝ => (∏ i, f i (torusProj S (u i))) * traceAlongCycle S u s) =
      fun u => ∑ R : Fin (q + 1) → OrderedPlane, cycleIntegrand f s R u := by
    funext u
    rw [traceAlongCycle_eq, Finset.mul_sum]
    rfl
  rw [e, integral_finsetSum]
  exact fun R _ => cycleIntegrand_integrableOn_periodBox hSN hn hT hq s R
private def planeChoiceConstant (q : ℕ) (vt A : ℝ) : ℝ :=
  (25 ^ 4) ^ (q + 1) * (q + 1) * ((2 + 2 * A) ^ q * A + 2 ^ (q + 1) * (2 / vt) + 2 ^ q * 120)
private lemma planeChoiceConstant_nonneg (q : ℕ) {vt A : ℝ} (hvt : 0 < vt) (hA : 0 ≤ A) : 0 ≤ planeChoiceConstant q vt A := by
  unfold planeChoiceConstant
  positivity
private lemma cellCount_mul_gap_le {n vt A ε : ℝ} (hn : 0 < n) (hvt : 0 < vt) (hA : 0 ≤ A) (hε : 0 ≤ ε) :
    ((25 * n) ^ 4) ^ (q + 1) * siteTermGap q n vt A ε ≤ planeChoiceConstant q vt A * (1 / n + n ^ 4 * ε) := by
  unfold siteTermGap unitCellGap planeChoiceConstant
  have hP : ((25 * n) ^ 4) ^ (q + 1) = (25 ^ 4) ^ (q + 1) * ((n ^ 4) ^ q * n ^ 4) := by
    rw [mul_pow, mul_pow, pow_succ (n ^ 4)]
  have e1 : ((2 + 2 * A) / n ^ 4) ^ q = (2 + 2 * A) ^ q / (n ^ 4) ^ q := div_pow _ _ _
  have e2 : (2 / n ^ 4) ^ (q + 1) = 2 ^ (q + 1) / ((n ^ 4) ^ q * n ^ 4) := by
    rw [div_pow, pow_succ (n ^ 4)]
  have e3 : ((2 : ℝ) / n ^ 4) ^ q = 2 ^ q / (n ^ 4) ^ q := div_pow _ _ _
  rw [hP, e1, e2, e3]
  have hZ : 0 < (n ^ 4) ^ q := by positivity
  have hc : (0 : ℝ) ≤ (25 ^ 4) ^ (q + 1) := by positivity
  have hY : 0 ≤ (2 + 2 * A) ^ q := by positivity
  have hW : (0 : ℝ) ≤ 2 ^ (q + 1) := by positivity
  have hU : (0 : ℝ) ≤ 2 ^ q := by positivity
  generalize (n ^ 4) ^ q = Z at hZ
  generalize ((25 : ℝ) ^ 4) ^ (q + 1) = c at hc
  generalize (2 + 2 * A) ^ q = Y at hY
  generalize (2 : ℝ) ^ (q + 1) = W at hW
  generalize (2 : ℝ) ^ q = U at hU
  have hL : c * (Z * n ^ 4) * (((q : ℝ) + 1) * (Y / Z) * (A * (1 / n ^ 5 + ε)) +
      (((q : ℝ) + 1) * (2 / (vt * n)) * (W / (Z * n ^ 4)) + ((q : ℝ) + 1) * (U / Z) * (120 / n ^ 5))) =
      c * ((q : ℝ) + 1) * (Y * A * (1 / n + n ^ 4 * ε) + (W * (2 / vt) + U * 120) * (1 / n)) := by
    field_simp
  rw [hL]
  have hgap : 0 ≤ c * ((q : ℝ) + 1) * ((W * (2 / vt) + U * 120) * (n ^ 4 * ε)) := by positivity
  nlinarith
private def cumulantConstant (q : ℕ) (vt A : ℝ) : ℝ :=
  3 / 2 * (Fintype.card (Equiv.Perm (Fin (q + 1))) * (Fintype.card (Fin (q + 1) → OrderedPlane) * planeChoiceConstant q vt A))
private lemma cumulantConstant_nonneg (q : ℕ) {vt A : ℝ} (hvt : 0 < vt) (hA : 0 ≤ A) : 0 ≤ cumulantConstant q vt A := by
  have := planeChoiceConstant_nonneg q hvt hA
  unfold cumulantConstant
  positivity
private theorem riemannSum_error_bound {n vt A ε : ℝ} (hSN : S = N) (h80 : 80 * n ≤ S) (hn : 1 ≤ n) (hvt : 0 < vt) (hA : 0 ≤ A)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1 / n ^ 4) {f : Fin (q + 1) → Torus4 S → ℝ} (hT : TupleBounds S n vt f)
    (hq : 1 ≤ q) {Tt : TorusPlaquette N → TorusPlaquette N → ℝ} (hTt : IsNearMaxwellKernel S A ε Tt) :
    |3 / 2 * kernelCycleSum (fun i p => f i (torusProj S (barycenterVec p))) Tt - gaussianCumulantLimit S f| ≤
      cumulantConstant q vt A * (1 / n + n ^ 4 * ε) := by
  classical
  have hn0 : 0 < n := by linarith
  have hS : 8 ≤ S := by linarith
  have h10 : 10 * n ≤ S / 8 := by linarith
  have hK : 0 ≤ planeChoiceConstant q vt A * (1 / n + n ^ 4 * ε) := mul_nonneg (planeChoiceConstant_nonneg q hvt hA) (by positivity)
  have hone : ∀ (s : Equiv.Perm (Fin (q + 1))) (R : Fin (q + 1) → OrderedPlane),
      |∑ x : Fin (q + 1) → TorusSite N, latticeTerm f Tt s R x - ∫ u in periodBox S q, cycleIntegrand f s R u| ≤
        planeChoiceConstant q vt A * (1 / n + n ^ 4 * ε) := fun s R =>
    (abs_latticeSum_sub_integral_le hSN hS hn hvt h10 hA hε hε' hT hq hTt s R).trans (cellCount_mul_gap_le hn0 hvt hA hε)
  have hlaw : gaussianCumulantLimit S f = 3 / 2 *
      ∑ s ∈ (Finset.univ : Finset (Equiv.Perm (Fin (q + 1)))).filter (fun s => s 0 = 0),
        ∑ R : Fin (q + 1) → OrderedPlane, ∫ u in periodBox S q, cycleIntegrand f s R u := by
    unfold gaussianCumulantLimit
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    exact cumulant_term_eq hSN hn0 hT hq s
  rw [hlaw, kernelCycleSum_eq, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  have hs : |∑ s ∈ (Finset.univ : Finset (Equiv.Perm (Fin (q + 1)))).filter (fun s => s 0 = 0),
      (∑ R : Fin (q + 1) → OrderedPlane, ∑ x : Fin (q + 1) → TorusSite N, latticeTerm f Tt s R x -
        ∑ R : Fin (q + 1) → OrderedPlane, ∫ u in periodBox S q, cycleIntegrand f s R u)| ≤
      Fintype.card (Equiv.Perm (Fin (q + 1))) * (Fintype.card (Fin (q + 1) → OrderedPlane) *
        (planeChoiceConstant q vt A * (1 / n + n ^ 4 * ε))) := by
    have hinner : ∀ s : Equiv.Perm (Fin (q + 1)),
        |∑ R : Fin (q + 1) → OrderedPlane, ∑ x : Fin (q + 1) → TorusSite N, latticeTerm f Tt s R x -
          ∑ R : Fin (q + 1) → OrderedPlane, ∫ u in periodBox S q, cycleIntegrand f s R u| ≤
        Fintype.card (Fin (q + 1) → OrderedPlane) * (planeChoiceConstant q vt A * (1 / n + n ^ 4 * ε)) := by
      intro s
      rw [← Finset.sum_sub_distrib]
      calc _ ≤ ∑ R : Fin (q + 1) → OrderedPlane,
            |∑ x : Fin (q + 1) → TorusSite N, latticeTerm f Tt s R x - ∫ u in periodBox S q, cycleIntegrand f s R u| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _R : Fin (q + 1) → OrderedPlane, planeChoiceConstant q vt A * (1 / n + n ^ 4 * ε) :=
            Finset.sum_le_sum fun R _ => hone s R
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hnn : 0 ≤ (Fintype.card (Fin (q + 1) → OrderedPlane) : ℝ) * (planeChoiceConstant q vt A * (1 / n + n ^ 4 * ε)) := by
      positivity
    calc _ ≤ ∑ s ∈ (Finset.univ : Finset (Equiv.Perm (Fin (q + 1)))).filter (fun s => s 0 = 0),
          |∑ R : Fin (q + 1) → OrderedPlane, ∑ x : Fin (q + 1) → TorusSite N, latticeTerm f Tt s R x -
            ∑ R : Fin (q + 1) → OrderedPlane, ∫ u in periodBox S q, cycleIntegrand f s R u| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ (Finset.univ : Finset (Equiv.Perm (Fin (q + 1)))).filter (fun s => s 0 = 0),
          (Fintype.card (Fin (q + 1) → OrderedPlane) : ℝ) * (planeChoiceConstant q vt A * (1 / n + n ^ 4 * ε)) :=
          Finset.sum_le_sum fun s _ => hinner s
      _ = (((Finset.univ : Finset (Equiv.Perm (Fin (q + 1)))).filter (fun s => s 0 = 0)).card : ℝ) *
          ((Fintype.card (Fin (q + 1) → OrderedPlane) : ℝ) * (planeChoiceConstant q vt A * (1 / n + n ^ 4 * ε))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) hnn
  calc _ ≤ 3 / 2 * _ := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by unfold cumulantConstant; ring
end ErrorBound
open TorusLumps WeightedResponses
private lemma tupleBounds_of_separatedTuple {ℓ : StepParameters} {m : ℕ} {n vt : ℝ} {p : ℕ} {f : Fin p → FourTorus ℓ.side m → ℝ}
    (hS : 0 < torusSide ℓ.side m) (hvt : 0 < vt) (hn : 0 < n) (hf : IsSeparatedTestTuple ℓ m n vt f) :
    TupleBounds (torusSide ℓ.side m) n vt f where
  bound i x := by
    have := abs_le_one_of_uniformNorm (hf.uniformNorm_eq i) x
    exact this
  lipschitz i x y := by
    refine (abs_sub_le_lipConst (hf.lipschitz i) x y).trans ?_
    exact mul_le_mul_of_nonneg_right (hf.lipConst_le i) (euclidNorm_nonneg _)
  separated i j hij v w hv hw := le_vecNorm_of_separated hS hf.separated hij hv hw
  close i j v w hv hw := vecNorm_le_of_near hS (hf.dist_le j i) hv hw
  continuous i := by
    obtain ⟨C, hC0, hC⟩ := hf.lipschitz i
    have hL : LipschitzWith (Real.toNNReal (C * 2)) fun v : Fin 4 → ℝ => f i (torusProj (torusSide ℓ.side m) v) := by
      refine LipschitzWith.of_dist_le_mul fun v w => ?_
      rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
      have e : torusProj (torusSide ℓ.side m) v - torusProj (torusSide ℓ.side m) w = torusProj (torusSide ℓ.side m) (v - w) := by
        funext μ
        simp [torusProj, AddCircle.coe_sub]
      have h1 : euclidDistTorus (torusProj (torusSide ℓ.side m) v) (torusProj (torusSide ℓ.side m) w) ≤ 2 * dist v w := by
        unfold euclidDistTorus
        rw [e]
        refine (euclidNorm_proj_le _).trans ?_
        refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
        have : ∀ k : Fin 4, (v - w) k ^ 2 ≤ dist v w ^ 2 := fun k => by
          have h2 : |(v - w) k| ≤ dist v w := by
            have := dist_le_pi_dist v w k
            rwa [Real.dist_eq] at this
          exact sq_le_sq' (by linarith [abs_le.1 h2]) (abs_le.1 h2).2
        unfold sqNorm
        calc _ ≤ ∑ _k : Fin 4, dist v w ^ 2 := Finset.sum_le_sum fun k _ => this k
          _ = _ := by simp; ring
      calc _ ≤ C * euclidDistTorus (torusProj (torusSide ℓ.side m) v) (torusProj (torusSide ℓ.side m) w) := hC _ _
        _ ≤ C * (2 * dist v w) := mul_le_mul_of_nonneg_left h1 hC0
        _ = _ := by ring
    exact hL.continuous
theorem fineTraceRiemannSum : fineTraceRiemannSumStatement := by
  intro ℓ vt A hF h0 h1 hA
  refine ⟨cumulantConstant 1 vt A + cumulantConstant 3 vt A, ?_⟩
  intro m q n ε Tt hq hn h80 hε hε' hTt f hf
  have hSN : torusSide ℓ.side m = ((fineSide ℓ.side 0 (2 * ℓ.side ^ m) : ℕ) : ℝ) := by
    simp [fineSide, torusSide]
  have hn0 : 0 < n := by linarith
  have hS0 : 0 < torusSide ℓ.side m := by linarith
  have hε'' : ε ≤ 1 / n ^ 4 := by
    have : n ^ (-(4 : ℤ)) = 1 / n ^ 4 := by
      rw [zpow_neg, one_div]
      norm_cast
    rwa [this] at hε'
  have hT : TupleBounds (torusSide ℓ.side m) n vt f := tupleBounds_of_separatedTuple hS0 h0 hn0 hf
  have hq1 : 1 ≤ q := by rcases hq with rfl | rfl <;> norm_num
  have hw : (fun i => testWeight ℓ.side 0 m (f i)) = fun i p => f i (torusProj (torusSide ℓ.side m) (barycenterVec p)) := by
    funext i p
    have e : (fun k : Fin 4 => (((p.1 k).val : ℝ) + (if k = p.2.1 then 1 / 2 else 0) +
        (if k = p.2.2 then 1 / 2 else 0)) / (ℓ.side : ℝ) ^ 0) = barycenterVec p := by
      funext k
      rw [pow_zero, div_one]
      rfl
    unfold testWeight plaquetteBarycenterAt
    rw [e]
  rw [hw]
  have hc := riemannSum_error_bound hSN h80 hn h0 hA hε hε'' hT hq1 (Tt := Tt) hTt
  refine hc.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have a1 := cumulantConstant_nonneg 1 h0 hA
  have a3 := cumulantConstant_nonneg 3 h0 hA
  rcases hq with rfl | rfl <;> linarith
end Assembly
end YangMills.Construction.FourPointCondition
end

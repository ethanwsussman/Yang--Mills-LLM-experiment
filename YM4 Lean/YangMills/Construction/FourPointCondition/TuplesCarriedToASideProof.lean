import YangMills.Construction.FourPointCondition.TuplesCarriedToASide
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Pointwise
open MeasureTheory Set
namespace YangMills.Construction
open TestFunctions TorusMetric PeriodicLattice ResponseInTheExpansion LinearResponse TorusLumps FourPointBounds
namespace FourPointCondition.DilationToSide
private def torusDilation {S T : ℝ} (hS : 0 < S) (hT : 0 < T) : Torus4 T ≃ₜ Torus4 S :=
  Homeomorph.piCongrRight fun _ => AddCircle.homeomorphAddCircle T S hT.ne' hS.ne'
private theorem torusDilation_torusProj {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (v : Fin 4 → ℝ) :
    torusDilation hS hT (torusProj T v) = torusProj S ((S / T) • v) := by
  funext i
  have h : torusDilation hS hT (torusProj T v) i = ((v i * (T⁻¹ * S) : ℝ) : AddCircle S) := rfl
  rw [h]
  have h' : v i * (T⁻¹ * S) = ((S / T) • v) i := by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h']
  rfl
private theorem torusDilation_sub {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (a b : Torus4 T) :
    torusDilation hS hT (a - b) = torusDilation hS hT a - torusDilation hS hT b := by
  funext i
  exact map_sub (AddCircle.equivAddCircle T S hT.ne' hS.ne') (a i) (b i)
private theorem euclidNormVec_smul_of_pos {c : ℝ} (hc : 0 < c) (v : Fin 4 → ℝ) :
    euclidNormVec (c • v) = c * euclidNormVec v := by
  have h : ∑ μ, (c • v) μ ^ 2 = c ^ 2 * ∑ μ, v μ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [euclidNormVec, euclidNormVec, h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
private theorem torusEuclidNorm_torusDilation {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (w : Torus4 T) :
    torusEuclidNorm (torusDilation hS hT w) = (S / T) * torusEuclidNorm w := by
  have hc : 0 < S / T := div_pos hS hT
  have hset : euclidNormVec '' (torusProj S ⁻¹' {torusDilation hS hT w}) =
      (S / T) • (euclidNormVec '' (torusProj T ⁻¹' {w})) := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : torusProj S v = torusDilation hS hT w := hv
      have hback : (S / T) • ((T / S) • v) = v := by
        rw [smul_smul, div_mul_div_comm, mul_comm S T, div_self (mul_pos hT hS).ne', one_smul]
      refine Set.mem_smul_set.mpr ⟨euclidNormVec ((T / S) • v), ⟨(T / S) • v, ?_, rfl⟩, ?_⟩
      · apply (torusDilation hS hT).injective
        show torusDilation hS hT (torusProj T ((T / S) • v)) = torusDilation hS hT w
        rw [torusDilation_torusProj, hback, hv']
      · rw [smul_eq_mul, ← euclidNormVec_smul_of_pos hc, hback]
    · intro hr
      obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hr
      have hv' : torusProj T v = w := hv
      refine ⟨(S / T) • v, ?_, euclidNormVec_smul_of_pos hc v⟩
      show torusProj S ((S / T) • v) = torusDilation hS hT w
      rw [← hv', torusDilation_torusProj]
  rw [torusEuclidNorm, torusEuclidNorm, hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
private theorem euclidDistTorus_torusDilation {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (x y : Torus4 T) :
    euclidDistTorus (torusDilation hS hT x) (torusDilation hS hT y) = (S / T) * euclidDistTorus x y := by
  rw [euclidDistTorus, euclidDistTorus, ← torusDilation_sub, torusEuclidNorm_torusDilation]
private theorem lipConstTorus_comp_torusDilation {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (f : Torus4 S → ℝ) :
    lipConstTorus (f ∘ torusDilation hS hT) = (S / T) * lipConstTorus f := by
  have hc : 0 < S / T := div_pos hS hT
  have hset : {C : ℝ | 0 ≤ C ∧ ∀ x y : Torus4 T, ‖(f ∘ torusDilation hS hT) x - (f ∘ torusDilation hS hT) y‖ ≤ C * euclidDistTorus x y} =
      (S / T) • {C : ℝ | 0 ≤ C ∧ ∀ x y : Torus4 S, ‖f x - f y‖ ≤ C * euclidDistTorus x y} := by
    ext C
    constructor
    · rintro ⟨h0, h⟩
      refine Set.mem_smul_set.mpr ⟨C / (S / T), ⟨div_nonneg h0 hc.le, fun x y => ?_⟩, ?_⟩
      · obtain ⟨a, rfl⟩ := (torusDilation hS hT).surjective x
        obtain ⟨b, rfl⟩ := (torusDilation hS hT).surjective y
        calc ‖f (torusDilation hS hT a) - f (torusDilation hS hT b)‖ ≤ C * euclidDistTorus a b := h a b
          _ = C / (S / T) * euclidDistTorus (torusDilation hS hT a) (torusDilation hS hT b) := by
            rw [euclidDistTorus_torusDilation]
            field_simp
      · rw [smul_eq_mul, mul_div_cancel₀ _ hc.ne']
    · intro hC
      obtain ⟨C', ⟨h0, h⟩, rfl⟩ := Set.mem_smul_set.mp hC
      refine ⟨by simpa only [smul_eq_mul] using mul_nonneg hc.le h0, fun x y => ?_⟩
      calc ‖f (torusDilation hS hT x) - f (torusDilation hS hT y)‖
          ≤ C' * euclidDistTorus (torusDilation hS hT x) (torusDilation hS hT y) := h _ _
        _ = (S / T) • C' * euclidDistTorus x y := by
          rw [euclidDistTorus_torusDilation, smul_eq_mul]
          ring
  rw [lipConstTorus, lipConstTorus, bestLipschitzConstant, bestLipschitzConstant, hset,
    Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
private theorem uniformNorm_comp_torusDilation {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (f : Torus4 S → ℝ) :
    uniformNorm (f ∘ torusDilation hS hT) = uniformNorm f :=
  (torusDilation hS hT).surjective.iSup_comp fun x => ‖f x‖
private theorem torusSide_pos {ℓ : StepParameters} (hfit : ℓ.Admissible) (m : ℕ) : 0 < torusSide ℓ.side m := by
  have hL : (0 : ℝ) < ℓ.side := Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num) hfit.L_ge)
  simp only [torusSide]
  positivity
private theorem dilateToSide_eq_comp (L m M : ℕ) (hS : 0 < torusSide L m) (hT : 0 < torusSide L M)
    (f : FourTorus L m → ℝ) :
    dilateToSide L m M f = f ∘ torusDilation hS hT := by
  funext y
  have h : torusDilation hS hT y = torusProj (torusSide L m) ((torusSide L m / torusSide L M) • liftPoint y) := by
    conv_lhs => rw [← torusProj_liftPoint y]
    exact torusDilation_torusProj hS hT _
  simp only [Function.comp, dilateToSide]
  rw [h]
  rfl
private theorem isSeparatedTestTuple_dilateToSide {ℓ : StepParameters} (hfit : ℓ.Admissible) {m M p : ℕ}
    {d n vt : ℝ} (hn : n * torusSide ℓ.side m = d * torusSide ℓ.side M) {f : Fin p → FourTorus ℓ.side m → ℝ}
    (hf : IsSeparatedTestTuple ℓ m d vt f) :
    IsSeparatedTestTuple ℓ M n vt fun i => dilateToSide ℓ.side m M (f i) := by
  have hS := torusSide_pos hfit m
  have hT := torusSide_pos hfit M
  have hc : 0 < torusSide ℓ.side m / torusSide ℓ.side M := div_pos hS hT
  have hd : 0 < d := hf.separated.1
  have hnd : n = d / (torusSide ℓ.side m / torusSide ℓ.side M) := by
    field_simp
    linarith
  have hnpos : 0 < n := by
    rw [hnd]
    exact div_pos hd hc
  have hcar : (fun i => dilateToSide ℓ.side m M (f i)) = fun i => f i ∘ torusDilation hS hT :=
    funext fun i => dilateToSide_eq_comp _ _ _ hS hT (f i)
  rw [hcar]
  have hsupp : ∀ i, ∀ x ∈ tsupport (f i ∘ torusDilation hS hT), torusDilation hS hT x ∈ tsupport (f i) :=
    fun i x hx => tsupport_comp_subset_preimage (f i) (torusDilation hS hT).continuous hx
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, ⟨hnpos, fun i k hik => ?_⟩, fun i j x hx z hz => ?_⟩
  · rw [uniformNorm_comp_torusDilation]
    exact hf.uniformNorm_eq i
  · obtain ⟨C, hC, h⟩ := hf.lipschitz i
    refine ⟨C * (torusSide ℓ.side m / torusSide ℓ.side M), mul_nonneg hC hc.le, fun x y => ?_⟩
    calc ‖(f i ∘ torusDilation hS hT) x - (f i ∘ torusDilation hS hT) y‖
        ≤ C * euclidDistTorus (torusDilation hS hT x) (torusDilation hS hT y) := h _ _
      _ = C * (torusSide ℓ.side m / torusSide ℓ.side M) * euclidDistTorus x y := by
        rw [euclidDistTorus_torusDilation, mul_assoc]
  · rw [lipConstTorus_comp_torusDilation]
    have h1 : 1 / (vt * n) = (torusSide ℓ.side m / torusSide ℓ.side M) * (1 / (vt * d)) := by
      rw [hnd]
      generalize torusSide ℓ.side m / torusSide ℓ.side M = c at hc
      field_simp
    rw [h1]
    exact mul_le_mul_of_nonneg_left (hf.lipConst_le i) hc.le
  · refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
    have h1 : ENNReal.ofReal d ≤ ENNReal.ofReal (torusEuclidNorm (torusDilation hS hT a - torusDilation hS hT b)) :=
      (hf.separated.2 i k hik).trans
        (iInf₂_le_of_le _ (hsupp i a ha) (iInf₂_le_of_le _ (hsupp k b hb) le_rfl))
    have h2 : d ≤ torusEuclidNorm (torusDilation hS hT a - torusDilation hS hT b) := by
      rcases ENNReal.ofReal_le_ofReal_iff'.mp h1 with h | h
      · exact h
      · exact absurd h (not_le.mpr hd)
    rw [← torusDilation_sub, torusEuclidNorm_torusDilation] at h2
    apply ENNReal.ofReal_le_ofReal
    rw [hnd, div_le_iff₀ hc, mul_comm]
    exact h2
  · have h1 := hf.dist_le i j _ (hsupp i x hx) _ (hsupp j z hz)
    rw [euclidDistTorus_torusDilation] at h1
    rw [hnd, mul_div_assoc', le_div_iff₀ hc, mul_comm]
    exact h1
private theorem sqNorm_smul (c : ℝ) (z : Fin 4 → ℝ) :
    sqNorm (c • z) = c ^ 2 * sqNorm z := by
  simp only [sqNorm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
private theorem hyperplaneReflection_smul {c : ℝ} (hc : c ≠ 0) (z : Fin 4 → ℝ) (i j : Fin 4) :
    hyperplaneReflection (c • z) i j = hyperplaneReflection z i j := by
  have h : 2 * (c • z) i * (c • z) j = c ^ 2 * (2 * z i * z j) := by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hyperplaneReflection, hyperplaneReflection, sqNorm_smul, h, mul_div_mul_left _ _ (pow_ne_zero 2 hc)]
private theorem planeKernelMatrix_smul {c : ℝ} (hc : c ≠ 0) (z : Fin 4 → ℝ) :
    planeKernelMatrix (c • z) = (c⁻¹) ^ 4 • planeKernelMatrix z := by
  ext P P'
  simp only [planeKernelMatrix, continuumCurvatureKernel, Matrix.smul_apply, smul_eq_mul,
    hyperplaneReflection_smul hc, sqNorm_smul]
  have h : Real.pi ^ 2 * (c ^ 2 * sqNorm z) ^ 2 = c ^ 4 * (Real.pi ^ 2 * sqNorm z ^ 2) := by
    ring
  rw [h, inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring
private theorem circleSub_mul {c : ℝ} (hc : c ≠ 0) (N u v : ℝ) :
    circleSub (c * N) (c * u) (c * v) = c * circleSub N u v := by
  have h : (c * u - c * v) / (c * N) = (u - v) / N := by
    rw [← mul_sub, mul_div_mul_left _ _ hc]
  rw [circleSub, circleSub, h]
  ring
private theorem periodicDisplacement_smul {c : ℝ} (hc : c ≠ 0) (N : ℝ) (x y : Fin 4 → ℝ) :
    periodicDisplacement (c * N) (c • x) (c • y) = c • periodicDisplacement N x y := by
  funext i
  simp only [periodicDisplacement, Pi.smul_apply, smul_eq_mul, circleSub_mul hc]
private theorem list_prod_ofFn_smul {A : Type*} [Semiring A] [Algebra ℝ A] (a : ℝ) :
    ∀ {n : ℕ} (B : Fin n → A), (List.ofFn fun i => a • B i).prod = a ^ n • (List.ofFn B).prod
  | 0, _ => by simp
  | n + 1, B => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, list_prod_ofFn_smul a fun i => B i.succ,
      smul_mul_smul_comm, pow_succ']
private theorem traceAlongCycle_smul {c : ℝ} (hc : c ≠ 0) (N : ℝ) {q : ℕ} (u : Fin (q + 1) → Fin 4 → ℝ)
    (s : Equiv.Perm (Fin (q + 1))) :
    traceAlongCycle (c * N) (c • u) s = ((c⁻¹) ^ 4) ^ (q + 1) * traceAlongCycle N u s := by
  have h : (fun i : Fin (q + 1) => planeKernelMatrix (periodicDisplacement (c * N) ((c • u) (s (finRotate (q + 1) i)))
      ((c • u) (s i)))) = fun i => (c⁻¹) ^ 4 • planeKernelMatrix (periodicDisplacement N (u (s (finRotate (q + 1) i))) (u (s i))) := by
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, periodicDisplacement_smul hc, planeKernelMatrix_smul hc]
  rw [traceAlongCycle, traceAlongCycle, h, list_prod_ofFn_smul, Matrix.trace_smul, smul_eq_mul]
private theorem smul_pi_Ico_cube {ρ S : ℝ} (hρ : 0 < ρ) (q : ℕ) :
    ρ • (Set.pi Set.univ fun _ : Fin (q + 1) => Set.pi Set.univ fun _ : Fin 4 => Set.Ico (0 : ℝ) S) =
      Set.pi Set.univ fun _ : Fin (q + 1) => Set.pi Set.univ fun _ : Fin 4 => Set.Ico (0 : ℝ) (ρ * S) := by
  ext u
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hρ.ne']
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Pi.smul_apply, smul_eq_mul, Set.mem_Ico]
  refine forall_congr' fun i => forall_congr' fun μ => ?_
  rw [inv_mul_eq_div, le_div_iff₀ hρ, div_lt_iff₀ hρ, zero_mul, mul_comm S]
private theorem gaussianCumulantLimit_comp_torusDilation {S T : ℝ} (hS : 0 < S) (hT : 0 < T) {q : ℕ}
    (f : Fin (q + 1) → Torus4 S → ℝ) :
    gaussianCumulantLimit T (fun i => f i ∘ torusDilation hS hT) = gaussianCumulantLimit S f := by
  have hρ : 0 < T / S := div_pos hT hS
  have hTS : T = T / S * S := (div_mul_cancel₀ T hS.ne').symm
  unfold gaussianCumulantLimit
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  set ρ := T / S with hρdef
  set F : (Fin (q + 1) → Fin 4 → ℝ) → ℝ := fun u =>
    (∏ i, (f i ∘ torusDilation hS hT) (torusProj T (u i))) * traceAlongCycle T u s with hF
  have hcomp := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Fin (q + 1) → Fin 4 → ℝ)) F
    (Set.pi Set.univ fun _ : Fin (q + 1) => Set.pi Set.univ fun _ : Fin 4 => Set.Ico (0 : ℝ) S) hρ
  rw [smul_pi_Ico_cube hρ, ← hTS] at hcomp
  have hfin : Module.finrank ℝ (Fin (q + 1) → Fin 4 → ℝ) = 4 * (q + 1) := by
    simp [Module.finrank_pi_fintype, mul_comm]
  have hval : ∀ v : Fin (q + 1) → Fin 4 → ℝ, F (ρ • v) =
      ((ρ⁻¹) ^ 4) ^ (q + 1) * ((∏ i, f i (torusProj S (v i))) * traceAlongCycle S v s) := by
    intro v
    have h1 : ∀ i, (f i ∘ torusDilation hS hT) (torusProj T ((ρ • v) i)) = f i (torusProj S (v i)) := by
      intro i
      have hsm : (S / T) • (ρ • v) i = v i := by
        rw [Pi.smul_apply, smul_smul, hρdef, div_mul_div_comm, mul_comm S T, div_self (mul_pos hT hS).ne', one_smul]
      simp only [Function.comp]
      rw [torusDilation_torusProj, hsm]
    simp only [hF, h1]
    conv_lhs => rw [hTS, traceAlongCycle_smul hρ.ne']
    ring
  simp only [hval, integral_const_mul] at hcomp
  rw [hfin, smul_eq_mul] at hcomp
  have hne : ((ρ ^ (4 * (q + 1)))⁻¹ : ℝ) ≠ 0 := inv_ne_zero (pow_pos hρ _).ne'
  apply mul_left_cancel₀ hne
  rw [← hcomp, pow_mul, inv_pow, inv_pow]
theorem dilatedTupleToSide : dilatedTupleToSideStatement := by
  intro ℓ m M p d n vt hfit hn f hf
  refine ⟨isSeparatedTestTuple_dilateToSide hfit hn hf, fun q _ g _ => ?_⟩
  have hS := torusSide_pos hfit m
  have hT := torusSide_pos hfit M
  have hcar : (fun i => dilateToSide ℓ.side m M (g i)) = fun i => g i ∘ torusDilation hS hT :=
    funext fun i => dilateToSide_eq_comp _ _ _ hS hT (g i)
  rw [hcar]
  exact gaussianCumulantLimit_comp_torusDilation hS hT g
end FourPointCondition.DilationToSide
end YangMills.Construction
end

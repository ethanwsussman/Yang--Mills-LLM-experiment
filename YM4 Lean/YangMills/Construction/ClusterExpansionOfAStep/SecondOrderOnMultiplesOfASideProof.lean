import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdChainAtEveryLevel.PowerWeightsThroughTheKernelProof
import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTopProof
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import YangMills.Construction.ClusterExpansionOfAStep.DensitiesAgainstAMirror
import YangMills.Construction.ClusterExpansionOfAStep.NumberOfFourDensitiesProof
import YangMills.Construction.ColdChainAtEveryLevel.DensityUnderAChangeOfFramingProof
import YangMills.Construction.ColdStepAtMirrorFrames.FirstDerivativeOfAnExpansionAtOneProof
import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormFromASmallDifferenceProof
import YangMills.Construction.RunningCouplingSlope.EnergyAtTheLeastFieldHasKernelsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages hiding unitStep gaugeTransform IsCold
open TorusFields TorusLumps
namespace AbelianSecondOrder
abbrev Offset : Type := Fin 4 → ℤ
def latticeStep (i : Fin 4) : Offset := Pi.single i 1
section Exact
variable {A : Type} [AddCommGroup A]
def primitive (f : ℤ → A) : ℤ → A
  | Int.ofNat m => ∑ s ∈ Finset.range m, f s
  | Int.negSucc m => - ∑ s ∈ Finset.range (m + 1), f (-(s : ℤ) - 1)
theorem primitive_succ (f : ℤ → A) (a : ℤ) : primitive f (a + 1) = primitive f a + f a := by
  cases a with
  | ofNat m =>
    show primitive f (Int.ofNat (m + 1)) = _
    simp [primitive, Finset.sum_range_succ]
  | negSucc m =>
    cases m with
    | zero =>
      have e : Int.negSucc 0 + 1 = Int.ofNat 0 := rfl
      rw [e]
      simp [primitive]
    | succ k =>
      have e : Int.negSucc (k + 1) + 1 = Int.negSucc k := by
        simp only [Int.negSucc_eq]
        push_cast
        ring
      rw [e]
      simp only [primitive]
      rw [Finset.sum_range_succ _ (k + 1)]
      have e2 : (-(((k + 1 : ℕ)) : ℤ) - 1) = Int.negSucc (k + 1) := by
        simp only [Int.negSucc_eq]
        push_cast
        ring
      rw [e2]
      abel
def IsClosedCochain (u : Offset → Fin 4 → A) : Prop :=
  ∀ x i j, u x i + u (x + latticeStep i) j = u x j + u (x + latticeStep j) i
theorem exists_potential_of_closed (u : Offset → Fin 4 → A) (hu : IsClosedCochain u) :
    ∃ φ : Offset → A, ∀ x i, φ (x + latticeStep i) - φ x = u x i := by
  suffices H : ∀ S : Finset (Fin 4), ∃ φ : Offset → A, ∀ k ∈ S, ∀ x, φ (x + latticeStep k) - φ x = u x k by
    obtain ⟨φ, hφ⟩ := H Finset.univ
    exact ⟨φ, fun x i => hφ i (Finset.mem_univ i) x⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a S ha ih =>
    obtain ⟨φ, hφ⟩ := ih
    set v : Offset → Fin 4 → A := fun x i => u x i - (φ (x + latticeStep i) - φ x) with hv
    have vclosed : IsClosedCochain v := by
      intro x i j
      simp only [hv]
      have e : x + latticeStep i + latticeStep j = x + latticeStep j + latticeStep i := by abel
      have h3 : u (x + latticeStep j) i = u x i + u (x + latticeStep i) j - u x j := by
        rw [hu x i j]; abel
      rw [e, h3]
      abel
    have vzero : ∀ k ∈ S, ∀ x, v x k = 0 := by
      intro k hk x
      simp [hv, hφ k hk x]
    have vinv : ∀ k ∈ S, ∀ x, v (x + latticeStep k) a = v x a := by
      intro k hk x
      have h1 := vclosed x a k
      rw [vzero k hk, vzero k hk] at h1
      simpa using h1.symm
    let ψ : Offset → A := fun x => primitive (fun s => v (Function.update x a s) a) (x a)
    have ψa : ∀ x, ψ (x + latticeStep a) - ψ x = v x a := by
      intro x
      simp only [ψ]
      have e1 : ∀ s, Function.update (x + latticeStep a) a s = Function.update x a s := by
        intro s
        ext i
        by_cases hi : i = a
        · subst hi; simp
        · simp [Function.update, latticeStep, hi]
      have e2 : (x + latticeStep a) a = x a + 1 := by simp [latticeStep]
      simp only [e1, e2, primitive_succ]
      simp
    have ψk : ∀ k ∈ S, ∀ x, ψ (x + latticeStep k) = ψ x := by
      intro k hk x
      have hka : k ≠ a := fun e => ha (e ▸ hk)
      simp only [ψ]
      have e1 : ∀ s, Function.update (x + latticeStep k) a s = Function.update x a s + latticeStep k := by
        intro s
        ext i
        by_cases hi : i = a
        · subst hi; simp [latticeStep, hka.symm]
        · simp [Function.update, hi]
      have e2 : (x + latticeStep k) a = x a := by simp [latticeStep, hka.symm]
      simp only [e1, e2, vinv k hk]
    refine ⟨φ + ψ, ?_⟩
    intro k hk x
    rcases Finset.mem_insert.mp hk with rfl | hk
    · have h1 := ψa x
      simp only [hv] at h1
      simp only [Pi.add_apply]
      rw [show φ (x + latticeStep k) + ψ (x + latticeStep k) - (φ x + ψ x) =
        (φ (x + latticeStep k) - φ x) + (ψ (x + latticeStep k) - ψ x) by abel, h1]
      abel
    · simp only [Pi.add_apply, ψk k hk x]
      rw [show φ (x + latticeStep k) + ψ x - (φ x + ψ x) = φ (x + latticeStep k) - φ x by abel]
      exact hφ k hk x
end Exact
section Group
theorem coe_expUnit (w : imaginaryQuaternions) :
    ((expUnit w : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (w : ℍ[ℝ]) := rfl
theorem expUnit_zero_eq_one : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem expUnit_smul_mul (X : imaginaryQuaternions) (a b : ℝ) :
    expUnit (a • X) * expUnit (b • X) = expUnit ((a + b) • X) := by apply _root_.YangMills.Construction.TorusFrame.expUnit_smul_mul <;> assumption
theorem expUnit_smul_inv (X : imaginaryQuaternions) (a : ℝ) : (expUnit (a • X))⁻¹ = expUnit ((-a) • X) := by apply _root_.YangMills.SharedProofs.p4359 <;> assumption
theorem norm_expUnit_sub_one_le (w : imaginaryQuaternions) :
    ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖w‖ := by apply _root_.YangMills.SharedProofs.p28543 <;> assumption
end Group
section Calc
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem iteratedFDeriv_comp_linear (G : E → ℝ) (L : F →L[ℝ] E) (q : F) {k : ℕ} (hk : k ≤ 3)
    (hG : ContDiffAt ℝ 3 G (L q)) (v : Fin k → F) :
    iteratedFDeriv ℝ k (fun z => G (L z)) q v = iteratedFDeriv ℝ k G (L q) (fun l => L (v l)) := by
  obtain ⟨u, hu, hC⟩ := hG.contDiffOn (m := 3) le_rfl (by simp)
  obtain ⟨s, hsu, hso, hqs⟩ := mem_nhds_iff.mp hu
  have hCs : ContDiffOn ℝ 3 G s := hC.mono hsu
  have hpre : IsOpen (L ⁻¹' s) := hso.preimage L.continuous
  have h1 := L.iteratedFDerivWithin_comp_right hCs hso.uniqueDiffOn hpre.uniqueDiffOn (x := q) hqs
    (i := k) (by exact_mod_cast hk)
  rw [iteratedFDerivWithin_of_isOpen k hpre (show q ∈ L ⁻¹' s from hqs),
    iteratedFDerivWithin_of_isOpen k hso hqs] at h1
  have h2 := congrArg (fun T => T v) h1
  simpa [Function.comp_def] using h2
theorem iteratedDeriv_along_line (G : E → ℝ) (α : E) (t : ℝ) {k : ℕ} (hk : k ≤ 3)
    (hG : ContDiffAt ℝ 3 G (t • α)) :
    iteratedDeriv k (fun s : ℝ => G (s • α)) t = iteratedFDeriv ℝ k G (t • α) (fun _ => α) := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have h1 := iteratedFDeriv_comp_linear G (ContinuousLinearMap.toSpanSingleton ℝ α) t hk (by simpa using hG)
    (fun _ => (1 : ℝ))
  simpa [ContinuousLinearMap.toSpanSingleton_apply] using h1
theorem multilinear_apply_const_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => ι → ℝ) ℝ) (α : ι → ℝ) :
    T (fun _ => α) = ∑ c : Fin k → ι, (∏ l, α (c l)) * T (fun l => Pi.single (c l) 1) := by
  have hα : α = ∑ b, α b • (Pi.single b 1 : ι → ℝ) := by
    ext x
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : T (fun _ => α) = T (fun _ => ∑ b, α b • (Pi.single b 1 : ι → ℝ)) := by rw [← hα]
  rw [h1, T.map_sum (fun _ b => α b • (Pi.single b 1 : ι → ℝ))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [T.map_smul_univ (fun l => α (c l)) (fun l => Pi.single (c l) 1)]
  simp
theorem taylor_second_order_bound (g : ℝ → ℝ) {γ M : ℝ} (hγ : 0 < γ)
    (hC : ∀ t ∈ Set.Icc 0 γ, ContDiffAt ℝ 3 g t)
    (hM : ∀ t ∈ Set.Icc 0 γ, |iteratedDeriv 3 g t| ≤ M) :
    |g γ - g 0 - γ * iteratedDeriv 1 g 0 - γ ^ 2 / 2 * iteratedDeriv 2 g 0| ≤ M * γ ^ 3 / 2 := by
  have hu : UniqueDiffOn ℝ (Set.Icc 0 γ) := uniqueDiffOn_Icc hγ
  have h0 : (0 : ℝ) ∈ Set.Icc 0 γ := Set.left_mem_Icc.2 hγ.le
  have hon : ContDiffOn ℝ ((2 : ℕ) + 1) g (Set.Icc 0 γ) := fun t ht => by
    have := (hC t ht).contDiffWithinAt (s := Set.Icc 0 γ)
    exact_mod_cast this
  have h1 := taylor_mean_remainder_bound (n := 2) (C := M) hγ.le hon (Set.right_mem_Icc.2 hγ.le)
    (fun y hy => by
      have e := iteratedDerivWithin_eq_iteratedDeriv (n := 2 + 1) hu (hC y hy) hy
      rw [e]
      exact hM y hy)
  have e1 : iteratedDerivWithin 1 g (Set.Icc 0 γ) 0 = iteratedDeriv 1 g 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (n := 1) hu ((hC 0 h0).of_le (by norm_num)) h0
  have e2 : iteratedDerivWithin 2 g (Set.Icc 0 γ) 0 = iteratedDeriv 2 g 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (n := 2) hu ((hC 0 h0).of_le (by norm_num)) h0
  have t2 : taylorWithinEval g 2 (Set.Icc 0 γ) 0 γ =
      g 0 + γ * iteratedDeriv 1 g 0 + γ ^ 2 / 2 * iteratedDeriv 2 g 0 := by
    have a1 := taylorWithinEval_succ g 1 (Set.Icc 0 γ) 0 γ
    have a0 := taylorWithinEval_succ g 0 (Set.Icc 0 γ) 0 γ
    rw [taylor_within_zero_eval] at a0
    have b1 : taylorWithinEval g 2 (Set.Icc 0 γ) 0 γ = taylorWithinEval g (1 + 1) (Set.Icc 0 γ) 0 γ := rfl
    have b0 : taylorWithinEval g 1 (Set.Icc 0 γ) 0 γ = taylorWithinEval g (0 + 1) (Set.Icc 0 γ) 0 γ := rfl
    have c1 : (((0 : ℕ) : ℝ) + 1) * ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
    have c2 : (((1 : ℕ) : ℝ) + 1) * ((Nat.factorial 1 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [b1, a1, b0, a0, c1, c2]
    simp only [zero_add, Nat.reduceAdd, e1, e2, sub_zero, smul_eq_mul, inv_one, one_mul, pow_one]
    ring
  have e4 : M * (γ - 0) ^ (2 + 1) / ((Nat.factorial 2 : ℕ) : ℝ) = M * γ ^ 3 / 2 := by
    norm_num [Nat.factorial]
  rw [Real.norm_eq_abs, t2, e4] at h1
  have e3 : g γ - g 0 - γ * iteratedDeriv 1 g 0 - γ ^ 2 / 2 * iteratedDeriv 2 g 0 =
      g γ - (g 0 + γ * iteratedDeriv 1 g 0 + γ ^ 2 / 2 * iteratedDeriv 2 g 0) := by ring
  rw [e3]
  exact h1
end Calc
section Along
variable {n : ℕ}
def fieldAlong (X : imaginaryQuaternions) (a : TorusBond n → ℝ) : TorusField n :=
  fun x i => expUnit (a (x, i) • X)
theorem holonomy_fieldAlong (X : imaginaryQuaternions) (a : TorusBond n → ℝ) (x : TorusSite n) (μ ν : Fin 4) :
    holonomy (fieldAlong X a) x μ ν =
      expUnit ((a (x, μ) + a (x + unitStep n μ, ν) - a (x + unitStep n ν, μ) - a (x, ν)) • X) := by
  simp only [holonomy, fieldAlong, expUnit_smul_inv, expUnit_smul_mul]
  congr 2
theorem curvature_fieldAlong_le (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (a : TorusBond n → ℝ)
    (x : TorusSite n) (μ ν : Fin 4) :
    curvature (fieldAlong X a) x μ ν ≤
      |a (x, μ) + a (x + unitStep n μ, ν) - a (x + unitStep n ν, μ) - a (x, ν)| := by
  unfold curvature
  rw [holonomy_fieldAlong]
  refine (norm_expUnit_sub_one_le _).trans_eq ?_
  rw [norm_smul, hX, mul_one, Real.norm_eq_abs]
theorem fieldAlong_zero (X : imaginaryQuaternions) : fieldAlong X (0 : TorusBond n → ℝ) = trivialField n := by
  funext x i
  simp [fieldAlong, trivialField, expUnit_zero_eq_one]
variable [NeZero n]
def perturbLinear {k : ℕ} (c : Fin k → TorusBond n) : (Fin k → ℝ) →L[ℝ] (TorusBond n → ℝ) :=
  ContinuousLinearMap.pi fun b => ∑ l, if c l = b then ContinuousLinearMap.proj l else 0
theorem perturbLinear_apply {k : ℕ} (c : Fin k → TorusBond n) (σ : Fin k → ℝ) (b : TorusBond n) :
    perturbLinear c σ b = ∑ l, if c l = b then σ l else 0 := by
  simp only [perturbLinear, ContinuousLinearMap.coe_pi', FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem perturbLinear_single {k : ℕ} (c : Fin k → TorusBond n) (l : Fin k) :
    perturbLinear c (Pi.single l 1) = Pi.single (c l) 1 := by
  ext b
  rw [perturbLinear_apply, Finset.sum_eq_single l]
  · simp [Pi.single_apply, eq_comm]
  · intro l' _ hl'
    simp [hl']
  · simp
theorem perturb_fieldAlong {k : ℕ} (c : Fin k → TorusBond n) (X : imaginaryQuaternions) (σ : Fin k → ℝ)
    (p : TorusBond n → ℝ) :
    perturb c (fun _ => X) σ (fieldAlong X p) = fieldAlong X (p + perturbLinear c σ) := by
  funext x i
  have h1 : (∑ l, if c l = (x, i) then σ l • X else 0) = (perturbLinear c σ (x, i)) • X := by
    rw [perturbLinear_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  simp only [perturb, fieldAlong, h1, expUnit_smul_mul, Pi.add_apply, add_comm]
def valueAlong (f : TorusField n → ℝ) (X : imaginaryQuaternions) (a : TorusBond n → ℝ) : ℝ :=
  f (fieldAlong X a)
theorem contDiffAt_valueAlong (f : TorusField n → ℝ) (X : imaginaryQuaternions) (p : TorusBond n → ℝ)
    (hf : ContDiffThreeAt f (fieldAlong X p)) : ContDiffAt ℝ 3 (valueAlong f X) p := by
  classical
  let e := Fintype.equivFin (TorusBond n)
  let c : Fin (Fintype.card (TorusBond n)) → TorusBond n := e.symm
  have h0 := hf _ c (fun _ => X)
  let T : (TorusBond n → ℝ) →L[ℝ] (Fin (Fintype.card (TorusBond n)) → ℝ) :=
    ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (c l)
  have hT : ∀ a, perturbLinear c (T a) = a := by
    intro a
    ext b
    rw [perturbLinear_apply, Finset.sum_eq_single (e b)]
    · simp [c, T]
    · intro l _ hl
      have : c l ≠ b := fun hb => hl (by simp [← hb, c])
      simp [this]
    · simp
  have key : valueAlong f X =
      fun q => (fun σ => f (perturb c (fun _ => X) σ (fieldAlong X p))) (T (q - p)) := by
    funext q
    simp only [valueAlong]
    rw [perturb_fieldAlong, hT]
    congr 2
    abel
  have hl : ContDiffAt ℝ 3 (fun q => T (q - p)) p := by
    have : ContDiff ℝ 3 (fun q => T (q - p)) := T.contDiff.comp (contDiff_id.sub contDiff_const)
    exact this.contDiffAt
  have h0' : ContDiffAt ℝ 3 (fun σ => f (perturb c (fun _ => X) σ (fieldAlong X p))) (T (p - p)) := by
    simpa using h0
  rw [key]
  exact ContDiffAt.comp (g := fun σ => f (perturb c (fun _ => X) σ (fieldAlong X p)))
    (f := fun q => T (q - p)) p h0' hl
theorem mixedDeriv_fieldAlong (f : TorusField n → ℝ) (X : imaginaryQuaternions) (p : TorusBond n → ℝ)
    (hf : ContDiffThreeAt f (fieldAlong X p)) {k : ℕ} (hk : k ≤ 3) (c : Fin k → TorusBond n) :
    mixedDeriv f (fieldAlong X p) c (fun _ => X) =
      iteratedFDeriv ℝ k (valueAlong f X) p (fun l => Pi.single (c l) 1) := by
  have h0 := contDiffAt_valueAlong f X p hf
  have e1 : (fun σ : Fin k → ℝ => f (perturb c (fun _ => X) σ (fieldAlong X p))) =
      fun σ => (fun a => valueAlong f X (p + a)) (perturbLinear c σ) := by
    funext σ
    simp only [valueAlong]
    rw [perturb_fieldAlong]
  unfold mixedDeriv
  rw [e1]
  have h1 : ContDiffAt ℝ 3 (fun a => valueAlong f X (p + a)) (perturbLinear c 0) := by
    have : ContDiffAt ℝ 3 (valueAlong f X) (p + perturbLinear c 0) := by simpa using h0
    exact this.comp _ (contDiff_const.add contDiff_id).contDiffAt
  rw [iteratedFDeriv_comp_linear (fun a => valueAlong f X (p + a)) (perturbLinear c) 0 hk h1]
  have e2 : (fun l => perturbLinear c (Pi.single l 1 : Fin k → ℝ)) =
      fun l => (Pi.single (c l) 1 : TorusBond n → ℝ) := by
    funext l
    exact perturbLinear_single c l
  rw [e2, map_zero, iteratedFDeriv_comp_add_left]
  simp
end Along
abbrev OffsetBond : Type := Offset × Fin 4
section Lattice
theorem natAbs_le_offsetSupNorm (u : Offset) (i : Fin 4) : (u i).natAbs ≤ offsetSupNorm u := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem offsetSupNorm_le_of_inBox {r : ℕ} {u : Offset} (h : OffsetInBox r u) : offsetSupNorm u ≤ r := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.offsetSupNorm_le_of_withinRadius <;> assumption
theorem inBox_of_offsetSupNorm_le {r : ℕ} {u : Offset} (h : offsetSupNorm u ≤ r) : OffsetInBox r u := by
  intro i
  rw [Int.abs_eq_natAbs]
  exact_mod_cast (natAbs_le_offsetSupNorm u i).trans h
theorem summable_geometric_natAbs {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable fun k : ℤ => ρ ^ k.natAbs := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.summable_pow_natAbs <;> assumption
def decayWeight (b : ℝ) (p : ℕ) (u : OffsetBond) : ℝ :=
  (1 + (offsetSupNorm u.1 : ℝ)) ^ p * Real.exp (-b * offsetSupNorm u.1)
theorem decayWeight_nonneg (b : ℝ) (p : ℕ) (u : OffsetBond) : 0 ≤ decayWeight b p u := by
  unfold decayWeight
  positivity
theorem summable_decayWeight {b : ℝ} (hb : 0 < b) (p : ℕ) : Summable (decayWeight b p) := by apply _root_.YangMills.DeltaSharedProofs.p500449 <;> assumption
end Lattice
section Torus
variable {n : ℕ}
def offsetFrom (Y z : TorusSite n) : Offset := fun i => (z i - Y i).valMinAbs
def offsetBond (Y : TorusSite n) (b : TorusBond n) : OffsetBond := (offsetFrom Y b.1, b.2)
theorem supDist_eq_offsetSupNorm (Y z : TorusSite n) : _root_.YangMills.Construction.TorusFields.supDist z Y = offsetSupNorm (offsetFrom Y z) := rfl
variable [NeZero n]
theorem add_siteOfInt_offsetFrom (Y z : TorusSite n) : Y + siteOfInt (offsetFrom Y z) = z := by apply _root_.YangMills.DeltaSharedProofs.p500399 <;> assumption
theorem offsetFrom_add_siteOfInt (Y : TorusSite n) (u : Offset) (hu : ∀ i, 2 * |u i| < n) :
    offsetFrom Y (Y + siteOfInt u) = u := by
  funext i
  simp only [offsetFrom, siteOfInt, Pi.add_apply, add_sub_cancel_left]
  rw [ZMod.valMinAbs_spec]
  have := hu i
  refine ⟨rfl, ?_, ?_⟩ <;> rcases abs_cases (u i) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
theorem bondFrom_offsetBond (Y : TorusSite n) (b : TorusBond n) : bondFrom Y (offsetBond Y b) = b := by
  simp [bondFrom, offsetBond, add_siteOfInt_offsetFrom]
theorem offsetBond_bondFrom (Y : TorusSite n) (u : OffsetBond) (hu : ∀ i, 2 * |u.1 i| < n) :
    offsetBond Y (bondFrom Y u) = u := by
  simp [bondFrom, offsetBond, offsetFrom_add_siteOfInt Y u.1 hu]
theorem offsetBond_injective (Y : TorusSite n) : Function.Injective (offsetBond Y) := fun b b' e => by
  rw [← bondFrom_offsetBond Y b, e, bondFrom_offsetBond]
theorem sum_offsetBond_le_tsum (Y : TorusSite n) (F : OffsetBond → ℝ) (hF : ∀ u, 0 ≤ F u) (hs : Summable F) :
    ∑ b : TorusBond n, F (offsetBond Y b) ≤ ∑' u, F u := by
  classical
  have e : ∑ b : TorusBond n, F (offsetBond Y b) = ∑ u ∈ Finset.univ.image (offsetBond Y), F u :=
    (Finset.sum_image fun _ _ _ _ h => offsetBond_injective Y h).symm
  rw [e]
  exact hs.sum_le_tsum _ fun u _ => hF u
end Torus
section Weights
variable {ℓ : StepParameters}
theorem weightRate_pos (hfit : ℓ.Admissible) : 0 < ℓ.weightRate := by
  unfold StepParameters.weightRate
  have := hfit.rt_pos
  positivity
theorem exp_le_weight (m : ℕ) : Real.exp (ℓ.weightRate * m) ≤ ℓ.weight m := by apply _root_.YangMills.SharedProofs.p47115 <;> assumption
theorem stepWeight_pos (m : ℕ) : 0 < ℓ.weight m := lt_of_lt_of_le (Real.exp_pos _) (exp_le_weight m)
theorem div_weight_le_exp {C : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    C / ℓ.weight m ≤ C * Real.exp (-ℓ.weightRate * m) := by apply _root_.YangMills.Construction.MirrorDensities.div_weight_le_mul_exp <;> assumption
theorem exists_const_mul_exp_lt {b : ℝ} (hb : 0 < b) (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → C * Real.exp (-b * m) < ε := by
  have h1 : Filter.Tendsto (fun m : ℕ => C * Real.exp (-b * m)) Filter.atTop (nhds (C * 0)) := by
    refine Filter.Tendsto.const_mul C ?_
    have h2 : Filter.Tendsto (fun m : ℕ => b * (m : ℝ)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hb tendsto_natCast_atTop_atTop
    have h3 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h2
    refine h3.congr fun m => ?_
    simp
  rw [mul_zero] at h1
  have h2 := (h1.eventually (gt_mem_nhds hε))
  exact Filter.eventually_atTop.1 h2
end Weights
section Derivatives
variable {n : ℕ}
theorem mixedDeriv_sub_const {k : ℕ} (hk : 1 ≤ k) (G : TorusField n → ℝ) (a : ℝ) (W : TorusField n)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun W => G W - a) W c X = mixedDeriv G W c X := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold mixedDeriv
  have e : (fun y => fderiv ℝ (fun σ : Fin (j + 1) → ℝ => G (perturb c X σ W) - a) y) =
      fun y => fderiv ℝ (fun σ : Fin (j + 1) → ℝ => G (perturb c X σ W)) y := by
    funext y
    exact fderiv_sub_const _
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, e]
theorem perturb_at_zero {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (W : TorusField n) : perturb c X 0 W = W := by apply _root_.YangMills.Construction.TorusFields.perturb_zero <;> assumption
theorem mixedDeriv_zero (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 0 → TorusBond n)
    (X : Fin 0 → imaginaryQuaternions) : mixedDeriv G W c X = G W := by apply _root_.YangMills.Construction.TorusLumps.mixedDeriv_of_fin_zero <;> assumption
theorem mixedDeriv_two_smul (G : TorusField n → ℝ) (W : TorusField n) (hG : ContDiffThreeAt G W)
    (c : Fin 2 → TorusBond n) (a b : ℝ) (X X' : imaginaryQuaternions) :
    mixedDeriv G W c ![a • X, b • X'] = a * b * mixedDeriv G W c ![X, X'] := by
  let L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi fun l => (![a, b] l) • ContinuousLinearMap.proj l
  have e1 : (fun σ => G (perturb c ![a • X, b • X'] σ W)) =
      fun σ => (fun τ => G (perturb c ![X, X'] τ W)) (L σ) := by
    funext σ
    have e0 : perturb c ![a • X, b • X'] σ W = perturb c ![X, X'] (L σ) W := by
      funext x i
      simp only [perturb, Fin.sum_univ_two]
      simp [L, smul_smul, mul_comm]
    simp only [e0]
  unfold mixedDeriv
  have hG0 : ContDiffAt ℝ 3 (fun τ => G (perturb c ![X, X'] τ W)) (L 0) := by
    simpa using hG 2 c ![X, X']
  rw [e1, iteratedFDeriv_comp_linear _ L 0 (by norm_num) hG0]
  have e2 : (fun l => L (Pi.single l 1)) = fun l => (![a, b] l) • (Pi.single l 1 : Fin 2 → ℝ) := by
    funext l
    ext l'
    simp only [L, ContinuousLinearMap.coe_pi', Pi.smul_apply, FunLike.coe_smul,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    by_cases hl : l = l'
    · subst hl
      simp
    · simp [Pi.single_apply, hl, Ne.symm hl]
  rw [e2, map_zero, ContinuousMultilinearMap.map_smul_univ]
  simp [Fin.prod_univ_two]
end Derivatives
section Units
def quatI : imaginaryQuaternions := ⟨⟨0, 1, 0, 0⟩, rfl⟩
theorem sq_norm_imaginary (w : imaginaryQuaternions) :
    ‖w‖ ^ 2 = (w : ℍ[ℝ]).imI ^ 2 + (w : ℍ[ℝ]).imJ ^ 2 + (w : ℍ[ℝ]).imK ^ 2 := by apply _root_.YangMills.SharedProofs.p1745 <;> assumption
theorem norm_eq_one_of_sq_eq_one {w : imaginaryQuaternions} (h : ‖w‖ ^ 2 = 1) : ‖w‖ = 1 := by
  have h0 := norm_nonneg w
  have h1 : (‖w‖ - 1) * (‖w‖ + 1) = 0 := by nlinarith
  rcases mul_eq_zero.1 h1 with h2 | h2 <;> linarith
theorem norm_quatI : ‖quatI‖ = 1 := by
  apply norm_eq_one_of_sq_eq_one
  rw [sq_norm_imaginary]
  simp [quatI]
theorem exists_eq_smul_unit (X : imaginaryQuaternions) :
    ∃ (a : ℝ) (U : imaginaryQuaternions), ‖U‖ = 1 ∧ X = a • U ∧ |a| = ‖X‖ := by apply _root_.YangMills.Construction.TorusLumps.SumOfFourCurvature.exists_smul_unit <;> assumption
end Units
section Kernel
def periodsAlong (X : imaginaryQuaternions) : AddSubgroup ℝ where
  carrier := {t | expUnit (t • X) = 1}
  zero_mem' := by simp [expUnit_zero_eq_one]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [← expUnit_smul_mul, ha, hb, one_mul]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [← expUnit_smul_inv, ha, inv_one]
theorem mem_periodsAlong (X : imaginaryQuaternions) (t : ℝ) : t ∈ periodsAlong X ↔ expUnit (t • X) = 1 :=
  Iff.rfl
theorem sub_mem_periodsAlong (X : imaginaryQuaternions) {a b : ℝ} (h : expUnit (a • X) = expUnit (b • X)) :
    a - b ∈ periodsAlong X := by
  rw [mem_periodsAlong, sub_eq_add_neg, ← expUnit_smul_mul, h, expUnit_smul_mul]
  simp [expUnit_zero_eq_one]
theorem expUnit_eq_of_sub_mem (X : imaginaryQuaternions) {a b : ℝ} (h : a - b ∈ periodsAlong X) :
    expUnit (a • X) = expUnit (b • X) := by
  have h1 : expUnit ((a - b) • X) * expUnit (b • X) = expUnit (a • X) := by
    rw [expUnit_smul_mul]
    simp
  rw [← h1, (mem_periodsAlong X _).1 h, one_mul]
end Kernel
section RotationStep
variable {n : ℕ}
theorem siteOfInt_latticeStep (i : Fin 4) : (siteOfInt (latticeStep i) : TorusSite n) = unitStep n i := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfInt_single <;> assumption
theorem add_siteOfInt_unitStep [NeZero n] (Y : TorusSite n) (u : Offset) (i : Fin 4) :
    Y + siteOfInt u + unitStep n i = Y + siteOfInt (u + latticeStep i) := by
  rw [siteOfInt_add, siteOfInt_latticeStep, add_assoc]
theorem holonomy_of_angles (X : imaginaryQuaternions) (V : TorusField n) (θ : TorusSite n → Fin 4 → ℝ)
    (hθ : ∀ x i, V x i = expUnit (θ x i • X)) (x : TorusSite n) (i j : Fin 4) :
    holonomy V x i j = expUnit ((θ x i + θ (x + unitStep n i) j - θ (x + unitStep n j) i - θ x j) • X) := by
  have e : V = fieldAlong X (fun b => θ b.1 b.2) := by
    funext x i
    exact hθ x i
  rw [e, holonomy_fieldAlong]
variable [NeZero n]
theorem exists_gauge_to_potential (X : imaginaryQuaternions) (ω : Fin 4 → Fin 4 → ℝ) (γ : ℝ)
    (V : TorusField n) (hV : IsAbelianWithCurvature X ω γ V) (Y : TorusSite n) (β : OffsetBond → ℝ)
    (hβ : ∀ u i j, β (u, i) + β (u + latticeStep i, j) - β (u + latticeStep j, i) - β (u, j) = ω i j)
    (r : ℕ) (hr : 2 * r < n) :
    ∃ g : TorusSite n → UnitQuaternion, ∀ b : OffsetBond, BondOffsetInBox r b →
      gaugeTransform g V (bondFrom Y b).1 (bondFrom Y b).2 = expUnit ((γ * β b) • X) := by
  obtain ⟨⟨θ, hθ⟩, hp⟩ := hV
  set Kr := periodsAlong X with hKr
  let ρ : Offset → Fin 4 → ℝ := fun u i => θ (Y + siteOfInt u) i - γ * β (u, i)
  let P : Offset → Fin 4 → Fin 4 → ℝ := fun u i j =>
    ρ u i + ρ (u + latticeStep i) j - ρ u j - ρ (u + latticeStep j) i
  have hP : ∀ u i j, i < j → P u i j ∈ Kr := by
    intro u i j hij
    have h1 := hp (Y + siteOfInt u) i j hij
    rw [holonomy_of_angles X V θ hθ] at h1
    have h2 := sub_mem_periodsAlong X h1
    have e : P u i j = (θ (Y + siteOfInt u) i + θ (Y + siteOfInt u + unitStep n i) j -
        θ (Y + siteOfInt u + unitStep n j) i - θ (Y + siteOfInt u) j) - γ * ω i j := by
      simp only [P, ρ, add_siteOfInt_unitStep]
      rw [← hβ u i j]
      ring
    rw [e]
    exact h2
  have hPall : ∀ u i j, P u i j ∈ Kr := by
    intro u i j
    rcases lt_trichotomy i j with hij | hij | hij
    · exact hP u i j hij
    · subst hij
      have : P u i i = 0 := by simp only [P]; ring
      rw [this]
      exact Kr.zero_mem
    · have : P u i j = - P u j i := by simp only [P]; ring
      rw [this]
      exact Kr.neg_mem (hP u j i hij)
  let c : Offset → Fin 4 → (ℝ ⧸ Kr) := fun u i => ((ρ u i : ℝ) : ℝ ⧸ Kr)
  have hcl : IsClosedCochain c := by
    intro u i j
    have h1 : ((P u i j : ℝ) : ℝ ⧸ Kr) = 0 := (QuotientAddGroup.eq_zero_iff _).2 (hPall u i j)
    simp only [P, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add] at h1
    simp only [c]
    rw [← sub_eq_zero, ← h1]
    abel
  obtain ⟨φ, hφ⟩ := exists_potential_of_closed c hcl
  let ψ : Offset → ℝ := fun u => Quotient.out (φ u)
  have hψ : ∀ u, ((ψ u : ℝ) : ℝ ⧸ Kr) = φ u := fun u => QuotientAddGroup.out_eq' _
  have hmem : ∀ u i, ψ (u + latticeStep i) - ψ u - ρ u i ∈ Kr := by
    intro u i
    apply (QuotientAddGroup.eq_zero_iff _).1
    rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_sub, hψ, hψ, hφ u i]
    simp [c]
  refine ⟨fun z => expUnit (ψ (offsetFrom Y z) • X), ?_⟩
  intro b hb
  obtain ⟨u, i⟩ := b
  have h1 : ∀ k, 2 * |u k| < n := by
    intro k
    have := hb.1 k
    simp only at this
    omega
  have h2 : ∀ k, 2 * |(u + latticeStep i) k| < n := by
    intro k
    have := hb.2 k
    simp only [latticeStep] at *
    omega
  have e1 : offsetFrom Y (Y + siteOfInt u) = u := offsetFrom_add_siteOfInt Y u h1
  have e2 : offsetFrom Y (Y + siteOfInt u + unitStep n i) = u + latticeStep i := by
    rw [add_siteOfInt_unitStep]
    exact offsetFrom_add_siteOfInt Y _ h2
  simp only [bondFrom, gaugeTransform, e1, e2, hθ, expUnit_smul_inv, expUnit_smul_mul]
  apply expUnit_eq_of_sub_mem
  have h3 := Kr.neg_mem (hmem u i)
  have e3 : ψ u + θ (Y + siteOfInt u) i + -ψ (u + latticeStep i) - γ * β (u, i) =
      -(ψ (u + latticeStep i) - ψ u - ρ u i) := by
    simp only [ρ]
    ring
  rw [e3]
  exact h3
end RotationStep
section Conj
theorem star_mul_self_unit (g : UnitQuaternion) : star (g : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 :=
  (Unitary.mem_iff.mp g.2).1
theorem mul_star_self_unit (g : UnitQuaternion) : (g : ℍ[ℝ]) * star (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.BlockAverages.GaugeChangeDensity.unitQuaternion_mul_star <;> assumption
theorem re_conj (g : UnitQuaternion) (w : ℍ[ℝ]) : ((g : ℍ[ℝ]) * w * star (g : ℍ[ℝ])).re = w.re := by
  have hc : ∀ a b : ℍ[ℝ], (a * b).re = (b * a).re := by
    intro a b
    simp only [Quaternion.re_mul]
    ring
  rw [hc, ← mul_assoc, star_mul_self_unit, one_mul]
def conjAction (g : UnitQuaternion) : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions where
  toFun w := ⟨(g : ℍ[ℝ]) * (w : ℍ[ℝ]) * star (g : ℍ[ℝ]), by
    show ((g : ℍ[ℝ]) * (w : ℍ[ℝ]) * star (g : ℍ[ℝ])).re = 0
    rw [re_conj]
    exact w.2⟩
  map_add' a b := by
    apply Subtype.ext
    simp [mul_add, add_mul]
  map_smul' c a := by
    apply Subtype.ext
    simp
theorem coe_conjAction (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ((conjAction g w : imaginaryQuaternions) : ℍ[ℝ]) = (g : ℍ[ℝ]) * (w : ℍ[ℝ]) * star (g : ℍ[ℝ]) := rfl
theorem conj_expUnit (g : UnitQuaternion) (w : imaginaryQuaternions) :
    g * expUnit w * g⁻¹ = expUnit (conjAction g w) := by
  let +nondep : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ ℍ[ℝ]
  apply Subtype.ext
  have h1 := NormedSpace.exp_units_conj (Unitary.toUnits g) (w : ℍ[ℝ])
  have e : (((Unitary.toUnits g)⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
  have e0 : ((Unitary.toUnits g : ℍ[ℝ]ˣ) : ℍ[ℝ]) = (g : ℍ[ℝ]) := rfl
  rw [e, e0] at h1
  rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_expUnit, coe_expUnit, coe_conjAction, h1,
    coe_inv_unitQuaternion]
def unitOfImaginary (w : imaginaryQuaternions) (hw : ‖w‖ = 1) : UnitQuaternion := ⟨(w : ℍ[ℝ]), by
  have h2 : ‖(w : ℍ[ℝ])‖ = 1 := hw
  have hs : Quaternion.normSq (w : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, h2]
    norm_num
  rw [Unitary.mem_iff]
  constructor
  · rw [Quaternion.star_mul_self, hs]
    simp
  · rw [Quaternion.self_mul_star, hs]
    simp⟩
theorem mul_comm_neg_of_orthogonal (q w : ℍ[ℝ]) (hq : q.re = 0) (hw : w.re = 0)
    (h : q.imI * w.imI + q.imJ * w.imJ + q.imK * w.imK = 0) : w * q = -(q * w) := by
  apply Quaternion.ext <;>
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg, hq, hw]
  · linear_combination (-2) * h
  all_goals ring
theorem conjAction_of_orthogonal (X w : imaginaryQuaternions) (hw : ‖w‖ = 1)
    (h : (X : ℍ[ℝ]).imI * (w : ℍ[ℝ]).imI + (X : ℍ[ℝ]).imJ * (w : ℍ[ℝ]).imJ +
      (X : ℍ[ℝ]).imK * (w : ℍ[ℝ]).imK = 0) : conjAction (unitOfImaginary w hw) X = -X := by
  apply Subtype.ext
  have h1 := mul_comm_neg_of_orthogonal (X : ℍ[ℝ]) (w : ℍ[ℝ]) X.2 w.2 h
  have h2 : ((conjAction (unitOfImaginary w hw) X : imaginaryQuaternions) : ℍ[ℝ]) =
      (w : ℍ[ℝ]) * (X : ℍ[ℝ]) * star (w : ℍ[ℝ]) := rfl
  have h3 : (w : ℍ[ℝ]) * star (w : ℍ[ℝ]) = 1 := mul_star_self_unit (unitOfImaginary w hw)
  rw [h2, h1, neg_mul, mul_assoc, h3, mul_one]
  simp
theorem exists_conjAction_neg (X : imaginaryQuaternions) : ∃ u : UnitQuaternion, conjAction u X = -X := by
  set a := (X : ℍ[ℝ]).imI with ha
  set b := (X : ℍ[ℝ]).imJ with hb
  by_cases hab : a = 0 ∧ b = 0
  · refine ⟨unitOfImaginary quatI norm_quatI, conjAction_of_orthogonal X quatI norm_quatI ?_⟩
    simp [quatI, ← ha, ← hb, hab.1]
  · have hs : 0 < a ^ 2 + b ^ 2 := by
      by_contra hc
      have h1 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      have h2 : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      exact hab ⟨h1, h2⟩
    set s := Real.sqrt (a ^ 2 + b ^ 2) with hsd
    have hs0 : 0 < s := Real.sqrt_pos.2 hs
    have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hs.le
    let w : imaginaryQuaternions := ⟨⟨0, -b / s, a / s, 0⟩, rfl⟩
    have hw : ‖w‖ = 1 := by
      apply norm_eq_one_of_sq_eq_one
      rw [sq_norm_imaginary]
      simp only [w]
      field_simp
      nlinarith
    refine ⟨unitOfImaginary w hw, conjAction_of_orthogonal X w hw ?_⟩
    simp only [w, ← ha, ← hb]
    field_simp
    ring
theorem gaugeTransform_flip_fieldAlong {n : ℕ} {X : imaginaryQuaternions} {u : UnitQuaternion}
    (hu : conjAction u X = -X) (a : TorusBond n → ℝ) :
    gaugeTransform (fun _ => u) (fieldAlong X a) = fieldAlong X (-a) := by
  funext x i
  simp only [gaugeTransform, fieldAlong]
  rw [conj_expUnit, map_smul, hu]
  simp only [Pi.neg_apply, smul_neg]
  exact congrArg expUnit (neg_smul _ _).symm
end Conj
section Cut
variable {n : ℕ}
open Classical in
def cutAngles (Y : TorusSite n) (r : ℕ) (β : OffsetBond → ℝ) (b : TorusBond n) : ℝ :=
  if BondOffsetInBox r (offsetBond Y b) then β (offsetBond Y b) else 0
open Classical in
def offsetBoxBonds (r : ℕ) : Finset OffsetBond :=
  ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(r : ℤ)) r) ×ˢ Finset.univ).filter (BondOffsetInBox r)
theorem mem_offsetBoxBonds {r : ℕ} {u : OffsetBond} : u ∈ offsetBoxBonds r ↔ BondOffsetInBox r u := by
  simp only [offsetBoxBonds, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc,
    Finset.mem_univ, and_true]
  exact ⟨fun h => h.2, fun h => ⟨fun i => abs_le.1 (h.1 i), h⟩⟩
variable [NeZero n]
theorem abs_cutAngles_le_growth {Y : TorusSite n} {r : ℕ} {β : OffsetBond → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ b, |β b| ≤ K * (1 + (offsetSupNorm b.1 : ℝ))) (b : TorusBond n) :
    |cutAngles Y r β b| ≤ K * (1 + (offsetSupNorm (offsetBond Y b).1 : ℝ)) := by
  unfold cutAngles
  split_ifs with hb
  · exact hK _
  · simp only [abs_zero]
    positivity
theorem abs_cutAngles_le {Y : TorusSite n} {r : ℕ} {β : OffsetBond → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ b, |β b| ≤ K * (1 + (offsetSupNorm b.1 : ℝ))) (b : TorusBond n) :
    |cutAngles Y r β b| ≤ K * (1 + (r : ℝ)) := by
  unfold cutAngles
  split_ifs with hb
  · refine (hK _).trans ?_
    have : (offsetSupNorm (offsetBond Y b).1 : ℝ) ≤ r := by exact_mod_cast offsetSupNorm_le_of_inBox hb.1
    exact mul_le_mul_of_nonneg_left (by linarith) hK0
  · simp only [abs_zero]
    positivity
theorem cutAngles_bondFrom {Y : TorusSite n} {r : ℕ} (β : OffsetBond → ℝ) (hr : 2 * r < n) (b : OffsetBond)
    (hb : BondOffsetInBox r b) : cutAngles Y r β (bondFrom Y b) = β b := by
  have h1 : ∀ k, 2 * |b.1 k| < n := by
    intro k
    have := hb.1 k
    omega
  unfold cutAngles
  rw [offsetBond_bondFrom Y b h1, if_pos hb]
theorem isCold_cutAngles {Y : TorusSite n} {r : ℕ} {β : OffsetBond → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ b, |β b| ≤ K * (1 + (offsetSupNorm b.1 : ℝ))) {X : imaginaryQuaternions} (hX : ‖X‖ = 1)
    {t s : ℝ} (hc : 4 * (|t| * (K * (1 + (r : ℝ)))) < s) :
    IsCold s (fieldAlong X (t • cutAngles Y r β)) := by
  intro x μ ν _
  refine lt_of_le_of_lt (curvature_fieldAlong_le X hX _ x μ ν) (lt_of_le_of_lt ?_ hc)
  have hb : ∀ b : TorusBond n, |(t • cutAngles Y r β) b| ≤ |t| * (K * (1 + (r : ℝ))) := by
    intro b
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_cutAngles_le hK0 hK b) (abs_nonneg t)
  have h1 := abs_le.1 (hb (x, μ))
  have h2 := abs_le.1 (hb (x + unitStep n μ, ν))
  have h3 := abs_le.1 (hb (x + unitStep n ν, μ))
  have h4 := abs_le.1 (hb (x, ν))
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
theorem sum_cutAngles_mul (Y : TorusSite n) (r : ℕ) (β : OffsetBond → ℝ) (F : TorusBond n → ℝ)
    (hr : 2 * r < n) :
    ∑ b, cutAngles Y r β b * F b = ∑ u ∈ offsetBoxBonds r, β u * F (bondFrom Y u) := by
  classical
  have e : ∑ b, cutAngles Y r β b * F b =
      ∑ b ∈ Finset.univ.filter (fun b => BondOffsetInBox r (offsetBond Y b)), β (offsetBond Y b) * F b := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold cutAngles
    split_ifs <;> simp
  rw [e]
  have hin : ∀ u ∈ offsetBoxBonds r, ∀ k, 2 * |u.1 k| < n := by
    intro u hu k
    have := (mem_offsetBoxBonds.1 hu).1 k
    omega
  refine Finset.sum_nbij' (offsetBond Y) (bondFrom Y) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    exact mem_offsetBoxBonds.2 (Finset.mem_filter.1 hb).2
  · intro u hu
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [offsetBond_bondFrom Y u (hin u hu)]
    exact mem_offsetBoxBonds.1 hu
  · intro b _
    exact bondFrom_offsetBond Y b
  · intro u hu
    exact offsetBond_bondFrom Y u (hin u hu)
  · intro b _
    rw [bondFrom_offsetBond]
end Cut
section Expansion
variable {ℓ : StepParameters} {d : ℕ} {C : ℝ} {h : LocalDensity}
theorem third_deriv_bound (hF : IsCurvatureFamilyOnMultiples ℓ d C h) (hC0 : 0 ≤ C) {n : ℕ} [NeZero n]
    (hn : ℓ.n₀ ≤ n) (hd : d ∣ n)
    (Y : TorusSite n) (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (p α : TorusBond n → ℝ)
    (hc : IsCold ℓ.threshold (fieldAlong X p)) (hr : 0 ≤ ℓ.weightRate) :
    |iteratedFDeriv ℝ 3 (valueAlong (h n Y) X) p (fun _ => α)| ≤
      C * (∑ b : TorusBond n, |α b| * Real.exp (-(ℓ.weightRate / 3) * _root_.YangMills.Construction.TorusFields.supDist Y b.1)) ^ 3 := by
  classical
  have hsm := hF.smooth n hn hd Y _ hc
  rw [multilinear_apply_const_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have term : ∀ c : Fin 3 → TorusBond n,
      |(∏ l, α (c l)) * iteratedFDeriv ℝ 3 (valueAlong (h n Y) X) p (fun l => Pi.single (c l) 1)| ≤
        C * ∏ l, (|α (c l)| * Real.exp (-(ℓ.weightRate / 3) * _root_.YangMills.Construction.TorusFields.supDist Y (c l).1)) := by
    intro c
    rw [← mixedDeriv_fieldAlong (h n Y) X p hsm le_rfl c, abs_mul, Finset.abs_prod]
    have hd := hF.decay n hn hd Y _ hc 3 c (fun _ => X) (by norm_num) le_rfl (fun _ => hX)
    have hw := div_weight_le_exp (ℓ := ℓ) hC0 (supportDiam Y c)
    have hle : ∀ l, (_root_.YangMills.Construction.TorusFields.supDist Y (c l).1 : ℝ) ≤ supportDiam Y c := by
      intro l
      have : _root_.YangMills.Construction.TorusFields.supDist Y (c l).1 ≤ supportDiam Y c :=
        le_max_of_le_left (Finset.le_sup (f := fun l : Fin 3 => _root_.YangMills.Construction.TorusFields.supDist Y (c l).1) (Finset.mem_univ l))
      exact_mod_cast this
    have hexp : Real.exp (-ℓ.weightRate * supportDiam Y c) ≤
        ∏ l, Real.exp (-(ℓ.weightRate / 3) * _root_.YangMills.Construction.TorusFields.supDist Y (c l).1) := by
      rw [← Real.exp_sum]
      apply Real.exp_le_exp.2
      rw [Fin.sum_univ_three]
      nlinarith [hle 0, hle 1, hle 2]
    rw [Finset.prod_mul_distrib]
    calc (∏ l, |α (c l)|) * |mixedDeriv (h n Y) (fieldAlong X p) c fun _ => X|
        ≤ (∏ l, |α (c l)|) * (C * ∏ l, Real.exp (-(ℓ.weightRate / 3) * _root_.YangMills.Construction.TorusFields.supDist Y (c l).1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun l _ => abs_nonneg _)
          exact hd.trans (hw.trans (mul_le_mul_of_nonneg_left hexp hC0))
      _ = _ := by ring
  calc ∑ c : Fin 3 → TorusBond n, |(∏ l, α (c l)) *
        iteratedFDeriv ℝ 3 (valueAlong (h n Y) X) p (fun l => Pi.single (c l) 1)|
      ≤ ∑ c : Fin 3 → TorusBond n,
          C * ∏ l, (|α (c l)| * Real.exp (-(ℓ.weightRate / 3) * _root_.YangMills.Construction.TorusFields.supDist Y (c l).1)) :=
        Finset.sum_le_sum fun c _ => term c
    _ = C * ∑ c : Fin 3 → TorusBond n,
          ∏ l, (|α (c l)| * Real.exp (-(ℓ.weightRate / 3) * _root_.YangMills.Construction.TorusFields.supDist Y (c l).1)) := by
        rw [Finset.mul_sum]
    _ = C * (∑ b : TorusBond n, |α b| * Real.exp (-(ℓ.weightRate / 3) * _root_.YangMills.Construction.TorusFields.supDist Y b.1)) ^ 3 := by
        congr 1
        have := Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset (TorusBond n)))
          (fun _ b => |α b| * Real.exp (-(ℓ.weightRate / 3) * _root_.YangMills.Construction.TorusFields.supDist Y b.1))
        rw [Fintype.piFinset_univ] at this
        rw [← this]
        simp
theorem second_deriv_expand (hF : IsCurvatureFamilyOnMultiples ℓ d C h) {n : ℕ} [NeZero n] (hn : ℓ.n₀ ≤ n)
    (hd : d ∣ n) (hσ : 0 < ℓ.threshold)
    (Y : TorusSite n) (X : imaginaryQuaternions) (α : TorusBond n → ℝ) :
    iteratedFDeriv ℝ 2 (valueAlong (h n Y) X) 0 (fun _ => α) =
      ∑ b, ∑ b', α b * α b' * mixedDeriv (h n Y) (trivialField n) ![b, b'] ![X, X] := by
  classical
  have hc : IsCold ℓ.threshold (fieldAlong X (0 : TorusBond n → ℝ)) := by
    rw [fieldAlong_zero]
    intro x μ ν _
    simpa [curvature, holonomy, trivialField] using hσ
  have hsm := hF.smooth n hn hd Y _ hc
  rw [multilinear_apply_const_eq_sum, ← Fintype.sum_prod_type'
    (f := fun b b' => α b * α b' * mixedDeriv (h n Y) (trivialField n) ![b, b'] ![X, X])]
  refine Fintype.sum_equiv (finTwoArrowEquiv (TorusBond n)) _ _ fun c => ?_
  have e1 : (fun _ : Fin 2 => X) = ![X, X] := by
    funext l
    fin_cases l <;> rfl
  have e2 : c = ![c 0, c 1] := by
    funext l
    fin_cases l <;> rfl
  rw [← mixedDeriv_fieldAlong (h n Y) X 0 hsm (by norm_num) c, fieldAlong_zero, e1, Fin.prod_univ_two]
  show _ = α (c 0) * α (c 1) * mixedDeriv (h n Y) (trivialField n) ![c 0, c 1] ![X, X]
  rw [← e2]
theorem centered_second_order (hF : IsCurvatureFamilyOnMultiples ℓ d C h) (hC0 : 0 ≤ C) {n : ℕ} [NeZero n]
    (hn : ℓ.n₀ ≤ n) (hd : d ∣ n)
    (hrate : 0 ≤ ℓ.weightRate) (Y : TorusSite n) (X : imaginaryQuaternions) (hX : ‖X‖ = 1)
    (α : TorusBond n → ℝ) {γ : ℝ} (hγ : 0 < γ)
    (hcold : ∀ t : ℝ, |t| ≤ γ → IsCold ℓ.threshold (fieldAlong X (t • α))) :
    |centered h n Y (fieldAlong X (γ • α)) -
        γ ^ 2 / 2 * iteratedFDeriv ℝ 2 (valueAlong (h n Y) X) 0 (fun _ => α)| ≤
      (C * (∑ b : TorusBond n, |α b| * Real.exp (-(ℓ.weightRate / 3) * _root_.YangMills.Construction.TorusFields.supDist Y b.1)) ^ 3) * γ ^ 3 / 2 := by
  set g : ℝ → ℝ := fun t => valueAlong (h n Y) X (t • α) with hg
  have hsm : ∀ t : ℝ, |t| ≤ γ → ContDiffAt ℝ 3 (valueAlong (h n Y) X) (t • α) := fun t ht =>
    contDiffAt_valueAlong _ _ _ (hF.smooth n hn hd Y _ (hcold t ht))
  have hline : ∀ t : ℝ, ContDiffAt ℝ 3 (fun s : ℝ => s • α) t := fun t =>
    (contDiff_id.smul contDiff_const).contDiffAt
  have hIcc : ∀ t ∈ Set.Icc 0 γ, |t| ≤ γ := fun t ht => by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have hC : ∀ t ∈ Set.Icc 0 γ, ContDiffAt ℝ 3 g t := fun t ht =>
    ContDiffAt.comp (g := valueAlong (h n Y) X) (f := fun s : ℝ => s • α) t (hsm t (hIcc t ht)) (hline t)
  have hM : ∀ t ∈ Set.Icc 0 γ, |iteratedDeriv 3 g t| ≤
      C * (∑ b : TorusBond n, |α b| * Real.exp (-(ℓ.weightRate / 3) * _root_.YangMills.Construction.TorusFields.supDist Y b.1)) ^ 3 := fun t ht => by
    rw [hg, iteratedDeriv_along_line _ α t le_rfl (hsm t (hIcc t ht))]
    exact third_deriv_bound hF hC0 hn hd Y X hX _ α (hcold t (hIcc t ht)) hrate
  have h1 := taylor_second_order_bound g hγ hC hM
  obtain ⟨u, hu⟩ := exists_conjAction_neg X
  have heven : g =ᶠ[nhds 0] fun t => g (-t) := by
    have : ∀ᶠ t : ℝ in nhds 0, |t| < γ := by
      have := (continuous_abs.tendsto (0 : ℝ)).eventually (gt_mem_nhds (by simpa using hγ))
      simpa using this
    filter_upwards [this] with t ht
    simp only [hg, valueAlong]
    have e : fieldAlong X ((-t) • α) = gaugeTransform (fun _ => u) (fieldAlong X (t • α)) := by
      rw [gaugeTransform_flip_fieldAlong hu]
      congr 1
      simp
    rw [e, hF.gauge n hn hd Y _ _ (hcold t ht.le)]
  have hd : iteratedDeriv 1 g 0 = 0 := by
    rw [iteratedDeriv_one]
    have e1 := heven.deriv_eq
    have e2 := deriv_comp_neg g (0 : ℝ)
    simp only [neg_zero] at e2
    linarith
  have h20 : iteratedDeriv 2 g 0 = iteratedFDeriv ℝ 2 (valueAlong (h n Y) X) 0 (fun _ => α) := by
    rw [hg, iteratedDeriv_along_line _ α 0 (by norm_num) (hsm 0 (by simpa using hγ.le))]
    simp
  have hg0 : g 0 = h n Y (trivialField n) := by
    simp only [hg, valueAlong, zero_smul, fieldAlong_zero]
  have hgγ : g γ = h n Y (fieldAlong X (γ • α)) := rfl
  rw [hd, h20, hg0, hgγ] at h1
  simpa [centered] using h1
end Expansion
section Cold
variable {n : ℕ}
theorem isCold_trivialField {s : ℝ} (hs : 0 < s) : IsCold s (trivialField n) := by
  intro x μ ν _
  simpa [curvature, holonomy, trivialField] using hs
theorem eventually_isCold_perturb [NeZero n] {s : ℝ} {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (W : TorusField n)
    (hW : IsCold s W) : ∀ᶠ σ in nhds (0 : Fin k → ℝ), IsCold s (perturb c X σ W) := by
  have h1 : ∀ (x : TorusSite n) (μ ν : Fin 4), ∀ᶠ σ in nhds (0 : Fin k → ℝ),
      μ < ν → curvature (perturb c X σ W) x μ ν < s := by
    intro x μ ν
    by_cases hμ : μ < ν
    · have hc : Continuous fun σ : Fin k → ℝ => curvature (perturb c X σ W) x μ ν :=
        (continuous_curvature x μ ν).comp (continuous_perturb c X W)
      have h2 := hc.tendsto 0
      simp only [perturb_at_zero] at h2
      filter_upwards [h2.eventually (gt_mem_nhds (hW x μ ν hμ))] with σ hσ _ using hσ
    · exact Filter.Eventually.of_forall fun σ h => absurd h hμ
  simp only [IsCold]
  rw [Filter.eventually_all]
  intro x
  rw [Filter.eventually_all]
  intro μ
  rw [Filter.eventually_all]
  exact fun ν => h1 x μ ν
end Cold
section Bilinear
variable {n : ℕ}
theorem mixedDeriv_swap (G : TorusField n → ℝ) (W : TorusField n) (hG : ContDiffThreeAt G W)
    (b b' : TorusBond n) (X X' : imaginaryQuaternions) :
    mixedDeriv G W ![b, b'] ![X, X'] = mixedDeriv G W ![b', b] ![X', X] := by
  let L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (1 - l)
  set F : (Fin 2 → ℝ) → ℝ := fun τ => G (perturb ![b, b'] ![X, X'] τ W) with hFd
  have e1 : (fun σ => G (perturb ![b', b] ![X', X] σ W)) = fun σ => F (L σ) := by
    funext σ
    have e0 : perturb ![b', b] ![X', X] σ W = perturb ![b, b'] ![X, X'] (L σ) W := by
      funext x i
      simp only [perturb, Fin.sum_univ_two]
      simp [L, add_comm]
      rfl
    simp only [hFd, e0]
  have hF : ContDiffAt ℝ 3 F (L 0) := by simpa [hFd] using hG 2 ![b, b'] ![X, X']
  have hF0 : ContDiffAt ℝ 3 F 0 := by simpa using hF
  unfold mixedDeriv
  rw [e1, iteratedFDeriv_comp_linear F L 0 (by norm_num) hF, map_zero, iteratedFDeriv_two_apply,
    iteratedFDeriv_two_apply]
  have hs := hF0.isSymmSndFDerivAt (by
    simp
    first
      | norm_num
      | exact_mod_cast (show (2 : ℕ) ≤ 3 by norm_num))
  rw [hs]
  have e2 : L (Pi.single 1 1) = (Pi.single 0 1 : Fin 2 → ℝ) := by
    ext l
    fin_cases l <;> simp [L]
  have e3 : L (Pi.single 0 1) = (Pi.single 1 1 : Fin 2 → ℝ) := by
    ext l
    fin_cases l <;> simp [L]
  simp only [e2, e3]
theorem mixedDeriv_add_right (G : TorusField n → ℝ) (W : TorusField n) (hG : ContDiffThreeAt G W)
    (b b' : TorusBond n) (X X₁ X₂ : imaginaryQuaternions) :
    mixedDeriv G W ![b, b'] ![X, X₁ + X₂] =
      mixedDeriv G W ![b, b'] ![X, X₁] + mixedDeriv G W ![b, b'] ![X, X₂] := by
  set F : (Fin 3 → ℝ) → ℝ := fun τ => G (perturb ![b, b', b'] ![X, X₁, X₂] τ W) with hFd
  have hF : ContDiffAt ℝ 3 F 0 := hG 3 ![b, b', b'] ![X, X₁, X₂]
  let L : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi
    ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 1]
  let L₁ : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi
    ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1, 0]
  let L₂ : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi
    ![ContinuousLinearMap.proj 0, 0, ContinuousLinearMap.proj 1]
  have e0 : (fun σ => G (perturb ![b, b'] ![X, X₁ + X₂] σ W)) = fun σ => F (L σ) := by
    funext σ
    have : perturb ![b, b'] ![X, X₁ + X₂] σ W = perturb ![b, b', b'] ![X, X₁, X₂] (L σ) W := by
      funext x i
      simp only [perturb, Fin.sum_univ_two, Fin.sum_univ_three]
      congr 2
      by_cases h1 : b = (x, i) <;> by_cases h2 : b' = (x, i) <;> simp [L, h1, h2, smul_add, add_assoc]
    simp only [hFd, this]
  have e1 : (fun σ => G (perturb ![b, b'] ![X, X₁] σ W)) = fun σ => F (L₁ σ) := by
    funext σ
    have : perturb ![b, b'] ![X, X₁] σ W = perturb ![b, b', b'] ![X, X₁, X₂] (L₁ σ) W := by
      funext x i
      simp only [perturb, Fin.sum_univ_two, Fin.sum_univ_three]
      congr 2
      by_cases h1 : b = (x, i) <;> by_cases h2 : b' = (x, i) <;> simp [L₁, h1, h2]
    simp only [hFd, this]
  have e2 : (fun σ => G (perturb ![b, b'] ![X, X₂] σ W)) = fun σ => F (L₂ σ) := by
    funext σ
    have : perturb ![b, b'] ![X, X₂] σ W = perturb ![b, b', b'] ![X, X₁, X₂] (L₂ σ) W := by
      funext x i
      simp only [perturb, Fin.sum_univ_two, Fin.sum_univ_three]
      congr 2
      by_cases h1 : b = (x, i) <;> by_cases h2 : b' = (x, i) <;> simp [L₂, h1, h2]
    simp only [hFd, this]
  have hL : ∀ M : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ), ContDiffAt ℝ 3 F (M 0) := fun M => by simpa using hF
  unfold mixedDeriv
  rw [e0, e1, e2, iteratedFDeriv_comp_linear F L 0 (by norm_num) (hL L),
    iteratedFDeriv_comp_linear F L₁ 0 (by norm_num) (hL L₁),
    iteratedFDeriv_comp_linear F L₂ 0 (by norm_num) (hL L₂)]
  simp only [map_zero, iteratedFDeriv_two_apply]
  have a0 : L (Pi.single 0 1) = L₁ (Pi.single 0 1) := by
    ext l
    fin_cases l <;> simp [L, L₁]
  have a0' : L (Pi.single 0 1) = L₂ (Pi.single 0 1) := by
    ext l
    fin_cases l <;> simp [L, L₂]
  have a1 : L (Pi.single 1 1) = L₁ (Pi.single 1 1) + L₂ (Pi.single 1 1) := by
    ext l
    fin_cases l <;> simp [L, L₁, L₂]
  rw [a1, map_add]
  rw [← a0, ← a0']
end Bilinear
section Limits
variable {ℓ : StepParameters} {d : ℕ} {C : ℝ} {h : LocalDensity}
theorem neZero_of_n₀_le (hfit : ℓ.Admissible) {n : ℕ} (hn : ℓ.n₀ ≤ n) : NeZero n :=
  ⟨by have := hfit.n₀_ge; omega⟩
theorem n₀_le_mul (hd0 : 0 < d) {m : ℕ} (hm : ℓ.n₀ ≤ m) : ℓ.n₀ ≤ d * m :=
  hm.trans (Nat.le_mul_of_pos_left m hd0)
theorem constant_nonneg (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h) :
    0 ≤ C := by
  have hn := n₀_le_mul (ℓ := ℓ) hd0 (le_refl ℓ.n₀)
  have := neZero_of_n₀_le hfit hn
  have h1 := hF.decay (d * ℓ.n₀) hn (dvd_mul_right _ _) 0 (trivialField _) (isCold_trivialField hfit.σ_pos) 1
    (fun _ => (0, 0)) (fun _ => quatI) le_rfl (by norm_num) (fun _ => norm_quatI)
  have h2 := (abs_nonneg _).trans h1
  have hw := stepWeight_pos (ℓ := ℓ)
    (supportDiam (0 : TorusSite (d * ℓ.n₀)) (fun _ : Fin 1 => ((0, 0) : TorusBond (d * ℓ.n₀))))
  by_contra hc
  exact absurd h2 (not_le.2 (div_neg_of_neg_of_pos (not_le.1 hc) hw))
theorem contDiffThreeAt_trivialField (hfit : ℓ.Admissible) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    {n : ℕ} [NeZero n] (hn : ℓ.n₀ ≤ n) (hd : d ∣ n) (y : TorusSite n) :
    ContDiffThreeAt (h n y) (trivialField n) :=
  hF.smooth n hn hd y _ (isCold_trivialField hfit.σ_pos)
theorem bondOffsetInBox_of_le {m : ℕ} {c : OffsetBond} (hm : offsetSupNorm c.1 + 1 ≤ m) :
    BondOffsetInBox m c := by
  have h1 : ∀ i, |c.1 i| ≤ (offsetSupNorm c.1 : ℤ) := by
    intro i
    rw [Int.abs_eq_natAbs]
    exact_mod_cast natAbs_le_offsetSupNorm c.1 i
  constructor
  · intro i
    have := h1 i
    omega
  · intro i
    have h2 := h1 i
    have h3 : |(Pi.single c.2 1 : Fin 4 → ℤ) i| ≤ 1 := by
      by_cases hi : i = c.2
      · subst hi
        simp
      · simp [hi]
    have h4 := abs_add_le (c.1 i) ((Pi.single c.2 1 : Fin 4 → ℤ) i)
    simp only [Pi.add_apply]
    omega
theorem flatSecondDeriv_close (hfit : ℓ.Admissible) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    {m n n' : ℕ} (hn : ℓ.n₀ ≤ n)
    (hn' : ℓ.n₀ ≤ n') (hd : d ∣ n) (hd' : d ∣ n') (hm : 2 * m + 2 < n) (hm' : 2 * m + 2 < n')
    {c c' : OffsetBond} (hc : BondOffsetInBox m c) (hc' : BondOffsetInBox m c')
    {X X' : imaginaryQuaternions} (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) :
    |flatSecondDeriv h n c c' X X' - flatSecondDeriv h n' c c' X X'| ≤ C / ℓ.weight m := by
  have := neZero_of_n₀_le hfit hn
  have := neZero_of_n₀_le hfit hn'
  have h1 := hF.local_density n n' hn hn' hd hd' 0 0 (trivialField n) (trivialField n') m hm hm'
    (isCold_trivialField hfit.σ_pos)
    (isCold_trivialField hfit.σ_pos) (fun _ _ => rfl) 2 ![c, c'] ![X, X'] le_rfl
    (fun l => by fin_cases l <;> assumption)
    (fun l => by fin_cases l <;> assumption)
  have e : ∀ (k : ℕ) [NeZero k], (fun l => bondFrom (0 : TorusSite k) ((![c, c'] : Fin 2 → OffsetBond) l)) =
      ![bondFrom 0 c, bondFrom 0 c'] := by
    intro k _
    funext l
    fin_cases l <;> rfl
  rw [e n, e n'] at h1
  have e2 : ∀ (k : ℕ), mixedDeriv (centered h k 0) (trivialField k) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] =
      flatSecondDeriv h k c c' X X' := by
    intro k
    exact mixedDeriv_sub_const (by norm_num) (h k 0) (h k 0 (trivialField k)) _ _ _
  rw [e2, e2] at h1
  exact h1
theorem tendsto_flatSecondDeriv_units (hfit : ℓ.Admissible) (hd0 : 0 < d)
    (hF : IsCurvatureFamilyOnMultiples ℓ d C h) (c c' : OffsetBond)
    {X X' : imaginaryQuaternions} (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) :
    Filter.Tendsto (fun m => flatSecondDeriv h (d * m) c c' X X') Filter.atTop
      (nhds (secondDerivLimitOnMultiples d h c c' X X')) := by
  have hC0 := constant_nonneg hfit hd0 hF
  have hc : CauchySeq fun m => flatSecondDeriv h (d * m) c c' X X' := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨m₀, hm₀⟩ := exists_const_mul_exp_lt (weightRate_pos hfit) C hε
    set m := max m₀ (offsetSupNorm c.1 + offsetSupNorm c'.1 + 1) with hm
    refine ⟨max ℓ.n₀ (2 * m + 3), fun n hn n' hn' => ?_⟩
    have a1 := le_of_max_le_left hn
    have a2 := le_of_max_le_right hn
    have a3 := le_of_max_le_left hn'
    have a4 := le_of_max_le_right hn'
    have a5 : n ≤ d * n := Nat.le_mul_of_pos_left n hd0
    have a6 : n' ≤ d * n' := Nat.le_mul_of_pos_left n' hd0
    have b1 : BondOffsetInBox m c := bondOffsetInBox_of_le (by omega)
    have b2 : BondOffsetInBox m c' := bondOffsetInBox_of_le (by omega)
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (flatSecondDeriv_close hfit hF (n₀_le_mul hd0 a1) (n₀_le_mul hd0 a3)
        (dvd_mul_right _ _) (dvd_mul_right _ _) (by omega) (by omega) b1 b2 hX hX')
      (lt_of_le_of_lt (div_weight_le_exp hC0 m) (hm₀ m (le_max_left _ _)))
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  have e : secondDerivLimitOnMultiples d h c c' X X' = a := ha.limUnder_eq
  rw [e]
  exact ha
theorem tendsto_flatSecondDeriv (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    (c c' : OffsetBond) (X X' : imaginaryQuaternions) :
    Filter.Tendsto (fun m => flatSecondDeriv h (d * m) c c' X X') Filter.atTop
      (nhds (secondDerivLimitOnMultiples d h c c' X X')) := by
  obtain ⟨a, U, hU, rfl, -⟩ := exists_eq_smul_unit X
  obtain ⟨b, U', hU', rfl, -⟩ := exists_eq_smul_unit X'
  have h1 := (tendsto_flatSecondDeriv_units hfit hd0 hF c c' hU hU').const_mul (a * b)
  have h2 : (fun m => flatSecondDeriv h (d * m) c c' (a • U) (b • U')) =ᶠ[Filter.atTop]
      fun m => a * b * flatSecondDeriv h (d * m) c c' U U' := by
    filter_upwards [Filter.eventually_ge_atTop ℓ.n₀] with m hm
    have hn := n₀_le_mul hd0 hm
    have := neZero_of_n₀_le hfit hn
    exact mixedDeriv_two_smul _ _ (contDiffThreeAt_trivialField hfit hF hn (dvd_mul_right _ _) 0) _ a b U U'
  have h3 := h1.congr' h2.symm
  have e : secondDerivLimitOnMultiples d h c c' (a • U) (b • U') =
      a * b * secondDerivLimitOnMultiples d h c c' U U' := h3.limUnder_eq
  rw [e]
  exact h3
theorem secondDerivLimit_smul (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    (c c' : OffsetBond) (a b : ℝ) (X X' : imaginaryQuaternions) :
    secondDerivLimitOnMultiples d h c c' (a • X) (b • X') = a * b * secondDerivLimitOnMultiples d h c c' X X' := by
  have h1 := tendsto_flatSecondDeriv hfit hd0 hF c c' (a • X) (b • X')
  have h2 := (tendsto_flatSecondDeriv hfit hd0 hF c c' X X').const_mul (a * b)
  have h3 : (fun m => flatSecondDeriv h (d * m) c c' (a • X) (b • X')) =ᶠ[Filter.atTop]
      fun m => a * b * flatSecondDeriv h (d * m) c c' X X' := by
    filter_upwards [Filter.eventually_ge_atTop ℓ.n₀] with m hm
    have hn := n₀_le_mul hd0 hm
    have := neZero_of_n₀_le hfit hn
    exact mixedDeriv_two_smul _ _ (contDiffThreeAt_trivialField hfit hF hn (dvd_mul_right _ _) 0) _ a b X X'
  exact tendsto_nhds_unique (h1.congr' h3) h2
theorem secondDerivLimit_add_right (hfit : ℓ.Admissible) (hd0 : 0 < d)
    (hF : IsCurvatureFamilyOnMultiples ℓ d C h) (c c' : OffsetBond)
    (X X₁ X₂ : imaginaryQuaternions) :
    secondDerivLimitOnMultiples d h c c' X (X₁ + X₂) =
      secondDerivLimitOnMultiples d h c c' X X₁ + secondDerivLimitOnMultiples d h c c' X X₂ := by
  have h1 := tendsto_flatSecondDeriv hfit hd0 hF c c' X (X₁ + X₂)
  have h2 := (tendsto_flatSecondDeriv hfit hd0 hF c c' X X₁).add (tendsto_flatSecondDeriv hfit hd0 hF c c' X X₂)
  have h3 : (fun m => flatSecondDeriv h (d * m) c c' X (X₁ + X₂)) =ᶠ[Filter.atTop]
      fun m => flatSecondDeriv h (d * m) c c' X X₁ + flatSecondDeriv h (d * m) c c' X X₂ := by
    filter_upwards [Filter.eventually_ge_atTop ℓ.n₀] with m hm
    have hn := n₀_le_mul hd0 hm
    have := neZero_of_n₀_le hfit hn
    exact mixedDeriv_add_right _ _ (contDiffThreeAt_trivialField hfit hF hn (dvd_mul_right _ _) 0) _ _ X X₁ X₂
  exact tendsto_nhds_unique (h1.congr' h3) h2
theorem secondDerivLimit_symm (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    (c c' : OffsetBond) (X X' : imaginaryQuaternions) :
    secondDerivLimitOnMultiples d h c c' X X' = secondDerivLimitOnMultiples d h c' c X' X := by
  have h1 := tendsto_flatSecondDeriv hfit hd0 hF c c' X X'
  have h2 := tendsto_flatSecondDeriv hfit hd0 hF c' c X' X
  have h3 : (fun m => flatSecondDeriv h (d * m) c c' X X') =ᶠ[Filter.atTop]
      fun m => flatSecondDeriv h (d * m) c' c X' X := by
    filter_upwards [Filter.eventually_ge_atTop ℓ.n₀] with m hm
    have hn := n₀_le_mul hd0 hm
    have := neZero_of_n₀_le hfit hn
    exact mixedDeriv_swap _ _ (contDiffThreeAt_trivialField hfit hF hn (dvd_mul_right _ _) 0) _ _ X X'
  exact tendsto_nhds_unique (h1.congr' h3) h2
theorem flatSecondDeriv_sub_limit_le (hfit : ℓ.Admissible) (hd0 : 0 < d)
    (hF : IsCurvatureFamilyOnMultiples ℓ d C h) {m n : ℕ}
    (hn : ℓ.n₀ ≤ n) (hd : d ∣ n) (hm : 2 * m + 2 < n) {c c' : OffsetBond} (hc : BondOffsetInBox m c)
    (hc' : BondOffsetInBox m c') {X X' : imaginaryQuaternions} (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) :
    |flatSecondDeriv h n c c' X X' - secondDerivLimitOnMultiples d h c c' X X'| ≤ C / ℓ.weight m := by
  have h1 := (tendsto_flatSecondDeriv_units hfit hd0 hF c c' hX hX').const_sub (flatSecondDeriv h n c c' X X')
  refine le_of_tendsto h1.abs ?_
  filter_upwards [Filter.eventually_ge_atTop (max ℓ.n₀ (2 * m + 3))] with n' hn'
  have a1 := le_of_max_le_left hn'
  have a2 := le_of_max_le_right hn'
  have a3 : n' ≤ d * n' := Nat.le_mul_of_pos_left n' hd0
  exact flatSecondDeriv_close hfit hF hn (n₀_le_mul hd0 a1) hd (dvd_mul_right _ _) hm (by omega) hc hc' hX hX'
end Limits
section Span
variable {n : ℕ} [NeZero n]
theorem supDist_siteOfInt (u : Offset) (hu : ∀ k, 2 * |u k| < n) :
    _root_.YangMills.Construction.TorusFields.supDist (0 : TorusSite n) (0 + siteOfInt u) = offsetSupNorm u := by
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm, _root_.YangMills.Construction.AbelianSecondOrder.supDist_eq_offsetSupNorm, offsetFrom_add_siteOfInt 0 u hu]
theorem supDist_siteOfInt_siteOfInt (u u' : Offset) (hd : ∀ k, 2 * |(u - u') k| < n) :
    _root_.YangMills.Construction.TorusFields.supDist ((0 : TorusSite n) + siteOfInt u) (0 + siteOfInt u') = offsetSupNorm (u - u') := by
  have e : (0 : TorusSite n) + siteOfInt u = (0 + siteOfInt u') + siteOfInt (u - u') := by
    rw [zero_add, zero_add, ← siteOfInt_add]
    congr 1
    abel
  rw [_root_.YangMills.Construction.AbelianSecondOrder.supDist_eq_offsetSupNorm, e, offsetFrom_add_siteOfInt _ _ hd]
theorem finset_sup_fin_two (f : Fin 2 → ℕ) : Finset.univ.sup f = max (f 0) (f 1) := by apply _root_.YangMills.Construction.TorusLumps.SumOfFourCurvature.sup_univ_fin_two <;> assumption
theorem supportDiam_pair (u u' : OffsetBond) (hu : ∀ k, 2 * |u.1 k| < n) (hu' : ∀ k, 2 * |u'.1 k| < n)
    (hd : ∀ k, 2 * |(u.1 - u'.1) k| < n) :
    supportDiam (0 : TorusSite n) ![bondFrom 0 u, bondFrom 0 u'] = offsetTriangleDiameter u.1 u'.1 := by
  have hd' : ∀ k, 2 * |(u'.1 - u.1) k| < n := by
    intro k
    have := hd k
    rwa [Pi.sub_apply, abs_sub_comm, ← Pi.sub_apply] at this
  unfold supportDiam offsetTriangleDiameter
  simp only [finset_sup_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, bondFrom, _root_.YangMills.Construction.TorusFields.supDist_self]
  rw [_root_.YangMills.Construction.AbelianSecondOrder.supDist_siteOfInt _ hu, _root_.YangMills.Construction.AbelianSecondOrder.supDist_siteOfInt _ hu', _root_.YangMills.Construction.AbelianSecondOrder.supDist_siteOfInt_siteOfInt _ _ hd,
    _root_.YangMills.Construction.AbelianSecondOrder.supDist_siteOfInt_siteOfInt _ _ hd']
  have e : offsetSupNorm (u'.1 - u.1) = offsetSupNorm (u.1 - u'.1) := by
    unfold offsetSupNorm
    refine Finset.sup_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]
    omega
  rw [e]
  omega
end Span
section Bounds
variable {ℓ : StepParameters} {d : ℕ} {C : ℝ} {h : LocalDensity}
theorem abs_le_offsetSupNorm (u : Offset) (k : Fin 4) : |u k| ≤ (offsetSupNorm u : ℤ) := by apply _root_.YangMills.Construction.LatticeFractionalIntegration.PowerWeightKernel.abs_apply_le_supNorm <;> assumption
theorem secondDerivLimit_bound_units (hfit : ℓ.Admissible) (hd0 : 0 < d)
    (hF : IsCurvatureFamilyOnMultiples ℓ d C h) (c c' : OffsetBond)
    {X X' : imaginaryQuaternions} (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) :
    |secondDerivLimitOnMultiples d h c c' X X'| ≤ C / ℓ.weight (offsetTriangleDiameter c.1 c'.1) := by
  refine le_of_tendsto (tendsto_flatSecondDeriv_units hfit hd0 hF c c' hX hX').abs ?_
  filter_upwards [Filter.eventually_ge_atTop (max ℓ.n₀ (2 * (offsetSupNorm c.1 + offsetSupNorm c'.1) + 1))]
    with m hm
  have a1' := le_of_max_le_left hm
  have a2' := le_of_max_le_right hm
  have a3 : m ≤ d * m := Nat.le_mul_of_pos_left m hd0
  set n := d * m with hn
  have a1 : ℓ.n₀ ≤ n := a1'.trans a3
  have a2 : 2 * (offsetSupNorm c.1 + offsetSupNorm c'.1) + 1 ≤ n := a2'.trans a3
  have := neZero_of_n₀_le hfit a1
  have b1 : ∀ k, 2 * |c.1 k| < n := fun k => by
    have := abs_le_offsetSupNorm c.1 k
    omega
  have b2 : ∀ k, 2 * |c'.1 k| < n := fun k => by
    have := abs_le_offsetSupNorm c'.1 k
    omega
  have b3 : ∀ k, 2 * |(c.1 - c'.1) k| < n := fun k => by
    have h1 := abs_le_offsetSupNorm c.1 k
    have h2 := abs_le_offsetSupNorm c'.1 k
    have h3 := abs_sub (c.1 k) (c'.1 k)
    simp only [Pi.sub_apply]
    omega
  have h1 := hF.decay n a1 (dvd_mul_right _ _) 0 (trivialField n) (isCold_trivialField hfit.σ_pos) 2
    ![bondFrom 0 c, bondFrom 0 c'] ![X, X']
    (by norm_num) (by norm_num) (fun l => by fin_cases l <;> assumption)
  rw [supportDiam_pair c c' b1 b2 b3] at h1
  exact h1
theorem secondDerivLimit_bound (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    (c c' : OffsetBond) (X X' : imaginaryQuaternions) :
    |secondDerivLimitOnMultiples d h c c' X X'| ≤
      ‖X‖ * ‖X'‖ * (C / ℓ.weight (offsetTriangleDiameter c.1 c'.1)) := by
  obtain ⟨a, U, hU, rfl, ha⟩ := exists_eq_smul_unit X
  obtain ⟨b, U', hU', rfl, hb⟩ := exists_eq_smul_unit X'
  rw [secondDerivLimit_smul hfit hd0 hF, abs_mul, abs_mul, ha, hb]
  exact mul_le_mul_of_nonneg_left (secondDerivLimit_bound_units hfit hd0 hF c c' hU hU')
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
theorem exp_le_split {δ t r s s' : ℝ} (hδ : 0 ≤ δ) (h1 : r ≤ t) (h2 : s ≤ t) (h3 : s' ≤ t) :
    Real.exp (-δ * t) ≤
      Real.exp (-(δ / 2) * r) * (Real.exp (-(δ / 4) * s) * Real.exp (-(δ / 4) * s')) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith
theorem secondDerivLimit_decay (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    (c c' : OffsetBond) (X X' : imaginaryQuaternions) :
    |secondDerivLimitOnMultiples d h c c' X X'| ≤ ‖X‖ * ‖X'‖ * (C * Real.exp (-ℓ.weightRate *
      (max (offsetSupNorm c.1) (offsetSupNorm c'.1) : ℕ))) := by
  have hC0 := constant_nonneg hfit hd0 hF
  refine (secondDerivLimit_bound hfit hd0 hF c c' X X').trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  refine (div_weight_le_exp hC0 _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
  apply Real.exp_le_exp.2
  have h1 : (max (offsetSupNorm c.1) (offsetSupNorm c'.1) : ℕ) ≤ offsetTriangleDiameter c.1 c'.1 :=
    le_max_left _ _
  have h2 : ((max (offsetSupNorm c.1) (offsetSupNorm c'.1) : ℕ) : ℝ) ≤ (offsetTriangleDiameter c.1 c'.1 : ℝ) := by
    exact_mod_cast h1
  have := weightRate_pos hfit
  nlinarith
theorem summable_secondDerivLimit (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    {B B' : OffsetBond → imaginaryQuaternions}
    (hB : HasPolynomialGrowth B) (hB' : HasPolynomialGrowth B') :
    Summable fun cc : OffsetBond × OffsetBond => secondDerivLimitOnMultiples d h cc.1 cc.2 (B cc.1) (B' cc.2) := by
  obtain ⟨K, p, hK⟩ := hB
  obtain ⟨K', p', hK'⟩ := hB'
  have hC0 := constant_nonneg hfit hd0 hF
  have hr := weightRate_pos hfit
  have hw : Summable fun cc : OffsetBond × OffsetBond =>
      decayWeight (ℓ.weightRate / 2) p cc.1 * decayWeight (ℓ.weightRate / 2) p' cc.2 :=
    Summable.mul_of_nonneg (summable_decayWeight (by positivity) p) (summable_decayWeight (by positivity) p')
      (decayWeight_nonneg _ _) (decayWeight_nonneg _ _)
  refine Summable.of_norm_bounded (hw.mul_left (|K| * |K'| * C)) fun cc => ?_
  rw [Real.norm_eq_abs]
  refine (secondDerivLimit_decay hfit hd0 hF cc.1 cc.2 _ _).trans ?_
  set s := (offsetSupNorm cc.1.1 : ℝ)
  set s' := (offsetSupNorm cc.2.1 : ℝ)
  have e1 : ‖B cc.1‖ ≤ |K| * (1 + s) ^ p := (hK cc.1).trans
    (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
  have e2 : ‖B' cc.2‖ ≤ |K'| * (1 + s') ^ p' := (hK' cc.2).trans
    (mul_le_mul_of_nonneg_right (le_abs_self K') (by positivity))
  have e3 : Real.exp (-ℓ.weightRate * ((max (offsetSupNorm cc.1.1) (offsetSupNorm cc.2.1) : ℕ) : ℝ)) ≤
      Real.exp (-(ℓ.weightRate / 2) * s) * Real.exp (-(ℓ.weightRate / 2) * s') := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have a1 : s ≤ ((max (offsetSupNorm cc.1.1) (offsetSupNorm cc.2.1) : ℕ) : ℝ) :=
      Nat.cast_le.2 (le_max_left _ _)
    have a2 : s' ≤ ((max (offsetSupNorm cc.1.1) (offsetSupNorm cc.2.1) : ℕ) : ℝ) :=
      Nat.cast_le.2 (le_max_right _ _)
    nlinarith
  calc ‖B cc.1‖ * ‖B' cc.2‖ *
        (C * Real.exp (-ℓ.weightRate * ((max (offsetSupNorm cc.1.1) (offsetSupNorm cc.2.1) : ℕ) : ℝ)))
      ≤ (|K| * (1 + s) ^ p) * (|K'| * (1 + s') ^ p') *
          (C * (Real.exp (-(ℓ.weightRate / 2) * s) * Real.exp (-(ℓ.weightRate / 2) * s'))) := by
        gcongr
    _ = _ := by
        simp only [decayWeight]
        ring
theorem growth_linearPotential (A : Fin 4 → Fin 4 → imaginaryQuaternions) :
    HasPolynomialGrowth (linearPotential A) := by
  refine ⟨∑ ν, ∑ i, ‖A ν i‖, 1, fun c => ?_⟩
  set s := (offsetSupNorm c.1 : ℝ) with hs
  have hs0 : 0 ≤ s := by positivity
  unfold linearPotential
  rw [norm_smul, pow_one]
  have h1 : ‖∑ ν, ((c.1 ν : ℤ) : ℝ) • A ν c.2‖ ≤ s * ∑ ν, ∑ i, ‖A ν i‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ν _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
    have a1 : |((c.1 ν : ℤ) : ℝ)| ≤ s := by
      rw [hs]
      have := abs_le_offsetSupNorm c.1 ν
      exact_mod_cast this
    have a2 : ‖A ν c.2‖ ≤ ∑ i, ‖A ν i‖ :=
      Finset.single_le_sum (f := fun i => ‖A ν i‖) (fun i _ => norm_nonneg _) (Finset.mem_univ c.2)
    exact mul_le_mul a1 a2 (norm_nonneg _) hs0
  have h2 : 0 ≤ ∑ ν, ∑ i, ‖A ν i‖ := Finset.sum_nonneg fun ν _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  have e : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  rw [e]
  have h3 := mul_nonneg hs0 h2
  nlinarith
end Bounds
section Beta
def symmetricAngle (ω : Fin 4 → Fin 4 → ℝ) (c : OffsetBond) : ℝ :=
  (1 / 2) * ∑ ν, ((c.1 ν : ℤ) : ℝ) * ω ν c.2
theorem symmetricAngle_step (ω : Fin 4 → Fin 4 → ℝ) (u : Offset) (i j : Fin 4) :
    symmetricAngle ω (u + latticeStep i, j) = symmetricAngle ω (u, j) + (1 / 2) * ω i j := by
  simp only [symmetricAngle, latticeStep, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib, mul_add]
  congr 2
  rw [Finset.sum_eq_single i]
  · simp
  · intro ν _ hν
    simp [hν]
  · simp
theorem symmetricAngle_closed (ω : Fin 4 → Fin 4 → ℝ) (hω : ∀ i j, ω i j = - ω j i) (u : Offset)
    (i j : Fin 4) :
    symmetricAngle ω (u, i) + symmetricAngle ω (u + latticeStep i, j) -
      symmetricAngle ω (u + latticeStep j, i) - symmetricAngle ω (u, j) = ω i j := by
  rw [symmetricAngle_step, symmetricAngle_step, hω j i]
  ring
def arrayNorm (ω : Fin 4 → Fin 4 → ℝ) : ℝ := ∑ ν, ∑ i, |ω ν i|
theorem arrayNorm_nonneg (ω : Fin 4 → Fin 4 → ℝ) : 0 ≤ arrayNorm ω :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem abs_le_arrayNorm (ω : Fin 4 → Fin 4 → ℝ) (ν i : Fin 4) : |ω ν i| ≤ arrayNorm ω :=
  (Finset.single_le_sum (f := fun i => |ω ν i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans
    (Finset.single_le_sum (f := fun ν => ∑ i, |ω ν i|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.mem_univ ν))
theorem abs_symmetricAngle_le (ω : Fin 4 → Fin 4 → ℝ) (c : OffsetBond) :
    |symmetricAngle ω c| ≤ arrayNorm ω * (1 + (offsetSupNorm c.1 : ℝ)) := by
  set s := (offsetSupNorm c.1 : ℝ) with hs
  have hs0 : 0 ≤ s := by positivity
  have h1 : |∑ ν, ((c.1 ν : ℤ) : ℝ) * ω ν c.2| ≤ s * arrayNorm ω := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ ν, |((c.1 ν : ℤ) : ℝ) * ω ν c.2| ≤ s * ∑ i, |ω ν i| := by
      intro ν
      rw [abs_mul]
      have a1 : |((c.1 ν : ℤ) : ℝ)| ≤ s := by
        rw [hs]
        have := abs_le_offsetSupNorm c.1 ν
        exact_mod_cast this
      have a2 : |ω ν c.2| ≤ ∑ i, |ω ν i| :=
        Finset.single_le_sum (f := fun i => |ω ν i|) (fun i _ => abs_nonneg _) (Finset.mem_univ c.2)
      exact mul_le_mul a1 a2 (abs_nonneg _) hs0
    calc ∑ ν, |((c.1 ν : ℤ) : ℝ) * ω ν c.2| ≤ ∑ ν, s * ∑ i, |ω ν i| := Finset.sum_le_sum fun ν _ => this ν
      _ = s * arrayNorm ω := by rw [← Finset.mul_sum]; rfl
  have h2 := arrayNorm_nonneg ω
  unfold symmetricAngle
  rw [abs_mul]
  norm_num
  nlinarith
end Beta
section Translate
variable {ℓ : StepParameters} {d : ℕ} {C : ℝ} {h : LocalDensity}
theorem translate_perturb {n k : ℕ} (Y : TorusSite n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) :
    TorusFields.translate Y (perturb c X σ (trivialField n)) =
      perturb (fun l => ((c l).1 - Y, (c l).2)) X σ (trivialField n) := by
  funext x i
  simp only [TorusFields.translate, perturb, trivialField]
  congr 2
  refine Finset.sum_congr rfl fun l _ => ?_
  have e : (c l = (x + Y, i)) ↔ (((c l).1 - Y, (c l).2) = (x, i)) := by
    constructor
    · intro hc
      simp [hc]
    · intro hc
      have h1 : (c l).1 - Y = x := congrArg Prod.fst hc
      have h2 : (c l).2 = i := congrArg Prod.snd hc
      refine Prod.ext ?_ h2
      simp only
      rw [← h1]
      abel
  simp only [e]
theorem mixedDeriv_translate (hfit : ℓ.Admissible) (hF : IsCurvatureFamilyOnMultiples ℓ d C h) {n : ℕ}
    [NeZero n] (hn : ℓ.n₀ ≤ n)
    (hd : d ∣ n) (Y : TorusSite n) (u u' : OffsetBond) (X X' : imaginaryQuaternions) :
    mixedDeriv (h n Y) (trivialField n) ![bondFrom Y u, bondFrom Y u'] ![X, X'] =
      flatSecondDeriv h n u u' X X' := by
  unfold flatSecondDeriv mixedDeriv
  have hev : (fun σ : Fin 2 → ℝ => h n Y (perturb ![bondFrom Y u, bondFrom Y u'] ![X, X'] σ (trivialField n)))
      =ᶠ[nhds 0] fun σ => h n 0 (perturb ![bondFrom 0 u, bondFrom 0 u'] ![X, X'] σ (trivialField n)) := by
    filter_upwards [eventually_isCold_perturb ![bondFrom Y u, bondFrom Y u'] ![X, X'] (trivialField n)
      (isCold_trivialField hfit.σ_pos)] with σ hσ
    have h1 := hF.translation n hn hd 0 Y _ hσ
    rw [zero_add] at h1
    rw [← h1, translate_perturb]
    congr 2
    funext l
    fin_cases l <;> simp [bondFrom]
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev 2).self_of_nhds]
end Translate
section Value
variable {ℓ : StepParameters} {d : ℕ} {C : ℝ} {h : LocalDensity}
def thirdOrderConstant (ℓ : StepParameters) (C K : ℝ) : ℝ :=
  C * (K * ∑' u, decayWeight (ℓ.weightRate / 3) 1 u) ^ 3
theorem sum_cutAngles_bound {n : ℕ} [NeZero n] (hfit : ℓ.Admissible) (Y : TorusSite n) (r : ℕ)
    {β : OffsetBond → ℝ} {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ b, |β b| ≤ K * (1 + (offsetSupNorm b.1 : ℝ))) :
    ∑ b : TorusBond n, |cutAngles Y r β b| * Real.exp (-(ℓ.weightRate / 3) * _root_.YangMills.Construction.TorusFields.supDist Y b.1) ≤
      K * ∑' u, decayWeight (ℓ.weightRate / 3) 1 u := by
  have hr := weightRate_pos hfit
  have hs := summable_decayWeight (b := ℓ.weightRate / 3) (by positivity) 1
  calc ∑ b : TorusBond n, |cutAngles Y r β b| * Real.exp (-(ℓ.weightRate / 3) * _root_.YangMills.Construction.TorusFields.supDist Y b.1)
      ≤ ∑ b : TorusBond n, K * decayWeight (ℓ.weightRate / 3) 1 (offsetBond Y b) := by
        refine Finset.sum_le_sum fun b _ => ?_
        have e : (_root_.YangMills.Construction.TorusFields.supDist Y b.1 : ℝ) = (offsetSupNorm (offsetBond Y b).1 : ℝ) := by
          rw [_root_.YangMills.Construction.TorusFields.supDist_comm, _root_.YangMills.Construction.AbelianSecondOrder.supDist_eq_offsetSupNorm]
          rfl
        rw [e]
        simp only [decayWeight, pow_one]
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (abs_cutAngles_le_growth hK0 hK b) (Real.exp_pos _).le
    _ = K * ∑ b : TorusBond n, decayWeight (ℓ.weightRate / 3) 1 (offsetBond Y b) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_offsetBond_le_tsum Y _ (decayWeight_nonneg _ _) hs) hK0
def boxSecondSum (h : LocalDensity) (n r : ℕ) (β : OffsetBond → ℝ) (X : imaginaryQuaternions) : ℝ :=
  ∑ u ∈ offsetBoxBonds r, ∑ u' ∈ offsetBoxBonds r, β u * β u' * flatSecondDeriv h n u u' X X
theorem centered_sub_boxSecondSum (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    {n : ℕ} [NeZero n]
    (hn : ℓ.n₀ ≤ n) (hd : d ∣ n) (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (ω : Fin 4 → Fin 4 → ℝ) {γ : ℝ}
    (hγ : 0 < γ) (V : TorusField n) (hV : IsAbelianWithCurvature X ω γ V) (hcV : IsCold ℓ.threshold V)
    (Y : TorusSite n) (β : OffsetBond → ℝ)
    (hβ : ∀ u i j, β (u, i) + β (u + latticeStep i, j) - β (u + latticeStep j, i) - β (u, j) = ω i j)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ b, |β b| ≤ K * (1 + (offsetSupNorm b.1 : ℝ))) {r : ℕ} (hr : 2 * r + 2 < n)
    (hcold : 4 * (γ * (K * (1 + (r : ℝ)))) < ℓ.threshold) :
    |centered h n Y V - γ ^ 2 / 2 * boxSecondSum h n r β X| ≤
      C * Real.exp (-ℓ.weightRate * r) + thirdOrderConstant ℓ C K * γ ^ 3 / 2 := by
  have hC0 := constant_nonneg hfit hd0 hF
  have hrate := weightRate_pos hfit
  obtain ⟨g, hg⟩ := exists_gauge_to_potential X ω γ V hV Y β hβ r (by omega)
  set α : TorusBond n → ℝ := cutAngles Y r β with hα
  have hcoldt : ∀ t : ℝ, |t| ≤ γ → IsCold ℓ.threshold (fieldAlong X (t • α)) := by
    intro t ht
    refine isCold_cutAngles hK0 hK hX (lt_of_le_of_lt ?_ hcold)
    have : 0 ≤ K * (1 + (r : ℝ)) := by positivity
    nlinarith
  have hW : IsCold ℓ.threshold (gaugeTransform g V) := by
    intro x μ ν hμ
    rw [_root_.YangMills.Construction.TorusFields.curvature_gaugeTransform]
    exact hcV x μ ν hμ
  have hW' := hcoldt γ (by rw [abs_of_pos hγ])
  have hag : FieldsAgreeNear (gaugeTransform g V) (fieldAlong X (γ • α)) Y Y r := by
    intro b hb
    rw [hg b hb]
    simp only [fieldAlong, Pi.smul_apply, smul_eq_mul]
    have e : ((bondFrom Y b).1, (bondFrom Y b).2) = bondFrom Y b := rfl
    rw [e, hα, cutAngles_bondFrom β (by omega) b hb]
  have e2 := hF.local_density n n hn hn hd hd Y Y _ _ r hr hr hW hW' hag 0 Fin.elim0 Fin.elim0 (by norm_num)
    (fun l => l.elim0) (fun l => l.elim0)
  rw [mixedDeriv_zero, mixedDeriv_zero] at e2
  have e3 : centered h n Y (gaugeTransform g V) = centered h n Y V := by
    simp only [centered]
    rw [hF.gauge n hn hd Y g V hcV]
  rw [e3] at e2
  have e4 := centered_second_order hF hC0 hn hd hrate.le Y X hX α hγ hcoldt
  have e5 : iteratedFDeriv ℝ 2 (valueAlong (h n Y) X) 0 (fun _ => α) = boxSecondSum h n r β X := by
    rw [second_deriv_expand hF hn hd hfit.σ_pos Y X α]
    have a1 : ∀ b : TorusBond n, ∑ b', α b * α b' * mixedDeriv (h n Y) (trivialField n) ![b, b'] ![X, X] =
        α b * ∑ b', α b' * mixedDeriv (h n Y) (trivialField n) ![b, b'] ![X, X] := by
      intro b
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b' _ => by ring
    simp only [a1]
    rw [hα, sum_cutAngles_mul Y r β _ (by omega)]
    unfold boxSecondSum
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [sum_cutAngles_mul Y r β _ (by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun u' _ => ?_
    rw [mixedDeriv_translate hfit hF hn hd Y u u' X X]
    ring
  rw [e5] at e4
  have e6 := sum_cutAngles_bound hfit Y r hK0 hK (β := β)
  have e7 : (C * (∑ b : TorusBond n, |α b| * Real.exp (-(ℓ.weightRate / 3) * _root_.YangMills.Construction.TorusFields.supDist Y b.1)) ^ 3) * γ ^ 3 / 2 ≤
      thirdOrderConstant ℓ C K * γ ^ 3 / 2 := by
    have b0 : 0 ≤ ∑ b : TorusBond n, |α b| * Real.exp (-(ℓ.weightRate / 3) * _root_.YangMills.Construction.TorusFields.supDist Y b.1) :=
      Finset.sum_nonneg fun b _ => by positivity
    have b1 := pow_le_pow_left₀ b0 e6 3
    have b2 := mul_le_mul_of_nonneg_left b1 hC0
    have b3 : 0 ≤ γ ^ 3 / 2 := by positivity
    have := mul_le_mul_of_nonneg_right b2 b3
    simp only [thirdOrderConstant]
    linarith
  have e8 := div_weight_le_exp (ℓ := ℓ) hC0 r
  have tri := abs_sub_le (centered h n Y V) (centered h n Y (fieldAlong X (γ • α)))
    (γ ^ 2 / 2 * boxSecondSum h n r β X)
  linarith
end Value
section TorusGradient
variable {ℓ : StepParameters} {d : ℕ} {C : ℝ} {h : LocalDensity} {n : ℕ}
def gradientAngles (φ : TorusSite n → ℝ) (b : TorusBond n) : ℝ := φ (b.1 + unitStep n b.2) - φ b.1
theorem fieldAlong_add_gradient (X : imaginaryQuaternions) (φ : TorusSite n → ℝ) (p : TorusBond n → ℝ) (s : ℝ) :
    fieldAlong X (p + s • gradientAngles φ) =
      gaugeTransform (fun x => expUnit ((-(s * φ x)) • X)) (fieldAlong X p) := by
  funext x i
  simp only [gaugeTransform, fieldAlong, expUnit_smul_inv, expUnit_smul_mul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, gradientAngles]
  congr 2
  ring
variable [NeZero n]
theorem fderiv_gradient_eq_zero (hF : IsCurvatureFamilyOnMultiples ℓ d C h) (hn : ℓ.n₀ ≤ n) (hd : d ∣ n)
    (Y : TorusSite n)
    (X : imaginaryQuaternions) (φ : TorusSite n → ℝ) (p : TorusBond n → ℝ)
    (hc : IsCold ℓ.threshold (fieldAlong X p)) :
    fderiv ℝ (valueAlong (h n Y) X) p (gradientAngles φ) = 0 := by
  set G := valueAlong (h n Y) X with hG
  have hsm : ContDiffAt ℝ 3 G p := contDiffAt_valueAlong _ _ _ (hF.smooth n hn hd Y _ hc)
  have hdiff : DifferentiableAt ℝ G p := hsm.differentiableAt (by norm_num)
  have h0 : HasFDerivAt G (fderiv ℝ G p) (p + (0 : ℝ) • gradientAngles φ) := by
    simpa using hdiff.hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => p + s • gradientAngles φ) (gradientAngles φ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (gradientAngles φ)).const_add p
  have h1 := h0.comp_hasDerivAt (0 : ℝ) hline
  have hconst : (G ∘ fun s : ℝ => p + s • gradientAngles φ) = fun _ => G p := by
    funext s
    simp only [Function.comp, hG, valueAlong]
    rw [fieldAlong_add_gradient, hF.gauge n hn hd Y _ _ hc]
  rw [hconst] at h1
  exact h1.unique (hasDerivAt_const _ _)
theorem eventually_isCold_fieldAlong (X : imaginaryQuaternions) (hX : ‖X‖ = 1) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ p in nhds (0 : TorusBond n → ℝ), IsCold s (fieldAlong X p) := by
  filter_upwards [Metric.ball_mem_nhds (0 : TorusBond n → ℝ) (show 0 < s / 4 by positivity)] with p hp
  have hb : ∀ b, |p b| < s / 4 := by
    intro b
    have h1 : ‖p‖ < s / 4 := by simpa using hp
    exact lt_of_le_of_lt (by simpa using norm_le_pi_norm p b) h1
  intro x μ ν _
  refine lt_of_le_of_lt (curvature_fieldAlong_le X hX _ x μ ν) ?_
  have h1 := abs_lt.1 (hb (x, μ))
  have h2 := abs_lt.1 (hb (x + unitStep n μ, ν))
  have h3 := abs_lt.1 (hb (x + unitStep n ν, μ))
  have h4 := abs_lt.1 (hb (x, ν))
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
theorem second_fderiv_gradient_eq_zero (hfit : ℓ.Admissible) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    (hn : ℓ.n₀ ≤ n) (hd : d ∣ n)
    (Y : TorusSite n) (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (φ : TorusSite n → ℝ) (e : TorusBond n → ℝ) :
    fderiv ℝ (fderiv ℝ (valueAlong (h n Y) X)) 0 e (gradientAngles φ) = 0 := by
  set G := valueAlong (h n Y) X with hG
  have hc0 : IsCold ℓ.threshold (fieldAlong X (0 : TorusBond n → ℝ)) := by
    rw [fieldAlong_zero]
    exact isCold_trivialField hfit.σ_pos
  have hsm : ContDiffAt ℝ 3 G 0 := contDiffAt_valueAlong _ _ _ (hF.smooth n hn hd Y _ hc0)
  have hD : DifferentiableAt ℝ (fderiv ℝ G) 0 :=
    (hsm.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  let ap : ((TorusBond n → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (gradientAngles φ)
  have h1 : HasFDerivAt (fun p => fderiv ℝ G p (gradientAngles φ)) (ap.comp (fderiv ℝ (fderiv ℝ G) 0)) 0 :=
    ap.hasFDerivAt.comp 0 hD.hasFDerivAt
  have h2 : (fun p => fderiv ℝ G p (gradientAngles φ)) =ᶠ[nhds 0] fun _ => 0 := by
    filter_upwards [eventually_isCold_fieldAlong X hX hfit.σ_pos] with p hp
    exact fderiv_gradient_eq_zero hF hn hd Y X φ p hp
  have h3 : HasFDerivAt (fun p => fderiv ℝ G p (gradientAngles φ)) (0 : (TorusBond n → ℝ) →L[ℝ] ℝ) 0 :=
    (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) (0 : TorusBond n → ℝ)).congr_of_eventuallyEq h2
  have h4 := h1.unique h3
  have h5 := congrArg (fun T : (TorusBond n → ℝ) →L[ℝ] ℝ => T e) h4
  simpa [ap, ContinuousLinearMap.apply_apply] using h5
theorem sum_gradient_mixedDeriv (hfit : ℓ.Admissible) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    (hn : ℓ.n₀ ≤ n) (hd : d ∣ n)
    (Y : TorusSite n) (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (φ : TorusSite n → ℝ) (b : TorusBond n) :
    ∑ b', gradientAngles φ b' * mixedDeriv (h n Y) (trivialField n) ![b, b'] ![X, X] = 0 := by
  classical
  set G := valueAlong (h n Y) X with hG
  have hc0 : IsCold ℓ.threshold (fieldAlong X (0 : TorusBond n → ℝ)) := by
    rw [fieldAlong_zero]
    exact isCold_trivialField hfit.σ_pos
  have hsm := hF.smooth n hn hd Y _ hc0
  have e1 : (fun _ : Fin 2 => X) = ![X, X] := by
    funext l
    fin_cases l <;> rfl
  have hT : ∀ b' : TorusBond n, mixedDeriv (h n Y) (trivialField n) ![b, b'] ![X, X] =
      fderiv ℝ (fderiv ℝ G) 0 (Pi.single b 1) (Pi.single b' 1) := by
    intro b'
    have := mixedDeriv_fieldAlong (h n Y) X 0 hsm (k := 2) (by norm_num) ![b, b']
    rw [fieldAlong_zero, e1, iteratedFDeriv_two_apply] at this
    simpa using this
  have hα : gradientAngles φ = ∑ b', gradientAngles φ b' • (Pi.single b' 1 : TorusBond n → ℝ) := by
    ext x
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 := second_fderiv_gradient_eq_zero hfit hF hn hd Y X hX φ (Pi.single b 1)
  rw [hα, map_sum] at h1
  simp only [map_smul, smul_eq_mul] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [hT b']
end TorusGradient
section LatticeGradient
variable {ℓ : StepParameters} {d : ℕ} {C : ℝ} {h : LocalDensity}
def offsetGradient (φ : Offset → ℝ) (c : OffsetBond) : ℝ := φ (c.1 + latticeStep c.2) - φ c.1
theorem offsetSupNorm_le_step (u : Offset) (i : Fin 4) :
    offsetSupNorm u ≤ offsetSupNorm (u + latticeStep i) + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.offsetSupNorm_le_add_single <;> assumption
theorem offsetSupNorm_step_le (u : Offset) (i : Fin 4) :
    offsetSupNorm (u + latticeStep i) ≤ offsetSupNorm u + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.offsetSupNorm_add_single_le <;> assumption
theorem not_inBox_of_lt {R : ℕ} {u : Offset} (h : R < offsetSupNorm u) : ¬ OffsetInBox R u := fun hb =>
  absurd (offsetSupNorm_le_of_inBox hb) (not_le.2 h)
theorem le_offsetSupNorm_of_not_bondInBox {R : ℕ} {u : OffsetBond} (h : ¬ BondOffsetInBox (R + 2) u) :
    R + 2 ≤ offsetSupNorm u.1 := by
  by_contra hc
  exact h (bondOffsetInBox_of_le (by omega))
theorem offsetGradient_outside {φ : Offset → ℝ} {R : ℕ} (hφ : ∀ z, ¬ OffsetInBox R z → φ z = 0)
    {u : OffsetBond} (hu : ¬ BondOffsetInBox (R + 2) u) : offsetGradient φ u = 0 := by
  have h1 := le_offsetSupNorm_of_not_bondInBox hu
  have h2 := offsetSupNorm_le_step u.1 u.2
  unfold offsetGradient
  rw [hφ _ (not_inBox_of_lt (by omega)), hφ _ (not_inBox_of_lt (by omega)), sub_zero]
theorem gradientAngles_eq_cutAngles {n : ℕ} [NeZero n] {φ : Offset → ℝ} {R : ℕ}
    (hφ : ∀ z, ¬ OffsetInBox R z → φ z = 0)
    (hn : 2 * (R + 2) < n) :
    gradientAngles (fun z : TorusSite n => φ (offsetFrom 0 z)) = cutAngles 0 (R + 2) (offsetGradient φ) := by
  funext b
  obtain ⟨x, i⟩ := b
  unfold cutAngles gradientAngles
  split_ifs with hb
  · have hx : (0 : TorusSite n) + siteOfInt (offsetFrom 0 x) = x := add_siteOfInt_offsetFrom 0 x
    have h2 : ∀ k, 2 * |(offsetFrom 0 x + latticeStep i) k| < n := by
      intro k
      have := hb.2 k
      simp only [offsetBond, latticeStep] at *
      omega
    have e : offsetFrom 0 (x + unitStep n i) = offsetFrom 0 x + latticeStep i := by
      conv_lhs => rw [← hx]
      rw [add_siteOfInt_unitStep]
      exact offsetFrom_add_siteOfInt 0 _ h2
    simp only [e, offsetGradient, offsetBond]
  · have h1 := le_offsetSupNorm_of_not_bondInBox hb
    simp only [offsetBond] at h1
    have h3 : offsetSupNorm (offsetFrom 0 x) ≤ offsetSupNorm (offsetFrom 0 (x + unitStep n i)) + 1 := by
      rw [← _root_.YangMills.Construction.AbelianSecondOrder.supDist_eq_offsetSupNorm, ← _root_.YangMills.Construction.AbelianSecondOrder.supDist_eq_offsetSupNorm]
      have := _root_.YangMills.Construction.TorusFields.supDist_triangle x (x + unitStep n i) 0
      have h4 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le x i
      omega
    simp only
    rw [hφ _ (not_inBox_of_lt (by omega)), hφ _ (not_inBox_of_lt (by omega)), sub_zero]
theorem sum_offsetGradient_flat_eq_zero (hfit : ℓ.Admissible) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    {n : ℕ} (hn : ℓ.n₀ ≤ n)
    (hd : d ∣ n) {φ : Offset → ℝ} {R : ℕ} (hφ : ∀ z, ¬ OffsetInBox R z → φ z = 0) (hnR : 2 * (R + 2) < n)
    (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (c : OffsetBond) :
    ∑ u ∈ offsetBoxBonds (R + 2), offsetGradient φ u * flatSecondDeriv h n c u X X = 0 := by
  have := neZero_of_n₀_le hfit hn
  have h1 := sum_gradient_mixedDeriv hfit hF hn hd 0 X hX (fun z : TorusSite n => φ (offsetFrom 0 z))
    (bondFrom 0 c)
  rw [gradientAngles_eq_cutAngles hφ hnR, sum_cutAngles_mul 0 (R + 2) _ _ hnR] at h1
  exact h1
theorem hasSum_offsetGradient_of_support (hfit : ℓ.Admissible) (hd0 : 0 < d)
    (hF : IsCurvatureFamilyOnMultiples ℓ d C h) {φ : Offset → ℝ}
    {R : ℕ} (hφ : ∀ z, ¬ OffsetInBox R z → φ z = 0) (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (c : OffsetBond) :
    HasSum (fun u => offsetGradient φ u * secondDerivLimitOnMultiples d h c u X X) 0 := by
  have h1 : ∑ u ∈ offsetBoxBonds (R + 2), offsetGradient φ u * secondDerivLimitOnMultiples d h c u X X = 0 := by
    have h2 : Filter.Tendsto
        (fun m => ∑ u ∈ offsetBoxBonds (R + 2), offsetGradient φ u * flatSecondDeriv h (d * m) c u X X)
        Filter.atTop
        (nhds (∑ u ∈ offsetBoxBonds (R + 2), offsetGradient φ u * secondDerivLimitOnMultiples d h c u X X)) :=
      tendsto_finsetSum _ fun u _ => (tendsto_flatSecondDeriv hfit hd0 hF c u X X).const_mul _
    have h3 : (fun m => ∑ u ∈ offsetBoxBonds (R + 2), offsetGradient φ u * flatSecondDeriv h (d * m) c u X X)
        =ᶠ[Filter.atTop] fun _ => 0 := by
      filter_upwards [Filter.eventually_ge_atTop (max ℓ.n₀ (2 * (R + 2) + 1))] with m hm
      have a1 := le_of_max_le_left hm
      have a2 := le_of_max_le_right hm
      have a3 : m ≤ d * m := Nat.le_mul_of_pos_left m hd0
      exact sum_offsetGradient_flat_eq_zero hfit hF (n₀_le_mul hd0 a1) (dvd_mul_right _ _) hφ (by omega) X hX c
    exact tendsto_nhds_unique (h2.congr' h3) tendsto_const_nhds
  rw [← h1]
  refine hasSum_sum_of_ne_finset_zero fun u hu => ?_
  rw [offsetGradient_outside hφ (fun hb => hu (mem_offsetBoxBonds.2 hb)), zero_mul]
open Classical in
def truncate (φ : Offset → ℝ) (R : ℕ) (z : Offset) : ℝ := if OffsetInBox R z then φ z else 0
theorem hasSum_offsetGradient (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    {φ : Offset → ℝ}
    {K : ℝ} {p : ℕ} (hφ : ∀ z, |φ z| ≤ K * (1 + (offsetSupNorm z : ℝ)) ^ p) (X : imaginaryQuaternions)
    (hX : ‖X‖ = 1) (c : OffsetBond) :
    HasSum (fun u => offsetGradient φ u * secondDerivLimitOnMultiples d h c u X X) 0 := by
  have hC0 := constant_nonneg hfit hd0 hF
  have hr := weightRate_pos hfit
  have hK0 : 0 ≤ K := by
    have := (abs_nonneg _).trans (hφ 0)
    have e : offsetSupNorm (0 : Offset) = 0 := by simp [offsetSupNorm]
    simpa [e] using this
  have hsw := summable_decayWeight hr p
  set M : ℝ := 2 * K * 2 ^ p * C with hM
  have hcut : ∀ (R : ℕ) (z : Offset), |truncate φ R z| ≤ K * (1 + (offsetSupNorm z : ℝ)) ^ p := by
    intro R z
    unfold truncate
    split_ifs
    · exact hφ z
    · simp only [abs_zero]
      positivity
  have hdom : ∀ (ψ : Offset → ℝ), (∀ z, |ψ z| ≤ K * (1 + (offsetSupNorm z : ℝ)) ^ p) → ∀ u : OffsetBond,
      ‖offsetGradient ψ u * secondDerivLimitOnMultiples d h c u X X‖ ≤ M * decayWeight ℓ.weightRate p u := by
    intro ψ hψ u
    set s := (offsetSupNorm u.1 : ℝ) with hs
    have e1 : |offsetGradient ψ u| ≤ 2 * K * 2 ^ p * (1 + s) ^ p := by
      have a1 := hψ u.1
      have a2 := hψ (u.1 + latticeStep u.2)
      have a3 : (offsetSupNorm (u.1 + latticeStep u.2) : ℝ) ≤ s + 1 := by
        rw [hs]
        exact_mod_cast offsetSupNorm_step_le u.1 u.2
      have a4 : (1 + (offsetSupNorm (u.1 + latticeStep u.2) : ℝ)) ^ p ≤ 2 ^ p * (1 + s) ^ p := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) p
      have a5 : (1 + s) ^ p ≤ 2 ^ p * (1 + s) ^ p := by
        have : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
        have h0 : 0 ≤ (1 + s) ^ p := by positivity
        nlinarith
      unfold offsetGradient
      calc |ψ (u.1 + latticeStep u.2) - ψ u.1| ≤ |ψ (u.1 + latticeStep u.2)| + |ψ u.1| := abs_sub _ _
        _ ≤ K * (2 ^ p * (1 + s) ^ p) + K * (2 ^ p * (1 + s) ^ p) :=
            add_le_add (a2.trans (mul_le_mul_of_nonneg_left a4 hK0))
              (a1.trans (mul_le_mul_of_nonneg_left a5 hK0))
        _ = _ := by ring
    have e2 : |secondDerivLimitOnMultiples d h c u X X| ≤ C * Real.exp (-ℓ.weightRate * s) := by
      have a1 := secondDerivLimit_decay hfit hd0 hF c u X X
      rw [hX, one_mul, one_mul] at a1
      refine a1.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      apply Real.exp_le_exp.2
      have a2 : s ≤ ((max (offsetSupNorm c.1) (offsetSupNorm u.1) : ℕ) : ℝ) := by
        rw [hs]
        exact_mod_cast le_max_right _ _
      nlinarith
    rw [Real.norm_eq_abs, abs_mul]
    calc |offsetGradient ψ u| * |secondDerivLimitOnMultiples d h c u X X|
        ≤ (2 * K * 2 ^ p * (1 + s) ^ p) * (C * Real.exp (-ℓ.weightRate * s)) :=
          mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
      _ = M * decayWeight ℓ.weightRate p u := by
          simp only [hM, decayWeight]
          ring
  have hsummable : Summable (fun u => offsetGradient φ u * secondDerivLimitOnMultiples d h c u X X) :=
    Summable.of_norm_bounded (hsw.mul_left M) (hdom φ hφ)
  have hlim : Filter.Tendsto
      (fun R : ℕ => ∑' u, offsetGradient (truncate φ R) u * secondDerivLimitOnMultiples d h c u X X)
      Filter.atTop (nhds (∑' u, offsetGradient φ u * secondDerivLimitOnMultiples d h c u X X)) := by
    refine tendsto_tsum_of_dominated_convergence (hsw.mul_left M) ?_
      (Filter.Eventually.of_forall fun R u => hdom _ (hcut R) u)
    intro u
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (offsetSupNorm u.1 + 1)] with R hR
    have b1 : OffsetInBox R u.1 := inBox_of_offsetSupNorm_le (by omega)
    have b2 : OffsetInBox R (u.1 + latticeStep u.2) :=
      inBox_of_offsetSupNorm_le ((offsetSupNorm_step_le u.1 u.2).trans hR)
    simp only [offsetGradient, truncate, if_pos b1, if_pos b2]
  have hzero : ∀ R : ℕ, ∑' u, offsetGradient (truncate φ R) u * secondDerivLimitOnMultiples d h c u X X = 0 := by
    intro R
    refine (hasSum_offsetGradient_of_support hfit hd0 hF (R := R) ?_ X hX c).tsum_eq
    intro z hz
    simp [truncate, hz]
  simp only [hzero] at hlim
  have h0 := tendsto_nhds_unique hlim tendsto_const_nhds
  rw [show (0 : ℝ) = ∑' u, offsetGradient φ u * secondDerivLimitOnMultiples d h c u X X from h0.symm]
  exact hsummable.hasSum
end LatticeGradient
section Close
variable {ℓ : StepParameters} {d : ℕ} {C : ℝ} {h : LocalDensity}
def pairDecayWeight (ℓ : StepParameters) (cc : OffsetBond × OffsetBond) : ℝ :=
  decayWeight (ℓ.weightRate / 4) 1 cc.1 * decayWeight (ℓ.weightRate / 4) 1 cc.2
theorem summable_pairDecayWeight (hfit : ℓ.Admissible) : Summable (pairDecayWeight ℓ) := by
  have hr := weightRate_pos hfit
  exact Summable.mul_of_nonneg (summable_decayWeight (by positivity) 1) (summable_decayWeight (by positivity) 1)
    (decayWeight_nonneg _ _) (decayWeight_nonneg _ _)
theorem pairDecayWeight_nonneg (cc : OffsetBond × OffsetBond) : 0 ≤ pairDecayWeight ℓ cc :=
  mul_nonneg (decayWeight_nonneg _ _ _) (decayWeight_nonneg _ _ _)
def boxCloseConstant (ℓ : StepParameters) (C K : ℝ) : ℝ := C * K ^ 2 * ∑' cc, pairDecayWeight ℓ cc
theorem norm_pair_le {K : ℝ} {β : OffsetBond → ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ b, |β b| ≤ K * (1 + (offsetSupNorm b.1 : ℝ)))
    {C E F r : ℝ} (cc : OffsetBond × OffsetBond) (hC0 : 0 ≤ C) (hF0 : 0 ≤ F) (hr0 : 0 ≤ r)
    (hE : |E| ≤ C * (r * (Real.exp (-(F / 4) * offsetSupNorm cc.1.1) *
      Real.exp (-(F / 4) * offsetSupNorm cc.2.1)))) :
    ‖β cc.1 * β cc.2 * E‖ ≤ C * K ^ 2 * r *
      (decayWeight (F / 4) 1 cc.1 * decayWeight (F / 4) 1 cc.2) := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have h1 := hK cc.1
  have h2 := hK cc.2
  set s := (offsetSupNorm cc.1.1 : ℝ)
  set s' := (offsetSupNorm cc.2.1 : ℝ)
  calc |β cc.1| * |β cc.2| * |E|
      ≤ (K * (1 + s)) * (K * (1 + s')) *
          (C * (r * (Real.exp (-(F / 4) * s) * Real.exp (-(F / 4) * s')))) := by
        gcongr
    _ = _ := by
        simp only [decayWeight, pow_one]
        ring
theorem boxSecondSum_sub_tsum_le (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    {n : ℕ} (hn : ℓ.n₀ ≤ n)
    (hd : d ∣ n) {r : ℕ} (hr : 2 * r + 2 < n) (X : imaginaryQuaternions) (hX : ‖X‖ = 1)
    {β : OffsetBond → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ b, |β b| ≤ K * (1 + (offsetSupNorm b.1 : ℝ))) :
    |boxSecondSum h n r β X -
        ∑' cc : OffsetBond × OffsetBond, β cc.1 * β cc.2 * secondDerivLimitOnMultiples d h cc.1 cc.2 X X| ≤
      boxCloseConstant ℓ C K * Real.exp (-(ℓ.weightRate / 2) * r) := by
  classical
  have hC0 := constant_nonneg hfit hd0 hF
  have hrate := weightRate_pos hfit
  have hpw := summable_pairDecayWeight (ℓ := ℓ) hfit
  set e : ℝ := Real.exp (-(ℓ.weightRate / 2) * r) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  let F₁ : OffsetBond × OffsetBond → ℝ := fun cc => if cc.1 ∈ offsetBoxBonds r ∧ cc.2 ∈ offsetBoxBonds r then
    β cc.1 * β cc.2 * flatSecondDeriv h n cc.1 cc.2 X X else 0
  let F₂ : OffsetBond × OffsetBond → ℝ := fun cc =>
    β cc.1 * β cc.2 * secondDerivLimitOnMultiples d h cc.1 cc.2 X X
  have hs1 : HasSum F₁ (boxSecondSum h n r β X) := by
    have e1 : boxSecondSum h n r β X = ∑ cc ∈ offsetBoxBonds r ×ˢ offsetBoxBonds r, F₁ cc := by
      unfold boxSecondSum
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' hu' => ?_
      simp only [F₁, if_pos (And.intro hu hu')]
    rw [e1]
    refine hasSum_sum_of_ne_finset_zero fun cc hcc => ?_
    have : ¬ (cc.1 ∈ offsetBoxBonds r ∧ cc.2 ∈ offsetBoxBonds r) := fun hh => hcc (Finset.mem_product.2 hh)
    simp only [F₁, if_neg this]
  have hq : ∀ cc : OffsetBond × OffsetBond, |secondDerivLimitOnMultiples d h cc.1 cc.2 X X| ≤
      C * Real.exp (-ℓ.weightRate * ((max (offsetSupNorm cc.1.1) (offsetSupNorm cc.2.1) : ℕ) : ℝ)) := by
    intro cc
    have := secondDerivLimit_decay hfit hd0 hF cc.1 cc.2 X X
    rwa [hX, one_mul, one_mul] at this
  have hsum2 : Summable F₂ := by
    have hb : ∀ cc, ‖F₂ cc‖ ≤ C * K ^ 2 * 1 * pairDecayWeight ℓ cc := by
      intro cc
      refine norm_pair_le hK0 hK cc hC0 hrate.le zero_le_one ((hq cc).trans ?_)
      refine mul_le_mul_of_nonneg_left ?_ hC0
      have := exp_le_split (δ := ℓ.weightRate)
        (t := ((max (offsetSupNorm cc.1.1) (offsetSupNorm cc.2.1) : ℕ) : ℝ))
        (r := 0) (s := offsetSupNorm cc.1.1) (s' := offsetSupNorm cc.2.1) hrate.le (by positivity)
        (by exact_mod_cast le_max_left _ _) (by exact_mod_cast le_max_right _ _)
      simpa using this
    exact Summable.of_norm_bounded (hpw.mul_left _) hb
  have hs2 := hsum2.hasSum
  have hdiff := hs1.sub hs2
  have hbound : ∀ cc, ‖F₁ cc - F₂ cc‖ ≤ C * K ^ 2 * e * pairDecayWeight ℓ cc := by
    intro cc
    by_cases hin : cc.1 ∈ offsetBoxBonds r ∧ cc.2 ∈ offsetBoxBonds r
    · have b1 := mem_offsetBoxBonds.1 hin.1
      have b2 := mem_offsetBoxBonds.1 hin.2
      have e1 : F₁ cc - F₂ cc = β cc.1 * β cc.2 *
          (flatSecondDeriv h n cc.1 cc.2 X X - secondDerivLimitOnMultiples d h cc.1 cc.2 X X) := by
        simp only [F₁, F₂, if_pos hin]
        ring
      rw [e1]
      refine norm_pair_le hK0 hK cc hC0 hrate.le he0 ?_
      refine (flatSecondDeriv_sub_limit_le hfit hd0 hF hn hd hr b1 b2 hX hX).trans
        ((div_weight_le_exp hC0 r).trans ?_)
      refine mul_le_mul_of_nonneg_left ?_ hC0
      have s1 : (offsetSupNorm cc.1.1 : ℝ) ≤ r := by exact_mod_cast offsetSupNorm_le_of_inBox b1.1
      have s2 : (offsetSupNorm cc.2.1 : ℝ) ≤ r := by exact_mod_cast offsetSupNorm_le_of_inBox b2.1
      exact exp_le_split hrate.le le_rfl s1 s2
    · have e1 : F₁ cc - F₂ cc = β cc.1 * β cc.2 * (-secondDerivLimitOnMultiples d h cc.1 cc.2 X X) := by
        simp only [F₁, F₂, if_neg hin]
        ring
      rw [e1]
      refine norm_pair_le hK0 hK cc hC0 hrate.le he0 ?_
      rw [abs_neg]
      refine (hq cc).trans (mul_le_mul_of_nonneg_left ?_ hC0)
      have hbig : r ≤ max (offsetSupNorm cc.1.1) (offsetSupNorm cc.2.1) := by
        by_contra hc
        have c1 : offsetSupNorm cc.1.1 + 1 ≤ r := by
          have := le_max_left (offsetSupNorm cc.1.1) (offsetSupNorm cc.2.1)
          omega
        have c2 : offsetSupNorm cc.2.1 + 1 ≤ r := by
          have := le_max_right (offsetSupNorm cc.1.1) (offsetSupNorm cc.2.1)
          omega
        exact hin ⟨mem_offsetBoxBonds.2 (bondOffsetInBox_of_le c1), mem_offsetBoxBonds.2 (bondOffsetInBox_of_le c2)⟩
      exact exp_le_split hrate.le (by exact_mod_cast hbig) (by exact_mod_cast le_max_left _ _)
        (by exact_mod_cast le_max_right _ _)
  have hg : HasSum (fun cc => C * K ^ 2 * e * pairDecayWeight ℓ cc)
      (C * K ^ 2 * e * ∑' cc, pairDecayWeight ℓ cc) :=
    hpw.hasSum.mul_left _
  have h3 := tsum_of_norm_bounded hg hbound
  rw [hdiff.tsum_eq, Real.norm_eq_abs] at h3
  refine h3.trans_eq ?_
  simp only [boxCloseConstant]
  ring
end Close
section ValueBeta
variable {ℓ : StepParameters} {d : ℕ} {C : ℝ} {h : LocalDensity}
theorem curvature_le_of_abelian {n : ℕ} {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {ω : Fin 4 → Fin 4 → ℝ}
    {γ : ℝ} {V : TorusField n}
    (hV : IsAbelianWithCurvature X ω γ V) (x : TorusSite n) {μ ν : Fin 4} (hμ : μ < ν) :
    curvature V x μ ν ≤ |γ * ω μ ν| := by
  unfold curvature
  rw [hV.2 x μ ν hμ]
  refine (norm_expUnit_sub_one_le _).trans_eq ?_
  rw [norm_smul, hX, mul_one, Real.norm_eq_abs]
theorem exists_large_log (δ C₁ C₂ C₃ K σ N ε : ℝ) (hδ : 0 < δ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → 0 ≤ L ∧ 3 / δ ≤ L ∧ Real.exp (-L) * K < σ ∧
      4 * (Real.exp (-L) * (K * (2 + L ^ 2))) < σ ∧ C₁ * Real.exp (-L) < ε / 3 ∧
      C₂ * Real.exp (-L) / 2 < ε / 3 ∧ C₃ * Real.exp (-L) / 2 < ε / 3 ∧ N ≤ 4 * L ^ 2 + 4 := by
  have t1 : Filter.Tendsto (fun L : ℝ => Real.exp (-L)) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have t2 : Filter.Tendsto (fun L : ℝ => L ^ 2 * Real.exp (-L)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have a1 : Filter.Tendsto (fun L : ℝ => Real.exp (-L) * K) Filter.atTop (nhds 0) := by
    simpa using t1.mul_const K
  have a2 : Filter.Tendsto (fun L : ℝ => 4 * (Real.exp (-L) * (K * (2 + L ^ 2)))) Filter.atTop (nhds 0) := by
    have := ((t1.const_mul (8 * K)).add (t2.const_mul (4 * K)))
    simp only [mul_zero, add_zero] at this
    refine this.congr fun L => ?_
    ring
  have a3 : Filter.Tendsto (fun L : ℝ => C₁ * Real.exp (-L)) Filter.atTop (nhds 0) := by
    simpa using t1.const_mul C₁
  have a4 : Filter.Tendsto (fun L : ℝ => C₂ * Real.exp (-L) / 2) Filter.atTop (nhds 0) := by
    simpa using (t1.const_mul C₂).div_const 2
  have a5 : Filter.Tendsto (fun L : ℝ => C₃ * Real.exp (-L) / 2) Filter.atTop (nhds 0) := by
    simpa using (t1.const_mul C₃).div_const 2
  have hε3 : 0 < ε / 3 := by positivity
  have ev := ((a1.eventually (gt_mem_nhds hσ)).and ((a2.eventually (gt_mem_nhds hσ)).and
    ((a3.eventually (gt_mem_nhds hε3)).and ((a4.eventually (gt_mem_nhds hε3)).and
      (a5.eventually (gt_mem_nhds hε3))))))
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.1 ev
  refine ⟨max (max L₁ 0) (max (3 / δ) N), fun L hL => ?_⟩
  have b1 : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have b2 : 0 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have b3 : 3 / δ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have b4 : N ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  obtain ⟨c1, c2, c3, c4, c5⟩ := hL₁ L b1
  refine ⟨b2, b3, c1, c2, c3, c4, c5, ?_⟩
  nlinarith [sq_nonneg (L - 1)]
set_option maxHeartbeats 1000000 in
theorem centered_sub_symmetric_le (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    (ω : Fin 4 → Fin 4 → ℝ) (hω : ∀ i j, ω i j = - ω j i) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ < γ₀ → ∀ (n : ℕ) [NeZero n], d ∣ n →
      4 * Real.log (1 / γ) ^ 2 + 4 < n → ∀ (X : imaginaryQuaternions) (V : TorusField n), ‖X‖ = 1 →
        IsAbelianWithCurvature X ω γ V →
        ∀ Y : TorusSite n, |centered h n Y V - γ ^ 2 / 2 *
          ∑' cc : OffsetBond × OffsetBond, symmetricAngle ω cc.1 * symmetricAngle ω cc.2 *
            secondDerivLimitOnMultiples d h cc.1 cc.2 X X| ≤ ε * γ ^ 2 := by
  have hC0 := constant_nonneg hfit hd0 hF
  have hrate := weightRate_pos hfit
  set K := arrayNorm ω with hKd
  have hK0 : 0 ≤ K := arrayNorm_nonneg ω
  have hK := abs_symmetricAngle_le ω
  obtain ⟨L₀, hL₀⟩ := exists_large_log ℓ.weightRate C (thirdOrderConstant ℓ C K) (boxCloseConstant ℓ C K) K
    ℓ.threshold (ℓ.n₀ : ℝ) ε hrate hfit.σ_pos hε
  refine ⟨Real.exp (-L₀), Real.exp_pos _, fun γ hγ hγ₀ n _ hd hside X V hX hV Y => ?_⟩
  set L := Real.log (1 / γ) with hLd
  have hγL : Real.exp (-L) = γ := by
    rw [hLd, Real.log_div one_ne_zero hγ.ne', Real.log_one, zero_sub, neg_neg, Real.exp_log hγ]
  have hLL : L₀ ≤ L := by
    have : -L₀ ≥ -L := by
      have := Real.log_lt_log hγ hγ₀
      rw [Real.log_exp] at this
      have e : L = - Real.log γ := by
        rw [hLd, Real.log_div one_ne_zero hγ.ne', Real.log_one, zero_sub]
      linarith
    linarith
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩ := hL₀ L hLL
  rw [hγL] at l2 l3 l4 l5 l6
  set r : ℕ := ⌈L ^ 2⌉₊ with hr
  have r1 : L ^ 2 ≤ r := Nat.le_ceil _
  have r2 : (r : ℝ) < L ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hnR : (4 * L ^ 2 + 4 : ℝ) < n := hside
  have hrn : 2 * r + 2 < n := by
    have : ((2 * r + 2 : ℕ) : ℝ) < n := by
      push_cast
      linarith [sq_nonneg L]
    exact_mod_cast this
  have hn : ℓ.n₀ ≤ n := by
    have : (ℓ.n₀ : ℝ) < n := lt_of_le_of_lt l7 hnR
    exact_mod_cast this.le
  have hcV : IsCold ℓ.threshold V := by
    intro x μ ν hμ
    refine lt_of_le_of_lt (curvature_le_of_abelian hX hV x hμ) (lt_of_le_of_lt ?_ l2)
    rw [abs_mul, abs_of_pos hγ]
    exact mul_le_mul_of_nonneg_left (abs_le_arrayNorm ω μ ν) hγ.le
  have hcold : 4 * (γ * (K * (1 + (r : ℝ)))) < ℓ.threshold := by
    refine lt_of_le_of_lt ?_ l3
    have h1 : K * (1 + (r : ℝ)) ≤ K * (2 + L ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hK0
    have h2 := mul_le_mul_of_nonneg_left h1 hγ.le
    linarith
  have e1 := centered_sub_boxSecondSum hfit hd0 hF hn hd X hX ω hγ V hV hcV Y (symmetricAngle ω)
    (symmetricAngle_closed ω hω) hK0 hK hrn hcold
  have e2 := boxSecondSum_sub_tsum_le hfit hd0 hF hn hd hrn X hX hK0 hK
  set Q := ∑' cc : OffsetBond × OffsetBond, symmetricAngle ω cc.1 * symmetricAngle ω cc.2 *
    secondDerivLimitOnMultiples d h cc.1 cc.2 X X with hQ
  set S := boxSecondSum h n r (symmetricAngle ω) X with hS
  have l1' : 3 * L ≤ ℓ.weightRate * L ^ 2 := by
    have h2 : 3 ≤ L * ℓ.weightRate := (div_le_iff₀ hrate).1 l1
    calc 3 * L ≤ (L * ℓ.weightRate) * L := mul_le_mul_of_nonneg_right h2 l0
      _ = ℓ.weightRate * L ^ 2 := by ring
  have l1'' : ℓ.weightRate * L ^ 2 ≤ ℓ.weightRate * r := mul_le_mul_of_nonneg_left r1 hrate.le
  have x1 : Real.exp (-ℓ.weightRate * r) ≤ γ ^ 3 := by
    have : γ ^ 3 = Real.exp (-(3 * L)) := by
      rw [← hγL, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [this]
    apply Real.exp_le_exp.2
    linarith
  have x2 : Real.exp (-(ℓ.weightRate / 2) * r) ≤ γ := by
    rw [← hγL]
    apply Real.exp_le_exp.2
    linarith
  have hγ2 : 0 < γ ^ 2 := by positivity
  have y1 : C * Real.exp (-ℓ.weightRate * r) ≤ ε / 3 * γ ^ 2 := by
    have h2 := mul_le_mul_of_nonneg_left x1 hC0
    have h3 : C * γ ^ 3 = (C * γ) * γ ^ 2 := by ring
    rw [h3] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right l4.le hγ2.le)
  have y2 : thirdOrderConstant ℓ C K * γ ^ 3 / 2 ≤ ε / 3 * γ ^ 2 := by
    have h3 : thirdOrderConstant ℓ C K * γ ^ 3 / 2 = (thirdOrderConstant ℓ C K * γ / 2) * γ ^ 2 := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right l5.le hγ2.le
  have hcc0 : 0 ≤ boxCloseConstant ℓ C K := by
    unfold boxCloseConstant
    have : 0 ≤ ∑' cc, pairDecayWeight ℓ cc := tsum_nonneg pairDecayWeight_nonneg
    positivity
  have y3 : γ ^ 2 / 2 * |S - Q| ≤ ε / 3 * γ ^ 2 := by
    have h4 : |S - Q| ≤ boxCloseConstant ℓ C K * γ :=
      e2.trans (mul_le_mul_of_nonneg_left x2 hcc0)
    have h5 : γ ^ 2 / 2 * |S - Q| ≤ γ ^ 2 / 2 * (boxCloseConstant ℓ C K * γ) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 : γ ^ 2 / 2 * (boxCloseConstant ℓ C K * γ) = (boxCloseConstant ℓ C K * γ / 2) * γ ^ 2 := by ring
    rw [h6] at h5
    exact h5.trans (mul_le_mul_of_nonneg_right l6.le hγ2.le)
  have tri : |centered h n Y V - γ ^ 2 / 2 * Q| ≤
      |centered h n Y V - γ ^ 2 / 2 * S| + γ ^ 2 / 2 * |S - Q| := by
    have e0 : centered h n Y V - γ ^ 2 / 2 * Q =
        (centered h n Y V - γ ^ 2 / 2 * S) + γ ^ 2 / 2 * (S - Q) := by ring
    rw [e0]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ γ ^ 2 / 2)]
  linarith
end ValueBeta
section Orth
variable {ℓ : StepParameters} {d : ℕ} {C : ℝ} {h : LocalDensity}
theorem gaugeTransform_const_perturb {n k : ℕ} (g : UnitQuaternion) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) :
    gaugeTransform (fun _ => g) (perturb c X σ (trivialField n)) =
      perturb c (fun l => conjAction g (X l)) σ (trivialField n) := by
  funext x i
  simp only [gaugeTransform, perturb, trivialField, mul_one]
  rw [conj_expUnit, map_sum]
  congr 2
  funext l
  split_ifs <;> simp
theorem flatSecondDeriv_orthogonal (hfit : ℓ.Admissible) (hF : IsCurvatureFamilyOnMultiples ℓ d C h) {n : ℕ}
    (hn : ℓ.n₀ ≤ n) (hd : d ∣ n)
    (c c' : OffsetBond) {X X' : imaginaryQuaternions} {g : UnitQuaternion} (h1 : conjAction g X = X)
    (h2 : conjAction g X' = -X') :
    flatSecondDeriv h n c c' X X' = 0 := by
  have := neZero_of_n₀_le hfit hn
  have hev : (fun σ : Fin 2 → ℝ => h n 0 (perturb ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] σ (trivialField n)))
      =ᶠ[nhds 0] fun σ =>
        h n 0 (perturb ![bondFrom 0 c, bondFrom 0 c'] ![(1 : ℝ) • X, (-1 : ℝ) • X'] σ (trivialField n)) := by
    filter_upwards [eventually_isCold_perturb ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] (trivialField n)
      (isCold_trivialField hfit.σ_pos)] with σ hσ
    rw [← hF.gauge n hn hd 0 (fun _ => g) _ hσ, gaugeTransform_const_perturb]
    congr 2
    funext l
    fin_cases l
    · show conjAction g X = (1 : ℝ) • X
      rw [h1, one_smul]
    · show conjAction g X' = (-1 : ℝ) • X'
      rw [h2]
      exact (neg_one_smul ℝ X').symm
  have h3 : mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] =
      mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![(1 : ℝ) • X, (-1 : ℝ) • X'] := by
    unfold mixedDeriv
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev 2).self_of_nhds]
  rw [mixedDeriv_two_smul _ _ (contDiffThreeAt_trivialField hfit hF hn hd 0)] at h3
  unfold flatSecondDeriv
  linarith
theorem secondDerivLimit_orthogonal (hfit : ℓ.Admissible) (hd0 : 0 < d)
    (hF : IsCurvatureFamilyOnMultiples ℓ d C h) (c c' : OffsetBond) {X X' : imaginaryQuaternions}
    {g : UnitQuaternion} (h1 : conjAction g X = X) (h2 : conjAction g X' = -X') :
    secondDerivLimitOnMultiples d h c c' X X' = 0 := by
  have a1 := tendsto_flatSecondDeriv hfit hd0 hF c c' X X'
  have a2 : (fun m => flatSecondDeriv h (d * m) c c' X X') =ᶠ[Filter.atTop] fun _ => 0 := by
    filter_upwards [Filter.eventually_ge_atTop ℓ.n₀] with m hm
    exact flatSecondDeriv_orthogonal hfit hF (n₀_le_mul hd0 hm) (dvd_mul_right _ _) c c' h1 h2
  exact tendsto_nhds_unique (a1.congr' a2) tendsto_const_nhds
def quatJ : imaginaryQuaternions := ⟨⟨0, 0, 1, 0⟩, rfl⟩
def quatK : imaginaryQuaternions := ⟨⟨0, 0, 0, 1⟩, rfl⟩
theorem norm_quatJ : ‖quatJ‖ = 1 := by
  apply norm_eq_one_of_sq_eq_one
  rw [sq_norm_imaginary]
  simp [quatJ]
theorem norm_quatK : ‖quatK‖ = 1 := by
  apply norm_eq_one_of_sq_eq_one
  rw [sq_norm_imaginary]
  simp [quatK]
def imaginaryBasis : Fin 3 → imaginaryQuaternions := ![quatI, quatJ, quatK]
theorem norm_imaginaryBasis (a : Fin 3) : ‖imaginaryBasis a‖ = 1 := by
  fin_cases a
  · exact norm_quatI
  · exact norm_quatJ
  · exact norm_quatK
def coord (w : imaginaryQuaternions) : Fin 3 → ℝ := ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK]
theorem eq_sum_coord (w : imaginaryQuaternions) : w = ∑ a, coord w a • imaginaryBasis a := by
  apply Subtype.ext
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  rw [Fin.sum_univ_three]
  apply Quaternion.ext
  · show (w : ℍ[ℝ]).re = (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0
    rw [hw]
    ring
  · show (w : ℍ[ℝ]).imI = (w : ℍ[ℝ]).imI * 1 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0
    ring
  · show (w : ℍ[ℝ]).imJ = (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 1 + (w : ℍ[ℝ]).imK * 0
    ring
  · show (w : ℍ[ℝ]).imK = (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 1
    ring
theorem coord_sub (w w' : imaginaryQuaternions) (a : Fin 3) : coord (w - w') a = coord w a - coord w' a := by
  fin_cases a <;> simp [coord]
theorem abs_coord_le (w : imaginaryQuaternions) (a : Fin 3) : |coord w a| ≤ ‖w‖ := by
  have h1 := sq_norm_imaginary w
  have h2 : coord w a ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [h1]
    fin_cases a <;> simp [coord] <;>
      nlinarith [sq_nonneg (w : ℍ[ℝ]).imI, sq_nonneg (w : ℍ[ℝ]).imJ, sq_nonneg (w : ℍ[ℝ]).imK]
  exact abs_le.2 (abs_le_of_sq_le_sq' h2 (norm_nonneg _))
theorem conjAction_self (w : imaginaryQuaternions) (hw : ‖w‖ = 1) : conjAction (unitOfImaginary w hw) w = w := by
  apply Subtype.ext
  have h2 : ((conjAction (unitOfImaginary w hw) w : imaginaryQuaternions) : ℍ[ℝ]) =
      (w : ℍ[ℝ]) * (w : ℍ[ℝ]) * star (w : ℍ[ℝ]) := rfl
  have h3 : (w : ℍ[ℝ]) * star (w : ℍ[ℝ]) = 1 := mul_star_self_unit (unitOfImaginary w hw)
  rw [h2, mul_assoc, h3, mul_one]
theorem secondDerivLimit_basis_orthogonal (hfit : ℓ.Admissible) (hd0 : 0 < d)
    (hF : IsCurvatureFamilyOnMultiples ℓ d C h) (c c' : OffsetBond) {a b : Fin 3}
    (hab : a ≠ b) : secondDerivLimitOnMultiples d h c c' (imaginaryBasis a) (imaginaryBasis b) = 0 := by
  refine secondDerivLimit_orthogonal hfit hd0 hF c c' (conjAction_self (imaginaryBasis a) (norm_imaginaryBasis a))
    (conjAction_of_orthogonal (imaginaryBasis b) (imaginaryBasis a) (norm_imaginaryBasis a) ?_)
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | simp [imaginaryBasis, quatI, quatJ, quatK]
theorem secondDerivLimit_smul_right (hfit : ℓ.Admissible) (hd0 : 0 < d)
    (hF : IsCurvatureFamilyOnMultiples ℓ d C h) (c c' : OffsetBond)
    (X : imaginaryQuaternions) (t : ℝ) (W : imaginaryQuaternions) :
    secondDerivLimitOnMultiples d h c c' X (t • W) = t * secondDerivLimitOnMultiples d h c c' X W := by
  have := secondDerivLimit_smul hfit hd0 hF c c' 1 t X W
  simpa using this
theorem secondDerivLimit_expand_right (hfit : ℓ.Admissible) (hd0 : 0 < d)
    (hF : IsCurvatureFamilyOnMultiples ℓ d C h) (c c' : OffsetBond)
    (X Z : imaginaryQuaternions) :
    secondDerivLimitOnMultiples d h c c' X Z =
      ∑ b, coord Z b * secondDerivLimitOnMultiples d h c c' X (imaginaryBasis b) := by
  conv_lhs => rw [eq_sum_coord Z]
  rw [Fin.sum_univ_three, Fin.sum_univ_three, secondDerivLimit_add_right hfit hd0 hF,
    secondDerivLimit_add_right hfit hd0 hF, secondDerivLimit_smul_right hfit hd0 hF,
    secondDerivLimit_smul_right hfit hd0 hF, secondDerivLimit_smul_right hfit hd0 hF]
theorem secondDerivLimit_expand (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    (c c' : OffsetBond)
    (Z Z' : imaginaryQuaternions) : secondDerivLimitOnMultiples d h c c' Z Z' =
      ∑ a, coord Z a * coord Z' a *
        secondDerivLimitOnMultiples d h c c' (imaginaryBasis a) (imaginaryBasis a) := by
  have hl : ∀ b, secondDerivLimitOnMultiples d h c c' Z (imaginaryBasis b) =
      ∑ a, coord Z a * secondDerivLimitOnMultiples d h c c' (imaginaryBasis a) (imaginaryBasis b) := by
    intro b
    rw [secondDerivLimit_symm hfit hd0 hF, secondDerivLimit_expand_right hfit hd0 hF]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [secondDerivLimit_symm hfit hd0 hF c' c]
  rw [secondDerivLimit_expand_right hfit hd0 hF]
  simp only [hl, Fin.sum_univ_three]
  rw [secondDerivLimit_basis_orthogonal hfit hd0 hF c c' (show (0 : Fin 3) ≠ 1 by decide),
    secondDerivLimit_basis_orthogonal hfit hd0 hF c c' (show (0 : Fin 3) ≠ 2 by decide),
    secondDerivLimit_basis_orthogonal hfit hd0 hF c c' (show (1 : Fin 3) ≠ 0 by decide),
    secondDerivLimit_basis_orthogonal hfit hd0 hF c c' (show (1 : Fin 3) ≠ 2 by decide),
    secondDerivLimit_basis_orthogonal hfit hd0 hF c c' (show (2 : Fin 3) ≠ 0 by decide),
    secondDerivLimit_basis_orthogonal hfit hd0 hF c c' (show (2 : Fin 3) ≠ 1 by decide)]
  ring
theorem secondDerivLimit_add_left (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    (c c' : OffsetBond)
    (X₁ X₂ X : imaginaryQuaternions) :
    secondDerivLimitOnMultiples d h c c' (X₁ + X₂) X =
      secondDerivLimitOnMultiples d h c c' X₁ X + secondDerivLimitOnMultiples d h c c' X₂ X := by
  rw [secondDerivLimit_symm hfit hd0 hF, secondDerivLimit_add_right hfit hd0 hF,
    secondDerivLimit_symm hfit hd0 hF c' c X X₁, secondDerivLimit_symm hfit hd0 hF c' c X X₂]
end Orth
section Growth
theorem growth_discreteGradient {φ : Offset → imaginaryQuaternions} {K : ℝ} {p : ℕ}
    (hφ : ∀ z, ‖φ z‖ ≤ K * (1 + (offsetSupNorm z : ℝ)) ^ p) :
    HasPolynomialGrowth (discreteGradient φ) := by
  have hK0 : 0 ≤ K := by
    have h1 := (norm_nonneg _).trans (hφ 0)
    have e : offsetSupNorm (0 : Offset) = 0 := by simp [offsetSupNorm]
    simpa [e] using h1
  refine ⟨2 * K * 2 ^ p, p, fun u => ?_⟩
  set s := (offsetSupNorm u.1 : ℝ) with hs
  have a1 := hφ u.1
  have a2 := hφ (u.1 + latticeStep u.2)
  have a3 : (offsetSupNorm (u.1 + latticeStep u.2) : ℝ) ≤ s + 1 := by
    rw [hs]
    exact_mod_cast offsetSupNorm_step_le u.1 u.2
  have a4 : (1 + (offsetSupNorm (u.1 + latticeStep u.2) : ℝ)) ^ p ≤ 2 ^ p * (1 + s) ^ p := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) p
  have a5 : (1 + s) ^ p ≤ 2 ^ p * (1 + s) ^ p := by
    have : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    have h0 : 0 ≤ (1 + s) ^ p := by positivity
    nlinarith
  unfold discreteGradient
  calc ‖φ (u.1 + Pi.single u.2 1) - φ u.1‖ ≤ ‖φ (u.1 + latticeStep u.2)‖ + ‖φ u.1‖ := norm_sub_le _ _
    _ ≤ K * (2 ^ p * (1 + s) ^ p) + K * (2 ^ p * (1 + s) ^ p) :=
        add_le_add (a2.trans (mul_le_mul_of_nonneg_left a4 hK0))
          (a1.trans (mul_le_mul_of_nonneg_left a5 hK0))
    _ = _ := by ring
theorem growth_smul {f : OffsetBond → ℝ} {W : imaginaryQuaternions} (hW : ‖W‖ = 1) {K : ℝ} {p : ℕ}
    (hf : ∀ c, |f c| ≤ K * (1 + (offsetSupNorm c.1 : ℝ)) ^ p) :
    HasPolynomialGrowth fun c => f c • W :=
  ⟨K, p, fun c => by rw [norm_smul, hW, mul_one, Real.norm_eq_abs]; exact hf c⟩
end Growth
section LieGradient
variable {ℓ : StepParameters} {d : ℕ} {C : ℝ} {h : LocalDensity}
theorem hasSum_coord_gradient (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    {φ : Offset → ℝ}
    {K : ℝ} {p : ℕ} (hφ : ∀ z, |φ z| ≤ K * (1 + (offsetSupNorm z : ℝ)) ^ p) {f : OffsetBond → ℝ} {K' : ℝ}
    {p' : ℕ} (hf : ∀ c, |f c| ≤ K' * (1 + (offsetSupNorm c.1 : ℝ)) ^ p') (a : Fin 3) :
    HasSum (fun cc : OffsetBond × OffsetBond => offsetGradient φ cc.1 * f cc.2 *
      secondDerivLimitOnMultiples d h cc.1 cc.2 (imaginaryBasis a) (imaginaryBasis a)) 0 := by
  set g : OffsetBond × OffsetBond → ℝ := fun cc => offsetGradient φ cc.1 * f cc.2 *
    secondDerivLimitOnMultiples d h cc.1 cc.2 (imaginaryBasis a) (imaginaryBasis a) with hg
  have hW := norm_imaginaryBasis a
  have hφ' : ∀ z, ‖(fun z => φ z • imaginaryBasis a) z‖ ≤ K * (1 + (offsetSupNorm z : ℝ)) ^ p := fun z => by
    simp only [norm_smul, hW, mul_one, Real.norm_eq_abs]
    exact hφ z
  have hG : HasPolynomialGrowth fun c => offsetGradient φ c • imaginaryBasis a := by
    obtain ⟨K₁, p₁, h₁⟩ := growth_discreteGradient hφ'
    refine ⟨K₁, p₁, fun c => ?_⟩
    have e : discreteGradient (fun z => φ z • imaginaryBasis a) c = offsetGradient φ c • imaginaryBasis a := by
      simp only [discreteGradient, offsetGradient, latticeStep]
      exact (sub_smul _ _ _).symm
    show ‖offsetGradient φ c • imaginaryBasis a‖ ≤ _
    rw [← e]
    exact h₁ c
  have hs0 := summable_secondDerivLimit hfit hd0 hF hG (growth_smul hW hf)
  have hsum : Summable g := by
    refine hs0.congr fun cc => ?_
    simp only [hg]
    rw [secondDerivLimit_smul hfit hd0 hF]
  have hswap : Summable (g ∘ Prod.swap) := (Equiv.prodComm OffsetBond OffsetBond).summable_iff.2 hsum
  have hfib : ∀ c₂ : OffsetBond, HasSum (fun c₁ : OffsetBond => g (c₁, c₂)) 0 := by
    intro c₂
    have h1 := (hasSum_offsetGradient hfit hd0 hF hφ (imaginaryBasis a) hW c₂).mul_right (f c₂)
    rw [zero_mul] at h1
    have e : (fun c₁ : OffsetBond => g (c₁, c₂)) = fun u => offsetGradient φ u *
        secondDerivLimitOnMultiples d h c₂ u (imaginaryBasis a) (imaginaryBasis a) * f c₂ := by
      funext u
      simp only [hg]
      rw [secondDerivLimit_symm hfit hd0 hF u c₂]
      ring
    rw [e]
    exact h1
  have htsum : ∑' cc, g cc = 0 := by
    have e1 : ∑' cc, g cc = ∑' cc, (g ∘ Prod.swap) cc := ((Equiv.prodComm OffsetBond OffsetBond).tsum_eq g).symm
    rw [e1, hswap.tsum_prod' (fun c₂ => (hfib c₂).summable)]
    have : ∀ c₂ : OffsetBond, ∑' c₁ : OffsetBond, (g ∘ Prod.swap) (c₂, c₁) = 0 := fun c₂ => (hfib c₂).tsum_eq
    simp only [this, tsum_zero]
  rw [← htsum]
  exact hsum.hasSum
theorem hasSum_discreteGradient (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    {φ : Offset → imaginaryQuaternions}
    {B' : OffsetBond → imaginaryQuaternions}
    (hφ : ∃ (K : ℝ) (p : ℕ), ∀ z, ‖φ z‖ ≤ K * (1 + (offsetSupNorm z : ℝ)) ^ p)
    (hB' : HasPolynomialGrowth B') :
    HasSum (fun cc : OffsetBond × OffsetBond =>
      secondDerivLimitOnMultiples d h cc.1 cc.2 (discreteGradient φ cc.1) (B' cc.2)) 0 := by
  obtain ⟨K, p, hK⟩ := hφ
  obtain ⟨K', p', hK'⟩ := hB'
  have hcomp : ∀ a : Fin 3, HasSum (fun cc : OffsetBond × OffsetBond =>
      offsetGradient (fun z => coord (φ z) a) cc.1 *
      coord (B' cc.2) a * secondDerivLimitOnMultiples d h cc.1 cc.2 (imaginaryBasis a) (imaginaryBasis a)) 0 :=
    fun a =>
    hasSum_coord_gradient hfit hd0 hF (fun z => (abs_coord_le _ a).trans (hK z))
      (fun c => (abs_coord_le _ a).trans (hK' c)) a
  have h1 := hasSum_sum (s := Finset.univ) fun a _ => hcomp a
  simp only [Finset.sum_const_zero] at h1
  have e : (fun cc : OffsetBond × OffsetBond =>
      secondDerivLimitOnMultiples d h cc.1 cc.2 (discreteGradient φ cc.1) (B' cc.2)) =
      fun cc => ∑ a, offsetGradient (fun z => coord (φ z) a) cc.1 * coord (B' cc.2) a *
        secondDerivLimitOnMultiples d h cc.1 cc.2 (imaginaryBasis a) (imaginaryBasis a) := by
    funext cc
    rw [secondDerivLimit_expand hfit hd0 hF]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [discreteGradient, offsetGradient, latticeStep, coord_sub]
  rw [e]
  exact h1
end LieGradient
section Quadratic
variable (S : Fin 4 → Fin 4 → imaginaryQuaternions) (e : Fin 4 → imaginaryQuaternions)
def bilinearOf (z w : Fin 4 → ℝ) : imaginaryQuaternions := ∑ a, ∑ b, (z a * w b) • S a b
def quadraticOf (z : Fin 4 → ℝ) : imaginaryQuaternions :=
  (1 / 2 : ℝ) • bilinearOf S z z - (1 / 2 : ℝ) • (∑ a, z a • S a a) + ∑ a, z a • e a
theorem bilinearOf_add (t u : Fin 4 → ℝ) :
    bilinearOf S (t + u) (t + u) = bilinearOf S t t + bilinearOf S t u + bilinearOf S u t + bilinearOf S u u := by
  simp only [bilinearOf, Pi.add_apply, add_mul, mul_add, add_smul, Finset.sum_add_distrib]
  abel
theorem bilinearOf_single_right (t : Fin 4 → ℝ) (μ : Fin 4) :
    bilinearOf S t (Pi.single μ 1) = ∑ a, t a • S a μ := by
  unfold bilinearOf
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single μ]
  · simp
  · intro b _ hb
    simp [hb]
  · simp
theorem bilinearOf_single_left (t : Fin 4 → ℝ) (μ : Fin 4) :
    bilinearOf S (Pi.single μ 1) t = ∑ b, t b • S μ b := by
  unfold bilinearOf
  rw [Finset.sum_eq_single μ]
  · simp
  · intro a _ ha
    simp [ha]
  · simp
theorem quadraticOf_step (hS : ∀ a b, S a b = S b a) (t : Fin 4 → ℝ) (μ : Fin 4) :
    quadraticOf S e (t + Pi.single μ 1) - quadraticOf S e t = (∑ ν, t ν • S μ ν) + e μ := by
  have h1 : ∑ a, (t + Pi.single μ 1 : Fin 4 → ℝ) a • S a a = (∑ a, t a • S a a) + S μ μ := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single μ]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  have h2 : ∑ a, (t + Pi.single μ 1 : Fin 4 → ℝ) a • e a = (∑ a, t a • e a) + e μ := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single μ]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  have h3 : bilinearOf S t (Pi.single μ 1) = ∑ ν, t ν • S μ ν := by
    rw [bilinearOf_single_right]
    exact Finset.sum_congr rfl fun a _ => by rw [hS a μ]
  have h4 : bilinearOf S (Pi.single μ 1) (Pi.single μ 1) = S μ μ := by
    rw [bilinearOf_single_left]
    rw [Finset.sum_eq_single μ]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  unfold quadraticOf
  rw [bilinearOf_add, h1, h2, h3, bilinearOf_single_left, h4]
  module
theorem norm_quadraticOf_le (z : Fin 4 → ℝ) {s : ℝ} (hz : ∀ a, |z a| ≤ 1 + s) (hs : 0 ≤ s) :
    ‖quadraticOf S e z‖ ≤ ((∑ a, ∑ b, ‖S a b‖) + (∑ a, ‖S a a‖) + ∑ a, ‖e a‖) * (1 + s) ^ 2 := by
  have hsq : 1 + s ≤ (1 + s) ^ 2 := by nlinarith
  have b1 : ‖bilinearOf S z z‖ ≤ (∑ a, ∑ b, ‖S a b‖) * (1 + s) ^ 2 := by
    unfold bilinearOf
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [sq]
    exact mul_le_mul (hz a) (hz b) (abs_nonneg _) (by linarith)
  have b2 : ‖∑ a, z a • S a a‖ ≤ (∑ a, ‖S a a‖) * (1 + s) ^ 2 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_left ((hz a).trans hsq) (norm_nonneg _)
  have b3 : ‖∑ a, z a • e a‖ ≤ (∑ a, ‖e a‖) * (1 + s) ^ 2 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_left ((hz a).trans hsq) (norm_nonneg _)
  have n1 : 0 ≤ ‖bilinearOf S z z‖ := norm_nonneg _
  have n2 : 0 ≤ ‖∑ a, z a • S a a‖ := norm_nonneg _
  unfold quadraticOf
  have t1 : ‖(1 / 2 : ℝ) • bilinearOf S z z - (1 / 2 : ℝ) • (∑ a, z a • S a a) + ∑ a, z a • e a‖ ≤
      ‖(1 / 2 : ℝ) • bilinearOf S z z‖ + ‖(1 / 2 : ℝ) • (∑ a, z a • S a a)‖ + ‖∑ a, z a • e a‖ :=
    (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
  refine t1.trans ?_
  rw [norm_smul, norm_smul]
  have e0 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  rw [e0]
  nlinarith
end Quadratic
section Linear
variable {ℓ : StepParameters} {d : ℕ} {C : ℝ} {h : LocalDensity}
def realCoords (z : Offset) : Fin 4 → ℝ := fun i => ((z i : ℤ) : ℝ)
theorem realCoords_add_single (z : Offset) (μ : Fin 4) :
    realCoords (z + Pi.single μ 1) = realCoords z + Pi.single μ 1 := by
  funext i
  by_cases hi : i = μ
  · subst hi
    simp [realCoords]
  · simp [realCoords, hi]
theorem abs_realCoords_le (z : Offset) (a : Fin 4) : |realCoords z a| ≤ 1 + (offsetSupNorm z : ℝ) := by
  have h1 := abs_le_offsetSupNorm z a
  have h2 : |realCoords z a| ≤ (offsetSupNorm z : ℝ) := by
    simp only [realCoords]
    exact_mod_cast h1
  linarith
theorem growth_symmetricAngle (ω : Fin 4 → Fin 4 → ℝ) (X : imaginaryQuaternions) :
    HasPolynomialGrowth fun c => symmetricAngle ω c • X := by
  refine ⟨arrayNorm ω * ‖X‖, 1, fun c => ?_⟩
  rw [norm_smul, Real.norm_eq_abs, pow_one]
  have := mul_le_mul_of_nonneg_right (abs_symmetricAngle_le ω c) (norm_nonneg X)
  linarith
theorem linear_eq_symmetric_add_gradient (ω : Fin 4 → Fin 4 → ℝ) (hω : ∀ i j, ω i j = - ω j i)
    (X : imaginaryQuaternions) (B : OffsetBond → imaginaryQuaternions)
    (hB : ColdStepAtMirrorFrames.IsLinearPotential (curvatureAlong X ω) B) :
    ∃ Φ : Offset → imaginaryQuaternions, (∃ (K : ℝ) (p : ℕ), ∀ z, ‖Φ z‖ ≤ K * (1 + (offsetSupNorm z : ℝ)) ^ p) ∧
      ∀ c, B c = symmetricAngle ω c • X + discreteGradient Φ c := by
  obtain ⟨A, e, hBx, hA⟩ := hB
  let S : Fin 4 → Fin 4 → imaginaryQuaternions := fun μ ν => A μ ν - ((1 / 2 : ℝ) * ω ν μ) • X
  have hS : ∀ a b, S a b = S b a := by
    intro a b
    have h1 := hA a b
    simp only [curvatureAlong] at h1
    have h2 : A a b = A b a - ω a b • X := by rw [← h1]; abel
    simp only [S]
    rw [h2, hω b a]
    module
  refine ⟨fun z => quadraticOf S e (realCoords z),
    ⟨_, 2, fun z => norm_quadraticOf_le S e _ (abs_realCoords_le z) (by positivity)⟩, ?_⟩
  rintro ⟨x, μ⟩
  have h1 := quadraticOf_step S e hS (realCoords x) μ
  simp only [discreteGradient]
  rw [realCoords_add_single, h1, hBx x μ]
  simp only [S, smul_sub, Finset.sum_sub_distrib, realCoords, symmetricAngle, Finset.mul_sum, Finset.sum_smul,
    smul_smul]
  have e2 : ∀ ν : Fin 4, ((1 / 2 : ℝ) * (((x ν : ℤ) : ℝ) * ω ν μ)) =
      ((x ν : ℤ) : ℝ) * ((1 / 2 : ℝ) * ω ν μ) := by
    intro ν
    ring
  simp only [e2]
  abel
theorem tsum_linear_eq_symmetric (hfit : ℓ.Admissible) (hd0 : 0 < d) (hF : IsCurvatureFamilyOnMultiples ℓ d C h)
    (ω : Fin 4 → Fin 4 → ℝ) (hω : ∀ i j, ω i j = - ω j i) (X : imaginaryQuaternions)
    (B : OffsetBond → imaginaryQuaternions)
    (hB : ColdStepAtMirrorFrames.IsLinearPotential (curvatureAlong X ω) B) :
    ∑' cc : OffsetBond × OffsetBond, secondDerivLimitOnMultiples d h cc.1 cc.2 (B cc.1) (B cc.2) =
      ∑' cc : OffsetBond × OffsetBond, symmetricAngle ω cc.1 * symmetricAngle ω cc.2 *
        secondDerivLimitOnMultiples d h cc.1 cc.2 X X := by
  obtain ⟨Φ, hΦ, hdec⟩ := linear_eq_symmetric_add_gradient ω hω X B hB
  set B₀ : OffsetBond → imaginaryQuaternions := fun c => symmetricAngle ω c • X with hB₀
  have g0 : HasPolynomialGrowth B₀ := growth_symmetricAngle ω X
  have gG : HasPolynomialGrowth (discreteGradient Φ) := by
    obtain ⟨K, p, hK⟩ := hΦ
    exact growth_discreteGradient hK
  have h00 := (summable_secondDerivLimit hfit hd0 hF g0 g0).hasSum
  have h10 := hasSum_discreteGradient hfit hd0 hF hΦ g0
  have h11 := hasSum_discreteGradient hfit hd0 hF hΦ gG
  have h01 : HasSum (fun cc : OffsetBond × OffsetBond =>
      secondDerivLimitOnMultiples d h cc.1 cc.2 (B₀ cc.1) (discreteGradient Φ cc.2)) 0 := by
    have e : ((fun cc : OffsetBond × OffsetBond =>
        secondDerivLimitOnMultiples d h cc.1 cc.2 (B₀ cc.1) (discreteGradient Φ cc.2)) ∘
        (Equiv.prodComm OffsetBond OffsetBond)) =
        fun cc => secondDerivLimitOnMultiples d h cc.1 cc.2 (discreteGradient Φ cc.1) (B₀ cc.2) := by
      funext cc
      simp only [Function.comp, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      exact secondDerivLimit_symm hfit hd0 hF _ _ _ _
    rw [← (Equiv.prodComm OffsetBond OffsetBond).hasSum_iff, e]
    exact h10
  have hall := ((h00.add h10).add h01).add h11
  simp only [add_zero] at hall
  have e1 : (fun cc : OffsetBond × OffsetBond => secondDerivLimitOnMultiples d h cc.1 cc.2 (B cc.1) (B cc.2)) =
      fun cc =>
      secondDerivLimitOnMultiples d h cc.1 cc.2 (B₀ cc.1) (B₀ cc.2) +
        secondDerivLimitOnMultiples d h cc.1 cc.2 (discreteGradient Φ cc.1) (B₀ cc.2) +
        secondDerivLimitOnMultiples d h cc.1 cc.2 (B₀ cc.1) (discreteGradient Φ cc.2) +
        secondDerivLimitOnMultiples d h cc.1 cc.2 (discreteGradient Φ cc.1) (discreteGradient Φ cc.2) := by
    funext cc
    rw [hdec cc.1, hdec cc.2, secondDerivLimit_add_left hfit hd0 hF, secondDerivLimit_add_right hfit hd0 hF,
      secondDerivLimit_add_right hfit hd0 hF]
    ring
  rw [e1, hall.tsum_eq]
  refine tsum_congr fun cc => ?_
  simp only [hB₀]
  exact secondDerivLimit_smul hfit hd0 hF _ _ _ _ _ _
end Linear
section Statement
theorem isLinearPotential_linearPotential (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (hA : ∀ i j, A i j = - A j i) :
    ColdStepAtMirrorFrames.IsLinearPotential A (linearPotential A) := by
  refine ⟨fun μ ν => (1 / 2 : ℝ) • A ν μ, 0, ?_, ?_⟩
  · intro x μ
    simp only [Pi.zero_apply, add_zero]
    unfold linearPotential
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun ν _ => smul_comm _ _ _
  · intro μ ν
    show (1 / 2 : ℝ) • A μ ν - (1 / 2 : ℝ) • A ν μ = A μ ν
    rw [hA ν μ]
    module
theorem exists_side_large (l : ℕ) (hl : 0 < l) {γ₀ : ℝ} (hγ₀ : 0 < γ₀) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → 0 < 2 * Real.pi * l / (n : ℝ) ^ 2 ∧ 2 * Real.pi * l / (n : ℝ) ^ 2 < γ₀ ∧
      4 * Real.log (1 / (2 * Real.pi * l / (n : ℝ) ^ 2)) ^ 2 + 4 < n := by
  set a : ℝ := 2 * Real.pi * l with ha
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have ha1 : 1 ≤ a := by
    have := Real.pi_gt_three
    nlinarith
  have ha0 : 0 < a := by linarith
  have t1 : Filter.Tendsto (fun n : ℕ => a / (n : ℝ) ^ 2) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 2) Filter.atTop Filter.atTop :=
      (Filter.tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    exact h1.const_div_atTop a
  have hlo : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ 2 ≤ (1 / 32) * x := by
    have h1 := (Real.isLittleO_pow_log_id_atTop (n := 2)).def (show (0 : ℝ) < 1 / 32 by norm_num)
    filter_upwards [h1, Filter.eventually_gt_atTop 0] with x hx hx0
    simp only [id, Real.norm_eq_abs] at hx
    rw [abs_of_pos hx0] at hx
    exact (le_abs_self _).trans hx
  have ev := (t1.eventually (gt_mem_nhds hγ₀)).and ((t1.eventually (gt_mem_nhds one_pos)).and
    ((tendsto_natCast_atTop_atTop.eventually hlo).and (Filter.eventually_ge_atTop 9)))
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1 ev
  refine ⟨n₁, fun n hn => ?_⟩
  obtain ⟨c1, c2, c3, c4⟩ := hn₁ n hn
  have hn0 : (9 : ℝ) ≤ n := by exact_mod_cast c4
  have hpos : 0 < a / (n : ℝ) ^ 2 := by positivity
  refine ⟨hpos, c1, ?_⟩
  set L := Real.log (n : ℝ) with hL
  have hx0 : 0 ≤ Real.log (1 / (a / (n : ℝ) ^ 2)) :=
    Real.log_nonneg ((one_le_div hpos).2 c2.le)
  have hx1 : Real.log (1 / (a / (n : ℝ) ^ 2)) = 2 * L - Real.log a := by
    rw [one_div_div, Real.log_div (by positivity) ha0.ne', Real.log_pow]
    norm_num
    rfl
  have hla := Real.log_nonneg ha1
  have hx2 : Real.log (1 / (a / (n : ℝ) ^ 2)) ≤ 2 * L := by linarith
  have hx3 : Real.log (1 / (a / (n : ℝ) ^ 2)) ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hx0 hx2 2
  nlinarith
theorem secondOrderOnMultiplesOfSide : SecondOrderOnMultiplesOfSide := by
  intro ℓ hfit d hd0 C h hF
  have wide : ∀ ω : Fin 4 → Fin 4 → ℝ, (∀ i j, ω i j = - ω j i) → ∀ ε : ℝ, 0 < ε → ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ < γ₀ → ∀ (n : ℕ) [NeZero n], d ∣ n → 4 * Real.log (1 / γ) ^ 2 + 4 < n →
        ∀ (X : imaginaryQuaternions) (V : TorusField n) (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
          ‖X‖ = 1 → IsAbelianWithCurvature X ω γ V →
          ColdStepAtMirrorFrames.IsLinearPotential (curvatureAlong X ω) B → ∀ Y : TorusSite n,
            |centered h n Y V - γ ^ 2 / 2 *
                ∑' cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4),
                  secondDerivLimitOnMultiples d h cc.1 cc.2 (B cc.1) (B cc.2)| ≤ ε * γ ^ 2 := by
    intro ω hω ε hε
    obtain ⟨γ₀, h0, hγ⟩ := centered_sub_symmetric_le hfit hd0 hF ω hω hε
    refine ⟨γ₀, h0, fun γ a b n _ hd hs X V B hX hV hB Y => ?_⟩
    rw [tsum_linear_eq_symmetric hfit hd0 hF ω hω X B hB]
    exact hγ γ a b n hd hs X V hX hV Y
  refine ⟨tendsto_flatSecondDeriv hfit hd0 hF, secondDerivLimit_bound hfit hd0 hF,
    secondDerivLimit_symm hfit hd0 hF,
    fun B B' hB hB' => summable_secondDerivLimit hfit hd0 hF hB hB',
    fun A A' _ _ => summable_secondDerivLimit hfit hd0 hF (growth_linearPotential A) (growth_linearPotential A'),
    fun φ B' hφ hB' => hasSum_discreteGradient hfit hd0 hF hφ hB', wide, ?_⟩
  intro ω l X hω hl _ hX
  have hs := summable_secondDerivLimit hfit hd0 hF (growth_linearPotential (curvatureAlong X ω))
    (growth_linearPotential (curvatureAlong X ω))
  refine ⟨_, hs.hasSum, fun ε hε => ?_⟩
  obtain ⟨γ₀, h0, hγ⟩ := wide ω hω ε hε
  obtain ⟨n₁, hn₁⟩ := exists_side_large l hl h0
  refine ⟨n₁, fun n _ hn hd V hV Y => ?_⟩
  obtain ⟨a, b, c⟩ := hn₁ n hn
  have hanti : ∀ i j, curvatureAlong X ω i j = - curvatureAlong X ω j i := by
    intro i j
    simp only [curvatureAlong]
    rw [hω i j]
    exact neg_smul (ω j i) X
  exact hγ _ a b n hd c X V _ hX hV (isLinearPotential_linearPotential _ hanti) Y
end Statement
end AbelianSecondOrder
end YangMills.Construction
end

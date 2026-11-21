import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMeanProof
import YangMills.Construction.ResponseInTheExpansion.MeanOfATwiceDominatedFamily
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.LinearResponse
namespace GibbsMeanDerivatives
variable {Ω : Type} [MeasurableSpace Ω] {k : ℕ}
section Dominated
variable {μ : Measure Ω} {B : Set (Fin k → ℝ)}
def IsDominated (μ : Measure Ω) (n : ℕ) (B : Set (Fin k → ℝ)) (G : (Fin k → ℝ) → Ω → ℝ) : Prop :=
  ∃ K, IsDominatedSmoothFamily μ n B K G
omit [MeasurableSpace Ω] in
theorem paramIteratedDeriv_single (G : (Fin k → ℝ) → Ω → ℝ) (u : Fin k → ℝ) :
    paramIteratedDeriv G ![u] = fun τ ω => fderiv ℝ (fun τ' => G τ' ω) τ u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.paramIteratedDeriv_one <;> assumption
theorem IsDominated.mono {G : (Fin k → ℝ) → Ω → ℝ} {n m : ℕ} (h : IsDominated μ n B G) (hmn : m ≤ n) :
    IsDominated μ m B G := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsDominated.mono <;> assumption
theorem IsDominated.paramDeriv (hB : IsOpen B) {G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ} (h : IsDominated μ (n + 1) B G)
    (u : Fin k → ℝ) : IsDominated μ n B (paramIteratedDeriv G ![u]) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsDominated.paramDeriv <;> assumption
theorem IsDominated.sub (hB : IsOpen B) {G₁ G₂ : (Fin k → ℝ) → Ω → ℝ} {n : ℕ} (h₁ : IsDominated μ n B G₁)
    (h₂ : IsDominated μ n B G₂) : IsDominated μ n B (fun τ ω => G₁ τ ω - G₂ τ ω) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsDominated.sub <;> assumption
theorem IsDominated.mul (hB : IsOpen B) {G₁ G₂ : (Fin k → ℝ) → Ω → ℝ} {n : ℕ} (h₁ : IsDominated μ n B G₁)
    (h₂ : IsDominated μ n B G₂) : IsDominated μ n B (fun τ ω => G₁ τ ω * G₂ τ ω) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsDominated.mul <;> assumption
theorem IsDominated.expNeg (hB : IsOpen B) {A : (Fin k → ℝ) → Ω → ℝ} {n : ℕ} (h : IsDominated μ n B A) :
    IsDominated μ n B (fun τ ω => Real.exp (- A τ ω)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsDominated.exp_neg <;> assumption
end Dominated
section Means
variable {μ : Measure Ω} {B : Set (Fin k → ℝ)}
def IsEssBounded (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  AEStronglyMeasurable f μ ∧ ∃ C, ∀ᵐ ω ∂μ, |f ω| ≤ C
theorem IsEssBounded.mul {f g : Ω → ℝ} (hf : IsEssBounded μ f) (hg : IsEssBounded μ g) :
    IsEssBounded μ (fun ω => f ω * g ω) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsEssBounded.mul <;> assumption
theorem IsEssBounded.sub {f g : Ω → ℝ} (hf : IsEssBounded μ f) (hg : IsEssBounded μ g) :
    IsEssBounded μ (fun ω => f ω - g ω) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.AEBounded.sub <;> assumption
theorem IsEssBounded.integrable [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : IsEssBounded μ f) : Integrable f μ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsEssBounded.integrable <;> assumption
theorem IsEssBounded.expNeg {A : Ω → ℝ} (hA : IsEssBounded μ A) : IsEssBounded μ (fun ω => Real.exp (- A ω)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsEssBounded.exp_neg <;> assumption
theorem gibbsMean_add [IsFiniteMeasure μ] {A f g : Ω → ℝ} (hA : IsEssBounded μ A) (hf : IsEssBounded μ f)
    (hg : IsEssBounded μ g) :
    gibbsMean μ A (fun ω => f ω + g ω) = gibbsMean μ A f + gibbsMean μ A g := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.gibbsMean_add <;> assumption
theorem gibbsMean_sub [IsFiniteMeasure μ] {A f g : Ω → ℝ} (hA : IsEssBounded μ A) (hf : IsEssBounded μ f)
    (hg : IsEssBounded μ g) :
    gibbsMean μ A (fun ω => f ω - g ω) = gibbsMean μ A f - gibbsMean μ A g := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.gibbsMean_sub <;> assumption
theorem gibbsMean_congr_ae {A f g : Ω → ℝ} (h : f =ᵐ[μ] g) : gibbsMean μ A f = gibbsMean μ A g := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.gibbsMean_congr_ae <;> assumption
theorem IsDominated.isEssBounded {G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ} (h : IsDominated μ n B G) {τ : Fin k → ℝ}
    (hτ : τ ∈ B) : IsEssBounded μ (G τ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsDominated.isEssBounded <;> assumption
def paramGibbsMean (μ : Measure Ω) (A G : (Fin k → ℝ) → Ω → ℝ) : (Fin k → ℝ) → ℝ :=
  fun τ => gibbsMean μ (A τ) (G τ)
def responseShift (A G : (Fin k → ℝ) → Ω → ℝ) (u : Fin k → ℝ) : (Fin k → ℝ) → Ω → ℝ :=
  fun τ ω => paramIteratedDeriv G ![u] τ ω - G τ ω * paramIteratedDeriv A ![u] τ ω
theorem IsDominated.responseShift (hB : IsOpen B) {A G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ}
    (hA : IsDominated μ (n + 1) B A) (hG : IsDominated μ (n + 1) B G) (u : Fin k → ℝ) :
    IsDominated μ n B (responseShift A G u) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsDominated.centeredDeriv <;> assumption
theorem paramGibbsMean_contDiffOn_and_fderiv [IsFiniteMeasure μ] (hB : IsOpen B) (hμ : μ ≠ 0) {A G : (Fin k → ℝ) → Ω → ℝ}
    {n : ℕ} (hA : IsDominated μ (n + 1) B A) (hG : IsDominated μ (n + 1) B G) :
    ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (paramGibbsMean μ A G) B ∧
      ∀ τ ∈ B, ∀ u, fderiv ℝ (paramGibbsMean μ A G) τ u =
        paramGibbsMean μ A (responseShift A G u) τ +
          paramGibbsMean μ A G τ * paramGibbsMean μ A (paramIteratedDeriv A ![u]) τ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.gibbsMeanFamily_contDiffOn_and_fderiv <;> assumption
end Means
section Pure
variable {B : Set (Fin k → ℝ)}
def dirDeriv (g : (Fin k → ℝ) → ℝ) (u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  fun τ => iteratedFDeriv ℝ 1 g τ ![u]
def dirDerivTwo (g : (Fin k → ℝ) → ℝ) (v u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  fun τ => iteratedFDeriv ℝ 2 g τ ![v, u]
theorem dirDeriv_apply (g : (Fin k → ℝ) → ℝ) (u τ : Fin k → ℝ) : dirDeriv g u τ = fderiv ℝ g τ u := by
  simp [dirDeriv, iteratedFDeriv_one_apply]
theorem fderiv_iteratedFDeriv_apply_eq_cons {j : ℕ} {g : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    (hg : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) g τ) (w : Fin k → ℝ) (m : Fin j → Fin k → ℝ) :
    DifferentiableAt ℝ (fun τ' => iteratedFDeriv ℝ j g τ' m) τ ∧
      fderiv ℝ (fun τ' => iteratedFDeriv ℝ j g τ' m) τ w =
        iteratedFDeriv ℝ (j + 1) g τ (Fin.cons w m) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.fderiv_iteratedFDeriv_apply_eq_cons <;> assumption
theorem dirDeriv_differentiableAt_and_fderiv {g : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    (hg : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) g τ) (v u : Fin k → ℝ) :
    DifferentiableAt ℝ (dirDeriv g u) τ ∧ fderiv ℝ (dirDeriv g u) τ v = dirDerivTwo g v u τ :=
  fderiv_iteratedFDeriv_apply_eq_cons (j := 1) hg v ![u]
def shiftOp (α : (Fin k → ℝ) → ℝ) (u : Fin k → ℝ) (g : (Fin k → ℝ) → ℝ) : (Fin k → ℝ) → ℝ :=
  dirDeriv g u - g * dirDeriv α u
def shiftOpTwiceExpansion (h α : (Fin k → ℝ) → ℝ) (v u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  dirDerivTwo h v u - dirDeriv h u * dirDeriv α v - dirDeriv h v * dirDeriv α u - h * dirDerivTwo α v u + h * dirDeriv α u * dirDeriv α v
theorem shiftOp_shiftOp {h α : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    (hh : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) h τ) (hα : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) α τ)
    (v u : Fin k → ℝ) : shiftOp α v (shiftOp α u h) τ = shiftOpTwiceExpansion h α v u τ := by
  have n2 : ((2 : ℕ) : WithTop ℕ∞) ≠ 0 := by norm_num
  have H0 := (hh.differentiableAt n2).hasFDerivAt
  obtain ⟨D1, F1⟩ := dirDeriv_differentiableAt_and_fderiv hh v u
  obtain ⟨D2, F2⟩ := dirDeriv_differentiableAt_and_fderiv hα v u
  have e := D1.hasFDerivAt.sub (H0.mul D2.hasFDerivAt)
  have e' : dirDeriv (shiftOp α u h) v τ = fderiv ℝ (dirDeriv h u - h * dirDeriv α u) τ v := dirDeriv_apply _ _ _
  simp only [shiftOp, Pi.sub_apply, Pi.mul_apply] at e' ⊢
  rw [e', e.fderiv]
  simp only [sub_apply, add_apply,
    smul_apply, smul_eq_mul, F1, F2, shiftOpTwiceExpansion, Pi.add_apply, Pi.sub_apply,
    Pi.mul_apply, ← dirDeriv_apply]
  ring
theorem shiftOp_dirDeriv {α : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    (hα : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) α τ) (v u : Fin k → ℝ) :
    shiftOp α v (dirDeriv α u) τ = dirDerivTwo α v u τ - dirDeriv α u τ * dirDeriv α v τ := by
  simp only [shiftOp, Pi.sub_apply, Pi.mul_apply, dirDeriv_apply _ v, (dirDeriv_differentiableAt_and_fderiv hα v u).2]
end Pure
section Main
variable {μ : Measure Ω} {B : Set (Fin k → ℝ)}
theorem paramIteratedDeriv_isEssBounded [IsFiniteMeasure μ] (hB : IsOpen B) {G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ} {K : ℝ}
    (hG : IsDominatedSmoothFamily μ n B K G) {τ : Fin k → ℝ} (hτ : τ ∈ B) {j : ℕ} (hj : j ≤ n)
    (v : Fin j → Fin k → ℝ) : IsEssBounded μ (paramIteratedDeriv G v τ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.isEssBounded_paramIteratedDeriv <;> assumption
theorem gibbsMean_sub_sub_sub_add [IsFiniteMeasure μ] {A x₁ x₂ x₃ x₄ x₅ : Ω → ℝ} (hA : IsEssBounded μ A) (b₁ : IsEssBounded μ x₁)
    (b₂ : IsEssBounded μ x₂) (b₃ : IsEssBounded μ x₃) (b₄ : IsEssBounded μ x₄) (b₅ : IsEssBounded μ x₅) :
    gibbsMean μ A (fun ω => x₁ ω - x₂ ω - x₃ ω - x₄ ω + x₅ ω) =
      gibbsMean μ A x₁ - gibbsMean μ A x₂ - gibbsMean μ A x₃ - gibbsMean μ A x₄ +
        gibbsMean μ A x₅ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.gibbsMean_sum_five <;> assumption
theorem gibbsMean_contDiffOn_two_and_iteratedFDeriv [IsFiniteMeasure μ] (hB : IsOpen B) (hμ : μ ≠ 0) {K : ℝ}
    {A H : (Fin k → ℝ) → Ω → ℝ} (hA : IsDominatedSmoothFamily μ 2 B K A)
    (hH : IsDominatedSmoothFamily μ 2 B K H) :
    ContDiffOn ℝ 2 (fun τ => gibbsMean μ (A τ) (H τ)) B ∧
      ∀ τ ∈ B, ∀ u v : Fin k → ℝ,
        iteratedFDeriv ℝ 1 (fun τ => gibbsMean μ (A τ) (H τ)) τ ![u] =
          gibbsMean μ (A τ) (paramIteratedDeriv H ![u] τ) -
            gibbsCovariance μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ) ∧
        iteratedFDeriv ℝ 2 (fun τ => gibbsMean μ (A τ) (H τ)) τ ![v, u] =
          gibbsMean μ (A τ) (paramIteratedDeriv H ![v, u] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![v] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![u] τ) -
            gibbsCovariance μ (A τ) (H τ) (paramIteratedDeriv A ![v, u] τ) +
            gibbsCumulantThree μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ) (paramIteratedDeriv A ![v] τ) := by
  have DA : IsDominated μ 2 B A := ⟨K, hA⟩
  have DH : IsDominated μ 2 B H := ⟨K, hH⟩
  have DA1 : IsDominated μ 1 B A := DA.mono (by omega)
  have Da : ∀ u, IsDominated μ 1 B (paramIteratedDeriv A ![u]) := fun u => IsDominated.paramDeriv hB DA u
  have DS : ∀ u, IsDominated μ 1 B (responseShift A H u) := fun u => IsDominated.responseShift hB DA DH u
  have R2 := paramGibbsMean_contDiffOn_and_fderiv hB hμ (n := 1) DA DH
  have R1 : ∀ G, IsDominated μ 1 B G → ContDiffOn ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (paramGibbsMean μ A G) B ∧
      ∀ τ ∈ B, ∀ u, fderiv ℝ (paramGibbsMean μ A G) τ u = paramGibbsMean μ A (responseShift A G u) τ +
        paramGibbsMean μ A G τ * paramGibbsMean μ A (paramIteratedDeriv A ![u]) τ :=
    fun G hG => paramGibbsMean_contDiffOn_and_fderiv hB hμ (n := 0) DA1 hG
  have c2 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) (paramGibbsMean μ A H) B := by simpa using R2.1
  have c2' : ContDiffOn ℝ 2 (paramGibbsMean μ A H) B := by simpa using c2
  refine ⟨c2', fun τ hτ u v => ?_⟩
  have d2f : ∀ σ ∈ B, DifferentiableAt ℝ (paramGibbsMean μ A H) σ := fun σ hσ =>
    (c2.contDiffAt (hB.mem_nhds hσ)).differentiableAt (by norm_num)
  have d1f : ∀ G, IsDominated μ 1 B G → ∀ σ ∈ B, DifferentiableAt ℝ (paramGibbsMean μ A G) σ := fun G hG σ hσ =>
    ((R1 G hG).1.contDiffAt (hB.mem_nhds hσ)).differentiableAt (by norm_num)
  have e1 : ∀ u, ∀ σ ∈ B, iteratedFDeriv ℝ 1 (paramGibbsMean μ A H) σ ![u] =
      (paramGibbsMean μ A (responseShift A H u) + paramGibbsMean μ A H * paramGibbsMean μ A (paramIteratedDeriv A ![u])) σ := by
    intro u σ hσ
    rw [iteratedFDeriv_one_apply]
    exact R2.2 σ hσ u
  have e2f : iteratedFDeriv ℝ 2 (paramGibbsMean μ A H) τ ![v, u] =
      (paramGibbsMean μ A (responseShift A (responseShift A H u) v) +
          paramGibbsMean μ A (responseShift A H u) * paramGibbsMean μ A (paramIteratedDeriv A ![v]) +
        (paramGibbsMean μ A (responseShift A H v) + paramGibbsMean μ A H * paramGibbsMean μ A (paramIteratedDeriv A ![v])) *
          paramGibbsMean μ A (paramIteratedDeriv A ![u]) +
        paramGibbsMean μ A H * (paramGibbsMean μ A (responseShift A (paramIteratedDeriv A ![u]) v) +
          paramGibbsMean μ A (paramIteratedDeriv A ![u]) * paramGibbsMean μ A (paramIteratedDeriv A ![v]))) τ := by
    have ci := (fderiv_iteratedFDeriv_apply_eq_cons (j := 1) (g := paramGibbsMean μ A H) (τ := τ)
      (c2.contDiffAt (hB.mem_nhds hτ)) v ![u]).2
    have ev : (fun τ' => iteratedFDeriv ℝ 1 (paramGibbsMean μ A H) τ' ![u]) =ᶠ[𝓝 τ]
        (paramGibbsMean μ A (responseShift A H u) + paramGibbsMean μ A H * paramGibbsMean μ A (paramIteratedDeriv A ![u])) := by
      filter_upwards [hB.mem_nhds hτ] with ρ hρ
      exact e1 u ρ hρ
    have hX := (d1f _ (DS u) τ hτ).hasFDerivAt.add
      ((d2f τ hτ).hasFDerivAt.mul (d1f _ (Da u) τ hτ).hasFDerivAt)
    have ci' : iteratedFDeriv ℝ 2 (paramGibbsMean μ A H) τ ![v, u] =
        fderiv ℝ (paramGibbsMean μ A (responseShift A H u) + paramGibbsMean μ A H * paramGibbsMean μ A (paramIteratedDeriv A ![u])) τ v := by
      rw [← ev.fderiv_eq]
      exact ci.symm
    rw [ci', hX.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, Pi.add_apply, Pi.mul_apply,
      (R1 _ (DS u)).2 τ hτ v, (R1 _ (Da u)).2 τ hτ v, R2.2 τ hτ v]
    ring
  have bA : IsEssBounded μ (A τ) := DA.isEssBounded hτ
  have bH : IsEssBounded μ (H τ) := DH.isEssBounded hτ
  have bh1 : ∀ u, IsEssBounded μ (paramIteratedDeriv H ![u] τ) := fun u =>
    paramIteratedDeriv_isEssBounded hB hH hτ (j := 1) (by omega) ![u]
  have ba1 : ∀ u, IsEssBounded μ (paramIteratedDeriv A ![u] τ) := fun u =>
    paramIteratedDeriv_isEssBounded hB hA hτ (j := 1) (by omega) ![u]
  have bh2 : ∀ v u, IsEssBounded μ (paramIteratedDeriv H ![v, u] τ) := fun v u =>
    paramIteratedDeriv_isEssBounded hB hH hτ (j := 2) (by omega) ![v, u]
  have ba2 : ∀ v u, IsEssBounded μ (paramIteratedDeriv A ![v, u] τ) := fun v u =>
    paramIteratedDeriv_isEssBounded hB hA hτ (j := 2) (by omega) ![v, u]
  have mS : ∀ u, paramGibbsMean μ A (responseShift A H u) τ = gibbsMean μ (A τ) (paramIteratedDeriv H ![u] τ) -
      gibbsMean μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![u] τ ω) := fun u =>
    gibbsMean_sub bA (bh1 u) (bH.mul (ba1 u))
  have c3H : ∀ᵐ ω ∂μ, ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) (fun τ => H τ ω) B ∧
      ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) (fun τ => A τ ω) B := by
    filter_upwards [hH.contDiffOn, hA.contDiffOn] with ω a b
    exact ⟨a, b⟩
  have at2 : ∀ {g : (Fin k → ℝ) → ℝ}, ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) g B →
      ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) g τ := fun hg => hg.contDiffAt (hB.mem_nhds hτ)
  have mSS : paramGibbsMean μ A (responseShift A (responseShift A H u) v) τ =
      gibbsMean μ (A τ) (paramIteratedDeriv H ![v, u] τ) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv H ![u] τ ω * paramIteratedDeriv A ![v] τ ω) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv H ![v] τ ω * paramIteratedDeriv A ![u] τ ω) -
        gibbsMean μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![v, u] τ ω) +
        gibbsMean μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![u] τ ω * paramIteratedDeriv A ![v] τ ω) := by
    rw [← gibbsMean_sub_sub_sub_add bA (bh2 v u) ((bh1 u).mul (ba1 v)) ((bh1 v).mul (ba1 u)) (bH.mul (ba2 v u))
      ((bH.mul (ba1 u)).mul (ba1 v))]
    refine gibbsMean_congr_ae ?_
    filter_upwards [c3H] with ω a
    exact shiftOp_shiftOp (at2 a.1) (at2 a.2) v u
  have mSa : paramGibbsMean μ A (responseShift A (paramIteratedDeriv A ![u]) v) τ =
      gibbsMean μ (A τ) (paramIteratedDeriv A ![v, u] τ) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv A ![u] τ ω * paramIteratedDeriv A ![v] τ ω) := by
    rw [← gibbsMean_sub bA (ba2 v u) ((ba1 u).mul (ba1 v))]
    refine gibbsMean_congr_ae ?_
    filter_upwards [c3H] with ω a
    exact shiftOp_dirDeriv (at2 a.2) v u
  have hM : ∀ G : (Fin k → ℝ) → Ω → ℝ, paramGibbsMean μ A G τ = gibbsMean μ (A τ) (G τ) := fun _ => rfl
  refine ⟨?_, ?_⟩
  · have := e1 u τ hτ
    simp only [Pi.add_apply, Pi.mul_apply] at this
    change iteratedFDeriv ℝ 1 (paramGibbsMean μ A H) τ ![u] = _
    rw [this, mS u, hM H, hM (paramIteratedDeriv A ![u])]
    simp only [gibbsCovariance]
    ring
  · have := e2f
    simp only [Pi.add_apply, Pi.mul_apply] at this
    change iteratedFDeriv ℝ 2 (paramGibbsMean μ A H) τ ![v, u] = _
    rw [this, mSS, mS u, mS v, mSa, hM H, hM (paramIteratedDeriv A ![u]), hM (paramIteratedDeriv A ![v])]
    simp only [gibbsCovariance, gibbsCumulantThree]
    ring
end Main
end GibbsMeanDerivatives
theorem gibbsMeanSecondDerivative_holds : GibbsMeanSecondDerivative := by
  intro Ω _ μ _ k B K A H hB hμ hA hH
  exact GibbsMeanDerivatives.gibbsMean_contDiffOn_two_and_iteratedFDeriv hB hμ hA hH
end YangMills.Construction.LinearResponse
end

import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMeanProof
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOverASecondMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.TiltedMeans
namespace GibbsCalculus
variable {Ω : Type} [MeasurableSpace Ω] {k : ℕ}
theorem contDiffOn_integral_and_iteratedFDeriv (μ : Measure Ω) [IsFiniteMeasure μ]
    {B : Set (Fin k → ℝ)} (hB : IsOpen B) (K : ℝ) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (G : (Fin k → ℝ) → Ω → F),
      (∀ τ ∈ B, AEStronglyMeasurable (G τ) μ) →
      (∀ᵐ ω ∂μ, ContDiffOn ℝ n (fun τ => G τ ω) B) →
      (∀ᵐ ω ∂μ, ∀ j, j ≤ n → ∀ τ ∈ B, ‖iteratedFDeriv ℝ j (fun τ => G τ ω) τ‖ ≤ K) →
      ContDiffOn ℝ n (fun τ => ∫ ω, G τ ω ∂μ) B ∧
      ∀ τ ∈ B, ∀ j, j ≤ n → ∀ v : Fin j → Fin k → ℝ,
        AEStronglyMeasurable (fun ω => iteratedFDeriv ℝ j (fun τ' => G τ' ω) τ v) μ ∧
        iteratedFDeriv ℝ j (fun τ => ∫ ω, G τ ω ∂μ) τ v =
          ∫ ω, iteratedFDeriv ℝ j (fun τ' => G τ' ω) τ v ∂μ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.contDiffOn_integral_and_iteratedFDeriv <;> assumption
section
variable {μ : Measure Ω} {B : Set (Fin k → ℝ)}
def IsDominated (μ : Measure Ω) (n : ℕ) (B : Set (Fin k → ℝ)) (G : (Fin k → ℝ) → Ω → ℝ) : Prop :=
  ∃ K, IsDominatedSmoothFamily μ n B K G
omit [MeasurableSpace Ω] in
theorem paramIteratedDeriv_single (G : (Fin k → ℝ) → Ω → ℝ) (u : Fin k → ℝ) :
    paramIteratedDeriv G ![u] = fun τ ω => fderiv ℝ (fun τ' => G τ' ω) τ u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.paramIteratedDeriv_one <;> assumption
theorem IsDominated.mono {G : (Fin k → ℝ) → Ω → ℝ} {n m : ℕ} (h : IsDominated μ n B G)
    (hmn : m ≤ n) : IsDominated μ m B G := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsDominated.mono <;> assumption
theorem IsDominated.paramDeriv (hB : IsOpen B) {G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ}
    (h : IsDominated μ (n + 1) B G) (u : Fin k → ℝ) :
    IsDominated μ n B (paramIteratedDeriv G ![u]) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsDominated.paramDeriv <;> assumption
theorem IsDominated.sub (hB : IsOpen B) {G₁ G₂ : (Fin k → ℝ) → Ω → ℝ} {n : ℕ}
    (h₁ : IsDominated μ n B G₁) (h₂ : IsDominated μ n B G₂) :
    IsDominated μ n B (fun τ ω => G₁ τ ω - G₂ τ ω) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsDominated.sub <;> assumption
theorem IsDominated.mul (hB : IsOpen B) {G₁ G₂ : (Fin k → ℝ) → Ω → ℝ} {n : ℕ}
    (h₁ : IsDominated μ n B G₁) (h₂ : IsDominated μ n B G₂) :
    IsDominated μ n B (fun τ ω => G₁ τ ω * G₂ τ ω) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsDominated.mul <;> assumption
theorem IsDominated.exp_neg (hB : IsOpen B) {A : (Fin k → ℝ) → Ω → ℝ} {n : ℕ}
    (h : IsDominated μ n B A) : IsDominated μ n B (fun τ ω => Real.exp (- A τ ω)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsDominated.exp_neg <;> assumption
end
section
variable {μ : Measure Ω} {B : Set (Fin k → ℝ)}
def IsBoundedMeasurable (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  AEStronglyMeasurable f μ ∧ ∃ C, ∀ᵐ ω ∂μ, |f ω| ≤ C
theorem IsBoundedMeasurable.mul {f g : Ω → ℝ} (hf : IsBoundedMeasurable μ f)
    (hg : IsBoundedMeasurable μ g) : IsBoundedMeasurable μ (fun ω => f ω * g ω) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsEssBounded.mul <;> assumption
theorem IsBoundedMeasurable.add {f g : Ω → ℝ} (hf : IsBoundedMeasurable μ f)
    (hg : IsBoundedMeasurable μ g) : IsBoundedMeasurable μ (fun ω => f ω + g ω) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.AEBounded.add <;> assumption
theorem IsBoundedMeasurable.sub {f g : Ω → ℝ} (hf : IsBoundedMeasurable μ f)
    (hg : IsBoundedMeasurable μ g) : IsBoundedMeasurable μ (fun ω => f ω - g ω) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.AEBounded.sub <;> assumption
theorem IsBoundedMeasurable.integrable [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : IsBoundedMeasurable μ f) : Integrable f μ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsEssBounded.integrable <;> assumption
theorem IsBoundedMeasurable.exp_neg {A : Ω → ℝ} (hA : IsBoundedMeasurable μ A) :
    IsBoundedMeasurable μ (fun ω => Real.exp (- A ω)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsEssBounded.exp_neg <;> assumption
theorem gibbsMean_add [IsFiniteMeasure μ] {A f g : Ω → ℝ} (hA : IsBoundedMeasurable μ A)
    (hf : IsBoundedMeasurable μ f) (hg : IsBoundedMeasurable μ g) :
    gibbsMean μ A (fun ω => f ω + g ω) = gibbsMean μ A f + gibbsMean μ A g := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.gibbsMean_add <;> assumption
theorem gibbsMean_sub [IsFiniteMeasure μ] {A f g : Ω → ℝ} (hA : IsBoundedMeasurable μ A)
    (hf : IsBoundedMeasurable μ f) (hg : IsBoundedMeasurable μ g) :
    gibbsMean μ A (fun ω => f ω - g ω) = gibbsMean μ A f - gibbsMean μ A g := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.gibbsMean_sub <;> assumption
theorem gibbsMean_congr_ae {A f g : Ω → ℝ} (h : f =ᵐ[μ] g) : gibbsMean μ A f = gibbsMean μ A g := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.gibbsMean_congr_ae <;> assumption
theorem IsDominated.isBoundedMeasurable {G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ}
    (h : IsDominated μ n B G) {τ : Fin k → ℝ} (hτ : τ ∈ B) : IsBoundedMeasurable μ (G τ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsDominated.isEssBounded <;> assumption
def gibbsMeanCurve (μ : Measure Ω) (A G : (Fin k → ℝ) → Ω → ℝ) : (Fin k → ℝ) → ℝ :=
  fun τ => gibbsMean μ (A τ) (G τ)
def gibbsShift (A G : (Fin k → ℝ) → Ω → ℝ) (u : Fin k → ℝ) : (Fin k → ℝ) → Ω → ℝ :=
  fun τ ω => paramIteratedDeriv G ![u] τ ω - G τ ω * paramIteratedDeriv A ![u] τ ω
theorem IsDominated.shift (hB : IsOpen B) {A G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ}
    (hA : IsDominated μ (n + 1) B A) (hG : IsDominated μ (n + 1) B G) (u : Fin k → ℝ) :
    IsDominated μ n B (gibbsShift A G u) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.IsDominated.centeredDeriv <;> assumption
theorem gibbsMeanCurve_fderiv [IsFiniteMeasure μ] (hB : IsOpen B) (hμ : μ ≠ 0)
    {A G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ} (hA : IsDominated μ (n + 1) B A)
    (hG : IsDominated μ (n + 1) B G) :
    ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (gibbsMeanCurve μ A G) B ∧
      ∀ τ ∈ B, ∀ u, fderiv ℝ (gibbsMeanCurve μ A G) τ u =
        gibbsMeanCurve μ A (gibbsShift A G u) τ +
          gibbsMeanCurve μ A G τ * gibbsMeanCurve μ A (paramIteratedDeriv A ![u]) τ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.gibbsMeanFamily_contDiffOn_and_fderiv <;> assumption
end
section
variable {B : Set (Fin k → ℝ)}
def firstDirDeriv (g : (Fin k → ℝ) → ℝ) (u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  fun τ => iteratedFDeriv ℝ 1 g τ ![u]
def secondDirDeriv (g : (Fin k → ℝ) → ℝ) (v u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  fun τ => iteratedFDeriv ℝ 2 g τ ![v, u]
def thirdDirDeriv (g : (Fin k → ℝ) → ℝ) (w v u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  fun τ => iteratedFDeriv ℝ 3 g τ ![w, v, u]
theorem firstDirDeriv_eq_fderiv (g : (Fin k → ℝ) → ℝ) (u τ : Fin k → ℝ) :
    firstDirDeriv g u τ = fderiv ℝ g τ u := by
  simp [firstDirDeriv, iteratedFDeriv_one_apply]
theorem iteratedFDeriv_apply_fderiv {j : ℕ} {g : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    (hg : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) g τ) (w : Fin k → ℝ) (m : Fin j → Fin k → ℝ) :
    DifferentiableAt ℝ (fun τ' => iteratedFDeriv ℝ j g τ' m) τ ∧
      fderiv ℝ (fun τ' => iteratedFDeriv ℝ j g τ' m) τ w =
        iteratedFDeriv ℝ (j + 1) g τ (Fin.cons w m) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.fderiv_iteratedFDeriv_apply_eq_cons <;> assumption
theorem firstDirDeriv_differentiableAt_fderiv {g : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    (hg : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) g τ) (v u : Fin k → ℝ) :
    DifferentiableAt ℝ (firstDirDeriv g u) τ ∧
      fderiv ℝ (firstDirDeriv g u) τ v = secondDirDeriv g v u τ :=
  iteratedFDeriv_apply_fderiv (j := 1) hg v ![u]
theorem secondDirDeriv_differentiableAt_fderiv {g : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    (hg : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) g τ) (w v u : Fin k → ℝ) :
    DifferentiableAt ℝ (secondDirDeriv g v u) τ ∧
      fderiv ℝ (secondDirDeriv g v u) τ w = thirdDirDeriv g w v u τ :=
  iteratedFDeriv_apply_fderiv (j := 2) hg w ![v, u]
def shiftedDeriv (α : (Fin k → ℝ) → ℝ) (u : Fin k → ℝ) (g : (Fin k → ℝ) → ℝ) :
    (Fin k → ℝ) → ℝ :=
  firstDirDeriv g u - g * firstDirDeriv α u
def shiftedDerivTwoExpansion (h α : (Fin k → ℝ) → ℝ) (v u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  secondDirDeriv h v u - firstDirDeriv h u * firstDirDeriv α v -
    firstDirDeriv h v * firstDirDeriv α u - h * secondDirDeriv α v u +
    h * firstDirDeriv α u * firstDirDeriv α v
def shiftedDerivThreeExpansion (h α : (Fin k → ℝ) → ℝ) (w v u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  thirdDirDeriv h w v u - secondDirDeriv h v u * firstDirDeriv α w -
    secondDirDeriv h w u * firstDirDeriv α v - secondDirDeriv h w v * firstDirDeriv α u -
    firstDirDeriv h u * secondDirDeriv α w v - firstDirDeriv h v * secondDirDeriv α w u -
    firstDirDeriv h w * secondDirDeriv α v u +
    firstDirDeriv h u * firstDirDeriv α v * firstDirDeriv α w +
    firstDirDeriv h v * firstDirDeriv α u * firstDirDeriv α w +
    firstDirDeriv h w * firstDirDeriv α u * firstDirDeriv α v -
    h * thirdDirDeriv α w v u + h * secondDirDeriv α v u * firstDirDeriv α w +
    h * secondDirDeriv α w u * firstDirDeriv α v + h * secondDirDeriv α w v * firstDirDeriv α u -
    h * firstDirDeriv α u * firstDirDeriv α v * firstDirDeriv α w
def shiftedDerivDerivExpansion (α : (Fin k → ℝ) → ℝ) (w v u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  thirdDirDeriv α w v u - secondDirDeriv α v u * firstDirDeriv α w -
    secondDirDeriv α w u * firstDirDeriv α v - secondDirDeriv α w v * firstDirDeriv α u +
    firstDirDeriv α u * firstDirDeriv α v * firstDirDeriv α w
theorem shiftedDeriv_shiftedDeriv {h α : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    (hh : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) h τ) (hα : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) α τ)
    (v u : Fin k → ℝ) :
    shiftedDeriv α v (shiftedDeriv α u h) τ = shiftedDerivTwoExpansion h α v u τ := by
  have n2 : ((2 : ℕ) : WithTop ℕ∞) ≠ 0 := by norm_num
  have H0 := (hh.differentiableAt n2).hasFDerivAt
  obtain ⟨D1, F1⟩ := firstDirDeriv_differentiableAt_fderiv hh v u
  obtain ⟨D2, F2⟩ := firstDirDeriv_differentiableAt_fderiv hα v u
  have e := D1.hasFDerivAt.sub (H0.mul D2.hasFDerivAt)
  have e' : firstDirDeriv (shiftedDeriv α u h) v τ =
      fderiv ℝ (firstDirDeriv h u - h * firstDirDeriv α u) τ v := firstDirDeriv_eq_fderiv _ _ _
  simp only [shiftedDeriv, Pi.sub_apply, Pi.mul_apply] at e' ⊢
  rw [e', e.fderiv]
  simp only [sub_apply, add_apply,
    smul_apply, smul_eq_mul, F1, F2, shiftedDerivTwoExpansion, Pi.add_apply, Pi.sub_apply,
    Pi.mul_apply, ← firstDirDeriv_eq_fderiv]
  ring
theorem shiftedDeriv_shiftedDeriv_shiftedDeriv {h α : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    {B : Set (Fin k → ℝ)} (hB : IsOpen B)
    (hτ : τ ∈ B) (hh : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) h B)
    (hα : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) α B) (w v u : Fin k → ℝ) :
    shiftedDeriv α w (shiftedDeriv α v (shiftedDeriv α u h)) τ =
      shiftedDerivThreeExpansion h α w v u τ := by
  have n3 : ((3 : ℕ) : WithTop ℕ∞) ≠ 0 := by norm_num
  have c3 : ∀ {g : (Fin k → ℝ) → ℝ}, ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) g B → ∀ σ ∈ B,
      ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) g σ := fun hg σ hσ => hg.contDiffAt (hB.mem_nhds hσ)
  have c2 : ∀ {g : (Fin k → ℝ) → ℝ}, ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) g B → ∀ σ ∈ B,
      ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) g σ := fun hg σ hσ =>
    (c3 hg σ hσ).of_le (by norm_num)
  have heq : shiftedDeriv α v (shiftedDeriv α u h) =ᶠ[𝓝 τ] shiftedDerivTwoExpansion h α v u := by
    filter_upwards [hB.mem_nhds hτ] with σ hσ
    exact shiftedDeriv_shiftedDeriv (c2 hh σ hσ) (c2 hα σ hσ) v u
  have H0 := ((c3 hh τ hτ).differentiableAt n3).hasFDerivAt
  obtain ⟨Dhu, Fhu⟩ := firstDirDeriv_differentiableAt_fderiv (c2 hh τ hτ) w u
  obtain ⟨Dhv, Fhv⟩ := firstDirDeriv_differentiableAt_fderiv (c2 hh τ hτ) w v
  obtain ⟨Dau, Fau⟩ := firstDirDeriv_differentiableAt_fderiv (c2 hα τ hτ) w u
  obtain ⟨Dav, Fav⟩ := firstDirDeriv_differentiableAt_fderiv (c2 hα τ hτ) w v
  obtain ⟨Dh2, Fh2⟩ := secondDirDeriv_differentiableAt_fderiv (c3 hh τ hτ) w v u
  obtain ⟨Da2, Fa2⟩ := secondDirDeriv_differentiableAt_fderiv (c3 hα τ hτ) w v u
  have e := (((Dh2.hasFDerivAt.sub (Dhu.hasFDerivAt.mul Dav.hasFDerivAt)).sub
    (Dhv.hasFDerivAt.mul Dau.hasFDerivAt)).sub (H0.mul Da2.hasFDerivAt)).add
      ((H0.mul Dau.hasFDerivAt).mul Dav.hasFDerivAt)
  have e' : firstDirDeriv (shiftedDeriv α v (shiftedDeriv α u h)) w τ =
      fderiv ℝ (shiftedDerivTwoExpansion h α v u) τ w := by
    rw [firstDirDeriv_eq_fderiv, heq.fderiv_eq]
  have e0 : shiftedDeriv α v (shiftedDeriv α u h) τ = shiftedDerivTwoExpansion h α v u τ :=
    heq.eq_of_nhds
  have e'' : fderiv ℝ (shiftedDerivTwoExpansion h α v u) τ = _ := e.fderiv
  have a1 : firstDirDeriv (shiftedDeriv α v (shiftedDeriv α u h)) w τ -
      shiftedDeriv α v (shiftedDeriv α u h) τ * firstDirDeriv α w τ =
      fderiv ℝ (shiftedDerivTwoExpansion h α v u) τ w -
        shiftedDerivTwoExpansion h α v u τ * firstDirDeriv α w τ := by rw [e', e0]
  change firstDirDeriv (shiftedDeriv α v (shiftedDeriv α u h)) w τ -
    shiftedDeriv α v (shiftedDeriv α u h) τ * firstDirDeriv α w τ = _
  rw [a1, e'']
  simp only [sub_apply, add_apply,
    smul_apply, smul_eq_mul, Fhu, Fhv, Fau, Fav, Fh2, Fa2, shiftedDerivTwoExpansion,
    shiftedDerivThreeExpansion, Pi.add_apply,
    Pi.sub_apply, Pi.mul_apply, ← firstDirDeriv_eq_fderiv]
  ring
theorem shiftedDeriv_firstDirDeriv {α : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    (hα : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) α τ) (v u : Fin k → ℝ) :
    shiftedDeriv α v (firstDirDeriv α u) τ =
      secondDirDeriv α v u τ - firstDirDeriv α u τ * firstDirDeriv α v τ := by
  simp only [shiftedDeriv, Pi.sub_apply, Pi.mul_apply, firstDirDeriv_eq_fderiv _ v,
    (firstDirDeriv_differentiableAt_fderiv hα v u).2]
theorem shiftedDeriv_shiftedDeriv_firstDirDeriv {α : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    {B : Set (Fin k → ℝ)} (hB : IsOpen B)
    (hτ : τ ∈ B) (hα : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) α B) (w v u : Fin k → ℝ) :
    shiftedDeriv α w (shiftedDeriv α v (firstDirDeriv α u)) τ =
      shiftedDerivDerivExpansion α w v u τ := by
  have c3 : ∀ σ ∈ B, ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) α σ := fun σ hσ =>
    hα.contDiffAt (hB.mem_nhds hσ)
  have c2 : ∀ σ ∈ B, ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) α σ := fun σ hσ =>
    (c3 σ hσ).of_le (by norm_num)
  have heq : shiftedDeriv α v (firstDirDeriv α u) =ᶠ[𝓝 τ]
      secondDirDeriv α v u - firstDirDeriv α u * firstDirDeriv α v := by
    filter_upwards [hB.mem_nhds hτ] with σ hσ
    exact shiftedDeriv_firstDirDeriv (c2 σ hσ) v u
  obtain ⟨Dau, Fau⟩ := firstDirDeriv_differentiableAt_fderiv (c2 τ hτ) w u
  obtain ⟨Dav, Fav⟩ := firstDirDeriv_differentiableAt_fderiv (c2 τ hτ) w v
  obtain ⟨Da2, Fa2⟩ := secondDirDeriv_differentiableAt_fderiv (c3 τ hτ) w v u
  have e := Da2.hasFDerivAt.sub (Dau.hasFDerivAt.mul Dav.hasFDerivAt)
  have e' : firstDirDeriv (shiftedDeriv α v (firstDirDeriv α u)) w τ =
      fderiv ℝ (secondDirDeriv α v u - firstDirDeriv α u * firstDirDeriv α v) τ w := by
    rw [firstDirDeriv_eq_fderiv, heq.fderiv_eq]
  have e0 : shiftedDeriv α v (firstDirDeriv α u) τ =
      (secondDirDeriv α v u - firstDirDeriv α u * firstDirDeriv α v) τ := heq.eq_of_nhds
  change firstDirDeriv (shiftedDeriv α v (firstDirDeriv α u)) w τ -
    shiftedDeriv α v (firstDirDeriv α u) τ * firstDirDeriv α w τ = _
  rw [e', e0, e.fderiv]
  simp only [sub_apply, add_apply,
    smul_apply, smul_eq_mul, Fau, Fav, Fa2, shiftedDerivDerivExpansion, Pi.add_apply,
    Pi.sub_apply, Pi.mul_apply, ← firstDirDeriv_eq_fderiv]
  ring
end
section
variable {μ : Measure Ω} {B : Set (Fin k → ℝ)}
theorem paramIteratedDeriv_isBoundedMeasurable [IsFiniteMeasure μ] (hB : IsOpen B)
    {G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ} {K : ℝ}
    (hG : IsDominatedSmoothFamily μ n B K G) {τ : Fin k → ℝ} (hτ : τ ∈ B) {j : ℕ} (hj : j ≤ n)
    (v : Fin j → Fin k → ℝ) : IsBoundedMeasurable μ (paramIteratedDeriv G v τ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.isEssBounded_paramIteratedDeriv <;> assumption
theorem gibbsMean_sub_sub_sub_add [IsFiniteMeasure μ] {A x₁ x₂ x₃ x₄ x₅ : Ω → ℝ}
    (hA : IsBoundedMeasurable μ A) (b₁ : IsBoundedMeasurable μ x₁)
    (b₂ : IsBoundedMeasurable μ x₂) (b₃ : IsBoundedMeasurable μ x₃)
    (b₄ : IsBoundedMeasurable μ x₄) (b₅ : IsBoundedMeasurable μ x₅) :
    gibbsMean μ A (fun ω => x₁ ω - x₂ ω - x₃ ω - x₄ ω + x₅ ω) =
      gibbsMean μ A x₁ - gibbsMean μ A x₂ - gibbsMean μ A x₃ - gibbsMean μ A x₄ +
        gibbsMean μ A x₅ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GibbsMeanDerivatives.gibbsMean_sum_five <;> assumption
end
section
variable {μ ν : Measure Ω} {B : Set (Fin k → ℝ)}
def tiltedMeanCurve (ν μ : Measure Ω) (A G : (Fin k → ℝ) → Ω → ℝ) : (Fin k → ℝ) → ℝ :=
  fun τ => tiltedMean ν μ (A τ) (G τ)
theorem IsBoundedMeasurable.of_absolutelyContinuous (hac : ν ≪ μ) {f : Ω → ℝ}
    (h : IsBoundedMeasurable μ f) : IsBoundedMeasurable ν f := by
  obtain ⟨mf, C, hC⟩ := h
  exact ⟨mf.mono_ac hac, C, hac.ae_le hC⟩
theorem IsDominated.of_absolutelyContinuous (hac : ν ≪ μ) {G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ}
    (h : IsDominated μ n B G) : IsDominated ν n B G := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, fun τ hτ => (hK.aestronglyMeasurable τ hτ).mono_ac hac, hac.ae_le hK.contDiffOn,
    hac.ae_le hK.norm_iteratedFDeriv_le⟩
theorem tiltedMean_add [IsFiniteMeasure ν] (hac : ν ≪ μ) {A f g : Ω → ℝ}
    (hA : IsBoundedMeasurable μ A) (hf : IsBoundedMeasurable μ f) (hg : IsBoundedMeasurable μ g) :
    tiltedMean ν μ A (fun ω => f ω + g ω) = tiltedMean ν μ A f + tiltedMean ν μ A g := by
  unfold tiltedMean
  rw [← add_div, ← integral_add ((hf.mul hA.exp_neg).of_absolutelyContinuous hac).integrable
    ((hg.mul hA.exp_neg).of_absolutelyContinuous hac).integrable]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [add_mul])
theorem tiltedMean_sub [IsFiniteMeasure ν] (hac : ν ≪ μ) {A f g : Ω → ℝ}
    (hA : IsBoundedMeasurable μ A) (hf : IsBoundedMeasurable μ f) (hg : IsBoundedMeasurable μ g) :
    tiltedMean ν μ A (fun ω => f ω - g ω) = tiltedMean ν μ A f - tiltedMean ν μ A g := by
  unfold tiltedMean
  rw [← sub_div, ← integral_sub ((hf.mul hA.exp_neg).of_absolutelyContinuous hac).integrable
    ((hg.mul hA.exp_neg).of_absolutelyContinuous hac).integrable]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [sub_mul])
theorem tiltedMean_congr_ae (hac : ν ≪ μ) {A f g : Ω → ℝ} (h : f =ᵐ[μ] g) :
    tiltedMean ν μ A f = tiltedMean ν μ A g := by
  unfold tiltedMean
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hac.ae_le h] with ω a
  rw [a]
theorem tiltedMean_sub_sub_sub_add [IsFiniteMeasure ν] (hac : ν ≪ μ) {A x₁ x₂ x₃ x₄ x₅ : Ω → ℝ}
    (hA : IsBoundedMeasurable μ A) (b₁ : IsBoundedMeasurable μ x₁)
    (b₂ : IsBoundedMeasurable μ x₂) (b₃ : IsBoundedMeasurable μ x₃)
    (b₄ : IsBoundedMeasurable μ x₄) (b₅ : IsBoundedMeasurable μ x₅) :
    tiltedMean ν μ A (fun ω => x₁ ω - x₂ ω - x₃ ω - x₄ ω + x₅ ω) =
      tiltedMean ν μ A x₁ - tiltedMean ν μ A x₂ - tiltedMean ν μ A x₃ - tiltedMean ν μ A x₄ +
        tiltedMean ν μ A x₅ := by
  have s₂ := b₁.sub b₂
  have s₃ := s₂.sub b₃
  have s₄ := s₃.sub b₄
  rw [tiltedMean_add hac hA s₄ b₅, tiltedMean_sub hac hA s₃ b₄, tiltedMean_sub hac hA s₂ b₃,
    tiltedMean_sub hac hA b₁ b₂]
theorem tiltedMean_fifteen_terms [IsFiniteMeasure ν] (hac : ν ≪ μ)
    {A x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅ : Ω → ℝ}
    (hA : IsBoundedMeasurable μ A) (b₁ : IsBoundedMeasurable μ x₁)
    (b₂ : IsBoundedMeasurable μ x₂) (b₃ : IsBoundedMeasurable μ x₃)
    (b₄ : IsBoundedMeasurable μ x₄) (b₅ : IsBoundedMeasurable μ x₅)
    (b₆ : IsBoundedMeasurable μ x₆) (b₇ : IsBoundedMeasurable μ x₇)
    (b₈ : IsBoundedMeasurable μ x₈) (b₉ : IsBoundedMeasurable μ x₉)
    (b₁₀ : IsBoundedMeasurable μ x₁₀) (b₁₁ : IsBoundedMeasurable μ x₁₁)
    (b₁₂ : IsBoundedMeasurable μ x₁₂) (b₁₃ : IsBoundedMeasurable μ x₁₃)
    (b₁₄ : IsBoundedMeasurable μ x₁₄) (b₁₅ : IsBoundedMeasurable μ x₁₅) :
    tiltedMean ν μ A (fun ω => x₁ ω - x₂ ω - x₃ ω - x₄ ω - x₅ ω - x₆ ω - x₇ ω + x₈ ω + x₉ ω +
        x₁₀ ω - x₁₁ ω + x₁₂ ω + x₁₃ ω + x₁₄ ω - x₁₅ ω) =
      tiltedMean ν μ A x₁ - tiltedMean ν μ A x₂ - tiltedMean ν μ A x₃ - tiltedMean ν μ A x₄ -
        tiltedMean ν μ A x₅ - tiltedMean ν μ A x₆ - tiltedMean ν μ A x₇ + tiltedMean ν μ A x₈ +
        tiltedMean ν μ A x₉ + tiltedMean ν μ A x₁₀ - tiltedMean ν μ A x₁₁ +
        tiltedMean ν μ A x₁₂ + tiltedMean ν μ A x₁₃ + tiltedMean ν μ A x₁₄ -
        tiltedMean ν μ A x₁₅ := by
  have s₂ := b₁.sub b₂
  have s₃ := s₂.sub b₃
  have s₄ := s₃.sub b₄
  have s₅ := s₄.sub b₅
  have s₆ := s₅.sub b₆
  have s₇ := s₆.sub b₇
  have s₈ := s₇.add b₈
  have s₉ := s₈.add b₉
  have s₁₀ := s₉.add b₁₀
  have s₁₁ := s₁₀.sub b₁₁
  have s₁₂ := s₁₁.add b₁₂
  have s₁₃ := s₁₂.add b₁₃
  have s₁₄ := s₁₃.add b₁₄
  rw [tiltedMean_sub hac hA s₁₄ b₁₅, tiltedMean_add hac hA s₁₃ b₁₄,
    tiltedMean_add hac hA s₁₂ b₁₃, tiltedMean_add hac hA s₁₁ b₁₂,
    tiltedMean_sub hac hA s₁₀ b₁₁, tiltedMean_add hac hA s₉ b₁₀, tiltedMean_add hac hA s₈ b₉,
    tiltedMean_add hac hA s₇ b₈, tiltedMean_sub hac hA s₆ b₇, tiltedMean_sub hac hA s₅ b₆,
    tiltedMean_sub hac hA s₄ b₅, tiltedMean_sub hac hA s₃ b₄, tiltedMean_sub hac hA s₂ b₃,
    tiltedMean_sub hac hA b₁ b₂]
theorem tiltedMeanCurve_fderiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hB : IsOpen B)
    (hμ : μ ≠ 0) (hac : ν ≪ μ) {A G : (Fin k → ℝ) → Ω → ℝ}
    {n : ℕ} (hA : IsDominated μ (n + 1) B A) (hG : IsDominated μ (n + 1) B G) :
    ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (tiltedMeanCurve ν μ A G) B ∧
      ∀ τ ∈ B, ∀ u, fderiv ℝ (tiltedMeanCurve ν μ A G) τ u =
        tiltedMeanCurve ν μ A (gibbsShift A G u) τ +
          tiltedMeanCurve ν μ A G τ * gibbsMeanCurve μ A (paramIteratedDeriv A ![u]) τ := by
  have hE : IsDominated μ (n + 1) B (fun τ ω => Real.exp (- A τ ω)) := hA.exp_neg hB
  have hP : IsDominated ν (n + 1) B (fun τ ω => G τ ω * Real.exp (- A τ ω)) :=
    (hG.of_absolutelyContinuous hac).mul hB ((hA.of_absolutelyContinuous hac).exp_neg hB)
  obtain ⟨KE, hKE⟩ := id hE
  obtain ⟨KP, hKP⟩ := id hP
  obtain ⟨cZ, fZ⟩ := contDiffOn_integral_and_iteratedFDeriv μ hB KE (n + 1) ℝ _
    hKE.aestronglyMeasurable hKE.contDiffOn hKE.norm_iteratedFDeriv_le
  obtain ⟨cN, fN⟩ := contDiffOn_integral_and_iteratedFDeriv ν hB KP (n + 1) ℝ _
    hKP.aestronglyMeasurable hKP.contDiffOn hKP.norm_iteratedFDeriv_le
  have Zpos : ∀ τ ∈ B, 0 < ∫ ω, Real.exp (- A τ ω) ∂μ := by
    intro τ hτ
    have hi : Integrable (fun ω => Real.exp (- A τ ω)) μ :=
      (hA.isBoundedMeasurable hτ).exp_neg.integrable
    have : NeZero μ := ⟨hμ⟩
    exact integral_exp_pos hi
  have hcont : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (tiltedMeanCurve ν μ A G) B :=
    cN.div cZ fun τ hτ => (Zpos τ hτ).ne'
  refine ⟨hcont, fun τ hτ u => ?_⟩
  have hn0 : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have dN : DifferentiableAt ℝ (fun τ => ∫ ω, G τ ω * Real.exp (- A τ ω) ∂ν) τ :=
    (cN.differentiableOn hn0 τ hτ).differentiableAt (hB.mem_nhds hτ)
  have dZ : DifferentiableAt ℝ (fun τ => ∫ ω, Real.exp (- A τ ω) ∂μ) τ :=
    (cZ.differentiableOn hn0 τ hτ).differentiableAt (hB.mem_nhds hτ)
  have dM : DifferentiableAt ℝ (tiltedMeanCurve ν μ A G) τ :=
    (hcont.differentiableOn hn0 τ hτ).differentiableAt (hB.mem_nhds hτ)
  obtain ⟨KA, hKA⟩ := id hA
  obtain ⟨KG, hKG⟩ := id hG
  have diffs : ∀ᵐ ω ∂μ, DifferentiableAt ℝ (fun τ => A τ ω) τ ∧
      DifferentiableAt ℝ (fun τ => G τ ω) τ := by
    filter_upwards [hKA.contDiffOn, hKG.contDiffOn] with ω a b
    exact ⟨(a.differentiableOn hn0 τ hτ).differentiableAt (hB.mem_nhds hτ),
      (b.differentiableOn hn0 τ hτ).differentiableAt (hB.mem_nhds hτ)⟩
  have eZ : fderiv ℝ (fun τ => ∫ ω, Real.exp (- A τ ω) ∂μ) τ u =
      - ∫ ω, paramIteratedDeriv A ![u] τ ω * Real.exp (- A τ ω) ∂μ := by
    have h1 := (fZ τ hτ 1 (by omega) ![u]).2
    rw [iteratedFDeriv_one_apply] at h1
    simp only [Matrix.cons_val_zero] at h1
    rw [h1, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [diffs] with ω a
    rw [iteratedFDeriv_one_apply]
    simp only [Matrix.cons_val_zero, paramIteratedDeriv_single]
    have he : HasFDerivAt (fun τ' => Real.exp (- A τ' ω))
        (Real.exp (- A τ ω) • (- fderiv ℝ (fun τ' => A τ' ω) τ)) τ := a.1.hasFDerivAt.neg.exp
    rw [he.fderiv]
    simp [mul_comm]
  have eN : fderiv ℝ (fun τ => ∫ ω, G τ ω * Real.exp (- A τ ω) ∂ν) τ u =
      ∫ ω, gibbsShift A G u τ ω * Real.exp (- A τ ω) ∂ν := by
    have h1 := (fN τ hτ 1 (by omega) ![u]).2
    rw [iteratedFDeriv_one_apply] at h1
    simp only [Matrix.cons_val_zero] at h1
    rw [h1]
    refine integral_congr_ae ?_
    filter_upwards [hac.ae_le diffs] with ω a
    rw [iteratedFDeriv_one_apply]
    simp only [Matrix.cons_val_zero, gibbsShift, paramIteratedDeriv_single]
    have he : HasFDerivAt (fun τ' => Real.exp (- A τ' ω))
        (Real.exp (- A τ ω) • (- fderiv ℝ (fun τ' => A τ' ω) τ)) τ := a.1.hasFDerivAt.neg.exp
    have hm : HasFDerivAt (fun τ' => G τ' ω * Real.exp (- A τ' ω))
        (G τ ω • (Real.exp (- A τ ω) • (- fderiv ℝ (fun τ' => A τ' ω) τ)) +
          Real.exp (- A τ ω) • fderiv ℝ (fun τ' => G τ' ω) τ) τ := a.2.hasFDerivAt.mul he
    rw [hm.fderiv]
    simp
    ring
  set Nf : (Fin k → ℝ) → ℝ := fun τ => ∫ ω, G τ ω * Real.exp (- A τ ω) ∂ν with hNf
  set Zf : (Fin k → ℝ) → ℝ := fun τ => ∫ ω, Real.exp (- A τ ω) ∂μ with hZf
  have hl : HasDerivAt (fun t : ℝ => τ + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add τ
  have at0 : τ + (0 : ℝ) • u = τ := by simp
  have lN : HasDerivAt (Nf ∘ fun t : ℝ => τ + t • u) (fderiv ℝ Nf τ u) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by rw [at0]; exact dN.hasFDerivAt) hl
  have lZ : HasDerivAt (Zf ∘ fun t : ℝ => τ + t • u) (fderiv ℝ Zf τ u) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by rw [at0]; exact dZ.hasFDerivAt) hl
  have lM : HasDerivAt (tiltedMeanCurve ν μ A G ∘ fun t : ℝ => τ + t • u)
      (fderiv ℝ (tiltedMeanCurve ν μ A G) τ u) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by rw [at0]; exact dM.hasFDerivAt) hl
  have hz0 : (Zf ∘ fun t : ℝ => τ + t • u) 0 ≠ 0 := by
    simp only [Function.comp, at0]
    exact (Zpos τ hτ).ne'
  have lQ := lN.div lZ hz0
  have uniq := lM.unique lQ
  rw [uniq]
  simp only [Function.comp, at0]
  rw [eN, eZ]
  have hZ := (Zpos τ hτ).ne'
  simp only [tiltedMeanCurve, tiltedMean, gibbsMeanCurve, gibbsMean]
  rw [hZf]
  field_simp
  ring
theorem tiltedMean_iteratedFDeriv_upToThree [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hB : IsOpen B)
    (hμ : μ ≠ 0) (hac : ν ≪ μ) {K : ℝ}
    {A H : (Fin k → ℝ) → Ω → ℝ} (hA : IsDominatedSmoothFamily μ 3 B K A)
    (hH : IsDominatedSmoothFamily μ 3 B K H) :
    ContDiffOn ℝ 3 (fun τ => tiltedMean ν μ (A τ) (H τ)) B ∧
      ∀ τ ∈ B, ∀ u v w : Fin k → ℝ,
        iteratedFDeriv ℝ 1 (fun τ => tiltedMean ν μ (A τ) (H τ)) τ ![u] =
          tiltedMean ν μ (A τ) (paramIteratedDeriv H ![u] τ) -
            tiltedCov ν μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ) ∧
        iteratedFDeriv ℝ 2 (fun τ => tiltedMean ν μ (A τ) (H τ)) τ ![v, u] =
          tiltedMean ν μ (A τ) (paramIteratedDeriv H ![v, u] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![v] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![u] τ) -
            tiltedCov ν μ (A τ) (H τ) (paramIteratedDeriv A ![v, u] τ) +
            tiltedCumulantThree ν μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ)
              (paramIteratedDeriv A ![v] τ) ∧
        iteratedFDeriv ℝ 3 (fun τ => tiltedMean ν μ (A τ) (H τ)) τ ![w, v, u] =
          tiltedMean ν μ (A τ) (paramIteratedDeriv H ![w, v, u] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![v, u] τ) (paramIteratedDeriv A ![w] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![w, u] τ) (paramIteratedDeriv A ![v] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![w, v] τ) (paramIteratedDeriv A ![u] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![w, v] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![w, u] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![w] τ) (paramIteratedDeriv A ![v, u] τ) +
            tiltedCumulantThree ν μ (A τ) (paramIteratedDeriv H ![u] τ)
              (paramIteratedDeriv A ![v] τ) (paramIteratedDeriv A ![w] τ) +
            tiltedCumulantThree ν μ (A τ) (paramIteratedDeriv H ![v] τ)
              (paramIteratedDeriv A ![u] τ) (paramIteratedDeriv A ![w] τ) +
            tiltedCumulantThree ν μ (A τ) (paramIteratedDeriv H ![w] τ)
              (paramIteratedDeriv A ![u] τ) (paramIteratedDeriv A ![v] τ) -
            tiltedCov ν μ (A τ) (H τ) (paramIteratedDeriv A ![w, v, u] τ) +
            tiltedCumulantThree ν μ (A τ) (H τ) (paramIteratedDeriv A ![v, u] τ)
              (paramIteratedDeriv A ![w] τ) +
            tiltedCumulantThree ν μ (A τ) (H τ) (paramIteratedDeriv A ![w, u] τ)
              (paramIteratedDeriv A ![v] τ) +
            tiltedCumulantThree ν μ (A τ) (H τ) (paramIteratedDeriv A ![w, v] τ)
              (paramIteratedDeriv A ![u] τ) -
            tiltedCumulantFour ν μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ)
              (paramIteratedDeriv A ![v] τ) (paramIteratedDeriv A ![w] τ) := by
  have DA : IsDominated μ 3 B A := ⟨K, hA⟩
  have DH : IsDominated μ 3 B H := ⟨K, hH⟩
  have DA2 : IsDominated μ 2 B A := DA.mono (by omega)
  have DA1 : IsDominated μ 1 B A := DA.mono (by omega)
  have Da : ∀ u, IsDominated μ 2 B (paramIteratedDeriv A ![u]) := fun u =>
    IsDominated.paramDeriv hB DA u
  have DS : ∀ u, IsDominated μ 2 B (gibbsShift A H u) := fun u => IsDominated.shift hB DA DH u
  have DSS : ∀ u v, IsDominated μ 1 B (gibbsShift A (gibbsShift A H u) v) := fun u v =>
    IsDominated.shift hB DA2 (DS u) v
  have DSa : ∀ u v, IsDominated μ 1 B (gibbsShift A (paramIteratedDeriv A ![u]) v) := fun u v =>
    IsDominated.shift hB DA2 (Da u) v
  have R3 := tiltedMeanCurve_fderiv hB hμ hac (n := 2) DA DH
  have R2 : ∀ G, IsDominated μ 2 B G →
      ContDiffOn ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) (gibbsMeanCurve μ A G) B ∧
      ∀ τ ∈ B, ∀ u, fderiv ℝ (gibbsMeanCurve μ A G) τ u = gibbsMeanCurve μ A (gibbsShift A G u) τ +
        gibbsMeanCurve μ A G τ * gibbsMeanCurve μ A (paramIteratedDeriv A ![u]) τ :=
    fun G hG => gibbsMeanCurve_fderiv hB hμ (n := 1) DA2 hG
  have R1 : ∀ G, IsDominated μ 1 B G →
      ContDiffOn ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (gibbsMeanCurve μ A G) B ∧
      ∀ τ ∈ B, ∀ u, fderiv ℝ (gibbsMeanCurve μ A G) τ u = gibbsMeanCurve μ A (gibbsShift A G u) τ +
        gibbsMeanCurve μ A G τ * gibbsMeanCurve μ A (paramIteratedDeriv A ![u]) τ :=
    fun G hG => gibbsMeanCurve_fderiv hB hμ (n := 0) DA1 hG
  have R2T : ∀ G, IsDominated μ 2 B G →
      ContDiffOn ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) (tiltedMeanCurve ν μ A G) B ∧
      ∀ τ ∈ B, ∀ u, fderiv ℝ (tiltedMeanCurve ν μ A G) τ u =
        tiltedMeanCurve ν μ A (gibbsShift A G u) τ +
        tiltedMeanCurve ν μ A G τ * gibbsMeanCurve μ A (paramIteratedDeriv A ![u]) τ :=
    fun G hG => tiltedMeanCurve_fderiv hB hμ hac (n := 1) DA2 hG
  have R1T : ∀ G, IsDominated μ 1 B G →
      ContDiffOn ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (tiltedMeanCurve ν μ A G) B ∧
      ∀ τ ∈ B, ∀ u, fderiv ℝ (tiltedMeanCurve ν μ A G) τ u =
        tiltedMeanCurve ν μ A (gibbsShift A G u) τ +
        tiltedMeanCurve ν μ A G τ * gibbsMeanCurve μ A (paramIteratedDeriv A ![u]) τ :=
    fun G hG => tiltedMeanCurve_fderiv hB hμ hac (n := 0) DA1 hG
  have c3 : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (tiltedMeanCurve ν μ A H) B := by
    simpa using R3.1
  have c3' : ContDiffOn ℝ 3 (tiltedMeanCurve ν μ A H) B := by simpa using c3
  refine ⟨c3', fun τ hτ u v w => ?_⟩
  have d3f : ∀ σ ∈ B, DifferentiableAt ℝ (tiltedMeanCurve ν μ A H) σ := fun σ hσ =>
    (c3.contDiffAt (hB.mem_nhds hσ)).differentiableAt (by norm_num)
  have d2f : ∀ G, IsDominated μ 2 B G → ∀ σ ∈ B, DifferentiableAt ℝ (gibbsMeanCurve μ A G) σ :=
    fun G hG σ hσ => ((R2 G hG).1.contDiffAt (hB.mem_nhds hσ)).differentiableAt (by norm_num)
  have d1f : ∀ G, IsDominated μ 1 B G → ∀ σ ∈ B, DifferentiableAt ℝ (gibbsMeanCurve μ A G) σ :=
    fun G hG σ hσ => ((R1 G hG).1.contDiffAt (hB.mem_nhds hσ)).differentiableAt (by norm_num)
  have d2fT : ∀ G, IsDominated μ 2 B G → ∀ σ ∈ B,
      DifferentiableAt ℝ (tiltedMeanCurve ν μ A G) σ :=
    fun G hG σ hσ => ((R2T G hG).1.contDiffAt (hB.mem_nhds hσ)).differentiableAt (by norm_num)
  have d1fT : ∀ G, IsDominated μ 1 B G → ∀ σ ∈ B,
      DifferentiableAt ℝ (tiltedMeanCurve ν μ A G) σ :=
    fun G hG σ hσ => ((R1T G hG).1.contDiffAt (hB.mem_nhds hσ)).differentiableAt (by norm_num)
  have e1 : ∀ u, ∀ σ ∈ B, iteratedFDeriv ℝ 1 (tiltedMeanCurve ν μ A H) σ ![u] =
      (tiltedMeanCurve ν μ A (gibbsShift A H u) +
        tiltedMeanCurve ν μ A H * gibbsMeanCurve μ A (paramIteratedDeriv A ![u])) σ := by
    intro u σ hσ
    rw [iteratedFDeriv_one_apply]
    exact R3.2 σ hσ u
  have e2f : ∀ v u, ∀ σ ∈ B, iteratedFDeriv ℝ 2 (tiltedMeanCurve ν μ A H) σ ![v, u] =
      (tiltedMeanCurve ν μ A (gibbsShift A (gibbsShift A H u) v) +
          tiltedMeanCurve ν μ A (gibbsShift A H u) *
            gibbsMeanCurve μ A (paramIteratedDeriv A ![v]) +
        (tiltedMeanCurve ν μ A (gibbsShift A H v) +
            tiltedMeanCurve ν μ A H * gibbsMeanCurve μ A (paramIteratedDeriv A ![v])) *
          gibbsMeanCurve μ A (paramIteratedDeriv A ![u]) +
        tiltedMeanCurve ν μ A H *
          (gibbsMeanCurve μ A (gibbsShift A (paramIteratedDeriv A ![u]) v) +
            gibbsMeanCurve μ A (paramIteratedDeriv A ![u]) *
              gibbsMeanCurve μ A (paramIteratedDeriv A ![v]))) σ := by
    intro v u σ hσ
    have ci := (iteratedFDeriv_apply_fderiv (j := 1) (g := tiltedMeanCurve ν μ A H) (τ := σ)
      ((c3.contDiffAt (hB.mem_nhds hσ)).of_le (by norm_num)) v ![u]).2
    have ev : (fun τ' => iteratedFDeriv ℝ 1 (tiltedMeanCurve ν μ A H) τ' ![u]) =ᶠ[𝓝 σ]
        (tiltedMeanCurve ν μ A (gibbsShift A H u) +
          tiltedMeanCurve ν μ A H * gibbsMeanCurve μ A (paramIteratedDeriv A ![u])) := by
      filter_upwards [hB.mem_nhds hσ] with ρ hρ
      exact e1 u ρ hρ
    have hX := (d2fT _ (DS u) σ hσ).hasFDerivAt.add
      ((d3f σ hσ).hasFDerivAt.mul (d2f _ (Da u) σ hσ).hasFDerivAt)
    have ci' : iteratedFDeriv ℝ 2 (tiltedMeanCurve ν μ A H) σ ![v, u] =
        fderiv ℝ (tiltedMeanCurve ν μ A (gibbsShift A H u) +
          tiltedMeanCurve ν μ A H * gibbsMeanCurve μ A (paramIteratedDeriv A ![u])) σ v := by
      rw [← ev.fderiv_eq]
      exact ci.symm
    rw [ci', hX.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, Pi.add_apply, Pi.mul_apply,
      (R2T _ (DS u)).2 σ hσ v, (R2 _ (Da u)).2 σ hσ v, R3.2 σ hσ v]
    ring
  have H1 := (d1fT _ (DSS u v) τ hτ).hasFDerivAt
  have H2 := (d2fT _ (DS u) τ hτ).hasFDerivAt
  have H3 := (d2f _ (Da v) τ hτ).hasFDerivAt
  have H4 := (d2fT _ (DS v) τ hτ).hasFDerivAt
  have H5 := (d3f τ hτ).hasFDerivAt
  have H6 := (d2f _ (Da u) τ hτ).hasFDerivAt
  have H7 := (d1f _ (DSa u v) τ hτ).hasFDerivAt
  have hQ := ((H1.add (H2.mul H3)).add ((H4.add (H5.mul H3)).mul H6)).add
    (H5.mul (H7.add (H6.mul H3)))
  have e3f : iteratedFDeriv ℝ 3 (tiltedMeanCurve ν μ A H) τ ![w, v, u] =
      fderiv ℝ (tiltedMeanCurve ν μ A (gibbsShift A (gibbsShift A H u) v) +
          tiltedMeanCurve ν μ A (gibbsShift A H u) *
            gibbsMeanCurve μ A (paramIteratedDeriv A ![v]) +
        (tiltedMeanCurve ν μ A (gibbsShift A H v) +
            tiltedMeanCurve ν μ A H * gibbsMeanCurve μ A (paramIteratedDeriv A ![v])) *
          gibbsMeanCurve μ A (paramIteratedDeriv A ![u]) +
        tiltedMeanCurve ν μ A H *
          (gibbsMeanCurve μ A (gibbsShift A (paramIteratedDeriv A ![u]) v) +
            gibbsMeanCurve μ A (paramIteratedDeriv A ![u]) *
              gibbsMeanCurve μ A (paramIteratedDeriv A ![v]))) τ w := by
    have ci := (iteratedFDeriv_apply_fderiv (j := 2) (g := tiltedMeanCurve ν μ A H) (τ := τ)
      (c3.contDiffAt (hB.mem_nhds hτ)) w ![v, u]).2
    have ev : (fun τ' => iteratedFDeriv ℝ 2 (tiltedMeanCurve ν μ A H) τ' ![v, u]) =ᶠ[𝓝 τ]
        (tiltedMeanCurve ν μ A (gibbsShift A (gibbsShift A H u) v) +
          tiltedMeanCurve ν μ A (gibbsShift A H u) *
            gibbsMeanCurve μ A (paramIteratedDeriv A ![v]) +
        (tiltedMeanCurve ν μ A (gibbsShift A H v) +
            tiltedMeanCurve ν μ A H * gibbsMeanCurve μ A (paramIteratedDeriv A ![v])) *
          gibbsMeanCurve μ A (paramIteratedDeriv A ![u]) +
        tiltedMeanCurve ν μ A H *
          (gibbsMeanCurve μ A (gibbsShift A (paramIteratedDeriv A ![u]) v) +
            gibbsMeanCurve μ A (paramIteratedDeriv A ![u]) *
              gibbsMeanCurve μ A (paramIteratedDeriv A ![v]))) := by
      filter_upwards [hB.mem_nhds hτ] with ρ hρ
      exact e2f v u ρ hρ
    rw [← ev.fderiv_eq]
    exact ci.symm
  have bA : IsBoundedMeasurable μ (A τ) := DA.isBoundedMeasurable hτ
  have bH : IsBoundedMeasurable μ (H τ) := DH.isBoundedMeasurable hτ
  have bh1 : ∀ u, IsBoundedMeasurable μ (paramIteratedDeriv H ![u] τ) := fun u =>
    paramIteratedDeriv_isBoundedMeasurable hB hH hτ (j := 1) (by omega) ![u]
  have ba1 : ∀ u, IsBoundedMeasurable μ (paramIteratedDeriv A ![u] τ) := fun u =>
    paramIteratedDeriv_isBoundedMeasurable hB hA hτ (j := 1) (by omega) ![u]
  have bh2 : ∀ v u, IsBoundedMeasurable μ (paramIteratedDeriv H ![v, u] τ) := fun v u =>
    paramIteratedDeriv_isBoundedMeasurable hB hH hτ (j := 2) (by omega) ![v, u]
  have ba2 : ∀ v u, IsBoundedMeasurable μ (paramIteratedDeriv A ![v, u] τ) := fun v u =>
    paramIteratedDeriv_isBoundedMeasurable hB hA hτ (j := 2) (by omega) ![v, u]
  have bh3 : IsBoundedMeasurable μ (paramIteratedDeriv H ![w, v, u] τ) :=
    paramIteratedDeriv_isBoundedMeasurable hB hH hτ (j := 3) (by omega) ![w, v, u]
  have ba3 : IsBoundedMeasurable μ (paramIteratedDeriv A ![w, v, u] τ) :=
    paramIteratedDeriv_isBoundedMeasurable hB hA hτ (j := 3) (by omega) ![w, v, u]
  have mS : ∀ u, tiltedMeanCurve ν μ A (gibbsShift A H u) τ =
      tiltedMean ν μ (A τ) (paramIteratedDeriv H ![u] τ) -
        tiltedMean ν μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![u] τ ω) := fun u =>
    tiltedMean_sub hac bA (bh1 u) (bH.mul (ba1 u))
  have c3H : ∀ᵐ ω ∂μ, ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ => H τ ω) B ∧
      ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ => A τ ω) B := by
    filter_upwards [hH.contDiffOn, hA.contDiffOn] with ω a b
    exact ⟨a, b⟩
  have at2 : ∀ {g : (Fin k → ℝ) → ℝ}, ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) g B →
      ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) g τ := fun hg =>
    (hg.contDiffAt (hB.mem_nhds hτ)).of_le (by norm_num)
  have mSS : ∀ v u, tiltedMeanCurve ν μ A (gibbsShift A (gibbsShift A H u) v) τ =
      tiltedMean ν μ (A τ) (paramIteratedDeriv H ![v, u] τ) -
        tiltedMean ν μ (A τ) (fun ω => paramIteratedDeriv H ![u] τ ω *
          paramIteratedDeriv A ![v] τ ω) -
        tiltedMean ν μ (A τ) (fun ω => paramIteratedDeriv H ![v] τ ω *
          paramIteratedDeriv A ![u] τ ω) -
        tiltedMean ν μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![v, u] τ ω) +
        tiltedMean ν μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![u] τ ω *
          paramIteratedDeriv A ![v] τ ω) := by
    intro v u
    rw [← tiltedMean_sub_sub_sub_add hac bA (bh2 v u) ((bh1 u).mul (ba1 v))
      ((bh1 v).mul (ba1 u)) (bH.mul (ba2 v u)) ((bH.mul (ba1 u)).mul (ba1 v))]
    refine tiltedMean_congr_ae hac ?_
    filter_upwards [c3H] with ω a
    exact shiftedDeriv_shiftedDeriv (at2 a.1) (at2 a.2) v u
  have mSa : ∀ v u, gibbsMeanCurve μ A (gibbsShift A (paramIteratedDeriv A ![u]) v) τ =
      gibbsMean μ (A τ) (paramIteratedDeriv A ![v, u] τ) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv A ![u] τ ω *
          paramIteratedDeriv A ![v] τ ω) := by
    intro v u
    rw [← gibbsMean_sub bA (ba2 v u) ((ba1 u).mul (ba1 v))]
    refine gibbsMean_congr_ae ?_
    filter_upwards [c3H] with ω a
    exact shiftedDeriv_firstDirDeriv (at2 a.2) v u
  have mSSS : tiltedMeanCurve ν μ A (gibbsShift A (gibbsShift A (gibbsShift A H u) v) w) τ =
      tiltedMean ν μ (A τ) (paramIteratedDeriv H ![w, v, u] τ) -
        tiltedMean ν μ (A τ) (fun ω => paramIteratedDeriv H ![v, u] τ ω *
          paramIteratedDeriv A ![w] τ ω) -
        tiltedMean ν μ (A τ) (fun ω => paramIteratedDeriv H ![w, u] τ ω *
          paramIteratedDeriv A ![v] τ ω) -
        tiltedMean ν μ (A τ) (fun ω => paramIteratedDeriv H ![w, v] τ ω *
          paramIteratedDeriv A ![u] τ ω) -
        tiltedMean ν μ (A τ) (fun ω => paramIteratedDeriv H ![u] τ ω *
          paramIteratedDeriv A ![w, v] τ ω) -
        tiltedMean ν μ (A τ) (fun ω => paramIteratedDeriv H ![v] τ ω *
          paramIteratedDeriv A ![w, u] τ ω) -
        tiltedMean ν μ (A τ) (fun ω => paramIteratedDeriv H ![w] τ ω *
          paramIteratedDeriv A ![v, u] τ ω) +
        tiltedMean ν μ (A τ) (fun ω => paramIteratedDeriv H ![u] τ ω *
          paramIteratedDeriv A ![v] τ ω * paramIteratedDeriv A ![w] τ ω) +
        tiltedMean ν μ (A τ) (fun ω => paramIteratedDeriv H ![v] τ ω *
          paramIteratedDeriv A ![u] τ ω * paramIteratedDeriv A ![w] τ ω) +
        tiltedMean ν μ (A τ) (fun ω => paramIteratedDeriv H ![w] τ ω *
          paramIteratedDeriv A ![u] τ ω * paramIteratedDeriv A ![v] τ ω) -
        tiltedMean ν μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![w, v, u] τ ω) +
        tiltedMean ν μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![v, u] τ ω *
          paramIteratedDeriv A ![w] τ ω) +
        tiltedMean ν μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![w, u] τ ω *
          paramIteratedDeriv A ![v] τ ω) +
        tiltedMean ν μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![w, v] τ ω *
          paramIteratedDeriv A ![u] τ ω) -
        tiltedMean ν μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![u] τ ω *
          paramIteratedDeriv A ![v] τ ω * paramIteratedDeriv A ![w] τ ω) := by
    rw [← tiltedMean_fifteen_terms hac bA bh3 ((bh2 v u).mul (ba1 w)) ((bh2 w u).mul (ba1 v))
      ((bh2 w v).mul (ba1 u))
      ((bh1 u).mul (ba2 w v)) ((bh1 v).mul (ba2 w u)) ((bh1 w).mul (ba2 v u))
      (((bh1 u).mul (ba1 v)).mul (ba1 w)) (((bh1 v).mul (ba1 u)).mul (ba1 w))
      (((bh1 w).mul (ba1 u)).mul (ba1 v)) (bH.mul ba3) ((bH.mul (ba2 v u)).mul (ba1 w))
      ((bH.mul (ba2 w u)).mul (ba1 v)) ((bH.mul (ba2 w v)).mul (ba1 u))
      (((bH.mul (ba1 u)).mul (ba1 v)).mul (ba1 w))]
    refine tiltedMean_congr_ae hac ?_
    filter_upwards [c3H] with ω a
    exact shiftedDeriv_shiftedDeriv_shiftedDeriv hB hτ a.1 a.2 w v u
  have mSSa : gibbsMeanCurve μ A (gibbsShift A (gibbsShift A (paramIteratedDeriv A ![u]) v) w) τ =
      gibbsMean μ (A τ) (paramIteratedDeriv A ![w, v, u] τ) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv A ![v, u] τ ω *
          paramIteratedDeriv A ![w] τ ω) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv A ![w, u] τ ω *
          paramIteratedDeriv A ![v] τ ω) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv A ![w, v] τ ω *
          paramIteratedDeriv A ![u] τ ω) +
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv A ![u] τ ω *
          paramIteratedDeriv A ![v] τ ω * paramIteratedDeriv A ![w] τ ω) := by
    rw [← gibbsMean_sub_sub_sub_add bA ba3 ((ba2 v u).mul (ba1 w)) ((ba2 w u).mul (ba1 v))
      ((ba2 w v).mul (ba1 u)) (((ba1 u).mul (ba1 v)).mul (ba1 w))]
    refine gibbsMean_congr_ae ?_
    filter_upwards [c3H] with ω a
    exact shiftedDeriv_shiftedDeriv_firstDirDeriv hB hτ a.2 w v u
  have hM : ∀ G : (Fin k → ℝ) → Ω → ℝ, gibbsMeanCurve μ A G τ = gibbsMean μ (A τ) (G τ) :=
    fun _ => rfl
  have hMH : tiltedMeanCurve ν μ A H τ = tiltedMean ν μ (A τ) (H τ) := rfl
  refine ⟨?_, ?_, ?_⟩
  · have := e1 u τ hτ
    simp only [Pi.add_apply, Pi.mul_apply] at this
    change iteratedFDeriv ℝ 1 (tiltedMeanCurve ν μ A H) τ ![u] = _
    rw [this, mS u, hMH, hM (paramIteratedDeriv A ![u])]
    simp only [tiltedCov]
    ring
  · have := e2f v u τ hτ
    simp only [Pi.add_apply, Pi.mul_apply] at this
    change iteratedFDeriv ℝ 2 (tiltedMeanCurve ν μ A H) τ ![v, u] = _
    rw [this, mSS v u, mS u, mS v, mSa v u, hMH, hM (paramIteratedDeriv A ![u]),
      hM (paramIteratedDeriv A ![v])]
    simp only [tiltedCov, tiltedCumulantThree]
    ring
  · change iteratedFDeriv ℝ 3 (tiltedMeanCurve ν μ A H) τ ![w, v, u] = _
    rw [e3f, hQ.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, Pi.add_apply, Pi.mul_apply,
      (R1T _ (DSS u v)).2 τ hτ w, (R2T _ (DS u)).2 τ hτ w, (R2 _ (Da v)).2 τ hτ w,
      (R2T _ (DS v)).2 τ hτ w, R3.2 τ hτ w, (R2 _ (Da u)).2 τ hτ w, (R1 _ (DSa u v)).2 τ hτ w]
    rw [mSSS, mSS v u, mSS w u, mSS w v, mS u, mS v, mS w, mSa v u, mSa w u, mSa w v, mSSa, hMH,
      hM (paramIteratedDeriv A ![u]), hM (paramIteratedDeriv A ![v]),
      hM (paramIteratedDeriv A ![w])]
    simp only [tiltedCov, tiltedCumulantThree, tiltedCumulantFour]
    ring
end
end GibbsCalculus
theorem tiltedMeanDifferentiation_holds : TiltedMeanDifferentiation := by
  intro Ω _ ν μ _ _ k B K A H hB hμ hac hA hH
  exact GibbsCalculus.tiltedMean_iteratedFDeriv_upToThree hB hμ hac hA hH
end YangMills.Construction.TiltedMeans
end

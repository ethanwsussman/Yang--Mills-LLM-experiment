import YangMills.Construction.Lattice.MatricesBlocksAndGaugeTransformations
import YangMills.Construction.Matrices.SecondOrderSupBallBound
import YangMills.Construction.Towers.BoundsOfTheIteratedAveragesOnASideProof
import YangMills.Construction.Towers.QuadraticFormsAndTransposesOnTheRealSpacesProof
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.StepRemainder
open YangMills.Construction.Matrices YangMills.Construction.Coordinates
section AnalyticFunctions
variable {σ : Type} [Fintype σ]
def IsLocallyAnalyticOn (O : Set (σ → ComplexMatrix2)) (g : (σ → ComplexMatrix2) → ComplexMatrix2) :
    Prop :=
  ∀ A₀ ∈ O, ∃ H : (σ → ComplexMatrix2) → ComplexMatrix2, AnalyticAt ℂ H A₀ ∧
    ∀ᶠ A in 𝓝[O] A₀, g A = H A
theorem IsLocallyAnalyticOn.congr {O : Set (σ → ComplexMatrix2)}
    {g g' : (σ → ComplexMatrix2) → ComplexMatrix2}
    (h : IsLocallyAnalyticOn O g) (hg : ∀ A ∈ O, g A = g' A) : IsLocallyAnalyticOn O g' := by
  intro A₀ hA₀
  obtain ⟨H, hH, hev⟩ := h A₀ hA₀
  refine ⟨H, hH, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with A h₁ h₂
  rw [← hg A h₂, h₁]
theorem IsLocallyAnalyticOn.comp {O : Set (σ → ComplexMatrix2)} {τ : Type} [Fintype τ]
    {D : Set (τ → ComplexMatrix2)} {Ψ : (σ → ComplexMatrix2) → τ → ComplexMatrix2}
    (hΨ : ∀ i, IsLocallyAnalyticOn O fun A => Ψ A i)
    (hmaps : MapsTo Ψ O D) {φ : (τ → ComplexMatrix2) → ComplexMatrix2}
    (hφ : ∀ x ∈ D, ∃ G : (τ → ComplexMatrix2) → Unit → ComplexMatrix2, AnalyticAt ℂ G x ∧
      ∀ᶠ y in 𝓝[D] x, (fun _ => φ y) = G y) :
    IsLocallyAnalyticOn O fun A => φ (Ψ A) := by
  intro A₀ hA₀
  choose H hH hev using fun i => hΨ i A₀ hA₀
  have hvec : AnalyticAt ℂ (fun A i => H i A) A₀ := AnalyticAt.pi hH
  have hall : ∀ᶠ A in 𝓝[O] A₀, Ψ A = fun i => H i A := by
    filter_upwards [eventually_all.2 hev] with A hA
    exact funext hA
  have hat : Ψ A₀ = fun i => H i A₀ :=
    funext fun i => (hev i).self_of_nhdsWithin hA₀
  have htend : Tendsto Ψ (𝓝[O] A₀) (𝓝[D] (Ψ A₀)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h₁ : Tendsto (fun A i => H i A) (𝓝[O] A₀) (𝓝 (Ψ A₀)) := by
        rw [hat]
        exact hvec.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact h₁.congr' (hall.mono fun A hA => hA.symm)
    · filter_upwards [self_mem_nhdsWithin] with A hA using hmaps hA
  obtain ⟨G, hG, hGev⟩ := hφ (Ψ A₀) (hmaps hA₀)
  rw [hat] at hG
  have hcomp : AnalyticAt ℂ (G ∘ fun A i => H i A) A₀ := hG.comp hvec
  refine ⟨fun A => G (fun i => H i A) (), analyticAt_pi_iff.1 hcomp (), ?_⟩
  filter_upwards [htend.eventually hGev, hall] with A h₁ h₂
  have h₃ := congrFun h₁ ()
  rw [h₂] at h₃
  rw [h₂]
  exact h₃
theorem IsLocallyAnalyticOn.matLog {O : Set (σ → ComplexMatrix2)}
    {g : (σ → ComplexMatrix2) → ComplexMatrix2}
    (hlog : AnalyticOnNhd ℂ ComplexMatrix2.logSeries ComplexMatrix2.logBall)
    (h : IsLocallyAnalyticOn O g) (hd : ∀ A ∈ O, g A ∈ ComplexMatrix2.logBall) :
    IsLocallyAnalyticOn O fun A => ComplexMatrix2.logSeries (g A) := by
  intro A₀ hA₀
  obtain ⟨H, hH, hev⟩ := h A₀ hA₀
  have h₀ : H A₀ ∈ ComplexMatrix2.logBall := by
    rw [← hev.self_of_nhdsWithin hA₀]
    exact hd A₀ hA₀
  refine ⟨fun A => ComplexMatrix2.logSeries (H A),
    AnalyticAt.comp (g := ComplexMatrix2.logSeries) (hlog _ h₀) hH, ?_⟩
  filter_upwards [hev] with A hA
  rw [hA]
theorem operatorNorm_le_supNorm (A : σ → ComplexMatrix2) (i : σ) :
    ComplexMatrix2.operatorNorm (A i) ≤ GroupLieProduct.supNorm A :=
  le_ciSup (f := fun i => ComplexMatrix2.operatorNorm (A i)) (Set.finite_range _).bddAbove i
theorem supNorm_lt_iff {ρ : ℝ} (hρ : 0 < ρ) (A : σ → ComplexMatrix2) :
    GroupLieProduct.supNorm A < ρ ↔ ∀ i, ComplexMatrix2.operatorNorm (A i) < ρ := by apply _root_.YangMills.SharedProofs.p9363 <;> assumption
theorem isOpen_supNorm_lt {ρ : ℝ} (hρ : 0 < ρ) :
    IsOpen {A : σ → ComplexMatrix2 | GroupLieProduct.supNorm A < ρ} := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.isOpen_supNorm_lt <;> assumption
theorem isSupOpen_supBall {ρ : ℝ} (hρ : 0 < ρ) :
    GroupLieProduct.IsSupOpen (GroupLieProduct.supBall σ ρ) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.isSupOpen_supBall <;> assumption
def coordsLinearMap (e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) :
    ComplexCoordinates (Fintype.card σ * 3) →ₗ[ℂ] (σ → ComplexMatrix2) where
  toFun := GroupLieProduct.tupleOfCoords e ν
  map_add' w w' := by
    funext i
    simp [GroupLieProduct.tupleOfCoords, ComplexCoordinates.tracelessTuple, add_smul,
      Finset.sum_add_distrib]
  map_smul' c w := by
    funext i
    simp [GroupLieProduct.tupleOfCoords, ComplexCoordinates.tracelessTuple, mul_smul,
      Finset.smul_sum]
def entriesLinearMap : ComplexMatrix2 →ₗ[ℂ] ComplexCoordinates 4 where
  toFun := ComplexCoordinates.matrixEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem tupleOfCoords_mem (e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) (w : ComplexCoordinates (Fintype.card σ * 3)) :
    GroupLieProduct.tupleOfCoords e ν w ∈ GroupLieProduct.tracelessPi σ := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.tupleOfCoords_mem <;> assumption
theorem IsLocallyAnalyticOn.isHolomorphicOnTraceless {ρ : ℝ} (hρ : 0 < ρ)
    (e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {f : (σ → ComplexMatrix2) → ComplexMatrix2}
    (hf : IsLocallyAnalyticOn (GroupLieProduct.supBall σ ρ) f) :
    GroupLieProduct.IsHolomorphicOnTraceless e ComplexCoordinates.matrixEquiv
      (GroupLieProduct.supBall σ ρ) f := by
  refine ⟨isSupOpen_supBall hρ, fun ν => ?_⟩
  set T := GroupLieProduct.tupleOfCoords e ν with hT
  have hTc : Continuous T := (LinearMap.toContinuousLinearMap (coordsLinearMap e ν)).continuous
  have hset : T ⁻¹' GroupLieProduct.supBall σ ρ =
      T ⁻¹' {A | GroupLieProduct.supNorm A < ρ} := by
    ext w
    exact ⟨fun h => h.2, fun h => ⟨tupleOfCoords_mem e ν w, h⟩⟩
  have hS : IsOpen (T ⁻¹' GroupLieProduct.supBall σ ρ) := by
    rw [hset]
    exact (isOpen_supNorm_lt hρ).preimage hTc
  have hAn : ∀ w ∈ T ⁻¹' GroupLieProduct.supBall σ ρ,
      AnalyticAt ℂ (ComplexCoordinates.matrixEquiv ∘ f ∘ T) w := by
    intro w hw
    obtain ⟨H, hH, hev⟩ := hf (T w) hw
    have htend : Tendsto T (𝓝 w) (𝓝[GroupLieProduct.supBall σ ρ] (T w)) :=
      tendsto_nhdsWithin_iff.2 ⟨hTc.tendsto w, hS.mem_nhds hw⟩
    have hH' : AnalyticAt ℂ (fun v => LinearMap.toContinuousLinearMap entriesLinearMap
        (H (LinearMap.toContinuousLinearMap (coordsLinearMap e ν) v))) w :=
      (ContinuousLinearMap.analyticAt _ _).comp
        (AnalyticAt.comp (f := LinearMap.toContinuousLinearMap (coordsLinearMap e ν)) hH
          (ContinuousLinearMap.analyticAt _ _))
    refine hH'.congr ?_
    filter_upwards [htend.eventually hev] with v hv
    change ComplexCoordinates.matrixEquiv (H (T v)) = ComplexCoordinates.matrixEquiv (f (T v))
    rw [hv]
  refine ⟨hS, fun w hw => (hAn w hw).continuousAt.continuousWithinAt, fun a ha j => ?_⟩
  have hline : Continuous fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j := by fun_prop
  have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ),
      a + ζ • ComplexCoordinates.stdBasisVector j ∈ T ⁻¹' GroupLieProduct.supBall σ ρ :=
    (hS.preimage hline).mem_nhds (by simpa using ha)
  filter_upwards [hnear] with ζ hζ
  have hd : DifferentiableAt ℂ (fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) ζ := by
    fun_prop
  exact DifferentiableAt.comp (g := ComplexCoordinates.matrixEquiv ∘ f ∘ T) ζ
    (hAn _ hζ).differentiableAt hd
theorem zero_mem_supBall {ρ : ℝ} (hρ : 0 < ρ) :
    (0 : σ → ComplexMatrix2) ∈ GroupLieProduct.supBall σ ρ := by
  refine ⟨fun _ => ComplexMatrix2.traceless.zero_mem, (supNorm_lt_iff hρ _).2 fun i => ?_⟩
  simpa [ComplexMatrix2.operatorNorm] using hρ
end AnalyticFunctions
section Linearity
variable {L n k : ℕ}
theorem linearSmoothing_linear {i : ℕ} (hfin : Finite (Vertex L n k i)) (c : ℂ)
    (B B' : Edge L n k i → ComplexMatrix2) :
    linearSmoothing L n k i (c • B + B') =
      c • linearSmoothing L n k i B + linearSmoothing L n k i B' := by apply _root_.YangMills.Construction.Tower.RescaledTrivialStepsProof.linearSmoothing_smul_add <;> assumption
end Linearity
section Levels
variable {L n k j : ℕ}
def antisymmetrize (a : Edge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  fun b => (1 / 2 : ℂ) • (a b - a b.opposite)
theorem antisymmetrize_of_mem {a : Edge L n k j → ComplexMatrix2}
    (ha : a ∈ complexEdgeForms L n k j) : antisymmetrize a = a := by
  funext b
  have h : a b.opposite = -a b := ha.2 b
  simp only [antisymmetrize, h, sub_neg_eq_add]
  rw [← two_smul ℂ (a b), smul_smul]
  norm_num
theorem antisymmetrize_smul (z : ℂ) (a : Edge L n k j → ComplexMatrix2) :
    antisymmetrize (z • a) = z • antisymmetrize a := by
  funext b
  simp only [antisymmetrize, Pi.smul_apply, ← smul_sub]
  rw [smul_comm]
theorem antisymmetrize_add (a a' : Edge L n k j → ComplexMatrix2) :
    antisymmetrize (a + a') = antisymmetrize a + antisymmetrize a' := by
  funext b
  simp only [antisymmetrize, Pi.add_apply, ← smul_add]
  congr 1
  abel
theorem antisymmetrize_mem {a : Edge L n k j → ComplexMatrix2}
    (ha : a ∈ GroupLieProduct.tracelessPi (Edge L n k j)) :
    antisymmetrize a ∈ complexEdgeForms L n k j := by
  refine ⟨fun b _ => ?_, fun b => ?_⟩
  · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (ha _) (ha _))
  · simp only [antisymmetrize, PeriodicLattice.Bond.opposite_opposite]
    rw [← smul_neg, neg_sub]
theorem operatorNorm_antisymmetrize_lt [Fintype (Edge L n k j)]
    {a : Edge L n k j → ComplexMatrix2} {υ : ℝ}
    (h : GroupLieProduct.supNorm a < υ) (b : Edge L n k j) :
    ComplexMatrix2.operatorNorm (antisymmetrize a b) < υ := by
  have h₁ := operatorNorm_le_supNorm a b
  have h₂ := operatorNorm_le_supNorm a b.opposite
  have h₃ := norm_sub_le (a b) (a b.opposite)
  simp only [ComplexMatrix2.operatorNorm, antisymmetrize, norm_smul] at h₁ h₂ ⊢
  norm_num
  linarith
theorem form_mem_traceless {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j)
    (b : Edge L n k j) : B b ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.RealQuadraticTransposes.complexEdgeForm_apply_mem <;> assumption
theorem expForm_apply {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j)
    (b : Edge L n k j) :
    IdentityExpChart.expForm B b = ComplexMatrix2.matExp (Complex.I • B b) := by apply _root_.YangMills.Construction.Tower.IteratedMeanBounds.expForm_apply <;> assumption
theorem real_exp_sub_one_lt {x r : ℝ} (hxr : x ≤ r) (hr : 0 < r) (hr₁ : r ≤ 1 / 2) :
    Real.exp x - 1 < 2 * r := by
  have h₁ := Real.exp_bound_div_one_sub_of_interval' hr (by linarith)
  have h₂ : Real.exp x ≤ Real.exp r := Real.exp_le_exp.2 hxr
  have h₃ : 1 / (1 - r) ≤ 1 + 2 * r := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith
theorem expForm_mem_polydisc (hE : ComplexMatrix2.ExpLogEstimates) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ₁ : ρ ≤ 1) (c : Edge L n k (j + 1)) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) (hs : ∀ b, ComplexMatrix2.operatorNorm (B b) ≤ ρ / 2) :
    IdentityExpChart.expForm B ∈ nearIdentityPolydisc ρ c := by
  refine ⟨⟨fun b _ => ?_, fun b _ => ?_⟩, fun b _ => ?_⟩
  · change (IdentityExpChart.expForm B b).det = 1
    have ht : ComplexMatrix2.fullTrace (Complex.I • B b) = 0 :=
      ComplexMatrix2.traceless.smul_mem Complex.I (form_mem_traceless hB b)
    rw [expForm_apply hB, hE.2.2.2.2.2.1, ht, Complex.exp_zero]
  · rw [expForm_apply hB, expForm_apply hB, hB.2 b, smul_neg]
    exact Matrix.exp_neg _
  · rw [expForm_apply hB]
    have h₁ := (hE.1 (Complex.I • B b)).2
    have h₂ : ComplexMatrix2.operatorNorm (Complex.I • B b) = ComplexMatrix2.operatorNorm (B b) := by
      simp [ComplexMatrix2.operatorNorm, norm_smul]
    rw [h₂] at h₁
    have h₃ := real_exp_sub_one_lt (hs b) (half_pos hρ) (by linarith)
    linarith
def exponentCLM [Fintype (Edge L n k j)] (b : Edge L n k j) :
    (Edge L n k j → ComplexMatrix2) →L[ℂ] ComplexMatrix2 :=
  (Complex.I * (1 / 2 : ℂ)) •
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Edge L n k j => ComplexMatrix2) b -
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Edge L n k j => ComplexMatrix2) b.opposite)
theorem exponentCLM_apply [Fintype (Edge L n k j)] (b : Edge L n k j)
    (a : Edge L n k j → ComplexMatrix2) : exponentCLM b a = Complex.I • antisymmetrize a b := by
  ext r s
  simp [exponentCLM, antisymmetrize, Matrix.smul_apply]
  ring
theorem expForm_antisymmetrize_analytic [Fintype (Edge L n k j)] {ρ : ℝ} (b : Edge L n k j) :
    IsLocallyAnalyticOn (GroupLieProduct.supBall (Edge L n k j) ρ)
      fun a => IdentityExpChart.expForm (antisymmetrize a) b := by
  have hval : ∀ a ∈ GroupLieProduct.supBall (Edge L n k j) ρ,
      ComplexMatrix2.matExp (exponentCLM b a) = IdentityExpChart.expForm (antisymmetrize a) b := by
    intro a ha
    rw [expForm_apply (antisymmetrize_mem ha.1), exponentCLM_apply]
  refine IsLocallyAnalyticOn.congr (g := fun a => ComplexMatrix2.matExp (exponentCLM b a)) ?_ hval
  intro A₀ _
  exact ⟨_, AnalyticAt.comp (f := exponentCLM b) (NormedSpace.exp_analytic (𝕂 := ℂ) _)
    (ContinuousLinearMap.analyticAt _ _), Eventually.of_forall fun _ => rfl⟩
theorem extendFromPositive_restrict {ℬ : Set (Edge L n k j)}
    (hℬ : ∀ b ∈ ℬ, b.opposite ∈ ℬ) {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b ∈ ℬ, V b.opposite = (V b)⁻¹) (b : Edge L n k j) (hb : b ∈ ℬ) :
    PeriodicLattice.extendFromPositive ℬ (PeriodicLattice.restrictToPositive ℬ V) b = V b := by
  unfold PeriodicLattice.extendFromPositive
  by_cases hp : b.IsPositivelyOriented
  · rw [dif_pos ⟨hb, hp⟩]
    rfl
  · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hp
    rw [dif_neg (fun h => hp h.2), dif_pos ⟨hℬ b hb, hr⟩]
    have h := hV b.opposite (hℬ b hb)
    rw [PeriodicLattice.Bond.opposite_opposite] at h
    exact h.symm
def smoothingAt (c : Edge L n k (j + 1)) (a : Edge L n k j → ComplexMatrix2) : ComplexMatrix2 :=
  PeriodicLattice.complexBlockAverageStep j (IdentityExpChart.expForm (antisymmetrize a)) c
def defectAt (c : Edge L n k (j + 1)) (a : Edge L n k j → ComplexMatrix2) : ComplexMatrix2 :=
  logMeanDefect (antisymmetrize a) c
theorem expForm_mem_of_supBall [Fintype (Edge L n k j)] (hE : ComplexMatrix2.ExpLogEstimates)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (c : Edge L n k (j + 1)) {a : Edge L n k j → ComplexMatrix2}
    (ha : a ∈ GroupLieProduct.supBall (Edge L n k j) (ρ / 2)) :
    IdentityExpChart.expForm (antisymmetrize a) ∈ nearIdentityPolydisc ρ c :=
  expForm_mem_polydisc hE hρ hρ₁ c (antisymmetrize_mem ha.1)
    fun b => (operatorNorm_antisymmetrize_lt ha.2 b).le
theorem smoothingAt_analytic [Fintype (Edge L n k j)] (hE : ComplexMatrix2.ExpLogEstimates)
    (hread : PeriodicLattice.ComplexAverageIsLocal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k) {ρ : ℝ}
    (hrad : IsAdmissiblePolydiscRadius L ρ) {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) :
    IsLocallyAnalyticOn (GroupLieProduct.supBall (Edge L n k j) (ρ / 2)) (smoothingAt c) := by
  have hserve := hrad.periodic n k j hn hj c hc
  obtain ⟨inst, hol⟩ := hserve.holomorphic_smoothing.1
  have hclosed : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
      b.opposite ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
    fun b hb => ⟨hb.2, hb.1⟩
  have hreads := hread L n k j hL.1 hL.2 hn hj c hc
  have hpoly : ∀ a ∈ GroupLieProduct.supBall (Edge L n k j) (ρ / 2),
      IdentityExpChart.expForm (antisymmetrize a) ∈ nearIdentityPolydisc ρ c :=
    fun a ha => expForm_mem_of_supBall hE hrad.pos hrad.le_one c ha
  have hagree : ∀ a ∈ GroupLieProduct.supBall (Edge L n k j) (ρ / 2),
      PeriodicLattice.complexBlockAverage (PeriodicLattice.extendFromPositive
        (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
        (PeriodicLattice.restrictToPositive
          (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
          (IdentityExpChart.expForm (antisymmetrize a)))) c = smoothingAt c a := by
    intro a ha
    change _ = PeriodicLattice.complexBlockAverage (IdentityExpChart.expForm (antisymmetrize a)) c
    simp only [PeriodicLattice.complexBlockAverage, if_pos hc]
    exact hreads.average_eq _ _ fun b hb =>
      extendFromPositive_restrict hclosed (hpoly a ha).1.2 b hb
  have hmaps : MapsTo
      (fun a => PeriodicLattice.restrictToPositive
        (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
        (IdentityExpChart.expForm (antisymmetrize a)))
      (GroupLieProduct.supBall (Edge L n k j) (ρ / 2))
      (PeriodicLattice.restrictToPositive
        (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) ''
        nearIdentityPolydisc ρ c) :=
    fun a ha => ⟨_, hpoly a ha, rfl⟩
  refine IsLocallyAnalyticOn.congr (IsLocallyAnalyticOn.comp (fun i => ?_) hmaps hol.2.2) hagree
  exact expForm_antisymmetrize_analytic i.1
theorem smoothingAt_near_one [Fintype (Edge L n k j)] (hE : ComplexMatrix2.ExpLogEstimates)
    {ρ : ℝ} (hn : 0 < n) (hj : j < k) (hrad : IsAdmissiblePolydiscRadius L ρ)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) {a : Edge L n k j → ComplexMatrix2}
    (ha : a ∈ GroupLieProduct.supBall (Edge L n k j) (ρ / 2)) :
    ComplexMatrix2.operatorNorm (smoothingAt c a - 1) < 1 / 2 :=
  (hrad.periodic n k j hn hj c hc).smoothing_near_one _
    (expForm_mem_of_supBall hE hrad.pos hrad.le_one c ha)
theorem linearSmoothing_zero (hfin : Finite (Vertex L n k j)) :
    linearSmoothing L n k j 0 = 0 := by
  have h := linearSmoothing_linear hfin (-1) (0 : Edge L n k j → ComplexMatrix2) 0
  simpa using h
theorem linearSmoothing_smul (hfin : Finite (Vertex L n k j)) (z : ℂ)
    (B : Edge L n k j → ComplexMatrix2) :
    linearSmoothing L n k j (z • B) = z • linearSmoothing L n k j B := by
  have h := linearSmoothing_linear hfin z B 0
  rw [add_zero, linearSmoothing_zero hfin, add_zero] at h
  exact h
theorem linearSmoothing_add (hfin : Finite (Vertex L n k j)) (B B' : Edge L n k j → ComplexMatrix2) :
    linearSmoothing L n k j (B + B') = linearSmoothing L n k j B + linearSmoothing L n k j B' := by apply _root_.YangMills.Construction.Tower.StepQuadraticFormProof.linearSmoothing_add <;> assumption
def smoothingCLM [Fintype (Edge L n k j)] (hfin : Finite (Vertex L n k j))
    (c : Edge L n k (j + 1)) : (Edge L n k j → ComplexMatrix2) →L[ℂ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => linearSmoothing L n k j (antisymmetrize a) c
      map_add' := fun a a' => by
        rw [antisymmetrize_add, linearSmoothing_add hfin]
        rfl
      map_smul' := fun z a => by
        rw [antisymmetrize_smul, linearSmoothing_smul hfin]
        rfl }
theorem logSmoothingAt_analytic [Fintype (Edge L n k j)] (hE : ComplexMatrix2.ExpLogEstimates)
    (hread : PeriodicLattice.ComplexAverageIsLocal)
    (hlog : AnalyticOnNhd ℂ ComplexMatrix2.logSeries ComplexMatrix2.logBall)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k) {ρ : ℝ}
    (hrad : IsAdmissiblePolydiscRadius L ρ) {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) :
    IsLocallyAnalyticOn (GroupLieProduct.supBall (Edge L n k j) (ρ / 2))
      fun a => ComplexMatrix2.logSeries (smoothingAt c a) :=
  IsLocallyAnalyticOn.matLog hlog (smoothingAt_analytic hE hread hL hn hj hrad hc) fun _ ha =>
    (smoothingAt_near_one hE hn hj hrad hc ha).trans (by norm_num)
theorem defectAt_analytic [Fintype (Edge L n k j)] (hfin : Finite (Vertex L n k j)) {ρ : ℝ}
    {c : Edge L n k (j + 1)}
    (h : IsLocallyAnalyticOn (GroupLieProduct.supBall (Edge L n k j) (ρ / 2))
      fun a => ComplexMatrix2.logSeries (smoothingAt c a)) :
    IsLocallyAnalyticOn (GroupLieProduct.supBall (Edge L n k j) (ρ / 2)) (defectAt c) := by
  intro A₀ hA₀
  obtain ⟨H, hH, hev⟩ := h A₀ hA₀
  have h₁ : AnalyticAt ℂ (fun a => Complex.I⁻¹ • H a) A₀ :=
    (analyticAt_const (v := Complex.I⁻¹)).smul hH
  refine ⟨fun a => Complex.I⁻¹ • H a - smoothingCLM hfin c a,
    h₁.sub ((smoothingCLM hfin c).analyticAt _), ?_⟩
  filter_upwards [hev] with a ha
  change Complex.I⁻¹ • ComplexMatrix2.logSeries (smoothingAt c a) -
    linearSmoothing L n k j (antisymmetrize a) c = _
  rw [ha]
  rfl
theorem hasDerivAt_defectAt [Fintype (Edge L n k j)] (hfin : Finite (Vertex L n k j)) {υ : ℝ}
    (hυ : 0 < υ) {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented)
    (hs : RescaledConditions.TrivialStep L n k j)
    (h : IsLocallyAnalyticOn (GroupLieProduct.supBall (Edge L n k j) υ)
      fun a => ComplexMatrix2.logSeries (smoothingAt c a))
    {a : Edge L n k j → ComplexMatrix2} (ha : a ∈ GroupLieProduct.tracelessPi (Edge L n k j)) :
    HasDerivAt (fun z : ℂ => ComplexCoordinates.matrixEquiv (defectAt c (z • a))) 0 0 := by
  have hB := antisymmetrize_mem ha
  obtain ⟨H, hH, hev⟩ := h 0 (zero_mem_supBall hυ)
  have hline : Continuous fun z : ℂ => z • a := by fun_prop
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), z • a ∈ GroupLieProduct.supBall (Edge L n k j) υ := by
    have h₀ : (0 : ℂ) • a ∈ {A : Edge L n k j → ComplexMatrix2 | GroupLieProduct.supNorm A < υ} := by
      rw [zero_smul]
      exact (zero_mem_supBall hυ).2
    filter_upwards [((isOpen_supNorm_lt hυ).preimage hline).mem_nhds h₀] with z hz
    exact ⟨fun i => ComplexMatrix2.traceless.smul_mem z (ha i), hz⟩
  have htend : Tendsto (fun z : ℂ => z • a) (𝓝 0)
      (𝓝[GroupLieProduct.supBall (Edge L n k j) υ] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hnear⟩
    have := hline.tendsto 0
    simpa using this
  set F : ℂ → ComplexMatrix2 := fun z => ComplexMatrix2.logSeries (smoothingAt c (z • a)) with hFdef
  have hFH : F =ᶠ[𝓝 0] fun z => H (z • a) := htend.eventually hev
  have hHd : DifferentiableAt ℂ (fun z : ℂ => H (z • a)) 0 := by
    have h₀ : DifferentiableAt ℂ H ((0 : ℂ) • a) := by
      rw [zero_smul]
      exact hH.differentiableAt
    exact DifferentiableAt.comp (g := H) (0 : ℂ) h₀ (by fun_prop)
  have hFd : DifferentiableAt ℂ F 0 := hHd.congr_of_eventuallyEq hFH
  set Qc : ComplexMatrix2 := linearSmoothing L n k j (antisymmetrize a) c with hQc
  have hderiv : Complex.I⁻¹ • deriv F 0 = Qc := by
    have h₁ := congrFun (hs.2.2.2.2.1 (antisymmetrize a) hB).1 c
    have hW : PeriodicLattice.complexBlockAverageStep j (trivialField L n k j) c = 1 :=
      congrFun hs.1 c
    unfold complexSmoothingDeriv holLeftDifferential extendOddly at h₁
    simp only [if_pos hc, logDirectionalDeriv, hW, inv_one, mul_one] at h₁
    rw [← hQc] at h₁
    have hfun : F = fun t : ℂ => ComplexMatrix2.logSeries (PeriodicLattice.complexBlockAverageStep j
        (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • antisymmetrize a)
          (trivialField L n k j)) c) := by
      funext t
      simp only [hFdef, smoothingAt, antisymmetrize_smul, IdentityExpChart.expForm]
      rfl
    rw [hfun]
    exact h₁
  have hD : HasDerivAt (fun z : ℂ => Complex.I⁻¹ • F z - z • Qc) 0 0 := by
    have h₁ := hFd.hasDerivAt.const_smul Complex.I⁻¹
    have h₂ : HasDerivAt (fun z : ℂ => z • Qc) Qc 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const Qc
    have h₃ := h₁.sub h₂
    rw [hderiv, sub_self] at h₃
    exact h₃
  have hr : (fun z : ℂ => defectAt c (z • a)) = fun z : ℂ => Complex.I⁻¹ • F z - z • Qc := by
    funext z
    change Complex.I⁻¹ • ComplexMatrix2.logSeries (smoothingAt c (z • a)) -
      linearSmoothing L n k j (antisymmetrize (z • a)) c = _
    rw [antisymmetrize_smul, linearSmoothing_smul hfin]
    rfl
  have hcl := (LinearMap.toContinuousLinearMap entriesLinearMap).hasFDerivAt.comp_hasDerivAt
    (0 : ℂ) (hr ▸ hD)
  rw [map_zero] at hcl
  exact hcl
theorem linearSmoothing_apply_le (hLin : TwoLevelMaps.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ b, ComplexMatrix2.operatorNorm (B b) ≤ M) (c : Edge L n k (j + 1)) :
    ComplexMatrix2.operatorNorm (linearSmoothing L n k j B c) ≤ 5 * L * M := by
  have hk : 1 ≤ k := by omega
  have h := (((hLin L hL k hk).1 n hn).2.1) 1 (j + 1) (by omega) (by omega) (by omega)
  have e : ∀ h' : j ≤ j + 1,
      TwoLevelMaps.linearSmoothingBetween L n k h' B = linearSmoothing L n k j B := by
    intro h'
    simp only [TwoLevelMaps.linearSmoothingBetween]
    rw [levelwiseComposition_succ _ le_rfl, levelwiseComposition_self]
    rfl
  have h₂ : maxOperatorNorm (linearSmoothing L n k j B) ≤ 5 * (L : ℝ≥0∞) ^ 1 * maxOperatorNorm B := by
    rw [← e (Nat.sub_le (j + 1) 1)]
    exact h.linearSmoothing_norm_le B hB
  have h₃ : maxOperatorNorm B ≤ ENNReal.ofReal M :=
    iSup_le fun b => ENNReal.ofReal_le_ofReal (hb b)
  have h₄ : ENNReal.ofReal (ComplexMatrix2.operatorNorm (linearSmoothing L n k j B c)) ≤
      maxOperatorNorm (linearSmoothing L n k j B) :=
    le_iSup (fun c => ENNReal.ofReal (ComplexMatrix2.operatorNorm (linearSmoothing L n k j B c))) c
  have h₅ : 5 * (L : ℝ≥0∞) ^ 1 * ENNReal.ofReal M = ENNReal.ofReal (5 * L * M) := by
    rw [pow_one, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp
  have h₆ : ENNReal.ofReal (ComplexMatrix2.operatorNorm (linearSmoothing L n k j B c)) ≤
      ENNReal.ofReal (5 * L * M) := by
    rw [← h₅]
    exact h₄.trans (h₂.trans (by gcongr))
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h₆
theorem defectAt_le [Fintype (Edge L n k j)] (hE : ComplexMatrix2.ExpLogEstimates)
    (hLin : TwoLevelMaps.Statement) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) {ρ : ℝ} (hrad : IsAdmissiblePolydiscRadius L ρ)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) {a : Edge L n k j → ComplexMatrix2}
    (ha : a ∈ GroupLieProduct.supBall (Edge L n k j) (ρ / 2)) :
    ComplexMatrix2.operatorNorm (defectAt c a) ≤ 1 + 5 * L * (ρ / 2) := by
  have hρ := hrad.pos
  have hsm := smoothingAt_near_one hE hn hj hrad hc ha
  have hl : ComplexMatrix2.operatorNorm (ComplexMatrix2.logSeries (smoothingAt c a)) ≤ 1 := by
    set E : ComplexMatrix2 := smoothingAt c a - 1 with hEdef
    have hX : smoothingAt c a = 1 + E := by
      rw [hEdef]
      abel
    obtain ⟨h₁, h₂, -⟩ := hE.2.2.2.1 E (hsm.trans (by norm_num))
    rw [hX]
    refine h₁.trans (h₂.trans ?_)
    rw [div_le_one (by linarith)]
    linarith
  have hq := linearSmoothing_apply_le hLin hL hn hj (antisymmetrize_mem ha.1) (M := ρ / 2)
    (by positivity) (fun b => (operatorNorm_antisymmetrize_lt ha.2 b).le) c
  have hI : ComplexMatrix2.operatorNorm (Complex.I⁻¹ • ComplexMatrix2.logSeries (smoothingAt c a)) =
      ComplexMatrix2.operatorNorm (ComplexMatrix2.logSeries (smoothingAt c a)) := by
    simp [ComplexMatrix2.operatorNorm, norm_smul]
  have hsub := norm_sub_le (Complex.I⁻¹ • ComplexMatrix2.logSeries (smoothingAt c a))
    (linearSmoothing L n k j (antisymmetrize a) c)
  change ComplexMatrix2.operatorNorm (Complex.I⁻¹ • ComplexMatrix2.logSeries (smoothingAt c a) -
    linearSmoothing L n k j (antisymmetrize a) c) ≤ _
  simp only [ComplexMatrix2.operatorNorm] at hI hl hq ⊢
  linarith
end Levels
theorem quadraticBound_holds (h₁ : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (h₂ : PeriodicLattice.ComplexAverageIsLocal)
    (h₃ : ComplexMatrix2.ExpLogEstimates)
    (h₄ : PeriodicLattice.ElementaryStepFacts)
    (h₅ : GroupLieProduct.SecondOrderBoundOnSupBall)
    (h₆ : TwoLevelMaps.Statement)
    (h₇ : RescaledTrivialSteps) : QuadraticBound := by
  intro L hL n k j hn hj c hc A hA hsup
  have hrad := (h₁.1 L hL).2.2
  have hρ := hrad.pos
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL.2
  have hfin : Finite (Vertex L n k j) := SeparatedSequences.BaseParameters.site_finite hLpos n _
  have : Finite (Edge L n k j) :=
    Finite.of_injective (fun b : Edge L n k j => (b.source, b.target)) fun b b' hb =>
      PeriodicLattice.Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  let _ : Fintype (Edge L n k j) := Fintype.ofFinite _
  have : Nonempty (Edge L n k j) :=
    ⟨PeriodicLattice.Bond.forwardFrom
      (c.source.toSublattice (PeriodicLattice.levelDepth k j)) 0⟩
  have hseries := (h₄ L n k j hL hn hj).2.2.1
  have hs := (h₇ L hL k (by omega) n hn).2 j hj
  set υ := stepRemainderRadius L with hυdef
  have hυe : υ = polydiscRadius L / 2 := rfl
  have hυ : 0 < υ := by
    rw [hυe]
    exact half_pos hρ
  have hfinite : maxOperatorNorm A ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsup
  have hpoint : ∀ b, ComplexMatrix2.operatorNorm (A b) ≤ (maxOperatorNorm A).toReal := fun b =>
    (ENNReal.ofReal_le_iff_le_toReal hfinite).1
      (le_iSup (fun b => ENNReal.ofReal (ComplexMatrix2.operatorNorm (A b))) b)
  have hhalf : ∀ b, ComplexMatrix2.operatorNorm (A b) ≤ υ / 2 := fun b =>
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1
      ((le_iSup (fun b => ENNReal.ofReal (ComplexMatrix2.operatorNorm (A b))) b).trans hsup)
  refine ⟨expForm_mem_polydisc h₃ hρ hrad.le_one c hA fun b => ?_, ?_⟩
  · have := hhalf b
    rw [hυe] at this
    linarith
  have hlogAn := logSmoothingAt_analytic h₃ h₂ hseries.1 hL hn hj hrad hc
  have hball : A ∈ GroupLieProduct.supBall (Edge L n k j) υ :=
    ⟨fun b => form_mem_traceless hA b, (supNorm_lt_iff hυ A).2 fun b => by
      have := hhalf b
      linarith⟩
  have hM : 0 ≤ 1 + 5 * (L : ℝ) * υ := by positivity
  have hzero : defectAt c (0 : Edge L n k j → ComplexMatrix2) = 0 := by
    have hf : antisymmetrize (0 : Edge L n k j → ComplexMatrix2) = 0 := by
      have := antisymmetrize_smul (0 : ℂ) (0 : Edge L n k j → ComplexMatrix2)
      simpa using this
    have he : IdentityExpChart.expForm (0 : Edge L n k j → ComplexMatrix2) = trivialField L n k j := by
      funext b
      rw [expForm_apply (complexEdgeForms L n k j).zero_mem]
      simp [ComplexMatrix2.matExp]
    have hW : PeriodicLattice.complexBlockAverageStep j (trivialField L n k j) c = 1 :=
      congrFun hs.1 c
    simp only [defectAt, logMeanDefect, hf, he, hW, hseries.2.1, linearSmoothing_zero hfin]
    simp
  have hmain := h₅ (Edge L n k j) υ (1 + 5 * (L : ℝ) * υ) hυ hM OneLoop.pauliBasis
    (defectAt c)
    (IsLocallyAnalyticOn.isHolomorphicOnTraceless hυ _ (defectAt_analytic hfin hlogAn))
    (fun a ha => defectAt_le h₃ h₆ hL hn hj hrad hc ha) hzero
    (fun a ha => hasDerivAt_defectAt hfin hυ hc hs hlogAn ha) A hball
  have hrem : defectAt c A = logMeanDefect A c := by
    rw [defectAt, antisymmetrize_of_mem hA]
  rw [hrem] at hmain
  have htn : GroupLieProduct.supNorm A ≤ (maxOperatorNorm A).toReal := ciSup_le hpoint
  have htn₀ : 0 ≤ GroupLieProduct.supNorm A :=
    (norm_nonneg _).trans (operatorNorm_le_supNorm A (Classical.arbitrary _))
  have hconst : stepRemainderConstant L = (1 + 5 * (L : ℝ) * υ) * (υ ^ 2)⁻¹ := by
    rw [stepRemainderConstant, inv_pow]
  rw [hconst]
  refine hmain.trans ?_
  gcongr
end YangMills.Construction.Tower.StepRemainder
end

import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreHolomorphicAtARadiusProof
import YangMills.Construction.Towers.IteratedAveragesAreHolomorphicOnASide
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.IteratedMeansHolomorphic
section Generic
variable {σ : Type} [Fintype σ]
def IsLocallyAnalyticOn (O : Set (σ → Matrices.ComplexMatrix2))
    (g : (σ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) : Prop :=
  ∀ A₀ ∈ O, ∃ H : (σ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2,
    AnalyticAt ℂ H A₀ ∧ ∀ᶠ A in 𝓝[O] A₀, g A = H A
theorem IsLocallyAnalyticOn.congr {O : Set (σ → Matrices.ComplexMatrix2)}
    {g g' : (σ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (h : IsLocallyAnalyticOn O g) (hgg : ∀ A ∈ O, g A = g' A) : IsLocallyAnalyticOn O g' := by
  intro A₀ hA₀
  obtain ⟨H, hH, hev⟩ := h A₀ hA₀
  refine ⟨H, hH, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with A h₁ h₂
  rw [← hgg A h₂, h₁]
def adjugateLinearMap : Matrices.ComplexMatrix2 →ₗ[ℂ] Matrices.ComplexMatrix2 where
  toFun := Matrix.adjugate
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> ring
  map_smul' c X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]
theorem IsLocallyAnalyticOn.inv {O : Set (σ → Matrices.ComplexMatrix2)}
    {g : (σ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (h : IsLocallyAnalyticOn O g) (hdet : ∀ A ∈ O, (g A).det = 1) :
    IsLocallyAnalyticOn O fun A => (g A)⁻¹ := by
  intro A₀ hA₀
  obtain ⟨H, hH, hev⟩ := h A₀ hA₀
  refine ⟨fun A => LinearMap.toContinuousLinearMap adjugateLinearMap (H A),
    (ContinuousLinearMap.analyticAt _ _).comp hH, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with A h₁ h₂
  have hd := hdet A h₂
  change (g A)⁻¹ = Matrix.adjugate (H A)
  rw [← h₁, Matrix.inv_def, hd]
  simp
theorem IsLocallyAnalyticOn.comp {O : Set (σ → Matrices.ComplexMatrix2)} {τ : Type} [Fintype τ]
    {D : Set (τ → Matrices.ComplexMatrix2)}
    {Ψ : (σ → Matrices.ComplexMatrix2) → τ → Matrices.ComplexMatrix2}
    (hΨ : ∀ i, IsLocallyAnalyticOn O fun A => Ψ A i)
    (hmaps : MapsTo Ψ O D) {φ : (τ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (hφ : ∀ x ∈ D, ∃ G : (τ → Matrices.ComplexMatrix2) → Unit → Matrices.ComplexMatrix2,
      AnalyticAt ℂ G x ∧ ∀ᶠ y in 𝓝[D] x, (fun _ => φ y) = G y) :
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
theorem operatorNorm_le_supNorm (A : σ → Matrices.ComplexMatrix2) (i : σ) :
    Matrices.ComplexMatrix2.operatorNorm (A i) ≤ Matrices.GroupLieProduct.supNorm A :=
  le_ciSup (f := fun i => Matrices.ComplexMatrix2.operatorNorm (A i)) (Set.finite_range _).bddAbove i
theorem isOpen_supNorm_lt {ρ : ℝ} (hρ : 0 < ρ) :
    IsOpen {A : σ → Matrices.ComplexMatrix2 | Matrices.GroupLieProduct.supNorm A < ρ} := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.isOpen_supNorm_lt <;> assumption
theorem isSupOpen_supBall {ρ : ℝ} (hρ : 0 < ρ) :
    Matrices.GroupLieProduct.IsSupOpen (Matrices.GroupLieProduct.supBall σ ρ) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.isSupOpen_supBall <;> assumption
def coordsLinearMap (e : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) :
    Coordinates.ComplexCoordinates (Fintype.card σ * 3) →ₗ[ℂ] (σ → Matrices.ComplexMatrix2) where
  toFun := Matrices.GroupLieProduct.tupleOfCoords e ν
  map_add' w w' := by
    funext i
    simp [Matrices.GroupLieProduct.tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple,
      add_smul, Finset.sum_add_distrib]
  map_smul' c w := by
    funext i
    simp [Matrices.GroupLieProduct.tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple,
      mul_smul, Finset.smul_sum]
def entriesLinearMap : Matrices.ComplexMatrix2 →ₗ[ℂ] Coordinates.ComplexCoordinates 4 where
  toFun := Coordinates.ComplexCoordinates.matrixEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem tupleOfCoords_mem_tracelessPi (e : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) (w : Coordinates.ComplexCoordinates (Fintype.card σ * 3)) :
    Matrices.GroupLieProduct.tupleOfCoords e ν w ∈ Matrices.GroupLieProduct.tracelessPi σ := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.tupleOfCoords_mem <;> assumption
theorem IsLocallyAnalyticOn.isHolomorphicOnTraceless {ρ : ℝ} (hρ : 0 < ρ)
    (e : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    {f : (σ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (hf : IsLocallyAnalyticOn (Matrices.GroupLieProduct.supBall σ ρ) f) :
    Matrices.GroupLieProduct.IsHolomorphicOnTraceless e Coordinates.ComplexCoordinates.matrixEquiv
      (Matrices.GroupLieProduct.supBall σ ρ) f := by
  refine ⟨isSupOpen_supBall hρ, fun ν => ?_⟩
  set T := Matrices.GroupLieProduct.tupleOfCoords e ν with hT
  have hTc : Continuous T := (LinearMap.toContinuousLinearMap (coordsLinearMap e ν)).continuous
  have hset : T ⁻¹' Matrices.GroupLieProduct.supBall σ ρ =
      T ⁻¹' {A | Matrices.GroupLieProduct.supNorm A < ρ} := by
    ext w
    exact ⟨fun h => h.2, fun h => ⟨tupleOfCoords_mem_tracelessPi e ν w, h⟩⟩
  have hS : IsOpen (T ⁻¹' Matrices.GroupLieProduct.supBall σ ρ) := by
    rw [hset]
    exact (isOpen_supNorm_lt hρ).preimage hTc
  have hAn : ∀ w ∈ T ⁻¹' Matrices.GroupLieProduct.supBall σ ρ,
      AnalyticAt ℂ (Coordinates.ComplexCoordinates.matrixEquiv ∘ f ∘ T) w := by
    intro w hw
    obtain ⟨H, hH, hev⟩ := hf (T w) hw
    have htend : Tendsto T (𝓝 w) (𝓝[Matrices.GroupLieProduct.supBall σ ρ] (T w)) :=
      tendsto_nhdsWithin_iff.2 ⟨hTc.tendsto w, hS.mem_nhds hw⟩
    have hH' : AnalyticAt ℂ (fun v => LinearMap.toContinuousLinearMap entriesLinearMap
        (H (LinearMap.toContinuousLinearMap (coordsLinearMap e ν) v))) w :=
      (ContinuousLinearMap.analyticAt _ _).comp
        (AnalyticAt.comp (f := LinearMap.toContinuousLinearMap (coordsLinearMap e ν)) hH
          (ContinuousLinearMap.analyticAt _ _))
    refine hH'.congr ?_
    filter_upwards [htend.eventually hev] with v hv
    change Coordinates.ComplexCoordinates.matrixEquiv (H (T v)) =
      Coordinates.ComplexCoordinates.matrixEquiv (f (T v))
    rw [hv]
  refine ⟨hS, fun w hw => (hAn w hw).continuousAt.continuousWithinAt, fun a ha j => ?_⟩
  have hline : Continuous fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j := by
    fun_prop
  have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ),
      a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j ∈
        T ⁻¹' Matrices.GroupLieProduct.supBall σ ρ :=
    (hS.preimage hline).mem_nhds (by simpa using ha)
  filter_upwards [hnear] with ζ hζ
  have hd : DifferentiableAt ℂ
      (fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ζ := by
    fun_prop
  exact DifferentiableAt.comp (g := Coordinates.ComplexCoordinates.matrixEquiv ∘ f ∘ T) ζ
    (hAn _ hζ).differentiableAt hd
end Generic
section Tower
variable {L n k : ℕ} {F : Finset (Edge L n k 0)}
def antisymmetrize (hF : ∀ b, b ∈ F) (A : F → Matrices.ComplexMatrix2) :
    Edge L n k 0 → Matrices.ComplexMatrix2 :=
  fun b => (1 / 2 : ℂ) • (A ⟨b, hF b⟩ - A ⟨b.opposite, hF _⟩)
def iterAt (hF : ∀ b, b ∈ F) (j : ℕ) (A : F → Matrices.ComplexMatrix2) :
    Edge L n k j → Matrices.ComplexMatrix2 :=
  PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField (antisymmetrize hF A))
theorem antisymmetrize_of_form (hF : ∀ b, b ∈ F) {a : Edge L n k 0 → Matrices.ComplexMatrix2}
    (ha : a ∈ complexEdgeForms L n k 0) : antisymmetrize hF (fun b => a b) = a := by
  funext b
  have h : a b.opposite = -a b := ha.2 b
  simp only [antisymmetrize, h, sub_neg_eq_add]
  rw [← two_smul ℂ (a b), smul_smul]
  norm_num
theorem antisymmetrize_mem (hF : ∀ b, b ∈ F) {ρ : ℝ} {A : F → Matrices.ComplexMatrix2}
    (hA : A ∈ Matrices.GroupLieProduct.supBall F ρ) :
    antisymmetrize hF A ∈ complexEdgeForms L n k 0 := by
  refine ⟨fun b _ => ?_, fun b => ?_⟩
  · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hA.1 _) (hA.1 _))
  · simp only [antisymmetrize, PeriodicLattice.Bond.opposite_opposite]
    rw [← smul_neg, neg_sub]
theorem maxOperatorNorm_antisymmetrize_lt (hF : ∀ b, b ∈ F) {ρ : ℝ} (hρ : 0 < ρ)
    {A : F → Matrices.ComplexMatrix2} (hA : A ∈ Matrices.GroupLieProduct.supBall F ρ) :
    maxOperatorNorm (antisymmetrize hF A) < ENNReal.ofReal ρ := by
  have hle : maxOperatorNorm (antisymmetrize hF A) ≤
      ENNReal.ofReal (Matrices.GroupLieProduct.supNorm A) := by
    refine iSup_le fun b => ENNReal.ofReal_le_ofReal ?_
    have h₁ := operatorNorm_le_supNorm A ⟨b, hF b⟩
    have h₂ := operatorNorm_le_supNorm A ⟨b.opposite, hF _⟩
    have h₃ := norm_sub_le (A ⟨b, hF b⟩) (A ⟨b.opposite, hF _⟩)
    simp only [Matrices.ComplexMatrix2.operatorNorm, antisymmetrize, norm_smul] at h₁ h₂ ⊢
    norm_num
    linarith
  exact hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hρ).2 hA.2)
def exponentCLM (hF : ∀ b, b ∈ F) (b : Edge L n k 0) :
    (F → Matrices.ComplexMatrix2) →L[ℂ] Matrices.ComplexMatrix2 :=
  (Complex.I * (finestMesh L k : ℂ) * (1 / 2 : ℂ)) •
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : F => Matrices.ComplexMatrix2) ⟨b, hF b⟩ -
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : F => Matrices.ComplexMatrix2)
        ⟨b.opposite, hF _⟩)
theorem exponentCLM_apply (hF : ∀ b, b ∈ F) (b : Edge L n k 0) (A : F → Matrices.ComplexMatrix2) :
    exponentCLM hF b A = Complex.I • scaledRemainderForm (antisymmetrize hF A) b := by
  ext r s
  simp [exponentCLM, scaledRemainderForm, antisymmetrize, Matrix.smul_apply]
  ring
theorem locallyAnalytic_iterAt_zero (hF : ∀ b, b ∈ F) {ρ : ℝ} (b : Edge L n k 0) :
    IsLocallyAnalyticOn (Matrices.GroupLieProduct.supBall F ρ) fun A => iterAt hF 0 A b := by
  have hval : ∀ A ∈ Matrices.GroupLieProduct.supBall F ρ,
      Matrices.ComplexMatrix2.matExp (exponentCLM hF b A) = iterAt hF 0 A b := by
    intro A hA
    change _ = IdentityExpChart.expForm (scaledRemainderForm (antisymmetrize hF A)) b
    have hrev : scaledRemainderForm (antisymmetrize hF A) b.opposite =
        -scaledRemainderForm (antisymmetrize hF A) b := by
      have h : antisymmetrize hF A b.opposite = -antisymmetrize hF A b :=
        (antisymmetrize_mem hF hA).2 b
      simp only [scaledRemainderForm, Pi.smul_apply, h, smul_neg]
    unfold IdentityExpChart.expForm PeriodicLattice.expTwist
    rw [exponentCLM_apply]
    split_ifs with hb
    · simp
    · rw [Pi.one_apply, mul_one, hrev, smul_neg]
      have h := Matrix.exp_neg (-(Complex.I • scaledRemainderForm (antisymmetrize hF A) b))
      rw [neg_neg] at h
      exact h
  refine IsLocallyAnalyticOn.congr
    (g := fun A => Matrices.ComplexMatrix2.matExp (exponentCLM hF b A)) ?_ hval
  intro A₀ _
  exact ⟨_, AnalyticAt.comp (f := exponentCLM hF b) (NormedSpace.exp_analytic (𝕂 := ℂ) _)
    (ContinuousLinearMap.analyticAt _ _), Eventually.of_forall fun _ => rfl⟩
theorem extendFromPositive_restrictToPositive {j : ℕ} {S : Set (Edge L n k j)}
    (hS : ∀ b ∈ S, b.opposite ∈ S) {V : Edge L n k j → Matrices.ComplexMatrix2}
    (hV : ∀ b : Edge L n k j, V b.opposite = (V b)⁻¹) (b : Edge L n k j) (hb : b ∈ S) :
    PeriodicLattice.extendFromPositive S (PeriodicLattice.restrictToPositive S V) b = V b := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.extendFromPositive_restrict_eq <;> assumption
theorem locallyAnalytic_iterAt_succ_positive (hF : ∀ b, b ∈ F) {ρ : ℝ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hrad : IsAdmissiblePolydiscRadius L (polydiscRadius L))
    (hread : PeriodicLattice.ComplexAverageIsLocal)
    (hprem : ∀ A ∈ Matrices.GroupLieProduct.supBall F ρ, ∀ j < k,
      iterAt hF j A ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
        ∀ b : Edge L n k j,
          Matrices.ComplexMatrix2.operatorNorm (iterAt hF j A b - 1) < polydiscRadius L / 2)
    {j : ℕ} (hj : j < k)
    (ih : ∀ b : Edge L n k j,
      IsLocallyAnalyticOn (Matrices.GroupLieProduct.supBall F ρ) fun A => iterAt hF j A b)
    (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    IsLocallyAnalyticOn (Matrices.GroupLieProduct.supBall F ρ) (fun A => iterAt hF (j + 1) A c) ∧
      ∀ A ∈ Matrices.GroupLieProduct.supBall F ρ, (iterAt hF (j + 1) A c).det = 1 := by
  have hserve := hrad.periodic n k j hn hj c hc
  obtain ⟨inst, hol⟩ := hserve.holomorphic_smoothing.1
  have hclosed : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
      b.opposite ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
    fun b hb => ⟨hb.2, hb.1⟩
  have hreads := hread L n k j hL.1 hL.2 hn hj c hc
  have hpoly : ∀ A ∈ Matrices.GroupLieProduct.supBall F ρ,
      iterAt hF j A ∈ nearIdentityPolydisc (polydiscRadius L) c := by
    intro A hA
    obtain ⟨h₁, h₂⟩ := hprem A hA j hj
    have h₁' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ (iterAt hF j A) :=
      h₁
    refine ⟨⟨fun b _ => h₁'.1 b (mem_univ b), fun b _ => h₁'.2 b (mem_univ b)⟩, fun b _ => ?_⟩
    have := h₂ b
    have hpos := hrad.pos
    linarith
  have hagree : ∀ A ∈ Matrices.GroupLieProduct.supBall F ρ,
      PeriodicLattice.complexBlockAverage (PeriodicLattice.extendFromPositive
        (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
        (PeriodicLattice.restrictToPositive
          (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (iterAt hF j A))) c =
        iterAt hF (j + 1) A c := by
    intro A hA
    have h₁' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ (iterAt hF j A) :=
      (hprem A hA j hj).1
    change _ = PeriodicLattice.complexBlockAverage (iterAt hF j A) c
    simp only [PeriodicLattice.complexBlockAverage, if_pos hc]
    exact hreads.average_eq _ _ fun b hb =>
      extendFromPositive_restrictToPositive hclosed (fun b => h₁'.2 b (mem_univ b)) b hb
  have hmaps : MapsTo
      (fun A => PeriodicLattice.restrictToPositive
        (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (iterAt hF j A))
      (Matrices.GroupLieProduct.supBall F ρ)
      (PeriodicLattice.restrictToPositive
          (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) ''
        nearIdentityPolydisc (polydiscRadius L) c) :=
    fun A hA => ⟨_, hpoly A hA, rfl⟩
  refine ⟨?_, fun A hA => ?_⟩
  · refine IsLocallyAnalyticOn.congr (IsLocallyAnalyticOn.comp (fun i => ?_) hmaps hol.2.2) hagree
    exact ih i.1
  · have h := hol.2.1 (hmaps hA) ()
    rw [← hagree A hA]
    exact h
end Tower
theorem iteratedMeansHolomorphicOnSide_holds (h₁ : SmoothingNearIdentity)
    (h₂ : PeriodicLattice.ComplexAverageIsLocal) : IteratedMeansHolomorphicOnSide := by
  intro L hL ρ hρ n k hn _ hprem j hj c
  have hrad := (h₁.1 L hL).2.2
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL.2
  have : Finite (PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0)) :=
    SeparatedSequences.BaseParameters.site_finite hLpos n _
  have : Finite (Edge L n k 0) :=
    Finite.of_injective (fun b : Edge L n k 0 => (b.source, b.target)) fun b b' hb =>
      PeriodicLattice.Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  letI := Fintype.ofFinite (Edge L n k 0)
  have hF : ∀ b : Edge L n k 0, b ∈ (Finset.univ : Finset (Edge L n k 0)) := Finset.mem_univ
  have hP : ∀ A ∈ Matrices.GroupLieProduct.supBall (Finset.univ : Finset (Edge L n k 0)) ρ,
      ∀ j < k,
      iterAt hF j A ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
        ∀ b : Edge L n k j,
          Matrices.ComplexMatrix2.operatorNorm (iterAt hF j A b - 1) < polydiscRadius L / 2 :=
    fun A hA j hj =>
      hprem _ (antisymmetrize_mem hF hA) (maxOperatorNorm_antisymmetrize_lt hF hρ hA) j hj
  have hall : ∀ j ≤ k, ∀ c : Edge L n k j,
      IsLocallyAnalyticOn
        (Matrices.GroupLieProduct.supBall (Finset.univ : Finset (Edge L n k 0)) ρ)
        fun A => iterAt hF j A c := by
    intro j
    induction j with
    | zero => exact fun _ c => locallyAnalytic_iterAt_zero hF c
    | succ j ih =>
      intro hj c
      have hjk : j < k := hj
      by_cases hc : c.IsPositivelyOriented
      · exact (locallyAnalytic_iterAt_succ_positive hF hL hn hrad h₂ hP hjk (ih hjk.le) c hc).1
      · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive c).resolve_left hc
        obtain ⟨ha, hd⟩ :=
          locallyAnalytic_iterAt_succ_positive hF hL hn hrad h₂ hP hjk (ih hjk.le) c.opposite hr
        refine (ha.inv hd).congr fun A _ => ?_
        change (PeriodicLattice.complexBlockAverage (iterAt hF j A) c.opposite)⁻¹ =
          PeriodicLattice.complexBlockAverage (iterAt hF j A) c
        simp only [PeriodicLattice.complexBlockAverage, if_pos hr, if_neg hc]
  refine ⟨Finset.univ, fun A => iterAt hF j A c,
    fun e => (hall j hj c).isHolomorphicOnTraceless hρ e, fun a ha _ => ?_⟩
  change PeriodicLattice.complexBlockFieldAtLevel j
    (remainderGaugeField (antisymmetrize hF fun b => a b)) c = _
  rw [antisymmetrize_of_form hF ha]
end YangMills.Construction.Tower.IteratedMeansHolomorphic
end

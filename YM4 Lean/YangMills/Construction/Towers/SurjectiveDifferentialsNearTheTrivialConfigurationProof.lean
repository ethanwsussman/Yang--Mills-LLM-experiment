import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.Matrices.ImplicitFunctionOnTheRealFormProof
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantOnTheSidesProof
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.SurjectiveDifferentialsNearTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.NearIdentitySurjectivity
open YangMills.Construction.Matrices YangMills.Construction.Coordinates
theorem eventually_surjOn_of_continuousAt {X E F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (A : Submodule ℝ E) (B : Submodule ℝ F)
    (Q : X → E →L[ℝ] F) (p : X) (hQ : ContinuousAt Q p)
    (h : ∀ f ∈ B, ∃ x ∈ A, Q p x = f) :
    ∀ᶠ w in 𝓝 p, (∀ x ∈ A, Q w x ∈ B) → ∀ f ∈ B, ∃ x ∈ A, Q w x = f := by
  classical
  let β := Module.finBasis ℝ B
  choose s hsA hs using fun i => h (β i) (β i).2
  let S : B →ₗ[ℝ] A := β.constr ℝ fun i => (⟨s i, hsA i⟩ : A)
  have hS : ∀ y : B, Q p (S y : E) = y := by
    intro y
    have e : ((Q p : E →ₗ[ℝ] F) ∘ₗ A.subtype ∘ₗ S) = B.subtype :=
      β.ext fun i => by simp [S, hs]
    exact LinearMap.congr_fun e y
  obtain ⟨π, hπ⟩ := B.subtype.exists_leftInverse_of_injective (by simp)
  have hπ' : ∀ z : B, π (z : F) = z := fun z => LinearMap.congr_fun hπ z
  have : CompleteSpace B := FiniteDimensional.complete ℝ B
  let πL : F →L[ℝ] B := π.toContinuousLinearMap
  let SL : B →L[ℝ] E := (A.subtype ∘ₗ S).toContinuousLinearMap
  let C : X → B →L[ℝ] B := fun w => πL.comp ((Q w).comp SL)
  have hC : ContinuousAt C p := by
    have h₁ : Continuous fun T : E →L[ℝ] F => πL.comp (T.comp SL) :=
      ((ContinuousLinearMap.compL ℝ B F B πL).continuous).comp
        ((ContinuousLinearMap.compL ℝ B E F).flip SL).continuous
    exact h₁.continuousAt.comp hQ
  have hCp : C p = 1 := by
    ext1 y
    have : C p y = π (Q p (S y : E)) := rfl
    rw [this, hS, hπ']
    rfl
  have hset : range ((↑) : (B ≃L[ℝ] B) → B →L[ℝ] B) ∈ 𝓝 (C p) := by
    rw [hCp]
    exact ContinuousLinearEquiv.nhds (ContinuousLinearEquiv.refl ℝ B)
  have hU : ∀ᶠ w in 𝓝 p, C w ∈ range ((↑) : (B ≃L[ℝ] B) → B →L[ℝ] B) := hC.eventually hset
  filter_upwards [hU] with w hw hmap f hf
  obtain ⟨u, hu⟩ := hw
  let y : B := u.symm ⟨f, hf⟩
  refine ⟨(S y : E), (S y).2, ?_⟩
  have h₁ : C w y = ⟨f, hf⟩ := by
    rw [← hu]
    exact u.apply_symm_apply _
  have h₂ : C w y = ⟨Q w (S y : E), hmap _ (S y).2⟩ := by
    have : C w y = π (Q w (S y : E)) := rfl
    rw [this]
    exact hπ' ⟨_, hmap _ (S y).2⟩
  have := congrArg Subtype.val (h₁.symm.trans h₂)
  exact this.symm
theorem nonempty_tracelessBasis : Nonempty (Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.traceless_basis_nonempty <;> assumption
open YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces YangMills.Construction.Matrices.GroupLieProduct.ExpChartHolomorphy
theorem continuous_matExp : Continuous (ComplexMatrix2.matExp : ComplexMatrix2 → ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.continuous_matExp <;> assumption
theorem continuous_expChartAt {ι κ : Type} (p : ι ⊕ κ → ComplexMatrix2) :
    Continuous (expChartAt p) := by
  refine continuous_pi ?_
  rintro (i | k)
  · exact (continuous_matExp.comp (continuous_apply _)).mul continuous_const
  · exact continuous_const.add (continuous_apply _)
theorem expChartAt_zero {ι κ : Type} (p : ι ⊕ κ → ComplexMatrix2) : expChartAt p 0 = p := by apply _root_.YangMills.SharedProofs.p39871 <;> assumption
theorem isHolomorphicOnTraceless_inter {σ E : Type} [Fintype σ] {l : ℕ}
    (hH : ExpChartTheory)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {e : E ≃ ComplexCoordinates l}
    {O : Set (σ → ComplexMatrix2)}
    {f : (σ → ComplexMatrix2) → E} (h : IsHolomorphicOnTraceless b e O f)
    {P : Set (σ → ComplexMatrix2)}
    (hP : IsOpen P) : IsHolomorphicOnTraceless b e (O ∩ P) f := by
  have hsub := h.1.1
  have hT := (hH.2.1 σ).1
  have hO : IsSupOpen (O ∩ P) := by
    obtain ⟨Q, hQ, hQe⟩ := ((hT O hsub).1).1 h.1
    refine ((hT (O ∩ P) (inter_subset_left.trans hsub)).1).2 ⟨Q ∩ P, hQ.inter hP, ?_⟩
    rw [hQe]
    ext x
    simp only [mem_inter_iff]
    tauto
  refine ⟨hO, fun ν => ?_⟩
  have h₂ := h.2 ν
  exact ⟨((hT _ (inter_subset_left.trans hsub)).2 b ν).1 hO,
    h₂.2.1.mono (preimage_mono inter_subset_left), fun a ha j => h₂.2.2 a ha.1 j⟩
theorem isHolomorphicToUnimodular_inter {ι κ : Type} [Fintype ι] [Fintype κ]
    (hH : ExpChartTheory)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (h : IsHolomorphicToUnimodular b W Φ) {P : Set (ι ⊕ κ → ComplexMatrix2)} (hP : IsOpen P) :
    IsHolomorphicToUnimodular b (W ∩ P) Φ := by
  obtain ⟨⟨Q, hQ, hW⟩, hmaps, hc, hat⟩ := h
  refine ⟨⟨Q ∩ P, hQ.inter hP, ?_⟩, hmaps.mono_left inter_subset_left,
    hc.mono inter_subset_left, ?_⟩
  · rw [hW]
    ext x
    simp only [mem_inter_iff]
    tauto
  · intro p hp
    obtain ⟨O, h0, hO, hhol⟩ := hat p hp.1
    refine ⟨O ∩ expChartAt p ⁻¹' P, ⟨h0, ?_⟩,
      fun A hA => ⟨⟨(hO A hA.1).1, hA.2⟩, (hO A hA.1).2⟩, ?_⟩
    · rw [mem_preimage, expChartAt_zero]
      exact hp.2
    · exact isHolomorphicOnTraceless_inter hH hhol (hP.preimage (continuous_expChartAt p))
theorem isSubspaceAnalyticToProduct_inter {R R' : Type} [Fintype R]
    (hH : ExpChartTheory)
    {𝒲 : Set (R ⊕ Empty → ComplexMatrix2)}
    {f : (R ⊕ Empty → ComplexMatrix2) → R' ⊕ Empty → ComplexMatrix2}
    (h : IsSubspaceAnalyticToProduct (⊥ : Submodule ℝ (Empty → ComplexMatrix2))
      (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) 𝒲 f) {O : Set (R → ComplexMatrix2)}
    (hO : IsOpen O) :
    IsSubspaceAnalyticToProduct (⊥ : Submodule ℝ (Empty → ComplexMatrix2))
      (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) (𝒲 ∩ groupComponent ⁻¹' O) f := by
  obtain ⟨⟨hle, Q, hQ, hW⟩, hle', hmaps, hloc⟩ := h
  have hgp : IsOpen ((groupComponent : (R ⊕ Empty → ComplexMatrix2) → R → ComplexMatrix2) ⁻¹' O) :=
    hO.preimage (continuous_pi fun r => continuous_apply _)
  refine ⟨⟨hle, Q ∩ groupComponent ⁻¹' O, hQ.inter hgp, ?_⟩, hle',
    hmaps.mono_left inter_subset_left, ?_⟩
  · rw [hW]
    ext x
    simp only [mem_inter_iff]
    tauto
  · rintro p ⟨hp, hpO⟩
    obtain ⟨𝒳, hp𝒳, ⟨P, hP, h𝒳⟩, hsub, Ψ, hΨ, hEq⟩ := hloc p hp
    refine ⟨𝒳 ∩ groupComponent ⁻¹' O, ⟨hp𝒳, hpO⟩,
      ⟨P ∩ groupComponent ⁻¹' O, hP.inter hgp, ?_⟩,
      fun q hq => ⟨hsub ⟨hq.1.1, hq.2⟩, hq.1.2⟩, Ψ, fun b => ?_, fun q hq => hEq ⟨hq.1.1, hq.2⟩⟩
    · rw [h𝒳]
      ext x
      simp only [mem_inter_iff]
      tauto
    · have hb := hΨ b
      obtain ⟨⟨P', hP', hb₁⟩, hb₂, -⟩ := hb
      refine ⟨⟨P' ∩ groupComponent ⁻¹' O, hP'.inter hgp, ?_⟩,
        fun i => isHolomorphicToUnimodular_inter hH (hb₂ i) hgp, fun k => k.elim⟩
      rw [hb₁]
      ext x
      simp only [mem_inter_iff]
      tauto
def matrixLinearEquiv : ComplexMatrix2 ≃ₗ[ℝ] ComplexCoordinates 4 :=
  { ComplexCoordinates.matrixEquiv with
    map_add' := fun X Y => by
      funext k
      simp [ComplexCoordinates.matrixEquiv]
    map_smul' := fun c X => by
      funext k
      simp [ComplexCoordinates.matrixEquiv] }
theorem contDiff_matrixEquiv :
    ContDiff ℝ 1 (ComplexCoordinates.matrixEquiv : ComplexMatrix2 → ComplexCoordinates 4) :=
  (matrixLinearEquiv.toContinuousLinearEquiv : ComplexMatrix2 →L[ℝ] ComplexCoordinates 4).contDiff
theorem contDiff_matrixEquiv_symm :
    ContDiff ℝ 1 (ComplexCoordinates.matrixEquiv.symm : ComplexCoordinates 4 → ComplexMatrix2) :=
  (matrixLinearEquiv.symm.toContinuousLinearEquiv :
    ComplexCoordinates 4 →L[ℝ] ComplexMatrix2).contDiff
theorem contDiffAt_logSeries_one (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    ContDiffAt ℝ 1 ComplexMatrix2.logSeries 1 := by
  have hlog := hP.2.2.2.2.2
  have hO := hlog.1
  have hcd := ((hP.1 _ _ hO).1 4 _ hlog).2.1
  have h1 : ComplexCoordinates.matrixEquiv (1 : ComplexMatrix2) ∈
      ComplexCoordinates.matrixEquiv '' ComplexMatrix2.logBall :=
    ⟨1, by simp [ComplexMatrix2.logBall], rfl⟩
  have hat := (hcd.contDiffAt (hO.mem_nhds h1)).of_le (m := 1) (by simp)
  have h₁ := ContDiffAt.comp (f := ComplexCoordinates.matrixEquiv) (1 : ComplexMatrix2) hat
    contDiff_matrixEquiv.contDiffAt
  have h₂ := ContDiffAt.comp (1 : ComplexMatrix2) contDiff_matrixEquiv_symm.contDiffAt h₁
  refine h₂.congr_of_eventuallyEq (Eventually.of_forall fun X => ?_)
  simp
theorem logSeries_one : ComplexMatrix2.logSeries 1 = 0 := by
  simp [ComplexMatrix2.logSeries]
theorem exists_contDiffAt_extension {R R' : Type} [Fintype R] [Fintype R']
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hH : ExpChartTheory)
    {𝒲 : Set (R ⊕ Empty → ComplexMatrix2)}
    {f : (R ⊕ Empty → ComplexMatrix2) → R' ⊕ Empty → ComplexMatrix2}
    (hf : IsSubspaceAnalyticToProduct (⊥ : Submodule ℝ (Empty → ComplexMatrix2))
      (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) 𝒲 f)
    (h1 : ofParts (1 : R → ComplexMatrix2) (Empty.elim : Empty → ComplexMatrix2) ∈ 𝒲) :
    ∃ M : (R → ComplexMatrix2) → R' → ComplexMatrix2, ContDiffAt ℝ 1 M 1 ∧
      ∀ᶠ w in 𝓝 (1 : R → ComplexMatrix2), w ∈ specialUnitaryPower R → ∀ c,
        M w c = f (ofParts w (Empty.elim : Empty → ComplexMatrix2)) (.inl c) := by
  classical
  obtain ⟨b⟩ := nonempty_tracelessBasis
  obtain ⟨-, -, -, hloc⟩ := hf
  obtain ⟨𝒳, hq𝒳, h𝒳, h𝒳sub, Ψ, hΨ, hEq⟩ := hloc _ h1
  set q₁ := ofParts (1 : R → ComplexMatrix2) (Empty.elim : Empty → ComplexMatrix2) with hq₁
  have hmat : ∀ c : R', IsHolomorphicToCoords b ComplexCoordinates.matrixEquiv 𝒳
      (fun p => Ψ p (.inl c)) := fun c => by
    have hg := (hΨ b).2.1 c
    exact ((hH.2.2.2.1 R Empty).2.1 b 𝒳 _ h𝒳 hg.2.1).1 hg
  have hat := fun c => (hmat c).2.2 q₁ hq𝒳
  choose O hO0 hOX hOh using hat
  let ν := Fintype.equivFin (R ⊕ Empty)
  let tC := tupleOfCoords b ν
  let g : R' → ComplexCoordinates (Fintype.card (R ⊕ Empty) * 3) → ComplexCoordinates 4 :=
    fun c => ComplexCoordinates.matrixEquiv ∘ ((fun p => Ψ p (.inl c)) ∘ expChartAt q₁) ∘ tC
  have hgo : ∀ c, IsOpen (tC ⁻¹' O c) := fun c => ((hOh c).2 ν).1
  have hgc : ∀ c, ContDiffOn ℝ ∞ (g c) (tC ⁻¹' O c) := fun c =>
    ((hP.1 _ _ (hgo c)).1 4 (g c) ((hOh c).2 ν)).2.1
  obtain ⟨proj, hproj⟩ :=
    ComplexMatrix2.traceless.subtype.exists_leftInverse_of_injective (by simp)
  have hproj' : ∀ y : ComplexMatrix2.traceless, proj (y : ComplexMatrix2) = y :=
    fun y => LinearMap.congr_fun hproj y
  let θ : (R ⊕ Empty → ComplexMatrix2) →ₗ[ℂ] ComplexCoordinates (Fintype.card (R ⊕ Empty) * 3) :=
    LinearMap.pi fun k => (b.coord (finProdFinEquiv.symm k).2) ∘ₗ proj ∘ₗ
      LinearMap.proj (ν.symm (finProdFinEquiv.symm k).1)
  have hθ : ∀ Y ∈ tracelessPi (R ⊕ Empty), tC (θ Y) = Y := by
    intro Y hY
    funext i
    have hy : proj (Y i) = ⟨Y i, hY i⟩ := hproj' ⟨Y i, hY i⟩
    have hsum := congrArg (Subtype.val) (b.sum_repr ⟨Y i, hY i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    simp only [tC, tupleOfCoords, ComplexCoordinates.tracelessTuple, θ, LinearMap.pi_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      Module.Basis.coord_apply, hy]
    exact hsum
  let θR : (R ⊕ Empty → ComplexMatrix2) →L[ℝ] ComplexCoordinates (Fintype.card (R ⊕ Empty) * 3) :=
    (θ.restrictScalars ℝ).toContinuousLinearMap
  let ℓ : (R → ComplexMatrix2) → R ⊕ Empty → ComplexMatrix2 := fun w =>
    ofParts (fun r => ComplexMatrix2.logSeries (w r)) (Empty.elim : Empty → ComplexMatrix2)
  have hℓ1 : ℓ 1 = 0 := by
    funext i
    rcases i with r | e
    · exact logSeries_one
    · exact e.elim
  have hℓ : ContDiffAt ℝ 1 ℓ 1 := by
    refine contDiffAt_pi.2 fun i => ?_
    rcases i with r | e
    · exact ContDiffAt.comp (g := ComplexMatrix2.logSeries)
        (f := fun w : R → ComplexMatrix2 => w r) (1 : R → ComplexMatrix2)
        (contDiffAt_logSeries_one hP) (contDiff_apply ℝ ComplexMatrix2 r).contDiffAt
    · exact e.elim
  have htC0 : tC 0 = 0 := by
    funext i
    simp [tC, tupleOfCoords, ComplexCoordinates.tracelessTuple]
  have hz : ∀ c, θ (ℓ 1) ∈ tC ⁻¹' O c := fun c => by
    rw [hℓ1, map_zero, mem_preimage, htC0]
    exact hO0 c
  have hθℓ : ContDiffAt ℝ 1 (fun w => θ (ℓ w)) 1 :=
    ContDiffAt.comp (g := θR) (f := ℓ) (1 : R → ComplexMatrix2) θR.contDiff.contDiffAt hℓ
  refine ⟨fun w c => ComplexCoordinates.matrixEquiv.symm (g c (θ (ℓ w))), ?_, ?_⟩
  · refine contDiffAt_pi.2 fun c => ?_
    have h₁ : ContDiffAt ℝ 1 (g c) (θ (ℓ 1)) :=
      ((hgc c).contDiffAt ((hgo c).mem_nhds (hz c))).of_le (by simp)
    have h₂ := ContDiffAt.comp (f := fun w => θ (ℓ w)) (1 : R → ComplexMatrix2) h₁ hθℓ
    exact ContDiffAt.comp (1 : R → ComplexMatrix2) contDiff_matrixEquiv_symm.contDiffAt h₂
  · have hnorm : ∀ᶠ w in 𝓝 (1 : R → ComplexMatrix2), ∀ r,
        ComplexMatrix2.operatorNorm (w r - 1) < 9 / 10 := by
      refine eventually_all.2 fun r => ?_
      have hc : ContinuousAt (fun w : R → ComplexMatrix2 => ‖w r - 1‖) 1 :=
        (((continuous_apply r).sub continuous_const).norm).continuousAt
      refine hc.eventually_lt continuousAt_const ?_
      simp
    have hO' : ∀ᶠ w in 𝓝 (1 : R → ComplexMatrix2), ∀ c, θ (ℓ w) ∈ tC ⁻¹' O c :=
      eventually_all.2 fun c => hθℓ.continuousAt.eventually ((hgo c).mem_nhds (hz c))
    filter_upwards [hnorm, hO'] with w hn hOw hG c
    have hdet : ∀ r, (w r).det = 1 := fun r => (Matrix.mem_specialUnitaryGroup_iff.1 (hG r)).2
    have hY : ℓ w ∈ tracelessPi (R ⊕ Empty) := by
      rintro (r | e)
      · exact (hE.2.2.2.2.2.2.1 (w r) (hdet r) (hn r).le).2
      · exact e.elim
    have hx : tC (θ (ℓ w)) = ℓ w := hθ _ hY
    have hex : expChartAt q₁ (ℓ w) = ofParts w (Empty.elim : Empty → ComplexMatrix2) := by
      funext i
      rcases i with r | e
      · have hlt : ComplexMatrix2.operatorNorm (w r - 1) < 1 := (hn r).trans (by norm_num)
        have := (hE.2.2.2.1 (w r - 1) hlt).2.2.2.2
        rw [add_sub_cancel] at this
        change ComplexMatrix2.matExp (ComplexMatrix2.logSeries (w r)) * 1 = w r
        rw [this, mul_one]
      · exact e.elim
    have hmem : ℓ w ∈ O c := by
      have := hOw c
      rwa [mem_preimage, hx] at this
    have hq𝒳' : ofParts w (Empty.elim : Empty → ComplexMatrix2) ∈ 𝒳 := hex ▸ hOX c _ hmem
    have hsp : ofParts w (Empty.elim : Empty → ComplexMatrix2) ∈
        subspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) R :=
      ⟨(Submodule.mem_bot ℝ).2 (Subsingleton.elim _ _), hG⟩
    have hfin : ComplexCoordinates.matrixEquiv.symm (g c (θ (ℓ w))) =
        Ψ (ofParts w (Empty.elim : Empty → ComplexMatrix2)) (.inl c) := by
      simp only [g, Function.comp_apply, hx, hex, Equiv.symm_apply_apply]
    rw [hfin]
    exact congrFun (hEq ⟨hq𝒳', hsp⟩) _
open YangMills.Construction.Tower.LeftChartFields
variable {L n k j a b : ℕ}
theorem opposite_opposite (x : Edge L n k j) : x.opposite.opposite = x := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
theorem not_isPositivelyOriented_opposite (hC : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) {x : Edge L n k j}
    (hx : x.IsPositivelyOriented) : ¬ x.opposite.IsPositivelyOriented := by
  intro hr
  obtain ⟨hfin, hne, hcl, -⟩ := ((hC L hL k j hj).1 n hn).2
  rcases (((hC L hL k j hj).1 n hn).1 univ hfin hne hcl).1.2.2 x (mem_univ x) with
    ⟨_, hno⟩ | ⟨_, hno⟩
  · refine hno ⟨x.opposite, ⟨⟨mem_univ _, hr⟩, opposite_opposite x⟩, fun y hy => ?_⟩
    have : y.opposite = x := hy.2
    rw [← this, opposite_opposite]
  · exact hno ⟨mem_univ x, hx⟩
theorem exists_edgeForm
    (hx : ∀ x : Edge L n k j, x.IsPositivelyOriented → ¬ x.opposite.IsPositivelyOriented)
    {f : PositiveEdge L n k j → ComplexMatrix2}
    (hf : f ∈ hermitianTracelessFunctions (PositiveEdge L n k j)) :
    ∃ B ∈ edgeFormSpace L n k j, restrictToPositiveEdges B = f := by
  classical
  have hval : ∀ (y : Edge L n k j) (h : y.IsPositivelyOriented),
      edgeFormOfPositiveValues f y = f ⟨y, h⟩ :=
    fun y h => dif_pos h
  have hneg : ∀ (y : Edge L n k j) (h : ¬ y.IsPositivelyOriented)
      (h' : y.opposite.IsPositivelyOriented),
      edgeFormOfPositiveValues f y = -f ⟨y.opposite, h'⟩ := fun y h h' => by
    unfold edgeFormOfPositiveValues
    rw [dif_neg h, dif_pos h']
  refine ⟨edgeFormOfPositiveValues f, ⟨fun y hy => ?_, fun y => ?_⟩, ?_⟩
  · rw [hval y hy]
    exact hf ⟨y, hy⟩ (mem_univ _)
  · by_cases hy : y.IsPositivelyOriented
    · have hr : y.opposite.opposite.IsPositivelyOriented := by rwa [opposite_opposite]
      rw [hneg y.opposite (hx y hy) hr, hval y hy]
      congr 2
    · have hr := PeriodicLattice.Bond.opposite_isPositivelyOriented hy
      rw [hneg y hy hr, hval _ hr, neg_neg]
  · funext r
    exact hval r.1 r.2
theorem fieldOfPositiveValues_restrict {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k j) :
    fieldOfPositiveValues (restrictToPositiveEdges U) = U := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem restrict_fieldOfPositiveValues (w : PositiveEdge L n k j → ComplexMatrix2) :
    restrictToPositiveEdges (fieldOfPositiveValues w) = w := by apply _root_.YangMills.SharedProofs.p777 <;> assumption
theorem logDirectionalDeriv_eq_of_extension
    [Fintype (PositiveEdge L n k a)] [Fintype (PositiveEdge L n k b)]
    (hlog : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra)
    (hleft : ∀ U ∈ fieldSpace L n k a, ∀ B ∈ edgeFormSpace L n k a,
      ∀ r : PositiveEdge L n k a,
      (∀ t : ℝ, leftExpMul ((t : ℂ) • B r) (U r) ∈ PeriodicLattice.compactGaugeGroup) ∧
      HasDerivAt (fun t : ℝ => leftExpMul ((t : ℂ) • B r) (U r)) (Complex.I • B r * U r) 0)
    (hbij : BijOn restrictToPositiveEdges (fieldSpace L n k a)
      (specialUnitaryPower (PositiveEdge L n k a)))
    {𝒰 : Set (Edge L n k a → ComplexMatrix2)}
    (hU : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰)
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (hmaps : MapsTo m 𝒰 (fieldSpace L n k b))
    {M : (PositiveEdge L n k a → ComplexMatrix2) → PositiveEdge L n k b → ComplexMatrix2}
    {O : Set (PositiveEdge L n k a → ComplexMatrix2)} (hO : IsOpen O)
    (hM : ∀ w ∈ O, w ∈ specialUnitaryPower (PositiveEdge L n k a) →
      fieldOfPositiveValues w ∈ 𝒰 → ∀ c, M w c = m (fieldOfPositiveValues w) c)
    {V : Edge L n k a → ComplexMatrix2} (hV : V ∈ 𝒰) (hv : restrictToPositiveEdges V ∈ O)
    {D : (PositiveEdge L n k a → ComplexMatrix2) →L[ℝ] (PositiveEdge L n k b → ComplexMatrix2)}
    (hD : HasFDerivAt M D (restrictToPositiveEdges V))
    {B : Edge L n k a → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k a)
    (c : PositiveEdge L n k b) :
    logDirectionalDeriv ℝ (fun X => m (PeriodicLattice.expTwist X V) c) (m V c) B =
        Complex.I⁻¹ • (D (fun r => Complex.I • B r * V r) c *
          star (M (restrictToPositiveEdges V) c)) ∧
      Complex.I⁻¹ • (D (fun r => Complex.I • B r * V r) c *
          star (M (restrictToPositiveEdges V) c)) ∈
        ComplexMatrix2.hermitianTraceless := by
  classical
  have hVc : V ∈ fieldSpace L n k a := hU.1 hV
  obtain ⟨OU, hOUo, hOUe⟩ := hU.2
  have himg : ∀ w ∈ OU, w ∈ specialUnitaryPower (PositiveEdge L n k a) →
      ∃ U ∈ 𝒰, restrictToPositiveEdges U = w := fun w h₁ h₂ => by
    have : w ∈ restrictToPositiveEdges '' 𝒰 := by
      rw [hOUe]
      exact ⟨h₁, h₂⟩
    exact this
  have hvOU : restrictToPositiveEdges V ∈ OU := by
    have : restrictToPositiveEdges V ∈ restrictToPositiveEdges '' 𝒰 := ⟨V, hV, rfl⟩
    rw [hOUe] at this
    exact this.1
  let w : ℝ → PositiveEdge L n k a → ComplexMatrix2 := fun t r => leftExpMul ((t : ℂ) • B r) (V r)
  have hw' : HasDerivAt w (fun r => Complex.I • B r * V r) 0 :=
    hasDerivAt_pi.2 fun r => (hleft V hVc B hB r).2
  have hwG : ∀ t, w t ∈ specialUnitaryPower (PositiveEdge L n k a) := fun t r =>
    (hleft V hVc B hB r).1 t
  have hw0 : w 0 = restrictToPositiveEdges V := by
    funext r
    simp [w, leftExpMul, restrictToPositiveEdges]
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), w t ∈ O ∩ OU :=
    hw'.continuousAt.eventually ((hO.inter hOUo).mem_nhds (by rw [hw0]; exact ⟨hv, hvOU⟩))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have h0I : (0 : ℝ) ∈ Metric.ball (0 : ℝ) ε := Metric.mem_ball_self hε
  have hI : IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) ε) :=
    ⟨Metric.isOpen_ball, by rw [Real.ball_eq_Ioo]; exact ordConnected_Ioo, h0I⟩
  have key : ∀ t ∈ Metric.ball (0 : ℝ) ε, PeriodicLattice.expTwist ((t : ℂ) • B) V ∈ 𝒰 ∧
      fieldOfPositiveValues (w t) = PeriodicLattice.expTwist ((t : ℂ) • B) V := by
    intro t ht
    obtain ⟨U', hU'c, hU'e⟩ := hbij.surjOn (hwG t)
    have hUeq : U' = PeriodicLattice.expTwist ((t : ℂ) • B) V := by
      funext x
      unfold PeriodicLattice.expTwist
      by_cases hx : x.IsPositivelyOriented
      · rw [if_pos hx]
        exact congrFun hU'e ⟨x, hx⟩
      · have hr := PeriodicLattice.Bond.opposite_isPositivelyOriented hx
        have h₁ : U' x.opposite = w t ⟨x.opposite, hr⟩ := congrFun hU'e ⟨x.opposite, hr⟩
        have h₂ := hU'c.2 x.opposite (mem_univ _)
        rw [opposite_opposite] at h₂
        rw [if_neg hx, h₂, h₁]
        rfl
    obtain ⟨U'', hU''𝒰, hU''e⟩ := himg (w t) (hball t ht).2 (hwG t)
    have hU'' : U'' = U' := hbij.injOn (hU.1 hU''𝒰) hU'c (hU''e.trans hU'e.symm)
    refine ⟨hUeq ▸ hU'' ▸ hU''𝒰, ?_⟩
    rw [← hU'e, fieldOfPositiveValues_restrict hU'c, hUeq]
  have hexp0 : PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B) V = V := by
    rw [← (key 0 h0I).2, hw0]
    exact fieldOfPositiveValues_restrict hVc
  let W : ℝ → ComplexMatrix2 := fun t => m (PeriodicLattice.expTwist (algebraMap ℝ ℂ t • B) V) c
  have hWM : ∀ t ∈ Metric.ball (0 : ℝ) ε, W t = M (w t) c := by
    intro t ht
    have h₁ := hM (w t) (hball t ht).1 (hwG t) ((key t ht).2 ▸ (key t ht).1) c
    rw [(key t ht).2] at h₁
    exact h₁.symm
  have hW0 : W 0 = m V c := by
    change m (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B) V) c = m V c
    rw [hexp0]
  have hMV : M (restrictToPositiveEdges V) c = m V c := by
    rw [← hW0, hWM 0 h0I, hw0]
  have hMw : HasDerivAt (fun t => M (w t)) (D fun r => Complex.I • B r * V r) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := w) (l := M) 0 (by rw [hw0]; exact hD) hw'
  have hMc : HasDerivAt (fun t => M (w t) c) (D (fun r => Complex.I • B r * V r) c) 0 :=
    (hasDerivAt_pi.1 hMw) c
  have hW : HasDerivAt W (D (fun r => Complex.I • B r * V r) c) 0 :=
    hMc.congr_of_eventuallyEq
      (Filter.eventually_of_mem (Metric.ball_mem_nhds _ hε) fun t ht => hWM t ht)
  have hG : MapsTo W (Metric.ball (0 : ℝ) ε) PeriodicLattice.compactGaugeGroup := fun t ht =>
    (hmaps (key t ht).1).1 c.1 (mem_univ _)
  obtain ⟨-, -, hd, hmem⟩ := hlog _ hI W hG hW.differentiableAt
  have hWG : W 0 ∈ ComplexMatrix2.specialUnitary := hG h0I
  have hinv : (W 0)⁻¹ = star (W 0) :=
    Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.1
      (Matrix.mem_specialUnitaryGroup_iff.1 hWG).1)
  rw [hW.deriv, hinv] at hmem
  rw [hW.deriv, hinv] at hd
  rw [hMV, ← hW0]
  refine ⟨?_, hmem⟩
  rw [← hd, ← hinv, hW0]
  rfl
def twistedDerivOp {P P' : Type} [Fintype P] [Fintype P']
    (D : (P → ComplexMatrix2) →L[ℝ] (P' → ComplexMatrix2))
    (w : P → ComplexMatrix2) (z : P' → ComplexMatrix2) :
    (P → ComplexMatrix2) →L[ℝ] (P' → ComplexMatrix2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X c => Complex.I⁻¹ • (D (fun r => Complex.I • X r * w r) c * star (z c))
      map_add' := fun X Y => by
        have h : (fun r => Complex.I • (X + Y) r * w r) =
            (fun r => Complex.I • X r * w r) + fun r => Complex.I • Y r * w r := by
          funext r
          simp [smul_add, add_mul]
        funext c
        have hD : D (fun r => Complex.I • (X + Y) r * w r) c =
            D (fun r => Complex.I • X r * w r) c + D (fun r => Complex.I • Y r * w r) c := by
          rw [h, map_add]
          rfl
        change Complex.I⁻¹ • (D (fun r => Complex.I • (X + Y) r * w r) c * star (z c)) =
          Complex.I⁻¹ • (D (fun r => Complex.I • X r * w r) c * star (z c)) +
            Complex.I⁻¹ • (D (fun r => Complex.I • Y r * w r) c * star (z c))
        rw [hD, add_mul, smul_add]
      map_smul' := fun t X => by
        have h : (fun r => Complex.I • (t • X) r * w r) =
            t • fun r => Complex.I • X r * w r := by
          funext r
          simp only [Pi.smul_apply, smul_comm Complex.I t, smul_mul_assoc]
        funext c
        have hD : D (fun r => Complex.I • (t • X) r * w r) c =
            t • D (fun r => Complex.I • X r * w r) c := by
          rw [h, map_smul]
          rfl
        change Complex.I⁻¹ • (D (fun r => Complex.I • (t • X) r * w r) c * star (z c)) =
          t • (Complex.I⁻¹ • (D (fun r => Complex.I • X r * w r) c * star (z c)))
        rw [hD, smul_mul_assoc, smul_comm] }
theorem twistedDerivOp_apply {P P' : Type} [Fintype P] [Fintype P']
    (D : (P → ComplexMatrix2) →L[ℝ] (P' → ComplexMatrix2)) (w : P → ComplexMatrix2)
    (z : P' → ComplexMatrix2) (X : P → ComplexMatrix2) (c : P') :
    twistedDerivOp D w z X c =
      Complex.I⁻¹ • (D (fun r => Complex.I • X r * w r) c * star (z c)) := rfl
theorem continuousOn_twistedDerivOp {P P' : Type} [Fintype P] [Fintype P']
    {D : (P → ComplexMatrix2) → (P → ComplexMatrix2) →L[ℝ] (P' → ComplexMatrix2)}
    {M : (P → ComplexMatrix2) → P' → ComplexMatrix2}
    {O : Set (P → ComplexMatrix2)} (hD : ContinuousOn D O) (hM : ContinuousOn M O) :
    ContinuousOn (fun w => twistedDerivOp (D w) w (M w)) O := by
  refine continuousOn_clm_apply.2 fun X => ?_
  refine continuousOn_pi.2 fun c => ?_
  simp only [twistedDerivOp_apply]
  have h₀ : ContinuousOn (fun w : P → ComplexMatrix2 => fun r => Complex.I • X r * w r) O :=
    (continuous_pi fun r => continuous_const.mul (continuous_apply r)).continuousOn
  have h₁ : ContinuousOn (fun w => D w fun r => Complex.I • X r * w r) O := hD.clm_apply h₀
  have h₂ : ContinuousOn (fun w => (D w fun r => Complex.I • X r * w r) c) O :=
    (continuous_apply c).comp_continuousOn h₁
  have h₃ : ContinuousOn (fun w => M w c) O := (continuous_apply c).comp_continuousOn hM
  have hs : Continuous (star : ComplexMatrix2 → ComplexMatrix2) :=
    Continuous.matrix_conjTranspose continuous_id
  exact (h₂.mul (hs.comp_continuousOn h₃)).const_smul Complex.I⁻¹
theorem leftDifferential_of_not_isPositivelyOriented
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    {V B : Edge L n k a → ComplexMatrix2} {y : Edge L n k b} (hy : ¬ y.IsPositivelyOriented) :
    leftDifferential m V B y = -leftDifferential m V B y.opposite := by
  have hr := PeriodicLattice.Bond.opposite_isPositivelyOriented hy
  simp only [leftDifferential, extendOddly, if_neg hy, if_pos hr]
theorem differentialSurjectiveNearIdentity_holds (hE : ComplexMatrix2.ExpLogEstimates)
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hH : ExpChartTheory)
    (hA : LeftChartFields.Claim)
    (hC : BondSetFields.ProductStructureHolds) :
    DifferentialSurjectiveNearIdentity := by
  intro L n k a b hL hn ha hb 𝒰 m hU hm honto
  classical
  obtain ⟨-, hmaps, iR, iR', hra⟩ := hm
  obtain ⟨hclA, hTanA, -⟩ := (hA.2.2 L k a hL ha).1 n hn
  have hbijA : BijOn restrictToPositiveEdges (fieldSpace L n k a)
      (specialUnitaryPower (PositiveEdge L n k a)) := hTanA.2.1
  have hlog : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra :=
    fun I hI => (hA.1 I hI).1
  have hxa : ∀ x : Edge L n k a, x.IsPositivelyOriented → ¬ x.opposite.IsPositivelyOriented :=
    fun x hx => not_isPositivelyOriented_opposite hC hL hn ha hx
  have hxb : ∀ x : Edge L n k b, x.IsPositivelyOriented → ¬ x.opposite.IsPositivelyOriented :=
    fun x hx => not_isPositivelyOriented_opposite hC hL hn hb hx
  have hone : restrictToPositiveEdges (trivialField L n k a) =
      (1 : PositiveEdge L n k a → ComplexMatrix2) := funext fun _ => rfl
  have hconf1 : fieldOfPositiveValues (1 : PositiveEdge L n k a → ComplexMatrix2) =
      trivialField L n k a := by
    rw [← hone]
    exact fieldOfPositiveValues_restrict (hU.1.1 hU.2)
  have hq₁ : ofParts (1 : PositiveEdge L n k a → ComplexMatrix2)
      (Empty.elim : Empty → ComplexMatrix2) ∈
      {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
    change fieldOfPositiveValues (1 : PositiveEdge L n k a → ComplexMatrix2) ∈ 𝒰
    rw [hconf1]
    exact hU.2
  obtain ⟨M, hMcd, hMev⟩ := exists_contDiffAt_extension hE hP hH hra hq₁
  obtain ⟨f', u, hu, hf'c, hf'⟩ := contDiffAt_one_iff.1 hMcd
  obtain ⟨O₁, hO₁sub, hO₁o, h1O₁⟩ := mem_nhds_iff.1 (inter_mem hu hMev)
  have hMO₁ : ContinuousOn M O₁ := fun w hw =>
    (hf' w (hO₁sub hw).1).continuousAt.continuousWithinAt
  have hf'O₁ : ContinuousOn f' O₁ := hf'c.mono fun w hw => (hO₁sub hw).1
  let Q : (PositiveEdge L n k a → ComplexMatrix2) →
      (PositiveEdge L n k a → ComplexMatrix2) →L[ℝ] (PositiveEdge L n k b → ComplexMatrix2) :=
    fun w => twistedDerivOp (f' w) w (M w)
  have hQ : ContinuousAt Q 1 :=
    (continuousOn_twistedDerivOp hf'O₁ hMO₁).continuousAt (hO₁o.mem_nhds h1O₁)
  have hMext : ∀ w ∈ O₁, w ∈ specialUnitaryPower (PositiveEdge L n k a) →
      fieldOfPositiveValues w ∈ 𝒰 → ∀ c, M w c = m (fieldOfPositiveValues w) c :=
    fun w hw hG _ c => (hO₁sub hw).2 hG c
  have hread : ∀ V ∈ 𝒰, restrictToPositiveEdges V ∈ O₁ → ∀ B ∈ edgeFormSpace L n k a,
      ∀ c : PositiveEdge L n k b,
      logDirectionalDeriv ℝ (fun X => m (PeriodicLattice.expTwist X V) c) (m V c) B =
          Q (restrictToPositiveEdges V) (restrictToPositiveEdges B) c ∧
        Q (restrictToPositiveEdges V) (restrictToPositiveEdges B) c ∈
          ComplexMatrix2.hermitianTraceless :=
    fun V hV hv B hB c => logDirectionalDeriv_eq_of_extension hlog hclA.1.1 hbijA hU.1 hmaps
      hO₁o hMext hV hv (hf' _ (hO₁sub hv).1) hB c
  have hvalue : ∀ V ∈ 𝒰, restrictToPositiveEdges V ∈ O₁ → ∀ B ∈ edgeFormSpace L n k a,
      ∀ c : PositiveEdge L n k b,
      leftDifferential m V B c = Q (restrictToPositiveEdges V) (restrictToPositiveEdges B) c := by
    intro V hV hv B hB c
    have hc : (c : Edge L n k b).IsPositivelyOriented := c.2
    simp only [leftDifferential, extendOddly, if_pos hc]
    exact (hread V hV hv B hB c).1
  have hinto : ∀ V ∈ 𝒰, restrictToPositiveEdges V ∈ O₁ →
      ∀ x ∈ hermitianTracelessFunctions (PositiveEdge L n k a),
      Q (restrictToPositiveEdges V) x ∈ hermitianTracelessFunctions (PositiveEdge L n k b) := by
    intro V hV hv x hx
    obtain ⟨B, hB, rfl⟩ := exists_edgeForm hxa hx
    exact fun c _ => (hread V hV hv B hB c).2
  have honto1 : ∀ f ∈ hermitianTracelessFunctions (PositiveEdge L n k b),
      ∃ x ∈ hermitianTracelessFunctions (PositiveEdge L n k a), Q 1 x = f := by
    intro f hf
    obtain ⟨B', hB', rfl⟩ := exists_edgeForm hxb hf
    obtain ⟨B, hB, hBe⟩ := honto B' hB'
    refine ⟨restrictToPositiveEdges B, fun r _ => hB.1 r.1 r.2, ?_⟩
    funext c
    have h := hvalue _ hU.2 (hone ▸ h1O₁) B hB c
    rw [hBe, hone] at h
    exact h.symm
  have hev := eventually_surjOn_of_continuousAt
    (hermitianTracelessFunctions (PositiveEdge L n k a))
    (hermitianTracelessFunctions (PositiveEdge L n k b)) Q 1 hQ honto1
  obtain ⟨O₂', hsub₂, hO₂'o, h1O₂'⟩ := mem_nhds_iff.1 hev
  have hO₂o : IsOpen (O₂' ∩ O₁) := hO₂'o.inter hO₁o
  obtain ⟨OU, hOUo, hOUe⟩ := hU.1.2
  have h1OU : restrictToPositiveEdges (trivialField L n k a) ∈ OU := by
    have : restrictToPositiveEdges (trivialField L n k a) ∈ restrictToPositiveEdges '' 𝒰 :=
      ⟨_, hU.2, rfl⟩
    rw [hOUe] at this
    exact this.1
  have h1O₂ : restrictToPositiveEdges (trivialField L n k a) ∈ O₂' ∩ O₁ := by
    rw [hone]
    exact ⟨h1O₂', h1O₁⟩
  have hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup
      {V | V ∈ 𝒰 ∧ restrictToPositiveEdges V ∈ O₂' ∩ O₁} := by
    refine ⟨fun V hV => hU.1.1 hV.1, OU ∩ (O₂' ∩ O₁), hOUo.inter hO₂o, ?_⟩
    ext w
    constructor
    · rintro ⟨V, ⟨hV, hv⟩, rfl⟩
      have : restrictToPositiveEdges V ∈ restrictToPositiveEdges '' 𝒰 := ⟨V, hV, rfl⟩
      rw [hOUe] at this
      exact ⟨⟨this.1, hv⟩, this.2⟩
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      have : w ∈ restrictToPositiveEdges '' 𝒰 := by
        rw [hOUe]
        exact ⟨h₁, h₃⟩
      obtain ⟨V, hV, rfl⟩ := this
      exact ⟨V, ⟨hV, h₂⟩, rfl⟩
  refine ⟨{V | V ∈ 𝒰 ∧ restrictToPositiveEdges V ∈ O₂' ∩ O₁}, fun V hV => hV.1,
    ⟨hopen, hU.2, h1O₂⟩, ?_, ⟨hopen, hmaps.mono_left fun V hV => hV.1, iR, iR', ?_⟩, ?_⟩
  · have hcontP : Continuous (restrictToPositiveEdges :
        (Edge L n k a → ComplexMatrix2) → PositiveEdge L n k a → ComplexMatrix2) :=
      continuous_pi fun r => continuous_apply _
    have hnear : ∀ᶠ V in 𝓝 (fun _ => (1 : ComplexMatrix2) : Edge L n k a → ComplexMatrix2),
        restrictToPositiveEdges V ∈ OU ∩ (O₂' ∩ O₁) :=
      hcontP.continuousAt.eventually
        ((hOUo.inter hO₂o).mem_nhds ⟨h1OU, h1O₂⟩)
    unfold EventuallyNearIdentity
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnear, self_mem_nhdsWithin] with V hV hVc
    have hb' := hbijA.mapsTo hVc
    have : restrictToPositiveEdges V ∈ restrictToPositiveEdges '' 𝒰 := by
      rw [hOUe]
      exact ⟨hV.1, hb'⟩
    obtain ⟨V', hV', he⟩ := this
    have hVV : V' = V := hbijA.injOn (hU.1.1 hV') hVc he
    exact ⟨hVV ▸ hV', hV.2⟩
  · have h𝒲 : {q : PositiveEdge L n k a ⊕ Empty → ComplexMatrix2 |
        fieldOfPositiveValues (groupComponent q) ∈
          {V | V ∈ 𝒰 ∧ restrictToPositiveEdges V ∈ O₂' ∩ O₁}} =
        {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰} ∩
          groupComponent ⁻¹' (O₂' ∩ O₁) := by
      ext q
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, restrict_fieldOfPositiveValues]
    rw [h𝒲]
    exact isSubspaceAnalyticToProduct_inter hH hra hO₂o
  · rintro V ⟨hV, hv₂, hv₁⟩ B' hB'
    have hf : restrictToPositiveEdges B' ∈ hermitianTracelessFunctions (PositiveEdge L n k b) :=
      fun r _ => hB'.1 r.1 r.2
    obtain ⟨x, hx, hQx⟩ := hsub₂ hv₂ (hinto V hV hv₁) _ hf
    obtain ⟨B, hB, rfl⟩ := exists_edgeForm hxa hx
    refine ⟨B, hB, ?_⟩
    have hval : ∀ c : PositiveEdge L n k b, leftDifferential m V B c = B' c := fun c =>
      (hvalue V hV hv₁ B hB c).trans (congrFun hQx c)
    funext y
    by_cases hy : y.IsPositivelyOriented
    · exact hval ⟨y, hy⟩
    · have hr := PeriodicLattice.Bond.opposite_isPositivelyOriented hy
      have h₂ := hB'.2 y.opposite
      rw [opposite_opposite] at h₂
      rw [leftDifferential_of_not_isPositivelyOriented hy, h₂]
      exact congrArg Neg.neg (hval ⟨y.opposite, hr⟩)
end YangMills.Construction.Tower.NearIdentitySurjectivity
end

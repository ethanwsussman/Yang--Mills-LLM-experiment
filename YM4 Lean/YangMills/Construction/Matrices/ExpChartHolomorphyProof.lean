import YangMills.Construction.Lattice.GaugeCovarianceOfHolonomyProof
import YangMills.Construction.Lattice.DomainsOfTheTwoSchemesProof
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import Mathlib
open Set Filter
open scoped Matrix.Norms.L2Operator Topology
open YangMills.Construction.Coordinates YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct.ExpChartHolomorphy
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy renaming Properties → HoloFacts
variable {σ τ ι κ ι' κ' : Type}
private theorem isHolomorphicIn_iff (hH : HoloFacts)
    {N N' : ℕ} {O : Set (ComplexCoordinates N)} {f : ComplexCoordinates N → ComplexCoordinates N'} :
    ComplexCoordinates.IsHolomorphicIn O f ↔ IsOpen O ∧ DifferentiableOn ℂ f O := by apply _root_.YangMills.SharedProofs.p123 <;> assumption
private def matrixLinearEquiv : ComplexMatrix2 ≃ₗ[ℂ] ComplexCoordinates 4 :=
  { ComplexCoordinates.matrixEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
private def matrixCLE : ComplexMatrix2 ≃L[ℂ] ComplexCoordinates 4 :=
  matrixLinearEquiv.toContinuousLinearEquiv
private def piLinearEquiv {k : ℕ} (ν : σ ≃ Fin k) : (σ → ComplexMatrix2) ≃ₗ[ℂ] ComplexCoordinates
    (ComplexCoordinates.productDim fun _ : Fin k => ComplexCoordinates.Component.matrix) :=
  { matrixPiEquiv ν with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
private def piCLE [Fintype σ] {k : ℕ} (ν : σ ≃ Fin k) : (σ → ComplexMatrix2) ≃L[ℂ] ComplexCoordinates
    (ComplexCoordinates.productDim fun _ : Fin k => ComplexCoordinates.Component.matrix) :=
  (piLinearEquiv ν).toContinuousLinearEquiv
private def tracelessProj : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2.traceless :=
  LinearMap.codRestrict ComplexMatrix2.traceless
    (LinearMap.id - (Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight ((1 / 2 : ℂ) • (1 : ComplexMatrix2)))
    (by
      intro X
      change Matrix.trace _ = 0
      simp [Matrix.trace_fin_two])
private theorem tracelessProj_of_mem (A : ComplexMatrix2) (hA : A ∈ ComplexMatrix2.traceless) :
    tracelessProj A = ⟨A, hA⟩ := by
  apply Subtype.ext
  have h : Matrix.trace A = 0 := hA
  simp [tracelessProj, h]
private def basisCoords (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    ComplexMatrix2 →ₗ[ℂ] Fin 3 → ℂ :=
  b.equivFun.toLinearMap ∘ₗ tracelessProj
private theorem sum_smul_mem_traceless (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (v : Fin 3 → ℂ) : ∑ c, v c • (b c : ComplexMatrix2) ∈ ComplexMatrix2.traceless :=
  Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (b c).2
private theorem basisCoords_sum (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (v : Fin 3 → ℂ) :
    basisCoords b (∑ c, v c • (b c : ComplexMatrix2)) = v := by
  have h : (⟨∑ c, v c • (b c : ComplexMatrix2), sum_smul_mem_traceless b v⟩ :
      ComplexMatrix2.traceless) = b.equivFun.symm v := by
    apply Subtype.ext
    simp [Module.Basis.equivFun_symm_apply]
  rw [basisCoords, LinearMap.comp_apply, tracelessProj_of_mem _ (sum_smul_mem_traceless b v), h]
  exact b.equivFun.apply_symm_apply v
private theorem sum_basisCoords (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (A : ComplexMatrix2) (hA : A ∈ ComplexMatrix2.traceless) :
    ∑ c, basisCoords b A c • (b c : ComplexMatrix2) = A := by
  have h : basisCoords b A = b.equivFun ⟨A, hA⟩ := by
    rw [basisCoords, LinearMap.comp_apply, tracelessProj_of_mem A hA]
    rfl
  rw [h]
  calc ∑ c, b.equivFun ⟨A, hA⟩ c • (b c : ComplexMatrix2)
      = ((∑ c, b.equivFun ⟨A, hA⟩ c • b c : ComplexMatrix2.traceless) : ComplexMatrix2) := by
        simp only [Submodule.coe_sum, Submodule.coe_smul]
    _ = A := by rw [b.sum_equivFun]
variable {n : ℕ}
private def coordChart (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (μ : σ ≃ Fin n) :
    ComplexCoordinates (n * 3) →ₗ[ℂ] σ → ComplexMatrix2 where
  toFun w i := ComplexCoordinates.tracelessTuple b w (μ i)
  map_add' w w' := by
    funext i
    simp [ComplexCoordinates.tracelessTuple, add_smul, Finset.sum_add_distrib]
  map_smul' c w := by
    funext j
    simp [ComplexCoordinates.tracelessTuple, Finset.smul_sum, smul_smul]
private def coordChartInv (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (μ : σ ≃ Fin n) :
    (σ → ComplexMatrix2) →ₗ[ℂ] ComplexCoordinates (n * 3) where
  toFun A k := basisCoords b (A (μ.symm (finProdFinEquiv.symm k).1)) (finProdFinEquiv.symm k).2
  map_add' A B := by
    funext k
    simp
  map_smul' c A := by
    funext k
    simp
private theorem coordChart_mem (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (μ : σ ≃ Fin n) (w) :
    coordChart b μ w ∈ tracelessPi σ := fun _ =>
  sum_smul_mem_traceless b _
private theorem coordChartInv_coordChart (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (μ : σ ≃ Fin n) (w) : coordChartInv b μ (coordChart b μ w) = w := by
  funext k
  have h : coordChart b μ w (μ.symm (finProdFinEquiv.symm k).1) =
      ∑ c, w (finProdFinEquiv ((finProdFinEquiv.symm k).1, c)) • (b c : ComplexMatrix2) := by
    simp [coordChart, ComplexCoordinates.tracelessTuple]
  change basisCoords b (coordChart b μ w (μ.symm (finProdFinEquiv.symm k).1)) _ = _
  rw [h, basisCoords_sum]
  exact congrArg w (finProdFinEquiv.apply_symm_apply k)
private theorem coordChart_coordChartInv (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (μ : σ ≃ Fin n) {A : σ → ComplexMatrix2} (hA : A ∈ tracelessPi σ) :
    coordChart b μ (coordChartInv b μ A) = A := by
  funext i
  change ∑ c, coordChartInv b μ A (finProdFinEquiv (μ i, c)) • (b c : ComplexMatrix2) = A i
  have h : ∀ c, coordChartInv b μ A (finProdFinEquiv (μ i, c)) = basisCoords b (A i) c := by
    intro c
    change basisCoords b (A (μ.symm (finProdFinEquiv.symm (finProdFinEquiv (μ i, c))).1))
      (finProdFinEquiv.symm (finProdFinEquiv (μ i, c))).2 = _
    rw [Equiv.symm_apply_apply]
    simp
  simp only [h]
  exact sum_basisCoords b (A i) (hA i)
private def coordChartL [Fintype σ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (μ : σ ≃ Fin n) : ComplexCoordinates (n * 3) →L[ℂ] σ → ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap (coordChart b μ)
private def coordChartInvL [Fintype σ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (μ : σ ≃ Fin n) : (σ → ComplexMatrix2) →L[ℂ] ComplexCoordinates (n * 3) :=
  LinearMap.toContinuousLinearMap (coordChartInv b μ)
private theorem coordChart_continuous [Fintype σ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (μ : σ ≃ Fin n) : Continuous (coordChart b μ) := (coordChartL b μ).continuous
private theorem coordChartInv_continuous [Fintype σ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (μ : σ ≃ Fin n) : Continuous (coordChartInv b μ) := (coordChartInvL b μ).continuous
private theorem coordChart_differentiable [Fintype σ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (μ : σ ≃ Fin n) : Differentiable ℂ (coordChart b μ) := (coordChartL b μ).differentiable
private theorem coordChartInv_differentiable [Fintype σ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (μ : σ ≃ Fin n) : Differentiable ℂ (coordChartInv b μ) := (coordChartInvL b μ).differentiable
private theorem supNorm_lt_iff [Fintype σ] {s : ℝ} (hs : 0 < s) (A : σ → ComplexMatrix2) :
    supNorm A < s ↔ ∀ i, ComplexMatrix2.operatorNorm (A i) < s := by
  have hb : BddAbove (range fun i => ComplexMatrix2.operatorNorm (A i)) :=
    (Set.finite_range _).bddAbove
  constructor
  · intro h i
    exact (le_ciSup hb i).trans_lt h
  · intro h
    rcases isEmpty_or_nonempty σ with he | he
    · simpa [supNorm] using hs
    · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => ComplexMatrix2.operatorNorm (A i))
      change ⨆ i, ComplexMatrix2.operatorNorm (A i) < s
      rw [← hi]
      exact h i
abbrev _root_.YangMills.SharedProofs.p9363 := @supNorm_lt_iff
private theorem supNorm_sub_lt_iff [Fintype σ] {s : ℝ} (hs : 0 < s) (A B : σ → ComplexMatrix2) :
    supNorm (B - A) < s ↔ dist B A < s := by
  rw [supNorm_lt_iff hs, dist_pi_lt_iff hs]
  simp only [Pi.sub_apply, dist_eq_norm]
private theorem isSupOpen_iff_isRelativelyOpen [Fintype σ] {O : Set (σ → ComplexMatrix2)}
    (hO : O ⊆ tracelessPi σ) :
    IsSupOpen O ↔ ComplexMatrix2.IsRelativelyOpen (tracelessPi σ) O := by
  constructor
  · rintro ⟨-, h⟩
    choose! s hs hB using h
    refine ⟨⋃ A ∈ O, Metric.ball A (s A), isOpen_biUnion fun _ _ => Metric.isOpen_ball, ?_⟩
    ext B
    constructor
    · intro hBO
      exact ⟨mem_biUnion hBO (Metric.mem_ball_self (hs B hBO)), hO hBO⟩
    · rintro ⟨hBU, hBa⟩
      obtain ⟨A, hA, hBA⟩ := mem_iUnion₂.mp hBU
      exact hB A hA B hBa ((supNorm_sub_lt_iff (hs A hA) A B).2 hBA)
  · rintro ⟨V, hV, rfl⟩
    refine ⟨hO, fun A hA => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV A hA.1
    exact ⟨ε, hε, fun B hB hlt => ⟨hball ((supNorm_sub_lt_iff hε A B).1 hlt), hB⟩⟩
private theorem isRelativelyOpen_iff_isOpen_preimage [Fintype σ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (μ : σ ≃ Fin n) {O : Set (σ → ComplexMatrix2)} (hO : O ⊆ tracelessPi σ) :
    ComplexMatrix2.IsRelativelyOpen (tracelessPi σ) O ↔ IsOpen (coordChart b μ ⁻¹' O) := by
  constructor
  · rintro ⟨V, hV, rfl⟩
    have : coordChart b μ ⁻¹' (V ∩ tracelessPi σ) = coordChart b μ ⁻¹' V := by
      ext w
      exact ⟨fun h => h.1, fun h => ⟨h, coordChart_mem b μ w⟩⟩
    rw [this]
    exact hV.preimage (coordChart_continuous b μ)
  · intro h
    refine ⟨coordChartInv b μ ⁻¹' (coordChart b μ ⁻¹' O),
      h.preimage (coordChartInv_continuous b μ), ?_⟩
    ext A
    constructor
    · intro hA
      refine ⟨?_, hO hA⟩
      change coordChart b μ (coordChartInv b μ A) ∈ O
      rwa [coordChart_coordChartInv b μ (hO hA)]
    · rintro ⟨hA, hAa⟩
      have : coordChart b μ (coordChartInv b μ A) ∈ O := hA
      rwa [coordChart_coordChartInv b μ hAa] at this
private theorem isSupOpen_iff [Fintype σ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (μ : σ ≃ Fin n) {O : Set (σ → ComplexMatrix2)} (hO : O ⊆ tracelessPi σ) :
    IsSupOpen O ↔ IsOpen (coordChart b μ ⁻¹' O) :=
  (isSupOpen_iff_isRelativelyOpen hO).trans (isRelativelyOpen_iff_isOpen_preimage b μ hO)
private theorem differentiableOn_coordChart_change [Fintype σ] {n' l : ℕ}
    (b b' : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (μ : σ ≃ Fin n) (μ' : σ ≃ Fin n')
    {O : Set (σ → ComplexMatrix2)} {g : (σ → ComplexMatrix2) → ComplexCoordinates l}
    (h : DifferentiableOn ℂ (g ∘ coordChart b μ) (coordChart b μ ⁻¹' O)) :
    DifferentiableOn ℂ (g ∘ coordChart b' μ') (coordChart b' μ' ⁻¹' O) := by
  have hL : Differentiable ℂ fun w => coordChartInv b μ (coordChart b' μ' w) :=
    (coordChartInv_differentiable b μ).comp (coordChart_differentiable b' μ')
  have hback : ∀ w, coordChart b μ (coordChartInv b μ (coordChart b' μ' w)) = coordChart b' μ' w :=
    fun w => coordChart_coordChartInv b μ (coordChart_mem b' μ' w)
  have hc := h.comp hL.differentiableOn (s := coordChart b' μ' ⁻¹' O) (fun w hw => by
    change coordChart b μ (coordChartInv b μ (coordChart b' μ' w)) ∈ O
    rw [hback]
    exact hw)
  refine hc.congr fun w _ => ?_
  simp only [Function.comp_apply, hback]
private theorem isHolomorphicOnTraceless_iff (hH : HoloFacts) [Fintype σ]
    {E : Type} {l : ℕ} (b₀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E ≃ ComplexCoordinates l)
    (μ : σ ≃ Fin n) (O : Set (σ → ComplexMatrix2)) (f : (σ → ComplexMatrix2) → E) :
    IsHolomorphicOnTraceless b₀ e O f ↔
      IsSupOpen O ∧ DifferentiableOn ℂ (e ∘ f ∘ coordChart b μ) (coordChart b μ ⁻¹' O) := by
  constructor
  · rintro ⟨hO, h⟩
    refine ⟨hO, ?_⟩
    have h' := ((isHolomorphicIn_iff hH).1 (h (Fintype.equivFin σ))).2
    exact differentiableOn_coordChart_change (g := e ∘ f) b₀ b (Fintype.equivFin σ) μ h'
  · rintro ⟨hO, h⟩
    refine ⟨hO, fun ν => (isHolomorphicIn_iff hH).2 ⟨(isSupOpen_iff b₀ ν hO.1).1 hO, ?_⟩⟩
    exact differentiableOn_coordChart_change (g := e ∘ f) b b₀ μ ν h
private theorem mvPolynomial_eval_differentiable (N : ℕ) (P : MvPolynomial (Fin N) ℂ) :
    Differentiable ℂ fun z : ComplexCoordinates N => MvPolynomial.eval z P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have h : (fun z : ComplexCoordinates N => MvPolynomial.eval z (p + q)) =
        fun z => MvPolynomial.eval z p + MvPolynomial.eval z q := by
      funext z
      simp
    rw [h]
    exact hp.add hq
  | mul_X p i hp =>
    have h : (fun z : ComplexCoordinates N => MvPolynomial.eval z (p * MvPolynomial.X i)) =
        fun z => MvPolynomial.eval z p * z i := by
      funext z
      simp
    rw [h]
    exact hp.mul (differentiable_apply i)
abbrev _root_.YangMills.SharedProofs.p63145 := @mvPolynomial_eval_differentiable
private theorem affineHolomorphy_holds (hH : HoloFacts) : AffineHolomorphy := by
  intro N N' P _
  refine (isHolomorphicIn_iff hH).2 ⟨isOpen_univ, ?_⟩
  exact (differentiable_pi.2 fun j => mvPolynomial_eval_differentiable N (P j)).differentiableOn
private theorem tracelessTopologiesAgree_holds (σ : Type) [Fintype σ] :
    TracelessTopologiesAgree σ := fun _ hO =>
  ⟨isSupOpen_iff_isRelativelyOpen hO, fun b ν => isSupOpen_iff b ν hO⟩
private theorem tracelessHolomorphyBasisFree_holds (hH : HoloFacts) (σ : Type) [Fintype σ] :
    TracelessHolomorphyBasisFree σ := by
  intro E l e b b' O f
  rw [isHolomorphicOnTraceless_iff hH b b e (Fintype.equivFin σ),
    isHolomorphicOnTraceless_iff hH b' b e (Fintype.equivFin σ)]
private theorem differentiableOn_of_isHolomorphicVia (hH : HoloFacts) [Fintype σ] {E : Type}
    {l k M : ℕ} (e : E ≃ ComplexCoordinates l) (ν : σ ≃ Fin k) {O : Set (σ → ComplexMatrix2)}
    {h : (σ → ComplexMatrix2) → E}
    (hh : ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν) e O h)
    {U : Set (ComplexCoordinates M)} {G : ComplexCoordinates M → σ → ComplexMatrix2}
    (hG : DifferentiableOn ℂ G U) (hm : MapsTo G U O) : DifferentiableOn ℂ (e ∘ h ∘ G) U := by
  have hd := ((isHolomorphicIn_iff hH).1 hh).2
  have hc : DifferentiableOn ℂ (fun w => piCLE ν (G w)) U :=
    (piCLE ν).differentiable.comp_differentiableOn hG
  have := hd.comp hc (fun w hw => ⟨G w, hm hw, rfl⟩)
  refine this.congr fun w _ => ?_
  exact congrArg (fun u => e (h u)) ((matrixPiEquiv ν).symm_apply_apply (G w)).symm
private theorem isOpen_of_isHolomorphicVia (hH : HoloFacts) [Fintype σ] {E : Type} {l k : ℕ}
    (e : E ≃ ComplexCoordinates l) (ν : σ ≃ Fin k) {O : Set (σ → ComplexMatrix2)}
    {h : (σ → ComplexMatrix2) → E}
    (hh : ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν) e O h) : IsOpen O := by
  have ho := ((isHolomorphicIn_iff hH).1 hh).1
  have hp : O = piCLE ν ⁻¹' (matrixPiEquiv ν '' O) :=
    ((matrixPiEquiv ν).injective.preimage_image O).symm
  rw [hp]
  exact ho.preimage (piCLE ν).continuous
private theorem tracelessRestrictionHolomorphy_holds (hH : HoloFacts) (σ : Type) [Fintype σ] :
    TracelessRestrictionHolomorphy σ := by
  intro E l k e ν O h hh b
  have ho := isOpen_of_isHolomorphicVia hH e ν hh
  have hT : IsSupOpen (O ∩ tracelessPi σ) :=
    (isSupOpen_iff_isRelativelyOpen inter_subset_right).2 ⟨O, ho, rfl⟩
  refine (isHolomorphicOnTraceless_iff hH b b e (Fintype.equivFin σ) _ h).2 ⟨hT, ?_⟩
  exact differentiableOn_of_isHolomorphicVia hH e ν hh
    (coordChart_differentiable b _).differentiableOn fun w hw => hw.1
private theorem tracelessCoordsHolomorphy_holds (hH : HoloFacts) (σ τ : Type) [Fintype σ]
    [Fintype τ] : TracelessCoordsHolomorphy σ τ := by
  intro k ν b O f hf hm b' ν'
  refine ⟨fun A => coordChartInv b' ν' (f A), ?_, fun A hA => ?_⟩
  · obtain ⟨hO, hd⟩ := (isHolomorphicOnTraceless_iff hH b b (matrixPiEquiv ν)
      (Fintype.equivFin σ) O f).1 hf
    refine (isHolomorphicOnTraceless_iff hH b b (Equiv.refl _) (Fintype.equivFin σ) O _).2
      ⟨hO, ?_⟩
    have h1 : DifferentiableOn ℂ (fun w => f (coordChart b (Fintype.equivFin σ) w))
        (coordChart b (Fintype.equivFin σ) ⁻¹' O) :=
      (piCLE ν).comp_differentiableOn_iff.1 hd
    exact (coordChartInv_differentiable b' ν').comp_differentiableOn h1
  · exact coordChart_coordChartInv b' ν' (hm hA)
private theorem matExp_differentiable (hH : HoloFacts) : Differentiable ℂ ComplexMatrix2.matExp := by apply _root_.YangMills.SharedProofs.p11731 <;> assumption
private theorem logSeries_differentiableOn (hH : HoloFacts) :
    DifferentiableOn ℂ ComplexMatrix2.logSeries ComplexMatrix2.logBall := by apply _root_.YangMills.SharedProofs.p36036 <;> assumption
private theorem mem_groupLieProduct_iff {x : ι ⊕ κ → ComplexMatrix2} :
    x ∈ GroupLieProduct ι κ ↔
      (∀ i, x (.inl i) ∈ ComplexMatrix2.unitDeterminant) ∧
        ∀ k, x (.inr k) ∈ ComplexMatrix2.traceless := by
  constructor
  · exact fun h => ⟨fun i => h (.inl i), fun k => h (.inr k)⟩
  · rintro ⟨h₁, h₂⟩ (i | k)
    · exact h₁ i
    · exact h₂ k
private theorem expChartAt_differentiable (hH : HoloFacts) [Fintype ι] [Fintype κ]
    (p : ι ⊕ κ → ComplexMatrix2) : Differentiable ℂ (expChartAt p) := by
  refine differentiable_pi.2 fun t => ?_
  rcases t with i | k
  · change Differentiable ℂ fun A : ι ⊕ κ → ComplexMatrix2 =>
      ComplexMatrix2.matExp (A (.inl i)) * p (.inl i)
    exact ((matExp_differentiable hH).comp (differentiable_apply _)).mul_const _
  · change Differentiable ℂ fun A : ι ⊕ κ → ComplexMatrix2 => p (.inr k) + A (.inr k)
    exact (differentiable_apply _).const_add _
private theorem matExp_mem_unitDeterminant (hE : ComplexMatrix2.ExpLogEstimates) {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.matExp A ∈ ComplexMatrix2.unitDeterminant := by
  have h := hE.2.2.2.2.2.1 A
  have ht : ComplexMatrix2.fullTrace A = 0 := hA
  change (ComplexMatrix2.matExp A).det = 1
  rw [h, ht, Complex.exp_zero]
abbrev _root_.YangMills.DeltaSharedProofs.p501082 := @matExp_mem_unitDeterminant
abbrev _root_.YangMills.SharedProofs.p27134 := @matExp_mem_unitDeterminant
private theorem mul_mem_unitDeterminant {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.unitDeterminant) (hY : Y ∈ ComplexMatrix2.unitDeterminant) :
    X * Y ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p36859 <;> assumption
private theorem inv_mem_unitDeterminant {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.unitDeterminant) : X⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
private theorem mul_inv_of_unitDeterminant {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.unitDeterminant) : X * X⁻¹ = 1 := by apply _root_.YangMills.DeltaSharedProofs.p2618 <;> assumption
private theorem inv_mul_of_unitDeterminant {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.unitDeterminant) : X⁻¹ * X = 1 := by apply _root_.YangMills.DeltaSharedProofs.p40097 <;> assumption
private theorem matExp_logSeries (hE : ComplexMatrix2.ExpLogEstimates) {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.logBall) :
    ComplexMatrix2.matExp (ComplexMatrix2.logSeries Y) = Y := by
  have h := (hE.2.2.2.1 (Y - 1) hY).2.2.2.2
  simpa using h
private theorem logSeries_one (hE : ComplexMatrix2.ExpLogEstimates) :
    ComplexMatrix2.logSeries 1 = 0 := by
  have h := (hE.2.2.2.2.1 0 (by simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  simpa [ComplexMatrix2.matExp, NormedSpace.exp_zero] using h
private theorem expChartAt_mem (hE : ComplexMatrix2.ExpLogEstimates) {p A : ι ⊕ κ → ComplexMatrix2}
    (hp : p ∈ GroupLieProduct ι κ) (hA : A ∈ tracelessPi (ι ⊕ κ)) :
    expChartAt p A ∈ GroupLieProduct ι κ := by
  have hp' := mem_groupLieProduct_iff.1 hp
  refine mem_groupLieProduct_iff.2 ⟨fun i => ?_, fun k => ?_⟩
  · exact mul_mem_unitDeterminant (matExp_mem_unitDeterminant hE (hA (.inl i))) (hp'.1 i)
  · exact Submodule.add_mem _ (hp'.2 k) (hA (.inr k))
private theorem expChartAt_zero (p : ι ⊕ κ → ComplexMatrix2) : expChartAt p 0 = p := by apply _root_.YangMills.SharedProofs.p39871 <;> assumption
private theorem zero_mem_tracelessPi : (0 : σ → ComplexMatrix2) ∈ tracelessPi σ := fun _ =>
  Submodule.zero_mem _
private theorem isSupOpen_tracelessPi [Fintype σ] : IsSupOpen (tracelessPi σ) :=
  ⟨subset_rfl, fun _ _ => ⟨1, one_pos, fun _ hB _ => hB⟩⟩
private theorem logSeries_continuousOn (hH : HoloFacts) :
    ContinuousOn ComplexMatrix2.logSeries ComplexMatrix2.logBall :=
  (logSeries_differentiableOn hH).continuousOn
private theorem expChartLocalHomeomorph_holds (hH : HoloFacts) (hE : ComplexMatrix2.ExpLogEstimates)
    (ι κ : Type) [Fintype ι] [Fintype κ] : ExpChartLocalHomeomorph ι κ := by
  intro p hp
  have hp' := mem_groupLieProduct_iff.1 hp
  have hD : Differentiable ℂ (expChartAt p) := expChartAt_differentiable hH p
  refine ⟨fun b k ν => ?_, hD.continuous.continuousOn, fun A hA => expChartAt_mem hE hp hA,
    expChartAt_zero p, fun s hs hes => ?_⟩
  · refine (isHolomorphicOnTraceless_iff hH b b _ (Fintype.equivFin _) _ _).2
      ⟨isSupOpen_tracelessPi, ?_⟩
    exact (piCLE ν).differentiable.comp_differentiableOn
      (hD.comp (coordChart_differentiable b _)).differentiableOn
  · have hs2 : s < Real.log 2 := (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith)
    have hleft : LeftInvOn (logChart p) (expChartAt p) (supBall (ι ⊕ κ) s) := by
      intro A hA
      have hn := (supNorm_lt_iff hs A).1 hA.2
      funext t
      rcases t with i | k
      · change ComplexMatrix2.logSeries
          (ComplexMatrix2.matExp (A (.inl i)) * p (.inl i) * (p (.inl i))⁻¹) = A (.inl i)
        rw [mul_assoc, mul_inv_of_unitDeterminant (hp'.1 i), mul_one]
        exact (hE.2.2.2.2.1 _ ((hn _).trans hs2)).2
      · change p (.inr k) + A (.inr k) - p (.inr k) = A (.inr k)
        simp
    set S : Set ComplexMatrix2 := {Y | ComplexMatrix2.operatorNorm (Y - 1) < 9 / 10 ∧
      ComplexMatrix2.operatorNorm (ComplexMatrix2.logSeries Y) < s} with hSdef
    have hB : IsOpen {Y : ComplexMatrix2 | ComplexMatrix2.operatorNorm (Y - 1) < 9 / 10} :=
      isOpen_lt (by fun_prop) continuous_const
    have hS : IsOpen S := by
      have hc : ContinuousOn ComplexMatrix2.logSeries
          {Y : ComplexMatrix2 | ComplexMatrix2.operatorNorm (Y - 1) < 9 / 10} :=
        (logSeries_continuousOn hH).mono fun Y hY => by
          have : ComplexMatrix2.operatorNorm (Y - 1) < 9 / 10 := hY
          change ComplexMatrix2.operatorNorm (Y - 1) < 1
          linarith
      exact hc.isOpen_inter_preimage hB (isOpen_lt continuous_norm continuous_const)
    set V : Set (ι ⊕ κ → ComplexMatrix2) :=
      (⋂ i, (fun q : ι ⊕ κ → ComplexMatrix2 => q (.inl i) * (p (.inl i))⁻¹) ⁻¹' S) ∩
        ⋂ k, {q | ComplexMatrix2.operatorNorm (q (.inr k) - p (.inr k)) < s} with hVdef
    have hV : IsOpen V := by
      refine (isOpen_iInter_of_finite fun i => hS.preimage (by fun_prop)).inter
        (isOpen_iInter_of_finite fun k => isOpen_lt (by fun_prop) continuous_const)
    have himage : expChartAt p '' supBall (ι ⊕ κ) s = V ∩ GroupLieProduct ι κ := by
      ext q
      constructor
      · rintro ⟨A, hA, rfl⟩
        have hn := (supNorm_lt_iff hs A).1 hA.2
        refine ⟨⟨mem_iInter.2 fun i => ?_, mem_iInter.2 fun k => ?_⟩,
          expChartAt_mem hE hp hA.1⟩
        · change ComplexMatrix2.matExp (A (.inl i)) * p (.inl i) * (p (.inl i))⁻¹ ∈ S
          rw [mul_assoc, mul_inv_of_unitDeterminant (hp'.1 i), mul_one]
          have h1 := (hE.1 (A (.inl i))).2
          have h2 : Real.exp (ComplexMatrix2.operatorNorm (A (.inl i))) < Real.exp s :=
            Real.exp_lt_exp.2 (hn _)
          refine ⟨by linarith, ?_⟩
          rw [(hE.2.2.2.2.1 _ ((hn _).trans hs2)).2]
          exact hn _
        · change ComplexMatrix2.operatorNorm (p (.inr k) + A (.inr k) - p (.inr k)) < s
          simpa using hn (.inr k)
      · rintro ⟨⟨hq1, hq2⟩, hqP⟩
        have hq' := mem_groupLieProduct_iff.1 hqP
        have hq1' := fun i => mem_iInter.1 hq1 i
        have hq2' := fun k => mem_iInter.1 hq2 k
        refine ⟨logChart p q, ⟨?_, ?_⟩, ?_⟩
        · rintro (i | k)
          · have hdet : (q (.inl i) * (p (.inl i))⁻¹).det = 1 :=
              mul_mem_unitDeterminant (hq'.1 i) (inv_mem_unitDeterminant (hp'.1 i))
            exact (hE.2.2.2.2.2.2.1 _ hdet (hq1' i).1.le).2
          · exact Submodule.sub_mem _ (hq'.2 k) (hp'.2 k)
        · refine (supNorm_lt_iff hs _).2 ?_
          rintro (i | k)
          · exact (hq1' i).2
          · exact hq2' k
        · funext t
          rcases t with i | k
          · change ComplexMatrix2.matExp (ComplexMatrix2.logSeries (q (.inl i) * (p (.inl i))⁻¹)) *
              p (.inl i) = q (.inl i)
            have hdom : q (.inl i) * (p (.inl i))⁻¹ ∈ ComplexMatrix2.logBall := by
              have := (hq1' i).1
              change ComplexMatrix2.operatorNorm _ < 1
              linarith
            rw [matExp_logSeries hE hdom, mul_assoc, inv_mul_of_unitDeterminant (hp'.1 i), mul_one]
          · change p (.inr k) + (q (.inr k) - p (.inr k)) = q (.inr k)
            simp
    refine ⟨hleft.injOn, ⟨V, hV, himage⟩, ⟨hleft, ?_⟩, ?_⟩
    · rintro _ ⟨A, hA, rfl⟩
      rw [hleft hA]
    · rw [himage]
      refine continuousOn_pi.2 fun t => ?_
      rcases t with i | k
      · change ContinuousOn (fun q : ι ⊕ κ → ComplexMatrix2 =>
          ComplexMatrix2.logSeries (q (.inl i) * (p (.inl i))⁻¹)) _
        refine (logSeries_continuousOn hH).comp (by fun_prop) fun q hq => ?_
        have := (mem_iInter.1 hq.1.1 i).1
        change ComplexMatrix2.operatorNorm _ < 1
        linarith
      · change ContinuousOn (fun q : ι ⊕ κ → ComplexMatrix2 => q (.inr k) - p (.inr k)) _
        fun_prop
private theorem differentiableOn_matrixEquiv_comp_iff {M : ℕ} {U : Set (ComplexCoordinates M)}
    {F : ComplexCoordinates M → ComplexMatrix2} :
    DifferentiableOn ℂ (ComplexCoordinates.matrixEquiv ∘ F) U ↔ DifferentiableOn ℂ F U :=
  matrixCLE.comp_differentiableOn_iff
private theorem continuousOn_matrixEquiv_comp_iff {X : Type} [TopologicalSpace X] {U : Set X}
    {F : X → ComplexMatrix2} :
    ContinuousOn (ComplexCoordinates.matrixEquiv ∘ F) U ↔ ContinuousOn F U :=
  matrixCLE.toHomeomorph.comp_continuousOn_iff F U
private theorem isOpen_logBall : IsOpen ComplexMatrix2.logBall :=
  isOpen_lt (by fun_prop) continuous_const
private theorem one_mem_logBall : (1 : ComplexMatrix2) ∈ ComplexMatrix2.logBall := by
  simp [ComplexMatrix2.logBall]
private theorem unimodularValuedHolomorphy_holds (hH : HoloFacts)
    (hE : ComplexMatrix2.ExpLogEstimates) (ι κ : Type) [Fintype ι] [Fintype κ] :
    UnimodularValuedHolomorphy ι κ := by
  intro b W Φ hW hm
  constructor
  · rintro ⟨-, -, hc, hloc⟩
    refine ⟨hW, continuousOn_matrixEquiv_comp_iff.2 hc, fun p hp => ?_⟩
    obtain ⟨O, h0, hO, hh⟩ := hloc p hp
    obtain ⟨hOt, hd⟩ :=
      (isHolomorphicOnTraceless_iff hH b b _ (Fintype.equivFin (ι ⊕ κ)) _ _).1 hh
    refine ⟨O, h0, fun A hA => (hO A hA).1, ?_⟩
    refine (isHolomorphicOnTraceless_iff hH b b _ (Fintype.equivFin (ι ⊕ κ)) _ _).2 ⟨hOt, ?_⟩
    have hd' := differentiableOn_matrixEquiv_comp_iff.1 hd
    have h2 := ((matExp_differentiable hH).comp_differentiableOn hd').mul_const (Φ p)
    refine differentiableOn_matrixEquiv_comp_iff.2 (h2.congr fun w hw => ?_)
    have hmem := (hO _ hw).2
    simp only [Function.comp_apply]
    rw [matExp_logSeries hE hmem, mul_assoc, inv_mul_of_unitDeterminant (hm hp), mul_one]
  · rintro ⟨-, hc, hloc⟩
    refine ⟨hW, hm, continuousOn_matrixEquiv_comp_iff.1 hc, fun p hp => ?_⟩
    obtain ⟨O, h0, hO, hh⟩ := hloc p hp
    set μ := Fintype.equivFin (ι ⊕ κ)
    obtain ⟨hOt, hd⟩ := (isHolomorphicOnTraceless_iff hH b b _ μ _ _).1 hh
    have hd' := differentiableOn_matrixEquiv_comp_iff.1 hd
    have hq := hd'.mul_const (Φ p)⁻¹
    set O' : Set (ι ⊕ κ → ComplexMatrix2) :=
      O ∩ {A | Φ (expChartAt p A) * (Φ p)⁻¹ ∈ ComplexMatrix2.logBall} with hO'
    have hsub : O' ⊆ tracelessPi (ι ⊕ κ) := inter_subset_left.trans hOt.1
    have hopen : IsOpen (coordChart b μ ⁻¹' O') :=
      hq.continuousOn.isOpen_inter_preimage ((isSupOpen_iff b μ hOt.1).1 hOt) isOpen_logBall
    refine ⟨O', ⟨h0, ?_⟩, fun A hA => ⟨hO A hA.1, hA.2⟩, ?_⟩
    · change Φ (expChartAt p 0) * (Φ p)⁻¹ ∈ ComplexMatrix2.logBall
      rw [expChartAt_zero, mul_inv_of_unitDeterminant (hm hp)]
      exact one_mem_logBall
    · refine (isHolomorphicOnTraceless_iff hH b b _ μ _ _).2
        ⟨(isSupOpen_iff b μ hsub).2 hopen, differentiableOn_matrixEquiv_comp_iff.2 ?_⟩
      exact (logSeries_differentiableOn hH).comp (hq.mono (preimage_mono inter_subset_left))
        fun w hw => hw.2
private theorem productRestrictionHolomorphy_holds (hH : HoloFacts)
    (hE : ComplexMatrix2.ExpLogEstimates) (ι κ : Type) [Fintype ι]
    [Fintype κ] : ProductRestrictionHolomorphy ι κ := by
  intro E l k e ν O Φ hh
  have ho := isOpen_of_isHolomorphicVia hH e ν hh
  have hoi : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) (O ∩ GroupLieProduct ι κ) :=
    ⟨O, ho, rfl⟩
  refine ⟨hoi, fun b => ⟨hoi, ?_, fun p hp => ?_⟩⟩
  · have hd := ((isHolomorphicIn_iff hH).1 hh).2.continuousOn
    have h2 := hd.comp (piCLE ν).continuous.continuousOn
      (s := O ∩ GroupLieProduct ι κ) (fun x hx => ⟨x, hx.1, rfl⟩)
    refine h2.congr fun x _ => ?_
    exact congrArg (fun u => e (Φ u)) ((matrixPiEquiv ν).symm_apply_apply x).symm
  · have hD : Differentiable ℂ (expChartAt p) := expChartAt_differentiable hH p
    set O' : Set (ι ⊕ κ → ComplexMatrix2) := expChartAt p ⁻¹' O ∩ tracelessPi (ι ⊕ κ) with hO'
    have hoT : IsSupOpen O' := (isSupOpen_iff_isRelativelyOpen inter_subset_right).2
      ⟨expChartAt p ⁻¹' O, ho.preimage hD.continuous, rfl⟩
    refine ⟨O', ⟨?_, zero_mem_tracelessPi⟩, fun A hA => ⟨hA.1, expChartAt_mem hE hp.2 hA.2⟩, ?_⟩
    · change expChartAt p 0 ∈ O
      rw [expChartAt_zero]
      exact hp.1
    · refine (isHolomorphicOnTraceless_iff hH b b _ (Fintype.equivFin (ι ⊕ κ)) _ _).2 ⟨hoT, ?_⟩
      exact differentiableOn_of_isHolomorphicVia hH e ν hh
        (G := expChartAt p ∘ coordChart b (Fintype.equivFin (ι ⊕ κ)))
        (hD.comp (coordChart_differentiable b _)).differentiableOn fun w hw => hw.1
private theorem logChart_self (hE : ComplexMatrix2.ExpLogEstimates) {p : ι ⊕ κ → ComplexMatrix2}
    (hp : p ∈ GroupLieProduct ι κ) : logChart p p = 0 := by
  have hp' := mem_groupLieProduct_iff.1 hp
  funext t
  rcases t with i | k
  · change ComplexMatrix2.logSeries (p (.inl i) * (p (.inl i))⁻¹) = 0
    rw [mul_inv_of_unitDeterminant (hp'.1 i), logSeries_one hE]
  · change p (.inr k) - p (.inr k) = 0
    simp
private theorem comp_local (hH : HoloFacts) (hE : ComplexMatrix2.ExpLogEstimates) [Fintype ι]
    [Fintype κ] [Fintype ι'] [Fintype κ'] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {W O₁ : Set (ι ⊕ κ → ComplexMatrix2)}
    (hO₁ : IsOpen O₁) (hW₁ : W = O₁ ∩ GroupLieProduct ι κ)
    {Ψ : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ κ' → ComplexMatrix2}
    (hG : ∀ i, IsHolomorphicToUnimodular b W fun p => Ψ p (.inl i))
    (hA : ∀ k, IsHolomorphicToTraceless b W fun p => Ψ p (.inr k))
    (hcont : ContinuousOn Ψ W) (hmaps : MapsTo Ψ W (GroupLieProduct ι' κ'))
    {E : Type} {l : ℕ} (e : E ≃ ComplexCoordinates l) {W' : Set (ι' ⊕ κ' → ComplexMatrix2)}
    {Φ : (ι' ⊕ κ' → ComplexMatrix2) → E} (hΦ : IsHolomorphicToCoords b e W' Φ)
    {q₀ : ι ⊕ κ → ComplexMatrix2} (hq₀ : q₀ ∈ W ∩ Ψ ⁻¹' W') :
    ∃ O : Set (ι ⊕ κ → ComplexMatrix2), 0 ∈ O ∧
      (∀ A ∈ O, expChartAt q₀ A ∈ W ∩ Ψ ⁻¹' W') ∧
      IsHolomorphicOnTraceless b e O ((Φ ∘ Ψ) ∘ expChartAt q₀) := by
  classical
  set μ := Fintype.equivFin (ι ⊕ κ) with hμ
  set μ' := Fintype.equivFin (ι' ⊕ κ') with hμ'
  set T := coordChart b μ with hT
  set T' := coordChart b μ' with hT'
  set p₀ := Ψ q₀ with hp₀
  have hqW : q₀ ∈ W := hq₀.1
  have hqP : q₀ ∈ GroupLieProduct ι κ := by
    rw [hW₁] at hqW
    exact hqW.2
  have hpP : p₀ ∈ GroupLieProduct ι' κ' := hmaps hqW
  have hpP' := mem_groupLieProduct_iff.1 hpP
  have hcD : Differentiable ℂ (expChartAt q₀) := expChartAt_differentiable hH q₀
  set Λ : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ κ' → ComplexMatrix2 :=
    fun A => logChart p₀ (Ψ (expChartAt q₀ A)) with hΛ
  have hpiece : ∀ t : ι' ⊕ κ', ∃ O : Set (ι ⊕ κ → ComplexMatrix2), IsSupOpen O ∧
      (0 : ι ⊕ κ → ComplexMatrix2) ∈ O ∧
      DifferentiableOn ℂ (fun w => Λ (T w) t) (T ⁻¹' O) := by
    rintro (i | k)
    · obtain ⟨O, h0, -, hh⟩ := (hG i).2.2.2 q₀ hqW
      obtain ⟨hOt, hd⟩ := (isHolomorphicOnTraceless_iff hH b b _ μ _ _).1 hh
      exact ⟨O, hOt, h0, differentiableOn_matrixEquiv_comp_iff.1 hd⟩
    · obtain ⟨O, h0, -, hh⟩ := (hA k).2.2.2 q₀ hqW
      obtain ⟨hOt, hd⟩ := (isHolomorphicOnTraceless_iff hH b b _ μ _ _).1 hh
      have hd' := differentiableOn_matrixEquiv_comp_iff.1 hd
      exact ⟨O, hOt, h0, hd'.sub_const (p₀ (.inr k))⟩
  choose Ot hOt h0 hd using hpiece
  have hTzero : T 0 = 0 := map_zero T
  set U₀ : Set (ComplexCoordinates (Fintype.card (ι ⊕ κ) * 3)) :=
    (fun w => expChartAt q₀ (T w)) ⁻¹' O₁ with hU₀
  have hU₀o : IsOpen U₀ :=
    hO₁.preimage (hcD.continuous.comp (coordChart_continuous b μ))
  have hU₀W : ∀ w ∈ U₀, expChartAt q₀ (T w) ∈ W := fun w hw => by
    rw [hW₁]
    exact ⟨hw, expChartAt_mem hE hqP (coordChart_mem b μ w)⟩
  set U₁ := U₀ ∩ ⋂ t, T ⁻¹' Ot t with hU₁
  have hU₁o : IsOpen U₁ := hU₀o.inter (isOpen_iInter_of_finite fun t =>
    (isSupOpen_iff b μ (hOt t).1).1 (hOt t))
  have hU₁W : ∀ w ∈ U₁, expChartAt q₀ (T w) ∈ W := fun w hw => hU₀W w hw.1
  have hΛd : DifferentiableOn ℂ (fun w => Λ (T w)) U₁ :=
    differentiableOn_pi.2 fun t => (hd t).mono fun w hw => mem_iInter.1 hw.2 t
  have hGc : ContinuousOn (fun w => Ψ (expChartAt q₀ (T w))) U₁ :=
    hcont.comp (hcD.continuous.comp (coordChart_continuous b μ)).continuousOn hU₁W
  set F : ι' → ComplexCoordinates (Fintype.card (ι ⊕ κ) * 3) → ComplexMatrix2 :=
    fun i w => Ψ (expChartAt q₀ (T w)) (.inl i) * (p₀ (.inl i))⁻¹ with hF
  have hFc : ∀ i, ContinuousOn (F i) U₁ := fun i =>
    ((continuous_apply (Sum.inl i : ι' ⊕ κ')).comp_continuousOn hGc).mul continuousOn_const
  have hB : IsOpen {Y : ComplexMatrix2 | ComplexMatrix2.operatorNorm (Y - 1) < 9 / 10} :=
    isOpen_lt (by fun_prop) continuous_const
  set U₂ := U₁ ∩ ⋂ i, (U₁ ∩ F i ⁻¹'
    {Y : ComplexMatrix2 | ComplexMatrix2.operatorNorm (Y - 1) < 9 / 10}) with hU₂
  have hU₂o : IsOpen U₂ := hU₁o.inter (isOpen_iInter_of_finite fun i =>
    (hFc i).isOpen_inter_preimage hU₁o hB)
  have hFnear : ∀ w ∈ U₂, ∀ i, ComplexMatrix2.operatorNorm (F i w - 1) < 9 / 10 := fun w hw i =>
    (mem_iInter.1 hw.2 i).2
  have hFdet : ∀ w ∈ U₂, ∀ i, (F i w).det = 1 := fun w hw i =>
    mul_mem_unitDeterminant ((hG i).2.1 (hU₁W w hw.1)) (inv_mem_unitDeterminant (hpP'.1 i))
  have hΛmem : ∀ w ∈ U₂, Λ (T w) ∈ tracelessPi (ι' ⊕ κ') := by
    intro w hw
    rintro (i | k)
    · exact (hE.2.2.2.2.2.2.1 _ (hFdet w hw i) (hFnear w hw i).le).2
    · exact Submodule.sub_mem _ ((hA k).1 (hU₁W w hw.1)) (hpP'.2 k)
  have hkey : ∀ w ∈ U₂, expChartAt p₀ (Λ (T w)) = Ψ (expChartAt q₀ (T w)) := by
    intro w hw
    funext t
    rcases t with i | k
    · change ComplexMatrix2.matExp (ComplexMatrix2.logSeries (F i w)) * p₀ (.inl i) = _
      have hdom : F i w ∈ ComplexMatrix2.logBall := by
        have := hFnear w hw i
        change ComplexMatrix2.operatorNorm _ < 1
        linarith
      rw [matExp_logSeries hE hdom]
      change Ψ _ (.inl i) * (p₀ (.inl i))⁻¹ * p₀ (.inl i) = _
      rw [mul_assoc, inv_mul_of_unitDeterminant (hpP'.1 i), mul_one]
    · change p₀ (.inr k) + (Ψ (expChartAt q₀ (T w)) (.inr k) - p₀ (.inr k)) = _
      simp
  obtain ⟨OΦ, h0Φ, hOΦ, hhΦ⟩ := hΦ.2.2 p₀ hq₀.2
  obtain ⟨hOΦt, hdΦ⟩ := (isHolomorphicOnTraceless_iff hH b b _ μ' _ _).1 hhΦ
  set L := fun w => coordChartInv b μ' (Λ (T w)) with hL
  have hLd : DifferentiableOn ℂ L U₁ :=
    (coordChartInv_differentiable b μ').comp_differentiableOn hΛd
  have hTL : ∀ w ∈ U₂, T' (L w) = Λ (T w) := fun w hw =>
    coordChart_coordChartInv b μ' (hΛmem w hw)
  set U₃ := U₂ ∩ L ⁻¹' (T' ⁻¹' OΦ) with hU₃
  have hU₃o : IsOpen U₃ :=
    (hLd.continuousOn.mono fun w (hw : w ∈ U₂) => hw.1).isOpen_inter_preimage
      hU₂o ((isSupOpen_iff b μ' hOΦt.1).1 hOΦt)
  set O : Set (ι ⊕ κ → ComplexMatrix2) := tracelessPi (ι ⊕ κ) ∩ coordChartInv b μ ⁻¹' U₃ with hOdef
  have hpre : T ⁻¹' O = U₃ := by
    ext w
    constructor
    · intro h
      have := h.2
      rwa [mem_preimage, hT, coordChartInv_coordChart] at this
    · intro h
      refine ⟨coordChart_mem b μ w, ?_⟩
      rwa [mem_preimage, hT, coordChartInv_coordChart]
  have hOt' : IsSupOpen O := (isSupOpen_iff b μ inter_subset_left).2 (by rwa [hpre])
  have h0U₁ : (0 : ComplexCoordinates (Fintype.card (ι ⊕ κ) * 3)) ∈ U₁ := by
    refine ⟨?_, mem_iInter.2 fun t => ?_⟩
    · change expChartAt q₀ (T 0) ∈ O₁
      rw [hTzero, expChartAt_zero]
      rw [hW₁] at hqW
      exact hqW.1
    · change T 0 ∈ Ot t
      rw [hTzero]
      exact h0 t
  have h0U₂ : (0 : ComplexCoordinates (Fintype.card (ι ⊕ κ) * 3)) ∈ U₂ := by
    refine ⟨h0U₁, mem_iInter.2 fun i => ⟨h0U₁, ?_⟩⟩
    change ComplexMatrix2.operatorNorm (F i 0 - 1) < 9 / 10
    have : F i 0 = 1 := by
      change Ψ (expChartAt q₀ (T 0)) (.inl i) * (p₀ (.inl i))⁻¹ = 1
      rw [hTzero, expChartAt_zero]
      exact mul_inv_of_unitDeterminant (hpP'.1 i)
    rw [this]
    simp only [sub_self, ComplexMatrix2.operatorNorm, norm_zero]
    norm_num
  have hΛ0 : Λ (T 0) = 0 := by
    change logChart p₀ (Ψ (expChartAt q₀ (T 0))) = 0
    rw [hTzero, expChartAt_zero]
    exact logChart_self hE hpP
  have h0U₃ : (0 : ComplexCoordinates (Fintype.card (ι ⊕ κ) * 3)) ∈ U₃ := by
    refine ⟨h0U₂, ?_⟩
    change T' (L 0) ∈ OΦ
    rw [hTL 0 h0U₂, hΛ0]
    exact h0Φ
  refine ⟨O, ⟨zero_mem_tracelessPi, ?_⟩, fun A hA => ?_, ?_⟩
  · change coordChartInv b μ 0 ∈ U₃
    rw [map_zero]
    exact h0U₃
  · have hw : coordChartInv b μ A ∈ U₃ := hA.2
    have hTA : T (coordChartInv b μ A) = A := coordChart_coordChartInv b μ hA.1
    have h1 := hU₁W _ hw.1.1
    rw [hTA] at h1
    refine ⟨h1, ?_⟩
    have h2 := hOΦ _ hw.2
    have h3 := hTL _ hw.1
    have h4 := hkey _ hw.1
    rw [h3, h4, hTA] at h2
    exact h2
  · refine (isHolomorphicOnTraceless_iff hH b b _ μ _ _).2 ⟨hOt', ?_⟩
    rw [hpre]
    have hc := hdΦ.comp (hLd.mono fun w hw => hw.1.1) (s := U₃) fun w hw => hw.2
    refine hc.congr fun w hw => ?_
    simp only [Function.comp_apply]
    rw [hTL w hw.1, hkey w hw.1]
private theorem compHolomorphy_holds (hH : HoloFacts) (hE : ComplexMatrix2.ExpLogEstimates)
    (ι κ ι' κ' : Type) [Fintype ι] [Fintype κ]
    [Fintype ι'] [Fintype κ'] : CompHolomorphy ι κ ι' κ' := by
  intro b W Ψ hW hΨ E l e W' Φ hΦ
  obtain ⟨-, hG, hA⟩ := hΨ
  have hmaps : MapsTo Ψ W (GroupLieProduct ι' κ') := fun q hq =>
    mem_groupLieProduct_iff.2 ⟨fun i => (hG i).2.1 hq, fun k => (hA k).1 hq⟩
  have hcont : ContinuousOn Ψ W := by
    refine continuousOn_pi.2 ?_
    rintro (i | k)
    · exact (hG i).2.2.1
    · exact continuousOn_matrixEquiv_comp_iff.1 (hA k).2.2.1
  obtain ⟨O₂, hO₂, hW₂⟩ := hΦ.1
  obtain ⟨O₁, hO₁, hW₁⟩ := hW
  have hopen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) (W ∩ Ψ ⁻¹' W') := by
    obtain ⟨u, hu, huW⟩ := continuousOn_iff'.1 hcont O₂ hO₂
    refine ⟨u ∩ O₁, hu.inter hO₁, ?_⟩
    have h1 : W ∩ Ψ ⁻¹' W' = Ψ ⁻¹' O₂ ∩ W := by
      ext q
      constructor
      · rintro ⟨hq, hq'⟩
        rw [mem_preimage, hW₂] at hq'
        exact ⟨hq'.1, hq⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h2, ?_⟩
        rw [mem_preimage, hW₂]
        exact ⟨h1, hmaps h2⟩
    rw [h1, huW, hW₁, inter_assoc]
  refine ⟨hcont, hopen, hopen, ?_, fun q₀ hq₀ => ?_⟩
  · exact hΦ.2.1.comp (hcont.mono inter_subset_left) fun q hq => hq.2
  · obtain ⟨O, h0, hO, hh⟩ := comp_local hH hE b hO₁ hW₁ hG hA hcont hmaps e hΦ hq₀
    exact ⟨O, h0, hO, hh⟩
private theorem tracelessPowerHolomorphy_holds (hH : HoloFacts) (ι κ : Type) [Fintype ι]
    [Fintype κ] [IsEmpty ι] : TracelessPowerHolomorphy ι κ := by
  intro E l e b W Φ hW
  have heq : GroupLieProduct ι κ = tracelessPi (ι ⊕ κ) := by
    ext x
    constructor
    · intro h
      rintro (i | k)
      · exact isEmptyElim i
      · exact h (.inr k)
    · intro h
      rintro (i | k)
      · exact isEmptyElim i
      · exact h (.inr k)
  have hadd : ∀ p A : ι ⊕ κ → ComplexMatrix2, expChartAt p A = p + A := by
    intro p A
    funext t
    rcases t with i | k
    · exact isEmptyElim i
    · rfl
  have hW' : ComplexMatrix2.IsRelativelyOpen (tracelessPi (ι ⊕ κ)) W := by
    rw [← heq]
    exact hW
  have hWsub : W ⊆ tracelessPi (ι ⊕ κ) := by
    obtain ⟨V, -, hV⟩ := hW'
    rw [hV]
    exact inter_subset_right
  have hTo := (isSupOpen_iff_isRelativelyOpen hWsub).2 hW'
  set μ := Fintype.equivFin (ι ⊕ κ)
  set T := coordChart b μ with hT
  have hWo : IsOpen (T ⁻¹' W) := (isSupOpen_iff b μ hWsub).1 hTo
  constructor
  · rintro ⟨-, -, hloc⟩
    refine (isHolomorphicOnTraceless_iff hH b b _ μ _ _).2 ⟨hTo, fun w hw => ?_⟩
    obtain ⟨O, h0, -, hh⟩ := hloc (T w) hw
    obtain ⟨hOt, hd⟩ := (isHolomorphicOnTraceless_iff hH b b _ μ _ _).1 hh
    have hOo := (isSupOpen_iff b μ hOt.1).1 hOt
    have hmem0 : (0 : ComplexCoordinates (Fintype.card (ι ⊕ κ) * 3)) ∈ T ⁻¹' O := by
      change T 0 ∈ O
      rw [map_zero]
      exact h0
    have hat := hd.differentiableAt (hOo.mem_nhds hmem0)
    have hat0 : DifferentiableAt ℂ (e ∘ (Φ ∘ expChartAt (T w)) ∘ coordChart b μ) (w - w) := by
      rwa [sub_self]
    have hc := hat0.comp w (f := fun w' => w' - w) (differentiableAt_id.sub_const w)
    have heq2 : e ∘ Φ ∘ coordChart b μ =
        (e ∘ (Φ ∘ expChartAt (T w)) ∘ coordChart b μ) ∘ fun w' => w' - w := by
      funext w'
      simp only [Function.comp_apply]
      rw [hadd, ← hT, ← map_add]
      simp
    rw [heq2]
    exact hc.differentiableWithinAt
  · intro hh
    obtain ⟨-, hd⟩ := (isHolomorphicOnTraceless_iff hH b b _ μ _ _).1 hh
    have hTC : ∀ A ∈ W, T (coordChartInv b μ A) = A := fun A hA =>
      coordChart_coordChartInv b μ (hWsub hA)
    refine ⟨hW, ?_, fun p hp => ?_⟩
    · have h2 := hd.continuousOn.comp (coordChartInv_continuous b μ).continuousOn (s := W)
        fun A hA => by
          change T (coordChartInv b μ A) ∈ W
          rwa [hTC A hA]
      refine h2.congr fun A hA => ?_
      simp only [Function.comp_apply]
      rw [← hT, hTC A hA]
    · have hTp : ∀ w, T (coordChartInv b μ p + w) = p + T w := by
        intro w
        rw [map_add, hTC p hp]
      set O : Set (ι ⊕ κ → ComplexMatrix2) :=
        tracelessPi (ι ⊕ κ) ∩ (fun A => p + A) ⁻¹' W with hO
      have hpre : T ⁻¹' O = (fun w => coordChartInv b μ p + w) ⁻¹' (T ⁻¹' W) := by
        ext w
        constructor
        · intro h
          change T (coordChartInv b μ p + w) ∈ W
          rw [hTp]
          exact h.2
        · intro h
          have h' : T (coordChartInv b μ p + w) ∈ W := h
          rw [hTp] at h'
          exact ⟨coordChart_mem b μ w, h'⟩
      have hOo : IsOpen (T ⁻¹' O) := by
        rw [hpre]
        exact hWo.preimage (continuous_const.add continuous_id)
      refine ⟨O, ⟨zero_mem_tracelessPi, ?_⟩, fun A hA => ?_,
        (isHolomorphicOnTraceless_iff hH b b _ μ _ _).2
          ⟨(isSupOpen_iff b μ inter_subset_left).2 hOo, ?_⟩⟩
      · change p + 0 ∈ W
        rwa [add_zero]
      · rw [hadd]
        exact hA.2
      · rw [← hT, hpre]
        have hs : Differentiable ℂ fun w => coordChartInv b μ p + w :=
          differentiable_id.const_add _
        have hc := hd.comp hs.differentiableOn
          (s := (fun w => coordChartInv b μ p + w) ⁻¹' (T ⁻¹' W)) fun w hw => hw
        refine hc.congr fun w _ => ?_
        simp only [Function.comp_apply]
        rw [hadd, ← hT, hTp]
private theorem unimodularPowerHolomorphy_holds (hH : HoloFacts) (κ : Type) [Fintype κ]
    [IsEmpty κ] : UnimodularPowerHolomorphy κ := by
  intro n hn b b' W Φ hW hm
  set μ : Fin n ⊕ κ ≃ Fin n := Equiv.sumEmpty (Fin n) κ with hμ
  set T := coordChart b' μ with hTdef
  let π : (Fin n → ComplexMatrix2) → Fin n ⊕ κ → ComplexMatrix2 := pointOfUnimodularPower
  have hπc : Continuous π := by
    refine continuous_pi ?_
    rintro (i | k)
    · exact continuous_apply i
    · exact isEmptyElim k
  have hρ : ∀ p : Fin n ⊕ κ → ComplexMatrix2, π (fun i => p (.inl i)) = p := by
    intro p
    funext t
    rcases t with i | k
    · rfl
    · exact isEmptyElim k
  have hT : ∀ w, π (ComplexCoordinates.tracelessTuple b' w) = T w := by
    intro w
    funext t
    rcases t with i | k
    · simp [hTdef, coordChart, hμ, π, pointOfUnimodularPower]
    · exact isEmptyElim k
  have hch : ∀ X A, π (ComplexCoordinates.expChart X A) =
      expChartAt (π X) (π A) := by
    intro X A
    funext t
    rcases t with i | k
    · rfl
    · exact isEmptyElim k
  have hPmem : ∀ X, π X ∈ GroupLieProduct (Fin n) κ ↔
      X ∈ ComplexMatrix2.complexifiedProduct fun _ : Fin n => ComplexMatrix2.FactorKind.group := by
    intro X
    constructor
    · exact fun h i => h (.inl i)
    · intro h
      rintro (i | k)
      · exact h i
      · exact isEmptyElim k
  have hcq : ∀ X w, ComplexCoordinates.expChartQuotient (Φ ∘ π) X
      (ComplexCoordinates.tracelessTuple b' w) =
      Φ (expChartAt (π X) (T w)) * (Φ (π X))⁻¹ := by
    intro X w
    simp only [ComplexCoordinates.expChartQuotient, Function.comp_apply, hch, hT]
  constructor
  · rintro ⟨-, -, hc, hloc⟩
    obtain ⟨O₁, hO₁, hW₁⟩ := hW
    refine ⟨hn, ⟨π ⁻¹' O₁, hO₁.preimage hπc, ?_⟩, fun X hX => hm hX,
      hc.comp hπc.continuousOn fun X hX => hX, fun X hX => ?_⟩
    · ext X
      change π X ∈ W ↔ _
      rw [hW₁]
      exact and_congr_right' (hPmem X)
    · obtain ⟨O, h0, hO, hh⟩ := hloc (π X) hX
      obtain ⟨hOt, hd⟩ := (isHolomorphicOnTraceless_iff hH b b' _ μ _ _).1 hh
      refine ⟨T ⁻¹' O, ?_, fun w hw => ?_, ?_⟩
      · change T 0 ∈ O
        rw [map_zero]
        exact h0
      · obtain ⟨h1, h2⟩ := hO (T w) hw
        refine ⟨?_, ?_⟩
        · change π _ ∈ W
          rw [hch, hT]
          exact h1
        · rw [hcq]
          exact h2
      · refine (isHolomorphicIn_iff hH).2 ⟨(isSupOpen_iff b' μ hOt.1).1 hOt,
          hd.congr fun w _ => ?_⟩
        simp only [Function.comp_apply]
        rw [hcq]
  · rintro ⟨-, -, -, hc, hloc⟩
    refine ⟨hW, hm, ?_, fun p hp => ?_⟩
    · have hρc : Continuous fun p : Fin n ⊕ κ → ComplexMatrix2 => fun i => p (.inl i) := by
        fun_prop
      have h2 := hc.comp hρc.continuousOn (s := W) fun p hp => by
        change π _ ∈ W
        rwa [hρ]
      refine h2.congr fun p _ => ?_
      exact congrArg Φ (hρ p).symm
    · set X : Fin n → ComplexMatrix2 := fun i => p (.inl i) with hXdef
      have hX : π X = p := hρ p
      obtain ⟨W', h0, hW', hh⟩ := hloc X (by
        change π X ∈ W
        rwa [hX])
      obtain ⟨ho, hd⟩ := (isHolomorphicIn_iff hH).1 hh
      set O : Set (Fin n ⊕ κ → ComplexMatrix2) :=
        tracelessPi (Fin n ⊕ κ) ∩ coordChartInv b' μ ⁻¹' W' with hO
      have hpre : T ⁻¹' O = W' := by
        ext w
        constructor
        · intro h
          have h2 := h.2
          rwa [mem_preimage, hTdef, coordChartInv_coordChart] at h2
        · intro h
          refine ⟨coordChart_mem b' μ w, ?_⟩
          rwa [mem_preimage, hTdef, coordChartInv_coordChart]
      refine ⟨O, ⟨zero_mem_tracelessPi, ?_⟩, fun A hA => ?_,
        (isHolomorphicOnTraceless_iff hH b b' _ μ _ _).2
          ⟨(isSupOpen_iff b' μ inter_subset_left).2 (by rwa [← hTdef, hpre]), ?_⟩⟩
      · change coordChartInv b' μ 0 ∈ W'
        rw [map_zero]
        exact h0
      · have hw : coordChartInv b' μ A ∈ W' := hA.2
        have hTA : T (coordChartInv b' μ A) = A := coordChart_coordChartInv b' μ hA.1
        obtain ⟨h1, h2⟩ := hW' _ hw
        have h1' : π (ComplexCoordinates.expChart X
            (ComplexCoordinates.tracelessTuple b' (coordChartInv b' μ A))) ∈ W := h1
        rw [hch, hT, hTA, hX] at h1'
        rw [hcq, hTA, hX] at h2
        exact ⟨h1', h2⟩
      · rw [← hTdef, hpre]
        refine hd.congr fun w _ => ?_
        simp only [Function.comp_apply]
        rw [hX.symm, ← hcq]
theorem expChartTheory_of_estimates (hE : ComplexMatrix2.ExpLogEstimates) (hH : HoloFacts) :
    ExpChartTheory :=
  ⟨affineHolomorphy_holds hH,
    fun σ _ => ⟨tracelessTopologiesAgree_holds σ, tracelessHolomorphyBasisFree_holds hH σ,
      tracelessRestrictionHolomorphy_holds hH σ⟩,
    fun σ τ _ _ => tracelessCoordsHolomorphy_holds hH σ τ,
    fun ι κ _ _ => ⟨expChartLocalHomeomorph_holds hH hE ι κ, unimodularValuedHolomorphy_holds hH hE ι κ,
      productRestrictionHolomorphy_holds hH hE ι κ⟩,
    fun ι κ ι' κ' _ _ _ _ => compHolomorphy_holds hH hE ι κ ι' κ',
    fun κ _ _ => unimodularPowerHolomorphy_holds hH κ,
    fun ι κ _ _ _ => tracelessPowerHolomorphy_holds hH ι κ⟩
end YangMills.Construction.Matrices.GroupLieProduct.ExpChartHolomorphy

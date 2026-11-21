import YangMills.Construction.Towers.EntriesOfTheSaddleOperatorAreRealAnalyticNearOneProof
import YangMills.Construction.Towers.IteratesOfTheCovariantAveragesHaveRealAnalyticEntriesProof
import YangMills.Construction.Towers.TermsOfTheBackgroundOperatorAreRealAnalytic
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
namespace Tower
namespace BackgroundTerms
def reHermPart (X : ComplexMatrix2) : ComplexMatrix2 := (1 / 2 : ℂ) • (X + X.conjTranspose)
def imHermPart (X : ComplexMatrix2) : ComplexMatrix2 := (-Complex.I / 2) • (X - X.conjTranspose)
theorem reHermPart_add (X Y : ComplexMatrix2) :
    reHermPart (X + Y) = reHermPart X + reHermPart Y := by
  simp only [reHermPart, Matrix.conjTranspose_add]
  module
theorem imHermPart_add (X Y : ComplexMatrix2) : imHermPart (X + Y) = imHermPart X + imHermPart Y := by
  simp only [imHermPart, Matrix.conjTranspose_add]
  module
theorem reHermPart_smul (c : ℂ) (X : ComplexMatrix2) :
    reHermPart (c • X) = c.re • reHermPart X - c.im • imHermPart X := by
  ext i j
  simp only [reHermPart, imHermPart, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.conjTranspose_apply, Matrix.conjTranspose_smul]
  apply Complex.ext <;> simp <;> ring
theorem imHermPart_smul (c : ℂ) (X : ComplexMatrix2) :
    imHermPart (c • X) = c.im • reHermPart X + c.re • imHermPart X := by
  ext i j
  simp only [reHermPart, imHermPart, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.conjTranspose_apply, Matrix.conjTranspose_smul]
  apply Complex.ext <;> simp <;> ring
def complexifyOnHermitian (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := (φ (reHermPart X) : ℂ) + Complex.I * (φ (imHermPart X) : ℂ)
  map_add' X Y := by
    simp only [reHermPart_add, imHermPart_add, map_add]
    push_cast
    ring
  map_smul' c X := by
    simp only [reHermPart_smul, imHermPart_smul, map_add, map_sub, map_smul, smul_eq_mul,
      RingHom.id_apply]
    apply Complex.ext <;> simp
    ring
theorem complexifyOnHermitian_apply (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) {X : ComplexMatrix2}
    (hX : X.IsHermitian) : complexifyOnHermitian φ X = (φ X : ℂ) := by
  have h₁ : reHermPart X = X := by
    simp only [reHermPart, hX.eq]
    module
  have h₂ : imHermPart X = 0 := by
    simp only [imHermPart, hX.eq, sub_self, smul_zero]
  change (φ (reHermPart X) : ℂ) + Complex.I * (φ (imHermPart X) : ℂ) = _
  rw [h₁, h₂]
  simp
section Sets
variable {L n k j : ℕ}
theorem exists_openNhd_of_eventuallyNearIdentity (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝒰₀ : Set (Edge L n k j → ComplexMatrix2)} {P : (Edge L n k j → ComplexMatrix2) → Prop}
    (h : IsOpenNhdOfOne 𝒰₀) (hne : EventuallyNearIdentity (fieldSpace L n k j) P) :
    ∃ 𝒰 : Set (Edge L n k j → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧ 𝒰 ⊆ 𝒰₀ ∧ ∀ W ∈ 𝒰, P W := by apply _root_.YangMills.Construction.Tower.SaddleAnalytic.exists_isOpenNhdOfOne_of_eventually <;> assumption
end Sets
section Holomorphic
variable {L n k : ℕ}
theorem isHolomorphicToCoords_fst {ι κ : Type} [Fintype ι] [Fintype κ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {N : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (h : IsHolomorphicToCoords b Coordinates.ComplexCoordinates.matrixEquiv W N) :
    IsHolomorphicToCoords b (Equiv.refl (Coordinates.ComplexCoordinates 1)) W
      fun q _ => Coordinates.ComplexCoordinates.matrixEquiv (N q) 0 := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.isHolomorphicToCoords_firstEntry <;> assumption
abbrev fieldOfPoint (q : PositiveEdge L n k 0 ⊕ Empty → ComplexMatrix2) :
    Edge L n k 0 → ComplexMatrix2 :=
  fieldOfPositiveValues (groupComponent q)
theorem isAnalyticFieldFunction_of_holomorphic (hH : HolomorphyClosureStatement)
    {𝒰 : Set (Edge L n k 0 → ComplexMatrix2)} {F : (Edge L n k 0 → ComplexMatrix2) → ComplexMatrix2}
    (h0 : IsAnalyticFieldFunction 𝒰 fun _ => (0 : ℝ))
    (hF : ∀ (_ : Fintype (PositiveEdge L n k 0)) (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless),
      IsHolomorphicToMatrixEntries b (GroupLieProduct (PositiveEdge L n k 0) Empty)
        fun q => F (fieldOfPoint q))
    (hh : ∀ U ∈ 𝒰, (F U).IsHermitian) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) :
    IsAnalyticFieldFunction 𝒰 fun U => φ (F U) := by
  obtain ⟨hO, inst, hE, hX⟩ := h0
  refine ⟨hO, inst, hE, fun p hp => ?_⟩
  obtain ⟨𝒳, hp𝒳, h𝒳, hsub, -⟩ := hX p hp
  refine ⟨𝒳, hp𝒳, h𝒳, hsub, fun q _ => Coordinates.ComplexCoordinates.matrixEquiv
    ((complexifyOnHermitian φ).smulRight (1 : ComplexMatrix2) (F (fieldOfPoint q))) 0,
    fun b => ?_, fun q hq => ?_⟩
  · have hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveEdge L n k 0) Empty)
        (GroupLieProduct (PositiveEdge L n k 0) Empty) := ⟨univ, isOpen_univ, by simp⟩
    obtain ⟨-, -, -, -, hl, -, -, -, -, hm, -⟩ := hH _ _ b _ hW
    have hs : 𝒳 ⊆ GroupLieProduct (PositiveEdge L n k 0) Empty := by
      obtain ⟨O, -, e⟩ := h𝒳
      rw [e]
      exact inter_subset_right
    exact isHolomorphicToCoords_fst (hm _ hs h𝒳 _ (hl _ _ (hF inst b)))
  · have hU : fieldOfPoint q ∈ 𝒰 := hsub hq
    funext i
    have e0 : Coordinates.ComplexCoordinates.entryIndex.symm (0 : Fin 4) =
        ((0 : Fin 2), (0 : Fin 2)) := rfl
    show ((complexifyOnHermitian φ).smulRight (1 : ComplexMatrix2) (F (fieldOfPoint q)))
      (Coordinates.ComplexCoordinates.entryIndex.symm 0).1
      (Coordinates.ComplexCoordinates.entryIndex.symm 0).2 = _
    rw [e0]
    simp [complexifyOnHermitian_apply φ (hh _ hU)]
theorem fieldOfPoint_apply (q : PositiveEdge L n k 0 ⊕ Empty → ComplexMatrix2)
    {c : Edge L n k 0} (h : c.IsPositivelyOriented) :
    fieldOfPoint q c = q (.inl ⟨c, h⟩) := by
  simp [fieldOfPositiveValues, h, groupComponent]
theorem holomorphic_conjugateBy [Fintype (PositiveEdge L n k 0)]
    (hH : HolomorphyClosureStatement) (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {c : Edge L n k 0} (h : c.IsPositivelyOriented) (A : ComplexMatrix2) :
    IsHolomorphicToMatrixEntries b (GroupLieProduct (PositiveEdge L n k 0) Empty)
      fun q => ComplexMatrix2.conjugateBy (fieldOfPoint q c) A := by
  have hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveEdge L n k 0) Empty)
      (GroupLieProduct (PositiveEdge L n k 0) Empty) := ⟨univ, isOpen_univ, by simp⟩
  obtain ⟨hc, hm, -, hp, -, hi, -⟩ := hH _ _ b _ hW
  have e : (fun q : PositiveEdge L n k 0 ⊕ Empty → ComplexMatrix2 =>
      ComplexMatrix2.conjugateBy (fieldOfPoint q c) A) =
      fun q => q (.inl ⟨c, h⟩) * A * (q (.inl ⟨c, h⟩))⁻¹ := by
    funext q
    rw [fieldOfPoint_apply q h]
    rfl
  rw [e]
  refine hp _ _ (hp _ _ (hm _) (hc A)) (hi _ (hm _) fun q hq => ?_)
  have hd : (q (.inl ⟨c, h⟩)).det = 1 := hq (.inl ⟨c, h⟩)
  rw [hd]
  exact isUnit_one
end Holomorphic
section Values
variable {L n k : ℕ}
theorem isPositivelyOriented_or_opposite (b : Edge L n k 0) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.isPositivelyOriented_or_opposite <;> assumption
theorem isAnalytic_extendOddly {𝒰 : Set (Edge L n k 0 → ComplexMatrix2)}
    (f : (Edge L n k 0 → ComplexMatrix2) → Edge L n k 0 → ComplexMatrix2)
    (hf : ∀ c : Edge L n k 0, c.IsPositivelyOriented → ∀ φ : ComplexMatrix2 →ₗ[ℝ] ℝ,
      IsAnalyticFieldFunction 𝒰 fun U => φ (f U c))
    (b : Edge L n k 0) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) :
    IsAnalyticFieldFunction 𝒰 fun U => φ (extendOddly (f U) b) := by
  by_cases h : b.IsPositivelyOriented
  · have e : (fun U => φ (extendOddly (f U) b)) = fun U => φ (f U b) := by
      funext U
      simp [extendOddly, h]
    rw [e]
    exact hf b h φ
  · have e : (fun U => φ (extendOddly (f U) b)) = fun U => (-φ) (f U b.opposite) := by
      funext U
      simp [extendOddly, h]
    rw [e]
    exact hf _ ((isPositivelyOriented_or_opposite b).resolve_left h) _
theorem isHermitian_conjugateBy {g A : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary)
    (hA : A.IsHermitian) : (ComplexMatrix2.conjugateBy g A).IsHermitian := by apply _root_.YangMills.Construction.CovariantIterates.isHermitian_conjugateBy <;> assumption
theorem isHermitian_smul_lie {X Y : ComplexMatrix2} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ((Complex.I / 2) • ⁅X, Y⁆ : ComplexMatrix2).IsHermitian := by
  have e : star (Complex.I / 2) = -(Complex.I / 2) := by simp [Complex.conj_I, neg_div]
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Ring.lie_def,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hX.eq, hY.eq, e]
  module
theorem isHermitian_of_mem_hermitianTraceless {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.hermitianTraceless) : X.IsHermitian := h.1.symm
variable (hH : HolomorphyClosureStatement)
include hH
theorem isAnalytic_covDiff {𝒰 : Set (Edge L n k 0 → ComplexMatrix2)}
    (h0 : IsAnalyticFieldFunction 𝒰 fun _ => (0 : ℝ))
    (l : vertexFunctionSpace L n k 0) (c : Edge L n k 0) (hc : c.IsPositivelyOriented)
    (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) :
    IsAnalyticFieldFunction 𝒰 fun U =>
      φ (ComplexMatrix2.conjugateBy (U c) ((l : Vertex L n k 0 → ComplexMatrix2) c.target) -
        (l : Vertex L n k 0 → ComplexMatrix2) c.source) := by
  refine isAnalyticFieldFunction_of_holomorphic hH h0
    (F := fun U => ComplexMatrix2.conjugateBy (U c) ((l : Vertex L n k 0 → ComplexMatrix2) c.target) -
      (l : Vertex L n k 0 → ComplexMatrix2) c.source) (fun _ b => ?_) (fun U hU => ?_) φ
  · have hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveEdge L n k 0) Empty)
        (GroupLieProduct (PositiveEdge L n k 0) Empty) := ⟨univ, isOpen_univ, by simp⟩
    obtain ⟨hconst, -, ha, -⟩ := hH _ _ b _ hW
    simpa only [sub_eq_add_neg] using ha _ _ (holomorphic_conjugateBy hH b hc _) (hconst _)
  · have hU' : U ∈ fieldSpace L n k 0 := h0.1.1 hU
    exact (isHermitian_conjugateBy (hU'.1 c (mem_univ c))
      (isHermitian_of_mem_hermitianTraceless (l.2 _ (mem_univ _)))).sub
      (isHermitian_of_mem_hermitianTraceless (l.2 _ (mem_univ _)))
theorem isAnalytic_lieTerm {𝒰 : Set (Edge L n k 0 → ComplexMatrix2)}
    (h0 : IsAnalyticFieldFunction 𝒰 fun _ => (0 : ℝ))
    (l : vertexFunctionSpace L n k 0) (B : edgeFormSpace L n k 0) (c : Edge L n k 0)
    (hc : c.IsPositivelyOriented) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) :
    IsAnalyticFieldFunction 𝒰 fun U =>
      φ ((Complex.I / 2) • ⁅(l : Vertex L n k 0 → ComplexMatrix2) c.source +
        ComplexMatrix2.conjugateBy (U c) ((l : Vertex L n k 0 → ComplexMatrix2) c.target),
        (B : Edge L n k 0 → ComplexMatrix2) c⁆) := by
  refine isAnalyticFieldFunction_of_holomorphic hH h0
    (F := fun U => (Complex.I / 2) • ⁅(l : Vertex L n k 0 → ComplexMatrix2) c.source +
      ComplexMatrix2.conjugateBy (U c) ((l : Vertex L n k 0 → ComplexMatrix2) c.target),
      (B : Edge L n k 0 → ComplexMatrix2) c⁆)
    (fun _ b => ?_) (fun U hU => ?_) φ
  · have hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveEdge L n k 0) Empty)
        (GroupLieProduct (PositiveEdge L n k 0) Empty) := ⟨univ, isOpen_univ, by simp⟩
    obtain ⟨hconst, -, ha, -, hl, -⟩ := hH _ _ b _ hW
    have h := hl ((Complex.I / 2) • (LinearMap.mulRight ℂ ((B : Edge L n k 0 → ComplexMatrix2) c) -
      LinearMap.mulLeft ℂ ((B : Edge L n k 0 → ComplexMatrix2) c))) _
      (ha _ _ (hconst ((l : Vertex L n k 0 → ComplexMatrix2) c.source))
        (holomorphic_conjugateBy hH b hc ((l : Vertex L n k 0 → ComplexMatrix2) c.target)))
    simpa only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply, Ring.lie_def] using h
  · have hU' : U ∈ fieldSpace L n k 0 := h0.1.1 hU
    exact isHermitian_smul_lie
      ((isHermitian_of_mem_hermitianTraceless (l.2 _ (mem_univ _))).add
        (isHermitian_conjugateBy (hU'.1 c (mem_univ c))
          (isHermitian_of_mem_hermitianTraceless (l.2 _ (mem_univ _)))))
      (isHermitian_of_mem_hermitianTraceless (B.2.1 c hc))
end Values
section Second
variable {L n k : ℕ}
theorem lineLogarithm_eventuallyEq {U : Edge L n k 0 → ComplexMatrix2} (hU : IterLogRatioAnalytic U)
    (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k k) :
    lineLogarithm (smoothingIter L n k k) U B c =ᶠ[𝓝 0]
      fun t : ℝ => iterLogRatio U c ((t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2)) := by
  obtain ⟨-, hreal, hev, -⟩ := hU
  have hcont : Continuous fun t : ℝ => t • B :=
    continuous_induced_rng.2 (continuous_pi fun b => by
      change Continuous fun t : ℝ => t • (B : Edge L n k 0 → ComplexMatrix2) b
      exact continuous_id.smul continuous_const)
  have hlim : Tendsto (fun t : ℝ => t • B) (𝓝 0) (𝓝 0) := by
    have h := hcont.tendsto 0
    rwa [zero_smul] at h
  filter_upwards [hlim.eventually hev] with t ht
  have e : (((t • B : edgeFormSpace L n k 0)) : Edge L n k 0 → ComplexMatrix2) =
      (t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2) := by
    funext b
    ext i j
    simp
  rw [e] at ht
  simp only [lineLogarithm, iterLogRatio]
  rw [ht.2.1 c, hreal c]
theorem iterQuadraticTerm_diag {U : Edge L n k 0 → ComplexMatrix2} (hU : IterLogRatioAnalytic U)
    (hQ : IterHasUniqueQuadraticExpansion U) (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k k) :
    iterQuadraticTerm U B B c =
      iteratedDeriv 2 (lineLogarithm (smoothingIter L n k k) U B c) 0 := by
  have h := hQ.2.2 _ hQ.2.1 B c
  have e : taylorCoeffAtZero 2 (iterLogRatio U c) (B : Edge L n k 0 → ComplexMatrix2) =
      (2 : ℝ)⁻¹ • iteratedDeriv 2 (lineLogarithm (smoothingIter L n k k) U B c) 0 := by
    rw [(lineLogarithm_eventuallyEq hU B c).iteratedDeriv_eq 2]
    unfold taylorCoeffAtZero
    norm_num [Nat.factorial]
  rw [e, one_div] at h
  exact smul_right_injective _ (inv_ne_zero (two_ne_zero' ℝ)) h
theorem iterQuadraticTerm_polarization {U : Edge L n k 0 → ComplexMatrix2}
    (hU : IterLogRatioAnalytic U) (hQ : IterHasUniqueQuadraticExpansion U)
    (B B' : edgeFormSpace L n k 0) (c : PositiveEdge L n k k) :
    iterQuadraticTerm U B B' c = (1 / 2 : ℝ) •
      (iteratedDeriv 2 (lineLogarithm (smoothingIter L n k k) U
          ((B + B' : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) c) 0 -
        iteratedDeriv 2 (lineLogarithm (smoothingIter L n k k) U B c) 0 -
        iteratedDeriv 2 (lineLogarithm (smoothingIter L n k k) U B' c) 0) := by
  rw [← iterQuadraticTerm_diag hU hQ, ← iterQuadraticTerm_diag hU hQ,
    ← iterQuadraticTerm_diag hU hQ]
  have hs := hQ.2.1.1 B' B
  simp only [map_add, LinearMap.add_apply, Pi.add_apply, hs]
  module
end Second
end BackgroundTerms
open BackgroundTerms in
theorem backgroundTermsAnalytic_proof
    (hExp : IterLeftChartExpansion)
    (hIter : SmoothingIterAnalyticNearOne)
    (hTay : LeftChartTaylorCoefficientsAnalytic)
    (hAct : WilsonActionAnalytic)
    (hAlg : AnalyticFieldFunctionsClosed)
    (hE : BondSetFields.ProductStructureHolds)
    (hHol : HolomorphyClosureStatement) :
    BackgroundTermsAnalytic := by
  intro L n k hL hn hk
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  obtain ⟨𝒰₁, h𝒰₁, hM, -⟩ := hIter L n (i + 1) i hL hn (Nat.lt_succ_self i)
  obtain ⟨𝒰, h𝒰, hsub, hP⟩ := exists_openNhd_of_eventuallyNearIdentity hE hL hn (Nat.zero_le _)
    h𝒰₁ (hExp L n (i + 1) hL hn hk)
  have hop := h𝒰.1
  obtain ⟨hconst, hsp, hmono, hcongr, -⟩ :=
    hAlg L n (i + 1) 0 0 hL hn (Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨hTayF, hTayM⟩ := hTay L n (i + 1) 0 (i + 1) hL hn (Nat.zero_le _) le_rfl
  have h0 := hconst 𝒰 0 hop
  have hscale : ∀ (c : ℝ) (G : (Edge L n (i + 1) 0 → ComplexMatrix2) → ℝ),
      IsAnalyticFieldFunction 𝒰 G → IsAnalyticFieldFunction 𝒰 fun U => c * G U :=
    fun c G h => (hsp _ _ _ (hconst 𝒰 c hop) h).2
  have hdiff : ∀ G₁ G₂ : (Edge L n (i + 1) 0 → ComplexMatrix2) → ℝ, IsAnalyticFieldFunction 𝒰 G₁ →
      IsAnalyticFieldFunction 𝒰 G₂ → IsAnalyticFieldFunction 𝒰 fun U => G₁ U - G₂ U := by
    intro G₁ G₂ h₁ h₂
    refine hcongr _ _ _ (hsp _ _ _ h₁ (hscale (-1) _ h₂)).1 fun U _ => ?_
    ring
  have hsecond : ∀ (B : edgeFormSpace L n (i + 1) 0) (c : PositiveEdge L n (i + 1) (i + 1))
      (φ : ComplexMatrix2 →ₗ[ℝ] ℝ), IsAnalyticFieldFunction 𝒰 fun U =>
        φ (iteratedDeriv 2 (lineLogarithm (smoothingIter L n (i + 1) (i + 1)) U B c) 0) :=
    fun B c φ => hmono _ _ _ (hTayM 𝒰₁ _ hM B B.2 c φ).2 hop hsub
  refine ⟨𝒰, h𝒰, fun B B' => ?_, fun B B' c φ => ?_, fun l B b φ => ?_, fun l b φ => ?_⟩
  · exact ((hTayF 𝒰 _ (hmono _ _ _ (hAct L n (i + 1) hL hn) hop hop.1) B B.2).2 B' B'.2)
  · refine hcongr _ _ _ (hscale (1 / 2) _ (hdiff _ _ (hdiff _ _ (hsecond (B + B') c φ)
      (hsecond B c φ)) (hsecond B' c φ))) fun U hU => ?_
    obtain ⟨hlog, -, hQ⟩ := hP U hU
    simp only [iterQuadraticTerm_polarization hlog hQ B B' c, map_smul, map_sub, smul_eq_mul]
  · exact isAnalytic_extendOddly _
      (fun c hc φ => isAnalytic_lieTerm hHol h0 l B c hc φ) b φ
  · exact isAnalytic_extendOddly _
      (fun c hc φ => isAnalytic_covDiff hHol h0 l c hc φ) b φ
end Tower
end YangMills.Construction
end

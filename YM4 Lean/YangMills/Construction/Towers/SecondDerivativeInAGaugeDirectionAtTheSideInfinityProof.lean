import YangMills.Construction.ComplexAnalysis.MixedDerivativeOnSurface
import YangMills.Construction.Towers.DerivativesOfTheActionOnFinitePlaquetteSetsAtTheSideInfinity
import YangMills.Construction.Towers.ExpansionOfTheMoveAtTheSideInfinity
import YangMills.Construction.Towers.ExpansionOfThreeExponentialsInTheLeftChartProof
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartAtTheSideInfinity
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinityProof
import YangMills.Construction.Towers.SecondDerivativeInAGaugeDirectionAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.GaugeDirectionHessian
section OneLattice
variable {a : ℝ}
theorem not_opposite_isPositivelyOriented (ha : 0 < a) {b : InfiniteLattice.Link a}
    (h : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
theorem gaugeAct_opposite {u : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2}
    {V : InfiniteLattice.Link a → Matrices.ComplexMatrix2} (hu : ∀ x, (u x).det = 1)
    {b : InfiniteLattice.Link a} (hV : V b.opposite = (V b)⁻¹) :
    gaugeAct u V b.opposite = (gaugeAct u V b)⁻¹ := by
  change u b.terminal * V b.opposite * (u b.initial)⁻¹ =
    (u b.initial * V b * (u b.terminal)⁻¹)⁻¹
  rw [hV, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ (by simp [hu]), mul_assoc]
theorem extendOddly_mem (ha : 0 < a) {f : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hf : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented →
      f b ∈ Matrices.ComplexMatrix2.traceless) :
    extendOddly f ∈ complexEdgeForms a := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.extendOddly_mem <;> assumption
theorem conjugateBy_mem_traceless {V A : Matrices.ComplexMatrix2} (hV : V.det = 1)
    (hA : A ∈ Matrices.ComplexMatrix2.traceless) :
    Matrices.ComplexMatrix2.conjugateBy V A ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
theorem lie_mem_traceless (X Y : Matrices.ComplexMatrix2) :
    ⁅X, Y⁆ ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TripleExpExpansion.lie_mem_traceless <;> assumption
theorem finite_positive_links_near {S : Set (InfiniteLattice.LatticePoint a)} (hS : S.Finite) :
    {b : InfiniteLattice.Link a | b.IsPositivelyOriented ∧
      (b.initial ∈ S ∨ b.terminal ∈ S)}.Finite := by
  have h1 : ((fun q : InfiniteLattice.LatticePoint a × Fin 4 =>
      InfiniteLattice.Link.forwardFrom q.1 q.2) ''
      (S ×ˢ (univ : Set (Fin 4)))).Finite := (hS.prod finite_univ).image _
  have h2 : ((fun q : InfiniteLattice.LatticePoint a × Fin 4 =>
      InfiniteLattice.Link.forwardFrom (q.1 - InfiniteLattice.axisStep a q.2) q.2) ''
      (S ×ˢ (univ : Set (Fin 4)))).Finite := (hS.prod finite_univ).image _
  refine (h1.union h2).subset ?_
  rintro b ⟨⟨μ, hμ⟩, hb | hb⟩
  · refine Or.inl ⟨(b.initial, μ), ⟨hb, mem_univ _⟩, ?_⟩
    refine InfiniteLattice.Link.ext rfl ?_
    change b.initial + InfiniteLattice.axisStep a μ = b.terminal
    rw [← hμ]
    abel
  · refine Or.inr ⟨(b.terminal, μ), ⟨hb, mem_univ _⟩, ?_⟩
    refine InfiniteLattice.Link.ext ?_ ?_
    · change b.terminal - InfiniteLattice.axisStep a μ = b.initial
      rw [← hμ]
      abel
    · change b.terminal - InfiniteLattice.axisStep a μ + InfiniteLattice.axisStep a μ = b.terminal
      abel
end OneLattice
variable {L k j : ℕ}
theorem complexFaceTerm_congr {V V' : Edge L k j → Matrices.ComplexMatrix2} {p : Face L k j}
    (h : ∀ b ∈ faceEdges p, V b = V' b ∧ V b.opposite = V' b.opposite) :
    complexFaceTerm V p = complexFaceTerm V' p := by
  simp only [complexFaceTerm, faceVariable, linkHolonomy, faceBoundary,
    List.map_cons, List.map_nil]
  rw [(h _ (by simp [faceEdges])).1, (h _ (by simp [faceEdges])).1,
    (h _ (by simp [faceEdges])).2, (h _ (by simp [faceEdges])).2]
theorem covDiff_hasFiniteEdgeSupport {U : Edge L k j → Matrices.ComplexMatrix2}
    {l : Vertex L k j → Matrices.ComplexMatrix2}
    (hl : HasFiniteSupp l) : HasFiniteEdgeSupport (covDiff U l) := by
  refine (finite_positive_links_near hl).subset ?_
  rintro b ⟨hb, hne⟩
  refine ⟨hb, ?_⟩
  by_contra hc
  have h1 : l b.initial = 0 := by simpa using fun h => hc (Or.inl h)
  have h2 : l b.terminal = 0 := by simpa using fun h => hc (Or.inr h)
  apply hne
  simp only [covDiff, extendOddly, if_pos hb, h1, h2]
  simp [Matrices.ComplexMatrix2.conjugateBy]
theorem levelBracketTerm_support_subset (U : Edge L k j → Matrices.ComplexMatrix2)
    (l : Vertex L k j → Matrices.ComplexMatrix2) (B : Edge L k j → Matrices.ComplexMatrix2) :
    edgeSupport (levelBracketTerm U l B) ⊆ edgeSupport B := by
  rintro b ⟨hb, hne⟩
  refine ⟨hb, fun h0 => hne ?_⟩
  simp only [levelBracketTerm, extendOddly, if_pos hb, h0]
  simp [lie_eq_mul_sub_mul]
def truncatedRemainder (F : Finset (Edge L k j)) (U : Edge L k j → Matrices.ComplexMatrix2)
    (l : Vertex L k j → Matrices.ComplexMatrix2) (B : Edge L k j → Matrices.ComplexMatrix2)
    (z : Coordinates.ComplexCoordinates 2) : Edge L k j → Matrices.ComplexMatrix2 :=
  open Classical in
  extendOddly fun b => if b ∈ F then expansionRemainder U l B (z 0) (z 1) b else 0
def surfaceForm (F : Finset (Edge L k j)) (U : Edge L k j → Matrices.ComplexMatrix2)
    (l : Vertex L k j → Matrices.ComplexMatrix2) (B : Edge L k j → Matrices.ComplexMatrix2)
    (s t : ℂ) : Edge L k j → Matrices.ComplexMatrix2 :=
  s • B + (-t) • covDiff U l + (s * t) • levelBracketTerm U l B +
    t ^ 2 • extendOddly (gaugeQuadTerm U l) + truncatedRemainder F U l B ![s, t]
theorem surfaceForm_apply_of_mem (F : Finset (Edge L k j))
    (U : Edge L k j → Matrices.ComplexMatrix2) (l : Vertex L k j → Matrices.ComplexMatrix2)
    (B : Edge L k j → Matrices.ComplexMatrix2) (s t : ℂ) {b : Edge L k j}
    (hb : b.IsPositivelyOriented) (hm : b ∈ F) :
    surfaceForm F U l B s t b = principalExponent U l B s t b + expansionRemainder U l B s t b := by
  have h1 : extendOddly (gaugeQuadTerm U l) b = gaugeQuadTerm U l b := by
    simp only [extendOddly, if_pos hb]
  have h2 : truncatedRemainder F U l B ![s, t] b = expansionRemainder U l B s t b := by
    simp only [truncatedRemainder, extendOddly, if_pos hb, if_pos hm]
    rfl
  simp only [surfaceForm, principalExponent, Pi.add_apply, Pi.smul_apply, h1, h2, neg_smul,
    Pi.neg_apply, sub_eq_add_neg]
def matrixOfCoords : Coordinates.ComplexCoordinates 4 →ₗ[ℂ] Matrices.ComplexMatrix2 where
  toFun w := Coordinates.ComplexCoordinates.matrixEquiv.symm w
  map_add' w w' := by
    ext i i'
    simp [Coordinates.ComplexCoordinates.matrixEquiv]
  map_smul' c w := by
    ext i i'
    simp [Coordinates.ComplexCoordinates.matrixEquiv]
theorem claim_holds
    (hD : ActionDerivsOnFiniteFaces.Claim)
    (hM : SurfaceMixedDerivative.MixedDerivAlongSurface)
    (hT : VanishingOrderThreeIffCubicBound)
    (hE : FullSpaceTwistExpansionClaim)
    (hG : LeftChartAlgebra.GaugeConditionsInfiniteSide)
    (hF : FaceEdgeFinsets.FacesAndEdgesFinite)
    (hH : Coordinates.ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement) :
    GaugeDirectionHessianClaim := by
  classical
  intro L k j hL hj U l B hU hl hlfin hB hBfin
  have ha : 0 < meshAt L k j :=
    zpow_pos (by have := hL.2; exact_mod_cast (by omega : 0 < L)) _
  have hfin := (hF L hL k j hj).2
  have hpos : ∀ p : Face L k j, ∀ b ∈ faceEdges p, b.IsPositivelyOriented := hfin.1.2
  have hdet : ∀ b, (U b).det = 1 := fun b => hU.1 b
  have hDl : covDiff U l ∈ complexEdgeForms (meshAt L k j) :=
    extendOddly_mem ha fun b _ =>
      Matrices.ComplexMatrix2.traceless.sub_mem
        (conjugateBy_mem_traceless (hdet b) (hl b.terminal)) (hl b.initial)
  have hcT : levelBracketTerm U l B ∈ complexEdgeForms (meshAt L k j) :=
    extendOddly_mem ha fun b _ =>
      Matrices.ComplexMatrix2.traceless.smul_mem _ (lie_mem_traceless _ _)
  have hξ : extendOddly (gaugeQuadTerm U l) ∈ complexEdgeForms (meshAt L k j) :=
    extendOddly_mem ha fun b _ =>
      Matrices.ComplexMatrix2.traceless.neg_mem
        (Matrices.ComplexMatrix2.traceless.smul_mem _ (lie_mem_traceless _ _))
  have hDfin : HasFiniteEdgeSupport (covDiff U l) :=
    covDiff_hasFiniteEdgeSupport hlfin
  have hcfin : HasFiniteEdgeSupport (levelBracketTerm U l B) :=
    hBfin.subset (levelBracketTerm_support_subset U l B)
  set S : Set (Edge L k j) := edgeSupport B ∪ edgeSupport (covDiff U l) with hSdef
  have hSfin : S.Finite := hBfin.union hDfin
  have hSpos : ∀ b ∈ S, b.IsPositivelyOriented := by
    rintro b (hb | hb)
    · exact hb.1
    · exact hb.1
  set Ω : Set (Face L k j) := FaceEdgeFinsets.Unbounded.facesMeetingWithBase S with hΩdef
  have hΩ := hfin.2.1 S hSfin hSpos
  obtain ⟨hder, F, Φ, ⟨hFne, hbpos⟩, hFmem, hΦa, hΦ⟩ := hD L k j hL hj U hU Ω hΩ.2.2.1 hΩ.2.2.2
  have hbmem : ∀ p ∈ Ω, ∀ b ∈ faceEdges p, b ∈ F := fun p hp b hb =>
    (hFmem b).2 ⟨p, hp, hb⟩
  obtain ⟨hexpS, hexpT, hexp⟩ := hE L k j hL hj U l B hU hl hB
  have hexpF : ∀ b : F,
      HasLocalExpExpansion (fun s t => twistedField U l B s t b.1) (U b.1)
        (fun s t => principalExponent U l B s t b.1) := fun b => hexp b.1 (hbpos b.1 b.2)
  simp only [HasLocalExpExpansion] at hexpF
  choose O hOopen h0 hOval hOhol hO3 using hexpF
  set W : Set (Coordinates.ComplexCoordinates 2) := ⋂ b, O b with hWdef
  have hWopen : IsOpen W := isOpen_iInter_of_finite hOopen
  have h0W : (0 : Coordinates.ComplexCoordinates 2) ∈ W := mem_iInter.2 h0
  have hWO : ∀ b, W ⊆ O b := fun b => iInter_subset _ b
  have hbd : ∀ b : F, ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ z : Coordinates.ComplexCoordinates 2,
      ‖z‖ < δ → ‖Coordinates.ComplexCoordinates.matrixEquiv
        (expansionRemainder U l B (z 0) (z 1) b.1)‖ ≤ C * ‖z‖ ^ 3 :=
    fun b => (hT (O b) _ (h0 b) (hOhol b)).1 (hO3 b)
  choose C δ hC hδ hbound using hbd
  let ℓ : Coordinates.ComplexCoordinates 4 →L[ℂ] Matrices.ComplexMatrix2 :=
    LinearMap.toContinuousLinearMap matrixOfCoords
  have hℓ : ∀ X : Matrices.ComplexMatrix2,
      ℓ (Coordinates.ComplexCoordinates.matrixEquiv X) = X := fun X =>
    Coordinates.ComplexCoordinates.matrixEquiv.symm_apply_apply X
  have hev : ∀ᶠ z in 𝓝 (0 : Coordinates.ComplexCoordinates 2), z ∈ W ∧ ∀ b : F,
      ‖Coordinates.ComplexCoordinates.matrixEquiv
        (expansionRemainder U l B (z 0) (z 1) b.1)‖ ≤ C b * ‖z‖ ^ 3 := by
    refine (show ∀ᶠ z in 𝓝 (0 : Coordinates.ComplexCoordinates 2), z ∈ W from
      hWopen.mem_nhds h0W).and (eventually_all.2 fun b => ?_)
    filter_upwards [Metric.ball_mem_nhds (0 : Coordinates.ComplexCoordinates 2) (hδ b)] with z hz
    exact hbound b z (by simpa using hz)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  let r : Coordinates.ComplexCoordinates 2 → (F → Matrices.ComplexMatrix2) := fun z b =>
    expansionRemainder U l B (z 0) (z 1) b.1
  have hrem : ∀ z ∈ W, ∀ b : F,
      expansionRemainder U l B (z 0) (z 1) b.1 ∈ Matrices.ComplexMatrix2.traceless :=
    fun z hz b => (hOval b z (hWO b hz)).2.2
  have hrdiff : DifferentiableOn ℂ r W := by
    refine differentiableOn_pi.2 fun b => ?_
    have hf : DifferentiableOn ℂ (fun z : Coordinates.ComplexCoordinates 2 =>
        Coordinates.ComplexCoordinates.matrixEquiv
          (expansionRemainder U l B (z 0) (z 1) b.1)) W :=
      ((hH 2 4 (O b) _ (hOopen b)).1 (hOhol b)).mono (hWO b)
    exact (ℓ.differentiable.comp_differentiableOn hf).congr fun z _ => (hℓ _).symm
  have hrbound : ∀ z : Coordinates.ComplexCoordinates 2, ‖z‖ < ε →
      ‖r z‖ ≤ (‖ℓ‖ * ∑ b, C b) * ‖z‖ ^ 3 := by
    intro z hz
    obtain ⟨hzW, hzb⟩ := hball (y := z) (by simpa using hz)
    have hCnn : ∀ b, 0 ≤ C b := fun b => (hC b).le
    have hnn : 0 ≤ (‖ℓ‖ * ∑ b, C b) * ‖z‖ ^ 3 :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun b _ => hCnn b)) (by positivity)
    refine (pi_norm_le_iff_of_nonneg hnn).2 fun b => ?_
    calc ‖r z b‖ = ‖ℓ (Coordinates.ComplexCoordinates.matrixEquiv
              (expansionRemainder U l B (z 0) (z 1) b.1))‖ := by rw [hℓ]
      _ ≤ ‖ℓ‖ * ‖Coordinates.ComplexCoordinates.matrixEquiv
              (expansionRemainder U l B (z 0) (z 1) b.1)‖ := ℓ.le_opNorm _
      _ ≤ ‖ℓ‖ * (C b * ‖z‖ ^ 3) := by gcongr; exact hzb b
      _ ≤ ‖ℓ‖ * ((∑ b, C b) * ‖z‖ ^ 3) := by
          gcongr
          exact Finset.single_le_sum (fun b _ => hCnn b) (Finset.mem_univ b)
      _ = _ := by ring
  let v : (Edge L k j → Matrices.ComplexMatrix2) → (F → Matrices.ComplexMatrix2) :=
    fun E b => E b.1
  have hsurf : ∀ s t : ℂ, (![s, t] : Coordinates.ComplexCoordinates 2) ∈ W →
      Φ (SurfaceMixedDerivative.surfaceParam
          (v B) (-v (covDiff U l)) (v (levelBracketTerm U l B))
          (v (extendOddly (gaugeQuadTerm U l))) r s t) =
        faceTermSum Ω (expTwist (s • B) U) := by
    intro s t hz
    have hRf : truncatedRemainder F U l B ![s, t] ∈ complexEdgeForms (meshAt L k j) := by
      refine extendOddly_mem ha fun b _ => ?_
      by_cases hm : b ∈ F
      · rw [if_pos hm]
        exact hrem _ hz ⟨b, hm⟩
      · rw [if_neg hm]
        exact Matrices.ComplexMatrix2.traceless.zero_mem
    have m1 := (complexEdgeForms (meshAt L k j)).smul_mem s hB
    have m2 := (complexEdgeForms (meshAt L k j)).smul_mem (-t) hDl
    have m3 := (complexEdgeForms (meshAt L k j)).smul_mem (s * t) hcT
    have m4 := (complexEdgeForms (meshAt L k j)).smul_mem (t ^ 2) hξ
    have m12 := (complexEdgeForms (meshAt L k j)).add_mem m1 m2
    have m123 := (complexEdgeForms (meshAt L k j)).add_mem m12 m3
    have m1234 := (complexEdgeForms (meshAt L k j)).add_mem m123 m4
    have hC' : surfaceForm F U l B s t ∈ complexEdgeForms (meshAt L k j) :=
      (complexEdgeForms (meshAt L k j)).add_mem m1234 hRf
    have hco : v (surfaceForm F U l B s t) =
        SurfaceMixedDerivative.surfaceParam
          (v B) (-v (covDiff U l)) (v (levelBracketTerm U l B))
          (v (extendOddly (gaugeQuadTerm U l))) r s t := by
      funext b
      have h2 : truncatedRemainder F U l B ![s, t] b.1 = r ![s, t] b := by
        simp only [truncatedRemainder, extendOddly, if_pos (hbpos b.1 b.2), if_pos b.2]
        rfl
      simp only [v, surfaceForm, SurfaceMixedDerivative.surfaceParam,
        Pi.add_apply, Pi.smul_apply, Pi.neg_apply, h2, neg_smul, smul_neg]
    rw [← hco]
    refine (hΦ _ hC').trans ?_
    refine finsum_mem_congr rfl fun p hp => ?_
    have hg := (hG L k j hL hj).1 (expTwist (s • B) U) (vertexExp (t • l))
      (hexpS s) (hexpT t)
    refine Eq.trans (complexFaceTerm_congr fun b hb => ?_) (hg.2 p).2
    have hbF := hbmem p hp b hb
    have hbP := hpos p b hb
    have hv := (hOval ⟨b, hbF⟩ _ (hWO ⟨b, hbF⟩ hz)).2.1
    have hw := surfaceForm_apply_of_mem F U l B s t hbP hbF
    have e1 : Matrices.ComplexMatrix2.matExp (Complex.I • surfaceForm F U l B s t b) * U b =
        twistedField U l B s t b := by
      rw [hw]
      exact hv.symm
    have hr : ¬ b.opposite.IsPositivelyOriented := not_opposite_isPositivelyOriented ha hbP
    have hrr : b.opposite.opposite = b := InfiniteLattice.Link.ext rfl rfl
    have e2 : twistedField U l B s t b.opposite = (twistedField U l B s t b)⁻¹ :=
      gaugeAct_opposite (fun x => hexpT t x) ((hexpS s).2 b)
    constructor
    · simp only [expTwist, if_pos hbP]
      exact e1
    · simp only [expTwist, if_neg hr, hrr]
      rw [e1]
      exact e2.symm
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ < ε := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with s hs
    simpa using hs
  have hzero : SurfaceMixedDerivative.mixedDerivAtOrigin
      (fun s t => Φ (SurfaceMixedDerivative.surfaceParam
          (v B) (-v (covDiff U l)) (v (levelBracketTerm U l B))
          (v (extendOddly (gaugeQuadTerm U l))) r s t)) = 0 := by
    unfold SurfaceMixedDerivative.mixedDerivAtOrigin
    have h1 : (fun s : ℂ => deriv (fun t : ℂ => Φ
        (SurfaceMixedDerivative.surfaceParam
          (v B) (-v (covDiff U l)) (v (levelBracketTerm U l B))
          (v (extendOddly (gaugeQuadTerm U l))) r s t)) 0)
        =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hsmall] with s hs
      have h2 : (fun t : ℂ => Φ
          (SurfaceMixedDerivative.surfaceParam
            (v B) (-v (covDiff U l)) (v (levelBracketTerm U l B))
            (v (extendOddly (gaugeQuadTerm U l))) r s t))
          =ᶠ[𝓝 0] fun _ => faceTermSum Ω (expTwist (s • B) U) := by
        filter_upwards [hsmall] with t ht
        refine hsurf s t (hball (y := ![s, t]) ?_).1
        rw [dist_zero_right, pi_norm_lt_iff hε]
        intro i
        fin_cases i
        · simpa using hs
        · simpa using ht
      rw [h2.deriv_eq]
      simp
    rw [h1.deriv_eq]
    simp
  have key := hM (F → Matrices.ComplexMatrix2) univ Φ W r (v B) (-v (covDiff U l))
    (v (levelBracketTerm U l B)) (v (extendOddly (gaugeQuadTerm U l)))
    (‖ℓ‖ * ∑ b, C b) ε isOpen_univ (mem_univ _) hΦa.differentiableOn hWopen h0W hrdiff hε hrbound
  rw [hzero] at key
  have hsub1 : FaceEdgeFinsets.Unbounded.facesMeeting
      (edgeSupport B ∪ edgeSupport (covDiff U l)) ⊆ Ω :=
    subset_union_left
  have hsub2 : FaceEdgeFinsets.Unbounded.facesMeeting (edgeSupport (levelBracketTerm U l B) ∪
      edgeSupport (levelBracketTerm U l B)) ⊆ Ω := by
    rintro p ⟨b, hb, hbp⟩
    have hbB : b ∈ edgeSupport B := by
      rcases hb with hb | hb <;> exact levelBracketTerm_support_subset U l B hb
    exact Or.inl ⟨b, Or.inl hbB, hbp⟩
  have h1 := (hder B _ hB hDl hBfin hDfin hsub1).2
  have h2 := (hder _ _ hcT hcT hcfin hcfin hsub2).1
  have hsum : ∀ s t : ℂ, Φ (s • v B + t • v (covDiff U l)) =
      ActionDerivsOnFiniteFaces.actionAtExpTwist Ω U (s • B + t • covDiff U l) := fun s t =>
    hΦ _ ((complexEdgeForms (meshAt L k j)).add_mem
      ((complexEdgeForms (meshAt L k j)).smul_mem s hB)
      ((complexEdgeForms (meshAt L k j)).smul_mem t hDl))
  have hmix : SurfaceMixedDerivative.mixedDerivAtOrigin
      (fun s t => Φ (s • v B + t • (-v (covDiff U l)))) =
      -complexActionHessian U B (covDiff U l) := by
    unfold SurfaceMixedDerivative.mixedDerivAtOrigin
    have h3 : (fun s : ℂ => deriv (fun t : ℂ => Φ (s • v B +
        t • (-v (covDiff U l)))) 0) =
        fun s : ℂ => -deriv (fun t : ℂ => ActionDerivsOnFiniteFaces.actionAtExpTwist Ω U
          (s • B + t • covDiff U l)) 0 := by
      funext s
      have h4 := deriv_comp_neg (fun t : ℂ => ActionDerivsOnFiniteFaces.actionAtExpTwist Ω U
          (s • B + t • covDiff U l)) (0 : ℂ)
      have h5 : (fun t : ℂ => Φ (s • v B + t • (-v (covDiff U l)))) =
          fun t : ℂ => ActionDerivsOnFiniteFaces.actionAtExpTwist Ω U
            (s • B + (-t) • covDiff U l) := by
        funext t
        rw [← hsum, neg_smul, smul_neg]
      rw [h5]
      simpa only [neg_zero] using h4
    rw [h3, deriv.fun_neg, h1]
    simp [mixedDirectionalDeriv]
  have hone : deriv (fun t : ℂ => Φ (t • v (levelBracketTerm U l B))) 0 =
      complexActionDeriv U (levelBracketTerm U l B) := by
    have h6 : (fun t : ℂ => Φ (t • v (levelBracketTerm U l B))) =
        fun t : ℂ => ActionDerivsOnFiniteFaces.actionAtExpTwist Ω U
          (t • levelBracketTerm U l B) := by
      funext t
      exact hΦ _ ((complexEdgeForms (meshAt L k j)).smul_mem t hcT)
    rw [h6, h2]
    simp [directionalDeriv]
  rw [hmix, hone] at key
  linear_combination key
end YangMills.Construction.Tower.FullSpace.GaugeDirectionHessian
end

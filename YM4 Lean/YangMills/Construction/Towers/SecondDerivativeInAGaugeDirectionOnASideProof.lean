import YangMills.Construction.ComplexAnalysis.MixedDerivativeOnSurface
import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.DerivativesOnFiniteSetsOfPlaquettesOnASide
import YangMills.Construction.Towers.ExpansionOfTheMoveOnASide
import YangMills.Construction.Towers.ExpansionOfThreeExponentialsInTheLeftChartProof
import YangMills.Construction.Towers.GaugeConditionsOfTheAlgebraOfTheLeftChartOnASide
import YangMills.Construction.Towers.SecondDerivativeInAGaugeDirectionOnASide
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.LeftChartAlgebra
namespace GaugeDirectionHessian
open FiniteFaceDerivatives
variable {L n k j : ℕ}
def pauliCoeffLinear : Coordinates.ComplexCoordinates 4 →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun w := ![(w 1 + w 2) / 2, (w 2 - w 1) / (2 * Complex.I), w 0]
  map_add' w w' := by
    ext a
    fin_cases a <;> simp <;> ring
  map_smul' c w := by
    ext a
    fin_cases a <;> simp <;> ring
theorem pauliCoeff_eq_pauliCoeffLinear {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a X = pauliCoeffLinear (Coordinates.ComplexCoordinates.matrixEquiv X) a := by
  have h0 : Coordinates.ComplexCoordinates.matrixEquiv X 0 = X 0 0 := rfl
  have h1 : Coordinates.ComplexCoordinates.matrixEquiv X 1 = X 0 1 := rfl
  have h2 : Coordinates.ComplexCoordinates.matrixEquiv X 2 = X 1 0 := rfl
  simp only [pauliCoeff, dif_pos hX, pauliCoeffLinear, LinearMap.coe_mk, AddHom.coe_mk, h0, h1,
    h2]
  fin_cases a <;> simp [OneLoop.pauliCoordinateEquiv]
theorem complexFaceTerm_congr {V V' : Edge L n k j → Matrices.ComplexMatrix2}
    {p : Face L n k j}
    (h : ∀ b ∈ faceEdges p, V b = V' b ∧ V b.opposite = V' b.opposite) :
    complexFaceTerm V p = complexFaceTerm V' p := by
  simp only [complexFaceTerm, PeriodicLattice.plaquetteEnergy,
    PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil]
  rw [(h _ (by simp [faceEdges])).1, (h _ (by simp [faceEdges])).1,
    (h _ (by simp [faceEdges])).2, (h _ (by simp [faceEdges])).2]
theorem gaugeTransform_opposite {u : Vertex L n k j → Matrices.ComplexMatrix2}
    {V : Edge L n k j → Matrices.ComplexMatrix2}
    (hu : ∀ x, (u x).det = 1) {b : Edge L n k j} (hV : V b.opposite = (V b)⁻¹) :
    PeriodicLattice.gaugeTransform u V b.opposite =
      (PeriodicLattice.gaugeTransform u V b)⁻¹ := by
  change u b.target * V b.opposite * (u b.source)⁻¹ = (u b.source * V b * (u b.target)⁻¹)⁻¹
  rw [hV, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ (by simp [hu]), mul_assoc]
theorem extendOddly_mem_complexEdgeForms (hL : 1 < L) (hn : 0 < n) (hj : j ≤ k)
    {f : Edge L n k j → Matrices.ComplexMatrix2}
    (hf : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ Matrices.ComplexMatrix2.traceless) :
    extendOddly f ∈ complexEdgeForms L n k j := by
  have hdepth : -(n : ℤ) < (k : ℤ) - (j : ℤ) := by omega
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [extendOddly, if_pos hb]
    exact hf b hb
  · have hrr : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
    by_cases hb : b.IsPositivelyOriented
    · have hr : ¬ b.opposite.IsPositivelyOriented :=
        PeriodicLattice.Bond.opposite_not_isPositivelyOriented hL hdepth hb
      simp only [extendOddly, if_neg hr, if_pos hb, hrr]
    · have hr : b.opposite.IsPositivelyOriented :=
        PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      simp only [extendOddly, if_pos hr, if_neg hb, neg_neg]
theorem conjugateBy_mem_traceless {V A : Matrices.ComplexMatrix2} (hV : V.det = 1)
    (hA : A ∈ Matrices.ComplexMatrix2.traceless) :
    Matrices.ComplexMatrix2.conjugateBy V A ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
theorem lie_mem_traceless (X Y : Matrices.ComplexMatrix2) :
    ⁅X, Y⁆ ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TripleExpExpansion.lie_mem_traceless <;> assumption
def remainderEdgeForm (Ω : Finset (Face L n k j)) (U : Edge L n k j → Matrices.ComplexMatrix2)
    (l : Vertex L n k j → Matrices.ComplexMatrix2) (B : Edge L n k j → Matrices.ComplexMatrix2)
    (z : Coordinates.ComplexCoordinates 2) :
    Edge L n k j → Matrices.ComplexMatrix2 :=
  open Classical in
  extendOddly fun b => if b ∈ faceSetEdges Ω then expansionRemainder U l B (z 0) (z 1) b else 0
def surfaceEdgeForm (Ω : Finset (Face L n k j)) (U : Edge L n k j → Matrices.ComplexMatrix2)
    (l : Vertex L n k j → Matrices.ComplexMatrix2) (B : Edge L n k j → Matrices.ComplexMatrix2)
    (s t : ℂ) : Edge L n k j → Matrices.ComplexMatrix2 :=
  s • B + (-t) • covDiff U l + (s * t) • levelBracketTerm U l B +
    t ^ 2 • extendOddly (gaugeQuadTerm U l) + remainderEdgeForm Ω U l B ![s, t]
theorem surfaceEdgeForm_apply_of_mem (Ω : Finset (Face L n k j))
    (U : Edge L n k j → Matrices.ComplexMatrix2)
    (l : Vertex L n k j → Matrices.ComplexMatrix2) (B : Edge L n k j → Matrices.ComplexMatrix2)
    (s t : ℂ) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) (hm : b ∈ faceSetEdges Ω) :
    surfaceEdgeForm Ω U l B s t b =
      principalExponent U l B s t b + expansionRemainder U l B s t b := by
  have h1 : extendOddly (gaugeQuadTerm U l) b = gaugeQuadTerm U l b := by
    simp only [extendOddly, if_pos hb]
  have h2 : remainderEdgeForm Ω U l B ![s, t] b = expansionRemainder U l B s t b := by
    simp only [remainderEdgeForm, extendOddly, if_pos hb, if_pos hm]
    rfl
  simp only [surfaceEdgeForm, principalExponent, Pi.add_apply, Pi.smul_apply, h1, h2, neg_smul,
    Pi.neg_apply, sub_eq_add_neg]
end GaugeDirectionHessian
open GaugeDirectionHessian FiniteFaceDerivatives in
theorem hessianGaugeDirectionFiniteSide_holds
    (hD : FiniteFaceDerivatives.ReadOnFiniteFaceSets)
    (hM : SurfaceMixedDerivative.MixedDerivAlongSurface)
    (hT : VanishingOrderThreeIffCubicBound)
    (hE : TwistExpansionOnTorus.Claim)
    (hG : GaugeConditionsFiniteSide)
    (hF : FaceEdgeFinsets.FacesAndEdgesFinite)
    (hH : Coordinates.ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement) :
    HessianGaugeDirectionFiniteSide := by
  classical
  intro L n k j hL hn hj U l B hU hl hB
  have hL' : 1 < L := lt_of_lt_of_le (by norm_num) hL.2
  have hfin := (hF L hL k j hj).1 n hn
  have hpos : ∀ p : Face L n k j, ∀ b ∈ faceEdges p, b.IsPositivelyOriented := hfin.1.2
  have hfinU : (univ : Set (Face L n k j)).Finite := hfin.2.2.2.1
  set Ω : Finset (Face L n k j) := hfinU.toFinset with hΩdef
  have hΩmem : ∀ p : Face L n k j, p ∈ Ω := fun p => by simp [hΩdef]
  have hne : Ω.Nonempty := ⟨FaceEdgeFinsets.baseFace L n k j, hΩmem _⟩
  obtain ⟨hlin, hΩ⟩ := hD L n k j hL hn hj Ω hne
  obtain ⟨Φ, hΦa, hΦ, hder⟩ := hΩ U hU
  have hbmem : ∀ p : Face L n k j, ∀ b ∈ faceEdges p, b ∈ faceSetEdges Ω := by
    intro p b hb
    simp only [faceSetEdges, Finset.mem_biUnion, List.mem_toFinset]
    exact ⟨p, hΩmem p, hb⟩
  have hbpos : ∀ b ∈ faceSetEdges Ω, b.IsPositivelyOriented := by
    intro b hb
    simp only [faceSetEdges, Finset.mem_biUnion, List.mem_toFinset] at hb
    obtain ⟨p, -, hp⟩ := hb
    exact hpos p b hp
  have hdet : ∀ b, (U b).det = 1 := fun b => hU.1 b (mem_univ b)
  have hDl : covDiff U l ∈ complexEdgeForms L n k j :=
    extendOddly_mem_complexEdgeForms hL' hn hj fun b _ =>
      Matrices.ComplexMatrix2.traceless.sub_mem
        (conjugateBy_mem_traceless (hdet b) (hl b.target)) (hl b.source)
  have hcT : levelBracketTerm U l B ∈ complexEdgeForms L n k j :=
    extendOddly_mem_complexEdgeForms hL' hn hj fun b _ =>
      Matrices.ComplexMatrix2.traceless.smul_mem _ (lie_mem_traceless _ _)
  have hξ : extendOddly (gaugeQuadTerm U l) ∈ complexEdgeForms L n k j :=
    extendOddly_mem_complexEdgeForms hL' hn hj fun b _ =>
      Matrices.ComplexMatrix2.traceless.neg_mem
        (Matrices.ComplexMatrix2.traceless.smul_mem _ (lie_mem_traceless _ _))
  obtain ⟨hexpS, hexpT, hexp⟩ := (hE L n k j hL hn hj U l B hU hl hB)
  have hexpΩ : ∀ b : faceSetEdges Ω,
      HasLocalExpExpansion (fun s t => twistedField U l B s t b.1) (U b.1)
        (fun s t => principalExponent U l B s t b.1) := fun b => hexp b.1 (hbpos b.1 b.2)
  simp only [HasLocalExpExpansion] at hexpΩ
  choose O hOopen h0 hOval hOhol hO3 using hexpΩ
  set W : Set (Coordinates.ComplexCoordinates 2) := ⋂ b, O b with hWdef
  have hWopen : IsOpen W := isOpen_iInter_of_finite hOopen
  have h0W : (0 : Coordinates.ComplexCoordinates 2) ∈ W := mem_iInter.2 h0
  have hWO : ∀ b, W ⊆ O b := fun b => iInter_subset _ b
  have hbd : ∀ b : faceSetEdges Ω, ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ z : Coordinates.ComplexCoordinates 2, ‖z‖ < δ →
      ‖Coordinates.ComplexCoordinates.matrixEquiv (expansionRemainder U l B (z 0) (z 1) b.1)‖ ≤
        C * ‖z‖ ^ 3 :=
    fun b => (hT (O b) _ (h0 b) (hOhol b)).1 (hO3 b)
  choose C δ hC hδ hbound using hbd
  let ℓ : Coordinates.ComplexCoordinates 4 →L[ℂ] (Fin 3 → ℂ) :=
    LinearMap.toContinuousLinearMap pauliCoeffLinear
  have hev : ∀ᶠ z in 𝓝 (0 : Coordinates.ComplexCoordinates 2), z ∈ W ∧ ∀ b : faceSetEdges Ω,
      ‖Coordinates.ComplexCoordinates.matrixEquiv (expansionRemainder U l B (z 0) (z 1) b.1)‖ ≤
        C b * ‖z‖ ^ 3 := by
    refine (show ∀ᶠ z in 𝓝 (0 : Coordinates.ComplexCoordinates 2), z ∈ W from
      hWopen.mem_nhds h0W).and (eventually_all.2 fun b => ?_)
    filter_upwards [Metric.ball_mem_nhds (0 : Coordinates.ComplexCoordinates 2) (hδ b)] with z hz
    exact hbound b z (by simpa using hz)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  let r : Coordinates.ComplexCoordinates 2 → (Fin 3 × faceSetEdges Ω → ℂ) :=
    fun z => faceSetCoords Ω (remainderEdgeForm Ω U l B z)
  have hrem : ∀ z ∈ W, ∀ b : faceSetEdges Ω,
      expansionRemainder U l B (z 0) (z 1) b.1 ∈ Matrices.ComplexMatrix2.traceless :=
    fun z hz b => (hOval b z (hWO b hz)).2.2
  have hr_eq : ∀ z ∈ W, ∀ ι : Fin 3 × faceSetEdges Ω, r z ι =
      ℓ (Coordinates.ComplexCoordinates.matrixEquiv
        (expansionRemainder U l B (z 0) (z 1) ι.2.1)) ι.1 := by
    intro z hz ι
    have hv : remainderEdgeForm Ω U l B z ι.2.1 = expansionRemainder U l B (z 0) (z 1) ι.2.1 := by
      simp only [remainderEdgeForm, extendOddly, if_pos (hbpos _ ι.2.2), if_pos ι.2.2]
    change pauliCoeff ι.1 (remainderEdgeForm Ω U l B z ι.2.1) = _
    rw [hv, pauliCoeff_eq_pauliCoeffLinear (hrem z hz ι.2)]
    rfl
  have hrdiff : DifferentiableOn ℂ r W := by
    refine differentiableOn_pi.2 fun ι => ?_
    have hf : DifferentiableOn ℂ (fun z : Coordinates.ComplexCoordinates 2 =>
        Coordinates.ComplexCoordinates.matrixEquiv
          (expansionRemainder U l B (z 0) (z 1) ι.2.1)) W :=
      ((hH 2 4 (O ι.2) _ (hOopen ι.2)).1 (hOhol ι.2)).mono (hWO ι.2)
    have hg := (differentiableOn_pi.1 (ℓ.differentiable.comp_differentiableOn hf)) ι.1
    exact hg.congr fun z hz => hr_eq z hz ι
  have hrbound : ∀ z : Coordinates.ComplexCoordinates 2, ‖z‖ < ε →
      ‖r z‖ ≤ (‖ℓ‖ * ∑ b, C b) * ‖z‖ ^ 3 := by
    intro z hz
    obtain ⟨hzW, hzb⟩ := hball (y := z) (by simpa using hz)
    have hCnn : ∀ b, 0 ≤ C b := fun b => (hC b).le
    have hnn : 0 ≤ (‖ℓ‖ * ∑ b, C b) * ‖z‖ ^ 3 :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun b _ => hCnn b)) (by positivity)
    refine (pi_norm_le_iff_of_nonneg hnn).2 fun ι => ?_
    rw [hr_eq z hzW ι]
    calc _ ≤ ‖ℓ (Coordinates.ComplexCoordinates.matrixEquiv
              (expansionRemainder U l B (z 0) (z 1) ι.2.1))‖ := norm_le_pi_norm _ ι.1
      _ ≤ ‖ℓ‖ * ‖Coordinates.ComplexCoordinates.matrixEquiv
              (expansionRemainder U l B (z 0) (z 1) ι.2.1)‖ := ℓ.le_opNorm _
      _ ≤ ‖ℓ‖ * (C ι.2 * ‖z‖ ^ 3) := by gcongr; exact hzb ι.2
      _ ≤ ‖ℓ‖ * ((∑ b, C b) * ‖z‖ ^ 3) := by
          gcongr
          exact Finset.single_le_sum (fun b _ => hCnn b) (Finset.mem_univ ι.2)
      _ = _ := by ring
  have hadd : ∀ E ∈ complexEdgeForms L n k j, ∀ E' ∈ complexEdgeForms L n k j,
      faceSetCoords Ω (E + E') = faceSetCoords Ω E + faceSetCoords Ω E' := by
    intro E hE' E' hE''
    simpa using hlin E hE' E' hE'' 1 1
  have hsm : ∀ E ∈ complexEdgeForms L n k j, ∀ c : ℂ,
      faceSetCoords Ω (c • E) = c • faceSetCoords Ω E := by
    intro E hE' c
    simpa using hlin E hE' 0 (Submodule.zero_mem _) c 0
  have hsurf : ∀ s t : ℂ, (![s, t] : Coordinates.ComplexCoordinates 2) ∈ W →
      Φ (SurfaceMixedDerivative.surfaceParam
          (faceSetCoords Ω B) (-faceSetCoords Ω (covDiff U l))
          (faceSetCoords Ω (levelBracketTerm U l B))
          (faceSetCoords Ω (extendOddly (gaugeQuadTerm U l))) r s t) =
        faceSetAction Ω (PeriodicLattice.expTwist (s • B) U) := by
    intro s t hz
    have hRf : remainderEdgeForm Ω U l B ![s, t] ∈ complexEdgeForms L n k j := by
      refine extendOddly_mem_complexEdgeForms hL' hn hj fun b _ => ?_
      by_cases hm : b ∈ faceSetEdges Ω
      · rw [if_pos hm]
        exact hrem _ hz ⟨b, hm⟩
      · rw [if_neg hm]
        exact Matrices.ComplexMatrix2.traceless.zero_mem
    have m1 := (complexEdgeForms L n k j).smul_mem s hB
    have m2 := (complexEdgeForms L n k j).smul_mem (-t) hDl
    have m3 := (complexEdgeForms L n k j).smul_mem (s * t) hcT
    have m4 := (complexEdgeForms L n k j).smul_mem (t ^ 2) hξ
    have m12 := (complexEdgeForms L n k j).add_mem m1 m2
    have m123 := (complexEdgeForms L n k j).add_mem m12 m3
    have m1234 := (complexEdgeForms L n k j).add_mem m123 m4
    have hC' : surfaceEdgeForm Ω U l B s t ∈ complexEdgeForms L n k j :=
      (complexEdgeForms L n k j).add_mem m1234 hRf
    have hco : faceSetCoords Ω (surfaceEdgeForm Ω U l B s t) =
        SurfaceMixedDerivative.surfaceParam
          (faceSetCoords Ω B) (-faceSetCoords Ω (covDiff U l))
          (faceSetCoords Ω (levelBracketTerm U l B))
          (faceSetCoords Ω (extendOddly (gaugeQuadTerm U l))) r s t := by
      simp only [surfaceEdgeForm, SurfaceMixedDerivative.surfaceParam]
      rw [hadd _ m1234 _ hRf, hadd _ m123 _ m4, hadd _ m12 _ m3, hadd _ m1 _ m2, hsm _ hB,
        hsm _ hDl, hsm _ hcT, hsm _ hξ, neg_smul, smul_neg]
    rw [← hco, hΦ _ hC']
    refine Finset.sum_congr rfl fun p _ => ?_
    have hg := (hG L n k j hL hn hj).1 (PeriodicLattice.expTwist (s • B) U) (vertexExp (t • l))
      (hexpS s) (hexpT t)
    refine Eq.trans (complexFaceTerm_congr fun b hb => ?_) (hg.2 p).2
    have hbΩ := hbmem p b hb
    have hbP := hpos p b hb
    have hv := (hOval ⟨b, hbΩ⟩ _ (hWO ⟨b, hbΩ⟩ hz)).2.1
    have hw := surfaceEdgeForm_apply_of_mem Ω U l B s t hbP hbΩ
    have e1 : Matrices.ComplexMatrix2.matExp (Complex.I • surfaceEdgeForm Ω U l B s t b) * U b =
        twistedField U l B s t b := by
      rw [hw]
      exact hv.symm
    have hdepth : -(n : ℤ) < (k : ℤ) - (j : ℤ) := by omega
    have hr : ¬ b.opposite.IsPositivelyOriented :=
      PeriodicLattice.Bond.opposite_not_isPositivelyOriented hL' hdepth hbP
    have hrr : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
    have e2 : twistedField U l B s t b.opposite = (twistedField U l B s t b)⁻¹ :=
      _root_.YangMills.Construction.Tower.LeftChartAlgebra.GaugeDirectionHessian.gaugeTransform_opposite (fun x => hexpT t x) ((hexpS s).2 b (mem_univ b))
    constructor
    · simp only [PeriodicLattice.expTwist, if_pos hbP]
      exact e1
    · simp only [PeriodicLattice.expTwist, if_neg hr, hrr]
      rw [e1]
      exact e2.symm
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ < ε := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with s hs
    simpa using hs
  have hzero : SurfaceMixedDerivative.mixedDerivAtOrigin
      (fun s t => Φ (SurfaceMixedDerivative.surfaceParam
          (faceSetCoords Ω B) (-faceSetCoords Ω (covDiff U l))
          (faceSetCoords Ω (levelBracketTerm U l B))
          (faceSetCoords Ω (extendOddly (gaugeQuadTerm U l))) r s t)) = 0 := by
    unfold SurfaceMixedDerivative.mixedDerivAtOrigin
    have h1 : (fun s : ℂ => deriv (fun t : ℂ => Φ
        (SurfaceMixedDerivative.surfaceParam
          (faceSetCoords Ω B) (-faceSetCoords Ω (covDiff U l))
          (faceSetCoords Ω (levelBracketTerm U l B))
          (faceSetCoords Ω (extendOddly (gaugeQuadTerm U l))) r s t)) 0)
        =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hsmall] with s hs
      have h2 : (fun t : ℂ => Φ
          (SurfaceMixedDerivative.surfaceParam
            (faceSetCoords Ω B) (-faceSetCoords Ω (covDiff U l))
            (faceSetCoords Ω (levelBracketTerm U l B))
            (faceSetCoords Ω (extendOddly (gaugeQuadTerm U l))) r s t))
          =ᶠ[𝓝 0] fun _ => faceSetAction Ω (PeriodicLattice.expTwist (s • B) U) := by
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
  have key := hM (Fin 3 × faceSetEdges Ω → ℂ) univ Φ W r (faceSetCoords Ω B)
    (-faceSetCoords Ω (covDiff U l))
    (faceSetCoords Ω (levelBracketTerm U l B))
    (faceSetCoords Ω (extendOddly (gaugeQuadTerm U l))) (‖ℓ‖ * ∑ b, C b) ε
    isOpen_univ (mem_univ _) hΦa.differentiableOn hWopen h0W hrdiff hε hrbound
  rw [hzero] at key
  have hsub : ∀ E E' : Edge L n k j → Matrices.ComplexMatrix2,
      FaceEdgeFinsets.facesMeeting (edgeSupport E ∪ edgeSupport E') ⊆
        (Ω : Set (Face L n k j)) := fun E E' p _ => hΩmem p
  have h1 := (hder B hB _ hDl (hsub _ _)).2.2
  have h2 := (hder _ hcT _ hcT (hsub _ _)).2.1
  have hmix : SurfaceMixedDerivative.mixedDerivAtOrigin
      (fun s t => Φ (s • faceSetCoords Ω B +
        t • (-faceSetCoords Ω (covDiff U l)))) =
      -complexActionHessian U B (covDiff U l) := by
    unfold SurfaceMixedDerivative.mixedDerivAtOrigin
    have h3 : (fun s : ℂ => deriv (fun t : ℂ => Φ (s • faceSetCoords Ω B +
        t • (-faceSetCoords Ω (covDiff U l)))) 0) =
        fun s : ℂ => -deriv (fun t : ℂ => Φ (s • faceSetCoords Ω B +
          t • faceSetCoords Ω (covDiff U l))) 0 := by
      funext s
      have h4 := deriv_comp_neg (fun t : ℂ => Φ (s • faceSetCoords Ω B +
          t • faceSetCoords Ω (covDiff U l))) (0 : ℂ)
      simpa only [neg_smul, smul_neg, neg_zero] using h4
    rw [h3]
    exact h1.neg.deriv
  rw [hmix, h2.deriv] at key
  linear_combination key
end YangMills.Construction.Tower.LeftChartAlgebra
end

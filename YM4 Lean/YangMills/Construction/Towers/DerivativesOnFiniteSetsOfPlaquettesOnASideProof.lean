import YangMills.Construction.Towers.DerivativesOfAPlaquetteTermProof
import YangMills.Construction.Towers.DerivativesOnFiniteSetsOfPlaquettesOnASide
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.LeftChartAlgebra.FiniteFaceDerivatives
open FaceEdgeFinsets (facesMeeting)
section Lines
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem differentiableAt_smul_line {Φ : E → ℂ} (hΦ : AnalyticOnNhd ℂ Φ univ) (v : E) :
    DifferentiableAt ℂ (fun t : ℂ => Φ (t • v)) 0 := by
  have hd : DifferentiableAt ℂ Φ ((0 : ℂ) • v) := (hΦ _ (mem_univ _)).differentiableAt
  exact DifferentiableAt.comp (f := fun t : ℂ => t • v) (0 : ℂ) hd (by fun_prop)
theorem differentiableAt_deriv_along_line {Φ : E → ℂ} (hΦ : AnalyticOnNhd ℂ Φ univ) (v w : E) :
    DifferentiableAt ℂ (fun s : ℂ => deriv (fun t : ℂ => Φ (s • v + t • w)) 0) 0 := by
  have hderiv : ∀ s : ℂ, deriv (fun t : ℂ => Φ (s • v + t • w)) 0 = fderiv ℂ Φ (s • v) w := by
    intro s
    have hf : HasFDerivAt Φ (fderiv ℂ Φ (s • v + (0 : ℂ) • w)) (s • v + (0 : ℂ) • w) :=
      ((hΦ _ (mem_univ _)).differentiableAt).hasFDerivAt
    have hl : HasDerivAt (fun t : ℂ => s • v + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const w).const_add (s • v)
    have hc : HasDerivAt (fun t : ℂ => Φ (s • v + t • w))
        (fderiv ℂ Φ (s • v + (0 : ℂ) • w) w) 0 := hf.comp_hasDerivAt (0 : ℂ) hl
    rw [hc.deriv]
    simp
  simp_rw [hderiv]
  have han : AnalyticOnNhd ℂ (fderiv ℂ Φ) univ := hΦ.fderiv
  have hda : DifferentiableAt ℂ (fderiv ℂ Φ) ((0 : ℂ) • v) := (han _ (mem_univ _)).differentiableAt
  have hdl : DifferentiableAt ℂ (fun s : ℂ => fderiv ℂ Φ (s • v)) 0 :=
    DifferentiableAt.comp (f := fun s : ℂ => s • v) (0 : ℂ) hda (by fun_prop)
  exact hdl.clm_apply (differentiableAt_const w)
end Lines
theorem pauliCoeff_eq_coordinateEquiv {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a X = OneLoop.pauliCoordinateEquiv ⟨X, hX⟩ a := by
  simp only [pauliCoeff, dif_pos hX]
theorem sum_pauliCoeff_smul {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • Matrices.ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_linearCombination {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (hY : Y ∈ Matrices.ComplexMatrix2.traceless)
    (s t : ℂ) (a : Fin 3) :
    pauliCoeff a (s • X + t • Y) = s * pauliCoeff a X + t * pauliCoeff a Y := by
  have hZ : s • X + t • Y ∈ Matrices.ComplexMatrix2.traceless :=
    Matrices.ComplexMatrix2.traceless.add_mem (Matrices.ComplexMatrix2.traceless.smul_mem s hX)
      (Matrices.ComplexMatrix2.traceless.smul_mem t hY)
  have hsub : (⟨s • X + t • Y, hZ⟩ : Matrices.ComplexMatrix2.traceless) =
      s • ⟨X, hX⟩ + t • ⟨Y, hY⟩ := rfl
  rw [pauliCoeff_eq_coordinateEquiv hZ, pauliCoeff_eq_coordinateEquiv hX,
    pauliCoeff_eq_coordinateEquiv hY, hsub, map_add, map_smul, map_smul]
  simp
variable {L n k j : ℕ}
theorem mem_faceSetEdges {S : Finset (Face L n k j)} {f : Face L n k j} (hf : f ∈ S)
    {e : Edge L n k j} (he : e ∈ faceEdges f) : e ∈ faceSetEdges S := by
  classical
  simp only [faceSetEdges, Finset.mem_biUnion, List.mem_toFinset]
  exact ⟨f, hf, he⟩
theorem isPositivelyOriented_of_mem_faceSetEdges
    (hpos : ∀ f : Face L n k j, ∀ e ∈ faceEdges f, e.IsPositivelyOriented)
    {S : Finset (Face L n k j)} {e : Edge L n k j} (he : e ∈ faceSetEdges S) :
    e.IsPositivelyOriented := by
  classical
  simp only [faceSetEdges, Finset.mem_biUnion, List.mem_toFinset] at he
  obtain ⟨f, -, he⟩ := he
  exact hpos f e he
def twistedFaceWord (U : Edge L n k j → Matrices.ComplexMatrix2) (f : Face L n k j)
    (A : Edge L n k j → Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  Matrices.ComplexMatrix2.matExp (Complex.I • A (faceEdge f 0)) * U (faceEdge f 0) *
    (Matrices.ComplexMatrix2.matExp (Complex.I • A (faceEdge f 1)) * U (faceEdge f 1)) *
    ((U (faceEdge f 2))⁻¹ * Matrices.ComplexMatrix2.matExp (-(Complex.I • A (faceEdge f 2)))) *
    ((U (faceEdge f 3))⁻¹ * Matrices.ComplexMatrix2.matExp (-(Complex.I • A (faceEdge f 3))))
theorem faceEdge_mem_faceEdges (f : Face L n k j) (i : Fin 4) :
    faceEdge f i ∈ faceEdges f := List.getElem_mem _
theorem plaquetteHolonomy_eq_product (V : Edge L n k j → Matrices.ComplexMatrix2)
    (f : Face L n k j) :
    PeriodicLattice.plaquetteHolonomy V f = V (faceEdge f 0) * V (faceEdge f 1) *
      V (faceEdge f 2).opposite * V (faceEdge f 3).opposite := by apply _root_.YangMills.Construction.Tower.FaceTermDerivatives.plaquetteHolonomy_eq_faceEdges <;> assumption
theorem plaquetteHolonomy_expTwist
    (hopp : ∀ e : Edge L n k j, e.IsPositivelyOriented → ¬ e.opposite.IsPositivelyOriented)
    (hpos : ∀ f : Face L n k j, ∀ e ∈ faceEdges f, e.IsPositivelyOriented)
    (A U : Edge L n k j → Matrices.ComplexMatrix2) (f : Face L n k j) :
    PeriodicLattice.plaquetteHolonomy (PeriodicLattice.expTwist A U) f = twistedFaceWord U f A := by
  have hfwd : ∀ i, PeriodicLattice.expTwist A U (faceEdge f i) =
      Matrices.ComplexMatrix2.matExp (Complex.I • A (faceEdge f i)) * U (faceEdge f i) := fun i =>
    if_pos (hpos f _ (faceEdge_mem_faceEdges f i))
  have hbwd : ∀ i, PeriodicLattice.expTwist A U (faceEdge f i).opposite =
      (U (faceEdge f i))⁻¹ * Matrices.ComplexMatrix2.matExp (-(Complex.I • A (faceEdge f i))) :=
    fun i => by
      have h : PeriodicLattice.expTwist A U (faceEdge f i).opposite =
          (Matrices.ComplexMatrix2.matExp (Complex.I • A (faceEdge f i)) * U (faceEdge f i))⁻¹ :=
        if_neg (hopp _ (hpos f _ (faceEdge_mem_faceEdges f i)))
      rw [h, Matrix.mul_inv_rev, Matrices.ComplexMatrix2.matExp, Matrices.ComplexMatrix2.matExp,
        Matrix.exp_neg]
  rw [plaquetteHolonomy_eq_product, hfwd, hfwd, hbwd, hbwd]
  rfl
def formOfCoords (S : Finset (Face L n k j)) (c : Fin 3 × faceSetEdges S → ℂ)
    (e : Edge L n k j) : Matrices.ComplexMatrix2 :=
  open Classical in if h : e ∈ faceSetEdges S then ofPauliCoeffs c ⟨e, h⟩ else 0
theorem formOfCoords_faceSetCoords {S : Finset (Face L n k j)}
    {C : Edge L n k j → Matrices.ComplexMatrix2} {e : Edge L n k j} (he : e ∈ faceSetEdges S)
    (hC : C e ∈ Matrices.ComplexMatrix2.traceless) : formOfCoords S (faceSetCoords S C) e = C e := by
  rw [formOfCoords, dif_pos he]
  exact sum_pauliCoeff_smul hC
theorem analyticAt_formOfCoords (S : Finset (Face L n k j)) (e : Edge L n k j)
    (c : Fin 3 × faceSetEdges S → ℂ) :
    AnalyticAt ℂ (fun c' => formOfCoords S c' e) c := by
  classical
  by_cases h : e ∈ faceSetEdges S
  · simp only [formOfCoords, dif_pos h, ofPauliCoeffs]
    refine Finset.analyticAt_fun_sum _ fun a _ => ?_
    have hproj : AnalyticAt ℂ (fun c' : Fin 3 × faceSetEdges S → ℂ => c' (a, ⟨e, h⟩)) c :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 × faceSetEdges S => ℂ)
        (a, ⟨e, h⟩)).analyticAt c
    exact hproj.smul analyticAt_const
  · simp only [formOfCoords, dif_neg h]
    exact analyticAt_const
theorem analyticAt_matExp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : E → Matrices.ComplexMatrix2} {x : E} (hg : AnalyticAt ℂ g x) :
    AnalyticAt ℂ (fun y => Matrices.ComplexMatrix2.matExp (g y)) x :=
  AnalyticAt.comp (g := NormedSpace.exp) (NormedSpace.exp_analytic _) hg
def coordAction (S : Finset (Face L n k j)) (U : Edge L n k j → Matrices.ComplexMatrix2)
    (c : Fin 3 × faceSetEdges S → ℂ) : ℂ :=
  ∑ f ∈ S, (1 - (1 / 2) * Matrices.ComplexMatrix2.fullTrace (twistedFaceWord U f (formOfCoords S c)))
theorem analyticAt_twistedFaceWord (S : Finset (Face L n k j))
    (U : Edge L n k j → Matrices.ComplexMatrix2) (f : Face L n k j)
    (c : Fin 3 × faceSetEdges S → ℂ) :
    AnalyticAt ℂ (fun c' => twistedFaceWord U f (formOfCoords S c')) c := by
  have hI : ∀ i, AnalyticAt ℂ
      (fun c' => Complex.I • formOfCoords S c' (faceEdge f i)) c := fun i =>
    AnalyticAt.const_smul (c := Complex.I) (analyticAt_formOfCoords S _ c)
  have hpos : ∀ i, AnalyticAt ℂ
      (fun c' => Matrices.ComplexMatrix2.matExp (Complex.I • formOfCoords S c' (faceEdge f i))) c :=
    fun i => analyticAt_matExp (hI i)
  have hneg : ∀ i, AnalyticAt ℂ
      (fun c' => Matrices.ComplexMatrix2.matExp (-(Complex.I • formOfCoords S c' (faceEdge f i)))) c :=
    fun i => analyticAt_matExp (hI i).neg
  exact ((((hpos 0).mul analyticAt_const).mul ((hpos 1).mul analyticAt_const)).mul
    (analyticAt_const.mul (hneg 2))).mul (analyticAt_const.mul (hneg 3))
theorem analyticOnNhd_coordAction (S : Finset (Face L n k j))
    (U : Edge L n k j → Matrices.ComplexMatrix2) :
    AnalyticOnNhd ℂ (coordAction S U) univ := by
  intro c _
  refine Finset.analyticAt_fun_sum _ fun f _ => ?_
  have htr : AnalyticAt ℂ
      (fun c' => Matrices.ComplexMatrix2.fullTrace (twistedFaceWord U f (formOfCoords S c'))) c := by
    have h0 : AnalyticAt ℂ (fun M : Matrices.ComplexMatrix2 => Matrices.ComplexMatrix2.fullTrace M)
        (twistedFaceWord U f (formOfCoords S c)) :=
      (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)).analyticAt _
    exact AnalyticAt.comp (g := fun M : Matrices.ComplexMatrix2 =>
      Matrices.ComplexMatrix2.fullTrace M) h0 (analyticAt_twistedFaceWord S U f c)
  exact analyticAt_const.sub (analyticAt_const.mul htr)
theorem coordAction_faceSetCoords
    (hopp : ∀ e : Edge L n k j, e.IsPositivelyOriented → ¬ e.opposite.IsPositivelyOriented)
    (hpos : ∀ f : Face L n k j, ∀ e ∈ faceEdges f, e.IsPositivelyOriented)
    (S : Finset (Face L n k j)) (U : Edge L n k j → Matrices.ComplexMatrix2)
    {C : Edge L n k j → Matrices.ComplexMatrix2} (hC : C ∈ complexEdgeForms L n k j) :
    coordAction S U (faceSetCoords S C) = faceSetAction S (PeriodicLattice.expTwist C U) := by
  refine Finset.sum_congr rfl fun f hf => ?_
  have hval : ∀ i, formOfCoords S (faceSetCoords S C) (faceEdge f i) = C (faceEdge f i) :=
    fun i => formOfCoords_faceSetCoords (mem_faceSetEdges hf (faceEdge_mem_faceEdges f i))
      (hC.1 _ (hpos f _ (faceEdge_mem_faceEdges f i)))
  show _ = 1 - (1 / 2) * Matrices.ComplexMatrix2.fullTrace
    (PeriodicLattice.plaquetteHolonomy (PeriodicLattice.expTwist C U) f)
  rw [plaquetteHolonomy_expTwist hopp hpos]
  simp only [twistedFaceWord, hval]
theorem faceSetCoords_linearCombination
    (hpos : ∀ f : Face L n k j, ∀ e ∈ faceEdges f, e.IsPositivelyOriented)
    (S : Finset (Face L n k j)) {C C' : Edge L n k j → Matrices.ComplexMatrix2}
    (hC : C ∈ complexEdgeForms L n k j) (hC' : C' ∈ complexEdgeForms L n k j) (s t : ℂ) :
    faceSetCoords S (s • C + t • C') = s • faceSetCoords S C + t • faceSetCoords S C' := by
  funext ι
  obtain ⟨a, e⟩ := ι
  have he := isPositivelyOriented_of_mem_faceSetEdges hpos e.2
  exact pauliCoeff_linearCombination (hC.1 _ he) (hC'.1 _ he) s t a
theorem complexAction_sub_faceSetAction (hfin : (univ : Set (Face L n k j)).Finite)
    (S : Finset (Face L n k j)) {V W : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ f, f ∉ S → complexFaceTerm V f = complexFaceTerm W f) :
    complexAction V - faceSetAction S V = complexAction W - faceSetAction S W := by
  classical
  have : Finite (Face L n k j) := Set.finite_univ_iff.mp hfin
  let _ := Fintype.ofFinite (Face L n k j)
  have hsplit : ∀ V' : Edge L n k j → Matrices.ComplexMatrix2,
      complexAction V' - faceSetAction S V' = ∑ f ∈ Sᶜ, complexFaceTerm V' f := fun V' => by
    rw [complexAction, finsum_eq_sum_of_fintype, ← Finset.sum_add_sum_compl S, faceSetAction]
    ring
  rw [hsplit, hsplit]
  exact Finset.sum_congr rfl fun f hf => h f (Finset.mem_compl.mp hf)
theorem holdsOnTorus
    (hopp : ∀ e : Edge L n k j, e.IsPositivelyOriented → ¬ e.opposite.IsPositivelyOriented)
    (hpos : ∀ f : Face L n k j, ∀ e ∈ faceEdges f, e.IsPositivelyOriented)
    (hfin : (univ : Set (Face L n k j)).Finite) : HoldsOnTorus L n k j := by
  intro S _
  refine ⟨fun C hC C' hC' s t => faceSetCoords_linearCombination hpos S hC hC' s t, fun U _ => ?_⟩
  have hΦ := analyticOnNhd_coordAction S U
  refine ⟨coordAction S U, hΦ, fun C hC => coordAction_faceSetCoords hopp hpos S U hC, ?_⟩
  intro B hB B' hB' hsub
  set x := faceSetCoords S B with hx
  set x' := faceSetCoords S B' with hx'
  have hmem : ∀ s t : ℂ, s • B + t • B' ∈ complexEdgeForms L n k j := fun s t =>
    Submodule.add_mem _ (Submodule.smul_mem _ s hB) (Submodule.smul_mem _ t hB')
  have hF : ∀ s t : ℂ, faceSetAction S (PeriodicLattice.expTwist (s • B + t • B') U) =
      coordAction S U (s • x + t • x') := fun s t => by
    rw [hx, hx', ← faceSetCoords_linearCombination hpos S hB hB' s t,
      coordAction_faceSetCoords hopp hpos S U (hmem s t)]
  have hoff : ∀ s t : ℂ, ∀ f, f ∉ S →
      complexFaceTerm (PeriodicLattice.expTwist (s • B + t • B') U) f =
        complexFaceTerm
          (PeriodicLattice.expTwist (0 : Edge L n k j → Matrices.ComplexMatrix2) U) f := by
    intro s t f hf
    have hzero : ∀ e ∈ faceEdges f, (s • B + t • B') e = 0 := by
      intro e he
      have hepos := hpos f e he
      have hB0 : B e = 0 := by
        by_contra hne
        exact hf (hsub ⟨e, Or.inl ⟨hepos, hne⟩, he⟩)
      have hB0' : B' e = 0 := by
        by_contra hne
        exact hf (hsub ⟨e, Or.inr ⟨hepos, hne⟩, he⟩)
      simp [hB0, hB0']
    have hword : twistedFaceWord U f (s • B + t • B') =
        twistedFaceWord U f (0 : Edge L n k j → Matrices.ComplexMatrix2) := by
      simp only [twistedFaceWord, hzero _ (faceEdge_mem_faceEdges f _), Pi.zero_apply]
    show 1 - (1 / 2) * Matrices.ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy _ f) =
      1 - (1 / 2) * Matrices.ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy _ f)
    rw [plaquetteHolonomy_expTwist hopp hpos, plaquetteHolonomy_expTwist hopp hpos, hword]
  set K : ℂ := complexAction (PeriodicLattice.expTwist (0 : Edge L n k j → Matrices.ComplexMatrix2) U) -
    faceSetAction S (PeriodicLattice.expTwist (0 : Edge L n k j → Matrices.ComplexMatrix2) U) with hK
  have hA : ∀ s t : ℂ, complexAction (PeriodicLattice.expTwist (s • B + t • B') U) =
      coordAction S U (s • x + t • x') + K := fun s t => by
    have h := complexAction_sub_faceSetAction hfin S (hoff s t)
    rw [← hF, hK, ← h]
    ring
  have hF1 : ∀ t : ℂ, faceSetAction S (PeriodicLattice.expTwist (t • B) U) =
      coordAction S U (t • x) := fun t => by
    simpa using hF t 0
  have hA1 : ∀ t : ℂ, complexAction (PeriodicLattice.expTwist (t • B) U) =
      coordAction S U (t • x) + K := fun t => by
    simpa using hA t 0
  have hD : complexActionDeriv U B = deriv (fun t : ℂ => coordAction S U (t • x)) 0 := by
    show deriv (fun t : ℂ => complexAction
      (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • B) U)) 0 = _
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hA1]
    simp
  have hD' : complexActionHessian U B B' =
      deriv (fun s : ℂ => deriv (fun t : ℂ => coordAction S U (s • x + t • x')) 0) 0 := by
    show deriv (fun s : ℂ => deriv (fun t : ℂ => complexAction
      (PeriodicLattice.expTwist (algebraMap ℂ ℂ s • B + algebraMap ℂ ℂ t • B') U)) 0) 0 = _
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hA]
    simp
  have h1 := (differentiableAt_smul_line hΦ x).hasDerivAt
  have h2 := (differentiableAt_deriv_along_line hΦ x x').hasDerivAt
  rw [hD, hD']
  refine ⟨⟨?_, ?_⟩, ⟨h1, h2⟩⟩
  · simpa only [hF1] using h1
  · simpa only [hF] using h2
theorem readOnFiniteFaceSets (hF : FaceEdgeFinsets.FacesAndEdgesFinite) :
    ReadOnFiniteFaceSets := by
  intro L n k j hL hn hj
  obtain ⟨⟨-, hpos⟩, -, -, hfin, -⟩ := (hF L hL k j hj).1 n hn
  refine holdsOnTorus (fun e he hr => ?_) hpos hfin
  rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (by have := hL.2; omega)
    (by show -(n : ℤ) < (k : ℤ) - (j : ℤ); omega) e with ⟨-, h'⟩ | ⟨-, h⟩
  · exact h' hr
  · exact h he
end YangMills.Construction.Tower.LeftChartAlgebra.FiniteFaceDerivatives
end

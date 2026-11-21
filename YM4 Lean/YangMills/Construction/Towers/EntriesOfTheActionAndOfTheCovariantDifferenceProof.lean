import YangMills.Construction.Towers.ConfigurationsNearOneHaveSmallIteratesProof
import YangMills.Construction.Towers.EntriesOfTheActionAndOfTheCovariantDifference
import YangMills.Construction.Towers.SecondDifferentialOfAFieldIsLocalWithEntireKernelsProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.FieldValueFunctions.LocalComponents
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.LocalKernels (FieldIdx FieldComponent)
open YangMills.Construction.Tower.FaceEdgeFinsets.Unbounded (facesMeeting)
open YangMills.Construction.Tower.FullSpace.ActionDerivsOnFiniteFaces (actionAtExpTwist)
section EvaluationMaps
variable {F : PeriodicData} {S : Set F.Carrier} {l : ℕ}
theorem fieldExtend_apply_equiv (e : Fin l ≃ S) (z : Coordinates.ComplexCoordinates l) (j : Fin l) :
    fieldExtend e z ((e j : S) : F.Carrier) = z j := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.fieldExtend_apply <;> assumption
theorem contDiff_fieldExtend (e : Fin l ≃ S) (κ : F.Carrier) :
    ContDiff ℂ ∞ (fun z : Coordinates.ComplexCoordinates l => fieldExtend e z κ) := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldHessianEntries.contDiff_fieldExtend <;> assumption
theorem holomorphicInValuesBelow_of_entire (hS : S.Finite) {g : (F.Carrier → ℂ) → ℂ}
    (hdep : ∀ ζ ζ' : F.Carrier → ℂ, (∀ κ ∈ S, ζ κ = ζ' κ) → g ζ = g ζ')
    (hent : ∀ (l : ℕ) (e : Fin l ≃ S),
      Differentiable ℂ fun z : Coordinates.ComplexCoordinates l => g (fieldExtend e z))
    (ρ : ℝ) : HolomorphicInValuesBelow F ρ S g := by
  have := hS.to_subtype
  let e : Fin (Nat.card S) ≃ S := (Finite.equivFin S).symm
  have hd := hent _ e
  refine ⟨Nat.card S, e, fun z => g (fieldExtend e z), ⟨?_, ?_, ?_⟩, ?_⟩
  · have h : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk
        (0 : Coordinates.ComplexCoordinates (Nat.card S)) ρ = ⋂ j, {z | ‖z j‖ < ρ} := by
      ext z
      simp only [Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk, Set.mem_ofPred_eq,
        mem_iInter, Pi.zero_apply, sub_zero]
    rw [h]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt (continuous_norm.comp (continuous_apply j)) continuous_const
  · exact (continuous_pi fun _ => hd.continuous).continuousOn
  · intro a _ j
    refine Eventually.of_forall fun ζ => differentiableAt_pi.2 fun _ => ?_
    have hline : DifferentiableAt ℂ
        (fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ζ :=
      (differentiableAt_const _).add (differentiableAt_id.smul_const _)
    exact (hd _).comp ζ hline
  · intro ζ _
    refine hdep _ _ fun κ hκ => ?_
    obtain ⟨j, hj⟩ := e.surjective ⟨κ, hκ⟩
    have hk : κ = ((e j : S) : F.Carrier) := by rw [hj]
    rw [hk, fieldExtend_apply_equiv]
    rfl
end EvaluationMaps
section Partial
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem contDiff_deriv_snd_zero {H : E × ℂ → ℂ} (hH : ContDiff ℂ ∞ H) :
    ContDiff ℂ ∞ (fun x : E => deriv (fun t : ℂ => H (x, t)) 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldHessianEntries.contDiff_deriv_snd_at_zero <;> assumption
end Partial
theorem contDiff_matExp :
    ContDiff ℂ ∞ (fun Z : Matrices.ComplexMatrix2 => Matrices.ComplexMatrix2.matExp Z) :=
  contDiff_iff_contDiffAt.2 fun Z => (NormedSpace.exp_analytic (𝕂 := ℂ) Z).contDiffAt
section Lattice
variable {L k : ℕ}
theorem forwardFrom_isPositivelyOriented {a : ℝ} (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem meshAt_pos (hL : 0 < L) : 0 < meshAt L k 0 :=
  zpow_pos (by exact_mod_cast hL) _
theorem opposite_isPositivelyOriented_iff {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.link_opposite_positive_iff <;> assumption
def boundaryLink (p : Face L k 0) : Fin 4 → Edge L k 0 :=
  ![InfiniteLattice.Link.forwardFrom p.corner p.lowAxis,
    InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep _ p.lowAxis) p.highAxis,
    InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep _ p.highAxis) p.lowAxis,
    InfiniteLattice.Link.forwardFrom p.corner p.highAxis]
theorem boundaryLink_mem (p : Face L k 0) (i : Fin 4) : boundaryLink p i ∈ faceEdges p := by
  fin_cases i <;> simp [boundaryLink, faceEdges]
theorem boundaryLink_isPositivelyOriented (p : Face L k 0) (i : Fin 4) :
    (boundaryLink p i).IsPositivelyOriented := by
  fin_cases i <;> simp [boundaryLink, forwardFrom_isPositivelyOriented]
theorem exists_face_of_isPositivelyOriented {c : Edge L k 0} (hc : c.IsPositivelyOriented) :
    ∃ p : Face L k 0, c ∈ faceEdges p := by
  obtain ⟨x, κ, rfl⟩ := InfiniteLattice.mem_positiveLinks_iff.2 hc
  by_cases h : κ = 3
  · subst h
    exact ⟨⟨x, 0, 3, by decide⟩, by simp [faceEdges]⟩
  · exact ⟨⟨x, κ, 3, lt_of_le_of_ne (Fin.le_last κ) h⟩, by simp [faceEdges]⟩
end Lattice
section Forms
variable {L k : ℕ}
theorem pauliFamily_mem_traceless (a : Fin 3) :
    Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem extendOddly_mem (hL : 0 < L) {g : Edge L k 0 → Matrices.ComplexMatrix2}
    (hg : ∀ c : Edge L k 0, c.IsPositivelyOriented → g c ∈ Matrices.ComplexMatrix2.traceless) :
    extendOddly g ∈ complexEdgeForms (meshAt L k 0) := by
  have hiff := opposite_isPositivelyOriented_iff (meshAt_pos (k := k) hL)
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · have e : extendOddly g b = g b := if_pos hb
    rw [e]
    exact hg b hb
  · by_cases hb : b.IsPositivelyOriented
    · have h' : ¬ b.opposite.IsPositivelyOriented := fun h => (hiff b).1 h hb
      have e : extendOddly g b = g b := if_pos hb
      have e' : extendOddly g b.opposite = -g b.opposite.opposite := if_neg h'
      rw [e, e', InfiniteLattice.Link.opposite_opposite]
    · have h' : b.opposite.IsPositivelyOriented := (hiff b).2 hb
      have e : extendOddly g b = -g b.opposite := if_neg hb
      have e' : extendOddly g b.opposite = g b.opposite := if_pos h'
      rw [e, e', neg_neg]
theorem backgroundOfCoeffs_apply (hL : 0 < L) (f : FieldIdx L k hL → ℂ) {c : Edge L k 0}
    (hc : c.IsPositivelyOriented) :
    backgroundOfCoeffs hL f c =
      ∑ a, f ⟨.background, (a, ⟨c, hc⟩)⟩ • Matrices.ComplexMatrix2.pauliFamily a := by
  classical
  simp [backgroundOfCoeffs, edgePauliCoordinates, extendOddly, hc, ofPauliCoeffs]
  rfl
theorem backgroundOfCoeffs_mem (hL : 0 < L) (f : FieldIdx L k hL → ℂ) :
    backgroundOfCoeffs hL f ∈ complexEdgeForms (meshAt L k 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.SmallIterates.backgroundOfCoeffs_mem <;> assumption
theorem backgroundOfCoeffs_congr (hL : 0 < L) {f f' : FieldIdx L k hL → ℂ} {c : Edge L k 0}
    (hc : c.IsPositivelyOriented)
    (h : ∀ a : Fin 3, f ⟨.background, (a, ⟨c, hc⟩)⟩ = f' ⟨.background, (a, ⟨c, hc⟩)⟩) :
    backgroundOfCoeffs hL f c = backgroundOfCoeffs hL f' c := by
  simp only [backgroundOfCoeffs_apply hL _ hc, h]
theorem contDiff_backgroundOfCoeffs (hL : 0 < L) {S : Set (fieldPeriodicData L k hL).Carrier} {l : ℕ}
    (e : Fin l ≃ S) {c : Edge L k 0} (hc : c.IsPositivelyOriented) :
    ContDiff ℂ ∞
      (fun z : Coordinates.ComplexCoordinates l => backgroundOfCoeffs hL (fieldExtend e z) c) := by
  simp only [backgroundOfCoeffs_apply hL _ hc]
  exact ContDiff.sum fun a _ => (contDiff_fieldExtend e _).smul contDiff_const
theorem backgroundCoords_finite (hL : 0 < L) {T : Set (Edge L k 0)} (hT : T.Finite) :
    (backgroundCoords L k hL T).Finite := by
  have hW : ((Set.univ : Set (Fin 3)) ×ˢ
      ((fun b : PositiveEdge (meshAt L k 0) => b.1) ⁻¹' T)).Finite :=
    Set.finite_univ.prod (hT.preimage Subtype.val_injective.injOn)
  refine (hW.image fun ι => (⟨.background, ι⟩ : FieldIdx L k hL)).subset ?_
  rintro κ ⟨a, b, hb, rfl⟩
  exact ⟨(a, b), ⟨Set.mem_univ _, hb⟩, rfl⟩
theorem mem_backgroundCoords (hL : 0 < L) {T : Set (Edge L k 0)} {c : Edge L k 0}
    (hc : c.IsPositivelyOriented) (hT : c ∈ T) (a : Fin 3) :
    (⟨.background, (a, ⟨c, hc⟩)⟩ : FieldIdx L k hL) ∈ backgroundCoords L k hL T :=
  ⟨a, ⟨c, hc⟩, hT, rfl⟩
end Forms
section Term
variable {L k : ℕ}
abbrev expI (Y : Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  Matrices.ComplexMatrix2.matExp (Complex.I • Y)
abbrev expNegI (Y : Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  Matrices.ComplexMatrix2.matExp (-(Complex.I • Y))
def twistedFaceTerm (X A : Edge L k 0 → Matrices.ComplexMatrix2) (p : Face L k 0) : ℂ :=
  1 - (1 / 2) * Matrices.ComplexMatrix2.fullTrace
    (expI (X (boundaryLink p 0)) * expI (A (boundaryLink p 0)) *
    (expI (X (boundaryLink p 1)) * expI (A (boundaryLink p 1))) *
    (expNegI (A (boundaryLink p 2)) * expNegI (X (boundaryLink p 2))) *
    (expNegI (A (boundaryLink p 3)) * expNegI (X (boundaryLink p 3))))
theorem inv_expI_mul (Y V : Matrices.ComplexMatrix2) :
    (Matrices.ComplexMatrix2.matExp (Complex.I • Y) * V)⁻¹ =
      V⁻¹ * Matrices.ComplexMatrix2.matExp (-(Complex.I • Y)) := by apply _root_.YangMills.Construction.Tower.HessianKernel.inv_matExp_smul_mul <;> assumption
theorem expForm_of_isPositivelyOriented (A : Edge L k 0 → Matrices.ComplexMatrix2) {b : Edge L k 0}
    (hb : b.IsPositivelyOriented) : expForm A b = expI (A b) := by apply _root_.YangMills.Construction.Tower.FullSpace.SmallIterates.expForm_of_pos <;> assumption
theorem complexFaceTerm_expTwist
    (hrev : ∀ b : Edge L k 0, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (X A : Edge L k 0 → Matrices.ComplexMatrix2) (p : Face L k 0) :
    complexFaceTerm (expTwist X (expForm A)) p = twistedFaceTerm X A p := by
  have e : ∀ b : Edge L k 0, b.IsPositivelyOriented →
      expTwist X (expForm A) b = expI (X b) * expI (A b) := fun b hb => by
    have e' : expTwist X (expForm A) b =
        Matrices.ComplexMatrix2.matExp (Complex.I • X b) * expForm A b := if_pos hb
    rw [e', expForm_of_isPositivelyOriented A hb]
  have r : ∀ b : Edge L k 0, b.IsPositivelyOriented →
      expTwist X (expForm A) b.opposite = expNegI (A b) * expNegI (X b) := fun b hb => by
    have e' : expTwist X (expForm A) b.opposite =
        (Matrices.ComplexMatrix2.matExp (Complex.I • X b.opposite.opposite) *
          expForm A b.opposite.opposite)⁻¹ :=
      if_neg (hrev b hb)
    have h2 : (expI (A b))⁻¹ = expNegI (A b) := (Matrix.exp_neg _).symm
    rw [e', InfiniteLattice.Link.opposite_opposite, expForm_of_isPositivelyOriented A hb,
      inv_expI_mul, h2]
  simp only [complexFaceTerm, faceVariable, linkHolonomy, faceBoundary, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [e _ (forwardFrom_isPositivelyOriented _ _), e _ (forwardFrom_isPositivelyOriented _ _),
    r _ (forwardFrom_isPositivelyOriented _ _), r _ (forwardFrom_isPositivelyOriented _ _)]
  simp [twistedFaceTerm, boundaryLink, mul_assoc]
theorem twistedFaceTerm_congr {X X' A A' : Edge L k 0 → Matrices.ComplexMatrix2} {p : Face L k 0}
    (h : ∀ i, X (boundaryLink p i) = X' (boundaryLink p i))
    (h' : ∀ i, A (boundaryLink p i) = A' (boundaryLink p i)) :
    twistedFaceTerm X A p = twistedFaceTerm X' A' p := by
  simp only [twistedFaceTerm, h, h']
theorem faceTermSum_expTwist {Ω : Set (Face L k 0)} (hΩ : Ω.Finite)
    (hrev : ∀ b : Edge L k 0, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (X A : Edge L k 0 → Matrices.ComplexMatrix2) :
    faceTermSum Ω (expTwist X (expForm A)) = ∑ p ∈ hΩ.toFinset, twistedFaceTerm X A p := by
  rw [faceTermSum, finsum_mem_eq_finite_toFinset_sum _ hΩ]
  exact Finset.sum_congr rfl fun p _ => complexFaceTerm_expTwist hrev X A p
theorem contDiff_twistedFaceTerm {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    {X A : Q → Edge L k 0 → Matrices.ComplexMatrix2} (p : Face L k 0)
    (hX : ∀ i, ContDiff ℂ ∞ fun q => X q (boundaryLink p i))
    (hA : ∀ i, ContDiff ℂ ∞ fun q => A q (boundaryLink p i)) :
    ContDiff ℂ ∞ fun q => twistedFaceTerm (X q) (A q) p := by
  have hl : ∀ {W : Q → Matrices.ComplexMatrix2}, ContDiff ℂ ∞ W →
      ContDiff ℂ ∞ fun q => expI (W q) :=
    fun h => contDiff_matExp.comp (h.const_smul Complex.I)
  have hi : ∀ {W : Q → Matrices.ComplexMatrix2}, ContDiff ℂ ∞ W →
      ContDiff ℂ ∞ fun q => expNegI (W q) :=
    fun h => contDiff_matExp.comp (h.const_smul Complex.I).neg
  have htr : ContDiff ℂ ∞
      (fun M : Matrices.ComplexMatrix2 => Matrices.ComplexMatrix2.fullTrace M) :=
    (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)).contDiff
  have hP := ((((hl (hX 0)).mul (hl (hA 0))).mul ((hl (hX 1)).mul (hl (hA 1)))).mul
    ((hi (hA 2)).mul (hi (hX 2)))).mul ((hi (hA 3)).mul (hi (hX 3)))
  exact contDiff_const.sub (contDiff_const.mul (htr.comp hP))
end Term
section Elementary
variable {L k : ℕ}
theorem basisForm_of_ne (a : Fin 3) (b : PositiveEdge (meshAt L k 0))
    {c : Edge L k 0} (hc : c.IsPositivelyOriented) (h : c ≠ b.1) : basisForm a b c = 0 := by
  classical
  simp [basisForm, extendOddly, hc, h]
theorem basisForm_mem (hL : 0 < L) (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    basisForm a b ∈ complexEdgeForms (meshAt L k 0) := by
  classical
  refine extendOddly_mem hL fun c _ => ?_
  by_cases h : c = b.1
  · simp only [if_pos h]
    exact pauliFamily_mem_traceless a
  · simp only [if_neg h]
    exact Matrices.ComplexMatrix2.traceless.zero_mem
theorem edgeSupport_basisForm (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    edgeSupport (basisForm a b) ⊆ {b.1} := by
  rintro c ⟨hc, hne⟩
  by_contra h
  exact hne (basisForm_of_ne a b hc h)
theorem basisForm_hasFiniteEdgeSupport (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    HasFiniteEdgeSupport (basisForm a b) := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.basisForm_finiteSupport <;> assumption
theorem expForm_mem_fieldsValuedIn (hL : 0 < L)
    (hl : ∀ X ∈ complexEdgeForms (meshAt L k 0), ∀ b : Edge L k 0, b.IsPositivelyOriented →
      Matrices.ComplexMatrix2.matExp (Complex.I • X b) ∈ PeriodicLattice.complexGaugeGroup)
    {A : Edge L k 0 → Matrices.ComplexMatrix2} (hA : A ∈ complexEdgeForms (meshAt L k 0)) :
    expForm A ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup := by
  have hiff := opposite_isPositivelyOriented_iff (meshAt_pos (k := k) hL)
  have hdet : ∀ b : Edge L k 0, b.IsPositivelyOriented →
      (Matrices.ComplexMatrix2.matExp (Complex.I • A b)).det = 1 :=
    fun b hb => hl A hA b hb
  have hp : ∀ b : Edge L k 0, b.IsPositivelyOriented →
      expForm A b = Matrices.ComplexMatrix2.matExp (Complex.I • A b) :=
    fun b hb => expForm_of_isPositivelyOriented A hb
  have hn : ∀ b : Edge L k 0, ¬ b.IsPositivelyOriented →
      expForm A b = (Matrices.ComplexMatrix2.matExp (Complex.I • A b.opposite))⁻¹ := fun b hb => by
    have e : expForm A b = (Matrices.ComplexMatrix2.matExp (Complex.I • A b.opposite) *
        (1 : Edge L k 0 → Matrices.ComplexMatrix2) b.opposite)⁻¹ := if_neg hb
    rw [e, Pi.one_apply, mul_one]
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [hp b hb]
      exact hdet b hb
    · rw [hn b hb]
      change Matrix.det _ = 1
      rw [Matrix.det_nonsing_inv, hdet _ ((hiff b).2 hb)]
      simp
  · by_cases hb : b.IsPositivelyOriented
    · rw [hp b hb, hn _ (fun h => (hiff b).1 h hb), InfiniteLattice.Link.opposite_opposite]
    · rw [hn b hb, hp _ ((hiff b).2 hb), Matrix.nonsing_inv_nonsing_inv]
      simp [hdet _ ((hiff b).2 hb)]
end Elementary
section Action
variable {L k : ℕ}
def mixedDerivOfFaceTerms (hL : 0 < L) (P : Finset (Face L k 0))
    (B B' : Edge L k 0 → Matrices.ComplexMatrix2) (f : FieldIdx L k hL → ℂ) : ℂ :=
  deriv (fun s : ℂ => deriv (fun t : ℂ =>
    ∑ p ∈ P, twistedFaceTerm (s • B + t • B') (backgroundOfCoeffs hL f) p) 0) 0
theorem hessianEntry_eq (hL : 0 < L)
    (hD : ∀ U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
      ∀ Ω : Set (Face L k 0), Ω.Finite → Ω.Nonempty →
        ActionDerivsOnFiniteFaces.DerivsMatchFaceSum Ω U)
    (hl : ∀ X ∈ complexEdgeForms (meshAt L k 0), ∀ b : Edge L k 0, b.IsPositivelyOriented →
      Matrices.ComplexMatrix2.matExp (Complex.I • X b) ∈ PeriodicLattice.complexGaugeGroup)
    (a' a : Fin 3) (b' b : PositiveEdge (meshAt L k 0))
    (hΩ : (facesMeeting ({b'.1, b.1} : Set (Edge L k 0))).Finite)
    (f : FieldIdx L k hL → ℂ) :
    hessianEntry L k hL a' b' a b f =
      mixedDerivOfFaceTerms hL hΩ.toFinset (basisForm a' b') (basisForm a b) f := by
  have hiff := opposite_isPositivelyOriented_iff (meshAt_pos (k := k) hL)
  have hrev : ∀ c : Edge L k 0, c.IsPositivelyOriented → ¬ c.opposite.IsPositivelyOriented :=
    fun c hc h => (hiff c).1 h hc
  have hU : gaugeFieldOfCoeffs hL f ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup :=
    expForm_mem_fieldsValuedIn hL hl (backgroundOfCoeffs_mem hL f)
  have hne : (facesMeeting ({b'.1, b.1} : Set (Edge L k 0))).Nonempty := by
    obtain ⟨p, hp⟩ := exists_face_of_isPositivelyOriented b'.2
    exact ⟨p, b'.1, Or.inl rfl, hp⟩
  have hsub : facesMeeting (edgeSupport (basisForm a' b') ∪ edgeSupport (basisForm a b)) ⊆
      facesMeeting ({b'.1, b.1} : Set (Edge L k 0)) := by
    rintro p ⟨c, hc, hp⟩
    refine ⟨c, ?_, hp⟩
    rcases hc with hc | hc
    · exact Or.inl (edgeSupport_basisForm a' b' hc)
    · exact Or.inr (edgeSupport_basisForm a b hc)
  have h := (hD _ hU _ hΩ hne _ _ (basisForm_mem hL a' b') (basisForm_mem hL a b)
    (basisForm_hasFiniteEdgeSupport a' b') (basisForm_hasFiniteEdgeSupport a b) hsub).2
  rw [hessianEntry, h]
  simp only [mixedDirectionalDeriv, mixedDerivOfFaceTerms, actionAtExpTwist, gaugeFieldOfCoeffs,
    faceTermSum_expTwist hΩ hrev]
  rfl
theorem mixedDerivOfFaceTerms_eq_zero (hL : 0 < L) (a' a : Fin 3)
    (b' b : PositiveEdge (meshAt L k 0)) (P : Finset (Face L k 0))
    (hnone : ¬ ∃ p : Face L k 0, b'.1 ∈ faceEdges p ∧ b.1 ∈ faceEdges p)
    (f : FieldIdx L k hL → ℂ) :
    mixedDerivOfFaceTerms hL P (basisForm a' b') (basisForm a b) f = 0 := by
  classical
  set B := basisForm (L := L) (k := k) (j := 0) a' b' with hB
  set B' := basisForm (L := L) (k := k) (j := 0) a b with hB'
  set A := backgroundOfCoeffs hL f with hA
  have hoff : ∀ (p : Face L k 0) (i : Fin 4), b.1 ∉ faceEdges p →
      B' (boundaryLink p i) = 0 := fun p i hp =>
    basisForm_of_ne a b (boundaryLink_isPositivelyOriented p i)
      fun h => hp (h ▸ boundaryLink_mem p i)
  have hoff' : ∀ (p : Face L k 0) (i : Fin 4), b'.1 ∉ faceEdges p →
      B (boundaryLink p i) = 0 := fun p i hp =>
    basisForm_of_ne a' b' (boundaryLink_isPositivelyOriented p i)
      fun h => hp (h ▸ boundaryLink_mem p i)
  have hsplit : ∀ s t : ℂ, ∑ p ∈ P, twistedFaceTerm (s • B + t • B') A p =
      (∑ p ∈ P with b.1 ∉ faceEdges p, twistedFaceTerm (s • B) A p) +
        ∑ p ∈ P with ¬ b.1 ∉ faceEdges p, twistedFaceTerm (t • B') A p := by
    intro s t
    rw [← Finset.sum_filter_add_sum_filter_not P (fun p => b.1 ∉ faceEdges p)]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun p hp => ?_)
      (Finset.sum_congr rfl fun p hp => ?_)
    · refine twistedFaceTerm_congr (fun i => ?_) fun _ => rfl
      have h0 := hoff p i (Finset.mem_filter.1 hp).2
      simp [h0]
    · refine twistedFaceTerm_congr (fun i => ?_) fun _ => rfl
      have hb : b.1 ∈ faceEdges p := not_not.1 (Finset.mem_filter.1 hp).2
      have h0 := hoff' p i fun h => hnone ⟨p, h, hb⟩
      simp [h0]
  change deriv (fun s : ℂ =>
    deriv (fun t : ℂ => ∑ p ∈ P, twistedFaceTerm (s • B + t • B') A p) 0) 0 = 0
  simp only [hsplit, deriv_const_add, deriv_const]
theorem edgesOfFacesMeeting_finite {b' b : Edge L k 0}
    (hfin : (facesMeeting ({b', b} : Set (Edge L k 0))).Finite) :
    (edgesOfFacesMeeting b' b).Finite := by
  refine (hfin.biUnion fun p _ => List.finite_toSet (faceEdges p)).subset ?_
  rintro c ⟨p, hp, hc⟩
  exact mem_biUnion hp hc
theorem mixedDerivOfFaceTerms_holomorphic (hL : 0 < L) (a' a : Fin 3)
    (b' b : PositiveEdge (meshAt L k 0))
    (hΩ : (facesMeeting ({b'.1, b.1} : Set (Edge L k 0))).Finite) (ρ : ℝ) :
    HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
      (backgroundCoords L k hL (edgesOfFacesMeeting b'.1 b.1))
      (mixedDerivOfFaceTerms hL hΩ.toFinset (basisForm a' b') (basisForm a b)) := by
  refine holomorphicInValuesBelow_of_entire
    (backgroundCoords_finite hL (edgesOfFacesMeeting_finite hΩ)) ?_ ?_ ρ
  · intro ζ ζ' h
    have hA : ∀ p ∈ hΩ.toFinset, ∀ i, backgroundOfCoeffs hL ζ (boundaryLink p i) =
        backgroundOfCoeffs hL ζ' (boundaryLink p i) := fun p hp i =>
      backgroundOfCoeffs_congr hL (boundaryLink_isPositivelyOriented p i) fun c =>
        h _ (mem_backgroundCoords hL (boundaryLink_isPositivelyOriented p i)
          (show boundaryLink p i ∈ edgesOfFacesMeeting b'.1 b.1 from
            ⟨p, hΩ.mem_toFinset.1 hp, boundaryLink_mem p i⟩) c)
    have hsum : ∀ s t : ℂ,
        ∑ p ∈ hΩ.toFinset, twistedFaceTerm (s • basisForm a' b' + t • basisForm a b)
          (backgroundOfCoeffs hL ζ) p =
        ∑ p ∈ hΩ.toFinset, twistedFaceTerm (s • basisForm a' b' + t • basisForm a b)
          (backgroundOfCoeffs hL ζ') p := fun s t =>
      Finset.sum_congr rfl fun p hp => twistedFaceTerm_congr (fun _ => rfl) (hA p hp)
    simp only [mixedDerivOfFaceTerms, hsum]
  · intro l e
    have hG : ContDiff ℂ ∞ (fun q : (Coordinates.ComplexCoordinates l × ℂ) × ℂ =>
        ∑ p ∈ hΩ.toFinset, twistedFaceTerm (q.1.2 • basisForm a' b' + q.2 • basisForm a b)
          (backgroundOfCoeffs hL (fieldExtend e q.1.1)) p) := by
      refine ContDiff.sum fun p _ => contDiff_twistedFaceTerm p (fun i => ?_) fun i => ?_
      · exact ((contDiff_snd.comp contDiff_fst).smul contDiff_const).add
          (contDiff_snd.smul contDiff_const)
      · exact (contDiff_backgroundOfCoeffs hL e (boundaryLink_isPositivelyOriented p i)).comp
          (contDiff_fst.comp contDiff_fst)
    have h2 := contDiff_deriv_snd_zero (contDiff_deriv_snd_zero hG)
    exact h2.differentiable (by simp)
end Action
section Bonds
variable {L k : ℕ}
def pauliCoeffOfEntries (a : Fin 3) (X : Matrices.ComplexMatrix2) : ℂ :=
  ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
theorem pauliCoeff_eq (a : Fin 3) {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    pauliCoeff a X = pauliCoeffOfEntries a X := by
  rw [pauliCoeff, dif_pos hX]
  rfl
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem differentiable_pauliCoeffOfEntries (a : Fin 3) :
    Differentiable ℂ (pauliCoeffOfEntries a) := by
  have he : ∀ i j : Fin 2, Differentiable ℂ (fun X : Matrices.ComplexMatrix2 => X i j) :=
    fun i j => (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiable
  fin_cases a
  · change Differentiable ℂ (fun X : Matrices.ComplexMatrix2 => (X 0 1 + X 1 0) / 2)
    simp only [div_eq_mul_inv]
    exact ((he 0 1).fun_add (he 1 0)).mul_const _
  · change Differentiable ℂ
      (fun X : Matrices.ComplexMatrix2 => (X 1 0 - X 0 1) / (2 * Complex.I))
    simp only [div_eq_mul_inv]
    exact ((he 1 0).fun_sub (he 0 1)).mul_const _
  · exact he 0 0
theorem holomorphicInValuesBelow_at_edge (hL : 0 < L) (a' : Fin 3)
    (b' : PositiveEdge (meshAt L k 0))
    {Ψ : Matrices.ComplexMatrix2 → Matrices.ComplexMatrix2} (hΨ : Differentiable ℂ Ψ)
    (hsl : ∀ A, Ψ A ∈ Matrices.ComplexMatrix2.traceless)
    {g : ((fieldPeriodicData L k hL).Carrier → ℂ) → ℂ}
    (hg : ∀ f, g f = pauliCoeff a' (Ψ (backgroundOfCoeffs hL f b'.1))) (ρ : ℝ) :
    HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ (backgroundCoords L k hL {b'.1}) g := by
  refine holomorphicInValuesBelow_of_entire
    (backgroundCoords_finite hL (Set.finite_singleton _)) ?_ ?_ ρ
  · intro ζ ζ' h
    rw [hg, hg, backgroundOfCoeffs_congr hL b'.2 fun c =>
      h _ (mem_backgroundCoords hL b'.2 (Set.mem_singleton _) c)]
  · intro l e
    simp only [hg, pauliCoeff_eq a' (hsl _)]
    exact (differentiable_pauliCoeffOfEntries a').comp
      (hΨ.comp ((contDiff_backgroundOfCoeffs hL e b'.2).differentiable (by simp)))
def expConj (A Y : Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 := expI A * Y * expNegI A
theorem conjugateBy_expI (A Y : Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.conjugateBy (expI A) Y = expConj A Y := by
  have h : expNegI A = (expI A)⁻¹ := Matrix.exp_neg _
  rw [Matrices.ComplexMatrix2.conjugateBy, expConj, h]
theorem expConj_mem (A : Matrices.ComplexMatrix2) {Y : Matrices.ComplexMatrix2}
    (hY : Y ∈ Matrices.ComplexMatrix2.traceless) :
    expConj A Y ∈ Matrices.ComplexMatrix2.traceless := by
  have h : expNegI A * expI A = 1 := by
    have h' : expNegI A = (expI A)⁻¹ := Matrix.exp_neg _
    rw [h']
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))
  change Matrix.trace _ = 0
  rw [expConj, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul]
  exact hY
theorem differentiable_expConj (Y : Matrices.ComplexMatrix2) :
    Differentiable ℂ (fun A => expConj A Y) := by
  have hl : Differentiable ℂ (fun A : Matrices.ComplexMatrix2 => expI A) :=
    (contDiff_matExp.comp (contDiff_id.const_smul Complex.I)).differentiable (by simp)
  have hi : Differentiable ℂ (fun A : Matrices.ComplexMatrix2 => expNegI A) :=
    (contDiff_matExp.comp (contDiff_id.const_smul Complex.I).neg).differentiable (by simp)
  exact (hl.mul (differentiable_const Y)).mul hi
theorem vertexBasisFunction_mem (a : Fin 3) (x y : Vertex L k 0) :
    vertexBasisFunction a x y ∈ Matrices.ComplexMatrix2.traceless := by
  classical
  by_cases h : y = x
  · simpa [vertexBasisFunction, h] using pauliFamily_mem_traceless a
  · simp [vertexBasisFunction, h]
theorem vertexBasisFunction_of_ne (a : Fin 3) {x y : Vertex L k 0} (h : x ≠ y) :
    vertexBasisFunction a x y = 0 := by
  classical
  simp [vertexBasisFunction, h.symm]
theorem covDiffEntry_eq (hL : 0 < L) (a' a : Fin 3) (b' : PositiveEdge (meshAt L k 0))
    (x : Vertex L k 0) (f : FieldIdx L k hL → ℂ) :
    covDiffEntry L k hL a' b' a x f =
      pauliCoeff a' (expConj (backgroundOfCoeffs hL f b'.1)
        (vertexBasisFunction a x b'.1.terminal) - vertexBasisFunction a x b'.1.initial) := by
  have hU : gaugeFieldOfCoeffs hL f b'.1 = expI (backgroundOfCoeffs hL f b'.1) :=
    expForm_of_isPositivelyOriented _ b'.2
  have h : covDiff (gaugeFieldOfCoeffs hL f) (vertexBasisFunction a x) b'.1 =
      Matrices.ComplexMatrix2.conjugateBy (gaugeFieldOfCoeffs hL f b'.1)
        (vertexBasisFunction a x b'.1.terminal) -
        vertexBasisFunction a x b'.1.initial := if_pos b'.2
  change pauliCoeff a' (covDiff (gaugeFieldOfCoeffs hL f)
    (vertexBasisFunction a x) b'.1) = _
  rw [h, hU, conjugateBy_expI]
theorem bracketEntry_eq (hL : 0 < L) (a' a c : Fin 3)
    (b' b : PositiveEdge (meshAt L k 0)) (x : Vertex L k 0)
    (f : FieldIdx L k hL → ℂ) :
    bracketEntry L k hL a' b' a x c b f =
      pauliCoeff a' ((Complex.I / 2) • ⁅vertexBasisFunction a x b'.1.initial +
        expConj (backgroundOfCoeffs hL f b'.1) (vertexBasisFunction a x b'.1.terminal),
        basisForm c b b'.1⁆) := by
  have hU : gaugeFieldOfCoeffs hL f b'.1 = expI (backgroundOfCoeffs hL f b'.1) :=
    expForm_of_isPositivelyOriented _ b'.2
  have h : levelBracketTerm (gaugeFieldOfCoeffs hL f) (vertexBasisFunction a x)
      (basisForm c b) b'.1 = (Complex.I / 2) • ⁅vertexBasisFunction a x b'.1.initial +
        Matrices.ComplexMatrix2.conjugateBy (gaugeFieldOfCoeffs hL f b'.1)
          (vertexBasisFunction a x b'.1.terminal),
        basisForm c b b'.1⁆ := if_pos b'.2
  change pauliCoeff a' (levelBracketTerm (gaugeFieldOfCoeffs hL f)
    (vertexBasisFunction a x) (basisForm c b) b'.1) = _
  rw [h, hU, conjugateBy_expI]
end Bonds
theorem entriesAreLocalAndEntire_of (hD : ActionDerivsOnFiniteFaces.Claim)
    (hN : FaceEdgeFinsets.FacesAndEdgesFinite)
    (hC : LeftChartFields.Claim) : EntriesAreLocalAndEntire := by
  intro L hL hs k
  have hNk := (hN L hs k 0 (Nat.zero_le k)).2
  have hDk := hD L k 0 hs (Nat.zero_le k)
  have h1 : (1 : Edge L k 0 → Matrices.ComplexMatrix2) ∈
      fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup :=
    ⟨fun _ => Matrix.det_one, fun _ => by simp⟩
  have hl : ∀ X ∈ complexEdgeForms (meshAt L k 0), ∀ b : Edge L k 0, b.IsPositivelyOriented →
      Matrices.ComplexMatrix2.matExp (Complex.I • X b) ∈ PeriodicLattice.complexGaugeGroup := by
    intro X hX b hb
    have h := (((hC.2.2 L k 0 hs (Nat.zero_le k)).2.1).1.2 1 h1 X hX ⟨b, hb⟩).1 1
    simpa [LeftChartFields.leftExpMul, LeftChartFields.LatticeData.onPositive,
      LeftChartFields.fullData] using h
  have hfin : ∀ b' b : PositiveEdge (meshAt L k 0),
      (facesMeeting ({b'.1, b.1} : Set (Edge L k 0))).Finite := fun b' b =>
    (hNk.2.1 _ ((Set.finite_singleton _).insert _) (by
      rintro c (rfl | rfl)
      · exact b'.2
      · exact b.2)).1
  have hE := fun (a' a : Fin 3) (b' b : PositiveEdge (meshAt L k 0)) =>
    hessianEntry_eq hL (fun U hU Ω h₁ h₂ => (hDk U hU Ω h₁ h₂).1) hl a' a b' b (hfin b' b)
  refine ⟨fun a' a b' b => ⟨fun hnone f => ?_, fun ρ _ => ?_⟩,
    fun a' a b' x => ⟨fun h₁ h₂ f => ?_, fun ρ _ => ?_⟩, fun a' a c b' b x ρ _ => ?_⟩
  · rw [hE, mixedDerivOfFaceTerms_eq_zero hL a' a b' b _ hnone]
  · rw [show hessianEntry L k hL a' b' a b = _ from funext (hE a' a b' b)]
    exact mixedDerivOfFaceTerms_holomorphic hL a' a b' b (hfin b' b) ρ
  · rw [covDiffEntry_eq, vertexBasisFunction_of_ne a h₁, vertexBasisFunction_of_ne a h₂]
    simp [expConj, pauliCoeff_zero]
  · refine holomorphicInValuesBelow_at_edge hL a' b'
      (Ψ := fun A => expConj A (vertexBasisFunction a x b'.1.terminal) -
        vertexBasisFunction a x b'.1.initial)
      ((differentiable_expConj _).sub (differentiable_const _))
      (fun A => Matrices.ComplexMatrix2.traceless.sub_mem
        (expConj_mem A (vertexBasisFunction_mem a x _)) (vertexBasisFunction_mem a x _))
      (fun f => covDiffEntry_eq hL a' a b' x f) ρ
  · refine holomorphicInValuesBelow_at_edge hL a' b'
      (Ψ := fun A => (Complex.I / 2) • ⁅vertexBasisFunction a x b'.1.initial +
        expConj A (vertexBasisFunction a x b'.1.terminal), basisForm c b b'.1⁆)
      ?_ (fun A => ?_) (fun f => bracketEntry_eq hL a' a c b' b x f) ρ
    · simp only [Ring.lie_def]
      have hc := (differentiable_const (vertexBasisFunction a x b'.1.initial)).fun_add
        (differentiable_expConj (vertexBasisFunction a x b'.1.terminal))
      have hd := (hc.fun_mul (differentiable_const (basisForm c b b'.1))).fun_sub
        ((differentiable_const (basisForm c b b'.1)).fun_mul hc)
      exact hd.const_smul (Complex.I / 2)
    · change Matrix.trace _ = 0
      rw [Matrix.trace_smul, Ring.lie_def, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self,
        smul_zero]
end YangMills.Construction.Tower.FullSpace.FieldValueFunctions.LocalComponents
end

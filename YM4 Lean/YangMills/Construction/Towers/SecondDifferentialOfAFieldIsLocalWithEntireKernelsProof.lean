import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.CriterionForLocalKernelsWithEntireEntriesProof
import YangMills.Construction.Towers.DerivativesOfTheActionOnFinitePlaquetteSetsAtTheSideInfinity
import YangMills.Construction.Towers.IsometriesKeepThePairingsAndTheSecondDerivativeAtTheSideInfinity
import YangMills.Construction.Towers.KernelsOfAFieldAreRealAtRealFieldsProof
import YangMills.Construction.Towers.KernelsOfTheTwoOperatorsAreProductsProof
import YangMills.Construction.Towers.KernelsFieldsAndPropertiesOfTheTwoOperators
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAsAKernel
import Mathlib
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAsAKernelProof
set_option autoImplicit false

section
open Set
noncomputable section
namespace YangMills.Construction.Tower.FieldHessian
def kernelOfField (L : ℕ) (ζ : (PeriodicOperators.colourEdges L 0 0).Carrier → ℂ) :
    (PeriodicOperators.colourEdges L 0 0).Carrier →
      (PeriodicOperators.colourEdges L 0 0).Carrier → ℂ :=
  FullSpace.complexHessianKernel (FullSpace.expField ζ)
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ ρ : ℝ, 0 < ρ →
      PeriodicOperators.IsLocalWith (PeriodicOperators.colourEdges L 0 0)
        (PeriodicOperators.colourEdges L 0 0) (PeriodicOperators.colourEdges L 0 0)
        (kernelOfField L) ρ 2) ∧
    PeriodicOperators.HasEntireKernelEntries (PeriodicOperators.colourEdges L 0 0)
      (PeriodicOperators.colourEdges L 0 0) (PeriodicOperators.colourEdges L 0 0)
      (kernelOfField L) ∧
    ∀ ζ : (PeriodicOperators.colourEdges L 0 0).Carrier → ℂ,
      HessianKernel.SupportedOnRelation (FullSpace.complexHessianKernel (FullSpace.expField ζ))
        (fun e e' : FullSpace.PositiveEdge (meshAt L 0 0) =>
          ∃ f : FullSpace.Face L 0 0,
            e.1 ∈ FullSpace.faceEdges f ∧ e'.1 ∈ FullSpace.faceEdges f)
end YangMills.Construction.Tower.FieldHessian
end
end

open Set Filter
open scoped Topology Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace YangMills.Construction.Tower
namespace FullSpace.FieldHessianEntries
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Matrices
open YangMills.Construction.Coordinates
open YangMills.Construction.Tower.FaceEdgeFinsets.Unbounded (facesMeeting)
open YangMills.Construction.Tower.FullSpace.ActionDerivsOnFiniteFaces (actionAtExpTwist)
open YangMills.Construction.TorusMetric (euclidNormVec)
section EvaluationMaps
variable {F : PeriodicData} {S : Set F.Carrier} {l : ℕ}
theorem fieldExtend_apply (e : Fin l ≃ S) (z : ComplexCoordinates l) (j : Fin l) :
    fieldExtend e z ((e j : S) : F.Carrier) = z j := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.fieldExtend_apply <;> assumption
theorem contDiff_fieldExtend (e : Fin l ≃ S) (κ : F.Carrier) :
    ContDiff ℂ ∞ (fun z : ComplexCoordinates l => fieldExtend e z κ) := by
  by_cases h : ∃ j, ((e j : S) : F.Carrier) = κ
  · obtain ⟨j, rfl⟩ := h
    simp only [fieldExtend_apply]
    exact contDiff_apply ℂ ℂ j
  · have h' : (fun z : ComplexCoordinates l => fieldExtend e z κ) = fun _ => 0 := by
      funext z
      exact Function.extend_apply' _ _ _ h
    rw [h']
    exact contDiff_const
theorem fieldExtend_fieldValues (e : Fin l ≃ S) (ζ : F.Carrier → ℂ) {κ : F.Carrier} (hκ : κ ∈ S) :
    fieldExtend e (fieldValues e ζ) κ = ζ κ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.fieldExtend_fieldValues <;> assumption
end EvaluationMaps
section Partial
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem contDiff_deriv_snd_at_zero {H : E × ℂ → ℂ} (hH : ContDiff ℂ ∞ H) :
    ContDiff ℂ ∞ (fun x : E => deriv (fun t : ℂ => H (x, t)) 0) := by
  have h1 : ContDiff ℂ ∞ (fderiv ℂ H) := hH.fderiv_right (by simp)
  have h2 : ContDiff ℂ ∞ (fun x : E => fderiv ℂ H (x, 0) ((0 : E), (1 : ℂ))) :=
    (h1.comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const
  suffices h : (fun x : E => deriv (fun t : ℂ => H (x, t)) 0) =
      fun x : E => fderiv ℂ H (x, 0) ((0 : E), (1 : ℂ)) by
    rw [h]
    exact h2
  funext x
  have hc : HasDerivAt (fun t : ℂ => (x, t)) ((0 : E), (1 : ℂ)) 0 :=
    (hasDerivAt_const (0 : ℂ) x).prodMk (hasDerivAt_id (0 : ℂ))
  have hd : HasFDerivAt H (fderiv ℂ H (x, 0)) (x, (0 : ℂ)) :=
    ((hH.differentiable (by simp)) (x, 0)).hasFDerivAt
  exact (hd.comp_hasDerivAt (0 : ℂ) hc).deriv
end Partial
theorem contDiff_matExp : ContDiff ℂ ∞ (fun Z : ComplexMatrix2 => ComplexMatrix2.matExp Z) :=
  contDiff_iff_contDiffAt.2 fun Z => (NormedSpace.exp_analytic (𝕂 := ℂ) Z).contDiffAt
section Lattice
variable {L : ℕ}
theorem meshAt_zero_zero : meshAt L 0 0 = 1 := by simp [meshAt]
theorem meshAt_zero_zero_pos : 0 < meshAt L 0 0 := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.meshAt_zero_pos <;> assumption
theorem forwardFrom_isPositivelyOriented {a : ℝ} (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem opposite_isPositivelyOriented_iff {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.link_opposite_positive_iff <;> assumption
def sideEdge (p : Face L 0 0) : Fin 4 → Edge L 0 0 :=
  ![InfiniteLattice.Link.forwardFrom p.corner p.lowAxis,
    InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep _ p.lowAxis) p.highAxis,
    InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep _ p.highAxis) p.lowAxis,
    InfiniteLattice.Link.forwardFrom p.corner p.highAxis]
theorem sideEdge_mem (p : Face L 0 0) (i : Fin 4) : sideEdge p i ∈ faceEdges p := by
  fin_cases i <;> simp [sideEdge, faceEdges]
theorem sideEdge_isPositivelyOriented (p : Face L 0 0) (i : Fin 4) :
    (sideEdge p i).IsPositivelyOriented := by
  fin_cases i <;> simp [sideEdge, forwardFrom_isPositivelyOriented]
theorem exists_sideEdge_eq {p : Face L 0 0} {b : Edge L 0 0}
    (hb : b ∈ faceEdges p) : ∃ i, sideEdge p i = b := by
  simp only [faceEdges, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩
  · exact ⟨2, h.symm⟩
  · exact ⟨3, h.symm⟩
theorem exists_face_of_positive {c : Edge L 0 0} (hc : c.IsPositivelyOriented) :
    ∃ p : Face L 0 0, c ∈ faceEdges p := by
  obtain ⟨x, κ, rfl⟩ := InfiniteLattice.mem_positiveLinks_iff.2 hc
  by_cases h : κ = 3
  · subst h
    exact ⟨⟨x, 0, 3, by decide⟩, by simp [faceEdges]⟩
  · exact ⟨⟨x, κ, 3, lt_of_le_of_ne (Fin.le_last κ) h⟩, by simp [faceEdges]⟩
theorem sum_sq_axisStep (μ : Fin 4) :
    ∑ ν, ((InfiniteLattice.axisStep (meshAt L 0 0) μ : Vertex L 0 0) :
      InfiniteLattice.AmbientSpace) ν ^ 2 = 1 := by
  simp only [InfiniteLattice.axisStep, meshAt_zero_zero]
  fin_cases μ <;> simp [Pi.single_apply]
theorem initial_sideEdge_offset (p : Face L 0 0) (i : Fin 4) :
    ∃ d : InfiniteLattice.AmbientSpace, ∑ ν, d ν ^ 2 ≤ 1 ∧
      (((sideEdge p i).initial : Vertex L 0 0) : InfiniteLattice.AmbientSpace) =
        (p.corner : InfiniteLattice.AmbientSpace) + d := by
  fin_cases i
  · exact ⟨0, by simp, by simp [sideEdge, InfiniteLattice.Link.forwardFrom]⟩
  · exact ⟨_, (sum_sq_axisStep (L := L) p.lowAxis).le,
      by simp [sideEdge, InfiniteLattice.Link.forwardFrom]⟩
  · exact ⟨_, (sum_sq_axisStep (L := L) p.highAxis).le,
      by simp [sideEdge, InfiniteLattice.Link.forwardFrom]⟩
  · exact ⟨0, by simp, by simp [sideEdge, InfiniteLattice.Link.forwardFrom]⟩
theorem euclid_initial_sub_le_two (p : Face L 0 0) {c c' : Edge L 0 0}
    (hc : c ∈ faceEdges p) (hc' : c' ∈ faceEdges p) :
    euclidNormVec (((c.initial : Vertex L 0 0) : InfiniteLattice.AmbientSpace) -
      ((c'.initial : Vertex L 0 0) : InfiniteLattice.AmbientSpace)) ≤ 2 := by
  obtain ⟨i, rfl⟩ := exists_sideEdge_eq hc
  obtain ⟨i', rfl⟩ := exists_sideEdge_eq hc'
  obtain ⟨d, hd, e⟩ := initial_sideEdge_offset p i
  obtain ⟨d', hd', e'⟩ := initial_sideEdge_offset p i'
  rw [e, e', add_sub_add_left_eq_sub]
  have hs : ∑ ν, (d - d') ν ^ 2 ≤ 2 ^ 2 := by
    have hle : ∀ ν, (d - d') ν ^ 2 ≤ 2 * d ν ^ 2 + 2 * d' ν ^ 2 := fun ν => by
      simp only [Pi.sub_apply]
      nlinarith [sq_nonneg (d ν + d' ν)]
    calc ∑ ν, (d - d') ν ^ 2 ≤ ∑ ν, (2 * d ν ^ 2 + 2 * d' ν ^ 2) :=
          Finset.sum_le_sum fun ν _ => hle ν
      _ = 2 * ∑ ν, d ν ^ 2 + 2 * ∑ ν, d' ν ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 ^ 2 := by linarith
  exact Real.sqrt_le_iff.2 ⟨by norm_num, hs⟩
end Lattice
section Forms
variable {L : ℕ}
def coeffForm (ζ : Fin 3 × PositiveEdge (meshAt L 0 0) → ℂ) : Edge L 0 0 → ComplexMatrix2 :=
  (edgePauliCoordinates L 0 0).ofCoeffs ζ
theorem coeffForm_apply (ζ : Fin 3 × PositiveEdge (meshAt L 0 0) → ℂ) {c : Edge L 0 0}
    (hc : c.IsPositivelyOriented) :
    coeffForm ζ c = ∑ a, ζ (a, ⟨c, hc⟩) • ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.edge_ofCoeffs_apply <;> assumption
theorem coeffForm_congr {ζ ζ' : Fin 3 × PositiveEdge (meshAt L 0 0) → ℂ}
    {c : Edge L 0 0} (hc : c.IsPositivelyOriented)
    (h : ∀ a : Fin 3, ζ (a, ⟨c, hc⟩) = ζ' (a, ⟨c, hc⟩)) : coeffForm ζ c = coeffForm ζ' c := by
  simp only [coeffForm_apply _ hc, h]
theorem contDiff_coeffForm {S : Set (colourEdges L 0 0).Carrier} {l : ℕ} (e : Fin l ≃ S)
    {c : Edge L 0 0} (hc : c.IsPositivelyOriented) :
    ContDiff ℂ ∞ (fun z : ComplexCoordinates l => coeffForm (fieldExtend e z) c) := by
  have h : (fun z : ComplexCoordinates l => coeffForm (fieldExtend e z) c) = fun z =>
      ∑ a, fieldExtend e z ((a, ⟨c, hc⟩) : (colourEdges L 0 0).Carrier) •
        ComplexMatrix2.pauliFamily a :=
    funext fun z => coeffForm_apply (fieldExtend e z) hc
  rw [h]
  exact ContDiff.sum fun a _ => (contDiff_fieldExtend e _).smul contDiff_const
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem extendOddly_mem {g : Edge L 0 0 → ComplexMatrix2}
    (hg : ∀ c : Edge L 0 0, c.IsPositivelyOriented → g c ∈ ComplexMatrix2.traceless) :
    extendOddly g ∈ complexEdgeForms (meshAt L 0 0) := by
  have hiff := opposite_isPositivelyOriented_iff (meshAt_zero_zero_pos (L := L))
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
end Forms
section Term
variable {L : ℕ}
abbrev expI (Y : ComplexMatrix2) : ComplexMatrix2 := ComplexMatrix2.matExp (Complex.I • Y)
abbrev expNegI (Y : ComplexMatrix2) : ComplexMatrix2 := ComplexMatrix2.matExp (-(Complex.I • Y))
def twistedFaceTerm (X A : Edge L 0 0 → ComplexMatrix2) (p : Face L 0 0) : ℂ :=
  1 - (1 / 2) * ComplexMatrix2.fullTrace (expI (X (sideEdge p 0)) * expI (A (sideEdge p 0)) *
    (expI (X (sideEdge p 1)) * expI (A (sideEdge p 1))) *
    (expNegI (A (sideEdge p 2)) * expNegI (X (sideEdge p 2))) *
    (expNegI (A (sideEdge p 3)) * expNegI (X (sideEdge p 3))))
theorem inv_matExp_mul (Y V : ComplexMatrix2) :
    (ComplexMatrix2.matExp (Complex.I • Y) * V)⁻¹ =
      V⁻¹ * ComplexMatrix2.matExp (-(Complex.I • Y)) := by apply _root_.YangMills.Construction.Tower.HessianKernel.inv_matExp_smul_mul <;> assumption
abbrev expForm (A : Edge L 0 0 → ComplexMatrix2) : Edge L 0 0 → ComplexMatrix2 :=
  expTwist A fun _ => 1
theorem expForm_of_positive (A : Edge L 0 0 → ComplexMatrix2) {b : Edge L 0 0}
    (hb : b.IsPositivelyOriented) : expForm A b = expI (A b) := by
  have e : expForm A b = ComplexMatrix2.matExp (Complex.I • A b) * (1 : ComplexMatrix2) := if_pos hb
  rw [e, mul_one]
theorem complexFaceTerm_expTwist
    (hrev : ∀ b : Edge L 0 0, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (X A : Edge L 0 0 → ComplexMatrix2) (p : Face L 0 0) :
    complexFaceTerm (expTwist X (expForm A)) p = twistedFaceTerm X A p := by
  have e : ∀ b : Edge L 0 0, b.IsPositivelyOriented →
      expTwist X (expForm A) b = expI (X b) * expI (A b) := fun b hb => by
    have e' : expTwist X (expForm A) b = ComplexMatrix2.matExp (Complex.I • X b) * expForm A b :=
      if_pos hb
    rw [e', expForm_of_positive A hb]
  have r : ∀ b : Edge L 0 0, b.IsPositivelyOriented →
      expTwist X (expForm A) b.opposite =
        expNegI (A b) * expNegI (X b) := fun b hb => by
    have e' : expTwist X (expForm A) b.opposite =
        (ComplexMatrix2.matExp (Complex.I • X b.opposite.opposite) *
          expForm A b.opposite.opposite)⁻¹ :=
      if_neg (hrev b hb)
    have h2 : (expI (A b))⁻¹ = expNegI (A b) := (Matrix.exp_neg _).symm
    rw [e', InfiniteLattice.Link.opposite_opposite, expForm_of_positive A hb,
      inv_matExp_mul, h2]
  simp only [complexFaceTerm, faceVariable, linkHolonomy, faceBoundary, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [e _ (forwardFrom_isPositivelyOriented _ _), e _ (forwardFrom_isPositivelyOriented _ _),
    r _ (forwardFrom_isPositivelyOriented _ _), r _ (forwardFrom_isPositivelyOriented _ _)]
  simp [twistedFaceTerm, sideEdge, mul_assoc]
theorem twistedFaceTerm_congr {X X' A A' : Edge L 0 0 → ComplexMatrix2} {p : Face L 0 0}
    (h : ∀ i, X (sideEdge p i) = X' (sideEdge p i)) (h' : ∀ i, A (sideEdge p i) = A' (sideEdge p i)) :
    twistedFaceTerm X A p = twistedFaceTerm X' A' p := by
  simp only [twistedFaceTerm, h, h']
theorem faceTermSum_expTwist {Ω : Set (Face L 0 0)} (hΩ : Ω.Finite)
    (hrev : ∀ b : Edge L 0 0, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (X A : Edge L 0 0 → ComplexMatrix2) :
    faceTermSum Ω (expTwist X (expForm A)) = ∑ p ∈ hΩ.toFinset, twistedFaceTerm X A p := by
  rw [faceTermSum, finsum_mem_eq_finite_toFinset_sum _ hΩ]
  exact Finset.sum_congr rfl fun p _ => complexFaceTerm_expTwist hrev X A p
theorem contDiff_twistedFaceTerm {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    {X A : Q → Edge L 0 0 → ComplexMatrix2} (p : Face L 0 0)
    (hX : ∀ i, ContDiff ℂ ∞ fun q => X q (sideEdge p i))
    (hA : ∀ i, ContDiff ℂ ∞ fun q => A q (sideEdge p i)) :
    ContDiff ℂ ∞ fun q => twistedFaceTerm (X q) (A q) p := by
  have hl : ∀ {W : Q → ComplexMatrix2}, ContDiff ℂ ∞ W → ContDiff ℂ ∞ fun q => expI (W q) :=
    fun h => contDiff_matExp.comp (h.const_smul Complex.I)
  have hi : ∀ {W : Q → ComplexMatrix2}, ContDiff ℂ ∞ W → ContDiff ℂ ∞ fun q => expNegI (W q) :=
    fun h => contDiff_matExp.comp (h.const_smul Complex.I).neg
  have htr : ContDiff ℂ ∞ (fun M : ComplexMatrix2 => ComplexMatrix2.fullTrace M) :=
    (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)).contDiff
  have hP := ((((hl (hX 0)).mul (hl (hA 0))).mul ((hl (hX 1)).mul (hl (hA 1)))).mul
    ((hi (hA 2)).mul (hi (hX 2)))).mul ((hi (hA 3)).mul (hi (hX 3)))
  exact contDiff_const.sub (contDiff_const.mul (htr.comp hP))
def mixedFaceDeriv (B B' A : Edge L 0 0 → ComplexMatrix2) (p : Face L 0 0) : ℂ :=
  deriv (fun s : ℂ => deriv (fun t : ℂ => twistedFaceTerm (s • B + t • B') A p) 0) 0
theorem contDiff_twistedFaceTerm_line (B B' A : Edge L 0 0 → ComplexMatrix2) (p : Face L 0 0) :
    ContDiff ℂ ∞ fun q : ℂ × ℂ => twistedFaceTerm (q.1 • B + q.2 • B') A p :=
  contDiff_twistedFaceTerm (X := fun q : ℂ × ℂ => q.1 • B + q.2 • B') (A := fun _ => A) p
    (fun _ => (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const))
    fun _ => contDiff_const
theorem mixed_deriv_finset_sum (P : Finset (Face L 0 0)) (B B' A : Edge L 0 0 → ComplexMatrix2) :
    deriv (fun s : ℂ => deriv (fun t : ℂ => ∑ p ∈ P, twistedFaceTerm (s • B + t • B') A p) 0) 0 =
      ∑ p ∈ P, mixedFaceDeriv B B' A p := by
  have hd : ∀ (p : Face L 0 0) (s : ℂ),
      DifferentiableAt ℂ (fun t : ℂ => twistedFaceTerm (s • B + t • B') A p) 0 := fun p s =>
    ((contDiff_twistedFaceTerm_line B B' A p).differentiable (by simp) (s, 0)).comp (0 : ℂ)
      (f := fun t : ℂ => (s, t)) (by fun_prop)
  have h1 : ∀ s : ℂ, deriv (fun t : ℂ => ∑ p ∈ P, twistedFaceTerm (s • B + t • B') A p) 0 =
      ∑ p ∈ P, deriv (fun t : ℂ => twistedFaceTerm (s • B + t • B') A p) 0 := fun s =>
    deriv_fun_sum fun p _ => hd p s
  simp only [h1]
  have hd2 : ∀ p : Face L 0 0,
      DifferentiableAt ℂ
        (fun s : ℂ => deriv (fun t : ℂ => twistedFaceTerm (s • B + t • B') A p) 0) 0 :=
    fun p => (contDiff_deriv_snd_at_zero (contDiff_twistedFaceTerm_line B B' A p)).differentiable
      (by simp) 0
  exact deriv_fun_sum fun p _ => hd2 p
theorem mixedFaceDeriv_eq_zero_left {B B' A : Edge L 0 0 → ComplexMatrix2} {p : Face L 0 0}
    (h : ∀ i, B (sideEdge p i) = 0) : mixedFaceDeriv B B' A p = 0 := by
  have e : ∀ s t : ℂ, twistedFaceTerm (s • B + t • B') A p = twistedFaceTerm (t • B') A p :=
    fun s t => twistedFaceTerm_congr (fun i => by simp [h i]) fun _ => rfl
  simp only [mixedFaceDeriv, e, deriv_const]
theorem mixedFaceDeriv_eq_zero_right {B B' A : Edge L 0 0 → ComplexMatrix2} {p : Face L 0 0}
    (h : ∀ i, B' (sideEdge p i) = 0) : mixedFaceDeriv B B' A p = 0 := by
  have e : ∀ s t : ℂ, twistedFaceTerm (s • B + t • B') A p = twistedFaceTerm (s • B) A p :=
    fun s t => twistedFaceTerm_congr (fun i => by simp [h i]) fun _ => rfl
  simp only [mixedFaceDeriv, e, deriv_const]
theorem mixedFaceDeriv_congr {B B' A A' : Edge L 0 0 → ComplexMatrix2} {p : Face L 0 0}
    (h : ∀ i, A (sideEdge p i) = A' (sideEdge p i)) :
    mixedFaceDeriv B B' A p = mixedFaceDeriv B B' A' p := by
  have e : ∀ s t : ℂ, twistedFaceTerm (s • B + t • B') A p = twistedFaceTerm (s • B + t • B') A' p :=
    fun s t => twistedFaceTerm_congr (fun _ => rfl) h
  simp only [mixedFaceDeriv, e]
theorem differentiable_mixedFaceDeriv (B B' : Edge L 0 0 → ComplexMatrix2) (p : Face L 0 0)
    {S : Set (colourEdges L 0 0).Carrier} {l : ℕ} (e : Fin l ≃ S) :
    Differentiable ℂ fun z : ComplexCoordinates l =>
      mixedFaceDeriv B B' (coeffForm (fieldExtend e z)) p := by
  have hG : ContDiff ℂ ∞ (fun q : (ComplexCoordinates l × ℂ) × ℂ =>
      twistedFaceTerm (q.1.2 • B + q.2 • B') (coeffForm (fieldExtend e q.1.1)) p) := by
    refine contDiff_twistedFaceTerm p (fun i => ?_) fun i => ?_
    · exact ((contDiff_snd.comp contDiff_fst).smul contDiff_const).add
        (contDiff_snd.smul contDiff_const)
    · exact (contDiff_coeffForm e (sideEdge_isPositivelyOriented p i)).comp
        (contDiff_fst.comp contDiff_fst)
  exact (contDiff_deriv_snd_at_zero (contDiff_deriv_snd_at_zero hG)).differentiable (by simp)
end Term
section Elementary
variable {L : ℕ}
theorem basisForm_of_ne (a : Fin 3) (b : PositiveEdge (meshAt L 0 0))
    {c : Edge L 0 0} (hc : c.IsPositivelyOriented) (h : c ≠ b.1) : basisForm a b c = 0 := by
  classical
  simp [basisForm, extendOddly, hc, h]
theorem basisForm_mem (a : Fin 3) (b : PositiveEdge (meshAt L 0 0)) :
    basisForm a b ∈ complexEdgeForms (meshAt L 0 0) := by
  classical
  refine extendOddly_mem fun c _ => ?_
  by_cases h : c = b.1
  · simp only [if_pos h]
    exact pauliFamily_mem_traceless a
  · simp only [if_neg h]
    exact ComplexMatrix2.traceless.zero_mem
theorem edgeSupport_basisForm_subset (a : Fin 3) (b : PositiveEdge (meshAt L 0 0)) :
    edgeSupport (basisForm a b) ⊆ {b.1} := by
  rintro c ⟨hc, hne⟩
  by_contra h
  exact hne (basisForm_of_ne a b hc h)
theorem basisForm_hasFiniteEdgeSupport (a : Fin 3) (b : PositiveEdge (meshAt L 0 0)) :
    HasFiniteEdgeSupport (basisForm a b) := by apply _root_.YangMills.SharedProofs.p37344 <;> assumption
theorem matExp_mem_complexGaugeGroup (hE : ComplexMatrix2.ExpLogEstimates) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.complexGaugeGroup := by
  have ht : Matrix.trace X = 0 := hX
  change (ComplexMatrix2.matExp (Complex.I • X)).det = 1
  rw [hE.2.2.2.2.2.1]
  simp [ComplexMatrix2.fullTrace, Matrix.trace_smul, ht]
theorem coeffForm_mem_traceless (ζ : Fin 3 × PositiveEdge (meshAt L 0 0) → ℂ)
    {c : Edge L 0 0} (hc : c.IsPositivelyOriented) : coeffForm ζ c ∈ ComplexMatrix2.traceless := by
  rw [coeffForm_apply ζ hc]
  exact ComplexMatrix2.traceless.sum_mem fun a _ =>
    ComplexMatrix2.traceless.smul_mem _ (pauliFamily_mem_traceless a)
theorem expField_of_positive (ζ : Fin 3 × PositiveEdge (meshAt L 0 0) → ℂ)
    {b : Edge L 0 0} (h : b.IsPositivelyOriented) :
    expField ζ b = ComplexMatrix2.matExp (Complex.I • coeffForm ζ b) :=
  expForm_of_positive (coeffForm ζ) h
theorem expField_of_not_positive (ζ : Fin 3 × PositiveEdge (meshAt L 0 0) → ℂ)
    {b : Edge L 0 0} (h : ¬ b.IsPositivelyOriented) :
    expField ζ b = (ComplexMatrix2.matExp (Complex.I • coeffForm ζ b.opposite))⁻¹ := by
  have e : expField ζ b =
      (ComplexMatrix2.matExp (Complex.I • coeffForm ζ b.opposite) * (1 : ComplexMatrix2))⁻¹ :=
    if_neg h
  rw [e, mul_one]
theorem expField_mem (hE : ComplexMatrix2.ExpLogEstimates)
    (hF : ComplexMatrix2.NormExpLogBasics)
    (ζ : Fin 3 × PositiveEdge (meshAt L 0 0) → ℂ) :
    expField ζ ∈ fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup := by
  have hiff := opposite_isPositivelyOriented_iff (meshAt_zero_zero_pos (L := L))
  have inv_exp : ∀ Z : ComplexMatrix2,
      (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := fun Z =>
    (hF.2.1 Z).2.2.2.2.1
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases h : b.IsPositivelyOriented
    · rw [expField_of_positive ζ h]
      exact matExp_mem_complexGaugeGroup hE (coeffForm_mem_traceless ζ h)
    · have hb := coeffForm_mem_traceless ζ ((hiff b).2 h)
      rw [expField_of_not_positive ζ h, inv_exp, ← smul_neg]
      exact matExp_mem_complexGaugeGroup hE (ComplexMatrix2.traceless.neg_mem hb)
  · by_cases h : b.IsPositivelyOriented
    · rw [expField_of_not_positive ζ (fun h' => (hiff b).1 h' h),
        expField_of_positive ζ h]
      rfl
    · rw [expField_of_positive ζ ((hiff b).2 h), expField_of_not_positive ζ h,
        inv_exp, inv_exp, neg_neg]
end Elementary
section Entries
variable {L : ℕ}
open Classical in
def sharedFaces {Ω : Set (Face L 0 0)} (hΩ : Ω.Finite)
    (b' b : PositiveEdge (meshAt L 0 0)) : Finset (Face L 0 0) :=
  hΩ.toFinset.filter fun p => b'.1 ∈ faceEdges p ∧ b.1 ∈ faceEdges p
theorem complexHessianKernel_eq_sum
    (hD : ∀ U ∈ fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup,
      ∀ Ω : Set (Face L 0 0), Ω.Finite → Ω.Nonempty →
        ActionDerivsOnFiniteFaces.DerivsMatchFaceSum Ω U)
    (a' a : Fin 3) (b' b : PositiveEdge (meshAt L 0 0))
    (hΩ : (facesMeeting ({b'.1, b.1} : Set (Edge L 0 0))).Finite)
    (ζ : Fin 3 × PositiveEdge (meshAt L 0 0) → ℂ)
    (hU : expField ζ ∈ fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup) :
    complexHessianKernel (expField ζ) (a', b') (a, b) =
      ∑ p ∈ sharedFaces hΩ b' b,
        mixedFaceDeriv (basisForm a' b') (basisForm a b) (coeffForm ζ) p := by
  classical
  have hiff := opposite_isPositivelyOriented_iff (meshAt_zero_zero_pos (L := L))
  have hrev : ∀ c : Edge L 0 0, c.IsPositivelyOriented → ¬ c.opposite.IsPositivelyOriented :=
    fun c hc h => (hiff c).1 h hc
  have hne : (facesMeeting ({b'.1, b.1} : Set (Edge L 0 0))).Nonempty := by
    obtain ⟨p, hp⟩ := exists_face_of_positive b'.2
    exact ⟨p, b'.1, Or.inl rfl, hp⟩
  have hsub : facesMeeting (edgeSupport (basisForm a' b') ∪ edgeSupport (basisForm a b)) ⊆
      facesMeeting ({b'.1, b.1} : Set (Edge L 0 0)) := by
    rintro p ⟨c, hc, hp⟩
    refine ⟨c, ?_, hp⟩
    rcases hc with hc | hc
    · exact Or.inl (edgeSupport_basisForm_subset a' b' hc)
    · exact Or.inr (edgeSupport_basisForm_subset a b hc)
  have h := (hD _ hU _ hΩ hne _ _ (basisForm_mem a' b') (basisForm_mem a b)
    (basisForm_hasFiniteEdgeSupport a' b') (basisForm_hasFiniteEdgeSupport a b) hsub).2
  have hm : complexHessianKernel (expField ζ) (a', b') (a, b) =
      deriv (fun s : ℂ => deriv (fun t : ℂ => ∑ p ∈ hΩ.toFinset,
        twistedFaceTerm (s • basisForm a' b' + t • basisForm a b) (coeffForm ζ) p) 0) 0 := by
    change complexActionHessian (expField ζ) _ _ = _
    rw [h]
    simp only [mixedDirectionalDeriv, actionAtExpTwist]
    have e : ∀ X : Edge L 0 0 → ComplexMatrix2,
        faceTermSum (facesMeeting ({b'.1, b.1} : Set (Edge L 0 0)))
          (expTwist X (expField ζ)) =
        ∑ p ∈ hΩ.toFinset, twistedFaceTerm X (coeffForm ζ) p :=
      fun X => faceTermSum_expTwist hΩ hrev X (coeffForm ζ)
    simp only [e]
    rfl
  rw [hm, mixed_deriv_finset_sum]
  refine (Finset.sum_filter_of_ne fun p _ hne' => ?_).symm
  constructor
  · by_contra hp
    refine hne' (mixedFaceDeriv_eq_zero_left fun i => ?_)
    exact basisForm_of_ne a' b' (sideEdge_isPositivelyOriented p i)
      fun e => hp (e ▸ sideEdge_mem p i)
  · by_contra hp
    refine hne' (mixedFaceDeriv_eq_zero_right fun i => ?_)
    exact basisForm_of_ne a b (sideEdge_isPositivelyOriented p i)
      fun e => hp (e ▸ sideEdge_mem p i)
open Classical in
theorem mem_faceEdges_of_mem_sharedFaces {Ω : Set (Face L 0 0)} (hΩ : Ω.Finite)
    {b' b : PositiveEdge (meshAt L 0 0)} {p : Face L 0 0}
    (hp : p ∈ sharedFaces hΩ b' b) : b'.1 ∈ faceEdges p :=
  (Finset.mem_filter.1 hp).2.1
theorem exists_differentiable_kernel_representation
    (hK : ∀ (a' a : Fin 3) (b' b : PositiveEdge (meshAt L 0 0))
      (hΩ : (facesMeeting ({b'.1, b.1} : Set (Edge L 0 0))).Finite)
      (ζ : Fin 3 × PositiveEdge (meshAt L 0 0) → ℂ),
      complexHessianKernel (expField ζ) (a', b') (a, b) =
        ∑ p ∈ sharedFaces hΩ b' b,
          mixedFaceDeriv (basisForm a' b') (basisForm a b) (coeffForm ζ) p)
    (hfin : ∀ b' b : PositiveEdge (meshAt L 0 0),
      (facesMeeting ({b'.1, b.1} : Set (Edge L 0 0))).Finite)
    (ι' ι : (colourEdges L 0 0).Carrier) {l : ℕ}
    (e : Fin l ≃ nearIndices (colourEdges L 0 0) ((colourEdges L 0 0).pos ι') 2) :
    ∃ h : ComplexCoordinates l → ℂ, Differentiable ℂ h ∧
      ∀ ζ : (colourEdges L 0 0).Carrier → ℂ,
        complexHessianKernel (expField ζ) ι' ι = h (fieldValues e ζ) := by
  obtain ⟨a', b'⟩ := ι'
  obtain ⟨a, b⟩ := ι
  refine ⟨fun z => ∑ p ∈ sharedFaces (hfin b' b) b' b,
    mixedFaceDeriv (basisForm a' b') (basisForm a b) (coeffForm (fieldExtend e z)) p,
    Differentiable.fun_sum fun p _ => differentiable_mixedFaceDeriv _ _ p e, fun ζ => ?_⟩
  refine (hK a' a b' b (hfin b' b) ζ).trans (Finset.sum_congr rfl fun p hp => ?_)
  refine mixedFaceDeriv_congr fun i => ?_
  refine coeffForm_congr (sideEdge_isPositivelyOriented p i) fun c => ?_
  refine (fieldExtend_fieldValues e ζ ?_).symm
  exact euclid_initial_sub_le_two p (sideEdge_mem p i)
    (mem_faceEdges_of_mem_sharedFaces (hfin b' b) hp)
end Entries
section Translations
open YangMills.Construction.Tower.FullSpace.Translations (spaceShift)
section OneLattice
variable {a : ℝ} (v : InfiniteLattice.AmbientSpace)
theorem edgePreimage_spaceShift_eq {b b' : InfiniteLattice.Link a}
    (ht : (b.initial : InfiniteLattice.AmbientSpace) = (b'.initial : InfiniteLattice.AmbientSpace) + v)
    (hh : (b.terminal : InfiniteLattice.AmbientSpace) =
      (b'.terminal : InfiniteLattice.AmbientSpace) + v) :
    edgePreimage (spaceShift v) b = b' := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.edgePreimage_eq <;> assumption
end OneLattice
theorem castVec_neg (n : Fin 4 → ℤ) : castVec (-n) = -castVec n := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.castVec_neg <;> assumption
variable {L : ℕ} {n₀ : Fin 4 → ℤ}
def latticeVertex (n : Fin 4 → ℤ) : Vertex L 0 0 :=
  ⟨fun μ => (n μ : ℝ) * meshAt L 0 0, n, fun _ => rfl⟩
theorem exists_vertex_intShift (n : Fin 4 → ℤ) (x : Vertex L 0 0) :
    ∃ x' : Vertex L 0 0, (x' : InfiniteLattice.AmbientSpace) = intShift n x := by
  obtain ⟨m, hm⟩ := x.2
  refine ⟨latticeVertex (m + n), funext fun μ => ?_⟩
  simp [latticeVertex, intShift, castVec, hm μ, meshAt_zero_zero]
theorem coe_vertexImage_intShift (n : Fin 4 → ℤ) (x : Vertex L 0 0) :
    ((vertexImage (intShift n) x : Vertex L 0 0) : InfiniteLattice.AmbientSpace) =
      intShift n x :=
  Classical.epsilon_spec (exists_vertex_intShift n x)
theorem vertexImage_intShift_sub (n : Fin 4 → ℤ) (x y : Vertex L 0 0) :
    vertexImage (intShift n) y - vertexImage (intShift n) x = y - x := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_sub, coe_vertexImage_intShift, intShift, add_sub_add_right_eq_sub]
theorem vertexImage_neg_vertexImage (n : Fin 4 → ℤ) (x : Vertex L 0 0) :
    vertexImage (intShift (-n)) (vertexImage (intShift n) x) = x := by
  apply Subtype.ext
  rw [coe_vertexImage_intShift]
  rw [coe_vertexImage_intShift]
  funext μ
  simp [intShift, castVec]
theorem edgeImage_intShift_ends (n : Fin 4 → ℤ) (b : Edge L 0 0) :
    (edgeImage (intShift n) b).initial = vertexImage (intShift n) b.initial ∧
      (edgeImage (intShift n) b).terminal = vertexImage (intShift n) b.terminal := by
  refine Classical.epsilon_spec (p := fun b' : Edge L 0 0 =>
    b'.initial = vertexImage (intShift n) b.initial ∧
      b'.terminal = vertexImage (intShift n) b.terminal) ?_
  refine ⟨⟨vertexImage (intShift n) b.initial, vertexImage (intShift n) b.terminal, ?_⟩,
    rfl, rfl⟩
  rw [vertexImage_intShift_sub]
  exact b.isAdjacent
theorem shiftEdge_val (n : Fin 4 → ℤ) (b : PosEdge L 0 0) :
    (shiftEdge n b).1 = edgeImage (intShift n) b.1 := by
  refine Classical.epsilon_spec (p := fun b' : PosEdge L 0 0 =>
    b'.1 = edgeImage (intShift n) b.1) ?_
  refine ⟨⟨edgeImage (intShift n) b.1, ?_⟩, rfl⟩
  obtain ⟨μ, hμ⟩ := b.2
  refine ⟨μ, ?_⟩
  rw [(edgeImage_intShift_ends n b.1).1, (edgeImage_intShift_ends n b.1).2, vertexImage_intShift_sub]
  exact hμ
theorem shiftEdge_terminal (n : Fin 4 → ℤ) (b : PosEdge L 0 0) :
    (shiftEdge n b).1.terminal = vertexImage (intShift n) b.1.terminal := by
  rw [shiftEdge_val, (edgeImage_intShift_ends n b.1).2]
theorem shiftEdge_initial (n : Fin 4 → ℤ) (b : PosEdge L 0 0) :
    (shiftEdge n b).1.initial = vertexImage (intShift n) b.1.initial := by
  rw [shiftEdge_val, (edgeImage_intShift_ends n b.1).1]
theorem shiftEdge_neg_shiftEdge (n : Fin 4 → ℤ) (b : PosEdge L 0 0) :
    shiftEdge (-n) (shiftEdge n b) = b := by
  apply Subtype.ext
  apply InfiniteLattice.Link.ext
  · rw [shiftEdge_initial, shiftEdge_initial, vertexImage_neg_vertexImage]
  · rw [shiftEdge_terminal, shiftEdge_terminal, vertexImage_neg_vertexImage]
theorem shiftEdge_shiftEdge_neg (n : Fin 4 → ℤ) (b : PosEdge L 0 0) :
    shiftEdge n (shiftEdge (-n) b) = b := by
  have h := shiftEdge_neg_shiftEdge (-n) b
  rwa [neg_neg] at h
theorem edgePreimage_castVec_positive (n : Fin 4 → ℤ) (b : PosEdge L 0 0) :
    edgePreimage (spaceShift (castVec n)) b.1 = (shiftEdge (-n) b).1 := by
  refine edgePreimage_spaceShift_eq _ ?_ ?_
  · rw [shiftEdge_initial, coe_vertexImage_intShift]
    simp [intShift, castVec_neg]
  · rw [shiftEdge_terminal, coe_vertexImage_intShift]
    simp [intShift, castVec_neg]
theorem expField_shiftField (n : Fin 4 → ℤ) (ζ : (colourEdges L 0 0).Carrier → ℂ) :
    expField (shiftField (colourEdges L 0 0) n ζ) =
      pushField (spaceShift (castVec n)) (expField ζ) := by
  have hiff := opposite_isPositivelyOriented_iff (meshAt_zero_zero_pos (L := L))
  have hF : ∀ (b : Edge L 0 0) (h : b.IsPositivelyOriented),
      coeffForm (shiftField (colourEdges L 0 0) n ζ) b =
        coeffForm ζ (shiftEdge (-n) ⟨b, h⟩).1 := by
    intro b h
    exact (coeffForm_apply _ h).trans
      (Eq.trans rfl (coeffForm_apply ζ (shiftEdge (-n) ⟨b, h⟩).2).symm)
  funext b
  by_cases h : b.IsPositivelyOriented
  · have hi : edgePreimage (spaceShift (castVec n)) b = (shiftEdge (-n) ⟨b, h⟩).1 :=
      edgePreimage_castVec_positive n ⟨b, h⟩
    simp only [pushField]
    rw [hi]
    exact (expField_of_positive _ h).trans
      ((congrArg (fun M => ComplexMatrix2.matExp (Complex.I • M)) (hF b h)).trans
        (expField_of_positive ζ (shiftEdge _ _).2).symm)
  · have hr : b.opposite.IsPositivelyOriented := (hiff b).2 h
    have hi : edgePreimage (spaceShift (castVec n)) b =
        (shiftEdge (-n) ⟨b.opposite, hr⟩).1.opposite := by
      refine edgePreimage_spaceShift_eq _ ?_ ?_
      · change (b.initial : InfiniteLattice.AmbientSpace) =
          ((shiftEdge (-n) ⟨b.opposite, hr⟩).1.terminal : InfiniteLattice.AmbientSpace) + _
        rw [shiftEdge_terminal, coe_vertexImage_intShift]
        change (b.initial : InfiniteLattice.AmbientSpace) =
          (b.initial : InfiniteLattice.AmbientSpace) + _ + _
        simp [castVec_neg]
      · change (b.terminal : InfiniteLattice.AmbientSpace) =
          ((shiftEdge (-n) ⟨b.opposite, hr⟩).1.initial : InfiniteLattice.AmbientSpace) + _
        rw [shiftEdge_initial, coe_vertexImage_intShift]
        change (b.terminal : InfiniteLattice.AmbientSpace) =
          (b.terminal : InfiniteLattice.AmbientSpace) + _ + _
        simp [castVec_neg]
    have h2 : ¬ ((shiftEdge (-n) ⟨b.opposite, hr⟩).1.opposite).IsPositivelyOriented :=
      fun h' => (hiff _).1 h' (shiftEdge _ _).2
    simp only [pushField]
    rw [hi]
    exact (expField_of_not_positive _ h).trans
      ((congrArg (fun M => (ComplexMatrix2.matExp (Complex.I • M))⁻¹) (hF _ hr)).trans
        (expField_of_not_positive ζ h2).symm)
theorem basisForm_shiftEdge (n : Fin 4 → ℤ) (U : Edge L 0 0 → ComplexMatrix2) (a : Fin 3)
    (b : PosEdge L 0 0) :
    basisForm a (shiftEdge n b) =
      isometryOnTangent (spaceShift (castVec n)) U (basisForm a b) := by
  classical
  have hp : ∀ c : Edge L 0 0, c.IsPositivelyOriented →
      (if c = (shiftEdge n b).1 then ComplexMatrix2.pauliFamily a else 0) =
        tangentEdgeValue U (basisForm a b) (edgePreimage (spaceShift (castVec n)) c) := by
    intro c h
    have hi := edgePreimage_castVec_positive n (⟨c, h⟩ : PosEdge L 0 0)
    have hi' : (edgePreimage (spaceShift (castVec n)) c).IsPositivelyOriented := by
      rw [show edgePreimage (spaceShift (castVec n)) c = _ from hi]
      exact (shiftEdge _ _).2
    have hv : basisForm a b (edgePreimage (spaceShift (castVec n)) c) =
        if edgePreimage (spaceShift (castVec n)) c = b.1 then ComplexMatrix2.pauliFamily a
        else 0 := by
      simp [basisForm, extendOddly, hi']
    simp only [tangentEdgeValue, if_pos hi', hv]
    refine if_congr ?_ rfl rfl
    constructor
    · intro e
      have e' : (⟨c, h⟩ : PosEdge L 0 0) = shiftEdge n b := Subtype.ext e
      rw [show edgePreimage (spaceShift (castVec n)) c = _ from hi, e', shiftEdge_neg_shiftEdge]
    · intro e
      have e' : shiftEdge (-n) (⟨c, h⟩ : PosEdge L 0 0) = b :=
        Subtype.ext ((show _ = edgePreimage (spaceShift (castVec n)) c from hi.symm).trans e)
      rw [← e', shiftEdge_shiftEdge_neg]
  unfold basisForm isometryOnTangent
  funext c
  by_cases h : c.IsPositivelyOriented
  · simp only [extendOddly, if_pos h]
    exact hp c h
  · have hr : c.opposite.IsPositivelyOriented :=
      (opposite_isPositivelyOriented_iff (meshAt_zero_zero_pos (L := L)) c).2 h
    simp only [extendOddly, if_neg h]
    rw [hp _ hr]
    rfl
theorem complexHessianKernel_shift
    (hI : FullSpace.LeftChartAlgebra.SymmetryPairingHessian L 0 0)
    (hT : FullSpace.Translations.ShiftRespectsLevels L 0 0 (castVec n₀))
    (hc : ∀ ζ : (colourEdges L 0 0).Carrier → ℂ,
      expField ζ ∈ fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup)
    (ζ : (colourEdges L 0 0).Carrier → ℂ) (ι' ι : (colourEdges L 0 0).Carrier) :
    complexHessianKernel (expField (shiftField (colourEdges L 0 0) n₀ ζ))
        ((colourEdges L 0 0).translate n₀ ι') ((colourEdges L 0 0).translate n₀ ι) =
      complexHessianKernel (expField ζ) ι' ι := by
  obtain ⟨a', b'⟩ := ι'
  obtain ⟨a, b⟩ := ι
  change complexActionHessian
    (expField (shiftField (colourEdges L 0 0) n₀ ζ))
    (basisForm a' (shiftEdge n₀ b')) (basisForm a (shiftEdge n₀ b)) =
      complexActionHessian (expField ζ) (basisForm a' b') (basisForm a b)
  rw [expField_shiftField, basisForm_shiftEdge n₀ (expField ζ) a' b',
    basisForm_shiftEdge n₀ (expField ζ) a b]
  exact (hI _ _ hT.1 (hT.2.1 0 le_rfl) (hc ζ) _ (basisForm_mem a' b') _
    (basisForm_mem a b)).2 (basisForm_hasFiniteEdgeSupport a' b') (basisForm_hasFiniteEdgeSupport a b)
end Translations
section Near
variable {L : ℕ}
theorem abs_le_euclidNormVec (v : Fin 4 → ℝ) (ν : Fin 4) : |v ν| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
def forwardPosEdge (n : Fin 4 → ℤ) (μ : Fin 4) : PosEdge L 0 0 :=
  ⟨InfiniteLattice.Link.forwardFrom (latticeVertex n) μ, μ,
    by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem nearIndices_finite (y : InfiniteLattice.AmbientSpace) (R : ℝ) :
    (nearIndices (colourEdges L 0 0) y R).Finite := by
  have hT : (Icc (fun ν => ⌊y ν - R⌋) (fun ν => ⌈y ν + R⌉) : Set (Fin 4 → ℤ)).Finite :=
    Set.finite_Icc _ _
  refine (((finite_univ (α := Fin 3)).prod ((finite_univ (α := Fin 4)).prod hT)).image
    (fun p : Fin 3 × Fin 4 × (Fin 4 → ℤ) =>
      ((p.1, forwardPosEdge p.2.2 p.2.1) : (colourEdges L 0 0).Carrier))).subset ?_
  rintro ⟨c, b⟩ hκ
  obtain ⟨μ, hμ⟩ := b.2
  obtain ⟨m, hm⟩ := b.1.initial.2
  have hm' : ∀ ν, ((b.1.initial : Vertex L 0 0) : InfiniteLattice.AmbientSpace) ν = m ν :=
    fun ν => by rw [hm ν, meshAt_zero_zero, mul_one]
  have hd : ∀ ν, |(m ν : ℝ) - y ν| ≤ R := fun ν => by
    have := abs_le_euclidNormVec
      (((b.1.initial : Vertex L 0 0) : InfiniteLattice.AmbientSpace) - y) ν
    simp only [Pi.sub_apply, hm'] at this
    exact this.trans hκ
  refine ⟨(c, μ, m), ⟨mem_univ _, mem_univ _, fun ν => ?_, fun ν => ?_⟩, ?_⟩
  · have h₁ := Int.floor_le (y ν - R)
    have h₂ := (abs_le.1 (hd ν)).1
    have : ((⌊y ν - R⌋ : ℤ) : ℝ) ≤ m ν := by linarith
    exact_mod_cast this
  · have h₁ := Int.le_ceil (y ν + R)
    have h₂ := (abs_le.1 (hd ν)).2
    have : (m ν : ℝ) ≤ ((⌈y ν + R⌉ : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  · have ht : latticeVertex (L := L) m = b.1.initial :=
      Subtype.ext (funext fun ν => (hm ν).symm)
    refine Prod.ext rfl (Subtype.ext (InfiniteLattice.Link.ext ht ?_))
    change latticeVertex m + InfiniteLattice.axisStep _ μ = b.1.terminal
    rw [ht, ← hμ]
    abel
theorem mem_nearIndices_self (ι' : (colourEdges L 0 0).Carrier) :
    ι' ∈ nearIndices (colourEdges L 0 0) ((colourEdges L 0 0).pos ι') 2 := by
  change euclidNormVec (_ - _) ≤ 2
  rw [sub_self]
  simp [euclidNormVec]
theorem isHolomorphicIn_of_differentiable {l : ℕ} {h : ComplexCoordinates l → ℂ}
    (hd : Differentiable ℂ h) {O : Set (ComplexCoordinates l)} (hO : IsOpen O) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => h z := by apply _root_.YangMills.Construction.Tower.FullSpace.EntireLocal.isHolomorphicIn_of_differentiable <;> assumption
theorem isOpen_openPolydisk {l : ℕ} (ρ : ℝ) : IsOpen
    (ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk (0 : ComplexCoordinates l) ρ) := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isOpen_openPolydisk_zero <;> assumption
end Near
end FullSpace.FieldHessianEntries
namespace FieldHessian
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.FullSpace.FieldHessianEntries
open YangMills.Construction.Tower.FaceEdgeFinsets.Unbounded (facesMeeting)
theorem claim_holds (hA : HessianKernel.KernelProperties)
    (hD : FullSpace.ActionDerivsOnFiniteFaces.Claim)
    (hN : FaceEdgeFinsets.FacesAndEdgesFinite)
    (hI : FullSpace.LeftChartAlgebra.SymmetriesPreservePairingsAndHessian)
    (hT : Translations.TranslationProperties)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hF : ComplexMatrix2.NormExpLogBasics) : Claim := by
  intro L hs
  have hc : ∀ ζ : (colourEdges L 0 0).Carrier → ℂ,
      FullSpace.expField ζ ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup :=
    fun ζ => expField_mem hE hF ζ
  have hNk := (hN L hs 0 0 le_rfl).2
  have hDk := hD L 0 0 hs le_rfl
  have hfin : ∀ b' b : FullSpace.PositiveEdge (meshAt L 0 0),
      (facesMeeting ({b'.1, b.1} : Set (FullSpace.Edge L 0 0))).Finite := fun b' b =>
    (hNk.2.1 _ ((Set.finite_singleton _).insert _) (by
      rintro c (rfl | rfl)
      · exact b'.2
      · exact b.2)).1
  have hK := fun (a' a : Fin 3) (b' b : FullSpace.PositiveEdge (meshAt L 0 0))
      (hΩ : (facesMeeting ({b'.1, b.1} : Set (FullSpace.Edge L 0 0))).Finite)
      (ζ : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ) =>
    complexHessianKernel_eq_sum (fun U hU Ω h₁ h₂ => (hDk U hU Ω h₁ h₂).1) a' a b' b hΩ ζ (hc ζ)
  have hV := fun ζ : (colourEdges L 0 0).Carrier → ℂ =>
    ((hA L hs 0 0 le_rfl).2 _ (hc ζ)).2.1
  have hE' := fun (ι' ι : (colourEdges L 0 0).Carrier) {l : ℕ}
      (e : Fin l ≃ nearIndices (colourEdges L 0 0) ((colourEdges L 0 0).pos ι') 2) =>
    exists_differentiable_kernel_representation hK hfin ι' ι e
  refine ⟨fun ρ hρ => ⟨hρ, fun ζ _ ι' ι h => ?_, fun ι' ι => ?_, fun ζ _ n ι' ι => ?_⟩,
    fun ι' ι => ?_, hV⟩
  · refine hV ζ ι' ι fun ⟨p, h₁, h₂⟩ => h ?_
    exact euclid_initial_sub_le_two p h₂ h₁
  · have := (nearIndices_finite (L := L) ((colourEdges L 0 0).pos ι') 2).to_subtype
    let e := (Finite.equivFin (nearIndices (colourEdges L 0 0)
      ((colourEdges L 0 0).pos ι') 2)).symm
    obtain ⟨h, hd, hv⟩ := hE' ι' ι e
    exact ⟨_, e, h, isHolomorphicIn_of_differentiable hd (isOpen_openPolydisk ρ),
      fun ζ _ => hv ζ⟩
  · exact complexHessianKernel_shift (hI L 0 0 hs le_rfl) ((hT L hs 0 0 le_rfl).2.2.2.1 n) hc ζ ι' ι
  · have := (nearIndices_finite (L := L) ((colourEdges L 0 0).pos ι') 2).to_subtype
    let e := (Finite.equivFin (nearIndices (colourEdges L 0 0)
      ((colourEdges L 0 0).pos ι') 2)).symm
    obtain ⟨h, hd, hv⟩ := hE' ι' ι e
    exact ⟨_, _, e, h, ⟨Fin.pos (e.symm ⟨ι', mem_nearIndices_self ι'⟩),
      isHolomorphicIn_of_differentiable hd isOpen_univ⟩, hv⟩
end FieldHessian
end YangMills.Construction.Tower
end

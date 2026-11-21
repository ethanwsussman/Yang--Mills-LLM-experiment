import YangMills.Construction.OneLoopLaw.GaugeColourMomentaAndDifferencesOfFunctionalsProof
import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLatticeProof
import YangMills.Construction.Lattice.CovarianceOfComplexActions
import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAndTheTwoDeterminantsProof
import YangMills.Construction.Towers.TheMassiveFunctionalIsGaugeInvariantProof
import YangMills.Construction.Towers.TheMassiveFunctionalIsInvariantUnderIsometries
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower.MassiveLogDet.IsometryInvariance
open PairedFunctionSpace (linearOfValues transposeOfValues)
open Massive (shiftedDetOn restrictToSubmodule)
section Determinants
variable {ι : Type} {V : Submodule ℝ (ι → ComplexMatrix2)}
theorem shiftedDetOn_eq_det {T : (ι → ComplexMatrix2) → ι → ComplexMatrix2} (T' : V →ₗ[ℝ] V)
    (h : ∀ f : V, (T' f : ι → ComplexMatrix2) = T f) (z : ℝ) :
    shiftedDetOn V T z = LinearMap.det (T' + z • LinearMap.id) := by apply _root_.YangMills.Construction.Tower.HessianDeterminants.shiftedDetOn_eq <;> assumption
theorem shiftedDetOn_eq_of_conj {T₁ T₂ : (ι → ComplexMatrix2) → ι → ComplexMatrix2}
    (e : V ≃ₗ[ℝ] V)
    (h₁ : ∃ T' : V →ₗ[ℝ] V, ∀ f : V, (T' f : ι → ComplexMatrix2) = T₁ f)
    (h₂ : ∃ T' : V →ₗ[ℝ] V, ∀ f : V, (T' f : ι → ComplexMatrix2) = T₂ f)
    (hc' : ∀ (T' : V →ₗ[ℝ] V), (∀ f : V, (T' f : ι → ComplexMatrix2) = T₁ f) →
      ∀ f : V, T₂ (e f) = (e (T' f) : ι → ComplexMatrix2)) (z : ℝ) :
    shiftedDetOn V T₂ z = shiftedDetOn V T₁ z := by
  obtain ⟨A₁, hA₁⟩ := h₁
  obtain ⟨A₂, hA₂⟩ := h₂
  rw [shiftedDetOn_eq_det A₁ hA₁, shiftedDetOn_eq_det A₂ hA₂]
  have hconj : A₂ + z • LinearMap.id = (e : V →ₗ[ℝ] V) ∘ₗ (A₁ + z • LinearMap.id) ∘ₗ
      (e.symm : V →ₗ[ℝ] V) := by
    ext1 g
    obtain ⟨f, rfl⟩ := e.surjective g
    apply Subtype.ext
    simp [hA₂, hc' A₁ hA₁ f]
  rw [hconj, LinearMap.det_conj]
end Determinants
section Pairing
variable {ι : Type}
theorem traceFinsumPairing_comm (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = traceFinsumPairing g f := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelAtZeroSources.traceFinsumPairing_comm <;> assumption
def hermitianComponent (X : ComplexMatrix2) : ComplexMatrix2 := (1 / 2 : ℂ) • (X + X.conjTranspose)
def skewComponent (X : ComplexMatrix2) : ComplexMatrix2 :=
  (-Complex.I / 2) • (X - X.conjTranspose)
theorem conjTranspose_eq_components (X : ComplexMatrix2) :
    X.conjTranspose = hermitianComponent X + (-Complex.I) • skewComponent X := by
  simp only [hermitianComponent, skewComponent, smul_smul]
  have : -Complex.I * (-Complex.I / 2) = -(1 / 2) := by
    have := Complex.I_mul_I
    linear_combination (1 / 2 : ℂ) * this
  rw [this, neg_smul, ← sub_eq_add_neg, ← smul_sub]
  have h2 : X + X.conjTranspose - (X - X.conjTranspose) = (2 : ℂ) • X.conjTranspose := by
    rw [two_smul]; abel
  rw [h2, smul_smul]
  norm_num
theorem fullTrace_conjTranspose_of_mem_traceless {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) : ComplexMatrix2.fullTrace X.conjTranspose = 0 := by apply _root_.YangMills.Construction.Tower.RescaledTrivialStepsProof.fullTrace_conjTranspose_of_traceless <;> assumption
theorem hermitianComponent_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    hermitianComponent X ∈ ComplexMatrix2.hermitianTraceless := by
  have t : ComplexMatrix2.fullTrace X = 0 := hX
  refine ⟨?_, ?_⟩
  · simp only [hermitianComponent, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
    rw [add_comm X.conjTranspose X]
    simp
  · simp only [hermitianComponent, ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_add]
    have t' := fullTrace_conjTranspose_of_mem_traceless hX
    simp only [ComplexMatrix2.fullTrace] at t t'
    rw [t, t']
    simp
theorem skewComponent_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    skewComponent X ∈ ComplexMatrix2.hermitianTraceless := by
  have t : ComplexMatrix2.fullTrace X = 0 := hX
  refine ⟨?_, ?_⟩
  · simp only [skewComponent, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    have : star (-Complex.I / 2) = -(-Complex.I / 2) := by
      simp [Complex.conj_I]
      ring
    rw [this, neg_smul, ← smul_neg, neg_sub]
  · simp only [skewComponent, ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_sub]
    have t' := fullTrace_conjTranspose_of_mem_traceless hX
    simp only [ComplexMatrix2.fullTrace] at t t'
    rw [t, t']
    simp
variable [Finite ι]
theorem traceFinsumPairing_add_right (f g h : ι → ComplexMatrix2) :
    traceFinsumPairing f (g + h) = traceFinsumPairing f g + traceFinsumPairing f h := by apply _root_.YangMills.Construction.Tower.HessianDeterminants.traceFinsumPairing_add_right <;> assumption
theorem traceFinsumPairing_smul_right (c : ℂ) (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f (c • g) = c * traceFinsumPairing f g := by apply _root_.YangMills.Construction.Tower.HessianDeterminants.traceFinsumPairing_smul_right <;> assumption
theorem traceFinsumPairing_add_left (f g h : ι → ComplexMatrix2) :
    traceFinsumPairing (f + g) h = traceFinsumPairing f h + traceFinsumPairing g h := by apply _root_.YangMills.Construction.Tower.HessianDeterminants.traceFinsumPairing_add_left <;> assumption
theorem traceFinsumPairing_smul_left (c : ℂ) (f g : ι → ComplexMatrix2) :
    traceFinsumPairing (c • f) g = c * traceFinsumPairing f g := by
  rw [traceFinsumPairing_comm, traceFinsumPairing_smul_right, traceFinsumPairing_comm g f]
theorem traceFinsumPairing_sub_right (f g h : ι → ComplexMatrix2) :
    traceFinsumPairing f (g - h) = traceFinsumPairing f g - traceFinsumPairing f h := by apply _root_.YangMills.Construction.Tower.MassiveFunctionals.GaugeInvariance.traceFinsumPairing_sub_right <;> assumption
theorem eq_zero_of_traceFinsumPairing_conjTranspose {g : ι → ComplexMatrix2}
    (h : traceFinsumPairing (fun i => (g i).conjTranspose) g = 0) : g = 0 := by apply _root_.YangMills.Construction.Tower.MassiveFunctionals.GaugeInvariance.eq_zero_of_traceFinsumPairing_conjTranspose_self <;> assumption
theorem eq_zero_of_traceFinsumPairing_self {g : ι → ComplexMatrix2}
    (hg : ∀ i, g i ∈ ComplexMatrix2.hermitianTraceless) (h : traceFinsumPairing g g = 0) :
    g = 0 := by
  refine eq_zero_of_traceFinsumPairing_conjTranspose ?_
  have e : (fun i => (g i).conjTranspose) = g := funext fun i => (hg i).1.symm
  rw [e, h]
theorem eq_of_traceFinsumPairing_hermitian {a b : ι → ComplexMatrix2}
    (ha : ∀ i, a i ∈ ComplexMatrix2.traceless) (hb : ∀ i, b i ∈ ComplexMatrix2.traceless)
    (h : ∀ E : ι → ComplexMatrix2, (∀ i, E i ∈ ComplexMatrix2.hermitianTraceless) →
      traceFinsumPairing E a = traceFinsumPairing E b) : a = b := by
  have hd : ∀ i, (a - b) i ∈ ComplexMatrix2.traceless := fun i =>
    ComplexMatrix2.traceless.sub_mem (ha i) (hb i)
  have h0 : ∀ E : ι → ComplexMatrix2, (∀ i, E i ∈ ComplexMatrix2.hermitianTraceless) →
      traceFinsumPairing E (a - b) = 0 := fun E hE => by
    rw [traceFinsumPairing_sub_right, h E hE, sub_self]
  have e : (fun i => ((a - b) i).conjTranspose) =
      (fun i => hermitianComponent ((a - b) i)) +
        (-Complex.I) • fun i => skewComponent ((a - b) i) :=
    funext fun i => conjTranspose_eq_components _
  have hz : a - b = 0 := by
    refine eq_zero_of_traceFinsumPairing_conjTranspose ?_
    rw [e, traceFinsumPairing_add_left, traceFinsumPairing_smul_left,
      h0 _ fun i => hermitianComponent_mem (hd i), h0 _ fun i => skewComponent_mem (hd i)]
    simp
  exact sub_eq_zero.mp hz
end Pairing
section Torus
variable {L n : ℕ}
theorem mem_traceless_of_mem_hermitianTraceless {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.hermitianTraceless) : X ∈ ComplexMatrix2.traceless := h.2
theorem apply_mem_hermitianTraceless {σ : Type} {l : σ → ComplexMatrix2}
    (hl : l ∈ GroupLieProduct.hermitianTracelessFunctions σ) (x : σ) :
    l x ∈ ComplexMatrix2.hermitianTraceless :=
  (Submodule.mem_pi.mp hl) x (mem_univ x)
theorem apply_mem_traceless {σ : Type} {l : σ → ComplexMatrix2}
    (hl : l ∈ GroupLieProduct.tracelessFunctions σ) (x : σ) : l x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.PauliCoefficientNorm.apply_mem_traceless <;> assumption
theorem mem_hermitianTracelessFunctions {σ : Type} {l : σ → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) :
    l ∈ GroupLieProduct.hermitianTracelessFunctions σ :=
  Submodule.mem_pi.mpr fun x _ => hl x
theorem mem_tracelessFunctions_of_mem_hermitian {σ : Type} {l : σ → ComplexMatrix2}
    (hl : l ∈ GroupLieProduct.hermitianTracelessFunctions σ) :
    l ∈ GroupLieProduct.tracelessFunctions σ := by apply _root_.YangMills.Construction.Tower.HessianDeterminants.mem_tracelessFunctions_of_mem <;> assumption
theorem mem_complexEdgeForms_of_mem {B : Edge L n 0 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n 0 0) : B ∈ complexEdgeForms L n 0 0 := by apply _root_.YangMills.DeltaSharedProofs.p8199 <;> assumption
theorem positive_or_opposite_positive (b : Edge L n 0 0) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.isPositivelyOriented_or_opposite <;> assumption
theorem apply_mem_traceless_of_mem_complexEdgeForms {B : Edge L n 0 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) (b : Edge L n 0 0) : B b ∈ ComplexMatrix2.traceless := by
  rcases positive_or_opposite_positive b with h | h
  · exact hB.1 b h
  · have h1 := hB.1 _ h
    rw [hB.2 b] at h1
    simpa using ComplexMatrix2.traceless.neg_mem h1
theorem eq_zero_of_odd_of_positive {Z : Edge L n 0 0 → ComplexMatrix2}
    (hZ : ∀ b, Z b.opposite = -Z b)
    (h : ∀ b : Edge L n 0 0, b.IsPositivelyOriented → Z b = 0) : Z = 0 := by apply _root_.YangMills.Construction.Tower.HessianDeterminants.eq_zero_of_positive_edges <;> assumption
def covDiffTranspose (U : Edge L n 0 0 → ComplexMatrix2) :
    (Edge L n 0 0 → ComplexMatrix2) → Vertex L n 0 0 → ComplexMatrix2 :=
  transposeOfValues (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0) (covDiff U)
theorem covDiff_apply_of_positive (U : Edge L n 0 0 → ComplexMatrix2)
    (l : Vertex L n 0 0 → ComplexMatrix2) {b : Edge L n 0 0} (hb : b.IsPositivelyOriented) :
    covDiff U l b = ComplexMatrix2.conjugateBy (U b) (l b.target) - l b.source := by
  simp [covDiff, extendOddly, if_pos hb]
structure CovDiffTransposeFacts (U : Edge L n 0 0 → ComplexMatrix2) : Prop where
  map_mem : ∀ l ∈ GroupLieProduct.tracelessFunctions (Vertex L n 0 0),
    covDiff U l ∈ complexEdgeForms L n 0 0
  transpose_mem : ∀ B ∈ complexEdgeForms L n 0 0,
    covDiffTranspose U B ∈ GroupLieProduct.tracelessFunctions (Vertex L n 0 0)
  pairing_eq : ∀ B ∈ complexEdgeForms L n 0 0,
    ∀ l ∈ GroupLieProduct.tracelessFunctions (Vertex L n 0 0),
      traceFinsumPairing (covDiffTranspose U B) l = edgeFormPairing B (covDiff U l)
theorem covDiffTransposeFacts [Finite (Vertex L n 0 0)] (hX : CovDiffTransposes.OnTorus L n 0 0)
    {U : Edge L n 0 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup) : CovDiffTransposeFacts U := by
  have hC := hX U hU
  have hlin := hC.covDiff.coe_linear
  have htr := hC.covDiff.isTranspose
  refine ⟨fun l hl => (hC.transposeComp_mem l hl).1,
    fun B hB => (hC.compTranspose_mem B hB).1, fun B hB l hl => ?_⟩
  have hv : covDiffTranspose U B =
      (PairedFunctionSpace.transposeMap (linearOfValues (pairedFunctions (Vertex L n 0 0))
        (edgePairedSpace L n 0 0) (covDiff U)) ⟨B, hB⟩ :
        (pairedFunctions (Vertex L n 0 0)).complexSubmodule).1 := dif_pos hB
  have hl' : covDiff U l = (linearOfValues (pairedFunctions (Vertex L n 0 0))
      (edgePairedSpace L n 0 0) (covDiff U) ⟨l, hl⟩ : (edgePairedSpace L n 0 0).complexSubmodule).1 :=
    (hlin ⟨l, hl⟩).symm
  rw [hv, hl']
  exact htr ⟨B, hB⟩ ⟨l, hl⟩ (Set.toFinite _)
theorem covDiff_mem_edgeFormSpace {U : Edge L n 0 0 → ComplexMatrix2} (hF : CovDiffTransposeFacts U)
    (hU : U ∈ fieldSpace L n 0 0) {l : Vertex L n 0 0 → ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace L n 0 0) : covDiff U l ∈ edgeFormSpace L n 0 0 := by
  have hc : covDiff U l ∈ complexEdgeForms L n 0 0 :=
    hF.map_mem l (mem_tracelessFunctions_of_mem_hermitian hl)
  refine ⟨fun b hb => ?_, hc.2⟩
  rw [covDiff_apply_of_positive U l hb]
  exact ComplexMatrix2.hermitianTraceless.sub_mem
    (ComplexMatrix2.conjugateBy_mem_hermitianTraceless (hU.1 b (mem_univ b)) _
      (apply_mem_hermitianTraceless hl _))
    (apply_mem_hermitianTraceless hl _)
theorem tangentEdgeValue_covDiff {U : Edge L n 0 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup)
    (l : Vertex L n 0 0 → ComplexMatrix2) (c : Edge L n 0 0) :
    tangentEdgeValue U (covDiff U l) c =
      ComplexMatrix2.conjugateBy (U c) (l c.target) - l c.source := by
  by_cases hc : c.IsPositivelyOriented
  · rw [tangentEdgeValue, if_pos hc, covDiff_apply_of_positive U l hc]
  · have hp : c.opposite.IsPositivelyOriented := (positive_or_opposite_positive c).resolve_left hc
    have hd : (U c.opposite).det = 1 := hU.1 _ (mem_univ _)
    have hr : U c = (U c.opposite)⁻¹ := hU.2 c.opposite (mem_univ _)
    rw [tangentEdgeValue, if_neg hc, covDiff_apply_of_positive U l hp, hr]
    change -ComplexMatrix2.conjugateBy (U c.opposite)⁻¹
        (ComplexMatrix2.conjugateBy (U c.opposite) (l c.source) - l c.target) =
      ComplexMatrix2.conjugateBy (U c.opposite)⁻¹ (l c.target) - l c.source
    generalize U c.opposite = W at hd
    generalize l c.source = Y
    generalize l c.target = X
    have h1 : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W (by rw [hd]; exact isUnit_one)
    have h2 : W⁻¹⁻¹ = W := Matrix.nonsing_inv_nonsing_inv W (by rw [hd]; exact isUnit_one)
    have h3 : W⁻¹ * (W * Y * W⁻¹) * W = Y := by
      calc W⁻¹ * (W * Y * W⁻¹) * W = (W⁻¹ * W) * Y * (W⁻¹ * W) := by simp only [mul_assoc]
        _ = Y := by rw [h1, one_mul, mul_one]
    simp only [ComplexMatrix2.conjugateBy, h2, mul_sub, sub_mul, h3]
    abel
theorem tangentEdgeValue_linear_combination (U B B' : Edge L n 0 0 → ComplexMatrix2) (s t : ℂ)
    (c : Edge L n 0 0) :
    tangentEdgeValue U (s • B + t • B') c =
      s • tangentEdgeValue U B c + t • tangentEdgeValue U B' c := by
  by_cases hc : c.IsPositivelyOriented
  · simp only [tangentEdgeValue, if_pos hc, Pi.add_apply, Pi.smul_apply]
  · simp only [tangentEdgeValue, if_neg hc, Pi.add_apply, Pi.smul_apply,
      ComplexMatrix2.conjugateBy, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, neg_add,
      smul_neg]
theorem isometryOnTangent_linear_combination
    (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (U B B' : Edge L n 0 0 → ComplexMatrix2) (s t : ℂ) :
    isometryOnTangent f U (s • B + t • B') =
      s • isometryOnTangent f U B + t • isometryOnTangent f U B' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [isometryOnTangent, extendOddly, if_pos hb, tangentEdgeValue_linear_combination,
      Pi.add_apply, Pi.smul_apply]
  · simp only [isometryOnTangent, extendOddly, if_neg hb, tangentEdgeValue_linear_combination,
      Pi.add_apply, Pi.smul_apply, neg_add, smul_neg]
theorem expTwist_mem_fieldsIn (hL : 1 < L) (hn : 0 < n) {U X : Edge L n 0 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup)
    (hX : X ∈ complexEdgeForms L n 0 0) :
    PeriodicLattice.expTwist X U ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup := by
  have hrev : ∀ b : Edge L n 0 0, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented :=
    fun b hb => PeriodicLattice.Bond.opposite_not_isPositivelyOriented hL
      (by simp only [PeriodicLattice.levelDepth]; omega) hb
  have hdet : ∀ b : Edge L n 0 0, (ComplexMatrix2.matExp (Complex.I • X b) * U b).det = 1 :=
    fun b => by
      have ht : ComplexMatrix2.fullTrace (Complex.I • X b) = 0 :=
        ComplexMatrix2.traceless.smul_mem _ (apply_mem_traceless_of_mem_complexEdgeForms hX b)
      have hb : (U b).det = 1 := hU.1 b (mem_univ b)
      rw [Matrix.det_mul, SpinHarmonics.det_matExp_of_trace_eq_zero ht, hb, one_mul]
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · have e : PeriodicLattice.expTwist X U b = ComplexMatrix2.matExp (Complex.I • X b) * U b :=
        if_pos hb
      rw [e]
      exact hdet b
    · have e : PeriodicLattice.expTwist X U b =
          (ComplexMatrix2.matExp (Complex.I • X b.opposite) * U b.opposite)⁻¹ := if_neg hb
      rw [e]
      change Matrix.det _ = 1
      rw [Matrix.det_nonsing_inv, hdet]
      simp
  · by_cases hb : b.IsPositivelyOriented
    · have e : PeriodicLattice.expTwist X U b = ComplexMatrix2.matExp (Complex.I • X b) * U b :=
        if_pos hb
      have e' : PeriodicLattice.expTwist X U b.opposite =
          (ComplexMatrix2.matExp (Complex.I • X b) * U b)⁻¹ := if_neg (hrev b hb)
      rw [e, e']
    · have hp := (positive_or_opposite_positive b).resolve_left hb
      have e : PeriodicLattice.expTwist X U b =
          (ComplexMatrix2.matExp (Complex.I • X b.opposite) * U b.opposite)⁻¹ := if_neg hb
      have e' : PeriodicLattice.expTwist X U b.opposite =
          ComplexMatrix2.matExp (Complex.I • X b.opposite) * U b.opposite := if_pos hp
      rw [e, e', Matrix.nonsing_inv_nonsing_inv _ (by rw [hdet]; exact isUnit_one)]
structure LatticeMotion (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n) :
    Prop where
  vertex_image : ∀ x : Vertex L n 0 0, f (vertexPreimage (k := 0) (j := 0) f x) = x
  edge_endpoints : ∀ b : Edge L n 0 0,
    (edgePreimage (k := 0) (j := 0) f b).source = vertexPreimage (k := 0) (j := 0) f b.source ∧
      (edgePreimage (k := 0) (j := 0) f b).target = vertexPreimage (k := 0) (j := 0) f b.target
  action_eq : ∀ Y ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup,
    complexAction (pushField (k := 0) (j := 0) f Y) = complexAction Y
theorem vertexPreimage_eq {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hf : Function.Injective f) {x x' : Vertex L n 0 0} (h : f x' = x) :
    vertexPreimage (k := 0) (j := 0) f x = x' := by
  have hs : f (vertexPreimage (k := 0) (j := 0) f x) = x :=
    Classical.epsilon_spec (p := fun y : Vertex L n 0 0 => f y = x) ⟨x', h⟩
  exact Subtype.ext (hf (hs.trans h.symm))
theorem latticeMotion (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hC : PeriodicLattice.ComplexEnergiesIsometryInvariant)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hf : IsDistancePreserving f) (hm : MapsSublatticeOnto 0 0 f) : LatticeMotion f := by
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨⟨w, hw, v, hv, hwv⟩, hrest⟩ :=
    (hT L hL0 hL 0).2.2.2.1 n hn 0 (Nat.zero_le 0) f hf hm
  obtain ⟨-, hbonds, -⟩ := hrest 0 le_rfl
  obtain ⟨π, s, hπ⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w).mp hw
  let r : PeriodicLattice.SignedFrame := (π, s)
  have hr : ∀ x : Fin 4 → ℝ, r.actOnVector x = w x := fun x => by
    funext μ
    simp [PeriodicLattice.SignedFrame.actOnVector, r, hπ]
  let σ : PeriodicLattice.FourTorus L n ≃ PeriodicLattice.FourTorus L n :=
    (PeriodicLattice.SignedFrame.torusEquiv L n r).trans
      (Equiv.addRight (PeriodicLattice.toFourTorus L n v))
  have hσind : PeriodicLattice.IsInducedByAffine σ r v := by
    intro x
    funext μ
    rcases Int.units_eq_one_or (s μ) with h | h <;>
      simp [σ, r, PeriodicLattice.SignedFrame.torusEquiv, PeriodicLattice.signedCoordinatePerm,
        PeriodicLattice.toFourTorus, PeriodicLattice.SignedFrame.actOnVector, h]
  have hσf : ∀ x, σ x = f x := by
    intro x
    obtain ⟨y, rfl⟩ : ∃ y : Fin 4 → ℝ, PeriodicLattice.toFourTorus L n y = x := by
      refine ⟨fun μ => Function.surjInv (QuotientAddGroup.mk_surjective) (x μ), ?_⟩
      funext μ
      exact Function.surjInv_eq QuotientAddGroup.mk_surjective (x μ)
    rw [hσind y, hr y]
    exact (hwv y).symm
  have hinj : Function.Injective f := by
    have : f = σ := funext fun x => (hσf x).symm
    rw [this]
    exact σ.injective
  have hσ : σ ∈ PeriodicLattice.latticeIsometries L n (PeriodicLattice.levelDepth 0 0) := by
    obtain ⟨N, hN⟩ := hv
    refine ⟨r, v, ⟨N, fun μ => ?_⟩, hσind⟩
    rw [meshSize_levelDepth]
    exact hN μ
  have hj : -(n : ℤ) ≤ PeriodicLattice.levelDepth 0 0 := by
    simp only [PeriodicLattice.levelDepth]
    omega
  have hends : ∀ b : Edge L n 0 0,
      (edgePreimage (k := 0) (j := 0) f b).source = vertexPreimage (k := 0) (j := 0) f b.source ∧
        (edgePreimage (k := 0) (j := 0) f b).target =
          vertexPreimage (k := 0) (j := 0) f b.target := by
    intro b
    obtain ⟨b₀, ht, hh⟩ := hbonds.2 b
    exact Classical.epsilon_spec (p := fun b' : Edge L n 0 0 =>
      b'.source = vertexPreimage (k := 0) (j := 0) f b.source ∧
        b'.target = vertexPreimage (k := 0) (j := 0) f b.target)
      ⟨b₀, (vertexPreimage_eq hinj ht.symm).symm, (vertexPreimage_eq hinj hh.symm).symm⟩
  have hbond : ∀ Y : Edge L n 0 0 → ComplexMatrix2,
      pushField (k := 0) (j := 0) f Y = PeriodicLattice.transportGaugeField σ Y := by
    intro Y
    funext b
    obtain ⟨b₀, ht, hh⟩ := hbonds.2 b
    have hex : ∃ b' : Edge L n 0 0,
        (b'.source : PeriodicLattice.FourTorus L n) = σ.symm b.source ∧
          (b'.target : PeriodicLattice.FourTorus L n) = σ.symm b.target :=
      ⟨b₀, by rw [ht, ← hσf, Equiv.symm_apply_apply], by rw [hh, ← hσf, Equiv.symm_apply_apply]⟩
    have h1 : PeriodicLattice.bondPreimage σ b = b₀ := by
      simp only [PeriodicLattice.bondPreimage, dif_pos hex]
      have hc := hex.choose_spec
      refine PeriodicLattice.Bond.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · rw [hc.1, ht, ← hσf, Equiv.symm_apply_apply]
      · rw [hc.2, hh, ← hσf, Equiv.symm_apply_apply]
    have h2 : edgePreimage (k := 0) (j := 0) f b = b₀ := by
      refine PeriodicLattice.Bond.ext ?_ ?_
      · rw [(hends b).1, vertexPreimage_eq hinj ht.symm]
      · rw [(hends b).2, vertexPreimage_eq hinj hh.symm]
    simp only [pushField, PeriodicLattice.transportGaugeField, h1, h2]
  refine ⟨fun x => ?_, hends, fun Y hY => ?_⟩
  · have hx : (x : PeriodicLattice.FourTorus L n) ∈
        f '' (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth 0 0) :
          Set (PeriodicLattice.FourTorus L n)) := by
      rw [hm]
      exact x.2
    obtain ⟨y, hy, hfy⟩ := hx
    exact Classical.epsilon_spec
      (p := fun x' : Vertex L n 0 0 => f (x' : PeriodicLattice.FourTorus L n) = x) ⟨⟨y, hy⟩, hfy⟩
  · have hid := ((hC L n _ σ hL hn hj hσ) _ le_rfl).2.1 (fun _ => (1 : ℂ))
    have e := hid.2.2.1 Y ⟨hY, hY⟩
    have hw1 : ∀ Z : Edge L n 0 0 → ComplexMatrix2,
        PeriodicLattice.plaquetteWeightedEnergy (fun _ => (1 : ℂ)) Z = complexAction Z := fun Z => by
      simp [PeriodicLattice.plaquetteWeightedEnergy, complexAction, complexFaceTerm]
    rw [hbond]
    exact (hw1 _).symm.trans (e.trans (hw1 Y))
theorem complexActionHessian_isometryOnTangent
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n} (hM : LatticeMotion f)
    (hL : 1 < L) (hn : 0 < n) {U : Edge L n 0 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup)
    (hE : ∀ B ∈ complexEdgeForms L n 0 0,
      PeriodicLattice.expTwist (isometryOnTangent f U B) (pushField (k := 0) (j := 0) f U) =
        pushField (k := 0) (j := 0) f (PeriodicLattice.expTwist B U))
    {B B' : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n 0 0)
    (hB' : B' ∈ complexEdgeForms L n 0 0) :
    complexActionHessian (pushField (k := 0) (j := 0) f U)
        (isometryOnTangent f U B) (isometryOnTangent f U B') =
      complexActionHessian U B B' := by
  have key : ∀ s t : ℂ, complexAction (PeriodicLattice.expTwist
        (s • isometryOnTangent f U B + t • isometryOnTangent f U B')
        (pushField (k := 0) (j := 0) f U)) =
      complexAction (PeriodicLattice.expTwist (s • B + t • B') U) := by
    intro s t
    have hS : s • B + t • B' ∈ complexEdgeForms L n 0 0 :=
      (complexEdgeForms L n 0 0).add_mem ((complexEdgeForms L n 0 0).smul_mem s hB)
        ((complexEdgeForms L n 0 0).smul_mem t hB')
    rw [← isometryOnTangent_linear_combination, hE _ hS]
    exact hM.action_eq _ (expTwist_mem_fieldsIn hL hn hU hS)
  have hcancelled' : ∀ s t : ℂ, complexAction (PeriodicLattice.expTwist
        (algebraMap ℂ ℂ s • isometryOnTangent f U B + algebraMap ℂ ℂ t • isometryOnTangent f U B')
        (pushField (k := 0) (j := 0) f U)) =
      complexAction (PeriodicLattice.expTwist (algebraMap ℂ ℂ s • B + algebraMap ℂ ℂ t • B') U) :=
    fun s t => key _ _
  simp only [complexActionHessian, holLeftSecondDeriv, mixedDirectionalDeriv, hcancelled']
section Conjugation
variable [Finite (Vertex L n 0 0)] [Finite (Edge L n 0 0)]
  {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
omit [Finite (Vertex L n 0 0)] in
theorem edgeFormPairing_add_right (a b c : Edge L n 0 0 → ComplexMatrix2) :
    edgeFormPairing a (b + c) = edgeFormPairing a b + edgeFormPairing a c :=
  traceFinsumPairing_add_right _ _ _
omit [Finite (Vertex L n 0 0)] in
theorem edgeFormPairing_sub_right (a b c : Edge L n 0 0 → ComplexMatrix2) :
    edgeFormPairing a (b - c) = edgeFormPairing a b - edgeFormPairing a c :=
  traceFinsumPairing_sub_right _ _ _
omit [Finite (Vertex L n 0 0)] in
theorem eq_of_edgeFormPairing {a b : Edge L n 0 0 → ComplexMatrix2}
    (ha : a ∈ edgeFormSpace L n 0 0) (hb : b ∈ edgeFormSpace L n 0 0)
    (h : ∀ E ∈ edgeFormSpace L n 0 0, edgeFormPairing E a = edgeFormPairing E b) : a = b := by
  have hd : a - b ∈ edgeFormSpace L n 0 0 := (edgeFormSpace L n 0 0).sub_mem ha hb
  have h0 : edgeFormPairing (a - b) (a - b) = 0 := by
    rw [edgeFormPairing_sub_right, h _ hd, sub_self]
  have hz : restrictToPositiveEdges (a - b) = 0 :=
    eq_zero_of_traceFinsumPairing_self (fun i => hd.1 i.1 i.2) h0
  have : a - b = 0 := eq_zero_of_odd_of_positive hd.2 fun c hc => congrFun hz ⟨c, hc⟩
  exact sub_eq_zero.mp this
omit [Finite (Edge L n 0 0)] in
theorem vertexPreimage_bijective (hM : LatticeMotion f) :
    Function.Bijective (vertexPreimage (k := 0) (j := 0) f) :=
  Finite.injective_iff_bijective.mp fun x x' e => Subtype.ext (by
    rw [← hM.vertex_image x, ← hM.vertex_image x', e])
omit [Finite (Edge L n 0 0)] in
theorem traceFinsumPairing_pushSiteFunction (hM : LatticeMotion f)
    (g h : Vertex L n 0 0 → ComplexMatrix2) :
    traceFinsumPairing (pushSiteFunction (k := 0) (j := 0) f g)
        (pushSiteFunction (k := 0) (j := 0) f h) =
      traceFinsumPairing g h :=
  finsum_comp_equiv (Equiv.ofBijective _ (vertexPreimage_bijective hM))
    (f := fun x => ComplexMatrix2.halfTrace (g x * h x))
omit [Finite (Edge L n 0 0)] in
theorem exists_linearEquiv_pushSiteFunction (hM : LatticeMotion f) :
    ∃ e : vertexFunctionSpace L n 0 0 ≃ₗ[ℝ] vertexFunctionSpace L n 0 0,
      ∀ l : vertexFunctionSpace L n 0 0,
        (e l : Vertex L n 0 0 → ComplexMatrix2) = pushSiteFunction (k := 0) (j := 0) f l := by
  let T : vertexFunctionSpace L n 0 0 →ₗ[ℝ] vertexFunctionSpace L n 0 0 :=
    { toFun := fun l => ⟨pushSiteFunction (k := 0) (j := 0) f l,
        mem_hermitianTracelessFunctions fun x => apply_mem_hermitianTraceless l.2 _⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  have hT : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).mpr fun l hl => Subtype.ext (funext fun x => ?_)
    obtain ⟨y, rfl⟩ := (vertexPreimage_bijective hM).2 x
    exact congrFun (congrArg Subtype.val hl) y
  refine ⟨LinearEquiv.ofInjectiveEndo T hT, fun l => ?_⟩
  rw [LinearEquiv.coe_ofInjectiveEndo]
  rfl
structure ConjugationData (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (U : Edge L n 0 0 → ComplexMatrix2) : Prop where
  motion : LatticeMotion f
  mem_fieldSpace : U ∈ fieldSpace L n 0 0
  mem_fieldsIn : U ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup
  transposeFacts : CovDiffTransposeFacts U
  image_transposeFacts : CovDiffTransposeFacts (pushField (k := 0) (j := 0) f U)
  hessian_pairing : ∀ B ∈ complexEdgeForms L n 0 0, ∀ B' ∈ complexEdgeForms L n 0 0,
    edgeFormPairing B (complexHessianOperator U B') = complexActionHessian U B B'
  image_hessian_pairing : ∀ B ∈ complexEdgeForms L n 0 0, ∀ B' ∈ complexEdgeForms L n 0 0,
    edgeFormPairing B (complexHessianOperator (pushField (k := 0) (j := 0) f U) B') =
      complexActionHessian (pushField (k := 0) (j := 0) f U) B B'
  isOrthogonal : LeftChartFacts.IsOrthogonalOn (edgeFormSpace L n 0 0) edgeFormPairing
    (isometryOnTangent f U)
  hessian_eq : ∀ B ∈ complexEdgeForms L n 0 0, ∀ B' ∈ complexEdgeForms L n 0 0,
    complexActionHessian (pushField (k := 0) (j := 0) f U)
        (isometryOnTangent f U B) (isometryOnTangent f U B') =
      complexActionHessian U B B'
variable {U : Edge L n 0 0 → ComplexMatrix2}
omit [Finite (Vertex L n 0 0)] [Finite (Edge L n 0 0)] in
theorem covDiff_pushSiteFunction (hM : LatticeMotion f)
    (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup)
    (l : Vertex L n 0 0 → ComplexMatrix2) :
    covDiff (pushField (k := 0) (j := 0) f U) (pushSiteFunction (k := 0) (j := 0) f l) =
      isometryOnTangent f U (covDiff U l) := by
  change extendOddly _ = extendOddly _
  congr 1
  funext b
  rw [tangentEdgeValue_covDiff hU l]
  simp only [pushField, pushSiteFunction, (hM.edge_endpoints b).1, (hM.edge_endpoints b).2]
omit [Finite (Vertex L n 0 0)] [Finite (Edge L n 0 0)] in
theorem isometryOnTangent_mem (hc : ConjugationData f U) {B : Edge L n 0 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n 0 0) : isometryOnTangent f U B ∈ edgeFormSpace L n 0 0 := by
  obtain ⟨e, he, -⟩ := hc.isOrthogonal
  have := (e ⟨B, hB⟩).2
  rwa [he ⟨B, hB⟩] at this
omit [Finite (Edge L n 0 0)] in
theorem covDiffTranspose_isometryOnTangent (hc : ConjugationData f U)
    {B : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n 0 0) :
    covDiffTranspose (pushField (k := 0) (j := 0) f U) (isometryOnTangent f U B) =
      pushSiteFunction (k := 0) (j := 0) f (covDiffTranspose U B) := by
  obtain ⟨e, he⟩ := exists_linearEquiv_pushSiteFunction (L := L) (n := n) hc.motion
  obtain ⟨-, -, hp⟩ := hc.isOrthogonal
  have hRB := isometryOnTangent_mem hc hB
  have hdt := hc.transposeFacts.transpose_mem B (mem_complexEdgeForms_of_mem hB)
  have hdv := hc.image_transposeFacts.transpose_mem _ (mem_complexEdgeForms_of_mem hRB)
  refine eq_of_traceFinsumPairing_hermitian (apply_mem_traceless hdv)
    (fun x => apply_mem_traceless hdt _) fun E hE => ?_
  obtain ⟨l, hl⟩ := e.surjective ⟨E, mem_hermitianTracelessFunctions hE⟩
  have hlE : pushSiteFunction (k := 0) (j := 0) f (l : Vertex L n 0 0 → ComplexMatrix2) = E := by
    rw [← he l, hl]
  have hTl : pushSiteFunction (k := 0) (j := 0) f (l : Vertex L n 0 0 → ComplexMatrix2) ∈
      vertexFunctionSpace L n 0 0 := by
    rw [hlE]
    exact mem_hermitianTracelessFunctions hE
  have hD := covDiff_mem_edgeFormSpace hc.transposeFacts hc.mem_fieldSpace l.2
  rw [← hlE]
  calc traceFinsumPairing
        (pushSiteFunction (k := 0) (j := 0) f (l : Vertex L n 0 0 → ComplexMatrix2))
        (covDiffTranspose (pushField (k := 0) (j := 0) f U) (isometryOnTangent f U B))
      = traceFinsumPairing
          (covDiffTranspose (pushField (k := 0) (j := 0) f U) (isometryOnTangent f U B))
          (pushSiteFunction (k := 0) (j := 0) f (l : Vertex L n 0 0 → ComplexMatrix2)) :=
        traceFinsumPairing_comm _ _
    _ = edgeFormPairing (isometryOnTangent f U B) (covDiff
          (pushField (k := 0) (j := 0) f U)
          (pushSiteFunction (k := 0) (j := 0) f (l : Vertex L n 0 0 → ComplexMatrix2))) :=
        hc.image_transposeFacts.pairing_eq _ (mem_complexEdgeForms_of_mem hRB) _
          (mem_tracelessFunctions_of_mem_hermitian hTl)
    _ = edgeFormPairing (isometryOnTangent f U B) (isometryOnTangent f U (covDiff U l)) := by
        rw [covDiff_pushSiteFunction hc.motion hc.mem_fieldsIn]
    _ = edgeFormPairing B (covDiff U l) := hp ⟨B, hB⟩ ⟨_, hD⟩
    _ = traceFinsumPairing (covDiffTranspose U B) (l : Vertex L n 0 0 → ComplexMatrix2) :=
        (hc.transposeFacts.pairing_eq B (mem_complexEdgeForms_of_mem hB) _
          (mem_tracelessFunctions_of_mem_hermitian l.2)).symm
    _ = traceFinsumPairing (pushSiteFunction (k := 0) (j := 0) f (covDiffTranspose U B))
          (pushSiteFunction (k := 0) (j := 0) f (l : Vertex L n 0 0 → ComplexMatrix2)) :=
        (traceFinsumPairing_pushSiteFunction hc.motion _ _).symm
    _ = traceFinsumPairing
          (pushSiteFunction (k := 0) (j := 0) f (l : Vertex L n 0 0 → ComplexMatrix2))
          (pushSiteFunction (k := 0) (j := 0) f (covDiffTranspose U B)) :=
        traceFinsumPairing_comm _ _
omit [Finite (Edge L n 0 0)] in
theorem gaugeLaplacian_pushSiteFunction (hc : ConjugationData f U)
    {l : Vertex L n 0 0 → ComplexMatrix2} (hl : l ∈ vertexFunctionSpace L n 0 0) :
    gaugeLaplacian (pushField (k := 0) (j := 0) f U) (pushSiteFunction (k := 0) (j := 0) f l) =
      pushSiteFunction (k := 0) (j := 0) f (gaugeLaplacian U l) := by
  change covDiffTranspose _ (covDiff _ _) =
    pushSiteFunction (k := 0) (j := 0) f (covDiffTranspose U (covDiff U l))
  rw [covDiff_pushSiteFunction hc.motion hc.mem_fieldsIn]
  exact covDiffTranspose_isometryOnTangent hc
    (covDiff_mem_edgeFormSpace hc.transposeFacts hc.mem_fieldSpace hl)
omit [Finite (Vertex L n 0 0)] in
theorem edgeFormPairing_massiveHessian {W : Edge L n 0 0 → ComplexMatrix2}
    (hF : CovDiffTransposeFacts W)
    (hP : ∀ B ∈ complexEdgeForms L n 0 0, ∀ B' ∈ complexEdgeForms L n 0 0,
      edgeFormPairing B (complexHessianOperator W B') = complexActionHessian W B B')
    {a b : Edge L n 0 0 → ComplexMatrix2} (ha : a ∈ complexEdgeForms L n 0 0)
    (hb : b ∈ complexEdgeForms L n 0 0) :
    edgeFormPairing a (massiveHessian W b) = complexActionHessian W a b +
      traceFinsumPairing (covDiffTranspose W a) (covDiffTranspose W b) := by
  have e : massiveHessian W b = complexHessianOperator W b +
      covDiff W (covDiffTranspose W b) := rfl
  rw [e, edgeFormPairing_add_right, hP a ha b hb, hF.pairing_eq a ha _ (hF.transpose_mem b hb)]
theorem massiveHessian_isometryOnTangent (hc : ConjugationData f U)
    (hKU : ∀ B ∈ edgeFormSpace L n 0 0, massiveHessian U B ∈ edgeFormSpace L n 0 0)
    (hKV : ∀ B ∈ edgeFormSpace L n 0 0,
      massiveHessian (pushField (k := 0) (j := 0) f U) B ∈ edgeFormSpace L n 0 0)
    {B : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n 0 0) :
    massiveHessian (pushField (k := 0) (j := 0) f U) (isometryOnTangent f U B) =
      isometryOnTangent f U (massiveHessian U B) := by
  obtain ⟨e, he, hp⟩ := hc.isOrthogonal
  have hRB := isometryOnTangent_mem hc hB
  refine eq_of_edgeFormPairing (hKV _ hRB) (isometryOnTangent_mem hc (hKU B hB)) fun E hE => ?_
  obtain ⟨B', hB'⟩ := e.surjective ⟨E, hE⟩
  have hEB : isometryOnTangent f U (B' : Edge L n 0 0 → ComplexMatrix2) = E := by
    rw [← he B', hB']
  have hq : edgeFormPairing (isometryOnTangent f U (B' : Edge L n 0 0 → ComplexMatrix2))
      (isometryOnTangent f U (massiveHessian U B)) =
        edgeFormPairing (B' : Edge L n 0 0 → ComplexMatrix2) (massiveHessian U B) :=
    hp B' ⟨_, hKU B hB⟩
  have hRB' := isometryOnTangent_mem hc B'.2
  rw [← hEB, hq, edgeFormPairing_massiveHessian hc.image_transposeFacts hc.image_hessian_pairing
    (mem_complexEdgeForms_of_mem hRB') (mem_complexEdgeForms_of_mem hRB),
    edgeFormPairing_massiveHessian hc.transposeFacts hc.hessian_pairing
      (mem_complexEdgeForms_of_mem B'.2) (mem_complexEdgeForms_of_mem hB),
    hc.hessian_eq _ (mem_complexEdgeForms_of_mem B'.2) _ (mem_complexEdgeForms_of_mem hB),
    covDiffTranspose_isometryOnTangent hc B'.2, covDiffTranspose_isometryOnTangent hc hB,
    traceFinsumPairing_pushSiteFunction hc.motion]
theorem massiveLogDet_pushField (hc : ConjugationData f U) (z : ℝ)
    (hSU : ∃ T' : vertexFunctionSpace L n 0 0 →ₗ[ℝ] vertexFunctionSpace L n 0 0,
      ∀ l : vertexFunctionSpace L n 0 0,
        (T' l : Vertex L n 0 0 → ComplexMatrix2) = gaugeLaplacian U l)
    (hSV : ∃ T' : vertexFunctionSpace L n 0 0 →ₗ[ℝ] vertexFunctionSpace L n 0 0,
      ∀ l : vertexFunctionSpace L n 0 0, (T' l : Vertex L n 0 0 → ComplexMatrix2) =
        gaugeLaplacian (pushField (k := 0) (j := 0) f U) l)
    (hFU : ∃ T' : edgeFormSpace L n 0 0 →ₗ[ℝ] edgeFormSpace L n 0 0,
      ∀ B : edgeFormSpace L n 0 0, (T' B : Edge L n 0 0 → ComplexMatrix2) = massiveHessian U B)
    (hFV : ∃ T' : edgeFormSpace L n 0 0 →ₗ[ℝ] edgeFormSpace L n 0 0,
      ∀ B : edgeFormSpace L n 0 0, (T' B : Edge L n 0 0 → ComplexMatrix2) =
        massiveHessian (pushField (k := 0) (j := 0) f U) B) :
    massiveLogDet z (pushField (k := 0) (j := 0) f U) = massiveLogDet z U := by
  obtain ⟨e, he⟩ := exists_linearEquiv_pushSiteFunction (L := L) (n := n) hc.motion
  obtain ⟨eF, heF, -⟩ := hc.isOrthogonal
  have hKU : ∀ B ∈ edgeFormSpace L n 0 0, massiveHessian U B ∈ edgeFormSpace L n 0 0 :=
    fun B hB => by
      obtain ⟨T', h⟩ := hFU
      rw [← h ⟨B, hB⟩]
      exact (T' _).2
  have hKV : ∀ B ∈ edgeFormSpace L n 0 0,
      massiveHessian (pushField (k := 0) (j := 0) f U) B ∈ edgeFormSpace L n 0 0 := fun B hB => by
    obtain ⟨T', h⟩ := hFV
    rw [← h ⟨B, hB⟩]
    exact (T' _).2
  have hs : shiftedDetOn (vertexFunctionSpace L n 0 0)
      (gaugeLaplacian (pushField (k := 0) (j := 0) f U)) z =
        shiftedDetOn (vertexFunctionSpace L n 0 0) (gaugeLaplacian U) z :=
    shiftedDetOn_eq_of_conj e hSU hSV (fun T' hT' l => by
      rw [he, he, hT']
      exact gaugeLaplacian_pushSiteFunction hc l.2) z
  have hf : shiftedDetOn (edgeFormSpace L n 0 0)
      (massiveHessian (pushField (k := 0) (j := 0) f U)) z =
        shiftedDetOn (edgeFormSpace L n 0 0) (massiveHessian U) z :=
    shiftedDetOn_eq_of_conj eF hFU hFV (fun T' hT' B => by
      rw [heF, heF, hT']
      exact massiveHessian_isometryOnTangent hc hKU hKV B.2) z
  simp only [massiveLogDet, hs, hf]
end Conjugation
end Torus
theorem proof (hA1 : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hC : PeriodicLattice.ComplexEnergiesIsometryInvariant)
    (hX : CovDiffTransposes.Claim)
    (hK : HessianKernel.KernelProperties)
    (hD : HessianDeterminants.HessianSymmAndDetsPositive)
    (hI : LeftChartIsometryEquivariance)
    (hG : GaugeAndSymmetryImages.statement) : IsometryInvariance := by
  intro L hL z hz n hn U hU f hf hm
  have hL1 : 1 < L := by have := hL.2; omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hfs, hfb, -⟩ := (hA1 L hL n 0 0 hn le_rfl).2.1
  have : Finite (Vertex L n 0 0) := hfs
  have : Finite (Edge L n 0 0) := hfb
  have hM : LatticeMotion f := latticeMotion hT hC hL hn hf hm
  have hUc : U ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup :=
    ⟨fun b hb => (Matrix.mem_specialUnitaryGroup_iff.mp (hU.1 b hb)).2, hU.2⟩
  have hu : PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup
      (fun _ : Vertex L n 0 0 => (1 : ComplexMatrix2)) := fun _ => Matrix.det_one
  have hGs := (hG L 0 0 hL le_rfl).1 n hn U (fun _ => 1) f hUc hu hf hm
  have hV : pushField (k := 0) (j := 0) f U ∈ fieldSpace L n 0 0 := hGs.2.2.2 hU
  have hVc : pushField (k := 0) (j := 0) f U ∈
      fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup := hGs.2.1
  have hXs := (hX L hL 0 0 le_rfl).1 n hn
  have hKs := (hK L hL 0 0 le_rfl).1 n hn
  have hIs := (hI L 0 0 hL le_rfl).1 n hn f hf hm U hUc
  have hDs := ((hD L hL).2 z hz n hn).1
  have hc : ConjugationData f U :=
    { motion := hM
      mem_fieldSpace := hU
      mem_fieldsIn := hUc
      transposeFacts := covDiffTransposeFacts hXs hUc
      image_transposeFacts := covDiffTransposeFacts hXs hVc
      hessian_pairing := (hKs U hUc).2.2.2.2.1
      image_hessian_pairing := (hKs _ hVc).2.2.2.2.1
      isOrthogonal := hIs.2 hU
      hessian_eq := fun B hB B' hB' =>
        complexActionHessian_isometryOnTangent hM hL1 hn hUc hIs.1 hB hB' }
  have hlog := massiveLogDet_pushField hc z (hDs U hU).1.1 (hDs _ hV).1.1 (hDs U hU).2.1.1
    (hDs _ hV).2.1.1
  change massiveLogDet z _ - _ = massiveLogDet z _ - _
  rw [hlog]
end Tower.MassiveLogDet.IsometryInvariance
end YangMills.Construction
end

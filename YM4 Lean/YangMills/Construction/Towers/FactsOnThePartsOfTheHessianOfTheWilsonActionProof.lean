import YangMills.Construction.Lattice.TransposesOfTheCovariantDerivativesOnALatticeProof
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.FactsOnThePartsOfTheHessianOfTheWilsonAction
import YangMills.Construction.Towers.PlaquettesOfABond
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicOperators YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Tower.CurvatureHessianFacts
theorem bracketSumOrdered_add_left (Y₁ Y₂ Y' : Fin 4 → ComplexMatrix2) :
    bracketSumOrdered (Y₁ + Y₂) Y' = bracketSumOrdered Y₁ Y' + bracketSumOrdered Y₂ Y' := by
  simp only [bracketSumOrdered, Pi.add_apply, add_mul, mul_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  abel
theorem bracketSumOrdered_add_right (Y Y₁ Y₂ : Fin 4 → ComplexMatrix2) :
    bracketSumOrdered Y (Y₁ + Y₂) = bracketSumOrdered Y Y₁ + bracketSumOrdered Y Y₂ := by
  simp only [bracketSumOrdered, Pi.add_apply, add_mul, mul_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  abel
theorem bracketSumOrdered_smul_left (c : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) :
    bracketSumOrdered (c • Y) Y' = c • bracketSumOrdered Y Y' := by
  simp only [bracketSumOrdered, Pi.smul_apply, Finset.smul_sum, smul_sub, smul_mul_assoc,
    mul_smul_comm]
theorem bracketSumOrdered_smul_right (c : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) :
    bracketSumOrdered Y (c • Y') = c • bracketSumOrdered Y Y' := by
  simp only [bracketSumOrdered, Pi.smul_apply, Finset.smul_sum, smul_sub, smul_mul_assoc,
    mul_smul_comm]
def bracketForm (F : ComplexMatrix2) :
    (Fin 4 → ComplexMatrix2) →ₗ[ℂ] (Fin 4 → ComplexMatrix2) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun Y Y' => (Complex.I / 2) * ComplexMatrix2.fullTrace (bracketSumOrdered Y Y' * F))
    (fun Y₁ Y₂ Y' => by
      simp only [bracketSumOrdered_add_left, add_mul, ComplexMatrix2.fullTrace, Matrix.trace_add,
        mul_add])
    (fun c Y Y' => by
      simp only [bracketSumOrdered_smul_left, smul_mul_assoc, ComplexMatrix2.fullTrace,
        Matrix.trace_smul, smul_eq_mul]
      ring)
    (fun Y Y₁ Y₂ => by
      simp only [bracketSumOrdered_add_right, add_mul, ComplexMatrix2.fullTrace, Matrix.trace_add,
        mul_add])
    (fun c Y Y' => by
      simp only [bracketSumOrdered_smul_right, smul_mul_assoc, ComplexMatrix2.fullTrace,
        Matrix.trace_smul, smul_eq_mul]
      ring)
theorem exists_bilinear_finsum {E Pl : Type} [AddCommGroup E] [Module ℂ E] (c : ℂ)
    (Y : Pl → E →ₗ[ℂ] (Fin 4 → ComplexMatrix2)) (Fm : Pl → ComplexMatrix2)
    (hfin : ∀ f, {p | Y p f ≠ 0}.Finite) :
    ∃ β : E →ₗ[ℂ] E →ₗ[ℂ] ℂ, ∀ f f', β f f' =
      c * ∑ᶠ p, (Complex.I / 2) * ComplexMatrix2.fullTrace (bracketSumOrdered (Y p f) (Y p f') * Fm p) := by
  have hl : ∀ f f', (Function.support fun p => bracketForm (Fm p) (Y p f) (Y p f')).Finite :=
    fun f f' => (hfin f).subset fun p hp h0 => hp (by
      have e : Y p f = 0 := by simpa using h0
      simp [e])
  refine ⟨LinearMap.mk₂ ℂ (fun f f' => c * ∑ᶠ p, bracketForm (Fm p) (Y p f) (Y p f'))
    (fun f g f' => ?_) (fun a f f' => ?_) (fun f g g' => ?_) (fun a f f' => ?_), fun f f' => rfl⟩
  · simp only [map_add, LinearMap.add_apply]
    rw [finsum_add_distrib (hl _ _) (hl _ _), mul_add]
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_finsum]
    ring
  · simp only [map_add]
    rw [finsum_add_distrib (hl _ _) (hl _ _), mul_add]
  · simp only [map_smul, smul_eq_mul]
    rw [← mul_finsum]
    ring
theorem epsilon_kernel_spec {N : Type} (w : N → ℝ)
    (β : finsuppFunctions N →ₗ[ℂ] finsuppFunctions N →ₗ[ℂ] ℂ)
    (form : (N → ℂ) → (N → ℂ) → ℂ)
    (hβ : ∀ f f' : finsuppFunctions N, β f f' = form f f')
    (hq : SymmetricKernels.QuadFormKernel w β)
    (P : KernelMatrix N N → Prop)
    (hP : ∀ X, P X ↔ IsSymmKernel w X ∧
      ∀ f : finsuppFunctions N, kernelPairing w X f f = form f f) :
    P (Classical.epsilon P) ∧ ∀ X, P X → X = Classical.epsilon P := by
  obtain ⟨X₀, hX₀, huniq⟩ := hq.1
  have h₀ : P X₀ := (hP _).2 ⟨hX₀.1, fun f => (hX₀.2 f).trans (hβ f f)⟩
  have hs : P (Classical.epsilon P) := Classical.epsilon_spec ⟨X₀, h₀⟩
  have u : ∀ X, P X → X = X₀ := fun X h =>
    huniq X ⟨((hP X).1 h).1, fun f => (((hP X).1 h).2 f).trans (hβ f f).symm⟩
  exact ⟨hs, fun X h => (u X h).trans (u _ hs).symm⟩
theorem real_smul_eq_complex_smul (η : ℝ) (X : ComplexMatrix2) : η • X = (η : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
theorem conjugateBy_mem_traceless_of_det {V X : ComplexMatrix2} (hV : V.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
theorem defect_mem_traceless (η : ℝ) {T X : Fin 4 → ComplexMatrix2} (hT : ∀ i, (T i).det = 1)
    (hX : ∀ i, X i ∈ ComplexMatrix2.traceless) :
    η • ∑ i, transportSign i • (ComplexMatrix2.conjugateBy (T i) (X i) - X i) ∈
      ComplexMatrix2.traceless := by
  rw [real_smul_eq_complex_smul]
  exact ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.sum_mem fun i _ =>
    ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.sub_mem
      (conjugateBy_mem_traceless_of_det (hT i) (hX i)) (hX i)))
theorem ofPauliCoeffs_add {σ : Type} (f g : Fin 3 × σ → ℂ) (s : σ) :
    ofPauliCoeffs (f + g) s = ofPauliCoeffs f s + ofPauliCoeffs g s := by
  simp only [ofPauliCoeffs, Pi.add_apply, add_smul, Finset.sum_add_distrib]
theorem ofPauliCoeffs_smul {σ : Type} (c : ℂ) (f : Fin 3 × σ → ℂ) (s : σ) :
    ofPauliCoeffs (c • f) s = c • ofPauliCoeffs f s := by
  simp only [ofPauliCoeffs, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]
section PeriodicSide
variable {L n k : ℕ}
theorem forwardFrom_isPositivelyOriented (x : Vertex L n k 0) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
theorem faceEdge_isPositivelyOriented (p : Face L n k 0) (i : Fin 4) :
    (faceEdge p i).IsPositivelyOriented := by
  fin_cases i <;> exact forwardFrom_isPositivelyOriented _ _
theorem faceEdge_mem_faceEdges (p : Face L n k 0) (i : Fin 4) :
    faceEdge p i ∈ faceEdges p :=
  List.getElem_mem _
abbrev edgeField (f : Fin 3 × PositiveEdge L n k 0 → ℂ) : Edge L n k 0 → ComplexMatrix2 :=
  (edgePauliCoordinates L n k 0).ofCoeffs f
theorem edgeField_apply (f : Fin 3 × PositiveEdge L n k 0 → ℂ) {b : Edge L n k 0}
    (h : b.IsPositivelyOriented) : edgeField f b = ofPauliCoeffs f ⟨b, h⟩ := by
  simp [edgeField, edgePauliCoordinates, extendOddly, h]
def edgeFieldLinear : (Fin 3 × PositiveEdge L n k 0 → ℂ) →ₗ[ℂ] (Edge L n k 0 → ComplexMatrix2) where
  toFun := edgeField
  map_add' f g := by
    funext b
    simp only [edgeField, edgePauliCoordinates, extendOddly, Pi.add_apply]
    split_ifs <;> simp [ofPauliCoeffs_add, add_comm]
  map_smul' c f := by
    funext b
    simp only [edgeField, edgePauliCoordinates, extendOddly, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [ofPauliCoeffs_smul]
def transportedLinear (U : Edge L n k 0 → ComplexMatrix2) (p : Face L n k 0) :
    (Edge L n k 0 → ComplexMatrix2) →ₗ[ℂ] (Fin 4 → ComplexMatrix2) where
  toFun B := transportedForm U B p
  map_add' B B' := by
    funext i
    simp [transportedForm, ComplexMatrix2.conjugateBy, mul_add, add_mul, smul_add]
  map_smul' c B := by
    funext i
    simp only [transportedForm, ComplexMatrix2.conjugateBy, Pi.smul_apply, mul_smul_comm,
      smul_mul_assoc, RingHom.id_apply]
    exact smul_comm _ _ _
theorem faceTransports_det {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup) (p : Face L n k 0)
    (i : Fin 4) : (faceTransports U p i).det = 1 := by
  have h : ∀ b, (U b).det = 1 := fun b => hU.1 b (mem_univ _)
  have hi : ∀ b, ((U b)⁻¹).det = 1 := fun b => by
    rw [Matrix.det_nonsing_inv, h]
    simp
  have h3 : (faceTransports U p 2).det = 1 := by
    simp [faceTransports, Matrix.det_mul, h, hi]
  have h4 : (faceTransports U p 3).det = 1 := by
    rw [faceTransports_three U (fun b => hU.2 b (mem_univ _)) p, Matrix.det_mul, h3, hi, one_mul]
  fin_cases i
  · simp [faceTransports]
  · simp [faceTransports, h]
  · exact h3
  · exact h4
theorem finite_faces_touching (hfaces : FacesContainingEdge.Periodic L n k 0)
    {f : Fin 3 × PositiveEdge L n k 0 → ℂ} (hf : (Function.support f).Finite) :
    {p : Face L n k 0 | ∃ i, edgeField f (faceEdge p i) ≠ 0}.Finite := by
  refine (hfaces.2.2 (Prod.snd '' Function.support f) (hf.image _)).subset ?_
  rintro p ⟨i, hi⟩
  rw [edgeField_apply f (faceEdge_isPositivelyOriented p i)] at hi
  have : ∃ a, f (a, ⟨faceEdge p i, faceEdge_isPositivelyOriented p i⟩) ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hi (Finset.sum_eq_zero fun a _ => by rw [hno a, zero_smul])
  obtain ⟨a, ha⟩ := this
  exact ⟨⟨faceEdge p i, faceEdge_isPositivelyOriented p i⟩, ⟨_, ha, rfl⟩, faceEdge_mem_faceEdges p i⟩
theorem onPeriodicSide_holds (hfaces : FacesContainingEdge.Periodic L n k 0)
    (hq : ∀ β : finsuppFunctions (Fin 3 × PositiveEdge L n k 0) →ₗ[ℂ]
        finsuppFunctions (Fin 3 × PositiveEdge L n k 0) →ₗ[ℂ] ℂ,
      SymmetricKernels.QuadFormKernel (meshWeight (finestMesh L k)) β) :
    OnPeriodicSide L n k := by
  refine ⟨fun U => ?_, fun U hU b hb p =>
    defect_mem_traceless _ (faceTransports_det hU p) fun i =>
      hb.1 _ (faceEdge_isPositivelyOriented p i)⟩
  obtain ⟨β, hβ⟩ := exists_bilinear_finsum ((finestMesh L k : ℂ) ^ 4)
    (fun p => (transportedLinear U p).comp (edgeFieldLinear.comp
      (finsuppFunctions (Fin 3 × PositiveEdge L n k 0)).subtype))
    (curvatureMatrix U) (fun f => (finite_faces_touching hfaces f.2).subset fun p hp => by
      by_contra hno
      refine hp ?_
      funext i
      have e : edgeField (f : Fin 3 × PositiveEdge L n k 0 → ℂ) (faceEdge p i) = 0 := by
        by_contra hne
        exact hno ⟨i, hne⟩
      change transportedForm U (edgeField _) p i = 0
      simp [transportedForm, e, ComplexMatrix2.conjugateBy])
  have hβ' : ∀ f f' : finsuppFunctions (Fin 3 × PositiveEdge L n k 0),
      β f f' = curvatureBilinear U (edgeField (f : Fin 3 × PositiveEdge L n k 0 → ℂ))
        (edgeField (f' : Fin 3 × PositiveEdge L n k 0 → ℂ)) := hβ
  obtain ⟨h₁, h₂⟩ := epsilon_kernel_spec (meshWeight (finestMesh L k)) β
    (fun f f' => curvatureBilinear U (edgeField f) (edgeField f')) hβ' (hq β)
    (IsCurvatureKernel U) (fun _ => Iff.rfl)
  exact ⟨⟨β, hβ'⟩, h₁, h₂⟩
end PeriodicSide
end YangMills.Construction.Tower.CurvatureHessianFacts
namespace YangMills.Construction.Tower.FullSpace.CurvatureHessianAtInfinity
open YangMills.Construction.Tower.CurvatureHessianFacts
  (exists_bilinear_finsum epsilon_kernel_spec defect_mem_traceless ofPauliCoeffs_add
    ofPauliCoeffs_smul)
section Unbounded
variable {L k : ℕ}
theorem forwardFrom_isPositivelyOriented (x : Vertex L k 0) (μ : Fin 4) :
    (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem faceEdge_isPositivelyOriented (p : Face L k 0) (i : Fin 4) :
    (faceEdge p i).IsPositivelyOriented := by
  fin_cases i <;> exact forwardFrom_isPositivelyOriented _ _
theorem faceEdge_mem_faceEdges (p : Face L k 0) (i : Fin 4) :
    faceEdge p i ∈ faceEdges p :=
  List.getElem_mem _
abbrev edgeField (f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) : Edge L k 0 → ComplexMatrix2 :=
  (edgePauliCoordinates L k 0).ofCoeffs f
theorem edgeField_apply (f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) {b : Edge L k 0}
    (h : b.IsPositivelyOriented) : edgeField f b = ofPauliCoeffs f ⟨b, h⟩ := by
  simp [edgeField, edgePauliCoordinates, extendOddly, h]
def edgeFieldLinear : (Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) →ₗ[ℂ] (Edge L k 0 → ComplexMatrix2) where
  toFun := edgeField
  map_add' f g := by
    funext b
    simp only [edgeField, edgePauliCoordinates, extendOddly, Pi.add_apply]
    split_ifs <;> simp [ofPauliCoeffs_add, add_comm]
  map_smul' c f := by
    funext b
    simp only [edgeField, edgePauliCoordinates, extendOddly, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [ofPauliCoeffs_smul]
def transportedLinear (U : Edge L k 0 → ComplexMatrix2) (p : Face L k 0) :
    (Edge L k 0 → ComplexMatrix2) →ₗ[ℂ] (Fin 4 → ComplexMatrix2) where
  toFun B := transportedForm U B p
  map_add' B B' := by
    funext i
    simp [transportedForm, ComplexMatrix2.conjugateBy, mul_add, add_mul, smul_add]
  map_smul' c B := by
    funext i
    simp only [transportedForm, ComplexMatrix2.conjugateBy, Pi.smul_apply, mul_smul_comm,
      smul_mul_assoc, RingHom.id_apply]
    exact smul_comm _ _ _
theorem faceTransports_det {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup) (p : Face L k 0)
    (i : Fin 4) : (faceTransports U p i).det = 1 := by
  have h : ∀ b, (U b).det = 1 := fun b => hU.1 b
  have hi : ∀ b, ((U b)⁻¹).det = 1 := fun b => by
    rw [Matrix.det_nonsing_inv, h]
    simp
  have h3 : (faceTransports U p 2).det = 1 := by
    simp [faceTransports, Matrix.det_mul, h, hi]
  have h4 : (faceTransports U p 3).det = 1 := by
    rw [faceTransports_three U (fun b => hU.2 b) p, Matrix.det_mul, h3, hi, one_mul]
  fin_cases i
  · simp [faceTransports]
  · simp [faceTransports, h]
  · exact h3
  · exact h4
theorem finite_faces_touching (hfaces : FacesContainingEdge.OnFullSpace L k 0)
    {f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ} (hf : (Function.support f).Finite) :
    {p : Face L k 0 | ∃ i, edgeField f (faceEdge p i) ≠ 0}.Finite := by
  refine (hfaces.2.2 (Prod.snd '' Function.support f) (hf.image _)).subset ?_
  rintro p ⟨i, hi⟩
  rw [edgeField_apply f (faceEdge_isPositivelyOriented p i)] at hi
  have : ∃ a, f (a, ⟨faceEdge p i, faceEdge_isPositivelyOriented p i⟩) ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hi (Finset.sum_eq_zero fun a _ => by rw [hno a, zero_smul])
  obtain ⟨a, ha⟩ := this
  exact ⟨⟨faceEdge p i, faceEdge_isPositivelyOriented p i⟩, ⟨_, ha, rfl⟩, faceEdge_mem_faceEdges p i⟩
theorem onFullSpace_holds (hfaces : FacesContainingEdge.OnFullSpace L k 0)
    (hq : ∀ β : finsuppFunctions (Fin 3 × PositiveEdge (meshAt L k 0)) →ₗ[ℂ]
        finsuppFunctions (Fin 3 × PositiveEdge (meshAt L k 0)) →ₗ[ℂ] ℂ,
      SymmetricKernels.QuadFormKernel (meshWeight (finestMesh L k)) β) :
    CurvatureHessianFacts.OnFullSpace L k := by
  refine ⟨fun U => ?_, fun U hU b hb p =>
    defect_mem_traceless _ (faceTransports_det hU p) fun i =>
      hb.1 _ (faceEdge_isPositivelyOriented p i)⟩
  obtain ⟨β, hβ⟩ := exists_bilinear_finsum ((finestMesh L k : ℂ) ^ 4)
    (fun p => (transportedLinear U p).comp (edgeFieldLinear.comp
      (finsuppFunctions (Fin 3 × PositiveEdge (meshAt L k 0))).subtype))
    (curvatureMatrix U) (fun f => (finite_faces_touching hfaces f.2).subset fun p hp => by
      by_contra hno
      refine hp ?_
      funext i
      have e : edgeField (f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ)
          (faceEdge p i) = 0 := by
        by_contra hne
        exact hno ⟨i, hne⟩
      change transportedForm U (edgeField _) p i = 0
      simp [transportedForm, e, ComplexMatrix2.conjugateBy])
  have hβ' : ∀ f f' : finsuppFunctions (Fin 3 × PositiveEdge (meshAt L k 0)),
      β f f' = curvatureBilinear U
        (edgeField (f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ))
        (edgeField (f' : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ)) := hβ
  obtain ⟨h₁, h₂⟩ := epsilon_kernel_spec (meshWeight (finestMesh L k)) β
    (fun f f' => curvatureBilinear U (edgeField f) (edgeField f')) hβ' (hq β)
    (IsCurvatureKernel U) (fun _ => Iff.rfl)
  exact ⟨⟨β, hβ'⟩, h₁, h₂⟩
end Unbounded
end YangMills.Construction.Tower.FullSpace.CurvatureHessianAtInfinity
namespace YangMills.Construction.Tower.CurvatureHessianFacts
theorem claim_holds (h₁ : SymmetricKernels.Claim) (h₂ : FacesContainingEdge.Holds) :
    Claim := by
  intro L hL k _
  have hL13 : 13 ≤ L := hL.2
  have hpos : 0 < meshAt L k 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    exact zpow_pos this _
  have hw : ∀ {N : Type} (ι : N), 0 < (fun _ : N => meshAt L k 0 ^ 4) ι :=
    fun _ => pow_pos hpos 4
  have p₂ := h₂ L hL k 0 (Nat.zero_le _)
  refine ⟨fun n _ => onPeriodicSide_holds (p₂.1 n ‹_›) fun β => (h₁.1 _ _ hw β).2,
    FullSpace.CurvatureHessianAtInfinity.onFullSpace_holds p₂.2 fun β => (h₁.1 _ _ hw β).2⟩
end YangMills.Construction.Tower.CurvatureHessianFacts
end

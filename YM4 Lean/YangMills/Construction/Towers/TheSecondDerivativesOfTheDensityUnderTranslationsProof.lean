import YangMills.Construction.Towers.FactsOfAbelianFields
import YangMills.Construction.Towers.LogarithmsSectorsAndTheDensity
import YangMills.Construction.Towers.TheAbelianOperatorsAsValuesOfTheOperatorFunctionsProof
import YangMills.Construction.Towers.TheRowSumsOfTheSecondDerivativesOfTheDensityVanishProof
import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensityUnderTranslations
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.ShiftInvariance
open PeriodicOperators (PeriodicData Represents intShift shiftEdge colourVertices colourEdges
  castVec)
open AbelianFieldFacts UnitLatticeL2 UnitGaugeDirections SectorDecomposition
  OperatorCalculus OneLoopNotation
section IndexShift
variable {J : Type}
theorem lpShift_apply {σ : J → J} (hσ : Function.Bijective σ) (f : lp (fun _ : J => ℂ) 2)
    (ι : J) : lpShift σ f (σ ι) = f ι := by
  let e : J ≃ J := Equiv.ofBijective σ hσ
  have hm : Memℓp (fun κ => f (e.symm κ)) 2 := by
    have h0 := (memℓp_gen_iff (p := 2) (by norm_num)).1 (lp.memℓp f)
    exact (memℓp_gen_iff (by norm_num)).2
      ((e.symm.summable_iff (f := fun κ => ‖f κ‖ ^ (2 : ENNReal).toReal)).2 h0)
  have h : ∃ g : lp (fun _ : J => ℂ) 2, ∀ κ : J, g (σ κ) = f κ :=
    ⟨⟨_, hm⟩, fun κ => congrArg f (e.symm_apply_apply κ)⟩
  exact Classical.epsilon_spec h ι
open Classical in
theorem lpShift_basisVec {σ : J → J} (hσ : Function.Bijective σ) (ι : J) :
    lpShift σ (basisVec ι) = basisVec (σ ι) := by
  refine lp.ext (funext fun κ => ?_)
  obtain ⟨κ, rfl⟩ := hσ.2 κ
  rw [lpShift_apply hσ]
  by_cases h : κ = ι
  · subst h
    simp [basisVec]
  · have h' : σ κ ≠ σ ι := fun e => h (hσ.1 e)
    simp [basisVec, lp.single_apply, h, h']
open Classical in
theorem lpShift_intertwine {σ : J → J} (hσ : Function.Bijective σ)
    (hU : IsUnitaryMap (lpShift σ))
    (T T' : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2)
    (h : ∀ ι' ι, matrixEntry T' (σ ι') (σ ι) = matrixEntry T ι' ι) (f : lp (fun _ : J => ℂ) 2) :
    lpShift σ (T f) = T' (lpShift σ f) := by
  obtain ⟨hlin, -, hnorm⟩ := hU
  let Vc : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2 :=
    (hlin.mk' (lpShift σ)).mkContinuous 1 fun g => by simp [hnorm]
  have hV : ∀ g, Vc g = lpShift σ g := fun g => rfl
  have hunit : ∀ ι, Vc (T (basisVec ι)) = T' (Vc (basisVec ι)) := by
    intro ι
    rw [hV, hV, lpShift_basisVec hσ]
    refine lp.ext (funext fun κ => ?_)
    obtain ⟨κ, rfl⟩ := hσ.2 κ
    rw [lpShift_apply hσ]
    exact (h κ ι).symm
  have hs : HasSum (fun ι => lp.single 2 ι (f ι)) f := lp.hasSum_single (by norm_num) f
  have hsingle : ∀ ι, lp.single 2 ι (f ι) = f ι • (basisVec ι : lp (fun _ : J => ℂ) 2) := by
    intro ι
    refine lp.ext (funext fun κ => ?_)
    by_cases hκ : κ = ι
    · subst hκ
      simp [basisVec]
    · simp [basisVec, lp.single_apply, hκ]
  have h₁ := (Vc.comp T).hasSum hs
  have h₂ := (T'.comp Vc).hasSum hs
  have e : (fun ι => (Vc.comp T) (lp.single 2 ι (f ι))) =
      fun ι => (T'.comp Vc) (lp.single 2 ι (f ι)) := by
    funext ι
    rw [hsingle ι]
    simp only [ContinuousLinearMap.comp_apply, map_smul, hunit ι]
  rw [e] at h₁
  exact h₁.unique h₂
end IndexShift
section UnitLattice
variable {L : ℕ}
def vertexOfInt (L : ℕ) (n : Fin 4 → ℤ) : FullSpace.Vertex L 0 0 :=
  ⟨castVec n, n, fun μ => by simp [castVec, meshAt]⟩
theorem vertexOfInt_zero : vertexOfInt L 0 = 0 :=
  Subtype.ext (funext fun μ => by simp [vertexOfInt, castVec])
theorem vertexImage_intShift (n : Fin 4 → ℤ) (x : FullSpace.Vertex L 0 0) :
    FullSpace.vertexImage (intShift n) x = x + vertexOfInt L n := by
  have h : ∃ x' : FullSpace.Vertex L 0 0, (x' : InfiniteLattice.AmbientSpace) =
      intShift n (x : InfiniteLattice.AmbientSpace) := ⟨x + vertexOfInt L n, rfl⟩
  exact Subtype.ext (Classical.epsilon_spec h)
def edgeTranslate (v : FullSpace.Vertex L 0 0) (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.PositiveEdge (meshAt L 0 0) :=
  ⟨⟨b.1.initial + v, b.1.terminal + v, b.1.isAdjacent.imp fun μ h => h.imp
      (fun e => by rw [add_sub_add_right_eq_sub]; exact e)
      (fun e => by rw [add_sub_add_right_eq_sub]; exact e)⟩,
    b.2.imp fun μ e => by
      show b.1.terminal + v - (b.1.initial + v) = _
      rw [add_sub_add_right_eq_sub]; exact e⟩
theorem edgeTranslate_edgeTranslate (v w : FullSpace.Vertex L 0 0)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    edgeTranslate w (edgeTranslate v b) = edgeTranslate (v + w) b := by
  refine Subtype.ext (InfiniteLattice.Link.ext ?_ ?_)
  · exact add_assoc _ _ _
  · exact add_assoc _ _ _
theorem edgeTranslate_zero (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    edgeTranslate (0 : FullSpace.Vertex L 0 0) b = b := by
  refine Subtype.ext (InfiniteLattice.Link.ext ?_ ?_)
  · exact add_zero _
  · exact add_zero _
theorem edgeTranslate_bijective (v : FullSpace.Vertex L 0 0) :
    Function.Bijective (edgeTranslate v) := by
  refine Function.bijective_iff_has_inverse.2 ⟨edgeTranslate (-v), fun b => ?_, fun b => ?_⟩
  · rw [edgeTranslate_edgeTranslate, add_neg_cancel, edgeTranslate_zero]
  · rw [edgeTranslate_edgeTranslate, neg_add_cancel, edgeTranslate_zero]
theorem edgeTranslate_forwardEdge (v y : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    edgeTranslate v (FullSpace.forwardEdge y μ) = FullSpace.forwardEdge (y + v) μ := by
  refine Subtype.ext (InfiniteLattice.Link.ext rfl ?_)
  exact add_right_comm _ _ _
theorem shiftEdge_eq_edgeTranslate (n : Fin 4 → ℤ) (b : PeriodicOperators.PosEdge L 0 0) :
    shiftEdge n b = edgeTranslate (vertexOfInt L n) b := by
  have hm : ∃ b' : FullSpace.Edge L 0 0,
      b'.initial = FullSpace.vertexImage (intShift n) b.1.initial ∧
        b'.terminal = FullSpace.vertexImage (intShift n) b.1.terminal :=
    ⟨(edgeTranslate (vertexOfInt L n) b).1, (vertexImage_intShift n _).symm,
      (vertexImage_intShift n _).symm⟩
  have hb := Classical.epsilon_spec hm
  have e : FullSpace.edgeImage (intShift n) b.1 = (edgeTranslate (vertexOfInt L n) b).1 :=
    InfiniteLattice.Link.ext (hb.1.trans (vertexImage_intShift n _))
      (hb.2.trans (vertexImage_intShift n _))
  have h : ∃ b' : PeriodicOperators.PosEdge L 0 0,
      b'.1 = FullSpace.edgeImage (intShift n) b.1 :=
    ⟨edgeTranslate (vertexOfInt L n) b, e.symm⟩
  exact Subtype.ext ((Classical.epsilon_spec h).trans e)
theorem vertexColour_translate (n : Fin 4 → ℤ) (ι : VertexIndex L) :
    (colourVertices L 0 0).translate n ι = (ι.1, ι.2 + vertexOfInt L n) :=
  Prod.ext rfl (vertexImage_intShift n ι.2)
theorem edgeColour_translate (n : Fin 4 → ℤ) (ι : EdgeIndex L) :
    (colourEdges L 0 0).translate n ι = (ι.1, edgeTranslate (vertexOfInt L n) ι.2) :=
  Prod.ext rfl (shiftEdge_eq_edgeTranslate n ι.2)
theorem vertexColour_translate_bijective (n : Fin 4 → ℤ) :
    Function.Bijective ((colourVertices L 0 0).translate n : VertexIndex L → VertexIndex L) := by
  have e : ((colourVertices L 0 0).translate n : VertexIndex L → VertexIndex L) =
      Prod.map id (fun x => x + vertexOfInt L n) := funext (vertexColour_translate n)
  rw [e]
  exact Function.Bijective.prodMap Function.bijective_id
    ⟨add_left_injective _, fun y => ⟨y - vertexOfInt L n, sub_add_cancel _ _⟩⟩
theorem edgeColour_translate_bijective (n : Fin 4 → ℤ) :
    Function.Bijective ((colourEdges L 0 0).translate n : EdgeIndex L → EdgeIndex L) := by
  have e : ((colourEdges L 0 0).translate n : EdgeIndex L → EdgeIndex L) =
      Prod.map id (edgeTranslate (vertexOfInt L n)) := funext (edgeColour_translate n)
  rw [e]
  exact Function.Bijective.prodMap Function.bijective_id (edgeTranslate_bijective _)
end UnitLattice
section KernelTranslation
variable {L : ℕ}
theorem shiftEdge_zero (b : PeriodicOperators.PosEdge L 0 0) :
    shiftEdge 0 b = b := by
  rw [shiftEdge_eq_edgeTranslate, vertexOfInt_zero, edgeTranslate_zero]
theorem vertexColour_translate_zero (ι : VertexIndex L) :
    (colourVertices L 0 0).translate 0 ι = ι := by
  rw [vertexColour_translate, vertexOfInt_zero]
  exact Prod.ext rfl (add_zero _)
theorem edgeColour_translate_zero (ι : EdgeIndex L) : (colourEdges L 0 0).translate 0 ι = ι := by
  rw [edgeColour_translate, vertexOfInt_zero, edgeTranslate_zero]
theorem kernel_translate {I : PeriodicData}
    {T : (FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) → I.Carrier → I.Carrier → ℂ}
    (hT : KernelEntriesTrigPoly L I T) (h0 : ∀ ι, I.translate 0 ι = ι)
    (n : Fin 4 → ℤ) {θ θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
    (hθ : ∀ b : PeriodicOperators.PosEdge L 0 0, θ' (shiftEdge n b) = θ b)
    (ι' ι : I.Carrier) : T θ' (I.translate n ι') (I.translate n ι) = T θ ι' ι := by
  obtain ⟨P, -, hP⟩ := hT ι' ι
  have e₂ := hP θ 0
  rw [h0, h0] at e₂
  rw [hP θ' n, e₂]
  exact congrArg P (funext fun b => by rw [hθ, shiftEdge_zero])
theorem laplacianOp_entry {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
    (hO : AbelianOperators θ)
    (hK : CompositesAreKernels (FullSpace.abelianLinkField θ)) (ι' ι : VertexIndex L) :
    matrixEntry (laplacianOp θ) ι' ι = abelianLaplacianKernel θ ι' ι := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.OpFunValues.matrixEntry_laplacianOp <;> assumption
theorem massiveOp_entry {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
    (hO : AbelianOperators θ)
    (hK : CompositesAreKernels (FullSpace.abelianLinkField θ)) (ι' ι : EdgeIndex L) :
    matrixEntry (massiveOp θ) ι' ι = abelianHessianKernel θ ι' ι := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.OpFunValues.matrixEntry_massiveOp <;> assumption
end KernelTranslation
section NearZero
variable {L : ℕ}
theorem densityDefined_of_small {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
    (hLB : SpectralLowerBounds θ)
    {z ε : ℝ} (hε : 0 ≤ ε) (hθ : ∀ b, |θ b| ≤ ε) (h₁ : 4 * ε ≤ Real.pi / 2) (h₂ : 192 * ε ≤ z) :
    DensityDefined (L := L) z θ := by
  have hang : ∀ p : FullSpace.Face L 0 0, |FullSpace.faceAngle θ p| ≤ 4 * ε := by
    intro p
    have e₁ := abs_le.1 (hθ (FullSpace.forwardEdge p.corner p.lowAxis))
    have e₂ := abs_le.1
      (hθ (FullSpace.forwardEdge (p.corner + InfiniteLattice.axisStep _ p.lowAxis) p.highAxis))
    have e₃ := abs_le.1
      (hθ (FullSpace.forwardEdge (p.corner + InfiniteLattice.axisStep _ p.highAxis) p.lowAxis))
    have e₄ := abs_le.1 (hθ (FullSpace.forwardEdge p.corner p.highAxis))
    show |θ _ + θ _ - θ _ - θ _| ≤ _
    rw [abs_le]
    constructor <;> linarith [e₁.1, e₁.2, e₂.1, e₂.2, e₃.1, e₃.2, e₄.1, e₄.2]
  have hlow := hLB.1 fun p => (hang p).trans h₁
  have hs0 : 0 ≤ ⨆ p : FullSpace.Face L 0 0, |Real.sin (FullSpace.faceAngle θ p)| :=
    Real.iSup_nonneg fun _ => abs_nonneg _
  have hs4 : (⨆ p : FullSpace.Face L 0 0, |Real.sin (FullSpace.faceAngle θ p)|) ≤ 4 * ε :=
    Real.iSup_le (fun p => Real.abs_sin_le_abs.trans (hang p)) (by positivity)
  generalize (⨆ p : FullSpace.Face L 0 0, |Real.sin (FullSpace.faceAngle θ p)|) = s
    at hlow hs0 hs4
  intro ψ
  obtain ⟨him, hre⟩ := hlow ψ
  have hN : inner ℂ ψ ψ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have e : inner ℂ ψ (addScalar (massiveOp θ) z ψ) - ((z / 2 : ℝ) : ℂ) * inner ℂ ψ ψ =
      (inner ℂ ψ (massiveOp θ ψ) - ((-24 * s : ℝ) : ℂ) * inner ℂ ψ ψ) +
        (((z / 2 - 24 * s) * ‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    have e' : addScalar (massiveOp θ) z ψ = massiveOp θ ψ + (z : ℂ) • ψ := rfl
    rw [e', inner_add_right, inner_smul_right, hN]
    push_cast
    ring
  have hnn : 0 ≤ (z / 2 - 24 * s) * ‖ψ‖ ^ 2 :=
    mul_nonneg (by linarith) (by positivity)
  rw [e, Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.ofReal_re, him]
  exact ⟨by simp, add_nonneg hre hnn⟩
end NearZero
section Translation
variable {L : ℕ}
theorem densityAt_translate {z : ℝ} {m : Fin 4 → ℤ}
    (hSym : DensityInvariance (L := L) z (vertexShift m) (edgeShift m) m)
    (hKer : KernelLocality L)
    (hO : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, AbelianOperators θ)
    (hK : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      CompositesAreKernels (FullSpace.abelianLinkField θ))
    {θ θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
    (hθ : ∀ b : PeriodicOperators.PosEdge L 0 0, θ' (shiftEdge m b) = θ b)
    (hf : DensityDefined (L := L) z θ) (x : FullSpace.Vertex L 0 0) :
    densityAt z θ' (x + vertexOfInt L m) = densityAt z θ x := by
  have hs : ∀ f, vertexShift m (laplacianOp θ f) =
      laplacianOp θ' (vertexShift m f) := fun f =>
    lpShift_intertwine (vertexColour_translate_bijective m) hSym.1.1 _ _ (fun ι' ι => by
      exact (laplacianOp_entry (hO θ') (hK θ') _ _).trans
        ((kernel_translate hKer.laplacian vertexColour_translate_zero m hθ ι' ι).trans
          (laplacianOp_entry (hO θ) (hK θ) _ _).symm)) f
  have hb : ∀ f, edgeShift m (massiveOp θ f) =
      massiveOp θ' (edgeShift m f) := fun f =>
    lpShift_intertwine (edgeColour_translate_bijective m) hSym.2.1.1 _ _ (fun ι' ι => by
      exact (massiveOp_entry (hO θ') (hK θ') _ _).trans
        ((kernel_translate hKer.hessian edgeColour_translate_zero m hθ ι' ι).trans
          (massiveOp_entry (hO θ) (hK θ) _ _).symm)) f
  have h := (hSym.2.2 θ θ' hf hs hb).2 x
  have e : vertexAdd m x = x + vertexOfInt L m := vertexImage_intShift m x
  rwa [e] at h
theorem edgeIndicator_translate (v : FullSpace.Vertex L 0 0)
    (b c : FullSpace.PositiveEdge (meshAt L 0 0)) :
    edgeIndicator (edgeTranslate v b) (edgeTranslate v c) = edgeIndicator b c := by
  unfold edgeIndicator
  by_cases h : c = b
  · simp [h]
  · have h' : edgeTranslate v c ≠ edgeTranslate v b :=
      fun e => h ((edgeTranslate_bijective v).1 e)
    simp [h, h']
theorem abs_edgeIndicator_le (b c : FullSpace.PositiveEdge (meshAt L 0 0)) :
    |edgeIndicator b c| ≤ 1 := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.RowSums.abs_edgeIndicator_le <;> assumption
theorem exists_vertexOfInt (v : FullSpace.Vertex L 0 0) :
    ∃ m : Fin 4 → ℤ, vertexOfInt L m = v := by
  obtain ⟨m, hm⟩ := v.2
  refine ⟨m, Subtype.ext (funext fun μ => ?_)⟩
  simp [vertexOfInt, castVec, hm μ, meshAt]
end Translation
theorem secondDerivativeShiftInvariant (hS : LogSectorsAndDensity)
    (hF : AbelianFieldFacts.AllFacts) (hY : UnitGaugeDirections.Claim) :
    SecondDerivativeShiftInvariant := by
  intro z hz L hL n x y y' μ ν
  obtain ⟨m, rfl⟩ := exists_vertexOfInt n
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSym⟩ := hS.2 L hL z hz
  obtain ⟨-, hKer, -, hθ⟩ := hF.2.2 L hL z hz
  have hcfg : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup (FullSpace.abelianLinkField θ) := by
    intro θ
    have h : FullSpace.IsFieldIn PeriodicLattice.compactGaugeGroup
        (FullSpace.abelianLinkField θ) :=
      (hθ θ).2.2.2.1.abelianLinkField_mem
    exact ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.mp (h.1 b)).2, h.2⟩
  have hK : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      CompositesAreKernels (FullSpace.abelianLinkField θ) := fun θ =>
    ((hY L hL).2 _ (hcfg θ)).2.2.2
  have hO : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, AbelianOperators θ :=
    fun θ => (hθ θ).1
  have hLB : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, SpectralLowerBounds θ :=
    fun θ => (hθ θ).2.2.2.2.2.1
  unfold secondDerivative
  rw [← edgeTranslate_forwardEdge, ← edgeTranslate_forwardEdge]
  generalize FullSpace.forwardEdge y μ = b
  generalize FullSpace.forwardEdge y' ν = b'
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (Real.pi / 8) (z / 192) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]
    exact lt_min (by positivity) (by positivity)
  have hδ₁ : δ ≤ Real.pi / 8 := hδ ▸ min_le_left _ _
  have hδ₂ : δ ≤ z / 192 := hδ ▸ min_le_right _ _
  have key : ∀ s t : ℝ, |s| + |t| ≤ δ →
      densityAt z (fun c => s * edgeIndicator (edgeTranslate (vertexOfInt L m) b) c +
          t * edgeIndicator (edgeTranslate (vertexOfInt L m) b') c) (x + vertexOfInt L m) =
        densityAt z (fun c => s * edgeIndicator b c + t * edgeIndicator b' c) x := by
    intro s t hst
    refine densityAt_translate (hSym m) hKer hO hK (fun c => ?_)
      (densityDefined_of_small (ε := |s| + |t|) (hLB _) ?_ ?_ ?_ ?_) x
    · rw [shiftEdge_eq_edgeTranslate, edgeIndicator_translate, edgeIndicator_translate]
    · exact (add_nonneg (abs_nonneg s) (abs_nonneg t))
    · intro c
      calc |s * edgeIndicator b c + t * edgeIndicator b' c|
          ≤ |s * edgeIndicator b c| + |t * edgeIndicator b' c| := abs_add_le _ _
        _ ≤ |s| * 1 + |t| * 1 := by
            rw [abs_mul, abs_mul]
            exact add_le_add
              (mul_le_mul_of_nonneg_left (abs_edgeIndicator_le _ _) (abs_nonneg _))
              (mul_le_mul_of_nonneg_left (abs_edgeIndicator_le _ _) (abs_nonneg _))
        _ = |s| + |t| := by ring
    · linarith
    · linarith
  have hδ2 : 0 < δ / 2 := by positivity
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ2] with s hs
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ2] with t ht
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs ht
  exact key s t (by linarith)
end YangMills.Construction.Tower.AbelianFieldDensity.ShiftInvariance
end

import YangMills.Construction.Towers.ChargedSectorOfTheConstantField
import YangMills.Construction.Towers.CovariantShiftsOfAnAbelianFieldProof
import YangMills.Construction.Towers.LowerBoundsOfTheAbelianOperatorsProof
import YangMills.Construction.Towers.PlaquetteAnglesOfTheLinearAbelianField
import YangMills.Construction.Towers.TheAbelianOperatorsAreShiftedPositive
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OneLoopNotation YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Matrices
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
open AbelianFieldDensity AbelianFieldDensity.SectorDecomposition
namespace ChargedSector
section Edges
theorem positivelyOriented_opposite_of_not {a : ℝ} {e : InfiniteLattice.Link a}
    (he : ¬ e.IsPositivelyOriented) : e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
variable {L : ℕ}
theorem formOfPositiveValues_apply_pos (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (e : PeriodicOperators.PosEdge L 0 0) : formOfPositiveValues g e.1 = g e := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.formOfPositiveValues_apply <;> assumption
theorem formOfPositiveValues_opposite (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (e : FullSpace.Edge L 0 0) : formOfPositiveValues g e.opposite = -formOfPositiveValues g e := by apply _root_.YangMills.Construction.Tower.AbelianOperatorBounds.formOfPositiveValues_opposite <;> assumption
theorem restrict_formOfPositiveValues (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2) :
    FullSpace.restrictToPositiveEdges (formOfPositiveValues g) = g :=
  funext (formOfPositiveValues_apply_pos g)
theorem formOfPositiveValues_mem_l2Forms {g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2}
    (hg : IsL2Traceless g) :
    formOfPositiveValues g ∈ FullSpace.l2Forms (meshAt L 0 0) := by apply _root_.YangMills.Construction.Tower.AbelianOperatorBounds.formOfPositiveValues_mem_l2Forms <;> assumption
theorem formOfPositiveValues_mem_edgeFormSpace
    {g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2}
    (hg : IsL2Traceless g) (hh : ∀ e, ComplexMatrix2.adjointMatrix (g e) = g e) :
    formOfPositiveValues g ∈ FullSpace.edgeFormSpace (meshAt L 0 0) := by apply _root_.YangMills.Construction.Tower.AbelianOperatorBounds.formOfPositiveValues_mem_edgeFormSpace <;> assumption
theorem formOfPositiveValues_finiteSupport
    {g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2}
    (hs : (Function.support g).Finite) :
    FullSpace.HasFiniteEdgeSupport (formOfPositiveValues g) := by apply _root_.YangMills.Construction.Tower.AbelianOperatorBounds.formOfPositiveValues_hasFiniteEdgeSupport <;> assumption
theorem formOfPositiveValues_fieldStar (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2) :
    formOfPositiveValues (fieldStar g) = fieldStar (formOfPositiveValues g) := by
  funext e
  by_cases he : e.IsPositivelyOriented
  · rw [show formOfPositiveValues (fieldStar g) e = fieldStar g ⟨e, he⟩ from
      formOfPositiveValues_apply_pos _ ⟨e, he⟩]
    show _ = ComplexMatrix2.adjointMatrix (formOfPositiveValues g e)
    rw [show formOfPositiveValues g e = g ⟨e, he⟩ from formOfPositiveValues_apply_pos g ⟨e, he⟩]
    rfl
  · have hr := positivelyOriented_opposite_of_not he
    have e₁ : formOfPositiveValues (fieldStar g) e =
        -formOfPositiveValues (fieldStar g) e.opposite :=
      formOfPositiveValues_opposite _ e.opposite
    have e₂ : formOfPositiveValues g e = -formOfPositiveValues g e.opposite :=
      formOfPositiveValues_opposite g e.opposite
    rw [e₁, show formOfPositiveValues (fieldStar g) e.opposite = fieldStar g ⟨e.opposite, hr⟩
      from formOfPositiveValues_apply_pos _ ⟨e.opposite, hr⟩]
    show _ = ComplexMatrix2.adjointMatrix (formOfPositiveValues g e)
    rw [e₂, show formOfPositiveValues g e.opposite = g ⟨e.opposite, hr⟩ from
      formOfPositiveValues_apply_pos g ⟨e.opposite, hr⟩]
    simp [fieldStar, ComplexMatrix2.adjointMatrix]
end Edges
section Products
variable {σ : Type}
theorem ofCoords_injective (hco : CoordsIsometry σ)
    {v w : L2Field σ} (h : ofCoords v = ofCoords w) :
    v = w := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.ofCoords_injective <;> assumption
theorem hermitianInner_eq_traceFinsumPairing (f g : σ → ComplexMatrix2)
    (hf : ∀ s, ComplexMatrix2.adjointMatrix (f s) = f s)
    (hs : (Function.support f).Finite) : hermitianInner f g = traceFinsumPairing f g := by apply _root_.YangMills.Construction.Tower.AbelianOperatorBounds.hermitianInner_eq_traceFinsumPairing <;> assumption
theorem inner_pointwiseStar (hJ : StarInvolutionFacts σ) (a b : L2Field σ) :
    (inner ℂ (pointwiseStar a) (pointwiseStar b) : ℂ) = conj (inner ℂ a b : ℂ) := by
  have h1 := lp.hasSum_inner (𝕜 := ℂ) (pointwiseStar a) (pointwiseStar b)
  have h2 : HasSum (fun ι => Complex.conjCLE (inner ℂ (a ι) (b ι) : ℂ))
      (Complex.conjCLE (inner ℂ a b : ℂ)) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasSum (lp.hasSum_inner (𝕜 := ℂ) a b)
  have e : (fun ι => (inner ℂ (pointwiseStar a ι) (pointwiseStar b ι) : ℂ)) =
      fun ι => Complex.conjCLE (inner ℂ (a ι) (b ι) : ℂ) := by
    funext ι
    simp [hJ.apply_eq_conj, RCLike.inner_apply]
  rw [e] at h1
  exact h1.unique h2
theorem raisingPauli_eq : raisingPauli = !![0, 1; 0, 0] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.raisingPauli_eq_matrix <;> assumption
theorem loweringPauli_eq : loweringPauli = !![0, 0; 1, 0] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.loweringPauli_eq_matrix <;> assumption
theorem halfTraceProduct_raising_lowering (c d : ℂ) :
    halfTraceProduct (c • raisingPauli) (d • loweringPauli) = 0 := by
  have h : ComplexMatrix2.adjointMatrix (c • raisingPauli) * (d • loweringPauli) = 0 := by
    rw [raisingPauli_eq, loweringPauli_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ComplexMatrix2.adjointMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  rw [halfTraceProduct, h]
  simp [ComplexMatrix2.halfTrace]
theorem halfTraceProduct_lowering_raising (c d : ℂ) :
    halfTraceProduct (c • loweringPauli) (d • raisingPauli) = 0 := by
  have h : ComplexMatrix2.adjointMatrix (c • loweringPauli) * (d • raisingPauli) = 0 := by
    rw [raisingPauli_eq, loweringPauli_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ComplexMatrix2.adjointMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  rw [halfTraceProduct, h]
  simp [ComplexMatrix2.halfTrace]
end Products
theorem inner_edgeTensor_eq_zero {L : ℕ}
    (hco : CoordsIsometry (PeriodicOperators.PosEdge L 0 0))
    (he : ∀ e : PeriodicOperators.PosEdge L 0 0,
      ∃! p : FullSpace.Vertex L 0 0 × Fin 4, FullSpace.forwardEdge p.1 p.2 = e)
    {X Y : ComplexMatrix2}
    (hX : ∀ (v : VectorL2 L 4) (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
      ofCoords (edgeTensor v X) (FullSpace.forwardEdge x μ) = v x μ • X)
    (hY : ∀ (v : VectorL2 L 4) (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
      ofCoords (edgeTensor v Y) (FullSpace.forwardEdge x μ) = v x μ • Y)
    (hXY : ∀ c d : ℂ, halfTraceProduct (c • X) (d • Y) = 0) (v v' : VectorL2 L 4) :
    (inner ℂ (edgeTensor v X) (edgeTensor v' Y) : ℂ) = 0 := by
  rw [← hco.2.2.2.2.2]
  have h : ∀ e : PeriodicOperators.PosEdge L 0 0,
      halfTraceProduct (ofCoords (edgeTensor v X) e)
        (ofCoords (edgeTensor v' Y) e) = 0 := by
    intro e
    obtain ⟨p, rfl, -⟩ := he e
    rw [hX, hY]
    exact hXY _ _
  simp only [hermitianInner, h, tsum_zero]
theorem chargedSectorClaim_holds (hOperators : AbelianOperatorsLocalSelfAdjoint)
    (hSymmetries : AbelianOperatorSymmetries)
    (hAngles : LinearFieldPlaquetteAngles.Claim)
    (hShifted : ShiftedPositive)
    (hLogarithms : AbelianOperatorLogarithms)
    (hMultiples : WeightMultiplesAndStar)
    (hSquare : UnitLatticeL2Statement) : ChargedSectorClaim := by
  intro L hL f hf
  set θ := scaledLinearAngle L f with hθ
  have hops := hOperators L hL θ
  have hsym := hSymmetries L hL θ
  have hcb := (hSquare.2 L).2.2.1
  obtain ⟨hedge, hsl, -, hval, -, hJ, -, hM⟩ := hMultiples L hL
  have hsp : raisingPauli ∈ ComplexMatrix2.traceless := hsl _ (Or.inr (Or.inl rfl))
  have hsm : loweringPauli ∈ ComplexMatrix2.traceless := hsl _ (Or.inr (Or.inr rfl))
  have hang : ∀ p : FullSpace.Face L 0 0,
      |FullSpace.faceAngle θ p| ≤ min (Real.pi / 2) ((100 : ℝ) / 48) := by
    intro p
    have hpi : Real.pi / 2 ≤ (100 : ℝ) / 48 := by
      have := Real.pi_lt_d2
      linarith
    rw [min_eq_left hpi]
    have h := hAngles L hL f p
    have e : FullSpace.faceAngle θ p = if p.lowAxis = 0 ∧ p.highAxis = 1 then f else 0 := h
    rw [e]
    split_ifs
    · exact hf
    · rw [abs_zero]
      positivity
  have hformed : DensityDefined (L := L) 100 θ :=
    ((hShifted L hL).1 100 (by norm_num) θ hang).2
  obtain ⟨-, -, -, -, -, ⟨⟨Sneu, Spos, Sneg⟩, hS, -⟩, hall⟩ :=
    (hLogarithms L hL 100 (by norm_num) θ hformed).2
  obtain ⟨-, ⟨⟨B₀, hB₀⟩, hshift⟩, -⟩ := hall Sneu Spos Sneg hS
  have hvalues : ∀ ψ, toBddOp Spos ψ = Spos ψ :=
    Classical.epsilon_spec (p := fun B : BddOp (VectorL2 L 4) => ∀ ψ, B ψ = Spos ψ)
      ⟨B₀, hB₀⟩
  have hmul : ∀ v : VectorL2 L 4,
      AbelianFieldDensity.massiveOp θ (edgeTensor v raisingPauli) =
        edgeTensor (toBddOp Spos v) raisingPauli := by
    intro v
    rw [hvalues]
    exact hS.2.1 v
  refine ⟨toBddOp Spos, hshift.1, hmul, fun w hw => ?_⟩
  have hcomm : ∀ F : L2Field (PeriodicOperators.PosEdge L 0 0),
      AbelianFieldDensity.massiveOp θ (pointwiseStar F) =
        pointwiseStar (AbelianFieldDensity.massiveOp θ F) := by
    intro F
    refine ofCoords_injective hcb ?_
    rw [hops.hessian_apply, hJ.ofCoords_eq_fieldStar (AbelianFieldDensity.massiveOp θ F),
      hops.hessian_apply, hJ.ofCoords_eq_fieldStar, formOfPositiveValues_fieldStar,
      hsym.hessian_star _ (formOfPositiveValues_mem_l2Forms (hcb.2.2.1 F).1)]
    rfl
  set Fp := edgeTensor w raisingPauli with hFp
  set F : L2Field (PeriodicOperators.PosEdge L 0 0) := Fp + pointwiseStar Fp
    with hF
  set g := ofCoords (F : Fin 3 × PeriodicOperators.PosEdge L 0 0 → ℂ) with hg
  have hgval : ∀ (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
      g (FullSpace.forwardEdge x μ) = w x μ • raisingPauli + conj (w x μ) • loweringPauli := by
    intro x μ
    have e := (hcb.2.2.2.2.1 1 Fp (pointwiseStar Fp)).1
    rw [hg, hF, e, Pi.add_apply, hFp, hM.star_raising, hval _ hsp, hval _ hsm,
      hM.conjVec_apply]
  have hstar : pointwiseStar F = F := by
    have hadd : pointwiseStar (Fp + pointwiseStar Fp) =
        pointwiseStar Fp + pointwiseStar (pointwiseStar Fp) :=
      hJ.isConjLinear.1 Fp (pointwiseStar Fp)
    rw [hF, hadd, hJ.involutive, add_comm]
  have hh : ∀ e, ComplexMatrix2.adjointMatrix (g e) = g e := by
    intro e
    have h := congrFun (hJ.ofCoords_eq_fieldStar F) e
    rw [hstar] at h
    exact h.symm
  have hgs : (Function.support g).Finite := by
    refine ((hw.prod (Set.finite_univ (α := Fin 4))).image
      fun p => FullSpace.forwardEdge p.1 p.2).subset fun e he => ?_
    obtain ⟨⟨x, μ⟩, rfl, -⟩ := hedge e
    refine ⟨(x, μ), ⟨?_, Set.mem_univ _⟩, rfl⟩
    intro hx
    apply he
    have hx' : w x = 0 := hx
    change g (FullSpace.forwardEdge x μ) = 0
    rw [hgval, hx']
    simp
  have hgsq : IsL2Traceless g := (hcb.2.2.1 F).1
  refine ⟨formOfPositiveValues g, ⟨formOfPositiveValues_mem_edgeFormSpace hgsq hh, fun x μ => ?_⟩,
    formOfPositiveValues_finiteSupport hgs, ?_⟩
  · rw [← hgval]
    exact formOfPositiveValues_apply_pos g (FullSpace.forwardEdge x μ)
  have hinner : (inner ℂ F (AbelianFieldDensity.massiveOp θ F) : ℂ) =
      FullSpace.finiteEdgePairing (formOfPositiveValues g)
        (FullSpace.abelianMassiveHessian θ (formOfPositiveValues g)) := by
    rw [← hcb.2.2.2.2.2 F (AbelianFieldDensity.massiveOp θ F), hops.hessian_apply F,
      hermitianInner_eq_traceFinsumPairing _ _ hh hgs]
    simp only [FullSpace.finiteEdgePairing, restrict_formOfPositiveValues]
    rfl
  rw [← hinner]
  set G := edgeTensor (toBddOp Spos w) raisingPauli with hG
  have hKF : AbelianFieldDensity.massiveOp θ F = G + pointwiseStar G := by
    rw [hF, map_add, hcomm, hFp, hmul]
  have hc₁ : (inner ℂ Fp (pointwiseStar G) : ℂ) = 0 := by
    rw [hG, hM.star_raising]
    exact inner_edgeTensor_eq_zero hcb hedge (fun v => hval _ hsp v) (fun v => hval _ hsm v)
      halfTraceProduct_raising_lowering _ _
  have hc₂ : (inner ℂ (pointwiseStar Fp) G : ℂ) = 0 := by
    rw [hFp, hM.star_raising]
    exact inner_edgeTensor_eq_zero hcb hedge (fun v => hval _ hsm v) (fun v => hval _ hsp v)
      halfTraceProduct_lowering_raising _ _
  have hmain : (inner ℂ Fp G : ℂ) = (1 / 2 : ℂ) * inner ℂ w (toBddOp Spos w) :=
    hM.inner_raising _ _
  rw [hKF, hF, inner_add_left, inner_add_right, inner_add_right, hc₁, hc₂, inner_pointwiseStar hJ,
    hmain]
  generalize (inner ℂ w (toBddOp Spos w) : ℂ) = c
  apply Complex.ext <;> simp <;> ring
end ChargedSector
end YangMills.Construction.Tower.ConstantFieldSymbols
end

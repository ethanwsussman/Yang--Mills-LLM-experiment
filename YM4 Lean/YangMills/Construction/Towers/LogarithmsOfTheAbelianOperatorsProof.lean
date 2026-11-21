import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import YangMills.Construction.Towers.CurvesAtTheSideInfinityInTheLeftChartProof
import YangMills.Construction.Towers.KeepingTheDensityGivesItsSymmetryProof
import YangMills.Construction.Towers.LogarithmOnTheSectorsOfSitesAndBonds
import YangMills.Construction.Towers.LogarithmsOfTheAbelianOperators
import YangMills.Construction.Towers.MultiplesOfTheSectorMatricesAndTheConjugation
import YangMills.Construction.Towers.TheDensityIsTheSumOverTheSectorsOnTheUnitLattice
import YangMills.Construction.Towers.TheDensityUnderTheConjugation
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.OneLoopNotation
open YangMills.Construction.Tower.UnitLatticeL2
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof
section Values
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem toBddOp_coe (A : BddOp H) : toBddOp (⇑A) = A :=
  ContinuousLinearMap.ext (Classical.epsilon_spec
    (p := fun B : BddOp H => ∀ ψ : H, B ψ = A ψ) ⟨A, fun _ => rfl⟩)
theorem isBoundedBelowBy_half_of_nonneg {T : BddOp H} {z : ℝ} (hz : 0 < z)
    (hT : IsBoundedBelowBy T 0) : IsBoundedBelowBy (addScalar T z) (z / 2) := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.DensityInvariance.addScalar_boundedBelow_of_nonneg <;> assumption
end Values
section Abstract
variable {L N' : ℕ} {σ : Type}
theorem weightMultiple_injective
    {multiple : VectorL2 L N' → Matrices.ComplexMatrix2 → L2Field σ}
    (hM : WeightMultipleFacts multiple) {t : Matrices.ComplexMatrix2} (ht : IsWeightMatrix t)
    {c : ℂ} (hc : c ≠ 0)
    (hin : ∀ v v' : VectorL2 L N',
      inner ℂ (multiple v t) (multiple v' t) = c * inner ℂ v v') :
    Function.Injective fun v : VectorL2 L N' => multiple v t := by
  intro v v' h
  have h' : multiple v t = multiple v' t := h
  have e : multiple (v + (-1 : ℂ) • v') t = 0 := by
    rw [hM.map_add t ht, hM.map_smul t ht, h']
    simp
  have e₂ := hin (v + (-1 : ℂ) • v') (v + (-1 : ℂ) • v')
  rw [e, inner_zero_left] at e₂
  have e₃ : (inner ℂ (v + (-1 : ℂ) • v') (v + (-1 : ℂ) • v') : ℂ) = 0 :=
    (mul_eq_zero.mp e₂.symm).resolve_left hc
  have e₄ : v + (-1 : ℂ) • v' = 0 := inner_self_eq_zero.mp e₃
  have e₅ : v + -v' = 0 := by simpa using e₄
  exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using e₅)
theorem abelianLogDecomposition_of_commutes
    {multiple : VectorL2 L N' → Matrices.ComplexMatrix2 → L2Field σ}
    {position : Fin 3 × σ → InfiniteLattice.AmbientSpace} {z : ℝ}
    {T : BddOp (L2Field σ)}
    (hT : ShiftedHalfPositive z T)
    (hSelf : IsSelfAdjointOp (opLog (addScalar T z)))
    (hInter : LogCommIntertwiner (L2Field σ) (L2Field σ) z)
    (hSector : LogRestrictsToSector multiple z)
    (hTrace : TraceSplitsBySector multiple position)
    (hDensity : TraceStarConj multiple position)
    (hJ : StarInvolutionFacts σ) (hM : WeightMultipleFacts multiple)
    (hNeutral : ∀ f : L2Field σ, IsNeutral (ofCoords f) → IsNeutral (ofCoords (T f)))
    (hPositive : ∀ f : L2Field σ,
      IsPositivelyCharged (ofCoords f) → IsPositivelyCharged (ofCoords (T f)))
    (hNegative : ∀ f : L2Field σ,
      IsNegativelyCharged (ofCoords f) → IsNegativelyCharged (ofCoords (T f)))
    (hCommutes : ∀ f : L2Field σ, T (pointwiseStar f) = pointwiseStar (T f)) :
    AbelianLogDecomposition multiple position z T := by
  have t₃ : IsWeightMatrix (Matrices.ComplexMatrix2.pauliFamily 2) := Or.inl rfl
  have tp : IsWeightMatrix raisingPauli := Or.inr (Or.inl rfl)
  have tm : IsWeightMatrix loweringPauli := Or.inr (Or.inr rfl)
  have i₃ := weightMultiple_injective hM t₃ (c := 1) one_ne_zero
    (fun v v' => by rw [hM.inner_third, one_mul])
  have ip := weightMultiple_injective hM tp (c := 1 / 2) (by norm_num) hM.inner_raising
  have im := weightMultiple_injective hM tm (c := 1 / 2) (by norm_num) hM.inner_lowering
  have hs₃ : ∀ v, ∃ v', T (multiple v (Matrices.ComplexMatrix2.pauliFamily 2)) =
      multiple v' (Matrices.ComplexMatrix2.pauliFamily 2) := fun v =>
    (hM.neutral_iff _).mp (hNeutral _ ((hM.neutral_iff _).mpr ⟨v, rfl⟩))
  have hsp : ∀ v, ∃ v', T (multiple v raisingPauli) = multiple v' raisingPauli := fun v =>
    (hM.positive_iff _).mp (hPositive _ ((hM.positive_iff _).mpr ⟨v, rfl⟩))
  have hsm : ∀ v, ∃ v', T (multiple v loweringPauli) = multiple v' loweringPauli := fun v =>
    (hM.negative_iff _).mp (hNegative _ ((hM.negative_iff _).mpr ⟨v, rfl⟩))
  choose S₃ hS₃ using hs₃
  choose Sp hSp using hsp
  choose Sm hSm using hsm
  have hSectors : IsSectorTriple multiple T S₃ Sp Sm := ⟨hS₃, hSp, hSm⟩
  have hLog₃ := (hSector _ t₃ T S₃ hT hS₃).2.2
  have hLogp := (hSector _ tp T Sp hT hSp).2.2
  have hLogm := (hSector _ tm T Sm hT hSm).2.2
  have hStar : ∀ f : L2Field σ,
      opLog (addScalar T z) (pointwiseStar f) =
        pointwiseStar (opLog (addScalar T z) f) := fun f =>
    (hInter T T pointwiseStar hT hT (Or.inr hJ.isConjLinear)
      ⟨1, zero_le_one, fun f => by rw [hJ.norm_eq, one_mul]⟩
      (fun f => (hCommutes f).symm) f).symm
  refine ⟨hT, ?_, ?_, ?_, hStar, ?_, ?_⟩
  · intro f hf
    obtain ⟨v, rfl⟩ := (hM.neutral_iff f).mp hf
    exact (hM.neutral_iff _).mpr ⟨_, hLog₃ v⟩
  · intro f hf
    obtain ⟨v, rfl⟩ := (hM.positive_iff f).mp hf
    exact (hM.positive_iff _).mpr ⟨_, hLogp v⟩
  · intro f hf
    obtain ⟨v, rfl⟩ := (hM.negative_iff f).mp hf
    exact (hM.negative_iff _).mpr ⟨_, hLogm v⟩
  · refine ⟨(S₃, Sp, Sm), hSectors, ?_⟩
    rintro ⟨R₃, Rp, Rm⟩ ⟨h₃, hp, hm⟩
    have e₃ : R₃ = S₃ := funext fun v => i₃ ((h₃ v).symm.trans (hS₃ v))
    have ep : Rp = Sp := funext fun v => ip ((hp v).symm.trans (hSp v))
    have em : Rm = Sm := funext fun v => im ((hm v).symm.trans (hSm v))
    rw [e₃, ep, em]
  · intro R₃ Rp Rm hR
    obtain ⟨b₃, p₃, l₃⟩ := hSector _ t₃ T R₃ hT hR.1
    obtain ⟨bp, pp, lp⟩ := hSector _ tp T Rp hT hR.2.1
    obtain ⟨bm, pm, lm⟩ := hSector _ tm T Rm hT hR.2.2
    have hLogSectors : IsSectorTriple multiple (opLog (addScalar T z))
        (⇑(opLog (addScalar (toBddOp R₃) z)))
        (⇑(opLog (addScalar (toBddOp Rp) z)))
        (⇑(opLog (addScalar (toBddOp Rm) z))) := ⟨l₃, lp, lm⟩
    refine ⟨⟨b₃, p₃⟩, ⟨bp, pp⟩, ⟨bm, pm⟩, l₃, lp, lm, fun x => ?_⟩
    have hsum := (hTrace _ _ _ _ hLogSectors).2.2.2 x
    have hequal := (hDensity (opLog (addScalar T z))).2.2.2 _ _ _ hLogSectors hSelf
      hStar x
    simp only [toBddOp_coe] at hsum hequal
    exact ⟨hsum, hequal⟩
end Abstract
section Bonds
variable {a : ℝ}
theorem isPositivelyOriented_opposite_of_not (b : InfiniteLattice.Link a)
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem extendOddly_of_pos (f : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = f b := if_pos hb
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (b : InfiniteLattice.Link a) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
variable {L : ℕ}
theorem meshAt_zero_pos (hL : 0 < L) : 0 < meshAt L 0 0 := by
  unfold meshAt
  positivity
theorem formOfPositiveValues_apply (g : PeriodicOperators.PosEdge L 0 0 → Matrices.ComplexMatrix2)
    (b : PeriodicOperators.PosEdge L 0 0) : formOfPositiveValues g b.1 = g b := by
  unfold formOfPositiveValues
  rw [extendOddly_of_pos _ b.2]
  exact dif_pos b.2
theorem formOfPositiveValues_opposite (hL : 0 < L)
    (g : PeriodicOperators.PosEdge L 0 0 → Matrices.ComplexMatrix2)
    (b : FullSpace.Edge L 0 0) : formOfPositiveValues g b.opposite = -formOfPositiveValues g b :=
  extendOddly_opposite (meshAt_zero_pos hL) _ b
theorem restrict_formOfPositiveValues
    (g : PeriodicOperators.PosEdge L 0 0 → Matrices.ComplexMatrix2) :
    FullSpace.restrictToPositiveEdges (formOfPositiveValues g) = g :=
  funext fun b => formOfPositiveValues_apply g b
theorem formOfPositiveValues_mem (hL : 0 < L)
    {g : PeriodicOperators.PosEdge L 0 0 → Matrices.ComplexMatrix2} (hg : IsL2Traceless g) :
    formOfPositiveValues g ∈ FullSpace.l2Forms (meshAt L 0 0) := by
  refine ⟨⟨fun b hb => ?_, formOfPositiveValues_opposite hL g⟩, ?_⟩
  · rw [show formOfPositiveValues g b = g ⟨b, hb⟩ from formOfPositiveValues_apply g ⟨b, hb⟩]
    exact hg.1 _
  · rw [restrict_formOfPositiveValues]
    exact hg
theorem formOfPositiveValues_fieldStar (hL : 0 < L)
    (g : PeriodicOperators.PosEdge L 0 0 → Matrices.ComplexMatrix2) :
    formOfPositiveValues (fieldStar g) = fieldStar (formOfPositiveValues g) := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [show formOfPositiveValues (fieldStar g) b = fieldStar g ⟨b, hb⟩ from
      formOfPositiveValues_apply _ ⟨b, hb⟩]
    show _ = Matrices.ComplexMatrix2.adjointMatrix (formOfPositiveValues g b)
    rw [show formOfPositiveValues g b = g ⟨b, hb⟩ from formOfPositiveValues_apply g ⟨b, hb⟩]
    rfl
  · have hr := isPositivelyOriented_opposite_of_not b hb
    have e₁ : formOfPositiveValues (fieldStar g) b =
        -formOfPositiveValues (fieldStar g) b.opposite :=
      formOfPositiveValues_opposite hL _ b.opposite
    have e₂ : formOfPositiveValues g b = -formOfPositiveValues g b.opposite :=
      formOfPositiveValues_opposite hL g b.opposite
    rw [e₁, show formOfPositiveValues (fieldStar g) b.opposite = fieldStar g ⟨b.opposite, hr⟩
      from formOfPositiveValues_apply _ ⟨b.opposite, hr⟩]
    show _ = Matrices.ComplexMatrix2.adjointMatrix (formOfPositiveValues g b)
    rw [e₂, show formOfPositiveValues g b.opposite = g ⟨b.opposite, hr⟩ from
      formOfPositiveValues_apply g ⟨b.opposite, hr⟩]
    simp [fieldStar, Matrices.ComplexMatrix2.adjointMatrix]
end Bonds
theorem ofCoords_injective {σ : Type} (hco : CoordsIsometry σ)
    {v w : L2Field σ} (h : ofCoords v = ofCoords w) : v = w :=
  lp.ext (funext fun ι => ((hco.2.2.1 v).2 ι).symm.trans
    ((congrArg (fun f => coordAt f ι) h).trans ((hco.2.2.1 w).2 ι)))
theorem abelianOperatorLogarithms_holds (hSquare : UnitLatticeL2Statement)
    (hFacts : AbelianFieldFacts.AllFacts)
    (hMultiples : AbelianFieldDensity.WeightMultiplesAndStar)
    (hLogarithm : LogShiftedAndIntertwiners)
    (hOnASector : LogOnVertexAndEdgeSectors)
    (hTrace : UnitLatticeTraceSplits.Claim)
    (hConjugate : AbelianFieldDensity.UnitLatticeStarConj.Claim) :
    AbelianOperatorLogarithms := by
  intro L hL z hz θ hformed
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨-, -, -, -, hJs, hJb, hMs, hMb⟩ := hMultiples L hL
  obtain ⟨-, -, -, hField⟩ := hFacts.2.2 L hL z hz
  obtain ⟨hops, hsym, -, -, -, hlow, -⟩ := hField θ
  have hco := (hSquare.2 L).2.1.1
  have hcb := (hSquare.2 L).2.2.1
  obtain ⟨hSiteSector, hBondSector⟩ := hOnASector L hL z hz
  obtain ⟨hSiteTrace, hBondTrace⟩ := hTrace L hL
  obtain ⟨hSiteConjugate, hBondConjugate⟩ := hConjugate L hL
  have hSiteShifted : ShiftedHalfPositive z (laplacianOp θ) :=
    ⟨hops.laplacian_isSelfAdjoint, isBoundedBelowBy_half_of_nonneg hz hlow.2⟩
  have hBondShifted : ShiftedHalfPositive z (massiveOp θ) :=
    ⟨hops.hessian_isSelfAdjoint, hformed⟩
  have hs : ∀ f : L2Field (FullSpace.Vertex L 0 0), IsL2Traceless (ofCoords f) := fun f =>
    (hco.2.2.1 f).1
  have hform : ∀ f : L2Field (PeriodicOperators.PosEdge L 0 0),
      formOfPositiveValues (ofCoords f) ∈ FullSpace.l2Forms (meshAt L 0 0) := fun f =>
    formOfPositiveValues_mem hL0 (hcb.2.2.1 f).1
  have hon : ∀ f : L2Field (PeriodicOperators.PosEdge L 0 0),
      FullSpace.restrictToPositiveEdges (formOfPositiveValues (ofCoords f)) = ofCoords f :=
    fun f => restrict_formOfPositiveValues _
  have hLs := hLogarithm (L2Field (FullSpace.Vertex L 0 0))
    (L2Field (FullSpace.Vertex L 0 0)) z hz
  have hLb := hLogarithm (L2Field (PeriodicOperators.PosEdge L 0 0))
    (L2Field (PeriodicOperators.PosEdge L 0 0)) z hz
  refine ⟨abelianLogDecomposition_of_commutes hSiteShifted (hLs.1 _ hSiteShifted).2.1 hLs.2.2
      hSiteSector hSiteTrace hSiteConjugate hJs hMs ?_ ?_ ?_ ?_,
    abelianLogDecomposition_of_commutes hBondShifted (hLb.1 _ hBondShifted).2.1 hLb.2.2
      hBondSector hBondTrace hBondConjugate hJb hMb ?_ ?_ ?_ ?_⟩
  · intro f hf
    rw [hops.laplacian_apply]
    exact hsym.laplacian_neutral _ (hs f) hf
  · intro f hf
    rw [hops.laplacian_apply]
    exact hsym.laplacian_pos _ (hs f) hf
  · intro f hf
    rw [hops.laplacian_apply]
    exact hsym.laplacian_neg _ (hs f) hf
  · intro f
    refine ofCoords_injective hco ?_
    rw [hops.laplacian_apply, hJs.ofCoords_eq_fieldStar, hJs.ofCoords_eq_fieldStar,
      hops.laplacian_apply]
    exact hsym.laplacian_star _ (hs f)
  · intro f hf
    rw [hops.hessian_apply]
    exact hsym.hessian_neutral _ (hform f) (by rw [hon]; exact hf)
  · intro f hf
    rw [hops.hessian_apply]
    exact hsym.hessian_pos _ (hform f) (by rw [hon]; exact hf)
  · intro f hf
    rw [hops.hessian_apply]
    exact hsym.hessian_neg _ (hform f) (by rw [hon]; exact hf)
  · intro f
    refine ofCoords_injective hcb ?_
    rw [hops.hessian_apply, hJb.ofCoords_eq_fieldStar (massiveOp θ f), hops.hessian_apply,
      hJb.ofCoords_eq_fieldStar, formOfPositiveValues_fieldStar hL0,
      hsym.hessian_star _ (hform f)]
    rfl
end YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof
end

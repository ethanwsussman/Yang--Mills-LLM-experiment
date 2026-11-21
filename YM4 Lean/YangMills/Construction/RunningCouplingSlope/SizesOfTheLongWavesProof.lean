import YangMills.Construction.PeriodicOperators.NormOfTheSymbolProof
import YangMills.Construction.RunningCouplingSlope.SizesOfTheLongWaves
import YangMills.Construction.RunningCouplingSlope.TheHessianOfTheWholeChainIsBoundedProof
import YangMills.Construction.Towers.ImagesUnderTheResponseReadAtTheSideInfinity
import YangMills.Construction.Towers.ResponseFieldOfAPlaneWaveProof
import YangMills.Construction.Towers.TheResponseSymbolComponentsNearZero
import Mathlib
set_option autoImplicit false
open Filter Set
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.LongWaveSizes
open Matrices (ComplexMatrix2)
open PeriodicOperators (ApplySummableAt colourEdges toComplexVec bilinDot applyKernel)
open Tower.PeriodicForm (coeffsOnEdges)
open LocalKernels (projPositiveEdge)
open LocalKernels.Periodisation (ProjEdgesCompatible ProjCellsClassified periodSide)
open InfiniteLattice (AmbientSpace)
open Tower.CriticalBranchResponse (meshScaledResponse periodicResponse periodicDefect)
private theorem pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) (c : ℂ)
    (a : Fin 3) : Tower.pauliCoeff a (c • X) = c * Tower.pauliCoeff a X := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.pauliCoeff_smul <;> assumption
private theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private theorem pauliFamily_mem_hermitianTraceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
private theorem pauliCoeff_pauliFamily (a' a : Fin 3) :
    Tower.pauliCoeff a' (ComplexMatrix2.pauliFamily a) = if a' = a then 1 else 0 := by apply _root_.YangMills.Construction.Tower.CrossingSmoothingContraction.pauliCoeff_pauliFamily <;> assumption
private theorem pauliCoeff_zero (a : Fin 3) : Tower.pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private theorem halfTrace_mul_eq_sum (hP : OneLoop.PauliMatrixRelations) {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hY : Y ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.halfTrace (X * Y) = ∑ a, Tower.pauliCoeff a X * Tower.pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p22145 <;> assumption
section Forms
variable {L n k : ℕ}
private theorem edge_opposite_opposite {j : ℕ} (b : Tower.Edge L n k j) :
    b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
private theorem opposite_isPositivelyOriented {j : ℕ} {b : Tower.Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.opposite_isPositivelyOriented_of_not <;> assumption
private theorem extendOddly_opposite (hL : 2 ≤ L) (hn : 0 < n)
    (f : Tower.Edge L n k k → ComplexMatrix2) (b : Tower.Edge L n k k) :
    Tower.extendOddly f b.opposite = -Tower.extendOddly f b := by
  by_cases h : b.IsPositivelyOriented
  · have hr : ¬b.opposite.IsPositivelyOriented := by
      rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (L := L) (m := n)
          (j := PeriodicLattice.levelDepth k k) hL (by simp [PeriodicLattice.levelDepth]; omega) b with
        ⟨-, h'⟩ | ⟨-, h'⟩
      · exact h'
      · exact absurd h h'
    simp only [Tower.extendOddly, if_pos h, if_neg hr, edge_opposite_opposite]
  · simp only [Tower.extendOddly, if_neg h, if_pos (opposite_isPositivelyOriented h), neg_neg]
private theorem pauliUnitForm_mem (hL : 2 ≤ L) (hn : 0 < n) (w : Fin 4 → ℤ) :
    pauliUnitForm L n k w ∈ Tower.edgeFormSpace L n k k := by
  refine ⟨fun b hb => ?_, fun b => extendOddly_opposite hL hn _ b⟩
  simp only [pauliUnitForm, Tower.extendOddly, if_pos hb]
  split_ifs
  · exact pauliFamily_mem_hermitianTraceless 2
  · exact ComplexMatrix2.hermitianTraceless.zero_mem
abbrev _root_.YangMills.SharedProofs.p46171 := @pauliUnitForm_mem
private theorem planeWaveValues_mem [NeZero (2 * L ^ n)] (hL : 2 ≤ L) (hn : 0 < n)
    (f : TorusFields.TorusSite (2 * L ^ n) → ℝ) :
    planeWaveValues L n k f ∈ Tower.edgeFormSpace L n k k :=
  (Tower.edgeFormSpace L n k k).sum_mem fun _ _ =>
    (Tower.edgeFormSpace L n k k).smul_mem _ (pauliUnitForm_mem hL hn _)
private theorem offsetSite_coe_apply (w : Fin 4 → ℤ) (ν : Fin 4) :
    (((PeriodicLattice.offsetSite (0 : Tower.Vertex L n k k) w : Tower.Vertex L n k k) :
        PeriodicLattice.FourTorus L n)) ν =
      ((w ν : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
  have h1 : ((∑ μ, w μ • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ :
      Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) =
        ∑ μ, w μ • ((PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ :
          Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) := by
    simp
  simp only [PeriodicLattice.offsetSite, zero_add]
  rw [h1, Finset.sum_apply, Finset.sum_eq_single ν]
  · have hs0 : PeriodicLattice.meshSize L 0 = 1 := by
      simp [PeriodicLattice.meshSize]
    simp only [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, PeriodicLattice.levelDepth,
      sub_self, hs0, Pi.smul_apply, Pi.single_eq_same]
    have e : ((w ν : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) =
        (((w ν) • (1 : ℝ) : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
      simp
    rw [e]
    exact (map_zsmul (QuotientAddGroup.mk'
      (AddSubgroup.zmultiples (PeriodicLattice.torusSide L n))) (w ν) (1 : ℝ)).symm
  · intro μ _ h
    simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h.symm]
  · simp
private theorem exists_int_of_coe_eq {u v : ℝ}
    (h : (u : AddCircle (PeriodicLattice.torusSide L n)) =
      (v : AddCircle (PeriodicLattice.torusSide L n))) :
    ∃ t : ℤ, u = v + (t : ℝ) * ((2 * L ^ n : ℕ) : ℝ) := by apply _root_.YangMills.Construction.OneLoopLaw.FourierExpansion.exists_int_of_addCircle_coe_eq <;> assumption
private theorem zmod_cast_eq_of_coe_eq {u v : ℤ}
    (h : ((u : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) =
      ((v : ℝ) : AddCircle (PeriodicLattice.torusSide L n))) :
    (u : ZMod (2 * L ^ n)) = (v : ZMod (2 * L ^ n)) := by
  obtain ⟨t, ht⟩ := exists_int_of_coe_eq h
  have h2 : u = v + t * ((2 * L ^ n : ℕ) : ℤ) := by
    exact_mod_cast ht
  have h3 : (((2 * L ^ n : ℕ) : ℤ) : ZMod (2 * L ^ n)) = 0 := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_self _
  rw [h2, Int.cast_add, Int.cast_mul, h3, mul_zero, add_zero]
private theorem coe_eq_of_zmod_cast_eq {u v : ℤ}
    (h : (u : ZMod (2 * L ^ n)) = (v : ZMod (2 * L ^ n))) :
    ((u : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) =
      ((v : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub u v (2 * L ^ n)).1 h
  have h1 : ((v : ℝ) - (u : ℝ) : ℝ) = (c : ℝ) * PeriodicLattice.torusSide L n := by
    have h2 : ((v - u : ℤ) : ℝ) = (((2 * L ^ n : ℕ) : ℤ) * c : ℤ) := by rw [hc]
    push_cast at h2
    rw [PeriodicLattice.torusSide, h2]
    ring
  have h3 : (((v : ℝ) - (u : ℝ) : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) = 0 :=
    (AddCircle.coe_eq_zero_iff _).2 ⟨c, by rw [h1, zsmul_eq_mul]⟩
  rw [AddCircle.coe_sub, sub_eq_zero] at h3
  exact h3.symm
end Forms
section EvaluationMaps
variable {L n k : ℕ}
private theorem meshAt_top : Tower.meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
private theorem projPositiveEdge_difference (hb : ProjEdgesCompatible L n k k)
    (b : PeriodicOperators.PosEdge L k k) (ν : Fin 4)
    (hν : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (Tower.meshAt L k k) ν) :
    (projPositiveEdge L n k k b).1.target - (projPositiveEdge L n k k b).1.source =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) ν := by apply _root_.YangMills.Construction.Tower.ResponseOfFourierMode.projPositiveEdge_sub <;> assumption
private theorem one_ne_zero_addCircle :
    ((1 : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) ≠ 0 := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.one_ne_zero_addCircle <;> assumption
private theorem unitStep_ne {ν μ : Fin 4} (h : ν ≠ μ) :
    PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) ν ≠
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ := by
  intro e
  have h1 : PeriodicLattice.pointOnAxis L n ν
        (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k)) ν =
      PeriodicLattice.pointOnAxis L n μ
        (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k)) ν :=
    congrFun (congrArg Subtype.val e) ν
  have hs : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) = 1 := by
    simp [PeriodicLattice.meshSize]
  simp only [PeriodicLattice.pointOnAxis, Pi.single_eq_same, Pi.single_eq_of_ne h, hs] at h1
  exact one_ne_zero_addCircle (by simpa using h1)
private theorem planeWaveValues_at_proj [NeZero (2 * L ^ n)] (hb : ProjEdgesCompatible L n k k)
    (f : TorusFields.TorusSite (2 * L ^ n) → ℝ) (b : PeriodicOperators.PosEdge L k k) (ρ : Fin 4)
    (hρ : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (Tower.meshAt L k k) ρ)
    (y : Fin 4 → ℤ) (hy : ∀ μ, (b.1.initial : AmbientSpace) μ = (y μ : ℝ)) :
    planeWaveValues L n k f (projPositiveEdge L n k k b).1 =
      if ρ = SlopeCoefficient.secondAxis then
        f (fun μ => (y μ : ZMod (2 * L ^ n))) • ComplexMatrix2.pauliFamily 2 else 0 := by
  classical
  have hpos := (projPositiveEdge L n k k b).2
  have hd := projPositiveEdge_difference hb b ρ hρ
  have e₀ : (projPositiveEdge L n k k b).1.source = Tower.FullSpace.projVertex L n k k b.1.initial := by
    rw [hb.2.1 b]
    exact (hb.1 b.1).1
  generalize (projPositiveEdge L n k k b).1 = q at hpos hd e₀ ⊢
  have hsource : ∀ ν, ((q.source : Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) ν =
      ((y ν : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
    intro ν
    rw [e₀]
    show (((b.1.initial : AmbientSpace) ν : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) = _
    rw [hy ν]
  have unitv : ∀ w, pauliUnitForm L n k w q =
      if q = PeriodicLattice.Bond.forwardFrom (PeriodicLattice.offsetSite 0 w)
          SlopeCoefficient.secondAxis then
        ComplexMatrix2.pauliFamily 2 else 0 := fun w => by
    simp only [pauliUnitForm, Tower.extendOddly, if_pos hpos]
  show (∑ x : TorusFields.TorusSite (2 * L ^ n), f x • pauliUnitForm L n k (centredCoords x)) q = _
  rw [Finset.sum_apply]
  by_cases h : ρ = SlopeCoefficient.secondAxis
  · rw [if_pos h, Finset.sum_eq_single (fun μ => (y μ : ZMod (2 * L ^ n)))]
    · rw [Pi.smul_apply, unitv, if_pos]
      have et : q.source = PeriodicLattice.offsetSite 0
          (centredCoords (fun μ => (y μ : ZMod (2 * L ^ n)))) := by
        apply Subtype.ext
        funext ν
        rw [hsource ν, offsetSite_coe_apply]
        apply coe_eq_of_zmod_cast_eq
        simp [centredCoords, ZMod.coe_valMinAbs]
      apply PeriodicLattice.Bond.ext
      · exact et
      · show q.target = _ + _
        rw [← et, ← h, ← hd]
        abel
    · intro x _ hx
      rw [Pi.smul_apply, unitv, if_neg, smul_zero]
      intro e
      apply hx
      funext μ
      have e' : q.source = PeriodicLattice.offsetSite 0 (centredCoords x) :=
        congrArg PeriodicLattice.Bond.source e
      have e'' := hsource μ
      rw [e', offsetSite_coe_apply] at e''
      have h2 := zmod_cast_eq_of_coe_eq e''
      simpa [centredCoords, ZMod.coe_valMinAbs] using h2
    · intro hx
      exact absurd (Finset.mem_univ _) hx
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Pi.smul_apply, unitv, if_neg, smul_zero]
    intro e
    apply unitStep_ne (L := L) (n := n) (k := k) h
    rw [← hd, e]
    simp [PeriodicLattice.Bond.forwardFrom]
private theorem phase_shift_by_period {t : ℝ} {M : ℤ}
    (ht : t * ((2 * L ^ n : ℕ) : ℝ) = 2 * Real.pi * M) (u : ℤ) :
    ∃ c : ℤ, t * (((u : ZMod (2 * L ^ n)).valMinAbs : ℤ) : ℝ) = t * u + (c : ℝ) * (2 * Real.pi) := by
  have h := ZMod.coe_valMinAbs (u : ZMod (2 * L ^ n))
  obtain ⟨d, hd⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (2 * L ^ n)).1 h
  refine ⟨-(M * d), ?_⟩
  have h2 : ((u - (u : ZMod (2 * L ^ n)).valMinAbs : ℤ) : ℝ) =
      (((2 * L ^ n : ℕ) : ℤ) * d : ℤ) := by
    rw [hd]
  push_cast at h2 ht ⊢
  have h3 : (((u : ZMod (2 * L ^ n)).valMinAbs : ℤ) : ℝ) = u - 2 * (L : ℝ) ^ n * d := by
    linarith
  rw [h3]
  linear_combination (-(d : ℝ)) * ht
private theorem cosinePhase_at_cast {t : ℝ} {M : ℤ}
    (ht : t * ((2 * L ^ n : ℕ) : ℝ) = 2 * Real.pi * M) (y : Fin 4 → ℤ) :
    cosinePhase t (fun μ => (y μ : ZMod (2 * L ^ n))) = Real.cos (t * y 0) := by
  obtain ⟨c, hc⟩ := phase_shift_by_period ht (y 0)
  show Real.cos (t * (((y 0 : ZMod (2 * L ^ n)).valMinAbs : ℤ) : ℝ)) = _
  rw [hc, Real.cos_add_int_mul_two_pi]
private theorem sinePhase_at_cast {t : ℝ} {M : ℤ}
    (ht : t * ((2 * L ^ n : ℕ) : ℝ) = 2 * Real.pi * M) (y : Fin 4 → ℤ) :
    sinePhase t (fun μ => (y μ : ZMod (2 * L ^ n))) = Real.sin (t * y 0) := by
  obtain ⟨c, hc⟩ := phase_shift_by_period ht (y 0)
  show Real.sin (t * (((y 0 : ZMod (2 * L ^ n)).valMinAbs : ℤ) : ℝ)) = _
  rw [hc, Real.sin_add_int_mul_two_pi]
private theorem constantFormAmplitude_mkQuot (hT : PeriodicOperators.TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hs : Tower.meshAt L k k ≠ 0)
    (ε : Fin 4 → ComplexMatrix2) (a : Fin 3) (b : PeriodicOperators.PosEdge L k k) (ρ : Fin 4)
    (hb : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (Tower.meshAt L k k) ρ) :
    Tower.FullSpace.constantFormAmplitude L k ε ((colourEdges L k k).mkQuot 1 (a, b)) =
      Tower.pauliCoeff a (ε ρ) := by apply _root_.YangMills.Construction.Tower.ResponseOfFourierMode.constantFormAmplitude_mkQuot <;> assumption
private def secondAxisThirdColour (ρ : Fin 4) (a : Fin 3) : ℂ :=
  if ρ = SlopeCoefficient.secondAxis ∧ a = 2 then 1 else 0
private theorem norm_secondAxisThirdColour_le (ρ : Fin 4) (a : Fin 3) :
    ‖secondAxisThirdColour ρ a‖ ≤ 1 := by
  unfold secondAxisThirdColour
  split_ifs <;> simp
private def longWave (L k : ℕ) (s : ℝ) : (colourEdges L k k).Carrier → ℂ :=
  Tower.FullSpace.planeWaveOfConstant L k (toComplexVec (Pi.single 0 s))
    (Tower.FullSpace.axisPauliElement SlopeCoefficient.secondAxis 2)
private theorem longWave_apply (hT : PeriodicOperators.TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (s : ℝ) (a : Fin 3)
    (b : PeriodicOperators.PosEdge L k k) (ρ : Fin 4)
    (hρ : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (Tower.meshAt L k k) ρ)
    (y : Fin 4 → ℤ) (hy : ∀ μ, (b.1.initial : AmbientSpace) μ = (y μ : ℝ)) :
    longWave L k s (a, b) =
      Complex.exp (Complex.I * ((s * y 0 : ℝ) : ℂ)) * secondAxisThirdColour ρ a := by
  have hs : Tower.meshAt L k k ≠ 0 := by
    rw [meshAt_top]
    exact one_ne_zero
  have hd : bilinDot (toComplexVec (Pi.single 0 s)) (toComplexVec (b.1.initial : AmbientSpace)) =
      ((s * y 0 : ℝ) : ℂ) := by
    simp only [bilinDot, toComplexVec]
    rw [Finset.sum_eq_single 0]
    · rw [hy 0]
      simp
    · intro μ _ h
      simp [Pi.single_eq_of_ne h]
    · simp
  show Complex.exp (Complex.I * bilinDot (toComplexVec (Pi.single 0 s))
      (toComplexVec (b.1.initial : AmbientSpace))) *
    Tower.FullSpace.constantFormAmplitude L k
      (Tower.FullSpace.axisPauliElement SlopeCoefficient.secondAxis 2)
      ((colourEdges L k k).mkQuot 1 (a, b)) = _
  rw [constantFormAmplitude_mkQuot hT hL hk hs _ a b ρ hρ, hd]
  congr 1
  by_cases h : ρ = SlopeCoefficient.secondAxis
  · subst h
    simp only [Tower.FullSpace.axisPauliElement, Pi.single_eq_same, pauliCoeff_pauliFamily,
      secondAxisThirdColour, true_and]
  · simp only [Tower.FullSpace.axisPauliElement, Pi.single_eq_of_ne h, pauliCoeff_zero,
      secondAxisThirdColour, h, false_and, if_false]
private theorem coeffsOnEdges_planeWaveValues [NeZero (2 * L ^ n)] (hb : ProjEdgesCompatible L n k k)
    (f : TorusFields.TorusSite (2 * L ^ n) → ℝ) (a : Fin 3)
    (b : PeriodicOperators.PosEdge L k k) (ρ : Fin 4)
    (hρ : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (Tower.meshAt L k k) ρ)
    (y : Fin 4 → ℤ) (hy : ∀ μ, (b.1.initial : AmbientSpace) μ = (y μ : ℝ)) :
    coeffsOnEdges L n k k (planeWaveValues L n k f) (a, b) =
      (f (fun μ => (y μ : ZMod (2 * L ^ n))) : ℂ) * secondAxisThirdColour ρ a := by
  show Tower.pauliCoeff a (planeWaveValues L n k f (projPositiveEdge L n k k b).1) = _
  rw [planeWaveValues_at_proj hb f b ρ hρ y hy]
  by_cases h : ρ = SlopeCoefficient.secondAxis
  · rw [if_pos h, ← Complex.coe_smul, pauliCoeff_smul (pauliFamily_mem_traceless 2),
      pauliCoeff_pauliFamily]
    simp [secondAxisThirdColour, h]
  · rw [if_neg h, pauliCoeff_zero]
    simp [secondAxisThirdColour, h]
private theorem ofReal_cos_eq_exp_combination (x : ℝ) :
    ((Real.cos x : ℝ) : ℂ) = 2⁻¹ * Complex.exp (Complex.I * (x : ℂ)) +
      2⁻¹ * Complex.exp (Complex.I * ((-x : ℝ) : ℂ)) := by
  rw [Complex.ofReal_cos, Complex.cos]
  push_cast
  rw [show (x : ℂ) * Complex.I = Complex.I * x by ring,
    show -(x : ℂ) * Complex.I = Complex.I * -x by ring]
  ring
private theorem ofReal_sin_eq_exp_combination (x : ℝ) :
    ((Real.sin x : ℝ) : ℂ) = (2 * Complex.I)⁻¹ * Complex.exp (Complex.I * (x : ℂ)) +
      -(2 * Complex.I)⁻¹ * Complex.exp (Complex.I * ((-x : ℝ) : ℂ)) := by
  rw [Complex.ofReal_sin, Complex.sin]
  push_cast
  rw [show (x : ℂ) * Complex.I = Complex.I * x by ring,
    show -(x : ℂ) * Complex.I = Complex.I * -x by ring]
  field_simp
  ring_nf
  simp [Complex.I_sq]
private theorem exists_axis_and_intCoords (b : PeriodicOperators.PosEdge L k k) :
    ∃ (ρ : Fin 4) (y : Fin 4 → ℤ),
      b.1.terminal - b.1.initial = InfiniteLattice.axisStep (Tower.meshAt L k k) ρ ∧
        ∀ μ, (b.1.initial : AmbientSpace) μ = (y μ : ℝ) := by
  obtain ⟨ρ, hρ⟩ := b.2
  obtain ⟨y, hy⟩ := b.1.initial.2
  refine ⟨ρ, y, hρ, fun μ => ?_⟩
  rw [hy μ, meshAt_top, mul_one]
end EvaluationMaps
section Kernels
private theorem applyKernel_linComb {J J' : Type} (T : J' → J → ℂ) {u f g : J → ℂ} {α β : ℂ}
    (hu : ∀ ι, u ι = α * f ι + β * g ι) {ι' : J'} (hf : ApplySummableAt T f ι')
    (hg : ApplySummableAt T g ι') :
    applyKernel T u ι' = α * applyKernel T f ι' + β * applyKernel T g ι' := by
  have sf : Summable fun ι => T ι' ι * f ι := hf.of_norm
  have sg : Summable fun ι => T ι' ι * g ι := hg.of_norm
  simp only [applyKernel]
  rw [← tsum_mul_left, ← tsum_mul_left, ← (sf.mul_left α).tsum_add (sg.mul_left β)]
  exact tsum_congr fun ι => by rw [hu ι]; ring
private theorem norm_blochWave (I : PeriodicOperators.PeriodicData) (p : AmbientSpace)
    (φ : I.UnitQuot → ℂ) (ι : I.Carrier) :
    ‖PeriodicOperators.blochWave I (toComplexVec p) φ ι‖ = ‖φ (I.mkQuot 1 ι)‖ := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolNorm.norm_blochWave <;> assumption
private theorem norm_halfCombination_le {α β x y : ℂ} {K : ℝ} (hα : ‖α‖ ≤ 2⁻¹) (hβ : ‖β‖ ≤ 2⁻¹)
    (hx : ‖x‖ ≤ K) (hy : ‖y‖ ≤ K) : ‖α * x + β * y‖ ≤ K := by
  calc ‖α * x + β * y‖ ≤ ‖α‖ * ‖x‖ + ‖β‖ * ‖y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ 2⁻¹ * K + 2⁻¹ * K := by gcongr
    _ = K := by ring
end Kernels
section Squares
variable {L n k : ℕ}
private theorem card_vertex (hC : PeriodicLattice.SiteAndPlaquetteCounts) (hL : 0 < L) {j : ℕ}
    (hj : j ≤ k) : Nat.card (Tower.Vertex L n k j) = (2 * L ^ (n + (k - j))) ^ 4 := by
  have h := (hC L n (PeriodicLattice.levelDepth k j) hL
    (by simp only [PeriodicLattice.levelDepth]; omega)).2.2.1
  have e : ((n : ℤ) + PeriodicLattice.levelDepth k j).toNat = n + (k - j) := by
    simp only [PeriodicLattice.levelDepth]
    omega
  rw [e] at h
  exact h
private theorem finite_vertex (hC : PeriodicLattice.SiteAndPlaquetteCounts) (hL : 0 < L) {j : ℕ}
    (hj : j ≤ k) : Finite (Tower.Vertex L n k j) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_vertex hC hL hj]
  positivity
private theorem finite_positiveEdge (hC : PeriodicLattice.SiteAndPlaquetteCounts) (hL : 0 < L)
    {j : ℕ} (hj : j ≤ k) : Finite (Tower.PositiveEdge L n k j) := by
  have := finite_vertex (n := n) hC hL hj
  exact Finite.of_injective (fun b : Tower.PositiveEdge L n k j => (b.1.source, b.1.target))
    fun _ _ h => Subtype.ext (PeriodicLattice.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
private theorem card_positiveEdge_le (hC : PeriodicLattice.SiteAndPlaquetteCounts) (hL : 0 < L)
    {j : ℕ} (hj : j ≤ k) :
    Nat.card (Tower.PositiveEdge L n k j) ≤ 4 * Nat.card (Tower.Vertex L n k j) := by
  have := finite_vertex (n := n) hC hL hj
  let g : Tower.PositiveEdge L n k j → Fin 4 × Tower.Vertex L n k j :=
    fun b => (b.2.choose, b.1.source)
  have hg : Function.Injective g := by
    intro b b' h
    have h1 : b.2.choose = b'.2.choose := congrArg Prod.fst h
    have h2 : b.1.source = b'.1.source := congrArg Prod.snd h
    have s₁ := b.2.choose_spec
    have s₂ := b'.2.choose_spec
    apply Subtype.ext
    apply PeriodicLattice.Bond.ext h2
    have e : b.1.target - b.1.source = b'.1.target - b'.1.source := by
      rw [s₁, s₂, h1]
    rw [h2] at e
    exact sub_left_injective e
  have h := Nat.card_le_card_of_injective g hg
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at h
private theorem edgeFormPairing_self_re_le (hP : OneLoop.PauliMatrixRelations)
    (hC : PeriodicLattice.SiteAndPlaquetteCounts) (hL : 0 < L) {j : ℕ} (hj : j ≤ k)
    (X : Tower.edgeFormSpace L n k j) {K : ℝ}
    (h : ∀ (a : Fin 3) (q : Tower.PositiveEdge L n k j),
      ‖Tower.pauliCoeff a ((X : Tower.Edge L n k j → ComplexMatrix2) q.1)‖ ≤ K) :
    (Tower.edgeFormPairing (X : Tower.Edge L n k j → ComplexMatrix2)
        (X : Tower.Edge L n k j → ComplexMatrix2)).re ≤
      12 * K ^ 2 * ((2 * L ^ (n + (k - j))) ^ 4 : ℕ) := by
  classical
  have hfin := finite_positiveEdge (n := n) hC hL hj
  let _ := Fintype.ofFinite (Tower.PositiveEdge L n k j)
  have each : ∀ q : Tower.PositiveEdge L n k j,
      (ComplexMatrix2.halfTrace ((X : Tower.Edge L n k j → ComplexMatrix2) q.1 *
        (X : Tower.Edge L n k j → ComplexMatrix2) q.1)).re ≤ 3 * K ^ 2 := by
    intro q
    have hm := (X.2.1 _ q.2).2
    rw [halfTrace_mul_eq_sum hP hm hm, Complex.re_sum]
    have h1 : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
        (Tower.pauliCoeff a ((X : Tower.Edge L n k j → ComplexMatrix2) q.1) *
          Tower.pauliCoeff a ((X : Tower.Edge L n k j → ComplexMatrix2) q.1)).re ≤ K ^ 2 := by
      intro a _
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, ← pow_two]
      exact pow_le_pow_left₀ (norm_nonneg _) (h a q) 2
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    simpa using h2
  show (∑ᶠ q : Tower.PositiveEdge L n k j,
    ComplexMatrix2.halfTrace ((X : Tower.Edge L n k j → ComplexMatrix2) q.1 *
      (X : Tower.Edge L n k j → ComplexMatrix2) q.1)).re ≤ _
  rw [finsum_eq_sum_of_fintype, Complex.re_sum]
  have h3 := Finset.sum_le_card_nsmul Finset.univ _ _ fun q _ => each q
  refine h3.trans ?_
  have hcard := card_positiveEdge_le (n := n) hC hL hj
  rw [card_vertex hC hL hj, Nat.card_eq_fintype_card] at hcard
  have hcard' : (Fintype.card (Tower.PositiveEdge L n k j) : ℝ) ≤
      4 * ((2 * L ^ (n + (k - j))) ^ 4 : ℕ) := by
    exact_mod_cast hcard
  rw [nsmul_eq_mul, Finset.card_univ]
  calc (Fintype.card (Tower.PositiveEdge L n k j) : ℝ) * (3 * K ^ 2)
      ≤ (4 * ((2 * L ^ (n + (k - j))) ^ 4 : ℕ)) * (3 * K ^ 2) := by gcongr
    _ = 12 * K ^ 2 * ((2 * L ^ (n + (k - j))) ^ 4 : ℕ) := by ring
private theorem norm_pauliCoeff_le_of_coeffsOnEdges {j : ℕ} (hc : ProjCellsClassified L n k j)
    (X : Tower.Edge L n k j → ComplexMatrix2) {K : ℝ} (h : ∀ ι, ‖coeffsOnEdges L n k j X ι‖ ≤ K)
    (a : Fin 3) (q : Tower.PositiveEdge L n k j) : ‖Tower.pauliCoeff a (X q.1)‖ ≤ K := by
  obtain ⟨b', hb'⟩ := (hc .edge).1 q
  have e : projPositiveEdge L n k j b' = q := hb'
  have h' := h (a, b')
  simpa [coeffsOnEdges, Tower.toPauliCoeffs, Tower.restrictToPositiveEdges, e] using h'
private theorem coeffsOnEdges_meshScaledResponse (B : Tower.Edge L n k k → ComplexMatrix2)
    (ι : (colourEdges L k 0).Carrier) :
    coeffsOnEdges L n k 0 (meshScaledResponse L n k B) ι =
      ((Tower.finestMesh L k : ℝ) : ℂ) * coeffsOnEdges L n k 0 (periodicResponse L n k B) ι := by
  show Tower.pauliCoeff ι.1 ((Tower.finestMesh L k : ℝ) • (periodicResponse L n k B :
      Tower.Edge L n k 0 → ComplexMatrix2) (projPositiveEdge L n k 0 ι.2).1) =
    ((Tower.finestMesh L k : ℝ) : ℂ) * Tower.pauliCoeff ι.1 ((periodicResponse L n k B :
      Tower.Edge L n k 0 → ComplexMatrix2) (projPositiveEdge L n k 0 ι.2).1)
  rw [← Complex.coe_smul]
  exact pauliCoeff_smul ((periodicResponse L n k B).2.1 _ (projPositiveEdge L n k 0 ι.2).2).2 _ _
private theorem tripleNormSq_backgroundOnlyTriple (A : Tower.edgeFormSpace L n k 0) :
    tripleNormSq (backgroundOnlyTriple A) =
      (Tower.edgeFormPairing (A : Tower.Edge L n k 0 → ComplexMatrix2)
        (A : Tower.Edge L n k 0 → ComplexMatrix2)).re := by apply _root_.YangMills.SharedProofs.p87848 <;> assumption
end Squares
section Main
variable {L n k : ℕ}
private abbrev secondAxisAmplitude : Fin 4 → ComplexMatrix2 :=
  Tower.FullSpace.axisPauliElement SlopeCoefficient.secondAxis 2
private theorem coeffsOnEdges_periodicDefect {O : Set (Fin 4 → ℂ)} {hL : 0 < L}
    (hOn : Tower.ResponseSymbolNearStrip.HoldsOn L k hL O) {s s' : ℝ}
    (hs : toComplexVec (Pi.single 0 s) ∈ O) (hs' : toComplexVec (Pi.single 0 s') ∈ O)
    (hε : Tower.ResponseSymbolNearStrip.IsTracelessTuple secondAxisAmplitude)
    (B : Tower.edgeFormSpace L n k k) (hB : Tower.ResponseImagesFullSide.AtForm L n k B)
    {α β : ℂ} (hu : ∀ ι, coeffsOnEdges L n k k B ι = α * longWave L k s ι + β * longWave L k s' ι)
    (ι' : (colourEdges L k k).Carrier) :
    coeffsOnEdges L n k k (periodicDefect L n k B) ι' =
      α * PeriodicOperators.blochWave (colourEdges L k k) (toComplexVec (Pi.single 0 s))
          (Tower.FullSpace.coarseResponseSymbol L k (toComplexVec (Pi.single 0 s))
            secondAxisAmplitude) ι' +
        β * PeriodicOperators.blochWave (colourEdges L k k) (toComplexVec (Pi.single 0 s'))
          (Tower.FullSpace.coarseResponseSymbol L k (toComplexVec (Pi.single 0 s'))
            secondAxisAmplitude) ι' := by
  rw [hB.defect_coeffs, (hOn.coarse_wave _ hs _ hε).2, (hOn.coarse_wave _ hs' _ hε).2]
  exact applyKernel_linComb _ hu ((hOn.coarse_wave _ hs _ hε).1 ι')
    ((hOn.coarse_wave _ hs' _ hε).1 ι')
private theorem coeffsOnEdges_meshScaledResponse_eq {O : Set (Fin 4 → ℂ)} {hL : 0 < L}
    (hOn : Tower.ResponseSymbolNearStrip.HoldsOn L k hL O) {s s' : ℝ}
    (hs : toComplexVec (Pi.single 0 s) ∈ O) (hs' : toComplexVec (Pi.single 0 s') ∈ O)
    (hε : Tower.ResponseSymbolNearStrip.IsTracelessTuple secondAxisAmplitude)
    (B : Tower.edgeFormSpace L n k k) (hB : Tower.ResponseImagesFullSide.AtForm L n k B)
    {α β : ℂ} (hu : ∀ ι, coeffsOnEdges L n k k B ι = α * longWave L k s ι + β * longWave L k s' ι)
    (ι' : (colourEdges L k 0).Carrier) :
    coeffsOnEdges L n k 0 (meshScaledResponse L n k B) ι' =
      α * PeriodicOperators.blochWave (colourEdges L k 0) (toComplexVec (Pi.single 0 s))
          (Tower.FullSpace.backgroundResponseSymbol L k (toComplexVec (Pi.single 0 s))
            secondAxisAmplitude) ι' +
        β * PeriodicOperators.blochWave (colourEdges L k 0) (toComplexVec (Pi.single 0 s'))
          (Tower.FullSpace.backgroundResponseSymbol L k (toComplexVec (Pi.single 0 s'))
            secondAxisAmplitude) ι' := by
  rw [coeffsOnEdges_meshScaledResponse, hB.resp_coeffs, (hOn.background_wave _ hs _ hε).2,
    (hOn.background_wave _ hs' _ hε).2,
    applyKernel_linComb _ hu ((hOn.background_wave _ hs _ hε).1 ι')
      ((hOn.background_wave _ hs' _ hε).1 ι')]
  simp only [Pi.smul_apply, smul_eq_mul]
  show _ = α * (_ * applyKernel (Tower.BackgroundFieldResponse.responseKernel L k)
      (longWave L k s) ι') +
    β * (_ * applyKernel (Tower.BackgroundFieldResponse.responseKernel L k) (longWave L k s') ι')
  ring
private theorem finite_unitQuot (hC : PeriodicLattice.SiteAndPlaquetteCounts) (hL : 0 < L)
    (hc : ProjCellsClassified L 1 k 0) : Finite (colourEdges L k 0).UnitQuot := by
  have := finite_positiveEdge (n := 1) (k := k) (j := 0) hC hL (Nat.zero_le k)
  choose pre hpre using (hc .edge).1
  let g : Fin 3 × Tower.PositiveEdge L 1 k 0 → (colourEdges L k 0).UnitQuot :=
    fun c => (colourEdges L k 0).mkQuot 1 (c.1, pre c.2)
  refine Finite.of_surjective g ?_
  intro c
  obtain ⟨⟨a, b⟩, rfl⟩ := Quot.exists_rep c
  refine ⟨(a, projPositiveEdge L 1 k 0 b), ?_⟩
  have e : projPositiveEdge L 1 k 0 (pre (projPositiveEdge L 1 k 0 b)) =
      projPositiveEdge L 1 k 0 b := hpre _
  obtain ⟨m, hm⟩ := ((hc .edge).2 _ _).1 e
  exact Quot.sound ⟨periodSide L 1 • m, by
    rw [one_nsmul]
    exact Prod.ext rfl hm⟩
private theorem euclidNorm_axisVec_sq (s : ℝ) :
    Tower.ResponseProperties.euclidNorm (toComplexVec (Pi.single 0 s)) ^ 2 = s ^ 2 := by
  unfold Tower.ResponseProperties.euclidNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity), Finset.sum_eq_single 0]
  · simp [toComplexVec]
  · intro μ _ h
    simp [toComplexVec, Pi.single_eq_of_ne h]
  · simp
private theorem norm_axisVec_lt {s r : ℝ} (hr : 0 < r) (hs : |s| < r) :
    ‖toComplexVec (Pi.single 0 s)‖ < r := by
  rw [pi_norm_lt_iff hr]
  intro μ
  by_cases h : μ = 0
  · subst h
    simpa [toComplexVec] using hs
  · simpa [toComplexVec, Pi.single_eq_of_ne h] using hr
theorem longWaveSizeBounds_holds (hI : Tower.ResponseImagesFullSide.ResponseImagesHold)
    (hS : Tower.ResponseSymbolNearStrip.ResponseSymbolHolomorphicNearStrip)
    (hZ : Tower.ResponseSymbolNearZero.ComponentsNearZero)
    (hY : LocalKernels.Periodisation.PeriodisationHolds)
    (hT : PeriodicOperators.TowerTranslations.Claim)
    (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (hP : OneLoop.PauliMatrixRelations)
    (hN : Tower.FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) :
    LongWaveSizeBounds := by
  intro L _ hst k hk
  have L0 : 0 < L := by
    have := hst.2
    omega
  have L2 : 2 ≤ L := by
    have := hst.2
    omega
  obtain ⟨δ₀, hδ₀, hS'⟩ := hS
  obtain ⟨O, -, hsub, hOn⟩ := hS' L L0 hst k hk
  obtain ⟨-, -, δ₁, hδ₁, C₀, -, hI', -, -⟩ := hN
  have e₀ : δ₀ = δ₁ := Part.mem_unique hδ₀ hδ₁
  have hδ : 0 < δ₀ := by
    rw [e₀]
    exact hI'.1
  have hO : ∀ s : ℝ, toComplexVec (Pi.single 0 s) ∈ O := fun s => hsub fun μ => by
    simp only [toComplexVec, Complex.ofReal_im, abs_zero]
    positivity
  have hε : Tower.ResponseSymbolNearStrip.IsTracelessTuple secondAxisAmplitude := by
    intro ρ
    by_cases h : ρ = SlopeCoefficient.secondAxis
    · subst h
      simpa [secondAxisAmplitude, Tower.FullSpace.axisPauliElement] using pauliFamily_mem_traceless 2
    · simp [secondAxisAmplitude, Tower.FullSpace.axisPauliElement, Pi.single_eq_of_ne h]
  obtain ⟨C₁, N, hN₀, hbound⟩ := hZ δ₀ hδ₀ L hst k hk secondAxisAmplitude hε
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hN₀
  have hfin : Finite (colourEdges L k 0).UnitQuot :=
    finite_unitQuot hC L0 ((hY L hst k 1 one_pos).1 0 (Nat.zero_le k)).1
  obtain ⟨K₂, hK₂, hbg⟩ : ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ p ∈ O, ∀ c,
      ‖Tower.FullSpace.backgroundResponseSymbol L k p secondAxisAmplitude c‖ ≤ K₂ := by
    have hb := (hOn.background_entries secondAxisAmplitude hε).2
    choose D hD using hb
    let _ := Fintype.ofFinite (colourEdges L k 0).UnitQuot
    refine ⟨∑ c, |D c|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun p hp c => ?_⟩
    exact (hD c p hp).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun c => |D c|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ c)))
  have hQ : 0 ≤ K₂ ^ 2 * (L : ℝ) ^ (4 * k) := by positivity
  refine ⟨12 * (1 + C₁ ^ 2 + K₂ ^ 2 * (L : ℝ) ^ (4 * k)), r, by positivity, hr, ?_⟩
  intro n₀ m t ht htr
  filter_upwards [eventually_ge_atTop (max n₀ 1)] with n hn
  have hn₀ : n₀ ≤ n := le_of_max_le_left hn
  have hn1 : 0 < n := le_of_max_le_right hn
  obtain ⟨hcb, -⟩ := hY L hst k n hn1
  have hc₀ := (hcb 0 (Nat.zero_le k)).1
  have hck := (hcb k le_rfl).1
  have hb := (hcb k le_rfl).2
  have hM : t * ((2 * L ^ n : ℕ) : ℝ) = 2 * Real.pi * ((m * (L : ℤ) ^ (n - n₀) : ℤ) : ℝ) := by
    have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast L0.ne'
    have e : (L : ℝ) ^ n = (L : ℝ) ^ n₀ * (L : ℝ) ^ (n - n₀) := by
      rw [← pow_add]
      congr 1
      omega
    rw [ht]
    push_cast
    rw [e]
    field_simp
  have mC := planeWaveValues_mem (k := k) L2 hn1 (cosinePhase t)
  have mS := planeWaveValues_mem (k := k) L2 hn1 (sinePhase t)
  set V : ℝ := (2 * (L : ℝ) ^ n) ^ 4 with hV
  have hV0 : 0 ≤ V := by positivity
  have cardTop : (((2 * L ^ (n + (k - k))) ^ 4 : ℕ) : ℝ) = V := by
    simp [hV]
  have cardBottom : (((2 * L ^ (n + (k - 0))) ^ 4 : ℕ) : ℝ) = (L : ℝ) ^ (4 * k) * V := by
    simp only [hV, Nat.sub_zero]
    push_cast
    rw [pow_add, pow_mul']
    ring
  have inN : ∀ s : ℝ, |s| < r → toComplexVec (Pi.single 0 s) ∈ N := fun s hs => hball (by
    rw [Metric.mem_ball, dist_zero_right]
    exact norm_axisVec_lt hr hs)
  have coarse : ∀ s : ℝ, s ^ 2 = t ^ 2 → |s| < r → ∀ c,
      ‖Tower.FullSpace.coarseResponseSymbol L k (toComplexVec (Pi.single 0 s))
        secondAxisAmplitude c‖ ≤ |C₁| * t ^ 2 := by
    intro s hs hsr c
    refine ((hbound _ (inN s hsr)).2.1 c).trans ?_
    rw [euclidNorm_axisVec_sq, hs]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have htr' : |(-t)| < r := by rwa [abs_neg]
  have key : ∀ (B : Tower.edgeFormSpace L n k k) (α β : ℂ), ‖α‖ ≤ 2⁻¹ → ‖β‖ ≤ 2⁻¹ →
      (∀ ι, coeffsOnEdges L n k k B ι = α * longWave L k t ι + β * longWave L k (-t) ι) →
      (∀ ι, ‖coeffsOnEdges L n k k B ι‖ ≤ 1) →
      topFormNormSq B ≤ 12 * (1 + C₁ ^ 2 + K₂ ^ 2 * (L : ℝ) ^ (4 * k)) * V ∧
      topFormNormSq (periodicDefect L n k B) ≤
        12 * (1 + C₁ ^ 2 + K₂ ^ 2 * (L : ℝ) ^ (4 * k)) * V * t ^ 4 ∧
      tripleNormSq (backgroundOnlyTriple (meshScaledResponse L n k B)) ≤
        12 * (1 + C₁ ^ 2 + K₂ ^ 2 * (L : ℝ) ^ (4 * k)) * V := by
    intro B α β hα hβ hu hone
    have hB := hI L hst k hk n hn1 B
    have hC1 : 0 ≤ C₁ ^ 2 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · have h1 := edgeFormPairing_self_re_le hP hC L0 le_rfl B (K := 1)
        (norm_pauliCoeff_le_of_coeffsOnEdges hck B hone)
      rw [cardTop] at h1
      refine h1.trans ?_
      nlinarith [mul_nonneg hC1 hV0, mul_nonneg hQ hV0]
    · have hread : ∀ ι, ‖coeffsOnEdges L n k k (periodicDefect L n k B) ι‖ ≤ |C₁| * t ^ 2 := by
        intro ι
        rw [coeffsOnEdges_periodicDefect hOn (hO t) (hO (-t)) hε B hB hu ι]
        refine norm_halfCombination_le hα hβ ?_ ?_
        · rw [norm_blochWave]
          exact coarse t rfl htr _
        · rw [norm_blochWave]
          exact coarse (-t) (by ring) htr' _
      have h1 := edgeFormPairing_self_re_le hP hC L0 le_rfl (periodicDefect L n k B)
        (K := |C₁| * t ^ 2) (norm_pauliCoeff_le_of_coeffsOnEdges hck _ hread)
      rw [cardTop] at h1
      refine h1.trans ?_
      have e : 12 * (|C₁| * t ^ 2) ^ 2 * V = 12 * C₁ ^ 2 * V * t ^ 4 := by
        rw [mul_pow, sq_abs]
        ring
      rw [e]
      have ht4 : 0 ≤ V * t ^ 4 := by positivity
      nlinarith [mul_nonneg hQ ht4]
    · have hread : ∀ ι, ‖coeffsOnEdges L n k 0 (meshScaledResponse L n k B) ι‖ ≤ K₂ := by
        intro ι
        rw [coeffsOnEdges_meshScaledResponse_eq hOn (hO t) (hO (-t)) hε B hB hu ι]
        refine norm_halfCombination_le hα hβ ?_ ?_
        · rw [norm_blochWave]
          exact hbg _ (hO t) _
        · rw [norm_blochWave]
          exact hbg _ (hO (-t)) _
      have h1 := edgeFormPairing_self_re_le hP hC L0 (Nat.zero_le k) (meshScaledResponse L n k B)
        (K := K₂) (norm_pauliCoeff_le_of_coeffsOnEdges hc₀ _ hread)
      rw [cardBottom] at h1
      rw [tripleNormSq_backgroundOnlyTriple]
      refine h1.trans ?_
      nlinarith [mul_nonneg hC1 hV0, mul_nonneg hQ hV0]
  have half : ‖(2⁻¹ : ℂ)‖ ≤ 2⁻¹ := by simp
  have halfI : ‖((2 * Complex.I)⁻¹ : ℂ)‖ ≤ 2⁻¹ := by simp
  have halfI' : ‖(-(2 * Complex.I)⁻¹ : ℂ)‖ ≤ 2⁻¹ := by simp
  refine ⟨⟨_, mC⟩, ⟨_, mS⟩, ⟨rfl, rfl⟩, ?_⟩
  intro B hBm
  rcases hBm with rfl | hBm
  · refine key _ _ _ half half ?_ ?_
    · rintro ⟨a, b⟩
      obtain ⟨ρ, y, hρ, hy⟩ := exists_axis_and_intCoords b
      show coeffsOnEdges L n k k (planeWaveValues L n k (cosinePhase t)) (a, b) = _
      rw [coeffsOnEdges_planeWaveValues hb _ a b ρ hρ y hy, longWave_apply hT hst hk t a b ρ hρ y hy,
        longWave_apply hT hst hk (-t) a b ρ hρ y hy, cosinePhase_at_cast hM y,
        ofReal_cos_eq_exp_combination, neg_mul]
      ring
    · rintro ⟨a, b⟩
      obtain ⟨ρ, y, hρ, hy⟩ := exists_axis_and_intCoords b
      show ‖coeffsOnEdges L n k k (planeWaveValues L n k (cosinePhase t)) (a, b)‖ ≤ 1
      rw [coeffsOnEdges_planeWaveValues hb _ a b ρ hρ y hy, cosinePhase_at_cast hM y, norm_mul,
        Complex.norm_real]
      calc _ ≤ (1 : ℝ) * 1 := mul_le_mul (Real.abs_cos_le_one _)
            (norm_secondAxisThirdColour_le ρ a) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  · obtain rfl := Set.mem_singleton_iff.1 hBm
    refine key _ _ _ halfI halfI' ?_ ?_
    · rintro ⟨a, b⟩
      obtain ⟨ρ, y, hρ, hy⟩ := exists_axis_and_intCoords b
      show coeffsOnEdges L n k k (planeWaveValues L n k (sinePhase t)) (a, b) = _
      rw [coeffsOnEdges_planeWaveValues hb _ a b ρ hρ y hy, longWave_apply hT hst hk t a b ρ hρ y hy,
        longWave_apply hT hst hk (-t) a b ρ hρ y hy, sinePhase_at_cast hM y,
        ofReal_sin_eq_exp_combination, neg_mul]
      ring
    · rintro ⟨a, b⟩
      obtain ⟨ρ, y, hρ, hy⟩ := exists_axis_and_intCoords b
      show ‖coeffsOnEdges L n k k (planeWaveValues L n k (sinePhase t)) (a, b)‖ ≤ 1
      rw [coeffsOnEdges_planeWaveValues hb _ a b ρ hρ y hy, sinePhase_at_cast hM y, norm_mul,
        Complex.norm_real]
      calc _ ≤ (1 : ℝ) * 1 := mul_le_mul (Real.abs_sin_le_one _)
            (norm_secondAxisThirdColour_le ρ a) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
end Main
end YangMills.Construction.RunningCouplingSlope.LongWaveSizes
end

import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreCarriedProof
import YangMills.Construction.ColdStepAtMirrorFrames.ChartUnderGaugesAndShiftsProof
import YangMills.Construction.ColdStepAtMirrorFrames.CurvedChainIsAbelianProof
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ColdChainAtEveryLevel.VariationOfABond
import YangMills.Construction.ColdStepAtMirrorFrames.BlockMeansOfFormsOnATorus
import YangMills.Construction.ColdStepAtMirrorFrames.SmallUnitsAndTheirLogarithms
import YangMills.Construction.ResponseInTheExpansion.KernelOfTheMaxwellForm
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesAboutASiteProof
import YangMills.Construction.SummableBoundsOfTheFlow.EntriesOfTheLevelsOnTwoTori
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ResponseInTheExpansion
namespace MaxwellKernel
section Paths
variable {F : BlockAverages.BlockFrame} {j : ℕ}
private def reverseStep (st : BlockAverages.PathStep) : BlockAverages.PathStep := (st.1, !st.2)
private theorem re_mul_comm (p q : ℍ[ℝ]) : (p * q).re = (q * p).re := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.quaternion_re_mul_comm <;> assumption
private theorem map_reverseStep_axisPath (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    (BlockAverages.axisPath h π).map reverseStep = BlockAverages.axisPath (-h) π := by
  unfold BlockAverages.axisPath
  rw [List.map_flatMap]
  congr 1
  funext k
  rw [List.map_replicate]
  have e : (h (π k)).natAbs = ((-h) (π k)).natAbs := by simp
  rw [← e]
  by_cases hz : h (π k) = 0
  · simp [hz]
  · have hd : decide (0 ≤ -(h (π k))) = !decide (0 ≤ h (π k)) := by
      rcases lt_or_gt_of_ne hz with hlt | hgt
      · rw [decide_eq_true (by omega : 0 ≤ -(h (π k))), decide_eq_false (by omega : ¬ 0 ≤ h (π k))]
        rfl
      · rw [decide_eq_false (by omega : ¬ 0 ≤ -(h (π k))), decide_eq_true (by omega : 0 ≤ h (π k))]
        rfl
    have hf : reverseStep (π k, decide (0 ≤ h (π k))) = (π k, decide (0 ≤ (-h) (π k))) := by
      show (π k, !decide (0 ≤ h (π k))) = (π k, decide (0 ≤ -(h (π k))))
      rw [hd]
    rw [hf]
private theorem map_reverseStep_bondContour (L : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (BlockAverages.bondContour L h π i).map reverseStep =
      BlockAverages.reversePath (BlockAverages.bondContour L (-h) π i) := by
  unfold BlockAverages.bondContour
  rw [← map_reverseStep_axisPath h π]
  simp [BlockAverages.reversePath, reverseStep, List.map_reverse, Function.comp_def]
private theorem pathHolonomy_reversePath_walkTarget (X : F.GaugeField j) (l : List BlockAverages.PathStep)
    (x : F.Site j) :
    BlockAverages.pathHolonomy X (ColdStepAtMirrorFrames.walkTarget x l) (BlockAverages.reversePath l) =
      (BlockAverages.pathHolonomy X x l)⁻¹ := by
  have e : ColdStepAtMirrorFrames.walkTarget x l =
      x + BlockAverages.siteOfCoords j (LatticePaths.endpoint 0 l) := by
    induction l generalizing x with
    | nil => simp [ColdStepAtMirrorFrames.walkTarget, LatticePaths.endpoint,
        ColdStepAtMirrorFrames.siteOfCoords_map_zero]
    | cons st r ih =>
      show ColdStepAtMirrorFrames.walkTarget (x + BlockAverages.stepDisplacement j st) r = _
      rw [ih]
      exact BondVariation.add_stepDisplacement_add_endpoint x st r
  rw [e]
  exact BondVariation.pathHolonomy_reversePath X l x
private def shiftField (v : F.Site j) (X : F.GaugeField j) : F.GaugeField j := fun x i => X (x + v) i
private def reflectField (X : F.GaugeField j) : F.GaugeField j :=
  fun x i => (X (-x - BlockAverages.unitStep j i) i)⁻¹
private theorem pathHolonomy_shiftField (v : F.Site j) (X : F.GaugeField j) (x : F.Site j)
    (l : List BlockAverages.PathStep) :
    BlockAverages.pathHolonomy (shiftField v X) x l = BlockAverages.pathHolonomy X (x + v) l := by apply _root_.YangMills.Construction.StepInvariance.pathHolonomy_translate <;> assumption
private theorem pathHolonomy_reflectField (X : F.GaugeField j) (x : F.Site j) (l : List BlockAverages.PathStep) :
    BlockAverages.pathHolonomy (reflectField X) x l = BlockAverages.pathHolonomy X (-x) (l.map reverseStep) := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have e1 : -(x + BlockAverages.stepDisplacement j st) = -x + BlockAverages.stepDisplacement j (reverseStep st) := by
      obtain ⟨k, b⟩ := st
      cases b <;> simp [BlockAverages.stepDisplacement, reverseStep] <;> abel
    have e2 : BlockAverages.linkValue (reflectField X) x st = BlockAverages.linkValue X (-x) (reverseStep st) := by
      obtain ⟨k, b⟩ := st
      cases b
      · have : -(x - BlockAverages.unitStep j k) - BlockAverages.unitStep j k = -x := by abel
        simp [BlockAverages.linkValue, reflectField, reverseStep, this]
      · simp [BlockAverages.linkValue, reflectField, reverseStep]
    simp only [BlockAverages.pathHolonomy, List.map_cons]
    rw [ih, e1, e2]
private theorem reflectField_reflectField (X : F.GaugeField j) : reflectField (reflectField X) = X := by
  funext x i
  have : -(-x - BlockAverages.unitStep j i) - BlockAverages.unitStep j i = x := by abel
  simp [reflectField, this]
private theorem plaquetteHolonomy_eq (U : F.GaugeField j) (x : F.Site j) (μ ν : Fin 4) :
    BlockAverages.plaquetteHolonomy U (x, μ, ν) =
      U x μ * U (x + BlockAverages.unitStep j μ) ν * (U (x + BlockAverages.unitStep j ν) μ)⁻¹ * (U x ν)⁻¹ := by apply _root_.YangMills.Construction.PlaquetteExpansion.plaquetteHolonomy_eq <;> assumption
private theorem re_plaquetteHolonomy_reflectField (U : F.GaugeField j) (x : F.Site j) (μ ν : Fin 4) :
    ((BlockAverages.plaquetteHolonomy (reflectField U) (x, μ, ν) : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re =
      ((BlockAverages.plaquetteHolonomy U
        (-x - BlockAverages.unitStep j μ - BlockAverages.unitStep j ν, μ, ν) : BlockAverages.UnitQuaternion) :
          ℍ[ℝ]).re := by
  rw [plaquetteHolonomy_eq, plaquetteHolonomy_eq]
  have b1 : -x - BlockAverages.unitStep j μ =
      (-x - BlockAverages.unitStep j μ - BlockAverages.unitStep j ν) + BlockAverages.unitStep j ν := by abel
  have b2 : -(x + BlockAverages.unitStep j μ) - BlockAverages.unitStep j ν =
      -x - BlockAverages.unitStep j μ - BlockAverages.unitStep j ν := by abel
  have b3 : -(x + BlockAverages.unitStep j ν) - BlockAverages.unitStep j μ =
      -x - BlockAverages.unitStep j μ - BlockAverages.unitStep j ν := by abel
  have b4 : -x - BlockAverages.unitStep j ν =
      (-x - BlockAverages.unitStep j μ - BlockAverages.unitStep j ν) + BlockAverages.unitStep j μ := by abel
  simp only [reflectField, b2, b3, inv_inv]
  rw [← b1, ← b4]
  have key : ∀ P Q : BlockAverages.UnitQuaternion,
      ((P * Q : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re = ((Q * P : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re :=
    fun P Q => re_mul_comm (P : ℍ[ℝ]) Q
  have := key ((U (-x - BlockAverages.unitStep j μ) μ)⁻¹ *
      (U (-x - BlockAverages.unitStep j μ - BlockAverages.unitStep j ν) ν)⁻¹)
    (U (-x - BlockAverages.unitStep j μ - BlockAverages.unitStep j ν) μ * U (-x - BlockAverages.unitStep j ν) ν)
  simpa only [mul_assoc] using this
end Paths
section Frames
variable {F : BlockAverages.BlockFrame}
private theorem mem_innerBonds_finiteCells (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {k : ℕ}
    (hk : k ≤ F.top) (b : F.Site k × Fin 4) :
    b ∈ BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells F) k := by
  unfold BlockAverages.innerBonds
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells hodd hs hk _,
    ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells hodd hs hk _⟩
private theorem mem_innerPlaquettes_finiteCells (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {k : ℕ}
    (hk : k ≤ F.top) (p : F.Site k × Fin 4 × Fin 4) :
    p ∈ BlockAverages.innerPlaquettes (ColdStepAtMirrorFrames.finiteCells F) k ↔ p.2.1 < p.2.2 := by
  unfold BlockAverages.innerPlaquettes
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, true_and]
  constructor
  · exact fun h => h.2.1
  · exact fun h => ⟨ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells hodd hs hk _, h,
      fun z _ => ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells hodd hs hk _⟩
private def liftedOffset (F : BlockAverages.BlockFrame) (w : Fin 4 → ℤ) (j : ℕ) : F.Site j :=
  BlockAverages.siteOfCoords j fun i => (F.blockSide : ℤ) ^ (F.top - j) * w i
private theorem refineSite_neg {j : ℕ} (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) :
    BlockAverages.refineSite (-y) = - BlockAverages.refineSite y := by
  conv_lhs => rw [← ColdStepAtMirrorFrames.siteOfCoords_siteCoords y, ← ColdStepAtMirrorFrames.siteOfCoords_neg,
    ColdStepAtMirrorFrames.blockRefine_siteOfCoords hj]
  conv_rhs => rw [← ColdStepAtMirrorFrames.siteOfCoords_siteCoords y, ColdStepAtMirrorFrames.blockRefine_siteOfCoords hj,
    ← ColdStepAtMirrorFrames.siteOfCoords_neg]
  congr 1
  funext i
  simp
private theorem neg_mem_centredCube {M : ℕ} {h : Fin 4 → ℤ} (hh : h ∈ BlockAverages.centredCube M) :
    -h ∈ BlockAverages.centredCube M := by apply _root_.YangMills.DeltaSharedProofs.p501275 <;> assumption
private theorem star_smul_real (r : ℝ) (q : ℍ[ℝ]) : star (r • q) = r • star q := by
  ext <;> simp
private theorem contourAverage_reflectField {j : ℕ} (hj : j + 1 ≤ F.top) (W : F.GaugeField j)
    (y : F.Site (j + 1)) (i : Fin 4) :
    BlockAverages.contourAverage (reflectField W) (y, i) =
      star (BlockAverages.contourAverage W (-y - BlockAverages.unitStep (j + 1) i, i)) := by
  unfold BlockAverages.contourAverage
  rw [star_smul_real, star_sum]
  congr 1
  refine Finset.sum_nbij' (fun h => -h) (fun h => -h) (fun h hh => neg_mem_centredCube hh)
    (fun h hh => neg_mem_centredCube hh) (fun h _ => neg_neg h) (fun h _ => neg_neg h) fun h _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  have e : ColdStepAtMirrorFrames.walkTarget (BlockAverages.refineSite (-y - BlockAverages.unitStep (j + 1) i))
      (BlockAverages.bondContour F.blockSide (-h) π i) = - BlockAverages.refineSite y := by
    rw [ColdStepAtMirrorFrames.walkTarget_bondContour (by omega)]
    have : -y - BlockAverages.unitStep (j + 1) i + BlockAverages.unitStep (j + 1) i = -y := by abel
    rw [this, refineSite_neg hj]
  rw [pathHolonomy_reflectField, map_reverseStep_bondContour, ← e, pathHolonomy_reversePath_walkTarget]
  rfl
private theorem blockFit_shiftField (w : Fin 4 → ℤ) {j : ℕ} (hj : j + 1 ≤ F.top) (W : F.GaugeField j)
    (V : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    BlockAverages.blockFit (shiftField (liftedOffset F w j) W) (shiftField (liftedOffset F w (j + 1)) V) c =
      BlockAverages.blockFit W V (c.1 + liftedOffset F w (j + 1), c.2) := by apply _root_.YangMills.Construction.ChartSymmetries.blockFit_translateBy <;> assumption
private theorem blockFit_reflectField {j : ℕ} (hj : j + 1 ≤ F.top) (W : F.GaugeField j) (V : F.GaugeField (j + 1))
    (y : F.Site (j + 1)) (i : Fin 4) :
    BlockAverages.blockFit (reflectField W) (reflectField V) (y, i) =
      BlockAverages.blockFit W V (-y - BlockAverages.unitStep (j + 1) i, i) := by
  unfold BlockAverages.blockFit
  rw [contourAverage_reflectField hj, norm_star]
  congr 1
  show (star _ * (((V (-y - BlockAverages.unitStep (j + 1) i) i)⁻¹)⁻¹ : BlockAverages.UnitQuaternion).1).re = _
  rw [inv_inv]
  set M := BlockAverages.contourAverage W (-y - BlockAverages.unitStep (j + 1) i, i)
  set g := V (-y - BlockAverages.unitStep (j + 1) i) i
  show _ = (M * star (g : ℍ[ℝ])).re
  rw [← Quaternion.re_star (M * star (g : ℍ[ℝ])), star_mul, star_star, re_mul_comm]
private theorem minimalAction_shiftField (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (a : ℝ)
    (w : Fin 4 → ℤ) (j : ℕ) :
    j ≤ F.top → ∀ X : F.GaugeField j,
      BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells F) j (shiftField (liftedOffset F w j) X) =
        BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells F) j X := by
  induction j with
  | zero =>
    intro hk U
    show BlockAverages.wilsonAction _ _ = BlockAverages.wilsonAction _ _
    unfold BlockAverages.wilsonAction
    refine Finset.sum_nbij' (fun p => (p.1 + liftedOffset F w 0, p.2)) (fun p => (p.1 - liftedOffset F w 0, p.2))
      ?_ ?_ ?_ ?_ ?_
    · intro p hp
      exact (mem_innerPlaquettes_finiteCells hodd hs hk _).2 ((mem_innerPlaquettes_finiteCells hodd hs hk p).1 hp)
    · intro p hp
      exact (mem_innerPlaquettes_finiteCells hodd hs hk _).2 ((mem_innerPlaquettes_finiteCells hodd hs hk p).1 hp)
    · intro p _
      simp
    · intro p _
      simp
    · intro p _
      simp only [BlockAverages.plaquetteHolonomy]
      rw [pathHolonomy_shiftField]
  | succ j ih =>
    intro hj V
    have hj' : j ≤ F.top := by omega
    let e : F.GaugeField j ≃ F.GaugeField j :=
      ⟨shiftField (liftedOffset F w j), shiftField (-liftedOffset F w j), fun X => by funext x i; simp [shiftField],
        fun X => by funext x i; simp [shiftField]⟩
    show (⨅ W : F.GaugeField j, (BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells F) j W +
      a * ∑ c ∈ BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells F) (j + 1),
        BlockAverages.blockFit W (shiftField (liftedOffset F w (j + 1)) V) c)) =
      ⨅ W : F.GaugeField j, (BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells F) j W +
        a * ∑ c ∈ BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells F) (j + 1),
          BlockAverages.blockFit W V c)
    rw [← e.iInf_comp]
    refine iInf_congr fun W => ?_
    show BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells F) j
      (shiftField (liftedOffset F w j) W) + _ = _
    rw [ih hj' W]
    congr 2
    refine Finset.sum_nbij' (fun c => (c.1 + liftedOffset F w (j + 1), c.2))
      (fun c => (c.1 - liftedOffset F w (j + 1), c.2))
      (fun c _ => mem_innerBonds_finiteCells hodd hs hj _) (fun c _ => mem_innerBonds_finiteCells hodd hs hj _)
      ?_ ?_ ?_
    · intro c _
      simp
    · intro c _
      simp
    · intro c _
      exact blockFit_shiftField w hj W V c
private theorem minimalAction_reflectField (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (a : ℝ) (j : ℕ) :
    j ≤ F.top → ∀ X : F.GaugeField j,
      BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells F) j (reflectField X) =
        BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells F) j X := by
  induction j with
  | zero =>
    intro hk U
    show BlockAverages.wilsonAction _ _ = BlockAverages.wilsonAction _ _
    unfold BlockAverages.wilsonAction
    refine Finset.sum_nbij' (fun p => (-p.1 - BlockAverages.unitStep 0 p.2.1 - BlockAverages.unitStep 0 p.2.2, p.2))
      (fun p => (-p.1 - BlockAverages.unitStep 0 p.2.1 - BlockAverages.unitStep 0 p.2.2, p.2)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      exact (mem_innerPlaquettes_finiteCells hodd hs hk _).2 ((mem_innerPlaquettes_finiteCells hodd hs hk p).1 hp)
    · intro p hp
      exact (mem_innerPlaquettes_finiteCells hodd hs hk _).2 ((mem_innerPlaquettes_finiteCells hodd hs hk p).1 hp)
    · rintro ⟨x, μ, ν⟩ _
      simp only [Prod.mk.injEq, and_true]
      abel
    · rintro ⟨x, μ, ν⟩ _
      simp only [Prod.mk.injEq, and_true]
      abel
    · rintro ⟨x, μ, ν⟩ _
      simp only
      rw [re_plaquetteHolonomy_reflectField]
  | succ j ih =>
    intro hj V
    have hj' : j ≤ F.top := by omega
    let e : F.GaugeField j ≃ F.GaugeField j :=
      ⟨reflectField, reflectField, reflectField_reflectField, reflectField_reflectField⟩
    show (⨅ W : F.GaugeField j, (BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells F) j W +
      a * ∑ c ∈ BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells F) (j + 1),
        BlockAverages.blockFit W (reflectField V) c)) =
      ⨅ W : F.GaugeField j, (BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells F) j W +
        a * ∑ c ∈ BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells F) (j + 1),
          BlockAverages.blockFit W V c)
    rw [← e.iInf_comp]
    refine iInf_congr fun W => ?_
    show BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells F) j (reflectField W) + _ = _
    rw [ih hj' W]
    congr 2
    refine Finset.sum_nbij' (fun c => (-c.1 - BlockAverages.unitStep (j + 1) c.2, c.2))
      (fun c => (-c.1 - BlockAverages.unitStep (j + 1) c.2, c.2))
      (fun c _ => mem_innerBonds_finiteCells hodd hs hj _) (fun c _ => mem_innerBonds_finiteCells hodd hs hj _)
      ?_ ?_ ?_
    · rintro ⟨y, i⟩ _
      simp only [Prod.mk.injEq, and_true]
      abel
    · rintro ⟨y, i⟩ _
      simp only [Prod.mk.injEq, and_true]
      abel
    · rintro ⟨y, i⟩ _
      exact blockFit_reflectField hj W V y i
end Frames
section Torus
variable {m L' : ℕ} [NeZero m]
private def reflectTorusField (W : TorusFields.TorusField m) : TorusFields.TorusField m :=
  fun x i => (W (-x - TorusFields.unitStep m i) i)⁻¹
private def reflectBond (b : TorusFields.TorusBond m) : TorusFields.TorusBond m :=
  (-(b.1 + TorusFields.unitStep m b.2), b.2)
private theorem actionAtLevel_univ (a : ℝ) (L t : ℕ) (W : TorusFields.TorusField m) :
    TorusFields.actionAtLevel a L (t + 1) Finset.univ W =
      BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t m)) (t + 1)
        (TorusFields.readAtLevel (TorusFields.torusFrame L t m) (t + 1) W) := by
  show BlockAverages.minimalAction a
    (TorusFields.cellsOfSites (TorusFields.torusFrame L t m) Finset.univ) (t + 1) _ = _
  rw [TopLevelSites.cellsOfSites_univ fun _ => rfl]
private theorem siteOfCell_add_liftedOffset (L t : ℕ) (u : TorusFields.TorusSite m)
    (x : (TorusFields.torusFrame L t m).Cell) :
    TorusFrame.siteOfCell (x + liftedOffset (TorusFields.torusFrame L t m) (fun i => ((u i).cast : ℤ))
      (TorusFields.torusFrame L t m).top) = TorusFrame.siteOfCell x + u := by
  rw [TorusFrame.siteOfCell_add]
  congr 1
  unfold liftedOffset
  rw [TorusFrame.siteOfCell_siteOfCoords]
  funext k
  simp [TorusFields.siteOfInt]
private theorem siteOfCell_reflect (L t : ℕ) (x : (TorusFields.torusFrame L t m).Cell) (i : Fin 4) :
    TorusFrame.siteOfCell (-x - BlockAverages.unitStep (TorusFields.torusFrame L t m).top i) =
      -TorusFrame.siteOfCell x - TorusFields.unitStep m i := by
  rw [sub_eq_add_neg, TorusFrame.siteOfCell_add, TorusFrame.siteOfCell_neg, TorusFrame.siteOfCell_neg,
    TorusFrame.siteOfCell_unitStep, sub_eq_add_neg]
private theorem readAtLevel_translate (L t : ℕ) (u : TorusFields.TorusSite m) (W : TorusFields.TorusField m) :
    TorusFields.readAtLevel (TorusFields.torusFrame L t m) (t + 1) (TorusFields.translate u W) =
      shiftField (liftedOffset (TorusFields.torusFrame L t m) (fun i => ((u i).cast : ℤ)) (t + 1))
        (TorusFields.readAtLevel (TorusFields.torusFrame L t m) (t + 1) W) := by
  funext x i
  exact congrArg (fun z => W z i) (siteOfCell_add_liftedOffset L t u x).symm
private theorem readAtLevel_reflect (L t : ℕ) (W : TorusFields.TorusField m) :
    TorusFields.readAtLevel (TorusFields.torusFrame L t m) (t + 1) (reflectTorusField W) =
      reflectField (TorusFields.readAtLevel (TorusFields.torusFrame L t m) (t + 1) W) := by
  funext x i
  exact congrArg (fun z => (W z i)⁻¹) (siteOfCell_reflect L t x i).symm
private theorem mem_plaquettesIn_univ (p : TorusFields.TorusPlaquette m) :
    p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite m)) ↔ p.2.1 < p.2.2 := by
  unfold TorusFields.plaquettesIn
  simp
private theorem wilsonAction_translate (u : TorusFields.TorusSite m) (W : TorusFields.TorusField m) :
    TorusFields.wilsonAction Finset.univ (TorusFields.translate u W) = TorusFields.wilsonAction Finset.univ W := by apply _root_.YangMills.SharedProofs.p7329 <;> assumption
private theorem wilsonAction_reflect (W : TorusFields.TorusField m) :
    TorusFields.wilsonAction Finset.univ (reflectTorusField W) = TorusFields.wilsonAction Finset.univ W := by
  unfold TorusFields.wilsonAction
  refine Finset.sum_nbij' (fun p => (-p.1 - TorusFields.unitStep m p.2.1 - TorusFields.unitStep m p.2.2, p.2))
    (fun p => (-p.1 - TorusFields.unitStep m p.2.1 - TorusFields.unitStep m p.2.2, p.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    exact (mem_plaquettesIn_univ _).2 ((mem_plaquettesIn_univ p).1 hp)
  · intro p hp
    exact (mem_plaquettesIn_univ _).2 ((mem_plaquettesIn_univ p).1 hp)
  · rintro ⟨x, μ, ν⟩ _
    simp only [Prod.mk.injEq, and_true]
    abel
  · rintro ⟨x, μ, ν⟩ _
    simp only [Prod.mk.injEq, and_true]
    abel
  · rintro ⟨x, μ, ν⟩ _
    simp only [TorusFields.plaquetteEnergy, TorusFields.holonomy, reflectTorusField]
    have b1 : -x - TorusFields.unitStep m μ =
        (-x - TorusFields.unitStep m μ - TorusFields.unitStep m ν) + TorusFields.unitStep m ν := by abel
    have b2 : -(x + TorusFields.unitStep m μ) - TorusFields.unitStep m ν =
        -x - TorusFields.unitStep m μ - TorusFields.unitStep m ν := by abel
    have b3 : -(x + TorusFields.unitStep m ν) - TorusFields.unitStep m μ =
        -x - TorusFields.unitStep m μ - TorusFields.unitStep m ν := by abel
    have b4 : -x - TorusFields.unitStep m ν =
        (-x - TorusFields.unitStep m μ - TorusFields.unitStep m ν) + TorusFields.unitStep m μ := by abel
    simp only [b2, b3, inv_inv]
    rw [← b1, ← b4]
    have key : ∀ P Q : BlockAverages.UnitQuaternion,
        ((P * Q : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re = ((Q * P : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re :=
      fun P Q => re_mul_comm (P : ℍ[ℝ]) Q
    have := key ((W (-x - TorusFields.unitStep m μ) μ)⁻¹ *
        (W (-x - TorusFields.unitStep m μ - TorusFields.unitStep m ν) ν)⁻¹)
      (W (-x - TorusFields.unitStep m μ - TorusFields.unitStep m ν) μ * W (-x - TorusFields.unitStep m ν) ν)
    congr 1
    simpa only [mul_assoc] using this
private theorem actionAtLevel_translate (hL : Odd L') (a : ℝ) (k : ℕ) (u : TorusFields.TorusSite m)
    (W : TorusFields.TorusField m) :
    TorusFields.actionAtLevel a L' k Finset.univ (TorusFields.translate u W) =
      TorusFields.actionAtLevel a L' k Finset.univ W := by
  cases k with
  | zero => exact wilsonAction_translate u W
  | succ t =>
    have hs : ∀ i, 0 < (TorusFields.torusFrame L' t m).extent i := fun _ => Nat.pos_of_ne_zero (NeZero.ne m)
    rw [actionAtLevel_univ, actionAtLevel_univ, readAtLevel_translate]
    exact minimalAction_shiftField hL hs a _ (t + 1) le_rfl _
private theorem actionAtLevel_reflect (hL : Odd L') (a : ℝ) (k : ℕ) (W : TorusFields.TorusField m) :
    TorusFields.actionAtLevel a L' k Finset.univ (reflectTorusField W) =
      TorusFields.actionAtLevel a L' k Finset.univ W := by
  cases k with
  | zero => exact wilsonAction_reflect W
  | succ t =>
    have hs : ∀ i, 0 < (TorusFields.torusFrame L' t m).extent i := fun _ => Nat.pos_of_ne_zero (NeZero.ne m)
    rw [actionAtLevel_univ, actionAtLevel_univ, readAtLevel_reflect]
    exact minimalAction_reflectField hL hs a (t + 1) le_rfl _
private theorem translate_perturb {k : ℕ} (c : Fin k → TorusFields.TorusBond m)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (σ : Fin k → ℝ) (u : TorusFields.TorusSite m) :
    TorusFields.translate u (TorusFields.perturb (fun l => ((c l).1 + u, (c l).2)) X σ (TorusFields.trivialField m)) =
      TorusFields.perturb c X σ (TorusFields.trivialField m) := by
  funext x i
  simp only [TorusFields.translate, TorusFields.perturb, TorusFields.trivialField, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  have : (((c l).1 + u, (c l).2) = (x + u, i)) ↔ c l = (x, i) := by
    obtain ⟨z, d⟩ := c l
    simp
  simp only [this]
private theorem reflect_perturb {k : ℕ} (c : Fin k → TorusFields.TorusBond m)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (σ : Fin k → ℝ) :
    reflectTorusField (TorusFields.perturb c X σ (TorusFields.trivialField m)) =
      TorusFields.perturb (fun l => reflectBond (c l)) X (-σ) (TorusFields.trivialField m) := by
  funext x i
  simp only [reflectTorusField, TorusFields.perturb, TorusFields.trivialField, mul_one]
  rw [← ColdStepAtMirrorFrames.SmallUnits.expUnit_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : c l = (-x - TorusFields.unitStep m i, i) ↔ reflectBond (c l) = (x, i) := by
    obtain ⟨z, d⟩ := c l
    simp only [reflectBond, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      refine ⟨?_, rfl⟩
      abel
    · rintro ⟨rfl, rfl⟩
      refine ⟨?_, rfl⟩
      abel
  by_cases h : c l = (-x - TorusFields.unitStep m i, i)
  · rw [if_pos h, if_pos (this.1 h)]
    apply Subtype.ext
    show -(σ l • (X l : ℍ[ℝ])) = (-σ l) • (X l : ℍ[ℝ])
    rw [neg_smul]
  · have h' : ¬ reflectBond (c l) = (x, i) := fun h' => h (this.2 h')
    rw [if_neg h, if_neg h']
    simp
private theorem iteratedFDeriv_two_comp_neg (G : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → Fin 2 → ℝ) :
    iteratedFDeriv ℝ 2 (fun σ => G (-σ)) 0 v = iteratedFDeriv ℝ 2 G 0 v := by
  let E : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) := ContinuousLinearEquiv.neg ℝ
  have e3 : (fun σ => G (-σ)) = G ∘ E := rfl
  have key : iteratedFDeriv ℝ 2 (G ∘ E) 0 =
      (iteratedFDeriv ℝ 2 G (E 0)).compContinuousLinearMap fun _ => E := by
    have h := E.iteratedFDerivWithin_comp_right G uniqueDiffOn_univ (Set.mem_univ (E 0)) 2
    simpa [iteratedFDerivWithin_univ, Set.preimage_univ] using h
  have hE0 : E 0 = 0 := map_zero E
  rw [e3, key, hE0, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simp [E]
private theorem maxwellKernel_translate (hL : Odd L') (a : ℝ) (k : ℕ) (u : TorusFields.TorusSite m)
    (b b' : TorusFields.TorusBond m) :
    WeightedResponses.maxwellKernel a L' k (b.1 + u, b.2) (b'.1 + u, b'.2) =
      WeightedResponses.maxwellKernel a L' k b b' := by
  unfold WeightedResponses.maxwellKernel TorusFields.mixedDeriv
  congr 1
  congr 1
  funext σ
  rw [← actionAtLevel_translate hL a k u
    (TorusFields.perturb ![(b.1 + u, b.2), (b'.1 + u, b'.2)] _ σ (TorusFields.trivialField m))]
  congr 1
  have := translate_perturb ![b, b'] ![WeightedResponses.unitGenerator, WeightedResponses.unitGenerator] σ u
  rw [← this]
  congr 2
  funext l
  fin_cases l <;> rfl
private theorem maxwellKernel_reflect (hL : Odd L') (a : ℝ) (k : ℕ) (b b' : TorusFields.TorusBond m) :
    WeightedResponses.maxwellKernel a L' k (reflectBond b) (reflectBond b') =
      WeightedResponses.maxwellKernel a L' k b b' := by
  unfold WeightedResponses.maxwellKernel TorusFields.mixedDeriv
  have e : (fun σ : Fin 2 → ℝ => TorusFields.actionAtLevel a L' k Finset.univ
      (TorusFields.perturb ![b, b'] ![WeightedResponses.unitGenerator, WeightedResponses.unitGenerator] σ
        (TorusFields.trivialField m))) =
      fun σ => (fun τ : Fin 2 → ℝ => TorusFields.actionAtLevel a L' k Finset.univ
        (TorusFields.perturb ![reflectBond b, reflectBond b']
          ![WeightedResponses.unitGenerator, WeightedResponses.unitGenerator] τ (TorusFields.trivialField m))) (-σ) := by
    funext σ
    rw [← actionAtLevel_reflect hL a k (TorusFields.perturb ![b, b'] _ σ (TorusFields.trivialField m)),
      reflect_perturb]
    congr 2
    funext l
    fin_cases l <;> rfl
  rw [e]
  exact (iteratedFDeriv_two_comp_neg (fun τ : Fin 2 → ℝ => TorusFields.actionAtLevel a L' k Finset.univ
    (TorusFields.perturb ![reflectBond b, reflectBond b']
      ![WeightedResponses.unitGenerator, WeightedResponses.unitGenerator] τ (TorusFields.trivialField m))) _).symm
end Torus
section Symmetry
private theorem mixedDeriv_swap {n : ℕ} (G : TorusFields.TorusField n → ℝ) (W : TorusFields.TorusField n)
    (hG : TorusFields.ContDiffThreeAt G W) (b b' : TorusFields.TorusBond n)
    (X X' : BlockAverages.imaginaryQuaternions) :
    TorusFields.mixedDeriv G W ![b, b'] ![X, X'] = TorusFields.mixedDeriv G W ![b', b] ![X', X] := by apply _root_.YangMills.Construction.AbelianSecondOrder.mixedDeriv_swap <;> assumption
private theorem maxwellKernel_symm (hW : WilsonDerivatives.BoundedDerivativesOfWilsonAction) {a : ℝ} {L : ℕ}
    {c : ColdStepAtMirrorFrames.ColdChainParameters} (hc : c.Admissible a L) (u n : ℕ) [NeZero n] (hn : 64 ≤ n)
    (b b' : TorusFields.TorusBond n) :
    WeightedResponses.maxwellKernel a L u b b' = WeightedResponses.maxwellKernel a L u b' b := by
  obtain ⟨C, -, hW⟩ := hW
  have hC : TorusFields.ContDiffThreeAt (TorusFields.actionAtLevel a L u Finset.univ) (TorusFields.trivialField n) := by
    cases u with
    | zero => exact (hW n (TorusFields.trivialField n)).1
    | succ t =>
      have hp : ∀ i, (TorusFields.torusFrame L t n).period (TorusFields.torusFrame L t n).top i = n :=
        fun i => TopLevelSites.period_top i
      have hcold : ColdStepAtMirrorFrames.IsSmallCurvature c.σA
          (ColdStepAtMirrorFrames.uniformField (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top) := by
        intro p _
        have h0 : 0 < c.σA := hc.positivity.2.2.2.1
        simpa [BlockAverages.plaquetteDefect, BlockAverages.plaquetteHolonomy, BlockAverages.pathHolonomy,
          BlockAverages.linkValue, ColdStepAtMirrorFrames.uniformField] using h0
      have hcl := hc.estimates (TorusFields.torusFrame L t n) c.σA _ ⟨rfl, n, hn, fun _ => rfl⟩
        hc.positivity.2.2.2.1 le_rfl hcold
      have han := hcl.cellShares.1
      have hsame : TorusFields.cellsOfSites (TorusFields.torusFrame L t n) (Finset.univ : Finset (TorusFields.TorusSite n)) =
          ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n) :=
        TopLevelSites.cellsOfSites_univ fun _ => rfl
      have := TorusChain.contDiffThreeAt_of_isBondAnalyticAt (W := TorusFields.trivialField n) hp han
      show TorusFields.ContDiffThreeAt (fun W => BlockAverages.minimalAction a
        (TorusFields.cellsOfSites (TorusFields.torusFrame L t n) Finset.univ) (t + 1)
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (t + 1) W)) (TorusFields.trivialField n)
      rw [hsame]
      exact this
  exact mixedDeriv_swap _ _ hC b b' _ _
end Symmetry
end MaxwellKernel
open MaxwellKernel in
theorem maxwellKernelBounds_holds (hE : WeightedResponses.MaxwellKernelDecayAndLocality)
    (hW : WilsonDerivatives.BoundedDerivativesOfWilsonAction) : maxwellKernelBoundsStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ T _ _ hD hCS _ _ _
  obtain ⟨c, nss, hTie, -⟩ := hCS
  have hc : c.Admissible T.coupling T.side := hTie.2.2.2.2.2.2.2
  obtain ⟨C, μ, hC, hμ, hent⟩ := hE T.coupling T.side c hc
  refine ⟨0, fun y _ _ _ => ?_⟩
  refine ⟨C, μ / 4, by positivity, ?_⟩
  intro k N _ hN
  have hN64 : 64 ≤ N := by
    have := hD.n₀_ge
    omega
  refine ⟨fun b b' => maxwellKernel_symm hW hc k N hN64 b b',
    fun u b b' => maxwellKernel_translate hD.L_odd T.coupling k u b b',
    fun b b' => maxwellKernel_reflect hD.L_odd T.coupling k b b', ?_, ?_⟩
  · intro b b'
    refine ((hent k N N hN64 hN64).1 b b').trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
    have h0 : (0 : ℝ) ≤ (TorusFields.supDist b.1 b'.1 : ℝ) := Nat.cast_nonneg _
    nlinarith
  · intro m _ hNm μ' ν w hw
    have hm64 : 64 ≤ m := le_trans hN64 hNm
    have hz : TorusFields.BondOffsetInBox 1 ((0 : Fin 4 → ℤ), μ') := by
      refine ⟨fun i => by simp, fun i => ?_⟩
      by_cases h : i = μ'
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    have hbox : TorusFields.BondOffsetInBox (N / 2 - 8) (w, ν) := by
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := hw i
        show |w i| ≤ _
        omega
      · have := hw i
        have h1 := abs_le.mp (le_refl |w i|)
        show |(w + Pi.single ν 1 : Fin 4 → ℤ) i| ≤ _
        rw [abs_le]
        by_cases h : i = ν
        · subst h
          simp only [Pi.add_apply, Pi.single_eq_same]
          omega
        · simp only [Pi.add_apply, Pi.single_eq_of_ne h]
          omega
    have hcmp := (hent k N m hN64 hm64).2 0 0 1 (N / 2 - 8) ((0 : Fin 4 → ℤ), μ') (w, ν)
      (by omega) (by omega) (by omega) hz hbox
    have hz0 : ∀ (q : ℕ), (TorusFields.siteOfInt (0 : Fin 4 → ℤ) : TorusFields.TorusSite q) = 0 := fun q => by
      funext i
      simp [TorusFields.siteOfInt]
    have e1 : TorusLumps.bondFrom (0 : TorusFields.TorusSite N) ((0 : Fin 4 → ℤ), μ') =
        ((0 : TorusFields.TorusSite N), μ') := by
      simp [TorusLumps.bondFrom, hz0]
    have e2 : TorusLumps.bondFrom (0 : TorusFields.TorusSite m) ((0 : Fin 4 → ℤ), μ') =
        ((0 : TorusFields.TorusSite m), μ') := by
      simp [TorusLumps.bondFrom, hz0]
    have e3 : TorusLumps.bondFrom (0 : TorusFields.TorusSite N) (w, ν) = (TorusFields.siteOfInt w, ν) := by
      simp [TorusLumps.bondFrom]
    have e4 : TorusLumps.bondFrom (0 : TorusFields.TorusSite m) (w, ν) = (TorusFields.siteOfInt w, ν) := by
      simp [TorusLumps.bondFrom]
    rw [e1, e2, e3, e4] at hcmp
    refine hcmp.trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
    have hr : N + 4 ≤ 4 * (N / 2 - 8) := by omega
    have hr' : (N : ℝ) + 4 ≤ 4 * ((N / 2 - 8 : ℕ) : ℝ) := by exact_mod_cast hr
    push_cast
    nlinarith
end YangMills.Construction.ResponseInTheExpansion
end

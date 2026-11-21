import YangMills.Construction.ClusterExpansionOfAStep.LumpsAreFibres
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ClusterExpansionOfAStep.TheImageIsGaugeInvariant
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open BlockAverages hiding gaugeTransform unitStep
open LumpContours
open TorusFields hiding gaugeTransform unitStep
section Haar
theorem haarUnit_isMulRightInvariant : haarUnit.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  let ν : Measure UnitQuaternion := Measure.map (· * g) haarUnit
  have hmeas : Measurable fun h : UnitQuaternion => h * g := (continuous_mul_right g).measurable
  have hprob : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have hleft : ν.IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    have hm2 : Measurable fun u : UnitQuaternion => h * u := (continuous_mul_left h).measurable
    show Measure.map (h * ·) (Measure.map (· * g) haarUnit) = Measure.map (· * g) haarUnit
    rw [Measure.map_map hm2 hmeas]
    have : (fun u : UnitQuaternion => h * u) ∘ (fun u => u * g) = (fun u => u * g) ∘ (fun u => h * u) := by
      funext u
      simp [mul_assoc]
    rw [this, ← Measure.map_map hmeas hm2, map_mul_left_eq_self]
  have h1 := Measure.haarMeasure_unique ν ⊤
  have h2 : ν (⊤ : TopologicalSpace.PositiveCompacts UnitQuaternion) = 1 := by
    simpa using measure_univ (μ := ν)
  rw [h2, one_smul] at h1
  exact h1
end Haar
section Paths
variable {F : BlockFrame} {j : ℕ}
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem linkValue_gaugeTransform (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j) (x : F.Site j)
    (st : PathStep) :
    linkValue (BlockAverages.gaugeTransform γ X) x st =
      γ x * linkValue X x st * (γ (x + stepDisplacement j st))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_gaugeTransform <;> assumption
theorem pathHolonomy_gaugeTransform (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (l : List PathStep) (x : F.Site j) :
    pathHolonomy (BlockAverages.gaugeTransform γ X) x l =
      γ x * pathHolonomy X x l * (γ (x + pathDisplacement j l))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_gaugeTransform <;> assumption
theorem pathDisplacement_append (l l' : List PathStep) :
    (pathDisplacement j (l ++ l') : F.Site j) = pathDisplacement j l + pathDisplacement j l' := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem pathDisplacement_replicate (m : ℕ) (st : PathStep) :
    (pathDisplacement j (List.replicate m st) : F.Site j) = m • stepDisplacement j st := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_replicate <;> assumption
theorem pathDisplacement_reversePath (l : List PathStep) :
    (pathDisplacement j (reversePath l) : F.Site j) = - pathDisplacement j l := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_reversePath <;> assumption
theorem pathDisplacement_axisPath (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    (pathDisplacement j (axisPath h π) : F.Site j) = siteOfCoords j h := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_axisPath <;> assumption
theorem siteOfCoords_minimalOffset [∀ i, NeZero (F.period j i)] (x x' : F.Site j) :
    (siteOfCoords j (minimalOffset x x') : F.Site j) = x' - x := by
  funext i
  simp [siteOfCoords, minimalOffset]
end Paths
section Curvature
variable {F : BlockFrame} {j : ℕ}
theorem plaquetteDefect_gaugeTransform (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteDefect (BlockAverages.gaugeTransform γ X) p = plaquetteDefect X p := by apply _root_.YangMills.Construction.GaugeFixing.plaquetteDefect_gaugeTransform <;> assumption
theorem hotLumps_gaugeTransform {L : ℕ} (g : LumpGrid L) (s : ℝ) (X : Finset (F.Site j))
    (γ : F.Site j → UnitQuaternion) (W : F.GaugeField j) :
    hotLumps g s X (BlockAverages.gaugeTransform γ W) = hotLumps g s X W := by
  classical
  unfold hotLumps
  simp only [plaquetteDefect_gaugeTransform]
end Curvature
section Step
variable {F : BlockFrame}
theorem top_sub_depth : F.top - F.depth = 1 := by apply _root_.YangMills.Construction.GaugeFixing.top_sub_depth <;> assumption
theorem period_depth (i : Fin 4) : F.period F.depth i = F.period F.top i * F.blockSide := by
  simp [BlockFrame.period, BlockFrame.top]
theorem cellCentre_add_unitStep (c : F.Cell) (i : Fin 4) :
    (cellCentre F.depth (c + BlockAverages.unitStep F.top i) : F.Site F.depth) =
      cellCentre F.depth c + F.blockSide • BlockAverages.unitStep F.depth i := by
  funext k
  simp only [cellCentre, BlockAverages.unitStep, siteOfCoords, top_sub_depth, pow_one, Pi.add_apply,
    Pi.smul_apply]
  have hc : ((siteCoords (c + siteOfCoords F.top (Pi.single i 1)) k : ℤ) : ZMod (F.period F.top k)) =
      ((siteCoords c k + (Pi.single i 1 : Fin 4 → ℤ) k : ℤ) : ZMod (F.period F.top k)) := by
    simp only [siteCoords, ZMod.intCast_zmod_cast, Int.cast_add, Pi.add_apply, siteOfCoords]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hc
  obtain ⟨q, hq⟩ := hc
  have hk : (F.blockSide : ℤ) * siteCoords (c + siteOfCoords F.top (Pi.single i 1)) k =
      ((F.blockSide : ℤ) * siteCoords c k + F.blockSide * (Pi.single i 1 : Fin 4 → ℤ) k) -
        (F.period F.depth k : ℤ) * q := by
    rw [period_depth]
    push_cast
    have : siteCoords (c + siteOfCoords F.top (Pi.single i 1)) k =
        siteCoords c k + (Pi.single i 1 : Fin 4 → ℤ) k - (F.period F.top k : ℤ) * q := by linarith
    rw [this]
    ring
  rw [hk]
  simp [nsmul_eq_mul]
theorem contourPath_displacement [∀ i, NeZero (F.period F.depth i)] (b : F.Cell → F.Site F.depth)
    (c : F.Cell × Fin 4) (ξ : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    b c.1 + pathDisplacement F.depth (contourPath b c ξ π) = b (c.1 + BlockAverages.unitStep F.top c.2) := by
  have h1 := cellCentre_add_unitStep (F := F) c.1 c.2
  unfold contourPath
  rw [pathDisplacement_append, pathDisplacement_append, pathDisplacement_replicate,
    pathDisplacement_reversePath, pathDisplacement_axisPath, pathDisplacement_axisPath,
    siteOfCoords_minimalOffset, siteOfCoords_minimalOffset, h1]
  simp only [stepDisplacement, if_true]
  abel
theorem contourMean_gaugeTransform [∀ i, NeZero (F.period F.depth i)] (J₀ : ℕ)
    (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth)
    (γ : F.Site F.depth → UnitQuaternion) (W : F.GaugeField F.depth) (c : F.Cell × Fin 4) :
    contourMean J₀ h b (BlockAverages.gaugeTransform γ W) c =
      ((γ (b c.1) : UnitQuaternion) : ℍ[ℝ]) * contourMean J₀ h b W c *
        (((γ (b (c.1 + BlockAverages.unitStep F.top c.2)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  unfold contourMean
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [pathHolonomy_gaugeTransform, contourPath_displacement, Submonoid.coe_mul, Submonoid.coe_mul]
end Step
section Blocks
variable {L n : ℕ} [NeZero L] [NeZero n]
theorem parentCoord_of_small_offset (hodd : Odd L) (c h : ℤ) (hh : |h| ≤ ((L : ℤ) - 1) / 2) :
    ((((((c * L + h : ℤ) : ZMod (n * L)).cast : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ) : ZMod n) =
      (c : ZMod n) := by
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [ZMod.coe_intCast]
  set N : ℤ := ((n * L : ℕ) : ℤ) with hN
  have h1 := Int.emod_add_mul_ediv (c * L + h) N
  set q := (c * L + h) / N
  obtain ⟨k, hk⟩ := hodd
  have hhalf : ((L : ℤ) - 1) / 2 = k := by
    rw [hk]
    push_cast
    omega
  rw [hhalf] at hh ⊢
  rw [abs_le] at hh
  have hLk : (L : ℤ) = 2 * k + 1 := by rw [hk]; push_cast; ring
  have e : (c * L + h) % N + k = (h + k) + (L : ℤ) * (c - (n : ℤ) * q) := by
    have : N = (n : ℤ) * L := by rw [hN]; push_cast; ring
    rw [this] at h1
    rw [this] at *
    nlinarith
  rw [e, Int.add_mul_ediv_left _ _ hLpos.ne', Int.ediv_eq_zero_of_lt (by omega) (by omega)]
  simp
end Blocks
section EvaluationMaps
theorem zmod_cast_add_of_eq {m k : ℕ} (hm : m = k) [NeZero m] (a b : ZMod m) :
    (((a + b : ZMod m).cast : ℤ) : ZMod k) = ((a.cast : ℤ) : ZMod k) + ((b.cast : ℤ) : ZMod k) := by apply _root_.YangMills.Construction.TorusLumps.castInt_add <;> assumption
theorem zmod_cast_intCast_of_eq {m k : ℕ} (hm : m = k) [NeZero m] (z : ℤ) :
    ((((z : ZMod m)).cast : ℤ) : ZMod k) = (z : ZMod k) := by apply _root_.YangMills.Construction.TorusLumps.castInt_intCast <;> assumption
variable {F : BlockFrame} {j m : ℕ}
theorem toTorusSite_add_of_period (hper : ∀ i, F.period j i = m) [∀ i, NeZero (F.period j i)]
    (x y : F.Site j) : toTorusSite m (x + y) = toTorusSite m x + toTorusSite m y := by
  funext k
  exact zmod_cast_add_of_eq (hper k) (x k) (y k)
theorem toTorusSite_siteOfCoords_of_period (hper : ∀ i, F.period j i = m) [∀ i, NeZero (F.period j i)]
    (h : Fin 4 → ℤ) : toTorusSite m (siteOfCoords j h : F.Site j) = siteOfInt h := by
  funext k
  exact zmod_cast_intCast_of_eq (hper k) (h k)
theorem toTorusSite_unitStep_of_period [NeZero m] (hper : ∀ i, F.period j i = m)
    [∀ i, NeZero (F.period j i)] (i : Fin 4) :
    toTorusSite m (BlockAverages.unitStep j i : F.Site j) = TorusFields.unitStep m i := by
  unfold BlockAverages.unitStep
  rw [toTorusSite_siteOfCoords_of_period hper]
  funext k
  by_cases hk : k = i
  · subst hk
    simp [siteOfInt, TorusFields.unitStep]
  · simp [siteOfInt, TorusFields.unitStep, hk]
theorem readAtLevel_gaugeTransform [NeZero m] (hper : ∀ i, F.period j i = m) [∀ i, NeZero (F.period j i)]
    (γ : TorusSite m → UnitQuaternion) (W : TorusField m) :
    readAtLevel F j (TorusFields.gaugeTransform γ W) =
      BlockAverages.gaugeTransform (fun x => γ (toTorusSite m x)) (readAtLevel F j W) := by
  funext x i
  show γ (toTorusSite m x) * W (toTorusSite m x) i * (γ (toTorusSite m x + TorusFields.unitStep m i))⁻¹ =
    γ (toTorusSite m x) * W (toTorusSite m x) i * (γ (toTorusSite m (x + BlockAverages.unitStep j i)))⁻¹
  rw [toTorusSite_add_of_period hper, toTorusSite_unitStep_of_period hper]
end EvaluationMaps
section Kernel
variable (ℓ : StepParameters) (x : ℝ) {n : ℕ} [NeZero n]
theorem stepBlockFrame_period_zero (i : Fin 4) : (stepBlockFrame ℓ.side n).period 0 i = n * ℓ.side := by
  simp [BlockFrame.period, stepBlockFrame, BlockFrame.top]
theorem stepBlockFrame_period_one (i : Fin 4) : (stepBlockFrame ℓ.side n).period 1 i = n := by
  simp [BlockFrame.period, stepBlockFrame, BlockFrame.top]
def bondKernelWithLumps
    (H : Finset (Finset ((stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth)))
    (W : (stepBlockFrame ℓ.side n).GaugeField 0) (V : (stepBlockFrame ℓ.side n).GaugeField 1)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) : ℝ :=
  Real.exp (ℓ.coupling * x * (contourMean ℓ.baseDepth H b W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).re) /
    partitionFn (ℓ.coupling * x * ‖contourMean ℓ.baseDepth H b W c‖)
theorem exp_re_div_partitionFn_conj (t : ℝ) (Q Q' : ℍ[ℝ]) (A B v v' : UnitQuaternion)
    (hQ : Q' = ((A : UnitQuaternion) : ℍ[ℝ]) * Q * ((B⁻¹ : UnitQuaternion) : ℍ[ℝ]))
    (hv : v' = A * v * B⁻¹) :
    Real.exp (t * (Q' * ((v'⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) / partitionFn (t * ‖Q'‖) =
      Real.exp (t * (Q * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) / partitionFn (t * ‖Q‖) := by
  have hre : ∀ a z : ℍ[ℝ], (a * z).re = (z * a).re := by
    intro a z
    simp only [Quaternion.re_mul]
    ring
  have hBB : ((B⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((B : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    rfl
  have hAA : ((A⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((A : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    rfl
  have h1 : (Q' * ((v'⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = (Q * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by
    have e : (v'⁻¹ : UnitQuaternion) = B * v⁻¹ * A⁻¹ := by
      rw [hv]
      group
    rw [e, hQ, Submonoid.coe_mul, Submonoid.coe_mul]
    have e2 : ((A : UnitQuaternion) : ℍ[ℝ]) * Q * ((B⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        (((B : UnitQuaternion) : ℍ[ℝ]) * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((A⁻¹ : UnitQuaternion) : ℍ[ℝ])) =
        ((A : UnitQuaternion) : ℍ[ℝ]) *
          (Q * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((A⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
      calc _ = ((A : UnitQuaternion) : ℍ[ℝ]) * Q *
            (((B⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((B : UnitQuaternion) : ℍ[ℝ])) *
            (((v⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((A⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by simp only [mul_assoc]
        _ = _ := by rw [hBB]; simp only [mul_one, mul_assoc]
    rw [e2, hre, mul_assoc, hAA, mul_one]
  have h2 : ‖Q'‖ = ‖Q‖ := by
    rw [hQ, norm_mul, norm_mul, norm_unitQuaternion, norm_unitQuaternion, one_mul, mul_one]
  rw [h1, h2]
theorem bondKernel_gaugeTransform (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (V : (stepBlockFrame ℓ.side n).GaugeField 1)
    (γ : (stepBlockFrame ℓ.side n).Site 0 → UnitQuaternion)
    (g₁ : (stepBlockFrame ℓ.side n).Site 1 → UnitQuaternion)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0) (hb : ∀ y, γ (b y) = g₁ y)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) :
    bondKernel ℓ x (BlockAverages.gaugeTransform γ W) (BlockAverages.gaugeTransform g₁ V) b c =
      bondKernel ℓ x W V b c := by
  have hhot : (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0)
      (BlockAverages.gaugeTransform γ W) :
      Finset (Finset ((stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth))) =
      hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W :=
    hotLumps_gaugeTransform _ _ _ _ _
  have hstep : bondKernelWithLumps ℓ x (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0)
      (BlockAverages.gaugeTransform γ W))
      (BlockAverages.gaugeTransform γ W) (BlockAverages.gaugeTransform g₁ V) b c =
      bondKernelWithLumps ℓ x (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W)
      (BlockAverages.gaugeTransform γ W) (BlockAverages.gaugeTransform g₁ V) b c :=
    congrArg (fun H => bondKernelWithLumps ℓ x H (BlockAverages.gaugeTransform γ W)
      (BlockAverages.gaugeTransform g₁ V) b c) hhot
  refine hstep.trans ?_
  have hm := contourMean_gaugeTransform (F := stepBlockFrame ℓ.side n) ℓ.baseDepth
    (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W) b γ W c
  rw [hb c.1, hb (c.1 + BlockAverages.unitStep (stepBlockFrame ℓ.side n).top c.2)] at hm
  exact exp_re_div_partitionFn_conj (ℓ.coupling * x) _ _ (g₁ c.1)
    (g₁ (c.1 + BlockAverages.unitStep (stepBlockFrame ℓ.side n).top c.2)) (V c.1 c.2)
    (BlockAverages.gaugeTransform g₁ V c.1 c.2) hm rfl
theorem baseChoices_gaugeTransform (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (γ : (stepBlockFrame ℓ.side n).Site 0 → UnitQuaternion) :
    baseChoices ℓ (BlockAverages.gaugeTransform γ W) = baseChoices ℓ W := by
  have hhot : (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0)
      (BlockAverages.gaugeTransform γ W) :
      Finset (Finset ((stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth))) =
      hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W :=
    hotLumps_gaugeTransform _ _ _ _ _
  classical
  have hgen : ∀ H H' : Finset (Finset ((stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth)),
      H = H' → (Finset.univ.filter fun b => IsBaseChoice ℓ.baseDepth H b) =
        Finset.univ.filter fun b => IsBaseChoice ℓ.baseDepth H' b := by
    intro H H' h
    rw [h]
  exact hgen _ _ hhot
theorem parentBlock_base (hfit : ℓ.Admissible) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0) (hb : b ∈ baseChoices ℓ W)
    (y : (stepBlockFrame ℓ.side n).Cell) :
    parentBlock ℓ.side (toTorusSite (n * ℓ.side) (b y)) = toTorusSite n y := by
  classical
  have hB := (Finset.mem_filter.mp hb).2 y
  have hrep : ∃ h : Fin 4 → ℤ, (∀ i, |h i| ≤ ((ℓ.side : ℤ) - 1) / 2) ∧
      b y = siteOfCoords 0 fun k => siteCoords y k * ℓ.side + h k := by
    by_cases hc : nearbyLumps (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W) y = ∅ ∨
        IsCrowded ℓ.baseDepth (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W) y
    · refine ⟨0, fun i => ?_, ?_⟩
      · have := hfit.L_ge
        simp only [Pi.zero_apply, abs_zero]
        omega
      · rw [hB.1 hc]
        funext k
        simp [cellCentre, siteOfCoords, mul_comm, stepBlockFrame, BlockFrame.top]
        rfl
    · obtain ⟨h, hh, he⟩ := Finset.mem_image.mp (hB.2 hc).1
      refine ⟨h, fun i => ?_, ?_⟩
      · have h1 := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hh i)
        have e1 : (stepBlockFrame ℓ.side n).blockSide ^
            ((stepBlockFrame ℓ.side n).top - (stepBlockFrame ℓ.side n).depth) = ℓ.side := by
          show ℓ.side ^ 1 = _
          simp
        rw [e1] at h1
        exact abs_le.mpr h1
      · rw [← he]
        funext k
        have e2 : ((stepBlockFrame ℓ.side n).blockSide : ℤ) ^
            ((stepBlockFrame ℓ.side n).top - (stepBlockFrame ℓ.side n).depth) = (ℓ.side : ℤ) := by
          show (ℓ.side : ℤ) ^ 1 = _
          simp
        simp only [e2, mul_comm]
        rfl
  obtain ⟨h, hh, he⟩ := hrep
  rw [he, toTorusSite_siteOfCoords_of_period (stepBlockFrame_period_zero ℓ)]
  funext k
  exact parentCoord_of_small_offset (n := n) hfit.L_odd (siteCoords y k) (h k) (hh k)
theorem averagedKernel_gaugeTransform (hfit : ℓ.Admissible) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (V : (stepBlockFrame ℓ.side n).GaugeField 1) (g : TorusSite n → UnitQuaternion)
    (γ : (stepBlockFrame ℓ.side n).Site 0 → UnitQuaternion)
    (hγ : ∀ z, γ z = g (parentBlock ℓ.side (toTorusSite (n * ℓ.side) z))) :
    averagedKernel ℓ x (BlockAverages.gaugeTransform γ W)
      (BlockAverages.gaugeTransform (fun y => g (toTorusSite n y)) V) = averagedKernel ℓ x W V := by
  show (1 / ((baseChoices ℓ (BlockAverages.gaugeTransform γ W)).card : ℝ)) *
      ∑ b ∈ baseChoices ℓ (BlockAverages.gaugeTransform γ W),
      ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
        bondKernel ℓ x (BlockAverages.gaugeTransform γ W)
          (BlockAverages.gaugeTransform (fun y => g (toTorusSite n y)) V) b c =
    (1 / ((baseChoices ℓ W).card : ℝ)) * ∑ b ∈ baseChoices ℓ W,
      ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4, bondKernel ℓ x W V b c
  rw [baseChoices_gaugeTransform]
  refine congrArg (fun z => (1 / ((baseChoices ℓ W).card : ℝ)) * z)
    (Finset.sum_congr rfl fun b hb => Finset.prod_congr rfl fun c _ => ?_)
  refine bondKernel_gaugeTransform ℓ x W V γ _ b (fun y => ?_) c
  rw [hγ, parentBlock_base ℓ hfit W b hb]
  rfl
end Kernel
section Image
variable {m : ℕ} [NeZero m]
theorem measurePreserving_gaugeTransform (γ : TorusSite m → UnitQuaternion) :
    MeasurePreserving (TorusFields.gaugeTransform γ) (fieldHaar m) (fieldHaar m) := by
  haveI := haarUnit_isMulRightInvariant
  have hone : ∀ A B : UnitQuaternion, MeasurePreserving (fun u : UnitQuaternion => A * u * B)
      haarUnit haarUnit := fun A B =>
    (measurePreserving_mul_right haarUnit B).comp (measurePreserving_mul_left haarUnit A)
  unfold fieldHaar
  exact measurePreserving_pi _ _ fun x =>
    measurePreserving_pi _ _ fun i => hone (γ x) (γ (x + TorusFields.unitStep m i))⁻¹
theorem gaugeTransform_inv_gaugeTransform (γ : TorusSite m → UnitQuaternion) (W : TorusField m) :
    TorusFields.gaugeTransform (fun x => (γ x)⁻¹) (TorusFields.gaugeTransform γ W) = W := by
  funext x i
  simp [TorusFields.gaugeTransform, mul_assoc]
theorem gaugeTransform_gaugeTransform_inv (γ : TorusSite m → UnitQuaternion) (W : TorusField m) :
    TorusFields.gaugeTransform γ (TorusFields.gaugeTransform (fun x => (γ x)⁻¹) W) = W := by
  funext x i
  simp [TorusFields.gaugeTransform, mul_assoc]
theorem continuous_gaugeTransform (γ : TorusSite m → UnitQuaternion) :
    Continuous (TorusFields.gaugeTransform (n := m) γ) := by
  unfold TorusFields.gaugeTransform
  fun_prop
def gaugeMeasurableEquiv (γ : TorusSite m → UnitQuaternion) : TorusField m ≃ᵐ TorusField m where
  toFun := TorusFields.gaugeTransform γ
  invFun := TorusFields.gaugeTransform fun x => (γ x)⁻¹
  left_inv := gaugeTransform_inv_gaugeTransform γ
  right_inv := gaugeTransform_gaugeTransform_inv γ
  measurable_toFun := (continuous_gaugeTransform γ).measurable
  measurable_invFun := (continuous_gaugeTransform _).measurable
end Image
theorem kernelImageGaugeInvariant_holds : KernelImageGaugeInvariant := by
  intro ℓ hfit x D n _ hD g V
  have hn : n ≠ 0 := NeZero.ne n
  let ĝ : TorusSite (n * ℓ.side) → UnitQuaternion := fun z => g (parentBlock ℓ.side z)
  simp only [kernelImage, dif_neg hn]
  have hmp : MeasurePreserving (gaugeMeasurableEquiv ĝ) (fieldHaar (n * ℓ.side)) (fieldHaar (n * ℓ.side)) :=
    measurePreserving_gaugeTransform ĝ
  rw [← hmp.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  show D (n * ℓ.side) (TorusFields.gaugeTransform ĝ W) *
      averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 (TorusFields.gaugeTransform ĝ W))
      (readAtLevel (stepBlockFrame ℓ.side n) 1 (TorusFields.gaugeTransform g V)) =
    D (n * ℓ.side) W * averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
      (readAtLevel (stepBlockFrame ℓ.side n) 1 V)
  rw [hD, readAtLevel_gaugeTransform (stepBlockFrame_period_zero ℓ),
    readAtLevel_gaugeTransform (stepBlockFrame_period_one ℓ)]
  rw [averagedKernel_gaugeTransform ℓ x hfit _ _ g _ fun z => rfl]
end YangMills.Construction.TorusLumps
end

import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.HullsInEveryVolume.ARuleDrawsTheChainProof
import YangMills.Construction.CellOfTheFlow.TheNoiseDrawsTheChainProof
import YangMills.Construction.HullsInEveryVolume.EachTowerHasARuleOfTheNoises
import YangMills.Construction.HullsInEveryVolume.TranslationsCarryTheBasesAtEverySide
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
open scoped unitInterval
namespace YangMills.Construction
open BlockAverages TorusLumps TorusFields StepSettings StepCosts ChainNoise CellWindows LumpContours HullTrees
  WeightedResponses ClusterExpansionOfAStep
namespace ChainNoise
namespace RuleFromSampler
section Frames
variable {F : BlockFrame} [∀ j i, NeZero (F.period j i)]
theorem siteAtOffset_add_siteOfCoords (v : Fin 4 → ℤ) (y : F.Cell) (z : Fin 4 → ℤ) :
    (siteAtOffset (y + siteOfCoords F.top v) z : F.Site F.depth) =
      siteAtOffset y z + siteOfCoords F.depth fun i => (F.blockSide : ℤ) * v i := by
  have h : (y + siteOfCoords F.top v : F.Cell) = siteOfCoords F.top (siteCoords y + v) := by
    rw [TorusContours.siteOfCoords_add, TorusContours.siteOfCoords_siteCoords]
  have e : (fun i => (F.blockSide : ℤ) * (siteCoords y + v) i) =
      (fun i => (F.blockSide : ℤ) * siteCoords y i) + fun i => (F.blockSide : ℤ) * v i := by
    funext k
    simp [mul_add]
  unfold siteAtOffset
  rw [h, TorusContours.cellCentre_siteOfCoords, TorusContours.cellCentre_eq, e, TorusContours.siteOfCoords_add]
  abel
end Frames
section Sites
variable (ℓ : StepParameters) {n : ℕ} [NeZero n]
def offsetFromCentre (L : ℕ) (o : BlockOffset L) : Fin 4 → ℤ := fun i => ((o i : ℕ) : ℤ) - ((L : ℤ) - 1) / 2
def torusSiteCoords (y : TorusSite n) : Fin 4 → ℤ := fun i => ((y i).cast : ℤ)
theorem offsetFromCentre_injective (L : ℕ) : Function.Injective (offsetFromCentre L) := by apply _root_.YangMills.Construction.ChainNoise.centredOffset_injective <;> assumption
theorem offsetFromCentre_mem_centredCube {L : ℕ} (hodd : Odd L) (o : BlockOffset L) :
    offsetFromCentre L o ∈ centredCube L := by apply _root_.YangMills.Construction.ChainNoise.centredOffset_mem <;> assumption
theorem baseChoice_torusSiteInFrame (o : TorusSite n → BlockOffset ℓ.side) (x : TorusSite n) :
    baseChoiceOfOffsets o (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x) =
      siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x) (offsetFromCentre ℓ.side (o x)) := by apply _root_.YangMills.Construction.ChainNoise.baseChoiceOfOffsets_apply <;> assumption
theorem baseChoice_mem_sitesBelow (hodd : Odd ℓ.side) (o : TorusSite n → BlockOffset ℓ.side) (x : TorusSite n) :
    baseChoiceOfOffsets o (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x) ∈
      sitesBelow 0 (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x) := by
  rw [baseChoice_torusSiteInFrame]
  exact (TorusContours.mem_sitesBelow_iff _ _).mpr ⟨_, offsetFromCentre_mem_centredCube hodd _, rfl⟩
theorem offsetFromCentre_siteOffset (hodd : Odd ℓ.side) (y : (stepBlockFrame ℓ.side n).Cell) {z : Fin 4 → ℤ}
    (hz : z ∈ centredCube ℓ.side) :
    offsetFromCentre ℓ.side (siteOffset (toTorusSite (n * ℓ.side) (siteAtOffset y z : (stepBlockFrame ℓ.side n).Site 0))) = z := by apply _root_.YangMills.Construction.ChainNoise.centredOffset_siteOffset <;> assumption
def recentre (ℓ : StepParameters) {n : ℕ} (y : TorusSite n) (W : TorusField (n * ℓ.side)) : TorusField (n * ℓ.side) :=
  TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * torusSiteCoords y i) W
theorem measurable_recentre (y : TorusSite n) : Measurable (recentre ℓ y) :=
  measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun i =>
    (measurable_pi_apply i).comp (measurable_pi_apply (x + siteOfInt fun i => (ℓ.side : ℤ) * torusSiteCoords y i))
theorem siteOfInt_torusSiteCoords (y : TorusSite n) : (siteOfInt (torusSiteCoords y) : TorusSite n) = y := by apply _root_.YangMills.Construction.BlockOffsets.siteOfInt_cast_self <;> assumption
theorem siteOfInt_scaled_add (y : TorusSite n) (h : Fin 4 → ℤ) :
    (siteOfInt (fun i => (ℓ.side : ℤ) * torusSiteCoords y i) + siteOfInt (fun i => (ℓ.side : ℤ) * h i) :
      TorusSite (n * ℓ.side)) = siteOfInt fun i => (ℓ.side : ℤ) * torusSiteCoords (y + siteOfInt h) i := by
  funext i
  have h1 : ((torusSiteCoords (y + siteOfInt h) i : ℤ) : ZMod n) = ((torusSiteCoords y i + h i : ℤ) : ZMod n) := by
    simp [torusSiteCoords, siteOfInt]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  obtain ⟨q, hq⟩ := h1
  simp only [siteOfInt, Pi.add_apply]
  rw [← Int.cast_add, ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨-q, ?_⟩
  push_cast
  linear_combination (-(ℓ.side : ℤ)) * hq
theorem recentre_translate (y : TorusSite n) (h : Fin 4 → ℤ) (W : TorusField (n * ℓ.side)) :
    recentre ℓ y (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * h i) W) = recentre ℓ (y + siteOfInt h) W := by
  funext x i
  show W (x + siteOfInt (fun i => (ℓ.side : ℤ) * torusSiteCoords y i) + siteOfInt fun i => (ℓ.side : ℤ) * h i) i =
    W (x + siteOfInt fun i => (ℓ.side : ℤ) * torusSiteCoords (y + siteOfInt h) i) i
  rw [add_assoc, siteOfInt_scaled_add]
theorem parentBlock_add_scaled (x : TorusSite (n * ℓ.side)) (e : Fin 4 → ℤ) :
    parentBlock ℓ.side (x + siteOfInt fun i => (ℓ.side : ℤ) * e i) = parentBlock ℓ.side x + siteOfInt e := by
  have hLpos : (0 : ℤ) < ℓ.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
  have h : x + (siteOfInt fun i => (ℓ.side : ℤ) * e i) =
      (siteOfInt fun i => ((x i).cast : ℤ) + (ℓ.side : ℤ) * e i : TorusSite (n * ℓ.side)) := by
    funext k
    simp [siteOfInt]
  rw [h]
  funext k
  rw [TorusBlocks.parentBlock_siteOfInt]
  have h2 : ((x k).cast : ℤ) + (ℓ.side : ℤ) * e k + ((ℓ.side : ℤ) - 1) / 2 =
      (((x k).cast : ℤ) + ((ℓ.side : ℤ) - 1) / 2) + (ℓ.side : ℤ) * e k := by ring
  rw [h2, Int.add_mul_ediv_left _ _ (ne_of_gt hLpos)]
  simp [parentBlock, siteOfInt]
theorem fieldsAgreeOn_recentre (y : TorusSite n) {Q Q' : Finset (TorusSite n)} (hQ : ∀ a ∈ Q, a + y ∈ Q')
    {W W' : TorusField (n * ℓ.side)} (h : AgreeAbove ℓ.side Q' W W') :
    FieldsAgreeOn (sitesInBlocks ℓ.side Q) (recentre ℓ y W) (recentre ℓ y W') := by
  intro b h1 h2
  have hy : (siteOfInt (torusSiteCoords y) : TorusSite n) = y := siteOfInt_torusSiteCoords y
  have m1 : parentBlock ℓ.side b.1 ∈ Q := (Finset.mem_filter.mp h1).2
  have m2 : parentBlock ℓ.side (b.1 + TorusFields.unitStep (n * ℓ.side) b.2) ∈ Q := (Finset.mem_filter.mp h2).2
  refine h (b.1 + siteOfInt fun i => (ℓ.side : ℤ) * torusSiteCoords y i, b.2) ?_ ?_
  · show parentBlock ℓ.side (b.1 + siteOfInt fun i => (ℓ.side : ℤ) * torusSiteCoords y i) ∈ Q'
    rw [parentBlock_add_scaled, hy]
    exact hQ _ m1
  · show parentBlock ℓ.side (b.1 + (siteOfInt fun i => (ℓ.side : ℤ) * torusSiteCoords y i) + TorusFields.unitStep (n * ℓ.side) b.2) ∈ Q'
    rw [add_right_comm, parentBlock_add_scaled, hy]
    exact hQ _ m2
end Sites
section Laws
variable (ℓ : StepParameters) {n : ℕ} [NeZero n]
theorem torusSiteInFrame_zero : torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n) = 0 := by
  funext i
  simp [torusSiteInFrame, siteOfCoords]
theorem torusSiteInFrame_zero_add (y : TorusSite n) :
    torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n) + siteOfCoords 1 (torusSiteCoords y) =
      torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y := by
  rw [torusSiteInFrame_zero, zero_add]
  rfl
theorem siteAtOffset_shift (y : (stepBlockFrame ℓ.side n).Cell) (v z : Fin 4 → ℤ) :
    (siteAtOffset (y + siteOfCoords 1 v) z : (stepBlockFrame ℓ.side n).Site 0) =
      siteAtOffset y z + siteOfCoords 0 fun i => (ℓ.side : ℤ) * v i :=
  siteAtOffset_add_siteOfCoords (F := stepBlockFrame ℓ.side n) v y z
private theorem card_eq_of_add_mem_iff {α : Type} [AddGroup α] (A B : Finset α) (u : α)
    (h : ∀ z, z ∈ A ↔ z + u ∈ B) : A.card = B.card := by
  refine Finset.card_bij (fun z _ => z + u) (fun z hz => (h z).mp hz) (fun _ _ _ _ e => add_right_cancel e)
    fun z hz => ⟨z - u, (h _).mpr (by simpa using hz), by simp⟩
private theorem uniformWeight_of_add_mem_iff {α : Type} [AddGroup α] (A B : Finset α) (u : α)
    (h : ∀ z, z ∈ A ↔ z + u ∈ B) (z : α) [Decidable (z ∈ A)] [Decidable (z + u ∈ B)] :
    (if z ∈ A then 1 / (A.card : ℝ) else 0) = if z + u ∈ B then 1 / (B.card : ℝ) else 0 := by
  rw [card_eq_of_add_mem_iff A B u h]
  by_cases hz : z ∈ A
  · rw [if_pos hz, if_pos ((h z).mp hz)]
  · rw [if_neg hz, if_neg fun h' => hz ((h z).mpr h')]
theorem blockBaseWeight_of_iff (h h' : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0)))
    (y y' : (stepBlockFrame ℓ.side n).Cell) (u : (stepBlockFrame ℓ.side n).Site 0)
    (hh : ∀ z : (stepBlockFrame ℓ.side n).Site 0, z ∈ baseSitesAt ℓ.baseDepth h y ↔ z + u ∈ baseSitesAt ℓ.baseDepth h' y')
    (z : (stepBlockFrame ℓ.side n).Site 0) : blockBaseWeight ℓ h y z = blockBaseWeight ℓ h' y' (z + u) := by
  unfold blockBaseWeight
  classical
  exact uniformWeight_of_add_mem_iff (α := (stepBlockFrame ℓ.side n).Site 0) _ _ u hh z
theorem blockBaseWeight_recentre (hT : translationCarriesBasesStatement) (W : TorusField (n * ℓ.side)) (y : TorusSite n)
    (z : (stepBlockFrame ℓ.side n).Site 0) :
    blockBaseWeight ℓ (stepHotLumps ℓ (recentre ℓ y W)) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n)) z =
      blockBaseWeight ℓ (stepHotLumps ℓ W) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y)
        (z + siteOfCoords 0 fun i => (ℓ.side : ℤ) * torusSiteCoords y i) := by
  have h0 := (hT ℓ n (torusSiteCoords y) W).1 (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n))
  have hc := torusSiteInFrame_zero_add ℓ y
  generalize (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y) = q at hc ⊢
  subst hc
  exact blockBaseWeight_of_iff ℓ _ _ _ _ _ h0 z
theorem siteAtOffset_zero_add (y : TorusSite n) (z : Fin 4 → ℤ) :
    (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n)) z : (stepBlockFrame ℓ.side n).Site 0) +
        siteOfCoords 0 (fun i => (ℓ.side : ℤ) * torusSiteCoords y i) =
      siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y) z :=
  (siteAtOffset_shift ℓ (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n)) (torusSiteCoords y) z).symm.trans
    (congrArg (fun q : (stepBlockFrame ℓ.side n).Cell => (siteAtOffset q z : (stepBlockFrame ℓ.side n).Site 0))
      (torusSiteInFrame_zero_add ℓ y))
theorem baseChoice_shift (o : TorusSite n → BlockOffset ℓ.side) (c : TorusSite n) (y : (stepBlockFrame ℓ.side n).Cell) :
    (baseChoiceOfOffsets (fun y => o (y + c)) y : (stepBlockFrame ℓ.side n).Site 0) +
        siteOfCoords 0 (fun i => (ℓ.side : ℤ) * torusSiteCoords c i) =
      baseChoiceOfOffsets o (y + siteOfCoords 1 (torusSiteCoords c)) := by
  obtain ⟨x, rfl⟩ : ∃ x : TorusSite n, torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x = y :=
    ⟨toTorusSite n y, TopLevelSites.torusSiteInFrame_toTorusSite TorusContours.stepBlockFrame_period_one y⟩
  have h1 := TopLevelSites.toTorusSite_add (F := stepBlockFrame ℓ.side n) (j := 1) (N := n)
    TorusContours.stepBlockFrame_period_one
    (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x) (siteOfCoords 1 (torusSiteCoords c))
  rw [TopLevelSites.toTorusSite_torusSiteInFrame TorusContours.stepBlockFrame_period_one,
    TopLevelSites.toTorusSite_siteOfCoords TorusContours.stepBlockFrame_period_one, siteOfInt_torusSiteCoords] at h1
  have e : (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x + siteOfCoords 1 (torusSiteCoords c) :
      (stepBlockFrame ℓ.side n).Site 1) = torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (x + c) :=
    (TopLevelSites.torusSiteInFrame_toTorusSite TorusContours.stepBlockFrame_period_one _).symm.trans
      (congrArg (torusSiteInFrame (stepBlockFrame ℓ.side n) 1) h1)
  have g1 := baseChoice_torusSiteInFrame ℓ (fun y => o (y + c)) x
  have g2 := baseChoice_torusSiteInFrame ℓ o (x + c)
  have g3 := siteAtOffset_shift ℓ (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x) (torusSiteCoords c)
    (offsetFromCentre ℓ.side (o (x + c)))
  have e' := congrArg (baseChoiceOfOffsets o) e
  have e'' := congrArg (fun q : (stepBlockFrame ℓ.side n).Cell =>
    (siteAtOffset q (offsetFromCentre ℓ.side (o (x + c))) : (stepBlockFrame ℓ.side n).Site 0)) e
  exact (congrArg (· + (siteOfCoords 0 (fun i => (ℓ.side : ℤ) * torusSiteCoords c i) : (stepBlockFrame ℓ.side n).Site 0)) g1).trans
    (g3.symm.trans (e''.trans (g2.symm.trans e'.symm)))
theorem bondKernel_recentre (hT : translationCarriesBasesStatement) (x : ℝ) (W : TorusField (n * ℓ.side))
    (o : TorusSite n → BlockOffset ℓ.side) (c : TorusBond n) (g : UnitQuaternion) :
    bondKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 (recentre ℓ c.1 W))
        (readAtLevel (stepBlockFrame ℓ.side n) 1 (fun _ _ => g : TorusField n))
        (baseChoiceOfOffsets fun y => o (y + c.1)) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n), c.2) =
      bondKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
        (readAtLevel (stepBlockFrame ℓ.side n) 1 (fun _ _ => g : TorusField n)) (baseChoiceOfOffsets o)
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) := by
  have h := (hT ℓ n (torusSiteCoords c.1) W).2 (baseChoiceOfOffsets o) (baseChoiceOfOffsets fun y => o (y + c.1))
    (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n), c.2) (baseChoice_shift ℓ o c.1)
  have hc := torusSiteInFrame_zero_add ℓ c.1
  generalize (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1) = q at hc ⊢
  subst hc
  rw [TorusContours.bondKernel_eq_meanKernel, TorusContours.bondKernel_eq_meanKernel]
  show TorusContours.meanKernel _ _ g = TorusContours.meanKernel _ _ g
  exact congrArg (fun q => TorusContours.meanKernel (ℓ.coupling * x) q g) h
end Laws
section Rule
variable {ℓ : StepParameters} (T : StageTower ℓ) (S : ChainSampler T)
def ofSampler : NoiseRule ℓ where
  base s n _ W y v := siteOffset (toTorusSite (n * ℓ.side) ((S s).sampleBase n (recentre ℓ y W) 0 v))
  value s n _ W o c v := (S s).sampleLink n (recentre ℓ c.1 W) (baseChoiceOfOffsets fun y => o (y + c.1)) (0, c.2) v
def cellEquivTorusSite (L n : ℕ) [NeZero L] [NeZero n] : (stepBlockFrame L n).Cell ≃ TorusSite n where
  toFun := toTorusSite (F := stepBlockFrame L n) (j := 1) n
  invFun := torusSiteInFrame (stepBlockFrame L n) 1
  left_inv := TopLevelSites.torusSiteInFrame_toTorusSite TorusContours.stepBlockFrame_period_one
  right_inv := TopLevelSites.toTorusSite_torusSiteInFrame TorusContours.stepBlockFrame_period_one
variable {n : ℕ} [NeZero n] {s : ℕ}
theorem base_preimage_eq (hodd : Odd ℓ.side) (hD : (S s).IsFaithful) (W : TorusField (n * ℓ.side)) (y : TorusSite n)
    (o₁ : BlockOffset ℓ.side) :
    {u : I | (ofSampler T S).base s n W y u = o₁} =
      {u : I | (S s).sampleBase n (recentre ℓ y W) 0 u =
        siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n)) (offsetFromCentre ℓ.side o₁)} := by
  ext u
  show siteOffset (toTorusSite (n * ℓ.side) ((S s).sampleBase n (recentre ℓ y W) 0 u)) = o₁ ↔ _
  obtain ⟨z, hz, e⟩ := (TorusContours.mem_sitesBelow_iff _ _).mp (hD.base_mem_sitesBelow n (recentre ℓ y W) 0 u)
  have e' : (S s).sampleBase n (recentre ℓ y W) 0 u =
      siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n)) z := e
  show _ ↔ (S s).sampleBase n (recentre ℓ y W) 0 u = _
  rw [e']
  have hq := offsetFromCentre_siteOffset ℓ hodd (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n))
    (offsetFromCentre_mem_centredCube hodd o₁)
  constructor
  · intro h
    have h1 := offsetFromCentre_siteOffset ℓ hodd (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n)) hz
    have h2 : offsetFromCentre ℓ.side o₁ = z := (congrArg (offsetFromCentre ℓ.side) h).symm.trans h1
    rw [h2]
  · intro h
    apply offsetFromCentre_injective ℓ.side
    exact (congrArg (fun q : (stepBlockFrame ℓ.side n).Site 0 =>
      offsetFromCentre ℓ.side (siteOffset (toTorusSite (n * ℓ.side) q))) h).trans hq
theorem volume_base_preimage (hodd : Odd ℓ.side) (hD : (S s).IsFaithful) (hT : translationCarriesBasesStatement)
    (W : TorusField (n * ℓ.side)) (y : TorusSite n) (o₁ : BlockOffset ℓ.side) :
    (volume : Measure I) {u : I | (ofSampler T S).base s n W y u = o₁} =
      ENNReal.ofReal (blockBaseWeight ℓ (stepHotLumps ℓ W) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y)
        (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y) (offsetFromCentre ℓ.side o₁))) := by
  have e1 := hD.base_distribution n (recentre ℓ y W) 0
    (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n)) (offsetFromCentre ℓ.side o₁))
  have e2 := blockBaseWeight_recentre ℓ hT W y
    (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n)) (offsetFromCentre ℓ.side o₁))
  have e3 := congrArg (blockBaseWeight ℓ (stepHotLumps ℓ W) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y))
    (siteAtOffset_zero_add ℓ y (offsetFromCentre ℓ.side o₁))
  exact (congrArg (volume : Measure I) (base_preimage_eq T S hodd hD W y o₁)).trans
    (e1.trans (congrArg ENNReal.ofReal (e2.trans e3)))
private theorem blockBaseWeight_nonneg (ℓ : StepParameters) (h : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0)))
    (y : (stepBlockFrame ℓ.side n).Cell) (z : (stepBlockFrame ℓ.side n).Site 0) : 0 ≤ blockBaseWeight ℓ h y z := by apply _root_.YangMills.SharedProofs.p16398 <;> assumption
theorem base_joint_law (hodd : Odd ℓ.side) (hD : (S s).IsFaithful) (hT : translationCarriesBasesStatement)
    (hBL : BaseLawIsProduct) (W : TorusField (n * ℓ.side)) (o : TorusSite n → BlockOffset ℓ.side) :
    (Measure.pi fun _ : TorusSite n => (volume : Measure I)).real
        {U | ∀ y, (ofSampler T S).base s n W y (U y) = o y} =
      baseLaw (R := (T.stage s).toStepSetup) W (baseChoiceOfOffsets o) := by
  have e : {U : TorusSite n → I | ∀ y, (ofSampler T S).base s n W y (U y) = o y} =
      Set.univ.pi fun y => {u : I | (ofSampler T S).base s n W y u = o y} := by
    ext U
    simp
  have hp := hBL (T.stage s).toStepSetup n W (baseChoiceOfOffsets o)
  have hf0 : ∀ x : TorusSite n, 0 ≤ blockBaseWeight ℓ (stepHotLumps ℓ W) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x)
      (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x) (offsetFromCentre ℓ.side (o x))) :=
    fun x => blockBaseWeight_nonneg _ _ _ _
  rw [measureReal_def, e, Measure.pi_pi]
  simp only [volume_base_preimage T S hodd hD hT]
  rw [← ENNReal.ofReal_prod_of_nonneg fun x _ => hf0 x, ENNReal.toReal_ofReal (Finset.prod_nonneg fun x _ => hf0 x)]
  refine Eq.trans ?_ hp.symm
  have h := Equiv.prod_comp (cellEquivTorusSite ℓ.side n).symm fun y =>
    blockBaseWeight ℓ (stepHotLumps ℓ W) y (baseChoiceOfOffsets o y)
  refine Eq.trans (Finset.prod_congr rfl fun x _ => ?_) h
  exact congrArg (blockBaseWeight ℓ (stepHotLumps ℓ W) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x))
    (baseChoice_torusSiteInFrame ℓ o x).symm
theorem add_mem_box (y : TorusSite n) (m : ℕ) {a : TorusSite n} (h : supDist a 0 ≤ m) : a + y ∈ HullTrees.box y m := by
  unfold HullTrees.box
  rw [mem_thickening]
  refine ⟨y, Finset.mem_singleton_self y, ?_⟩
  have := supDist_add_right a 0 y
  rw [zero_add] at this
  rw [this]
  exact h
end Rule
section Main
variable {ℓ : StepParameters} (T : StageTower ℓ) (S : ChainSampler T)
theorem ofSampler_isAdmissible (hodd : Odd ℓ.side) (hD : ∀ s, (S s).IsFaithful) (hT : translationCarriesBasesStatement)
    (hBL : BaseLawIsProduct) : (ofSampler T S).IsAdmissible T := by
  have hvb : ∀ (s n : ℕ) [NeZero n] (o : TorusSite n → BlockOffset ℓ.side) (c : TorusBond n),
      Measurable fun p : TorusField (n * ℓ.side) × I => (ofSampler T S).value s n p.1 o c p.2 := fun s n _ o c =>
    ((hD s).measurable_link n (0, c.2)).comp
      (((measurable_recentre ℓ c.1).comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
  refine ⟨?_, hvb, fun s n _ W o => base_joint_law T S hodd (hD s) hT hBL W o, ?_, ?_, ?_, ?_, ?_⟩
  · intro s n _ y
    have h1 : Measurable fun p : TorusField (n * ℓ.side) × I => (S s).sampleBase n (recentre ℓ y p.1) 0 p.2 :=
      ((hD s).measurable_base n 0).comp (((measurable_recentre ℓ y).comp measurable_fst).prodMk measurable_snd)
    exact (Measurable.of_discrete (f := fun z : (stepBlockFrame ℓ.side n).Site 0 =>
      (siteOffset (toTorusSite (n * ℓ.side) z) : BlockOffset ℓ.side))).comp h1
  · intro s n _ W o c
    have hm : Measurable ((ofSampler T S).value s n W o c) := (hvb s n o c).comp measurable_prodMk_left
    ext A hA
    rw [Measure.map_apply hm hA, withDensity_apply _ hA]
    refine ((hD s).link_distribution n (recentre ℓ c.1 W) (baseChoiceOfOffsets fun y => o (y + c.1)) (0, c.2) A hA).trans ?_
    refine lintegral_congr fun g => ?_
    exact congrArg ENNReal.ofReal (bondKernel_recentre ℓ hT _ W o c g)
  · intro s n _ W W' y v h
    have hQ : ∀ a ∈ thickening 3 {(0 : TorusSite n)}, a + y ∈ HullTrees.box y 3 := by
      intro a ha
      obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp ha
      rw [Finset.mem_singleton] at hx
      subst hx
      exact add_mem_box y 3 hd
    exact congrArg (fun z : (stepBlockFrame ℓ.side n).Site 0 => (siteOffset (toTorusSite (n * ℓ.side) z) : BlockOffset ℓ.side))
      ((hD s).base_local n (recentre ℓ y W) (recentre ℓ y W') 0 v (fieldsAgreeOn_recentre ℓ y hQ h))
  · intro s n _ W W' o o' c v h h1 h2
    have hQ : ∀ a ∈ thickening 3 {(0 : TorusSite n), 0 + TorusFields.unitStep n c.2}, a + c.1 ∈ HullTrees.box c.1 4 := by
      intro a ha
      obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp ha
      refine add_mem_box c.1 4 ?_
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · omega
      · have h3 := supDist_triangle a (0 + TorusFields.unitStep n c.2) 0
        have h4 := TorusContours.supDist_sub_unitStep_le (TorusFields.unitStep n c.2) c.2
        rw [sub_self] at h4
        rw [zero_add] at h3 hd
        omega
    have hodd' := hodd
    refine (hD s).link_local n (recentre ℓ c.1 W) (recentre ℓ c.1 W') _ _ (0, c.2) v (fieldsAgreeOn_recentre ℓ c.1 hQ h)
      (baseChoice_mem_sitesBelow ℓ hodd _ _) (baseChoice_mem_sitesBelow ℓ hodd _ _) ?_ ?_
    · have e : ((0 : TorusSite n) + c.1) = c.1 := zero_add _
      show baseChoiceOfOffsets _ (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n)) =
        baseChoiceOfOffsets _ (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (0 : TorusSite n))
      rw [baseChoice_torusSiteInFrame, baseChoice_torusSiteInFrame, e, h1]
    · have e : ((0 : TorusSite n) + TorusFields.unitStep n c.2 + c.1) = c.1 + TorusFields.unitStep n c.2 := by abel
      show baseChoiceOfOffsets _ (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 ((0 : TorusSite n) + TorusFields.unitStep n c.2)) =
        baseChoiceOfOffsets _ (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 ((0 : TorusSite n) + TorusFields.unitStep n c.2))
      rw [baseChoice_torusSiteInFrame, baseChoice_torusSiteInFrame, e, h2]
  · intro s n _ W h y v
    show siteOffset (toTorusSite (n * ℓ.side) ((S s).sampleBase n
        (recentre ℓ y (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * h i) W)) 0 v)) =
      siteOffset (toTorusSite (n * ℓ.side) ((S s).sampleBase n (recentre ℓ (y + siteOfInt h) W) 0 v))
    rw [recentre_translate]
  · intro s n _ W o h c v
    show (S s).sampleLink n (recentre ℓ c.1 (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * h i) W))
        (baseChoiceOfOffsets fun y => o (y + c.1 + siteOfInt h)) (0, c.2) v =
      (S s).sampleLink n (recentre ℓ (c.1 + siteOfInt h) W) (baseChoiceOfOffsets fun y => o (y + (c.1 + siteOfInt h)))
        (0, c.2) v
    rw [recentre_translate]
    simp only [add_assoc]
end Main
end RuleFromSampler
open RuleFromSampler in
theorem existsNoiseRule (hS : samplerExistsStatement) (hT : translationCarriesBasesStatement)
    (hBL : BaseLawIsProduct) : existsNoiseRuleStatement := by
  intro ℓ hfit T
  obtain ⟨S, hD⟩ := hS ℓ hfit T
  exact ⟨ofSampler T S, ofSampler_isAdmissible T S hfit.L_odd hD hT hBL⟩
end ChainNoise
end YangMills.Construction
end

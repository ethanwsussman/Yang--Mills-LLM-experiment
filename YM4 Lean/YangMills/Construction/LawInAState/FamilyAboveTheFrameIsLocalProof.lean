import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAboveTheFrameIsLocalProof
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionCoefficientsAtTwoFieldsProof
import YangMills.Construction.LawInAState.FamilyAboveTheFrameIsLocal
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open Estimates Interpolation ColdStepAtMirrorFrames LinearResponse
namespace FrameLocality
open ColdStepAtMirrorFrames.BlockOffsets ColdStepAtMirrorFrames.TwoTopLabels
namespace LocalityLemmas
variable {F F' : BlockFrame}
theorem torusDecayFactor_pos (L : ℕ) (δ x : ℝ) : 0 < torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
theorem one_le_torusDecayFactor (L : ℕ) {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) : 1 ≤ torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.one_le_decayWeight <;> assumption
theorem torusDecayFactor_mono {L : ℕ} {δ x x' : ℝ} (hL : 1 ≤ L) (hδ : 0 ≤ δ) (hx : 0 ≤ x) (h : x ≤ x') :
    torusDecayFactor L δ x ≤ torusDecayFactor L δ x' := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AxialSecondOrder.torusDecayFactor_mono <;> assumption
theorem bondDeriv_sub_const {j k : ℕ} (G : F.GaugeField j → ℝ) (a : ℝ) (U : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : 1 ≤ k) :
    bondDeriv (fun V => G V - a) U c X = bondDeriv G U c X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.bondDeriv_sub_const <;> assumption
theorem bondDeriv_sub_const_sub {j k : ℕ} (G : F.GaugeField j → ℝ) (a : ℝ) (W W' : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun V => G V - a) W c X - bondDeriv (fun V => G V - a) W' c X =
      bondDeriv G W c X - bondDeriv G W' c X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.RegularFamilyDerivs.bondDeriv_sub_const_sub <;> assumption
theorem stepCoordinates_zero {S : Finset F.Cell} (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable S) x i = 0 := by apply _root_.YangMills.SharedProofs.p7539 <;> assumption
theorem fieldAboveFrame_zero (star : Bool) (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    fieldAboveFrame star a ρ m V 0 = chartedField (frameCoordField star a ρ m V) V := by apply _root_.YangMills.SharedProofs.p2150 <;> assumption
theorem site_eq_cellCentre_add (Y : F.Cell) (o₀ g : Fin 4 → ℤ) :
    ((cellCentre F.depth Y + siteOfCoords F.depth o₀) + siteOfCoords F.depth g : F.Site F.depth) =
      cellCentre F.depth (Y + siteOfCoords F.top (cellIndex F.blockSide (o₀ + g))) +
        siteOfCoords F.depth (cellRemainder F.blockSide (o₀ + g)) := by
  rw [add_assoc, ← _root_.YangMills.Construction.BlockAverages.siteOfCoords_add, cellCentre_add_siteOfCoords_eq]
theorem cellIndex_withinRadius {L q : ℕ} (hL : Odd L) (hL2 : 2 ≤ L) {o₀ g : Fin 4 → ℤ} (ho : o₀ ∈ centredCube L)
    (hg : WithinRadius (L * q + 1) g) :
    WithinRadius (q + 3) (cellIndex L (o₀ + g)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.cellIndex_withinRadius <;> assumption
theorem cellSupDist_add_le {M : ℕ} (Y : F.Cell) (h : Fin 4 → ℤ) (hper : ∀ i, 2 * M + 2 < F.period F.top i)
    (hh : WithinRadius M h) :
    cellSupDist Y (Y + siteOfCoords F.top h) ≤ M := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.cellSupDist_add_le <;> assumption
structure AgreeingTops (star : Bool) (a ρ δ₂ κ₂ C σ : ℝ) (Kk : ℕ → ℝ) (m r : ℕ) (F F' : BlockFrame)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) : Prop where
  odd : Odd F.blockSide
  odd' : Odd F'.blockSide
  blockSide_eq : F'.blockSide = F.blockSide
  two_le_blockSide : 2 ≤ F.blockSide
  extent_gt : ∀ i, 2 * r + 2 < F.extent i
  extent_gt' : ∀ i, 2 * r + 2 < F'.extent i
  sixteen_le : 16 ≤ r
  δ₂_pos : 0 < δ₂
  σ_nonneg : 0 ≤ σ
  σ_le_one : σ ≤ 1
  ρ_le_one : ρ ≤ 1
  C_nonneg : 0 ≤ C
  small : FrameSmallness star a ρ δ₂ κ₂ C σ Kk m V
  small' : FrameSmallness star a ρ δ₂ κ₂ C σ Kk m V'
  near : ColdStepAtMirrorFrames.FrameLocality star a ρ δ₂ C σ m V V' Y Y' r
  agree : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r
  chord : ∀ d : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F)
  chord' : ∀ d : F'.Site F'.depth × Fin 4, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F')
  adjacent : ∀ (x : F.Site F.depth) (i : Fin 4), enclosingCell (x + unitStep F.depth i) = enclosingCell x ∨
    enclosingCell (x + unitStep F.depth i) = enclosingCell x + unitStep F.top i
section pair
variable {star : Bool} {a ρ δ₂ κ₂ C σ : ℝ} {Kk : ℕ → ℝ} {m r : ℕ} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
theorem AgreeingTops.two_le_extent (P : AgreeingTops star a ρ δ₂ κ₂ C σ Kk m r F F' V V' Y Y') :
    ∀ i, 2 ≤ F.extent i := fun i => by
  have := P.extent_gt i
  omega
theorem AgreeingTops.two_le_extent' (P : AgreeingTops star a ρ δ₂ κ₂ C σ Kk m r F F' V V' Y Y') :
    ∀ i, 2 ≤ F'.extent i := fun i => by
  have := P.extent_gt' i
  omega
theorem fineBond_withinRadius (P : AgreeingTops star a ρ δ₂ κ₂ C σ Kk m r F F' V V' Y Y') (h o : Fin 4 → ℤ)
    (i : Fin 4) (ho : o ∈ centredCube F.blockSide) (hh : WithinRadius (r / 4 + 3) h)
    (ht : ¬ IsAxialTreeBond (fineBondAt Y h o i)) :
    IsFineBondWithinRadius Y r h o i ∧
      (r : ℝ) / 2 ≤ (r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) := by
  have h16 := P.sixteen_le
  have hsp : ∀ (M : ℕ), M ≤ r / 4 + 4 → ∀ i, 2 * M + 2 < F.period F.top i := by
    intro M hM i
    rw [period_top]
    have := P.extent_gt i
    omega
  have hc : enclosingCell (fineBondAt Y h o i).1 = Y + siteOfCoords F.top h :=
    enclosingCell_offset P.odd P.two_le_extent _ o ho
  have hd : cellSupDist Y (Y + siteOfCoords F.top h) ≤ r / 4 + 3 := cellSupDist_add_le Y h (hsp _ (by omega)) hh
  have hdr : 2 * cellSupDist Y (Y + siteOfCoords F.top h) ≤ r := by omega
  refine ⟨⟨ho, P.chord _ ht, fun l => (hh l).trans (by exact_mod_cast (by omega : r / 4 + 3 ≤ r)), ?_, ?_⟩, ?_⟩
  · rw [hc]
    omega
  · rcases P.adjacent (fineBondAt Y h o i).1 i with e | e
    · show cellSupDist Y (enclosingCell ((fineBondAt Y h o i).1 + unitStep F.depth i)) ≤ r
      rw [e, hc]
      omega
    · show cellSupDist Y (enclosingCell ((fineBondAt Y h o i).1 + unitStep F.depth i)) ≤ r
      rw [e, hc, add_assoc, unitStep_eq, ← _root_.YangMills.Construction.BlockAverages.siteOfCoords_add]
      have h5 : WithinRadius (r / 4 + 4) (h + LatticeFractionalIntegration.basisVector i) := by
        intro l
        have a1 : |(h + LatticeFractionalIntegration.basisVector i : Fin 4 → ℤ) l| ≤
            |h l| + |(LatticeFractionalIntegration.basisVector i : Fin 4 → ℤ) l| := abs_add_le _ _
        have a2 : |(LatticeFractionalIntegration.basisVector i : Fin 4 → ℤ) l| ≤ 1 := by
          by_cases e : l = i
          · subst e
            simp [LatticeFractionalIntegration.basisVector]
          · simp [LatticeFractionalIntegration.basisVector, Pi.single_eq_of_ne e]
        have a3 := hh l
        push_cast at a3 ⊢
        linarith
      have := cellSupDist_add_le Y _ (hsp _ le_rfl) h5
      omega
  · rw [hc]
    have h6 : ((2 * cellSupDist Y (Y + siteOfCoords F.top h) : ℕ) : ℝ) ≤ r := by exact_mod_cast hdr
    push_cast at h6
    linarith
theorem exp_decay_le (P : AgreeingTops star a ρ δ₂ κ₂ C σ Kk m r F F' V V' Y Y') {d : ℝ}
    (hd : (r : ℝ) / 2 ≤ (r : ℝ) - d) :
    Real.exp (-(δ₂ / 4 * ((r : ℝ) - d))) ≤ Real.exp (-(δ₂ / 8 * r)) := by
  refine Real.exp_le_exp.2 ?_
  have := P.δ₂_pos
  nlinarith
theorem distFromOne_le (P : AgreeingTops star a ρ δ₂ κ₂ C σ Kk m r F F' V V' Y Y')
    (hshort : ∀ u v : imaginaryQuaternions,
      ‖((expUnit u : UnitQuaternion) : ℍ[ℝ]) - ((expUnit v : UnitQuaternion) : ℍ[ℝ])‖ ≤ ‖u - v‖)
    (h o : Fin 4 → ℤ) (i : Fin 4) (ho : o ∈ centredCube F.blockSide) (hh : WithinRadius (r / 4 + 3) h) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (chartedField (frameCoordField star a ρ m V') V'
          (cellCentre F'.depth (Y' + siteOfCoords F'.top h) + siteOfCoords F'.depth o) i *
        (chartedField (frameCoordField star a ρ m V) V
          (cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o) i)⁻¹) ≤
      C * σ * Real.exp (-(δ₂ / 8 * r)) := by
  classical
  have hnn : 0 ≤ C * σ * Real.exp (-(δ₂ / 8 * r)) :=
    mul_nonneg (mul_nonneg P.C_nonneg P.σ_nonneg) (Real.exp_pos _).le
  obtain ⟨-, ht⟩ := bondKind_iff P.odd P.two_le_extent P.odd' P.two_le_extent' P.blockSide_eq Y Y' h h o ho i
  by_cases h1 : IsAxialTreeBond ((cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o :
      F.Site F.depth), i)
  · have e1 : chartedField (frameCoordField star a ρ m V) V
        (cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o) i = 1 := by
      unfold chartedField
      rw [if_neg h1.1, if_pos h1]
    have h2 := ht.1 h1
    have e2 : chartedField (frameCoordField star a ρ m V') V'
        (cellCentre F'.depth (Y' + siteOfCoords F'.top h) + siteOfCoords F'.depth o) i = 1 := by
      unfold chartedField
      rw [if_neg h2.1, if_pos h2]
    rw [e1, e2]
    simpa [_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne] using hnn
  · have hb := fineBond_withinRadius P h o i ho hh h1
    have hr : BondWithinRadius r (h, i) := by
      have h16 := P.sixteen_le
      refine ⟨hb.1.2.2.1, fun l => ?_⟩
      have a1 : |(h + Pi.single i 1 : Fin 4 → ℤ) l| ≤ |h l| + |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| :=
        abs_add_le _ _
      have a2 : |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ 1 := by
        by_cases e : l = i
        · subst e
          simp
        · simp [e]
      have a3 := hh l
      have a4 : ((r / 4 + 3 : ℕ) : ℤ) + 1 ≤ (r : ℤ) := by exact_mod_cast (by omega : r / 4 + 3 + 1 ≤ r)
      linarith
    have hV := P.agree.2.2.2 (h, i) hr
    have g1 := distFromOne_chartedField_le P.odd P.two_le_extent P.odd' P.two_le_extent' P.blockSide_eq hshort
      (frameCoordField star a ρ m V) (frameCoordField star a ρ m V') V V' Y Y' h o ho i hV
    refine g1.trans ?_
    rw [norm_sub_rev]
    have g2 := P.near.value h o i hb.1
    refine le_trans g2 ?_
    exact mul_le_mul_of_nonneg_left (exp_decay_le P hb.2) (mul_nonneg P.C_nonneg P.σ_nonneg)
end pair
structure IsFrameMotion (star : Bool) (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions)
    (α : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions) : Prop where
  at_zero : ∀ x i, α 0 x i = 0
  contDiffAt : ∀ x i, ContDiffAt ℝ 3 (fun τ => α τ x i) 0
  vanishes_on_tree : ∀ x i, IsAxialTreeBond (x, i) → ∀ τ, α τ x i = 0
  eventually_eq : ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ),
    chartedField (frameCoordField star a ρ m (leftTranslate (bondSpread c X τ) V)) (leftTranslate (bondSpread c X τ) V) =
      leftTranslate (α τ) (chartedField (frameCoordField star a ρ m V) V)
def MotionComponentsBound (K C : ℝ) : Prop :=
  ∀ (F F' : BlockFrame) (w : F.GaugeField F.top → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (w' : F'.GaugeField F'.top → F'.Site F'.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (c : Fin 2 → F.Site F.top × Fin 4) (c' : Fin 2 → F'.Site F'.top × Fin 4) (X : Fin 2 → imaginaryQuaternions)
    (α : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (α' : (Fin 2 → ℝ) → F'.Site F'.depth → Fin 4 → imaginaryQuaternions)
    (x : F.Site F.depth) (x' : F'.Site F'.depth) (i : Fin 4) (ε : ℝ), 0 ≤ ε → AreUnitVectors X →
    ¬ IsAxialTreeBond (x, i) → ¬ IsAxialTreeBond (x', i) → (∀ z j, α 0 z j = 0) → (∀ z j, α' 0 z j = 0) →
    ContDiffAt ℝ 3 (fun τ => α τ x i) 0 → ContDiffAt ℝ 3 (fun τ => α' τ x' i) 0 →
    ContDiffAt ℝ 3 (fun τ => w (leftTranslate (bondSpread c X τ) V) x i) 0 →
    ContDiffAt ℝ 3 (fun τ => w' (leftTranslate (bondSpread c' X τ) V') x' i) 0 →
    ‖w V x i‖ ≤ 1 → ‖w' V' x' i‖ ≤ 1 →
    (∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), chartedField (w (leftTranslate (bondSpread c X τ) V)) (leftTranslate (bondSpread c X τ) V) =
      leftTranslate (α τ) (chartedField (w V) V)) →
    (∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ),
      chartedField (w' (leftTranslate (bondSpread c' X τ) V')) (leftTranslate (bondSpread c' X τ) V') =
        leftTranslate (α' τ) (chartedField (w' V') V')) →
    crossingMove c X x i = crossingMove c' X x' i →
    (∀ l, ‖bondDeriv (fun U => w U x i) V ![c l] ![X l]‖ ≤ K) →
    (∀ l, ‖bondDeriv (fun U => w' U x' i) V' ![c' l] ![X l]‖ ≤ K) →
    ‖bondDeriv (fun U => w U x i) V c X‖ ≤ K → ‖bondDeriv (fun U => w' U x' i) V' c' X‖ ≤ K →
    ‖w V x i - w' V' x' i‖ ≤ ε →
    (∀ l, ‖bondDeriv (fun U => w U x i) V ![c l] ![X l] - bondDeriv (fun U => w' U x' i) V' ![c' l] ![X l]‖ ≤ ε) →
    ‖bondDeriv (fun U => w U x i) V c X - bondDeriv (fun U => w' U x' i) V' c' X‖ ≤ ε →
    (∀ l, ‖motionComponent α ![l] x i - motionComponent α' ![l] x' i‖ ≤ C * ε) ∧
      ‖motionComponent α ![0, 1] x i - motionComponent α' ![0, 1] x' i‖ ≤ C * ε
theorem motionComponent_eq_zero {r' : ℕ} (α : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (x : F.Site F.depth) (i : Fin 4) (h : ∀ τ, α τ x i = 0) (e : Fin r' → Fin 2) :
    motionComponent α e x i = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.motionComponent_eq_zero_of_rest <;> assumption
section parts
variable {star : Bool} {a ρ δ₂ κ₂ C σ : ℝ} {Kk : ℕ → ℝ} {m r : ℕ} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
theorem bondsAt_vec_single (Y : F.Cell) (e : Fin 2 → (Fin 4 → ℤ) × Fin 4) (l : Fin 2) :
    bondsAt Y ![e l] = ![bondsAt Y e l] := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.bondsAt_single <;> assumption
theorem motionComponents_near (P : AgreeingTops star a ρ δ₂ κ₂ C σ Kk m r F F' V V' Y Y') {K₀ Cp : ℝ}
    (hCp : 0 ≤ Cp) (hCK : C ≤ K₀) (hNP : MotionComponentsBound K₀ Cp) (e : Fin 2 → (Fin 4 → ℤ) × Fin 4)
    (he : ∀ l, BondWithinRadius r (e l)) (X : Fin 2 → imaginaryQuaternions) (hX : AreUnitVectors X)
    {α : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {α' : (Fin 2 → ℝ) → F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    (hα : IsFrameMotion star a ρ m V (bondsAt Y e) X α) (hα' : IsFrameMotion star a ρ m V' (bondsAt Y' e) X α')
    (h o : Fin 4 → ℤ) (i : Fin 4) (ho : o ∈ centredCube F.blockSide) (hh : WithinRadius (r / 4 + 3) h) :
    (∀ l, ‖motionComponent α ![l] (cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o) i -
        motionComponent α' ![l] (cellCentre F'.depth (Y' + siteOfCoords F'.top h) + siteOfCoords F'.depth o) i‖ ≤
          Cp * (C * Real.exp (-(δ₂ / 8 * r)))) ∧
      ‖motionComponent α ![0, 1] (cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o) i -
        motionComponent α' ![0, 1] (cellCentre F'.depth (Y' + siteOfCoords F'.top h) + siteOfCoords F'.depth o) i‖ ≤
          Cp * (C * Real.exp (-(δ₂ / 8 * r))) := by
  classical
  have ho' : o ∈ centredCube F'.blockSide := by rw [P.blockSide_eq]; exact ho
  have hnn : 0 ≤ Cp * (C * Real.exp (-(δ₂ / 8 * r))) :=
    mul_nonneg hCp (mul_nonneg P.C_nonneg (Real.exp_pos _).le)
  obtain ⟨-, ht⟩ := bondKind_iff P.odd P.two_le_extent P.odd' P.two_le_extent' P.blockSide_eq Y Y' h h o ho i
  set x : F.Site F.depth := cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o with hx
  set x' : F'.Site F'.depth := cellCentre F'.depth (Y' + siteOfCoords F'.top h) + siteOfCoords F'.depth o with hx'
  by_cases h1 : IsAxialTreeBond (x, i)
  · have h2 := ht.1 h1
    refine ⟨fun l => ?_, ?_⟩
    · rw [motionComponent_eq_zero α x i (hα.vanishes_on_tree x i h1),
        motionComponent_eq_zero α' x' i (hα'.vanishes_on_tree x' i h2)]
      simpa using hnn
    · rw [motionComponent_eq_zero α x i (hα.vanishes_on_tree x i h1),
        motionComponent_eq_zero α' x' i (hα'.vanishes_on_tree x' i h2)]
      simpa using hnn
  · have h2 : ¬ IsAxialTreeBond (x', i) := fun q => h1 (ht.2 q)
    obtain ⟨hb, hd⟩ := fineBond_withinRadius P h o i ho hh h1
    have hch := P.chord _ h1
    have hch' := P.chord' _ h2
    have hexp := exp_decay_le P hd
    set e₁ := Real.exp (-(δ₂ / 8 * r)) with he₁
    have hCe : 0 ≤ C * e₁ := mul_nonneg P.C_nonneg (Real.exp_pos _).le
    have hunit : ∀ l, AreUnitVectors ![X l] := fun l q => by
      fin_cases q
      exact hX l
    have hdec : ∀ {G : BlockFrame} {U : G.GaugeField G.top} (_ : FrameSmallness star a ρ δ₂ κ₂ C σ Kk m U)
        (b : G.Site G.depth × Fin 4) (_ : b ∈ chordBonds (finiteCells G)) (k : ℕ)
        (c' : Fin k → G.Site G.top × Fin 4) (Z : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
        AreUnitVectors Z → ‖bondDeriv (stepFrame star a ρ m b) U c' Z‖ ≤ C := by
      intro G U hs b hb k c' Z h1 h2 h3
      refine (hs.deriv_decay b hb k c' Z h1 h2 h3).trans ?_
      have : Real.exp (-(δ₂ / 4 * bondListDistance (enclosingCell b.1) c')) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := P.δ₂_pos
        nlinarith
      nlinarith [P.C_nonneg]
    have hval := P.near.value h o i hb
    have hval2 : ‖frameCoordField star a ρ m V x i - frameCoordField star a ρ m V' x' i‖ ≤ C * e₁ := by
      refine le_trans hval ?_
      have a1 := mul_le_mul_of_nonneg_left hexp (mul_nonneg P.C_nonneg P.σ_nonneg)
      refine a1.trans ?_
      have a2 : C * σ ≤ C := by nlinarith [P.C_nonneg, P.σ_le_one]
      exact mul_le_mul_of_nonneg_right a2 (Real.exp_pos _).le
    have hder₁ : ∀ l, ‖bondDeriv (fun U => frameCoordField star a ρ m U x i) V ![bondsAt Y e l] ![X l] -
        bondDeriv (fun U => frameCoordField star a ρ m U x' i) V' ![bondsAt Y' e l] ![X l]‖ ≤ C * e₁ := by
      intro l
      have d1 := P.near.deriv h o i 1 ![e l] ![X l] hb le_rfl (by norm_num)
        (by intro q; fin_cases q; exact he l) (hunit l)
      rw [bondsAt_vec_single, bondsAt_vec_single] at d1
      exact d1.trans (mul_le_mul_of_nonneg_left hexp P.C_nonneg)
    have hder₂ : ‖bondDeriv (fun U => frameCoordField star a ρ m U x i) V (bondsAt Y e) X -
        bondDeriv (fun U => frameCoordField star a ρ m U x' i) V' (bondsAt Y' e) X‖ ≤ C * e₁ :=
      (P.near.deriv h o i 2 e X hb (by norm_num) (by norm_num) he hX).trans
        (mul_le_mul_of_nonneg_left hexp P.C_nonneg)
    have hmv : crossingMove (bondsAt Y e) X x i = crossingMove (bondsAt Y' e) X x' i :=
      crossingMove_eq (r := r) P.odd P.two_le_extent P.odd' P.two_le_extent' P.blockSide_eq
        (fun l => by rw [period_top]; exact P.extent_gt l)
        (fun l => by rw [period_top]; exact P.extent_gt' l) Y Y' h o ho hb.2.2.1 i e (fun l => (he l).1) X
    have hsz : ∀ {G : BlockFrame} {U : G.GaugeField G.top} (_ : FrameSmallness star a ρ δ₂ κ₂ C σ Kk m U)
        (b : G.Site G.depth × Fin 4) (_ : b ∈ chordBonds (finiteCells G)), ‖stepFrame star a ρ m b U‖ ≤ 1 := by
      intro G U hs b hb
      have := hs.norm_add_le b hb
      have h3 := P.ρ_le_one
      have h4 := P.σ_nonneg
      linarith
    exact hNP F F' (fun U => frameCoordField star a ρ m U) (fun U => frameCoordField star a ρ m U) V V'
      (bondsAt Y e) (bondsAt Y' e) X α α' x x' i (C * e₁) hCe hX h1 h2 hα.at_zero hα'.at_zero
      (hα.contDiffAt x i) (hα'.contDiffAt x' i)
      ((P.small.analytic _ hch 2 (bondsAt Y e) X).contDiffAt)
      ((P.small'.analytic _ hch' 2 (bondsAt Y' e) X).contDiffAt)
      (hsz P.small _ hch) (hsz P.small' _ hch') hα.eventually_eq hα'.eventually_eq hmv
      (fun l => (hdec P.small _ hch 1 _ _ le_rfl (by norm_num) (hunit l)).trans hCK)
      (fun l => (hdec P.small' _ hch' 1 _ _ le_rfl (by norm_num) (hunit l)).trans hCK)
      ((hdec P.small _ hch 2 _ _ (by norm_num) (by norm_num) hX).trans hCK)
      ((hdec P.small' _ hch' 2 _ _ (by norm_num) (by norm_num) hX).trans hCK)
      hval2 hder₁ hder₂
end parts
def FlowDerivBound (C₀ : ℝ) : Prop :=
  ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame)
    (T : Finset (F.Site F.depth × Fin 4)) (y : F.Site F.depth) (W W' : F.GaugeField F.depth)
    (B : F.Site F.depth → Fin 4 → imaginaryQuaternions) (r k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4)
    (X : Fin k → imaginaryQuaternions),
    IsRegularOnTorus L t n₀ σ δ E E₃ f F → IsCubicTorusAbove L t n₀ F → 0 ≤ δ → 0 ≤ E → E ≤ E₃ →
    (∀ b, b ∈ T) → (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature σ (expFlow B W u)) → IsSmallCurvature σ W' →
    AgreeOnBox (expFlow B W 1) W' y y r → k ≤ 2 → (∀ l, BondWithinRadius r (h l)) → AreUnitVectors X →
    |bondDeriv (subtractTrivial f F y) W (bondsAt y h) X - bondDeriv (subtractTrivial f F y) W' (bondsAt y h) X| ≤
      E / torusDecayFactor L δ r + C₀ * E₃ * ∑ b ∈ T, ‖B b.1 b.2‖
theorem exists_flowDerivBound (hflow : DerivBoundAlongFlow) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ FlowDerivBound C₀ := by
  obtain ⟨C₀, hC₀, hfl⟩ := hflow
  refine ⟨3 * C₀, by positivity, ?_⟩
  intro L t n₀ σ δ E E₃ f F T y W W' B r k h X hf hF hδ hE hEE hT hflc hW' hag hk hb hX
  have hW1 := hflc 1 zero_le_one le_rfl
  have h1 := hf.locality hF y (expFlow B W 1) W' r k h X hW1 hW' hag hk hb hX
  have hsm : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ContDiffThreeAlongBonds (f F y) (expFlow B W u) := fun u h0 h1 =>
    hf.smooth hF y _ (hflc u h0 h1)
  have hbd : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ (l : ℕ) (c : Fin l → F.Site F.depth × Fin 4)
      (Z : Fin l → imaginaryQuaternions),
      1 ≤ l → l ≤ 3 → AreUnitVectors Z → ‖bondDeriv (f F y) (expFlow B W u) c Z‖ ≤ E₃ := by
    intro u h0 h1 l c Z hl1 hl3 hZ
    have a := hf.decay hF y _ l c Z (hflc u h0 h1) hl1 hl3 hZ
    rw [Real.norm_eq_abs]
    have hE3 : 0 ≤ E₃ := hE.trans hEE
    have hG := one_le_torusDecayFactor L (x := (bondSpan y c : ℝ)) hδ (by positivity)
    have hc : 0 ≤ (if l = 3 then E₃ else E) := by split_ifs <;> assumption
    have hle : (if l = 3 then E₃ else E) ≤ E₃ := by split_ifs <;> linarith
    refine a.trans ((div_le_self hc hG).trans hle)
  have h2 := hfl ℝ F F.depth T (f F y) W B (fun _ => E₃) hT (fun _ => hE.trans hEE) hsm hbd k (bondsAt y h) X hk hX
  rw [Real.norm_eq_abs] at h2
  have e := bondDeriv_sub_const_sub (f F y) (f F y (uniformField F F.depth)) (expFlow B W 1) W (bondsAt y h) X
  have e' : bondDeriv (subtractTrivial f F y) (expFlow B W 1) (bondsAt y h) X -
      bondDeriv (subtractTrivial f F y) W (bondsAt y h) X =
      bondDeriv (f F y) (expFlow B W 1) (bondsAt y h) X - bondDeriv (f F y) W (bondsAt y h) X := e
  have h3 : |bondDeriv (subtractTrivial f F y) W (bondsAt y h) X -
      bondDeriv (subtractTrivial f F y) (expFlow B W 1) (bondsAt y h) X| ≤
      C₀ * (E₃ + E₃ + E₃) * ∑ b ∈ T, ‖B b.1 b.2‖ := by
    rw [abs_sub_comm, e']
    exact h2
  have h4 := abs_sub_le (bondDeriv (subtractTrivial f F y) W (bondsAt y h) X)
    (bondDeriv (subtractTrivial f F y) (expFlow B W 1) (bondsAt y h) X)
    (bondDeriv (subtractTrivial f F y) W' (bondsAt y h) X)
  linarith
def bondLabels (R : ℕ) : Finset ((Fin 4 → ℤ) × Fin 4) :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) R) ×ˢ Finset.univ
theorem mem_bondLabels {R : ℕ} {p : (Fin 4 → ℤ) × Fin 4} : p ∈ bondLabels R ↔ WithinRadius R p.1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.mem_bondLabels <;> assumption
theorem card_bondLabels (R : ℕ) : ((bondLabels R).card : ℝ) = 4 * (2 * (R : ℝ) + 1) ^ 4 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.card_bondLabels <;> assumption
theorem bondWithinRadius_of_mem {R : ℕ} {p : (Fin 4 → ℤ) × Fin 4} (h : p ∈ bondLabels R) :
    BondWithinRadius (R + 1) p := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.bondWithinRadius_of_mem <;> assumption
theorem bondsAt_fin_two {G : BlockFrame} {j : ℕ} (y : G.Site j) (p q : (Fin 4 → ℤ) × Fin 4) :
    bondsAt y ![p, q] = ![(y + siteOfCoords j p.1, p.2), (y + siteOfCoords j q.1, q.2)] := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AxialSecondOrder.bondsAt_pair <;> assumption
theorem bondsAt_fin_one {G : BlockFrame} {j : ℕ} (y : G.Site j) (p : (Fin 4 → ℤ) × Fin 4) :
    bondsAt y ![p] = ![(y + siteOfCoords j p.1, p.2)] := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.bondsAt_solo <;> assumption
theorem siteSupDist_le_bondSpan {G : BlockFrame} {j k : ℕ} (y : G.Site j) (c : Fin k → G.Site j × Fin 4)
    (l : Fin k) : siteSupDist y (c l).1 ≤ bondSpan y c :=
  le_max_of_le_left (Finset.le_sup (f := fun l : Fin k => siteSupDist y (c l).1) (Finset.mem_univ l))
theorem le_siteSupDist_of_not_mem {G : BlockFrame} {R : ℕ} (hne : ∀ i, G.period G.depth i ≠ 0)
    (y : G.Site G.depth) (b : G.Site G.depth × Fin 4)
    (hb : b ∉ (fun p : (Fin 4 → ℤ) × Fin 4 => ((y + siteOfCoords G.depth p.1 : G.Site G.depth), p.2)) ''
      (bondLabels R : Set _)) :
    R ≤ siteSupDist y b.1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.radius_le_siteSupDist_of_not_mem <;> assumption
theorem bondLabels_injOn {G : BlockFrame} {R : ℕ} (hper : ∀ i, 2 * (R + 1) + 2 < G.period G.depth i)
    (y : G.Site G.depth) :
    Set.InjOn (fun p : (Fin 4 → ℤ) × Fin 4 => ((y + siteOfCoords G.depth p.1 : G.Site G.depth), p.2))
      (bondLabels R : Set _) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.bondLabels_injOn <;> assumption
section site
variable {star : Bool} {a ρ δ₂ κ₂ C σ : ℝ} {Kk : ℕ → ℝ} {m r : ℕ} {V V' : F.GaugeField F.top}
  {Y : F.Cell} {L t n₀ : ℕ} {δ E E₃ : ℝ} {f : LocalFamily}
theorem smallCurvature_mono {j : ℕ} {W : F.GaugeField j} {s s' : ℝ} (h : IsSmallCurvature s W) (hs : s ≤ s') :
    IsSmallCurvature s' W :=
  fun p hp => lt_of_lt_of_le (h p hp) hs
set_option maxHeartbeats 4000000 in
theorem site_derivs_compare (P : AgreeingTops star a ρ δ₂ κ₂ C σ Kk m r F F V V' Y Y) (hTM : TwoMotionsCompare)
    (hFl : FlowBetweenFields)
    (hshort : ∀ u v : imaginaryQuaternions,
      ‖((expUnit u : UnitQuaternion) : ℍ[ℝ]) - ((expUnit v : UnitQuaternion) : ℍ[ℝ])‖ ≤ ‖u - v‖)
    {C₀ K₀ Cp K : ℝ} (hC₀ : 0 ≤ C₀) (hRE : FlowDerivBound C₀) (hCp : 0 ≤ Cp) (hCK : C ≤ K₀)
    (hNP : MotionComponentsBound K₀ Cp)
    (hrow : IsRegularOnTorus L t n₀ σ δ E E₃ f F) (hlow : IsCubicTorusAbove L t n₀ F)
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hE : 0 ≤ E) (hEE : E ≤ E₃) (hL1 : 1 ≤ L) (hK : 0 ≤ K)
    (hT : ∀ b, b ∈ fineBonds F) (hT' : ∀ b, b ∈ fineBonds F)
    (hW : IsSmallCurvature (3 / 4 * σ) (chartedField (frameCoordField star a ρ m V) V))
    (hW' : IsSmallCurvature (3 / 4 * σ) (chartedField (frameCoordField star a ρ m V') V'))
    (hsmall : C * Real.exp (-(δ₂ / 8 * r)) ≤ 1 / 64)
    (e : Fin 2 → (Fin 4 → ℤ) × Fin 4) (he : ∀ l, BondWithinRadius r (e l)) (X : Fin 2 → imaginaryQuaternions)
    (hX : AreUnitVectors X)
    {α : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {α' : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hα : IsFrameMotion star a ρ m V (bondsAt Y e) X α) (hα' : IsFrameMotion star a ρ m V' (bondsAt Y e) X α')
    (hK1 : ∀ l, ∑ b ∈ fineBonds F, ‖motionComponent α ![l] b.1 b.2‖ ≤ K)
    (hK1' : ∀ l, ∑ b ∈ fineBonds F, ‖motionComponent α' ![l] b.1 b.2‖ ≤ K)
    (hK2 : ∑ b ∈ fineBonds F, ‖motionComponent α ![0, 1] b.1 b.2‖ ≤ K)
    (hK2' : ∑ b ∈ fineBonds F, ‖motionComponent α' ![0, 1] b.1 b.2‖ ≤ K)
    (o₀ : Fin 4 → ℤ) (ho₀ : o₀ ∈ centredCube F.blockSide) :
    (∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (Z : Fin k → imaginaryQuaternions), k ≤ 2 →
      (∀ l, BondWithinRadius (L * (r / 4) + 1) (h l)) → AreUnitVectors Z →
      |bondDeriv (subtractTrivial f F (cellCentre F.depth Y + siteOfCoords F.depth o₀))
          (chartedField (frameCoordField star a ρ m V) V)
          (bondsAt (cellCentre F.depth Y + siteOfCoords F.depth o₀) h) Z -
        bondDeriv (subtractTrivial f F (cellCentre F.depth Y + siteOfCoords F.depth o₀))
          (chartedField (frameCoordField star a ρ m V') V')
          (bondsAt (cellCentre F.depth Y + siteOfCoords F.depth o₀) h) Z| ≤
        E / torusDecayFactor L δ ((L * (r / 4) + 1 : ℕ) : ℝ) +
          C₀ * E₃ * (4 * (2 * ((L * (r / 4) + 1 : ℕ) : ℝ) + 1) ^ 4 *
          (2 * (C * σ * Real.exp (-(δ₂ / 8 * r)))))) ∧
    (∀ l : Fin 2, |iteratedFDeriv ℝ 1 (fun τ => subtractTrivial f F (cellCentre F.depth Y + siteOfCoords F.depth o₀)
          (leftTranslate (α τ) (chartedField (frameCoordField star a ρ m V) V))) 0 ![Pi.single l 1] -
        iteratedFDeriv ℝ 1 (fun τ => subtractTrivial f F (cellCentre F.depth Y + siteOfCoords F.depth o₀)
          (leftTranslate (α' τ) (chartedField (frameCoordField star a ρ m V') V'))) 0 ![Pi.single l 1]| ≤
        (E / torusDecayFactor L δ ((L * (r / 4) + 1 : ℕ) : ℝ) +
          C₀ * E₃ * (4 * (2 * ((L * (r / 4) + 1 : ℕ) : ℝ) + 1) ^ 4 *
          (2 * (C * σ * Real.exp (-(δ₂ / 8 * r)))))) * K +
          2 * (E / torusDecayFactor L δ ((L * (r / 4) : ℕ) : ℝ)) * K +
          E * (4 * (2 * ((L * (r / 4) : ℕ) : ℝ) + 1) ^ 4 * (Cp * (C * Real.exp (-(δ₂ / 8 * r)))))) ∧
    |iteratedFDeriv ℝ 2 (fun τ => subtractTrivial f F (cellCentre F.depth Y + siteOfCoords F.depth o₀)
          (leftTranslate (α τ) (chartedField (frameCoordField star a ρ m V) V))) 0
          ![Pi.single 0 1, Pi.single 1 1] -
        iteratedFDeriv ℝ 2 (fun τ => subtractTrivial f F (cellCentre F.depth Y + siteOfCoords F.depth o₀)
          (leftTranslate (α' τ) (chartedField (frameCoordField star a ρ m V') V'))) 0
          ![Pi.single 0 1, Pi.single 1 1]| ≤
      (E / torusDecayFactor L δ ((L * (r / 4) + 1 : ℕ) : ℝ) +
          C₀ * E₃ * (4 * (2 * ((L * (r / 4) + 1 : ℕ) : ℝ) + 1) ^ 4 *
          (2 * (C * σ * Real.exp (-(δ₂ / 8 * r)))))) * (K ^ 2 + K) +
        2 * (E / torusDecayFactor L δ ((L * (r / 4) : ℕ) : ℝ)) * (K ^ 2 + K) +
        E * (2 * K + 1) * (4 * (2 * ((L * (r / 4) : ℕ) : ℝ) + 1) ^ 4 * (Cp * (C * Real.exp (-(δ₂ / 8 * r))))) := by
  classical
  have h16 := P.sixteen_le
  have hFL : F.blockSide = L := hlow.1
  have hFL : F.blockSide = L := hlow.1
  set q : ℕ := r / 4 with hq
  set R : ℕ := L * q with hR
  have hqr : 4 * q ≤ r := by omega
  have hperF : ∀ (G : BlockFrame), G.blockSide = L → (∀ i, 2 * r + 2 < G.extent i) →
      ∀ i, 2 * (R + 1) + 2 < G.period G.depth i := by
    intro G hG hs i
    rw [period_depth, hG]
    have h1 := hs i
    have h2 : (2 * r + 3) * L ≤ G.extent i * L := Nat.mul_le_mul_right _ h1
    have h3 : 4 * R ≤ r * L := by
      rw [hR, mul_comm L q, ← mul_assoc]
      exact Nat.mul_le_mul_right _ hqr
    nlinarith
  have hper := hperF F hFL P.extent_gt
  have hper' := hperF F hFL P.extent_gt'
  set y : F.Site F.depth := cellCentre F.depth Y + siteOfCoords F.depth o₀ with hy
  set y : F.Site F.depth := cellCentre F.depth Y + siteOfCoords F.depth o₀ with hy
  set W := chartedField (frameCoordField star a ρ m V) V with hWdef
  set W' := chartedField (frameCoordField star a ρ m V') V' with hWdef'
  set e₁ := Real.exp (-(δ₂ / 8 * r)) with he₁
  have he₁p : 0 < e₁ := Real.exp_pos _
  set ε := C * σ * e₁ with hεdef
  have hε0 : 0 ≤ ε := mul_nonneg (mul_nonneg P.C_nonneg P.σ_nonneg) he₁p.le
  have hε64 : ε ≤ σ / 64 := by
    have : ε = σ * (C * e₁) := by rw [hεdef]; ring
    rw [this]
    nlinarith
  have hε1 : ε ≤ 1 := by
    have := P.σ_le_one
    linarith
  have ho₀' : o₀ ∈ centredCube F.blockSide := by rw [P.blockSide_eq]; exact ho₀
  have hL2 := P.two_le_blockSide
  have hlab : ∀ g : Fin 4 → ℤ, WithinRadius (R + 1) g → WithinRadius (q + 3) (cellIndex F.blockSide (o₀ + g)) := by
    intro g hg
    refine cellIndex_withinRadius P.odd hL2 ho₀ ?_
    rw [hFL]
    exact hg
  have hsite : ∀ g : Fin 4 → ℤ, (y + siteOfCoords F.depth g : F.Site F.depth) =
      cellCentre F.depth (Y + siteOfCoords F.top (cellIndex F.blockSide (o₀ + g))) +
        siteOfCoords F.depth (cellRemainder F.blockSide (o₀ + g)) := fun g => site_eq_cellCentre_add Y o₀ g
  have hgap : ∀ (g : Fin 4 → ℤ) (i : Fin 4), WithinRadius (R + 1) g →
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W' (y + siteOfCoords F.depth g) i * (W (y + siteOfCoords F.depth g) i)⁻¹) ≤ ε := by
    intro g i hg
    rw [hsite g]
    exact distFromOne_le P hshort _ _ i (cellRemainder_mem_centredCube P.odd _) (hlab g hg)
  obtain ⟨B, hBc, hBa, hBs⟩ := hFl F F (fineBonds F) W W' y y (R + 1) ε (3 / 4 * σ) σ hT hper hper' hε0 hε1 hW
    (by nlinarith) hgap
  have hW'σ : IsSmallCurvature σ W' := smallCurvature_mono hW' (by linarith)
  have hWσ : IsSmallCurvature σ W := smallCurvature_mono hW (by linarith)
  have hE₃ : 0 ≤ E₃ := hE.trans hEE
  have hnear : ∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (Z : Fin k → imaginaryQuaternions), k ≤ 2 →
      (∀ l, BondWithinRadius (R + 1) (h l)) → AreUnitVectors Z →
      |bondDeriv (subtractTrivial f F y) W (bondsAt y h) Z - bondDeriv (subtractTrivial f F y) W' (bondsAt y h) Z| ≤
        E / torusDecayFactor L δ ((R + 1 : ℕ) : ℝ) + C₀ * E₃ * (4 * (2 * ((R + 1 : ℕ) : ℝ) + 1) ^ 4 * (2 * ε)) := by
    intro k h Z hk hb hZ
    refine (hRE L t n₀ σ δ E E₃ f F (fineBonds F) y W W' B (R + 1) k h Z hrow hlow hδ hE hEE hT hBc hW'σ hBa
      hk hb hZ).trans ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hBs (mul_nonneg hC₀ hE₃))
  refine ⟨hnear, ?_⟩
  set ι : (Fin 4 → ℤ) × Fin 4 → F.Site F.depth × Fin 4 :=
    fun p => ((y + siteOfCoords F.depth p.1 : F.Site F.depth), p.2) with hι
  set ι : (Fin 4 → ℤ) × Fin 4 → F.Site F.depth × Fin 4 :=
    fun p => ((y + siteOfCoords F.depth p.1 : F.Site F.depth), p.2) with hι
  have hinj : Set.InjOn ι (bondLabels R : Set _) := bondLabels_injOn hper y
  have hinj' : Set.InjOn ι (bondLabels R : Set _) := bondLabels_injOn hper' y
  have hne : ∀ i, F.period F.depth i ≠ 0 := fun i => by have := hper i; omega
  have hne' : ∀ i, F.period F.depth i ≠ 0 := fun i => by have := hper' i; omega
  have hdec : ∀ (z : F.Site F.depth) (U : F.GaugeField F.depth) (_ : IsSmallCurvature σ U)
      (k : ℕ) (c : Fin k → F.Site F.depth × Fin 4) (Z : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 2 →
      AreUnitVectors Z →
      |bondDeriv (subtractTrivial f F z) U c Z| ≤ E / torusDecayFactor L δ (bondSpan z c) := by
    intro z U hU k c Z hk1 hk2 hZ
    have e1 : bondDeriv (subtractTrivial f F z) U c Z = bondDeriv (f F z) U c Z :=
      bondDeriv_sub_const (f F z) _ U c Z hk1
    rw [e1]
    have h1 := hrow.decay hlow z U k c Z hU hk1 (by omega) hZ
    rwa [if_neg (by omega)] at h1
  have hsizeE : ∀ (z : F.Site F.depth) (U : F.GaugeField F.depth) (_ : IsSmallCurvature σ U)
      (k : ℕ) (c : Fin k → F.Site F.depth × Fin 4) (Z : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 2 →
      AreUnitVectors Z → |bondDeriv (subtractTrivial f F z) U c Z| ≤ E := by
    intro z U hU k c Z hk1 hk2 hZ
    exact (hdec z U hU k c Z hk1 hk2 hZ).trans (div_le_self hE (one_le_torusDecayFactor L hδ (Nat.cast_nonneg _)))
  have hfarE : ∀ (z : F.Site F.depth) (U : F.GaugeField F.depth) (_ : IsSmallCurvature σ U)
      (k : ℕ) (c : Fin k → F.Site F.depth × Fin 4) (Z : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 2 →
      AreUnitVectors Z → R ≤ bondSpan z c →
      |bondDeriv (subtractTrivial f F z) U c Z| ≤ E / torusDecayFactor L δ (R : ℝ) := by
    intro z U hU k c Z hk1 hk2 hZ hs
    refine (hdec z U hU k c Z hk1 hk2 hZ).trans ?_
    exact div_le_div_of_nonneg_left hE (torusDecayFactor_pos _ _ _)
      (torusDecayFactor_mono hL1 hδ (Nat.cast_nonneg _) (by exact_mod_cast hs))
  have hu1 : ∀ U : imaginaryQuaternions, ‖U‖ = 1 → AreUnitVectors ![U] := fun U hU l => by
    fin_cases l
    exact hU
  have hu2 : ∀ U U' : imaginaryQuaternions, ‖U‖ = 1 → ‖U'‖ = 1 → AreUnitVectors ![U, U'] := fun U U' hU hU' l => by
    fin_cases l
    · exact hU
    · exact hU'
  have hEC : DerivativesCompare (subtractTrivial f F y) (subtractTrivial f F y) W W' (bondLabels R) ι ι
      (E / torusDecayFactor L δ ((R + 1 : ℕ) : ℝ) + C₀ * E₃ * (4 * (2 * ((R + 1 : ℕ) : ℝ) + 1) ^ 4 * (2 * ε)))
      (E / torusDecayFactor L δ (R : ℝ)) E := by
    refine ⟨fun p Z hp hZ => ?_, fun p p' Z Z' hp hp' hZ hZ' => ?_, fun b Z hb hZ => ?_, fun b Z hb hZ => ?_,
      fun b b' Z Z' hb hZ hZ' => ?_, fun b b' Z Z' hb hZ hZ' => ?_, fun b Z hZ => ?_, fun b b' Z Z' hZ hZ' => ?_⟩
    · have h1 := hnear 1 ![p] ![Z] (by norm_num)
        (by intro l; fin_cases l; exact bondWithinRadius_of_mem hp) (hu1 Z hZ)
      rwa [bondsAt_fin_one] at h1
    · have h1 := hnear 2 ![p, p'] ![Z, Z'] (by norm_num)
        (by intro l; fin_cases l; exacts [bondWithinRadius_of_mem hp, bondWithinRadius_of_mem hp'])
        (hu2 Z Z' hZ hZ')
      rwa [bondsAt_fin_two] at h1
    · exact hfarE y W hWσ 1 _ _ le_rfl (by norm_num) (hu1 Z hZ)
        ((le_siteSupDist_of_not_mem hne y b hb).trans (siteSupDist_le_bondSpan y ![b] 0))
    · exact hfarE y W' hW'σ 1 _ _ le_rfl (by norm_num) (hu1 Z hZ)
        ((le_siteSupDist_of_not_mem hne' y b hb).trans (siteSupDist_le_bondSpan y ![b] 0))
    · refine hfarE y W hWσ 2 _ _ (by norm_num) (by norm_num) (hu2 Z Z' hZ hZ') ?_
      rcases hb with h | h
      · exact (le_siteSupDist_of_not_mem hne y b h).trans (siteSupDist_le_bondSpan y ![b, b'] 0)
      · exact (le_siteSupDist_of_not_mem hne y b' h).trans (siteSupDist_le_bondSpan y ![b, b'] 1)
    · refine hfarE y W' hW'σ 2 _ _ (by norm_num) (by norm_num) (hu2 Z Z' hZ hZ') ?_
      rcases hb with h | h
      · exact (le_siteSupDist_of_not_mem hne' y b h).trans (siteSupDist_le_bondSpan y ![b, b'] 0)
      · exact (le_siteSupDist_of_not_mem hne' y b' h).trans (siteSupDist_le_bondSpan y ![b, b'] 1)
    · exact hsizeE y W' hW'σ 1 _ _ le_rfl (by norm_num) (hu1 Z hZ)
    · exact hsizeE y W' hW'σ 2 _ _ (by norm_num) (by norm_num) (hu2 Z Z' hZ hZ')
  have hpn := fun (p : (Fin 4 → ℤ) × Fin 4) (hp : p ∈ bondLabels R) =>
    motionComponents_near P hCp hCK hNP e he X hX hα hα' (cellIndex F.blockSide (o₀ + p.1))
      (cellRemainder F.blockSide (o₀ + p.1)) p.2 (cellRemainder_mem_centredCube P.odd _)
      (hlab p.1 (fun l => ((mem_bondLabels.1 hp) l).trans (by push_cast; linarith)))
  have hμ1 : ∀ l, ∑ p ∈ bondLabels R,
      ‖motionComponent α ![l] (ι p).1 (ι p).2 - motionComponent α' ![l] (ι p).1 (ι p).2‖ ≤
      4 * (2 * (R : ℝ) + 1) ^ 4 * (Cp * (C * e₁)) := by
    intro l
    refine (Finset.sum_le_card_nsmul _ _ (Cp * (C * e₁)) fun p hp => ?_).trans ?_
    · show ‖motionComponent α ![l] (y + siteOfCoords F.depth p.1) p.2 -
        motionComponent α' ![l] (y + siteOfCoords F.depth p.1) p.2‖ ≤ _
      rw [hsite p.1]
      exact (hpn p hp).1 l
    · rw [nsmul_eq_mul, card_bondLabels]
  have hμ2 : ∑ p ∈ bondLabels R,
      ‖motionComponent α ![0, 1] (ι p).1 (ι p).2 - motionComponent α' ![0, 1] (ι p).1 (ι p).2‖ ≤
      4 * (2 * (R : ℝ) + 1) ^ 4 * (Cp * (C * e₁)) := by
    refine (Finset.sum_le_card_nsmul _ _ (Cp * (C * e₁)) fun p hp => ?_).trans ?_
    · show ‖motionComponent α ![0, 1] (y + siteOfCoords F.depth p.1) p.2 -
        motionComponent α' ![0, 1] (y + siteOfCoords F.depth p.1) p.2‖ ≤ _
      rw [hsite p.1]
      exact (hpn p hp).2
    · rw [nsmul_eq_mul, card_bondLabels]
  have hsm : ContDiffThreeAlongBonds (subtractTrivial f F y) W := fun k c Z =>
    (hrow.smooth hlow y W hWσ k c Z).sub contDiffAt_const
  have hsm' : ContDiffThreeAlongBonds (subtractTrivial f F y) W' := fun k c Z =>
    (hrow.smooth hlow y W' hW'σ k c Z).sub contDiffAt_const
  have hCe0 : 0 ≤ C * e₁ := mul_nonneg P.C_nonneg he₁p.le
  have hμ0 : 0 ≤ 4 * (2 * (R : ℝ) + 1) ^ 4 * (Cp * (C * e₁)) := by positivity
  have hε₁0 : 0 ≤ E / torusDecayFactor L δ ((R + 1 : ℕ) : ℝ) +
      C₀ * E₃ * (4 * (2 * ((R + 1 : ℕ) : ℝ) + 1) ^ 4 * (2 * ε)) :=
    add_nonneg (div_nonneg hE (torusDecayFactor_pos _ _ _).le) (by positivity)
  have hε₂0 : 0 ≤ E / torusDecayFactor L δ (R : ℝ) := div_nonneg hE (torusDecayFactor_pos _ _ _).le
  exact hTM F F F.depth F.depth ((Fin 4 → ℤ) × Fin 4) (fineBonds F) (fineBonds F) (subtractTrivial f F y)
    (subtractTrivial f F y) W W' (bondLabels R) ι ι _ _ E K _ α α' hT hT' hinj hinj' hsm hsm' hε₁0 hε₂0 hE hK hμ0
    hEC hα.at_zero hα'.at_zero hα.contDiffAt hα'.contDiffAt hK1 hK1' hK2 hK2' hμ1 hμ2
end site
def MotionAboveFrameBound (K M : ℕ → ℝ) : Prop :=
  ∀ (F : BlockFrame) (s a ρA r : ℝ) (m p : ℕ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F))
      (w : Fin p → Perturbation F),
      (∀ i, F.period F.depth i ≠ 0) → 0 ≤ r → (∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F)) →
      (∀ x i, ¬ IsAxialTreeBond (x, i) → ‖interpolatedCoords s a ρA m V η x i‖ ≤ 1) →
      (∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (interpolatedFrame s a ρA m d) V) →
      (∀ d ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4)
        (X' : Fin k → imaginaryQuaternions),
        1 ≤ k → AreUnitVectors X' →
        ‖bondDeriv (interpolatedFrame s a ρA m d) V c' X'‖ ≤
          K k * Real.exp (-(r * bondListDistance (enclosingCell d.1) c'))) →
      (∀ l, (w l).IsUnit) →
      ∃ α : (Fin p → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ x i, α 0 x i = 0) ∧
        (∀ x i, ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ => α τ x i) 0) ∧
        (∀ x i, IsAxialTreeBond (x, i) → ∀ τ, α τ x i = 0) ∧
        (∀ᶠ τ in 𝓝 0, interpolatedField s a ρA m (perturbedTop V w τ) (perturbedVariable η w τ) =
          leftTranslate (α τ) (interpolatedField s a ρA m V η)) ∧
        (∀ (q : ℕ) (e : Fin q → Fin p) (x : F.Site F.depth) (i : Fin 4) (l : Fin q), q ≤ 3 →
          ‖motionComponent α e x i‖ ≤ M q * (w (e l)).decayWeight r x i) ∧
        ∀ (l : Fin p) (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (x : F.Site F.depth) (i : Fin 4), 1 ≤ 3 →
          w l = .top c X → ¬ IsAxialTreeBond (x, i) →
          ‖motionComponent α (fun _ : Fin 1 => l) x i - bondResponse s a ρA m V c X x i‖ ≤
            M 0 * ‖interpolatedCoords s a ρA m V η x i‖
theorem exists_frameMotion {star : Bool} {a ρ δ₂ κ₂ C σ : ℝ} {Kk K M : ℕ → ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (hm : MotionAboveFrameBound K M) (hends : interpolationAtEndpoints) (hK : ∀ k, 16 ^ k * Kk k ≤ K k)
    (hκ : 0 ≤ κ₂) (hρ1 : ρ ≤ 1) (hσ0 : 0 ≤ σ) (hper : ∀ i, F.period F.depth i ≠ 0)
    (hch : ∀ d : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F))
    (hs : FrameSmallness star a ρ δ₂ κ₂ C σ Kk m V) (c : Fin 2 → F.Site F.top × Fin 4)
    (X : Fin 2 → imaginaryQuaternions) (hX : AreUnitVectors X) :
    ∃ α : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions, IsFrameMotion star a ρ m V c X α ∧
      ∀ (q : ℕ) (e : Fin q → Fin 2) (x : F.Site F.depth) (i : Fin 4) (l : Fin q), q ≤ 3 →
        ‖motionComponent α e x i‖ ≤ M q * Real.exp (-(κ₂ * cellSupDist (enclosingCell x) (c (e l)).1)) := by
  have hE : ∀ V' : F.GaugeField F.top,
      (∀ b, interpolatedFrame (segmentEnd star) a ρ m b V' = stepFrame star a ρ m b V') ∧
      (∀ η', interpolatedCoords (segmentEnd star) a ρ m V' η' = coordsAboveFrame star a ρ m V' η') ∧
      (∀ η', interpolatedField (segmentEnd star) a ρ m V' η' = fieldAboveFrame star a ρ m V' η') := fun V' => by
    obtain ⟨h1, h2, h3, -⟩ := hends F star a ρ 0 0 0 m V'
    exact ⟨h1, h2, h3⟩
  have hfb : ∀ d : F.Site F.depth × Fin 4, interpolatedFrame (segmentEnd star) a ρ m d = stepFrame star a ρ m d :=
    fun d => funext fun V' => (hE V').1 d
  obtain ⟨α, h0, hc, htree, hid, hp, -⟩ := hm F (segmentEnd star) a ρ κ₂ m 2 V 0
    (fun l => Perturbation.top (c l) (X l)) hper hκ hch
    (fun x i ht => by
      rw [(hE V).2.1]
      have e : coordsAboveFrame star a ρ m V 0 x i = stepFrame star a ρ m (x, i) V := by
        simp [coordsAboveFrame, stepCoordinates_zero]
      rw [e]
      have := hs.norm_add_le _ (hch _ ht)
      linarith)
    (fun d hd => by rw [hfb]; exact hs.analytic d hd)
    (fun d hd k c' X' hk hX' => by
      rw [hfb]
      exact (hs.deriv_bound d hd k c' X' hk hX').trans (mul_le_mul_of_nonneg_right (hK k) (Real.exp_pos _).le))
    (fun l => hX l)
  refine ⟨α, ⟨h0, hc, htree, hid.mono fun τ h => ?_⟩, fun q e x i l hq => hp q e x i l hq⟩
  have h1 : perturbedVariable (0 : StepVariable (finiteCells F)) (fun l => Perturbation.top (c l) (X l)) τ = 0 := by
    simp [perturbedVariable, Perturbation.variableDirection]
  have h2 : perturbedTop V (fun l => Perturbation.top (c l) (X l)) τ = leftTranslate (bondSpread c X τ) V := rfl
  rw [h1, h2, (hE _).2.2, (hE V).2.2, fieldAboveFrame_zero, fieldAboveFrame_zero] at h
  exact h
open Classical in
theorem abs_sum_cell_sites_sub_le {G G' : BlockFrame} (hL : Odd G.blockSide) (hs : ∀ i, 2 ≤ G.extent i)
    (hL' : Odd G'.blockSide) (hs' : ∀ i, 2 ≤ G'.extent i)
    (hLL : G'.blockSide = G.blockSide) (Y : G.Cell) (Y' : G'.Cell) (d : G.Site G.depth → ℝ)
    (d' : G'.Site G'.depth → ℝ) {Q : ℝ}
    (h : ∀ o ∈ centredCube G.blockSide,
      |d (cellCentre G.depth Y + siteOfCoords G.depth o) - d' (cellCentre G'.depth Y' + siteOfCoords G'.depth o)| ≤ Q) :
    |∑ y ∈ (sitesOfCells (finiteCells G) G.depth).filter (fun y => enclosingCell y = Y), d y -
      ∑ y ∈ (sitesOfCells (finiteCells G') G'.depth).filter (fun y => enclosingCell y = Y'), d' y| ≤
        (G.blockSide : ℝ) ^ 4 * Q := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.abs_sum_block_sub_le <;> assumption
theorem final_bound_le {E η K Cp C Ct C₀ σ D₀ D₁ Rr e₁ : ℝ} (hE : 0 ≤ E) (hη : 0 < η) (hη1 : η ≤ 1)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hC : 0 ≤ C) (hCt : C ≤ Ct) (hC₀ : 0 ≤ C₀) (hCp : 0 ≤ Cp) (hK : 1 ≤ K)
    (hD₀ : 0 < D₀) (hD : D₀ ≤ D₁) (hR : 0 ≤ Rr) (he : 0 < e₁) :
    (E / D₁ + C₀ * (E / η) * (4 * (2 * (Rr + 1) + 1) ^ 4 * (2 * (C * σ * e₁)))) * (K ^ 2 + K) +
        2 * (E / D₀) * (K ^ 2 + K) + E * (2 * K + 1) * (4 * (2 * Rr + 1) ^ 4 * (Cp * (C * e₁))) ≤
      E * ((3 * (K ^ 2 + K) + 8 * (K ^ 2 + K) * C₀ * Ct + 4 * (2 * K + 1) * Cp * Ct) *
        (1 / D₀ + (1 / η) * (2 * Rr + 5) ^ 4 * e₁)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.final_bound <;> assumption
theorem final_bound_mono {E η K Cp C C₀ σ D₀ D₁ Rr e₁ : ℝ} (hE : 0 ≤ E) (hη : 0 < η) (hσ0 : 0 ≤ σ)
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hCp : 0 ≤ Cp) (hK : 1 ≤ K) (hD₀ : 0 < D₀) (hD : D₀ ≤ D₁) (hR : 0 ≤ Rr)
    (he : 0 < e₁) :
    (E / D₁ + C₀ * (E / η) * (4 * (2 * (Rr + 1) + 1) ^ 4 * (2 * (C * σ * e₁)))) ≤
        (E / D₁ + C₀ * (E / η) * (4 * (2 * (Rr + 1) + 1) ^ 4 * (2 * (C * σ * e₁)))) * (K ^ 2 + K) +
        2 * (E / D₀) * (K ^ 2 + K) + E * (2 * K + 1) * (4 * (2 * Rr + 1) ^ 4 * (Cp * (C * e₁))) ∧
    (E / D₁ + C₀ * (E / η) * (4 * (2 * (Rr + 1) + 1) ^ 4 * (2 * (C * σ * e₁)))) * K + 2 * (E / D₀) * K +
        E * (4 * (2 * Rr + 1) ^ 4 * (Cp * (C * e₁))) ≤
      (E / D₁ + C₀ * (E / η) * (4 * (2 * (Rr + 1) + 1) ^ 4 * (2 * (C * σ * e₁)))) * (K ^ 2 + K) +
        2 * (E / D₀) * (K ^ 2 + K) + E * (2 * K + 1) * (4 * (2 * Rr + 1) ^ 4 * (Cp * (C * e₁))) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.final_bound_mono <;> assumption
def motionSumBound (Mc : ℕ → ℝ) (Cg : ℝ) (L : ℕ) : ℝ := max 1 ((|Mc 1| + |Mc 2|) * (|Cg| * (L : ℝ) ^ 4))
def localityConstant (C₀ Cp Ct K : ℝ) : ℝ :=
  3 * (K ^ 2 + K) + 8 * (K ^ 2 + K) * C₀ * Ct + 4 * (2 * K + 1) * Cp * Ct
theorem exists_norm_eq_one : ∃ U : imaginaryQuaternions, ‖U‖ = 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSecondDeriv.exists_norm_eq_one <;> assumption
theorem bondDeriv_fin_zero {j : ℕ} (G : F.GaugeField j → ℝ) (U : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4)
    (Z : Fin 0 → imaginaryQuaternions) :
    bondDeriv G U c Z = G U := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
theorem fderiv_line {E P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup P]
    [NormedSpace ℝ P] (φ : P → E) (v : P) (h : DifferentiableAt ℝ φ 0) :
    fderiv ℝ (fun s : Fin 1 → ℝ => φ (s 0 • v)) 0 (Pi.single 0 1) = fderiv ℝ φ 0 v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.fderiv_line <;> assumption
theorem bondSpread_smul_single {j : ℕ} (c : Fin 2 → F.Site j × Fin 4) (X : Fin 2 → imaginaryQuaternions)
    (l : Fin 2) (s : Fin 1 → ℝ) :
    bondSpread c X (s 0 • Pi.single l 1) = bondSpread ![c l] ![X l] s := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearMotionComponents.bondSpread_smul_single <;> assumption
section standingConstraints
variable {star : Bool} {a ρ : ℝ} {m : ℕ} {V : F.GaugeField F.top} {f : LocalFamily}
  {c : Fin 2 → F.Site F.top × Fin 4} {X : Fin 2 → imaginaryQuaternions}
  {α : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions}
theorem centredExpansion_eventuallyEq (hα : IsFrameMotion star a ρ m V c X α) (y : F.Site F.depth) :
    (fun τ => centredExpansion star a ρ m f y 0 (leftTranslate (bondSpread c X τ) V)) =ᶠ[𝓝 0]
      fun τ => subtractTrivial f F y (leftTranslate (α τ) (chartedField (frameCoordField star a ρ m V) V)) := by
  filter_upwards [hα.eventually_eq] with τ h
  show subtractTrivial f F y (fieldAboveFrame star a ρ m _ 0) = _
  rw [fieldAboveFrame_zero, h]
theorem centredExpansion_contDiffAt (hSm : SmoothAlongMotion) (hα : IsFrameMotion star a ρ m V c X α)
    (hper : ∀ i, F.period F.depth i ≠ 0) (y : F.Site F.depth)
    (hG : ContDiffThreeAlongBonds (subtractTrivial f F y) (chartedField (frameCoordField star a ρ m V) V)) :
    ContDiffAt ℝ 3 (fun τ => centredExpansion star a ρ m f y 0 (leftTranslate (bondSpread c X τ) V)) 0 := by
  have h1 := hSm F F.depth 3 2 (subtractTrivial f F y) (chartedField (frameCoordField star a ρ m V) V) α hper
    (fun q c' X' => hG q c' X') hα.contDiffAt hα.at_zero
  exact h1.congr_of_eventuallyEq (centredExpansion_eventuallyEq hα y)
open Classical in
theorem bondDeriv_cellCentredExpansion_two (hSm : SmoothAlongMotion) (hα : IsFrameMotion star a ρ m V c X α)
    (hper : ∀ i, F.period F.depth i ≠ 0) (Y : F.Cell)
    (hG : ∀ y, ContDiffThreeAlongBonds (subtractTrivial f F y) (chartedField (frameCoordField star a ρ m V) V)) :
    bondDeriv (cellCentredExpansion star a ρ m f Y 0) V c X =
      ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
        iteratedFDeriv ℝ 2 (fun τ => subtractTrivial f F y
          (leftTranslate (α τ) (chartedField (frameCoordField star a ρ m V) V))) 0
          ![Pi.single 0 1, Pi.single 1 1] := by
  have hs : ∀ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
      ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞)
      (fun τ : Fin 2 → ℝ => centredExpansion star a ρ m f y 0 (leftTranslate (bondSpread c X τ) V)) 0 :=
    fun y _ => (centredExpansion_contDiffAt hSm hα hper y (hG y)).of_le (by norm_num)
  have h1 := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := 2) (x := (0 : Fin 2 → ℝ))
    (u := (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y))
    (f := fun y (τ : Fin 2 → ℝ) => centredExpansion star a ρ m f y 0 (leftTranslate (bondSpread c X τ) V)) hs
  have e3 : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![Pi.single 0 1, Pi.single 1 1] := by
    funext l
    fin_cases l <;> rfl
  unfold bondDeriv cellCentredExpansion
  rw [h1, e3, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ (centredExpansion_eventuallyEq hα y) 2).eq_of_nhds]
open Classical in
theorem bondDeriv_cellCentredExpansion_one (hSm : SmoothAlongMotion) (hα : IsFrameMotion star a ρ m V c X α)
    (hper : ∀ i, F.period F.depth i ≠ 0) (Y : F.Cell) (l : Fin 2)
    (hG : ∀ y, ContDiffThreeAlongBonds (subtractTrivial f F y) (chartedField (frameCoordField star a ρ m V) V)) :
    bondDeriv (cellCentredExpansion star a ρ m f Y 0) V ![c l] ![X l] =
      ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
        iteratedFDeriv ℝ 1 (fun τ => subtractTrivial f F y
          (leftTranslate (α τ) (chartedField (frameCoordField star a ρ m V) V))) 0
          ![Pi.single l 1] := by
  have hline : ∀ y, (fun s : Fin 1 → ℝ => centredExpansion star a ρ m f y 0
      (leftTranslate (bondSpread ![c l] ![X l] s) V)) =
      fun s : Fin 1 → ℝ => (fun τ : Fin 2 → ℝ => centredExpansion star a ρ m f y 0
        (leftTranslate (bondSpread c X τ) V)) (s 0 • Pi.single l 1) := by
    intro y
    funext s
    show _ = centredExpansion star a ρ m f y 0 (leftTranslate (bondSpread c X (s 0 • Pi.single l 1)) V)
    rw [bondSpread_smul_single]
  have hs : ∀ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
      ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun s : Fin 1 → ℝ => centredExpansion star a ρ m f y 0 (leftTranslate (bondSpread ![c l] ![X l] s) V)) 0 := by
    intro y _
    rw [hline y]
    let ι : (Fin 1 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight (Pi.single l 1)
    have h0 : ContDiffAt ℝ 1 (fun τ : Fin 2 → ℝ => centredExpansion star a ρ m f y 0
        (leftTranslate (bondSpread c X τ) V)) (ι 0) := by
      rw [map_zero]
      exact (centredExpansion_contDiffAt hSm hα hper y (hG y)).of_le (by norm_num)
    exact h0.comp (0 : Fin 1 → ℝ) ι.contDiff.contDiffAt
  have h1 := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := 1) (x := (0 : Fin 1 → ℝ))
    (u := (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y))
    (f := fun y (s : Fin 1 → ℝ) => centredExpansion star a ρ m f y 0 (leftTranslate (bondSpread ![c l] ![X l] s) V)) hs
  unfold bondDeriv cellCentredExpansion
  rw [h1, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hd : DifferentiableAt ℝ (fun τ : Fin 2 → ℝ => centredExpansion star a ρ m f y 0
      (leftTranslate (bondSpread c X τ) V)) 0 :=
    (centredExpansion_contDiffAt hSm hα hper y (hG y)).differentiableAt (by norm_num)
  have e1 : iteratedFDeriv ℝ 1 (fun s : Fin 1 → ℝ => centredExpansion star a ρ m f y 0
      (leftTranslate (bondSpread ![c l] ![X l] s) V)) 0 (fun l' => Pi.single l' 1) =
      fderiv ℝ (fun s : Fin 1 → ℝ => centredExpansion star a ρ m f y 0
        (leftTranslate (bondSpread ![c l] ![X l] s) V)) 0 (Pi.single 0 1) :=
    iteratedFDeriv_one_apply _
  rw [e1, hline y, fderiv_line _ _ hd, iteratedFDeriv_one_apply, (centredExpansion_eventuallyEq hα y).fderiv_eq]
  rfl
end standingConstraints
theorem sum_le_of_exp_decay {κ₂ Cg Mq : ℝ} {Y₀ : F.Cell}
    (hCg : ∑ b ∈ fineBonds F, Real.exp (-(κ₂ * cellSupDist (enclosingCell b.1) (Y₀ : F.Cell))) ≤
      Cg * (F.blockSide : ℝ) ^ 4)
    (g : F.Site F.depth × Fin 4 → ℝ)
    (hg : ∀ b, g b ≤ Mq * Real.exp (-(κ₂ * cellSupDist (enclosingCell b.1) (Y₀ : F.Cell)))) :
    ∑ b ∈ fineBonds F, g b ≤ |Mq| * (|Cg| * (F.blockSide : ℝ) ^ 4) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.sum_fineBonds_le <;> assumption
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem frameFamilyLocalAt_of (hTM : TwoMotionsCompare) (hFl : FlowBetweenFields)
    (hshort : ∀ u v : imaginaryQuaternions,
      ‖((expUnit u : UnitQuaternion) : ℍ[ℝ]) - ((expUnit v : UnitQuaternion) : ℍ[ℝ])‖ ≤ ‖u - v‖)
    (hS : SiteDecomposition) (hends : interpolationAtEndpoints) (hSm : SmoothAlongMotion) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hRE : FlowDerivBound C₀) (Mf : ColdChainParameters → ℕ → ℝ)
    (hMf : ∀ c : ColdChainParameters, MotionAboveFrameBound (fun k => |16 ^ k * c.Kk k|) (Mf c))
    (Cgf : ColdChainParameters → ℝ)
    (hCg : ∀ c : ColdChainParameters, 0 < c.κ₂ → ∀ G : BlockFrame, Odd G.blockSide → IsLargeCubicTorus G →
      ∀ z : G.Cell,
      ∑ b ∈ fineBonds G, Real.exp (-(c.κ₂ * cellSupDist (enclosingCell b.1) z)) ≤ Cgf c * (G.blockSide : ℝ) ^ 4)
    (Cpf : ℝ → ℝ) (hCp : ∀ Ct : ℝ, 0 ≤ Ct → 0 ≤ Cpf Ct ∧ MotionComponentsBound (Ct + 1) (Cpf Ct))
    (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hd : T.IsOrdered)
    (hP : FrameBoundsForParameters T ∧
      LocalExpansionParametersAt (fun _ L c Ct => localityConstant C₀ (Cpf Ct) Ct (motionSumBound (Mf c) (Cgf c) L)) T) :
    frameFamilyLocalAt T := by
  obtain ⟨⟨Cf, C, hCf, hC1, hCfC, hCC, hL40, h64, hκ1, hσ1, hc1, hc2, hσA, hy1, hay, hFH⟩, hl⟩ := hP
  intro t x f F V hx hrow hF hV star V' Y r k h X hV' hag hr hk hb hX
  classical
  obtain ⟨h16, hCt1, htail⟩ := hl r hr
  obtain ⟨hFL, hFt, n, hside, hn⟩ := id hF
  obtain ⟨hFL, hFt, n', hside', hn'⟩ := id hF
  have hodd : Odd T.L := hd.odd_L
  have hoddF : Odd F.blockSide := by rw [hFL]; exact hodd
  have hoddF : Odd F.blockSide := by rw [hFL]; exact hodd
  have hLL : F.blockSide = F.blockSide := rfl
  have hL1 : 1 ≤ T.L := hodd.pos
  have hL2 : 2 ≤ F.blockSide := by
    rw [hFL]
    have : (2 : ℕ) ^ 40 ≤ T.L := hL40
    have h2 : (2 : ℕ) ≤ 2 ^ 40 := by norm_num
    omega
  have hsd : ∀ i, 2 * r + 2 < F.extent i := fun i => (hag.1 i).resolve_left (by rw [hside i]; omega)
  have hsd' : ∀ i, 2 * r + 2 < F.extent i := fun i => (hag.2.1 i).resolve_left (by rw [hside' i]; omega)
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by have := hsd i; omega
  have hs2' : ∀ i, 2 ≤ F.extent i := fun i => by have := hsd' i; omega
  have hcub : IsLargeCubicTorus F := ⟨n, by omega, hside⟩
  have hcub' : IsLargeCubicTorus F := ⟨n', by omega, hside'⟩
  have hlow : IsCubicTorusAbove T.L t T.n₀ F := ⟨hFL, hFt, n, hside, hn.trans (Nat.le_mul_of_pos_right n hL1)⟩
  have hlow : IsCubicTorusAbove T.L t T.n₀ F := ⟨hFL, hFt, n', hside', hn'.trans (Nat.le_mul_of_pos_right n' hL1)⟩
  have hcov : ∀ {G : BlockFrame}, Odd G.blockSide → (∀ i, 2 ≤ G.extent i) →
      ∀ x : G.Site G.depth, x ∈ sitesOfCells (finiteCells G) G.depth := by
    intro G hGo hGs x
    obtain ⟨-, h2, -⟩ := hS G hGo hGs
    obtain ⟨e, hcu⟩ := h2 x
    refine mem_sitesOfCells.2 ⟨enclosingCell x, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_finiteCells hGs _, cellOffset x, ?_, e.symm⟩
    rw [top_sub_depth, pow_one]
    exact hcu
  have hT : ∀ b : F.Site F.depth × Fin 4, b ∈ fineBonds F := fun b =>
    Finset.mem_product.2 ⟨hcov hoddF hs2 _, Finset.mem_univ _⟩
  have hT' : ∀ b : F.Site F.depth × Fin 4, b ∈ fineBonds F := fun b =>
    Finset.mem_product.2 ⟨hcov hoddF hs2' _, Finset.mem_univ _⟩
  have hch : ∀ d : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d hd' =>
    Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hcov hoddF hs2 _, Finset.mem_univ _⟩,
      hcov hoddF hs2 _⟩, hd'⟩
  have hch' : ∀ d : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d hd' =>
    Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hcov hoddF hs2' _, Finset.mem_univ _⟩,
      hcov hoddF hs2' _⟩, hd'⟩
  have hperT : ∀ {G : BlockFrame}, (∀ i, 2 ≤ G.extent i) → 1 ≤ G.blockSide → ∀ i, G.period G.depth i ≠ 0 := by
    intro G hGs hGL i
    rw [period_depth]
    have := hGs i
    exact Nat.mul_ne_zero (by omega) (by omega)
  have hper := hperT hs2 (by rw [hFL]; exact hL1)
  have hper' := hperT hs2' (by rw [hFL]; exact hL1)
  have hchain := hd.chain_admissible
  obtain ⟨⟨hρ0, hρ1, -, hδ₂, hκ₂, -, -, -⟩, -⟩ := hchain.classical
  have hκ₂p : 0 < T.chainParams.κ₂ := by
    have : 0 < (2 : ℝ) ^ 6 * T.chainParams.δ₂ := by positivity
    linarith
  have hσ : 0 < T.σ := hd.σ_pos
  have hE : 0 ≤ T.E := by linarith [hd.one_le_E]
  have hη : 0 < T.η₃ := hd.η₃_pos
  have hη1 : T.η₃ ≤ 1 := hd.η₃_le_one
  have hδ : 0 ≤ T.decayRate := (div_pos hd.κ_pos (by norm_num)).le
  have hEE : T.E ≤ T.energyRatio := by
    show T.E ≤ T.E / T.η₃
    rw [le_div_iff₀ hη]
    nlinarith
  have fh := hFH t x F V hx hF hV
  have fh' := hFH t x F V' hx hF hV'
  have hsm := fh.2.1 star
  have hsm' := fh'.2.1 star
  have hC0 : 0 ≤ C := by linarith
  have hCtC : C ≤ T.Ct := hCC
  have hCt0 : 0 ≤ T.Ct := hC0.trans hCtC
  obtain ⟨hCp0, hNP⟩ := hCp T.Ct hCt0
  set Cp := Cpf T.Ct with hCpdef
  set K := motionSumBound (Mf T.chainParams) (Cgf T.chainParams) T.L with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKb : (|Mf T.chainParams 1| + |Mf T.chainParams 2|) * (|Cgf T.chainParams| * (T.L : ℝ) ^ 4) ≤ K :=
    le_max_right _ _
  have P : AgreeingTops star T.a T.chainParams.ρA T.chainParams.δ₂ T.chainParams.κ₂ C T.σ T.chainParams.Kk
      (frameRadius x) r F F V V' Y Y :=
    ⟨hoddF, hoddF, hLL, hL2, hsd, hsd', h16, hδ₂, hσ.le, hσ1, hρ1, hC0, hsm, hsm',
      (fh.2.2.2 F V' Y Y r hF hV' hag).1 star, hag, hch, hch', fun x' i => ((hS F hoddF hs2).2.2.2 x' i)⟩
  have hcold : ∀ {G : BlockFrame} {U : G.GaugeField G.top}
      (_ : FrameSmallness star T.a T.chainParams.ρA T.chainParams.δ₂ T.chainParams.κ₂ C T.σ T.chainParams.Kk
        (frameRadius x) U),
      IsSmallCurvature (3 / 4 * T.σ)
        (chartedField (frameCoordField star T.a T.chainParams.ρA (frameRadius x) U) U) := by
    intro G U hs
    refine smallCurvature_mono hs.small_curvature ?_
    split_ifs <;> nlinarith
  have hW := hcold hsm
  have hW' := hcold hsm'
  set e₁ := Real.exp (-(T.chainParams.δ₂ / 8 * r)) with he₁
  have he₁p : 0 < e₁ := Real.exp_pos _
  have hsmall : C * e₁ ≤ 1 / 64 := (mul_le_mul_of_nonneg_right hCtC he₁p.le).trans hCt1
  have hKc := hCg T.chainParams hκ₂p
  have hKc' := hCg T.chainParams hκ₂p
  have hpairs : ∀ (e : Fin 2 → (Fin 4 → ℤ) × Fin 4) (_ : ∀ l, BondWithinRadius r (e l))
      (Xe : Fin 2 → imaginaryQuaternions) (_ : AreUnitVectors Xe),
      ∃ (α : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions)
        (α' : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions),
        IsFrameMotion star T.a T.chainParams.ρA (frameRadius x) V (bondsAt Y e) Xe α ∧
        IsFrameMotion star T.a T.chainParams.ρA (frameRadius x) V' (bondsAt Y e) Xe α' ∧
        (∀ l, ∑ b ∈ fineBonds F, ‖motionComponent α ![l] b.1 b.2‖ ≤ K) ∧
        (∀ l, ∑ b ∈ fineBonds F, ‖motionComponent α' ![l] b.1 b.2‖ ≤ K) ∧
        ∑ b ∈ fineBonds F, ‖motionComponent α ![0, 1] b.1 b.2‖ ≤ K ∧
        ∑ b ∈ fineBonds F, ‖motionComponent α' ![0, 1] b.1 b.2‖ ≤ K := by
    intro e he Xe hXe
    obtain ⟨α, hα, hαb⟩ := exists_frameMotion (hMf T.chainParams) hends (fun k => le_abs_self _) hκ₂p.le hρ1
      hσ.le hper hch hsm (bondsAt Y e) Xe hXe
    obtain ⟨α', hα', hαb'⟩ := exists_frameMotion (hMf T.chainParams) hends (fun k => le_abs_self _) hκ₂p.le hρ1
      hσ.le hper' hch' hsm' (bondsAt Y e) Xe hXe
    have hM1 : ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → p * q ≤ (p + |Mf T.chainParams 2|) * q := fun p q _ hq =>
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (Mf T.chainParams 2)]) hq
    have hM2 : ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → p * q ≤ (|Mf T.chainParams 1| + p) * q := fun p q _ hq =>
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (Mf T.chainParams 1)]) hq
    have hLq : 0 ≤ |Cgf T.chainParams| * (T.L : ℝ) ^ 4 := by positivity
    refine ⟨α, α', hα, hα', fun l => ?_, fun l => ?_, ?_, ?_⟩
    · have s1 := sum_le_of_exp_decay (hKc F hoddF hcub (bondsAt Y e l).1)
        (fun b => ‖motionComponent α ![l] b.1 b.2‖) (fun b => hαb 1 ![l] b.1 b.2 0 (by norm_num))
      rw [hFL] at s1
      exact s1.trans ((hM1 _ _ (abs_nonneg _) hLq).trans hKb)
    · have s1 := sum_le_of_exp_decay (hKc F hoddF hcub' (bondsAt Y e l).1)
        (fun b => ‖motionComponent α' ![l] b.1 b.2‖) (fun b => hαb' 1 ![l] b.1 b.2 0 (by norm_num))
      rw [hFL] at s1
      exact s1.trans ((hM1 _ _ (abs_nonneg _) hLq).trans hKb)
    · have s1 := sum_le_of_exp_decay (hKc F hoddF hcub (bondsAt Y e 0).1)
        (fun b => ‖motionComponent α ![0, 1] b.1 b.2‖) (fun b => hαb 2 ![0, 1] b.1 b.2 0 (by norm_num))
      rw [hFL] at s1
      exact s1.trans ((hM2 _ _ (abs_nonneg _) hLq).trans hKb)
    · have s1 := sum_le_of_exp_decay (hKc F hoddF hcub' (bondsAt Y e 0).1)
        (fun b => ‖motionComponent α' ![0, 1] b.1 b.2‖) (fun b => hαb' 2 ![0, 1] b.1 b.2 0 (by norm_num))
      rw [hFL] at s1
      exact s1.trans ((hM2 _ _ (abs_nonneg _) hLq).trans hKb)
  clear hc1 hc2 hσA hy1 hay hL40 hFH fh fh'
  have hWσ := smallCurvature_mono hW (by linarith : 3 / 4 * T.σ ≤ T.σ)
  have hWσ' := smallCurvature_mono hW' (by linarith : 3 / 4 * T.σ ≤ T.σ)
  have hG : ∀ y, ContDiffThreeAlongBonds (subtractTrivial f F y)
      (chartedField (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V) V) :=
    fun y k c Z => (hrow.smooth hlow y _ hWσ k c Z).sub contDiffAt_const
  have hG' : ∀ y, ContDiffThreeAlongBonds (subtractTrivial f F y)
      (chartedField (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V') V') :=
    fun y k c Z => (hrow.smooth hlow y _ hWσ' k c Z).sub contDiffAt_const
  have hcast : ((T.L * (r / 4) + 1 : ℕ) : ℝ) = ((T.L * (r / 4) : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  set Rr : ℝ := ((T.L * (r / 4) : ℕ) : ℝ) with hRr
  have hRr0 : 0 ≤ Rr := Nat.cast_nonneg _
  set D₀ := torusDecayFactor T.L T.decayRate Rr with hD₀
  set D₁ := torusDecayFactor T.L T.decayRate (Rr + 1) with hD₁
  have hD₀p : 0 < D₀ := torusDecayFactor_pos _ _ _
  have hDD : D₀ ≤ D₁ := torusDecayFactor_mono hL1 hδ hRr0 (by linarith)
  have hK0 : 0 ≤ K := by linarith
  have hnum := final_bound_le hE hη hη1 hσ.le hσ1 hC0 hCtC hC₀ hCp0 hK1 hD₀p hDD hRr0 he₁p
  set Q₂ := (T.E / D₁ + C₀ * (T.E / T.η₃) * (4 * (2 * (Rr + 1) + 1) ^ 4 * (2 * (C * T.σ * e₁)))) * (K ^ 2 + K) +
        2 * (T.E / D₀) * (K ^ 2 + K) + T.E * (2 * K + 1) * (4 * (2 * Rr + 1) ^ 4 * (Cp * (C * e₁))) with hQ₂
  set ε₁ := T.E / D₁ + C₀ * (T.E / T.η₃) * (4 * (2 * (Rr + 1) + 1) ^ 4 * (2 * (C * T.σ * e₁))) with hε₁
  obtain ⟨hQ₀, hQ₁⟩ := final_bound_mono hE hη hσ.le hC0 hC₀ hCp0 hK1 hD₀p hDD hRr0 he₁p
  have hend : ∀ {Q : ℝ}, Q ≤ Q₂ →
      (F.blockSide : ℝ) ^ 4 * Q ≤ 2⁻¹ ^ 8 * T.E / torusDecayFactor T.L T.decayRate r := by
    intro Q hQ
    rw [hFL]
    have h1 : (T.L : ℝ) ^ 4 * Q ≤ T.E * localExpansionTail T (localityConstant C₀ Cp T.Ct K) r := by
      refine (mul_le_mul_of_nonneg_left (hQ.trans hnum) (by positivity)).trans (le_of_eq ?_)
      unfold localExpansionTail localityConstant
      ring
    have h2 := mul_le_mul_of_nonneg_left htail hE
    refine h1.trans (h2.trans (le_of_eq ?_))
    ring
  have hsite := fun (e : Fin 2 → (Fin 4 → ℤ) × Fin 4) (he : ∀ l, BondWithinRadius r (e l))
      (Xe : Fin 2 → imaginaryQuaternions) (hXe : AreUnitVectors Xe)
      {α : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions}
      {α' : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions}
      (hα : IsFrameMotion star T.a T.chainParams.ρA (frameRadius x) V (bondsAt Y e) Xe α)
      (hα' : IsFrameMotion star T.a T.chainParams.ρA (frameRadius x) V' (bondsAt Y e) Xe α')
      (a1 : ∀ l, ∑ b ∈ fineBonds F, ‖motionComponent α ![l] b.1 b.2‖ ≤ K)
      (a2 : ∀ l, ∑ b ∈ fineBonds F, ‖motionComponent α' ![l] b.1 b.2‖ ≤ K)
      (a3 : ∑ b ∈ fineBonds F, ‖motionComponent α ![0, 1] b.1 b.2‖ ≤ K)
      (a4 : ∑ b ∈ fineBonds F, ‖motionComponent α' ![0, 1] b.1 b.2‖ ≤ K) (o : Fin 4 → ℤ)
      (ho : o ∈ centredCube F.blockSide) =>
    site_derivs_compare P hTM hFl hshort hC₀ hRE hCp0 (by linarith : C ≤ T.Ct + 1) hNP hrow hlow hσ hδ hE hEE hL1
      hK0 hT hT' hW hW' hsmall e he Xe hXe hα hα' a1 a2 a3 a4 o ho
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk3 with rfl | rfl | rfl
  · obtain ⟨U, hU⟩ := exists_norm_eq_one
    have he0 : ∀ l : Fin 2, BondWithinRadius r ((fun _ => ((0 : Fin 4 → ℤ), (0 : Fin 4))) l) := by
      intro l
      refine ⟨fun i => by simp, fun i => ?_⟩
      have h1 : (1 : ℤ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
      by_cases e : i = 0
      · subst e
        simpa using h1
      · simp [e]
    obtain ⟨α, α', hα, hα', a1, a2, a3, a4⟩ := hpairs _ he0 (fun _ => U) (fun _ => hU)
    have e1 : ∀ {G : BlockFrame} (U' : G.GaugeField G.top) (Z : G.Cell) (c : Fin 0 → G.Site G.top × Fin 4)
        (Xz : Fin 0 → imaginaryQuaternions),
        bondDeriv (cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Z 0) U' c Xz =
          ∑ y ∈ (sitesOfCells (finiteCells G) G.depth).filter (fun y => enclosingCell y = Z),
            subtractTrivial f G y (chartedField (frameCoordField star T.a T.chainParams.ρA (frameRadius x) U') U') := by
      intro G U' Z c Xz
      rw [bondDeriv_fin_zero]
      unfold cellCentredExpansion centredExpansion
      simp only [fieldAboveFrame_zero]
    rw [e1, e1]
    refine (abs_sum_cell_sites_sub_le hoddF hs2 hoddF hs2' hLL Y Y _ _ (Q := ε₁) fun o ho => ?_).trans (hend hQ₀)
    have h1 := (hsite _ he0 _ (fun _ => hU) hα hα' a1 a2 a3 a4 o ho).1 0 h X (by norm_num) (fun l => l.elim0)
      (fun l => l.elim0)
    rw [bondDeriv_fin_zero, bondDeriv_fin_zero, hcast] at h1
    exact h1
  · have he1 : ∀ l, BondWithinRadius r ((![h 0, h 0] : Fin 2 → _) l) := by
      intro l
      fin_cases l <;> exact hb 0
    have hXe : AreUnitVectors (![X 0, X 0] : Fin 2 → imaginaryQuaternions) := by
      intro l
      fin_cases l <;> exact hX 0
    obtain ⟨α, α', hα, hα', a1, a2, a3, a4⟩ := hpairs _ he1 _ hXe
    have eb : ∀ {G : BlockFrame} (Z : G.Cell), bondsAt Z h = ![bondsAt Z (![h 0, h 0] : Fin 2 → _) 0] := by
      intro G Z
      funext l
      fin_cases l
      rfl
    have eX : X = ![(![X 0, X 0] : Fin 2 → imaginaryQuaternions) 0] := by
      funext l
      fin_cases l
      rfl
    rw [eb Y, eX, bondDeriv_cellCentredExpansion_one hSm hα hper Y 0 hG, bondDeriv_cellCentredExpansion_one hSm hα' hper' Y 0 hG']
    refine (abs_sum_cell_sites_sub_le hoddF hs2 hoddF hs2' hLL Y Y _ _
      (Q := ε₁ * K + 2 * (T.E / D₀) * K + T.E * (4 * (2 * Rr + 1) ^ 4 * (Cp * (C * e₁))))
      fun o ho => ?_).trans (hend hQ₁)
    have h1 := (hsite _ he1 _ hXe hα hα' a1 a2 a3 a4 o ho).2.1 0
    rw [hcast] at h1
    exact h1
  · have he2 : ∀ l, BondWithinRadius r (h l) := hb
    obtain ⟨α, α', hα, hα', a1, a2, a3, a4⟩ := hpairs h he2 X hX
    rw [bondDeriv_cellCentredExpansion_two hSm hα hper Y hG, bondDeriv_cellCentredExpansion_two hSm hα' hper' Y hG']
    refine (abs_sum_cell_sites_sub_le hoddF hs2 hoddF hs2' hLL Y Y _ _ (Q := Q₂) fun o ho => ?_).trans (hend le_rfl)
    have h1 := (hsite h he2 X hX hα hα' a1 a2 a3 a4 o ho).2.2
    rw [hcast] at h1
    exact h1
end LocalityLemmas
open LocalityLemmas in
theorem frameFamilyLocalStatement_holds (hTM : TwoMotionsCompare) (hFl : FlowBetweenFields)
    (hflow : DerivBoundAlongFlow) (hNP : NearMotionComponentsOfTwoTops)
    (hSh : ChartLipschitz.ChartedFieldLipschitz)
    (hS : SiteDecomposition) (hends : interpolationAtEndpoints) (hSm : SmoothAlongMotion)
    (hM : motionAboveFrameStatement) (hgeo : CubicTorusCellGeometry) (hTJ : EventuallyInParametersCombines)
    (hFr : FrameBoundsEventually) (hLet : LocalExpansionParametersEventually) :
    frameFamilyLocalStatement := by
  obtain ⟨C₀, hC₀, hREb⟩ := exists_flowDerivBound hflow
  have hMex : ∀ c : ColdChainParameters, ∃ M : ℕ → ℝ, MotionAboveFrameBound (fun k => |16 ^ k * c.Kk k|) M :=
    fun c => by
    obtain ⟨M, -, h⟩ := hM 3 (fun k => |16 ^ k * c.Kk k|) (fun k => abs_nonneg _)
    exact ⟨M, h⟩
  choose Mf hMf using hMex
  have hCex : ∀ c : ColdChainParameters, ∃ Cg : ℝ, 0 < c.κ₂ → ∀ G : BlockFrame, Odd G.blockSide →
      IsLargeCubicTorus G → ∀ z : G.Cell,
      ∑ b ∈ fineBonds G, Real.exp (-(c.κ₂ * cellSupDist (enclosingCell b.1) z)) ≤ Cg * (G.blockSide : ℝ) ^ 4 :=
    fun c => by
    by_cases h : 0 < c.κ₂
    · obtain ⟨C, -, hC⟩ := hgeo.2 c.κ₂ h
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Cgf hCg using hCex
  have hPex : ∀ Ct : ℝ, ∃ Cp : ℝ, 0 ≤ Ct → 0 ≤ Cp ∧ MotionComponentsBound (Ct + 1) Cp := fun Ct => by
    by_cases h : 0 ≤ Ct
    · obtain ⟨C, h0, hb⟩ := hNP (Ct + 1) (by linarith)
      exact ⟨C, fun _ => ⟨h0, hb⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Cpf hCp using hPex
  have hjoin := hTJ.1 _ _ hFr
    (hLet fun _ L c Ct => localityConstant C₀ (Cpf Ct) Ct (motionSumBound (Mf c) (Cgf c) L))
  exact hTJ.2 _ _ (fun T hd hP => frameFamilyLocalAt_of hTM hFl hSh.1 hS hends hSm hC₀ hREb Mf hMf Cgf hCg Cpf hCp
    T hd hP) hjoin
end FrameLocality
end YangMills.Construction
end

import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ColdChainAtEveryLevel.HomotopyFormulaProof
import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfACellProof
import YangMills.Construction.ColdChainAtEveryLevel.FirstOrderOnAPlaquette
import YangMills.Construction.ColdChainAtEveryLevel.FloorOfTheChartForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.ChartFloor
open PlaquetteLinearization GaugeFixing
variable {F : BlockFrame}
def distOne (g : UnitQuaternion) : ℝ := ‖(g : ℍ[ℝ]) - 1‖
theorem distOne_nonneg (g : UnitQuaternion) : 0 ≤ distOne g := norm_nonneg _
theorem distOne_one : distOne 1 = 0 := by simp [distOne]
theorem coe_inv_mul_coe (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_inv_mul_coe <;> assumption
theorem coe_mul_coe_inv (g : UnitQuaternion) : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
theorem distOne_mul_le (g h : UnitQuaternion) : distOne (g * h) ≤ distOne g + distOne h := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
theorem distOne_inv (g : UnitQuaternion) : distOne g⁻¹ = distOne g := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
theorem distOne_conj (g h : UnitQuaternion) : distOne (g * h * g⁻¹) = distOne h := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem norm_adjointAction_sub_le (g : UnitQuaternion) (a : ℍ[ℝ]) :
    ‖adjointAction g a - a‖ ≤ 2 * distOne g * ‖a‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction_sub_le <;> assumption
theorem pathHolonomyVariation_append {j : ℕ} (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions)
    (l l' : List PathStep) :
    ∀ x, pathHolonomyVariation X v x (l ++ l') = pathHolonomyVariation X v x l +
      adjointAction (pathHolonomy X x l) (pathHolonomyVariation X v (x + pathDisplacement j l) l') := by
  induction l with
  | nil => intro x; simp [pathHolonomyVariation, pathHolonomy, pathDisplacement, adjointAction]
  | cons st r ih =>
    intro x
    simp only [List.cons_append, pathHolonomyVariation, pathHolonomy]
    have : x + stepDisplacement j st + pathDisplacement j r = x + pathDisplacement j (st :: r) := by
      simp [pathDisplacement, add_assoc]
    rw [ih, adjointAction_add, ← adjointAction_mul, this, add_assoc]
def IsControlledOn {j : ℕ} (Q : Finset (F.Site j)) (X : F.GaugeField j)
    (v : F.Site j → Fin 4 → imaginaryQuaternions) (m δ : ℝ) : Prop :=
  ∀ z i, z ∈ Q → z + unitStep j i ∈ Q → ‖(v z i : ℍ[ℝ])‖ ≤ m ∧ distOne (X z i) ≤ δ
theorem controlled_link {j : ℕ} {Q : Finset (F.Site j)} {X : F.GaugeField j}
    {v : F.Site j → Fin 4 → imaginaryQuaternions} {m δ : ℝ}
    (h : IsControlledOn Q X v m δ) {z : F.Site j} {st : PathStep} (hz : z ∈ Q)
    (hz' : z + stepDisplacement j st ∈ Q) :
    ‖linkValueVariation X v z st‖ ≤ m ∧ distOne (linkValue X z st) ≤ δ := by
  obtain ⟨i, b⟩ := st
  cases b with
  | true =>
    simp only [stepDisplacement, if_true] at hz'
    simpa [linkValueVariation, linkValue] using h z i hz hz'
  | false =>
    simp only [stepDisplacement, Bool.false_eq_true, if_false] at hz'
    have h1 : z - unitStep j i ∈ Q := by rwa [sub_eq_add_neg]
    have h2 : z - unitStep j i + unitStep j i ∈ Q := by simpa using hz
    obtain ⟨a, b⟩ := h _ i h1 h2
    constructor
    · simp only [linkValueVariation, Bool.false_eq_true, if_false, norm_neg, norm_adjointAction]
      exact a
    · simp only [linkValue, Bool.false_eq_true, if_false, distOne_inv]
      exact b
theorem controlled_path {j : ℕ} {Q : Finset (F.Site j)} {X : F.GaugeField j}
    {v : F.Site j → Fin 4 → imaginaryQuaternions} {m δ : ℝ}
    (h : IsControlledOn Q X v m δ) (l : List PathStep) : ∀ x, PathWithin Q x l →
      ‖pathHolonomyVariation X v x l‖ ≤ l.length * m ∧ distOne (pathHolonomy X x l) ≤ l.length * δ := by
  induction l with
  | nil => intro x _; simp [pathHolonomyVariation, pathHolonomy, distOne_one]
  | cons st r ih =>
    intro x hp
    obtain ⟨a, b⟩ := controlled_link h hp.1 hp.2.head_mem
    obtain ⟨c, d⟩ := ih _ hp.2
    simp only [pathHolonomyVariation, pathHolonomy, List.length_cons]
    push_cast
    constructor
    · refine (norm_add_le _ _).trans ?_
      rw [norm_adjointAction]
      linarith
    · refine (distOne_mul_le _ _).trans ?_
      linarith
theorem variationCurl_eq {j : ℕ} (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions)
    (x : F.Site j) (μ ν : Fin 4) :
    variationCurl X v (x, μ, ν) = (v x μ : ℍ[ℝ]) + adjointAction (X x μ) (v (x + unitStep j μ) ν) -
      adjointAction (X x μ * X (x + unitStep j μ) ν * (X (x + unitStep j ν) μ)⁻¹) (v (x + unitStep j ν) μ) -
      adjointAction (X x μ * X (x + unitStep j μ) ν * (X (x + unitStep j ν) μ)⁻¹ * (X x ν)⁻¹) (v x ν) := by
  have e1 : x + unitStep j μ + unitStep j ν - unitStep j μ = x + unitStep j ν := by abel
  have e2 : x + unitStep j μ + unitStep j ν + - unitStep j μ = x + unitStep j ν := by abel
  have e3 : x + unitStep j ν - unitStep j ν = x := by abel
  simp only [variationCurl, pathHolonomyVariation, linkValueVariation, linkValue, stepDisplacement, if_true,
    Bool.false_eq_true, if_false, e1, e2, e3, adjointAction_add, adjointAction_mul]
  have z : ∀ g : UnitQuaternion, adjointAction g (0 : ℍ[ℝ]) = 0 := fun g => by simp [adjointAction]
  have n : ∀ (g : UnitQuaternion) (a : ℍ[ℝ]), adjointAction g (-a) = - adjointAction g a :=
    fun g a => by simp [adjointAction]
  simp only [z, n, add_zero]
  abel
theorem norm_sub_le_of_curl_first (g1 g2 g3 g4 : UnitQuaternion) (u1 u2 u3 u4 : ℍ[ℝ]) :
    ‖u1 - u3‖ ≤ ‖u1 + adjointAction g1 u2 - adjointAction (g1 * g2 * g3⁻¹) u3 -
      adjointAction (g1 * g2 * g3⁻¹ * g4⁻¹) u4‖ + ‖u2‖ + ‖u4‖ +
      2 * distOne (g1 * g2 * g3⁻¹) * ‖u3‖ := by
  set c := u1 + adjointAction g1 u2 - adjointAction (g1 * g2 * g3⁻¹) u3 -
    adjointAction (g1 * g2 * g3⁻¹ * g4⁻¹) u4 with hc
  have e : u1 - u3 = c - adjointAction g1 u2 + adjointAction (g1 * g2 * g3⁻¹ * g4⁻¹) u4 +
      (adjointAction (g1 * g2 * g3⁻¹) u3 - u3) := by
    rw [hc]; abel
  rw [e]
  have h1 := norm_add_le (c - adjointAction g1 u2 + adjointAction (g1 * g2 * g3⁻¹ * g4⁻¹) u4)
    (adjointAction (g1 * g2 * g3⁻¹) u3 - u3)
  have h2 := norm_add_le (c - adjointAction g1 u2) (adjointAction (g1 * g2 * g3⁻¹ * g4⁻¹) u4)
  have h3 := norm_sub_le c (adjointAction g1 u2)
  have h4 := norm_adjointAction_sub_le (g1 * g2 * g3⁻¹) u3
  rw [norm_adjointAction] at h2 h3
  linarith
theorem norm_sub_le_of_curl_second (g1 g2 g3 g4 : UnitQuaternion) (u1 u2 u3 u4 : ℍ[ℝ]) :
    ‖u2 - u4‖ ≤ ‖u1 + adjointAction g1 u2 - adjointAction (g1 * g2 * g3⁻¹) u3 -
      adjointAction (g1 * g2 * g3⁻¹ * g4⁻¹) u4‖ + ‖u1‖ + ‖u3‖ +
      2 * distOne g1 * ‖u2‖ + 2 * distOne (g1 * g2 * g3⁻¹ * g4⁻¹) * ‖u4‖ := by
  set c := u1 + adjointAction g1 u2 - adjointAction (g1 * g2 * g3⁻¹) u3 -
    adjointAction (g1 * g2 * g3⁻¹ * g4⁻¹) u4 with hc
  have e : u2 - u4 = c - u1 + adjointAction (g1 * g2 * g3⁻¹) u3 - (adjointAction g1 u2 - u2) +
      (adjointAction (g1 * g2 * g3⁻¹ * g4⁻¹) u4 - u4) := by
    rw [hc]; abel
  rw [e]
  have h1 := norm_add_le (c - u1 + adjointAction (g1 * g2 * g3⁻¹) u3 - (adjointAction g1 u2 - u2))
    (adjointAction (g1 * g2 * g3⁻¹ * g4⁻¹) u4 - u4)
  have h2 := norm_sub_le (c - u1 + adjointAction (g1 * g2 * g3⁻¹) u3) (adjointAction g1 u2 - u2)
  have h3 := norm_add_le (c - u1) (adjointAction (g1 * g2 * g3⁻¹) u3)
  have h4 := norm_sub_le c u1
  have h5 := norm_adjointAction_sub_le g1 u2
  have h6 := norm_adjointAction_sub_le (g1 * g2 * g3⁻¹ * g4⁻¹) u4
  rw [norm_adjointAction] at h3
  linarith
section Offsets
abbrev basisOffset (i : Fin 4) : Fin 4 → ℤ := Pi.single i 1
def offsetSite (y : F.Cell) (a : Fin 4 → ℤ) : F.Site F.depth := cellCentre F.depth y + siteOfCoords F.depth a
theorem enclosingCell_offsetSite (hodd : Odd F.blockSide) (y : F.Cell) {a : Fin 4 → ℤ}
    (ha : a ∈ centredCube F.blockSide) : enclosingCell (offsetSite y a) = y := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.enclosingCell_blockPoint <;> assumption
theorem cellOffset_offsetSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (y : F.Cell)
    {a : Fin 4 → ℤ} (ha : a ∈ centredCube F.blockSide) : cellOffset (offsetSite y a) = a := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.cellOffset_blockPoint <;> assumption
theorem offsetSite_add_unitStep (y : F.Cell) (a : Fin 4 → ℤ) (i : Fin 4) :
    offsetSite y a + unitStep F.depth i = offsetSite y (a + basisOffset i) := by apply _root_.YangMills.Construction.GaugeFixing.cellCentre_add_siteOfCoords_add_unitStep <;> assumption
theorem offsetSite_shift (y : F.Cell) (a : Fin 4 → ℤ) (i : Fin 4) :
    offsetSite (y + unitStep F.top i) a = offsetSite y (a + (F.blockSide : ℤ) • basisOffset i) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.blockPoint_neighbour <;> assumption
theorem add_unitStep_ne (hamb : IsAdmissibleAmbient F) (y : F.Cell) (i : Fin 4) : y + unitStep F.top i ≠ y := by
  intro h
  have h0 : (unitStep F.top i : F.Cell) i = 0 := by
    have := congrFun (add_eq_left.1 h) i
    simpa using this
  simp only [unitStep, siteOfCoords, Pi.single_eq_same] at h0
  have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd 1 (F.period F.top i)).1 (by exact_mod_cast h0)
  have h2 : F.period F.top i ∣ 1 := by exact_mod_cast h1
  have h3 := Nat.dvd_one.1 h2
  rw [period_top] at h3
  rcases hamb with h | h
  · have := h i
    omega
  · have := h i
    omega
theorem basisOffset_apply (i k : Fin 4) : basisOffset i k = if k = i then 1 else 0 := by apply _root_.YangMills.Construction.LatticeFractionalIntegration.StaircaseHomotopy.basisVector_apply <;> assumption
theorem add_basisOffset_mem {a : Fin 4 → ℤ} (ha : a ∈ centredCube F.blockSide) {i : Fin 4}
    (hi : a i < halfSide F.blockSide) : a + basisOffset i ∈ centredCube F.blockSide := by
  rw [mem_centredCube] at ha ⊢
  intro k
  have := ha k
  simp only [Pi.add_apply, basisOffset_apply]
  split_ifs with h
  · subst h
    omega
  · omega
theorem eq_halfSide_of_add_not_mem {a : Fin 4 → ℤ} (ha : a ∈ centredCube F.blockSide) {i : Fin 4}
    (h : a + basisOffset i ∉ centredCube F.blockSide) : a i = halfSide F.blockSide := by
  by_contra hne
  have := (mem_centredCube.1 ha i).2
  exact h (add_basisOffset_mem ha (by omega))
theorem not_isCrossingBond_offsetSite (hodd : Odd F.blockSide) (y : F.Cell) {a : Fin 4 → ℤ} {i : Fin 4}
    (ha : a ∈ centredCube F.blockSide) (ha' : a + basisOffset i ∈ centredCube F.blockSide) :
    ¬ IsCrossingBond (offsetSite y a, i) := by
  unfold IsCrossingBond
  simp only [offsetSite_add_unitStep, enclosingCell_offsetSite hodd y ha, enclosingCell_offsetSite hodd y ha',
    ne_eq, not_true_eq_false, not_false_eq_true]
def acrossFace (a : Fin 4 → ℤ) (i : Fin 4) : Fin 4 → ℤ := a + basisOffset i - (F.blockSide : ℤ) • basisOffset i
theorem acrossFace_apply (hodd : Odd F.blockSide) {a : Fin 4 → ℤ} {i : Fin 4} (hi : a i = halfSide F.blockSide)
    (k : Fin 4) : acrossFace (F := F) a i k = if k = i then - halfSide F.blockSide else a k := by
  have h2 := blockSide_eq_two_mul_halfSide_add_one hodd
  simp only [acrossFace, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, basisOffset_apply, smul_eq_mul]
  split_ifs with h
  · subst h
    omega
  · omega
theorem halfSide_nonneg (hodd : Odd F.blockSide) : 0 ≤ halfSide F.blockSide := by
  have h2 := blockSide_eq_two_mul_halfSide_add_one hodd
  omega
theorem acrossFace_mem (hodd : Odd F.blockSide) {a : Fin 4 → ℤ} (ha : a ∈ centredCube F.blockSide) {i : Fin 4}
    (hi : a i = halfSide F.blockSide) : acrossFace (F := F) a i ∈ centredCube F.blockSide := by
  rw [mem_centredCube] at ha ⊢
  intro k
  rw [acrossFace_apply hodd hi]
  have := halfSide_nonneg hodd
  split_ifs
  · omega
  · exact ha k
theorem offsetSite_add_unitStep_eq_acrossFace (y : F.Cell) (a : Fin 4 → ℤ) (i : Fin 4) :
    offsetSite y a + unitStep F.depth i = offsetSite (y + unitStep F.top i) (acrossFace (F := F) a i) := by
  rw [offsetSite_shift, offsetSite_add_unitStep]
  congr 1
  simp [acrossFace]
theorem isCrossingBond_offsetSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (y : F.Cell)
    {a : Fin 4 → ℤ} {i : Fin 4} (ha : a ∈ centredCube F.blockSide) (hi : a i = halfSide F.blockSide) :
    IsCrossingBond (offsetSite y a, i) ∧
      enclosingCell (offsetSite y a + unitStep F.depth i) = y + unitStep F.top i := by
  have h1 : enclosingCell (offsetSite y a + unitStep F.depth i) = y + unitStep F.top i := by
    rw [offsetSite_add_unitStep_eq_acrossFace, enclosingCell_offsetSite hodd _ (acrossFace_mem hodd ha hi)]
  refine ⟨?_, h1⟩
  unfold IsCrossingBond
  simp only [h1, enclosingCell_offsetSite hodd y ha]
  exact add_unitStep_ne hamb y i
theorem offsetSite_mem_sitesOfCells {S : Finset F.Cell} {y : F.Cell} (hy : y ∈ S) {a : Fin 4 → ℤ}
    (ha : a ∈ centredCube F.blockSide) : offsetSite y a ∈ sitesOfCells S F.depth := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.blockPoint_mem <;> assumption
theorem exists_offsetSite {S : Finset F.Cell} {x : F.Site F.depth} (hx : x ∈ sitesOfCells S F.depth) :
    ∃ y ∈ S, ∃ a ∈ centredCube F.blockSide, x = offsetSite y a := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.exists_blockPoint <;> assumption
def siteBlock (y : F.Cell) : Finset (F.Site F.depth) := (centredCube F.blockSide).image (offsetSite y)
theorem mem_siteBlock {y : F.Cell} {z : F.Site F.depth} :
    z ∈ siteBlock y ↔ ∃ a ∈ centredCube F.blockSide, z = offsetSite y a := by
  simp only [siteBlock, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
theorem offsetSite_mem_siteBlock (y : F.Cell) {a : Fin 4 → ℤ} (ha : a ∈ centredCube F.blockSide) :
    offsetSite y a ∈ siteBlock y :=
  mem_siteBlock.2 ⟨a, ha, rfl⟩
end Offsets
section Chords
structure FloorHypotheses (S : Finset F.Cell) (w v : F.Site F.depth → Fin 4 → imaginaryQuaternions) (ρ : ℝ) :
    Prop where
  admissible : IsAdmissibleAmbient F
  oddSide : Odd F.blockSide
  nonneg : 0 ≤ ρ
  small : ρ ≤ 1 / 4
  supported : SupportedOnChords S v
  normLe : ∀ b ∈ chordBonds S, ‖w b.1 b.2‖ ≤ ρ
open Classical in
def interiorChords (S : Finset F.Cell) (y : F.Cell) : Finset (F.Site F.depth × Fin 4) :=
  (chordBonds S).filter fun b => ¬ IsCrossingBond b ∧ enclosingCell b.1 = y
open Classical in
def wallBonds (S : Finset F.Cell) (c : F.Cell × Fin 4) : Finset (F.Site F.depth × Fin 4) :=
  (chordBonds S).filter fun b => IsCrossingBond b ∧ (enclosingCell b.1, b.2) = c
def sqNormOn (B : Finset (F.Site F.depth × Fin 4)) (v : F.Site F.depth → Fin 4 → imaginaryQuaternions) : ℝ :=
  ∑ b ∈ B, ‖(v b.1 b.2 : ℍ[ℝ])‖ ^ 2
open Classical in
def curlSqOn (S : Finset F.Cell) (X : F.GaugeField F.depth) (v : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (y : F.Cell) : ℝ :=
  ∑ p ∈ (innerPlaquettes S F.depth).filter (fun p => enclosingCell p.1 = y), ‖variationCurl X v p‖ ^ 2
theorem sqNormOn_nonneg (B : Finset (F.Site F.depth × Fin 4))
    (v : F.Site F.depth → Fin 4 → imaginaryQuaternions) : 0 ≤ sqNormOn B v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
theorem curlSqOn_nonneg (S : Finset F.Cell) (X : F.GaugeField F.depth)
    (v : F.Site F.depth → Fin 4 → imaginaryQuaternions) (y : F.Cell) : 0 ≤ curlSqOn S X v y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
theorem norm_le_sqrt_sqNormOn {B : Finset (F.Site F.depth × Fin 4)}
    (v : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    {b : F.Site F.depth × Fin 4} (hb : b ∈ B) : ‖(v b.1 b.2 : ℍ[ℝ])‖ ≤ Real.sqrt (sqNormOn B v) := by
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  exact Finset.single_le_sum (f := fun b : F.Site F.depth × Fin 4 => ‖(v b.1 b.2 : ℍ[ℝ])‖ ^ 2)
    (fun _ _ => sq_nonneg _) hb
theorem norm_le_sqrt_curlSqOn {S : Finset F.Cell} (X : F.GaugeField F.depth)
    (v : F.Site F.depth → Fin 4 → imaginaryQuaternions) {y : F.Cell}
    {p : F.Site F.depth × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S F.depth) (hy : enclosingCell p.1 = y) :
    ‖variationCurl X v p‖ ≤ Real.sqrt (curlSqOn S X v y) := by
  classical
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  exact Finset.single_le_sum (f := fun p : F.Site F.depth × Fin 4 × Fin 4 => ‖variationCurl X v p‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_filter.2 ⟨hp, hy⟩)
variable {S : Finset F.Cell} {w v : F.Site F.depth → Fin 4 → imaginaryQuaternions} {ρ : ℝ} (V : F.GaugeField F.top)
theorem mem_chordBonds_iff {b : F.Site F.depth × Fin 4} :
    b ∈ chordBonds S ↔ b ∈ innerBonds S F.depth ∧ ¬ IsAxialTreeBond b := by
  simp only [chordBonds, Finset.mem_filter]
theorem mem_innerBonds_of_offset {y y' : F.Cell} (hy : y ∈ S) (hy' : y' ∈ S) {a a' : Fin 4 → ℤ} {i : Fin 4}
    (ha : a ∈ centredCube F.blockSide) (ha' : a' ∈ centredCube F.blockSide)
    (e : offsetSite y a + unitStep F.depth i = offsetSite y' a') : (offsetSite y a, i) ∈ innerBonds S F.depth := by
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨offsetSite_mem_sitesOfCells hy ha, by rw [e]; exact offsetSite_mem_sitesOfCells hy' ha'⟩
theorem tree_bond_values (hc : FloorHypotheses S w v ρ) {y : F.Cell} {a : Fin 4 → ℤ} {i : Fin 4}
    (ha : a ∈ centredCube F.blockSide) (ha' : a + basisOffset i ∈ centredCube F.blockSide)
    (ht : ∀ l, i < l → a l = 0) :
    v (offsetSite y a) i = 0 ∧ chartedField w V (offsetSite y a) i = 1 := by
  have hnc := not_isCrossingBond_offsetSite hc.oddSide y ha ha'
  have hT : IsAxialTreeBond (offsetSite y a, i) := by
    refine ⟨hnc, fun l hl => ?_⟩
    simp only [cellOffset_offsetSite hc.admissible hc.oddSide y ha]
    exact ht l hl
  constructor
  · exact hc.supported (offsetSite y a, i) fun h => (mem_chordBonds_iff.1 h).2 hT
  · unfold chartedField
    rw [if_neg hnc, if_pos hT]
theorem controlled_siteBlock (hc : FloorHypotheses S w v ρ) {y : F.Cell} (hy : y ∈ S) :
    IsControlledOn (siteBlock y) (chartedField w V) v (Real.sqrt (sqNormOn (interiorChords S y) v)) (2 * ρ) := by
  intro z i hz hz'
  obtain ⟨a, ha, rfl⟩ := mem_siteBlock.1 hz
  obtain ⟨a', ha', e⟩ := mem_siteBlock.1 hz'
  have hnc : ¬ IsCrossingBond (offsetSite y a, i) := by
    unfold IsCrossingBond
    simp only [e, enclosingCell_offsetSite hc.oddSide y ha, enclosingCell_offsetSite hc.oddSide y ha', ne_eq,
      not_true_eq_false, not_false_eq_true]
  have hb := mem_innerBonds_of_offset hy hy ha ha' e
  by_cases ht : IsAxialTreeBond (offsetSite y a, i)
  · have h0 : v (offsetSite y a) i = 0 := hc.supported (offsetSite y a, i) fun h => (mem_chordBonds_iff.1 h).2 ht
    have h1 : chartedField w V (offsetSite y a) i = 1 := by
      unfold chartedField
      rw [if_neg hnc, if_pos ht]
    rw [h0, h1, distOne_one]
    have := hc.nonneg
    exact ⟨by simp, by linarith⟩
  · have hch : (offsetSite y a, i) ∈ chordBonds S := mem_chordBonds_iff.2 ⟨hb, ht⟩
    have h1 : chartedField w V (offsetSite y a) i = expUnit (w (offsetSite y a) i) := by
      unfold chartedField
      rw [if_neg hnc, if_neg ht]
    have hs := hc.normLe _ hch
    constructor
    · classical
      exact norm_le_sqrt_sqNormOn v (b := (offsetSite y a, i))
        (Finset.mem_filter.2 ⟨hch, hnc, enclosingCell_offsetSite hc.oddSide y ha⟩)
    · rw [h1]
      have := norm_coe_expUnit_sub_one_le (w (offsetSite y a) i) (hs.trans hc.small)
      unfold distOne
      have h2 : ‖(w (offsetSite y a) i : ℍ[ℝ])‖ ≤ ρ := hs
      linarith
theorem distOne_expUnit_le (hc : FloorHypotheses S w v ρ) {b : F.Site F.depth × Fin 4} (hb : b ∈ chordBonds S) :
    distOne (expUnit (w b.1 b.2)) ≤ 2 * ρ := by
  have hs := hc.normLe _ hb
  have := norm_coe_expUnit_sub_one_le (w b.1 b.2) (hs.trans hc.small)
  unfold distOne
  have h2 : ‖(w b.1 b.2 : ℍ[ℝ])‖ ≤ ρ := hs
  linarith
theorem mem_innerPlaquettes_of_corners {x : F.Site F.depth} {μ ν : Fin 4} (h : μ < ν)
    (h1 : x ∈ sitesOfCells S F.depth)
    (h2 : x + unitStep F.depth μ ∈ sitesOfCells S F.depth) (h3 : x + unitStep F.depth ν ∈ sitesOfCells S F.depth)
    (h4 : x + unitStep F.depth μ + unitStep F.depth ν ∈ sitesOfCells S F.depth) :
    (x, μ, ν) ∈ innerPlaquettes S F.depth := by
  simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, true_and]
  refine ⟨h1, h, fun z hz => ?_⟩
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> assumption
theorem norm_sub_transport_le (hc : FloorHypotheses S w v ρ) {y : F.Cell} (hy : y ∈ S) {b : Fin 4 → ℤ}
    {i l : Fin 4} (hil : i < l)
    (h1 : b ∈ centredCube F.blockSide) (h2 : b + basisOffset i ∈ centredCube F.blockSide)
    (h3 : b + basisOffset l ∈ centredCube F.blockSide)
    (h4 : b + basisOffset i + basisOffset l ∈ centredCube F.blockSide)
    (hz : ∀ k, l < k → b k = 0) :
    ‖(v (offsetSite y b) i : ℍ[ℝ]) - v (offsetSite y (b + basisOffset l)) i‖ ≤
      Real.sqrt (curlSqOn S (chartedField w V) v y) +
      12 * ρ * Real.sqrt (sqNormOn (interiorChords S y) v) := by
  have hg := controlled_siteBlock V hc hy
  have h5 : b + basisOffset l + basisOffset i ∈ centredCube F.blockSide := by rwa [add_right_comm]
  obtain ⟨t1, t1'⟩ := tree_bond_values (w := w) V hc (y := y) h1 h3 hz
  obtain ⟨t2, t2'⟩ := tree_bond_values (w := w) V hc (y := y) h2 h4 (fun k hk => by
    have hne : k ≠ i := (hil.trans hk).ne'
    simp [basisOffset_apply, hne, hz k hk])
  have g1 := (hg (offsetSite y b) i (offsetSite_mem_siteBlock y h1)
    (by rw [offsetSite_add_unitStep]; exact offsetSite_mem_siteBlock y h2)).2
  obtain ⟨n3, g3⟩ := hg (offsetSite y (b + basisOffset l)) i (offsetSite_mem_siteBlock y h3)
    (by rw [offsetSite_add_unitStep]; exact offsetSite_mem_siteBlock y h5)
  have hcurl := norm_sub_le_of_curl_first (chartedField w V (offsetSite y b) i)
    (chartedField w V (offsetSite y b + unitStep F.depth i) l)
    (chartedField w V (offsetSite y b + unitStep F.depth l) i) (chartedField w V (offsetSite y b) l)
    (v (offsetSite y b) i) (v (offsetSite y b + unitStep F.depth i) l)
    (v (offsetSite y b + unitStep F.depth l) i) (v (offsetSite y b) l)
  rw [← variationCurl_eq] at hcurl
  have hp : (offsetSite y b, i, l) ∈ innerPlaquettes S F.depth := by
    refine mem_innerPlaquettes_of_corners hil (offsetSite_mem_sitesOfCells hy h1) ?_ ?_ ?_
    · rw [offsetSite_add_unitStep]; exact offsetSite_mem_sitesOfCells hy h2
    · rw [offsetSite_add_unitStep]; exact offsetSite_mem_sitesOfCells hy h3
    · rw [offsetSite_add_unitStep, offsetSite_add_unitStep]; exact offsetSite_mem_sitesOfCells hy h4
  have hcell := norm_le_sqrt_curlSqOn (chartedField w V) v hp (enclosingCell_offsetSite hc.oddSide y h1)
  simp only [offsetSite_add_unitStep, t2, t2', t1, t1'] at hcurl n3 g3 ⊢
  have hoff : distOne (chartedField w V (offsetSite y b) i * 1 *
      (chartedField w V (offsetSite y (b + basisOffset l)) i)⁻¹) ≤ 6 * ρ := by
    have a1 := distOne_mul_le (chartedField w V (offsetSite y b) i * 1)
      (chartedField w V (offsetSite y (b + basisOffset l)) i)⁻¹
    rw [distOne_inv, mul_one] at a1
    rw [mul_one]
    have := hc.nonneg
    linarith
  have hn := norm_nonneg ((v (offsetSite y (b + basisOffset l)) i : ℍ[ℝ]))
  have hoffn := distOne_nonneg (chartedField w V (offsetSite y b) i * 1 *
    (chartedField w V (offsetSite y (b + basisOffset l)) i)⁻¹)
  have key : 2 * distOne (chartedField w V (offsetSite y b) i * 1 *
      (chartedField w V (offsetSite y (b + basisOffset l)) i)⁻¹) *
      ‖(v (offsetSite y (b + basisOffset l)) i : ℍ[ℝ])‖ ≤
      12 * ρ * Real.sqrt (sqNormOn (interiorChords S y) v) := by
    have : 2 * distOne (chartedField w V (offsetSite y b) i * 1 *
        (chartedField w V (offsetSite y (b + basisOffset l)) i)⁻¹) ≤ 12 * ρ := by
      linarith
    exact mul_le_mul this n3 hn (by have := hc.nonneg; linarith)
  simp only [ZeroMemClass.coe_zero, norm_zero, add_zero] at hcurl
  linarith
def treeDistance (i : Fin 4) (a : Fin 4 → ℤ) : ℕ := ∑ l ∈ Finset.univ.filter (i < ·), (a l).natAbs
theorem treeDistance_lt {i l : Fin 4} {a a' : Fin 4 → ℤ} (hil : i < l) (h : ∀ k, k ≠ l → a' k = a k)
    (hlt : (a' l).natAbs < (a l).natAbs) : treeDistance i a' < treeDistance i a := by
  refine Finset.sum_lt_sum (fun k _ => ?_) ⟨l, by simpa using hil, hlt⟩
  by_cases hk : k = l
  · subst hk
    exact hlt.le
  · rw [h k hk]
theorem halfSide_le (hodd : Odd F.blockSide) : halfSide F.blockSide ≤ F.blockSide := by
  have h2 := blockSide_eq_two_mul_halfSide_add_one hodd
  omega
theorem treeDistance_le (hodd : Odd F.blockSide) {i : Fin 4} {a : Fin 4 → ℤ}
    (ha : a ∈ centredCube F.blockSide) : treeDistance i a ≤ 4 * F.blockSide := by
  have h1 : ∀ l ∈ Finset.univ.filter (i < ·), (a l).natAbs ≤ F.blockSide := by
    intro l _
    have := mem_centredCube_iff_abs_le.1 ha l
    have h2 := halfSide_le hodd
    rw [Int.abs_eq_natAbs] at this
    omega
  have := Finset.sum_le_card_nsmul _ _ _ h1
  refine this.trans ?_
  have hc : (Finset.univ.filter (i < ·)).card ≤ 4 := by
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin 4)) (i < ·)
  simpa using Nat.mul_le_mul_right F.blockSide hc
theorem exists_last_nonzero {i : Fin 4} {a : Fin 4 → ℤ} (h : ¬ ∀ l, i < l → a l = 0) :
    ∃ l, i < l ∧ a l ≠ 0 ∧ ∀ k, l < k → a k = 0 := by
  classical
  have hs : (Finset.univ.filter fun l => i < l ∧ a l ≠ 0).Nonempty := by
    obtain ⟨l, h1⟩ := not_forall.1 h
    obtain ⟨h1, h2⟩ := Classical.not_imp.1 h1
    exact ⟨l, by simp [h1, h2]⟩
  set l := (Finset.univ.filter fun l => i < l ∧ a l ≠ 0).max' hs with hl
  have hm := Finset.max'_mem _ hs
  rw [← hl] at hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
  refine ⟨l, hm.1, hm.2, fun k hk => ?_⟩
  by_contra hne
  have : k ∈ Finset.univ.filter fun l => i < l ∧ a l ≠ 0 := by
    simp [hm.1.trans hk, hne]
  exact absurd (Finset.le_max' _ _ this) (not_le.2 hk)
theorem sub_basisOffset_mem {a : Fin 4 → ℤ} (ha : a ∈ centredCube F.blockSide) {l : Fin 4} (hl : 0 < a l) :
    a - basisOffset l ∈ centredCube F.blockSide := by
  rw [mem_centredCube] at ha ⊢
  intro k
  have := ha k
  simp only [Pi.sub_apply, basisOffset_apply]
  split_ifs with h
  · subst h
    omega
  · omega
theorem norm_chord_le (hc : FloorHypotheses S w v ρ) {y : F.Cell} (hy : y ∈ S) {R : ℝ}
    (hR : Real.sqrt (curlSqOn S (chartedField w V) v y) +
      12 * ρ * Real.sqrt (sqNormOn (interiorChords S y) v) ≤ R)
    (D : ℕ) : ∀ (a : Fin 4 → ℤ) (i : Fin 4), treeDistance i a ≤ D → a ∈ centredCube F.blockSide →
      a + basisOffset i ∈ centredCube F.blockSide →
      ‖(v (offsetSite y a) i : ℍ[ℝ])‖ ≤ D * R := by
  have hR0 : 0 ≤ R := by
    have h1 := Real.sqrt_nonneg (curlSqOn S (chartedField w V) v y)
    have h2 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hc.nonneg)
      (Real.sqrt_nonneg (sqNormOn (interiorChords S y) v))
    linarith
  have tree : ∀ (a : Fin 4 → ℤ) (i : Fin 4), (∀ l, i < l → a l = 0) → a ∈ centredCube F.blockSide →
      a + basisOffset i ∈ centredCube F.blockSide →
      ‖(v (offsetSite y a) i : ℍ[ℝ])‖ = 0 := by
    intro a i ht ha ha'
    rw [(tree_bond_values (w := w) V hc (y := y) ha ha' ht).1]
    simp
  induction D with
  | zero =>
    intro a i hd ha ha'
    have ht : ∀ l, i < l → a l = 0 := by
      intro l hl
      have h0 : treeDistance i a = 0 := by omega
      have := (Finset.sum_eq_zero_iff.1 h0) l (by simpa using hl)
      omega
    rw [tree a i ht ha ha']
    simp
  | succ D ih =>
    intro a i hd ha ha'
    by_cases ht : ∀ l, i < l → a l = 0
    · rw [tree a i ht ha ha']
      positivity
    obtain ⟨l, hil, hl0, hz⟩ := exists_last_nonzero ht
    have hne : i ≠ l := hil.ne
    have hli : ∀ (c : Fin 4 → ℤ), (c + basisOffset i) l = c l := fun c => by simp [basisOffset_apply, hne.symm]
    push_cast
    rcases lt_or_gt_of_ne hl0 with hneg | hpos
    · have hh := halfSide_nonneg (F := F) hc.oddSide
      have h3 : a + basisOffset l ∈ centredCube F.blockSide := add_basisOffset_mem ha (by omega)
      have h4 : a + basisOffset i + basisOffset l ∈ centredCube F.blockSide :=
        add_basisOffset_mem ha' (by rw [hli]; omega)
      have h5 : a + basisOffset l + basisOffset i ∈ centredCube F.blockSide := by rwa [add_right_comm]
      have htr := norm_sub_transport_le V hc hy hil ha ha' h3 h4 hz
      have hdep : treeDistance i (a + basisOffset l) < treeDistance i a :=
        treeDistance_lt hil (fun k hk => by simp [basisOffset_apply, hk])
          (by simp only [Pi.add_apply, basisOffset_apply, if_true]; omega)
      have hi := ih (a + basisOffset l) i (by omega) h3 h5
      have := norm_sub_norm_le (v (offsetSite y a) i : ℍ[ℝ]) (v (offsetSite y (a + basisOffset l)) i)
      linarith
    · have h3 : a - basisOffset l ∈ centredCube F.blockSide := sub_basisOffset_mem ha hpos
      have e1 : a - basisOffset l + basisOffset l = a := by abel
      have e2 : a - basisOffset l + basisOffset i = a + basisOffset i - basisOffset l := by abel
      have e3 : a - basisOffset l + basisOffset i + basisOffset l = a + basisOffset i := by abel
      have h2 : a - basisOffset l + basisOffset i ∈ centredCube F.blockSide := by
        rw [e2]
        exact sub_basisOffset_mem ha' (by rw [hli]; exact hpos)
      have h4 : a - basisOffset l + basisOffset i + basisOffset l ∈ centredCube F.blockSide := by rwa [e3]
      have h5 : a - basisOffset l + basisOffset l ∈ centredCube F.blockSide := by rwa [e1]
      have htr := norm_sub_transport_le V hc hy hil h3 h2 h5 h4 (fun k hk => by
        have hkl : k ≠ l := hk.ne'
        simp [basisOffset_apply, hkl, hz k hk])
      rw [e1] at htr
      have hdep : treeDistance i (a - basisOffset l) < treeDistance i a :=
        treeDistance_lt hil (fun k hk => by simp [basisOffset_apply, hk])
          (by simp only [Pi.sub_apply, basisOffset_apply, if_true]; omega)
      have hi := ih (a - basisOffset l) i (by omega) h3 h2
      have := norm_sub_norm_le (v (offsetSite y a) i : ℍ[ℝ]) (v (offsetSite y (a - basisOffset l)) i)
      rw [norm_sub_rev] at htr
      linarith
theorem exists_offset_of_mem_interiorChords (hc : FloorHypotheses S w v ρ) {y : F.Cell}
    {b : F.Site F.depth × Fin 4} (hb : b ∈ interiorChords S y) :
    ∃ a, a ∈ centredCube F.blockSide ∧ a + basisOffset b.2 ∈ centredCube F.blockSide ∧ b.1 = offsetSite y a := by
  classical
  obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hb
  have hs : b.1 ∈ sitesOfCells S F.depth :=
    (Finset.mem_product.1 (Finset.mem_filter.1 (mem_chordBonds_iff.1 h1).1).1).1
  obtain ⟨y', _, a, ha, e⟩ := exists_offsetSite hs
  have hy' : y' = y := by
    rw [e, enclosingCell_offsetSite hc.oddSide y' ha] at h3
    exact h3
  subst hy'
  refine ⟨a, ha, ?_, e⟩
  by_contra hn
  have := (isCrossingBond_offsetSite hc.admissible hc.oddSide y' ha (eq_halfSide_of_add_not_mem ha hn)).1
  apply h2
  have eb : b = (offsetSite y' a, b.2) := by rw [← e]
  rw [eb]
  exact this
theorem sqNormOn_interiorChords_le (hc : FloorHypotheses S w v ρ) {y : F.Cell} (hy : y ∈ S) :
    sqNormOn (interiorChords S y) v ≤ (4 * (centredCube F.blockSide).card : ℝ) * (32 * (F.blockSide : ℝ) ^ 2) *
      (curlSqOn S (chartedField w V) v y + 144 * ρ ^ 2 * sqNormOn (interiorChords S y) v) := by
  set e := Real.sqrt (curlSqOn S (chartedField w V) v y) with he
  set m := Real.sqrt (sqNormOn (interiorChords S y) v) with hm
  have he2 : e ^ 2 = curlSqOn S (chartedField w V) v y := Real.sq_sqrt (curlSqOn_nonneg _ _ _ _)
  have hm2 : m ^ 2 = sqNormOn (interiorChords S y) v := Real.sq_sqrt (sqNormOn_nonneg _ _)
  have each : ∀ b ∈ interiorChords S y, ‖(v b.1 b.2 : ℍ[ℝ])‖ ^ 2 ≤ 32 * (F.blockSide : ℝ) ^ 2 *
      (curlSqOn S (chartedField w V) v y + 144 * ρ ^ 2 * sqNormOn (interiorChords S y) v) := by
    intro b hb
    obtain ⟨a, ha, ha', eb⟩ := exists_offset_of_mem_interiorChords hc hb
    have h1 := norm_chord_le V hc hy le_rfl (treeDistance b.2 a) a b.2 le_rfl ha ha'
    have h2 : (treeDistance b.2 a : ℝ) ≤ 4 * F.blockSide := by exact_mod_cast treeDistance_le hc.oddSide ha
    rw [eb]
    have hn := norm_nonneg ((v (offsetSite y a) b.2 : ℍ[ℝ]))
    have hR0 : 0 ≤ e + 12 * ρ * m := by
      have := hc.nonneg
      positivity
    have h3 : ‖(v (offsetSite y a) b.2 : ℍ[ℝ])‖ ≤ 4 * F.blockSide * (e + 12 * ρ * m) :=
      h1.trans (mul_le_mul_of_nonneg_right h2 hR0)
    have h4 : ‖(v (offsetSite y a) b.2 : ℍ[ℝ])‖ ^ 2 ≤ (4 * F.blockSide * (e + 12 * ρ * m)) ^ 2 :=
      pow_le_pow_left₀ hn h3 2
    refine h4.trans ?_
    rw [← he2, ← hm2]
    have : (e + 12 * ρ * m) ^ 2 ≤ 2 * (e ^ 2 + 144 * ρ ^ 2 * m ^ 2) := by
      nlinarith [sq_nonneg (e - 12 * ρ * m)]
    have hsq : (0 : ℝ) ≤ 16 * (F.blockSide : ℝ) ^ 2 := by positivity
    calc (4 * (F.blockSide : ℝ) * (e + 12 * ρ * m)) ^ 2 =
          16 * (F.blockSide : ℝ) ^ 2 * (e + 12 * ρ * m) ^ 2 := by ring
      _ ≤ 16 * (F.blockSide : ℝ) ^ 2 * (2 * (e ^ 2 + 144 * ρ ^ 2 * m ^ 2)) :=
          mul_le_mul_of_nonneg_left this hsq
      _ = _ := by ring
  have hcard : ((interiorChords S y).card : ℝ) ≤ 4 * (centredCube F.blockSide).card := by
    classical
    have hsub : interiorChords S y ⊆ ((centredCube F.blockSide) ×ˢ (Finset.univ : Finset (Fin 4))).image
        (fun p => (offsetSite y p.1, p.2)) := by
      intro b hb
      obtain ⟨a, ha, _, eb⟩ := exists_offset_of_mem_interiorChords hc hb
      refine Finset.mem_image.2 ⟨(a, b.2), by simp [ha], ?_⟩
      rw [← eb]
    have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_product] at h1
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    have : ((interiorChords S y).card : ℝ) ≤ ((centredCube F.blockSide).card * 4 : ℕ) := by exact_mod_cast h1
    push_cast at this
    linarith
  have hsum := Finset.sum_le_card_nsmul _ _ _ each
  have hB : 0 ≤ 32 * (F.blockSide : ℝ) ^ 2 *
      (curlSqOn S (chartedField w V) v y + 144 * ρ ^ 2 * sqNormOn (interiorChords S y) v) := by
    have h1 := curlSqOn_nonneg S (chartedField w V) v y
    have h2 := sqNormOn_nonneg (interiorChords S y) v
    positivity
  have h5 : sqNormOn (interiorChords S y) v ≤ ((interiorChords S y).card : ℝ) * (32 * (F.blockSide : ℝ) ^ 2 *
      (curlSqOn S (chartedField w V) v y + 144 * ρ ^ 2 * sqNormOn (interiorChords S y) v)) := by
    simpa [sqNormOn] using hsum
  calc _ ≤ _ := h5
    _ ≤ (4 * (centredCube F.blockSide).card : ℝ) * (32 * (F.blockSide : ℝ) ^ 2 *
      (curlSqOn S (chartedField w V) v y + 144 * ρ ^ 2 * sqNormOn (interiorChords S y) v)) :=
        mul_le_mul_of_nonneg_right hcard hB
    _ = _ := by ring
theorem distOne_first_le (E1 E3 U g : UnitQuaternion) :
    distOne (E1 * U * g * (E3 * U)⁻¹) ≤ distOne E1 + distOne g + distOne E3 := by
  have e : E1 * U * g * (E3 * U)⁻¹ = E1 * (U * g * U⁻¹) * E3⁻¹ := by group
  rw [e]
  have h1 := distOne_mul_le (E1 * (U * g * U⁻¹)) E3⁻¹
  have h2 := distOne_mul_le E1 (U * g * U⁻¹)
  rw [distOne_inv] at h1
  rw [distOne_conj] at h2
  linarith
theorem distOne_second_le (g1 E2 g3 E4 U : UnitQuaternion) :
    distOne (g1 * (E2 * U) * g3⁻¹ * (E4 * U)⁻¹) ≤ distOne g1 + distOne E2 + distOne g3 + distOne E4 := by
  have e : g1 * (E2 * U) * g3⁻¹ * (E4 * U)⁻¹ = g1 * E2 * (U * g3⁻¹ * U⁻¹) * E4⁻¹ := by group
  rw [e]
  have h1 := distOne_mul_le (g1 * E2 * (U * g3⁻¹ * U⁻¹)) E4⁻¹
  have h2 := distOne_mul_le (g1 * E2) (U * g3⁻¹ * U⁻¹)
  have h3 := distOne_mul_le g1 E2
  rw [distOne_inv] at h1
  rw [distOne_conj, distOne_inv] at h2
  linarith
theorem wall_bond_spec (hc : FloorHypotheses S w v ρ) {y : F.Cell} {i : Fin 4} (hy : y ∈ S)
    (hy' : y + unitStep F.top i ∈ S)
    {a : Fin 4 → ℤ} (ha : a ∈ centredCube F.blockSide) (hi : a i = halfSide F.blockSide) :
    (offsetSite y a, i) ∈ wallBonds S (y, i) ∧ (offsetSite y a, i) ∈ chordBonds S ∧
      chartedField w V (offsetSite y a) i = expUnit (w (offsetSite y a) i) * V y i := by
  classical
  obtain ⟨hx, _⟩ := isCrossingBond_offsetSite hc.admissible hc.oddSide y ha hi
  have hb := mem_innerBonds_of_offset hy hy' ha (acrossFace_mem hc.oddSide ha hi)
    (offsetSite_add_unitStep_eq_acrossFace y a i)
  have hch : (offsetSite y a, i) ∈ chordBonds S := mem_chordBonds_iff.2 ⟨hb, fun ht => ht.1 hx⟩
  refine ⟨Finset.mem_filter.2 ⟨hch, hx, by simp [enclosingCell_offsetSite hc.oddSide y ha]⟩, hch, ?_⟩
  unfold chartedField
  rw [if_pos hx, enclosingCell_offsetSite hc.oddSide y ha]
theorem acrossFace_add (a : Fin 4 → ℤ) (i k : Fin 4) :
    acrossFace (F := F) (a + basisOffset k) i = acrossFace (F := F) a i + basisOffset k := by
  simp only [acrossFace]
  abel
theorem norm_sub_wall_neighbour_le (hc : FloorHypotheses S w v ρ) {y : F.Cell} {i k : Fin 4} (hy : y ∈ S)
    (hy' : y + unitStep F.top i ∈ S) (hk : k ≠ i) {a : Fin 4 → ℤ} (ha : a ∈ centredCube F.blockSide)
    (ha' : a + basisOffset k ∈ centredCube F.blockSide) (hi : a i = halfSide F.blockSide) :
    ‖(v (offsetSite y a) i : ℍ[ℝ]) - v (offsetSite y (a + basisOffset k)) i‖ ≤
      Real.sqrt (curlSqOn S (chartedField w V) v y) +
      Real.sqrt (sqNormOn (interiorChords S y) v) +
      Real.sqrt (sqNormOn (interiorChords S (y + unitStep F.top i)) v) +
      20 * ρ * Real.sqrt (sqNormOn (wallBonds S (y, i)) v) := by
  have hρ := hc.nonneg
  have hi' : (a + basisOffset k) i = halfSide F.blockSide := by simp [basisOffset_apply, hk.symm, hi]
  set a1 := acrossFace (F := F) a i with ha1
  have m1 : a1 ∈ centredCube F.blockSide := acrossFace_mem hc.oddSide ha hi
  have m2 : a1 + basisOffset k ∈ centredCube F.blockSide := by
    rw [ha1, ← acrossFace_add]
    exact acrossFace_mem hc.oddSide ha' hi'
  have s1 : offsetSite y a + unitStep F.depth i = offsetSite (y + unitStep F.top i) a1 :=
    offsetSite_add_unitStep_eq_acrossFace y a i
  have s2 : offsetSite y (a + basisOffset k) + unitStep F.depth i =
      offsetSite (y + unitStep F.top i) (a1 + basisOffset k) := by
    rw [offsetSite_add_unitStep_eq_acrossFace, acrossFace_add]
  have s3 : offsetSite y a + unitStep F.depth k = offsetSite y (a + basisOffset k) :=
    offsetSite_add_unitStep y a k
  have s4 : offsetSite (y + unitStep F.top i) a1 + unitStep F.depth k =
      offsetSite (y + unitStep F.top i) (a1 + basisOffset k) :=
    offsetSite_add_unitStep _ a1 k
  obtain ⟨w1, c1, f1⟩ := wall_bond_spec V hc hy hy' ha hi
  obtain ⟨w2, c2, f2⟩ := wall_bond_spec V hc hy hy' ha' hi'
  have o1 := distOne_expUnit_le hc c1
  have o2 := distOne_expUnit_le hc c2
  simp only at o1 o2
  have n1 := norm_le_sqrt_sqNormOn v w1
  have n2 := norm_le_sqrt_sqNormOn v w2
  simp only at n1 n2
  obtain ⟨n3, o3⟩ := controlled_siteBlock V hc hy (offsetSite y a) k (offsetSite_mem_siteBlock y ha)
    (by rw [s3]; exact offsetSite_mem_siteBlock y ha')
  obtain ⟨n4, o4⟩ := controlled_siteBlock V hc hy' (offsetSite (y + unitStep F.top i) a1) k
    (offsetSite_mem_siteBlock _ m1)
    (by rw [s4]; exact offsetSite_mem_siteBlock _ m2)
  have sy := offsetSite_mem_sitesOfCells hy ha
  have sy2 := offsetSite_mem_sitesOfCells hy ha'
  have sy3 := offsetSite_mem_sitesOfCells hy' m1
  have sy4 := offsetSite_mem_sitesOfCells hy' m2
  have hmw := Real.sqrt_nonneg (sqNormOn (wallBonds S (y, i)) v)
  rcases lt_or_gt_of_ne hk.symm with hlt | hgt
  · have hp : (offsetSite y a, i, k) ∈ innerPlaquettes S F.depth := by
      refine mem_innerPlaquettes_of_corners hlt sy ?_ ?_ ?_
      · rwa [s1]
      · rwa [s3]
      · rwa [s1, s4]
    have hcell := norm_le_sqrt_curlSqOn (chartedField w V) v hp (enclosingCell_offsetSite hc.oddSide y ha)
    have hcurl := norm_sub_le_of_curl_first (chartedField w V (offsetSite y a) i)
      (chartedField w V (offsetSite y a + unitStep F.depth i) k)
      (chartedField w V (offsetSite y a + unitStep F.depth k) i) (chartedField w V (offsetSite y a) k)
      (v (offsetSite y a) i) (v (offsetSite y a + unitStep F.depth i) k)
      (v (offsetSite y a + unitStep F.depth k) i) (v (offsetSite y a) k)
    rw [← variationCurl_eq] at hcurl
    rw [s1, s3] at hcurl
    have hoff := distOne_first_le (expUnit (w (offsetSite y a) i))
      (expUnit (w (offsetSite y (a + basisOffset k)) i)) (V y i)
      (chartedField w V (offsetSite (y + unitStep F.top i) a1) k)
    rw [f1, f2] at hcurl
    have hb : 2 * distOne (expUnit (w (offsetSite y a) i) * V y i *
        chartedField w V (offsetSite (y + unitStep F.top i) a1) k *
        (expUnit (w (offsetSite y (a + basisOffset k)) i) * V y i)⁻¹) *
        ‖(v (offsetSite y (a + basisOffset k)) i : ℍ[ℝ])‖ ≤
        12 * ρ * Real.sqrt (sqNormOn (wallBonds S (y, i)) v) :=
      mul_le_mul (by linarith) n2 (norm_nonneg _) (by positivity)
    have : 0 ≤ 8 * ρ * Real.sqrt (sqNormOn (wallBonds S (y, i)) v) := by positivity
    linarith
  · have hp : (offsetSite y a, k, i) ∈ innerPlaquettes S F.depth := by
      refine mem_innerPlaquettes_of_corners hgt sy ?_ ?_ ?_
      · rwa [s3]
      · rwa [s1]
      · rwa [s3, s2]
    have hcell := norm_le_sqrt_curlSqOn (chartedField w V) v hp (enclosingCell_offsetSite hc.oddSide y ha)
    have hcurl := norm_sub_le_of_curl_second (chartedField w V (offsetSite y a) k)
      (chartedField w V (offsetSite y a + unitStep F.depth k) i)
      (chartedField w V (offsetSite y a + unitStep F.depth i) k) (chartedField w V (offsetSite y a) i)
      (v (offsetSite y a) k) (v (offsetSite y a + unitStep F.depth k) i)
      (v (offsetSite y a + unitStep F.depth i) k) (v (offsetSite y a) i)
    rw [← variationCurl_eq] at hcurl
    rw [s1, s3] at hcurl
    have hoff := distOne_second_le (chartedField w V (offsetSite y a) k)
      (expUnit (w (offsetSite y (a + basisOffset k)) i))
      (chartedField w V (offsetSite (y + unitStep F.top i) a1) k) (expUnit (w (offsetSite y a) i)) (V y i)
    rw [f1, f2] at hcurl
    have hb1 : 2 * distOne (chartedField w V (offsetSite y a) k) *
        ‖(v (offsetSite y (a + basisOffset k)) i : ℍ[ℝ])‖ ≤
        4 * ρ * Real.sqrt (sqNormOn (wallBonds S (y, i)) v) :=
      mul_le_mul (by linarith) n2 (norm_nonneg _) (by positivity)
    have hb2 : 2 * distOne (chartedField w V (offsetSite y a) k *
        (expUnit (w (offsetSite y (a + basisOffset k)) i) * V y i) *
        (chartedField w V (offsetSite (y + unitStep F.top i) a1) k)⁻¹ *
        (expUnit (w (offsetSite y a) i) * V y i)⁻¹) *
        ‖(v (offsetSite y a) i : ℍ[ℝ])‖ ≤ 16 * ρ * Real.sqrt (sqNormOn (wallBonds S (y, i)) v) :=
      mul_le_mul (by linarith) n1 (norm_nonneg _) (by positivity)
    rw [norm_sub_rev]
    linarith
def axisGap (a a' : Fin 4 → ℤ) : ℕ := ∑ k, (a k - a' k).natAbs
theorem axisGap_lt {a b a' : Fin 4 → ℤ} {k : Fin 4} (h : ∀ j, j ≠ k → b j = a j)
    (hlt : (b k - a' k).natAbs < (a k - a' k).natAbs) : axisGap b a' < axisGap a a' := by
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨k, Finset.mem_univ _, hlt⟩
  by_cases hj : j = k
  · subst hj
    exact hlt.le
  · rw [h j hj]
theorem axisGap_le (hodd : Odd F.blockSide) {a a' : Fin 4 → ℤ} (ha : a ∈ centredCube F.blockSide)
    (ha' : a' ∈ centredCube F.blockSide) : axisGap a a' ≤ 4 * F.blockSide := by
  have h1 : ∀ k ∈ (Finset.univ : Finset (Fin 4)), (a k - a' k).natAbs ≤ F.blockSide := by
    intro k _
    have b1 := mem_centredCube.1 ha k
    have b2 := mem_centredCube.1 ha' k
    have h2 := blockSide_eq_two_mul_halfSide_add_one hodd
    omega
  have := Finset.sum_le_card_nsmul _ _ _ h1
  simpa [axisGap] using this
theorem norm_sub_wall_le (hc : FloorHypotheses S w v ρ) {y : F.Cell} {i : Fin 4} (hy : y ∈ S)
    (hy' : y + unitStep F.top i ∈ S) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : Real.sqrt (curlSqOn S (chartedField w V) v y) +
      Real.sqrt (sqNormOn (interiorChords S y) v) +
      Real.sqrt (sqNormOn (interiorChords S (y + unitStep F.top i)) v) +
      20 * ρ * Real.sqrt (sqNormOn (wallBonds S (y, i)) v) ≤ R) (D : ℕ) :
    ∀ a a' : Fin 4 → ℤ, axisGap a a' ≤ D → a ∈ centredCube F.blockSide → a' ∈ centredCube F.blockSide →
      a i = halfSide F.blockSide → a' i = halfSide F.blockSide →
      ‖(v (offsetSite y a) i : ℍ[ℝ]) - v (offsetSite y a') i‖ ≤ D * R := by
  induction D with
  | zero =>
    intro a a' hd ha ha' hi hi'
    have : a = a' := by
      funext k
      have h0 : axisGap a a' = 0 := by omega
      have := (Finset.sum_eq_zero_iff.1 h0) k (Finset.mem_univ _)
      omega
    subst this
    simp
  | succ D ih =>
    intro a a' hd ha ha' hi hi'
    by_cases he : a = a'
    · subst he
      simp only [sub_self, norm_zero]
      positivity
    obtain ⟨k, hk⟩ := Function.ne_iff.1 he
    have hki : k ≠ i := fun h => hk (by rw [h, hi, hi'])
    have b1 := mem_centredCube.1 ha k
    have b2 := mem_centredCube.1 ha' k
    push_cast
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have h3 : a + basisOffset k ∈ centredCube F.blockSide := add_basisOffset_mem ha (by omega)
      have hn := norm_sub_wall_neighbour_le V hc hy hy' hki ha h3 hi
      have hg : axisGap (a + basisOffset k) a' < axisGap a a' := axisGap_lt (k := k) (fun j hj => by simp [hj])
        (by simp only [Pi.add_apply, basisOffset_apply, if_true]; omega)
      have hi3 : (a + basisOffset k) i = halfSide F.blockSide := by simp [hki.symm, hi]
      have h4 := ih (a + basisOffset k) a' (by omega) h3 ha' hi3 hi'
      have := norm_sub_le_norm_sub_add_norm_sub (v (offsetSite y a) i : ℍ[ℝ])
        (v (offsetSite y (a + basisOffset k)) i) (v (offsetSite y a') i)
      linarith
    · have e1 : a - basisOffset k + basisOffset k = a := by abel
      have h3 : a - basisOffset k ∈ centredCube F.blockSide := by
        rw [mem_centredCube] at ha ⊢
        intro j
        have := ha j
        simp only [Pi.sub_apply, basisOffset_apply]
        split_ifs with h
        · subst h
          omega
        · omega
      have hi3 : (a - basisOffset k) i = halfSide F.blockSide := by simp [hki.symm, hi]
      have hn := norm_sub_wall_neighbour_le V hc hy hy' hki h3 (by rwa [e1]) hi3
      rw [e1, norm_sub_rev] at hn
      have hg : axisGap (a - basisOffset k) a' < axisGap a a' := axisGap_lt (k := k) (fun j hj => by simp [hj])
        (by simp only [Pi.sub_apply, basisOffset_apply, if_true]; omega)
      have h4 := ih (a - basisOffset k) a' (by omega) h3 ha' hi3 hi'
      have := norm_sub_le_norm_sub_add_norm_sub (v (offsetSite y a) i : ℍ[ℝ])
        (v (offsetSite y (a - basisOffset k)) i) (v (offsetSite y a') i)
      linarith
theorem offsetSite_add_nsmul (y : F.Cell) (a : Fin 4 → ℤ) (i : Fin 4) (k : ℕ) :
    offsetSite y a + k • unitStep F.depth i = offsetSite y (a + (k : ℤ) • basisOffset i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, ← add_assoc, ih, offsetSite_add_unitStep]
    congr 1
    push_cast
    rw [add_smul, one_smul, add_assoc]
theorem add_nsmul_basisOffset_mem {a : Fin 4 → ℤ} (ha : a ∈ centredCube F.blockSide) {i : Fin 4} {k : ℕ}
    (hk : a i + k ≤ halfSide F.blockSide) : a + (k : ℤ) • basisOffset i ∈ centredCube F.blockSide := by
  rw [mem_centredCube] at ha ⊢
  intro j
  have := ha j
  simp only [Pi.add_apply, Pi.smul_apply, basisOffset_apply, smul_eq_mul]
  split_ifs with h
  · subst h
    omega
  · omega
theorem length_axisPath_le (hodd : Odd F.blockSide) {h : Fin 4 → ℤ} (hh : h ∈ centredCube F.blockSide)
    (π : Equiv.Perm (Fin 4)) : (axisPath h π).length ≤ 4 * F.blockSide := by
  have b : ∀ k, (h k).natAbs ≤ F.blockSide := by
    intro k
    have := mem_centredCube.1 hh k
    have h2 := blockSide_eq_two_mul_halfSide_add_one hodd
    omega
  rw [axisPath_eq_append]
  simp only [List.length_append, List.length_replicate, List.length_nil]
  have b0 := b (π 0)
  have b1 := b (π 1)
  have b2 := b (π 2)
  have b3 := b (π 3)
  omega
theorem length_reversePath (l : List PathStep) : (reversePath l).length = l.length := by
  simp [reversePath]
theorem offsetSite_zero_add (y : F.Cell) (o : Fin 4 → ℤ) :
    offsetSite y 0 + siteOfCoords F.depth o = offsetSite y o := by
  simp [offsetSite, siteOfCoords_zero]
theorem norm_contour_sub_le (hc : FloorHypotheses S w v ρ) {y : F.Cell} {i : Fin 4} (hy : y ∈ S)
    (hy' : y + unitStep F.top i ∈ S) {h : Fin 4 → ℤ} (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    ∃ a₀, a₀ ∈ centredCube F.blockSide ∧ a₀ i = halfSide F.blockSide ∧
      ‖pathHolonomyVariation (chartedField w V) v (refineSite y) (bondContour F.blockSide h π i) -
        v (offsetSite y a₀) i‖ ≤
        5 * F.blockSide * (Real.sqrt (sqNormOn (interiorChords S y) v) +
          Real.sqrt (sqNormOn (interiorChords S (y + unitStep F.top i)) v)) +
        20 * F.blockSide * ρ * Real.sqrt (sqNormOn (wallBonds S (y, i)) v) := by
  have hodd := hc.oddSide
  have hρ := hc.nonneg
  have hh1 := mem_centredCube.1 hh i
  have h2 := blockSide_eq_two_mul_halfSide_add_one hodd
  obtain ⟨r₀, hr₀⟩ : ∃ r : ℕ, (r : ℤ) = halfSide F.blockSide - h i :=
    ⟨(halfSide F.blockSide - h i).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨r₁, hr₁⟩ : ∃ r : ℕ, (r : ℤ) = halfSide F.blockSide + h i :=
    ⟨(halfSide F.blockSide + h i).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hLr : F.blockSide = r₀ + (1 + r₁) := by omega
  have hrep : List.replicate F.blockSide ((i, true) : PathStep) =
      List.replicate r₀ ((i, true) : PathStep) ++ (i, true) :: List.replicate r₁ ((i, true) : PathStep) := by
    conv_lhs => rw [hLr]
    rw [List.replicate_add, List.replicate_add]
    simp
  have esteps : bondContour F.blockSide h π i =
      (axisPath h π ++ List.replicate r₀ ((i, true) : PathStep)) ++
      ((i, true) :: (List.replicate r₁ ((i, true) : PathStep) ++ reversePath (axisPath h π))) := by
    simp only [bondContour, hrep, List.append_assoc, List.cons_append]
  set a₀ : Fin 4 → ℤ := h + (r₀ : ℤ) • basisOffset i with ha₀
  have m₀ : a₀ ∈ centredCube F.blockSide := add_nsmul_basisOffset_mem hh (by omega)
  have i₀ : a₀ i = halfSide F.blockSide := by
    simp only [ha₀, Pi.add_apply, Pi.smul_apply, basisOffset_apply, if_true, smul_eq_mul]
    omega
  have hstep : stepDisplacement F.depth ((i, true) : PathStep) = (unitStep F.depth i : F.Site F.depth) := by
    simp [stepDisplacement]
  have hz : refineSite (j := F.depth) y = offsetSite y 0 := by
    rw [refineSite_eq_cellCentre]
    simp [offsetSite, siteOfCoords_zero]
  have hQ : ∀ y' : F.Cell, ∀ o ∈ centredCube F.blockSide, offsetSite y' 0 + siteOfCoords F.depth o ∈ siteBlock y' := by
    intro y' o ho
    rw [offsetSite_zero_add]
    exact offsetSite_mem_siteBlock y' ho
  have hv1 : ∀ y' : F.Cell, offsetSite y' 0 + pathDisplacement F.depth (axisPath h π) = offsetSite y' h := by
    intro y'
    rw [pathDisplacement_axisPath, offsetSite_zero_add]
  have rep : PathWithin (siteBlock y) (offsetSite y h) (List.replicate r₀ ((i, true) : PathStep)) := by
    refine pathWithin_replicate _ _ _ fun k hk => ?_
    rw [hstep, offsetSite_add_nsmul]
    exact offsetSite_mem_siteBlock y (add_nsmul_basisOffset_mem hh (by omega))
  have p1 : PathWithin (siteBlock y) (offsetSite y 0)
      (axisPath h π ++ List.replicate r₀ ((i, true) : PathStep)) :=
    pathWithin_append _ _ _ (pathWithin_axisPath _ (hQ y) h hh π) (by rw [hv1]; exact rep)
  have hv2 : offsetSite y 0 + pathDisplacement F.depth (axisPath h π ++ List.replicate r₀ ((i, true) : PathStep)) =
      offsetSite y a₀ := by
    rw [pathDisplacement_append, ← add_assoc, hv1, pathDisplacement_replicate, hstep, offsetSite_add_nsmul]
  set y' := y + unitStep F.top i with hy'def
  set a1 := acrossFace (F := F) a₀ i with ha1
  have m1 : a1 ∈ centredCube F.blockSide := acrossFace_mem hodd m₀ i₀
  have hs1 : offsetSite y a₀ + stepDisplacement F.depth ((i, true) : PathStep) = offsetSite y' a1 := by
    rw [hstep]
    exact offsetSite_add_unitStep_eq_acrossFace y a₀ i
  have ia1 : a1 i = - halfSide F.blockSide := by
    rw [ha1, acrossFace_apply hodd i₀]
    simp
  have rep2 : PathWithin (siteBlock y') (offsetSite y' a1) (List.replicate r₁ ((i, true) : PathStep)) := by
    refine pathWithin_replicate _ _ _ fun k hk => ?_
    rw [hstep, offsetSite_add_nsmul]
    exact offsetSite_mem_siteBlock y' (add_nsmul_basisOffset_mem m1 (by omega))
  have hv3 : offsetSite y' a1 + pathDisplacement F.depth (List.replicate r₁ ((i, true) : PathStep)) =
      offsetSite y' h := by
    rw [pathDisplacement_replicate, hstep, offsetSite_add_nsmul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.smul_apply, basisOffset_apply, if_true, smul_eq_mul, ia1]
      omega
    · have : a1 j = h j := by
        rw [ha1, acrossFace_apply hodd i₀, if_neg hj]
        simp [ha₀, hj]
      simp [hj, this]
  have rev : PathWithin (siteBlock y') (offsetSite y' h) (reversePath (axisPath h π)) := by
    have := pathWithin_reversePath _ _ (pathWithin_axisPath (Q := siteBlock y') (offsetSite y' 0) (hQ y') h hh π)
    rwa [hv1] at this
  have p2 : PathWithin (siteBlock y') (offsetSite y' a1)
      (List.replicate r₁ ((i, true) : PathStep) ++ reversePath (axisPath h π)) :=
    pathWithin_append _ _ _ rep2 (by rw [hv3]; exact rev)
  obtain ⟨g1, g1'⟩ := controlled_path (controlled_siteBlock V hc hy) _ _ p1
  obtain ⟨g2, _⟩ := controlled_path (controlled_siteBlock V hc hy') _ _ p2
  have hlen := length_axisPath_le hodd hh π
  have l1 : (((axisPath h π ++ List.replicate r₀ ((i, true) : PathStep)).length : ℕ) : ℝ) ≤
      5 * F.blockSide := by
    have : (axisPath h π ++ List.replicate r₀ ((i, true) : PathStep)).length ≤ 5 * F.blockSide := by
      simp only [List.length_append, List.length_replicate]
      omega
    exact_mod_cast this
  have l2 : (((List.replicate r₁ ((i, true) : PathStep) ++ reversePath (axisPath h π)).length : ℕ) : ℝ) ≤
      5 * F.blockSide := by
    have : (List.replicate r₁ ((i, true) : PathStep) ++ reversePath (axisPath h π)).length ≤
        5 * F.blockSide := by
      simp only [List.length_append, List.length_replicate, length_reversePath]
      omega
    exact_mod_cast this
  refine ⟨a₀, m₀, i₀, ?_⟩
  obtain ⟨w1, _, _⟩ := wall_bond_spec V hc hy hy' m₀ i₀
  have nu := norm_le_sqrt_sqNormOn v w1
  simp only at nu
  rw [esteps, hz, pathHolonomyVariation_append, hv2]
  simp only [pathHolonomyVariation]
  rw [hs1]
  have hsv : linkValueVariation (chartedField w V) v (offsetSite y a₀) ((i, true) : PathStep) =
      v (offsetSite y a₀) i := by
    simp [linkValueVariation]
  rw [hsv]
  set A := pathHolonomyVariation (chartedField w V) v (offsetSite y 0)
    (axisPath h π ++ List.replicate r₀ ((i, true) : PathStep)) with hA
  set H := pathHolonomy (chartedField w V) (offsetSite y 0)
    (axisPath h π ++ List.replicate r₀ ((i, true) : PathStep)) with hH
  set T := pathHolonomyVariation (chartedField w V) v (offsetSite y' a1)
    (List.replicate r₁ ((i, true) : PathStep) ++ reversePath (axisPath h π)) with hT
  set G := linkValue (chartedField w V) (offsetSite y a₀) ((i, true) : PathStep) with hG
  set u : ℍ[ℝ] := (v (offsetSite y a₀) i : ℍ[ℝ]) with hu
  have e : A + adjointAction H (u + adjointAction G T) - u =
      A + (adjointAction H u - u) + adjointAction H (adjointAction G T) := by
    rw [adjointAction_add]
    abel
  rw [e]
  have t1 := norm_add_le (A + (adjointAction H u - u)) (adjointAction H (adjointAction G T))
  have t2 := norm_add_le A (adjointAction H u - u)
  rw [norm_adjointAction, norm_adjointAction] at t1
  have c := norm_adjointAction_sub_le H u
  set m := Real.sqrt (sqNormOn (interiorChords S y) v) with hm
  set m' := Real.sqrt (sqNormOn (interiorChords S y') v) with hm'
  set mw := Real.sqrt (sqNormOn (wallBonds S (y, i)) v) with hmw
  have m0 : 0 ≤ m := Real.sqrt_nonneg _
  have m0' : 0 ≤ m' := Real.sqrt_nonneg _
  have mw0 : 0 ≤ mw := Real.sqrt_nonneg _
  have hL0 : (0 : ℝ) ≤ F.blockSide := by positivity
  have b1 : ‖A‖ ≤ 5 * F.blockSide * m := g1.trans (mul_le_mul_of_nonneg_right l1 m0)
  have b2 : ‖T‖ ≤ 5 * F.blockSide * m' := g2.trans (mul_le_mul_of_nonneg_right l2 m0')
  have b3 : distOne H ≤ 5 * F.blockSide * (2 * ρ) :=
    g1'.trans (mul_le_mul_of_nonneg_right l1 (by positivity))
  have b4 : 2 * distOne H * ‖u‖ ≤ 2 * (5 * F.blockSide * (2 * ρ)) * mw :=
    mul_le_mul (by linarith) nu (norm_nonneg _) (by positivity)
  nlinarith
theorem card_centredCube (hodd : Odd F.blockSide) : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by apply _root_.YangMills.Construction.CompositeMean.card_centredCube_blockSide <;> assumption
theorem norm_mean_sub_le (hodd : Odd F.blockSide) {u : ℍ[ℝ]} {R : ℝ} (hR : 0 ≤ R)
    (H : (Fin 4 → ℤ) → Equiv.Perm (Fin 4) → ℍ[ℝ])
    (hb : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖H h π - u‖ ≤ R) :
    ‖(1 / (24 * (F.blockSide : ℝ) ^ 4)) •
      (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), H h π) - u‖ ≤ R := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hcard := card_centredCube (F := F) hodd
  set c : ℝ := 1 / (24 * (F.blockSide : ℝ) ^ 4) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcount : c * (((centredCube F.blockSide).card : ℝ) * 24) = 1 := by
    rw [hcard, hc]
    field_simp
  have hs : ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (H h π - u) =
      (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), H h π) -
        (((centredCube F.blockSide).card : ℝ) * 24) • u := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    norm_num [Nat.factorial]
  have e : c • (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), H h π) - u =
      c • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (H h π - u) := by
    rw [hs, smul_sub, smul_smul, hcount, one_smul]
  rw [e, norm_smul, Real.norm_of_nonneg hc0]
  have hn : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (H h π - u)‖ ≤
      ((centredCube F.blockSide).card : ℝ) * 24 * R := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ h ∈ centredCube F.blockSide, ‖∑ π : Equiv.Perm (Fin 4), (H h π - u)‖ ≤ 24 * R := by
      intro h hh
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ _ fun π _ => hb h hh π).trans ?_
      simp [Finset.card_univ, Fintype.card_perm, Fintype.card_fin, Nat.factorial]
    refine (Finset.sum_le_card_nsmul _ _ _ h1).trans ?_
    simp only [nsmul_eq_mul]
    linarith
  calc c * ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (H h π - u)‖
      ≤ c * (((centredCube F.blockSide).card : ℝ) * 24 * R) := mul_le_mul_of_nonneg_left hn hc0
    _ = c * (((centredCube F.blockSide).card : ℝ) * 24) * R := by ring
    _ = R := by rw [hcount, one_mul]
theorem exists_offset_of_mem_wallBonds (hc : FloorHypotheses S w v ρ) {y : F.Cell} {i : Fin 4}
    {b : F.Site F.depth × Fin 4} (hb : b ∈ wallBonds S (y, i)) :
    ∃ a, a ∈ centredCube F.blockSide ∧ a i = halfSide F.blockSide ∧ b = (offsetSite y a, i) := by
  classical
  obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hb
  have hs : b.1 ∈ sitesOfCells S F.depth :=
    (Finset.mem_product.1 (Finset.mem_filter.1 (mem_chordBonds_iff.1 h1).1).1).1
  obtain ⟨y', _, a, ha, e⟩ := exists_offsetSite hs
  obtain ⟨c1, c2⟩ := Prod.mk.inj h3
  have hy' : y' = y := by
    rw [e, enclosingCell_offsetSite hc.oddSide y' ha] at c1
    exact c1
  subst hy'
  have eb : b = (offsetSite y' a, i) := by rw [← e, ← c2]
  refine ⟨a, ha, ?_, eb⟩
  by_contra hn
  have hlt : a i < halfSide F.blockSide := lt_of_le_of_ne (mem_centredCube.1 ha i).2 hn
  apply not_isCrossingBond_offsetSite hc.oddSide y' ha (add_basisOffset_mem ha hlt)
  rw [← eb]
  exact h2
theorem norm_wall_le (hc : FloorHypotheses S w v ρ) {y : F.Cell} {i : Fin 4} (hy : y ∈ S)
    (hy' : y + unitStep F.top i ∈ S) {b : F.Site F.depth × Fin 4} (hb : b ∈ wallBonds S (y, i)) :
    ‖(v b.1 b.2 : ℍ[ℝ])‖ ≤ ‖bondContourVariation (chartedField w V) v (y, i)‖ +
      (4 * F.blockSide * Real.sqrt (curlSqOn S (chartedField w V) v y) +
        9 * F.blockSide * Real.sqrt (sqNormOn (interiorChords S y) v) +
        9 * F.blockSide * Real.sqrt (sqNormOn (interiorChords S (y + unitStep F.top i)) v) +
        100 * F.blockSide * ρ * Real.sqrt (sqNormOn (wallBonds S (y, i)) v)) := by
  obtain ⟨a, ha, hi, rfl⟩ := exists_offset_of_mem_wallBonds hc hb
  have hρ := hc.nonneg
  set e := Real.sqrt (curlSqOn S (chartedField w V) v y) with he
  set m := Real.sqrt (sqNormOn (interiorChords S y) v) with hm
  set m' := Real.sqrt (sqNormOn (interiorChords S (y + unitStep F.top i)) v) with hm'
  set mw := Real.sqrt (sqNormOn (wallBonds S (y, i)) v) with hmw
  have hR0 : 0 ≤ e + m + m' + 20 * ρ * mw := by positivity
  have hcl : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖pathHolonomyVariation (chartedField w V) v (refineSite y) (bondContour F.blockSide h π i) -
        v (offsetSite y a) i‖ ≤
        4 * F.blockSide * e + 9 * F.blockSide * m + 9 * F.blockSide * m' + 100 * F.blockSide * ρ * mw := by
    intro h hh π
    obtain ⟨a₀, m₀, i₀, hcc⟩ := norm_contour_sub_le V hc hy hy' hh π
    have c1 := norm_sub_wall_le V hc hy hy' hR0 le_rfl (axisGap a₀ a) a₀ a le_rfl m₀ ha i₀ hi
    have g : (axisGap a₀ a : ℝ) ≤ 4 * F.blockSide := by exact_mod_cast axisGap_le hc.oddSide m₀ ha
    have c2 := c1.trans (mul_le_mul_of_nonneg_right g hR0)
    have t := norm_sub_le_norm_sub_add_norm_sub
      (pathHolonomyVariation (chartedField w V) v (refineSite y) (bondContour F.blockSide h π i))
      (v (offsetSite y a₀) i : ℍ[ℝ]) (v (offsetSite y a) i)
    nlinarith
  have hmean := norm_mean_sub_le (F := F) hc.oddSide (u := (v (offsetSite y a) i : ℍ[ℝ]))
    (by positivity : 0 ≤ 4 * F.blockSide * e + 9 * F.blockSide * m + 9 * F.blockSide * m' +
      100 * F.blockSide * ρ * mw)
    (fun h π => pathHolonomyVariation (chartedField w V) v (refineSite y) (bondContour F.blockSide h π i)) hcl
  have hq : bondContourVariation (chartedField w V) v (y, i) = (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
      (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        pathHolonomyVariation (chartedField w V) v (refineSite y) (bondContour F.blockSide h π i)) := rfl
  rw [← hq] at hmean
  have := norm_sub_norm_le (v (offsetSite y a) i : ℍ[ℝ]) (bondContourVariation (chartedField w V) v (y, i))
  rw [norm_sub_rev] at this
  simp only
  linarith
theorem sqNormOn_wallBonds_le (hc : FloorHypotheses S w v ρ) {y : F.Cell} {i : Fin 4} (hy : y ∈ S)
    (hy' : y + unitStep F.top i ∈ S) :
    sqNormOn (wallBonds S (y, i)) v ≤ ((centredCube F.blockSide).card : ℝ) *
      (5 * (‖bondContourVariation (chartedField w V) v (y, i)‖ ^ 2 +
      16 * (F.blockSide : ℝ) ^ 2 * curlSqOn S (chartedField w V) v y +
      81 * (F.blockSide : ℝ) ^ 2 * sqNormOn (interiorChords S y) v +
      81 * (F.blockSide : ℝ) ^ 2 * sqNormOn (interiorChords S (y + unitStep F.top i)) v +
      10000 * (F.blockSide : ℝ) ^ 2 * ρ ^ 2 * sqNormOn (wallBonds S (y, i)) v)) := by
  set q := ‖bondContourVariation (chartedField w V) v (y, i)‖ with hq
  set e := Real.sqrt (curlSqOn S (chartedField w V) v y) with he
  set m := Real.sqrt (sqNormOn (interiorChords S y) v) with hm
  set m' := Real.sqrt (sqNormOn (interiorChords S (y + unitStep F.top i)) v) with hm'
  set mw := Real.sqrt (sqNormOn (wallBonds S (y, i)) v) with hmw
  have he2 : e ^ 2 = curlSqOn S (chartedField w V) v y := Real.sq_sqrt (curlSqOn_nonneg _ _ _ _)
  have hm2 : m ^ 2 = sqNormOn (interiorChords S y) v := Real.sq_sqrt (sqNormOn_nonneg _ _)
  have hm2' : m' ^ 2 = sqNormOn (interiorChords S (y + unitStep F.top i)) v := Real.sq_sqrt (sqNormOn_nonneg _ _)
  have hmw2 : mw ^ 2 = sqNormOn (wallBonds S (y, i)) v := Real.sq_sqrt (sqNormOn_nonneg _ _)
  rw [← he2, ← hm2, ← hm2', ← hmw2]
  have five : ∀ A B C D E : ℝ, (A + (B + C + D + E)) ^ 2 ≤ 5 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 + E ^ 2) := by
    intro A B C D E
    nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (A - D), sq_nonneg (A - E), sq_nonneg (B - C),
      sq_nonneg (B - D), sq_nonneg (B - E), sq_nonneg (C - D), sq_nonneg (C - E), sq_nonneg (D - E)]
  have each : ∀ b ∈ wallBonds S (y, i), ‖(v b.1 b.2 : ℍ[ℝ])‖ ^ 2 ≤
      5 * (q ^ 2 + 16 * (F.blockSide : ℝ) ^ 2 * e ^ 2 +
      81 * (F.blockSide : ℝ) ^ 2 * m ^ 2 + 81 * (F.blockSide : ℝ) ^ 2 * m' ^ 2 +
      10000 * (F.blockSide : ℝ) ^ 2 * ρ ^ 2 * mw ^ 2) := by
    intro b hb
    have h1 := norm_wall_le V hc hy hy' hb
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    refine h2.trans ((five _ _ _ _ _).trans (le_of_eq ?_))
    ring
  have hcard : ((wallBonds S (y, i)).card : ℝ) ≤ ((centredCube F.blockSide).card : ℝ) := by
    classical
    have hsub : wallBonds S (y, i) ⊆ (centredCube F.blockSide).image (fun a => (offsetSite y a, i)) := by
      intro b hb
      obtain ⟨a, ha, _, eb⟩ := exists_offset_of_mem_wallBonds hc hb
      exact Finset.mem_image.2 ⟨a, ha, eb.symm⟩
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  have hsum := Finset.sum_le_card_nsmul _ _ _ each
  have h5 : sqNormOn (wallBonds S (y, i)) v ≤ ((wallBonds S (y, i)).card : ℝ) * (5 * (q ^ 2 +
      16 * (F.blockSide : ℝ) ^ 2 * e ^ 2 + 81 * (F.blockSide : ℝ) ^ 2 * m ^ 2 +
      81 * (F.blockSide : ℝ) ^ 2 * m' ^ 2 +
      10000 * (F.blockSide : ℝ) ^ 2 * ρ ^ 2 * mw ^ 2)) := by
    simpa [sqNormOn] using hsum
  rw [hmw2] at h5 ⊢
  refine h5.trans (mul_le_mul_of_nonneg_right hcard ?_)
  rw [← hmw2]
  positivity
theorem sum_innerBonds_fst_le (f : F.Cell → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ∑ c ∈ innerBonds S F.top, f c.1 ≤ 4 * ∑ y ∈ S, f y := by
  have hsub : innerBonds S F.top ⊆ S ×ˢ (Finset.univ : Finset (Fin 4)) := by
    intro c hc
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hc ⊢
    exact mem_sitesOfCells_top.1 hc.1
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hf _).trans (le_of_eq ?_)
  rw [Finset.sum_product]
  simp [Finset.mul_sum, mul_comm]
theorem sum_innerBonds_snd_le (hamb : IsAdmissibleAmbient F) (f : F.Cell → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ∑ c ∈ innerBonds S F.top, f (c.1 + unitStep F.top c.2) ≤ 4 * ∑ y ∈ S, f y := by
  classical
  have hinj : Set.InjOn (fun c : F.Cell × Fin 4 => (c.1 + unitStep F.top c.2, c.2))
      (innerBonds S F.top : Set _) := by
    rintro ⟨c1, c2⟩ _ ⟨d1, d2⟩ _ h
    obtain ⟨e1, e2⟩ := Prod.mk.inj h
    simp only at e1 e2
    subst e2
    simpa using e1
  have hsub : (innerBonds S F.top).image (fun c : F.Cell × Fin 4 => (c.1 + unitStep F.top c.2, c.2)) ⊆
      S ×ˢ (Finset.univ : Finset (Fin 4)) := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hd
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hc ⊢
    exact mem_sitesOfCells_top.1 hc.2
  have e := Finset.sum_image (f := fun d : F.Cell × Fin 4 => f d.1) hinj
  simp only at e
  rw [← e]
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hf _).trans (le_of_eq ?_)
  rw [Finset.sum_product]
  simp [Finset.mul_sum, mul_comm]
theorem chordSqNorm_eq_split (hc : FloorHypotheses S w v ρ) :
    chordSqNorm S v = ∑ y ∈ S, sqNormOn (interiorChords S y) v +
      ∑ c ∈ innerBonds S F.top, sqNormOn (wallBonds S c) v := by
  classical
  have hodd := hc.oddSide
  have hsite : ∀ b ∈ chordBonds S, b.1 ∈ sitesOfCells S F.depth := fun b hb =>
    (Finset.mem_product.1 (Finset.mem_filter.1 (mem_chordBonds_iff.1 hb).1).1).1
  have h1 : ∑ y ∈ S, sqNormOn (interiorChords S y) v =
      ∑ b ∈ (chordBonds S).filter (fun b => ¬ IsCrossingBond b), ‖(v b.1 b.2 : ℍ[ℝ])‖ ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun b : F.Site F.depth × Fin 4 => enclosingCell b.1) (t := S)
      (fun b hb => LocalPartition.enclosingCell_mem hodd (hsite b (Finset.mem_filter.1 hb).1))]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [sqNormOn, interiorChords, Finset.filter_filter]
  have hwall : ∀ b ∈ (chordBonds S).filter (fun b => IsCrossingBond b),
      (enclosingCell b.1, b.2) ∈ innerBonds S F.top := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
    obtain ⟨y, hy, a, ha, e⟩ := exists_offsetSite (hsite b hb1)
    have hai : a b.2 = halfSide F.blockSide := by
      by_contra hn
      have hlt : a b.2 < halfSide F.blockSide := lt_of_le_of_ne (mem_centredCube.1 ha b.2).2 hn
      apply not_isCrossingBond_offsetSite hc.oddSide y ha (add_basisOffset_mem ha hlt)
      have eb : (offsetSite y a, b.2) = b := by rw [← e]
      rw [eb]
      exact hb2
    have hcell := (isCrossingBond_offsetSite hc.admissible hodd y ha hai).2
    have hend : b.1 + unitStep F.depth b.2 ∈ sitesOfCells S F.depth :=
      (Finset.mem_filter.1 (mem_chordBonds_iff.1 hb1).1).2
    have hc1 : enclosingCell b.1 = y := by rw [e, enclosingCell_offsetSite hodd y ha]
    have hy' : y + unitStep F.top b.2 ∈ S := by
      have := LocalPartition.enclosingCell_mem hodd hend
      rwa [e, hcell] at this
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, hc1]
    exact ⟨mem_sitesOfCells_top.2 hy, mem_sitesOfCells_top.2 hy'⟩
  have h2 : ∑ c ∈ innerBonds S F.top, sqNormOn (wallBonds S c) v =
      ∑ b ∈ (chordBonds S).filter (fun b => IsCrossingBond b), ‖(v b.1 b.2 : ℍ[ℝ])‖ ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun b : F.Site F.depth × Fin 4 => (enclosingCell b.1, b.2))
      (t := innerBonds S F.top) hwall]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [sqNormOn, wallBonds, Finset.filter_filter]
  rw [h1, h2, add_comm]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
theorem sum_curlSqOn_eq (hc : FloorHypotheses S w v ρ) (X : F.GaugeField F.depth) :
    ∑ y ∈ S, curlSqOn S X v y = ∑ p ∈ innerPlaquettes S F.depth, ‖variationCurl X v p‖ ^ 2 := by
  classical
  have hm : ∀ p ∈ innerPlaquettes S F.depth, enclosingCell p.1 ∈ S := by
    intro p hp
    have : p.1 ∈ sitesOfCells S F.depth := by
      have := (Finset.mem_filter.1 hp).1
      exact (Finset.mem_product.1 this).1
    exact LocalPartition.enclosingCell_mem hc.oddSide this
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : F.Site F.depth × Fin 4 × Fin 4 => enclosingCell p.1) hm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [curlSqOn]
def floorConstant (N L : ℝ) : ℝ :=
  (1 + 3240 * N * L ^ 2) * (128 * N * L ^ 2) * 144 + 5 * N + 320 * N * L ^ 2 + 50000 * N * L ^ 2 + 1
theorem chordSqNorm_le_floor (hc : FloorHypotheses S w v ρ) :
    chordSqNorm S v ≤ floorConstant ((centredCube F.blockSide).card) F.blockSide *
        (∑ p ∈ innerPlaquettes S F.depth, ‖variationCurl (chartedField w V) v p‖ ^ 2 +
          ∑ c ∈ innerBonds S F.top, ‖bondContourVariation (chartedField w V) v c‖ ^ 2) +
      floorConstant ((centredCube F.blockSide).card) F.blockSide * ρ ^ 2 * chordSqNorm S v := by
  set N : ℝ := ((centredCube F.blockSide).card : ℝ) with hN
  set L : ℝ := (F.blockSide : ℝ) with hL
  have N0 : 0 ≤ N := by positivity
  set A := ∑ p ∈ innerPlaquettes S F.depth, ‖variationCurl (chartedField w V) v p‖ ^ 2 with hA
  set B := ∑ c ∈ innerBonds S F.top, ‖bondContourVariation (chartedField w V) v c‖ ^ 2 with hB
  set Qc := ∑ y ∈ S, sqNormOn (interiorChords S y) v with hQc
  set T := ∑ c ∈ innerBonds S F.top, sqNormOn (wallBonds S c) v with hT
  have A0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have B0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have Q0 : 0 ≤ Qc := Finset.sum_nonneg fun _ _ => sqNormOn_nonneg _ _
  have T0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => sqNormOn_nonneg _ _
  have hA' : ∑ y ∈ S, curlSqOn S (chartedField w V) v y = A := sum_curlSqOn_eq hc _
  have hsplit : chordSqNorm S v = Qc + T := chordSqNorm_eq_split hc
  have hQ : Qc ≤ 128 * N * L ^ 2 * (A + 144 * ρ ^ 2 * Qc) := by
    calc Qc ≤ ∑ y ∈ S, (4 * N) * (32 * L ^ 2) *
          (curlSqOn S (chartedField w V) v y + 144 * ρ ^ 2 * sqNormOn (interiorChords S y) v) :=
          Finset.sum_le_sum fun y hy => sqNormOn_interiorChords_le V hc hy
      _ = 128 * N * L ^ 2 * (A + 144 * ρ ^ 2 * Qc) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hA']
          ring
  have hWall : T ≤ N * (5 * (B + 16 * L ^ 2 * (4 * A) + 81 * L ^ 2 * (4 * Qc) + 81 * L ^ 2 * (4 * Qc) +
      10000 * L ^ 2 * ρ ^ 2 * T)) := by
    have c1 := sum_innerBonds_fst_le (S := S) (fun y => curlSqOn S (chartedField w V) v y)
      (fun y => curlSqOn_nonneg _ _ _ _)
    have c2 := sum_innerBonds_fst_le (S := S) (fun y => sqNormOn (interiorChords S y) v)
      (fun y => sqNormOn_nonneg _ _)
    have c3 := sum_innerBonds_snd_le (S := S) hc.admissible (fun y => sqNormOn (interiorChords S y) v)
      (fun y => sqNormOn_nonneg _ _)
    rw [hA'] at c1
    have each : ∀ c ∈ innerBonds S F.top, sqNormOn (wallBonds S c) v ≤
        N * (5 * (‖bondContourVariation (chartedField w V) v c‖ ^ 2 +
        16 * L ^ 2 * curlSqOn S (chartedField w V) v c.1 + 81 * L ^ 2 * sqNormOn (interiorChords S c.1) v +
        81 * L ^ 2 * sqNormOn (interiorChords S (c.1 + unitStep F.top c.2)) v +
        10000 * L ^ 2 * ρ ^ 2 * sqNormOn (wallBonds S c) v)) := by
      rintro ⟨y, i⟩ hc'
      simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hc'
      exact sqNormOn_wallBonds_le V hc (mem_sitesOfCells_top.1 hc'.1) (mem_sitesOfCells_top.1 hc'.2)
    refine (Finset.sum_le_sum each).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum]
    have d1 := mul_le_mul_of_nonneg_left c1 (by positivity : 0 ≤ 16 * L ^ 2)
    have d2 := mul_le_mul_of_nonneg_left c2 (by positivity : 0 ≤ 81 * L ^ 2)
    have d3 := mul_le_mul_of_nonneg_left c3 (by positivity : 0 ≤ 81 * L ^ 2)
    refine mul_le_mul_of_nonneg_left ?_ N0
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    linarith
  set c3 : ℝ := 3240 * N * L ^ 2 with hc3
  set K1 : ℝ := 128 * N * L ^ 2 with hK1
  have c30 : 0 ≤ c3 := by positivity
  have hbig : floorConstant N L = (1 + c3) * K1 * 144 + 5 * N + 320 * N * L ^ 2 + 50000 * N * L ^ 2 + 1 := rfl
  set K := floorConstant N L with hK
  have s0 : 0 ≤ (1 + c3) * K1 := by positivity
  have r2 : 0 ≤ ρ ^ 2 := by positivity
  have k1 : (1 + c3) * K1 + 320 * N * L ^ 2 ≤ K := by rw [hbig]; nlinarith
  have k2 : (1 + c3) * K1 * 144 ≤ K := by rw [hbig]; linarith
  have k3 : 5 * N ≤ K := by rw [hbig]; nlinarith
  have k5 : 50000 * N * L ^ 2 ≤ K := by rw [hbig]; nlinarith
  have t1 : (1 + c3) * Qc ≤ (1 + c3) * K1 * A + (1 + c3) * K1 * 144 * (ρ ^ 2 * Qc) := by
    have := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 1 + c3)
    refine this.trans (le_of_eq ?_)
    ring
  have u1 := mul_le_mul_of_nonneg_right k1 A0
  have u2 := mul_le_mul_of_nonneg_right k2 (mul_nonneg r2 Q0)
  have u3 := mul_le_mul_of_nonneg_right k3 B0
  have u5 := mul_le_mul_of_nonneg_right k5 (mul_nonneg r2 T0)
  rw [hsplit]
  have e1 : K * (A + B) + K * ρ ^ 2 * (Qc + T) = K * A + K * B + K * (ρ ^ 2 * Qc) + K * (ρ ^ 2 * T) := by ring
  rw [e1]
  linarith
theorem floorConstant_pos {N L : ℝ} (hN : 0 ≤ N) (hL : 0 ≤ L) : 0 < floorConstant N L := by
  unfold floorConstant
  positivity
end Chords
theorem chartFormFloor : chartFormFloorStatement := by
  intro L hodd _
  have hK := floorConstant_pos (N := ((centredCube L).card : ℝ)) (L := (L : ℝ)) (by positivity) (by positivity)
  refine ⟨1 / floorConstant ((centredCube L).card) L, 1, 1 / 4, 1, by positivity, one_pos, by norm_num, one_pos, ?_⟩
  intro F m S hFL hamb _ _ ρ σ V w dw hρ hρ₀ hσ _ _ _ hdw hw _
  subst hFL
  have hc : FloorHypotheses S w dw ρ := ⟨hamb, hodd, hρ.le, hρ₀, hdw, hw⟩
  have h := chordSqNorm_le_floor V hc
  set K := floorConstant ((centredCube F.blockSide).card) F.blockSide with hKdef
  set A := ∑ p ∈ innerPlaquettes S F.depth, ‖variationCurl (chartedField w V) dw p‖ ^ 2 with hA
  set B := ∑ c ∈ innerBonds S F.top, ‖bondContourVariation (chartedField w V) dw c‖ ^ 2 with hB
  set Q := chordSqNorm S dw with hQ
  have Q0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : 1 / K * Q ≤ A + B + ρ ^ 2 * Q := by
    rw [one_div, inv_mul_le_iff₀ hK]
    refine h.trans (le_of_eq ?_)
    ring
  have h2 : ρ ^ 2 * Q ≤ 1 * (ρ + σ) * Q := by
    refine mul_le_mul_of_nonneg_right ?_ Q0
    nlinarith
  linarith
end YangMills.Construction.BlockAverages.ChartFloor
end

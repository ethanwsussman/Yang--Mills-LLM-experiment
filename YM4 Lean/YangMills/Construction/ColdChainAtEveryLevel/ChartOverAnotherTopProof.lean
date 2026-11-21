import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfTheReferenceProof
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfTheReferenceForm
import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTop
import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.FramedChainsOverATopProof
import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
namespace ChartOverTop
open LatticePaths LatticeFractionalIntegration GaugeMap
variable {F : BlockFrame}
section Log
def quatI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
theorem quatI_re : quatI.re = 0 := rfl
theorem quatI_imI : quatI.imI = 1 := rfl
theorem quatI_imJ : quatI.imJ = 0 := rfl
theorem quatI_imK : quatI.imK = 0 := rfl
theorem exists_expUnit_eq (g : UnitQuaternion) :
    ∃ w : imaginaryQuaternions, expUnit w = g ∧ ‖(w : ℍ[ℝ])‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ := by
  classical
  set q : ℍ[ℝ] := (g : ℍ[ℝ]) with hq
  have hn : ‖q‖ = 1 := norm_coe_unitQuaternion g
  have n1 := Quaternion.normSq_eq_norm_mul_self q
  have n2 := Quaternion.normSq_eq_norm_mul_self q.im
  have n3 := Quaternion.normSq_eq_norm_mul_self (q - 1)
  rw [hn] at n1
  simp only [Quaternion.normSq_def'] at n1 n2 n3
  simp at n2 n3
  have hre1 : -1 ≤ q.re ∧ q.re ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg ‖q.im‖, sq_nonneg (q.re - 1), sq_nonneg (q.re + 1)]
  set θ := Real.arccos q.re with hθ
  have hc : Real.cos θ = q.re := Real.cos_arccos hre1.1 hre1.2
  have hs : Real.sin θ = ‖q.im‖ := by
    rw [hθ, Real.sin_arccos]
    have : 1 - q.re ^ 2 = ‖q.im‖ ^ 2 := by linarith
    rw [this, Real.sqrt_sq (norm_nonneg _)]
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hθπ : θ ≤ Real.pi := Real.arccos_le_pi _
  obtain ⟨e, he0, he1, heq⟩ : ∃ e : ℍ[ℝ], e.re = 0 ∧ ‖e‖ = 1 ∧
      q = ((Real.cos θ : ℝ) : ℍ[ℝ]) + Real.sin θ • e := by
    by_cases hr : ‖q.im‖ = 0
    · refine ⟨quatI, rfl, ?_, ?_⟩
      · have m := Quaternion.normSq_eq_norm_mul_self quatI
        simp only [Quaternion.normSq_def', quatI_re, quatI_imI, quatI_imJ, quatI_imK] at m
        nlinarith [norm_nonneg quatI]
      · rw [hs, hr, zero_smul, add_zero, hc]
        have h0 : q.im = 0 := norm_eq_zero.1 hr
        have := Quaternion.re_add_im q
        rw [h0, add_zero] at this
        exact this.symm
    · refine ⟨‖q.im‖⁻¹ • q.im, by simp, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr]
      · rw [hs, hc, smul_smul, mul_inv_cancel₀ hr, one_smul]
        exact (Quaternion.re_add_im q).symm
  have hw0 : (θ • e).re = 0 := by simp [he0]
  have hwn : ‖θ • e‖ = θ := by
    rw [norm_smul, he1, mul_one, Real.norm_of_nonneg hθ0]
  refine ⟨⟨θ • e, hw0⟩, ?_, ?_⟩
  · apply Subtype.ext
    show NormedSpace.exp (θ • e) = q
    rw [Quaternion.exp_of_re_eq_zero _ hw0, hwn, heq]
    by_cases h0 : θ = 0
    · simp [h0]
    · rw [smul_smul, div_mul_cancel₀ _ h0]
  · show ‖θ • e‖ ≤ _
    rw [hwn]
    have hsin : 2 / Real.pi * (θ / 2) ≤ Real.sin (θ / 2) :=
      Real.mul_le_sin (by linarith) (by linarith)
    have hsin0 : 0 ≤ Real.sin (θ / 2) := le_trans (by positivity) hsin
    have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have := Real.cos_two_mul (θ / 2)
      have h2 := Real.sin_sq_add_cos_sq (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at this
      nlinarith
    have hd : ‖q - 1‖ = 2 * Real.sin (θ / 2) := by
      have hsq2 : ‖q - 1‖ ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 := by
        have : ‖q - 1‖ ^ 2 = 2 - 2 * q.re := by nlinarith
        rw [this, ← hc, hcos]
        ring
      exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq2
    rw [hd]
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have hpi0 : 0 < Real.pi := Real.pi_pos
    have h3 : θ / 4 ≤ 2 / Real.pi * (θ / 2) := by
      rw [show 2 / Real.pi * (θ / 2) = θ / Real.pi by field_simp]
      exact div_le_div_of_nonneg_left hθ0 hpi0 hpi
    linarith
end Log
section Paths
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem pathDisplacement_nil (j : ℕ) : pathDisplacement (F := F) j [] = 0 := rfl
theorem pathDisplacement_cons (j : ℕ) (st : PathStep) (l : List PathStep) :
    pathDisplacement (F := F) j (st :: l) = stepDisplacement j st + pathDisplacement j l := by
  simp [pathDisplacement]
theorem pathDisplacement_append (j : ℕ) (l l' : List PathStep) :
    pathDisplacement (F := F) j (l ++ l') = pathDisplacement j l + pathDisplacement j l' := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem stepDisplacement_flip (j : ℕ) (st : PathStep) :
    stepDisplacement (F := F) j (st.1, !st.2) = - stepDisplacement j st := by
  obtain ⟨i, b⟩ := st
  cases b <;> simp [stepDisplacement]
theorem pathDisplacement_reversePath (j : ℕ) (l : List PathStep) :
    pathDisplacement (F := F) j (reversePath l) = - pathDisplacement j l := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_reversePath <;> assumption
theorem stepDisplacement_eq (j : ℕ) (st : PathStep) :
    stepDisplacement (F := F) j st = siteOfCoords j (FlatPairing.stepDisplacement st) := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.stepDisplacement_eq_siteOfCoords <;> assumption
theorem siteOfCoords_endpoint (j : ℕ) (u : Lattice4) (l : List PathStep) :
    siteOfCoords (F := F) j (endpoint u l) = siteOfCoords j u + pathDisplacement j l := by
  induction l generalizing u with
  | nil => simp [endpoint, pathDisplacement]
  | cons st r ih =>
    simp only [endpoint]
    rw [ih, pathDisplacement_cons, siteOfCoords_add, stepDisplacement_eq, add_assoc]
theorem linkValue_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (x : F.Site j) (st : PathStep) :
    linkValue (gaugeTransform γ X) x st = γ x * linkValue X x st * (γ (x + stepDisplacement j st))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_gaugeTransform <;> assumption
theorem pathHolonomy_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomy (gaugeTransform γ X) x l =
      γ x * pathHolonomy X x l * (γ (x + pathDisplacement j l))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_gaugeTransform <;> assumption
theorem pathHolonomy_append {j : ℕ} (X : F.GaugeField j) (l l' : List PathStep) :
    ∀ x : F.Site j, pathHolonomy X x (l ++ l') =
      pathHolonomy X x l * pathHolonomy X (x + pathDisplacement j l) l' := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_append <;> assumption
theorem linkValue_flip {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    linkValue X (x + stepDisplacement j st) (st.1, !st.2) = (linkValue X x st)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_reverse <;> assumption
theorem pathHolonomy_reversePath {j : ℕ} (X : F.GaugeField j) (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomy X (x + pathDisplacement j l) (reversePath l) = (pathHolonomy X x l)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_reversePath <;> assumption
def SitesAlong {j : ℕ} (P : F.Site j → Prop) : F.Site j → List PathStep → Prop
  | x, [] => P x
  | x, st :: r => P x ∧ SitesAlong P (x + stepDisplacement j st) r
theorem sitesAlong_head {j : ℕ} {P : F.Site j → Prop} {x : F.Site j} {l : List PathStep}
    (h : SitesAlong P x l) : P x := by
  cases l with
  | nil => exact h
  | cons st r => exact h.1
theorem sitesAlong_of_allAlong {j : ℕ} (P : F.Site j → Prop) (x0 : F.Site j) {u : Lattice4}
    {l : List PathStep} (h : AllAlong (fun v => P (x0 + siteOfCoords j v)) u l) :
    SitesAlong P (x0 + siteOfCoords j u) l := by
  induction l generalizing u with
  | nil => exact h
  | cons st r ih =>
    refine ⟨h.1, ?_⟩
    have := ih h.2
    rwa [siteOfCoords_add, ← stepDisplacement_eq, ← add_assoc] at this
theorem coe_mul_sub_mul_le (a a' b b' : UnitQuaternion) :
    ‖((a * b : UnitQuaternion) : ℍ[ℝ]) - ((a' * b' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(a : ℍ[ℝ]) - a'‖ + ‖(b : ℍ[ℝ]) - b'‖ := by
  have e : ((a * b : UnitQuaternion) : ℍ[ℝ]) - ((a' * b' : UnitQuaternion) : ℍ[ℝ]) =
      ((a : ℍ[ℝ]) - a') * (b : ℍ[ℝ]) + (a' : ℍ[ℝ]) * ((b : ℍ[ℝ]) - b') := by
    simp only [Submonoid.coe_mul, mul_sub, sub_mul]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, mul_one, one_mul]
theorem coe_inv_sub_inv (a b : UnitQuaternion) :
    ‖((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((b⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(a : ℍ[ℝ]) - b‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
theorem pathHolonomy_close {j : ℕ} {P : F.Site j → Prop} {X Y : F.GaugeField j} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x i, P x → P (x + unitStep j i) → ‖(X x i : ℍ[ℝ]) - (Y x i : ℍ[ℝ])‖ ≤ ε) :
    ∀ (l : List PathStep) (x : F.Site j), SitesAlong P x l →
      ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy Y x l : UnitQuaternion) : ℍ[ℝ])‖ ≤ l.length * ε := by
  intro l
  induction l with
  | nil =>
    intro x _
    simp [pathHolonomy]
  | cons st r ih =>
    intro x hx
    have hnext := sitesAlong_head hx.2
    have hstep : ‖((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) -
        ((linkValue Y x st : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
      obtain ⟨i, b⟩ := st
      cases b
      · simp only [linkValue, Bool.false_eq_true, if_false]
        rw [coe_inv_sub_inv]
        have e1 : x + stepDisplacement j (i, false) = x - unitStep j i := by
          simp [stepDisplacement, sub_eq_add_neg]
        rw [e1] at hnext
        refine h _ i hnext ?_
        rw [sub_add_cancel]
        exact sitesAlong_head hx
      · simp only [linkValue, if_true]
        have e1 : x + stepDisplacement j (i, true) = x + unitStep j i := by
          simp [stepDisplacement]
        rw [e1] at hnext
        exact h x i (sitesAlong_head hx) hnext
    simp only [pathHolonomy]
    refine (coe_mul_sub_mul_le _ _ _ _).trans ?_
    have := ih _ hx.2
    simp only [List.length_cons]
    push_cast
    linarith
theorem pathHolonomy_one {j : ℕ} (l : List PathStep) (x : F.Site j) :
    pathHolonomy (fun _ _ => (1 : UnitQuaternion) : F.GaugeField j) x l = 1 := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    obtain ⟨i, b⟩ := st
    cases b <;> simp [pathHolonomy, linkValue, ih]
theorem pathHolonomy_norm_sub_one_le {j : ℕ} {P : F.Site j → Prop} {X : F.GaugeField j} {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ x i, P x → P (x + unitStep j i) → ‖(X x i : ℍ[ℝ]) - 1‖ ≤ ε)
    (l : List PathStep) (x : F.Site j) (hx : SitesAlong P x l) :
    ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * ε := by
  have := pathHolonomy_close (X := X) (Y := fun _ _ => (1 : UnitQuaternion)) hε
    (fun y i h1 h2 => by simpa using h y i h1 h2) l x hx
  simpa [pathHolonomy_one] using this
end Paths
section Blocks
def blockPoint (y : F.Cell) (h : Lattice4) : F.Site F.depth := cellCentre F.depth y + siteOfCoords F.depth h
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem mem_centredCube_top_iff (h : Lattice4) :
    h ∈ centredCube (F.blockSide ^ (F.top - F.depth)) ↔ h ∈ centredCube F.blockSide := by
  rw [top_sub_depth, pow_one]
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) {j : ℕ} (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h : F.Site j) = z := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_cellCentre_add <;> assumption
theorem enclosingCell_blockPoint (hL : Odd F.blockSide) (y : F.Cell) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) : enclosingCell (blockPoint y h) = y :=
  enclosingCell_cellCentre_add hL y h ((mem_centredCube_top_iff h).2 hh)
theorem period_depth_eq_zero_or (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) (i : Fin 4) :
    F.period F.depth i = 0 ∨ 64 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ) := by
  rcases hamb with h | h
  · left
    simp [BlockFrame.period, h i]
  · right
    have e : ((F.period F.depth i : ℕ) : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) := by
      simp [BlockFrame.period]
    rw [e]
    have : (64 : ℤ) ≤ F.extent i := by exact_mod_cast h i
    nlinarith
theorem valMinAbs_siteOfCoords (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) {A : Lattice4}
    (hA : ∀ i, |A i| < 32 * (F.blockSide : ℤ)) (i : Fin 4) :
    ((siteOfCoords F.depth A : F.Site F.depth) i).valMinAbs = A i := by
  show (((A i : ℤ) : ZMod (F.period F.depth i))).valMinAbs = A i
  apply valMinAbs_intCast_of_small
  rcases period_depth_eq_zero_or hamb hL i with h | h
  · exact Or.inl h
  · right
    have := hA i
    linarith
theorem siteOfCoords_injOn_small (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) {A B : Lattice4}
    (hA : ∀ i, |A i| < 32 * (F.blockSide : ℤ)) (hB : ∀ i, |B i| < 32 * (F.blockSide : ℤ))
    (h : (siteOfCoords F.depth A : F.Site F.depth) = siteOfCoords F.depth B) : A = B := by
  funext i
  rw [← valMinAbs_siteOfCoords hamb hL hA i, ← valMinAbs_siteOfCoords hamb hL hB i, h]
theorem abs_lt_of_mem_centredCube (hL : 0 < F.blockSide) {h : Lattice4} (hh : h ∈ centredCube F.blockSide)
    (i : Fin 4) : |h i| < 32 * (F.blockSide : ℤ) := by
  have h1 := ((mem_centredCube_iff F.blockSide h).1 hh) i
  rw [abs_lt]
  constructor <;> omega
theorem cellOffset_blockPoint (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (y : F.Cell)
    {h : Lattice4} (hh : h ∈ centredCube F.blockSide) : cellOffset (blockPoint y h) = h := by
  funext i
  unfold cellOffset
  rw [enclosingCell_blockPoint hodd y hh]
  have e : blockPoint y h - cellCentre F.depth y = siteOfCoords F.depth h := by
    simp [blockPoint]
  rw [e]
  exact valMinAbs_siteOfCoords hamb hodd.pos (abs_lt_of_mem_centredCube hodd.pos hh) i
theorem blockPoint_add_unitStep (y : F.Cell) (h : Lattice4) (i : Fin 4) :
    blockPoint y h + unitStep F.depth i = blockPoint y (h + basisVector i) := by apply _root_.YangMills.Construction.GaugeFixing.cellCentre_add_siteOfCoords_add_unitStep <;> assumption
theorem blockPoint_neighbour (y : F.Cell) (h : Lattice4) (i : Fin 4) :
    blockPoint (y + siteOfCoords F.top (basisVector i)) h =
      blockPoint y (h + (F.blockSide : ℤ) • basisVector i) := by
  have e := cellCentre_add F.depth (by simp [BlockFrame.top]) y (basisVector i)
  have e2 : (fun l => (F.blockSide : ℤ) ^ (F.top - F.depth) * basisVector i l) =
      (F.blockSide : ℤ) • basisVector i := by
    funext l
    simp [top_sub_depth]
  rw [e2] at e
  simp only [blockPoint]
  rw [e, siteOfCoords_add]
  abel
theorem blockPoint_mem {S : Finset F.Cell} {y : F.Cell} (hy : y ∈ S) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) : blockPoint y h ∈ sitesOfCells S F.depth :=
  mem_sitesOfCells.2 ⟨y, hy, h, (mem_centredCube_top_iff h).2 hh, rfl⟩
theorem exists_blockPoint {S : Finset F.Cell} {x : F.Site F.depth} (hx : x ∈ sitesOfCells S F.depth) :
    ∃ y ∈ S, ∃ h ∈ centredCube F.blockSide, x = blockPoint y h := by
  obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 hx
  exact ⟨y, hy, h, (mem_centredCube_top_iff h).1 hh, e⟩
theorem mem_innerBonds {S : Finset F.Cell} {j : ℕ} {b : F.Site j × Fin 4} :
    b ∈ innerBonds S j ↔ b.1 ∈ sitesOfCells S j ∧ b.1 + unitStep j b.2 ∈ sitesOfCells S j := by
  simp [innerBonds]
def treeGauge (k : F.Cell → UnitQuaternion) (X : F.GaugeField F.depth) (x : F.Site F.depth) :
    UnitQuaternion :=
  k (enclosingCell x) * pathHolonomy X (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) 1)
theorem treeGauge_blockPoint (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (k : F.Cell → UnitQuaternion) (X : F.GaugeField F.depth) (y : F.Cell) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) :
    treeGauge k X (blockPoint y h) = k y * pathHolonomy X (cellCentre F.depth y) (axisPath h 1) := by
  unfold treeGauge
  rw [enclosingCell_blockPoint hodd y hh, cellOffset_blockPoint hamb hodd y hh]
theorem axisPath_zero (π : Equiv.Perm (Fin 4)) : axisPath (0 : Lattice4) π = [] := by apply _root_.YangMills.Construction.GaugeFixing.axisPath_zero <;> assumption
theorem zero_mem_centredCube (hL : 0 < F.blockSide) : (0 : Lattice4) ∈ centredCube F.blockSide := by
  rw [mem_centredCube_iff]
  intro i
  simp only [Pi.zero_apply]
  omega
theorem treeGauge_cellCentre (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (k : F.Cell → UnitQuaternion) (X : F.GaugeField F.depth) (y : F.Cell) :
    treeGauge k X (cellCentre F.depth y) = k y := by
  have e : cellCentre F.depth y = blockPoint y 0 := by simp [blockPoint, siteOfCoords_zero]
  rw [e, treeGauge_blockPoint hamb hodd k X y (zero_mem_centredCube hodd.pos), axisPath_zero]
  simp [pathHolonomy]
theorem pathDisplacement_axisPath (j : ℕ) (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    pathDisplacement (F := F) j (axisPath h π) = siteOfCoords j h := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_axisPath <;> assumption
def blockLoop (h : Lattice4) (i : Fin 4) : List PathStep :=
  axisPath h 1 ++ ((i, true) :: reversePath (axisPath (h + basisVector i) 1))
theorem pathHolonomy_blockLoop (X : F.GaugeField F.depth) (y : F.Cell) (h : Lattice4) (i : Fin 4) :
    pathHolonomy X (cellCentre F.depth y) (blockLoop h i) =
      pathHolonomy X (cellCentre F.depth y) (axisPath h 1) * X (blockPoint y h) i *
        (pathHolonomy X (cellCentre F.depth y) (axisPath (h + basisVector i) 1))⁻¹ := by
  unfold blockLoop
  rw [pathHolonomy_append, pathDisplacement_axisPath]
  simp only [pathHolonomy]
  have e : cellCentre F.depth y + siteOfCoords F.depth h + stepDisplacement F.depth (i, true) =
      cellCentre F.depth y + pathDisplacement F.depth (axisPath (h + basisVector i) 1) := by
    rw [pathDisplacement_axisPath, siteOfCoords_add, ← unitStep_eq]
    simp [stepDisplacement, add_assoc]
  rw [e, pathHolonomy_reversePath, ← mul_assoc]
  rfl
theorem pathDisplacement_blockLoop (h : Lattice4) (i : Fin 4) :
    pathDisplacement (F := F) F.depth (blockLoop h i) = 0 := by
  unfold blockLoop
  rw [pathDisplacement_append, pathDisplacement_cons, pathDisplacement_reversePath,
    pathDisplacement_axisPath, pathDisplacement_axisPath, siteOfCoords_add, ← unitStep_eq]
  simp [stepDisplacement]
theorem mem_centredCube_of_between {L : ℕ} {h v : Lattice4} (hh : h ∈ centredCube L)
    (hv : BetweenOrigin h v) (hL : 1 ≤ L) : v ∈ centredCube L := by
  rw [mem_centredCube_iff]
  intro μ
  have h1 := ((mem_centredCube_iff L h).1 hh) μ
  have h2 := hv μ
  have hk : (0 : ℤ) ≤ ((L : ℤ) - 1) / 2 := by omega
  have a1 : min 0 (h μ) ≥ -(((L : ℤ) - 1) / 2) := le_min (by omega) h1.1
  have a2 : max 0 (h μ) ≤ ((L : ℤ) - 1) / 2 := max_le hk h1.2
  constructor <;> omega
theorem allAlong_blockLoop {L : ℕ} (hL : 1 ≤ L) {h : Lattice4} {i : Fin 4} (hh : h ∈ centredCube L)
    (hh' : h + basisVector i ∈ centredCube L) :
    AllAlong (fun v => v ∈ centredCube L) 0 (blockLoop h i) := by
  have q1 : AllAlong (fun v => v ∈ centredCube L) 0 (axisPath h 1) :=
    allAlong_mono (fun v hv => mem_centredCube_of_between hh hv hL) (axisPath_spec h 1).1
  have q2 : AllAlong (fun v => v ∈ centredCube L) 0 (axisPath (h + basisVector i) 1) :=
    allAlong_mono (fun v hv => mem_centredCube_of_between hh' hv hL) (axisPath_spec (h + basisVector i) 1).1
  have q3 := allAlong_reversePath q2
  rw [(axisPath_spec (h + basisVector i) 1).2] at q3
  refine allAlong_append q1 ?_
  rw [(axisPath_spec h 1).2]
  refine ⟨hh, ?_⟩
  have e : FlatPairing.stepDisplacement (i, true) = basisVector i := by simp [FlatPairing.stepDisplacement]
  rw [e]
  exact q3
theorem length_axisPath_le {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (π : Equiv.Perm (Fin 4)) :
    (axisPath h π).length ≤ 2 * (L - 1) := by
  have hlen : ∀ μ, (h μ).natAbs ≤ (L - 1) / 2 := by
    intro μ
    have h1 := ((mem_centredCube_iff L h).1 hh) μ
    omega
  have h0 := hlen (π 0)
  have h1 := hlen (π 1)
  have h2 := hlen (π 2)
  have h3 := hlen (π 3)
  rw [length_axisPath]
  omega
theorem length_blockLoop_le {L : ℕ} (hL : 1 ≤ L) {h : Lattice4} {i : Fin 4} (hh : h ∈ centredCube L)
    (hh' : h + basisVector i ∈ centredCube L) : (blockLoop h i).length ≤ 5 * L := by
  have h1 := length_axisPath_le hh 1
  have h2 := length_axisPath_le hh' 1
  have e : (blockLoop h i).length =
      (axisPath h 1).length + 1 + (axisPath (h + basisVector i) 1).length := by
    simp [blockLoop, reversePath]
    omega
  omega
theorem blockLoop_norm_sub_one_le {R X : F.GaugeField F.depth} {g : F.Site F.depth → UnitQuaternion}
    {ε e : ℝ} (hε : 0 ≤ ε) (he : 0 ≤ e) (hL : 1 ≤ F.blockSide) {y : F.Cell} {P : F.Site F.depth → Prop}
    (hP : ∀ h ∈ centredCube F.blockSide, P (blockPoint y h))
    (hXR : ∀ x i, P x → P (x + unitStep F.depth i) → ‖(X x i : ℍ[ℝ]) - (R x i : ℍ[ℝ])‖ ≤ ε)
    (hRf : ∀ x i, P x → P (x + unitStep F.depth i) →
      ‖((gaugeTransform g R x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e)
    {h : Lattice4} {i : Fin 4} (hh : h ∈ centredCube F.blockSide)
    (hh' : h + basisVector i ∈ centredCube F.blockSide) :
    ‖((pathHolonomy X (cellCentre F.depth y) (blockLoop h i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      5 * F.blockSide * (ε + e) := by
  have hs : SitesAlong P (cellCentre F.depth y) (blockLoop h i) := by
    have := sitesAlong_of_allAlong P (cellCentre F.depth y) (u := 0)
      (allAlong_mono (fun v hv => hP v hv) (allAlong_blockLoop hL hh hh'))
    simpa [siteOfCoords_zero] using this
  have c1 := pathHolonomy_close hε hXR _ _ hs
  have c2 := pathHolonomy_norm_sub_one_le he hRf _ _ hs
  have c3 : ‖((pathHolonomy R (cellCentre F.depth y) (blockLoop h i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      (blockLoop h i).length * e := by
    rw [pathHolonomy_gaugeTransform, pathDisplacement_blockLoop, add_zero, norm_coe_conj_sub_one] at c2
    exact c2
  have hlen : (((blockLoop h i).length : ℕ) : ℝ) ≤ 5 * F.blockSide := by
    exact_mod_cast length_blockLoop_le hL hh hh'
  calc ‖((pathHolonomy X (cellCentre F.depth y) (blockLoop h i) : UnitQuaternion) : ℍ[ℝ]) - 1‖
      ≤ ‖((pathHolonomy X (cellCentre F.depth y) (blockLoop h i) : UnitQuaternion) : ℍ[ℝ]) -
          ((pathHolonomy R (cellCentre F.depth y) (blockLoop h i) : UnitQuaternion) : ℍ[ℝ])‖ +
        ‖((pathHolonomy R (cellCentre F.depth y) (blockLoop h i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (blockLoop h i).length * ε + (blockLoop h i).length * e := add_le_add c1 c3
    _ = (blockLoop h i).length * (ε + e) := by ring
    _ ≤ 5 * F.blockSide * (ε + e) := mul_le_mul_of_nonneg_right hlen (by positivity)
theorem treeGauge_inner (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (k : F.Cell → UnitQuaternion) (X : F.GaugeField F.depth) (y : F.Cell) {h : Lattice4} {i : Fin 4}
    (hh : h ∈ centredCube F.blockSide) (hh' : h + basisVector i ∈ centredCube F.blockSide) :
    gaugeTransform (treeGauge k X) X (blockPoint y h) i =
      k y * pathHolonomy X (cellCentre F.depth y) (blockLoop h i) * (k y)⁻¹ := by
  unfold gaugeTransform
  rw [blockPoint_add_unitStep, treeGauge_blockPoint hamb hodd k X y hh,
    treeGauge_blockPoint hamb hodd k X y hh', pathHolonomy_blockLoop]
  group
theorem fin_four_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by apply _root_.YangMills.Construction.GaugeFixing.fin_four_cases <;> assumption
theorem axisPath_add_basisVector_of_nonneg {h : Lattice4} {i : Fin 4} (hl : ∀ l, i < l → h l = 0)
    (h0 : 0 ≤ h i) : axisPath (h + basisVector i) 1 = axisPath h 1 ++ [(i, true)] := by apply _root_.YangMills.Construction.GaugeFixing.axisPath_add_single_of_nonneg <;> assumption
theorem axisPath_of_neg {h : Lattice4} {i : Fin 4} (hl : ∀ l, i < l → h l = 0) (h0 : h i < 0) :
    axisPath h 1 = axisPath (h + basisVector i) 1 ++ [(i, false)] := by apply _root_.YangMills.Construction.GaugeFixing.axisPath_of_neg <;> assumption
theorem pathHolonomy_blockLoop_tree (X : F.GaugeField F.depth) (y : F.Cell) {h : Lattice4} {i : Fin 4}
    (hl : ∀ l, i < l → h l = 0) :
    pathHolonomy X (cellCentre F.depth y) (blockLoop h i) = 1 := by
  rw [pathHolonomy_blockLoop]
  by_cases h0 : 0 ≤ h i
  · rw [axisPath_add_basisVector_of_nonneg hl h0, pathHolonomy_append, pathDisplacement_axisPath]
    simp only [pathHolonomy, linkValue, if_true, mul_one]
    have e : blockPoint y h = cellCentre F.depth y + siteOfCoords F.depth h := rfl
    rw [e]
    group
  · rw [axisPath_of_neg hl (not_le.1 h0), pathHolonomy_append, pathDisplacement_axisPath]
    simp only [pathHolonomy, linkValue, Bool.false_eq_true, if_false, mul_one]
    have e : blockPoint y h =
        cellCentre F.depth y + siteOfCoords F.depth (h + basisVector i) - unitStep F.depth i := by
      simp only [blockPoint]
      rw [siteOfCoords_add, ← unitStep_eq]
      abel
    rw [← e]
    group
end Blocks
section Crossing
theorem coe_mul_inv_sub_one (a b : UnitQuaternion) :
    ‖((a * b⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(a : ℍ[ℝ]) - (b : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.GaugeFixing.norm_mul_inv_sub_one <;> assumption
theorem polarUnit_dist_le {a b : ℍ[ℝ]} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖((polarUnit a : UnitQuaternion) : ℍ[ℝ]) - ((polarUnit b : UnitQuaternion) : ℍ[ℝ])‖ ≤
      2 * ‖a - b‖ / ‖b‖ := by
  have na : 0 < ‖a‖ := norm_pos_iff.2 ha
  have nb : 0 < ‖b‖ := norm_pos_iff.2 hb
  rw [coe_polarUnit ha, coe_polarUnit hb]
  have e : ‖a‖⁻¹ • a - ‖b‖⁻¹ • b = (‖a‖⁻¹ - ‖b‖⁻¹) • a + ‖b‖⁻¹ • (a - b) := by
    rw [sub_smul, smul_sub]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 nb)]
  have e2 : |‖a‖⁻¹ - ‖b‖⁻¹| * ‖a‖ = |‖b‖ - ‖a‖| / ‖b‖ := by
    have : ‖a‖⁻¹ - ‖b‖⁻¹ = (‖b‖ - ‖a‖) / (‖a‖ * ‖b‖) := by
      field_simp
    rw [this, abs_div, abs_of_pos (mul_pos na nb)]
    field_simp
  rw [e2]
  have e3 : |‖b‖ - ‖a‖| ≤ ‖a - b‖ := by
    rw [abs_sub_comm]
    exact abs_norm_sub_norm_le a b
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hi := (inv_pos.2 nb).le
  nlinarith [mul_le_mul_of_nonneg_right e3 hi]
theorem contourAverage_dist_le {X Y : F.GaugeField F.depth} {c : F.Site (F.depth + 1) × Fin 4} {B : ℝ}
    (hodd : Odd F.blockSide)
    (h : ∀ u ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy X (refineSite c.1) (bondContour F.blockSide u π c.2) : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy Y (refineSite c.1) (bondContour F.blockSide u π c.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤ B)
    (hB : 0 ≤ B) :
    ‖contourAverage X c - contourAverage Y c‖ ≤ B := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  unfold contourAverage
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul]
  have hs : ‖∑ u ∈ centredCube F.blockSide, ((∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide u π c.2) : UnitQuaternion) : ℍ[ℝ])) -
      ∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy Y (refineSite c.1) (bondContour F.blockSide u π c.2) : UnitQuaternion) : ℍ[ℝ]))‖ ≤
      24 * (F.blockSide : ℝ) ^ 4 * B := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ u ∈ centredCube F.blockSide, ‖(∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide u π c.2) : UnitQuaternion) : ℍ[ℝ])) -
      ∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy Y (refineSite c.1) (bondContour F.blockSide u π c.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤
        24 * B := by
      intro u hu
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun π _ => h u hu π).trans ?_
      simp [Finset.card_univ, Fintype.card_perm, Nat.factorial]
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, card_centredCube hodd, nsmul_eq_mul]
    push_cast
    linarith
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc (1 / (24 * (F.blockSide : ℝ) ^ 4)) * _ ≤
        (1 / (24 * (F.blockSide : ℝ) ^ 4)) * (24 * (F.blockSide : ℝ) ^ 4 * B) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = B := by field_simp
theorem blockPoint_mem_of_hull {S : Finset F.Cell} {y : F.Cell} {i : Fin 4} (hodd : Odd F.blockSide)
    (hy : y ∈ S) (hE : y + siteOfCoords F.top (basisVector i) ∈ S) {u : Lattice4}
    (hu : u ∈ FlatPairing.twoBlockHull F.blockSide i) :
    blockPoint y u ∈ sitesOfCells S F.depth := by
  obtain ⟨m, hm⟩ := hodd
  have hM : ((F.blockSide : ℤ) - 1) / 2 = m := by omega
  by_cases hc : u i ≤ ((F.blockSide : ℤ) - 1) / 2
  · refine blockPoint_mem hy ?_
    rw [mem_centredCube_iff]
    intro μ
    have := hu μ
    by_cases hμ : μ = i
    · subst hμ
      simp only [if_true] at this
      exact ⟨this.1, hc⟩
    · simpa [hμ] using this
  · have e : blockPoint y u =
        blockPoint (y + siteOfCoords F.top (basisVector i)) (u - (F.blockSide : ℤ) • basisVector i) := by
      rw [blockPoint_neighbour, sub_add_cancel]
    rw [e]
    refine blockPoint_mem hE ?_
    rw [mem_centredCube_iff]
    intro μ
    have := hu μ
    by_cases hμ : μ = i
    · subst hμ
      simp only [if_true] at this
      simp only [Pi.sub_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one]
      omega
    · have e2 : (u - (F.blockSide : ℤ) • basisVector i) μ = u μ := by
        simp [basisVector, hμ]
      rw [e2]
      simpa [hμ] using this
theorem bondContour_dist_le {S : Finset F.Cell} {X R : F.GaugeField F.depth} {ε : ℝ} (hε : 0 ≤ ε)
    (hodd : Odd F.blockSide)
    (hXR : ∀ b ∈ innerBonds S F.depth, ‖(X b.1 b.2 : ℍ[ℝ]) - (R b.1 b.2 : ℍ[ℝ])‖ ≤ ε) {y : F.Cell}
    {i : Fin 4} (hy : y ∈ S) (hE : y + siteOfCoords F.top (basisVector i) ∈ S) {u : Lattice4}
    (hu : u ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    ‖((pathHolonomy X (cellCentre F.depth y) (bondContour F.blockSide u π i) : UnitQuaternion) : ℍ[ℝ]) -
      ((pathHolonomy R (cellCentre F.depth y) (bondContour F.blockSide u π i) : UnitQuaternion) : ℍ[ℝ])‖ ≤
      5 * F.blockSide * ε := by
  have hs : SitesAlong (fun x => x ∈ sitesOfCells S F.depth) (cellCentre F.depth y)
      (bondContour F.blockSide u π i) := by
    have := sitesAlong_of_allAlong (fun x => x ∈ sitesOfCells S F.depth) (cellCentre F.depth y) (u := 0)
      (allAlong_mono (fun v hv => blockPoint_mem_of_hull hodd hy hE hv)
        (bondContour_spec π i hodd.pos hu).1)
    simpa [siteOfCoords_zero] using this
  have c1 := pathHolonomy_close (P := fun x => x ∈ sitesOfCells S F.depth) hε
    (fun x l h1 h2 => hXR (x, l) (mem_innerBonds.2 ⟨h1, h2⟩)) _ _ hs
  have hlen : (((bondContour F.blockSide u π i).length : ℕ) : ℝ) ≤ 5 * F.blockSide := by
    exact_mod_cast length_bondContour_le π i hodd.pos hu
  exact c1.trans (mul_le_mul_of_nonneg_right hlen hε)
theorem refineSite_eq_cellCentre (y : F.Cell) : refineSite y = cellCentre F.depth y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
theorem polarUnit_conj {q : ℍ[ℝ]} (hq : q ≠ 0) (a b : UnitQuaternion) :
    polarUnit ((a : ℍ[ℝ]) * q * ((b⁻¹ : UnitQuaternion) : ℍ[ℝ])) = a * polarUnit q * b⁻¹ := by
  have hn : ‖(a : ℍ[ℝ]) * q * ((b⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖q‖ := by
    rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
  have h0 : (a : ℍ[ℝ]) * q * ((b⁻¹ : UnitQuaternion) : ℍ[ℝ]) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact hq (norm_eq_zero.1 hn.symm)
  apply Subtype.ext
  rw [coe_polarUnit h0, hn]
  simp only [Submonoid.coe_mul]
  rw [coe_polarUnit hq]
  simp only [mul_smul_comm, smul_mul_assoc]
end Crossing
section Value
theorem pathDisplacement_replicate (j : ℕ) (n : ℕ) (st : PathStep) :
    pathDisplacement (F := F) j (List.replicate n st) =
      siteOfCoords j ((n : ℤ) • FlatPairing.stepDisplacement st) := by
  have := siteOfCoords_endpoint (F := F) j 0 (List.replicate n st)
  rw [endpoint_replicate, siteOfCoords_zero, zero_add, zero_add] at this
  exact this.symm
theorem crossing_bondContour (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (k : F.Cell → UnitQuaternion) (X : F.GaugeField F.depth) (y : F.Cell) {h : Lattice4} {i : Fin 4}
    (hh : h ∈ centredCube F.blockSide) :
    k y * pathHolonomy X (cellCentre F.depth y) (bondContour F.blockSide h 1 i) *
        (k (y + siteOfCoords F.top (basisVector i)))⁻¹ =
      gaugeTransform (treeGauge k X) X (blockPoint y h) i *
        pathHolonomy (gaugeTransform (treeGauge k X) X)
          (blockPoint (y + siteOfCoords F.top (basisVector i))
            (h + basisVector i - (F.blockSide : ℤ) • basisVector i))
          (List.replicate (F.blockSide - 1) (i, true)) := by
  set E := y + siteOfCoords F.top (basisVector i) with hE
  set h1 := h + basisVector i - (F.blockSide : ℤ) • basisVector i with hh1
  have hpos := hodd.pos
  have e0 : FlatPairing.stepDisplacement (i, true) = basisVector i := by simp [FlatPairing.stepDisplacement]
  have e1 : blockPoint y h + unitStep F.depth i = blockPoint E h1 := by
    rw [hE, blockPoint_neighbour, blockPoint_add_unitStep, hh1, sub_add_cancel]
  have e2 : blockPoint E h1 + pathDisplacement F.depth (List.replicate (F.blockSide - 1) (i, true)) =
      blockPoint E h := by
    rw [pathDisplacement_replicate, e0]
    simp only [blockPoint]
    rw [add_assoc, ← siteOfCoords_add]
    congr 2
    funext l
    have hc : ((F.blockSide - 1 : ℕ) : ℤ) = (F.blockSide : ℤ) - 1 := by
      omega
    simp only [hh1, hc, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e3 : cellCentre F.depth y +
      pathDisplacement F.depth (axisPath h 1 ++ List.replicate F.blockSide (i, true)) =
      cellCentre F.depth E + pathDisplacement F.depth (axisPath h 1) := by
    rw [pathDisplacement_append, pathDisplacement_axisPath, pathDisplacement_replicate, e0]
    have := blockPoint_neighbour y h i
    rw [← hE] at this
    simp only [blockPoint] at this
    rw [this, siteOfCoords_add]
  have c1 : List.replicate F.blockSide ((i, true) : PathStep) =
      (i, true) :: List.replicate (F.blockSide - 1) (i, true) := by
    have : F.blockSide = (F.blockSide - 1) + 1 := by omega
    exact (congrArg (fun n => List.replicate n ((i, true) : PathStep)) this).trans (List.replicate_succ ..)
  have hc : pathHolonomy X (cellCentre F.depth y) (bondContour F.blockSide h 1 i) =
      pathHolonomy X (cellCentre F.depth y) (axisPath h 1) * (X (blockPoint y h) i *
        pathHolonomy X (blockPoint E h1) (List.replicate (F.blockSide - 1) (i, true))) *
        (pathHolonomy X (cellCentre F.depth E) (axisPath h 1))⁻¹ := by
    unfold bondContour
    rw [pathHolonomy_append, e3, pathHolonomy_reversePath, pathHolonomy_append, pathDisplacement_axisPath, c1]
    simp only [pathHolonomy]
    have e4 : cellCentre F.depth y + siteOfCoords F.depth h + stepDisplacement F.depth (i, true) =
        blockPoint E h1 := by
      rw [← e1]
      simp [stepDisplacement, blockPoint]
    rw [e4]
    simp [linkValue, blockPoint]
  rw [hc, pathHolonomy_gaugeTransform, e2]
  unfold gaugeTransform
  rw [e1, treeGauge_blockPoint hamb hodd k X y hh, treeGauge_blockPoint hamb hodd k X E hh]
  group
theorem bond_cases (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {S : Finset F.Cell}
    {y : F.Cell} {h : Lattice4} {i : Fin 4} (hh : h ∈ centredCube F.blockSide)
    (hb : blockPoint y h + unitStep F.depth i ∈ sitesOfCells S F.depth) :
    (h + basisVector i ∈ centredCube F.blockSide ∧ ¬ IsCrossingBond (blockPoint y h, i)) ∨
      (IsCrossingBond (blockPoint y h, i) ∧ h i = ((F.blockSide : ℤ) - 1) / 2 ∧
        y + siteOfCoords F.top (basisVector i) ∈ S ∧
        h + basisVector i - (F.blockSide : ℤ) • basisVector i ∈ centredCube F.blockSide) := by
  by_cases hc : h + basisVector i ∈ centredCube F.blockSide
  · left
    refine ⟨hc, ?_⟩
    unfold IsCrossingBond
    simp only [ne_eq, not_not]
    rw [blockPoint_add_unitStep, enclosingCell_blockPoint hodd y hc, enclosingCell_blockPoint hodd y hh]
  · right
    obtain ⟨m, hm⟩ := id hodd
    have hM : ((F.blockSide : ℤ) - 1) / 2 = m := by omega
    have hcube := (mem_centredCube_iff F.blockSide h).1 hh
    have hi : h i = ((F.blockSide : ℤ) - 1) / 2 := by
      by_contra hne
      apply hc
      rw [mem_centredCube_iff]
      intro μ
      have h1 := hcube μ
      by_cases hμ : μ = i
      · subst hμ
        have e : (h + basisVector μ) μ = h μ + 1 := by simp [basisVector]
        rw [e]
        omega
      · have e : (h + basisVector i) μ = h μ := by simp [basisVector, hμ]
        rw [e]
        exact h1
    set E := y + siteOfCoords F.top (basisVector i) with hE
    have h1c : h + basisVector i - (F.blockSide : ℤ) • basisVector i ∈ centredCube F.blockSide := by
      rw [mem_centredCube_iff]
      intro μ
      have h1 := hcube μ
      by_cases hμ : μ = i
      · subst hμ
        have e : (h + basisVector μ - (F.blockSide : ℤ) • basisVector μ) μ = h μ + 1 - (F.blockSide : ℤ) := by
          simp [basisVector]
        rw [e]
        omega
      · have e : (h + basisVector i - (F.blockSide : ℤ) • basisVector i) μ = h μ := by
          simp [basisVector, hμ]
        rw [e]
        exact h1
    have hsite : blockPoint y h + unitStep F.depth i =
        blockPoint E (h + basisVector i - (F.blockSide : ℤ) • basisVector i) := by
      rw [hE, blockPoint_neighbour, blockPoint_add_unitStep, sub_add_cancel]
    have hcell : enclosingCell (blockPoint y h + unitStep F.depth i) = E := by
      rw [hsite, enclosingCell_blockPoint hodd E h1c]
    obtain ⟨y', hy', u, hu, e'⟩ := exists_blockPoint hb
    have hyE : y' = E := by
      rw [← hcell, e', enclosingCell_blockPoint hodd y' hu]
    refine ⟨?_, hi, hyE ▸ hy', h1c⟩
    unfold IsCrossingBond
    simp only [ne_eq]
    rw [hcell, enclosingCell_blockPoint hodd y hh, hE]
    intro hEq
    have h0 : (siteOfCoords F.top (basisVector i) : F.Cell) = 0 := by simpa using hEq
    have h2 := congrFun h0 i
    have h3 := valMinAbs_cell_of_small hamb i (A := 1) (by norm_num)
    have h4 : ((siteOfCoords F.top (basisVector i) : F.Cell) i) = ((1 : ℤ) : ZMod (F.period F.top i)) := by
      simp [siteOfCoords, basisVector]
    rw [h4] at h2
    rw [h2] at h3
    simp at h3
theorem exists_chart (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {S : Finset F.Cell}
    {V : F.GaugeField F.top} {X : F.GaugeField F.depth} {k : F.Cell → UnitQuaternion} {Nc Nx : ℝ}
    (hc0 : 0 ≤ Nc) (hx0 : 0 ≤ Nx)
    (hNc : ∀ y ∈ S, ∀ (h : Lattice4) (i : Fin 4), h ∈ centredCube F.blockSide →
      h + basisVector i ∈ centredCube F.blockSide →
      ‖((pathHolonomy X (cellCentre F.depth y) (blockLoop h i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Nc)
    (hNx : ∀ y ∈ S, ∀ (h : Lattice4) (i : Fin 4), h ∈ centredCube F.blockSide →
      y + siteOfCoords F.top (basisVector i) ∈ S →
      ‖((k y * pathHolonomy X (cellCentre F.depth y) (bondContour F.blockSide h 1 i) *
          (k (y + siteOfCoords F.top (basisVector i)))⁻¹ * (V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Nx) :
    ∃ w : F.Site F.depth → Fin 4 → imaginaryQuaternions,
      (∀ b, b ∉ chordBonds S → w b.1 b.2 = 0) ∧
      (∀ b ∈ chordBonds S, ‖w b.1 b.2‖ ≤ 2 * (Nx + F.blockSide * Nc)) ∧
      AgreeOnBonds S F.depth (chartedField w V) (gaugeTransform (treeGauge k X) X) := by
  classical
  choose lg hlg1 hlg2 using exists_expUnit_eq
  set W := gaugeTransform (treeGauge k X) X with hW
  have hLr : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hinner : ∀ y ∈ S, ∀ (h : Lattice4) (i : Fin 4), h ∈ centredCube F.blockSide →
      h + basisVector i ∈ centredCube F.blockSide →
      ‖((W (blockPoint y h) i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Nc := by
    intro y hy h i hh hh'
    rw [hW, treeGauge_inner hamb hodd k X y hh hh', norm_coe_conj_sub_one]
    exact hNc y hy h i hh hh'
  refine ⟨fun x i => if (x, i) ∈ chordBonds S then
      (if IsCrossingBond (x, i) then lg (W x i * (V (enclosingCell x) i)⁻¹) else lg (W x i)) else 0,
    fun b hb => ?_, fun b hb => ?_, fun b hb => ?_⟩
  · have : (b.1, b.2) ∉ chordBonds S := hb
    simp [this]
  · obtain ⟨x, i⟩ := b
    have hbb : (x, i) ∈ innerBonds S F.depth := (Finset.mem_filter.1 hb).1
    obtain ⟨hx1, hx2⟩ := mem_innerBonds.1 hbb
    obtain ⟨y, hy, h, hh, rfl⟩ := exists_blockPoint hx1
    simp only [hb, if_true]
    have hNnn : 0 ≤ Nx + F.blockSide * Nc := by positivity
    rcases bond_cases hamb hodd (i := i) hh hx2 with ⟨hc, hnc⟩ | ⟨hcr, hi, hE, h1c⟩
    · simp only [hnc, if_false]
      have := hlg2 (W (blockPoint y h) i)
      have h2 := hinner y hy h i hh hc
      have h3 : Nc ≤ Nx + F.blockSide * Nc := by nlinarith
      exact this.trans (by linarith)
    · simp only [hcr, if_true]
      rw [enclosingCell_blockPoint hodd y hh]
      set E := y + siteOfCoords F.top (basisVector i) with hEdef
      set h1 := h + basisVector i - (F.blockSide : ℤ) • basisVector i with hh1
      set H := pathHolonomy W (blockPoint E h1) (List.replicate (F.blockSide - 1) (i, true)) with hH
      have hA := crossing_bondContour hamb hodd k X y hh (i := i)
      rw [← hEdef, ← hh1, ← hW, ← hH] at hA
      have hP : SitesAlong (fun x => ∃ u ∈ centredCube F.blockSide, x = blockPoint E u) (blockPoint E h1)
          (List.replicate (F.blockSide - 1) (i, true)) := by
        refine sitesAlong_of_allAlong _ (cellCentre F.depth E) (allAlong_replicate fun m hm => ⟨_, ?_, rfl⟩)
        have e0 : FlatPairing.stepDisplacement (i, true) = basisVector i := by
          simp [FlatPairing.stepDisplacement]
        rw [e0]
        obtain ⟨q, hq⟩ := id hodd
        have hM : ((F.blockSide : ℤ) - 1) / 2 = q := by omega
        have hc1 := (mem_centredCube_iff F.blockSide h1).1 h1c
        rw [mem_centredCube_iff]
        intro μ
        have h2 := hc1 μ
        by_cases hμ : μ = i
        · subst hμ
          have e : (h1 + (m : ℤ) • basisVector μ) μ = h1 μ + m := by simp [basisVector]
          have e' : h1 μ = h μ + 1 - (F.blockSide : ℤ) := by simp [hh1, basisVector]
          rw [e]
          omega
        · have e : (h1 + (m : ℤ) • basisVector i) μ = h1 μ := by simp [basisVector, hμ]
          rw [e]
          exact h2
      have hHs : ‖((H : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ (F.blockSide - 1 : ℕ) * Nc := by
        have := pathHolonomy_norm_sub_one_le
          (P := fun x => ∃ u ∈ centredCube F.blockSide, x = blockPoint E u) (X := W) hc0
          (fun x l h1' h2' => by
            obtain ⟨u, hu, rfl⟩ := h1'
            obtain ⟨u', hu', e'⟩ := h2'
            have e1 : u + basisVector l = u' := by
              rw [blockPoint_add_unitStep] at e'
              simp only [blockPoint] at e'
              refine siteOfCoords_injOn_small hamb hodd.pos (fun μ => ?_)
                (abs_lt_of_mem_centredCube hodd.pos hu') (add_left_cancel e')
              have h1 := ((mem_centredCube_iff F.blockSide u).1 hu) μ
              have hp : (1 : ℤ) ≤ (F.blockSide : ℤ) := by exact_mod_cast hodd.pos
              have h2 : |basisVector l μ| ≤ 1 := by
                by_cases hμ : μ = l
                · subst hμ
                  simp [basisVector]
                · simp [basisVector, hμ]
              have h3 := abs_le.1 h2
              rw [abs_lt]
              simp only [Pi.add_apply]
              constructor <;> omega
            exact hinner E hE u l hu (e1 ▸ hu')) _ _ hP
        simpa using this
      have hL1 : (((F.blockSide - 1 : ℕ) : ℝ)) ≤ F.blockSide := by
        exact_mod_cast Nat.sub_le _ _
      have hprod : ((W (blockPoint y h) i * (V y i)⁻¹ : UnitQuaternion)) =
          ((k y * pathHolonomy X (cellCentre F.depth y) (bondContour F.blockSide h 1 i) * (k E)⁻¹) *
            (V y i)⁻¹) * ((V y i) * H⁻¹ * (V y i)⁻¹) := by
        rw [hA]
        group
      have hs : ‖((W (blockPoint y h) i * (V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
          Nx + F.blockSide * Nc := by
        rw [hprod]
        refine (norm_coe_mul_sub_one_le _ _).trans ?_
        rw [norm_coe_conj_sub_one, norm_coe_inv_sub_one]
        have := hNx y hy h i hh hE
        have h3 : ((F.blockSide - 1 : ℕ) : ℝ) * Nc ≤ F.blockSide * Nc := mul_le_mul_of_nonneg_right hL1 hc0
        linarith
      exact (hlg2 _).trans (by linarith)
  · obtain ⟨x, i⟩ := b
    obtain ⟨hx1, hx2⟩ := mem_innerBonds.1 hb
    obtain ⟨y, hy, h, hh, rfl⟩ := exists_blockPoint hx1
    show chartedField _ V (blockPoint y h) i = W (blockPoint y h) i
    unfold chartedField
    rcases bond_cases hamb hodd (i := i) hh hx2 with ⟨hc, hnc⟩ | ⟨hcr, hi, hE, h1c⟩
    · rw [if_neg hnc]
      by_cases ht : IsAxialTreeBond (blockPoint y h, i)
      · rw [if_pos ht, hW, treeGauge_inner hamb hodd k X y hh hc, pathHolonomy_blockLoop_tree]
        · simp
        · intro l hl
          have := ht.2 l hl
          rwa [cellOffset_blockPoint hamb hodd y hh] at this
      · rw [if_neg ht]
        have hmem : (blockPoint y h, i) ∈ chordBonds S :=
          Finset.mem_filter.2 ⟨hb, ht⟩
        simp only [hmem, if_true, hnc, if_false]
        exact hlg1 _
    · rw [if_pos hcr]
      have hmem : (blockPoint y h, i) ∈ chordBonds S :=
        Finset.mem_filter.2 ⟨hb, fun ht => ht.1 hcr⟩
      simp only [hmem, if_true, hcr]
      rw [hlg1, enclosingCell_blockPoint hodd y hh]
      group
end Value
section Energy
theorem gaugedBlockFit_gaugeTransform {j : ℕ} (γ : F.Site (j + 1) → UnitQuaternion) (X : F.GaugeField j)
    (k : F.Site (j + 1) → UnitQuaternion) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    gaugedBlockFit X (fun y => γ y * k y) (gaugeTransform γ X') c = gaugedBlockFit X k X' c := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.gaugedBlockFit_gaugeTransform <;> assumption
def partialGaugedTotal (a : ℝ) (S : Finset F.Cell) (X : F.FieldChain) (k : F.SiteGauge) (j : ℕ) : ℝ :=
  wilsonAction S (X 0) + a * ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1),
    gaugedBlockFit (X i) (k (i + 1)) (X (i + 1)) c
theorem wilsonAction_gaugeTransform (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide)
    (S : Finset F.Cell) (γ : F.Site 0 → UnitQuaternion) (U : F.GaugeField 0) :
    wilsonAction S (gaugeTransform γ U) = wilsonAction S U := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.wilsonAction_gaugeTransform <;> assumption
theorem blockFit_gaugeTransform (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide) {j : ℕ}
    (hj : j < F.top) (γ : F.Site j → UnitQuaternion) (k : F.Site (j + 1) → UnitQuaternion)
    (hγ : ∀ y, γ (refineSite y) = k y) (X : F.GaugeField j) (X' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) :
    blockFit (gaugeTransform γ X) X' c = gaugedBlockFit X k X' c := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.blockFit_gaugeTransform_eq <;> assumption
theorem minimalAction_step_le (hG : gaugeCovarianceStatement) (a : ℝ) (hL : 0 < F.blockSide)
    (S : Finset F.Cell) {j : ℕ} (hj : j < F.top)
    (ih : ∀ (X : F.FieldChain) (k : F.SiteGauge), minimalAction a S j (X j) ≤ partialGaugedTotal a S X k j)
    (ha : 0 ≤ a) (X : F.FieldChain) (k : F.SiteGauge) (γ : F.Site j → UnitQuaternion)
    (hγd : ∀ y, γ (refineSite y) = k (j + 1) y) :
    minimalAction a S j (gaugeTransform γ (X j)) +
        a * ∑ c ∈ innerBonds S (j + 1), blockFit (gaugeTransform γ (X j)) (X (j + 1)) c ≤
      partialGaugedTotal a S X k (j + 1) := by
  classical
  set W := gaugeTransform γ (X j) with hW
  set X2 : F.FieldChain := Function.update X j W with hX2
  set k2 : F.SiteGauge := Function.update k j (fun y => γ y * k j y) with hk2
  have hlow := ih X2 k2
  have hX2j : X2 j = W := by simp [hX2]
  rw [hX2j] at hlow
  have hfit : ∑ c ∈ innerBonds S (j + 1), blockFit W (X (j + 1)) c =
      ∑ c ∈ innerBonds S (j + 1), gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c :=
    Finset.sum_congr rfl fun c _ => blockFit_gaugeTransform hG hL hj γ _ hγd _ _ c
  have hpart : partialGaugedTotal a S X2 k2 j = partialGaugedTotal a S X k j := by
    cases j with
    | zero =>
      simp only [partialGaugedTotal, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero, hX2j]
      exact wilsonAction_gaugeTransform hG hL S γ (X 0)
    | succ i =>
      have hlo : ∀ m, m ≤ i → X2 m = X m := fun m hm => Function.update_of_ne (by omega) _ _
      have hkl : ∀ m, m ≤ i → k2 m = k m := fun m hm => Function.update_of_ne (by omega) _ _
      simp only [partialGaugedTotal]
      rw [hlo 0 (Nat.zero_le _), Finset.sum_range_succ, Finset.sum_range_succ]
      have h1 : ∑ m ∈ Finset.range i, ∑ c ∈ innerBonds S (m + 1),
          gaugedBlockFit (X2 m) (k2 (m + 1)) (X2 (m + 1)) c =
          ∑ m ∈ Finset.range i, ∑ c ∈ innerBonds S (m + 1),
            gaugedBlockFit (X m) (k (m + 1)) (X (m + 1)) c := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mem_range] at hm
        rw [hlo m (by omega), hlo (m + 1) (by omega), hkl (m + 1) (by omega)]
      have h2 : ∑ c ∈ innerBonds S (i + 1), gaugedBlockFit (X2 i) (k2 (i + 1)) (X2 (i + 1)) c =
          ∑ c ∈ innerBonds S (i + 1), gaugedBlockFit (X i) (k (i + 1)) (X (i + 1)) c := by
        rw [hlo i le_rfl, hX2j]
        have : k2 (i + 1) = fun y => γ y * k (i + 1) y := by simp [hk2]
        rw [this]
        exact Finset.sum_congr rfl fun c _ => gaugedBlockFit_gaugeTransform γ _ _ _ c
      rw [h1, h2]
  calc minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W (X (j + 1)) c
      ≤ partialGaugedTotal a S X k j + a * ∑ c ∈ innerBonds S (j + 1),
          gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c := by
        rw [hfit, ← hpart]
        gcongr
    _ = _ := by
        simp only [partialGaugedTotal]
        rw [Finset.sum_range_succ]
        ring
theorem minimalAction_le_partial (hG : gaugeCovarianceStatement) (hV : minimalChainExistenceStatement)
    (a : ℝ) (ha : 0 ≤ a) (hL : 0 < F.blockSide) (S : Finset F.Cell) :
    ∀ j, j ≤ F.top → ∀ (X : F.FieldChain) (k : F.SiteGauge),
      minimalAction a S j (X j) ≤ partialGaugedTotal a S X k j := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.minimalAction_le_partialGaugedAction <;> assumption
theorem plaquetteHolonomy_congr (S : Finset F.Cell) {j : ℕ} (X X' : F.GaugeField j)
    (h : AgreeOnBonds S j X X') (p : F.Site j × Fin 4 × Fin 4) (hp : p ∈ innerPlaquettes S j) :
    plaquetteHolonomy X p = plaquetteHolonomy X' p := by
  obtain ⟨x, μ, ν⟩ := p
  have hc := (Finset.mem_filter.1 hp).2.2
  have c0 : x ∈ sitesOfCells S j := hc (by simp [plaquetteCorners])
  have c1 : x + unitStep j μ ∈ sitesOfCells S j := hc (by simp [plaquetteCorners])
  have c2 : x + unitStep j ν ∈ sitesOfCells S j := hc (by simp [plaquetteCorners])
  have c3 : x + unitStep j μ + unitStep j ν ∈ sitesOfCells S j := hc (by simp [plaquetteCorners])
  have mk : ∀ (y : F.Site j) (i : Fin 4), y ∈ sitesOfCells S j → y + unitStep j i ∈ sitesOfCells S j →
      (y, i) ∈ innerBonds S j := fun y i h1 h2 => mem_innerBonds.2 ⟨h1, h2⟩
  have e1 := h _ (mk x μ c0 c1)
  have e2 := h _ (mk (x + unitStep j μ) ν c1 c3)
  have e3 := h _ (mk (x + unitStep j ν) μ c2 (by rw [add_right_comm]; exact c3))
  have e4 := h _ (mk x ν c0 c2)
  simp only [] at e1 e2 e3 e4
  have s3 : x + unitStep j μ + unitStep j ν - unitStep j μ = x + unitStep j ν := by abel
  have s4 : x + unitStep j μ + unitStep j ν + - unitStep j μ - unitStep j ν = x := by abel
  simp only [plaquetteHolonomy, pathHolonomy, stepDisplacement, linkValue, if_true, Bool.false_eq_true,
    if_false]
  rw [s3, s4, e1, e2, e3, e4]
theorem minimalAction_congr (a : ℝ) (S : Finset F.Cell) :
    ∀ (j : ℕ) (A B : F.GaugeField j), AgreeOnBonds S j A B → minimalAction a S j A = minimalAction a S j B
  | 0, A, B, h => by
    simp only [minimalAction, wilsonAction]
    exact Finset.sum_congr rfl fun p hp => by rw [plaquetteHolonomy_congr S A B h p hp]
  | j + 1, A, B, h => by
    simp only [minimalAction]
    refine iInf_congr fun W => ?_
    have : ∑ c ∈ innerBonds S (j + 1), blockFit W A c = ∑ c ∈ innerBonds S (j + 1), blockFit W B c :=
      Finset.sum_congr rfl fun c hc => by
        unfold blockFit
        rw [h c hc]
    rw [this]
end Energy
section Main
theorem normSubOne_le_of_quartic {S : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F} {θ E : ℝ}
    (hE : 0 ≤ E) (hL : 0 < F.blockSide)
    (hq : ∀ (p : F.Site 0) (r : ℝ), 1 ≤ r → r ≤ (F.blockSide : ℝ) ^ (F.top - F.depth) →
      localQuarticSum S R U F.depth p r ≤ E ^ 4 * (r / (F.blockSide : ℝ) ^ (F.top - F.depth)) ^ (4 * θ))
    {b : F.Site F.depth × Fin 4} (hb : b ∈ innerBonds S F.depth) :
    normSubOne (chartField R U F.depth b.1 b.2 * (R F.depth b.1 b.2)⁻¹) ≤ E := by
  classical
  have hLr : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ (F.top - F.depth) := one_le_pow₀ (by exact_mod_cast hL)
  have hpos : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - F.depth) := by linarith
  have h1 := hq (baseSite b.1) _ hLr le_rfl
  rw [div_self hpos.ne', Real.one_rpow, mul_one] at h1
  have h2 : normSubOne (chartField R U F.depth b.1 b.2 * (R F.depth b.1 b.2)⁻¹) ^ 4 ≤
      localQuarticSum S R U F.depth (baseSite b.1) ((F.blockSide : ℝ) ^ (F.top - F.depth)) := by
    unfold localQuarticSum
    refine Finset.single_le_sum
      (f := fun b : F.Site F.depth × Fin 4 =>
        normSubOne (chartField R U F.depth b.1 b.2 * (R F.depth b.1 b.2)⁻¹) ^ 4)
      (fun _ _ => by positivity) (Finset.mem_filter.2 ⟨hb, ?_⟩)
    have : baseDistance b.1 (baseSite b.1) = 0 := by simp [baseDistance]
    rw [this]
    simp only [Nat.cast_zero]
    positivity
  have h3 : (0 : ℝ) ≤ normSubOne (chartField R U F.depth b.1 b.2 * (R F.depth b.1 b.2)⁻¹) := norm_nonneg _
  exact (pow_le_pow_iff_left₀ h3 hE (by norm_num)).1 (h2.trans h1)
theorem normSubOne_misfit_le {S : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F}
    {V : F.GaugeField F.top} {E : ℝ} (hE : 0 ≤ E)
    (hm : ∀ z : F.Cell, cellMisfitSum S R U V F.depth 2 z ≤
      (E * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - F.depth)) ^ 2)
    {c : F.Site (F.depth + 1) × Fin 4} (hc : c ∈ innerBonds S (F.depth + 1)) :
    normSubOne (chartBondMisfit R U V F.depth c) ≤ E := by
  classical
  have h1 := hm (enclosingCell c.1)
  have e : F.top - 1 - F.depth = 0 := by simp [BlockFrame.top]
  rw [e, pow_zero, mul_one] at h1
  have h2 : normSubOne (chartBondMisfit R U V F.depth c) ^ 2 ≤
      cellMisfitSum S R U V F.depth 2 (enclosingCell c.1) := by
    unfold cellMisfitSum
    refine Finset.single_le_sum
      (f := fun c : F.Site (F.depth + 1) × Fin 4 => normSubOne (chartBondMisfit R U V F.depth c) ^ 2)
      (fun _ _ => by positivity) ?_
    unfold bondsOver
    exact Finset.mem_filter.2 ⟨hc, by simp⟩
  have h3 : (0 : ℝ) ≤ normSubOne (chartBondMisfit R U V F.depth c) := norm_nonneg _
  exact (pow_le_pow_iff_left₀ h3 hE (by norm_num)).1 (h2.trans h1)
theorem baseSite_blockPoint_mem_patch {S : Finset F.Cell} {y : F.Cell}
    (hsign : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1)
    (hodd : Odd F.blockSide) (hy : y ∈ S) {h : Lattice4} (hh : h ∈ centredCube F.blockSide) :
    baseSite (blockPoint y h) ∈ (patchDomain S y).image (patchSite S y) := by
  classical
  have hLp : (0 : ℤ) < (F.blockSide : ℤ) := by exact_mod_cast hodd.pos
  set P : ℤ := (F.blockSide : ℤ) ^ F.depth with hP
  have hPpos : 1 ≤ P := one_le_pow₀ (by omega)
  obtain ⟨m, hm⟩ := id hodd
  have hmz : (F.blockSide : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hm
  have hcs : cellSideLength F = 2 * (P * m) + P := by
    have e : cellSideLength F = P * (F.blockSide : ℤ) := by
      simp only [cellSideLength, BlockFrame.top, pow_succ, hP]
    rw [e, hmz]
    ring
  have hcube := (mem_centredCube_iff F.blockSide h).1 hh
  have hM : ((F.blockSide : ℤ) - 1) / 2 = m := by omega
  have hb : ∀ i, |P * h i| ≤ P * m := by
    intro i
    have h1 := hcube i
    rw [hM] at h1
    rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < P)]
    exact mul_le_mul_of_nonneg_left (abs_le.2 h1) (by omega)
  set xl : Lattice4 := fun i => closedOrthant S y i * (P * h i) + (cellSideLength F - 1) / 2 with hxl
  have hxb : ∀ i, 0 ≤ xl i ∧ xl i ≤ cellSideLength F - 1 := by
    intro i
    have h1 := abs_le.1 (hb i)
    simp only [hxl]
    rw [hcs]
    generalize P * h i = w at h1
    generalize P * (m : ℤ) = q at h1
    rcases hsign i with e | e <;> rw [e] <;> constructor <;> omega
  refine Finset.mem_image.2 ⟨xl, ?_, ?_⟩
  · unfold patchDomain
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ?_,
      ⟨0, ?_, fun i => (hxb i).1⟩⟩
    · have := hxb i
      constructor <;> omega
    · unfold patchCorners
      refine Finset.mem_image.2 ⟨y, ?_, ?_⟩
      · unfold cellBall
        exact Finset.mem_filter.2 ⟨hy, by simp [cellSupDist]⟩
      · funext i
        simp [cellDisplacement]
  · have e1 : baseSite (blockPoint y h) = cellCentre 0 y + siteOfCoords 0 (fun i => P * h i) := by
      simp only [blockPoint]
      rw [baseSite_add F.depth (by simp [BlockFrame.top]), baseSite_cellCentre F.depth (by simp [BlockFrame.top])]
    rw [e1]
    unfold patchSite
    congr 2
    funext i
    simp only [hxl, add_sub_cancel_right]
    rcases hsign i with e | e <;> rw [e] <;> ring
theorem chartChain_top (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) :
    chartChain R U V (F.depth + 1) = V := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.chartChain_top <;> assumption
theorem chartChain_depth (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) :
    chartChain R U V F.depth = chartField R U F.depth := by
  unfold chartChain
  exact Function.update_of_ne (by simp [BlockFrame.top]) _ _
theorem levelScale_top : levelScale F (F.depth + 1) = 1 := by apply _root_.YangMills.Construction.ReferenceBounds.levelScale_top_eq_one <;> assumption
theorem levelScale_depth_le_one (hL : 0 < F.blockSide) : levelScale F F.depth ≤ 1 := by
  unfold levelScale
  have : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  exact pow_le_one₀ (by positivity) (by rw [div_le_one (by linarith)]; exact this)
end Main
theorem criticalChainChartOverTop (hB : referenceBoundsStatement) (hG : gaugeCovarianceStatement)
    (hV : minimalChainExistenceStatement) : criticalChainChartOverTopStatement := by
  classical
  intro a θ del Ca ha _ _ _ _ _
  obtain ⟨C, c0, L1, hC, hc0, hbd⟩ := hB
  refine ⟨max L1 1, fun L hL hge C₁ hC₁ => ?_⟩
  have hL1 : L1 ≤ L := le_of_max_le_left hge
  have hLpos : 0 < L := hL.pos
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
  set Nc : ℝ := 5 * L * (C₁ + C) with hNcdef
  set Nx : ℝ := 25 * L * C₁ + C + C₁ with hNxdef
  have hNc0 : 0 < Nc := by positivity
  have hNx0 : 0 < Nx := by positivity
  refine ⟨min c0 (min 1 (min (1 / (2 * C)) (1 / (20 * L * C₁)))), 2 * (Nx + L * Nc),
    lt_min hc0 (lt_min one_pos (lt_min (by positivity) (by positivity))), by positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V V' hs hsσ hcold U hU
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hs1 : s ≤ c0 := hsσ.trans (min_le_left _ _)
  have hs2 : s ≤ 1 := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs3 : s ≤ 1 / (2 * C) :=
    hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs4 : s ≤ 1 / (20 * L * C₁) :=
    hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hCs : 2 * C * s ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hs3
    linarith
  have hLCs : 20 * L * C₁ * s ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hs4
    linarith
  obtain ⟨b1, -, -, -, b5, b6⟩ := hbd F m S hodd (hFL ▸ hL1) hamb hm hreg s V hs hs1 hcold
  set R := referenceFieldChain S V with hRdef
  set Xf := chartField R U F.depth with hXf
  set kk : F.Cell → UnitQuaternion := chartGauge R U F.top with hkk
  set ε : ℝ := C₁ * s with hεdef
  have hε : 0 ≤ ε := by positivity
  have hLF : (F.blockSide : ℝ) = L := by rw [hFL]
  have hXR : ∀ b ∈ innerBonds S F.depth, ‖(Xf b.1 b.2 : ℍ[ℝ]) - (R F.depth b.1 b.2 : ℍ[ℝ])‖ ≤ ε := by
    intro b hb
    have := normSubOne_le_of_quartic (U := U) hε hodd.pos
      (fun p r h1 h2 => hU.quartic F.depth p r (by simp [BlockFrame.top]) h1 h2) hb
    rw [← coe_mul_inv_sub_one]
    exact this
  have hNc : ∀ y ∈ S, ∀ (h : Lattice4) (i : Fin 4), h ∈ centredCube F.blockSide →
      h + basisVector i ∈ centredCube F.blockSide →
      ‖((pathHolonomy Xf (cellCentre F.depth y) (blockLoop h i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Nc * s := by
    intro y hy h i hh hh'
    have hsign := (closedOrthant_spec hreg (by omega) y).1
    have := blockLoop_norm_sub_one_le (R := R F.depth) (X := Xf)
      (g := fun x => (frameChange S V y (baseSite x))⁻¹)
      (ε := ε) (e := C * s) hε (by positivity) hodd.pos (y := y)
      (P := fun x => x ∈ sitesOfCells S F.depth ∧ baseSite x ∈ (patchDomain S y).image (patchSite S y))
      (fun u hu => ⟨blockPoint_mem hy hu, baseSite_blockPoint_mem_patch hsign hodd hy hu⟩)
      (fun x l h1 h2 => hXR (x, l) (mem_innerBonds.2 ⟨h1.1, h2.1⟩))
      (fun x l h1 h2 => by
        have h3 := b1 F.depth (by simp [BlockFrame.top]) y hy (x, l) (mem_innerBonds.2 ⟨h1.1, h2.1⟩) h1.2 h2.2
        have h4 := levelScale_depth_le_one (F := F) hodd.pos
        have h5 : C * s * levelScale F F.depth ≤ C * s :=
          mul_le_of_le_one_right (by positivity) h4
        exact h3.trans h5) hh hh'
    rw [hLF] at this
    refine this.trans (le_of_eq ?_)
    simp only [hNcdef, hεdef]
    ring
  have hNx : ∀ y ∈ S, ∀ (h : Lattice4) (i : Fin 4), h ∈ centredCube F.blockSide →
      y + siteOfCoords F.top (basisVector i) ∈ S →
      ‖((kk y * pathHolonomy Xf (cellCentre F.depth y) (bondContour F.blockSide h 1 i) *
          (kk (y + siteOfCoords F.top (basisVector i)))⁻¹ * (V' y i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        Nx * s := by
    intro y hy h i hh hE
    set E := y + siteOfCoords F.top (basisVector i) with hEdef
    have hcb : ((y, i) : F.Site (F.depth + 1) × Fin 4) ∈ innerBonds S (F.depth + 1) :=
      mem_innerBonds.2 ⟨mem_sitesOfCells_top.2 hy, mem_sitesOfCells_top.2 hE⟩
    set cmX := contourAverage Xf ((y, i) : F.Site (F.depth + 1) × Fin 4) with hcmX
    set cmR := contourAverage (R F.depth) ((y, i) : F.Site (F.depth + 1) × Fin 4) with hcmR
    set B : ℝ := 5 * F.blockSide * ε with hBdef
    have hB0 : 0 ≤ B := by positivity
    have hB4 : B ≤ 1 / 4 := by
      simp only [hBdef, hεdef, hLF]
      nlinarith
    have hclose : ‖cmX - cmR‖ ≤ B := by
      refine contourAverage_dist_le hodd (fun u hu π => ?_) hB0
      have := bondContour_dist_le hε hodd hXR hy hE hu π
      rw [← refineSite_eq_cellCentre] at this
      exact this
    have h5 := b5 F.depth (by simp [BlockFrame.top]) (y, i) hcb h hh 1
    have h6 := (b6 F.depth (by simp [BlockFrame.top]) (y, i) hcb).2
    rw [levelScale_top, one_pow, mul_one] at h5 h6
    have hnR : 1 / 2 ≤ ‖cmR‖ := by
      have : C * s ^ 2 ≤ 1 / 2 := by nlinarith
      linarith
    have hR0 : cmR ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hnR
      linarith
    have hX0 : cmX ≠ 0 := by
      intro h0
      rw [h0, zero_sub, norm_neg] at hclose
      linarith
    have hu := polarUnit_dist_le hX0 hR0
    have hu2 : ‖((polarUnit cmX : UnitQuaternion) : ℍ[ℝ]) - ((polarUnit cmR : UnitQuaternion) : ℍ[ℝ])‖ ≤
        4 * B := by
      refine hu.trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (cmX - cmR)]
    have hcc := bondContour_dist_le hε hodd hXR hy hE hh 1
    have h5' : ‖((pathHolonomy (R F.depth) (cellCentre F.depth y) (bondContour F.blockSide h 1 i) :
        UnitQuaternion) : ℍ[ℝ]) - ((polarUnit cmR : UnitQuaternion) : ℍ[ℝ])‖ ≤ C * s := by
      rw [← coe_mul_inv_sub_one, ← refineSite_eq_cellCentre]
      exact h5
    have hhu : ‖((pathHolonomy Xf (cellCentre F.depth y) (bondContour F.blockSide h 1 i) *
        (polarUnit cmX)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 5 * B + C * s := by
      rw [coe_mul_inv_sub_one]
      have t1 := norm_sub_le_norm_sub_add_norm_sub
        ((pathHolonomy Xf (cellCentre F.depth y) (bondContour F.blockSide h 1 i) : UnitQuaternion) : ℍ[ℝ])
        ((pathHolonomy (R F.depth) (cellCentre F.depth y) (bondContour F.blockSide h 1 i) :
          UnitQuaternion) : ℍ[ℝ])
        ((polarUnit cmX : UnitQuaternion) : ℍ[ℝ])
      have t2 := norm_sub_le_norm_sub_add_norm_sub
        ((pathHolonomy (R F.depth) (cellCentre F.depth y) (bondContour F.blockSide h 1 i) :
          UnitQuaternion) : ℍ[ℝ])
        ((polarUnit cmR : UnitQuaternion) : ℍ[ℝ]) ((polarUnit cmX : UnitQuaternion) : ℍ[ℝ])
      have t3 : ‖((polarUnit cmR : UnitQuaternion) : ℍ[ℝ]) - ((polarUnit cmX : UnitQuaternion) : ℍ[ℝ])‖ ≤
          4 * B := by
        rw [norm_sub_rev]
        exact hu2
      linarith
    have hmis := normSubOne_misfit_le (U := U) (V := V') hε
      (fun z => (hU.misfits_on_cells F.depth z (by simp [BlockFrame.top])).2) hcb
    have hfm : polarUnit (gaugedContourAverage (chartChain R U V' F.depth) (chartGauge R U (F.depth + 1))
        ((y, i) : F.Site (F.depth + 1) × Fin 4)) = kk y * polarUnit cmX * (kk E)⁻¹ := by
      rw [chartChain_depth, ← polarUnit_conj hX0]
      rfl
    have hM : normSubOne (chartBondMisfit R U V' F.depth ((y, i) : F.Site (F.depth + 1) × Fin 4)) =
        ‖((V' y i * (kk y * polarUnit cmX * (kk E)⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
      unfold chartBondMisfit
      rw [hfm, chartChain_top]
      rfl
    rw [hM] at hmis
    have hprod : kk y * pathHolonomy Xf (cellCentre F.depth y) (bondContour F.blockSide h 1 i) *
        (kk E)⁻¹ * (V' y i)⁻¹ =
        (kk y * (pathHolonomy Xf (cellCentre F.depth y) (bondContour F.blockSide h 1 i) *
          (polarUnit cmX)⁻¹) * (kk y)⁻¹) *
          (V' y i * (kk y * polarUnit cmX * (kk E)⁻¹)⁻¹)⁻¹ := by
      group
    rw [hprod]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    rw [norm_coe_conj_sub_one, norm_coe_inv_sub_one]
    have e5 : 5 * B + C * s + ε = Nx * s := by
      simp only [hBdef, hεdef, hNxdef, hLF]
      ring
    linarith
  obtain ⟨w, h0, hb, hsame⟩ := exists_chart (V := V') (X := Xf) (k := kk) hamb hodd
    (by positivity : 0 ≤ Nc * s) (by positivity : 0 ≤ Nx * s) hNc hNx
  set γ := treeGauge kk Xf with hγ
  have hcent : ∀ y : F.Cell, γ (cellCentre F.depth y) = kk y :=
    fun y => treeGauge_cellCentre hamb hodd kk Xf y
  refine ⟨w, fun b hb' => h0 b hb', fun b hb' => ?_, fun b hb' => ?_, ?_⟩
  · refine (hb b hb').trans (le_of_eq ?_)
    rw [hLF]
    ring
  · have hbs : b ∈ innerBonds S F.depth := (Finset.mem_filter.1 hb').1
    have h1 := hsame b hbs
    have hnt : ¬ IsAxialTreeBond b := (Finset.mem_filter.1 hb').2
    obtain ⟨x, i⟩ := b
    simp only [chartedField, gaugeTransform, gaugedBondElement, treeHolonomy] at h1 ⊢
    have hg : ∀ u : F.Site F.depth, treeGauge kk Xf u =
        kk (enclosingCell u) * pathHolonomy Xf (cellCentre F.depth (enclosingCell u))
          (axisPath (cellOffset u) 1) := fun _ => rfl
    rw [hγ, hg, hg] at h1
    by_cases hcr : IsCrossingBond (x, i)
    · rw [if_pos hcr] at h1 ⊢
      rw [eq_mul_inv_iff_mul_eq.2 h1]
      group
    · rw [if_neg hcr, if_neg hnt] at h1
      rw [if_neg hcr, h1]
      group
  · have hzero : ∀ b ∈ innerBonds S F.depth, ‖((chartedField w V' b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) -
        ((gaugeTransform γ Xf b.1 b.2 : UnitQuaternion) : ℍ[ℝ])‖ ≤ 0 := by
      intro b hb'
      rw [hsame b hb', sub_self, norm_zero]
    have hfit : ∑ c ∈ innerBonds S (F.depth + 1), blockFit (chartedField w V') V' c =
        ∑ c ∈ innerBonds S (F.depth + 1), blockFit (gaugeTransform γ Xf) V' c := by
      refine Finset.sum_congr rfl fun c hc => ?_
      obtain ⟨y, i⟩ := c
      obtain ⟨hc1, hc2⟩ := mem_innerBonds.1 hc
      have hy : y ∈ S := mem_sitesOfCells_top.1 hc1
      have hE : y + siteOfCoords F.top (basisVector i) ∈ S := mem_sitesOfCells_top.1 hc2
      have hm0 : contourAverage (chartedField w V') ((y, i) : F.Site (F.depth + 1) × Fin 4) =
          contourAverage (gaugeTransform γ Xf) ((y, i) : F.Site (F.depth + 1) × Fin 4) := by
        have := contourAverage_dist_le (X := chartedField w V') (Y := gaugeTransform γ Xf)
          (c := ((y, i) : F.Site (F.depth + 1) × Fin 4)) (B := 0) hodd (fun u hu π => by
            have h1 := bondContour_dist_le le_rfl hodd hzero hy hE hu π
            rw [mul_zero, ← refineSite_eq_cellCentre] at h1
            exact h1) le_rfl
        exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
      unfold blockFit
      rw [hm0]
    have hstep := minimalAction_step_le hG a hodd.pos S (j := F.depth) (by simp [BlockFrame.top])
      (fun X k => minimalAction_le_partial hG hV a ha.le hodd.pos S F.depth (by simp [BlockFrame.top]) X k)
      ha.le (chartChain R U V') (chartGauge R U) γ (fun y => by
        rw [refineSite_eq_cellCentre]
        exact hcent y)
    rw [chartChain_depth, chartChain_top] at hstep
    unfold blockEnergy
    rw [minimalAction_congr a S F.depth _ _ hsame, hfit]
    exact hstep
end ChartOverTop
end BlockAverages
end YangMills.Construction
end

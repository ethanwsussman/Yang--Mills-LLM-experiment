import YangMills.Construction.ColdChainAtEveryLevel.FramedChainsOverATop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
theorem smul_inv_norm_mem_unitary (q : ℍ[ℝ]) (hq : q ≠ 0) : (‖q‖⁻¹ • q) ∈ unitary ℍ[ℝ] := by
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have hs : Quaternion.normSq (‖q‖⁻¹ • q) = 1 := by
    rw [Quaternion.normSq_smul, Quaternion.normSq_eq_norm_mul_self]
    field_simp
  rw [Unitary.mem_iff, Quaternion.star_mul_self, Quaternion.self_mul_star, hs]
  simp
open Classical in
def polarUnit (q : ℍ[ℝ]) : UnitQuaternion :=
  if hq : q = 0 then 1 else ⟨‖q‖⁻¹ • q, smul_inv_norm_mem_unitary q hq⟩
def baseSite {j : ℕ} (y : F.Site j) : F.Site 0 :=
  siteOfCoords 0 fun i => (F.blockSide : ℤ) ^ j * siteCoords y i
def cutoffProfile (t : ℝ) : ℝ := Real.smoothTransition ((0.9 - |t|) / 0.3)
def cellCutoff (x : F.Site 0) (z : F.Cell) : ℝ :=
  ∏ i, cutoffProfile ((((x - cellCentre 0 z) i).valMinAbs : ℝ) / (F.blockSide : ℝ) ^ F.top)
def cellPartition (S : Finset F.Cell) (x : F.Site 0) (z : F.Cell) : ℝ :=
  cellCutoff x z ^ 2 / ∑ y ∈ S, cellCutoff x y ^ 2
def signVectors : List (Fin 4 → ℤ) :=
  [![1, 1, 1, 1], ![1, 1, 1, -1], ![1, 1, -1, 1], ![1, 1, -1, -1], ![1, -1, 1, 1], ![1, -1, 1, -1],
    ![1, -1, -1, 1], ![1, -1, -1, -1], ![-1, 1, 1, 1], ![-1, 1, 1, -1], ![-1, 1, -1, 1],
    ![-1, 1, -1, -1], ![-1, -1, 1, 1], ![-1, -1, 1, -1], ![-1, -1, -1, 1], ![-1, -1, -1, -1]]
def IsOrthantClosedNear (S : Finset F.Cell) (z : F.Cell) (e : Fin 4 → ℤ) : Prop :=
  ∀ q ∈ S, cellSupDist q z ≤ 32 → ∀ h : Fin 4 → ℤ, (∀ i, 0 ≤ e i * h i) → (∀ i, |h i| ≤ 32) →
    q + siteOfCoords F.top h ∈ S
open Classical in
def closedOrthant (S : Finset F.Cell) (z : F.Cell) : Fin 4 → ℤ :=
  (signVectors.find? fun e => decide (IsOrthantClosedNear S z e)).getD fun _ => 1
def cellDisplacement (y y' : F.Cell) : Fin 4 → ℤ := fun i => ((y' - y) i).valMinAbs
def orthantPart (e o : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => if 0 ≤ e i * o i then o i else 0
def cellParallelTransport (S : Finset F.Cell) (V : F.GaugeField F.top) (y y' : F.Cell) : UnitQuaternion :=
  pathHolonomy V y (axisPath (orthantPart (closedOrthant S y) (cellDisplacement y y')) 1 ++
    axisPath (cellDisplacement y y' - orthantPart (closedOrthant S y) (cellDisplacement y y')) 1)
def localizationOperator (S : Finset F.Cell) (V : F.GaugeField F.top) (x : F.Site 0)
    (v : F.Cell → ℍ[ℝ]) : F.Cell → ℍ[ℝ] :=
  fun y => ∑ y' ∈ S, ∑ y'' ∈ S,
    (cellPartition S x y' * Real.sqrt (cellPartition S x y) * Real.sqrt (cellPartition S x y'')) •
      (((cellParallelTransport S V y y' : UnitQuaternion) : ℍ[ℝ]) *
        (((cellParallelTransport S V y'' y')⁻¹ : UnitQuaternion) : ℍ[ℝ]) * v y'')
def IsLeadingEigenvector (S : Finset F.Cell) (V : F.GaugeField F.top) (x : F.Site 0)
    (f : F.Cell → ℍ[ℝ]) : Prop :=
  ∑ y ∈ S, ‖f y‖ ^ 2 = 1 ∧ ∃ l : ℝ, 1 / 2 ≤ l ∧ ∀ y ∈ S, localizationOperator S V x f y = l • f y
open Classical in
def leadingFrame (S : Finset F.Cell) (V : F.GaugeField F.top) (x : F.Site 0) : F.Cell → ℍ[ℝ] :=
  if hc : ∃ y ∈ S, x = cellCentre 0 y then fun y => if y = hc.choose then 1 else 0
  else if h : ∃ f, IsLeadingEigenvector S V x f then
    fun y => h.choose y * (((polarUnit (h.choose (enclosingCell x)))⁻¹ : UnitQuaternion) : ℍ[ℝ])
  else 0
def quaternionPairing (S : Finset F.Cell) (f g : F.Cell → ℍ[ℝ]) : ℍ[ℝ] := ∑ y ∈ S, star (f y) * g y
def referenceGaugeField (S : Finset F.Cell) (V : F.GaugeField F.top) (j : ℕ) : F.GaugeField j :=
  fun y i => polarUnit (quaternionPairing S (leadingFrame S V (baseSite y))
    (leadingFrame S V (baseSite (y + unitStep j i))))
def referenceFieldChain (S : Finset F.Cell) (V : F.GaugeField F.top) : F.FieldChain := by
  classical exact Function.update (fun j => referenceGaugeField S V j) F.top V
def referenceDefect (R : F.FieldChain) (j : ℕ) (c : F.Site (j + 1) × Fin 4) : UnitQuaternion :=
  R (j + 1) c.1 c.2 * (polarUnit (contourAverage (R j) c))⁻¹
def relativePathAverage {j : ℕ} (X R : F.GaugeField j) (y : F.Site (j + 1)) : ℍ[ℝ] :=
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    ((pathHolonomy X (refineSite y) (axisPath h π) *
      (pathHolonomy R (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ])
def balancingGauge {j : ℕ} (X R : F.GaugeField j) (y : F.Site (j + 1)) : UnitQuaternion :=
  (polarUnit (relativePathAverage X R y))⁻¹
structure ChainChart (F : BlockFrame) where
  fine : F.Site 0 → Fin 4 → imaginaryQuaternions
  coarse : (j : ℕ) → F.Site (j + 1) → Fin 4 → imaginaryQuaternions
def chartField (R : F.FieldChain) (U : ChainChart F) : (j : ℕ) → F.GaugeField j
  | 0 => fun x i => expUnit (U.fine x i) * R 0 x i
  | j + 1 => fun y i => expUnit (U.coarse j y i) * referenceDefect R j (y, i) *
      polarUnit (gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) (y, i))
def chartChain (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) : F.FieldChain := by
  classical exact Function.update (chartField R U) F.top V
def chartGauge (R : F.FieldChain) (U : ChainChart F) : F.SiteGauge
  | 0 => fun _ => 1
  | j + 1 => balancingGauge (chartField R U j) (R j)
def chartAction (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (V : F.GaugeField F.top) : ℝ :=
  gaugedChainAction a S (chartChain R U V) (chartGauge R U)
end BlockAverages
end YangMills.Construction
end

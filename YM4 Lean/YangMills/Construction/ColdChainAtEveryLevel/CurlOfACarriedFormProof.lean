import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.ColdnessOfTheFieldBelowTheTopProof
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMotionsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.NormsOnNearCells
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace CarriedCurl
open BlockAverages
open BlockLines (lineBond lineBond_fst lineBond_mem_innerBonds refineSite_add_unitStep refineSite_add_injective
  enclosingCell_mem card_innerBonds_le innerBonds_mono norm_parallelAverage_le norm_adjointAction_sub_le)
open LatticePaths (AllAlong allAlong_head endpoint endpoint_append endpoint_replicate axisPath_spec length_axisPath
  card_centredCube)
open BlockWeights (shiftedWeight one_le_shiftedWeight shiftedWeight_succ_le cellsNearPoint card_cellsNearPoint_le)
open PlaquetteExpansion (covariantCurlAt baseDistance_add_unitStep_le)
open LatticeFractionalIntegration (Lattice4 basisVector)
variable {F : BlockFrame}
def frameForm (γ : F.Site 0 → UnitQuaternion) {j : ℕ} (f : F.Site j → Fin 4 → ℍ[ℝ]) : F.Site j → Fin 4 → ℍ[ℝ] :=
  fun x i => adjointAction (γ (baseSite x)) (f x i)
def frameField (γ : F.Site 0 → UnitQuaternion) {j : ℕ} (X : F.GaugeField j) : F.GaugeField j :=
  gaugeTransform (fun x => γ (baseSite x)) X
theorem endpoint_axisPath_append_replicate (h : Lattice4) (π : Equiv.Perm (Fin 4)) (i : Fin 4) (r : ℕ) :
    endpoint 0 (axisPath h π ++ List.replicate r (i, true)) = h + (r : ℤ) • basisVector i := by
  rw [endpoint_append, (axisPath_spec h π).2, endpoint_replicate]
  simp [FlatPairing.stepDisplacement]
theorem adjointAction_conj_pair (a b g : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction (a * g * b⁻¹) (adjointAction b w) = adjointAction a (adjointAction g w) := by
  rw [adjointAction_mul, adjointAction_mul, ← adjointAction_mul b⁻¹ b, inv_mul_cancel, adjointAction_one]
theorem parallelAverage_frameField (γ : F.Site 0 → UnitQuaternion) {j : ℕ} (hj : j < F.top) (X : F.GaugeField j)
    (f : F.Site j → Fin 4 → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) :
    parallelAverage (frameField γ X) (frameForm γ f) c =
      adjointAction (γ (baseSite c.1)) (parallelAverage X f c) := by
  unfold parallelAverage
  rw [adjointAction_smul]
  congr 1
  rw [adjointAction_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [adjointAction_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [adjointAction_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have e1 := GaugeMotions.pathHolonomy_gaugeTransform_of_base (fun x => γ (baseSite x)) X (refineSite c.1)
    (axisPath h π ++ List.replicate r (c.2, true))
  rw [endpoint_axisPath_append_replicate] at e1
  have e2 : refineSite c.1 + siteOfCoords j (h + (r : ℤ) • basisVector c.2) =
      refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2 :=
    (lineBond_fst c h r).symm
  rw [e2] at e1
  unfold frameField frameForm
  rw [e1, baseSite_refineSite j (by omega), adjointAction_conj_pair]
theorem covariantCurlAt_frameField (γ : F.Site 0 → UnitQuaternion) {j : ℕ} (X : F.GaugeField j)
    (f : F.Site j → Fin 4 → ℍ[ℝ]) (q : F.Site j × Fin 4 × Fin 4) :
    covariantCurlAt (frameField γ X) (frameForm γ f) q =
      adjointAction (γ (baseSite q.1)) (covariantCurlAt X f q) := by
  obtain ⟨x, μ, ν⟩ := q
  simp only [covariantCurlAt, frameField, frameForm, gaugeTransform]
  have e : x + unitStep j ν + unitStep j μ = x + unitStep j μ + unitStep j ν := add_right_comm _ _ _
  rw [e, BlockLines.adjointAction_sub, BlockLines.adjointAction_sub, adjointAction_add]
  set a := γ (baseSite x)
  set b := γ (baseSite (x + unitStep j μ))
  set c := γ (baseSite (x + unitStep j ν))
  set d := γ (baseSite (x + unitStep j μ + unitStep j ν))
  set r1 := X x μ
  set r2 := X (x + unitStep j μ) ν
  set r3 := X (x + unitStep j ν) μ
  set r4 := X x ν
  have t3 : a * r1 * b⁻¹ * (b * r2 * d⁻¹) * (c * r3 * d⁻¹)⁻¹ = a * (r1 * r2 * r3⁻¹) * c⁻¹ := by group
  have t4 : a * r1 * b⁻¹ * (b * r2 * d⁻¹) * (c * r3 * d⁻¹)⁻¹ * (a * r4 * c⁻¹)⁻¹ =
      a * (r1 * r2 * r3⁻¹ * r4⁻¹) * a⁻¹ := by group
  rw [t4, t3, adjointAction_conj_pair, adjointAction_conj_pair, adjointAction_conj_pair]
theorem norm_pathHolonomy_sub_one_le {j : ℕ} {Dset : Set (F.Site j)} {Y : F.GaugeField j} {ε : ℝ}
    (hY : ∀ x i, x ∈ Dset → x + unitStep j i ∈ Dset → ‖((Y x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (x0 : F.Site j) :
    ∀ (l : List PathStep) (v : Lattice4), AllAlong (fun v => x0 + siteOfCoords j v ∈ Dset) v l →
      ‖((pathHolonomy Y (x0 + siteOfCoords j v) l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * ε := by
  intro l
  induction l with
  | nil =>
    intro v _
    simp [pathHolonomy]
  | cons st r ih =>
    intro v hp
    have hnext : x0 + siteOfCoords j v + stepDisplacement j st =
        x0 + siteOfCoords j (v + FlatPairing.stepDisplacement st) := by
      rw [ChartCoordinates.stepDisplacement_eq_siteOfCoords, add_assoc, ← siteOfCoords_add]
    have hv : x0 + siteOfCoords j v ∈ Dset := hp.1
    have hw : x0 + siteOfCoords j v + stepDisplacement j st ∈ Dset := by
      rw [hnext]; exact allAlong_head hp.2
    simp only [pathHolonomy]
    rw [hnext]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    have h2 := ih _ hp.2
    have h1 : ‖((linkValue Y (x0 + siteOfCoords j v) st : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε := by
      rcases st with ⟨i, b⟩
      cases b
      · simp only [linkValue, Bool.false_eq_true, if_false]
        have e : x0 + siteOfCoords j v + stepDisplacement j (i, false) = x0 + siteOfCoords j v - unitStep j i := by
          simp [stepDisplacement, sub_eq_add_neg]
        rw [e] at hw
        rw [norm_coe_inv_sub_one]
        exact hY _ i hw (by rw [sub_add_cancel]; exact hv)
      · simp only [linkValue, if_true]
        have e : x0 + siteOfCoords j v + stepDisplacement j (i, true) = x0 + siteOfCoords j v + unitStep j i := by
          simp [stepDisplacement]
        rw [e] at hw
        exact hY _ i hv hw
    simp only [List.length_cons]
    push_cast
    linarith
theorem allAlong_of_append_left {p : Lattice4 → Prop} {u : Lattice4} {l l' : List PathStep}
    (h : AllAlong p u (l ++ l')) : AllAlong p u l := by
  induction l generalizing u with
  | nil => exact allAlong_head h
  | cons st r ih => exact ⟨h.1, ih h.2⟩
theorem allAlong_transportPath {D : Finset F.Cell} (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds D (j + 1)) {h : Lattice4} (hh : h ∈ centredCube F.blockSide)
    (π : Equiv.Perm (Fin 4)) {r : ℕ} (hr : r < F.blockSide) :
    AllAlong (fun v => refineSite c.1 + siteOfCoords j v ∈ (sitesOfCells D j : Set (F.Site j))) 0
      (axisPath h π ++ List.replicate r (c.2, true)) := by
  have h1 := ChartCoordinates.allAlong_bondContour hodd (by omega) hc hh π
  unfold bondContour at h1
  have h2 := allAlong_of_append_left h1
  have e : F.blockSide = r + (F.blockSide - r) := by omega
  rw [e, List.replicate_add, ← List.append_assoc] at h2
  exact allAlong_of_append_left h2
theorem length_transportPath_le (hL : 1 ≤ F.blockSide) {h : Lattice4} (hh : h ∈ centredCube F.blockSide)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) {r : ℕ} (hr : r < F.blockSide) :
    ((axisPath h π ++ List.replicate r (i, true)).length : ℝ) ≤ 3 * F.blockSide := by
  have h1 := length_axisPath h π
  have hc := (LatticePaths.mem_centredCube_iff _ _).1 hh
  have hb : ∀ k, 2 * (h k).natAbs ≤ F.blockSide := fun k => by
    have := hc k
    omega
  have a0 := hb (π 0)
  have a1 := hb (π 1)
  have a2 := hb (π 2)
  have a3 := hb (π 3)
  have h2 : (axisPath h π ++ List.replicate r (i, true)).length ≤ 3 * F.blockSide := by
    rw [List.length_append, List.length_replicate, h1]
    omega
  exact_mod_cast h2
def flatAverage {j : ℕ} (g : F.Site j → Fin 4 → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) : ℍ[ℝ] :=
  (1 / (F.blockSide : ℝ) ^ 4) • ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
    g (lineBond c h r).1 (lineBond c h r).2
theorem flatAverage_eq_perm_sum (hL : 0 < F.blockSide) {j : ℕ} (g : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    flatAverage g c = (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide,
      ∑ _π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide, g (lineBond c h r).1 (lineBond c h r).2 := by
  have e : ∀ h, ∑ _π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide, g (lineBond c h r).1 (lineBond c h r).2 =
      (24 : ℝ) • ∑ r ∈ Finset.range F.blockSide, g (lineBond c h r).1 (lineBond c h r).2 := by
    intro h
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    simp [Nat.factorial, ← Nat.cast_smul_eq_nsmul ℝ]
  simp only [e]
  rw [← Finset.smul_sum, smul_smul]
  unfold flatAverage
  congr 1
  field_simp
theorem norm_parallelAverage_sub_flatAverage_le (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top)
    {D : Finset F.Cell} {Y : F.GaugeField j} {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ x i, x ∈ sitesOfCells D j → x + unitStep j i ∈ sitesOfCells D j →
      ‖((Y x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (g : F.Site j → Fin 4 → ℍ[ℝ]) {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds D (j + 1)) :
    ‖parallelAverage Y g c - flatAverage g c‖ ≤
      6 * F.blockSide * ε * lineBlockAverage (fun x i => ‖g x i‖) c := by
  have hL := hodd.pos
  rw [flatAverage_eq_perm_sum hL, lineBlockAverage_eq]
  unfold parallelAverage
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
  simp only [← Finset.sum_sub_distrib]
  have hterm : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4), ∀ r ∈ Finset.range F.blockSide,
      ‖adjointAction (pathHolonomy Y (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
          (g (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2) -
          g (lineBond c h r).1 (lineBond c h r).2‖ ≤
        6 * F.blockSide * ε * ‖g (lineBond c h r).1 (lineBond c h r).2‖ := by
    intro h hh π r hr
    have hr' := Finset.mem_range.1 hr
    have h1 := norm_pathHolonomy_sub_one_le (Dset := (sitesOfCells D j : Set (F.Site j))) (Y := Y) hY
      (refineSite c.1) _ 0 (allAlong_transportPath hodd hj hc hh π hr')
    rw [ChartCoordinates.add_siteOfCoords_zero] at h1
    have h2 := length_transportPath_le hL hh π c.2 hr'
    have h3 : ‖((pathHolonomy Y (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)) :
        UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 3 * F.blockSide * ε :=
      h1.trans (mul_le_mul_of_nonneg_right h2 hε)
    have h4 := norm_adjointAction_sub_le
      (pathHolonomy Y (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
      (g (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)
    refine h4.trans ?_
    have h5 := mul_le_mul_of_nonneg_right h3
      (norm_nonneg (g (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2))
    show _ ≤ 6 * F.blockSide * ε * ‖g (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2‖
    linarith
  have hsum : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide,
      (adjointAction (pathHolonomy Y (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
          (g (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2) -
          g (lineBond c h r).1 (lineBond c h r).2)‖ ≤
      24 * (6 * F.blockSide * ε * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        ‖g (lineBond c h r).1 (lineBond c h r).2‖) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun h hh => ?_
    refine (norm_sum_le _ _).trans ?_
    have h2 : ∀ π : Equiv.Perm (Fin 4), ‖∑ r ∈ Finset.range F.blockSide,
        (adjointAction (pathHolonomy Y (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
          (g (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2) -
          g (lineBond c h r).1 (lineBond c h r).2)‖ ≤
        6 * F.blockSide * ε * ∑ r ∈ Finset.range F.blockSide, ‖g (lineBond c h r).1 (lineBond c h r).2‖ := by
      intro π
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun r hr => hterm h hh π r hr
    refine (Finset.sum_le_sum fun π _ => h2 π).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    simp [Nat.factorial]
  calc _ ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) *
        (24 * (6 * F.blockSide * ε * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
          ‖g (lineBond c h r).1 (lineBond c h r).2‖)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
        field_simp
def flatTransported (g0 : F.Site 0 → Fin 4 → ℍ[ℝ]) : (j : ℕ) → F.Site j → Fin 4 → ℍ[ℝ]
  | 0 => g0
  | j + 1 => fun y i => flatAverage (flatTransported g0 j) (y, i)
def averagedNorm (g0 : F.Site 0 → Fin 4 → ℝ) : (j : ℕ) → F.Site j → Fin 4 → ℝ
  | 0 => g0
  | j + 1 => fun y i => lineBlockAverage (averagedNorm g0 j) (y, i)
theorem averagedNorm_nonneg {g0 : F.Site 0 → Fin 4 → ℝ} (h : ∀ x i, 0 ≤ g0 x i) :
    ∀ j x i, 0 ≤ averagedNorm g0 j x i := by
  intro j
  induction j with
  | zero => exact h
  | succ j ih => exact fun y i => lineBlockAverage_nonneg ih (y, i)
theorem sum_averagedNorm_pow_four_le (hodd : Odd F.blockSide) (D : Finset F.Cell) {g0 : F.Site 0 → Fin 4 → ℝ}
    (h : ∀ x i, 0 ≤ g0 x i) :
    ∀ j, j ≤ F.top → ∑ b ∈ innerBonds D j, averagedNorm g0 j b.1 b.2 ^ 4 ≤ ∑ b ∈ innerBonds D 0, g0 b.1 b.2 ^ 4 := by
  intro j
  induction j with
  | zero => intro _; exact le_rfl
  | succ j ih =>
    intro hj
    exact (sum_lineBlockAverage_pow_four_le (by omega) hodd (innerBonds D (j + 1)) subset_rfl _
      (averagedNorm_nonneg h j)).trans (ih (by omega))
section Levels
variable (R : F.FieldChain) (γ : F.Site 0 → UnitQuaternion) (f : F.Site 0 → Fin 4 → ℍ[ℝ])
def framedTransportedForm (j : ℕ) : F.Site j → Fin 4 → ℍ[ℝ] := frameForm γ (transportedForm R f j)
theorem framedTransportedForm_succ {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (i : Fin 4) :
    framedTransportedForm R γ f (j + 1) y i =
      parallelAverage (frameField γ (R j)) (framedTransportedForm R γ f j) (y, i) := by
  unfold framedTransportedForm
  rw [parallelAverage_frameField γ hj]
  rfl
theorem norm_framedTransportedForm_le (hodd : Odd F.blockSide) : ∀ j, j ≤ F.top → ∀ x i,
    ‖framedTransportedForm R γ f j x i‖ ≤
      averagedNorm (fun x i => ‖framedTransportedForm R γ f 0 x i‖) j x i := by
  intro j
  induction j with
  | zero => intro _ x i; exact le_rfl
  | succ j ih =>
    intro hj y i
    rw [framedTransportedForm_succ R γ f (by omega)]
    refine (norm_parallelAverage_le hodd _ _ (y, i)).trans ?_
    have e := lineBlockAverage_eq (fun x i => ‖framedTransportedForm R γ f j x i‖)
      ((y, i) : F.Site (j + 1) × Fin 4)
    rw [← e]
    exact lineBlockAverage_mono (ih (by omega)) (y, i)
theorem levelScale_succ (hL : 0 < F.blockSide) {j : ℕ} (hj : j < F.top) :
    levelScale F (j + 1) = F.blockSide * levelScale F j := by
  unfold levelScale
  have e : F.top - j = (F.top - (j + 1)) + 1 := by omega
  rw [e, pow_succ]
  field_simp
theorem norm_framedTransportedForm_sub_flat_le (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) {D : Finset F.Cell}
    {E : ℝ} (hE : 0 ≤ E)
    (hR : ∀ j, j < F.top → ∀ x i, x ∈ sitesOfCells D j → x + unitStep j i ∈ sitesOfCells D j →
      ‖((frameField γ (R j) x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ E * levelScale F j) :
    ∀ j, j < F.top → ∀ b ∈ innerBonds D j,
      ‖framedTransportedForm R γ f j b.1 b.2 - flatTransported (framedTransportedForm R γ f 0) j b.1 b.2‖ ≤
        12 * E * levelScale F j * averagedNorm (fun x i => ‖framedTransportedForm R γ f 0 x i‖) j b.1 b.2 := by
  have hLpos := hodd.pos
  have hL2 : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  have hl0 : ∀ j, 0 ≤ levelScale F j := fun j => by
    unfold levelScale
    positivity
  have hm0 := averagedNorm_nonneg (g0 := fun x i => ‖framedTransportedForm R γ f 0 x i‖) (fun _ _ => norm_nonneg _)
  intro j
  induction j with
  | zero =>
    intro _ b _
    simp only [flatTransported, sub_self, norm_zero]
    have := hm0 0 b.1 b.2
    have h2 := hl0 0
    positivity
  | succ j ih =>
    intro hj c hc
    have hjn : j < F.top := by omega
    have e1 : framedTransportedForm R γ f (j + 1) c.1 c.2 =
        parallelAverage (frameField γ (R j)) (framedTransportedForm R γ f j) c :=
      framedTransportedForm_succ R γ f hjn c.1 c.2
    have e2 : flatTransported (framedTransportedForm R γ f 0) (j + 1) c.1 c.2 =
        flatAverage (flatTransported (framedTransportedForm R γ f 0) j) c := rfl
    rw [e1, e2]
    set g := framedTransportedForm R γ f j with hg
    set P := flatTransported (framedTransportedForm R γ f 0) j with hP
    set m := averagedNorm (fun x i => ‖framedTransportedForm R γ f 0 x i‖) j with hm
    have hmc : averagedNorm (fun x i => ‖framedTransportedForm R γ f 0 x i‖) (j + 1) c.1 c.2 =
        lineBlockAverage m c := rfl
    rw [hmc]
    have a1 := norm_parallelAverage_sub_flatAverage_le hodd hjn (mul_nonneg hE (hl0 j)) (hR j hjn) g hc
    have a2 : lineBlockAverage (fun x i => ‖g x i‖) c ≤ lineBlockAverage m c :=
      lineBlockAverage_mono (norm_framedTransportedForm_le R γ f hodd j hjn.le) c
    have a3 : ‖flatAverage g c - flatAverage P c‖ ≤ 12 * E * levelScale F j * lineBlockAverage m c := by
      unfold flatAverage
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity), lineBlockAverage_eq]
      simp only [← Finset.sum_sub_distrib]
      have hb : ‖∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
          (g (lineBond c h r).1 (lineBond c h r).2 - P (lineBond c h r).1 (lineBond c h r).2)‖ ≤
          12 * E * levelScale F j * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
            m (lineBond c h r).1 (lineBond c h r).2 := by
        refine (norm_sum_le _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun h hh => ?_
        refine (norm_sum_le _ _).trans ?_
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun r hr =>
          ih hjn _ (lineBond_mem_innerBonds hjn hodd c hc h hh r (Finset.mem_range.1 hr))
      have h3 := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 1 / (F.blockSide : ℝ) ^ 4)
      refine h3.trans (le_of_eq ?_)
      ring
    have hpa : 0 ≤ lineBlockAverage m c := lineBlockAverage_nonneg (hm0 j) c
    have hstep := levelScale_succ hLpos hjn
    have hlj := hl0 j
    have e3 : parallelAverage (frameField γ (R j)) g c - flatAverage P c =
        (parallelAverage (frameField γ (R j)) g c - flatAverage g c) + (flatAverage g c - flatAverage P c) := by
      abel
    rw [e3, hstep]
    refine (norm_add_le _ _).trans ?_
    have h5 : 6 * F.blockSide * (E * levelScale F j) * lineBlockAverage (fun x i => ‖g x i‖) c ≤
        6 * F.blockSide * (E * levelScale F j) * lineBlockAverage m c :=
      mul_le_mul_of_nonneg_left a2 (by positivity)
    have h6 : 0 ≤ E * levelScale F j * lineBlockAverage m c := by positivity
    nlinarith
end Levels
def flatCurl {j : ℕ} (f : F.Site j → Fin 4 → ℍ[ℝ]) (q : F.Site j × Fin 4 × Fin 4) : ℍ[ℝ] :=
  f q.1 q.2.1 + f (q.1 + unitStep j q.2.1) q.2.2 - f (q.1 + unitStep j q.2.2) q.2.1 - f q.1 q.2.2
def subSquareCorner {j : ℕ} (y : F.Site (j + 1)) (μ ν : Fin 4) (h : Fin 4 → ℤ) (a b : ℕ) : F.Site j :=
  refineSite y + siteOfCoords j h + (a : ℤ) • unitStep j μ + (b : ℤ) • unitStep j ν
theorem sum_sum_telescope (A B : ℕ → ℕ → ℍ[ℝ]) (L : ℕ) :
    ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, ((A a b - A a (b + 1)) + (B (a + 1) b - B a b)) =
      ∑ a ∈ Finset.range L, (A a 0 - A a L) + ∑ b ∈ Finset.range L, (B L b - B 0 b) := by
  simp only [Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun a _ => Finset.sum_range_sub' (fun b => A a b) L
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_range_sub (fun a => B a b) L
theorem siteOfCoords_zsmul_basisVector {j : ℕ} (k : ℤ) (μ : Fin 4) :
    siteOfCoords (F := F) j (k • basisVector μ) = k • unitStep j μ := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_single <;> assumption
theorem refineSite_add_unitStep_eq {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (μ : Fin 4) :
    refineSite (y + unitStep (j + 1) μ) = refineSite y + (F.blockSide : ℤ) • unitStep j μ := by
  rw [refineSite_add_unitStep hj, siteOfCoords_zsmul_basisVector]
theorem flatCurl_flatAverage {j : ℕ} (hj : j < F.top) (g : F.Site j → Fin 4 → ℍ[ℝ]) (y : F.Site (j + 1))
    (μ ν : Fin 4) :
    flatCurl (fun y' i => flatAverage g (y', i)) (y, μ, ν) = (1 / (F.blockSide : ℝ) ^ 4) •
      ∑ h ∈ centredCube F.blockSide, ∑ a ∈ Finset.range F.blockSide, ∑ b ∈ Finset.range F.blockSide,
        flatCurl g (subSquareCorner y μ ν h a b, μ, ν) := by
  simp only [flatCurl, flatAverage, lineBond]
  rw [← smul_add, ← smul_sub, ← smul_sub]
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  set x := refineSite y + siteOfCoords j h with hx
  set E1 := unitStep (F := F) j μ with hE1
  set E2 := unitStep (F := F) j ν with hE2
  set A : ℕ → ℕ → ℍ[ℝ] := fun a b => g (x + (a : ℤ) • E1 + (b : ℤ) • E2) μ with hA
  set B : ℕ → ℕ → ℍ[ℝ] := fun a b => g (x + (a : ℤ) • E1 + (b : ℤ) • E2) ν with hB
  have hsum := sum_sum_telescope A B F.blockSide
  have e1 : ∀ a b : ℕ, subSquareCorner y μ ν h a b = x + (a : ℤ) • E1 + (b : ℤ) • E2 := fun _ _ => rfl
  have e2 : ∀ a b : ℕ, x + (a : ℤ) • E1 + (b : ℤ) • E2 + E1 = x + ((a + 1 : ℕ) : ℤ) • E1 + (b : ℤ) • E2 := by
    intro a b
    push_cast
    rw [add_smul, one_smul]
    abel
  have e3 : ∀ a b : ℕ, x + (a : ℤ) • E1 + (b : ℤ) • E2 + E2 = x + (a : ℤ) • E1 + ((b + 1 : ℕ) : ℤ) • E2 := by
    intro a b
    push_cast
    rw [add_smul, one_smul]
    abel
  have hterm : ∀ a b : ℕ, flatCurl g (subSquareCorner y μ ν h a b, μ, ν) =
      (A a b - A a (b + 1)) + (B (a + 1) b - B a b) := by
    intro a b
    simp only [flatCurl, e1, hA, hB]
    rw [e2, e3]
    abel
  simp only [flatCurl, e1] at hterm
  have hrhs : ∑ a ∈ Finset.range F.blockSide, ∑ b ∈ Finset.range F.blockSide,
      (g (x + (a : ℤ) • E1 + (b : ℤ) • E2) μ + g (x + (a : ℤ) • E1 + (b : ℤ) • E2 + E1) ν -
        g (x + (a : ℤ) • E1 + (b : ℤ) • E2 + E2) μ - g (x + (a : ℤ) • E1 + (b : ℤ) • E2) ν) =
      ∑ a ∈ Finset.range F.blockSide, (A a 0 - A a F.blockSide) +
        ∑ b ∈ Finset.range F.blockSide, (B F.blockSide b - B 0 b) := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm a b
  simp only [subSquareCorner]
  rw [hrhs, refineSite_add_unitStep_eq hj, refineSite_add_unitStep_eq hj, ← hE1, ← hE2]
  simp only [hA, hB, Finset.sum_sub_distrib]
  have f1 : ∀ r : ℕ, refineSite y + (F.blockSide : ℤ) • E1 + siteOfCoords j h + (r : ℤ) • E2 =
      x + ((F.blockSide : ℕ) : ℤ) • E1 + (r : ℤ) • E2 := by
    intro r
    rw [hx]
    abel
  have f2 : ∀ r : ℕ, refineSite y + (F.blockSide : ℤ) • E2 + siteOfCoords j h + (r : ℤ) • E1 =
      x + (r : ℤ) • E1 + ((F.blockSide : ℕ) : ℤ) • E2 := by
    intro r
    rw [hx]
    abel
  have f3 : ∀ a : ℕ, x + (a : ℤ) • E1 + ((0 : ℕ) : ℤ) • E2 = x + (a : ℤ) • E1 := by
    intro a
    simp
  have f4 : ∀ b : ℕ, x + ((0 : ℕ) : ℤ) • E1 + (b : ℤ) • E2 = x + (b : ℤ) • E2 := by
    intro b
    simp
  simp only [f1, f2, f3, f4]
  abel
theorem innerBonds_of_mem_innerPlaquettes {D : Finset F.Cell} {j : ℕ} {q : F.Site j × Fin 4 × Fin 4}
    (hq : q ∈ innerPlaquettes D j) :
    (q.1, q.2.1) ∈ innerBonds D j ∧ (q.1 + unitStep j q.2.1, q.2.2) ∈ innerBonds D j ∧
      (q.1 + unitStep j q.2.2, q.2.1) ∈ innerBonds D j ∧ (q.1, q.2.2) ∈ innerBonds D j := by apply _root_.YangMills.Construction.BlockAverages.ColdBelowTop.plaquette_edges_mem_innerBonds <;> assumption
theorem norm_flatCurl_sub_covariantCurlAt_le {j : ℕ} (Y : F.GaugeField j) (g : F.Site j → Fin 4 → ℍ[ℝ])
    (q : F.Site j × Fin 4 × Fin 4) {ε : ℝ}
    (h1 : ‖((Y q.1 q.2.1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (h2 : ‖((Y (q.1 + unitStep j q.2.1) q.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (h3 : ‖((Y (q.1 + unitStep j q.2.2) q.2.1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (h4 : ‖((Y q.1 q.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε) :
    ‖flatCurl g q - covariantCurlAt Y g q‖ ≤ 8 * ε * (‖g (q.1 + unitStep j q.2.1) q.2.2‖ +
      ‖g (q.1 + unitStep j q.2.2) q.2.1‖ + ‖g q.1 q.2.2‖) := by
  obtain ⟨x, μ, ν⟩ := q
  simp only [flatCurl, covariantCurlAt] at *
  set r1 := Y x μ
  set r2 := Y (x + unitStep j μ) ν
  set r3 := Y (x + unitStep j ν) μ
  set r4 := Y x ν
  set g2 := g (x + unitStep j μ) ν
  set g3 := g (x + unitStep j ν) μ
  set g4 := g x ν
  have hε : 0 ≤ ε := (norm_nonneg _).trans h1
  have n2 : ‖((r1 * r2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * ε := by
    have := norm_coe_mul_sub_one_le r1 r2
    linarith
  have n3 : ‖((r1 * r2 * r3⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 3 * ε := by
    have := norm_coe_mul_sub_one_le (r1 * r2) r3⁻¹
    rw [norm_coe_inv_sub_one] at this
    linarith
  have n4 : ‖((r1 * r2 * r3⁻¹ * r4⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 4 * ε := by
    have := norm_coe_mul_sub_one_le (r1 * r2 * r3⁻¹) r4⁻¹
    rw [norm_coe_inv_sub_one] at this
    linarith
  have a2 := norm_adjointAction_sub_le r1 g2
  have a3 := norm_adjointAction_sub_le (r1 * r2 * r3⁻¹) g3
  have a4 := norm_adjointAction_sub_le (r1 * r2 * r3⁻¹ * r4⁻¹) g4
  have e : g x μ + g2 - g3 - g4 - (g x μ + adjointAction r1 g2 - adjointAction (r1 * r2 * r3⁻¹) g3 -
      adjointAction (r1 * r2 * r3⁻¹ * r4⁻¹) g4) =
      -(adjointAction r1 g2 - g2) + (adjointAction (r1 * r2 * r3⁻¹) g3 - g3) +
        (adjointAction (r1 * r2 * r3⁻¹ * r4⁻¹) g4 - g4) := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have b1 := norm_add_le (-(adjointAction r1 g2 - g2)) (adjointAction (r1 * r2 * r3⁻¹) g3 - g3)
  rw [norm_neg] at b1
  have p2 : 0 ≤ ‖g2‖ := norm_nonneg _
  have p3 : 0 ≤ ‖g3‖ := norm_nonneg _
  have p4 : 0 ≤ ‖g4‖ := norm_nonneg _
  have c2 : 2 * ‖(r1 : ℍ[ℝ]) - 1‖ * ‖g2‖ ≤ 2 * ε * ‖g2‖ := by
    have := mul_le_mul_of_nonneg_right h1 p2
    linarith
  have c3 : 2 * ‖((r1 * r2 * r3⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ * ‖g3‖ ≤ 6 * ε * ‖g3‖ := by
    have := mul_le_mul_of_nonneg_right n3 p3
    linarith
  have c4 : 2 * ‖((r1 * r2 * r3⁻¹ * r4⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ * ‖g4‖ ≤ 8 * ε * ‖g4‖ := by
    have := mul_le_mul_of_nonneg_right n4 p4
    linarith
  have d2 : 0 ≤ ε * ‖g2‖ := by positivity
  have d3 : 0 ≤ ε * ‖g3‖ := by positivity
  nlinarith
theorem subSquareCorner_eq {j : ℕ} (y : F.Site (j + 1)) (μ ν : Fin 4) (h : Fin 4 → ℤ) (a b : ℕ) :
    subSquareCorner y μ ν h a b =
      refineSite y + siteOfCoords j (h + (a : ℤ) • basisVector μ + (b : ℤ) • basisVector ν) := by
  simp only [subSquareCorner]
  rw [siteOfCoords_add, siteOfCoords_add, siteOfCoords_zsmul_basisVector, siteOfCoords_zsmul_basisVector]
  abel
theorem subSquare_offset_bounds {L : ℕ} {h : Fin 4 → ℤ} (hh : h ∈ centredCube L) {μ ν : Fin 4} (hμν : μ ≠ ν)
    {a b : ℕ} (ha : a ≤ L) (hb : b ≤ L) (k : Fin 4) :
    -(((L : ℤ) - 1) / 2) ≤ (h + (a : ℤ) • basisVector μ + (b : ℤ) • basisVector ν) k ∧
      (h + (a : ℤ) • basisVector μ + (b : ℤ) • basisVector ν) k ≤ ((L : ℤ) - 1) / 2 +
        (if k = μ then (a : ℤ) else 0) + (if k = ν then (b : ℤ) else 0) := by
  have hc := (LatticePaths.mem_centredCube_iff _ _).1 hh k
  by_cases h1 : k = μ
  · subst h1
    have h2 : k ≠ ν := hμν
    simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, Pi.single_eq_of_ne h2, smul_eq_mul,
      mul_one, mul_zero, add_zero, if_true, if_neg h2]
    omega
  · by_cases h2 : k = ν
    · subst h2
      simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, Pi.single_eq_of_ne h1, smul_eq_mul,
        mul_one, mul_zero, add_zero, if_true, if_neg h1]
      omega
    · simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2,
        smul_eq_mul, mul_zero, add_zero, if_neg h1, if_neg h2]
      omega
theorem subSquareCorner_mem_sitesOfCells {D : Finset F.Cell} (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top)
    {y : F.Site (j + 1)} {μ ν : Fin 4} (hμν : μ ≠ ν) (c1 : y ∈ sitesOfCells D (j + 1))
    (c2 : y + unitStep (j + 1) μ ∈ sitesOfCells D (j + 1)) (c3 : y + unitStep (j + 1) ν ∈ sitesOfCells D (j + 1))
    (c4 : y + unitStep (j + 1) μ + unitStep (j + 1) ν ∈ sitesOfCells D (j + 1)) {h : Fin 4 → ℤ}
    (hh : h ∈ centredCube F.blockSide) {a b : ℕ} (ha : a ≤ F.blockSide) (hb : b ≤ F.blockSide) :
    subSquareCorner y μ ν h a b ∈ sitesOfCells D j := by
  rw [subSquareCorner_eq]
  set v := h + (a : ℤ) • basisVector μ + (b : ℤ) • basisVector ν with hv
  have hk : ∀ k, -(((F.blockSide : ℤ) - 1) / 2) ≤ v k ∧ v k ≤ ((F.blockSide : ℤ) - 1) / 2 +
      (if k = μ then (a : ℤ) else 0) + (if k = ν then (b : ℤ) else 0) := fun k =>
    subSquare_offset_bounds hh hμν ha hb k
  have hLodd : (F.blockSide : ℤ) = 2 * (((F.blockSide : ℤ) - 1) / 2) + 1 := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm]
    push_cast
    omega
  by_cases hc : v ν ≤ ((F.blockSide : ℤ) - 1) / 2
  · refine BlockLines.refineSite_add_mem_of_mem_twoBlockHull hj hodd y μ c1 c2 v fun k => ?_
    obtain ⟨k1, k2⟩ := hk k
    refine ⟨k1, ?_⟩
    by_cases h1 : k = ν
    · subst h1
      have : k ≠ μ := fun e => hμν e.symm
      simp only [if_neg this]
      omega
    · by_cases h2 : k = μ
      · subst h2
        simp only [if_true, if_neg h1] at k2 ⊢
        omega
      · simp only [if_neg h1, if_neg h2] at k2 ⊢
        omega
  · have e : refineSite y + siteOfCoords j v =
        refineSite (y + unitStep (j + 1) ν) + siteOfCoords j (v - (F.blockSide : ℤ) • basisVector ν) := by
      rw [refineSite_add_unitStep hj, add_assoc, ← siteOfCoords_add]
      congr 2
      abel
    rw [e]
    refine BlockLines.refineSite_add_mem_of_mem_twoBlockHull hj hodd _ μ c3 ?_ _ fun k => ?_
    · rwa [add_right_comm]
    · obtain ⟨k1, k2⟩ := hk k
      by_cases h1 : k = ν
      · subst h1
        have hne : k ≠ μ := fun e => hμν e.symm
        simp only [if_neg hne, if_true, add_zero] at k2
        simp only [Pi.sub_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one, if_neg hne,
          add_zero]
        omega
      · have : ((F.blockSide : ℤ) • basisVector ν) k = 0 := by
          simp [basisVector, Pi.single_eq_of_ne h1]
        simp only [Pi.sub_apply, this, sub_zero]
        by_cases h2 : k = μ
        · subst h2
          simp only [if_true, if_neg h1, add_zero] at k2 ⊢
          omega
        · simp only [if_neg h1, if_neg h2, add_zero] at k2 ⊢
          omega
theorem subSquareCorner_add_unitStep_left {j : ℕ} (y : F.Site (j + 1)) (μ ν : Fin 4) (h : Fin 4 → ℤ) (a b : ℕ) :
    subSquareCorner y μ ν h a b + unitStep j μ = subSquareCorner y μ ν h (a + 1) b := by
  simp only [subSquareCorner]
  push_cast
  rw [add_smul, one_smul]
  abel
theorem subSquareCorner_add_unitStep_right {j : ℕ} (y : F.Site (j + 1)) (μ ν : Fin 4) (h : Fin 4 → ℤ) (a b : ℕ) :
    subSquareCorner y μ ν h a b + unitStep j ν = subSquareCorner y μ ν h a (b + 1) := by
  simp only [subSquareCorner]
  push_cast
  rw [add_smul, one_smul]
  abel
theorem subSquare_mem_innerPlaquettes {D : Finset F.Cell} (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top)
    {q : F.Site (j + 1) × Fin 4 × Fin 4} (hq : q ∈ innerPlaquettes D (j + 1)) {h : Fin 4 → ℤ}
    (hh : h ∈ centredCube F.blockSide) {a b : ℕ} (ha : a < F.blockSide) (hb : b < F.blockSide) :
    (subSquareCorner q.1 q.2.1 q.2.2 h a b, q.2.1, q.2.2) ∈ innerPlaquettes D j := by
  classical
  obtain ⟨h1, hlt, hc⟩ := Finset.mem_filter.1 hq
  have hne : q.2.1 ≠ q.2.2 := ne_of_lt hlt
  have c1 : q.1 ∈ sitesOfCells D (j + 1) := hc (by simp [plaquetteCorners])
  have c2 : q.1 + unitStep (j + 1) q.2.1 ∈ sitesOfCells D (j + 1) := hc (by simp [plaquetteCorners])
  have c3 : q.1 + unitStep (j + 1) q.2.2 ∈ sitesOfCells D (j + 1) := hc (by simp [plaquetteCorners])
  have c4 : q.1 + unitStep (j + 1) q.2.1 + unitStep (j + 1) q.2.2 ∈ sitesOfCells D (j + 1) :=
    hc (by simp [plaquetteCorners])
  have hs : ∀ a' b' : ℕ, a' ≤ F.blockSide → b' ≤ F.blockSide →
      subSquareCorner q.1 q.2.1 q.2.2 h a' b' ∈ sitesOfCells D j :=
    fun a' b' ha' hb' => subSquareCorner_mem_sitesOfCells hodd hj hne c1 c2 c3 c4 hh ha' hb'
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hs a b ha.le hb.le, by simp⟩, hlt, ?_⟩
  intro x hx
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hs a b ha.le hb.le
  · rw [subSquareCorner_add_unitStep_left]
    exact hs _ _ ha hb.le
  · rw [subSquareCorner_add_unitStep_right]
    exact hs _ _ ha.le hb
  · rw [subSquareCorner_add_unitStep_left, subSquareCorner_add_unitStep_right]
    exact hs _ _ ha hb
theorem shiftedWeight_le_subSquareCorner (hL : 2 ≤ F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (p : F.Site 0) {j : ℕ}
    (hj : j < F.top) (y : F.Site (j + 1)) {μ ν : Fin 4} (hμν : μ ≠ ν) {h : Fin 4 → ℤ}
    (hh : h ∈ centredCube F.blockSide) {a b : ℕ} (ha : a < F.blockSide) (hb : b < F.blockSide) :
    shiftedWeight F θ p (j + 1) y ≤ shiftedWeight F θ p j (subSquareCorner y μ ν h a b) := by
  rw [subSquareCorner_eq]
  refine shiftedWeight_succ_le hL hθ p hj y _ fun k => ?_
  obtain ⟨k1, k2⟩ := subSquare_offset_bounds hh hμν ha.le hb.le k
  have hbound : (if k = μ then (a : ℤ) else 0) + (if k = ν then (b : ℤ) else 0) ≤ F.blockSide := by
    by_cases h1 : k = μ
    · subst h1
      have : k ≠ ν := hμν
      simp only [if_true, if_neg this]
      omega
    · simp only [if_neg h1]
      split_ifs <;> omega
  omega
theorem sum_flatCurl_flatAverage_sq_le (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ)
    (p : F.Site 0) (D : Finset F.Cell) {j : ℕ} (hj : j < F.top) (g : F.Site j → Fin 4 → ℍ[ℝ]) :
    ∑ q ∈ innerPlaquettes D (j + 1),
        (shiftedWeight F θ p (j + 1) q.1 * ‖flatCurl (fun y i => flatAverage g (y, i)) q‖) ^ 2 ≤
      ∑ q ∈ innerPlaquettes D j, (shiftedWeight F θ p j q.1 * ‖flatCurl g q‖) ^ 2 := by
  classical
  have hLpos := hodd.pos
  set W : F.Site j × Fin 4 × Fin 4 → ℝ := fun q => shiftedWeight F θ p j q.1 * ‖flatCurl g q‖ with hW
  have hΩ0 : ∀ {j : ℕ} (x : F.Site j), 0 ≤ shiftedWeight F θ p j x := fun x =>
    zero_le_one.trans (one_le_shiftedWeight hLpos hθ p _ x)
  set I : Finset ((Fin 4 → ℤ) × ℕ × ℕ) :=
    centredCube F.blockSide ×ˢ (Finset.range F.blockSide ×ˢ Finset.range F.blockSide) with hI
  have hcard : (I.card : ℝ) = (F.blockSide : ℝ) ^ 6 := by
    rw [hI, Finset.card_product, Finset.card_product, card_centredCube hodd, Finset.card_range]
    push_cast
    ring
  set pt : F.Site (j + 1) × Fin 4 × Fin 4 → (Fin 4 → ℤ) × ℕ × ℕ → F.Site j × Fin 4 × Fin 4 :=
    fun q i => (subSquareCorner q.1 q.2.1 q.2.2 i.1 i.2.1 i.2.2, q.2.1, q.2.2) with hpt
  have hone : ∀ q ∈ innerPlaquettes D (j + 1),
      (shiftedWeight F θ p (j + 1) q.1 * ‖flatCurl (fun y i => flatAverage g (y, i)) q‖) ^ 2 ≤
        (1 / (F.blockSide : ℝ) ^ 2) * ∑ i ∈ I, W (pt q i) ^ 2 := by
    intro q hq
    have hne : q.2.1 ≠ q.2.2 := ne_of_lt (Finset.mem_filter.1 hq).2.1
    have hA : shiftedWeight F θ p (j + 1) q.1 * ‖flatCurl (fun y i => flatAverage g (y, i)) q‖ ≤
        (1 / (F.blockSide : ℝ) ^ 4) * ∑ i ∈ I, W (pt q i) := by
      obtain ⟨y, μ, ν⟩ := q
      simp only at hne
      rw [flatCurl_flatAverage hj, norm_smul, Real.norm_of_nonneg (by positivity), mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hI, Finset.sum_product]
      refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hΩ0 _)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun h hh => ?_
      rw [Finset.sum_product]
      refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hΩ0 _)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a ha => ?_
      refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hΩ0 _)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b hb => ?_
      exact mul_le_mul_of_nonneg_right
        (shiftedWeight_le_subSquareCorner hL hθ p hj y hne hh (Finset.mem_range.1 ha) (Finset.mem_range.1 hb))
        (norm_nonneg _)
    have hA0 : 0 ≤ shiftedWeight F θ p (j + 1) q.1 * ‖flatCurl (fun y i => flatAverage g (y, i)) q‖ :=
      mul_nonneg (hΩ0 _) (norm_nonneg _)
    have h2 := pow_le_pow_left₀ hA0 hA 2
    have h3 := sq_sum_le_card_mul_sum_sq (s := I) (f := fun i => W (pt q i))
    rw [hcard] at h3
    refine h2.trans ?_
    rw [mul_pow]
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ (1 / (F.blockSide : ℝ) ^ 4) ^ 2)
    refine h4.trans (le_of_eq ?_)
    field_simp
  have hab : ∀ a ∈ Finset.range F.blockSide, ∀ b ∈ Finset.range F.blockSide,
      ∑ q ∈ innerPlaquettes D (j + 1), ∑ h ∈ centredCube F.blockSide, W (pt q (h, a, b)) ^ 2 ≤
        ∑ q ∈ innerPlaquettes D j, W q ^ 2 := by
    intro a ha b hb
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    rw [← Finset.sum_product']
    have hinj : Set.InjOn (fun x : (F.Site (j + 1) × Fin 4 × Fin 4) × (Fin 4 → ℤ) => pt x.1 (x.2, a, b))
        (innerPlaquettes D (j + 1) ×ˢ centredCube F.blockSide : Finset _) := by
      intro x hx x' hx' e
      have h1 := Finset.mem_product.1 (Finset.mem_coe.1 hx)
      have h2 := Finset.mem_product.1 (Finset.mem_coe.1 hx')
      simp only [hpt] at e
      obtain ⟨e1, e2⟩ := Prod.ext_iff.1 e
      obtain ⟨e3, e4⟩ := Prod.ext_iff.1 e2
      simp only at e1 e3 e4
      simp only [subSquareCorner] at e1
      rw [e3, e4] at e1
      have e5 := add_right_cancel (add_right_cancel e1)
      obtain ⟨i1, i2⟩ := refineSite_add_injective hj hodd x.1.1 x'.1.1 x.2 x'.2 h1.2 h2.2 e5
      exact Prod.ext (Prod.ext i1 (Prod.ext e3 e4)) i2
    have := Finset.sum_image (f := fun q => W q ^ 2) hinj
    rw [← this]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => by positivity
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hq
    have h1 := Finset.mem_product.1 hx
    exact subSquare_mem_innerPlaquettes hodd hj h1.1 h1.2 ha' hb'
  refine (Finset.sum_le_sum hone).trans ?_
  rw [← Finset.mul_sum]
  have hswap : ∑ q ∈ innerPlaquettes D (j + 1), ∑ i ∈ I, W (pt q i) ^ 2 =
      ∑ a ∈ Finset.range F.blockSide, ∑ b ∈ Finset.range F.blockSide, ∑ q ∈ innerPlaquettes D (j + 1),
        ∑ h ∈ centredCube F.blockSide, W (pt q (h, a, b)) ^ 2 := by
    calc _ = ∑ q ∈ innerPlaquettes D (j + 1), ∑ h ∈ centredCube F.blockSide, ∑ a ∈ Finset.range F.blockSide,
          ∑ b ∈ Finset.range F.blockSide, W (pt q (h, a, b)) ^ 2 := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hI, Finset.sum_product]
          exact Finset.sum_congr rfl fun h _ => Finset.sum_product _ _ _
      _ = ∑ q ∈ innerPlaquettes D (j + 1), ∑ a ∈ Finset.range F.blockSide, ∑ b ∈ Finset.range F.blockSide,
          ∑ h ∈ centredCube F.blockSide, W (pt q (h, a, b)) ^ 2 := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a ∈ Finset.range F.blockSide, ∑ q ∈ innerPlaquettes D (j + 1), ∑ b ∈ Finset.range F.blockSide,
          ∑ h ∈ centredCube F.blockSide, W (pt q (h, a, b)) ^ 2 := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [hswap]
  have hle : ∑ a ∈ Finset.range F.blockSide, ∑ b ∈ Finset.range F.blockSide, ∑ q ∈ innerPlaquettes D (j + 1),
      ∑ h ∈ centredCube F.blockSide, W (pt q (h, a, b)) ^ 2 ≤
        (F.blockSide : ℝ) ^ 2 * ∑ q ∈ innerPlaquettes D j, W q ^ 2 := by
    refine (Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hab a ha b hb).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have h5 := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 1 / (F.blockSide : ℝ) ^ 2)
  refine h5.trans (le_of_eq ?_)
  rw [← mul_assoc, one_div, inv_mul_cancel₀ (by positivity), one_mul]
theorem sum_flatCurl_flatTransported_sq_le (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ)
    (p : F.Site 0) (D : Finset F.Cell) (g0 : F.Site 0 → Fin 4 → ℍ[ℝ]) : ∀ j, j < F.top →
    ∑ q ∈ innerPlaquettes D j, (shiftedWeight F θ p j q.1 * ‖flatCurl (flatTransported g0 j) q‖) ^ 2 ≤
      ∑ q ∈ innerPlaquettes D 0, (shiftedWeight F θ p 0 q.1 * ‖flatCurl g0 q‖) ^ 2 := by
  intro j
  induction j with
  | zero => intro _; exact le_rfl
  | succ j ih =>
    intro hj
    exact (sum_flatCurl_flatAverage_sq_le hodd hL hθ p D (by omega) (flatTransported g0 j)).trans (ih (by omega))
theorem sum_plaquettes_le_sixteen_mul_sum_bonds {P : Finset (F.Site 0 × Fin 4 × Fin 4)}
    {B : Finset (F.Site 0 × Fin 4)} (g : F.Site 0 × Fin 4 → ℝ) (hg : ∀ b, 0 ≤ g b)
    (T : F.Site 0 × Fin 4 × Fin 4 → F.Site 0 × Fin 4) (hT : ∀ q ∈ P, T q ∈ B)
    (hinj : ∀ q ∈ P, ∀ q' ∈ P, q.2 = q'.2 → T q = T q' → q.1 = q'.1) :
    ∑ q ∈ P, g (T q) ≤ 16 * ∑ b ∈ B, g b := by
  classical
  refine NearCellNorms.sum_le_of_fiber_le P fun d => ?_
  have hi : Set.InjOn T (P.filter fun p => p.2 = d : Finset _) := by
    intro q hq q' hq' e
    have a1 := Finset.mem_filter.1 (Finset.mem_coe.1 hq)
    have a2 := Finset.mem_filter.1 (Finset.mem_coe.1 hq')
    exact Prod.ext (hinj q a1.1 q' a2.1 (a1.2.trans a2.2.symm) e) (a1.2.trans a2.2.symm)
  rw [← Finset.sum_image (f := g) hi]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => hg b
  intro b hb
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hb
  exact hT q (Finset.mem_filter.1 hq).1
theorem sq_le_of_le_add_mul_sum {X e a b c y : ℝ} (hy0 : 0 ≤ y) (h : y ≤ X + e * (a + b + c)) (hX : 0 ≤ X)
    (he : 0 ≤ e) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    y ^ 2 ≤ 2 * X ^ 2 + 6 * e ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have h1 := pow_le_pow_left₀ hy0 h 2
  have h2 : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have h3 : (X + e * (a + b + c)) ^ 2 ≤ 2 * X ^ 2 + 2 * (e * (a + b + c)) ^ 2 := by
    nlinarith [sq_nonneg (X - e * (a + b + c))]
  have h4 : (e * (a + b + c)) ^ 2 ≤ e ^ 2 * (3 * (a ^ 2 + b ^ 2 + c ^ 2)) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith
theorem sum_flatCurl_frameForm_sq_le (hodd : Odd F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (p : F.Site 0)
    {D : Finset F.Cell} (γ : F.Site 0 → UnitQuaternion) (R0 : F.GaugeField 0) (f : F.Site 0 → Fin 4 → ℍ[ℝ])
    {ε E A B : ℝ} (hε : 0 ≤ ε) (hE : 0 ≤ E) (hεN : ε * (F.blockSide : ℝ) ^ F.top ≤ E) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hR : ∀ x i, x ∈ sitesOfCells D 0 → x + unitStep 0 i ∈ sitesOfCells D 0 →
      ‖((frameField γ R0 x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (hcard : ((innerBonds D 0).card : ℝ) ≤ 2500 * ((F.blockSide : ℝ) ^ F.top) ^ 4)
    (hA : ∑ q ∈ innerPlaquettes D 0, (shiftedWeight F θ p 0 q.1 * ‖covariantCurlAt R0 f q‖) ^ 2 ≤ A ^ 2)
    (hB : ∑ b ∈ innerBonds D 0, (shiftedWeight F θ p 0 b.1 * ‖f b.1 b.2‖) ^ 4 ≤ B ^ 4) :
    ∑ q ∈ innerPlaquettes D 0, (shiftedWeight F θ p 0 q.1 * ‖flatCurl (frameForm γ f) q‖) ^ 2 ≤
      (2 * A + 2000 * E * B) ^ 2 := by
  classical
  have hLpos := hodd.pos
  have hΩ0 : ∀ (x : F.Site 0), 0 ≤ shiftedWeight F θ p 0 x := fun x =>
    zero_le_one.trans (one_le_shiftedWeight hLpos hθ p _ x)
  set Gf : F.Site 0 × Fin 4 → ℝ := fun b => (shiftedWeight F θ p 0 b.1 * ‖f b.1 b.2‖) ^ 2 with hGf
  have hGf0 : ∀ b, 0 ≤ Gf b := fun b => by positivity
  have hnear : ∀ (x x' : F.Site 0), baseDistance x' p ≤ baseDistance x p + 1 → ∀ i,
      shiftedWeight F θ p 0 x * ‖f x' i‖ ≤ 2 * (shiftedWeight F θ p 0 x' * ‖f x' i‖) := by
    intro x x' h i
    have := shiftedWeight_le_two_mul_of_near hLpos hθ hθ1 p (j := 0) (Nat.zero_le _) x x' (by simpa using h)
    have h2 := mul_le_mul_of_nonneg_right this (norm_nonneg (f x' i))
    linarith
  have hstep : ∀ (x : F.Site 0) (i : Fin 4), baseDistance (x + unitStep 0 i) p ≤ baseDistance x p + 1 := by
    intro x i
    have := baseDistance_add_unitStep_le (F := F) (j := 0) (Nat.zero_le _) x i p
    simpa using this
  have hone : ∀ q ∈ innerPlaquettes D 0,
      (shiftedWeight F θ p 0 q.1 * ‖flatCurl (frameForm γ f) q‖) ^ 2 ≤
        2 * (shiftedWeight F θ p 0 q.1 * ‖covariantCurlAt R0 f q‖) ^ 2 + 6 * (16 * ε) ^ 2 *
          (Gf (q.1 + unitStep 0 q.2.1, q.2.2) + Gf (q.1 + unitStep 0 q.2.2, q.2.1) + Gf (q.1, q.2.2)) := by
    intro q hq
    obtain ⟨b1, b2, b3, b4⟩ := innerBonds_of_mem_innerPlaquettes hq
    have e1 := ChartCoordinates.innerBonds_ends b1
    have e2 := ChartCoordinates.innerBonds_ends b2
    have e3 := ChartCoordinates.innerBonds_ends b3
    have e4 := ChartCoordinates.innerBonds_ends b4
    have h1 := norm_flatCurl_sub_covariantCurlAt_le (frameField γ R0) (frameForm γ f) q (hR _ _ e1.1 e1.2)
      (hR _ _ e2.1 e2.2) (hR _ _ e3.1 e3.2) (hR _ _ e4.1 e4.2)
    have h2 : ‖covariantCurlAt (frameField γ R0) (frameForm γ f) q‖ = ‖covariantCurlAt R0 f q‖ := by
      rw [covariantCurlAt_frameField, BlockLines.norm_adjointAction]
    have h3 : ∀ x i, ‖frameForm γ f x i‖ = ‖f x i‖ := fun x i => BlockLines.norm_adjointAction _ _
    rw [h3, h3, h3] at h1
    have h4 : ‖flatCurl (frameForm γ f) q‖ ≤ ‖covariantCurlAt R0 f q‖ + 8 * ε * (‖f (q.1 + unitStep 0 q.2.1) q.2.2‖ +
        ‖f (q.1 + unitStep 0 q.2.2) q.2.1‖ + ‖f q.1 q.2.2‖) := by
      have := norm_sub_norm_le (flatCurl (frameForm γ f) q) (covariantCurlAt (frameField γ R0) (frameForm γ f) q)
      rw [h2] at this
      linarith
    have hΩ := hΩ0 q.1
    have h5 := mul_le_mul_of_nonneg_left h4 hΩ
    have n2 := hnear q.1 _ (hstep q.1 q.2.1) q.2.2
    have n3 := hnear q.1 _ (hstep q.1 q.2.2) q.2.1
    have n4 := hnear q.1 q.1 (by omega) q.2.2
    set a := shiftedWeight F θ p 0 (q.1 + unitStep 0 q.2.1) * ‖f (q.1 + unitStep 0 q.2.1) q.2.2‖ with ha
    set b := shiftedWeight F θ p 0 (q.1 + unitStep 0 q.2.2) * ‖f (q.1 + unitStep 0 q.2.2) q.2.1‖ with hb
    set c := shiftedWeight F θ p 0 q.1 * ‖f q.1 q.2.2‖ with hc
    have ha0 : 0 ≤ a := mul_nonneg (hΩ0 _) (norm_nonneg _)
    have hb0 : 0 ≤ b := mul_nonneg (hΩ0 _) (norm_nonneg _)
    have hc0 : 0 ≤ c := mul_nonneg (hΩ0 _) (norm_nonneg _)
    have h6 : shiftedWeight F θ p 0 q.1 * ‖flatCurl (frameForm γ f) q‖ ≤
        shiftedWeight F θ p 0 q.1 * ‖covariantCurlAt R0 f q‖ + 16 * ε * (a + b + c) := by
      have hk : shiftedWeight F θ p 0 q.1 * (8 * ε * (‖f (q.1 + unitStep 0 q.2.1) q.2.2‖ +
          ‖f (q.1 + unitStep 0 q.2.2) q.2.1‖ + ‖f q.1 q.2.2‖)) =
          8 * ε * (shiftedWeight F θ p 0 q.1 * ‖f (q.1 + unitStep 0 q.2.1) q.2.2‖ +
            shiftedWeight F θ p 0 q.1 * ‖f (q.1 + unitStep 0 q.2.2) q.2.1‖ +
            shiftedWeight F θ p 0 q.1 * ‖f q.1 q.2.2‖) := by
        ring
      have hk2 : 8 * ε * (shiftedWeight F θ p 0 q.1 * ‖f (q.1 + unitStep 0 q.2.1) q.2.2‖ +
          shiftedWeight F θ p 0 q.1 * ‖f (q.1 + unitStep 0 q.2.2) q.2.1‖ +
          shiftedWeight F θ p 0 q.1 * ‖f q.1 q.2.2‖) ≤ 8 * ε * (2 * a + 2 * b + 2 * c) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add n2 n3) n4) (by positivity)
      rw [mul_add, hk] at h5
      nlinarith
    exact sq_le_of_le_add_mul_sum (mul_nonneg hΩ (norm_nonneg _)) h6 (mul_nonneg hΩ (norm_nonneg _))
      (by positivity) ha0 hb0 hc0
  refine (Finset.sum_le_sum hone).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  have t2 := sum_plaquettes_le_sixteen_mul_sum_bonds (P := innerPlaquettes D 0) (B := innerBonds D 0) Gf hGf0
    (fun q => (q.1 + unitStep 0 q.2.1, q.2.2))
    (fun q hq => (innerBonds_of_mem_innerPlaquettes hq).2.1) (fun q _ q' _ h e => by
      have e1 := (Prod.ext_iff.1 e).1
      simp only at e1
      rw [h] at e1
      exact add_right_cancel e1)
  have t3 := sum_plaquettes_le_sixteen_mul_sum_bonds (P := innerPlaquettes D 0) (B := innerBonds D 0) Gf hGf0
    (fun q => (q.1 + unitStep 0 q.2.2, q.2.1))
    (fun q hq => (innerBonds_of_mem_innerPlaquettes hq).2.2.1) (fun q _ q' _ h e => by
      have e1 := (Prod.ext_iff.1 e).1
      simp only at e1
      rw [h] at e1
      exact add_right_cancel e1)
  have t4 := sum_plaquettes_le_sixteen_mul_sum_bonds (P := innerPlaquettes D 0) (B := innerBonds D 0) Gf hGf0
    (fun q => (q.1, q.2.2))
    (fun q hq => (innerBonds_of_mem_innerPlaquettes hq).2.2.2) (fun q _ q' _ _ e => (Prod.ext_iff.1 e).1)
  have hsq : (∑ b ∈ innerBonds D 0, Gf b) ^ 2 ≤ (50 * ((F.blockSide : ℝ) ^ F.top) ^ 2 * B ^ 2) ^ 2 := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := innerBonds D 0) (f := Gf)
    have h2 : ∑ b ∈ innerBonds D 0, Gf b ^ 2 ≤ B ^ 4 := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) hB
      simp only [hGf]
      ring
    have h3 : ((innerBonds D 0).card : ℝ) * ∑ b ∈ innerBonds D 0, Gf b ^ 2 ≤
        (2500 * ((F.blockSide : ℝ) ^ F.top) ^ 4) * B ^ 4 :=
      mul_le_mul hcard h2 (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    refine h1.trans (h3.trans (le_of_eq ?_))
    ring
  have hS : ∑ b ∈ innerBonds D 0, Gf b ≤ 50 * ((F.blockSide : ℝ) ^ F.top) ^ 2 * B ^ 2 :=
    le_of_not_gt fun hlt => absurd hsq (not_le.2 (pow_lt_pow_left₀ hlt (by positivity) (by norm_num)))
  have hεS : ε ^ 2 * ∑ b ∈ innerBonds D 0, Gf b ≤ 50 * E ^ 2 * B ^ 2 := by
    have h1 : (ε * (F.blockSide : ℝ) ^ F.top) ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ (by positivity) hεN 2
    have h2 := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ ε ^ 2)
    have h3 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 50 * B ^ 2)
    nlinarith
  set S0 := ∑ b ∈ innerBonds D 0, Gf b with hS0
  set T2 := ∑ q ∈ innerPlaquettes D 0, Gf (q.1 + unitStep 0 q.2.1, q.2.2)
  set T3 := ∑ q ∈ innerPlaquettes D 0, Gf (q.1 + unitStep 0 q.2.2, q.2.1)
  set T4 := ∑ q ∈ innerPlaquettes D 0, Gf (q.1, q.2.2)
  have hT : T2 + T3 + T4 ≤ 48 * S0 := by
    linarith
  have hfin : 6 * (16 * ε) ^ 2 * (T2 + T3 + T4) ≤ 6 * (16 * ε) ^ 2 * (48 * S0) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  have hAB : 0 ≤ A * (E * B) := by positivity
  nlinarith
theorem norm_flatCurl_le_add_norm_sub {j : ℕ} (f g : F.Site j → Fin 4 → ℍ[ℝ]) (q : F.Site j × Fin 4 × Fin 4) :
    ‖flatCurl f q‖ ≤ ‖flatCurl g q‖ + ‖f q.1 q.2.1 - g q.1 q.2.1‖ +
      ‖f (q.1 + unitStep j q.2.1) q.2.2 - g (q.1 + unitStep j q.2.1) q.2.2‖ +
      ‖f (q.1 + unitStep j q.2.2) q.2.1 - g (q.1 + unitStep j q.2.2) q.2.1‖ + ‖f q.1 q.2.2 - g q.1 q.2.2‖ := by
  set a := f q.1 q.2.1 - g q.1 q.2.1
  set b := f (q.1 + unitStep j q.2.1) q.2.2 - g (q.1 + unitStep j q.2.1) q.2.2
  set c := f (q.1 + unitStep j q.2.2) q.2.1 - g (q.1 + unitStep j q.2.2) q.2.1
  set d := f q.1 q.2.2 - g q.1 q.2.2
  have e : flatCurl f q = flatCurl g q + a + b - c - d := by
    simp only [flatCurl, a, b, c, d]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_sub_le (flatCurl g q + a + b) c
  have h2 := norm_add_le (flatCurl g q + a) b
  have h3 := norm_add_le (flatCurl g q) a
  linarith
theorem norm_covariantCurlAt_transportedForm_le (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) {θ : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (R : F.FieldChain) (γ : F.Site 0 → UnitQuaternion) {D : Finset F.Cell} {E : ℝ}
    (hE : 0 ≤ E)
    (hR : ∀ j, j < F.top → ∀ x i, x ∈ sitesOfCells D j → x + unitStep j i ∈ sitesOfCells D j →
      ‖((frameField γ (R j) x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ E * levelScale F j)
    (hcard : ((innerBonds D 0).card : ℝ) ≤ 2500 * ((F.blockSide : ℝ) ^ F.top) ^ 4) (f : F.Site 0 → Fin 4 → ℍ[ℝ])
    (p : F.Site 0) {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∑ q ∈ innerPlaquettes D 0, (shiftedWeight F θ p 0 q.1 * ‖covariantCurlAt (R 0) f q‖) ^ 2 ≤ A ^ 2)
    (hB : ∑ b ∈ innerBonds D 0, (shiftedWeight F θ p 0 b.1 * ‖f b.1 b.2‖) ^ 4 ≤ B ^ 4)
    {q : F.Site F.depth × Fin 4 × Fin 4} (hq : q ∈ innerPlaquettes D F.depth) :
    ‖covariantCurlAt (R F.depth) (transportedForm R f F.depth) q‖ ≤
      (shiftedWeight F θ p F.depth q.1)⁻¹ * (2 * A) + 2072 * E * B := by
  classical
  have hLpos := hodd.pos
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hLpos
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hLpos
  have htn : F.depth < F.top := Nat.lt_succ_self _
  have hl0 : ∀ j, 0 ≤ levelScale F j := fun j => by
    unfold levelScale
    positivity
  have hl1 : levelScale F F.depth ≤ 1 := by
    unfold levelScale
    exact pow_le_one₀ (by positivity) (by rw [one_div]; exact inv_le_one_of_one_le₀ hL1)
  have hln : levelScale F 0 * (F.blockSide : ℝ) ^ F.top = 1 := by
    unfold levelScale
    rw [Nat.sub_zero, ← mul_pow, one_div, inv_mul_cancel₀ hLr.ne', one_pow]
  set G := framedTransportedForm R γ f with hG
  set P := flatTransported (G 0) with hP
  set m := averagedNorm (fun x i => ‖G 0 x i‖) with hm
  have hG0 : G 0 = frameForm γ f := rfl
  have hGn : ∀ x i, ‖G 0 x i‖ = ‖f x i‖ := fun x i => BlockLines.norm_adjointAction _ _
  have hbot := sum_flatCurl_frameForm_sq_le hodd hθ hθ1 p γ (R 0) f (mul_nonneg hE (hl0 0)) hE
    (by rw [mul_assoc, hln, mul_one]) hA0 hB0 (hR 0 (Nat.succ_pos _)) hcard hA hB
  have hlev := sum_flatCurl_flatTransported_sq_le hodd hL hθ p D (G 0) F.depth htn
  rw [hG0] at hlev
  have hΩ := one_le_shiftedWeight hLpos hθ p F.depth q.1
  have hΩ0 : 0 < shiftedWeight F θ p F.depth q.1 := lt_of_lt_of_le one_pos hΩ
  have hP1 : shiftedWeight F θ p F.depth q.1 * ‖flatCurl (P F.depth) q‖ ≤ 2 * A + 2000 * E * B := by
    have h1 := Finset.single_le_sum
      (f := fun q' => (shiftedWeight F θ p F.depth q'.1 * ‖flatCurl (P F.depth) q'‖) ^ 2)
      (fun _ _ => by positivity) hq
    have h2 := h1.trans (hlev.trans hbot)
    exact le_of_not_gt fun hlt => absurd h2 (not_le.2 (pow_lt_pow_left₀ hlt (by positivity) (by norm_num)))
  have hP2 : ‖flatCurl (P F.depth) q‖ ≤ (shiftedWeight F θ p F.depth q.1)⁻¹ * (2 * A) + 2000 * E * B := by
    have h1 : ‖flatCurl (P F.depth) q‖ ≤ (shiftedWeight F θ p F.depth q.1)⁻¹ * (2 * A + 2000 * E * B) := by
      rw [inv_mul_eq_div, le_div_iff₀ hΩ0, mul_comm]
      exact hP1
    have h2 : (shiftedWeight F θ p F.depth q.1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΩ
    have h3 : 0 ≤ 2000 * E * B := by positivity
    have h4 := mul_le_mul_of_nonneg_right h2 h3
    rw [mul_add] at h1
    linarith
  obtain ⟨b1, b2, b3, b4⟩ := innerBonds_of_mem_innerPlaquettes hq
  have hm0 := averagedNorm_nonneg (g0 := fun x i => ‖G 0 x i‖) (fun _ _ => norm_nonneg _)
  have hmB : ∀ b ∈ innerBonds D F.depth, m F.depth b.1 b.2 ≤ B := by
    intro b hb
    have h1 := Finset.single_le_sum (f := fun b' : F.Site F.depth × Fin 4 => m F.depth b'.1 b'.2 ^ 4)
      (fun _ _ => by positivity) hb
    have h2 := sum_averagedNorm_pow_four_le hodd D (g0 := fun x i => ‖G 0 x i‖) (fun _ _ => norm_nonneg _)
      F.depth htn.le
    have h3 : ∑ b ∈ innerBonds D 0, ‖G 0 b.1 b.2‖ ^ 4 ≤ B ^ 4 := by
      refine le_trans (Finset.sum_le_sum fun b _ => ?_) hB
      rw [hGn]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 4
      exact le_mul_of_one_le_left (norm_nonneg _) (one_le_shiftedWeight hLpos hθ p 0 b.1)
    have h4 := h1.trans (h2.trans h3)
    exact le_of_not_gt fun hlt => absurd h4 (not_le.2 (pow_lt_pow_left₀ hlt hB0 (by norm_num)))
  have hGB : ∀ b ∈ innerBonds D F.depth, ‖G F.depth b.1 b.2‖ ≤ B := fun b hb =>
    (norm_framedTransportedForm_le R γ f hodd F.depth htn.le b.1 b.2).trans (hmB b hb)
  have hnear := norm_framedTransportedForm_sub_flat_le R γ f hodd hL hE hR F.depth htn
  have hGP : ∀ b ∈ innerBonds D F.depth, ‖G F.depth b.1 b.2 - P F.depth b.1 b.2‖ ≤ 12 * E * B := by
    intro b hb
    refine (hnear b hb).trans ?_
    have h1 := hmB b hb
    have h2 := hm0 F.depth b.1 b.2
    have h3 : levelScale F F.depth * m F.depth b.1 b.2 ≤ 1 * B := mul_le_mul hl1 h1 h2 zero_le_one
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 12 * E)
    linarith
  have hEl : ∀ x i, x ∈ sitesOfCells D F.depth → x + unitStep F.depth i ∈ sitesOfCells D F.depth →
      ‖((frameField γ (R F.depth) x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ E := by
    intro x i h1 h2
    refine (hR F.depth htn x i h1 h2).trans ?_
    exact mul_le_of_le_one_right hE hl1
  have e1 := ChartCoordinates.innerBonds_ends b1
  have e2 := ChartCoordinates.innerBonds_ends b2
  have e3 := ChartCoordinates.innerBonds_ends b3
  have e4 := ChartCoordinates.innerBonds_ends b4
  have h1 := norm_flatCurl_sub_covariantCurlAt_le (frameField γ (R F.depth)) (G F.depth) q (hEl _ _ e1.1 e1.2)
    (hEl _ _ e2.1 e2.2) (hEl _ _ e3.1 e3.2) (hEl _ _ e4.1 e4.2)
  have h2 : ‖covariantCurlAt (frameField γ (R F.depth)) (G F.depth) q‖ =
      ‖covariantCurlAt (R F.depth) (transportedForm R f F.depth) q‖ := by
    show ‖covariantCurlAt (frameField γ (R F.depth)) (frameForm γ (transportedForm R f F.depth)) q‖ = _
    rw [covariantCurlAt_frameField, BlockLines.norm_adjointAction]
  have h3 := norm_flatCurl_le_add_norm_sub (G F.depth) (P F.depth) q
  have g2 := hGB _ b2
  have g3 := hGB _ b3
  have g4 := hGB _ b4
  have p1 := hGP _ b1
  have p2 := hGP _ b2
  have p3 := hGP _ b3
  have p4 := hGP _ b4
  have h4 : 8 * E * (‖G F.depth (q.1 + unitStep F.depth q.2.1) q.2.2‖ +
      ‖G F.depth (q.1 + unitStep F.depth q.2.2) q.2.1‖ + ‖G F.depth q.1 q.2.2‖) ≤ 8 * E * (B + B + B) :=
    mul_le_mul_of_nonneg_left (add_le_add (add_le_add g2 g3) g4) (by positivity)
  have h5 := norm_sub_norm_le (covariantCurlAt (frameField γ (R F.depth)) (G F.depth) q) (flatCurl (G F.depth) q)
  rw [norm_sub_rev, h2] at h5
  simp only [] at p1 p2 p3 p4
  nlinarith
end CarriedCurl
open CarriedCurl BlockAverages
theorem CarriedCurl.cellSupDist_triangle {F : BlockFrame} (a b c : F.Cell) :
    cellSupDist a c ≤ cellSupDist a b + cellSupDist b c := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem CarriedCurl.scaled_mem_centredCube {F : BlockFrame} (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top)
    {h : Fin 4 → ℤ} (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    (fun i => (F.blockSide : ℤ) ^ j * h i) ∈ centredCube (F.blockSide ^ F.top) := by
  obtain ⟨K, hK1, hK2, hK3⟩ := BlockLines.odd_pow_eq_two_mul_add_one hodd (F.top - j)
  have hc := (LatticePaths.mem_centredCube_iff _ _).1 hh
  rw [hK2] at hc
  refine (PatchPoints.mem_centredCube_iff _).2 fun i => ?_
  have hA : 1 ≤ (F.blockSide : ℤ) ^ j := by
    have : 1 ≤ F.blockSide ^ j := Nat.one_le_pow _ _ hodd.pos
    exact_mod_cast this
  set A : ℤ := (F.blockSide : ℤ) ^ j with hAdef
  have hS : GaugeMap.cellSideLength F = A * (2 * (K : ℤ) + 1) := by
    have e1 : GaugeMap.cellSideLength F = (F.blockSide : ℤ) ^ j * (F.blockSide : ℤ) ^ (F.top - j) := by
      unfold GaugeMap.cellSideLength
      rw [← pow_add]
      congr 1
      omega
    have e2 : (F.blockSide : ℤ) ^ (F.top - j) = 2 * (K : ℤ) + 1 := by exact_mod_cast hK1
    rw [e1, e2]
  have hi := hc i
  set x := h i with hx
  have a1 : A * x ≤ A * K := mul_le_mul_of_nonneg_left hi.2 (by omega)
  have a2 : -(A * K) ≤ A * x := by
    have := mul_le_mul_of_nonneg_left hi.1 (by omega : (0 : ℤ) ≤ A)
    linarith
  have a3 : GaugeMap.cellSideLength F = 2 * (A * K) + A := by rw [hS]; ring
  rw [a3]
  constructor <;> omega
theorem CarriedCurl.baseSite_mem_patch {F : BlockFrame} (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S : Finset F.Cell} {z : F.Cell} (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {D : Finset F.Cell} (hDS : D ⊆ S) (hd : ∀ y ∈ D, cellSupDist z y ≤ 10) {j : ℕ} (hj : j ≤ F.top)
    {x : F.Site j} (hx : x ∈ sitesOfCells D j) :
    baseSite x ∈ (GaugeMap.patchDomain S z).image (GaugeMap.patchSite S z) := by
  classical
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
  rw [baseSite_add j hj, baseSite_cellCentre j hj]
  refine Finset.mem_image.2 ⟨_, PatchPoints.patchChart_mem_patchDomain hamb hodd he (hDS hy) (hd y hy)
    (CarriedCurl.scaled_mem_centredCube hodd hj hh), PatchPoints.patchSite_patchChart he _⟩
theorem CarriedCurl.transportedCurlBound_of_referenceBounds (hB : referenceBoundsStatement) :
    transportedCurlBoundStatement := by
  obtain ⟨Db, cb, L1, hDb, hcb, hBd⟩ := hB
  intro θ hθ hθ8
  refine ⟨2072 * Db, cb, max L1 2, by positivity, hcb, ?_⟩
  intro F m S hodd hLm hamb hm hreg s V hs0 hsc hcold f p A B hA0 hB0 hA hB q hq
  classical
  have hL1 : L1 ≤ F.blockSide := (le_max_left _ _).trans hLm
  have hL2 : 2 ≤ F.blockSide := (le_max_right _ _).trans hLm
  obtain ⟨c1, -, -, -, -, -⟩ := hBd F m S hodd hL1 hamb hm hreg s V hs0 hsc hcold
  have hDS : BlockWeights.cellsNearPoint S p ⊆ S := Finset.filter_subset _ _
  have hq1 : q.1 ∈ sitesOfCells (BlockWeights.cellsNearPoint S p) F.depth :=
    (Finset.mem_filter.1 hq).2.2 (by simp [plaquetteCorners])
  have hzD : enclosingCell q.1 ∈ BlockWeights.cellsNearPoint S p := BlockLines.enclosingCell_mem hodd hq1
  have hzS : enclosingCell q.1 ∈ S := hDS hzD
  have he := (closedOrthant_spec hreg (by omega : 32 ≤ m) (enclosingCell q.1)).1
  have hd : ∀ y ∈ BlockWeights.cellsNearPoint S p, cellSupDist (enclosingCell q.1) y ≤ 10 := by
    intro y hy
    have h1 : cellSupDist (enclosingCell q.1) (enclosingCell p) ≤ 2 := (Finset.mem_filter.1 hzD).2
    have h2 : cellSupDist y (enclosingCell p) ≤ 2 := (Finset.mem_filter.1 hy).2
    rw [BlockLines.cellSupDist_comm] at h2
    have := CarriedCurl.cellSupDist_triangle (enclosingCell q.1) (enclosingCell p) y
    omega
  have hR : ∀ j, j < F.top → ∀ x i, x ∈ sitesOfCells (BlockWeights.cellsNearPoint S p) j →
      x + unitStep j i ∈ sitesOfCells (BlockWeights.cellsNearPoint S p) j →
      ‖((frameField (fun x => (GaugeMap.frameChange S V (enclosingCell q.1) x)⁻¹) (referenceFieldChain S V j) x i :
        UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ (Db * s) * levelScale F j := by
    intro j hj x i h1 h2
    exact c1 j hj (enclosingCell q.1) hzS (x, i) (BlockLines.innerBonds_mono hDS j (ChartCoordinates.mem_innerBonds h1 h2))
      (CarriedCurl.baseSite_mem_patch hamb hodd he hDS hd hj.le h1)
      (CarriedCurl.baseSite_mem_patch hamb hodd he hDS hd hj.le h2)
  have hcard : ((innerBonds (BlockWeights.cellsNearPoint S p) 0).card : ℝ) ≤
      2500 * ((F.blockSide : ℝ) ^ F.top) ^ 4 := by
    have h2 := BlockLines.card_innerBonds_le hodd (BlockWeights.cellsNearPoint S p) 0
    have h3 : (BlockWeights.cellsNearPoint S p).card * (F.blockSide ^ (F.top - 0)) ^ 4 ≤
        625 * (F.blockSide ^ (F.top - 0)) ^ 4 :=
      Nat.mul_le_mul_right _ (BlockWeights.card_cellsNearPoint_le S p)
    have h4 : (innerBonds (BlockWeights.cellsNearPoint S p) 0).card ≤
        4 * (625 * (F.blockSide ^ (F.top - 0)) ^ 4) :=
      h2.trans (Nat.mul_le_mul_left 4 h3)
    have h5 : ((innerBonds (BlockWeights.cellsNearPoint S p) 0).card : ℝ) ≤
        ((4 * (625 * (F.blockSide ^ (F.top - 0)) ^ 4) : ℕ) : ℝ) := by
      exact_mod_cast h4
    refine h5.trans (le_of_eq ?_)
    push_cast
    simp only [Nat.sub_zero]
    ring
  have h := norm_covariantCurlAt_transportedForm_le hodd hL2 hθ.le (by linarith) (referenceFieldChain S V)
    (fun x => (GaugeMap.frameChange S V (enclosingCell q.1) x)⁻¹) (by positivity) hR hcard f p hA0 hB0 hA hB hq
  refine h.trans (le_of_eq ?_)
  ring
end YangMills.Construction
end

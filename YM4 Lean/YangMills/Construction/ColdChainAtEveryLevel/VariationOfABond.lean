import YangMills.Construction.ColdChainAtEveryLevel.CriticalForAllVariationsProof
import YangMills.Construction.ColdChainAtEveryLevel.ColdnessOfTheFieldBelowTheTopProof
import YangMills.Construction.ColdChainAtEveryLevel.CurvesOfUnits
import YangMills.Construction.ColdChainAtEveryLevel.MeanOfTheContoursOfABondProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BondVariation
open LatticePaths BlockLines BondHull UnitCurves BlockAverages LatticeFractionalIntegration
variable {F : BlockFrame} {j : ℕ}
theorem add_stepDisplacement_add_endpoint (x : F.Site j) (st : PathStep) (l : List PathStep) :
    x + stepDisplacement j st + siteOfCoords j (endpoint 0 l) = x + siteOfCoords j (endpoint 0 (st :: l)) := by apply _root_.YangMills.Construction.BlockAverages.ContourMean.add_stepDisplacement_add_siteOfCoords <;> assumption
theorem pathHolonomy_reversePath (X : F.GaugeField j) (l : List PathStep) (x : F.Site j) :
    pathHolonomy X (x + siteOfCoords j (endpoint 0 l)) (reversePath l) = (pathHolonomy X x l)⁻¹ := by apply _root_.YangMills.Construction.BlockAverages.ContourMean.pathHolonomy_reversePath <;> assumption
theorem pathHolonomy_bondContour (hj : j + 1 ≤ F.top) (Y : F.GaugeField j) (y : F.Site (j + 1)) (i : Fin 4)
    (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    pathHolonomy Y (refineSite y) (bondContour F.blockSide h π i) =
      pathHolonomy Y (refineSite y) (axisPath h π) *
        pathHolonomy Y (refineSite y + siteOfCoords j h) (List.replicate F.blockSide (i, true)) *
        (pathHolonomy Y (refineSite (y + unitStep (j + 1) i)) (axisPath h π))⁻¹ := by apply _root_.YangMills.Construction.BlockAverages.ContourMean.pathHolonomy_bondContour <;> assumption
section Curves
variable {X : ℝ → F.GaugeField j} {dX : F.Site j → Fin 4 → ℍ[ℝ]}
def LinkCurves (X : ℝ → F.GaugeField j) (dX : F.Site j → Fin 4 → ℍ[ℝ]) (x₀ : F.Site j) (H : Set Lattice4)
    (M : ℝ) : Prop :=
  ∀ a ∈ H, ∀ k, a + basisVector k ∈ H →
    HasDerivAt (fun τ => ((X τ (x₀ + siteOfCoords j a) k : UnitQuaternion) : ℍ[ℝ])) (dX (x₀ + siteOfCoords j a) k) 0 ∧
    ‖dX (x₀ + siteOfCoords j a) k‖ ≤ M
private def starCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := star, map_add' := star_add, map_smul' := fun c q => by ext <;> simp }
theorem hasDerivAt_star_zero {f : ℝ → ℍ[ℝ]} {f' : ℍ[ℝ]} (h : HasDerivAt f f' 0) :
    HasDerivAt (fun τ => star (f τ)) (star f') 0 :=
  starCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
theorem hasDerivAt_pureComponent_zero {f : ℝ → ℍ[ℝ]} {f' : ℍ[ℝ]} (h : HasDerivAt f f' 0) :
    HasDerivAt (fun τ => pureComponent (f τ)) (pureComponent f') 0 := by
  unfold pureComponent
  exact (h.sub (hasDerivAt_star_zero h)).const_smul (1 / 2 : ℝ)
theorem exists_hasDerivAt_linkValue {x₀ : F.Site j} {H : Set Lattice4} {M : ℝ} (hcl : LinkCurves X dX x₀ H M)
    (u : Lattice4) (st : PathStep) (hu : u ∈ H) (hv : u + FlatPairing.stepDisplacement st ∈ H) :
    ∃ w : ℍ[ℝ], HasDerivAt (fun τ => ((linkValue (X τ) (x₀ + siteOfCoords j u) st : UnitQuaternion) : ℍ[ℝ])) w 0 ∧
      ‖w‖ ≤ M := by
  obtain ⟨k, b⟩ := st
  cases b
  · have hs : FlatPairing.stepDisplacement ((k, false) : PathStep) = - basisVector k := by
      simp [FlatPairing.stepDisplacement]
    rw [hs] at hv
    have hu' : (u + -basisVector k) + basisVector k ∈ H := by simpa using hu
    obtain ⟨h1, h2⟩ := hcl _ hv k hu'
    have e : x₀ + siteOfCoords j u - unitStep j k = x₀ + siteOfCoords j (u + -basisVector k) := by
      rw [siteOfCoords_add, unitStep_eq, ← add_assoc, sub_eq_add_neg]
      congr 1
      rw [show siteOfCoords (F := F) j (-basisVector k) = -siteOfCoords j (basisVector k) from by
        rw [siteOfCoords_neg]]
    refine ⟨star (dX (x₀ + siteOfCoords j (u + -basisVector k)) k), ?_, by rw [norm_star]; exact h2⟩
    have h3 := hasDerivAt_star_zero h1
    simp only [linkValue, Bool.false_eq_true, if_false]
    rw [e]
    exact h3
  · have hs : FlatPairing.stepDisplacement ((k, true) : PathStep) = basisVector k := by
      simp [FlatPairing.stepDisplacement]
    rw [hs] at hv
    obtain ⟨h1, h2⟩ := hcl _ hu k hv
    refine ⟨_, ?_, h2⟩
    simp only [linkValue, if_true]
    exact h1
theorem exists_hasDerivAt_pathHolonomy {x₀ : F.Site j} {H : Set Lattice4} {M : ℝ} (hM : 0 ≤ M)
    (hcl : LinkCurves X dX x₀ H M) :
    ∀ (l : List PathStep) (u : Lattice4), AllAlong (fun v => v ∈ H) u l →
      ∃ w : ℍ[ℝ], HasDerivAt (fun τ => ((pathHolonomy (X τ) (x₀ + siteOfCoords j u) l : UnitQuaternion) : ℍ[ℝ])) w 0 ∧
        ‖w‖ ≤ l.length * M := by
  intro l
  induction l with
  | nil =>
    intro u _
    exact ⟨0, hasDerivAt_const _ _, by simp⟩
  | cons st r ih =>
    intro u hp
    have hnext : x₀ + siteOfCoords j u + stepDisplacement j st =
        x₀ + siteOfCoords j (u + FlatPairing.stepDisplacement st) := by
      rw [BondHull.stepDisplacement_eq_siteOfCoords, add_assoc, ← siteOfCoords_add]
    obtain ⟨w1, h1, n1⟩ := exists_hasDerivAt_linkValue hcl u st hp.1 (allAlong_head hp.2)
    obtain ⟨w2, h2, n2⟩ := ih _ hp.2
    simp only [pathHolonomy]
    rw [hnext]
    refine ⟨_, h1.mul h2, ?_⟩
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, mul_one, one_mul]
    simp only [List.length_cons]
    push_cast
    linarith
theorem exists_hasDerivAt_linePathHolonomy {x₀ : F.Site j} {H : Set Lattice4} {M : ℝ}
    (hcl : LinkCurves X dX x₀ H M) (i : Fin 4) :
    ∀ (r : ℕ) (v : Lattice4), (∀ r' : ℕ, r' ≤ r → v + (r' : ℤ) • basisVector i ∈ H) →
      ∃ w : ℍ[ℝ], HasDerivAt (fun τ => ((pathHolonomy (X τ) (x₀ + siteOfCoords j v) (List.replicate r (i, true)) :
          UnitQuaternion) : ℍ[ℝ])) w 0 ∧
        ‖w‖ ≤ ∑ r' ∈ Finset.range r, ‖dX (x₀ + siteOfCoords j (v + (r' : ℤ) • basisVector i)) i‖ := by
  intro r
  induction r with
  | zero =>
    intro v _
    exact ⟨0, hasDerivAt_const _ _, by simp⟩
  | succ r ih =>
    intro v hv
    have hs : FlatPairing.stepDisplacement ((i, true) : PathStep) = basisVector i := by
      simp [FlatPairing.stepDisplacement]
    have hnext : x₀ + siteOfCoords j v + stepDisplacement j (i, true) = x₀ + siteOfCoords j (v + basisVector i) := by
      rw [BondHull.stepDisplacement_eq_siteOfCoords, add_assoc, ← siteOfCoords_add, hs]
    have h0 : v ∈ H := by simpa using hv 0 (Nat.zero_le _)
    have h1' : v + basisVector i ∈ H := by simpa using hv 1 (by omega)
    obtain ⟨h1, n1⟩ := hcl v h0 i h1'
    have e : ∀ r' : ℕ, v + basisVector i + (r' : ℤ) • basisVector i = v + ((r' + 1 : ℕ) : ℤ) • basisVector i := by
      intro r'
      push_cast
      rw [add_smul, one_smul]
      abel
    obtain ⟨w2, h2, n2⟩ := ih (v + basisVector i) fun r' hr' => by
      rw [e]
      exact hv _ (by omega)
    rw [List.replicate_succ]
    simp only [pathHolonomy, linkValue, if_true]
    have hnext2 : x₀ + siteOfCoords j v + unitStep j i = x₀ + siteOfCoords j (v + basisVector i) := by
      rw [← hnext]
      simp [stepDisplacement]
    have hnext3 : x₀ + siteOfCoords j v + stepDisplacement j (i, true) = x₀ + siteOfCoords j (v + basisVector i) :=
      hnext
    rw [hnext3]
    refine ⟨_, h1.mul h2, ?_⟩
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, mul_one, one_mul,
      Finset.sum_range_succ']
    simp only [e] at n2
    simp only [Nat.cast_zero, zero_smul, add_zero]
    linarith
theorem exists_hasDerivAt_balancedLegs (hodd : Odd F.blockSide) (Rr : F.GaugeField j) (y : F.Site (j + 1)) {M : ℝ}
    (hM : 0 ≤ M) (hcl : LinkCurves X dX (refineSite y) {v | v ∈ centredCube F.blockSide} M)
    (hm : 1 / 2 ≤ ‖relativePathAverage (X 0) Rr y‖) :
    ∃ db : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ],
      (∀ h ∈ centredCube F.blockSide, ∀ π, HasDerivAt (fun τ => ((balancingGauge (X τ) Rr y *
        (pathHolonomy (X τ) (refineSite y) (axisPath h π) *
          (pathHolonomy Rr (refineSite y) (axisPath h π))⁻¹) : UnitQuaternion) : ℍ[ℝ])) (db h π) 0 ∧
        ‖db h π‖ ≤ 6 * F.blockSide * M) ∧
      pureComponent (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), db h π) = 0 := by
  classical
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hleg : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4), ∃ w : ℍ[ℝ],
      HasDerivAt (fun τ => ((pathHolonomy (X τ) (refineSite y) (axisPath h π) : UnitQuaternion) : ℍ[ℝ])) w 0 ∧
        ‖w‖ ≤ 2 * F.blockSide * M := by
    intro h hh π
    obtain ⟨w, h1, h2⟩ := exists_hasDerivAt_pathHolonomy hM hcl (axisPath h π) 0 (allAlong_axisPath_centredCube hh π)
    rw [siteOfCoords_zero, add_zero] at h1
    exact ⟨w, h1, h2.trans (mul_le_mul_of_nonneg_right (length_axisPath_le hh π) hM)⟩
  choose! w hw1 hw2 using hleg
  set T : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π =>
    (((pathHolonomy Rr (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hT
  have hTn : ∀ h π, ‖T h π‖ = 1 := fun h π => norm_coe_unitQuaternion _
  have hl : ∀ h ∈ centredCube F.blockSide, ∀ π, HasDerivAt (fun τ => ((pathHolonomy (X τ) (refineSite y) (axisPath h π) *
      (pathHolonomy Rr (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ])) (w h π * T h π) 0 :=
    fun h hh π => (hw1 h hh π).mul_const _
  set dm : ℍ[ℝ] := (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
    ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), w h π * T h π with hdm
  have hmD : HasDerivAt (fun τ => relativePathAverage (X τ) Rr y) dm 0 := by
    have hs : HasDerivAt (fun τ => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy (X τ) (refineSite y) (axisPath h π) *
          (pathHolonomy Rr (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]))
        (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), w h π * T h π) 0 := by
      refine HasDerivAt.fun_sum fun h hh => ?_
      exact HasDerivAt.fun_sum fun π _ => hl h hh π
    exact hs.const_smul (1 / (24 * (F.blockSide : ℝ) ^ 4))
  have hdmn : ‖dm‖ ≤ 2 * F.blockSide * M := by
    refine norm_smul_sum_perm_le hodd _ _ fun h hh π => ?_
    rw [norm_mul, hTn, mul_one]
    exact hw2 h hh π
  have hm0 : relativePathAverage (X 0) Rr y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hm
    linarith
  obtain ⟨dZ, hZ, nZ⟩ := exists_hasDerivAt_normalize_le hmD hm0
  have hne : ∀ᶠ τ in nhds (0 : ℝ), relativePathAverage (X τ) Rr y ≠ 0 := hmD.continuousAt.eventually_ne hm0
  have hκ : HasDerivAt (fun τ => ((balancingGauge (X τ) Rr y : UnitQuaternion) : ℍ[ℝ])) (star dZ) 0 := by
    refine (hasDerivAt_star_zero hZ).congr_of_eventuallyEq ?_
    filter_upwards [hne] with τ hτ
    simp only [balancingGauge]
    rw [coe_unitQuaternion_inv, coe_polarUnit hτ]
  have hdZ : ‖dZ‖ ≤ 4 * F.blockSide * M := by
    refine nZ.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have h0 : 0 ≤ F.blockSide * M := by positivity
    nlinarith
  set db : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π =>
    star dZ * ((pathHolonomy (X 0) (refineSite y) (axisPath h π) *
      (pathHolonomy Rr (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
    ((balancingGauge (X 0) Rr y : UnitQuaternion) : ℍ[ℝ]) * (w h π * T h π) with hdb
  have hbc : ∀ h ∈ centredCube F.blockSide, ∀ π, HasDerivAt (fun τ => ((balancingGauge (X τ) Rr y *
      (pathHolonomy (X τ) (refineSite y) (axisPath h π) *
        (pathHolonomy Rr (refineSite y) (axisPath h π))⁻¹) : UnitQuaternion) : ℍ[ℝ])) (db h π) 0 :=
    fun h hh π => hκ.mul (hl h hh π)
  refine ⟨db, fun h hh π => ⟨hbc h hh π, ?_⟩, ?_⟩
  · simp only [hdb]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, hTn, norm_star, mul_one,
      mul_one, one_mul]
    have := hw2 h hh π
    linarith
  · have hsum : HasDerivAt (fun τ => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ((balancingGauge (X τ) Rr y * (pathHolonomy (X τ) (refineSite y) (axisPath h π) *
          (pathHolonomy Rr (refineSite y) (axisPath h π))⁻¹) : UnitQuaternion) : ℍ[ℝ]))
        (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), db h π) 0 := by
      refine HasDerivAt.fun_sum fun h hh => ?_
      exact HasDerivAt.fun_sum fun π _ => hbc h hh π
    have hp := hasDerivAt_pureComponent_zero hsum
    have hzero : (fun τ => pureComponent (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ((balancingGauge (X τ) Rr y * (pathHolonomy (X τ) (refineSite y) (axisPath h π) *
          (pathHolonomy Rr (refineSite y) (axisPath h π))⁻¹) : UnitQuaternion) : ℍ[ℝ]))) =ᶠ[nhds 0]
        fun _ => (0 : ℍ[ℝ]) := by
      filter_upwards [hne] with τ hτ
      have e1 : ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
          ((balancingGauge (X τ) Rr y * (pathHolonomy (X τ) (refineSite y) (axisPath h π) *
            (pathHolonomy Rr (refineSite y) (axisPath h π))⁻¹) : UnitQuaternion) : ℍ[ℝ]) =
          (24 * (F.blockSide : ℝ) ^ 4) •
            (((balancingGauge (X τ) Rr y : UnitQuaternion) : ℍ[ℝ]) * relativePathAverage (X τ) Rr y) := by
        unfold relativePathAverage
        rw [mul_smul_comm, smul_smul, mul_one_div_cancel (by positivity), one_smul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.mul_sum]
        rfl
      have e2 : ((balancingGauge (X τ) Rr y : UnitQuaternion) : ℍ[ℝ]) * relativePathAverage (X τ) Rr y =
          ((‖relativePathAverage (X τ) Rr y‖ : ℝ) : ℍ[ℝ]) := by
        simp only [balancingGauge]
        rw [coe_unitQuaternion_inv, coe_polarUnit hτ, quaternion_star_real_smul, smul_mul_assoc,
          Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self]
        have hn : ‖relativePathAverage (X τ) Rr y‖ ≠ 0 := norm_ne_zero_iff.2 hτ
        have hs : ∀ r t : ℝ, r • (t : ℍ[ℝ]) = ((r * t : ℝ) : ℍ[ℝ]) := fun r t => by
          ext <;> simp
        rw [hs]
        congr 1
        field_simp
      rw [e1, e2, pureComponent_smul, pureComponent_coe, smul_zero]
    exact (hp.congr_of_eventuallyEq hzero.symm).unique (hasDerivAt_const _ _) |>.trans rfl
def balancedLeg (Y Rr : F.GaugeField j) (y : F.Site (j + 1)) (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    UnitQuaternion :=
  balancingGauge Y Rr y * (pathHolonomy Y (refineSite y) (axisPath h π) *
    (pathHolonomy Rr (refineSite y) (axisPath h π))⁻¹)
def framedLine (Y Rr : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    UnitQuaternion :=
  pathHolonomy Rr (refineSite c.1) (axisPath h π) *
    pathHolonomy Y (refineSite c.1 + siteOfCoords j h) (List.replicate F.blockSide (c.2, true)) *
    (pathHolonomy Rr (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath h π))⁻¹
def framedContour (Y Rr : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    UnitQuaternion :=
  balancedLeg Y Rr c.1 h π * framedLine Y Rr c h π * (balancedLeg Y Rr (c.1 + unitStep (j + 1) c.2) h π)⁻¹
theorem gaugedContourAverage_balancingGauge_eq (hj : j < F.top) (Y Rr : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) :
    gaugedContourAverage Y (balancingGauge Y Rr) c = (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
      ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ((framedContour Y Rr c h π : UnitQuaternion) : ℍ[ℝ]) := by
  unfold gaugedContourAverage contourAverage
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun π _ => ?_
  have e : balancingGauge Y Rr c.1 * pathHolonomy Y (refineSite c.1) (bondContour F.blockSide h π c.2) *
      (balancingGauge Y Rr (c.1 + unitStep (j + 1) c.2))⁻¹ = framedContour Y Rr c h π := by
    rw [pathHolonomy_bondContour (by omega)]
    simp only [framedContour, balancedLeg, framedLine]
    group
  rw [← e]
  rfl
theorem mem_twoBlockHull_of_mem_centredCube {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (i : Fin 4) :
    h ∈ FlatPairing.twoBlockHull L i := by apply _root_.YangMills.Construction.BlockAverages.ColdBelowTop.mem_twoBlockHull_of_mem_centredCube <;> assumption
theorem shift_mem_twoBlockHull_of_mem_centredCube {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (i : Fin 4) :
    (L : ℤ) • basisVector i + h ∈ FlatPairing.twoBlockHull L i := by apply _root_.YangMills.Construction.BlockAverages.ColdBelowTop.smul_basisVector_add_mem_twoBlockHull <;> assumption
theorem linkCurves_centredCube {c : F.Site (j + 1) × Fin 4} {M : ℝ}
    (hcl : LinkCurves X dX (refineSite c.1) {v | v ∈ FlatPairing.twoBlockHull F.blockSide c.2} M) :
    LinkCurves X dX (refineSite c.1) {v | v ∈ centredCube F.blockSide} M :=
  fun a ha k hk => hcl a (mem_twoBlockHull_of_mem_centredCube ha c.2) k (mem_twoBlockHull_of_mem_centredCube hk c.2)
theorem linkCurves_centredCube_next (hj : j < F.top) {c : F.Site (j + 1) × Fin 4} {M : ℝ}
    (hcl : LinkCurves X dX (refineSite c.1) {v | v ∈ FlatPairing.twoBlockHull F.blockSide c.2} M) :
    LinkCurves X dX (refineSite (c.1 + unitStep (j + 1) c.2)) {v | v ∈ centredCube F.blockSide} M := by
  intro a ha k hk
  have e : refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j a =
      refineSite c.1 + siteOfCoords j ((F.blockSide : ℤ) • basisVector c.2 + a) := by
    rw [refineSite_add_unitStep hj, add_assoc, ← siteOfCoords_add]
  rw [e]
  refine hcl _ (shift_mem_twoBlockHull_of_mem_centredCube ha c.2) k ?_
  rw [add_assoc]
  exact shift_mem_twoBlockHull_of_mem_centredCube hk c.2
theorem exists_hasDerivAt_gaugedContourAverage (hodd : Odd F.blockSide) (hj : j < F.top) (Rr : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) {M ε : ℝ} {u : ℍ[ℝ]} (hM : 0 ≤ M) (hε0 : 0 ≤ ε) (hu : ‖u‖ = 1)
    (hcl : LinkCurves X dX (refineSite c.1) {v | v ∈ FlatPairing.twoBlockHull F.blockSide c.2} M)
    (hm : 1 / 2 ≤ ‖relativePathAverage (X 0) Rr c.1‖)
    (hm' : 1 / 2 ≤ ‖relativePathAverage (X 0) Rr (c.1 + unitStep (j + 1) c.2)‖)
    (hb : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖((balancedLeg (X 0) Rr c.1 h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (hb' : ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖((balancedLeg (X 0) Rr (c.1 + unitStep (j + 1) c.2) h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (hP : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖((framedContour (X 0) Rr c h π : UnitQuaternion) : ℍ[ℝ]) - u‖ ≤ ε) :
    ∃ dY : ℍ[ℝ], HasDerivAt (fun τ => gaugedContourAverage (X τ) (balancingGauge (X τ) Rr) c) dY 0 ∧
      ‖dY‖ ≤ lineBlockAverage (fun x i => ‖dX x i‖) c + 24 * ε * F.blockSide * M ∧
      ∀ (v : ℍ[ℝ]) (e : ℝ), (∀ h ∈ centredCube F.blockSide, ∀ π,
          ‖v - ((framedContour (X 0) Rr c h π : UnitQuaternion) : ℍ[ℝ])‖ ≤ e) →
        |inner ℝ v dY| ≤ e * (13 * F.blockSide * M) := by
  classical
  have hLpos := hodd.pos
  obtain ⟨db, hdb, hbs⟩ := exists_hasDerivAt_balancedLegs hodd Rr c.1 hM (linkCurves_centredCube hcl) hm
  obtain ⟨dc, hdc, hcs⟩ := exists_hasDerivAt_balancedLegs hodd Rr (c.1 + unitStep (j + 1) c.2) hM
    (linkCurves_centredCube_next hj hcl) hm'
  have hline : ∀ h ∈ centredCube F.blockSide, ∃ w : ℍ[ℝ], HasDerivAt (fun τ => ((pathHolonomy (X τ)
      (refineSite c.1 + siteOfCoords j h) (List.replicate F.blockSide (c.2, true)) : UnitQuaternion) : ℍ[ℝ])) w 0 ∧
      ‖w‖ ≤ ∑ r ∈ Finset.range F.blockSide, ‖dX (lineBond c h r).1 (lineBond c h r).2‖ := by
    intro h hh
    obtain ⟨w, h1, h2⟩ := exists_hasDerivAt_linePathHolonomy hcl c.2 F.blockSide h fun r' hr' =>
      add_smul_basisVector_mem_twoBlockHull hh c.2 hr'
    refine ⟨w, h1, h2.trans (le_of_eq (Finset.sum_congr rfl fun r _ => ?_))⟩
    show ‖dX _ c.2‖ = ‖dX (lineBond c h r).1 c.2‖
    rw [lineBond_fst]
  choose! wl hwl1 hwl2 using hline
  have hsumM : ∀ h ∈ centredCube F.blockSide,
      ∑ r ∈ Finset.range F.blockSide, ‖dX (lineBond c h r).1 (lineBond c h r).2‖ ≤ F.blockSide * M := by
    intro h hh
    have h1 : ∀ r ∈ Finset.range F.blockSide, ‖dX (lineBond c h r).1 (lineBond c h r).2‖ ≤ M := by
      intro r hr
      have hr' := Finset.mem_range.1 hr
      have h2 := (hcl _ (add_smul_basisVector_mem_twoBlockHull hh c.2 hr'.le) c.2 ?_).2
      · show ‖dX (lineBond c h r).1 c.2‖ ≤ M
        rw [lineBond_fst]
        exact h2
      · have e2 : h + (r : ℤ) • basisVector c.2 + basisVector c.2 = h + ((r + 1 : ℕ) : ℤ) • basisVector c.2 := by
          push_cast
          rw [add_smul, one_smul]
          abel
        show h + (r : ℤ) • basisVector c.2 + basisVector c.2 ∈ FlatPairing.twoBlockHull F.blockSide c.2
        rw [e2]
        exact add_smul_basisVector_mem_twoBlockHull hh c.2 hr'
    refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
    simp
  set A : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π =>
    ((pathHolonomy Rr (refineSite c.1) (axisPath h π) : UnitQuaternion) : ℍ[ℝ]) with hA
  set B : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π =>
    (((pathHolonomy Rr (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hB
  set dW : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π => A h π * wl h * B h π with hdW
  have hWc : ∀ h ∈ centredCube F.blockSide, ∀ π,
      HasDerivAt (fun τ => ((framedLine (X τ) Rr c h π : UnitQuaternion) : ℍ[ℝ])) (dW h π) 0 :=
    fun h hh π => ((hwl1 h hh).const_mul _).mul_const _
  have hdWn : ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖dW h π‖ ≤ ∑ r ∈ Finset.range F.blockSide, ‖dX (lineBond c h r).1 (lineBond c h r).2‖ := by
    intro h hh π
    simp only [hdW, hA, hB]
    rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
    exact hwl2 h hh
  set dP : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π =>
    db h π * ((framedLine (X 0) Rr c h π : UnitQuaternion) : ℍ[ℝ]) *
      star ((balancedLeg (X 0) Rr (c.1 + unitStep (j + 1) c.2) h π : UnitQuaternion) : ℍ[ℝ]) +
    ((balancedLeg (X 0) Rr c.1 h π : UnitQuaternion) : ℍ[ℝ]) * dW h π *
      star ((balancedLeg (X 0) Rr (c.1 + unitStep (j + 1) c.2) h π : UnitQuaternion) : ℍ[ℝ]) +
    ((balancedLeg (X 0) Rr c.1 h π : UnitQuaternion) : ℍ[ℝ]) * ((framedLine (X 0) Rr c h π : UnitQuaternion) : ℍ[ℝ]) *
      star (dc h π) with hdP
  have hPc : ∀ h ∈ centredCube F.blockSide, ∀ π,
      HasDerivAt (fun τ => ((framedContour (X τ) Rr c h π : UnitQuaternion) : ℍ[ℝ])) (dP h π) 0 := by
    intro h hh π
    have h1 := ((hdb h hh π).1.mul (hWc h hh π)).mul (hasDerivAt_star_zero (hdc h hh π).1)
    have e : (fun τ => ((framedContour (X τ) Rr c h π : UnitQuaternion) : ℍ[ℝ])) =
        fun τ => ((balancedLeg (X τ) Rr c.1 h π : UnitQuaternion) : ℍ[ℝ]) *
          ((framedLine (X τ) Rr c h π : UnitQuaternion) : ℍ[ℝ]) *
          star ((balancedLeg (X τ) Rr (c.1 + unitStep (j + 1) c.2) h π : UnitQuaternion) : ℍ[ℝ]) := rfl
    rw [e]
    have e2 : dP h π = (db h π * ((framedLine (X 0) Rr c h π : UnitQuaternion) : ℍ[ℝ]) +
          ((balancedLeg (X 0) Rr c.1 h π : UnitQuaternion) : ℍ[ℝ]) * dW h π) *
        star ((balancedLeg (X 0) Rr (c.1 + unitStep (j + 1) c.2) h π : UnitQuaternion) : ℍ[ℝ]) +
        ((balancedLeg (X 0) Rr c.1 h π : UnitQuaternion) : ℍ[ℝ]) *
          ((framedLine (X 0) Rr c h π : UnitQuaternion) : ℍ[ℝ]) * star (dc h π) := by
      simp only [hdP, add_mul]
    rw [e2]
    exact h1
  set n : ℝ := 24 * (F.blockSide : ℝ) ^ 4 with hn
  have hn0 : 0 < n := by positivity
  set dY : ℍ[ℝ] := (1 / n) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), dP h π with hdY
  have hY : HasDerivAt (fun τ => gaugedContourAverage (X τ) (balancingGauge (X τ) Rr) c) dY 0 := by
    have hs : HasDerivAt (fun τ => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ((framedContour (X τ) Rr c h π : UnitQuaternion) : ℍ[ℝ]))
        (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), dP h π) 0 := by
      refine HasDerivAt.fun_sum fun h hh => ?_
      exact HasDerivAt.fun_sum fun π _ => hPc h hh π
    have e : (fun τ => gaugedContourAverage (X τ) (balancingGauge (X τ) Rr) c) =
        fun τ => (1 / n) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
          ((framedContour (X τ) Rr c h π : UnitQuaternion) : ℍ[ℝ]) := by
      funext τ
      exact gaugedContourAverage_balancingGauge_eq hj (X τ) Rr c
    rw [e]
    exact hs.const_smul (1 / n)
  set I : Finset (Lattice4 × Equiv.Perm (Fin 4)) := centredCube F.blockSide ×ˢ Finset.univ with hI
  have hIm : ∀ k ∈ I, k.1 ∈ centredCube F.blockSide := fun k hk => (Finset.mem_product.1 hk).1
  have hcardI : (I.card : ℝ) = n := by
    rw [hI, Finset.card_product, card_centredCube hodd, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, hn]
    simp [Nat.factorial]
    ring
  have hsumI : ∀ g : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ],
      ∑ k ∈ I, g k.1 k.2 = ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), g h π :=
    fun g => Finset.sum_product _ _ _
  have hsumR : ∀ g : Lattice4 → Equiv.Perm (Fin 4) → ℝ,
      ∑ k ∈ I, g k.1 k.2 = ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), g h π :=
    fun g => Finset.sum_product _ _ _
  have hbperp : ∀ k ∈ I, inner ℝ ((balancedLeg (X 0) Rr c.1 k.1 k.2 : UnitQuaternion) : ℍ[ℝ]) (db k.1 k.2) = 0 :=
    fun k hk => inner_deriv_eq_zero_of_norm_eq_one (hdb k.1 (hIm k hk) k.2).1 fun _ => norm_coe_unitQuaternion _
  have hcperp : ∀ k ∈ I, inner ℝ ((balancedLeg (X 0) Rr (c.1 + unitStep (j + 1) c.2) k.1 k.2 : UnitQuaternion) : ℍ[ℝ])
      (dc k.1 k.2) = 0 :=
    fun k hk => inner_deriv_eq_zero_of_norm_eq_one (hdc k.1 (hIm k hk) k.2).1 fun _ => norm_coe_unitQuaternion _
  have hmain := norm_sum_deriv_triple_product_le I
    (fun k => ((balancedLeg (X 0) Rr c.1 k.1 k.2 : UnitQuaternion) : ℍ[ℝ])) (fun k => db k.1 k.2)
    (fun k => ((framedLine (X 0) Rr c k.1 k.2 : UnitQuaternion) : ℍ[ℝ])) (fun k => dW k.1 k.2)
    (fun k => ((balancedLeg (X 0) Rr (c.1 + unitStep (j + 1) c.2) k.1 k.2 : UnitQuaternion) : ℍ[ℝ]))
    (fun k => dc k.1 k.2) u hu
    (fun _ _ => norm_coe_unitQuaternion _) (fun _ _ => norm_coe_unitQuaternion _)
    (fun _ _ => norm_coe_unitQuaternion _) hbperp hcperp
    (by rw [hsumI]; exact hbs) (by rw [hsumI]; exact hcs) hε0
    (fun k hk => hb k.1 (hIm k hk) k.2) (fun k hk => hb' k.1 (hIm k hk) k.2)
    (fun k hk => hP k.1 (hIm k hk) k.2)
  have hdbS : ∑ k ∈ I, ‖db k.1 k.2‖ ≤ n * (6 * F.blockSide * M) := by
    refine (Finset.sum_le_sum fun k hk => (hdb k.1 (hIm k hk) k.2).2).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hcardI]
  have hdcS : ∑ k ∈ I, ‖dc k.1 k.2‖ ≤ n * (6 * F.blockSide * M) := by
    refine (Finset.sum_le_sum fun k hk => (hdc k.1 (hIm k hk) k.2).2).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hcardI]
  have hdWS : ∑ k ∈ I, ‖dW k.1 k.2‖ ≤ n * lineBlockAverage (fun x i => ‖dX x i‖) c := by
    have h1 : ∑ k ∈ I, ‖dW k.1 k.2‖ ≤ ∑ h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4),
        ∑ r ∈ Finset.range F.blockSide, ‖dX (lineBond c h r).1 (lineBond c h r).2‖ := by
      rw [← hsumR (fun h _ => ∑ r ∈ Finset.range F.blockSide, ‖dX (lineBond c h r).1 (lineBond c h r).2‖)]
      exact Finset.sum_le_sum fun k hk => hdWn k.1 (hIm k hk) k.2
    refine h1.trans (le_of_eq ?_)
    rw [lineBlockAverage_eq, hn]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    simp [Nat.factorial]
    field_simp
  have hexp : ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), dP h π = ∑ k ∈ I,
      (db k.1 k.2 * ((framedLine (X 0) Rr c k.1 k.2 : UnitQuaternion) : ℍ[ℝ]) *
          star ((balancedLeg (X 0) Rr (c.1 + unitStep (j + 1) c.2) k.1 k.2 : UnitQuaternion) : ℍ[ℝ]) +
        ((balancedLeg (X 0) Rr c.1 k.1 k.2 : UnitQuaternion) : ℍ[ℝ]) * dW k.1 k.2 *
          star ((balancedLeg (X 0) Rr (c.1 + unitStep (j + 1) c.2) k.1 k.2 : UnitQuaternion) : ℍ[ℝ]) +
        ((balancedLeg (X 0) Rr c.1 k.1 k.2 : UnitQuaternion) : ℍ[ℝ]) *
          ((framedLine (X 0) Rr c k.1 k.2 : UnitQuaternion) : ℍ[ℝ]) * star (dc k.1 k.2)) :=
    (hsumI dP).symm
  refine ⟨dY, hY, ?_, ?_⟩
  · rw [hdY, norm_smul, Real.norm_of_nonneg (by positivity), hexp]
    have h1 := mul_le_mul_of_nonneg_left hmain (by positivity : (0 : ℝ) ≤ 1 / n)
    refine h1.trans ?_
    have h2 : ∑ k ∈ I, ‖dW k.1 k.2‖ + 2 * ε * (∑ k ∈ I, ‖db k.1 k.2‖ + ∑ k ∈ I, ‖dc k.1 k.2‖) ≤
        n * lineBlockAverage (fun x i => ‖dX x i‖) c +
          2 * ε * (n * (6 * F.blockSide * M) + n * (6 * F.blockSide * M)) :=
      add_le_add hdWS (mul_le_mul_of_nonneg_left (add_le_add hdbS hdcS) (by positivity))
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 / n)
    refine h3.trans (le_of_eq ?_)
    field_simp
    ring
  · intro v e hv
    have hperp : ∀ k ∈ I, inner ℝ ((framedContour (X 0) Rr c k.1 k.2 : UnitQuaternion) : ℍ[ℝ]) (dP k.1 k.2) = 0 :=
      fun k hk => inner_deriv_eq_zero_of_norm_eq_one (hPc k.1 (hIm k hk) k.2) fun _ => norm_coe_unitQuaternion _
    have h1 := abs_inner_sum_deriv_le I (fun k => ((framedContour (X 0) Rr c k.1 k.2 : UnitQuaternion) : ℍ[ℝ]))
      (fun k => dP k.1 k.2) v hperp (fun k hk => hv k.1 (hIm k hk) k.2)
    have he0 : 0 ≤ e := by
      obtain ⟨h0, hh0⟩ : ∃ h, h ∈ centredCube F.blockSide := ⟨0, (mem_centredCube_iff _ _).2 fun i => by
        have : (0 : ℤ) ≤ ((F.blockSide : ℤ) - 1) / 2 := by omega
        simp only [Pi.zero_apply]
        omega⟩
      exact (norm_nonneg _).trans (hv h0 hh0 1)
    have hPn : ∀ k ∈ I, ‖dP k.1 k.2‖ ≤ 13 * F.blockSide * M := by
      intro k hk
      have hk1 := hIm k hk
      simp only [hdP]
      refine (norm_add_le _ _).trans ?_
      have t1 := norm_add_le (db k.1 k.2 * ((framedLine (X 0) Rr c k.1 k.2 : UnitQuaternion) : ℍ[ℝ]) *
          star ((balancedLeg (X 0) Rr (c.1 + unitStep (j + 1) c.2) k.1 k.2 : UnitQuaternion) : ℍ[ℝ]))
        (((balancedLeg (X 0) Rr c.1 k.1 k.2 : UnitQuaternion) : ℍ[ℝ]) * dW k.1 k.2 *
          star ((balancedLeg (X 0) Rr (c.1 + unitStep (j + 1) c.2) k.1 k.2 : UnitQuaternion) : ℍ[ℝ]))
      have e1 : ‖db k.1 k.2 * ((framedLine (X 0) Rr c k.1 k.2 : UnitQuaternion) : ℍ[ℝ]) *
          star ((balancedLeg (X 0) Rr (c.1 + unitStep (j + 1) c.2) k.1 k.2 : UnitQuaternion) : ℍ[ℝ])‖ =
          ‖db k.1 k.2‖ := by
        rw [norm_mul, norm_mul, norm_star, norm_coe_unitQuaternion, norm_coe_unitQuaternion, mul_one, mul_one]
      have e2 : ‖((balancedLeg (X 0) Rr c.1 k.1 k.2 : UnitQuaternion) : ℍ[ℝ]) * dW k.1 k.2 *
          star ((balancedLeg (X 0) Rr (c.1 + unitStep (j + 1) c.2) k.1 k.2 : UnitQuaternion) : ℍ[ℝ])‖ =
          ‖dW k.1 k.2‖ := by
        rw [norm_mul, norm_mul, norm_star, norm_coe_unitQuaternion, norm_coe_unitQuaternion, mul_one, one_mul]
      have e3 : ‖((balancedLeg (X 0) Rr c.1 k.1 k.2 : UnitQuaternion) : ℍ[ℝ]) *
          ((framedLine (X 0) Rr c k.1 k.2 : UnitQuaternion) : ℍ[ℝ]) * star (dc k.1 k.2)‖ = ‖dc k.1 k.2‖ := by
        rw [norm_mul, norm_mul, norm_star, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, one_mul]
      have a1 := (hdb k.1 hk1 k.2).2
      have a2 := (hdc k.1 hk1 k.2).2
      have a3 := (hdWn k.1 hk1 k.2).trans (hsumM k.1 hk1)
      rw [e1, e2] at t1
      rw [e3]
      linarith
    have hS : ∑ k ∈ I, ‖dP k.1 k.2‖ ≤ n * (13 * F.blockSide * M) := by
      refine (Finset.sum_le_sum hPn).trans (le_of_eq ?_)
      rw [Finset.sum_const, nsmul_eq_mul, hcardI]
    rw [hdY, inner_smul_right, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / n), ← hsumI dP]
    have h2 := mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hS he0))
      (by positivity : (0 : ℝ) ≤ 1 / n)
    refine h2.trans (le_of_eq ?_)
    field_simp
end Curves
theorem norm_coe_sub_coe_eq_distFromOne (a v : UnitQuaternion) :
    ‖(a : ℍ[ℝ]) - (v : ℍ[ℝ])‖ = distFromOne (a * v⁻¹) := by apply _root_.YangMills.Construction.GaugedCriticality.norm_coe_sub_coe <;> assumption
theorem bond_estimates_of_near (hodd : Odd F.blockSide) (hj : j < F.top) (X Rr : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) {t ρ : ℝ} (v : UnitQuaternion) (ht0 : 0 ≤ t) (ht : 2 * F.blockSide * t ≤ 1 / 4)
    (hcl : ∀ a ∈ FlatPairing.twoBlockHull F.blockSide c.2, ∀ k,
      a + basisVector k ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      distFromOne (X (refineSite c.1 + siteOfCoords j a) k * (Rr (refineSite c.1 + siteOfCoords j a) k)⁻¹) ≤ t)
    (hρ : ∀ h ∈ centredCube F.blockSide, ∀ π,
      distFromOne (pathHolonomy Rr (refineSite c.1) (bondContour F.blockSide h π c.2) * v⁻¹) ≤ ρ) :
    1 / 2 ≤ ‖relativePathAverage X Rr c.1‖ ∧ 1 / 2 ≤ ‖relativePathAverage X Rr (c.1 + unitStep (j + 1) c.2)‖ ∧
      (∀ h ∈ centredCube F.blockSide, ∀ π,
        ‖((balancedLeg X Rr c.1 h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 8 * F.blockSide * t) ∧
      (∀ h ∈ centredCube F.blockSide, ∀ π,
        ‖((balancedLeg X Rr (c.1 + unitStep (j + 1) c.2) h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 8 * F.blockSide * t) ∧
      ∀ h ∈ centredCube F.blockSide, ∀ π,
        ‖((framedContour X Rr c h π : UnitQuaternion) : ℍ[ℝ]) - (v : ℍ[ℝ])‖ ≤ 17 * F.blockSide * t + ρ := by
  have hLpos := hodd.pos
  have hc1 : ∀ a ∈ centredCube F.blockSide, ∀ k, a + basisVector k ∈ centredCube F.blockSide →
      distFromOne (X (refineSite c.1 + siteOfCoords j a) k * (Rr (refineSite c.1 + siteOfCoords j a) k)⁻¹) ≤ t :=
    fun a ha k hk => hcl a (mem_twoBlockHull_of_mem_centredCube ha c.2) k (mem_twoBlockHull_of_mem_centredCube hk c.2)
  have hc2 : ∀ a ∈ centredCube F.blockSide, ∀ k, a + basisVector k ∈ centredCube F.blockSide →
      distFromOne (X (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j a) k *
        (Rr (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j a) k)⁻¹) ≤ t := by
    intro a ha k hk
    have e : refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j a =
        refineSite c.1 + siteOfCoords j ((F.blockSide : ℤ) • basisVector c.2 + a) := by
      rw [refineSite_add_unitStep hj, add_assoc, ← siteOfCoords_add]
    rw [e]
    refine hcl _ (shift_mem_twoBlockHull_of_mem_centredCube ha c.2) k ?_
    rw [add_assoc]
    exact shift_mem_twoBlockHull_of_mem_centredCube hk c.2
  have hnorm : ∀ y : F.Site (j + 1), (∀ a ∈ centredCube F.blockSide, ∀ k, a + basisVector k ∈ centredCube F.blockSide →
      distFromOne (X (refineSite y + siteOfCoords j a) k * (Rr (refineSite y + siteOfCoords j a) k)⁻¹) ≤ t) →
      1 / 2 ≤ ‖relativePathAverage X Rr y‖ := by
    intro y hy
    have h1 := norm_relativePathAverage_sub_one_le hodd X Rr y t ht0 hy
    have h2 := norm_sub_norm_le (1 : ℍ[ℝ]) (relativePathAverage X Rr y)
    rw [norm_one, norm_sub_rev] at h2
    linarith
  have hend : ∀ y : F.Site (j + 1), (∀ a ∈ centredCube F.blockSide, ∀ k, a + basisVector k ∈ centredCube F.blockSide →
      distFromOne (X (refineSite y + siteOfCoords j a) k * (Rr (refineSite y + siteOfCoords j a) k)⁻¹) ≤ t) →
      ∀ h ∈ centredCube F.blockSide, ∀ π, distFromOne (balancedLeg X Rr y h π) ≤ 8 * F.blockSide * t := by
    intro y hy h hh π
    have h1 := distFromOne_balancingGauge_le hodd X Rr y t ht0 ht hy
    have h2 := distFromOne_pathRatio_le X Rr (refineSite y) (fun v => v ∈ centredCube F.blockSide) t ht0
      (distFromOne_linkRatio_le X Rr (refineSite y) {v | v ∈ centredCube F.blockSide} t hy) (axisPath h π) 0
      (allAlong_axisPath_centredCube hh π)
    rw [siteOfCoords_zero, add_zero] at h2
    have h3 : ((axisPath h π).length : ℝ) * t ≤ 2 * F.blockSide * t :=
      mul_le_mul_of_nonneg_right (length_axisPath_le hh π) ht0
    have h4 := distFromOne_mul_le (balancingGauge X Rr y) (pathRatio X Rr (refineSite y) (axisPath h π))
    have e : balancedLeg X Rr y h π = balancingGauge X Rr y * pathRatio X Rr (refineSite y) (axisPath h π) := rfl
    rw [e]
    linarith
  have e1 := hend c.1 hc1
  have e2 := hend (c.1 + unitStep (j + 1) c.2) hc2
  refine ⟨hnorm _ hc1, hnorm _ hc2, e1, e2, fun h hh π => ?_⟩
  rw [norm_coe_sub_coe_eq_distFromOne]
  set T := pathHolonomy Rr (refineSite c.1) (axisPath h π) with hT
  set T' := pathHolonomy Rr (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath h π) with hT'
  set B := pathHolonomy X (refineSite c.1 + siteOfCoords j h) (List.replicate F.blockSide (c.2, true)) with hB
  set Br := pathHolonomy Rr (refineSite c.1 + siteOfCoords j h) (List.replicate F.blockSide (c.2, true)) with hBr
  set a := balancedLeg X Rr c.1 h π with ha
  set a' := balancedLeg X Rr (c.1 + unitStep (j + 1) c.2) h π with ha'
  have hsplit : pathHolonomy Rr (refineSite c.1) (bondContour F.blockSide h π c.2) = T * Br * T'⁻¹ :=
    pathHolonomy_bondContour (by omega) Rr c.1 c.2 h π
  set G := pathHolonomy Rr (refineSite c.1) (bondContour F.blockSide h π c.2) with hG
  have hline : distFromOne (B * Br⁻¹) ≤ F.blockSide * t := by
    have h1 := distFromOne_pathRatio_le X Rr (refineSite c.1) (fun v => v ∈ FlatPairing.twoBlockHull F.blockSide c.2)
      t ht0 (distFromOne_linkRatio_le X Rr (refineSite c.1) {v | v ∈ FlatPairing.twoBlockHull F.blockSide c.2} t hcl)
      (List.replicate F.blockSide (c.2, true)) h
      (allAlong_replicate fun k hk => by
        have : FlatPairing.stepDisplacement ((c.2, true) : PathStep) = basisVector c.2 := by
          simp [FlatPairing.stepDisplacement]
        rw [this]
        exact add_smul_basisVector_mem_twoBlockHull hh c.2 hk)
    simpa [pathRatio] using h1
  have hcon : framedContour X Rr c h π * v⁻¹ =
      a * (T * (B * Br⁻¹) * T⁻¹) * (G * a'⁻¹ * G⁻¹) * (G * v⁻¹) := by
    have e : framedContour X Rr c h π = a * (T * B * T'⁻¹) * a'⁻¹ := rfl
    rw [e, hsplit]
    group
  rw [hcon]
  have s1 := distFromOne_mul_le (a * (T * (B * Br⁻¹) * T⁻¹) * (G * a'⁻¹ * G⁻¹)) (G * v⁻¹)
  have s2 := distFromOne_mul_le (a * (T * (B * Br⁻¹) * T⁻¹)) (G * a'⁻¹ * G⁻¹)
  have s3 := distFromOne_mul_le a (T * (B * Br⁻¹) * T⁻¹)
  rw [distFromOne_conj] at s2 s3
  rw [distFromOne_inv] at s2
  have s4 := e1 h hh π
  have s5 := e2 h hh π
  have s6 := hρ h hh π
  linarith
end YangMills.Construction.BondVariation
end

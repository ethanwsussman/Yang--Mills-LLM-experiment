import YangMills.Construction.ColdChainAtEveryLevel.DifferencesAreNearlyFlatProof
import YangMills.Construction.RunningCouplingSlope.LeastPointsOverAFieldAreOneOrbitProof
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.Lattice.EndPointsAndOrientationOfABondProof
import YangMills.Construction.QuaternionicWilsonModel.TheQuaternionModelIsSUTwoWithWilsonsWeightProof
import YangMills.Construction.RunningCouplingSlope.PlainMeanReadsAnyFrame
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages TorusFields
namespace ContourMean
section Sites
variable {L n : ℕ}
private def latticeSite (d : ℤ) (z : Fin 4 → ℤ) : PeriodicLattice.Site L n d := PeriodicLattice.offsetSite 0 z
private theorem sum_single_zsmul {A : Type*} [AddCommGroup A] (f : Fin 4 → A) (μ : Fin 4) (c : ℤ) :
    ∑ ν, (Pi.single μ c : Fin 4 → ℤ) ν • f ν = c • f μ := by
  rw [Finset.sum_eq_single μ]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp
private theorem latticeSite_add (d : ℤ) (z w : Fin 4 → ℤ) : latticeSite (L := L) (n := n) d (z + w) =
    latticeSite d z + ∑ ν, w ν • PeriodicLattice.unitStep L n d ν := by
  simp [latticeSite, PeriodicLattice.offsetSite, add_smul, Finset.sum_add_distrib]
private theorem latticeSite_add_single (d : ℤ) (z : Fin 4 → ℤ) (μ : Fin 4) (c : ℤ) :
    latticeSite (L := L) (n := n) d (z + Pi.single μ c) = latticeSite d z + c • PeriodicLattice.unitStep L n d μ := by
  rw [latticeSite_add, sum_single_zsmul]
private theorem coe_latticeSite (d : ℤ) (z : Fin 4 → ℤ) (ν : Fin 4) :
    ((latticeSite (L := L) (n := n) d z : PeriodicLattice.Site L n d) : PeriodicLattice.FourTorus L n) ν =
      (((z ν : ℝ) * PeriodicLattice.meshSize L d : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
  have h1 : ((latticeSite (L := L) (n := n) d z : PeriodicLattice.Site L n d) : PeriodicLattice.FourTorus L n) =
      ∑ μ, z μ • PeriodicLattice.pointOnAxis L n μ (PeriodicLattice.meshSize L d) := by
    show (PeriodicLattice.sublattice L n d).subtype (latticeSite d z) = _
    simp only [latticeSite, PeriodicLattice.offsetSite, zero_add]
    rw [map_sum]
    exact Finset.sum_congr rfl fun μ _ => map_zsmul _ _ _
  rw [h1, Finset.sum_apply, Finset.sum_eq_single ν]
  · simp only [Pi.smul_apply, PeriodicLattice.pointOnAxis, Pi.single_eq_same]
    rw [← zsmul_eq_mul]
    exact (QuotientAddGroup.mk_zsmul _ _ _).symm
  · intro b _ hb
    simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hb.symm]
  · simp
end Sites
section Paths
variable {L n : ℕ}
private def stepVector (st : PathStep) : Fin 4 → ℤ :=
  if st.2 then Pi.single st.1 1 else -Pi.single st.1 1
private def pathDisplacement : List PathStep → Fin 4 → ℤ
  | [] => 0
  | st :: r => stepVector st + pathDisplacement r
private theorem pathDisplacement_append (p q : List PathStep) :
    pathDisplacement (p ++ q) = pathDisplacement p + pathDisplacement q := by
  induction p with
  | nil => simp [pathDisplacement]
  | cons st r ih => simp [pathDisplacement, ih, add_assoc]
abbrev _root_.YangMills.DeltaSharedProofs.p500756 := @pathDisplacement_append
private def bondOfStep (d : ℤ) (z : Fin 4 → ℤ) (st : PathStep) : PeriodicLattice.Bond L n d :=
  if st.2 then PeriodicLattice.Bond.forwardFrom (latticeSite d z) st.1
  else PeriodicLattice.Bond.backwardFrom (latticeSite d z) st.1
private def bondsOfPath (d : ℤ) : (Fin 4 → ℤ) → List PathStep → List (PeriodicLattice.Bond L n d)
  | _, [] => []
  | z, st :: r => bondOfStep d z st :: bondsOfPath d (z + stepVector st) r
private theorem bondsOfPath_append (d : ℤ) (p q : List PathStep) (z : Fin 4 → ℤ) :
    bondsOfPath (L := L) (n := n) d z (p ++ q) =
      bondsOfPath d z p ++ bondsOfPath d (z + pathDisplacement p) q := by
  induction p generalizing z with
  | nil => simp [bondsOfPath, pathDisplacement]
  | cons st r ih => simp [bondsOfPath, ih, pathDisplacement, add_assoc]
private theorem forwardFlow_eq (d : ℤ) (μ : Fin 4) (c : ℕ) (z : Fin 4 → ℤ) :
    PeriodicLattice.forwardAxisPath (latticeSite (L := L) (n := n) d z) μ c =
      bondsOfPath d z (List.replicate c (μ, true)) := by
  induction c generalizing z with
  | zero => rfl
  | succ c ih =>
    have h : latticeSite (L := L) (n := n) d z + PeriodicLattice.unitStep L n d μ =
        latticeSite d (z + stepVector (μ, true)) := by
      have := latticeSite_add_single (L := L) (n := n) d z μ 1
      simpa [stepVector] using this.symm
    simp only [List.replicate_succ, bondsOfPath, PeriodicLattice.forwardAxisPath, bondOfStep, if_true]
    rw [h, ih]
private theorem backwardFlow_eq (d : ℤ) (μ : Fin 4) (c : ℕ) (z : Fin 4 → ℤ) :
    PeriodicLattice.backwardAxisPath (latticeSite (L := L) (n := n) d z) μ c =
      bondsOfPath d z (List.replicate c (μ, false)) := by
  induction c generalizing z with
  | zero => rfl
  | succ c ih =>
    have h : latticeSite (L := L) (n := n) d z - PeriodicLattice.unitStep L n d μ =
        latticeSite d (z + stepVector (μ, false)) := by
      have := latticeSite_add_single (L := L) (n := n) d z μ (-1)
      have e : (Pi.single μ (-1) : Fin 4 → ℤ) = -Pi.single μ 1 := by
        funext i
        by_cases hi : i = μ
        · subst hi; simp
        · simp [Pi.single_eq_of_ne hi]
      rw [e] at this
      simpa [stepVector, sub_eq_add_neg] using this.symm
    simp only [List.replicate_succ, bondsOfPath, PeriodicLattice.backwardAxisPath, bondOfStep]
    rw [h, ih]
    simp
private theorem flowAlong_eq (d : ℤ) (μ : Fin 4) (c : ℤ) (z : Fin 4 → ℤ) :
    PeriodicLattice.flowAlong (latticeSite (L := L) (n := n) d z) μ c =
      bondsOfPath d z (List.replicate c.natAbs (μ, decide (0 ≤ c))) := by
  unfold PeriodicLattice.flowAlong
  by_cases h : 0 ≤ c
  · simp only [h, if_true, decide_true]
    rw [forwardFlow_eq]
    congr 2
    omega
  · simp only [h, if_false, decide_false]
    rw [backwardFlow_eq]
    congr 2
    omega
private theorem pathDisplacement_replicate (μ : Fin 4) (c : ℤ) :
    pathDisplacement (List.replicate c.natAbs (μ, decide (0 ≤ c))) = Pi.single μ c := by
  have key : ∀ (m : ℕ) (b : Bool), pathDisplacement (List.replicate m (μ, b)) =
      (if b then (m : ℤ) else -(m : ℤ)) • (Pi.single μ 1 : Fin 4 → ℤ) := by
    intro m b
    induction m with
    | zero => simp [pathDisplacement]
    | succ m ih =>
      rw [List.replicate_succ, pathDisplacement, ih]
      cases b <;> simp [stepVector] <;> ring_nf
  rw [key]
  funext i
  by_cases hi : i = μ
  · subst hi
    by_cases h : 0 ≤ c
    · simp [h, abs_of_nonneg h]
    · have : c < 0 := not_le.mp h
      simp [h, abs_of_neg this]
  · simp [Pi.single_eq_of_ne hi]
private def offsetPath (h : Fin 4 → ℤ) (l : List (Fin 4)) : List PathStep :=
  l.flatMap fun μ => List.replicate (h μ).natAbs (μ, decide (0 ≤ h μ))
private theorem stepsThroughAxes_eq (d : ℤ) (h : Fin 4 → ℤ) (l : List (Fin 4)) (z : Fin 4 → ℤ) :
    PeriodicLattice.stepsThroughAxes h (latticeSite (L := L) (n := n) d z) l =
      bondsOfPath d z (offsetPath h l) := by
  induction l generalizing z with
  | nil => rfl
  | cons μ l ih =>
    have e : offsetPath h (μ :: l) =
        List.replicate (h μ).natAbs (μ, decide (0 ≤ h μ)) ++ offsetPath h l := by
      simp [offsetPath]
    rw [e, bondsOfPath_append, pathDisplacement_replicate, PeriodicLattice.stepsThroughAxes, flowAlong_eq,
      ← latticeSite_add_single, ih]
end Paths
section FrameSide
variable {F : BlockFrame}
private theorem siteOfCoords_add (j : ℕ) (z w : Fin 4 → ℤ) :
    (siteOfCoords j (z + w) : F.Site j) = siteOfCoords j z + siteOfCoords j w := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
private theorem siteOfCoords_add_stepVector (j : ℕ) (z : Fin 4 → ℤ) (st : PathStep) :
    (siteOfCoords j (z + stepVector st) : F.Site j) = siteOfCoords j z + stepDisplacement j st := by apply _root_.YangMills.Construction.NearlyFlatDifferences.siteOfCoords_add_step <;> assumption
private theorem pathHolonomy_append {j : ℕ} (X : F.GaugeField j) (p q : List PathStep) (z : Fin 4 → ℤ) :
    pathHolonomy X (siteOfCoords j z) (p ++ q) =
      pathHolonomy X (siteOfCoords j z) p * pathHolonomy X (siteOfCoords j (z + pathDisplacement p)) q := by
  induction p generalizing z with
  | nil => simp [pathHolonomy, pathDisplacement]
  | cons st r ih =>
    simp only [List.cons_append, pathHolonomy, pathDisplacement]
    rw [← siteOfCoords_add_stepVector, ih, mul_assoc, add_assoc]
private theorem pathDisplacement_reversePath (r : List PathStep) :
    pathDisplacement (reversePath r) = -pathDisplacement r := by
  induction r with
  | nil => simp [reversePath, pathDisplacement]
  | cons s r' ih' =>
    have e3 : reversePath (s :: r') = reversePath r' ++ [(s.1, !s.2)] := by
      simp [reversePath]
    rw [e3, pathDisplacement_append, ih']
    cases hs : s with
    | mk a b =>
      cases b <;> simp [pathDisplacement, stepVector, neg_add]
abbrev _root_.YangMills.DeltaSharedProofs.p502468 := @pathDisplacement_reversePath
private theorem linkValue_flip {j : ℕ} (X : F.GaugeField j) (st : PathStep) (z : Fin 4 → ℤ) :
    linkValue X (siteOfCoords j (z + stepVector st)) (st.1, !st.2) = (linkValue X (siteOfCoords j z) st)⁻¹ := by
  rw [siteOfCoords_add_stepVector]
  cases st with
  | mk a b =>
    cases b <;> simp [linkValue, stepDisplacement, sub_eq_add_neg]
private theorem pathHolonomy_reversePath {j : ℕ} (X : F.GaugeField j) (p : List PathStep) (z : Fin 4 → ℤ) :
    pathHolonomy X (siteOfCoords j (z + pathDisplacement p)) (reversePath p) =
      (pathHolonomy X (siteOfCoords j z) p)⁻¹ := by
  induction p generalizing z with
  | nil => simp [pathHolonomy, pathDisplacement, reversePath]
  | cons st r ih =>
    have e : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    have e2 : z + pathDisplacement (st :: r) = (z + stepVector st) + pathDisplacement r := by
      simp [pathDisplacement, add_assoc]
    have e3 : z + stepVector st + pathDisplacement r + pathDisplacement (reversePath r) = z + stepVector st := by
      rw [pathDisplacement_reversePath]; abel
    rw [e, e2, pathHolonomy_append, ih, e3]
    simp only [pathHolonomy, mul_one]
    rw [linkValue_flip, ← siteOfCoords_add_stepVector, mul_inv_rev]
end FrameSide
section EvaluationMaps
variable {L n : ℕ} {F : BlockFrame}
private theorem toMatrix_mul (p q : ℍ[ℝ]) : SoftAverages.quaternionToMatrix (p * q) =
    SoftAverages.quaternionToMatrix p * SoftAverages.quaternionToMatrix q := by apply _root_.YangMills.Construction.SoftAverages.quaternionToMatrix_mul <;> assumption
private theorem toMatrix_inv (g : UnitQuaternion) : SoftAverages.quaternionToMatrix ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
    (SoftAverages.quaternionToMatrix (g : ℍ[ℝ]))⁻¹ := by apply _root_.YangMills.SharedProofs.p81137 <;> assumption
private theorem latticeSite_sub_unitStep (d : ℤ) (z : Fin 4 → ℤ) (μ : Fin 4) :
    latticeSite (L := L) (n := n) d z - PeriodicLattice.unitStep L n d μ =
      latticeSite d (z + stepVector (μ, false)) := by
  have := latticeSite_add_single (L := L) (n := n) d z μ (-1)
  have e : (Pi.single μ (-1) : Fin 4 → ℤ) = -Pi.single μ 1 := by
    funext i
    by_cases hi : i = μ
    · subst hi; simp
    · simp [Pi.single_eq_of_ne hi]
  rw [e] at this
  simpa [stepVector, sub_eq_add_neg] using this.symm
private theorem value_bondOfStep {d : ℤ} {t : ℕ} {U : PeriodicLattice.Bond L n d → Matrices.ComplexMatrix2}
    {X : F.GaugeField t}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L n d)
    (hR : ∀ (z : Fin 4 → ℤ) (μ : Fin 4), U (PeriodicLattice.Bond.forwardFrom (latticeSite d z) μ) =
      SoftAverages.quaternionToMatrix ((X (siteOfCoords t z) μ : UnitQuaternion) : ℍ[ℝ]))
    (z : Fin 4 → ℤ) (st : PathStep) :
    U (bondOfStep d z st) =
      SoftAverages.quaternionToMatrix ((linkValue X (siteOfCoords t z) st : UnitQuaternion) : ℍ[ℝ]) := by
  cases st with
  | mk μ b =>
    cases b
    · have hb : (PeriodicLattice.Bond.backwardFrom (latticeSite (L := L) (n := n) d z) μ) =
          (PeriodicLattice.Bond.forwardFrom (latticeSite d (z + stepVector (μ, false))) μ).opposite := by
        have h := latticeSite_sub_unitStep (L := L) (n := n) d z μ
        refine PeriodicLattice.Bond.ext ?_ ?_
        · show latticeSite d z = latticeSite d (z + stepVector (μ, false)) + PeriodicLattice.unitStep L n d μ
          rw [← h]; abel
        · exact h
      have hv : (X (siteOfCoords t z - BlockAverages.unitStep t μ) μ) = X (siteOfCoords t (z + stepVector (μ, false))) μ := by
        rw [siteOfCoords_add_stepVector]
        simp [stepDisplacement, sub_eq_add_neg]
      simp only [bondOfStep, linkValue]
      simp only [Bool.false_eq_true, if_false]
      rw [hb, hU.2 _ (Set.mem_univ _), hR, hv, toMatrix_inv]
    · simp only [bondOfStep, linkValue, if_true]
      exact hR z μ
private theorem holonomy_bondsOfPath {d : ℤ} {t : ℕ} {U : PeriodicLattice.Bond L n d → Matrices.ComplexMatrix2}
    {X : F.GaugeField t}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L n d)
    (hR : ∀ (z : Fin 4 → ℤ) (μ : Fin 4), U (PeriodicLattice.Bond.forwardFrom (latticeSite d z) μ) =
      SoftAverages.quaternionToMatrix ((X (siteOfCoords t z) μ : UnitQuaternion) : ℍ[ℝ]))
    (p : List PathStep) (z : Fin 4 → ℤ) :
    PeriodicLattice.pathHolonomy U (bondsOfPath d z p) =
      SoftAverages.quaternionToMatrix ((pathHolonomy X (siteOfCoords t z) p : UnitQuaternion) : ℍ[ℝ]) := by
  induction p generalizing z with
  | nil =>
    simp only [bondsOfPath, PeriodicLattice.pathHolonomy, pathHolonomy]
    simp [SoftAverages.quaternionToMatrix_one]
  | cons st r ih =>
    have := ih (z + stepVector st)
    simp only [PeriodicLattice.pathHolonomy] at this
    simp only [bondsOfPath, PeriodicLattice.pathHolonomy, pathHolonomy, List.map_cons, List.prod_cons]
    rw [this, value_bondOfStep hU hR, Submonoid.coe_mul, toMatrix_mul, siteOfCoords_add_stepVector]
end EvaluationMaps
section Lattices
variable {L n : ℕ}
private theorem latticeSite_zero (d : ℤ) : latticeSite (L := L) (n := n) d 0 = 0 := by
  simp [latticeSite, PeriodicLattice.offsetSite]
private theorem latticeSite_add' (d : ℤ) (z w : Fin 4 → ℤ) :
    latticeSite (L := L) (n := n) d (z + w) = latticeSite d z + latticeSite d w := by
  rw [latticeSite_add]
  simp [latticeSite, PeriodicLattice.offsetSite]
private theorem unitStep_eq_latticeSite (d : ℤ) (μ : Fin 4) :
    PeriodicLattice.unitStep L n d μ = latticeSite d (Pi.single μ 1) := by
  have := latticeSite_add_single (L := L) (n := n) d 0 μ 1
  simpa [latticeSite_zero] using this.symm
private theorem toSublattice_eq {d d' : ℤ} (y : PeriodicLattice.Site L n d) (x : PeriodicLattice.Site L n d')
    (h : (x : PeriodicLattice.FourTorus L n) = y) : y.toSublattice d' = x := by
  have hs : ((y.toSublattice d' : PeriodicLattice.Site L n d') : PeriodicLattice.FourTorus L n) = y :=
    Classical.epsilon_spec (p := fun x : PeriodicLattice.Site L n d' => (x : PeriodicLattice.FourTorus L n) = y)
      ⟨x, h⟩
  exact Subtype.ext (hs.trans h.symm)
private theorem latticeSite_eq_iff {d : ℤ} {P : ℕ} (hs : PeriodicLattice.meshSize L d ≠ 0)
    (hP : (P : ℝ) * PeriodicLattice.meshSize L d = PeriodicLattice.torusSide L n) (z z' : Fin 4 → ℤ) :
    latticeSite (L := L) (n := n) d z = latticeSite d z' ↔ ∀ ν, ∃ m : ℤ, z ν - z' ν = m * P := by
  have one : ∀ a b : ℤ, ((((a : ℝ) * PeriodicLattice.meshSize L d : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) =
      (((b : ℝ) * PeriodicLattice.meshSize L d : ℝ) : AddCircle (PeriodicLattice.torusSide L n))) ↔
      ∃ m : ℤ, a - b = m * P := by
    intro a b
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [← hP, zsmul_eq_mul, ← mul_assoc, ← sub_mul] at hm
      have := mul_right_cancel₀ hs hm
      exact_mod_cast this.symm
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [← hP, zsmul_eq_mul, ← mul_assoc, ← sub_mul]
      congr 1
      exact_mod_cast hm.symm
  constructor
  · intro h ν
    have := congrFun (congrArg (fun x : PeriodicLattice.Site L n d => (x : PeriodicLattice.FourTorus L n)) h) ν
    simp only [coe_latticeSite] at this
    exact (one _ _).mp this
  · intro h
    refine Subtype.ext (funext fun ν => ?_)
    rw [coe_latticeSite, coe_latticeSite]
    exact (one _ _).mpr (h ν)
private theorem sum_pointOnAxis (d : ℤ) (h : Fin 4 → ℤ) :
    (∑ μ, PeriodicLattice.pointOnAxis L n μ ((h μ : ℝ) * PeriodicLattice.meshSize L d)) =
      ((latticeSite (L := L) (n := n) d h : PeriodicLattice.Site L n d) : PeriodicLattice.FourTorus L n) := by
  funext ν
  rw [coe_latticeSite, Finset.sum_apply, Finset.sum_eq_single ν]
  · simp [PeriodicLattice.pointOnAxis]
  · intro b _ hb
    simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hb.symm]
  · simp
private theorem eq_zero_of_abs_lt_of_eq_mul {a m : ℤ} {P : ℕ} (hlt : |a| < P) (h : a = m * P) : a = 0 := by
  by_contra hne
  have hm : m ≠ 0 := fun h0 => hne (by simp [h, h0])
  have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
  have h2 : |a| = |m| * P := by rw [h, abs_mul]; simp
  nlinarith
end Lattices
section Legs
private theorem pathDisplacement_flatMap {α : Type*} (l : List α) (g : α → List PathStep) :
    pathDisplacement (l.flatMap g) = (l.map fun a => pathDisplacement (g a)).sum := by
  induction l with
  | nil => simp [pathDisplacement]
  | cons a l ih => simp [List.flatMap_cons, pathDisplacement_append, ih]
private theorem pathDisplacement_axisPath (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    pathDisplacement (axisPath h π) = h := by
  unfold axisPath
  rw [pathDisplacement_flatMap]
  have e : ∀ k : Fin 4, pathDisplacement (List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))) =
      Pi.single (π k) (h (π k)) := fun k => pathDisplacement_replicate _ _
  simp only [e]
  rw [← Fin.sum_univ_def, Equiv.sum_comp π (fun μ => (Pi.single μ (h μ) : Fin 4 → ℤ)),
    Finset.univ_sum_single]
abbrev _root_.YangMills.DeltaSharedProofs.p500824 := @pathDisplacement_axisPath
private theorem pathDisplacement_line (i : Fin 4) (c : ℕ) :
    pathDisplacement (List.replicate c (i, true)) = Pi.single i (c : ℤ) := by
  have := pathDisplacement_replicate i (c : ℤ)
  simpa using this
private theorem pathHolonomy_bondContour {F : BlockFrame} {t : ℕ} (X : F.GaugeField t) (c : ℕ) (h : Fin 4 → ℤ)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) (z : Fin 4 → ℤ) :
    pathHolonomy X (siteOfCoords t z) (bondContour c h π i) =
      pathHolonomy X (siteOfCoords t z) (axisPath h π) *
        pathHolonomy X (siteOfCoords t (z + h)) (List.replicate c (i, true)) *
        (pathHolonomy X (siteOfCoords t (z + Pi.single i (c : ℤ))) (axisPath h π))⁻¹ := by
  unfold bondContour
  have e : z + pathDisplacement (axisPath h π ++ List.replicate c (i, true)) =
      (z + Pi.single i (c : ℤ)) + pathDisplacement (axisPath h π) := by
    rw [pathDisplacement_append, pathDisplacement_axisPath, pathDisplacement_line]; abel
  rw [pathHolonomy_append, e, pathHolonomy_reversePath, pathHolonomy_append, pathDisplacement_axisPath]
end Legs
section Tower
variable {L n k j M : ℕ}
private def scaledCoords (L : ℕ) (w : Fin 4 → ℤ) : Fin 4 → ℤ := fun ν => (L : ℤ) * w ν
private theorem meshSize_succ (hL : 0 < L) :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k (j + 1)) =
      L * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold PeriodicLattice.meshSize
  have e : -PeriodicLattice.levelDepth k (j + 1) = -PeriodicLattice.levelDepth k j + 1 := by
    simp only [PeriodicLattice.levelDepth]; push_cast; ring
  rw [e, zpow_add₀ hL', zpow_one]
  ring
private theorem coe_coarse (hL : 0 < L) (w : Fin 4 → ℤ) :
    ((latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w :
        PeriodicLattice.Site L n (PeriodicLattice.levelDepth k (j + 1))) : PeriodicLattice.FourTorus L n) =
      (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) (scaledCoords L w) :
        PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j)) := by
  funext ν
  rw [coe_latticeSite, coe_latticeSite, meshSize_succ hL]
  have : (w ν : ℝ) * ((L : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j)) =
      ((scaledCoords L w ν : ℤ) : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j) := by
    simp [scaledCoords]; ring
  rw [this]
private theorem meshSize_ne_zero (hL : 0 < L) (d : ℤ) : PeriodicLattice.meshSize L d ≠ 0 := by apply _root_.YangMills.Construction.PeriodicLattice.BondEndpointsOrientation.meshSize_ne_zero <;> assumption
private theorem side_eq (hL : 0 < L) (hj : j < k) (hM : M * L = 2 * L ^ (n + (k - j))) :
    ((M * L : ℕ) : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j) =
      PeriodicLattice.torusSide L n := by
  have e : PeriodicLattice.levelDepth k j = ((k - j : ℕ) : ℤ) := by
    simp only [PeriodicLattice.levelDepth]; omega
  rw [hM, e]
  unfold PeriodicLattice.meshSize PeriodicLattice.torusSide
  rw [zpow_neg, zpow_natCast]
  push_cast
  rw [pow_add]
  field_simp
private theorem isBlockOffset (hL : 0 < L) (w h : Fin 4 → ℤ) (hb : ∀ μ, 2 * |h μ| ≤ (L : ℤ) - 1) :
    PeriodicLattice.IsBlockOffset
      (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w)
      (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) (scaledCoords L w + h)) h := by
  refine ⟨?_, hb⟩
  rw [sum_pointOnAxis, coe_coarse hL, latticeSite_add']
  simp
private theorem lt_period (hL : 0 < L) (hM : M * L = 2 * L ^ (n + (k - j))) (hn : 0 < n) :
    (L : ℤ) < ((M * L : ℕ) : ℤ) := by
  rw [hM]
  have h1 : L ≤ L ^ (n + (k - j)) := Nat.le_self_pow (by omega) L
  have : L < 2 * L ^ (n + (k - j)) := by omega
  exact_mod_cast this
private theorem blockOffset_unique (hL : 0 < L) (hj : j < k) (hM : M * L = 2 * L ^ (n + (k - j))) (hn : 0 < n)
    (w h n₁ : Fin 4 → ℤ) (hb : ∀ μ, 2 * |h μ| ≤ (L : ℤ) - 1)
    (h₁ : PeriodicLattice.IsBlockOffset
      (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w)
      (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) (scaledCoords L w + h)) n₁) : n₁ = h := by
  have h₂ := isBlockOffset (L := L) (n := n) (k := k) (j := j) hL w h hb
  obtain ⟨e₁, b₁⟩ := h₁
  have e₂ := h₂.1
  rw [sum_pointOnAxis] at e₁ e₂
  have hs : latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) n₁ = latticeSite _ h :=
    Subtype.ext (e₁.symm.trans e₂)
  have := (latticeSite_eq_iff (meshSize_ne_zero hL _) (side_eq hL hj hM) _ _).mp hs
  funext ν
  obtain ⟨m, hm⟩ := this ν
  have hlt : |n₁ ν - h ν| < ((M * L : ℕ) : ℤ) := by
    have h3 := abs_sub (n₁ ν) (h ν)
    have h4 := b₁ ν
    have h5 := hb ν
    have h6 := lt_period hL hM hn
    omega
  have := eq_zero_of_abs_lt_of_eq_mul hlt hm
  omega
private theorem blockOffset_eq (hL : 0 < L) (hj : j < k) (hM : M * L = 2 * L ^ (n + (k - j)))
    (hn : 0 < n) (w h : Fin 4 → ℤ) (hb : ∀ μ, 2 * |h μ| ≤ (L : ℤ) - 1) :
    PeriodicLattice.blockOffset (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w)
      (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) (scaledCoords L w + h)) = h :=
  blockOffset_unique hL hj hM hn w h _ hb
    (Classical.epsilon_spec (p := PeriodicLattice.IsBlockOffset _ _) ⟨h, isBlockOffset hL w h hb⟩)
private theorem contourLeg_eq (hL : 0 < L) (hj : j < k) (hM : M * L = 2 * L ^ (n + (k - j)))
    (hn : 0 < n) (w h : Fin 4 → ℤ) (hb : ∀ μ, 2 * |h μ| ≤ (L : ℤ) - 1) (π : Equiv.Perm (Fin 4)) :
    contourLeg (L := L) (m := n) (k := k) (j := j)
        (latticeSite (PeriodicLattice.levelDepth k (j + 1)) w)
        (latticeSite (PeriodicLattice.levelDepth k j) (scaledCoords L w + h)) π =
      bondsOfPath (PeriodicLattice.levelDepth k j) (scaledCoords L w) (axisPath h π) := by
  unfold contourLeg
  rw [blockOffset_eq hL hj hM hn w h hb,
    toSublattice_eq _ (latticeSite (PeriodicLattice.levelDepth k j) (scaledCoords L w)) (coe_coarse hL w).symm,
    stepsThroughAxes_eq]
  congr 1
private theorem mem_centredCube_iff (hL : Odd L) (h : Fin 4 → ℤ) :
    h ∈ centredCube L ↔ ∀ μ, 2 * |h μ| ≤ (L : ℤ) - 1 := by
  obtain ⟨a, ha⟩ := hL
  subst ha
  simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc]
  refine forall_congr' fun μ => ?_
  rcases abs_cases (h μ) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> push_cast <;> omega
private theorem shiftAcross_eq (hL : 0 < L) (w z : Fin 4 → ℤ) (μ : Fin 4) :
    PeriodicLattice.shiftAcross (PeriodicLattice.Bond.forwardFrom
      (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w) μ)
        (latticeSite (PeriodicLattice.levelDepth k j) z) =
      latticeSite (PeriodicLattice.levelDepth k j) z +
        (L : ℤ) • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ := by
  have hstep : (PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k (j + 1)) μ).toSublattice
      (PeriodicLattice.levelDepth k j) =
        latticeSite (PeriodicLattice.levelDepth k j) (scaledCoords L (Pi.single μ 1)) := by
    refine toSublattice_eq _ _ ?_
    rw [unitStep_eq_latticeSite]
    exact (coe_coarse hL _).symm
  have hlw : scaledCoords L (Pi.single μ 1) = Pi.single μ (L : ℤ) := by
    funext i
    by_cases hi : i = μ
    · subst hi; simp [scaledCoords]
    · simp [scaledCoords, Pi.single_eq_of_ne hi]
  unfold PeriodicLattice.shiftAcross
  simp only [PeriodicLattice.Bond.forwardFrom, add_sub_cancel_left]
  rw [hstep, hlw]
  congr 1
  have := latticeSite_add_single (L := L) (n := n) (PeriodicLattice.levelDepth k j) 0 μ (L : ℤ)
  simpa [latticeSite_zero] using this
private theorem crossingPath_eq (hL : 0 < L) (hL2 : 2 ≤ L) (hj : j < k) (hM : M * L = 2 * L ^ (n + (k - j)))
    (hn : 0 < n) (w z : Fin 4 → ℤ) (μ : Fin 4) :
    PeriodicLattice.crossingPath (PeriodicLattice.Bond.forwardFrom
        (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w) μ)
      (latticeSite (PeriodicLattice.levelDepth k j) z) =
      bondsOfPath (PeriodicLattice.levelDepth k j) z (List.replicate L (μ, true)) := by
  have htr := shiftAcross_eq (n := n) (k := k) (j := j) hL w z μ
  unfold PeriodicLattice.crossingPath
  rw [htr]
  set x := latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) z with hx
  have hdepth : PeriodicLattice.levelDepth k j = ((k - j : ℕ) : ℤ) := by
    simp only [PeriodicLattice.levelDepth]; omega
  have hpow : (L : ℝ) ^ ((n : ℤ) + PeriodicLattice.levelDepth k j) = ((L ^ (n + (k - j)) : ℕ) : ℝ) := by
    rw [hdepth]
    push_cast
    rw [← zpow_natCast]
    congr 1
  have hLlt : (L : ℤ) < ((L ^ (n + (k - j)) : ℕ) : ℤ) := by
    have h2 : L ^ 1 < L ^ (n + (k - j)) := Nat.pow_lt_pow_right (by omega) (by omega)
    rw [pow_one] at h2
    exact_mod_cast h2
  have hself : PeriodicLattice.IsAxialDisplacement x
      (x + (L : ℤ) • PeriodicLattice.unitStep L n _ μ) μ (L : ℤ) := by
    refine ⟨by abel, ?_⟩
    rw [hpow]
    have : |(L : ℤ)| = (L : ℤ) := abs_of_nonneg (by positivity)
    rw [this]
    exact_mod_cast hLlt
  have hex : ∃ q : Fin 4 × ℤ, PeriodicLattice.IsAxialDisplacement x
      (x + (L : ℤ) • PeriodicLattice.unitStep L n _ μ) q.1 q.2 := ⟨(μ, (L : ℤ)), hself⟩
  unfold PeriodicLattice.axialPath
  rw [dif_pos hex]
  obtain ⟨hq1, hq2⟩ := hex.choose_spec
  set q := hex.choose with hqdef
  have hsc : latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) (z + Pi.single μ (L : ℤ)) =
      latticeSite _ (z + Pi.single q.1 q.2) := by
    rw [latticeSite_add_single, latticeSite_add_single, ← hx, ← hq1]
    abel
  have hco := (latticeSite_eq_iff (meshSize_ne_zero hL _) (side_eq hL hj hM) _ _).mp hsc
  have hPZ : ((M * L : ℕ) : ℤ) = 2 * ((L ^ (n + (k - j)) : ℕ) : ℤ) := by
    rw [hM]; push_cast; ring
  have hq2' : |q.2| < ((L ^ (n + (k - j)) : ℕ) : ℤ) := by
    rw [hpow] at hq2
    exact_mod_cast hq2
  have hμ : q.1 = μ := by
    by_contra hne
    obtain ⟨m, hm⟩ := hco μ
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at hm
    have h0 : (L : ℤ) = m * ((M * L : ℕ) : ℤ) := by linarith
    have hlt : |(L : ℤ)| < ((M * L : ℕ) : ℤ) := by
      rw [abs_of_nonneg (by positivity)]; omega
    have := eq_zero_of_abs_lt_of_eq_mul hlt h0
    omega
  have hq : q.2 = (L : ℤ) := by
    obtain ⟨m, hm⟩ := hco μ
    rw [hμ] at hm
    simp only [Pi.add_apply, Pi.single_eq_same] at hm
    have h0 : (L : ℤ) - q.2 = m * ((M * L : ℕ) : ℤ) := by linarith
    have hlt : |(L : ℤ) - q.2| < ((M * L : ℕ) : ℤ) := by
      have h3 := abs_sub (L : ℤ) q.2
      have h4 : |(L : ℤ)| = L := abs_of_nonneg (by positivity)
      omega
    have := eq_zero_of_abs_lt_of_eq_mul hlt h0
    omega
  rw [hμ, hq, hx, flowAlong_eq]
  simp
end Tower
section Final
variable {L n k j M : ℕ}
private theorem cast_cast_eq (P Q : ℕ) (h : P = Q) (z : ℤ) :
    (((ZMod.cast ((z : ZMod P)) : ℤ)) : ZMod Q) = (z : ZMod Q) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_intCast <;> assumption
private theorem refine_cast (P Q : ℕ) (hP : P = M * L) (hQ : Q = M) (z : ℤ) :
    ((((L : ℤ) * (ZMod.cast ((z : ZMod Q)) : ℤ) : ℤ)) : ZMod P) = (((L : ℤ) * z : ℤ) : ZMod P) := by
  subst hP hQ
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (ZMod.cast ((z : ZMod Q)) : ℤ) z Q).mp (by simp)
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  push_cast
  rw [← mul_sub, hc]
  ring
private theorem toMatrix_smul (r : ℝ) (q : ℍ[ℝ]) : SoftAverages.quaternionToMatrix (r • q) =
    (r : ℂ) • SoftAverages.quaternionToMatrix q := by apply _root_.YangMills.DeltaSharedProofs.p501227 <;> assumption
private theorem finsum_sitesInBlock (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (hM : M * L = 2 * L ^ (n + (k - j)))
    (f : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j) → Matrices.ComplexMatrix2) (w : Fin 4 → ℤ) :
    ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w), f x =
      ∑ h ∈ centredCube L, f (latticeSite (PeriodicLattice.levelDepth k j) (scaledCoords L w + h)) := by
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨-, -, hB, -⟩ := hC L n hL.1 hL.2 hn
  have hdc : -(n : ℤ) ≤ PeriodicLattice.levelDepth k (j + 1) := by
    simp only [PeriodicLattice.levelDepth]; push_cast; omega
  obtain ⟨hmem, himg, -, -, -⟩ := hB (PeriodicLattice.levelDepth k (j + 1)) 1 hdc
    (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w)
  have hd : PeriodicLattice.levelDepth k (j + 1) + ((1 : ℕ) : ℤ) = PeriodicLattice.levelDepth k j := by
    simp only [PeriodicLattice.levelDepth]; push_cast; ring
  have hsame : ∀ (d' : ℤ), d' = PeriodicLattice.levelDepth k j → ∀ p : Fin 4 → ℤ,
      ((latticeSite (L := L) (n := n) d' p : PeriodicLattice.Site L n d') : PeriodicLattice.FourTorus L n) =
        (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) p :
          PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j)) := by
    rintro _ rfl p; rfl
  have hcoe : ∀ p : Fin 4 → ℤ, ((PeriodicLattice.refinedOffsetSite 1
      (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w) p :
        PeriodicLattice.Site L n (PeriodicLattice.levelDepth k (j + 1) + ((1 : ℕ) : ℤ))) :
          PeriodicLattice.FourTorus L n) =
      (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) (scaledCoords L w + p) :
        PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j)) := by
    intro p
    have h1 : ((((latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w).toSublattice
        (PeriodicLattice.levelDepth k (j + 1) + ((1 : ℕ) : ℤ))) :
          PeriodicLattice.Site L n (PeriodicLattice.levelDepth k (j + 1) + ((1 : ℕ) : ℤ))) :
            PeriodicLattice.FourTorus L n) =
        (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w : PeriodicLattice.Site L n _) :=
      Classical.epsilon_spec
        (p := fun x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k (j + 1) + ((1 : ℕ) : ℤ)) =>
          (x : PeriodicLattice.FourTorus L n) =
            (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w : PeriodicLattice.Site L n _))
        ⟨⟨_, hmem⟩, rfl⟩
    have h2 : PeriodicLattice.refinedOffsetSite 1
        (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w) p =
        (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w).toSublattice
          (PeriodicLattice.levelDepth k (j + 1) + ((1 : ℕ) : ℤ)) + latticeSite _ p := by
      simp [PeriodicLattice.refinedOffsetSite, PeriodicLattice.offsetSite, latticeSite]
    rw [h2, AddSubgroup.coe_add, h1, hsame _ hd p, coe_coarse hL0, latticeSite_add', AddSubgroup.coe_add]
  have hbij : Set.BijOn
      (fun h : Fin 4 → ℤ => latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) (scaledCoords L w + h))
      (centredCube L : Set (Fin 4 → ℤ))
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro h hh
      have hb := (mem_centredCube_iff hL.1 h).mp (Finset.mem_coe.mp hh)
      show _ ∈ PeriodicLattice.refinedBlock 1 _
      rw [himg]
      exact ⟨h, fun μ => by simpa using hb μ, hcoe h⟩
    · intro h hh h' hh' he
      have hb := (mem_centredCube_iff hL.1 h).mp (Finset.mem_coe.mp hh)
      have hb' := (mem_centredCube_iff hL.1 h').mp (Finset.mem_coe.mp hh')
      have := (latticeSite_eq_iff (meshSize_ne_zero hL0 _) (side_eq hL0 hj hM) _ _).mp he
      funext ν
      obtain ⟨m, hm⟩ := this ν
      simp only [Pi.add_apply, add_sub_add_left_eq_sub] at hm
      have hlt : |h ν - h' ν| < ((M * L : ℕ) : ℤ) := by
        have h3 := abs_sub (h ν) (h' ν)
        have h4 := hb ν
        have h5 := hb' ν
        have h6 := lt_period hL0 hM hn
        omega
      have := eq_zero_of_abs_lt_of_eq_mul hlt hm
      omega
    · intro x hx
      have hx' : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock 1
          (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) w) := hx
      rw [himg] at hx'
      obtain ⟨p, hp, hpe⟩ := hx'
      refine ⟨p, Finset.mem_coe.mpr ((mem_centredCube_iff hL.1 p).mpr fun μ => by simpa using hp μ), ?_⟩
      exact Subtype.ext ((hcoe p).symm.trans hpe)
  rw [← finsum_mem_coe_finset]
  exact (finsum_mem_eq_of_bijOn _ hbij fun _ _ => rfl).symm
end Final
end ContourMean
open ContourMean in
theorem contourMeanMatchesFrame_holds
    (hC : PeriodicLattice.CoordinateDescription) :
    ContourMeanMatchesFrame := by
  intro L hL n k j M hn hj hM F hFL hper hper1 V U hRd z μ
  obtain ⟨L', t', sd⟩ := F
  obtain rfl : L = L' := hFL.symm
  have hL0 : 0 < L := by have := hL.2; omega
  have hL2 : 2 ≤ L := by have := hL.2; omega
  have hU : U ∈ PeriodicLattice.compactGaugeFields L n (PeriodicLattice.levelDepth k j) := hRd.1
  have hR : ∀ (z : Fin 4 → ℤ) (μ : Fin 4),
      U (PeriodicLattice.Bond.forwardFrom (latticeSite (PeriodicLattice.levelDepth k j) z) μ) =
        SoftAverages.quaternionToMatrix
          ((readAtLevel ((⟨L, t', sd⟩ : BlockFrame)) j V (siteOfCoords j z) μ : UnitQuaternion) : ℍ[ℝ]) := by
    intro z μ
    let zc : TorusSite (M * L) := fun i => (z i : ZMod (M * L))
    have h1 := hRd.2 zc μ
    have h2 : (levelVertexOfTorusSite j zc : Tower.Vertex L n k j) =
        latticeSite (PeriodicLattice.levelDepth k j) z := by
      show latticeSite (PeriodicLattice.levelDepth k j) (fun μ => ((zc μ).cast : ℤ)) =
        latticeSite (PeriodicLattice.levelDepth k j) z
      refine (latticeSite_eq_iff (meshSize_ne_zero hL0 _) (side_eq hL0 hj hM) _ _).mpr fun ν => ?_
      have h3 : ((z ν : ℤ) : ZMod (M * L)) = (((zc ν).cast : ℤ) : ZMod (M * L)) := by
        simp [zc]
      obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h3
      exact ⟨m, by rw [hm]; ring⟩
    have h3 : readAtLevel ((⟨L, t', sd⟩ : BlockFrame)) j V (siteOfCoords j z) μ = V zc μ := by
      show V (fun i => ((siteCoords (siteOfCoords (F := (⟨L, t', sd⟩ : BlockFrame)) j z) i : ℤ) :
        ZMod (M * L))) μ = V zc μ
      congr 1
      funext i
      exact cast_cast_eq _ _ (hper i) (z i)
    rw [← h2, h1, h3]
  have hval : ∀ h : Fin 4 → ℤ, (∀ μ', 2 * |h μ'| ≤ (L : ℤ) - 1) → ∀ π : Equiv.Perm (Fin 4),
      contourHolonomy U
          (PeriodicLattice.Bond.forwardFrom (latticeSite (PeriodicLattice.levelDepth k (j + 1)) z) μ)
          (latticeSite (PeriodicLattice.levelDepth k j) (scaledCoords L z + h)) π =
        SoftAverages.quaternionToMatrix ((pathHolonomy (readAtLevel ((⟨L, t', sd⟩ : BlockFrame)) j V)
          (siteOfCoords j (scaledCoords L z)) (bondContour L h π μ) : UnitQuaternion) : ℍ[ℝ]) := by
    intro h hb π
    have hhead : latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) z +
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k (j + 1)) μ =
        latticeSite (PeriodicLattice.levelDepth k (j + 1)) (z + Pi.single μ 1) := by
      have := latticeSite_add_single (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) z μ 1
      simpa using this.symm
    have hlw1 : scaledCoords L (z + Pi.single μ 1) = scaledCoords L z + Pi.single μ (L : ℤ) := by
      funext i
      by_cases hi : i = μ
      · subst hi; simp [scaledCoords]; ring
      · simp [scaledCoords, Pi.single_eq_of_ne hi]
    have hlwe : scaledCoords L (z + Pi.single μ 1) + h = scaledCoords L z + h + Pi.single μ (L : ℤ) := by
      rw [hlw1]; abel
    have htr' : PeriodicLattice.shiftAcross (PeriodicLattice.Bond.forwardFrom
        (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) z) μ)
        (latticeSite (PeriodicLattice.levelDepth k j) (scaledCoords L z + h)) =
        latticeSite (PeriodicLattice.levelDepth k j) (scaledCoords L (z + Pi.single μ 1) + h) := by
      rw [shiftAcross_eq hL0, ← latticeSite_add_single, hlwe]
    show PeriodicLattice.pathHolonomy U (contourLeg (latticeSite (PeriodicLattice.levelDepth k (j + 1)) z)
          (latticeSite (PeriodicLattice.levelDepth k j) (scaledCoords L z + h)) π) *
        PeriodicLattice.pathHolonomy U (PeriodicLattice.crossingPath (PeriodicLattice.Bond.forwardFrom
          (latticeSite (PeriodicLattice.levelDepth k (j + 1)) z) μ)
            (latticeSite (PeriodicLattice.levelDepth k j) (scaledCoords L z + h))) *
        (PeriodicLattice.pathHolonomy U (contourLeg
          (latticeSite (PeriodicLattice.levelDepth k (j + 1)) z +
            PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k (j + 1)) μ)
          (PeriodicLattice.shiftAcross (PeriodicLattice.Bond.forwardFrom
            (latticeSite (PeriodicLattice.levelDepth k (j + 1)) z) μ)
              (latticeSite (PeriodicLattice.levelDepth k j) (scaledCoords L z + h))) π))⁻¹ = _
    rw [hhead, htr', contourLeg_eq hL0 hj hM hn z h hb, contourLeg_eq hL0 hj hM hn _ h hb,
      crossingPath_eq hL0 hL2 hj hM hn, holonomy_bondsOfPath hU hR, holonomy_bondsOfPath hU hR,
      holonomy_bondsOfPath hU hR, _root_.YangMills.Construction.RunningCouplingSlope.ContourMean.pathHolonomy_bondContour, hlw1, Submonoid.coe_mul, Submonoid.coe_mul,
      toMatrix_mul, toMatrix_mul, toMatrix_inv]
  have hdown : refineSite (F := (⟨L, t', sd⟩ : BlockFrame)) (siteOfCoords (j + 1) z) =
      siteOfCoords j (scaledCoords L z) := by
    funext i
    exact refine_cast (M := M) (L := L) _ _ (hper i) (hper1 i) (z i)
  have hsum : ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) z),
        ∑ π : Equiv.Perm (Fin 4), contourHolonomy U
          (PeriodicLattice.Bond.forwardFrom (latticeSite (PeriodicLattice.levelDepth k (j + 1)) z) μ) x π =
      ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
        SoftAverages.quaternionToMatrix ((pathHolonomy (readAtLevel ((⟨L, t', sd⟩ : BlockFrame)) j V)
          (siteOfCoords j (scaledCoords L z)) (bondContour L h π μ) : UnitQuaternion) : ℍ[ℝ]) :=
    (finsum_sitesInBlock hC hL hn hj hM _ z).trans (Finset.sum_congr rfl fun h hh =>
      Finset.sum_congr rfl fun π _ => hval h ((mem_centredCube_iff hL.1 h).mp hh) π)
  have hQ : ∀ {ι : Type} (s : Finset ι) (f : ι → ℍ[ℝ]),
      SoftAverages.quaternionToMatrix (∑ i ∈ s, f i) = ∑ i ∈ s, SoftAverages.quaternionToMatrix (f i) :=
    fun s f => map_sum SoftAverages.quaternionToMatrixRingHom f s
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  show ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) •
        ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
          (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) z),
        ∑ π : Equiv.Perm (Fin 4), contourHolonomy U
          (PeriodicLattice.Bond.forwardFrom (latticeSite (PeriodicLattice.levelDepth k (j + 1)) z) μ) x π =
      SoftAverages.quaternionToMatrix ((1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy (readAtLevel ((⟨L, t', sd⟩ : BlockFrame)) j V)
          (refineSite (F := (⟨L, t', sd⟩ : BlockFrame)) (siteOfCoords (j + 1) z))
          (bondContour L h π μ) : UnitQuaternion) : ℍ[ℝ]))
  rw [hsum, toMatrix_smul, hdown, hQ]
  simp only [hQ]
  congr 1
  simp only [PeriodicLattice.inverseFourthPowerWeight]
  push_cast
  rw [zpow_neg]
  norm_cast
  field_simp
  push_cast
  rfl
end YangMills.Construction.RunningCouplingSlope
end

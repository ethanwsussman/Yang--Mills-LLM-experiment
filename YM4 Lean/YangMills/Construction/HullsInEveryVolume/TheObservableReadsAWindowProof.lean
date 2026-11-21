import YangMills.Construction.FormsOnATorus.InteriorRegularityProof
import YangMills.Construction.HullsInEveryVolume.TheObservableReadsAWindow
import YangMills.Construction.LawByMomentsOfTheFlow.LawAtLimitPointsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology Quaternion
namespace YangMills.Construction.HullsInEveryVolume
section Action
private def clampAction (x : ℝ) : ℝ := max 0 (min 2 x)
private theorem continuous_clampAction : Continuous clampAction :=
  continuous_const.max (continuous_const.min continuous_id)
private theorem abs_clampAction_le (x : ℝ) : |clampAction x| ≤ 2 := by
  unfold clampAction
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le (by norm_num) (min_le_left _ _)
private theorem clampAction_of_mem {x : ℝ} (h0 : 0 ≤ x) (h2 : x ≤ 2) : clampAction x = x := by
  unfold clampAction
  rw [min_eq_right h2, max_eq_right h0]
private def wilsonLoopAction (A B C D : Matrices.ComplexMatrix2) : ℝ :=
  clampAction (1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (A * B * C.conjTranspose * D.conjTranspose)).re)
private theorem continuous_wilsonLoopAction {X : Type*} [TopologicalSpace X] {A B C D : X → Matrices.ComplexMatrix2}
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) (hD : Continuous D) :
    Continuous fun x => wilsonLoopAction (A x) (B x) (C x) (D x) := by
  unfold wilsonLoopAction
  refine continuous_clampAction.comp (continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp ?_)))
  exact (((hA.matrix_mul hB).matrix_mul hC.matrix_conjTranspose).matrix_mul hD.matrix_conjTranspose).matrix_trace
private theorem coe_inv_eq_conjTranspose (x : Matrices.ComplexMatrix2.specialUnitary) :
    ((x⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      (x : Matrices.ComplexMatrix2).conjTranspose := by apply _root_.YangMills.SharedProofs.p1210 <;> assumption
private theorem trace_action_mem (x : Matrices.ComplexMatrix2.specialUnitary) :
    0 ≤ 1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (x : Matrices.ComplexMatrix2)).re ∧
      1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (x : Matrices.ComplexMatrix2)).re ≤ 2 := by
  have hu := (Matrix.mem_specialUnitaryGroup_iff.1 x.2).1
  have h : ∀ i, ‖(x : Matrices.ComplexMatrix2) i i‖ ≤ 1 := fun i => entry_norm_bound_of_unitary hu i i
  have h0 := (abs_le.1 ((Complex.abs_re_le_norm _).trans (h 0)))
  have h1 := (abs_le.1 ((Complex.abs_re_le_norm _).trans (h 1)))
  have e : (Matrices.ComplexMatrix2.fullTrace (x : Matrices.ComplexMatrix2)).re =
      ((x : Matrices.ComplexMatrix2) 0 0).re + ((x : Matrices.ComplexMatrix2) 1 1).re := by
    simp [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
  rw [e]
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
private theorem faceEnergy_eq_wilsonLoopAction {a : ℝ}
    (U : InfiniteLattice.Link a → Matrices.ComplexMatrix2.specialUnitary) (p : InfiniteLattice.ElementaryPlaquette a) :
    InfiniteLattice.faceEnergy U p =
      wilsonLoopAction (U (InfiniteLattice.Link.forwardFrom p.corner p.lowAxis) : Matrices.ComplexMatrix2)
        (U (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.lowAxis) p.highAxis) :
          Matrices.ComplexMatrix2)
        (U (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.highAxis) p.lowAxis) :
          Matrices.ComplexMatrix2)
        (U (InfiniteLattice.Link.forwardFrom p.corner p.highAxis) : Matrices.ComplexMatrix2) := by
  unfold wilsonLoopAction
  rw [← coe_inv_eq_conjTranspose, ← coe_inv_eq_conjTranspose]
  have hb := trace_action_mem (InfiniteLattice.faceHolonomy U p)
  have e : ((U (InfiniteLattice.Link.forwardFrom p.corner p.lowAxis) : Matrices.ComplexMatrix2) *
      (U (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.lowAxis) p.highAxis) :
        Matrices.ComplexMatrix2) *
      (((U (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.highAxis) p.lowAxis))⁻¹ :
        Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) *
      (((U (InfiniteLattice.Link.forwardFrom p.corner p.highAxis))⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
        Matrices.ComplexMatrix2)) =
      (InfiniteLattice.faceHolonomy U p : Matrices.ComplexMatrix2) := rfl
  rw [e, clampAction_of_mem hb.1 hb.2]
  rfl
private theorem quaternionToMatrix_star (q : ℍ[ℝ]) :
    SoftAverages.quaternionToMatrix (star q) = (SoftAverages.quaternionToMatrix q).conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [SoftAverages.quaternionToMatrix, Matrix.conjTranspose_apply]
private theorem re_trace_quaternionToMatrix (q : ℍ[ℝ]) :
    (Matrices.ComplexMatrix2.fullTrace (SoftAverages.quaternionToMatrix q)).re = 2 * q.re := by
  simp [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_fin_two, SoftAverages.quaternionToMatrix]
  ring
private abbrev unitMatrix (g : BlockAverages.UnitQuaternion) : Matrices.ComplexMatrix2 :=
  SoftAverages.quaternionToMatrix (g : ℍ[ℝ])
private theorem re_mem_Icc (g : BlockAverages.UnitQuaternion) : -1 ≤ (g : ℍ[ℝ]).re ∧ (g : ℍ[ℝ]).re ≤ 1 := by
  have h2 : star (g : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := (Unitary.mem_iff.mp g.2).1
  rw [Quaternion.star_mul_self] at h2
  have h := congrArg (fun z : ℍ[ℝ] => z.re) h2
  simp only [Quaternion.re_coe, Quaternion.re_one] at h
  rw [Quaternion.normSq_def'] at h
  constructor <;> nlinarith [sq_nonneg (g : ℍ[ℝ]).imI, sq_nonneg (g : ℍ[ℝ]).imJ, sq_nonneg (g : ℍ[ℝ]).imK,
    sq_nonneg ((g : ℍ[ℝ]).re - 1), sq_nonneg ((g : ℍ[ℝ]).re + 1)]
private theorem plaquetteEnergy_eq_wilsonLoopAction {n : ℕ} (W : TorusFields.TorusField n)
    (x : TorusFields.TorusSite n) (μ ν : Fin 4) :
    TorusFields.plaquetteEnergy W x μ ν =
      wilsonLoopAction (unitMatrix (W x μ)) (unitMatrix (W (x + TorusFields.unitStep n μ) ν))
        (unitMatrix (W (x + TorusFields.unitStep n ν) μ)) (unitMatrix (W x ν)) := by
  unfold wilsonLoopAction
  have hinv : ∀ g : BlockAverages.UnitQuaternion, (unitMatrix g).conjTranspose = unitMatrix g⁻¹ :=
    fun g => (quaternionToMatrix_star _).symm
  rw [hinv, hinv]
  have e : unitMatrix (W x μ) * unitMatrix (W (x + TorusFields.unitStep n μ) ν) *
      unitMatrix (W (x + TorusFields.unitStep n ν) μ)⁻¹ * unitMatrix (W x ν)⁻¹ =
      SoftAverages.quaternionToMatrix ((TorusFields.holonomy W x μ ν : BlockAverages.UnitQuaternion) : ℍ[ℝ]) := by
    simp only [TorusFields.holonomy, unitMatrix, ← SoftAverages.quaternionToMatrix_mul]
    rfl
  rw [e, re_trace_quaternionToMatrix]
  have hb := re_mem_Icc (TorusFields.holonomy W x μ ν)
  rw [clampAction_of_mem (by linarith [hb.2]) (by linarith [hb.1])]
  unfold TorusFields.plaquetteEnergy
  ring
end Action
section Index
private abbrev OrderedAxes : Type := {q : Fin 4 × Fin 4 // q.1 < q.2}
private def cubeIndices (M : ℕ) : Finset ((Fin 4 → ℤ) × OrderedAxes) :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(M : ℤ)) M) ×ˢ Finset.univ
private theorem mem_cubeIndices {M : ℕ} {j : (Fin 4 → ℤ) × OrderedAxes} :
    j ∈ cubeIndices M ↔ ∀ i, |j.1 i| ≤ (M : ℤ) := by
  simp [cubeIndices, Fintype.mem_piFinset, abs_le]
private def linkValue {R : ℕ} (v : TorusLimits.WindowValuation R) (b : (Fin 4 → ℤ) × Fin 4) :
    Matrices.ComplexMatrix2 :=
  open Classical in if hb : TorusFields.BondOffsetInBox R b then v ⟨b, hb⟩ else 1
private theorem continuous_linkValue {R : ℕ} (b : (Fin 4 → ℤ) × Fin 4) :
    Continuous fun v : TorusLimits.WindowValuation R => linkValue v b := by
  unfold linkValue
  by_cases hb : TorusFields.BondOffsetInBox R b
  · simp only [hb, dite_true]
    exact continuous_apply _
  · simp only [hb, dite_false]
    exact continuous_const
private def windowAction {R : ℕ} (v : TorusLimits.WindowValuation R) (j : (Fin 4 → ℤ) × OrderedAxes) : ℝ :=
  wilsonLoopAction (linkValue v (j.1, j.2.1.1)) (linkValue v (j.1 + Pi.single j.2.1.1 1, j.2.1.2))
    (linkValue v (j.1 + Pi.single j.2.1.2 1, j.2.1.1)) (linkValue v (j.1, j.2.1.2))
private def cubeSum {R : ℕ} (M : ℕ) (F : (Fin 4 → ℤ) × OrderedAxes → ℝ) (v : TorusLimits.WindowValuation R) : ℝ :=
  ∑ j ∈ cubeIndices M, F j * windowAction v j
private theorem continuous_cubeSum {R M : ℕ} (F : (Fin 4 → ℤ) × OrderedAxes → ℝ) :
    Continuous (cubeSum (R := R) M F) := by
  unfold cubeSum
  refine continuous_finset_sum _ fun j _ => continuous_const.mul ?_
  exact continuous_wilsonLoopAction (continuous_linkValue _) (continuous_linkValue _) (continuous_linkValue _)
    (continuous_linkValue _)
private theorem isBounded_cubeSum {R M : ℕ} (F : (Fin 4 → ℤ) × OrderedAxes → ℝ) :
    TorusLimits.IsBoundedWindowObservable (cubeSum (R := R) M F) where
  measurable := by
    let _ : MeasurableSpace (TorusLimits.WindowValuation R) := borel _
    have : BorelSpace (TorusLimits.WindowValuation R) := ⟨rfl⟩
    exact (continuous_cubeSum F).measurable
  bounded := by
    refine ⟨∑ j ∈ cubeIndices M, |F j| * 2, fun v => ?_⟩
    unfold cubeSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_clampAction_le _) (abs_nonneg _)
private theorem links_mem_window {M : ℕ} {j : (Fin 4 → ℤ) × OrderedAxes} (hj : j ∈ cubeIndices M) :
    TorusFields.BondOffsetInBox (M + 2) (j.1, j.2.1.1) ∧
      TorusFields.BondOffsetInBox (M + 2) (j.1 + Pi.single j.2.1.1 1, j.2.1.2) ∧
      TorusFields.BondOffsetInBox (M + 2) (j.1 + Pi.single j.2.1.2 1, j.2.1.1) ∧
      TorusFields.BondOffsetInBox (M + 2) (j.1, j.2.1.2) := by
  have h := mem_cubeIndices.1 hj
  have hs : ∀ (μ i : Fin 4), |(Pi.single μ 1 : Fin 4 → ℤ) i| ≤ 1 := by
    intro μ i
    by_cases e : i = μ
    · subst e; simp
    · simp [Pi.single_eq_of_ne e]
  have h1 : ∀ (μ : Fin 4), TorusFields.OffsetInBox (M + 2) (j.1 + Pi.single μ 1) := by
    intro μ i
    have := abs_add_le (j.1 i) ((Pi.single μ 1 : Fin 4 → ℤ) i)
    have := h i
    have := hs μ i
    simp only [Pi.add_apply]
    push_cast
    omega
  have h0 : TorusFields.OffsetInBox (M + 2) j.1 := by
    intro i
    have := h i
    push_cast
    omega
  have h2 : ∀ (μ ν : Fin 4), TorusFields.OffsetInBox (M + 2) (j.1 + Pi.single μ 1 + Pi.single ν 1) := by
    intro μ ν i
    have := abs_add_le (j.1 i + (Pi.single μ 1 : Fin 4 → ℤ) i) ((Pi.single ν 1 : Fin 4 → ℤ) i)
    have := abs_add_le (j.1 i) ((Pi.single μ 1 : Fin 4 → ℤ) i)
    have := h i
    have := hs μ i
    have := hs ν i
    simp only [Pi.add_apply]
    push_cast
    omega
  exact ⟨⟨h0, h1 _⟩, ⟨h1 _, h2 _ _⟩, ⟨h1 _, h2 _ _⟩, ⟨h0, h1 _⟩⟩
private theorem cubeSum_eq {M : ℕ} (F : (Fin 4 → ℤ) × OrderedAxes → ℝ)
    (u : (Fin 4 → ℤ) × Fin 4 → Matrices.ComplexMatrix2) :
    cubeSum (R := M + 2) M F (fun b => u b.1) = ∑ j ∈ cubeIndices M, F j *
      wilsonLoopAction (u (j.1, j.2.1.1)) (u (j.1 + Pi.single j.2.1.1 1, j.2.1.2))
        (u (j.1 + Pi.single j.2.1.2 1, j.2.1.1)) (u (j.1, j.2.1.2)) := by
  unfold cubeSum
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨h1, h2, h3, h4⟩ := links_mem_window hj
  simp only [windowAction, linkValue, h1, h2, h3, h4, dite_true]
end Index
section Lattice
variable {a : ℝ}
private theorem latticePointOfInt_add_axisStep (h : Fin 4 → ℤ) (μ : Fin 4) :
    TorusLimits.latticePointOfInt a h + InfiniteLattice.axisStep a μ =
      TorusLimits.latticePointOfInt a (h + Pi.single μ 1) := by apply _root_.YangMills.SharedProofs.p61591 <;> assumption
private theorem latticePointOfInt_injective (ha : a ≠ 0) : Function.Injective (TorusLimits.latticePointOfInt a) := by
  intro h h' e
  funext i
  have := congrFun (congrArg Subtype.val e) i
  have e2 : (h i : ℝ) * a = (h' i : ℝ) * a := this
  exact_mod_cast mul_right_cancel₀ ha e2
private def latticeFace (a : ℝ) (j : (Fin 4 → ℤ) × OrderedAxes) : InfiniteLattice.ElementaryPlaquette a :=
  ⟨TorusLimits.latticePointOfInt a j.1, j.2.1.1, j.2.1.2, j.2.2⟩
private def faceCenter (a : ℝ) (j : (Fin 4 → ℤ) × OrderedAxes) (i : Fin 4) : ℝ :=
  a * ((j.1 i : ℝ) + (if i = j.2.1.1 then 1 / 2 else 0) + (if i = j.2.1.2 then 1 / 2 else 0))
private theorem center_latticeFace (j : (Fin 4 → ℤ) × OrderedAxes) :
    (latticeFace a j).center = faceCenter a j := by
  funext i
  show (j.1 i : ℝ) * a + (Pi.single j.2.1.1 (a / 2) : Fin 4 → ℝ) i + (Pi.single j.2.1.2 (a / 2) : Fin 4 → ℝ) i = _
  unfold faceCenter
  by_cases e1 : i = j.2.1.1 <;> by_cases e2 : i = j.2.1.2 <;>
    simp only [e1, e2, Pi.single_apply, if_true, if_false] <;>
    first
      | (split_ifs <;> ring)
      | ring
open Classical in
private theorem smearedEnergy_eq_evalOnField (ha : 0 < a) {M : ℕ} {f : (Fin 4 → ℝ) → ℝ}
    (hM : ∀ x, f x ≠ 0 → ∀ i, |x i| / a + 2 ≤ M) (U : InfiniteLattice.GaugeField a) :
    InfiniteLattice.smearedEnergy f U =
      TorusLimits.evalOnField (cubeSum (R := M + 2) M fun j => f (faceCenter a j)) U := by
  have hinj : Function.Injective (latticeFace a) := by
    rintro ⟨h, q⟩ ⟨h', q'⟩ e
    have e1 := congrArg InfiniteLattice.ElementaryPlaquette.corner e
    have e2 := congrArg InfiniteLattice.ElementaryPlaquette.lowAxis e
    have e3 := congrArg InfiniteLattice.ElementaryPlaquette.highAxis e
    have hh : h = h' := latticePointOfInt_injective ha.ne' e1
    have hq : q = q' := Subtype.ext (Prod.ext e2 e3)
    rw [hh, hq]
  have hsub : Function.support (fun p : InfiniteLattice.ElementaryPlaquette a =>
      InfiniteLattice.faceEnergy U p • f p.center) ⊆ ↑((cubeIndices M).image (latticeFace a)) := by
    intro p hp
    have hf : f p.center ≠ 0 := fun h0 => hp (by simp [h0])
    obtain ⟨n, hn⟩ := p.corner.2
    have hbase : p.corner = TorusLimits.latticePointOfInt a n := Subtype.ext (funext hn)
    have hp' : p = latticeFace a (n, ⟨(p.lowAxis, p.highAxis), p.lowAxis_lt_highAxis⟩) := by
      ext1
      · exact hbase
      · rfl
      · rfl
    rw [hp'] at hf
    rw [center_latticeFace] at hf
    have hmem : (n, (⟨(p.lowAxis, p.highAxis), p.lowAxis_lt_highAxis⟩ : OrderedAxes)) ∈ cubeIndices M := by
      refine mem_cubeIndices.2 fun i => ?_
      have h1 := hM _ hf i
      have h2 : |faceCenter a (n, ⟨(p.lowAxis, p.highAxis), p.lowAxis_lt_highAxis⟩) i| / a =
          |(n i : ℝ) + (if i = p.lowAxis then 1 / 2 else 0) + (if i = p.highAxis then 1 / 2 else 0)| := by
        unfold faceCenter
        rw [abs_mul, abs_of_pos ha]
        field_simp
      rw [h2] at h1
      have h3 : |(n i : ℝ)| ≤
          |(n i : ℝ) + (if i = p.lowAxis then 1 / 2 else 0) + (if i = p.highAxis then 1 / 2 else 0)| + 1 := by
        have e1 : |(if i = p.lowAxis then (1 / 2 : ℝ) else 0)| ≤ 1 / 2 := by split_ifs <;> norm_num
        have e2 : |(if i = p.highAxis then (1 / 2 : ℝ) else 0)| ≤ 1 / 2 := by split_ifs <;> norm_num
        obtain ⟨a1, a2⟩ := abs_le.1 e1
        obtain ⟨b1, b2⟩ := abs_le.1 e2
        rw [abs_le]
        constructor <;> [skip; skip] <;>
          cases abs_cases ((n i : ℝ) + (if i = p.lowAxis then 1 / 2 else 0) +
            (if i = p.highAxis then 1 / 2 else 0)) <;> linarith
      have h4 : ((|n i| : ℤ) : ℝ) ≤ M := by
        rw [Int.cast_abs]
        linarith
      exact_mod_cast h4
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, hmem, hp'.symm⟩)
  unfold InfiniteLattice.smearedEnergy
  rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_image fun x _ y _ e => hinj e]
  unfold TorusLimits.evalOnField
  have := cubeSum_eq (M := M) (fun j => f (faceCenter a j))
    (fun b => ((U (InfiniteLattice.Link.forwardFrom (TorusLimits.latticePointOfInt a b.1) b.2) :
      Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2))
  refine Eq.trans ?_ this.symm
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [center_latticeFace, smul_eq_mul, mul_comm, faceEnergy_eq_wilsonLoopAction]
  simp only [latticeFace, latticePointOfInt_add_axisStep]
end Lattice
section Torus
variable {N : ℕ} [NeZero N]
private def torusFace (N : ℕ) (j : (Fin 4 → ℤ) × OrderedAxes) : TorusFields.TorusPlaquette N :=
  (TorusFields.siteOfInt j.1, j.2.1.1, j.2.1.2)
private theorem siteOfInt_add_single (h : Fin 4 → ℤ) (μ : Fin 4) :
    (TorusFields.siteOfInt (h + Pi.single μ 1) : TorusFields.TorusSite N) =
      TorusFields.siteOfInt h + TorusFields.unitStep N μ := by apply _root_.YangMills.SharedProofs.p5434 <;> assumption
private theorem siteOfInt_injOn {M : ℕ} (hN : 2 * M < N) {h h' : Fin 4 → ℤ} (hh : ∀ i, |h i| ≤ (M : ℤ))
    (hh' : ∀ i, |h' i| ≤ (M : ℤ))
    (e : (TorusFields.siteOfInt h : TorusFields.TorusSite N) = TorusFields.siteOfInt h') : h = h' := by
  funext i
  have e1 : ((h i : ℤ) : ZMod N) = ((h' i : ℤ) : ZMod N) := congrFun e i
  have hd : (N : ℤ) ∣ h' i - h i := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 e1
  have hs : |h' i - h i| < (N : ℤ) := by
    have := abs_sub (h' i) (h i)
    have := hh i
    have := hh' i
    omega
  have := Int.eq_zero_of_abs_lt_dvd hd hs
  omega
private def halfSteps (p : TorusFields.TorusPlaquette N) (i : Fin 4) : ℝ :=
  (if i = p.2.1 then 1 / 2 else 0) + (if i = p.2.2 then 1 / 2 else 0)
private theorem halfSteps_mem (p : TorusFields.TorusPlaquette N) (i : Fin 4) :
    0 ≤ halfSteps p i ∧ halfSteps p i ≤ 1 := by
  unfold halfSteps
  split_ifs <;> norm_num
private theorem displacement_eq (L K : ℕ) (p : TorusFields.TorusPlaquette N) (i : Fin 4) :
    TwoPointLaw.displacementToPlaquette (TorusFields.siteOfInt fun k => (L : ℤ) ^ K * (0 : Fin 4 → ℤ) k) p i =
      ((p.1 i).val : ℝ) + halfSteps p i - N * round ((((p.1 i).val : ℝ) + halfSteps p i) / N) := by
  have h0 : ((TorusFields.siteOfInt fun k => (L : ℤ) ^ K * (0 : Fin 4 → ℤ) k : TorusFields.TorusSite N) i).val = 0 := by
    simp [TorusFields.siteOfInt]
  unfold TwoPointLaw.displacementToPlaquette halfSteps
  simp only [h0, Nat.cast_zero, sub_zero]
  ring_nf
private theorem displacement_torusFace (L K : ℕ) {M : ℕ} (hN : 4 * M + 8 ≤ N) {j : (Fin 4 → ℤ) × OrderedAxes}
    (hj : ∀ i, |j.1 i| ≤ (M : ℤ)) (i : Fin 4) :
    TwoPointLaw.displacementToPlaquette (TorusFields.siteOfInt fun k => (L : ℤ) ^ K * (0 : Fin 4 → ℤ) k)
      (torusFace N j) i = (j.1 i : ℝ) + halfSteps (torusFace N j) i := by
  have hNr : (4 : ℝ) * M + 8 ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    linarith
  rw [displacement_eq]
  obtain ⟨h0, h1⟩ := halfSteps_mem (torusFace N j) i
  set t : ℝ := (j.1 i : ℝ) + halfSteps (torusFace N j) i with ht
  set k : ℤ := j.1 i / (N : ℤ) with hk
  have hval : (((torusFace N j).1 i).val : ℝ) = (j.1 i : ℝ) - N * k := by
    have e1 : ((((j.1 i : ℤ) : ZMod N).val : ℕ) : ℤ) = j.1 i % (N : ℤ) := ZMod.val_intCast _
    have e2 : j.1 i % (N : ℤ) = j.1 i - N * k := by
      rw [Int.emod_def]
    have e3 := congrArg (fun z : ℤ => (z : ℝ)) (e1.trans e2)
    simp only [Int.cast_natCast] at e3
    push_cast at e3
    exact e3
  have hb : (((torusFace N j).1 i).val : ℝ) + halfSteps (torusFace N j) i = t - N * k := by
    rw [hval, ht]
    ring
  have hr : round ((t - N * k) / N) = -k := by
    have e : (t - N * k) / N = t / N + ((-k : ℤ) : ℝ) := by
      push_cast
      field_simp
      ring
    rw [e, round_add_intCast]
    have hz : round (t / N) = 0 := by
      rw [round_eq_zero_iff]
      have habs : |(j.1 i : ℝ)| ≤ M := by
        have := hj i
        exact_mod_cast this
      obtain ⟨a1, a2⟩ := abs_le.1 habs
      constructor
      · rw [le_div_iff₀ hNpos]
        linarith
      · rw [div_lt_iff₀ hNpos]
        linarith
    rw [hz, zero_add]
  rw [hb, hr]
  push_cast
  ring
private theorem exists_torusFace (L K : ℕ) {M : ℕ} (p : TorusFields.TorusPlaquette N) (hp : p.2.1 < p.2.2)
    (hb : ∀ i, |TwoPointLaw.displacementToPlaquette
      (TorusFields.siteOfInt fun k => (L : ℤ) ^ K * (0 : Fin 4 → ℤ) k) p i| + 2 ≤ M) :
    ∃ j ∈ cubeIndices M, torusFace N j = p := by
  set r : Fin 4 → ℤ := fun i => round ((((p.1 i).val : ℝ) + halfSteps p i) / N) with hr
  set h : Fin 4 → ℤ := fun i => ((p.1 i).val : ℤ) - N * r i with hh
  refine ⟨(h, ⟨(p.2.1, p.2.2), hp⟩), mem_cubeIndices.2 fun i => ?_, ?_⟩
  · have h1 := hb i
    rw [displacement_eq] at h1
    obtain ⟨h2, h3⟩ := halfSteps_mem p i
    have e : ((p.1 i).val : ℝ) + halfSteps p i - N * round ((((p.1 i).val : ℝ) + halfSteps p i) / N) =
        (h i : ℝ) + halfSteps p i := by
      simp only [hh, hr]
      push_cast
      ring
    rw [e] at h1
    have h4 : |(h i : ℝ)| ≤ |(h i : ℝ) + halfSteps p i| + 1 := by
      rw [abs_le]
      constructor <;> cases abs_cases ((h i : ℝ) + halfSteps p i) <;> linarith
    have h5 : ((|h i| : ℤ) : ℝ) ≤ M := by
      rw [Int.cast_abs]
      linarith
    exact_mod_cast h5
  · refine Prod.ext (funext fun i => ?_) rfl
    show ((h i : ℤ) : ZMod N) = p.1 i
    simp [hh]
private theorem energy_torusFace (W : TorusFields.TorusField N) (j : (Fin 4 → ℤ) × OrderedAxes) :
    WeightedResponses.plaquetteEnergyOf W (torusFace N j) =
      wilsonLoopAction (unitMatrix (W (TorusFields.siteOfInt j.1) j.2.1.1))
        (unitMatrix (W (TorusFields.siteOfInt (j.1 + Pi.single j.2.1.1 1)) j.2.1.2))
        (unitMatrix (W (TorusFields.siteOfInt (j.1 + Pi.single j.2.1.2 1)) j.2.1.1))
        (unitMatrix (W (TorusFields.siteOfInt j.1) j.2.1.2)) := by
  rw [siteOfInt_add_single, siteOfInt_add_single]
  exact plaquetteEnergy_eq_wilsonLoopAction W _ _ _
private theorem curvatureObservable_eq_evalOnTorus (L K : ℕ) {a : ℝ} (ha : 0 < a) (hca : a = ((L : ℝ) ^ K)⁻¹)
    {M : ℕ} {f : (Fin 4 → ℝ) → ℝ} (hM : ∀ x, f x ≠ 0 → ∀ i, |x i| / a + 2 ≤ M) (hN : 4 * M + 8 ≤ N)
    (W : TorusFields.TorusField N) :
    WeightedResponses.curvatureObservable (TwoPointLaw.scaledTestWeight L K K f 0 N) W =
      TorusLimits.evalOnTorus (cubeSum (R := M + 2) M fun j => f (faceCenter a j)) W := by
  have hc : (0 : ℝ) < (L : ℝ) ^ K := by
    rw [hca] at ha
    exact inv_pos.1 ha
  have hwt : ∀ p : TorusFields.TorusPlaquette N, TwoPointLaw.scaledTestWeight L K K f 0 N p =
      f fun i => a * TwoPointLaw.displacementToPlaquette
        (TorusFields.siteOfInt fun k => (L : ℤ) ^ K * (0 : Fin 4 → ℤ) k) p i := by
    intro p
    unfold TwoPointLaw.scaledTestWeight
    congr 1
    funext i
    rw [hca]
    field_simp
  have hN2 : 2 * M < N := by omega
  have hinj : Set.InjOn (torusFace N) (cubeIndices M : Set ((Fin 4 → ℤ) × OrderedAxes)) := by
    rintro ⟨h, q⟩ hj ⟨h', q'⟩ hj' e
    have e1 : (TorusFields.siteOfInt h : TorusFields.TorusSite N) = TorusFields.siteOfInt h' := congrArg Prod.fst e
    have e2 : q.1.1 = q'.1.1 := congrArg (fun p : TorusFields.TorusPlaquette N => p.2.1) e
    have e3 : q.1.2 = q'.1.2 := congrArg (fun p : TorusFields.TorusPlaquette N => p.2.2) e
    have hh : h = h' := siteOfInt_injOn hN2 (mem_cubeIndices.1 hj) (mem_cubeIndices.1 hj') e1
    have hq : q = q' := Subtype.ext (Prod.ext e2 e3)
    rw [hh, hq]
  have hval : ∀ j ∈ cubeIndices M, TwoPointLaw.scaledTestWeight L K K f 0 N (torusFace N j) = f (faceCenter a j) := by
    intro j hj
    rw [hwt]
    congr 1
    funext i
    rw [displacement_torusFace L K hN (mem_cubeIndices.1 hj) i]
    have hh : halfSteps (torusFace N j) i =
        (if i = j.2.1.1 then (1 / 2 : ℝ) else 0) + (if i = j.2.1.2 then (1 / 2 : ℝ) else 0) := rfl
    rw [hh]
    unfold faceCenter
    ring
  unfold WeightedResponses.curvatureObservable TorusLimits.evalOnTorus
  have hbox := cubeSum_eq (M := M) (fun j => f (faceCenter a j))
    (fun b => unitMatrix (W (TorusFields.siteOfInt b.1) b.2))
  refine Eq.trans ?_ hbox.symm
  have hsub : (cubeIndices M).image (torusFace N) ⊆ TorusFields.plaquettesIn Finset.univ := by
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hp
    simp only [TorusFields.plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and, implies_true, and_true]
    exact j.2.2
  rw [← Finset.sum_subset hsub, Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [hval j hj, energy_torusFace]
  · intro p hp hnot
    have hp2 : p.2.1 < p.2.2 := by
      simp only [TorusFields.plaquettesIn, Finset.mem_filter] at hp
      exact hp.2.1
    by_contra hne
    have hw : TwoPointLaw.scaledTestWeight L K K f 0 N p ≠ 0 := left_ne_zero_of_mul hne
    rw [hwt] at hw
    have hb : ∀ i, |TwoPointLaw.displacementToPlaquette
        (TorusFields.siteOfInt fun k => (L : ℤ) ^ K * (0 : Fin 4 → ℤ) k) p i| + 2 ≤ M := by
      intro i
      have := hM _ hw i
      rw [abs_mul, abs_of_pos ha] at this
      have e : a * |TwoPointLaw.displacementToPlaquette
          (TorusFields.siteOfInt fun k => (L : ℤ) ^ K * (0 : Fin 4 → ℤ) k) p i| / a =
          |TwoPointLaw.displacementToPlaquette
            (TorusFields.siteOfInt fun k => (L : ℤ) ^ K * (0 : Fin 4 → ℤ) k) p i| := by
        field_simp
      rwa [e] at this
    obtain ⟨j, hj, e⟩ := exists_torusFace L K p hp2 hb
    exact hnot (Finset.mem_image.2 ⟨j, hj, e⟩)
end Torus
private theorem measurable_evalOnField {R : ℕ} {a : ℝ} {G : TorusLimits.WindowValuation R → ℝ}
    (hG : TorusLimits.IsBoundedWindowObservable G) :
    Measurable (TorusLimits.evalOnField G : InfiniteLattice.GaugeField a → ℝ) := by
  have hc : Continuous fun U : InfiniteLattice.GaugeField a => fun b : TorusLimits.WindowLink R =>
      ((U (InfiniteLattice.Link.forwardFrom (TorusLimits.latticePointOfInt a b.1.1) b.1.2) :
        Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) := by
    refine continuous_pi fun b => continuous_subtype_val.comp ?_
    exact (continuous_apply _).comp continuous_subtype_val
  let _ : MeasurableSpace (TorusLimits.WindowValuation R) := borel _
  have : BorelSpace (TorusLimits.WindowValuation R) := ⟨rfl⟩
  exact hG.measurable.comp hc.measurable
abbrev _root_.YangMills.SharedProofs.p62357 := @measurable_evalOnField
theorem observableReadsWindow : observableReadsWindowStatement := by
  intro L K _ f _ hL hf
  have hca : PeriodicLattice.meshSize L (K : ℤ) = ((L : ℝ) ^ K)⁻¹ := by
    simp [PeriodicLattice.meshSize, zpow_neg]
  have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) := by
    rw [hca]
    positivity
  obtain ⟨Bd, hBd⟩ := IsCompact.exists_bound_of_continuousOn (f := fun x : Fin 4 → ℝ => x) hf
    continuous_id.continuousOn
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ⌈Bd / PeriodicLattice.meshSize L (K : ℤ)⌉₊ + 2 := ⟨_, rfl⟩
  have hM : ∀ x, f x ≠ 0 → ∀ i, |x i| / PeriodicLattice.meshSize L (K : ℤ) + 2 ≤ M := by
    intro x hx i
    have h1 : |x i| ≤ Bd := by
      have := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at this
      exact this.trans (hBd x (subset_tsupport _ hx))
    have h2 := Nat.le_ceil (Bd / PeriodicLattice.meshSize L (K : ℤ))
    have h3 : |x i| / PeriodicLattice.meshSize L (K : ℤ) ≤ Bd / PeriodicLattice.meshSize L (K : ℤ) :=
      div_le_div_of_nonneg_right h1 ha.le
    rw [hMdef]
    push_cast
    linarith
  have hG := isBounded_cubeSum (R := M + 2) (M := M) fun j => f (faceCenter (PeriodicLattice.meshSize L (K : ℤ)) j)
  refine ⟨M + 2, cubeSum M fun j => f (faceCenter (PeriodicLattice.meshSize L (K : ℤ)) j), hG,
    measurable_evalOnField hG, fun U => smearedEnergy_eq_evalOnField ha hM U, ?_⟩
  filter_upwards [eventually_ge_atTop (4 * M + 8)] with m hm W
  have hside : 4 * M + 8 ≤ WeightedResponses.fineSide L K (2 * L ^ m) := by
    have h1 : m < L ^ m := Nat.lt_pow_self hL
    have h2 : 1 ≤ L ^ K := Nat.one_le_pow _ _ (by omega)
    rw [WeightedResponses.fineSide_eq]
    nlinarith
  exact curvatureObservable_eq_evalOnTorus L K ha hca hM hside W
end YangMills.Construction.HullsInEveryVolume
end

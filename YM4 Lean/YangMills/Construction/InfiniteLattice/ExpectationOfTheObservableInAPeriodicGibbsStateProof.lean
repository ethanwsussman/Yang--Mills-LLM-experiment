import YangMills.Construction.InfiniteLattice.CoveringOnSitesBondsPlaquettesAndCornersProof
import YangMills.Construction.InfiniteLattice.CutoffLattice
import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import YangMills.Construction.ReflectionPositivity.LatticeFormulaForTheScalarProductProof
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenCopiesAtEveryDatumProof
import YangMills.Construction.InfiniteLattice.ExpectationOfTheObservableInAPeriodicGibbsState
import YangMills.Construction.InfiniteLattice.FaceEnergyUnderProbability
import YangMills.Construction.InfiniteLattice.UnitLatticeIsometriesAndPlaquettesProof
import YangMills.Construction.LawInAState.FromSixteenCopiesToOneBoxProof
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
import YangMills.Construction.VolumeTransfer.InvarianceOfPeriodicGibbsStates
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicExpectation
variable {a : ℝ}
theorem exists_perm_map_pair {μ κ μ' κ' : Fin 4} (h : μ ≠ κ) (h' : μ' ≠ κ') :
    ∃ ς : Equiv.Perm (Fin 4), ς μ = μ' ∧ ς κ = κ' := by apply _root_.YangMills.Construction.InfiniteLattice.UnitSymmetriesAndFaces.exists_perm_apply_pair <;> assumption
def coordPermMap (ς : Equiv.Perm (Fin 4)) : AmbientSpace →ₗ[ℝ] AmbientSpace :=
  frameLinearMap (ς⁻¹, 1)
theorem coordPermMap_apply (ς : Equiv.Perm (Fin 4)) (x : AmbientSpace) (μ : Fin 4) :
    coordPermMap ς x μ = x (ς⁻¹ μ) := by
  simp [coordPermMap, frameLinearMap, PeriodicLattice.SignedFrame.actOnVector]
theorem coordPermMap_axisStep (ς : Equiv.Perm (Fin 4)) (μ : Fin 4) :
    coordPermMap ς ((axisStep a μ : LatticePoint a) : AmbientSpace) =
      ((axisStep a (ς μ) : LatticePoint a) : AmbientSpace) := by
  funext ν
  rw [coordPermMap_apply]
  by_cases h : ν = ς μ
  · subst h
    simp [axisStep]
  · have h' : ς.symm ν ≠ μ := fun hc => h (by simp [← hc])
    simp [axisStep, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
theorem coordPermMap_mem_latticeSubgroup (ς : Equiv.Perm (Fin 4)) {x : AmbientSpace}
    (hx : x ∈ latticeSubgroup a) : coordPermMap ς x ∈ latticeSubgroup a := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨fun μ => n (ς⁻¹ μ), fun μ => by rw [coordPermMap_apply, hn]⟩
def motionBetween (ς : Equiv.Perm (Fin 4)) (x x' : LatticePoint a) : latticeMotions a :=
  ⟨fun y => coordPermMap ς y + ((x' : AmbientSpace) - coordPermMap ς (x : AmbientSpace)),
    coordPermMap ς, frameLinearMap_mem_hypercubicGroup _,
    (x' : AmbientSpace) - coordPermMap ς (x : AmbientSpace),
    sub_mem x'.2 (coordPermMap_mem_latticeSubgroup ς x.2), fun _ => rfl⟩
theorem pointMap_motionBetween_self (ς : Equiv.Perm (Fin 4)) (x x' : LatticePoint a) :
    (latticeMotionSymmetry (motionBetween ς x x')).pointMap x = x' := by
  apply Subtype.ext
  change coordPermMap ς (x : AmbientSpace) +
    ((x' : AmbientSpace) - coordPermMap ς (x : AmbientSpace)) = x'
  abel
theorem pointMap_motionBetween_add_axisStep (ς : Equiv.Perm (Fin 4)) (x x' y : LatticePoint a)
    (μ : Fin 4) :
    (latticeMotionSymmetry (motionBetween ς x x')).pointMap (y + axisStep a μ) =
      (latticeMotionSymmetry (motionBetween ς x x')).pointMap y + axisStep a (ς μ) := by
  apply Subtype.ext
  change coordPermMap ς ((y : AmbientSpace) + ((axisStep a μ : LatticePoint a) : AmbientSpace)) +
      ((x' : AmbientSpace) - coordPermMap ς (x : AmbientSpace)) =
    coordPermMap ς (y : AmbientSpace) + ((x' : AmbientSpace) - coordPermMap ς (x : AmbientSpace)) +
      ((axisStep a (ς μ) : LatticePoint a) : AmbientSpace)
  rw [map_add, coordPermMap_axisStep]
  abel
theorem exists_motion_carrying (p q : ElementaryPlaquette a) :
    ∃ r : latticeMotions a,
      (latticeMotionSymmetry r).pointMap p.corner = q.corner ∧
      (∀ y, (latticeMotionSymmetry r).pointMap (y + axisStep a p.lowAxis) =
        (latticeMotionSymmetry r).pointMap y + axisStep a q.lowAxis) ∧
      ∀ y, (latticeMotionSymmetry r).pointMap (y + axisStep a p.highAxis) =
        (latticeMotionSymmetry r).pointMap y + axisStep a q.highAxis := by
  obtain ⟨ς, h1, h2⟩ := exists_perm_map_pair (ne_of_lt p.lowAxis_lt_highAxis)
    (ne_of_lt q.lowAxis_lt_highAxis)
  refine ⟨motionBetween ς p.corner q.corner, pointMap_motionBetween_self _ _ _,
    fun y => ?_, fun y => ?_⟩
  · rw [pointMap_motionBetween_add_axisStep, h1]
  · rw [pointMap_motionBetween_add_axisStep, h2]
theorem image_cornerSet (s : LatticeSymmetry a) {p q : ElementaryPlaquette a}
    (hb : s.pointMap p.corner = q.corner)
    (h1 : ∀ y, s.pointMap (y + axisStep a p.lowAxis) = s.pointMap y + axisStep a q.lowAxis)
    (h2 : ∀ y, s.pointMap (y + axisStep a p.highAxis) = s.pointMap y + axisStep a q.highAxis) :
    s.pointMap '' p.cornerSet = q.cornerSet := by
  simp only [ElementaryPlaquette.cornerSet, image_insert_eq, image_singleton, h1, h2, hb]
theorem faceEnergy_pullbackField (s : LatticeSymmetry a) {p q : ElementaryPlaquette a}
    (hb : s.pointMap p.corner = q.corner)
    (h1 : ∀ y, s.pointMap (y + axisStep a p.lowAxis) = s.pointMap y + axisStep a q.lowAxis)
    (h2 : ∀ y, s.pointMap (y + axisStep a p.highAxis) = s.pointMap y + axisStep a q.highAxis)
    (U : GaugeField a) :
    faceEnergy (s.pullbackField U) p = faceEnergy U q := by
  have e : ∀ (x : LatticePoint a) (μ μ' : Fin 4),
      (∀ y, s.pointMap (y + axisStep a μ) = s.pointMap y + axisStep a μ') →
        s.linkMap (Link.forwardFrom x μ) = Link.forwardFrom (s.pointMap x) μ' :=
    fun x μ μ' h => Link.ext rfl (h x)
  have hv : faceHolonomy (s.pullbackField U) p = faceHolonomy U q := by
    change U (s.linkMap _) * U (s.linkMap _) * (U (s.linkMap _))⁻¹ * (U (s.linkMap _))⁻¹ = _
    rw [e _ _ _ h1, e _ _ _ h2, e _ _ _ h1, e _ _ _ h2, h1, h2, hb]
    rfl
  unfold faceEnergy
  rw [hv]
def plaquetteEquivAxesPoint (a : ℝ) :
    ElementaryPlaquette a ≃ (Σ μ : Fin 4, ↥(Finset.Ioi μ)) × LatticePoint a where
  toFun p := (⟨p.lowAxis, ⟨p.highAxis, Finset.mem_Ioi.2 p.lowAxis_lt_highAxis⟩⟩, p.corner)
  invFun m := ⟨m.2, m.1.1, m.1.2.1, Finset.mem_Ioi.1 m.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem center_eq (p : ElementaryPlaquette a) :
    p.center = (p.corner : AmbientSpace) +
      (a / 2) • (Pi.single p.lowAxis 1 + Pi.single p.highAxis 1 : AmbientSpace) := by
  funext ν
  simp only [ElementaryPlaquette.center, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> ring
theorem finsum_faces_eq_sum_axes {F : AmbientSpace → ℝ}
    (hF : {p : ElementaryPlaquette a | F p.center ≠ 0}.Finite) :
    ∑ᶠ p : ElementaryPlaquette a, F p.center =
      ∑ μ : Fin 4, ∑ κ ∈ Finset.Ioi μ, ∑ᶠ x : LatticePoint a,
        F ((x : AmbientSpace) + (a / 2) • (Pi.single μ 1 + Pi.single κ 1 : AmbientSpace)) := by
  classical
  have h0 : ∑ᶠ p : ElementaryPlaquette a, F p.center =
      ∑ᶠ m, F ((plaquetteEquivAxesPoint a).symm m).center :=
    (finsum_comp_equiv (plaquetteEquivAxesPoint a).symm (f := fun p => F p.center)).symm
  have hfin : (Function.support
      fun m => F ((plaquetteEquivAxesPoint a).symm m).center).Finite := by
    refine (hF.image (plaquetteEquivAxesPoint a)).subset fun m hm => ?_
    exact ⟨(plaquetteEquivAxesPoint a).symm m, hm, by simp⟩
  rw [h0, finsum_curry _ hfin, finsum_eq_sum_of_fintype, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_coe_sort (Finset.Ioi μ)]
  refine Finset.sum_congr rfl fun κ _ => finsum_congr fun x => ?_
  rw [center_eq]
  rfl
theorem realRiemannSum_eq_ofReal (L K : ℕ) (F : AmbientSpace → ℝ) :
    realRiemannSum L K F =
      ((1 / 6 * ∑ μ : Fin 4, ∑ κ ∈ Finset.Ioi μ, refinedSpacing L K ^ 4 *
        ∑ᶠ x : LatticePoint (refinedSpacing L K), F ((x : AmbientSpace) + (refinedSpacing L K / 2) •
          (Pi.single μ 1 + Pi.single κ 1 : AmbientSpace)) : ℝ) : ℂ) := by
  have h : ∀ g : LatticePoint (refinedSpacing L K) → ℝ,
      ∑ᶠ x, ((g x : ℝ) : ℂ) = ((∑ᶠ x, g x : ℝ) : ℂ) :=
    fun g => (Complex.ofRealHom.toAddMonoidHom.map_finsum_of_injective
      Complex.ofReal_injective g).symm
  simp only [realRiemannSum, refinedRiemannSum, h]
  push_cast
  rfl
def centeredCell (a : ℝ) (c : AmbientSpace) : Set AmbientSpace :=
  Set.pi univ fun μ => Ico (c μ - a / 2) (c μ + a / 2)
theorem measurableSet_centeredCell (c : AmbientSpace) : MeasurableSet (centeredCell a c) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico
theorem volume_centeredCell (ha : 0 < a) (c : AmbientSpace) :
    volume (centeredCell a c) = ENNReal.ofReal (a ^ 4) := by
  rw [centeredCell, Real.volume_pi_Ico]
  have h : ∀ μ : Fin 4, c μ + a / 2 - (c μ - a / 2) = a := fun μ => by ring
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow ha.le]
theorem mem_centeredCell_self (ha : 0 < a) (c : AmbientSpace) : c ∈ centeredCell a c :=
  fun μ _ => ⟨by linarith, by linarith⟩
theorem disjoint_centeredCell (ha : 0 < a) (v : AmbientSpace) {x x' : LatticePoint a}
    (hx : x ≠ x') :
    Disjoint (centeredCell a ((x : AmbientSpace) + v)) (centeredCell a ((x' : AmbientSpace) + v)) := by
  refine Set.disjoint_left.2 fun u hu hu' => hx ?_
  obtain ⟨n, hn⟩ := x.2
  obtain ⟨n', hn'⟩ := x'.2
  have hnn : n = n' := by
    funext μ
    have h1 := hu μ (mem_univ _)
    have h2 := hu' μ (mem_univ _)
    simp only [Pi.add_apply, mem_Ico] at h1 h2
    rw [hn μ] at h1
    rw [hn' μ] at h2
    have hlt : ((n μ - n' μ : ℤ) : ℝ) * a < a := by push_cast; nlinarith [h1.1, h1.2, h2.1, h2.2]
    have hgt : -a < ((n μ - n' μ : ℤ) : ℝ) * a := by push_cast; nlinarith [h1.1, h1.2, h2.1, h2.2]
    have h3 : ((n μ - n' μ : ℤ) : ℝ) < 1 := by nlinarith
    have h4 : (-1 : ℝ) < ((n μ - n' μ : ℤ) : ℝ) := by nlinarith
    have h5 : n μ - n' μ < 1 := by exact_mod_cast h3
    have h6 : -1 < n μ - n' μ := by exact_mod_cast h4
    omega
  apply Subtype.ext
  funext μ
  rw [hn μ, hn' μ, hnn]
theorem exists_mem_centeredCell (ha : 0 < a) (v u : AmbientSpace) :
    ∃ x : LatticePoint a, u ∈ centeredCell a ((x : AmbientSpace) + v) := by
  let n : Fin 4 → ℤ := fun μ => ⌊(u μ - v μ + a / 2) / a⌋
  refine ⟨⟨fun μ => (n μ : ℝ) * a, n, fun _ => rfl⟩, fun μ _ => ?_⟩
  have h1 : (n μ : ℝ) ≤ (u μ - v μ + a / 2) / a := Int.floor_le _
  have h2 : (u μ - v μ + a / 2) / a < (n μ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ ha] at h1
  rw [div_lt_iff₀ ha] at h2
  simp only [Pi.add_apply, mem_Ico]
  constructor <;> nlinarith
theorem euclidNormVec_le_of_mem_centeredCell (ha : 0 < a) {c u : AmbientSpace}
    (hu : u ∈ centeredCell a c) : TorusMetric.euclidNormVec (c - u) ≤ a := by
  rw [TorusMetric.euclidNormVec]
  apply Real.sqrt_le_iff.2 ⟨ha.le, ?_⟩
  have h : ∀ μ : Fin 4, (c - u) μ ^ 2 ≤ a ^ 2 / 4 := fun μ => by
    have h1 := hu μ (mem_univ _)
    simp only [mem_Ico] at h1
    simp only [Pi.sub_apply]
    nlinarith [h1.1, h1.2]
  calc ∑ μ, (c - u) μ ^ 2 ≤ ∑ _μ : Fin 4, a ^ 2 / 4 := Finset.sum_le_sum fun μ _ => h μ
    _ = a ^ 2 := by simp; ring
def closedBox (y : AmbientSpace) (r : ℝ) : Set AmbientSpace :=
  Set.pi univ fun μ => Icc (y μ - r) (y μ + r)
theorem volume_closedBox (y : AmbientSpace) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBox y r) = ENNReal.ofReal ((2 * r) ^ 4) := by
  rw [closedBox, Set.pi_univ_Icc, Real.volume_Icc_pi]
  have h : ∀ μ : Fin 4, (fun ν => y ν + r) μ - (fun ν => y ν - r) μ = 2 * r := fun μ => by
    simp only
    ring
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by linarith)]
theorem abs_latticeSum_sub_integral_le (ha : 0 < a) (v y : AmbientSpace) {R C : ℝ} (hR : 0 ≤ R)
    (hC : 0 ≤ C) {F : AmbientSpace → ℝ} (hint : Integrable F)
    (hLip : ∀ u w, |F u - F w| ≤ C * TorusMetric.euclidNormVec (u - w))
    (hsupp : ∀ u, F u ≠ 0 → u ∈ closedBox y R) :
    |a ^ 4 * ∑ᶠ x : LatticePoint a, F ((x : AmbientSpace) + v) - ∫ u, F u| ≤
      (2 * R + 2 * a) ^ 4 * a * C := by
  classical
  let G : AmbientSpace → ℝ := (closedBox y (R + a)).indicator fun _ => 1
  have hGc : HasCompactSupport G := by
    have hK : IsCompact (closedBox y (R + a)) := isCompact_univ_pi fun _ => isCompact_Icc
    exact HasCompactSupport.intro hK fun u hu => by simp [G, hu]
  let T : Set (LatticePoint a) :=
    {x | (centeredCell a ((x : AmbientSpace) + v) ∩ closedBox y R).Nonempty}
  have hsub : ∀ x ∈ T, centeredCell a ((x : AmbientSpace) + v) ⊆ closedBox y (R + a) := by
    rintro x ⟨u', hu', hu'y⟩ u hu μ _
    have h1 := hu μ (mem_univ _)
    have h2 := hu' μ (mem_univ _)
    have h3 := hu'y μ (mem_univ _)
    simp only [mem_Ico, mem_Icc] at h1 h2 h3 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  have hTfin : T.Finite := by
    refine (finite_shifted_latticePoints_ne_zero ha hGc v).subset fun x hx => ?_
    have : (x : AmbientSpace) + v ∈ closedBox y (R + a) :=
      hsub x hx (mem_centeredCell_self ha _)
    simp [G, this]
  set T' : Finset (LatticePoint a) := hTfin.toFinset with hT'
  have hmem : ∀ x, x ∈ T' ↔ x ∈ T := fun x => hTfin.mem_toFinset
  have hdisj : Set.Pairwise (T' : Set (LatticePoint a))
      (Function.onFun Disjoint fun x : LatticePoint a => centeredCell a ((x : AmbientSpace) + v)) :=
    fun x _ x' _ hne => disjoint_centeredCell ha v hne
  have hcard : (T'.card : ℝ) * a ^ 4 ≤ (2 * R + 2 * a) ^ 4 := by
    have h1 : volume (⋃ x ∈ T', centeredCell a ((x : AmbientSpace) + v)) ≤
        volume (closedBox y (R + a)) :=
      measure_mono (iUnion₂_subset fun x hx => hsub x ((hmem x).1 hx))
    rw [measure_biUnion_finset hdisj fun x _ => measurableSet_centeredCell _,
      volume_closedBox y (by linarith)] at h1
    simp only [volume_centeredCell ha, Finset.sum_const, nsmul_eq_mul] at h1
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    calc (T'.card : ℝ) * a ^ 4 ≤ (2 * (R + a)) ^ 4 := h1
      _ = (2 * R + 2 * a) ^ 4 := by ring
  have hsum : ∑ᶠ x : LatticePoint a, F ((x : AmbientSpace) + v) =
      ∑ x ∈ T', F ((x : AmbientSpace) + v) := by
    refine finsum_eq_sum_of_support_subset _ fun x hx => ?_
    exact (hmem x).2 ⟨_, mem_centeredCell_self ha _, hsupp _ hx⟩
  have hintegral : ∫ u, F u = ∑ x ∈ T', ∫ u in centeredCell a ((x : AmbientSpace) + v), F u := by
    rw [← integral_biUnion_finset T' (fun x _ => measurableSet_centeredCell _) hdisj
      fun x _ => hint.integrableOn]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
    by_contra hne
    obtain ⟨x, hx⟩ := exists_mem_centeredCell ha v u
    exact hu (mem_iUnion₂.2 ⟨x, (hmem x).2 ⟨u, hx, hsupp u hne⟩, hx⟩)
  have hone : ∀ x : LatticePoint a,
      |a ^ 4 * F ((x : AmbientSpace) + v) - ∫ u in centeredCell a ((x : AmbientSpace) + v), F u| ≤
        a ^ 4 * (C * a) := by
    intro x
    set c : AmbientSpace := (x : AmbientSpace) + v with hc
    have hvol : volume.real (centeredCell a c) = a ^ 4 := by
      rw [Measure.real, volume_centeredCell ha, ENNReal.toReal_ofReal (by positivity)]
    have hfin : volume (centeredCell a c) < ⊤ := by
      rw [volume_centeredCell ha]
      exact ENNReal.ofReal_lt_top
    have hconst : IntegrableOn (fun _ : AmbientSpace => F c) (centeredCell a c) :=
      integrableOn_const hfin.ne
    have heq : a ^ 4 * F c - ∫ u in centeredCell a c, F u =
        ∫ u in centeredCell a c, (F c - F u) := by
      rw [integral_sub hconst hint.integrableOn, setIntegral_const, hvol, smul_eq_mul]
    rw [heq]
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun u => F c - F u)
      (s := centeredCell a c) (C := C * a) hfin fun u hu => by
        rw [Real.norm_eq_abs]
        exact (hLip c u).trans
          (mul_le_mul_of_nonneg_left (euclidNormVec_le_of_mem_centeredCell ha hu) hC)
    rw [hvol, Real.norm_eq_abs] at hb
    linarith
  rw [hsum, hintegral, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ x ∈ T', (a ^ 4 * F ((x : AmbientSpace) + v) -
        ∫ u in centeredCell a ((x : AmbientSpace) + v), F u)|
      ≤ ∑ x ∈ T', |a ^ 4 * F ((x : AmbientSpace) + v) -
        ∫ u in centeredCell a ((x : AmbientSpace) + v), F u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ T', a ^ 4 * (C * a) := Finset.sum_le_sum fun x _ => hone x
    _ = (T'.card : ℝ) * a ^ 4 * (a * C) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (2 * R + 2 * a) ^ 4 * (a * C) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg ha.le hC)
    _ = (2 * R + 2 * a) ^ 4 * a * C := by ring
theorem abs_apply_le_euclidNormVec (v : AmbientSpace) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.SharedProofs.p10398 <;> assumption
theorem lipConstR4_nonneg (F : AmbientSpace → ℝ) : 0 ≤ TestFunctions.lipConstR4 F := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.lipConstR4_nonneg <;> assumption
theorem abs_sub_le_lipConstR4 {F : AmbientSpace → ℝ}
    (hF : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 F) (u w : AmbientSpace) :
    |F u - F w| ≤ TestFunctions.lipConstR4 F * TorusMetric.euclidNormVec (u - w) := by apply _root_.YangMills.DeltaSharedProofs.p2429 <;> assumption
theorem continuous_of_isLipschitzFor {F : AmbientSpace → ℝ}
    (hF : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 F) : Continuous F := by apply _root_.YangMills.SharedProofs.p29528 <;> assumption
theorem mem_closedBox_of_ne_zero {F : AmbientSpace → ℝ} {y : AmbientSpace} {R : ℝ}
    (hS : TorusCovering.IsSupportedIn F (TestFunctions.closedBallR4 y R)) {u : AmbientSpace}
    (hu : F u ≠ 0) : u ∈ closedBox y R := by
  have h : TorusMetric.euclidNormVec (u - y) ≤ R := hS (subset_closure hu)
  intro μ _
  have h1 := (abs_apply_le_euclidNormVec (u - y) μ).trans h
  rw [abs_le] at h1
  simp only [Pi.sub_apply] at h1
  constructor <;> linarith [h1.1, h1.2]
theorem integrable_of_isLipschitzFor {F : AmbientSpace → ℝ} {y : AmbientSpace} {R : ℝ}
    (hF : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 F)
    (hS : TorusCovering.IsSupportedIn F (TestFunctions.closedBallR4 y R)) : Integrable F := by
  have hK : IsCompact (closedBox y R) := isCompact_univ_pi fun _ => isCompact_Icc
  refine (continuous_of_isLipschitzFor hF).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hK fun u hu => ?_)
  by_contra hne
  exact hu (mem_closedBox_of_ne_zero hS hne)
theorem sum_card_Ioi_fin_four : ∑ μ : Fin 4, ((Finset.Ioi μ).card : ℝ) = 6 := by
  have h : ∑ μ : Fin 4, (Finset.Ioi μ).card = 6 := by decide
  exact_mod_cast h
theorem abs_pairMean_sub_le (X : Fin 4 → Fin 4 → ℝ) (I B : ℝ)
    (h : ∀ μ κ, |X μ κ - I| ≤ B) :
    |1 / 6 * ∑ μ : Fin 4, ∑ κ ∈ Finset.Ioi μ, X μ κ - I| ≤ B := by
  have hs : ∑ μ : Fin 4, ∑ κ ∈ Finset.Ioi μ, (X μ κ - I) =
      (∑ μ : Fin 4, ∑ κ ∈ Finset.Ioi μ, X μ κ) - 6 * I := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.sum_mul, sum_card_Ioi_fin_four]
  have he : 1 / 6 * ∑ μ : Fin 4, ∑ κ ∈ Finset.Ioi μ, X μ κ - I =
      1 / 6 * ∑ μ : Fin 4, ∑ κ ∈ Finset.Ioi μ, (X μ κ - I) := by
    rw [hs]
    ring
  have hb : |∑ μ : Fin 4, ∑ κ ∈ Finset.Ioi μ, (X μ κ - I)| ≤ 6 * B := by
    calc |∑ μ : Fin 4, ∑ κ ∈ Finset.Ioi μ, (X μ κ - I)|
        ≤ ∑ μ : Fin 4, |∑ κ ∈ Finset.Ioi μ, (X μ κ - I)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ μ : Fin 4, ∑ κ ∈ Finset.Ioi μ, |X μ κ - I| :=
          Finset.sum_le_sum fun μ _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ μ : Fin 4, ∑ _κ ∈ Finset.Ioi μ, B :=
          Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun κ _ => h μ κ
      _ = 6 * B := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [← Finset.sum_mul, sum_card_Ioi_fin_four]
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
  linarith
theorem spacing_pos_of_admissible {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (K : ℕ) : 0 < refinedSpacing L K := by apply _root_.YangMills.Construction.CutoffLattice.spacingAt_pos <;> assumption
theorem refinedSpacing_eq_inv_pow {L : ℕ} (K : ℕ) : refinedSpacing L K = ((L : ℝ)⁻¹) ^ K := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.refinedSpacing_eq_inv_pow <;> assumption
theorem refinedSpacing_le_one_of_admissible {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ) : refinedSpacing L K ≤ 1 := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeCovering.spacingAt_le_one <;> assumption
theorem norm_realRiemannSum_sub_integral_le {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ)
    {F : AmbientSpace → ℝ} {y : AmbientSpace} {R : ℝ} (hR : 0 < R)
    (hF : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 F)
    (hS : TorusCovering.IsSupportedIn F (TestFunctions.closedBallR4 y R)) :
    ‖realRiemannSum L K F - ((∫ x, F x : ℝ) : ℂ)‖ ≤
      riemannSumErrorConst * (R + 1) ^ 4 * refinedSpacing L K * TestFunctions.lipConstR4 F := by
  have ha := spacing_pos_of_admissible hL K
  have ha1 := refinedSpacing_le_one_of_admissible hL K
  have hC := lipConstR4_nonneg F
  rw [realRiemannSum_eq_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine (abs_pairMean_sub_le _ _ ((2 * R + 2 * refinedSpacing L K) ^ 4 * refinedSpacing L K *
    TestFunctions.lipConstR4 F) fun μ κ => ?_).trans ?_
  · exact abs_latticeSum_sub_integral_le ha _ y hR.le hC (integrable_of_isLipschitzFor hF hS)
      (abs_sub_le_lipConstR4 hF) fun u hu => mem_closedBox_of_ne_zero hS hu
  · have h : (2 * R + 2 * refinedSpacing L K) ^ 4 ≤ 16 * (R + 1) ^ 4 := by
      calc (2 * R + 2 * refinedSpacing L K) ^ 4 ≤ (2 * (R + 1)) ^ 4 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 4
        _ = 16 * (R + 1) ^ 4 := by ring
    rw [riemannSumErrorConst]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h ha.le) hC
theorem tendsto_realRiemannSum {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    {F : AmbientSpace → ℝ} {y : AmbientSpace} {R : ℝ} (hR : 0 < R)
    (hF : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 F)
    (hS : TorusCovering.IsSupportedIn F (TestFunctions.closedBallR4 y R)) :
    Filter.Tendsto (fun J : ℕ => realRiemannSum L J F) Filter.atTop
      (nhds ((∫ x, F x : ℝ) : ℂ)) := by
  have h13 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have hlim : Filter.Tendsto (fun J : ℕ => refinedSpacing L J) Filter.atTop (nhds 0) := by
    simp only [refinedSpacing_eq_inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by linarith))
  have hb : Filter.Tendsto (fun J : ℕ => riemannSumErrorConst * (R + 1) ^ 4 * refinedSpacing L J *
      TestFunctions.lipConstR4 F) Filter.atTop (nhds 0) := by
    simpa using (hlim.const_mul (riemannSumErrorConst * (R + 1) ^ 4)).mul_const
      (TestFunctions.lipConstR4 F)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun J => norm_realRiemannSum_sub_integral_le hL J hR hF hS) hb
theorem periodicGibbsState_expectation {L K : ℕ} (ν : Measure (RefinedGaugeField L K))
    [IsProbabilityMeasure ν] (hL : 0 < refinedSpacing L K)
    (hinv : ∀ r : latticeMotions (refinedSpacing L K),
      IsSymmetricUnder ν (latticeMotionSymmetry r))
    (hRV : ∀ p : LatticeCutoffPlaquette L K, Probability.IsBoundedRealRV
      fun U : RefinedGaugeField L K => faceEnergy U p)
    (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      {p : LatticeCutoffPlaquette L K | p.center ∈ S}.Finite) :
    MotionsTransitiveOnPlaquettes L K ∧
      (∀ p : LatticeCutoffPlaquette L K, ∫ U, faceEnergy U p ∂ν = meanFaceEnergy ν) ∧
      ∀ F ∈ compactTestFunctions, ExpectObservableEqRiemannMultiple ν F := by
  classical
  have hmean : ∀ p : LatticeCutoffPlaquette L K,
      ∫ U, faceEnergy U p ∂ν = meanFaceEnergy ν := by
    intro p
    obtain ⟨r, hb, h1, h2⟩ := exists_motion_carrying (basePlaquette L K) p
    obtain ⟨hm, C, hC⟩ := hRV (basePlaquette L K)
    have hobs : IsBoundedObservable
        (fun U : RefinedGaugeField L K => (faceEnergy U (basePlaquette L K) : ℂ)) :=
      ⟨Complex.measurable_ofReal.comp hm, C, fun U => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hC U⟩
    have h := hinv r _ hobs
    have he : (fun U => (latticeMotionSymmetry r).actOn
        (fun U : RefinedGaugeField L K => (faceEnergy U (basePlaquette L K) : ℂ)) U) =
        fun U : RefinedGaugeField L K => (faceEnergy U p : ℂ) := by
      funext U
      simp only [LatticeSymmetry.actOn]
      rw [faceEnergy_pullbackField _ hb h1 h2]
    rw [he, integral_complex_ofReal, integral_complex_ofReal] at h
    exact Complex.ofReal_injective h
  refine ⟨fun p q => ?_, hmean, fun F hF => ?_⟩
  · obtain ⟨r, hb, h1, h2⟩ := exists_motion_carrying p q
    exact ⟨r, image_cornerSet _ hb h1 h2⟩
  have hfinF : {p : LatticeCutoffPlaquette L K | F p.center ≠ 0}.Finite :=
    (hfin (tsupport F) hF.2.2.isCompact.isBounded).subset fun p hp => subset_tsupport F hp
  set T : Finset (LatticeCutoffPlaquette L K) := hfinF.toFinset with hT
  have hTm : ∀ p, p ∈ T ↔ F p.center ≠ 0 := fun p => hfinF.mem_toFinset
  have hsum : ∑ᶠ p : LatticeCutoffPlaquette L K, F p.center = ∑ p ∈ T, F p.center :=
    finsum_eq_sum_of_support_subset _ fun p hp => (hTm p).2 hp
  have hobs : ∀ U : RefinedGaugeField L K, smearedEnergy F U =
      ∑ p ∈ T, faceEnergy U p * F p.center := by
    intro U
    refine finsum_eq_sum_of_support_subset _ fun p hp => (hTm p).2 fun h0 => hp ?_
    simp [h0]
  have hint : ∀ p : LatticeCutoffPlaquette L K,
      Integrable (fun U : RefinedGaugeField L K => faceEnergy U p) ν := by
    intro p
    obtain ⟨hm, C, hC⟩ := hRV p
    exact Integrable.of_bound hm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun U => by simpa [Real.norm_eq_abs] using hC U)
  have hreal : ∫ U, PeriodicGibbsAtCutoff.smearedObservable F U ∂ν =
      meanFaceEnergy ν * ∑ᶠ p : LatticeCutoffPlaquette L K, F p.center := by
    simp only [PeriodicGibbsAtCutoff.smearedObservable, hobs]
    rw [integral_finsetSum T fun p _ => (hint p).mul_const _, hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_mul_const, hmean]
  refine ⟨?_, ?_⟩
  · rw [PeriodicGibbsAtCutoff.expectation, integral_complex_ofReal, hreal]
    push_cast
    rfl
  · rw [realRiemannSum_eq_ofReal, finsum_faces_eq_sum_axes hfinF]
    have ha : (refinedSpacing L K : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    simp only [← Finset.mul_sum]
    push_cast
    field_simp
theorem periodicGibbsObservableExpectation_holds
    (hInv : VolumeTransfer.PeriodicGibbsInvariance.Statement)
    (hPl : FaceEnergyBoundedAndFacesLocallyFinite) : PeriodicGibbsObservableExpectation := by
  refine ⟨fun L K β hL hβ ν hν => ?_, fun L hL F y R hR hF hS =>
    ⟨fun K => norm_realRiemannSum_sub_integral_le hL K hR hF hS,
      tendsto_realRiemannSum hL hR hF hS⟩⟩
  have : IsProbabilityMeasure ν :=
    PeriodicGibbsAtCutoff.isProbabilityMeasure_of_mem_gibbsSet hν
  have hinv := (hInv L hL K β hβ ν hν).2.1.1
  have hpl := hPl ⟨L, hL, K, 1⟩ ν inferInstance
  obtain ⟨h1, h2, h3⟩ := periodicGibbsState_expectation ν (spacing_pos_of_admissible hL K) hinv
    (fun p => (hpl.1.2 p).1) hpl.2
  exact ⟨h1, hinv, h2, h3⟩
end YangMills.Construction.InfiniteLattice.PeriodicExpectation
end

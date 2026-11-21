import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBounded
import YangMills.Construction.ReflectionPositivity.ContinuityOfTheLimitOfABoundedLatticeApproximation
import YangMills.Construction.ReflectionPositivity.ContractionOfTheLimitOfALatticeApproximation
import YangMills.Construction.ReflectionPositivity.LatticeFormulaForTheScalarProductProof
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitContraction
open YangMills.Construction.ReflectionPositivity.AxisMirror (MirrorData)
open YangMills.Construction.ReflectionPositivity.TupleForm (PositiveSpan reflectedCorrelation
  reflectionForm reflectConj)
open YangMills.Construction.InfiniteLattice (GaugeField LatticePoint AmbientSpace refinedSpacing
  latticeSubgroup axisStep)
open YangMills.Construction.LimitConventions (ApproxTriple)
open YangMills.Construction.ReflectionPositivity.LatticeScalarProduct (AdicLimitFormula
  LatticeRepresentatives SupportedAbove latticeExpectation conjReflMulShift meshAt)
open YangMills.Construction.LatticeConventions (Spacing timeAxis basisVector)
open YangMills.Construction.LatticeConventions.SiteFrame (siteForm upperSpace)
open YangMills.Construction.PeriodicLattice (adicGridPoints)
open YangMills.Construction.SeparatedTuples (FormalSpan TupleFunctional SepTuple push pushSpan
  pushList invMap basisVec)
theorem pushSpan_translate_zero (F : FormalSpan) :
    pushSpan (SeparatedTuples.translate 0) F = F := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.pushSpan_translate_zero <;> assumption
theorem reflectedCorrelation_zero (σ : TupleFunctional) (Z : PositiveSpan) :
    reflectedCorrelation σ Z 0 = reflectionForm σ Z Z := by
  simp only [reflectedCorrelation, reflectionForm, pushSpan_translate_zero]
theorem exists_eq_comp_of_mem_push {r : AmbientSpace → AmbientSpace} {X : SepTuple}
    {f : AmbientSpace → ℝ} (hf : f ∈ (push r X).1) : ∃ g ∈ X.1, f = g ∘ invMap r := by
  unfold push at hf
  split_ifs at hf with h
  · have hf' : f ∈ X.1.map fun f => f ∘ invMap r := hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf'
    exact ⟨g, hg, rfl⟩
  · simp [SepTuple.nil] at hf
theorem timeReflection_involutive : Function.Involutive TimeAxis.timeReflection := by
  intro x
  funext μ
  fin_cases μ <;> simp [TimeAxis.timeReflection]
theorem invMap_timeReflection (x : AmbientSpace) :
    invMap TimeAxis.timeReflection x = TimeAxis.timeReflection x := by
  calc invMap TimeAxis.timeReflection x
      = invMap TimeAxis.timeReflection
          (TimeAxis.timeReflection (TimeAxis.timeReflection x)) := by
        rw [timeReflection_involutive x]
    _ = TimeAxis.timeReflection x :=
        Function.leftInverse_invFun timeReflection_involutive.injective _
theorem timeComponent_timeReflection (x : AmbientSpace) :
    TimeAxis.timeComponent (TimeAxis.timeReflection x) = -TimeAxis.timeComponent x := by
  simp [TimeAxis.timeComponent, TimeAxis.timeReflection, TimeAxis.timeIdx]
theorem invMap_translate (v x : AmbientSpace) :
    invMap (SeparatedTuples.translate v) x = x - v := by
  have hinj : Function.Injective (SeparatedTuples.translate v) :=
    fun y z hyz => add_right_cancel hyz
  have hx : SeparatedTuples.translate v (x - v) = x := by simp [SeparatedTuples.translate]
  calc invMap (SeparatedTuples.translate v) x
      = invMap (SeparatedTuples.translate v) (SeparatedTuples.translate v (x - v)) := by rw [hx]
    _ = x - v := Function.leftInverse_invFun hinj _
theorem continuous_timeComponent : Continuous TimeAxis.timeComponent :=
  continuous_apply TimeAxis.timeIdx
theorem tsupport_push_timeReflection_subset {δ : ℝ} {X : SepTuple}
    (hX : ∀ f ∈ X.1, tsupport f ⊆ {x | 2 * δ ≤ TimeAxis.timeComponent x}) {f : AmbientSpace → ℝ}
    (hf : f ∈ (push TimeAxis.timeReflection X).1) :
    tsupport f ⊆ {x | TimeAxis.timeComponent x ≤ -(2 * δ)} := by
  obtain ⟨g, hg, rfl⟩ := exists_eq_comp_of_mem_push hf
  refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_timeComponent continuous_const)
  have hx' : TimeAxis.timeReflection x ∈ tsupport g := subset_tsupport g (by
    simpa [Function.mem_support, invMap_timeReflection] using hx)
  have h := hX g hg hx'
  simp only [Set.mem_ofPred_eq, timeComponent_timeReflection] at h
  change TimeAxis.timeComponent x ≤ _
  linarith
theorem tsupport_push_translate_subset {δ : ℝ} {X : SepTuple}
    (hX : ∀ f ∈ X.1, tsupport f ⊆ {x | 2 * δ ≤ TimeAxis.timeComponent x}) {v : AmbientSpace}
    (hv : 0 ≤ TimeAxis.timeComponent v) {f : AmbientSpace → ℝ}
    (hf : f ∈ (push (SeparatedTuples.translate v) X).1) :
    tsupport f ⊆ {x | 2 * δ ≤ TimeAxis.timeComponent x} := by
  obtain ⟨g, hg, rfl⟩ := exists_eq_comp_of_mem_push hf
  refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const continuous_timeComponent)
  have hx' : x - v ∈ tsupport g := subset_tsupport g (by
    simpa [Function.mem_support, invMap_translate] using hx)
  have h := hX g hg hx'
  have ht : TimeAxis.timeComponent (x - v) =
      TimeAxis.timeComponent x - TimeAxis.timeComponent v := rfl
  simp only [Set.mem_ofPred_eq, ht] at h
  change _ ≤ TimeAxis.timeComponent x
  linarith
theorem exists_of_mem_support_pushSpan {r : AmbientSpace → AmbientSpace} {G : FormalSpan}
    {Y : SepTuple} (hY : Y ∈ (pushSpan r G).support) : ∃ X ∈ G.support, Y = push r X := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.exists_of_mem_support_pushSpan <;> assumption
theorem exists_of_mem_support_reflectConj {Z : PositiveSpan} {Y : SepTuple}
    (hY : Y ∈ (reflectConj Z).support) :
    ∃ X ∈ Z.1.support, Y = push TimeAxis.timeReflection X := by
  obtain ⟨X, hX, rfl⟩ := exists_of_mem_support_pushSpan hY
  exact ⟨X, Finsupp.support_mapRange (hf := map_zero _) hX, rfl⟩
theorem composable_of_supportedAbove {δ : ℝ} (hδ : 0 < δ) {Z : PositiveSpan}
    (hZ : SupportedAbove δ Z.1) {v : AmbientSpace} (hv : 0 ≤ TimeAxis.timeComponent v) :
    ∀ X ∈ Z.1.support, ∀ Y ∈ (reflectConj Z).support,
      SepTuple.Composable Y (push (SeparatedTuples.translate v) X) := by
  intro X hX Y hY f hf h hh
  obtain ⟨X', hX', rfl⟩ := exists_of_mem_support_reflectConj hY
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have h1 := tsupport_push_timeReflection_subset (hZ X' hX') hf hx
  have h2 := tsupport_push_translate_subset (hZ X hX) hv hh hx'
  simp only [Set.mem_ofPred_eq] at h1 h2
  linarith
theorem thirteen_le_L (D : MirrorData) : (13 : ℝ) ≤ D.L := by
  exact_mod_cast D.isAdmissible.2
theorem meshSize_natCast_eq_inv_pow (L n : ℕ) :
    PeriodicLattice.meshSize L (n : ℤ) = ((L : ℝ)⁻¹) ^ n := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.refinedSpacing_eq_inv_pow <;> assumption
theorem eventually_refinedSpacing_le (D : MirrorData) (T : ApproxTriple D.L) {δ : ℝ}
    (hδ : 0 < δ) : ∀ᶠ j in atTop, refinedSpacing D.L (T.cutoff j) ≤ δ := by
  have hL := thirteen_le_L D
  have hy : ((D.L : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ hy
  have hK : ∀ᶠ j in atTop, (⟨N + 1, Nat.succ_pos N⟩ : ℕ+) ≤ T.cutoff j :=
    T.tendsto_cutoff.eventually_ge_atTop _
  filter_upwards [hK] with j hj
  have hj' : N ≤ (T.cutoff j : ℕ) := by
    have h : N + 1 ≤ (T.cutoff j : ℕ) := hj
    omega
  have hs : refinedSpacing D.L (T.cutoff j) = ((D.L : ℝ)⁻¹) ^ (T.cutoff j : ℕ) :=
    meshSize_natCast_eq_inv_pow _ _
  rw [hs]
  exact (pow_le_pow_of_le_one (by positivity) hy.le hj').trans hN.le
theorem zero_mem_adicGridPoints (L : ℕ) : (0 : ℝ) ∈ adicGridPoints L :=
  (PeriodicLattice.mem_adicGridPoints_iff _ _).2 ⟨0, 0, by simp⟩
theorem two_mul_mem_adicGridPoints {L : ℕ} {s : ℝ} (hs : s ∈ adicGridPoints L) :
    2 * s ∈ adicGridPoints L := by
  obtain ⟨k, n, h⟩ := (PeriodicLattice.mem_adicGridPoints_iff _ _).1 hs
  refine (PeriodicLattice.mem_adicGridPoints_iff _ _).2 ⟨k, 2 * n, ?_⟩
  rw [h]
  push_cast
  ring
theorem smul_basisVector_apply_mem {L : ℕ} {r : ℝ} (hr : r ∈ adicGridPoints L) (μ : Fin 4) :
    (r • basisVector TimeAxis.timeIdx) μ ∈ adicGridPoints L := by
  by_cases h : μ = TimeAxis.timeIdx
  · subst h
    simpa [basisVector] using hr
  · have h0 : (r • basisVector TimeAxis.timeIdx) μ = 0 := by
      simp [basisVector, Pi.single_eq_of_ne h]
    rw [h0]
    exact zero_mem_adicGridPoints L
theorem timeComponent_smul_basisVector (r : ℝ) :
    TimeAxis.timeComponent (r • basisVector TimeAxis.timeIdx) = r := by
  simp [TimeAxis.timeComponent, basisVector]
theorem integral_conjReflMulShift_eq_reflectedCorrelation (a : Spacing)
    (ν : Measure (GaugeField (a : ℝ))) (F : GaugeField (a : ℝ) → ℂ) (v : AmbientSpace)
    (w : LatticePoint (a : ℝ)) (hw : (w : AmbientSpace) = v) :
    ∫ U, conjReflMulShift a F F v U ∂ν =
      LatticeConventions.SiteFrame.reflectedCorrelation a timeAxis ν F w := by
  subst hw
  have hv : (w : AmbientSpace) ∈ latticeSubgroup (a : ℝ) := w.2
  unfold conjReflMulShift LatticeConventions.SiteFrame.reflectedCorrelation
    LatticeConventions.SiteFrame.reflectedCorrelationFun
  rw [dif_pos hv]
  rfl
theorem integral_conjReflMulShift_zero_eq_siteForm (a : Spacing)
    (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν] (F : upperSpace a timeAxis) :
    ∫ U, conjReflMulShift a F.1 F.1 0 U ∂ν = siteForm a timeAxis ν F F := by
  have hv : (0 : AmbientSpace) ∈ latticeSubgroup (a : ℝ) := zero_mem _
  have hF : (InfiniteLattice.shift (⟨0, hv⟩ : LatticePoint (a : ℝ))).actOn F.1 = F.1 :=
    funext fun U => congrArg F.1 (InfiniteLattice.shift_zero_pullbackField U)
  unfold conjReflMulShift siteForm
  rw [dif_pos hv, hF]
  rfl
theorem contraction_of_mem_adicGridPoints
    (hOne : LatticeConventions.ReflectionPositiveStates.Statement)
    (D : MirrorData) (T : ApproxTriple D.L) (σ : TupleFunctional)
    (hRP : ApproxTriple.IsReflPos T) (Z : PositiveSpan) {δ : ℝ}
    (hδ : 0 < δ) (hrep : LatticeRepresentatives D T Z Z δ)
    (hadic : AdicLimitFormula D T σ Z Z) {s : ℝ} (hs : s ∈ adicGridPoints D.L) (hs0 : 0 ≤ s) :
    (reflectedCorrelation σ Z (twiceTimeShift s)).im = 0 ∧
      (reflectedCorrelation σ Z 0).im = 0 ∧
      0 ≤ (reflectedCorrelation σ Z (twiceTimeShift s)).re ∧
      (reflectedCorrelation σ Z (twiceTimeShift s)).re ≤ (reflectedCorrelation σ Z 0).re := by
  have h1 := hadic (s • basisVector TimeAxis.timeIdx) (smul_basisVector_apply_mem hs)
    (by rw [timeComponent_smul_basisVector]; exact hs0)
  have h2 := hadic (twiceTimeShift s) (smul_basisVector_apply_mem (two_mul_mem_adicGridPoints hs))
    (by rw [twiceTimeShift, timeComponent_smul_basisVector]; positivity)
  have h0 := hadic 0 (fun _ => zero_mem_adicGridPoints _) (by simp [TimeAxis.timeComponent])
  have hlim2 : Tendsto (latticeExpectation D T Z.1 Z.1 (twiceTimeShift s)) atTop
      (𝓝 (reflectedCorrelation σ Z (twiceTimeShift s))) := h2.2.1
  have hlim0 : Tendsto (latticeExpectation D T Z.1 Z.1 0) atTop
      (𝓝 (reflectedCorrelation σ Z 0)) := h0.2.1
  have hev : ∀ᶠ j in atTop,
      (latticeExpectation D T Z.1 Z.1 (twiceTimeShift s) j).im = 0 ∧
      (latticeExpectation D T Z.1 Z.1 0 j).im = 0 ∧
      0 ≤ (latticeExpectation D T Z.1 Z.1 (twiceTimeShift s) j).re ∧
      (latticeExpectation D T Z.1 Z.1 (twiceTimeShift s) j).re ≤
        (latticeExpectation D T Z.1 Z.1 0 j).re := by
    filter_upwards [h1.1, eventually_refinedSpacing_le D T hδ] with j hj hjδ
    have ha := hRP j
    have hZmem := (hrep j hjδ).1
    obtain ⟨n, hn⟩ := hj TimeAxis.timeIdx
    have hapos : 0 < refinedSpacing D.L (T.cutoff j) := (meshAt D T j).2
    have hval : (s • basisVector TimeAxis.timeIdx) TimeAxis.timeIdx = s := by
      simp [basisVector]
    rw [hval] at hn
    have hsn : s = (n : ℝ) * refinedSpacing D.L (T.cutoff j) := by
      rw [← hn]
      field_simp
    have hn0 : 0 ≤ n := by
      have h : (0 : ℝ) ≤ (n : ℝ) := by
        rw [← hn]
        positivity
      exact_mod_cast h
    lift n to ℕ using hn0 with m
    have heven := (hOne (meshAt D T j) (T.state j) ha.1 ha.2).2.2.1 ⟨_, hZmem⟩ m
    have hw : (((2 * m) • axisStep ((meshAt D T j : Spacing) : ℝ) timeAxis :
        LatticePoint ((meshAt D T j : Spacing) : ℝ)) : AmbientSpace) = twiceTimeShift s := by
      funext μ
      have hsn' : s = (m : ℝ) * refinedSpacing D.L (T.cutoff j) := by simpa using hsn
      fin_cases μ <;>
        simp [twiceTimeShift, axisStep, basisVector, timeAxis, TimeAxis.timeIdx, hsn']
      ring
    have e2 : latticeExpectation D T Z.1 Z.1 (twiceTimeShift s) j = _ :=
      integral_conjReflMulShift_eq_reflectedCorrelation (meshAt D T j) (T.state j) _ _ _ hw
    have e0 : latticeExpectation D T Z.1 Z.1 0 j = _ :=
      integral_conjReflMulShift_zero_eq_siteForm (meshAt D T j) (T.state j) ⟨_, hZmem⟩
    rw [e2, e0]
    exact heven
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp hlim2)
      ((tendsto_const_nhds (x := (0 : ℝ))).congr' (hev.mono fun j h => h.1.symm))
  · exact tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp hlim0)
      ((tendsto_const_nhds (x := (0 : ℝ))).congr' (hev.mono fun j h => h.2.1.symm))
  · exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim2)
      (hev.mono fun j h => h.2.2.1)
  · exact le_of_tendsto_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim2)
      ((Complex.continuous_re.tendsto _).comp hlim0) (hev.mono fun j h => h.2.2.2)
def adicFloor (L : ℕ) (t : ℝ) (n : ℕ) : ℝ := (⌊t * (L : ℝ) ^ n⌋ : ℝ) * ((L : ℝ)⁻¹) ^ n
theorem adicFloor_mem (L : ℕ) (t : ℝ) (n : ℕ) : adicFloor L t n ∈ adicGridPoints L :=
  (PeriodicLattice.mem_adicGridPoints_iff _ _).2 ⟨n, ⌊t * (L : ℝ) ^ n⌋, by
    rw [meshSize_natCast_eq_inv_pow, adicFloor]⟩
theorem adicFloor_nonneg (L : ℕ) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ adicFloor L t n := by
  have h : (0 : ℝ) ≤ (⌊t * (L : ℝ) ^ n⌋ : ℝ) := by
    exact_mod_cast Int.floor_nonneg.2 (by positivity)
  exact mul_nonneg h (by positivity)
theorem tendsto_adicFloor {L : ℕ} (hL : (13 : ℝ) ≤ L) (t : ℝ) :
    Tendsto (adicFloor L t) atTop (𝓝 t) := by
  have hpos : (0 : ℝ) < L := by linarith
  have hy : ((L : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hpow : Tendsto (fun n : ℕ => ((L : ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hy
  have hcancel : ∀ n : ℕ, (L : ℝ) ^ n * ((L : ℝ)⁻¹) ^ n = 1 := fun n => by
    rw [← mul_pow, mul_inv_cancel₀ hpos.ne', one_pow]
  have hlow : Tendsto (fun n : ℕ => t - ((L : ℝ)⁻¹) ^ n) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub hpow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
    (fun n => ?_)
  · have h := (Int.lt_floor_add_one (t * (L : ℝ) ^ n)).le
    have he : (0 : ℝ) ≤ ((L : ℝ)⁻¹) ^ n := by positivity
    have h' := mul_le_mul_of_nonneg_right h he
    have ht : t * (L : ℝ) ^ n * ((L : ℝ)⁻¹) ^ n = t := by rw [mul_assoc, hcancel, mul_one]
    rw [ht, add_mul, one_mul] at h'
    change t - _ ≤ (⌊t * (L : ℝ) ^ n⌋ : ℝ) * _
    linarith
  · have h := Int.floor_le (t * (L : ℝ) ^ n)
    have he : (0 : ℝ) ≤ ((L : ℝ)⁻¹) ^ n := by positivity
    have h' := mul_le_mul_of_nonneg_right h he
    have ht : t * (L : ℝ) ^ n * ((L : ℝ)⁻¹) ^ n = t := by rw [mul_assoc, hcancel, mul_one]
    rw [ht] at h'
    exact h'
theorem continuous_twiceTimeShift : Continuous twiceTimeShift := by
  unfold twiceTimeShift
  fun_prop
theorem contractionBound_holds (hFormula : LatticeScalarProduct.LatticeFormula)
    (hCont : LimitContinuity.LimitIsContinuousFunctional)
    (hOne : LatticeConventions.ReflectionPositiveStates.Statement)
    (hBounded : ApproximatingSequences.LimitsOnTuplesImplyBounded) :
    ContractionBound := by
  intro D T σ hB hRP hLim Z t ht
  obtain ⟨⟨δ, hδ, hZδ, -⟩, hall⟩ := hFormula D T σ hRP hB hLim Z Z
  obtain ⟨hrep, hadic, -⟩ := hall δ hδ hZδ hZδ
  obtain ⟨C, hC⟩ := (hBounded.2.2 D T).2.1.1 hB
  obtain ⟨F, hFσ, -, -, -, -, -, -, hcomb⟩ := hCont D T C σ.toFun hB hC hLim
  have hF : F = σ := by
    cases F
    cases σ
    simp_all
  rw [hF] at hcomb
  have hvt : 0 ≤ TimeAxis.timeComponent (twiceTimeShift t) := by
    rw [twiceTimeShift, timeComponent_smul_basisVector]
    positivity
  obtain ⟨-, -, -, hlim, -⟩ := hcomb Z.1 (reflectConj Z) (twiceTimeShift t)
    (composable_of_supportedAbove hδ hZδ hvt)
  have hseq : Tendsto (fun n => reflectedCorrelation σ Z (twiceTimeShift (adicFloor D.L t n)))
      atTop (𝓝 (reflectedCorrelation σ Z (twiceTimeShift t))) :=
    hlim.comp ((continuous_twiceTimeShift.tendsto t).comp (tendsto_adicFloor (thirteen_le_L D) t))
  have hat := fun n => contraction_of_mem_adicGridPoints hOne D T σ hRP Z hδ hrep hadic
    (adicFloor_mem D.L t n) (adicFloor_nonneg D.L ht n)
  rw [← reflectedCorrelation_zero]
  refine ⟨?_, (hat 0).2.1, ?_, ?_⟩
  · exact tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp hseq)
      ((tendsto_const_nhds (x := (0 : ℝ))).congr fun n => ((hat n).1).symm)
  · exact ge_of_tendsto' ((Complex.continuous_re.tendsto _).comp hseq) fun n => (hat n).2.2.1
  · exact le_of_tendsto' ((Complex.continuous_re.tendsto _).comp hseq) fun n => (hat n).2.2.2
end YangMills.Construction.ReflectionPositivity.LimitContraction
end

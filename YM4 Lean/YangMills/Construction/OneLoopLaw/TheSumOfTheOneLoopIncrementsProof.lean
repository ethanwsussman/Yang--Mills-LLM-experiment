import YangMills.Construction.Towers.SecondDifferentialOfTheActionAndTheTwoDeterminantsProof
import YangMills.Construction.Lattice.GaugeSizeAnglesAndBlockMean
import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Matrices.SpecialUnitaryExpSurjective
import YangMills.Construction.OneLoopLaw.GaugeColourMomentaAndDifferencesOfFunctionalsProof
import YangMills.Construction.OneLoopLaw.TheSumOfTheOneLoopIncrements
import YangMills.Construction.Towers.CompositionOfATemperedFunctionalWithAStep
import YangMills.Construction.Towers.FamilyOfTheTotalNormaliserIsTempered
import YangMills.Construction.Towers.NormalisersOfTheCriticalBranch
import YangMills.Construction.Towers.TheProductOfTheNormalisers
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.OneLoopLaw.IncrementSum
open Tower PeriodicOperators.Tempered Matrices
private theorem tendsto_comp_nhdsWithin_one {ι κ : Type*} (e : κ → ι)
    {D : Set (ι → ComplexMatrix2)} {D' : Set (κ → ComplexMatrix2)}
    (h : MapsTo (fun U : ι → ComplexMatrix2 => U ∘ e) D D') :
    Tendsto (fun U : ι → ComplexMatrix2 => U ∘ e) (𝓝[D] fun _ => (1 : ComplexMatrix2))
      (𝓝[D'] fun _ => (1 : ComplexMatrix2)) := by
  have hc : Continuous (fun U : ι → ComplexMatrix2 => U ∘ e) :=
    continuous_pi fun b => continuous_apply (e b)
  exact (hc.continuousWithinAt (x := fun _ => (1 : ComplexMatrix2)) (s := D)).tendsto_nhdsWithin h
variable {L n : ℕ}
private theorem isPositivelyOriented_opposite_of_not {b : UnitEdge L n}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p9846 <;> assumption
private theorem not_isPositivelyOriented_opposite (h1 : 1 < L) (hn : 0 < n) {b : UnitEdge L n}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented :=
  PeriodicLattice.Bond.opposite_not_isPositivelyOriented h1
    (by simp [PeriodicLattice.levelDepth]; omega) hb
private theorem const_one_mem_fieldSpace :
    (fun _ => (1 : ComplexMatrix2)) ∈ fieldSpace L n 0 0 := by apply _root_.YangMills.Construction.Tower.HessianDeterminants.identityField_mem <;> assumption
private theorem comp_topEdge_mem_fieldSpace (k : ℕ) {U : UnitEdge L n → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n 0 0) :
    U ∘ topEdgeEquivUnit L n k ∈ fieldSpace L n k k :=
  ⟨fun _ _ => hU.1 _ (mem_univ _), fun b _ => hU.2 (topEdgeEquivUnit L n k b) (mem_univ _)⟩
private theorem comp_topVertex_mem_gaugeGroupAt (k : ℕ) {v : Vertex L n 0 0 → ComplexMatrix2}
    (hv : v ∈ gaugeGroupAt L n 0 0) :
    v ∘ topVertexEquivUnit L n k ∈ gaugeGroupAt L n k k :=
  fun _ => hv _
private def preimageVertex (d : ℤ)
    (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (x : PeriodicLattice.Site L n d) : PeriodicLattice.Site L n d :=
  Classical.epsilon fun x' => f x' = x
private def preimageEdge (d : ℤ)
    (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (b : PeriodicLattice.Bond L n d) : PeriodicLattice.Bond L n d :=
  Classical.epsilon fun b' : PeriodicLattice.Bond L n d =>
    b'.source = preimageVertex d f b.source ∧ b'.target = preimageVertex d f b.target
private theorem cast_preimageEdge {d d' : ℤ} (h : d = d')
    (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (b : PeriodicLattice.Bond L n d) :
    Equiv.cast (congrArg (PeriodicLattice.Bond L n) h) (preimageEdge d f b) =
      preimageEdge d' f (Equiv.cast (congrArg (PeriodicLattice.Bond L n) h) b) := by
  subst h
  rfl
private theorem pushField_comp_topEdge (k : ℕ)
    (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (U : UnitEdge L n → ComplexMatrix2) :
    pushField (k := 0) (j := 0) f U ∘ topEdgeEquivUnit L n k =
      pushField (k := k) (j := k) f (U ∘ topEdgeEquivUnit L n k) := by
  funext b
  rw [← topEdgeEquiv_eq_topEdgeEquivUnit]
  change U (preimageEdge _ f (topEdgeEquiv L n k b)) = U (topEdgeEquiv L n k (preimageEdge _ f b))
  exact congrArg U (cast_preimageEdge (by simp [PeriodicLattice.levelDepth]) f b).symm
section GermAtIdentity
open Classical in
private def extendPositiveValues (w : PositiveUnitEdge L n → ComplexMatrix2) :
    UnitEdge L n → ComplexMatrix2 :=
  fun b => if h : b.IsPositivelyOriented then w ⟨b, h⟩
    else if h' : b.opposite.IsPositivelyOriented then (w ⟨b.opposite, h'⟩).conjTranspose
    else 1
private theorem continuous_extendPositiveValues :
    Continuous (extendPositiveValues :
      (PositiveUnitEdge L n → ComplexMatrix2) → UnitEdge L n → ComplexMatrix2) := by
  refine continuous_pi fun b => ?_
  by_cases h : b.IsPositivelyOriented
  · simp only [extendPositiveValues, dif_pos h]
    exact continuous_apply _
  · by_cases h' : b.opposite.IsPositivelyOriented
    · simp only [extendPositiveValues, dif_neg h, dif_pos h']
      exact (continuous_apply _).matrix_conjTranspose
    · simp only [extendPositiveValues, dif_neg h, dif_neg h']
      exact continuous_const
private theorem inv_eq_conjTranspose_of_mem {A : ComplexMatrix2}
    (h : A ∈ ComplexMatrix2.specialUnitary) : A⁻¹ = A.conjTranspose := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_eq_conjTranspose_of_mem_specialUnitary <;> assumption
private theorem fieldOfPositiveValues_eq_extend {w : PositiveUnitEdge L n → ComplexMatrix2}
    (hw : w ∈ specialUnitaryPower (PositiveUnitEdge L n)) :
    fieldOfPositiveValues (k := 0) (j := 0) w = extendPositiveValues w := by
  funext b
  unfold fieldOfPositiveValues extendPositiveValues
  by_cases h : b.IsPositivelyOriented
  · simp only [dif_pos h]
  · by_cases h' : b.opposite.IsPositivelyOriented
    · simp only [dif_neg h, dif_pos h']
      exact inv_eq_conjTranspose_of_mem (hw _)
    · simp only [dif_neg h, dif_neg h']
private theorem fieldOfPositiveValues_mem_fieldSpace (h1 : 1 < L) (hn : 0 < n)
    {w : PositiveUnitEdge L n → ComplexMatrix2}
    (hw : w ∈ specialUnitaryPower (PositiveUnitEdge L n)) :
    fieldOfPositiveValues (k := 0) (j := 0) w ∈ fieldSpace L n 0 0 := by
  have hpos : ∀ b : UnitEdge L n, ∀ h : b.IsPositivelyOriented,
      fieldOfPositiveValues (k := 0) (j := 0) w b = w ⟨b, h⟩ := fun b h => by
    simp only [fieldOfPositiveValues, dif_pos h]
  have hneg : ∀ b : UnitEdge L n, ∀ h : ¬ b.IsPositivelyOriented,
      fieldOfPositiveValues (k := 0) (j := 0) w b =
        (w ⟨b.opposite, isPositivelyOriented_opposite_of_not h⟩)⁻¹ := fun b h => by
    simp only [fieldOfPositiveValues, dif_neg h, dif_pos (isPositivelyOriented_opposite_of_not h)]
  have hG : ∀ c, w c ∈ ComplexMatrix2.specialUnitary := hw
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases h : b.IsPositivelyOriented
    · rw [hpos b h]
      exact hG _
    · rw [hneg b h]
      exact PeriodicLattice.inv_mem_specialUnitary (hG _)
  · by_cases h : b.IsPositivelyOriented
    · rw [hneg b.opposite (not_isPositivelyOriented_opposite h1 hn h), hpos b h]
      rfl
    · rw [hneg b h, hpos b.opposite (isPositivelyOriented_opposite_of_not h)]
      have hd : IsUnit (w ⟨b.opposite, isPositivelyOriented_opposite_of_not h⟩).det := by
        rw [(Matrix.mem_specialUnitaryGroup_iff.1 (hG _)).2]
        exact isUnit_one
      exact (Matrix.nonsing_inv_nonsing_inv _ hd).symm
private theorem analyticNearIdentity_congr (h1 : 1 < L) (hn : 0 < n)
    {f g : (UnitEdge L n → ComplexMatrix2) → ℝ} (hf : IsAnalyticNearIdentity f)
    (hg : EventuallyNearIdentity (fieldSpace L n 0 0) fun U => g U = f U) :
    IsAnalyticNearIdentity g := by
  obtain ⟨inst, O, ⟨O₀, hO₀, rfl⟩, hone, hf⟩ := hf
  obtain ⟨T, hT, hone', hsub⟩ := mem_nhdsWithin.1 hg
  refine ⟨inst, (O₀ ∩ extendPositiveValues ⁻¹' T) ∩ specialUnitaryPower (PositiveUnitEdge L n),
    ⟨_, hO₀.inter (hT.preimage continuous_extendPositiveValues), rfl⟩, ?_, fun β p hp => ?_⟩
  · refine ⟨⟨hone.1, ?_⟩, hone.2⟩
    have e : extendPositiveValues (fun _ => (1 : ComplexMatrix2)) =
        fun _ : UnitEdge L n => (1 : ComplexMatrix2) := by
      rw [← fieldOfPositiveValues_eq_extend hone.2]
      funext b
      by_cases h : b.IsPositivelyOriented
      · simp only [fieldOfPositiveValues, dif_pos h]
      · simp only [fieldOfPositiveValues, dif_neg h,
          dif_pos (isPositivelyOriented_opposite_of_not h), inv_one]
    change extendPositiveValues (fun _ => (1 : ComplexMatrix2)) ∈ T
    rw [e]
    exact hone'
  · obtain ⟨W, Φ, hp', hΦ, hv⟩ := hf β p ⟨hp.1.1, hp.2⟩
    refine ⟨W, Φ, hp', hΦ, fun x hx hxW => ?_⟩
    rw [hv x ⟨hx.1.1, hx.2⟩ hxW]
    have hc := fieldOfPositiveValues_mem_fieldSpace h1 hn hx.2
    have hT' : fieldOfPositiveValues (k := 0) (j := 0) x ∈ T := by
      rw [fieldOfPositiveValues_eq_extend hx.2]
      exact hx.1.2
    exact congrArg Complex.ofReal (hsub ⟨hT', hc⟩).symm
private theorem matExp_I_smul_mem {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.ExpSurjective.matExp_I_smul_mem_specialUnitary <;> assumption
private theorem expTwist_identity_of_pos (B : UnitEdge L n → ComplexMatrix2) {b : UnitEdge L n}
    (h : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist B (identityField L n) b =
      ComplexMatrix2.matExp (Complex.I • B b) := by
  simp [PeriodicLattice.expTwist, h, identityField]
private theorem expTwist_identity_of_not_pos (B : UnitEdge L n → ComplexMatrix2)
    {b : UnitEdge L n} (h : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist B (identityField L n) b =
      (ComplexMatrix2.matExp (Complex.I • B b.opposite))⁻¹ := by
  simp [PeriodicLattice.expTwist, h, identityField]
private theorem expTwist_identity_mem (h1 : 1 < L) (hn : 0 < n)
    {B : UnitEdge L n → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n 0 0) :
    PeriodicLattice.expTwist B (identityField L n) ∈ fieldSpace L n 0 0 := by
  have hE : ∀ b : UnitEdge L n, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • B b) ∈ ComplexMatrix2.specialUnitary :=
    fun b h => matExp_I_smul_mem (hB.1 b h)
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases h : b.IsPositivelyOriented
    · rw [expTwist_identity_of_pos B h]
      exact hE b h
    · rw [expTwist_identity_of_not_pos B h]
      exact PeriodicLattice.inv_mem_specialUnitary (hE _ (isPositivelyOriented_opposite_of_not h))
  · by_cases h : b.IsPositivelyOriented
    · rw [expTwist_identity_of_not_pos B (not_isPositivelyOriented_opposite h1 hn h),
        expTwist_identity_of_pos B h]
      rfl
    · rw [expTwist_identity_of_not_pos B h,
        expTwist_identity_of_pos B (isPositivelyOriented_opposite_of_not h)]
      have hd : IsUnit (ComplexMatrix2.matExp (Complex.I • B b.opposite)).det := by
        rw [(Matrix.mem_specialUnitaryGroup_iff.1
          (hE _ (isPositivelyOriented_opposite_of_not h))).2]
        exact isUnit_one
      exact (Matrix.nonsing_inv_nonsing_inv _ hd).symm
private theorem tendsto_expTwist_identity (R R' : UnitEdge L n → ComplexMatrix2) :
    Tendsto (fun q : ℝ × ℝ => PeriodicLattice.expTwist
        (algebraMap ℝ ℂ q.1 • R + algebraMap ℝ ℂ q.2 • R') (identityField L n))
      (𝓝 (0, 0)) (𝓝 fun _ => (1 : ComplexMatrix2)) := by
  refine tendsto_pi_nhds.2 fun b => ?_
  have hX : ∀ c : UnitEdge L n, Continuous fun q : ℝ × ℝ =>
      Complex.I • (algebraMap ℝ ℂ q.1 • R + algebraMap ℝ ℂ q.2 • R') c := fun c => by
    change Continuous fun q : ℝ × ℝ =>
      Complex.I • (((q.1 : ℝ) : ℂ) • R c + ((q.2 : ℝ) : ℂ) • R' c)
    fun_prop
  have hlim : ∀ Z : ℝ × ℝ → ComplexMatrix2, Continuous Z → Z (0, 0) = 0 →
      Tendsto (fun q => ComplexMatrix2.matExp (Z q)) (𝓝 (0, 0)) (𝓝 1) := fun Z hZ h0 => by
    have hc : Continuous (ComplexMatrix2.matExp : ComplexMatrix2 → ComplexMatrix2) := by
      let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
      exact NormedSpace.exp_continuous
    have h := (hc.comp hZ).tendsto (0, 0)
    simpa [h0, Function.comp_def, ComplexMatrix2.matExp, NormedSpace.exp_zero] using h
  by_cases h : b.IsPositivelyOriented
  · simp only [expTwist_identity_of_pos _ h]
    exact hlim _ (hX b) (by simp)
  · simp only [expTwist_identity_of_not_pos _ h]
    have e : ∀ q : ℝ × ℝ, (ComplexMatrix2.matExp (Complex.I • (algebraMap ℝ ℂ q.1 • R +
        algebraMap ℝ ℂ q.2 • R') b.opposite))⁻¹ =
        ComplexMatrix2.matExp (-(Complex.I • (algebraMap ℝ ℂ q.1 • R +
          algebraMap ℝ ℂ q.2 • R') b.opposite)) := fun q => (Matrix.exp_neg _).symm
    simp only [e]
    exact hlim _ (hX b.opposite).neg (by simp)
private theorem hessianAtIdentity_congr (h1 : 1 < L) (hn : 0 < n) {F G : FieldFamily L}
    (h : EventuallyNearIdentity (fieldSpace L n 0 0) fun U => F n U = G n U)
    {R R' : UnitEdge L n → ComplexMatrix2} (hR : R ∈ edgeFormSpace L n 0 0)
    (hR' : R' ∈ edgeFormSpace L n 0 0) :
    hessianAtIdentity F n R R' = hessianAtIdentity G n R R' := by
  have hmem : ∀ q : ℝ × ℝ, PeriodicLattice.expTwist
      (algebraMap ℝ ℂ q.1 • R + algebraMap ℝ ℂ q.2 • R') (identityField L n) ∈
        fieldSpace L n 0 0 := fun q => by
    apply expTwist_identity_mem h1 hn
    have e : algebraMap ℝ ℂ q.1 • R + algebraMap ℝ ℂ q.2 • R' = q.1 • R + q.2 • R' := by
      simp only [algebraMap_smul]
    rw [e]
    exact add_mem (Submodule.smul_mem _ _ hR) (Submodule.smul_mem _ _ hR')
  have ht := tendsto_nhdsWithin_iff.2 ⟨tendsto_expTwist_identity R R', Eventually.of_forall hmem⟩
  have hc := (ht.eventually h).curry_nhds
  unfold hessianAtIdentity leftSecondDeriv mixedDirectionalDeriv
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [hc] with s hs
  exact Filter.EventuallyEq.deriv_eq hs
private theorem realComponent_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) : realComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p16359 <;> assumption
private theorem imagComponent_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) : imagComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p9724 <;> assumption
private theorem complexHessian_congr (h1 : 1 < L) (hn : 0 < n) {F G : FieldFamily L}
    (h : EventuallyNearIdentity (fieldSpace L n 0 0) fun U => F n U = G n U)
    {B B' : UnitEdge L n → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n 0 0)
    (hB' : B' ∈ complexEdgeForms L n 0 0) :
    complexHessian F n B B' = complexHessian G n B B' := by
  have e₁ := hessianAtIdentity_congr h1 hn h (realComponent_mem hB) (realComponent_mem hB')
  have e₂ := hessianAtIdentity_congr h1 hn h (imagComponent_mem hB) (imagComponent_mem hB')
  have e₃ := hessianAtIdentity_congr h1 hn h (realComponent_mem hB) (imagComponent_mem hB')
  have e₄ := hessianAtIdentity_congr h1 hn h (imagComponent_mem hB) (realComponent_mem hB')
  simp only [complexHessian, e₁, e₂, e₃, e₄]
end GermAtIdentity
private def stepDifference (hL : 0 < L) (i : ℕ) : FieldFamily L :=
  logNormaliserFamily L (i + 1) - compStep hL i (logNormaliserFamily L i)
private theorem logNormaliserFamily_transport {X : Type*} {m : ℕ} (i : ℕ) (h : m = n + 1)
    (e₀ : X ≃ Edge L m i i) (V : X → ComplexMatrix2) :
    logNormaliserFamily L i (n + 1) (transportTotal (e₀.trans ((topEdgeEquiv L m i).trans
        (Equiv.cast (congrArg (UnitEdge L) h)))) V) =
      logTotalNormaliserRatio L m i (transportTotal e₀ V) := by
  subst h
  have e : transportTotal (e₀.trans ((topEdgeEquiv L (n + 1) i).trans
      (Equiv.cast (congrArg (UnitEdge L) rfl)))) V =
      transportTotal (topEdgeEquivUnit L (n + 1) i) (transportTotal e₀ V) := by
    rw [← topEdgeEquiv_eq_topEdgeEquivUnit]
    funext b
    rfl
  rw [e, logNormaliserFamily_transportTotal]
private theorem compStep_logFamily_eq_level (hL : 0 < L) (n i : ℕ)
    (W : Edge L n (i + 1) (i + 1) → ComplexMatrix2) :
    compStep hL i (logNormaliserFamily L i) n
        (transportTotal (topEdgeEquivUnit L n (i + 1)) W) =
      logLevelNormaliserRatio hL (Nat.le_succ i) (chosenProlong L n (i + 1) i W) := by
  rw [← topEdgeEquiv_eq_topEdgeEquivUnit, compStep_transportTotal]
  exact logNormaliserFamily_transport i (scaledExponent_succ_self n i)
    (scaleEdge hL (Nat.le_succ i) i) _
private theorem near_stepDifference (hP : NormaliserProductTheorem) (hL : 0 < L)
    (hst : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (i : ℕ) :
    EventuallyNearIdentity (fieldSpace L n 0 0) fun U =>
      stepNormaliserFamily L i n U = stepDifference hL i n U := by
  have h := (hP L n i hst hn).log_eq
  have t := tendsto_comp_nhdsWithin_one (topEdgeEquivUnit L n (i + 1))
    (D := fieldSpace L n 0 0) (D' := fieldSpace L n (i + 1) (i + 1))
    fun U hU => comp_topEdge_mem_fieldSpace (i + 1) hU
  refine (t.eventually h).mono fun U hU => ?_
  obtain ⟨-, -, e⟩ := hU
  have e' : logTotalNormaliserRatio L n (i + 1) (U ∘ topEdgeEquivUnit L n (i + 1)) =
      logNormaliserRatio L n (i + 1) i (U ∘ topEdgeEquivUnit L n (i + 1)) +
        logLevelNormaliserRatio hL (Nat.le_succ i)
          (chosenProlong L n (i + 1) i (U ∘ topEdgeEquivUnit L n (i + 1))) := e
  have hU' : transportTotal (topEdgeEquivUnit L n (i + 1))
      (U ∘ topEdgeEquivUnit L n (i + 1)) = U := by
    funext b
    simp [transportTotal]
  have h2 := compStep_logFamily_eq_level hL n i (U ∘ topEdgeEquivUnit L n (i + 1))
  rw [hU'] at h2
  change logNormaliserRatio L n (i + 1) i (U ∘ topEdgeEquivUnit L n (i + 1)) =
    logTotalNormaliserRatio L n (i + 1) (U ∘ topEdgeEquivUnit L n (i + 1)) -
      compStep hL i (logNormaliserFamily L i) n U
  rw [h2, e']
  ring
private theorem isAdmissibleMember_step (hP : NormaliserProductTheorem)
    (hN : NormalisersHold) (hL : 0 < L)
    (hst : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (i : ℕ)
    (hE : IsAdmissibleMember (stepDifference hL i n)) :
    IsAdmissibleMember (stepNormaliserFamily L i n) := by
  have h1 : 1 < L := lt_of_lt_of_le (by norm_num) hst.2
  have hnear := near_stepDifference hP hL hst hn i
  have hS := hN L n (i + 1) hst hn i le_rfl
  have tc := tendsto_comp_nhdsWithin_one (topEdgeEquivUnit L n (i + 1))
    (D := fieldSpace L n 0 0) (D' := fieldSpace L n (i + 1) (i + 1))
    fun U hU => comp_topEdge_mem_fieldSpace (i + 1) hU
  have tg := tendsto_comp_nhdsWithin_one (topVertexEquivUnit L n (i + 1))
    (D := gaugeGroupAt L n 0 0) (D' := gaugeGroupAt L n (i + 1) (i + 1))
    fun v hv => comp_topVertex_mem_gaugeGroupAt (i + 1) hv
  refine ⟨analyticNearIdentity_congr h1 hn hE.analytic hnear, ?_, ?_, ?_, ?_⟩
  · have e := Filter.Eventually.self_of_nhdsWithin hnear const_one_mem_fieldSpace
    exact e.trans hE.map_identity
  · obtain ⟨pa, hpa, pb, hpb, hprod⟩ :=
      Filter.eventually_prod_iff.1 hS.logRatio_gauge_invariant.1
    refine ⟨{v | pa (v ∘ topVertexEquivUnit L n (i + 1))}, tg.eventually hpa, ?_⟩
    refine (tc.eventually hpb).mono fun U hU v _ hv => ?_
    exact hprod hv hU
  · refine (tc.eventually hS.logRatio_gauge_invariant.2).mono fun U hU g hg => ?_
    exact hU (fun _ => g) (fun _ => hg) fun _ _ => rfl
  · refine (tc.eventually hS.logRatio_symmetry_invariant).mono fun U hU σ hσ hl => ?_
    have e : stepNormaliserFamily L i n (pushField (k := 0) (j := 0) σ U) =
        logNormaliserRatio L n (i + 1) i (pushField (k := i + 1) (j := i + 1) σ
          (U ∘ topEdgeEquivUnit L n (i + 1))) := by
      change logNormaliserRatio L n (i + 1) i
        (pushField (k := 0) (j := 0) σ U ∘ topEdgeEquivUnit L n (i + 1)) = _
      rw [pushField_comp_topEdge]
    rw [e]
    refine hU σ ⟨hσ, ?_⟩
    unfold MapsSublatticeOnto at hl ⊢
    rw [FunctionalStiffness.sublattice_levelDepth_self]
    exact hl
private theorem isLatticeFunctional_step (hP : NormaliserProductTheorem)
    (hN : NormalisersHold) (hL : 0 < L)
    (hst : Conventions.IsAdmissibleBlockingFactor L) (i : ℕ)
    (hE : IsLatticeFunctional L (stepDifference hL i)) :
    IsLatticeFunctional L (stepNormaliserFamily L i) := by
  obtain ⟨s₀, hs₀, h⟩ := hE
  exact ⟨s₀, hs₀, fun s hs hle m hm hside =>
    isAdmissibleMember_step hP hN hL hst hm i (h s hs hle m hm hside)⟩
private theorem isTemperedWitness_step (hP : NormaliserProductTheorem)
    (hW : PlaneWaveSymmetries.PlaneWaveLawsHold) (hL : 0 < L)
    (hst : Conventions.IsAdmissibleBlockingFactor L) (i : ℕ) {δ : ℝ} {π : SymbolArray}
    {e : ℕ → ℝ} (c : IsTemperedWitness L (stepDifference hL i) δ π e) :
    IsTemperedWitness L (stepNormaliserFamily L i) δ π e := by
  have h1 : 1 < L := lt_of_lt_of_le (by norm_num) hst.2
  refine ⟨c.delta_pos, c.analytic, c.err_nonneg, c.err_tendsto, ?_⟩
  obtain ⟨s₀, hs₀, h⟩ := c.approx
  refine ⟨s₀, hs₀, fun s hs hle m hm hside p hp a a' μ ν => ?_⟩
  have hW' := hW L m hst hm
  rw [complexHessian_congr h1 hm (near_stepDifference hP hL hst hm i)
    (hW'.mem_complex a μ p hp) (hW'.mem_complex a' ν (-p) (neg_mem hp))]
  exact h s hs hle m hm hside p hp a a' μ ν
private theorem stiffnessConstant_eq_of_witness
    (hK : TemperedStiffness.TemperedStiffnessClaim) (hL : 0 < L)
    (hst : Conventions.IsAdmissibleBlockingFactor L) {F G : FieldFamily L} {δ : ℝ}
    {π : SymbolArray} {e : ℕ → ℝ} (hF : IsLatticeFunctional L F) (hG : IsLatticeFunctional L G)
    (cF : IsTemperedWitness L F δ π e) (cG : IsTemperedWitness L G δ π e) :
    FunctionalStiffness.stiffnessConstant hL F = FunctionalStiffness.stiffnessConstant hL G := by
  obtain ⟨-, -, -, b, -, -, f⟩ := hK L hL hst F δ π e hF cF
  obtain ⟨-, -, -, b', -, -, g⟩ := hK L hL hst G δ π e hG cG
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  exact Complex.ofReal_injective ((f 0 1 h01).hasSum_mixed.unique (g 0 1 h01).hasSum_mixed)
private theorem logNormaliserFamily_tempered (hT : NormaliserTempered.TemperedAndStiffness)
    (hD : GaugeColourMomenta.GaugeColourMomentumClaim) (hL : 0 < L)
    (hst : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    IsTemperedFunctional L (logNormaliserFamily L k) ∧
      (k = 0 → FunctionalStiffness.stiffnessConstant hL (logNormaliserFamily L k) = 0) := by
  obtain ⟨δ₀, -, h⟩ := hT
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have t1 := (h L hL hst 1 le_rfl).1
    obtain ⟨-, hz, -, hc⟩ := (hD L hL hst).2 _ _ t1 t1
    have e : logNormaliserFamily L 1 - logNormaliserFamily L 1 =
        logNormaliserFamily L 0 := by
      funext m U
      rw [logNormaliserFamily_zero]
      simp
    rw [e] at hz hc
    exact ⟨hz, fun _ => by rw [hc, sub_self]⟩
  · exact ⟨(h L hL hst k hk).1, fun h0 => absurd h0 hk.ne'⟩
private theorem step_tempered_and_stiffness (hT : NormaliserTempered.TemperedAndStiffness)
    (hC : TemperedComposition.TemperedCompStep)
    (hD : GaugeColourMomenta.GaugeColourMomentumClaim)
    (hK : TemperedStiffness.TemperedStiffnessClaim)
    (hP : NormaliserProductTheorem)
    (hN : NormalisersHold)
    (hW : PlaneWaveSymmetries.PlaneWaveLawsHold) (hL : 0 < L)
    (hst : Conventions.IsAdmissibleBlockingFactor L) (i : ℕ) :
    IsTemperedFunctional L (stepNormaliserFamily L i) ∧
      FunctionalStiffness.stiffnessConstant hL (stepNormaliserFamily L i) =
        FunctionalStiffness.stiffnessConstant hL (logNormaliserFamily L (i + 1)) -
          FunctionalStiffness.stiffnessConstant hL (logNormaliserFamily L i) := by
  have t1 := (logNormaliserFamily_tempered hT hD hL hst (i + 1)).1
  have t0 := (logNormaliserFamily_tempered hT hD hL hst i).1
  obtain ⟨tc, ec⟩ := hC L hL hst _ i t0
  obtain ⟨-, hE, -, hc⟩ := (hD L hL hst).2 _ _ t1 tc
  have hE' : IsTemperedFunctional L (stepDifference hL i) := hE
  obtain ⟨hf, δ, π, e, c⟩ := hE'
  have hf' := isLatticeFunctional_step hP hN hL hst i hf
  have c' := isTemperedWitness_step hP hW hL hst i c
  refine ⟨⟨hf', δ, π, e, c'⟩, ?_⟩
  rw [stiffnessConstant_eq_of_witness hK hL hst hf' hf c' c, ← ec, ← hc]
  rfl
theorem incrementsSumToTotal_holds (hT : NormaliserTempered.TemperedAndStiffness)
    (hC : TemperedComposition.TemperedCompStep)
    (hD : GaugeColourMomenta.GaugeColourMomentumClaim)
    (hK : TemperedStiffness.TemperedStiffnessClaim)
    (hP : NormaliserProductTheorem)
    (hN : NormalisersHold)
    (hW : PlaneWaveSymmetries.PlaneWaveLawsHold) :
    IncrementsSumToTotal := by
  refine ⟨fun L hst i => (step_tempered_and_stiffness hT hC hD hK hP hN hW
    (lt_of_lt_of_le (by norm_num) hst.2) hst i).1, ?_, fun L hL hst k => ?_⟩
  · refine ⟨fun q => if h : 0 < q.2 then FunctionalStiffness.stiffnessConstant h
      (stepNormaliserFamily q.2 q.1) else 0, fun d => ?_⟩
    simp only [dif_pos d.factor_pos]
    rfl
  · rw [Finset.sum_congr rfl fun i _ => (step_tempered_and_stiffness hT hC hD hK hP hN hW hL hst i).2,
      Finset.sum_range_sub (fun i => FunctionalStiffness.stiffnessConstant hL
        (logNormaliserFamily L i)) k, (logNormaliserFamily_tempered hT hD hL hst 0).2 rfl, sub_zero]
end YangMills.Construction.OneLoopLaw.IncrementSum
end

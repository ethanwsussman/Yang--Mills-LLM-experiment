import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.FirstPartProofForm
import YangMills.Construction.GrowingTori.MultilinearityOnADomainThatIsNotLinearProof
import Mathlib
set_option autoImplicit false
open Set
open scoped NNReal ENNReal ComplexConjugate
namespace YangMills.Construction
section
open Set Filter Topology
open scoped NNReal ENNReal ComplexConjugate
noncomputable section
namespace ToriLimits.GrowingVolumeLimits.ProofSteps.LimitInvariance
open PeriodicSpace TorusTransport TorusTransport.TestFunctionOrders
open GrowingTori (shiftFamily hyperoctahedralActFamily euclideanTranslation)
open TimeAxisSymbols (motionHomeomorph isEuclideanMotion_translationEquiv
  isEuclideanMotion_hyperoctahedral)
variable {D : Setup}
namespace MotionsOfLimit
theorem supp_comp_euclideanMotion {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s)
    (f : RealFn) : tsupport (f ∘ s) = s ⁻¹' tsupport f :=
  tsupport_comp_eq_preimage f (motionHomeomorph hs)
theorem comp_mem_sepC1Tuples (Y : PeriodicSpace.Params) {n : ℕ}
    {f : Fin n → RealFn}
    (hf : f ∈ Kind.sepC1Tuples Y .euclidean n) {s : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hs : IsEuclideanMotion s) :
    (fun i => f i ∘ s) ∈ Kind.sepC1Tuples Y .euclidean n := by
  obtain ⟨h₁, h₂, h₃⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff f).1 hf
  have hsupp : ∀ g : RealFn,
      BallTuples.fnSupport (g ∘ s) = s ⁻¹' BallTuples.fnSupport g :=
    supp_comp_euclideanMotion hs
  refine (BallTuples.mem_sepC1Tuples_euclidean_iff _).2 ⟨fun l => ?_, fun l => ?_, fun l l' hl => ?_⟩
  · exact (h₁ l).comp (TimeAxisSymbols.contDiff_of_isEuclideanMotion hs)
  · rw [hsupp]
    exact (motionHomeomorph hs).isCompact_preimage.2 (h₂ l)
  · rw [hsupp, hsupp]
    exact (h₃ l l' hl).preimage s
theorem mem_lipTuplesBall_of_sepC1 {Y : PeriodicSpace.Params} {n : ℕ}
    {f : Fin n → RealFn}
    (hf : f ∈ Kind.sepC1Tuples Y .euclidean n) {ρ : ℝ}
    (hρ : SuppsWithin f (ballOrigin ρ)) : f ∈ BallTuples.lipTuplesBall n ρ := by
  obtain ⟨h₁, h₂, h₃⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff f).1 hf
  exact ⟨⟨fun l => BallTuples.isLipschitzFor_of_contDiff (h₁ l) (h₂ l), h₂, h₃⟩,
    fun l => ⟨h₂ l, hρ l⟩⟩
theorem suppsWithin_ball_mono {n : ℕ} {f : Fin n → RealFn} {ρ ρ' : ℝ}
    (hρ : SuppsWithin f (ballOrigin ρ)) (h : ρ ≤ ρ') : SuppsWithin f (ballOrigin ρ') :=
  fun i _ hx => lt_of_lt_of_le (hρ i hx) h
theorem exists_suppsWithin_ball (h : CitedFacts) {Y : PeriodicSpace.Params} {n : ℕ} (hn : 2 ≤ n)
    {f : Fin n → RealFn}
    (hf : f ∈ Kind.sepC1Tuples Y .euclidean n) :
    ∃ ρ : ℝ, 0 < ρ ∧ SuppsWithin f (ballOrigin ρ) := by
  obtain ⟨h₁, h₂, h₃⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff f).1 hf
  have hl : IsSepLipTuple f :=
    ⟨fun l => BallTuples.isLipschitzFor_of_contDiff (h₁ l) (h₂ l), h₂, h₃⟩
  exact (h.collars.2.2.2.1 n hn f hl).2.1
theorem limit_eq_of_eventually_eq {S : ToriSequence D} {J : Sequences.PNatIndexSet} {n : ℕ}
    {f g : Fin n → RealFn} {z z' : ℂ} (hf : S.TendsAlong J f z)
    (hg : S.TendsAlong J g z')
    (h : ∃ j₀ : ℕ+, ∀ j, j₀ ≤ j → S.connected j f = S.connected j g) : z = z' := by
  obtain ⟨j₀, hj₀⟩ := h
  by_contra hne
  have hpos : 0 < ‖z - z'‖ / 2 := half_pos (norm_pos_iff.2 (sub_ne_zero.2 hne))
  obtain ⟨a, ha⟩ := hf _ hpos
  obtain ⟨b, hb⟩ := hg _ hpos
  obtain ⟨j, hj, hlt⟩ := J.infinite.exists_gt (max j₀ ⟨(max a b).toNat + 1, by omega⟩)
  have hlt₁ : j₀ ≤ j := (le_max_left _ _).trans hlt.le
  have hlt₂ : (⟨(max a b).toNat + 1, by omega⟩ : ℕ+) ≤ j := (le_max_right _ _).trans hlt.le
  have hle : max a b ≤ (((j : ℕ+) : ℕ) : ℤ) := by
    have h₁ : (max a b).toNat + 1 ≤ (j : ℕ) := hlt₂
    omega
  obtain ⟨u, hu⟩ := ha j hj ((le_max_left _ _).trans hle)
  obtain ⟨u', hu'⟩ := hb j hj ((le_max_right _ _).trans hle)
  replace hu : ‖S.connected j f - z‖ < ‖z - z'‖ / 2 := hu
  replace hu' : ‖S.connected j g - z'‖ < ‖z - z'‖ / 2 := hu'
  rw [hj₀ j hlt₁] at hu
  have : ‖z - z'‖ < ‖z - z'‖ / 2 + ‖z - z'‖ / 2 := by
    calc ‖z - z'‖ = ‖(S.connected j g - z') - (S.connected j g - z)‖ := by congr 1; ring
      _ ≤ ‖S.connected j g - z'‖ + ‖S.connected j g - z‖ := norm_sub_le _ _
      _ < ‖z - z'‖ / 2 + ‖z - z'‖ / 2 := by linarith
  linarith
theorem connectedFn_tupleComp (h : CitedFacts) (S : ToriSequence D) {n : ℕ} (hn : 2 ≤ n)
    (j : ℕ+) (s : TorusPeriodization.euclideanMotions)
    (hs : CentredTensorMoments.TorusFunctionals.IsLatticeSymmetry
      (LatticeLevel.momentDataAt S j) s)
    {X : Fin n → RealFn}
    (hX : X ∈ BallTuples.lipTuplesBall n (S.radius j))
    (hXs : BallPeriodization.tupleComp X s ∈
      BallTuples.lipTuplesBall n (S.radius j)) :
    S.connected j (BallPeriodization.tupleComp X s) = S.connected j X := by
  have hr : (LatticeLevel.momentDataAt S j).IsRadius (S.radius j) := by
    rw [S.radius_eq_latticeRadius]
    exact D.isRadius_latticeRadius _ _ _ _
  exact (h.functionals _ _ hr).2.2.2.1 n hn s hs X hX hXs
theorem eventually_le_radiusAt (h : CitedFacts) (S : ToriSequence D) (ρ : ℝ) :
    ∃ j₀ : ℕ+, ∀ j, j₀ ≤ j → ρ ≤ S.radius j :=
  eventually_atTop.1 ((h.cumulants D S).1.2.1.eventually_ge_atTop ρ)
theorem func_tupleComp (h : CitedFacts) {S : ToriSequence D} {J : Sequences.PNatIndexSet}
    {Ξ : D.LimitHierarchy} (hΞ : S.IsLimitHierarchy J Ξ) {n : ℕ} (hn : 2 ≤ n) (f : D.sepDomain n)
    (s : TorusPeriodization.euclideanMotions)
    (hfs : BallPeriodization.tupleComp f.1 s ∈ D.sepDomain n)
    (hs : ∃ j₀ : ℕ+, ∀ j, j₀ ≤ j →
      CentredTensorMoments.TorusFunctionals.IsLatticeSymmetry
        (LatticeLevel.momentDataAt S j) s) :
    Ξ.func n hn ⟨_, hfs⟩ = Ξ.func n hn f := by
  obtain ⟨ρ₁, -, h₁⟩ := exists_suppsWithin_ball h hn f.2
  obtain ⟨ρ₂, -, h₂⟩ := exists_suppsWithin_ball h hn hfs
  obtain ⟨j₁, hj₁⟩ := eventually_le_radiusAt h S (max ρ₁ ρ₂)
  obtain ⟨j₂, hj₂⟩ := hs
  have key := limit_eq_of_eventually_eq (hΞ n hn ⟨_, hfs⟩) (hΞ n hn f) ⟨max j₁ j₂, fun j hj => ?_⟩
  · exact_mod_cast key
  · have hρ := hj₁ j ((le_max_left _ _).trans hj)
    exact connectedFn_tupleComp h S hn j s (hj₂ j ((le_max_right _ _).trans hj))
      (mem_lipTuplesBall_of_sepC1 f.2 (suppsWithin_ball_mono h₁ ((le_max_left _ _).trans hρ)))
      (mem_lipTuplesBall_of_sepC1 hfs (suppsWithin_ball_mono h₂ ((le_max_right _ _).trans hρ)))
theorem func_hyperoctahedral (h : CitedFacts) {S : ToriSequence D} {J : Sequences.PNatIndexSet}
    {Ξ : D.LimitHierarchy} (hΞ : S.IsLimitHierarchy J Ξ) {n : ℕ} (hn : 2 ≤ n) (f : D.sepDomain n)
    (w : hyperoctahedral) (hw : hyperoctahedralActFamily w f.1 ∈ D.sepDomain n) :
    Ξ.func n hn ⟨_, hw⟩ = Ξ.func n hn f :=
  func_tupleComp h hΞ hn f
    ⟨(w⁻¹ : hyperoctahedral).1, GrowingTori.hyperoctahedral_le_euclideanMotions (w⁻¹).2⟩ hw
    ⟨1, fun _ _ => Or.inr (Or.inl (w⁻¹).2)⟩
theorem eventually_latticeSymmetry_translation (h : CitedFacts) (S : ToriSequence D)
    (a : Fin 4 → ℝ) (ha : ∀ μ, a μ ∈ PeriodicLattice.adicGridPointsPositive D.L) :
    ∃ j₀ : ℕ+, ∀ j, j₀ ≤ j →
      CentredTensorMoments.TorusFunctionals.IsLatticeSymmetry
        (LatticeLevel.momentDataAt S j) (euclideanTranslation (-a)) := by
  choose k n hkn using fun μ =>
    (PeriodicLattice.mem_adicGridPointsPositive_iff D.L (a μ)).1 (ha μ)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (S.K_tendsto.eventually_ge_atTop (∑ μ, (k μ : ℕ)))
  refine ⟨j₀, fun j hj => Or.inl ?_⟩
  have hnest := (h.nesting D.L D.admissible).2.1
  have hk : ∀ μ, k μ ≤ S.K j := fun μ => by
    have h₁ : (k μ : ℕ) ≤ ∑ ν, (k ν : ℕ) :=
      Finset.single_le_sum (f := fun ν => (k ν : ℕ)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ μ)
    exact h₁.trans (hj₀ j hj)
  choose n' hn' using fun μ => hnest (k μ) (S.K j) (hk μ) ⟨n μ, hkn μ⟩
  refine ⟨fun μ => - n' μ, fun x => ?_⟩
  funext ν
  have e := hn' ν
  show x ν + -a ν = x ν + _ * ((- n' ν : ℤ) : ℝ)
  rw [e]
  push_cast
  show _ = x ν + PeriodicLattice.meshSize D.L ((S.K j : ℕ) : ℤ) * _
  ring
theorem func_adicShift (h : CitedFacts) {S : ToriSequence D} {J : Sequences.PNatIndexSet}
    {Ξ : D.LimitHierarchy} (hΞ : S.IsLimitHierarchy J Ξ) {n : ℕ} (hn : 2 ≤ n) (f : D.sepDomain n)
    (a : Fin 4 → ℝ) (ha : ∀ μ, a μ ∈ PeriodicLattice.adicGridPointsPositive D.L)
    (hτ : shiftFamily a f.1 ∈ D.sepDomain n) :
    Ξ.func n hn ⟨_, hτ⟩ = Ξ.func n hn f :=
  func_tupleComp h hΞ hn f (euclideanTranslation (-a)) hτ
    (eventually_latticeSymmetry_translation h S a ha)
def unitMirrorData (D : Setup) : ReflectionPositivity.AxisMirror.MirrorData where
  toStandingParameters := (symbolSetup D).toStandingParameters
  β := 1
  β_pos := one_pos
def cubeScale (D : Setup) : ReflectionPositivity.AxisMirror.Ambient.ScaleParam :=
  ⟨(D.M : ℝ), Set.mem_Ici.2 (by exact_mod_cast D.one_le_M)⟩
theorem mem_compactC1 {f : RealFn} (h₁ : ContDiff ℝ 1 f)
    (hc : IsCompact (tsupport f)) :
    f ∈ ReflectionPositivity.AxisMirror.Ambient.compactC1 (unitMirrorData D) ℝ .euclidean := by
  refine ⟨h₁, ?_⟩
  have e : ReflectionPositivity.AxisMirror.Ambient.closedSupport (unitMirrorData D) .euclidean f =
      tsupport f :=
    SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
  rw [e]
  exact (SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) _).2 hc
theorem smoothModulus_eq {f : RealFn}
    (hf : f ∈ ReflectionPositivity.AxisMirror.Ambient.compactC1 (unitMirrorData D) ℝ .euclidean)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ReflectionPositivity.AxisMirror.Ambient.smoothModulus (cubeScale D)
        (⟨f, hf⟩ : ReflectionPositivity.AxisMirror.Ambient.compactC1 (unitMirrorData D) ℝ .euclidean)
        δ.toNNReal =
      D.params.toGrowth.shiftModulus f δ := by
  have e₁ : (ReflectionPositivity.AxisMirror.Ambient.gradSup (⟨f, hf⟩ :
        ReflectionPositivity.AxisMirror.Ambient.compactC1 (unitMirrorData D) ℝ .euclidean)).toReal =
      (GrowingTori.Ambient.euclidean :
        GrowingTori.Ambient D.params.toGrowth.L).gradSup f := rfl
  have e₂ : (ReflectionPositivity.AxisMirror.Ambient.gradOsc (⟨f, hf⟩ :
        ReflectionPositivity.AxisMirror.Ambient.compactC1 (unitMirrorData D) ℝ .euclidean)
          δ.toNNReal).toReal =
      D.params.toGrowth.gradModulus f δ := by
    unfold ReflectionPositivity.AxisMirror.Ambient.gradOsc GrowingTori.GrowthParameters.gradModulus
      GrowingTori.GrowthParameters.gradOscSup
    congr 1
    refine iSup_congr fun (x : Fin 4 → ℝ) => iSup_congr fun (y : Fin 4 → ℝ) => ?_
    have e₃ : (ReflectionPositivity.AxisMirror.Ambient.metric (unitMirrorData D) .euclidean x y ≤
        (δ.toNNReal : ℝ)) = (TorusMetric.euclidNormVec (x - y) ≤ δ) := by
      rw [Real.coe_toNNReal _ hδ]
      rfl
    refine iSup_congr_Prop e₃.to_iff fun _ => ?_
    congr 1
    simp only [ReflectionPositivity.AxisMirror.Ambient.vecLength, TorusMetric.euclidNormVec,
      Real.norm_eq_abs, sq_abs]
    rfl
  unfold ReflectionPositivity.AxisMirror.Ambient.smoothModulus GrowingTori.GrowthParameters.shiftModulus
  rw [e₁, e₂, Real.coe_toNNReal _ hδ]
  rfl
theorem sharpNormR4_comp_translation (h : CitedFacts) {f : RealFn} (hL : LipschitzR4 f)
    (hc : IsCompact (tsupport f)) (a : Fin 4 → ℝ) :
    TestFunctions.sharpNormR4 (D.M : ℝ) (f ∘ translationEquiv (-a)) =
      TestFunctions.sharpNormR4 (D.M : ℝ) f := by
  have h₁ := ((h.translations (unitMirrorData D) (cubeScale D)).2.2.1 1 (one_mem _) (-a)).2.1 f hL hc
  have e : orthoAffine (1 : Matrix (Fin 4) (Fin 4) ℝ) (-a) = translationEquiv (-a) := by
    funext x
    simp [orthoAffine]
  rw [e] at h₁
  exact h₁.2.2.2.1
theorem sharpNormR4_translation_sub_le (h : CitedFacts) {f : RealFn}
    (h₁ : ContDiff ℝ 1 f) (hc : IsCompact (tsupport f)) (a b : Fin 4 → ℝ) :
    TestFunctions.sharpNormR4 (D.M : ℝ)
        (f ∘ translationEquiv (-a) - f ∘ translationEquiv (-b)) ≤
      D.params.toGrowth.shiftModulus f (TorusMetric.euclidNormVec (a - b)) := by
  have hf := mem_compactC1 (D := D) h₁ hc
  have h₂ := ((h.translations (unitMirrorData D) (cubeScale D)).1 ⟨f, hf⟩).2.1.1 a b
  have h₃ := smoothModulus_eq hf (δ := TorusMetric.euclidNormVec (a - b)) (Real.sqrt_nonneg _)
  rw [← h₃]
  exact h₂
theorem euclidNormVec_sub_comm (a b : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (a - b) = TorusMetric.euclidNormVec (b - a) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem continuous_of_lipschitzR4 {f : RealFn} (hf : LipschitzR4 f) :
    Continuous f := by apply _root_.YangMills.Construction.ToriLimits.NonlinearDomain.continuous_of_lipschitzR4 <;> assumption
theorem sharpNormQ_eq_ofReal {f : RealFn} (hL : LipschitzR4 f)
    (hc : IsCompact (tsupport f)) :
    Kind.sharpNormQ D.euclidParams .euclidean f =
      ENNReal.ofReal (TestFunctions.sharpNormR4 (D.M : ℝ) f) := by
  have hb : BddAbove (range fun x => ‖f x‖) := by
    obtain ⟨C, hC⟩ := (continuous_of_lipschitzR4 hL).bounded_above_of_compact_support hc
    exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  have hsup : Kind.supNormQ D.euclidParams .euclidean f =
      ENNReal.ofReal (TestFunctions.uniformNorm f) := by
    have hle : Kind.supNormQ D.euclidParams .euclidean f ≤
        ENNReal.ofReal (TestFunctions.uniformNorm f) :=
      iSup_le fun y => ENNReal.ofReal_le_ofReal (le_ciSup hb y)
    refine le_antisymm hle ?_
    have htop : Kind.supNormQ D.euclidParams .euclidean f ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    rw [← ENNReal.ofReal_toReal htop]
    refine ENNReal.ofReal_le_ofReal (ciSup_le fun y => ?_)
    rw [← ENNReal.ofReal_le_iff_le_toReal htop]
    exact le_iSup (fun y : Fin 4 → ℝ => ENNReal.ofReal |f y|) y
  have hlip : Kind.lipConstQ D.euclidParams .euclidean f = TestFunctions.lipConstR4 f := by
    have : Kind.quotDist D.euclidParams .euclidean = TestFunctions.euclidDistR4 :=
      funext₂ (BallPeriodization.quotDist_euclidean D.euclidParams)
    exact congrArg (fun d : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ =>
      TestFunctions.bestLipschitzConstant d f) this
  simp only [PeriodicSpace.Kind.sharpNormQ, TestFunctions.sharpNormR4, hsup, hlip]
  exact (ENNReal.ofReal_mono.map_max).symm
theorem sharpNormR4_nonneg (M : ℝ) (f : RealFn) :
    0 ≤ TestFunctions.sharpNormR4 M f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem sharpNormReal_eq {f : RealFn} (hL : LipschitzR4 f)
    (hc : IsCompact (tsupport f)) :
    Kind.sharpNormReal D.euclidParams .euclidean f = TestFunctions.sharpNormR4 (D.M : ℝ) f := by
  show (PeriodicSpace.Kind.sharpNormQ D.euclidParams .euclidean f).toReal = _
  rw [sharpNormQ_eq_ofReal hL hc, ENNReal.toReal_ofReal (sharpNormR4_nonneg _ _)]
theorem shiftFamily_mem {Y : PeriodicSpace.Params} {n : ℕ} {f : Fin n → RealFn}
    (hf : f ∈ Kind.sepC1Tuples Y .euclidean n) (a : Fin 4 → ℝ) :
    shiftFamily a f ∈ Kind.sepC1Tuples Y .euclidean n :=
  comp_mem_sepC1Tuples Y hf (isEuclideanMotion_translationEquiv (-a))
theorem entry_regularity {Y : PeriodicSpace.Params} {n : ℕ} {f : Fin n → RealFn}
    (hf : f ∈ Kind.sepC1Tuples Y .euclidean n) (l : Fin n) :
    ContDiff ℝ 1 (f l) ∧ LipschitzR4 (f l) ∧ IsCompact (tsupport (f l)) := by
  obtain ⟨h₁, h₂, -⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff f).1 hf
  exact ⟨h₁ l, BallTuples.isLipschitzFor_of_contDiff (h₁ l) (h₂ l), h₂ l⟩
theorem supp_translation_subset (f : RealFn) (a : Fin 4 → ℝ) :
    tsupport (f ∘ translationEquiv (-a)) ⊆ (fun x => x + a) '' tsupport f := by
  rw [supp_comp_euclideanMotion (isEuclideanMotion_translationEquiv (-a))]
  intro x hx
  exact ⟨x + -a, hx, by simp⟩
theorem shift_difference_le (h : CitedFacts) {C : BoundFamily} {Ξ : D.LimitHierarchy}
    (hE : Ξ.SatisfiesSepEstimate C) {n : ℕ} (hn : 2 ≤ n) (f : D.sepDomain n)
    (R : ℝ) (hR : 0 < R) (hsupp : BallSupported R hR f.1) {d : ℝ} (hd : 0 < d)
    (hsep : ENNReal.ofReal d ≤ Kind.supportGap D.euclidParams .euclidean f.1)
    (a b : Fin 4 → ℝ) (hab : TorusMetric.euclidNormVec (a - b) ≤ d / 4) :
    |Ξ.func n hn ⟨_, shiftFamily_mem f.2 a⟩ - Ξ.func n hn ⟨_, shiftFamily_mem f.2 b⟩| ≤
      C.val n (d / 2) (R + d / 4) *
        ∑ i, D.params.toGrowth.shiftModulus (f.1 i) (TorusMetric.euclidNormVec (a - b)) *
          ∏ l ∈ Finset.univ.erase i, 2 * TestFunctions.sharpNormR4 (D.M : ℝ) (f.1 l) := by
  have hdist := BallPeriodization.quotDist_euclidean D.euclidParams
  have hwords := h.collars.2.2.2.2.1 D.euclidParams
  have hR' : 0 < R + d / 4 := by positivity
  have hadm : R + d / 4 ∈ Kind.allowedRadii D.euclidParams .euclidean := by
    rw [hwords.2.2.1.2.2.2.1]
    exact hR'
  choose x hx using hsupp
  let A : Fin n → Set (Fin 4 → ℝ) := fun l =>
    (fun y => y + a) '' tsupport (f.1 l) ∪ (fun y => y + b) '' tsupport (f.1 l)
  have hball : ∀ l, ∃ T, Kind.IsClosedBallWithRadius D.euclidParams .euclidean T (R + d / 4) ∧
      A l ⊆ T := by
    intro l
    refine ⟨Kind.closedBallAbout D.euclidParams .euclidean (x l + a) (R + d / 4), ⟨hR', _, rfl⟩, ?_⟩
    rintro z (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · have h₁ : TorusMetric.euclidNormVec (y - x l) ≤ R := hx l hy
      show Kind.quotDist D.euclidParams .euclidean _ _ ≤ _
      rw [hdist, show y + a - (x l + a) = y - x l by abel]
      linarith
    · have h₁ : TorusMetric.euclidNormVec (y - x l) ≤ R := hx l hy
      show Kind.quotDist D.euclidParams .euclidean _ _ ≤ _
      rw [hdist, show y + b - (x l + a) = (y - x l) + (b - a) by abel]
      have h₂ := Periodization.euclidNormVec_triangle (y - x l) (b - a)
      rw [← euclidNormVec_sub_comm a b] at h₂
      linarith
  have hpair : DiagonalLimits.PairwiseSetDistGe D.euclidParams .euclidean A
      (d / 2) := by
    intro l l' hll
    have hsep' : ENNReal.ofReal d ≤ Kind.setInfDist D.euclidParams .euclidean
        (Kind.supportQ D.euclidParams .euclidean (f.1 l))
        (Kind.supportQ D.euclidParams .euclidean (f.1 l')) :=
      hsep.trans ((iInf_le _ l).trans ((iInf_le _ l').trans (iInf_le _ hll)))
    refine le_iInf₂ fun z hz => le_iInf₂ fun z' hz' => ?_
    have key : ∀ (u u' y y' : Fin 4 → ℝ), TorusMetric.euclidNormVec (u - u') ≤ d / 4 →
        y ∈ tsupport (f.1 l) → y' ∈ tsupport (f.1 l') →
        ENNReal.ofReal (d / 2) ≤ ENNReal.ofReal
          (Kind.quotDist D.euclidParams .euclidean (y + u) (y' + u')) := by
      intro u u' y y' hu hy hy'
      have h₁ : ENNReal.ofReal d ≤ ENNReal.ofReal (TorusMetric.euclidNormVec (y - y')) := by
        have hy₁ : y ∈ Kind.supportQ D.euclidParams .euclidean (f.1 l) := by
          rw [BallTuples.supportQ_euclidean]; exact hy
        have hy₂ : y' ∈ Kind.supportQ D.euclidParams .euclidean (f.1 l') := by
          rw [BallTuples.supportQ_euclidean]; exact hy'
        have h₂ := hsep'.trans ((iInf₂_le y hy₁).trans (iInf₂_le y' hy₂))
        rwa [hdist] at h₂
      have h₂ : d ≤ TorusMetric.euclidNormVec (y - y') :=
        (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).1 h₁
      rw [hdist]
      refine ENNReal.ofReal_le_ofReal ?_
      have h₃ := Periodization.euclidNormVec_triangle (y + u - (y' + u')) (u' - u)
      rw [show y + u - (y' + u') + (u' - u) = y - y' by abel, ← euclidNormVec_sub_comm u u'] at h₃
      linarith
    have hself : ∀ v : Fin 4 → ℝ, TorusMetric.euclidNormVec (v - v) ≤ d / 4 := fun v => by
      have : TorusMetric.euclidNormVec (0 : Fin 4 → ℝ) = 0 := by simp [TorusMetric.euclidNormVec]
      rw [sub_self, this]
      positivity
    have hba : TorusMetric.euclidNormVec (b - a) ≤ d / 4 := by rwa [← euclidNormVec_sub_comm]
    rcases hz with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ <;> rcases hz' with ⟨y', hy', rfl⟩ | ⟨y', hy', rfl⟩
    · exact key a a y y' (hself a) hy hy'
    · exact key a b y y' hab hy hy'
    · exact key b a y y' hba hy hy'
    · exact key b b y y' (hself b) hy hy'
  have hsub : ∀ l, Kind.supportQ D.euclidParams .euclidean (shiftFamily a f.1 l) ∪
      Kind.supportQ D.euclidParams .euclidean (shiftFamily b f.1 l) ⊆ A l := by
    intro l
    rw [BallTuples.supportQ_euclidean, BallTuples.supportQ_euclidean]
    exact union_subset_union (supp_translation_subset (f.1 l) a)
      (supp_translation_subset (f.1 l) b)
  have hineq := hE n hn (d / 2) (R + d / 4) (by positivity) hadm A hball hpair
    ⟨_, shiftFamily_mem f.2 a⟩ ⟨_, shiftFamily_mem f.2 b⟩ hsub
  have hc : 0 ≤ C.val n (d / 2) (R + d / 4) := C.nonneg n hn _ _ (by positivity) hR'
  refine (hineq.1.trans hineq.2).trans (mul_le_mul_of_nonneg_left ?_ hc)
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨hi₁, hi₂, hi₃⟩ := entry_regularity f.2 i
  have hL : ∀ (v : Fin 4 → ℝ) (g : RealFn), LipschitzR4 g → IsCompact (tsupport g) →
      g ∘ translationEquiv (-v) ∈ lipSuppIn univ := by
    intro v g hg hcg
    obtain ⟨⟨K, hK, hg'⟩⟩ := (⟨hg⟩ : Nonempty (LipschitzR4 g))
    refine ⟨⟨K, hK, fun p q => ?_⟩, ?_, subset_univ _⟩
    · have := hg' (p + -v) (q + -v)
      simpa [TestFunctions.euclidDistR4] using this
    · have e := supp_comp_euclideanMotion (isEuclideanMotion_translationEquiv (-v)) g
      exact show IsCompact (tsupport (g ∘ translationEquiv (-v))) from by
        rw [e]
        exact (motionHomeomorph (isEuclideanMotion_translationEquiv (-v))).isCompact_preimage.2 hcg
  have hdiff := (TestTupleClass.lipSubmodule univ).sub_mem
    (hL a (f.1 i) hi₂ hi₃ : _ ∈ TestTupleClass.lipSubmodule univ)
    (hL b (f.1 i) hi₂ hi₃ : _ ∈ TestTupleClass.lipSubmodule univ)
  have hfirst : Kind.sharpNormReal D.euclidParams .euclidean
      (shiftFamily a f.1 i - shiftFamily b f.1 i) ≤
        D.params.toGrowth.shiftModulus (f.1 i) (TorusMetric.euclidNormVec (a - b)) := by
    have e := sharpNormReal_eq (D := D) hdiff.1 hdiff.2.1
    exact e.le.trans (sharpNormR4_translation_sub_le h hi₁ hi₃ a b)
  have hprod : ∏ k ∈ Finset.univ.erase i,
      (Kind.sharpNormReal D.euclidParams .euclidean (shiftFamily a f.1 k) +
        Kind.sharpNormReal D.euclidParams .euclidean (shiftFamily b f.1 k)) =
      ∏ l ∈ Finset.univ.erase i, 2 * TestFunctions.sharpNormR4 (D.M : ℝ) (f.1 l) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    obtain ⟨-, hk₂, hk₃⟩ := entry_regularity f.2 k
    have ea := hL a (f.1 k) hk₂ hk₃
    have eb := hL b (f.1 k) hk₂ hk₃
    have e₁ := sharpNormReal_eq (D := D) ea.1 ea.2.1
    have e₂ := sharpNormReal_eq (D := D) eb.1 eb.2.1
    have e₃ := sharpNormR4_comp_translation (D := D) h hk₂ hk₃ a
    have e₄ := sharpNormR4_comp_translation (D := D) h hk₂ hk₃ b
    show Kind.sharpNormReal D.euclidParams .euclidean (f.1 k ∘ translationEquiv (-a)) +
      Kind.sharpNormReal D.euclidParams .euclidean (f.1 k ∘ translationEquiv (-b)) = _
    exact (congrArg₂ (· + ·) (e₁.trans e₃) (e₂.trans e₄)).trans (by ring)
  rw [hprod]
  exact mul_le_mul_of_nonneg_right hfirst
    (Finset.prod_nonneg fun l _ => mul_nonneg (by norm_num) (sharpNormR4_nonneg _ _))
theorem isSepLipTuple_of_mem {Y : PeriodicSpace.Params} {n : ℕ}
    {f : Fin n → RealFn} (hf : f ∈ Kind.sepC1Tuples Y .euclidean n) :
    IsSepLipTuple f := by
  obtain ⟨h₁, h₂, h₃⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff f).1 hf
  exact ⟨fun l => BallTuples.isLipschitzFor_of_contDiff (h₁ l) (h₂ l), h₂, h₃⟩
theorem supportGap_pos (h : CitedFacts) {n : ℕ} (hn : 2 ≤ n) (f : D.sepDomain n) :
    0 < Kind.supportGap D.euclidParams .euclidean f.1 := by
  have hl := isSepLipTuple_of_mem f.2
  rw [(h.collars.2.2.2.2.1 D.euclidParams).2.2.1.2.2.1 n hn f.1 hl]
  exact (h.collars.2.2.2.1 n hn f.1 hl).1
theorem exists_real_le_supportGap (h : CitedFacts) {n : ℕ} (hn : 2 ≤ n) (f : D.sepDomain n) :
    ∃ d : ℝ, 0 < d ∧ ENNReal.ofReal d ≤ Kind.supportGap D.euclidParams .euclidean f.1 := by
  obtain ⟨r, -, hr, hr'⟩ := ENNReal.lt_iff_exists_real_btwn.1 (supportGap_pos h hn f)
  exact ⟨r, ENNReal.ofReal_pos.1 hr, hr'.le⟩
theorem ballSupported_of_suppsWithin {n : ℕ} {f : Fin n → RealFn} {ρ : ℝ}
    (hρ : 0 < ρ) (h : SuppsWithin f (ballOrigin ρ)) : BallSupported ρ hρ f := by
  intro i
  refine ⟨0, fun y hy => ?_⟩
  have h₁ : TorusMetric.euclidNormVec y < ρ := h i hy
  show TorusMetric.euclidNormVec (y - 0) ≤ ρ
  rw [sub_zero]
  exact h₁.le
theorem func_shift (h : CitedFacts) {S : ToriSequence D} {J : Sequences.PNatIndexSet}
    {C : BoundFamily} {Ξ : D.LimitHierarchy} (hΞ : S.IsLimitHierarchy J Ξ)
    (hE : Ξ.SatisfiesSepEstimate C) {n : ℕ} (hn : 2 ≤ n) (f : D.sepDomain n)
    (a : Fin 4 → ℝ) : Ξ.func n hn ⟨_, shiftFamily_mem f.2 a⟩ = Ξ.func n hn f := by
  obtain ⟨ρ, hρ, hsup⟩ := exists_suppsWithin_ball h hn f.2
  have hRs := ballSupported_of_suppsWithin hρ hsup
  obtain ⟨d, hd, hsep⟩ := exists_real_le_supportGap h hn f
  have hc : 0 ≤ C.val n (d / 2) (ρ + d / 4) :=
    C.nonneg n hn _ _ (by positivity) (by positivity)
  set c := C.val n (d / 2) (ρ + d / 4) with hcdef
  let P : Fin n → ℝ := fun i =>
    ∏ l ∈ Finset.univ.erase i, 2 * TestFunctions.sharpNormR4 (D.M : ℝ) (f.1 l)
  have hP : ∀ i, 0 ≤ P i := fun i =>
    Finset.prod_nonneg fun l _ => mul_nonneg (by norm_num) (sharpNormR4_nonneg _ _)
  have hf' : ∀ i, f.1 i ∈
      ReflectionPositivity.AxisMirror.Ambient.compactC1 (unitMirrorData D) ℝ .euclidean :=
    fun i => mem_compactC1 (entry_regularity f.2 i).1 (entry_regularity f.2 i).2.2
  have hmod := fun i => ((h.translations (unitMirrorData D) (cubeScale D)).1 ⟨f.1 i, hf' i⟩).1
  let G : ℝ≥0 → ℝ := fun δ => ∑ i, ReflectionPositivity.AxisMirror.Ambient.smoothModulus (cubeScale D)
    (⟨f.1 i, hf' i⟩ :
      ReflectionPositivity.AxisMirror.Ambient.compactC1 (unitMirrorData D) ℝ .euclidean) δ * P i
  have hG : Tendsto G (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) => (hmod i).2.mul_const (P i)
    simpa using this
  refine eq_of_abs_sub_le_all fun ε hε => ?_
  have hpos : 0 < ε / (c + 1) := by positivity
  obtain ⟨δ₀, hδ₁, hδ₂⟩ := ((hG.eventually (gt_mem_nhds hpos)).and self_mem_nhdsWithin).exists
  have hδ₂' : (0 : ℝ) < δ₀ := by exact_mod_cast hδ₂
  set η := min (δ₀ : ℝ) (d / 4) with hη
  have hηpos : 0 < η := lt_min hδ₂' (by positivity)
  have hdense := (h.nesting D.L D.admissible).2.2.1
  have hnear : ∀ μ, ∃ y ∈ PeriodicLattice.adicGridPointsPositive D.L, dist (a μ) y < η / 2 :=
    fun μ => Metric.dense_iff.1 hdense (a μ) (η / 2) (half_pos hηpos) |>.elim fun y hy =>
      ⟨y, hy.2, by simpa [dist_comm] using hy.1⟩
  choose a' ha' hclose using hnear
  have hlen : TorusMetric.euclidNormVec (a - a') ≤ η := by
    have h₁ := SeparatedTuplesR4.euclidNormVec_le_two_mul_norm (a - a')
    have h₂ : ‖a - a'‖ < η / 2 := (pi_norm_lt_iff (half_pos hηpos)).2 fun μ => by
      have := hclose μ
      rwa [Real.dist_eq] at this
    linarith
  have hest := shift_difference_le h hE hn f ρ hρ hRs hd hsep a a'
    (hlen.trans (min_le_right _ _))
  rw [func_adicShift h hΞ hn f a' ha' (shiftFamily_mem f.2 a')] at hest
  have hsum : ∑ i, D.params.toGrowth.shiftModulus (f.1 i)
      (TorusMetric.euclidNormVec (a - a')) * P i ≤ G δ₀ := by
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (hP i)
    have hm := smoothModulus_eq (hf' i) (δ := TorusMetric.euclidNormVec (a - a')) (Real.sqrt_nonneg _)
    have hle : (TorusMetric.euclidNormVec (a - a')).toNNReal ≤ δ₀ :=
      Real.toNNReal_le_iff_le_coe.2 (hlen.trans (min_le_left _ _))
    exact hm.symm.le.trans ((hmod i).1 hle)
  calc _ ≤ c * ∑ i, D.params.toGrowth.shiftModulus (f.1 i)
        (TorusMetric.euclidNormVec (a - a')) * P i := hest
    _ ≤ c * (ε / (c + 1)) := mul_le_mul_of_nonneg_left (hsum.trans hδ₁.le) hc
    _ ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
theorem func_euclideanMotion {Ξ : D.LimitHierarchy}
    (htr : ∀ (n : ℕ) (_ : 2 ≤ n) (f : D.sepDomain n) (a : Fin 4 → ℝ),
      Ξ.evalSigma ⟨n, shiftFamily a f.1⟩ = Ξ.evalSigma ⟨n, f.1⟩)
    (hhy : ∀ (n : ℕ) (_ : 2 ≤ n) (f : D.sepDomain n) (w : hyperoctahedral),
      Ξ.evalSigma ⟨n, hyperoctahedralActFamily w f.1⟩ = Ξ.evalSigma ⟨n, f.1⟩)
    {n : ℕ} (hn : 2 ≤ n) (f : D.sepDomain n) (s : TorusPeriodization.euclideanMotions)
    (hfs : (fun i => f.1 i ∘ s.1) ∈ D.sepDomain n) :
    Ξ.func n hn ⟨_, hfs⟩ = Ξ.func n hn f := by
  obtain ⟨w, hw, v, hv⟩ := (SourcesAndGluing.mem_euclideanMotions_iff s.1).1 s.2
  let W : hyperoctahedral := ⟨w, hw⟩
  let g : D.sepDomain n := ⟨shiftFamily (-v) f.1, shiftFamily_mem f.2 _⟩
  have e : (fun i => f.1 i ∘ s.1) = hyperoctahedralActFamily W⁻¹ g.1 := by
    funext i x
    show f.1 i (s.1 x) = f.1 i (W.1 x - -v)
    rw [hv x, sub_neg_eq_add]
  have h₁ := hhy n hn g W⁻¹
  have h₂ := htr n hn f (-v)
  have e₁ := Kind.Hierarchy.evalSigma_of_sep Ξ hn ⟨_, hfs⟩
  have e₂ := Kind.Hierarchy.evalSigma_of_sep Ξ hn f
  rw [← e₁, ← e₂]
  have e₄ : Ξ.evalSigma ⟨n, fun i => f.1 i ∘ s.1⟩ =
      Ξ.evalSigma ⟨n, hyperoctahedralActFamily W⁻¹ g.1⟩ :=
    congrArg (fun X : Fin n → RealFn => Ξ.evalSigma ⟨n, X⟩) e
  exact e₄.trans (h₁.trans h₂)
theorem partitionMoment_euclideanMotion {Ξ : D.LimitHierarchy}
    (htr : ∀ (n : ℕ) (_ : 2 ≤ n) (f : D.sepDomain n) (a : Fin 4 → ℝ),
      Ξ.evalSigma ⟨n, shiftFamily a f.1⟩ = Ξ.evalSigma ⟨n, f.1⟩)
    (hhy : ∀ (n : ℕ) (_ : 2 ≤ n) (f : D.sepDomain n) (w : hyperoctahedral),
      Ξ.evalSigma ⟨n, hyperoctahedralActFamily w f.1⟩ = Ξ.evalSigma ⟨n, f.1⟩)
    {q : ℕ} (f : D.sepDomain q) (s : TorusPeriodization.euclideanMotions)
    (hfs : (fun i => f.1 i ∘ s.1) ∈ D.sepDomain q) :
    Ξ.partitionMoment ⟨_, hfs⟩ = Ξ.partitionMoment f := by
  unfold Kind.Hierarchy.partitionMoment
  refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun B _ => ?_
  exact func_euclideanMotion htr hhy _ ⟨_, Kind.restrictTuple_mem_sepC1Tuples _ _ f.2 B.1⟩ s _
end MotionsOfLimit
section
open MotionsOfLimit
theorem symmetries_of_limit (h : CitedFacts) (S : ToriSequence D) (C : BoundFamily)
    {J : Sequences.PNatIndexSet} {Ξ : D.LimitHierarchy} (hJ : S.IsConvergenceSet C J)
    (hΞ : S.IsLimitHierarchy J Ξ) (hDist : MemberDistribsInvariant Ξ) : Symmetries C Ξ := by
  have hE : Ξ.SatisfiesSepEstimate C := by
    obtain ⟨Ξ', hΞ', -, hest⟩ := hJ.limit_hierarchy
    have hΞ'Ξ : Ξ' = Ξ := Kind.Hierarchy.ext (funext fun n => funext fun hn => funext fun f =>
      Complex.ofReal_injective ((hΞ' n hn f).unique (hΞ n hn f)))
    rwa [hΞ'Ξ] at hest
  have htr : ∀ (n : ℕ) (hn : 2 ≤ n) (f : D.sepDomain n) (a : Fin 4 → ℝ),
      Ξ.evalSigma ⟨n, shiftFamily a f.1⟩ = Ξ.func n hn f := fun n hn f a =>
    (Kind.Hierarchy.evalSigma_of_sep Ξ hn ⟨_, shiftFamily_mem f.2 a⟩).trans
      (func_shift h hΞ hE hn f a)
  have hhy : ∀ (n : ℕ) (hn : 2 ≤ n) (f : D.sepDomain n) (w : hyperoctahedral),
      Ξ.evalSigma ⟨n, hyperoctahedralActFamily w f.1⟩ = Ξ.func n hn f := fun n hn f w => by
    have hw : hyperoctahedralActFamily w f.1 ∈ D.sepDomain n :=
      comp_mem_sepC1Tuples _ f.2 (isEuclideanMotion_hyperoctahedral w⁻¹)
    exact (Kind.Hierarchy.evalSigma_of_sep Ξ hn ⟨_, hw⟩).trans
      (func_hyperoctahedral h hΞ hn f w hw)
  have htr' : ∀ (n : ℕ) (_ : 2 ≤ n) (f : D.sepDomain n) (a : Fin 4 → ℝ),
      Ξ.evalSigma ⟨n, shiftFamily a f.1⟩ = Ξ.evalSigma ⟨n, f.1⟩ := fun n hn f a =>
    (htr n hn f a).trans (Kind.Hierarchy.evalSigma_of_sep Ξ hn f).symm
  have hhy' : ∀ (n : ℕ) (_ : 2 ≤ n) (f : D.sepDomain n) (w : hyperoctahedral),
      Ξ.evalSigma ⟨n, hyperoctahedralActFamily w f.1⟩ = Ξ.evalSigma ⟨n, f.1⟩ := fun n hn f w =>
    (hhy n hn f w).trans (Kind.Hierarchy.evalSigma_of_sep Ξ hn f).symm
  refine ⟨htr, hhy, fun n hn f σ => ?_, fun n hn T hT => ?_, fun n hn f R hR hsupp d hlet a b hab => ?_⟩
  · have hσ : (fun i => f.1 (σ i)) ∈ D.sepDomain n := by
      obtain ⟨h₁, h₂, h₃⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff f.1).1 f.2
      exact (BallTuples.mem_sepC1Tuples_euclidean_iff _).2 ⟨fun l => h₁ _, fun l => h₂ _,
        fun l l' hl => h₃ _ _ (σ.injective.ne hl)⟩
    exact (Kind.Hierarchy.evalSigma_of_sep Ξ hn ⟨_, hσ⟩).trans
      (Ξ.symmetric n hn f σ hσ)
  · obtain ⟨h₁, h₂⟩ := hDist n hn T hT
    refine ⟨h₁, fun s => h₂ s.1 ?_ fun φ hφ => func_euclideanMotion htr' hhy' hn φ s hφ⟩
    intro y y'
    have hd := BallPeriodization.quotDist_euclidean D.euclidParams
    obtain ⟨Q, hQ, v, hv⟩ := (h.translations (unitMirrorData D) (cubeScale D)).2.1 s.1 s.2
    obtain ⟨e, he, hiso⟩ := ((h.translations (unitMirrorData D) (cubeScale D)).2.2.1 Q hQ v).1
    have key : TorusMetric.euclidNormVec (e y - e y') = TorusMetric.euclidNormVec (y - y') :=
      hiso y y'
    rw [he, ← hv] at key
    exact (hd _ _).trans (key.trans (hd _ _).symm)
  · have hle : 0 < d ∧ ENNReal.ofReal d ≤ Kind.supportGap D.euclidParams .euclidean f.1 := by
      by_cases hs : Kind.supportGap D.euclidParams .euclidean f.1 = ∞
      · exact ⟨hlet.2 hs, hs ▸ le_top⟩
      · have e := hlet.1 hs
        refine ⟨e ▸ ENNReal.toReal_pos (supportGap_pos h hn f).ne' hs, ?_⟩
        rw [e, ENNReal.ofReal_toReal hs]
    have e₁ := Kind.Hierarchy.evalSigma_of_sep Ξ hn ⟨_, shiftFamily_mem f.2 a⟩
    have e₂ := Kind.Hierarchy.evalSigma_of_sep Ξ hn ⟨_, shiftFamily_mem f.2 b⟩
    rw [e₁, e₂]
    exact shift_difference_le h hE hn f R hR hsupp hle.1 hle.2 a b hab
theorem symbolMoments_isMotionInvariant (_h : CitedFacts) {C : BoundFamily} {Ξ : D.LimitHierarchy}
    (hB : Symmetries C Ξ) : TimeAxisSymbols.IsMotionInvariant (symbolMoments Ξ) := by
  have htr' : ∀ (n : ℕ) (_ : 2 ≤ n) (f : D.sepDomain n) (a : Fin 4 → ℝ),
      Ξ.evalSigma ⟨n, shiftFamily a f.1⟩ = Ξ.evalSigma ⟨n, f.1⟩ := fun n hn f a =>
    (hB.shift_invariant n hn f a).trans (Kind.Hierarchy.evalSigma_of_sep Ξ hn f).symm
  have hhy' : ∀ (n : ℕ) (_ : 2 ≤ n) (f : D.sepDomain n) (w : hyperoctahedral),
      Ξ.evalSigma ⟨n, hyperoctahedralActFamily w f.1⟩ = Ξ.evalSigma ⟨n, f.1⟩ := fun n hn f w =>
    (hB.hyperoctahedral_invariant n hn f w).trans (Kind.Hierarchy.evalSigma_of_sep Ξ hn f).symm
  intro s hs hmem X
  have hp : hs.toPerm ∈ TorusPeriodization.euclideanMotions :=
    (GrowingTori.mem_euclideanMotions_iff_mem_affineHyperoctahedral _).2 (by
      rw [IsEuclideanMotion.coe_toPerm]
      exact hmem)
  exact partitionMoment_euclideanMotion htr' hhy'
    ⟨X.1.2, SymbolSequences.components_mem_sepC1Tuples _ X⟩ ⟨hs.toPerm.symm, inv_mem hp⟩ _
end
end ToriLimits.GrowingVolumeLimits.ProofSteps.LimitInvariance
end
end
section
open Set Filter Topology
open scoped NNReal ENNReal ComplexConjugate ComplexOrder
noncomputable section
namespace ToriLimits.GrowingVolumeLimits.ProofSteps.SequenceForm
open PeriodicSpace TorusTransport TorusTransport.TestFunctionOrders
open TorusTransport.TupleVectors
open ReflectionSpaces (finiteUpperSequences)
open TimeAxisSymbols SymbolSequences
open PositiveFormReconstruction
open FormsOperators (IsHilbertCompletion IsSesquilinear IsHermitianForm IsPosSemidefForm
  HasCountableDenseSet formRadical formOnQuotient)
section Transfer
variable {W V : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
theorem satisfies_of_surjective (S : PreHilbertData W) (T : PreHilbertData V)
    (τ : W →ₗ[ℂ] V) (hτ : Function.Surjective τ)
    (hform : ∀ X Y, T.form (τ X) (τ Y) = S.form X Y) (hunit : τ S.unitVec = T.unitVec)
    (htime : ∀ t X, T.semigroupMap t (τ X) = τ (S.semigroupMap t X))
    (hspace : ∀ a X, T.translationMap a (τ X) = τ (S.translationMap a X))
    (hgroup : ∀ w X, T.rotationMap w (τ X) = τ (S.rotationMap w X))
    (h : S.IsAdmissible) : T.IsAdmissible := by
  have hS := h.hermitian.toIsSesquilinear
  have hq : IsSesquilinear T.form :=
    { add_left := fun F₁ F₂ F' => by
        obtain ⟨X₁, rfl⟩ := hτ F₁
        obtain ⟨X₂, rfl⟩ := hτ F₂
        obtain ⟨Y, rfl⟩ := hτ F'
        rw [← map_add]
        simp only [hform]
        exact hS.add_left _ _ _
      smul_left := fun c F F' => by
        obtain ⟨X, rfl⟩ := hτ F
        obtain ⟨Y, rfl⟩ := hτ F'
        rw [← map_smul]
        simp only [hform]
        exact hS.smul_left _ _ _
      add_right := fun F F₁ F₂ => by
        obtain ⟨X, rfl⟩ := hτ F
        obtain ⟨Y₁, rfl⟩ := hτ F₁
        obtain ⟨Y₂, rfl⟩ := hτ F₂
        rw [← map_add]
        simp only [hform]
        exact hS.add_right _ _ _
      smul_right := fun c F F' => by
        obtain ⟨X, rfl⟩ := hτ F
        obtain ⟨Y, rfl⟩ := hτ F'
        rw [← map_smul]
        simp only [hform]
        exact hS.smul_right _ _ _ }
  refine
    { hermitian := { toIsSesquilinear := hq, conj_symm := fun F F' => ?_ }
      posSemidef := { toIsSesquilinear := hq, nonneg := fun F => ?_ }
      form_unitVec := ?_
      semigroupMap_zero := ?_
      translationMap_zero := ?_
      rotationMap_one := ?_
      semigroupMap_comp := fun t t' => ?_
      translationMap_comp := fun a a' => ?_
      rotationMap_comp := fun w w' => ?_
      translationMap_comm := fun a t => ?_
      rotationMap_comm := fun w t => ?_
      rotationMap_translationMap := fun w a => ?_
      semigroupMap_unitVec := fun t => ?_
      translationMap_unitVec := fun a => ?_
      rotationMap_unitVec := fun w => ?_
      form_semigroupMap := fun t F F' => ?_
      form_translationMap := fun a F F' => ?_
      form_rotationMap := fun w F F' => ?_
      bddAbove_semigroup := fun F => ?_
      tendsto_semigroup := fun F => ?_
      tendsto_translation := fun F => ?_ }
  · obtain ⟨X, rfl⟩ := hτ F
    obtain ⟨Y, rfl⟩ := hτ F'
    simp only [hform]
    exact h.hermitian.conj_symm _ _
  · obtain ⟨X, rfl⟩ := hτ F
    rw [hform]
    exact h.posSemidef.nonneg _
  · rw [← hunit, hform]
    exact h.form_unitVec
  · refine LinearMap.ext fun F => ?_
    obtain ⟨X, rfl⟩ := hτ F
    rw [htime, h.semigroupMap_zero]
    rfl
  · refine LinearMap.ext fun F => ?_
    obtain ⟨X, rfl⟩ := hτ F
    rw [hspace, h.translationMap_zero]
    rfl
  · refine LinearMap.ext fun F => ?_
    obtain ⟨X, rfl⟩ := hτ F
    rw [hgroup, h.rotationMap_one]
    rfl
  · refine LinearMap.ext fun F => ?_
    obtain ⟨X, rfl⟩ := hτ F
    rw [LinearMap.comp_apply, htime, htime, htime, ← h.semigroupMap_comp]
    rfl
  · refine LinearMap.ext fun F => ?_
    obtain ⟨X, rfl⟩ := hτ F
    rw [LinearMap.comp_apply, hspace, hspace, hspace, ← h.translationMap_comp]
    rfl
  · refine LinearMap.ext fun F => ?_
    obtain ⟨X, rfl⟩ := hτ F
    rw [LinearMap.comp_apply, hgroup, hgroup, hgroup, ← h.rotationMap_comp]
    rfl
  · refine LinearMap.ext fun F => ?_
    obtain ⟨X, rfl⟩ := hτ F
    have e := LinearMap.congr_fun (h.translationMap_comm a t) X
    simp only [LinearMap.comp_apply] at e
    rw [LinearMap.comp_apply, LinearMap.comp_apply, htime, hspace, hspace, htime, e]
  · refine LinearMap.ext fun F => ?_
    obtain ⟨X, rfl⟩ := hτ F
    have e := LinearMap.congr_fun (h.rotationMap_comm w t) X
    simp only [LinearMap.comp_apply] at e
    rw [LinearMap.comp_apply, LinearMap.comp_apply, htime, hgroup, hgroup, htime, e]
  · refine LinearMap.ext fun F => ?_
    obtain ⟨X, rfl⟩ := hτ F
    have e := LinearMap.congr_fun (h.rotationMap_translationMap w a) X
    simp only [LinearMap.comp_apply] at e
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hspace, hgroup, hgroup, hspace, e]
  · rw [← hunit, htime, h.semigroupMap_unitVec]
  · rw [← hunit, hspace, h.translationMap_unitVec]
  · rw [← hunit, hgroup, h.rotationMap_unitVec]
  · obtain ⟨X, rfl⟩ := hτ F
    obtain ⟨Y, rfl⟩ := hτ F'
    simp only [htime, hform]
    exact h.form_semigroupMap _ _ _
  · obtain ⟨X, rfl⟩ := hτ F
    obtain ⟨Y, rfl⟩ := hτ F'
    simp only [hspace, hform]
    exact h.form_translationMap _ _ _
  · obtain ⟨X, rfl⟩ := hτ F
    obtain ⟨Y, rfl⟩ := hτ F'
    simp only [hgroup, hform]
    exact h.form_rotationMap _ _ _
  · obtain ⟨X, rfl⟩ := hτ F
    simp only [htime, hform]
    exact h.bddAbove_semigroup X
  · obtain ⟨X, rfl⟩ := hτ F
    simp only [htime, hform]
    exact h.tendsto_semigroup X
  · obtain ⟨X, rfl⟩ := hτ F
    simp only [hspace, hform]
    exact h.tendsto_translation X
end Transfer
section Maps
def composeFamilyLinear (ψ : ∀ q : ℕ, Configuration q → Configuration q) :
    TestFamily →ₗ[ℂ] TestFamily where
  toFun := ReflectionSpaces.composeFamily ψ
  map_add' F G := by
    funext q
    cases q <;> rfl
  map_smul' c F := by
    funext q
    cases q <;> rfl
variable {D : TorusTransport.TransportData} (E : PeriodicSpace.Params)
theorem composeFamily_symbolSequence {s : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hs : IsEuclideanMotion s) (hp : MapsTo s posTimeHalf posTimeHalf)
    (ψ : ∀ q : ℕ, Configuration q → Configuration q) (hψ : ∀ q x i, ψ q x i = hs.toPerm.symm (x i))
    (X : PosSymbol D) :
    ReflectionSpaces.composeFamily ψ (symbolSequence E X).1 =
      (symbolSequence E (posMotion hs hp X)).1 := by
  obtain ⟨⟨k, f⟩, hX⟩ := X
  funext q
  by_cases hq : q = k
  · subst hq
    cases q with
    | zero => rfl
    | succ q =>
      have h₁ : (symbolSequence E ⟨⟨q + 1, f⟩, hX⟩).1 (q + 1) =
          symbolTensor ⟨⟨q + 1, f⟩, hX⟩ := symbolSequence_self E _
      have h₂ : (symbolSequence E (posMotion hs hp ⟨⟨q + 1, f⟩, hX⟩)).1 (q + 1) =
          symbolTensor (posMotion hs hp ⟨⟨q + 1, f⟩, hX⟩) := symbolSequence_self E _
      rw [h₂]
      show ReflectionSpaces.composeOrdered ψ ((symbolSequence E _).1 (q + 1)) = _
      rw [h₁]
      funext x
      show (∏ i, (((f i (ψ (q + 1) x i) : ℝ)) : ℂ)) = ∏ i, (((f i (hs.toPerm.symm (x i)) : ℝ)) : ℂ)
      simp only [hψ]
  · have h₁ : (symbolSequence E ⟨⟨k, f⟩, hX⟩).1 q = 0 := symbolSequence_of_ne E _ hq
    have h₂ : (symbolSequence E (posMotion hs hp ⟨⟨k, f⟩, hX⟩)).1 q = 0 :=
      symbolSequence_of_ne E _ hq
    rw [h₂]
    show ReflectionSpaces.composeOrdered ψ ((symbolSequence E _).1 q) = 0
    rw [h₁]
    cases q <;> rfl
theorem composeFamilyLinear_spanSequence (ψ : ∀ q : ℕ, Configuration q → Configuration q)
    (φ : PosSymbol D → PosSymbol D)
    (h : ∀ X, ReflectionSpaces.composeFamily ψ (symbolSequence E X).1 =
      (symbolSequence E (φ X)).1) (v : PosSymbolSpan D) :
    composeFamilyLinear ψ (spanSequence E v).1 =
      (spanSequence E (linExtend (fun X => basisVec (φ X)) v)).1 := by
  have key : (composeFamilyLinear ψ) ∘ₗ (finiteUpperSequences E).subtype ∘ₗ spanSequence E =
      (finiteUpperSequences E).subtype ∘ₗ spanSequence E ∘ₗ
        linExtend (fun X => basisVec (φ X)) := by
    refine (sepBasis D posTimeHalf).ext fun X => ?_
    rw [sepBasis_apply]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, linExtend_basisVec,
      spanSequence_basisVec]
    exact h X
  exact LinearMap.congr_fun key v
theorem composeFamilyLinear_mem (hs : Function.Surjective (spanSequence (D := D) E))
    (ψ : ∀ q : ℕ, Configuration q → Configuration q) (φ : PosSymbol D → PosSymbol D)
    (h : ∀ X, ReflectionSpaces.composeFamily ψ (symbolSequence E X).1 =
      (symbolSequence E (φ X)).1) :
    ∀ F ∈ finiteUpperSequences E, composeFamilyLinear ψ F ∈ finiteUpperSequences E := fun F hF => by
  obtain ⟨v, hv⟩ := hs ⟨F, hF⟩
  have e : F = (spanSequence E v).1 := by rw [hv]
  rw [e, composeFamilyLinear_spanSequence E ψ φ h v]
  exact Subtype.property _
def shiftConfig (v : Fin 4 → ℝ) : ∀ q : ℕ, Configuration q → Configuration q := fun _ x i => x i - v
theorem composeFamily_shiftConfig (v : Fin 4 → ℝ) (hp : MapsTo (translationEquiv v) posTimeHalf
    posTimeHalf) (X : PosSymbol D) :
    ReflectionSpaces.composeFamily (shiftConfig v) (symbolSequence E X).1 =
      (symbolSequence E (posMotion (isEuclideanMotion_translationEquiv v) hp X)).1 :=
  composeFamily_symbolSequence E _ hp _ (fun _ x i =>
    ((Equiv.symm_apply_eq _).mpr (by
      show x i = (x i - v) + v
      simp)).symm) X
theorem composeFamily_rotation (w : timeAxisStabilizer) (X : PosSymbol D) :
    ReflectionSpaces.composeFamily
        (fun _ => GrowingTori.diagMap (w.1⁻¹ : hyperoctahedral).1)
        (symbolSequence E X).1 =
      (symbolSequence E (posRotate w X)).1 :=
  composeFamily_symbolSequence E (isEuclideanMotion_hyperoctahedral w.1)
    (mapsTo_posTimeHalf_stabilizer w) _
    (fun _ x i => by
      have e : (isEuclideanMotion_hyperoctahedral w.1).toPerm.symm (x i) =
          (w.1⁻¹ : hyperoctahedral).1 (x i) :=
        (Equiv.symm_apply_eq _).mpr (w.1.1.apply_symm_apply (x i)).symm
      exact e.symm) X
end Maps
variable {D : Setup}
theorem denseChoice_nonempty (h : CitedFacts) (D' : TorusTransport.TransportData) :
    Nonempty (DenseChoice D') := by
  obtain ⟨-, h₂, -, -⟩ := h.countableFamily (euclideanParams D') .euclidean
  choose A hA using fun Q : euclideanStock D' => (h₂ Q.1 Q.2).2.2.1.2.2
  exact ⟨⟨A, fun Q => ⟨(hA Q).1, (hA Q).2.2⟩, fun Q => (hA Q).2.1⟩⟩
def sequencePreHilbertData (Ξ : D.LimitHierarchy) (hF : SymbolPairingMatches Ξ) :
    PreHilbertData (finiteUpperSequences D.euclidParams) where
  form := reflectionPairing Ξ
  unitVec := OSSpaces.vacuumSequence D.euclidParams
  semigroupMap t := (composeFamilyLinear (shiftConfig ((t : ℝ) • timeAxisVec))).restrict
    (composeFamilyLinear_mem D.euclidParams hF.surjective _ (posTimeShift t)
      (composeFamily_shiftConfig D.euclidParams _ (mapsTo_posTimeHalf_timeShift t)))
  translationMap a := (composeFamilyLinear (shiftConfig (spaceTimePoint a.ofLp 0))).restrict
    (composeFamilyLinear_mem D.euclidParams hF.surjective _ (posSpaceShift a.ofLp)
      (composeFamily_shiftConfig D.euclidParams _ (mapsTo_posTimeHalf_spaceShift a.ofLp)))
  rotationMap w := (composeFamilyLinear
      (fun _ => GrowingTori.diagMap (w.1⁻¹ : hyperoctahedral).1)).restrict
    (composeFamilyLinear_mem D.euclidParams hF.surjective _ (posRotate w)
      (composeFamily_rotation D.euclidParams w))
theorem isReconstructionData_sequence (Ξ : D.LimitHierarchy) (hF : SymbolPairingMatches Ξ) :
    IsReconstructionData Ξ (sequencePreHilbertData Ξ hF) where
  form_eq := rfl
  unitVec_eq := rfl
  semigroupMap_eq _ _ := rfl
  translationMap_eq _ _ := rfl
  rotationMap_eq _ _ := rfl
theorem satisfies_sequencePreHilbertData {Ξ : D.LimitHierarchy} (hF : SymbolPairingMatches Ξ)
    (h : (osPreHilbertData (symbolMoments Ξ)).IsAdmissible) :
    (sequencePreHilbertData Ξ hF).IsAdmissible := by
  have ht : ∀ t v, (sequencePreHilbertData Ξ hF).semigroupMap t (spanSequence D.euclidParams v) =
      spanSequence D.euclidParams ((osPreHilbertData (symbolMoments Ξ)).semigroupMap t v) :=
    fun t v => Subtype.ext (composeFamilyLinear_spanSequence D.euclidParams _ (posTimeShift t)
      (composeFamily_shiftConfig D.euclidParams _ (mapsTo_posTimeHalf_timeShift t)) v)
  have hs : ∀ a v, (sequencePreHilbertData Ξ hF).translationMap a (spanSequence D.euclidParams v) =
      spanSequence D.euclidParams ((osPreHilbertData (symbolMoments Ξ)).translationMap a v) :=
    fun a v => Subtype.ext (composeFamilyLinear_spanSequence D.euclidParams _
      (posSpaceShift a.ofLp)
      (composeFamily_shiftConfig D.euclidParams _ (mapsTo_posTimeHalf_spaceShift a.ofLp)) v)
  have hg : ∀ w v, (sequencePreHilbertData Ξ hF).rotationMap w (spanSequence D.euclidParams v) =
      spanSequence D.euclidParams ((osPreHilbertData (symbolMoments Ξ)).rotationMap w v) :=
    fun w v => Subtype.ext (composeFamilyLinear_spanSequence D.euclidParams _
      (posRotate w) (composeFamily_rotation D.euclidParams w) v)
  exact satisfies_of_surjective (osPreHilbertData (symbolMoments Ξ)) (sequencePreHilbertData Ξ hF)
    (spanSequence D.euclidParams) hF.surjective hF.pairing_eq
    (OSSpaces.symbolToSequence_posUnitSymbol D.euclidParams _) ht hs hg h
theorem osReconstruction_of_symbolMoments (h : CitedFacts) {C : BoundFamily} {Ξ : D.LimitHierarchy}
    (hM1 : IsNormedSymmMultilinear (symbolMoments Ξ))
    (hM2 : IsScaleBounded (symbolMoments Ξ) (momentBoundNN C))
    (hM3 : IsMotionInvariant (symbolMoments Ξ))
    (hM4 : IsReflPositive (symbolMoments Ξ)) (hF : SymbolPairingMatches Ξ) : OSReconstruction Ξ := by
  obtain ⟨-, -, hsym⟩ := h.symbols (symbolSetup D) (symbolMoments Ξ) (momentBoundNN C) hM1 hM2
  obtain ⟨hP, -, hdense⟩ := hsym hM3 hM4
  have hV := satisfies_sequencePreHilbertData hF hP
  obtain ⟨hdesc, hcontr, hex, hall⟩ :=
    h.reconstruction (finiteUpperSequences D.euclidParams) (sequencePreHilbertData Ξ hF) hV
  refine ⟨sequencePreHilbertData Ξ hF, hV, isReconstructionData_sequence Ξ hF, hdesc, hcontr, hex, ?_⟩
  intro H _ _ _ ι hι
  obtain ⟨⟨hvac, hsep⟩, hsem, htr, hgr, -, -⟩ := hall H ι hι
  obtain ⟨Ch⟩ := denseChoice_nonempty h (symbolSetup D)
  obtain ⟨hcount, happ⟩ := hdense Ch
  refine ⟨hsep (spanSequence D.euclidParams '' rationalSpan Ch) (hcount.image _) ?_,
    hvac, hsem, htr, hgr⟩
  intro F ε hε
  obtain ⟨X, rfl⟩ := hF.surjective F
  obtain ⟨F₀, hF₀, hlt⟩ := happ X ε hε
  refine ⟨_, mem_image_of_mem _ hF₀, ?_⟩
  rw [← map_sub]
  show reflectionPairing Ξ _ _ < _
  rw [hF.pairing_eq]
  exact hlt
end ToriLimits.GrowingVolumeLimits.ProofSteps.SequenceForm
end
end
end YangMills.Construction

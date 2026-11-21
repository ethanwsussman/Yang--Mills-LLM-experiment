import YangMills.Construction.Torus.CoveringMapOnSmallBalls
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Torus.OneBallIntegralsAndLiftOfATestPair
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open TorusMetric PeriodicLattice TestFunctions TestPairs
namespace SingleBallPairs
theorem volume_closedBallR4 (x : Fin 4 → ℝ) {d : ℝ} (hd : 0 ≤ d) :
    volume (closedBallR4 x d) = ENNReal.ofReal (Real.pi ^ 2 / 2 * d ^ 4) := by apply _root_.YangMills.Construction.TestPairs.volume_closedBallR4 <;> assumption
theorem integral_le_of_tsupport_subset_closedBallR4 {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} {d : ℝ}
    (hd : 0 < d) (hb : IsBoundedFun f) (hs : tsupport f ⊆ closedBallR4 x d) :
    (∫ y, f y) ≤ Real.pi ^ 2 / 2 * uniformNorm f * d ^ 4 := by
  have hvol := volume_closedBallR4 x hd.le
  have hfin : volume (closedBallR4 x d) < ⊤ := by
    rw [hvol]
    exact ENNReal.ofReal_lt_top
  have hnorm : ∀ y, ‖f y‖ ≤ uniformNorm f := fun y => by
    obtain ⟨C, hC⟩ := hb
    exact le_ciSup (f := fun y => ‖f y‖) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ y
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBallR4 x d)
    (fun y hy => image_eq_zero_of_notMem_tsupport fun hm => hy (hs hm))]
  have hbound := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := closedBallR4 x d) (f := f)
    (C := uniformNorm f) hfin (fun y _ => hnorm y)
  have hreal : (volume : Measure (Fin 4 → ℝ)).real (closedBallR4 x d) = Real.pi ^ 2 / 2 * d ^ 4 := by
    rw [Measure.real, hvol, ENNReal.toReal_ofReal (by positivity)]
  rw [hreal] at hbound
  calc (∫ y in closedBallR4 x d, f y) ≤ ‖∫ y in closedBallR4 x d, f y‖ := le_abs_self _
    _ ≤ uniformNorm f * (Real.pi ^ 2 / 2 * d ^ 4) := hbound
    _ = Real.pi ^ 2 / 2 * uniformNorm f * d ^ 4 := by ring
theorem euclidPairProperties_of (hG : GeometryAndKernelBounds) {d θ : ℝ}
    (hs : IsSepShapePair d θ) {x₁ x₂ : Fin 4 → ℝ} {f g : (Fin 4 → ℝ) → ℝ}
    (hc : (f, g) ∈ separatedPairsR4 d θ) (hz : IsCentrePairR4 d θ x₁ x₂ (f, g)) :
    EuclidPairProperties d θ x₁ x₂ f g := by
  obtain ⟨⟨hx, ⟨-, hsupp⟩, hapart, hker, hchain⟩, -⟩ := hG.1 d θ hs x₁ x₂ f g hc hz
  obtain ⟨⟨t₁, l₁, -⟩, ⟨t₂, l₂, -⟩, -, -⟩ := hz
  exact ⟨hx, ⟨subset_union_left.trans hsupp, subset_union_right.trans hsupp⟩, hapart,
    ⟨l₁, integral_le_of_tsupport_subset_closedBallR4 hs.1 hker.1 t₁⟩,
    ⟨l₂, integral_le_of_tsupport_subset_closedBallR4 hs.1 hker.2.1 t₂⟩, hker, hchain⟩
theorem continuous_of_isLipschitzFor {ℓ : ℝ} {φ : Torus4 ℓ → ℝ}
    (hφ : IsLipschitzFor euclidDistTorus φ) : Continuous φ := by apply _root_.YangMills.Construction.TestPairs.continuous_of_isLipschitzFor_torus <;> assumption
theorem tsupport_complexOfReal {X : Type*} [TopologicalSpace X] (g : X → ℝ) :
    tsupport (fun x => (g x : ℂ)) = tsupport g := by
  have hsupp : Function.support (fun x => (g x : ℂ)) = Function.support g := by
    ext x
    simp
  rw [tsupport, tsupport, hsupp]
theorem liftToBall_complexOfReal {ℓ r : ℝ} (c : Fin 4 → ℝ) (φ : Torus4 ℓ → ℝ) :
    liftToBall ℓ c r (fun u => (φ u : ℂ)) = fun x => ((liftToBall ℓ c r φ x : ℝ) : ℂ) := by
  funext x
  by_cases hx : x ∈ closedBallR4 c r <;> simp [liftToBall, indicator, hx]
theorem inverseEighthKernel_complexOfReal (ψ χ : (Fin 4 → ℝ) → ℝ) :
    inverseEighthKernel (fun x => (ψ x : ℂ)) (fun x => (χ x : ℂ)) =
      ((inverseEighthKernel ψ χ : ℝ) : ℂ) := by
  unfold inverseEighthKernel
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp
theorem isKernelPairR4_of_complexOfReal {ψ χ : (Fin 4 → ℝ) → ℝ}
    (hk : IsKernelPairR4 (fun x => (ψ x : ℂ)) (fun x => (χ x : ℂ))) : IsKernelPairR4 ψ χ := by
  obtain ⟨⟨C, hC⟩, ⟨D, hD⟩, m₁, m₂, k₁, k₂, p⟩ := hk
  refine ⟨⟨C, fun x => by simpa using hC x⟩, ⟨D, fun x => by simpa using hD x⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.measurable_re.comp m₁
  · exact Complex.measurable_re.comp m₂
  · rwa [HasCompactSupport, ← tsupport_complexOfReal]
  · rwa [HasCompactSupport, ← tsupport_complexOfReal]
  · rwa [tsupport_complexOfReal, tsupport_complexOfReal] at p
theorem torusKernelWellDefined_of (hC : SmallBalls.CoveringOnSmallBalls) {ℓ r : ℝ} (hℓ : 0 < ℓ)
    (hr : 0 < r) (hr8 : r ≤ ℓ / 8) {y : Torus4 ℓ} {f g : Torus4 ℓ → ℝ}
    (bf : IsBoundedFun f) (bg : IsBoundedFun g) (cf : Continuous f) (cg : Continuous g)
    (tf : tsupport f ⊆ closedBallTorus y r) (tg : tsupport g ⊆ closedBallTorus y r)
    (hq : ∃ q : (Fin 4 → ℝ) × ℝ, IsKernelBallTorus f g q.1 q.2) : TorusKernelWellDefined f g := by
  have : Fact (0 < ℓ) := ⟨hℓ⟩
  obtain ⟨-, -, -, hball, hfree⟩ := hC ℓ hℓ
  have hmeas : ∀ k : Torus4 ℓ → ℝ, IsBoundedFun k → Continuous k →
      IsBoundedMeasurableOnTorus (fun u => (k u : ℂ)) := fun k bk ck => by
    obtain ⟨C, hC'⟩ := bk
    exact ⟨⟨C, fun u => by simpa using hC' u⟩,
      (Complex.measurable_ofReal.comp ck.measurable).comp (measurable_torusProj ℓ)⟩
  have hsmall : SmallBalls.SupportsInSmallBall (fun u => (f u : ℂ)) (fun u => (g u : ℂ)) := by
    obtain ⟨q, hq'⟩ := hq
    rw [SmallBalls.SupportsInSmallBall, tsupport_complexOfReal, tsupport_complexOfReal]
    exact ⟨hq'.1, y, r, hr, hr8, tf, tg⟩
  have hcovers : ∀ (c : Fin 4 → ℝ) (s : ℝ), IsKernelBallTorus f g c s →
      SmallBalls.BallCoversSupports (fun u => (f u : ℂ)) (fun u => (g u : ℂ)) c s :=
    fun c s hk => by
      have himg := (hball c s hk.2.1 hk.2.2.1).1.1.image_eq
      rw [SmallBalls.BallCoversSupports, tsupport_complexOfReal, tsupport_complexOfReal, himg]
      exact ⟨hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2⟩
  have hindep := (hfree _ _ (hmeas f bf cf) (hmeas g bg cg) hsmall).1
  refine ⟨hq, fun c s hk => ?_⟩
  obtain ⟨-, p₂, -, e⟩ :=
    hindep hq.choose.1 hq.choose.2 c s (hcovers _ _ hq.choose_spec) (hcovers _ _ hk)
  simp only [liftToBall_complexOfReal, inverseEighthKernel_complexOfReal] at p₂ e
  refine ⟨isKernelPairR4_of_complexOfReal p₂, ?_⟩
  rw [inverseEighthKernelTorus, dif_pos hq]
  exact Complex.ofReal_injective e
theorem eq_of_liftToBall_eq {ℓ r : ℝ} {c : Fin 4 → ℝ} {φ φ' : Torus4 ℓ → ℝ}
    (v : ∀ u, u ∉ torusProj ℓ '' closedBallR4 c r → φ u = 0)
    (v' : ∀ u, u ∉ torusProj ℓ '' closedBallR4 c r → φ' u = 0)
    (e : liftToBall ℓ c r φ = liftToBall ℓ c r φ') : φ = φ' := by
  funext u
  by_cases hu : u ∈ torusProj ℓ '' closedBallR4 c r
  · obtain ⟨x, hx, rfl⟩ := hu
    simpa [liftToBall, indicator, hx] using congrFun e x
  · rw [v u hu, v' u hu]
theorem ballLiftProperties_of (hG : GeometryAndKernelBounds) (hC : SmallBalls.CoveringOnSmallBalls)
    {L : ℕ} {ℓ d θ : ℝ} (hs : IsSepShapePair d θ) (hside : IsAdmissibleSide L ℓ d)
    {x₁ x₂ : Torus4 ℓ} {X₁ X₂ : Fin 4 → ℝ} {f g : Torus4 ℓ → ℝ}
    (hl : LiftProperties ℓ d θ x₁ x₂ X₁ X₂ f g) :
    BallLiftProperties ℓ d θ (midpointR4 X₁ X₂) X₁ X₂ f g := by
  have hℓ : 0 < ℓ := by linarith [hs.1, hside.2]
  obtain ⟨-, ⟨y, iso, -, hsupp⟩, ⟨r0, r4, v₁⟩, ⟨-, -, v₂⟩, hcls, hcent, -⟩ := hl
  obtain ⟨tr₁, tr₂, -, -, ⟨-, -, w₁⟩, ⟨-, -, w₂⟩, b₁, b₂, -⟩ :=
    (hG.1 d θ hs X₁ X₂ _ _ hcls hcent).2 L ℓ hside
  have hsub : tsupport f ∪ tsupport g ⊆ torusProj ℓ '' closedBallR4 (midpointR4 X₁ X₂) (5 * d) := by
    rw [iso.1]
    exact hsupp
  exact ⟨((hC ℓ hℓ).2.2.2.1 _ _ r0 r4).1.1.image_eq,
    ⟨subset_union_left.trans hsub, subset_union_right.trans hsub⟩,
    ⟨r0, r4, fun u hu => by simp [v₁ u hu]⟩, ⟨r0, r4, fun u hu => by simp [v₂ u hu]⟩, hcls, hcent,
    tr₁, tr₂, eq_of_liftToBall_eq w₁ v₁ b₁, eq_of_liftToBall_eq w₂ v₂ b₂⟩
theorem torusPairProperties_of (hG : GeometryAndKernelBounds) (hC : SmallBalls.CoveringOnSmallBalls)
    {L : ℕ} {ℓ d θ : ℝ} (hs : IsSepShapePair d θ) (hside : IsAdmissibleSide L ℓ d)
    {x₁ x₂ : Torus4 ℓ} {f g : Torus4 ℓ → ℝ} (hc : (f, g) ∈ separatedPairsTorus ℓ d θ)
    (hz : IsCentrePairTorus ℓ d θ x₁ x₂ (f, g)) :
    TorusPairProperties d θ x₁ x₂ f g ∧ ∃ X₁ X₂ : Fin 4 → ℝ, IsIsometricLiftPair x₁ x₂ X₁ X₂ := by
  have hd := hs.1
  have hside2 := hside.2
  have hℓ : 0 < ℓ := by linarith
  have : Fact (0 < ℓ) := ⟨hℓ⟩
  obtain ⟨⟨hx, ⟨y, -, hsupp⟩, hapart, hq, hchain⟩, hlift⟩ := hG.2 L ℓ d θ hs hside x₁ x₂ f g hc hz
  obtain ⟨X₂, l₂, eX⟩ := (hC ℓ hℓ).2.1 x₁ x₂ (liftPoint x₁) (torusProj_liftPoint x₁)
  have lifts : IsIsometricLiftPair x₁ x₂ (liftPoint x₁) X₂ := ⟨torusProj_liftPoint x₁, l₂, eX⟩
  obtain ⟨-, -, -, -, hcls, hcent, ks₁, ks₂, ki₁, ki₂, -⟩ :=
    hlift _ _ lifts.1 lifts.2.1 lifts.2.2
  obtain ⟨-, -, ⟨lf, -⟩, ⟨lg, -⟩, -⟩ := hc
  have cf := continuous_of_isLipschitzFor lf
  have cg := continuous_of_isLipschitzFor lg
  have e₁ := torusVolumeIntegral_eq_integralTorusLebesgue hℓ f cf.measurable.aestronglyMeasurable
  have e₂ := torusVolumeIntegral_eq_integralTorusLebesgue hℓ g cg.measurable.aestronglyMeasurable
  have hbdd : ∀ k : Torus4 ℓ → ℝ, Continuous k → IsBoundedFun k := fun k ck => by
    obtain ⟨C, hC'⟩ := isCompact_univ.exists_bound_of_continuousOn ck.continuousOn
    exact ⟨C, fun u => hC' u (mem_univ u)⟩
  have hpair := euclidPairProperties_of hG hs hcls hcent
  have up₁ := hpair.2.2.2.1.2
  have up₂ := hpair.2.2.2.2.1.2
  rw [ks₁, ki₁, ← e₁] at up₁
  rw [ks₂, ki₂, ← e₂] at up₂
  obtain ⟨⟨-, lo₁, -⟩, ⟨-, lo₂, -⟩, -, -⟩ := hz
  have tf : tsupport f ⊆ closedBallTorus y (5 * d) := subset_union_left.trans hsupp
  have tg : tsupport g ⊆ closedBallTorus y (5 * d) := subset_union_right.trans hsupp
  have hformed := torusKernelWellDefined_of hC hℓ (by linarith : 0 < 5 * d)
    (by linarith : 5 * d ≤ ℓ / 8) (hbdd f cf) (hbdd g cg) cf cg tf tg hq
  rw [← e₁, ← e₂] at hchain
  exact ⟨⟨hx, ⟨y, tf, tg⟩, hapart, ⟨lo₁, up₁⟩, ⟨lo₂, up₂⟩, hformed, hchain⟩, ⟨_, _, lifts⟩⟩
theorem mainStatement_holds (hG : GeometryAndKernelBounds) (hC : SmallBalls.CoveringOnSmallBalls) :
    MainStatement := by
  refine ⟨fun d θ hs x₁ x₂ f g hc hz => euclidPairProperties_of hG hs hc hz,
    fun L ℓ d θ hs hside x₁ x₂ f g hc hz => ?_⟩
  obtain ⟨a, b⟩ := torusPairProperties_of hG hC hs hside hc hz
  exact ⟨a, b, fun X₁ X₂ hX => ballLiftProperties_of hG hC hs hside
    ((hG.2 L ℓ d θ hs hside x₁ x₂ f g hc hz).2 X₁ X₂ hX.1 hX.2.1 hX.2.2)⟩
end SingleBallPairs
end YangMills.Construction

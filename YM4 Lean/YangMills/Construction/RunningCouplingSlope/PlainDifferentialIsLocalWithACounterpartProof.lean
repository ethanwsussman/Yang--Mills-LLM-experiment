import YangMills.Construction.RunningCouplingSlope.PlainDifferentialIsLinear
import YangMills.Construction.RunningCouplingSlope.PlainDifferentialIsLocalWithACounterpart
import YangMills.Construction.RunningCouplingSlope.PlainMeanAlongTheQuotient
import YangMills.Construction.Towers.AverageDifferentialIsLocalWithACounterpartProof
import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATowerProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower LocalKernels LocalKernels.Periodisation
variable {L n k j : ℕ}
private theorem link_positive_or_opposite {a : ℝ} (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
private theorem fullSpace_extendOddly_opposite {a : ℝ} (ha : 0 < a)
    (g : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (b : InfiniteLattice.Link a) : FullSpace.extendOddly g b.opposite = -FullSpace.extendOddly g b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
private theorem extendOddly_opposite
    (h₉ : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 0 < k) {j : ℕ} (hj : j ≤ k)
    (g : Edge L n k j → Matrices.ComplexMatrix2) (b : Edge L n k j) :
    extendOddly g b.opposite = -extendOddly g b := by apply _root_.YangMills.Construction.LocalKernels.SmoothingDerivLocality.extendOddly_opposite <;> assumption
private theorem supNorm_le_of_mem_doubleCube (hZ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    (c : FullSpace.Edge L k (j + 1)) (hc : c.IsPositivelyOriented) {x : InfiniteLattice.AmbientSpace}
    (hx : x ∈ FullSpace.doubleCube L (meshAt L k j) c) :
    TorusMetric.supNormVec (x - (c.initial : InfiniteLattice.AmbientSpace)) ≤
      3 * meshAt L k (j + 1) / 2 := by apply _root_.YangMills.Construction.LocalKernels.SmoothingDerivLocality.supNormVec_le_of_mem_doubleCube <;> assumption
private theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
private theorem expTwist_lift_eq (h₁ : EdgeProjectionProperties)
    (h₉ : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {c : FullSpace.Edge L k (j + 1)} {V : Edge L n k j → Matrices.ComplexMatrix2}
    {f : FullSpace.Edge L k j → Matrices.ComplexMatrix2} {f' : Edge L n k j → Matrices.ComplexMatrix2}
    (hag : ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c, b.IsPositivelyOriented →
      f b = f' (FullSpace.projEdge L n k j b)) (t : ℂ) :
    ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c,
      FullSpace.expTwist (t • f) (liftGaugeField L n k j V) b =
        PeriodicLattice.expTwist (t • f') V (FullSpace.projEdge L n k j b) := by
  classical
  intro b hb
  have hq := (h₁ L n k j hL hn hj.le).1
  by_cases hp : b.IsPositivelyOriented
  · have hpq := (hq b).2.2.1 hp
    simp only [FullSpace.expTwist, PeriodicLattice.expTwist, if_pos hp, if_pos hpq, Pi.smul_apply,
      hag b hb hp]
    rfl
  · have hr : b.opposite.IsPositivelyOriented := (link_positive_or_opposite b).resolve_left hp
    have hrq : (FullSpace.projEdge L n k j b).opposite.IsPositivelyOriented := by
      rw [(hq b).2.2.2]
      exact (hq b.opposite).2.2.1 hr
    have hnq : ¬(FullSpace.projEdge L n k j b).IsPositivelyOriented := by
      rcases h₉ L n k hL hn (by omega) j hj.le (FullSpace.projEdge L n k j b) with
        ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd hrq h
      · exact h
    have hbr : b.opposite ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c := ⟨hb.2, hb.1⟩
    simp only [FullSpace.expTwist, PeriodicLattice.expTwist, if_neg hp, if_neg hnq, Pi.smul_apply,
      hag _ hbr hr, (hq b).2.2.2]
    rfl
private theorem differential_eq_periodic (hA : ContourMeanAlongProjection)
    (h₁ : EdgeProjectionProperties)
    (h₉ : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented) {V : Edge L n k j → Matrices.ComplexMatrix2}
    {f : FullSpace.Edge L k j → Matrices.ComplexMatrix2} {f' : Edge L n k j → Matrices.ComplexMatrix2}
    (hag : ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c, b.IsPositivelyOriented →
      f b = f' (FullSpace.projEdge L n k j b)) :
    FullLattice.normalizedMeanDifferential (liftGaugeField L n k j V) f c =
      holLeftDifferential normalizedMean V f' (FullSpace.projEdge L n k (j + 1) c) := by
  classical
  have hcq := ((h₁ L n k (j + 1) hL hn hj).1 c).2.2.1 hc
  have hmean : ∀ (W : FullSpace.Edge L k j → Matrices.ComplexMatrix2) (V' : Edge L n k j → Matrices.ComplexMatrix2),
      (∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c,
        W b = V' (FullSpace.projEdge L n k j b)) →
      FullLattice.normalizedMean W c = normalizedMean V' (FullSpace.projEdge L n k (j + 1) c) := by
    intro W V' h
    have e := hA L hL n k j hn hj c hc W V' h
    unfold FullLattice.normalizedMean normalizedMean FullLattice.meanRadius meanRadius
    rw [e]
  have h0 := hmean (liftGaugeField L n k j V) V fun _ _ => rfl
  have hpos : FullLattice.normalizedMeanDifferential (liftGaugeField L n k j V) f c =
      logDirectionalDeriv ℂ (fun X => FullLattice.normalizedMean
        (FullSpace.expTwist X (liftGaugeField L n k j V)) c)
        (FullLattice.normalizedMean (liftGaugeField L n k j V) c) f :=
    if_pos hc
  have hpos' : holLeftDifferential normalizedMean V f' (FullSpace.projEdge L n k (j + 1) c) =
      logDirectionalDeriv ℂ (fun X => normalizedMean (PeriodicLattice.expTwist X V)
        (FullSpace.projEdge L n k (j + 1) c))
        (normalizedMean V (FullSpace.projEdge L n k (j + 1) c)) f' :=
    if_pos hcq
  rw [hpos, hpos', h0]
  unfold logDirectionalDeriv
  refine congrArg (fun w => Complex.I⁻¹ • w) (congrArg (fun φ => deriv φ (0 : ℂ)) (funext fun t => ?_))
  have e := hmean (FullSpace.expTwist (algebraMap ℂ ℂ t • f) (liftGaugeField L n k j V))
    (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • f') V)
    (expTwist_lift_eq h₁ h₉ hL hn hj hag (algebraMap ℂ ℂ t))
  exact congrArg (fun M => Matrices.ComplexMatrix2.logSeries
    (M * (normalizedMean V (FullSpace.projEdge L n k (j + 1) c))⁻¹)) e
private theorem exists_periodic_representative (h₁ : EdgeProjectionProperties)
    (h₃ : ProjectionCarriesSetsStatement) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    (f : FullSpace.Edge L k j → Matrices.ComplexMatrix2) :
    ∃ f' : Edge L n k j → Matrices.ComplexMatrix2, ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c,
      f b = f' (FullSpace.projEdge L n k j b) := by
  classical
  have hL0 : 0 < L := by have := hL.2; omega
  have Q := (h₃ L hL0 hL k (by omega) n hn).2 j hj c hc
  have hq := (h₁ L n k j hL hn hj.le).1
  have hinj : InjOn (FullSpace.projEdge L n k j)
      (FullSpace.doubleCubeLinks L (meshAt L k j) c) := by
    intro b hb b' hb' h
    have e₁ : FullSpace.projVertex L n k j b.initial = FullSpace.projVertex L n k j b'.initial := by
      rw [← (hq b).1, ← (hq b').1, h]
    have e₂ : FullSpace.projVertex L n k j b.terminal = FullSpace.projVertex L n k j b'.terminal := by
      rw [← (hq b).2.1, ← (hq b').2.1, h]
    exact InfiniteLattice.Link.ext
      (Subtype.ext (Q.injOn_doubleCube hb.1 hb'.1 (congrArg Subtype.val e₁)))
      (Subtype.ext (Q.injOn_doubleCube hb.2 hb'.2 (congrArg Subtype.val e₂)))
  refine ⟨fun d => if h : ∃ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c,
    FullSpace.projEdge L n k j b = d then f h.choose else 0, fun b hb => ?_⟩
  have hex : ∃ b' ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c,
      FullSpace.projEdge L n k j b' = FullSpace.projEdge L n k j b := ⟨b, hb, rfl⟩
  show _ = dite _ _ _
  rw [dif_pos hex, hinj hex.choose_spec.1 hb hex.choose_spec.2]
theorem normalizedMeanDifferentialPeriodizes_proof (hA : ContourMeanAlongProjection)
    (hLin : HolDifferentialLinear)
    (h₁ : EdgeProjectionProperties) (h₃ : ProjectionCarriesSetsStatement)
    (h₉ : PeriodicLattice.LevelBondOrientationDichotomy)
    (hZ : BlockPathContourPivotStatement) : NormalizedMeanDifferentialPeriodizes := by
  intro L hL
  obtain ⟨ρ, hρ, hlin⟩ := hLin L hL
  refine ⟨ρ, hρ, fun k n hn j h V hV hnear => ?_⟩
  have hj : j < k := h
  have hk : 1 ≤ k := by omega
  obtain ⟨hval, hadd⟩ := hlin n k j hn hj V hV hnear
  have ha := meshAt_pos hL k (j + 1)
  have hzero : holLeftDifferential normalizedMean V (0 : Edge L n k j → Matrices.ComplexMatrix2) = 0 := by
    have e := hadd 1 0 0
    simp only [smul_zero, add_zero, one_smul] at e
    exact left_eq_add.1 e
  have hsum : ∀ B B' : Edge L n k j → Matrices.ComplexMatrix2, holLeftDifferential normalizedMean V (B + B') =
      holLeftDifferential normalizedMean V B + holLeftDifferential normalizedMean V B' := by
    intro B B'
    simpa using hadd 1 B B'
  have hsmul : ∀ (w : ℂ) (B : Edge L n k j → Matrices.ComplexMatrix2),
      holLeftDifferential normalizedMean V (w • B) = w • holLeftDifferential normalizedMean V B := by
    intro w B
    simpa [hzero] using hadd w B 0
  have value : ∀ {c : FullSpace.Edge L k (j + 1)}, c.IsPositivelyOriented →
      ∀ (f : FullSpace.Edge L k j → Matrices.ComplexMatrix2) (f' : Edge L n k j → Matrices.ComplexMatrix2),
      (∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c,
        f b = f' (FullSpace.projEdge L n k j b)) →
      FullLattice.normalizedMeanDifferential (liftGaugeField L n k j V) f c =
        holLeftDifferential normalizedMean V f' (FullSpace.projEdge L n k (j + 1) c) :=
    fun hc f f' hag => differential_eq_periodic hA h₁ h₉ hL hn hj hc fun b hb _ => hag b hb
  have hform : ∀ (F G : FullSpace.Edge L k (j + 1) → Matrices.ComplexMatrix2),
      (∀ c, ¬ c.IsPositivelyOriented → F c = -F c.opposite) →
      (∀ c, ¬ c.IsPositivelyOriented → G c = -G c.opposite) →
      (∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented → F c = G c) → F = G := by
    intro F G hF hG hp
    funext c
    by_cases hc : c.IsPositivelyOriented
    · exact hp c hc
    · rw [hF c hc, hG c hc, hp _ ((link_positive_or_opposite c).resolve_left hc)]
  have hneg : ∀ (f : FullSpace.Edge L k j → Matrices.ComplexMatrix2) (c : FullSpace.Edge L k (j + 1)),
      ¬ c.IsPositivelyOriented →
      FullLattice.normalizedMeanDifferential (liftGaugeField L n k j V) f c =
        -FullLattice.normalizedMeanDifferential (liftGaugeField L n k j V) f c.opposite := by
    intro f c hc
    unfold FullLattice.normalizedMeanDifferential
    rw [fullSpace_extendOddly_opposite ha, neg_neg]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    refine ⟨fun c hc => ?_, fun c => ?_⟩
    · obtain ⟨f', hf'⟩ := exists_periodic_representative (n := n) h₁ h₃ hL hn hj hc f
      rw [value hc f f' hf']
      exact hval f' _ (((h₁ L n k (j + 1) hL hn hj).1 c).2.2.1 hc)
    · unfold FullLattice.normalizedMeanDifferential
      exact fullSpace_extendOddly_opposite ha _ c
  · intro f₀ _ g₀ _
    let f : FullSpace.Edge L k j → Matrices.ComplexMatrix2 := f₀
    let g : FullSpace.Edge L k j → Matrices.ComplexMatrix2 := g₀
    exact show FullLattice.normalizedMeanDifferential (liftGaugeField L n k j V) (f + g) =
        fun c => FullLattice.normalizedMeanDifferential (liftGaugeField L n k j V) f c +
          FullLattice.normalizedMeanDifferential (liftGaugeField L n k j V) g c from by
      refine hform _ _ (hneg _) (fun c hc => ?_) fun c hc => ?_
      · show _ + _ = -(_ + _)
        rw [hneg f c hc, hneg g c hc]
        abel
      · obtain ⟨f', hf'⟩ := exists_periodic_representative (n := n) h₁ h₃ hL hn hj hc f
        obtain ⟨g', hg'⟩ := exists_periodic_representative (n := n) h₁ h₃ hL hn hj hc g
        show _ = _ + _
        rw [value hc f f' hf', value hc g g' hg',
          value hc (f + g) (f' + g') fun b hb => by
            show f b + g b = f' _ + g' _
            rw [hf' b hb, hg' b hb], hsum]
        rfl
  · intro w f₀ _
    let f : FullSpace.Edge L k j → Matrices.ComplexMatrix2 := f₀
    exact show FullLattice.normalizedMeanDifferential (liftGaugeField L n k j V) (w • f) =
        fun c => w • FullLattice.normalizedMeanDifferential (liftGaugeField L n k j V) f c from by
      refine hform _ _ (hneg _) (fun c hc => ?_) fun c hc => ?_
      · show w • _ = -(w • _)
        rw [hneg f c hc, smul_neg]
      · obtain ⟨f', hf'⟩ := exists_periodic_representative (n := n) h₁ h₃ hL hn hj hc f
        show _ = w • _
        rw [value hc f f' hf', value hc (w • f) (w • f') fun b hb => by
            show w • f b = w • f' _
            rw [hf' b hb], hsmul]
        rfl
  · intro f₀ _ g₀ _ c' hagree
    let f : FullSpace.Edge L k j → Matrices.ComplexMatrix2 := f₀
    let g : FullSpace.Edge L k j → Matrices.ComplexMatrix2 := g₀
    let c : PeriodicOperators.PosEdge L k (j + 1) := c'
    obtain ⟨f', hf'⟩ := exists_periodic_representative (n := n) h₁ h₃ hL hn hj c.2 f
    show FullLattice.normalizedMeanDifferential (liftGaugeField L n k j V) f c.1 =
      FullLattice.normalizedMeanDifferential (liftGaugeField L n k j V) g c.1
    rw [differential_eq_periodic hA h₁ h₉ hL hn hj c.2 (f' := f') fun b hb _ => hf' b hb,
      differential_eq_periodic hA h₁ h₉ hL hn hj c.2 (f' := f') fun b hb hp => ?_]
    rw [← hf' b hb]
    exact (hagree (show PeriodicOperators.PosEdge L k j from ⟨b, hp⟩)
      (supNorm_le_of_mem_doubleCube hZ hL hk hj c.1 c.2 hb.1)).symm
  · intro f _
    refine ⟨fun c hc => hval f c hc, fun c => ?_⟩
    unfold holLeftDifferential
    exact extendOddly_opposite h₉ hL hn (by omega) h _ c
  · intro f _ g _
    exact hsum f g
  · intro w f _
    exact hsmul w f
  · intro f _ c'
    let c : PeriodicOperators.PosEdge L k (j + 1) := c'
    let fT : Edge L n k j → Matrices.ComplexMatrix2 := f
    have hcq := ((h₁ L n k (j + 1) hL hn h).1 c.1).2.2.1 c.2
    have hquo : (projPositiveEdge L n k (j + 1) c).1 =
        FullSpace.projEdge L n k (j + 1) c.1 :=
      Classical.epsilon_spec (p := fun d : PositiveEdge L n k (j + 1) =>
        d.1 = FullSpace.projEdge L n k (j + 1) c.1) ⟨⟨_, hcq⟩, rfl⟩
    show FullLattice.normalizedMeanDifferential (liftGaugeField L n k j V)
        (fun b => fT (FullSpace.projEdge L n k j b)) c.1 =
      holLeftDifferential normalizedMean V fT (projPositiveEdge L n k (j + 1) c).1
    rw [hquo]
    exact value c.2 _ _ fun _ _ => rfl
end YangMills.Construction.RunningCouplingSlope
end

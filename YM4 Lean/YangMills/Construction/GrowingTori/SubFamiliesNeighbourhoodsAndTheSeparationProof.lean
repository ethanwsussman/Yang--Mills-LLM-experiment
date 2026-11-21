import YangMills.Construction.QuaternionicWilsonModel.WhatTheTopGivesAtEveryCouplingProof
import YangMills.Construction.GrowingTori.SubFamiliesNeighbourhoodsAndTheSeparation
import YangMills.Construction.GrowingTori.TranslationsIsometriesAndMirrorsOfFourSpaceProof
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefinedProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriLimits.SubfamiliesAndGaps
theorem euclidNormVec_add_le_add (u v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (u + v) ≤ TorusMetric.euclidNormVec u + TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_sub_comm (x y : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (x - y) = TorusMetric.euclidNormVec (y - x) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ TorusMetric.euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_sub_self (x : Fin 4 → ℝ) : TorusMetric.euclidNormVec (x - x) = 0 := by
  simp [TorusMetric.euclidNormVec]
theorem continuous_euclidNormVec : Continuous TorusMetric.euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem infDist_le_of_mem_mem {A B : Set (Fin 4 → ℝ)} {a b : Fin 4 → ℝ} (ha : a ∈ A) (hb : b ∈ B) :
    ToriLimits.infDist A B ≤ ENNReal.ofReal (TorusMetric.euclidNormVec (a - b)) :=
  iInf₂_le_of_le a ha (iInf₂_le b hb)
theorem le_infDist_of_forall {A B : Set (Fin 4 → ℝ)} {c : ℝ≥0∞}
    (h : ∀ a ∈ A, ∀ b ∈ B, c ≤ ENNReal.ofReal (TorusMetric.euclidNormVec (a - b))) :
    c ≤ ToriLimits.infDist A B :=
  le_iInf₂ fun a ha => le_iInf₂ fun b hb => h a ha b hb
theorem infDist_antitone_subsets {A A' B B' : Set (Fin 4 → ℝ)} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    ToriLimits.infDist A B ≤ ToriLimits.infDist A' B' :=
  le_infDist_of_forall fun _ ha _ hb => infDist_le_of_mem_mem (hA ha) (hB hb)
theorem disjoint_of_ofReal_le_infDist {A B : Set (Fin 4 → ℝ)} {d : ℝ} (hd : 0 < d)
    (h : ENNReal.ofReal d ≤ ToriLimits.infDist A B) : Disjoint A B := by apply _root_.YangMills.Construction.NonGaussianLimits.disjoint_of_le_setDistR4 <;> assumption
theorem exists_mem_near_of_ptInfDist_le {A : Set (Fin 4 → ℝ)} (hA : IsCompact A) {x : Fin 4 → ℝ}
    {η : ℝ} (hη : 0 < η) (hx : ptInfDist x A ≤ ENNReal.ofReal η) :
    ∃ a ∈ A, TorusMetric.euclidNormVec (x - a) ≤ η := by
  have hne : A.Nonempty := by
    rcases A.eq_empty_or_nonempty with rfl | h
    · have h₁ : ptInfDist x ∅ = ∞ := ToriLimits.infDist_empty_right _
      rw [h₁] at hx
      exact absurd hx (not_le.2 ENNReal.ofReal_lt_top)
    · exact h
  have hc : Continuous fun y : Fin 4 → ℝ => TorusMetric.euclidNormVec (x - y) :=
    continuous_euclidNormVec.comp (continuous_const.sub continuous_id)
  obtain ⟨a, ha, hmin⟩ := hA.exists_isMinOn hne hc.continuousOn
  refine ⟨a, ha, ?_⟩
  have h₁ : ENNReal.ofReal (TorusMetric.euclidNormVec (x - a)) ≤ ptInfDist x A :=
    le_infDist_of_forall fun x' hx' b hb => by
      rw [mem_singleton_iff.1 hx']
      exact ENNReal.ofReal_le_ofReal (hmin hb)
  exact (ENNReal.ofReal_le_ofReal_iff hη.le).1 (h₁.trans hx)
theorem subfamilyAdmissible : SubfamilyAdmissible := by
  intro d R hd hR q hq A hA I hI
  refine ⟨fun l => hA.1 _, fun l k hlk => hA.2 _ _ fun h => hlk ?_⟩
  exact (I.orderEmbOfFin rfl).injective h
theorem thickeningDistanceBound : ThickeningDistanceBound := by
  intro A A' hA hA' η η' hη hη'
  refine le_infDist_of_forall fun x hx x' hx' => ?_
  obtain ⟨a, ha, hxa⟩ := exists_mem_near_of_ptInfDist_le hA hη hx
  obtain ⟨a', ha', hxa'⟩ := exists_mem_near_of_ptInfDist_le hA' hη' hx'
  rw [tsub_le_iff_right, tsub_le_iff_right]
  have htri : TorusMetric.euclidNormVec (a - a') ≤ TorusMetric.euclidNormVec (x - x') + η' + η := by
    have h₁ : a - a' = (a - x) + (x - x') + (x' - a') := by abel
    have h₂ := euclidNormVec_add_le_add ((a - x) + (x - x')) (x' - a')
    have h₃ := euclidNormVec_add_le_add (a - x) (x - x')
    rw [← h₁] at h₂
    rw [euclidNormVec_sub_comm a x] at h₃
    linarith
  calc ToriLimits.infDist A A' ≤ ENNReal.ofReal (TorusMetric.euclidNormVec (a - a')) :=
        infDist_le_of_mem_mem ha ha'
    _ ≤ ENNReal.ofReal (TorusMetric.euclidNormVec (x - x') + η' + η) := ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal (TorusMetric.euclidNormVec (x - x')) + ENNReal.ofReal η' + ENNReal.ofReal η := by
      rw [ENNReal.ofReal_add (add_nonneg (euclidNormVec_nonneg _) hη'.le) hη.le,
        ENNReal.ofReal_add (euclidNormVec_nonneg _) hη'.le]
theorem lipschitzR4_of_contDiff {h : RealFn} (h₁ : ContDiff ℝ 1 h)
    (hc : IsCompact (fnSupport h)) : LipschitzR4 h := by apply _root_.YangMills.Construction.ToriLimits.EuclideanSymmetryFacts.lipschitzR4_of_contDiff <;> assumption
theorem sepTuplesLipschitz (s : Conventions.StandingParameters) : SepTuplesLipschitz s := by
  refine ⟨fun n f => ?_, fun A f hf => ?_⟩
  · rw [mem_sepTuplesR4_iff]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      exact ⟨⟨fun i => lipschitzR4_of_contDiff (h₁ i) (h₂ i), h₂, h₃⟩, h₁⟩
    · rintro ⟨⟨-, h₂, h₃⟩, h₁⟩
      exact ⟨h₁, h₂, h₃⟩
  · obtain ⟨h₁, h₂⟩ := (mem_c1SuppIn_iff s A f).1 hf
    exact ⟨lipschitzR4_of_contDiff h₁ h₂.1, h₂⟩
theorem isCompact_fnSupport_of_subset_closedBallR4 {u : RealFn} {x : Fin 4 → ℝ}
    {R : ℝ} (h : fnSupport u ⊆ closedBallR4 x R) : IsCompact (fnSupport u) := by
  refine (isCompact_closedBall x R).of_isClosed_subset isClosed_closure fun y hy => ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact (SeparatedTuplesR4.norm_le_euclidNormVec _).trans (h hy)
theorem mem_lipTuples_iff_parts (n : ℕ) (hn : 2 ≤ n) (d R : ℝ) (hd : 0 < d) (hR : 0 < R)
    (f : Fin n → RealFn) :
    f ∈ lipTuples n hn d R hd hR ↔
      (∀ i, LipschitzR4 (f i)) ∧ (∀ i, ∃ x, fnSupport (f i) ⊆ closedBallR4 x R) ∧
        ∀ i k, i ≠ k → ENNReal.ofReal d ≤ ToriLimits.infDist (fnSupport (f i)) (fnSupport (f k)) := by
  constructor
  · rintro ⟨hf, hr, hs⟩
    exact ⟨hf.1, hr, fun i k hik =>
      hs.trans (iInf_le_of_le i (iInf_le_of_le k (iInf_le _ hik)))⟩
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨⟨h₁, fun i => ?_, fun i k hik => disjoint_of_ofReal_le_infDist hd (h₃ i k hik)⟩, h₂,
      le_iInf fun i => le_iInf fun k => le_iInf fun hik => h₃ i k hik⟩
    obtain ⟨x, hx⟩ := h₂ i
    exact isCompact_fnSupport_of_subset_closedBallR4 hx
theorem admissibleProductsInClasses (s : Conventions.StandingParameters) :
    AdmissibleProductsInClasses s := by
  intro n hn d R hd hR A hA
  have hlip : ∀ h : Fin n → RealFn, (∀ l, h l ∈ lipSuppIn (A l)) →
      h ∈ lipTuples n hn d R hd hR := fun h hh => by
    refine (mem_lipTuples_iff_parts n hn d R hd hR h).2
      ⟨fun l => (hh l).1, fun l => ?_, fun l k hlk => ?_⟩
    · obtain ⟨x, hx⟩ := hA.1 l
      exact ⟨x, (hh l).2.2.trans hx⟩
    · exact (hA.2 l k hlk).trans (infDist_antitone_subsets (hh l).2.2 (hh k).2.2)
  refine ⟨hlip, fun h hh => ?_⟩
  have hmem := hlip h fun l => (sepTuplesLipschitz s).2 (A l) (hh l)
  obtain ⟨hf, -, -⟩ := id hmem
  exact ⟨(mem_sepTuplesR4_iff s h).2
    ⟨fun l => ((mem_c1SuppIn_iff s (A l) (h l)).1 (hh l)).1, hf.2.1, hf.2.2⟩, hmem⟩
theorem supportGapPositive : SupportGapPositive := by
  intro n hn f hf
  refine ⟨?_, ?_, fun ρ hρ hsup d hd hdf => ?_⟩
  · have hpair : ∀ i k, i ≠ k → 0 < ToriLimits.infDist (fnSupport (f i)) (fnSupport (f k)) :=
      fun i k hik =>
        SeparatedTuplesR4.setDistR4_pos_of_disjoint (hf.2.1 i) isClosed_closure (hf.2.2 i k hik)
    have hfin : ∃ p : {p : Fin n × Fin n // p.1 ≠ p.2}, ∀ q : {p : Fin n × Fin n // p.1 ≠ p.2},
        ToriLimits.infDist (fnSupport (f p.1.1)) (fnSupport (f p.1.2)) ≤
          ToriLimits.infDist (fnSupport (f q.1.1)) (fnSupport (f q.1.2)) := by
      have : Nonempty {p : Fin n × Fin n // p.1 ≠ p.2} :=
        ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩⟩
      exact Finite.exists_min _
    obtain ⟨p, hp⟩ := hfin
    exact (hpair _ _ p.2).trans_le
      (le_iInf fun i => le_iInf fun k => le_iInf fun hik => hp ⟨(i, k), hik⟩)
  · obtain ⟨C, hC⟩ := (isCompact_iUnion fun i => hf.2.1 i).isBounded.exists_norm_le
    refine ⟨2 * |C| + 1, by positivity, fun i x hx => ?_⟩
    have h₁ := hC x (mem_iUnion.2 ⟨i, hx⟩)
    have h₂ := SeparatedTuplesR4.euclidNormVec_le_two_mul_norm x
    have h₃ := le_abs_self C
    change TorusMetric.euclidNormVec x < 2 * |C| + 1
    linarith
  · have hadm : AdmissibleSets (q := n) (by omega) d ρ hd hρ (fun i => fnSupport (f i)) := by
      refine ⟨fun i => ⟨0, fun x hx => ?_⟩, fun i k hik => hdf.trans
        (iInf_le_of_le i (iInf_le_of_le k (iInf_le _ hik)))⟩
      have h₁ : TorusMetric.euclidNormVec x < ρ := hsup i hx
      change TorusMetric.euclidNormVec (x - 0) ≤ ρ
      rw [sub_zero]
      exact h₁.le
    exact ⟨hadm, (mem_lipTuples_iff_parts n hn d ρ hd hρ f).2 ⟨hf.1, hadm.1, hadm.2⟩⟩
section Euclidean
variable (D : PeriodicSpace.Params)
theorem euclidean_quotDist_eq (x x' : Fin 4 → ℝ) :
    PeriodicSpace.Kind.quotDist D .euclidean x x' = TorusMetric.euclidNormVec (x - x') := by apply _root_.YangMills.Construction.PeriodicSpace.QuotientGeometry.quotDist_euclidean <;> assumption
theorem euclidean_setInfDist_eq (S S' : Set (Fin 4 → ℝ)) :
    PeriodicSpace.Kind.setInfDist D .euclidean S S' = ToriLimits.infDist S S' := by
  simp only [PeriodicSpace.Kind.setInfDist, ToriLimits.infDist, TestFunctions.setDistR4]
  refine iInf_congr fun a => iInf_congr fun _ => iInf_congr fun b => iInf_congr fun _ => ?_
  exact congrArg ENNReal.ofReal (euclidean_quotDist_eq D a b)
theorem euclidean_supportQ_eq (u : RealFn) :
    PeriodicSpace.Kind.supportQ D .euclidean u = fnSupport u :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (euclidean_quotDist_eq D) _
theorem euclidean_isLipschitzQ_iff (u : RealFn) :
    PeriodicSpace.Kind.IsLipschitzQ D .euclidean u ↔ LipschitzR4 u := by
  constructor
  · rintro ⟨C, h₀, h⟩
    exact ⟨C, h₀, fun x y => (h x y).trans_eq (by rw [euclidean_quotDist_eq D x y]; rfl)⟩
  · rintro ⟨C, h₀, h⟩
    exact ⟨C, h₀, fun x y => (h x y).trans_eq (by rw [euclidean_quotDist_eq D x y]; rfl)⟩
theorem euclidean_isCompactQ_iff (Z : Set (Fin 4 → ℝ)) :
    PeriodicSpace.Kind.IsCompactQ D .euclidean Z ↔ IsCompact Z :=
  SeparatedTuplesR4.isCompactWrt_euclid_iff (euclidean_quotDist_eq D) Z
theorem euclidean_closedBallAbout_eq (x : Fin 4 → ℝ) (R : ℝ) :
    PeriodicSpace.Kind.closedBallAbout D .euclidean x R = closedBallR4 x R :=
  Set.ext fun (y : Fin 4 → ℝ) => Iff.of_eq (congrArg (· ≤ R) (euclidean_quotDist_eq D y x))
theorem euclidean_centredBall_eq (ρ : ℝ) (hρ : 0 < ρ) :
    PeriodicSpace.Kind.centredBall D .euclidean (ENNReal.ofReal ρ) = ballOrigin ρ := by
  unfold PeriodicSpace.Kind.centredBall
  rw [if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hρ.le]
  refine Set.ext fun (y : Fin 4 → ℝ) => ?_
  have h₁ : PeriodicSpace.Kind.quotDist D .euclidean y
      (PeriodicSpace.Kind.origin D .euclidean) = TorusMetric.euclidNormVec y :=
    (euclidean_quotDist_eq D y 0).trans (congrArg TorusMetric.euclidNormVec (sub_zero y))
  exact Iff.of_eq (congrArg (· < ρ) h₁)
theorem euclidean_isCompactQ_supportQ_iff (u : RealFn) :
    PeriodicSpace.Kind.IsCompactQ D .euclidean
      (PeriodicSpace.Kind.supportQ D .euclidean u) ↔ IsCompact (fnSupport u) :=
  (euclidean_isCompactQ_iff D _).trans (Iff.of_eq (congrArg IsCompact (euclidean_supportQ_eq D u)))
theorem euclidean_supportQ_subset_iff (u : RealFn) (A : Set (Fin 4 → ℝ)) :
    PeriodicSpace.Kind.supportQ D .euclidean u ⊆ A ↔ fnSupport u ⊆ A :=
  Iff.of_eq (congrArg (· ⊆ A) (euclidean_supportQ_eq D u))
theorem euclidean_supportQ_disjoint_iff (u v : RealFn) :
    Disjoint (PeriodicSpace.Kind.supportQ D .euclidean u)
      (PeriodicSpace.Kind.supportQ D .euclidean v) ↔ Disjoint (fnSupport u) (fnSupport v) :=
  Iff.of_eq (congrArg₂ Disjoint (euclidean_supportQ_eq D u) (euclidean_supportQ_eq D v))
theorem euclidean_setInfDist_supportQ_eq (u v : RealFn) :
    PeriodicSpace.Kind.setInfDist D .euclidean
      (PeriodicSpace.Kind.supportQ D .euclidean u)
      (PeriodicSpace.Kind.supportQ D .euclidean v) =
        ToriLimits.infDist (fnSupport u) (fnSupport v) :=
  (euclidean_setInfDist_eq D _ _).trans
    (congrArg₂ ToriLimits.infDist (euclidean_supportQ_eq D u) (euclidean_supportQ_eq D v))
theorem euclidean_supportQ_in_ball_iff (u : RealFn) (R : ℝ) (hR : 0 < R) :
    (∃ S, PeriodicSpace.Kind.IsClosedBallWithRadius D .euclidean S R ∧
      PeriodicSpace.Kind.supportQ D .euclidean u ⊆ S) ↔
      ∃ x, fnSupport u ⊆ closedBallR4 x R := by
  constructor
  · rintro ⟨S, ⟨-, x, rfl⟩, hS⟩
    exact ⟨x, (euclidean_supportQ_eq D u).symm.subset.trans
      (hS.trans (euclidean_closedBallAbout_eq D x R).subset)⟩
  · rintro ⟨x, hx⟩
    exact ⟨PeriodicSpace.Kind.closedBallAbout D .euclidean x R, ⟨hR, x, rfl⟩,
      (euclidean_supportQ_eq D u).subset.trans (hx.trans (euclidean_closedBallAbout_eq D x R).symm.subset)⟩
theorem euclideanSpaceNotions : EuclideanSpaceNotions D :=
  ⟨euclidean_quotDist_eq D, euclidean_setInfDist_eq D, fun y S => euclidean_setInfDist_eq D {y} S,
    fun _ => Iff.rfl, euclidean_supportQ_eq D, euclidean_isLipschitzQ_iff D⟩
theorem euclidean_lipschitzSupportedIn_eq (A : Set (Fin 4 → ℝ)) :
    PeriodicSpace.Kind.lipschitzSupportedIn D .euclidean A = lipSuppIn A :=
  Set.ext fun (h : RealFn) =>
    (euclidean_isLipschitzQ_iff D h).and
      ((euclidean_isCompactQ_supportQ_iff D h).and (euclidean_supportQ_subset_iff D h A))
theorem euclideanBallsAndLipClass : EuclideanBallsAndLipClass D :=
  ⟨fun x R _ => euclidean_closedBallAbout_eq D x R, euclidean_centredBall_eq D,
    euclidean_lipschitzSupportedIn_eq D⟩
theorem euclideanC1Classes (s : Conventions.StandingParameters) : EuclideanC1Classes D s := by
  refine ⟨fun A => Set.ext fun (h : RealFn) => ?_,
    fun n _ => Set.ext fun (f : Fin n → RealFn) => ?_⟩
  · exact Iff.trans ((Iff.rfl : ContDiff ℝ 1 h ↔ ContDiff ℝ 1 h).and
      ((euclidean_isCompactQ_supportQ_iff D h).and (euclidean_supportQ_subset_iff D h A)))
      (mem_c1SuppIn_iff s A h).symm
  · exact Iff.trans ((Iff.rfl : (∀ i, ContDiff ℝ 1 (f i)) ↔ ∀ i, ContDiff ℝ 1 (f i)).and
      ((forall_congr' fun i => euclidean_isCompactQ_supportQ_iff D (f i)).and
        (forall_congr' fun i => forall_congr' fun k => forall_congr' fun _ =>
          euclidean_supportQ_disjoint_iff D (f i) (f k))))
      (mem_sepTuplesR4_iff s f).symm
theorem euclidean_mem_sepLipTuples_iff {n : ℕ} (f : Fin n → RealFn) :
    f ∈ PeriodicSpace.Kind.sepLipTuples D .euclidean n ↔ IsSepLipTuple f :=
  (forall_congr' fun i => euclidean_isLipschitzQ_iff D (f i)).and
    ((forall_congr' fun i => euclidean_isCompactQ_supportQ_iff D (f i)).and
      (forall_congr' fun i => forall_congr' fun k => forall_congr' fun _ =>
        euclidean_supportQ_disjoint_iff D (f i) (f k)))
theorem euclideanTuples : EuclideanTuples D := by
  refine ⟨fun n _ f => euclidean_mem_sepLipTuples_iff D f, fun n _ ρ hρ f => ?_,
    fun n hn h hh => ?_, rfl, fun n hn d R hd hR =>
      Set.ext fun (f : Fin n → RealFn) => ?_⟩
  · exact (euclidean_mem_sepLipTuples_iff D f).and (forall_congr' fun i =>
      Iff.of_eq (congrArg₂ (· ⊆ ·) (euclidean_supportQ_eq D (f i)) (euclidean_centredBall_eq D ρ hρ)))
  · exact iInf_congr fun i => iInf_congr fun k => iInf_congr fun _ =>
      euclidean_setInfDist_supportQ_eq D (h i) (h k)
  · exact Iff.trans ((forall_congr' fun i => euclidean_isLipschitzQ_iff D (f i)).and
      ((forall_congr' fun i => euclidean_supportQ_in_ball_iff D (f i) R hR).and
        (forall_congr' fun i => forall_congr' fun k => forall_congr' fun _ =>
          Iff.of_eq (congrArg (ENNReal.ofReal d ≤ ·)
            (euclidean_setInfDist_supportQ_eq D (f i) (f k))))))
      (mem_lipTuples_iff_parts n hn d R hd hR f).symm
end Euclidean
theorem gluingClassEuclidean (G : SourcesAndGluing.GluingSetup) :
    GluingClassEuclidean G := by
  intro n hn d R hd hR
  exact Set.ext fun (f : Fin n → RealFn) =>
    (mem_lipTuples_iff_parts n hn d R hd hR f).symm
theorem statement_holds : Statement :=
  ⟨subfamilyAdmissible, thickeningDistanceBound,
    fun s => ⟨sepTuplesLipschitz s, admissibleProductsInClasses s⟩,
    supportGapPositive,
    fun D => ⟨euclideanSpaceNotions D, euclideanBallsAndLipClass D,
      euclideanTuples D, euclideanC1Classes D⟩,
    gluingClassEuclidean⟩
end YangMills.Construction.ToriLimits.SubfamiliesAndGaps
end

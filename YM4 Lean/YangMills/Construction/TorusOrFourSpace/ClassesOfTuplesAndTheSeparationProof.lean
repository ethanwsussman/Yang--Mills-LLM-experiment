import YangMills.Construction.TorusOrFourSpace.ClassesOfTuplesAndTheSeparation
import YangMills.Construction.TorusOrFourSpace.CompactnessAndLiftsOfClosedBallsAndOriginBalls
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.TupleClasses
open YangMills.Construction.PeriodicSpace YangMills.Construction.PeriodicSpace.Kind
variable (P : Params) (Y : Kind)
private theorem allowed_radius_pos {R : ℝ} (hR : R ∈ allowedRadii P Y) : 0 < R := by
  cases Y
  · exact hR
  · exact hR.1
private theorem lipTuples_monotone (n : ℕ) : LipTuplesMonotone P Y n := by
  intro d' d R R' _ hd _ hR' hRR' f hf
  obtain ⟨hlip, hball, hsep⟩ := hf
  refine ⟨hlip, fun i => ?_, fun i k hik => (ENNReal.ofReal_le_ofReal hd).trans (hsep i k hik)⟩
  obtain ⟨B, ⟨_, c, rfl⟩, hB⟩ := hball i
  refine ⟨closedBallAbout P Y c R', ⟨allowed_radius_pos P Y hR', c, rfl⟩, hB.trans ?_⟩
  intro y hy
  exact le_trans hy hRR'
private theorem supportGap_pos
    (hcpt : Kind.QuotientCompactC1.CompactSetsThickenings P Y)
    {n : ℕ} (hn : 2 ≤ n) {g : FnTuple P Y n} (hg : CompactDisjointSupports P Y g) :
    0 < supportGap P Y g := by
  classical
  have : Nonempty (Fin n × Fin n) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  let w : Fin n × Fin n → ℝ≥0∞ := fun p =>
    if p.1 ≠ p.2 then setInfDist P Y (supportQ P Y (g p.1)) (supportQ P Y (g p.2)) else ∞
  obtain ⟨p, hp⟩ := Finite.exists_min w
  have hw : 0 < w p := by
    by_cases hne : p.1 ≠ p.2
    · rw [show w p = setInfDist P Y (supportQ P Y (g p.1)) (supportQ P Y (g p.2)) from if_pos hne]
      exact hcpt.1 _ _ (hg.1 _) (hg.1 _) (hg.2 _ _ hne)
    · rw [show w p = ∞ from if_neg hne]
      exact ENNReal.zero_lt_top
  unfold supportGap
  refine lt_of_lt_of_le hw (le_iInf fun i => le_iInf fun k => le_iInf fun hik => ?_)
  have hwik : w (i, k) = setInfDist P Y (supportQ P Y (g i)) (supportQ P Y (g k)) := if_pos hik
  exact hwik ▸ hp (i, k)
private theorem supportGap_eq_top_iff {n : ℕ} (g : FnTuple P Y n) :
    supportGap P Y g = ∞ ↔ SupportsAtMostOneNonempty P Y g := by
  unfold supportGap
  constructor
  · intro htop i hi k hk
    by_contra hik
    obtain ⟨z, hz⟩ := hi
    obtain ⟨z', hz'⟩ := hk
    have h1 : (⨅ i, ⨅ k, ⨅ _ : i ≠ k, setInfDist P Y (supportQ P Y (g i)) (supportQ P Y (g k))) ≤
        setInfDist P Y (supportQ P Y (g i)) (supportQ P Y (g k)) :=
      (iInf_le _ i).trans ((iInf_le _ k).trans (iInf_le _ hik))
    have h2 : setInfDist P Y (supportQ P Y (g i)) (supportQ P Y (g k)) ≤
        ENNReal.ofReal (quotDist P Y z z') :=
      (iInf₂_le z hz).trans (iInf₂_le z' hz')
    rw [htop] at h1
    exact ENNReal.ofReal_ne_top (top_le_iff.mp (h1.trans h2))
  · intro hone
    refine top_unique (le_iInf fun i => le_iInf fun k => le_iInf fun hik => ?_)
    by_cases hi : (supportQ P Y (g i)).Nonempty
    · have hk : supportQ P Y (g k) = ∅ := by
        by_contra hk
        exact hik (hone hi (Set.nonempty_iff_ne_empty.mpr hk))
      simp [setInfDist, hk]
    · rw [Set.not_nonempty_iff_eq_empty] at hi
      simp [setInfDist, hi]
private theorem exists_zero_component
    (hmet : Kind.QuotientCompactC1.QuotDistIsMetricWithLifts P Y)
    {n : ℕ} (hn : 2 ≤ n) {g : FnTuple P Y n} (hone : SupportsAtMostOneNonempty P Y g) :
    ∃ i, ∀ y, g i y = 0 := by
  have hempty : ∃ j, supportQ P Y (g j) = ∅ := by
    by_contra hne
    have hall : ∀ j, (supportQ P Y (g j)).Nonempty := fun j =>
      Set.nonempty_iff_ne_empty.mpr fun hj => hne ⟨j, hj⟩
    have hik := hone (hall ⟨0, by omega⟩) (hall ⟨1, by omega⟩)
    simp [Fin.ext_iff] at hik
  obtain ⟨j, hj⟩ := hempty
  refine ⟨j, fun y => ?_⟩
  by_contra hy
  have hmem : y ∈ supportQ P Y (g j) := by
    intro r hr
    refine ⟨y, hy, ?_⟩
    rw [(hmet.2.1 y y).2 rfl]
    exact hr
  rw [hj] at hmem
  exact hmem
private theorem sepTuple_in_ball
    (hcov : ∀ S : Set (Y.Pt P), IsCompactQ P Y S →
      ∃ ρ : ℝ≥0∞, 0 < ρ ∧ ρ < ∞ ∧ S ⊆ centredBall P Y ρ) (n : ℕ) :
    SepC1TupleInBall P Y n := by
  intro f hf
  choose ρ _ hfin hsub using fun i => hcov (supportQ P Y (f i)) (hf.2.1 i)
  have hsum : ∑ i, ρ i < ∞ := ENNReal.sum_lt_top.2 fun i _ => hfin i
  have htot : 1 + ∑ i, ρ i < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hsum⟩
  refine ⟨1 + ∑ i, ρ i, lt_of_lt_of_le zero_lt_one le_self_add, htot, hf, fun i y hy => ?_⟩
  have hi := hsub i hy
  have hle : ρ i ≤ 1 + ∑ j, ρ j :=
    (Finset.single_le_sum (f := ρ) (fun _ _ => zero_le) (Finset.mem_univ i)).trans le_add_self
  rw [centredBall, if_neg (hfin i).ne] at hi
  rw [centredBall, if_neg htot.ne]
  exact lt_of_lt_of_le hi (ENNReal.toReal_mono htot.ne hle)
private theorem restrict_perm_separated (n : ℕ) : SepC1TupleRestrictPerm P Y n := by
  intro f hf
  refine ⟨fun J _ => ⟨fun j => hf.1 _, ⟨fun j => hf.2.1 _, fun j l hjl => ?_⟩⟩,
    fun σ => ⟨fun i => hf.1 _, ⟨fun i => hf.2.1 _, fun i k hik => ?_⟩⟩⟩
  · exact hf.2.2 _ _ ((J.orderEmbOfFin rfl).injective.ne hjl)
  · exact hf.2.2 _ _ (σ.injective.ne hik)
theorem statement_holds
    (hq : Kind.QuotientCompactC1.Claim)
    (hb : BallCompactnessAndTorusLifts) :
    Statement := by
  intro P Y n _
  obtain ⟨hmet, _, _, hcpt, _⟩ := hq P Y
  refine ⟨lipTuples_monotone P Y n, fun hn g hg => ⟨supportGap_pos P Y hcpt hn hg.2, le_top⟩,
    fun hn g _ => ⟨supportGap_eq_top_iff P Y g, exists_zero_component P Y hmet hn⟩,
    sepTuple_in_ball P Y ((hb P).2.2.2.2.2.2.1 Y) n, restrict_perm_separated P Y n⟩
end YangMills.Construction.PeriodicSpace.TupleClasses

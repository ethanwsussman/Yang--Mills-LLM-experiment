import YangMills.Construction.ClusterExpansionOfAStep.AZeroFactorKillsTheState
import YangMills.Construction.ClusterExpansionOfAStep.AdmissionIsAProduct
import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.ClusterExpansionOfAStep.FactorsAtACase
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours TorusFields TorusLumps StepSettings StepCosts
namespace CoarseWeightZero
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem chainConnected_labelSet_of_support {q : CoarseState R n} {C : Finset (TorusSite n)}
    {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))}
    {ωt : Yt → R.labels.Ω} {bad : Finset (TorusBond (n * R.params.side))}
    {b : BaseChoice R.params.side n} (hext : q.IsExtension C W Yt ωt bad b)
    {y z : TorusSite (n * R.params.side)} (hy : y ∈ q.labelSet)
    (hchain : ChainConnected R.range Yt y z) :
    ChainConnected R.range q.labelSet y z ∧ z ∈ q.labelSet := by
  classical
  induction hchain with
  | refl => exact ⟨Relation.ReflTransGen.refl, hy⟩
  | @tail u v _ hstep ih =>
    obtain ⟨hu, hv, hdist⟩ := hstep
    have huq := ih.2
    have hvq : v ∈ q.labelSet := by
      refine (hext.mem_support_iff v).mpr ⟨hv, ?_⟩
      by_contra hnot
      have hfar := hext.far_support v hv hnot u (by simp [huq])
      rw [supDist_comm] at hfar
      omega
    exact ⟨ih.1.tail ⟨huq, hvq, hdist⟩, hvq⟩
theorem chainConnected_mono {Y Y' : Finset (TorusSite (n * R.params.side))} (hsub : Y ⊆ Y')
    {y z : TorusSite (n * R.params.side)} (hchain : ChainConnected R.range Y y z) :
    ChainConnected R.range Y' y z := by
  induction hchain with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail ⟨hsub hstep.1, hsub hstep.2.1, hstep.2.2⟩
theorem mem_chainComponents_support {q : CoarseState R n} {C : Finset (TorusSite n)}
    {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))}
    {ωt : Yt → R.labels.Ω} {bad : Finset (TorusBond (n * R.params.side))}
    {b : BaseChoice R.params.side n} (hext : q.IsExtension C W Yt ωt bad b)
    {X : Finset (TorusSite (n * R.params.side))}
    (hX : X ∈ chainComponents R.range q.labelSet) : X ∈ chainComponents R.range Yt := by
  classical
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hX
  have hsub : q.labelSet ⊆ Yt := fun z hz => ((hext.mem_support_iff z).mp hz).1
  refine Finset.mem_image.mpr ⟨y, hsub hy, ?_⟩
  ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hz, hchain⟩
    have hboth := chainConnected_labelSet_of_support hext hy hchain
    exact ⟨hboth.2, hboth.1⟩
  · rintro ⟨hz, hchain⟩
    exact ⟨hsub hz, chainConnected_mono hsub hchain⟩
theorem mem_baseSitesAt {F : BlockFrame} {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))}
    {b : F.Cell → F.Site F.depth} (hb : IsBaseChoice J₀ h b) (y : F.Cell) :
    b y ∈ baseSitesAt J₀ h y := by
  unfold baseSitesAt
  by_cases hy : nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y
  · rw [if_pos hy]
    exact Finset.mem_singleton.mpr ((hb y).1 hy)
  · rw [if_neg hy]
    obtain ⟨h1, h2⟩ := (hb y).2 hy
    exact Finset.mem_filter.mpr ⟨h1, h2⟩
theorem blockBaseWeight_ne_zero {ℓ : StepParameters}
    {h : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0))} {b : BaseChoice ℓ.side n}
    (hb : IsBaseChoice ℓ.baseDepth h b) (y : (stepBlockFrame ℓ.side n).Cell) :
    blockBaseWeight ℓ h y (b y) ≠ 0 := by
  classical
  unfold blockBaseWeight
  have hmem := mem_baseSitesAt hb y
  split_ifs with hx
  · have h1 : 0 < (baseSitesAt ℓ.baseDepth h y).card := Finset.card_pos.mpr ⟨_, hmem⟩
    have h2 : (0 : ℝ) < ((baseSitesAt ℓ.baseDepth h y).card : ℝ) := by exact_mod_cast h1
    exact (div_pos one_pos h2).ne'
  · exact absurd hmem hx
end CoarseWeightZero
open CoarseWeightZero in
theorem coarseWeight_zero_of_factor_zero (hA : AdmissionIsProduct)
    (hF : ProdCoarseFactorEqStatement) : CoarseWeightZeroOfFactorZero := by
  classical
  intro R hR n _ hside V q hq hz
  obtain ⟨X, hX, h0⟩ := hz
  have hLpos : 0 < R.params.side := by have := hR.admissible.L_ge; omega
  have hsideL : IsBlockTorusSide R.params (n * R.params.side) := by
    refine ⟨Dvd.intro_left _ rfl, ?_⟩
    have h1 := hside.2
    have h2 : 1 ≤ R.params.side := hLpos
    nlinarith
  have hmass : coarseStateMass R (hotCoreSites R V) V q = 0 := by
    unfold coarseStateMass
    refine Finset.sum_eq_zero fun bad hbad => Finset.sum_eq_zero fun Yt _ =>
      Finset.sum_eq_zero fun b _ => ?_
    have hzero : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
        (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
            coarseStateOf R (hotCoreSites R V) (q.fieldWithStoredLinks W) Yt
              (q.fillLabels Yt ν) bad b = q then
          ENNReal.ofReal (stepWeight R (hotCoreSites R V) V (q.fieldWithStoredLinks W) Yt
            (q.fillLabels Yt ν) bad b) else 0) = 0 := by
      intro W ν
      split_ifs with hcond
      · obtain ⟨hH, hS⟩ := hcond
        have hbad' : bad ⊆ markedBonds R (hotCoreSites R V) := Finset.mem_powerset.mp hbad
        by_cases hbases : b ∈ baseChoices R.params
          (readAtLevel (stepBlockFrame R.params.side n) 0 (q.fieldWithStoredLinks W))
        swap
        · have hB : baseLaw (q.fieldWithStoredLinks W) b = 0 := by
            unfold baseLaw
            rw [if_neg hbases]
          have hw : stepWeight R (hotCoreSites R V) V (q.fieldWithStoredLinks W) Yt
              (q.fillLabels Yt ν) bad b = 0 := by
            unfold stepWeight
            rw [hB]
            ring
          rw [hw, ENNReal.ofReal_zero]
        have hIB : IsBaseChoice R.params.baseDepth
            (stepHotLumps R.params (q.fieldWithStoredLinks W)) b := (Finset.mem_filter.mp hbases).2
        have hprod := hF R hR n hside V q (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b
          hq hbad' hH hIB hS
        have hext := ((hA R hR n hside V q hq (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν)
          bad b hbad' hH).mp hS).2
        rw [Finset.prod_eq_zero hX h0] at hprod
        have hw : stepWeight R (hotCoreSites R V) V (q.fieldWithStoredLinks W) Yt
            (q.fillLabels Yt ν) bad b = 0 := by
          unfold stepWeight
          rcases mul_eq_zero.mp hprod.symm with h1 | h3
          · rcases mul_eq_zero.mp h1 with h1 | h2
            · obtain ⟨Xc, hXc, hΦ⟩ := Finset.prod_eq_zero_iff.mp h1
              have hD : R.labelWeight (n * R.params.side) (q.fieldWithStoredLinks W) Yt
                  (q.fillLabels Yt ν) = 0 := by
                have hP : ∏ X ∈ chainComponents (clusterRange R.coupling) Yt,
                    R.clusterFactor (n * R.params.side) (q.fieldWithStoredLinks W) Yt
                      (q.fillLabels Yt ν) X = 0 :=
                  Finset.prod_eq_zero (mem_chainComponents_support hext hXc) hΦ
                rw [hR.hasExpansions.2.form (n * R.params.side) hsideL _ Yt _ hH, hP, mul_zero]
              rw [hD]
              ring
            · obtain ⟨c, hcm, hc0⟩ := Finset.prod_eq_zero_iff.mp h2
              have hM : markProduct R (hotCoreSites R V) V (q.fieldWithStoredLinks W) bad = 0 := by
                unfold markProduct
                refine Finset.prod_eq_zero (Finset.mem_inter.mp hcm).1 ?_
                convert hc0
              rw [hM, mul_zero]
          · obtain ⟨y, _, hy0⟩ := Finset.prod_eq_zero_iff.mp h3
            exact absurd hy0 (blockBaseWeight_ne_zero hIB _)
        rw [hw, ENNReal.ofReal_zero]
      · rfl
    simp only [hzero, lintegral_const, zero_mul]
  unfold coarseStateWeight
  rw [hmass]
  rfl
end YangMills.Construction.ClusterExpansionOfAStep
end

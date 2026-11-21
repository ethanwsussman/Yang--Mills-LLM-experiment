import YangMills.Construction.TorusOrFourSpace.BoundOfC1FormsAtEveryRadius
import YangMills.Construction.TorusOrFourSpace.FactsOnTheEffectiveConstants
import YangMills.Construction.TorusOrFourSpace.FromTheFamilyToAllSeparatedTuples
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesInBallsAndTheirSeparation
import YangMills.Construction.TorusOrFourSpace.TheTwoKindsOfSequencesOfC1Forms
import Mathlib
set_option autoImplicit false
open scoped ENNReal Topology
open Filter
noncomputable section
namespace YangMills.Construction.PeriodicSpace.SeparatedExtension
open Kind
section
variable {D : Params} {E : Kind}
private theorem multilinearOnProduct_of_onClasses {n : ℕ} {K : Set (FnTuple D E n)} {Φ : K → ℝ}
    {W : Fin n → Set (E.Pt D → ℝ)} (hW : productSet D E W ⊆ K)
    (hΦ : MultilinearOnClasses D E K Φ W) :
    IsMultilinearOnProduct D E (productSet D E W) W fun t => Φ ⟨t.1, hW t.2⟩ := by
  obtain ⟨V, hVW, hmemK, hlinear⟩ := hΦ
  have hinV : ∀ l (u : E.Pt D → ℝ), u ∈ W l → u ∈ V l := fun l u hu => by
    rw [← SetLike.mem_coe, hVW l]
    exact hu
  refine ⟨subset_rfl, fun g hg i u hu v hv a b hua hvb hab => ?_⟩
  let x : ∀ l, V l := fun l => ⟨g l, hinV l _ (hg l (Set.mem_univ l))⟩
  have hupd : ∀ w : V i,
      (fun l => ((Function.update x i w l : V l) : E.Pt D → ℝ)) =
        Function.update g i (w : E.Pt D → ℝ) := by
    intro w
    funext l
    by_cases hl : l = i
    · subst hl
      simp
    · simp [Function.update_of_ne hl, x]
  let u₀ : V i := ⟨u, hinV i u hu⟩
  let v₀ : V i := ⟨v, hinV i v hv⟩
  let G : V i → ℝ := fun w =>
    Φ ⟨fun l => ((Function.update x i w l : V l) : E.Pt D → ℝ), hmemK _⟩
  have hG : ∀ (w : V i) (hw : Function.update g i (w : E.Pt D → ℝ) ∈
      productSet D E W), G w = Φ ⟨Function.update g i (w : E.Pt D → ℝ), hW hw⟩ := by
    intro w hw
    exact congrArg Φ (Subtype.ext (hupd w))
  have hlin : IsLinearMap ℝ G := hlinear x i
  have hsum : G (a • u₀ + b • v₀) = G (a • u₀) + G (b • v₀) := hlin.map_add _ _
  have hscaleU : G (a • u₀) = a * G u₀ := hlin.map_smul a u₀
  have hscaleV : G (b • v₀) = b * G v₀ := hlin.map_smul b v₀
  have q₁ : G (a • u₀ + b • v₀) = Φ ⟨Function.update g i (a • u + b • v), hW hab⟩ :=
    hG (a • u₀ + b • v₀) hab
  have q₂ : G u₀ = Φ ⟨Function.update g i u, hW hua⟩ := hG u₀ hua
  have q₃ : G v₀ = Φ ⟨Function.update g i v, hW hvb⟩ := hG v₀ hvb
  change Φ ⟨Function.update g i (a • u + b • v), hW hab⟩ =
    a * Φ ⟨Function.update g i u, hW hua⟩ + b * Φ ⟨Function.update g i v, hW hvb⟩
  rw [← q₁, ← q₂, ← q₃, hsum, hscaleU, hscaleV]
private theorem closedBallAbout_origin_subset_centredBall {R : ℝ} (hR : 0 < R) {r : ℝ≥0∞}
    (hRr : ENNReal.ofReal R < r) : closedBallAbout D E (origin D E) R ⊆ centredBall D E r := by
  intro y hy
  unfold centredBall
  split_ifs with htop
  · trivial
  · have hlt : R < r.toReal := (ENNReal.ofReal_lt_iff_lt_toReal hR.le htop).mp hRr
    exact lt_of_le_of_lt hy hlt
end
private theorem approximantValuesClose_of (hUnif : UniformC1Bounds)
    (hFam : DiagonalLimits.FamilyApproximation.Statement)
    (hConst : EffectiveConstantFacts.Claim) (D : Params) (E : Kind)
    (θ : RadiusRatio) (P : TorusPartitionChoice D θ) (F : DenseChoiceFamily D E)
    (C : BoundFamily) : ApproximantValuesClose D E θ P F C := by
  intro J₀ ρ Ψ n hn r hr f hf d hd hgap
  have hd3 : 0 < d / 3 := div_pos hd three_pos
  have hrad : 0 < r + d / 3 := add_pos hr hd3
  refine ⟨?_, ?_⟩
  · obtain ⟨i₀, hi₀⟩ := Ψ.radii.eventually_gt (r + d / 3) hrad
    exact ⟨max i₀ (Ψ.thresholdAtRadius θ n hn _ hrad), fun j hj =>
      ⟨(le_max_right _ _).trans hj, hi₀ j.1 j.2 ((le_max_left _ _).trans hj) j.2⟩⟩
  · intro j₁ hj₁ ε hε φ hφ j hj
    obtain ⟨hthr, hρj⟩ := hj₁ j hj
    obtain ⟨⟨-, hsepd, hinside⟩, -, hcompare, -⟩ := hFam D E F n hn f hf.1 d hd hgap ε hε
    have hinBall : ∀ l, DiagonalLimits.closedSupportThickening D E f hf.1 d hd l ⊆
        closedBallAbout D E (origin D E) (r + d / 3) := by
      have h := hinside (ENNReal.ofReal r) (ENNReal.ofReal_pos.mpr hr) ENNReal.ofReal_lt_top hf.2
      rwa [ENNReal.toReal_ofReal hr.le] at h
    have hsets : InBallsAndSeparated D E
        (DiagonalLimits.closedSupportThickening D E f hf.1 d hd) (d / 3) (r + d / 3) :=
      ⟨fun l => ⟨_, ⟨hrad, _, rfl⟩, hinBall l⟩, hsepd⟩
    obtain ⟨hmult, hsubset, hbd, -⟩ := (hUnif D E θ P C).1 J₀ ρ Ψ n hn (d / 3) (r + d / 3) hd3 hrad _
      hsets j hthr fun l => (hinBall l).trans (closedBallAbout_origin_subset_centredBall hrad hρj)
    have hnonneg : 0 ≤ effConstAt P E C n (d / 3) (r + d / 3) :=
      hConst.2.2.1 D θ P E C n hn (d / 3) (r + d / 3) hd3 hrad
    obtain ⟨hfin, hφin, hbound⟩ := hcompare φ hφ _ hnonneg (fun t => Ψ.func j n hn ⟨t.1, hsubset t.2⟩)
      (multilinearOnProduct_of_onClasses hsubset hmult) fun t => hbd ⟨t.1, hsubset t.2⟩ t.2
    exact ⟨hsubset hfin, hsubset hφin, hbound⟩
private theorem oneIsGoodThreshold_of (D : Params) (E : Kind) (θ : RadiusRatio) (C : BoundFamily) :
    OneIsGoodThresholdForHierarchies D E θ C := by
  intro J₀ Ψ hΨ n hn r hr f _ d hd _ j hj
  refine ⟨?_, ENNReal.ofReal_lt_top⟩
  have hone : Ψ.thresholdAtRadius θ n hn (r + d / 3) (add_pos hr (div_pos hd three_pos)) = 1 := by
    unfold BoundedC1FormSeq.thresholdAtRadius
    split_ifs with h
    · exact hΨ.1 _ _ _ _
    · exact hΨ.1 _ _ _ _
  rw [hone]
  exact hj
section
variable {D : Params} {E : Kind} {J₀ J : Sequences.PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞}
  {C : BoundFamily}
private def enumIndex (hJ : J.carrier ⊆ J₀.carrier) (k : ℕ) : J₀.carrier :=
  ⟨(DiagonalLimits.enumerate J k).1, hJ (DiagonalLimits.enumerate J k).2⟩
open Classical in
private def evalOrZero (Ψ : BoundedC1FormSeq D E J₀ ρ C) (n : ℕ) (hn : 2 ≤ n)
    (g : FnTuple D E n) (j : J₀.carrier) : ℝ :=
  if h : g ∈ sepC1TuplesInBall D E n (ρ j) then Ψ.func j n hn ⟨g, h⟩ else 0
private theorem evalOrZero_of_mem (Ψ : BoundedC1FormSeq D E J₀ ρ C) {n : ℕ} (hn : 2 ≤ n)
    {g : FnTuple D E n} {j : J₀.carrier} (h : g ∈ sepC1TuplesInBall D E n (ρ j)) :
    evalOrZero Ψ n hn g j = Ψ.func j n hn ⟨g, h⟩ :=
  dif_pos h
private def enumValues (Ψ : BoundedC1FormSeq D E J₀ ρ C) (hJ : J.carrier ⊆ J₀.carrier)
    (n : ℕ) (hn : 2 ≤ n) (g : FnTuple D E n) (k : ℕ) : ℝ :=
  evalOrZero Ψ n hn g (enumIndex hJ k)
private theorem enumValues_of_mem (Ψ : BoundedC1FormSeq D E J₀ ρ C)
    (hJ : J.carrier ⊆ J₀.carrier) {n : ℕ} (hn : 2 ≤ n) {g : FnTuple D E n} {k : ℕ}
    (h : g ∈ sepC1TuplesInBall D E n (ρ (enumIndex hJ k))) :
    enumValues Ψ hJ n hn g k = Ψ.func (enumIndex hJ k) n hn ⟨g, h⟩ :=
  evalOrZero_of_mem Ψ hn h
private theorem eventually_ge_enumerate (J : Sequences.PNatIndexSet) (m : ℤ) :
    ∀ᶠ k in atTop, m ≤ ((((DiagonalLimits.enumerate J k).1 : ℕ+) : ℕ) : ℤ) := by
  filter_upwards [eventually_ge_atTop m.toNat] with k hk
  have h := (DiagonalLimits.enumerate_strictMono J).le_apply (x := k)
  omega
private theorem eventually_mem_sepC1TuplesInBall (hDom : C1FormSeqKinds.EventuallyInDomains D E)
    (Ψ : BoundedC1FormSeq D E J₀ ρ C) (hJ : J.carrier ⊆ J₀.carrier) {n : ℕ} (hn : 2 ≤ n)
    {g : FnTuple D E n} (hg : g ∈ sepC1Tuples D E n) :
    ∀ᶠ k in atTop, g ∈ sepC1TuplesInBall D E n (ρ (enumIndex hJ k)) := by
  obtain ⟨m, hm⟩ := hDom J₀ ρ Ψ.toC1FormSeq n hn g hg
  filter_upwards [eventually_ge_enumerate J m] with k hk
  exact hm _ hk
private theorem cauchySeq_enumValues_of_hasLimitAt (Ψ : BoundedC1FormSeq D E J₀ ρ C)
    (hJ : J.carrier ⊆ J₀.carrier) {n : ℕ} (hn : 2 ≤ n) {g : FnTuple D E n}
    (h : HasLimitAt Ψ hJ n hn g) : CauchySeq (enumValues Ψ hJ n hn g) := by
  obtain ⟨m, hg, z, hz⟩ := h
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨m', hm'⟩ := hz (ε / 2) (half_pos hε)
  have hclose : ∀ᶠ k in atTop, ‖((enumValues Ψ hJ n hn g k : ℝ) : ℂ) - z‖ < ε / 2 := by
    filter_upwards [eventually_ge_enumerate J m, eventually_ge_enumerate J m'] with k h₁ h₂
    have hin : (DiagonalLimits.enumerate J k).1 ∈ (J.filterGe m).carrier :=
      ⟨(DiagonalLimits.enumerate J k).2, h₁⟩
    have hlt := hm' _ (DiagonalLimits.enumerate J k).2 h₂ hin
    rw [enumValues_of_mem Ψ hJ hn (hg ⟨_, hin⟩)]
    exact hlt
  obtain ⟨N, hN⟩ := eventually_atTop.mp hclose
  refine ⟨N, fun k hk => ?_⟩
  have h₁ := hN k hk
  have h₂ := hN N le_rfl
  rw [Real.dist_eq, ← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub]
  calc ‖((enumValues Ψ hJ n hn g k : ℝ) : ℂ) - ((enumValues Ψ hJ n hn g N : ℝ) : ℂ)‖
      = ‖(((enumValues Ψ hJ n hn g k : ℝ) : ℂ) - z) - (((enumValues Ψ hJ n hn g N : ℝ) : ℂ) - z)‖ := by
        congr 1
        ring
    _ ≤ _ := norm_sub_le _ _
    _ < ε := by linarith
private theorem cauchySeq_enumValues_of_mem_sepC1Tuples (θ : RadiusRatio) (P : TorusPartitionChoice D θ)
    (F : DenseChoiceFamily D E)
    (hFam : DiagonalLimits.FamilyApproximation.Statement)
    (hBasics : SeparatedTupleFacts.SeparatedTupleBasics)
    (hClose : ApproximantValuesClose D E θ P F C)
    (Ψ : BoundedC1FormSeq D E J₀ ρ C) (hJ : J.carrier ⊆ J₀.carrier)
    (hlim : ∀ (m : ℕ) (hm : 2 ≤ m) (φ : FnTuple D E m),
      (⟨m, φ⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ F.tuplesGeTwo →
        HasLimitAt Ψ hJ m hm φ)
    {n : ℕ} (hn : 2 ≤ n) {f : FnTuple D E n} (hf : f ∈ sepC1Tuples D E n) :
    CauchySeq (enumValues Ψ hJ n hn f) := by
  obtain ⟨⟨R₀, hR₀, hR₀top, hfR₀⟩, hgapPos, -⟩ := hBasics D E n hn f hf
  have hr : 0 < R₀.toReal := ENNReal.toReal_pos hR₀.ne' hR₀top.ne
  have hfr : f ∈ sepC1TuplesInBall D E n (ENNReal.ofReal R₀.toReal) := by
    rwa [ENNReal.ofReal_toReal hR₀top.ne]
  obtain ⟨s, hs₀, hs⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hgapPos.1.1
  have hd : 0 < (s : ℝ) := by exact_mod_cast ENNReal.coe_pos.mp hs₀
  have hgap : ENNReal.ofReal (s : ℝ) ≤ supportGap D E f := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hs.le
  obtain ⟨⟨j₁, hj₁⟩, hnear⟩ := hClose J₀ ρ Ψ n hn _ hr f hfr s hd hgap
  have hdefect := (hFam D E F n hn f hf s hd hgap 1 one_pos).2.2.2
  rw [Metric.cauchySeq_iff']
  intro τ hτ
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      effConstAt P E C n ((s : ℝ) / 3) (R₀.toReal + (s : ℝ) / 3) *
        DiagonalLimits.approxDefect D E f ε < τ / 4 := by
    have hprod := hdefect.const_mul
      (effConstAt P E C n ((s : ℝ) / 3) (R₀.toReal + (s : ℝ) / 3))
    rw [mul_zero] at hprod
    exact hprod.eventually (gt_mem_nhds (by positivity))
  obtain ⟨ε, hε₁, hε⟩ := (hsmall.and self_mem_nhdsWithin).exists
  obtain ⟨φ, hφ⟩ := (hFam D E F n hn f hf s hd hgap ε hε).2.1
  have hcauchyφ := cauchySeq_enumValues_of_hasLimitAt Ψ hJ hn (hlim n hn φ ⟨hφ.1, hn⟩)
  obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff'.mp hcauchyφ (τ / 4) (by positivity)
  have hfφ : ∀ᶠ k in atTop, |enumValues Ψ hJ n hn f k - enumValues Ψ hJ n hn φ k| ≤
      effConstAt P E C n ((s : ℝ) / 3) (R₀.toReal + (s : ℝ) / 3) *
        DiagonalLimits.approxDefect D E f ε := by
    filter_upwards [eventually_ge_enumerate J j₁] with k hk
    obtain ⟨h₁, h₂, hle⟩ := hnear j₁ hj₁ ε hε φ hφ (enumIndex hJ k) hk
    rw [enumValues_of_mem Ψ hJ hn h₁, enumValues_of_mem Ψ hJ hn h₂]
    exact hle
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hfφ
  refine ⟨max N₁ N₂, fun k hk => ?_⟩
  have hk₁ : N₁ ≤ k := (le_max_left _ _).trans hk
  have hk₂ : N₂ ≤ k := (le_max_right _ _).trans hk
  have b₁ := abs_le.mp (hN₂ k hk₂)
  have b₂ := abs_le.mp (hN₂ (max N₁ N₂) (le_max_right _ _))
  have b₃ := hN₁ k hk₁
  have b₄ := hN₁ (max N₁ N₂) (le_max_left _ _)
  rw [Real.dist_eq, abs_lt] at b₃ b₄
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [b₁.1, b₁.2, b₂.1, b₂.2, b₃.1, b₃.2, b₄.1, b₄.2]
end
private theorem familyLimitsExtend_of (hFam : DiagonalLimits.FamilyApproximation.Statement)
    (hBasics : SeparatedTupleFacts.SeparatedTupleBasics) (D : Params) (E : Kind)
    (θ : RadiusRatio) (P : TorusPartitionChoice D θ) (F : DenseChoiceFamily D E)
    (C : BoundFamily)
    (hDom : C1FormSeqKinds.EventuallyInDomains D E)
    (hClose : ApproximantValuesClose D E θ P F C) :
    FamilyLimitsExtend D E F C := by
  intro J₀ ρ Ψ J hJ hlim
  have hdef : EventuallyDefinedAlong Ψ hJ := by
    intro n hn f hf
    obtain ⟨m, hm⟩ := hDom J₀ ρ Ψ.toC1FormSeq n hn f hf
    exact ⟨m, fun j hj hle _ => hm ⟨j, hJ hj⟩ hle⟩
  have hconv : ∀ (n : ℕ) (hn : 2 ≤ n) (f : sepC1Tuples D E n),
      ∃ x, Tendsto (enumValues Ψ hJ n hn f.1) atTop (𝓝 x) := fun n hn f =>
    cauchySeq_tendsto_of_complete
      (cauchySeq_enumValues_of_mem_sepC1Tuples θ P F hFam hBasics hClose Ψ hJ hlim hn f.2)
  choose L hL using hconv
  have hmult : ∀ n (hn : 2 ≤ n),
      IsMultilinearOn D E (sepC1Tuples D E n) (L n hn) := by
    intro n hn i g g' hagree
    refine ⟨fun hAdd => ?_, fun a hScale => ?_⟩
    · refine tendsto_nhds_unique (hL n hn ⟨_, hAdd⟩)
        (Tendsto.congr' ?_ ((hL n hn g).add (hL n hn g')))
      filter_upwards [eventually_mem_sepC1TuplesInBall hDom Ψ hJ hn g.2,
        eventually_mem_sepC1TuplesInBall hDom Ψ hJ hn g'.2,
        eventually_mem_sepC1TuplesInBall hDom Ψ hJ hn hAdd] with k h₁ h₂ h₃
      have hk := (Ψ.multilinear (enumIndex hJ k) n hn i ⟨g.1, h₁⟩ ⟨g'.1, h₂⟩ hagree).1 h₃
      change enumValues Ψ hJ n hn g.1 k + enumValues Ψ hJ n hn g'.1 k =
        enumValues Ψ hJ n hn (Function.update g.1 i (g.1 i + g'.1 i)) k
      rw [enumValues_of_mem Ψ hJ hn h₁, enumValues_of_mem Ψ hJ hn h₂, enumValues_of_mem Ψ hJ hn h₃]
      exact hk.symm
    · refine tendsto_nhds_unique (hL n hn ⟨_, hScale⟩)
        (Tendsto.congr' ?_ ((hL n hn g).const_mul a))
      filter_upwards [eventually_mem_sepC1TuplesInBall hDom Ψ hJ hn g.2,
        eventually_mem_sepC1TuplesInBall hDom Ψ hJ hn hScale] with k h₁ h₃
      have hk := (Ψ.multilinear (enumIndex hJ k) n hn i ⟨g.1, h₁⟩ ⟨g.1, h₁⟩
        (fun _ _ => rfl)).2 a h₃
      change a * enumValues Ψ hJ n hn g.1 k =
        enumValues Ψ hJ n hn (Function.update g.1 i (a • g.1 i)) k
      rw [enumValues_of_mem Ψ hJ hn h₁, enumValues_of_mem Ψ hJ hn h₃]
      exact hk.symm
  have hsymm : ∀ n (hn : 2 ≤ n),
      IsPermSymmetricOn D E (sepC1Tuples D E n) (L n hn) := by
    intro n hn f σ hPerm
    refine tendsto_nhds_unique (hL n hn ⟨_, hPerm⟩) (Tendsto.congr' ?_ (hL n hn f))
    filter_upwards [eventually_mem_sepC1TuplesInBall hDom Ψ hJ hn f.2,
      eventually_mem_sepC1TuplesInBall hDom Ψ hJ hn hPerm] with k h₁ h₂
    have hk := Ψ.symmetric (enumIndex hJ k) n hn ⟨f.1, h₁⟩ σ h₂
    change enumValues Ψ hJ n hn f.1 k = enumValues Ψ hJ n hn (permuteComponents D E f.1 σ) k
    rw [enumValues_of_mem Ψ hJ hn h₁, enumValues_of_mem Ψ hJ hn h₂]
    exact hk.symm
  refine ⟨hdef, ⟨L, hmult, hsymm⟩, ?_, ?_⟩
  · intro n hn f
    obtain ⟨m, hm⟩ := hDom J₀ ρ Ψ.toC1FormSeq n hn f.1 f.2
    refine ⟨m, fun j => hm ⟨j.1, hJ j.2.1⟩ j.2.2, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hL n hn f) ε hε
    refine ⟨(((DiagonalLimits.enumerate J N).1 : ℕ+) : ℕ), fun j hj hle hj' => ?_⟩
    obtain ⟨k, hk⟩ := DiagonalLimits.exists_enumerate_eq J ⟨j, hj⟩
    have hval : (((DiagonalLimits.enumerate J k).1 : ℕ+) : ℕ) = ((j : ℕ+) : ℕ) := by rw [hk]
    have hNk : N ≤ k := by
      refine (DiagonalLimits.enumerate_strictMono J).le_iff_le.mp ?_
      change (((DiagonalLimits.enumerate J N).1 : ℕ+) : ℕ) ≤
        (((DiagonalLimits.enumerate J k).1 : ℕ+) : ℕ)
      rw [hval]
      exact_mod_cast hle
    have hdist := hN k hNk
    rw [Real.dist_eq] at hdist
    have hin := hm ⟨j, hJ hj⟩ hj'.2
    have hidx : enumIndex hJ k = ⟨j, hJ hj⟩ := Subtype.ext
      (show (DiagonalLimits.enumerate J k).1 = j from congrArg Subtype.val hk)
    have heq : enumValues Ψ hJ n hn f.1 k = Ψ.func ⟨j, hJ hj⟩ n hn ⟨f.1, hin⟩ := by
      unfold enumValues
      rw [hidx]
      exact evalOrZero_of_mem Ψ hn hin
    change ‖((Ψ.func ⟨j, hJ hj⟩ n hn ⟨f.1, hin⟩ : ℝ) : ℂ) - ((L n hn f : ℝ) : ℂ)‖ < ε
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← heq]
    exact hdist
  · change Hierarchy.IsBoundedBy _ C
    intro n hn d R hd hR f hLip
    have hlimAbs : Tendsto (fun k => ENNReal.ofReal |enumValues Ψ hJ n hn f.1 k|) atTop
        (𝓝 (ENNReal.ofReal |L n hn f|)) :=
      (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_abs.tendsto _).comp (hL n hn f))
    refine le_of_tendsto hlimAbs ?_
    filter_upwards [eventually_mem_sepC1TuplesInBall hDom Ψ hJ hn f.2,
      eventually_ge_enumerate J (Ψ.threshold n hn R hR)] with k h₁ h₂
    rw [enumValues_of_mem Ψ hJ hn h₁]
    exact Ψ.boundedFrom n hn R hR (enumIndex hJ k) h₂ d hd ⟨f.1, h₁⟩ hLip
theorem statement_holds (hUnif : UniformC1Bounds)
    (hFam : DiagonalLimits.FamilyApproximation.Statement)
    (hBasics : SeparatedTupleFacts.SeparatedTupleBasics)
    (hConst : EffectiveConstantFacts.Claim)
    (hKinds : C1FormSeqKinds.Statement) : Statement := by
  intro D E θ P F C
  have hClose := approximantValuesClose_of hUnif hFam hConst D E θ P F C
  exact ⟨hClose, oneIsGoodThreshold_of D E θ C,
    familyLimitsExtend_of hFam hBasics D E θ P F C (hKinds D θ E C).1 hClose⟩
end YangMills.Construction.PeriodicSpace.SeparatedExtension

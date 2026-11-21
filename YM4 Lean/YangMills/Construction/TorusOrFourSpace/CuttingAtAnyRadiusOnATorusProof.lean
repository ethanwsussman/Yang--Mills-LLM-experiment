import YangMills.Construction.TorusOrFourSpace.ClassC1FunctionsProductsAndNeighbourhoods
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNorm
import YangMills.Construction.TorusOrFourSpace.CuttingAtAnyRadiusOnATorus
import YangMills.Construction.TorusOrFourSpace.FinitePartitionsOfUnityAtAGivenScale
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import Mathlib
set_option autoImplicit false
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.CutAtRadius
variable (P : Params)
private theorem isClosedQ_supportQ (hQ : QuotientCompactC1.Claim)
    (f : Pt P torus → ℝ) : IsClosedQ P torus (supportQ P torus f) := by
  have tri := (hQ P torus).1.2.2.2.1
  intro x hx
  have hx' : ¬ ∀ r : ℝ, 0 < r → ∃ y ∈ {y | f y ≠ 0}, quotDist P torus x y < r := hx
  push Not at hx'
  obtain ⟨r, hr, hfar⟩ := hx'
  refine ⟨r / 2, by positivity, fun y hy hyc => ?_⟩
  obtain ⟨z, hz, hyz⟩ := hyc (r / 2) (by positivity)
  have h1 := hfar z hz
  have h2 := tri x y z
  linarith
private theorem cutting_member_regular (hQ : QuotientCompactC1.Claim)
    (hE : C1ProductsAndThickenings.Statement)
    (hC : VectorClasses.Claim)
    {A : Type} [Fintype A] {R : ℝ} {χ : A → Pt P torus → ℝ}
    (hχ : IsCuttingFamily P R χ) (a : A) :
    IsC1Fn P torus (χ a) ∧ IsCompactQ P torus (supportQ P torus (χ a)) ∧
      IsLipschitzQ P torus (χ a) := by
  have hsm : ContDiff ℝ ∞ (χ a ∘ torus.quotMap P) := (hχ.mem_unitInterval a).1
  have h1' : ContDiff ℝ 1 (χ a ∘ torus.quotMap P) := hsm.of_le (by exact_mod_cast le_top)
  have h1 : IsC1Fn P torus (χ a) := h1'
  obtain ⟨S, hS, hsub⟩ := hχ.support_subset_ball a
  have hc := (hC P torus).2.2 (supportQ P torus (χ a)) ⟨S, R, hS, hsub⟩
  have hcomp := hc.1 _ (isClosedQ_supportQ P hQ (χ a)) subset_rfl
  exact ⟨h1, hcomp, ((hE P torus).1.1 (χ a) h1 hcomp).2.1⟩
private theorem lipConstQ_nonneg (f : Pt P torus → ℝ) :
    0 ≤ lipConstQ P torus f :=
  Real.sInf_nonneg fun _ hL => hL.1
private theorem one_le_cutting_term (f : Pt P torus → ℝ) :
    1 ≤ 1 + 40 * P.M * lipConstQ P torus f := by
  have h1 := P.one_le_M
  have h2 := lipConstQ_nonneg P f
  have : 0 ≤ 40 * P.M * lipConstQ P torus f := by positivity
  linarith
private theorem one_le_cuttingTheta {A : Type} [Fintype A] {R : ℝ} {χ : A → Pt P torus → ℝ}
    (hχ : IsCuttingFamily P R χ) : 1 ≤ cuttingTheta P χ := by
  rcases isEmpty_or_nonempty A with hA | ⟨⟨a⟩⟩
  · have := hχ.sum_eq_one 0
    simp at this
  · calc (1 : ℝ) ≤ 1 + 40 * P.M * lipConstQ P torus (χ a) := one_le_cutting_term P _
      _ ≤ cuttingTheta P χ :=
        Finset.single_le_sum (f := fun a => 1 + 40 * P.M * lipConstQ P torus (χ a))
          (fun b _ => zero_le_one.trans (one_le_cutting_term P (χ b))) (Finset.mem_univ a)
private theorem isSpacedBallTuple_iff (hE : C1ProductsAndThickenings.Statement) (n : ℕ)
    (hn : 2 ≤ n) (d R : ℝ) (g : FnTuple P torus n) :
    IsSpacedBallTuple P n d R g ↔
      g ∈ sepC1Tuples P torus n ∩ lipTuplesSpacedInBalls P torus n d R := by
  constructor
  · rintro ⟨hg, hs, hb⟩
    have hl := (hE P torus).1.2.2 n (by omega) hg
    exact ⟨hg, hl.1, hb, fun i k hik =>
      hs.trans (iInf_le_of_le i (iInf_le_of_le k (iInf_le _ hik)))⟩
  · rintro ⟨hg, _, hb, hs⟩
    exact ⟨hg, le_iInf fun i => le_iInf fun k => le_iInf fun hik => hs i k hik, hb⟩
private theorem setInfDist_antitone {S S' T T' : Set (Pt P torus)} (h : T ⊆ S) (h' : T' ⊆ S') :
    setInfDist P torus S S' ≤ setInfDist P torus T T' :=
  le_iInf₂ fun z hz => le_iInf₂ fun z' hz' =>
    iInf₂_le_of_le z (h hz) (iInf₂_le_of_le z' (h' hz') le_rfl)
private theorem mem_sepC1Tuples_of_disjoint {n : ℕ} {S : Fin n → Set (Pt P torus)}
    (hdisj : ∀ i k, i ≠ k → Disjoint (S i) (S k)) {g : FnTuple P torus n}
    (hg : ∀ i, g i ∈ c1SupportedIn P torus (S i)) : g ∈ sepC1Tuples P torus n :=
  ⟨fun i => (hg i).1, fun i => (hg i).2.1, fun i k hik =>
    (hdisj i k hik).mono (hg i).2.2 (hg k).2.2⟩
private def multilinearOnDisjointClasses {n : ℕ} (S : Fin n → Set (Pt P torus))
    (hdisj : ∀ i k, i ≠ k → Disjoint (S i) (S k))
    (W : Fin n → Submodule ℝ (Pt P torus → ℝ))
    (hW : ∀ i, (W i : Set (Pt P torus → ℝ)) = c1SupportedIn P torus (S i))
    (Ψ : sepC1Tuples P torus n → ℝ)
    (hΨ : IsMultilinearOn P torus (sepC1Tuples P torus n) Ψ) :
    MultilinearMap ℝ (fun i => W i) ℝ :=
  have hmem : ∀ v : (i : Fin n) → W i, (fun i => (v i).1) ∈ sepC1Tuples P torus n :=
    fun v => mem_sepC1Tuples_of_disjoint P hdisj fun i => by
      rw [← hW i]
      exact (v i).2
  { toFun := fun v => Ψ ⟨fun i => (v i).1, hmem v⟩
    map_update_add' := by
      intro inst v i x y
      obtain rfl : inst = (fun a b => instDecidableEqFin n a b) := Subsingleton.elim _ _
      have e : (fun l => (Function.update v i (x + y) l).1) =
          Function.update (fun l => (Function.update v i x l).1) i
            ((Function.update v i x i).1 + (Function.update v i y i).1) := by
        funext l
        by_cases hl : l = i
        · subst hl
          simp
        · simp [hl]
      have H := (hΨ i ⟨_, hmem (Function.update v i x)⟩ ⟨_, hmem (Function.update v i y)⟩
        (fun l hl => by simp [hl])).1 (e ▸ hmem (Function.update v i (x + y)))
      rw [← H]
      exact congrArg Ψ (Subtype.ext e)
    map_update_smul' := by
      intro inst v i α x
      obtain rfl : inst = (fun a b => instDecidableEqFin n a b) := Subsingleton.elim _ _
      have e : (fun l => (Function.update v i (α • x) l).1) =
          Function.update (fun l => (Function.update v i x l).1) i
            (α • (Function.update v i x i).1) := by
        funext l
        by_cases hl : l = i
        · subst hl
          simp
        · simp [hl]
      have H := (hΨ i ⟨_, hmem (Function.update v i x)⟩ ⟨_, hmem (Function.update v i x)⟩
        (fun _ _ => rfl)).2 α (e ▸ hmem (Function.update v i (α • x)))
      rw [smul_eq_mul, ← H]
      exact congrArg Ψ (Subtype.ext e) }
private theorem cutting_bound (hQ : QuotientCompactC1.Claim)
    (hE : C1ProductsAndThickenings.Statement)
    (hC : VectorClasses.Claim)
    {A : Type} [Fintype A] {R : ℝ} {χ : A → Pt P torus → ℝ}
    (hχ : IsCuttingFamily P R χ) (n : ℕ) (d c : ℝ)
    (Ψ : sepC1Tuples P torus n → ℝ)
    (hΨ : IsMultilinearOn P torus (sepC1Tuples P torus n) Ψ)
    (hbd : ∀ g : sepC1Tuples P torus n, IsSpacedBallTuple P n d R g.1 →
      ENNReal.ofReal |Ψ g| ≤ ENNReal.ofReal c * ∏ i, sharpNormQ P torus (g.1 i))
    (h : sepC1Tuples P torus n) (hsep : ENNReal.ofReal d ≤ supportGap P torus h.1) :
    ENNReal.ofReal |Ψ h| ≤
      ENNReal.ofReal (cuttingTheta P χ ^ n * c) * ∏ i, sharpNormQ P torus (h.1 i) := by
  classical
  set S : Fin n → Set (Pt P torus) := fun i => supportQ P torus (h.1 i) with hSdef
  have hdisj : ∀ i k, i ≠ k → Disjoint (S i) (S k) := h.2.2.2
  have hdist : ∀ i k, i ≠ k → ENNReal.ofReal d ≤ setInfDist P torus (S i) (S k) :=
    fun i k hik => hsep.trans (iInf_le_of_le i (iInf_le_of_le k (iInf_le _ hik)))
  have hWex := fun i => ((hC P torus).1 (S i)).2.1
  choose W hW using hWex
  have hh : ∀ i, h.1 i ∈ c1SupportedIn P torus (S i) :=
    fun i => ⟨h.2.1 i, h.2.2.1 i, subset_rfl⟩
  have hpiece : ∀ (a : A) (i : Fin n),
      χ a * h.1 i ∈ c1SupportedIn P torus (S i ∩ supportQ P torus (χ a)) ∧
      sharpNormQ P torus (χ a * h.1 i) ≤
        ENNReal.ofReal (1 + 40 * P.M * lipConstQ P torus (χ a)) *
          sharpNormQ P torus (h.1 i) := by
    intro a i
    obtain ⟨h1, -, hl⟩ := cutting_member_regular P hQ hE hC hχ a
    have hp := (hE P torus).2.1 (χ a) (hχ.mem_unitInterval a).2 hl (S i) (h.1 i)
      ((hE P torus).1.2.1 (S i) (hh i))
    exact ⟨hp.2.2 h1 (hh i), hp.2.1⟩
  have hpS : ∀ (a : A) (i : Fin n), χ a * h.1 i ∈ c1SupportedIn P torus (S i) := fun a i =>
    ⟨(hpiece a i).1.1, (hpiece a i).1.2.1, (hpiece a i).1.2.2.trans Set.inter_subset_left⟩
  let p : (i : Fin n) → A → W i := fun i a => ⟨χ a * h.1 i, by
    have : χ a * h.1 i ∈ (W i : Set (Pt P torus → ℝ)) := by
      rw [hW i]
      exact hpS a i
    exact this⟩
  let v : (i : Fin n) → W i := fun i => ⟨h.1 i, by
    have : h.1 i ∈ (W i : Set (Pt P torus → ℝ)) := by
      rw [hW i]
      exact hh i
    exact this⟩
  have hv : ∀ i, v i = ∑ a, p i a := by
    intro i
    apply Subtype.ext
    rw [Submodule.coe_sum]
    funext y
    simp only [v, p, Finset.sum_apply, Pi.mul_apply]
    rw [← Finset.sum_mul, hχ.sum_eq_one y, one_mul]
  let F := multilinearOnDisjointClasses P S hdisj W hW Ψ hΨ
  have hFh : F v = Ψ h := rfl
  have hexp : Ψ h = ∑ r : Fin n → A, F fun i => p i (r i) := by
    rw [← hFh, ← F.map_sum p]
    exact congrArg F (funext hv)
  have hone : ∀ r : Fin n → A, ENNReal.ofReal |F fun i => p i (r i)| ≤
      ENNReal.ofReal c * ∏ i, sharpNormQ P torus (χ (r i) * h.1 i) := by
    intro r
    have hg : (fun i => χ (r i) * h.1 i) ∈ sepC1Tuples P torus n :=
      mem_sepC1Tuples_of_disjoint P hdisj fun i => hpS (r i) i
    refine hbd ⟨_, hg⟩ ⟨hg, ?_, fun i => ?_⟩
    · refine le_iInf fun i => le_iInf fun k => le_iInf fun hik => ?_
      exact (hdist i k hik).trans (setInfDist_antitone P (hpS (r i) i).2.2 (hpS (r k) k).2.2)
    · obtain ⟨B, hB, hsub⟩ := hχ.support_subset_ball (r i)
      exact ⟨B, hB, (hpiece (r i) i).1.2.2.trans (Set.inter_subset_right.trans hsub)⟩
  have hΘ0 : 0 ≤ cuttingTheta P χ := zero_le_one.trans (one_le_cuttingTheta P hχ)
  have hsum : ∀ i, ∑ a, sharpNormQ P torus (χ a * h.1 i) ≤
      ENNReal.ofReal (cuttingTheta P χ) * sharpNormQ P torus (h.1 i) := by
    intro i
    calc ∑ a, sharpNormQ P torus (χ a * h.1 i)
        ≤ ∑ a, ENNReal.ofReal (1 + 40 * P.M * lipConstQ P torus (χ a)) *
            sharpNormQ P torus (h.1 i) := Finset.sum_le_sum fun a _ => (hpiece a i).2
      _ = ENNReal.ofReal (cuttingTheta P χ) * sharpNormQ P torus (h.1 i) := by
        rw [← Finset.sum_mul, cuttingTheta, ENNReal.ofReal_sum_of_nonneg]
        exact fun b _ => zero_le_one.trans (one_le_cutting_term P (χ b))
  calc ENNReal.ofReal |Ψ h|
      ≤ ENNReal.ofReal (∑ r : Fin n → A, |F fun i => p i (r i)|) := by
        rw [hexp]
        exact ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ r : Fin n → A, ENNReal.ofReal |F fun i => p i (r i)| :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _
    _ ≤ ∑ r : Fin n → A, ENNReal.ofReal c * ∏ i, sharpNormQ P torus (χ (r i) * h.1 i) :=
        Finset.sum_le_sum fun r _ => hone r
    _ = ENNReal.ofReal c * ∏ i, ∑ a, sharpNormQ P torus (χ a * h.1 i) := by
        rw [← Finset.mul_sum, Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ ≤ ENNReal.ofReal c *
          ∏ i, (ENNReal.ofReal (cuttingTheta P χ) * sharpNormQ P torus (h.1 i)) := by
        gcongr with i
        exact hsum i
    _ = ENNReal.ofReal (cuttingTheta P χ ^ n * c) * ∏ i, sharpNormQ P torus (h.1 i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ENNReal.ofReal_mul (pow_nonneg hΘ0 n), ENNReal.ofReal_pow hΘ0]
        ring
theorem torusCutAtAnyRadius_holds (hQ : QuotientCompactC1.Claim)
    (hE : C1ProductsAndThickenings.Statement)
    (hC : VectorClasses.Claim)
    (hU : SmallScalePartitionsOfUnity) : TorusCutAtAnyRadius := by
  intro P R hR
  refine ⟨?_, ?_⟩
  · obtain ⟨N, -, θ, hθ, hθc, hθd, hθs⟩ := hU P torus Set.univ (hQ P torus).2.2.1 R hR
    refine ⟨Fin N, inferInstance, θ, ⟨hθ, fun y => hθs y (Set.mem_univ y), fun k => ?_⟩⟩
    exact (hE P torus).2.2.2 _ (hθc k) R hR (hθd k).le
  · intro A _ χ hχ
    refine ⟨fun a => (cutting_member_regular P hQ hE hC hχ a).2.2, one_le_cuttingTheta P hχ, ?_⟩
    intro n hn d _
    refine ⟨fun _ g => isSpacedBallTuple_iff P hE n hn d R g, ?_⟩
    intro c _ Ψ hΨ hbd h hsep
    exact cutting_bound P hQ hE hC hχ n d c Ψ hΨ hbd h hsep
end YangMills.Construction.PeriodicSpace.Kind.CutAtRadius

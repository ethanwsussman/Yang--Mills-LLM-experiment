import YangMills.Construction.ClusterExpansionOfAStep.BasesExist
import YangMills.Construction.ClusterExpansionOfAStep.LocalityOfTheKernel
import YangMills.Construction.FormsOnATorus.ChainMeansOfFarFunctionsSplit
import YangMills.Construction.HoleBesideASecondHole.CarriedSitesAndPaths
import YangMills.Construction.ResponseInTheExpansion.ElementsOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepCosts BlockAverages FrameTransfer LumpContours
section Coordinates
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
  (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
private def piJoin (p : ι → Prop) [DecidablePred p] (a : ∀ i : {i // p i}, X i) (b : ∀ i : {i // ¬ p i}, X i) : ∀ i, X i :=
  (MeasurableEquiv.piEquivPiSubtypeProd X p).symm (a, b)
private theorem lintegral_eq_prod_piJoin (p : ι → Prop) [DecidablePred p] {h : (∀ i, X i) → ENNReal} (hh : Measurable h) :
    ∫⁻ v, h v ∂(Measure.pi ν) =
      ∫⁻ z, h (piJoin p z.1 z.2) ∂((Measure.pi fun i : {i // p i} => ν i).prod
        (Measure.pi fun i : {i // ¬ p i} => ν i)) := by
  have hmp := (measurePreserving_piEquivPiSubtypeProd ν p).symm
  exact (hmp.lintegral_comp hh).symm
private theorem piJoin_apply_of_mem (p : ι → Prop) [DecidablePred p] (a : ∀ i : {i // p i}, X i) (b : ∀ i : {i // ¬ p i}, X i)
    {i : ι} (hi : p i) : piJoin p a b i = a ⟨i, hi⟩ := by
  simp [piJoin, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
private theorem piJoin_apply_of_not (p : ι → Prop) [DecidablePred p] (a : ∀ i : {i // p i}, X i) (b : ∀ i : {i // ¬ p i}, X i)
    {i : ι} (hi : ¬ p i) : piJoin p a b i = b ⟨i, hi⟩ := by
  simp [piJoin, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
private theorem measurable_piJoin (p : ι → Prop) [DecidablePred p] :
    Measurable fun z : (∀ i : {i // p i}, X i) × (∀ i : {i // ¬ p i}, X i) => piJoin p z.1 z.2 :=
  (MeasurableEquiv.piEquivPiSubtypeProd X p).symm.measurable
private theorem lintegral_eq_of_dependsOn (p : ι → Prop) [DecidablePred p] {f : (∀ i, X i) → ENNReal} (hf : Measurable f)
    (hS : ∀ v v', (∀ i, p i → v i = v' i) → f v = f v') (b₀ : ∀ i : {i // ¬ p i}, X i) :
    ∫⁻ v, f v ∂(Measure.pi ν) = ∫⁻ a, f (piJoin p a b₀) ∂(Measure.pi fun i : {i // p i} => ν i) := by
  rw [lintegral_eq_prod_piJoin ν p hf]
  have hm : Measurable fun a => f (piJoin p a b₀) :=
    hf.comp ((measurable_piJoin (X := X) p).comp (measurable_id.prodMk measurable_const))
  have e : ∀ z : (∀ i : {i // p i}, X i) × (∀ i : {i // ¬ p i}, X i),
      f (piJoin p z.1 z.2) = f (piJoin p z.1 b₀) := fun z =>
    hS _ _ fun i hi => by rw [piJoin_apply_of_mem p _ _ hi, piJoin_apply_of_mem p _ _ hi]
  simp only [e]
  rw [lintegral_prod (fun z : (∀ i : {i // p i}, X i) × (∀ i : {i // ¬ p i}, X i) => f (piJoin p z.1 b₀))
    (hm.comp measurable_fst).aemeasurable]
  simp
private theorem lintegral_mul_of_dependsOn_disjoint (S : Finset ι) {f g : (∀ i, X i) → ENNReal} (hf : Measurable f) (hg : Measurable g)
    (hfS : ∀ v v', (∀ i ∈ S, v i = v' i) → f v = f v') (hgS : ∀ v v', (∀ i, ¬ i ∈ S → v i = v' i) → g v = g v') :
    ∫⁻ v, f v * g v ∂(Measure.pi ν) = (∫⁻ v, f v ∂(Measure.pi ν)) * ∫⁻ v, g v ∂(Measure.pi ν) := by
  have hne : Nonempty (∀ i, X i) := ⟨fun i => (nonempty_of_isProbabilityMeasure (ν i)).some⟩
  obtain ⟨v₀⟩ := hne
  let p : ι → Prop := (· ∈ S)
  set a₀ : ∀ i : {i // p i}, X i := fun i => v₀ i with ha₀
  set b₀ : ∀ i : {i // ¬ p i}, X i := fun i => v₀ i with hb₀
  have hm1 : Measurable fun a => f (piJoin p a b₀) :=
    hf.comp ((measurable_piJoin (X := X) p).comp (measurable_id.prodMk measurable_const))
  have hm2 : Measurable fun b => g (piJoin p a₀ b) :=
    hg.comp ((measurable_piJoin (X := X) p).comp (measurable_const.prodMk measurable_id))
  rw [lintegral_eq_prod_piJoin ν p (h := fun v => f v * g v) (hf.mul hg), lintegral_eq_of_dependsOn ν p hf hfS b₀]
  have e : ∀ z : (∀ i : {i // p i}, X i) × (∀ i : {i // ¬ p i}, X i),
      f (piJoin p z.1 z.2) * g (piJoin p z.1 z.2) = f (piJoin p z.1 b₀) * g (piJoin p a₀ z.2) := fun z => by
    congr 1
    · exact hfS _ _ fun i hi => by rw [piJoin_apply_of_mem p _ _ hi, piJoin_apply_of_mem p _ _ hi]
    · exact hgS _ _ fun i hi => by rw [piJoin_apply_of_not p _ _ hi, piJoin_apply_of_not p _ _ hi]
  simp only [e]
  rw [lintegral_prod_mul hm1.aemeasurable hm2.aemeasurable]
  congr 1
  have h2 := lintegral_eq_prod_piJoin ν p hg
  have e2 : ∀ z : (∀ i : {i // p i}, X i) × (∀ i : {i // ¬ p i}, X i),
      g (piJoin p z.1 z.2) = g (piJoin p a₀ z.2) := fun z =>
    hgS _ _ fun i hi => by rw [piJoin_apply_of_not p _ _ hi, piJoin_apply_of_not p _ _ hi]
  simp only [e2] at h2
  rw [h2, lintegral_prod (fun z : (∀ i : {i // p i}, X i) × (∀ i : {i // ¬ p i}, X i) => g (piJoin p a₀ z.2))
    (hm2.comp measurable_snd).aemeasurable]
  simp
private theorem lintegral_finset_prod_of_dependsOn_disjoint {κ : Type} [DecidableEq κ] (J : Finset κ) (S : κ → Finset ι)
    (hdis : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → Disjoint (S j) (S j')) (f : κ → (∀ i, X i) → ENNReal)
    (hf : ∀ j ∈ J, Measurable (f j)) (hS : ∀ j ∈ J, ∀ v v', (∀ i ∈ S j, v i = v' i) → f j v = f j v') :
    ∫⁻ v, ∏ j ∈ J, f j v ∂(Measure.pi ν) = ∏ j ∈ J, ∫⁻ v, f j v ∂(Measure.pi ν) := by
  induction J using Finset.induction_on with
  | empty => simp
  | insert j J hj ih =>
    have hfJ : Measurable fun v => ∏ j' ∈ J, f j' v :=
      Finset.measurable_prod _ fun j' h => hf j' (Finset.mem_insert_of_mem h)
    simp only [Finset.prod_insert hj]
    rw [lintegral_mul_of_dependsOn_disjoint ν (S j) (hf j (Finset.mem_insert_self _ _)) hfJ
      (hS j (Finset.mem_insert_self _ _)) ?_]
    · rw [ih (fun a ha b hb => hdis a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb))
        (fun a ha => hf a (Finset.mem_insert_of_mem ha)) (fun a ha => hS a (Finset.mem_insert_of_mem ha))]
    · intro v v' h
      refine Finset.prod_congr rfl fun j' hj' => hS j' (Finset.mem_insert_of_mem hj') _ _ fun i hi => h i ?_
      have hne : j ≠ j' := fun e => hj (e ▸ hj')
      exact Finset.disjoint_right.mp (hdis j (Finset.mem_insert_self _ _) j' (Finset.mem_insert_of_mem hj') hne) hi
private theorem lintegral_density_mul_of_dependsOn (ρ : ∀ i, X i → ENNReal) (hρ : ∀ i, Measurable (ρ i)) (h1 : ∀ i, ∫⁻ w, ρ i w ∂(ν i) = 1)
    (S : Finset ι) {f : (∀ i, X i) → ENNReal} (hf : Measurable f) (hS : ∀ v v', (∀ i ∈ S, v i = v' i) → f v = f v') :
    ∫⁻ v, (∏ i, ρ i (v i)) * f v ∂(Measure.pi ν) = ∫⁻ v, (∏ i ∈ S, ρ i (v i)) * f v ∂(Measure.pi ν) := by
  have hm : ∀ i, Measurable fun v : ∀ i, X i => ρ i (v i) := fun i => (hρ i).comp (measurable_pi_apply i)
  have hA : Measurable fun v : ∀ i, X i => (∏ i ∈ S, ρ i (v i)) * f v :=
    (Finset.measurable_prod _ fun i _ => hm i).mul hf
  have hB : Measurable fun v : ∀ i, X i => ∏ i ∈ Sᶜ, ρ i (v i) := Finset.measurable_prod _ fun i _ => hm i
  have e : ∀ v : ∀ i, X i, (∏ i, ρ i (v i)) * f v = ((∏ i ∈ S, ρ i (v i)) * f v) * ∏ i ∈ Sᶜ, ρ i (v i) := fun v => by
    rw [← Finset.prod_mul_prod_compl S]
    ring
  simp only [e]
  rw [lintegral_mul_of_dependsOn_disjoint ν S hA hB ?_ ?_]
  · have hone : ∫⁻ v, ∏ i ∈ Sᶜ, ρ i (v i) ∂(Measure.pi ν) = 1 := by
      rw [lintegral_finset_prod_of_dependsOn_disjoint ν Sᶜ (fun i => {i}) ?_ (fun i v => ρ i (v i)) (fun i _ => hm i) ?_]
      · refine Finset.prod_eq_one fun i _ => ?_
        have hmp := measurePreserving_eval ν i
        have h2 := hmp.lintegral_comp (hρ i)
        exact h2.trans (h1 i)
      · intro a _ b _ hab
        simpa using hab
      · intro j _ v v' h
        rw [h j (Finset.mem_singleton_self _)]
    rw [hone, mul_one]
  · intro v v' h
    rw [hS v v' h, Finset.prod_congr rfl fun i hi => by rw [h i hi]]
  · intro v v' h
    exact Finset.prod_congr rfl fun i hi => by rw [h i (Finset.mem_compl.mp hi)]
end Coordinates
section Finite
variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
private def uniformMean {α : Type} (P : Finset α) (g : α → ENNReal) : ENNReal := (P.card : ENNReal)⁻¹ * ∑ b ∈ P, g b
private def uniformFinsetMeasure [MeasurableSpace Z] (B : Finset Z) : Measure Z := (B.card : ENNReal)⁻¹ • ∑ z ∈ B, Measure.dirac z
private theorem isProbabilityMeasure_uniformFinsetMeasure [MeasurableSpace Z] {B : Finset Z} (hB : B.Nonempty) :
    IsProbabilityMeasure (uniformFinsetMeasure B) := by
  constructor
  have hc : (B.card : ENNReal) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hB).ne'
  simp only [uniformFinsetMeasure, Measure.smul_apply, Measure.finset_sum_apply, measure_univ, Finset.sum_const, smul_eq_mul,
    nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel hc (ENNReal.natCast_ne_top _)
private theorem uniformFinsetMeasure_singleton [MeasurableSpace Z] [MeasurableSingletonClass Z] (B : Finset Z) (z : Z) :
    uniformFinsetMeasure B {z} = if z ∈ B then (B.card : ENNReal)⁻¹ else 0 := by
  simp only [uniformFinsetMeasure, Measure.smul_apply, Measure.finset_sum_apply, smul_eq_mul]
  have h : ∀ w ∈ B, (Measure.dirac w) ({z} : Set Z) = if w = z then 1 else 0 := by
    intro w _
    rw [Measure.dirac_apply' _ (measurableSet_singleton z)]
    by_cases hw : w = z
    · simp [hw]
    · simp [hw]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' B z]
  split_ifs <;> simp
private theorem inv_natCast_prod {A : Type} (s : Finset A) (c : A → ℕ) (hc : ∀ a ∈ s, c a ≠ 0) :
    (((∏ a ∈ s, c a : ℕ) : ENNReal))⁻¹ = ∏ a ∈ s, ((c a : ENNReal))⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _)), ih fun b hb => hc b (Finset.mem_insert_of_mem hb)]
private theorem lintegral_pi_uniform [MeasurableSpace Z] [MeasurableSingletonClass Z] (Bs : Y → Finset Z)
    (hne : ∀ y, (Bs y).Nonempty) (f : (Y → Z) → ENNReal) :
    haveI := fun y => isProbabilityMeasure_uniformFinsetMeasure (hne y)
    ∫⁻ b, f b ∂(Measure.pi fun y => uniformFinsetMeasure (Bs y)) = uniformMean (Fintype.piFinset Bs) f := by
  haveI := fun y => isProbabilityMeasure_uniformFinsetMeasure (hne y)
  rw [lintegral_fintype]
  have hs : ∀ b : Y → Z, (Measure.pi fun y => uniformFinsetMeasure (Bs y)) {b} =
      if b ∈ Fintype.piFinset Bs then ((Fintype.piFinset Bs).card : ENNReal)⁻¹ else 0 := by
    intro b
    rw [Measure.pi_singleton]
    simp only [uniformFinsetMeasure_singleton]
    by_cases hb : b ∈ Fintype.piFinset Bs
    · rw [if_pos hb, Fintype.card_piFinset, inv_natCast_prod _ _ fun y _ => (Finset.card_pos.mpr (hne y)).ne']
      exact Finset.prod_congr rfl fun y _ => if_pos (Fintype.mem_piFinset.mp hb y)
    · rw [if_neg hb]
      rw [Fintype.mem_piFinset] at hb
      push_neg at hb
      obtain ⟨y, hy⟩ := hb
      exact Finset.prod_eq_zero (Finset.mem_univ y) (if_neg hy)
  simp only [hs, mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, uniformMean, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _
private def clampTo (B : Finset Z) (z : Z) : Z :=
  open Classical in if z ∈ B then z else if h : B.Nonempty then h.choose else z
private theorem clampTo_mem {B : Finset Z} (hB : B.Nonempty) (z : Z) : clampTo B z ∈ B := by
  unfold clampTo
  split_ifs with h
  · exact h
  · exact hB.choose_spec
private theorem clampTo_of_mem {B : Finset Z} {z : Z} (h : z ∈ B) : clampTo B z = z := by
  unfold clampTo
  rw [if_pos h]
private theorem clamp_mem_piFinset {Bs : Y → Finset Z} (hne : ∀ y, (Bs y).Nonempty) (b : Y → Z) :
    (fun y => clampTo (Bs y) (b y)) ∈ Fintype.piFinset Bs :=
  Fintype.mem_piFinset.mpr fun y => clampTo_mem (hne y) _
private theorem uniformMean_clamp {Bs : Y → Finset Z} (g : (Y → Z) → ENNReal) :
    uniformMean (Fintype.piFinset Bs) (fun b => g fun y => clampTo (Bs y) (b y)) = uniformMean (Fintype.piFinset Bs) g := by
  unfold uniformMean
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  show g (fun y => clampTo (Bs y) (b y)) = g b
  congr 1
  funext y
  exact clampTo_of_mem (Fintype.mem_piFinset.mp hb y)
private theorem uniformMean_prod_of_dependsOn_disjoint {κ : Type} [DecidableEq κ] (Bs : Y → Finset Z) (hne : ∀ y, (Bs y).Nonempty) (J : Finset κ)
    (S : κ → Finset Y) (hdis : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → Disjoint (S j) (S j')) (g : κ → (Y → Z) → ENNReal)
    (hg : ∀ j ∈ J, ∀ b ∈ Fintype.piFinset Bs, ∀ b' ∈ Fintype.piFinset Bs, (∀ y ∈ S j, b y = b' y) → g j b = g j b') :
    uniformMean (Fintype.piFinset Bs) (fun b => ∏ j ∈ J, g j b) = ∏ j ∈ J, uniformMean (Fintype.piFinset Bs) (g j) := by
  letI : MeasurableSpace Z := ⊤
  haveI : MeasurableSingletonClass Z := ⟨fun _ => trivial⟩
  haveI := fun y => isProbabilityMeasure_uniformFinsetMeasure (hne y)
  have h1 : ∀ j, uniformMean (Fintype.piFinset Bs) (g j) =
      ∫⁻ b, g j (fun y => clampTo (Bs y) (b y)) ∂(Measure.pi fun y => uniformFinsetMeasure (Bs y)) := fun j => by
    rw [lintegral_pi_uniform Bs hne, uniformMean_clamp]
  have h2 : uniformMean (Fintype.piFinset Bs) (fun b => ∏ j ∈ J, g j b) =
      ∫⁻ b, ∏ j ∈ J, g j (fun y => clampTo (Bs y) (b y)) ∂(Measure.pi fun y => uniformFinsetMeasure (Bs y)) := by
    rw [lintegral_pi_uniform Bs hne]
    exact (uniformMean_clamp (fun b => ∏ j ∈ J, g j b)).symm
  rw [h2]
  simp only [h1]
  exact lintegral_finset_prod_of_dependsOn_disjoint _ J S hdis _ (fun j _ => Measurable.of_discrete) fun j hj v v' h =>
    hg j hj _ (clamp_mem_piFinset hne v) _ (clamp_mem_piFinset hne v') fun y hy => by rw [h y hy]
private theorem uniformMean_congr_of_dependsOn (Bs Bs' : Y → Finset Z) (hne : ∀ y, (Bs y).Nonempty) (hne' : ∀ y, (Bs' y).Nonempty)
    (S : Finset Y) (hS : ∀ y ∈ S, Bs y = Bs' y) (g g' : (Y → Z) → ENNReal)
    (hg : ∀ b ∈ Fintype.piFinset Bs, ∀ b' ∈ Fintype.piFinset Bs', (∀ y ∈ S, b y = b' y) → g b = g' b') :
    uniformMean (Fintype.piFinset Bs) g = uniformMean (Fintype.piFinset Bs') g' := by
  letI : MeasurableSpace Z := ⊤
  haveI : MeasurableSingletonClass Z := ⟨fun _ => trivial⟩
  haveI := fun y => isProbabilityMeasure_uniformFinsetMeasure (hne y)
  haveI := fun y => isProbabilityMeasure_uniformFinsetMeasure (hne' y)
  rw [← uniformMean_clamp g, ← uniformMean_clamp g', ← lintegral_pi_uniform Bs hne, ← lintegral_pi_uniform Bs' hne']
  have hsel : ∀ v v' : Y → Z, (∀ y ∈ S, v y = v' y) → g (fun y => clampTo (Bs y) (v y)) =
      g' (fun y => clampTo (Bs' y) (v' y)) := fun v v' h =>
    hg _ (clamp_mem_piFinset hne v) _ (clamp_mem_piFinset hne' v') fun y hy => by rw [h y hy, hS y hy]
  have hr : ∀ v v' : Y → Z, (∀ y ∈ S, v y = v' y) → g (fun y => clampTo (Bs y) (v y)) =
      g (fun y => clampTo (Bs y) (v' y)) := fun v v' h => (hsel v v' h).trans (hsel v' v' fun _ _ => rfl).symm
  have hr' : ∀ v v' : Y → Z, (∀ y ∈ S, v y = v' y) → g' (fun y => clampTo (Bs' y) (v y)) =
      g' (fun y => clampTo (Bs' y) (v' y)) := fun v v' h => (hsel v v fun _ _ => rfl).symm.trans (hsel v v' h)
  have e : (fun i : {i // i ∈ S} => uniformFinsetMeasure (Bs i.1)) = fun i : {i // i ∈ S} => uniformFinsetMeasure (Bs' i.1) :=
    funext fun i => by rw [hS i.1 i.2]
  let b₀ : ∀ i : {i // ¬ i ∈ S}, (fun _ : Y => Z) i.1 := fun i => (hne i.1).choose
  rw [lintegral_eq_of_dependsOn (fun y => uniformFinsetMeasure (Bs y)) (· ∈ S) Measurable.of_discrete (fun v v' h => hr v v' h) b₀,
    lintegral_eq_of_dependsOn (fun y => uniformFinsetMeasure (Bs' y)) (· ∈ S) Measurable.of_discrete (fun v v' h => hr' v v' h) b₀, e]
  exact lintegral_congr fun a => hsel _ _ fun _ _ => rfl
end Finite
section Step
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem intCast_cast_cast {m n : ℕ} (hm : m = n) [NeZero m] (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod n).cast : ℤ) : ZMod m) = a := by apply _root_.YangMills.Construction.WeightedResponses.intCast_cast_intCast_cast_of_eq <;> assumption
private theorem period_top (i : Fin 4) : (stepBlockFrame L n).period 1 i = n := by
  simp [BlockFrame.period, stepBlockFrame, BlockFrame.top]
private def cellEquivTorusSite : (stepBlockFrame L n).Cell ≃ TorusSite n where
  toFun := toTorusSite n
  invFun := fun z => siteOfCoords 1 fun i => ((z i).cast : ℤ)
  left_inv := fun x => by
    funext i
    exact intCast_cast_cast (period_top i) (x i)
  right_inv := fun z => by
    funext i
    have h := castInt_intCast (period_top (L := L) (n := n) i) ((z i).cast : ℤ)
    exact h.trans (ZMod.intCast_zmod_cast (z i))
end Step
section Kernel
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
private def bondDensity (ℓ : StepParameters) (x : ℝ) {n : ℕ} (W : (stepBlockFrame ℓ.side n).GaugeField 0) (b : BaseChoice ℓ.side n)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) (g : UnitQuaternion) : ℝ :=
  Real.exp (ℓ.coupling * x * (contourMean ℓ.baseDepth (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W) b W c *
      ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) /
    partitionFn (ℓ.coupling * x * ‖contourMean ℓ.baseDepth (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W) b W c‖)
private theorem bondKernel_eq_bondDensity (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0) (V : (stepBlockFrame ℓ.side n).GaugeField 1)
    (b : BaseChoice ℓ.side n) (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) :
    bondKernel ℓ x W V b c = bondDensity ℓ x W b c (V c.1 c.2) := rfl
private theorem continuous_bondDensity (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0) (b : BaseChoice ℓ.side n)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) : Continuous (bondDensity ℓ x W b c) := by
  unfold bondDensity
  refine Continuous.div_const (Real.continuous_exp.comp (continuous_const.mul ?_)) _
  refine Quaternion.continuous_re.comp (continuous_const.mul ?_)
  exact continuous_subtype_val.comp continuous_inv
private theorem integral_bondDensity (hK : BondKernelProperties) (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : BaseChoice ℓ.side n) (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) : ∫ g : UnitQuaternion, bondDensity ℓ x W b c g ∂haarUnit = 1 := by
  have h := (hK.2 ℓ x n W (fun _ _ => 1) b c).2.2
  have hw : ∀ g : UnitQuaternion, bondKernel ℓ x W (updateBond (fun _ _ => 1) c g) b c = bondDensity ℓ x W b c g := by
    intro g
    rw [bondKernel_eq_bondDensity]
    simp [updateBond]
  simpa only [hw] using h
private theorem bondDensity_pos (hK : BondKernelProperties) (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : BaseChoice ℓ.side n) (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) (g : UnitQuaternion) : 0 < bondDensity ℓ x W b c g :=
  (hK.2 ℓ x n W (fun _ _ => g) b c).1
private def siteDensity (ℓ : StepParameters) (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0) (b : BaseChoice ℓ.side n) (z : TorusSite n)
    (v : Fin 4 → UnitQuaternion) : ENNReal :=
  ∏ i, ENNReal.ofReal (bondDensity ℓ x W b (cellEquivTorusSite.symm z, i) (v i))
private theorem measurable_siteDensity (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0) (b : BaseChoice ℓ.side n) (z : TorusSite n) :
    Measurable (siteDensity ℓ x W b z) :=
  Finset.measurable_prod _ fun i _ =>
    ((continuous_bondDensity x W b _).measurable.comp (measurable_pi_apply i)).ennreal_ofReal
private theorem lintegral_siteDensity (hK : BondKernelProperties) (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0) (b : BaseChoice ℓ.side n)
    (z : TorusSite n) : ∫⁻ v, siteDensity ℓ x W b z v ∂(Measure.pi fun _ : Fin 4 => haarUnit) = 1 := by
  unfold siteDensity
  rw [lintegral_finset_prod_of_dependsOn_disjoint (fun _ : Fin 4 => haarUnit) Finset.univ (fun i => {i}) ?_
    (fun i v => ENNReal.ofReal (bondDensity ℓ x W b (cellEquivTorusSite.symm z, i) (v i)))
    (fun i _ => ((continuous_bondDensity x W b _).measurable.comp (measurable_pi_apply i)).ennreal_ofReal) ?_]
  · refine Finset.prod_eq_one fun i _ => ?_
    have hmp := measurePreserving_eval (fun _ : Fin 4 => haarUnit) i
    have hm : Measurable fun g : UnitQuaternion => ENNReal.ofReal (bondDensity ℓ x W b (cellEquivTorusSite.symm z, i) g) :=
      (continuous_bondDensity x W b _).measurable.ennreal_ofReal
    have h2 := hmp.lintegral_comp hm
    refine h2.trans ?_
    have hint : Integrable (bondDensity ℓ x W b (cellEquivTorusSite.symm z, i)) haarUnit :=
      (continuous_bondDensity x W b _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun g => (bondDensity_pos hK x W b _ g).le), integral_bondDensity hK, ENNReal.ofReal_one]
  · intro a _ c _ hac
    simpa using hac
  · intro j _ v v' h
    rw [h j (Finset.mem_singleton_self _)]
private def conditionalMean (ℓ : StepParameters) (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0) (b : BaseChoice ℓ.side n)
    (F : TorusField n → ENNReal) : ENNReal :=
  ∫⁻ V, (∏ z, siteDensity ℓ x W b z (V z)) * F V ∂(fieldHaar n)
private theorem ofReal_prod_bondKernel (hK : BondKernelProperties) (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : BaseChoice ℓ.side n) (V : TorusField n) :
    ENNReal.ofReal (∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4, bondKernel ℓ x W (coarseLevelField ℓ n V) b c) =
      ∏ z, siteDensity ℓ x W b z (V z) := by
  let e : (stepBlockFrame ℓ.side n).Cell ≃ TorusSite n := cellEquivTorusSite
  have hprod : ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4, bondKernel ℓ x W (coarseLevelField ℓ n V) b c =
      ∏ z : TorusSite n, ∏ i : Fin 4, bondDensity ℓ x W b (e.symm z, i) (V z i) := by
    rw [Fintype.prod_prod_type, ← e.symm.prod_comp (fun y => ∏ i : Fin 4,
      bondKernel ℓ x W (coarseLevelField ℓ n V) b (y, i))]
    refine Finset.prod_congr rfl fun z _ => Finset.prod_congr rfl fun i _ => ?_
    rw [bondKernel_eq_bondDensity]
    have hz : toTorusSite n (e.symm z) = z := e.apply_symm_apply z
    have hread : coarseLevelField ℓ n V (e.symm z) i = V z i := by
      show V (toTorusSite n (e.symm z)) i = _
      rw [hz]
    exact congrArg _ hread
  rw [hprod, ENNReal.ofReal_prod_of_nonneg fun z _ => Finset.prod_nonneg fun i _ => (bondDensity_pos hK x W b _ _).le]
  refine Finset.prod_congr rfl fun z _ => ?_
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => (bondDensity_pos hK x W b _ _).le]
  rfl
private theorem measurable_prod_siteDensity (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0) (b : BaseChoice ℓ.side n)
    (A : Finset (TorusSite n)) : Measurable fun V : TorusField n => ∏ z ∈ A, siteDensity ℓ x W b z (V z) :=
  Finset.measurable_prod _ fun z _ => (measurable_siteDensity x W b z).comp (measurable_pi_apply z)
private theorem stepExpectation_eq_uniformMean (hK : BondKernelProperties) (x : ℝ) {F : TorusField n → ENNReal} (hF : Measurable F)
    (W : TorusField (n * ℓ.side)) (hB : (baseChoices ℓ (fineLevelField ℓ n W)).Nonempty) :
    stepExpectation ℓ x F W =
      uniformMean (baseChoices ℓ (fineLevelField ℓ n W)) fun b => conditionalMean ℓ x (fineLevelField ℓ n W) b F := by
  unfold stepExpectation uniformMean
  have hcard : 0 < (baseChoices ℓ (fineLevelField ℓ n W)).card := Finset.card_pos.mpr hB
  have hcardR : (0 : ℝ) < ((baseChoices ℓ (fineLevelField ℓ n W)).card : ℝ) := by exact_mod_cast hcard
  have hnn : ∀ V : TorusField n, ∀ b ∈ baseChoices ℓ (fineLevelField ℓ n W),
      0 ≤ ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4, bondKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V) b c :=
    fun V b _ => Finset.prod_nonneg fun c _ => (hK.2 ℓ x n _ _ b c).1.le
  have e : ∀ V : TorusField n, ENNReal.ofReal (averagedKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V)) * F V =
      ((baseChoices ℓ (fineLevelField ℓ n W)).card : ENNReal)⁻¹ *
        ∑ b ∈ baseChoices ℓ (fineLevelField ℓ n W), (∏ z, siteDensity ℓ x (fineLevelField ℓ n W) b z (V z)) * F V := by
    intro V
    unfold averagedKernel
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (hnn V), one_div,
      ENNReal.ofReal_inv_of_pos hcardR, ENNReal.ofReal_natCast, mul_assoc, Finset.sum_mul]
    simp only [ofReal_prod_bondKernel hK]
  simp only [e]
  have hc0 : ((baseChoices ℓ (fineLevelField ℓ n W)).card : ENNReal) ≠ 0 := by exact_mod_cast hcard.ne'
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc0), lintegral_finset_sum _
    (f := fun b (V : TorusField n) => (∏ z, siteDensity ℓ x (fineLevelField ℓ n W) b z (V z)) * F V) fun b _ =>
      (measurable_prod_siteDensity x _ b Finset.univ).mul hF]
  rfl
private def DependsOnSites (A : Finset (TorusSite n)) (F : TorusField n → ENNReal) : Prop :=
  ∀ V V' : TorusField n, (∀ z ∈ A, V z = V' z) → F V = F V'
private theorem conditionalMean_eq_local (hK : BondKernelProperties) (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : BaseChoice ℓ.side n) (A : Finset (TorusSite n)) {F : TorusField n → ENNReal} (hF : Measurable F) (hA : DependsOnSites A F) :
    conditionalMean ℓ x W b F = ∫⁻ V, (∏ z ∈ A, siteDensity ℓ x W b z (V z)) * F V ∂(fieldHaar n) :=
  lintegral_density_mul_of_dependsOn (fun _ : TorusSite n => Measure.pi fun _ : Fin 4 => haarUnit) (fun z => siteDensity ℓ x W b z)
    (fun z => measurable_siteDensity x W b z) (fun z => lintegral_siteDensity hK x W b z) A hF hA
private theorem conditionalMean_prod (hK : BondKernelProperties) (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : BaseChoice ℓ.side n) {κ : Type} [Fintype κ] [DecidableEq κ] (A : κ → Finset (TorusSite n))
    (hdis : ∀ k k', k ≠ k' → Disjoint (A k) (A k'))
    {F : κ → TorusField n → ENNReal} (hF : ∀ k, Measurable (F k)) (hA : ∀ k, DependsOnSites (A k) (F k)) :
    conditionalMean ℓ x W b (fun V => ∏ k, F k V) = ∏ k, conditionalMean ℓ x W b (F k) := by
  classical
  have hU : DependsOnSites (Finset.univ.biUnion A) (fun V => ∏ k, F k V) := fun V V' h =>
    Finset.prod_congr rfl fun k _ => hA k V V' fun z hz => h z (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hz⟩)
  rw [conditionalMean_eq_local hK x W b _ (Finset.measurable_prod _ fun k _ => hF k) hU]
  have e : ∀ V : TorusField n, (∏ z ∈ Finset.univ.biUnion A, siteDensity ℓ x W b z (V z)) * ∏ k, F k V =
      ∏ k, (∏ z ∈ A k, siteDensity ℓ x W b z (V z)) * F k V := fun V => by
    rw [Finset.prod_biUnion fun k _ k' _ hk => hdis k k' hk, ← Finset.prod_mul_distrib]
  simp only [e]
  have hh : ∀ k ∈ (Finset.univ : Finset κ),
      Measurable fun V : TorusField n => (∏ z ∈ A k, siteDensity ℓ x W b z (V z)) * F k V :=
    fun k _ => (measurable_prod_siteDensity x W b (A k)).mul (hF k)
  have key := lintegral_finset_prod_of_dependsOn_disjoint (fun _ : TorusSite n => Measure.pi fun _ : Fin 4 => haarUnit)
    Finset.univ A (fun k _ k' _ hk => hdis k k' hk)
    (fun k (V : TorusField n) => (∏ z ∈ A k, siteDensity ℓ x W b z (V z)) * F k V) hh (by
      intro k _ V V' h
      show (∏ z ∈ A k, siteDensity ℓ x W b z (V z)) * F k V = (∏ z ∈ A k, siteDensity ℓ x W b z (V' z)) * F k V'
      rw [hA k V V' h, Finset.prod_congr rfl fun z hz => by rw [h z hz]])
  refine Eq.trans key ?_
  exact Finset.prod_congr rfl fun k _ => (conditionalMean_eq_local hK x W b (A k) (hF k) (hA k)).symm
private theorem conditionalMean_congr (hK : BondKernelProperties) (x : ℝ) (W W' : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b b' : BaseChoice ℓ.side n) (A : Finset (TorusSite n)) {F : TorusField n → ENNReal} (hF : Measurable F)
    (hA : DependsOnSites A F)
    (h : ∀ z ∈ A, ∀ i g, bondDensity ℓ x W b (cellEquivTorusSite.symm z, i) g =
      bondDensity ℓ x W' b' (cellEquivTorusSite.symm z, i) g) :
    conditionalMean ℓ x W b F = conditionalMean ℓ x W' b' F := by
  rw [conditionalMean_eq_local hK x W b A hF hA, conditionalMean_eq_local hK x W' b' A hF hA]
  refine lintegral_congr fun V => ?_
  have e : ∏ z ∈ A, siteDensity ℓ x W b z (V z) = ∏ z ∈ A, siteDensity ℓ x W' b' z (V z) := by
    refine Finset.prod_congr rfl fun z hz => ?_
    unfold siteDensity
    exact Finset.prod_congr rfl fun i _ => by rw [h z hz i]
  rw [e]
private theorem mem_of_mem_filter_inst {α : Type} {p : α → Prop} (inst : DecidablePred p) {s : Finset α} {a : α}
    (h : a ∈ @Finset.filter α p inst s) : a ∈ s := (Finset.mem_filter.mp h).1
private theorem exists_offset_of_mem_baseSitesAt {J₀ : ℕ} {h : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0))}
    {y : (stepBlockFrame ℓ.side n).Cell} {s : (stepBlockFrame ℓ.side n).Site 0} (hs : s ∈ baseSitesAt J₀ h y) :
    ∃ z ∈ centredCube ℓ.side, s = siteAtOffset y z := by
  classical
  unfold baseSitesAt at hs
  split_ifs at hs with hc
  · refine ⟨0, ?_, ?_⟩
    · refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_
      have hL : (1 : ℤ) ≤ ℓ.side := by
        have := NeZero.ne ℓ.side
        omega
      constructor <;> simp <;> omega
    · rw [Finset.mem_singleton.mp hs]
      funext i
      simp [siteAtOffset, siteOfCoords]
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (mem_of_mem_filter_inst _ hs)
    refine ⟨z, ?_, ?_⟩
    · simpa [stepBlockFrame, BlockFrame.top] using hz
    · funext i
      exact Int.cast_add _ _
private theorem fieldsAgreeNear_mono {W W' : TorusField (n * ℓ.side)} {c : TorusSite (n * ℓ.side)} {m m' : ℕ} (hm : m' ≤ m)
    (h : FieldsAgreeNear W W' c c m) : FieldsAgreeNear W W' c c m' := by
  intro b hb
  refine h b ⟨fun i => (hb.1 i).trans (by exact_mod_cast hm), fun i => (hb.2 i).trans (by exact_mod_cast hm)⟩
private theorem bondDensity_congr (hL : BondKernelLocality) (hfit : ℓ.Admissible)
    (hLam : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (h16 : 16 ≤ n) (x : ℝ) (W W' : TorusField (n * ℓ.side))
    (b b' : BaseChoice ℓ.side n)
    (hb : b ∈ Fintype.piFinset (baseSitesAt ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ n W))))
    (hb' : b' ∈ Fintype.piFinset (baseSitesAt ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ n W'))))
    (y : (stepBlockFrame ℓ.side n).Cell) (i : Fin 4)
    (hy : FieldsAgreeNear W W' (cellCentreOnTorus ℓ.side y) (cellCentreOnTorus ℓ.side y) (3 * ℓ.side))
    (hy' : FieldsAgreeNear W W' (cellCentreOnTorus ℓ.side (y + BlockAverages.unitStep 1 i))
      (cellCentreOnTorus ℓ.side (y + BlockAverages.unitStep 1 i)) (3 * ℓ.side))
    (e₀ : b y = b' y) (e₁ : b (y + BlockAverages.unitStep 1 i) = b' (y + BlockAverages.unitStep 1 i)) (g : UnitQuaternion) :
    bondDensity ℓ x (fineLevelField ℓ n W) b (y, i) g = bondDensity ℓ x (fineLevelField ℓ n W') b' (y, i) g := by
  obtain ⟨_, h2, _, h4⟩ := hL ℓ hfit hLam n n h16 h16 W W' y y
  have h2' := (hL ℓ hfit hLam n n h16 h16 W W' (y + BlockAverages.unitStep 1 i) (y + BlockAverages.unitStep 1 i)).2.1
  obtain ⟨z₀, hz₀, hb₀⟩ := exists_offset_of_mem_baseSitesAt (Fintype.mem_piFinset.mp hb y)
  obtain ⟨z₁, hz₁, hb₁⟩ := exists_offset_of_mem_baseSitesAt (Fintype.mem_piFinset.mp hb (y + BlockAverages.unitStep 1 i))
  have h5 := (h4 i x (fun _ _ => g) (fun _ _ => g) b b' z₀ z₁ hz₀ hz₁ hb₀ (e₀ ▸ hb₀) hb₁ (e₁ ▸ hb₁)
    (fieldsAgreeNear_mono (by omega) hy) (h2 hy) (h2' hy')).2 rfl
  exact h5
private theorem baseSitesAt_congr (hL : BondKernelLocality) (hfit : ℓ.Admissible)
    (hLam : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (h16 : 16 ≤ n) (W W' : TorusField (n * ℓ.side))
    (y : (stepBlockFrame ℓ.side n).Cell)
    (hy : FieldsAgreeNear W W' (cellCentreOnTorus ℓ.side y) (cellCentreOnTorus ℓ.side y) (3 * ℓ.side)) :
    baseSitesAt ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ n W)) y =
      baseSitesAt ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ n W')) y := by
  obtain ⟨_, h2, h3, _⟩ := hL ℓ hfit hLam n n h16 h16 W W' y y
  have h5 := (h3 (h2 hy)).2
  ext s
  constructor
  · intro hs
    obtain ⟨z, hz, rfl⟩ := exists_offset_of_mem_baseSitesAt hs
    exact (h5 z hz).mp hs
  · intro hs
    obtain ⟨z, hz, rfl⟩ := exists_offset_of_mem_baseSitesAt hs
    exact (h5 z hz).mpr hs
private theorem supDist_scale_le (a b : Fin 4 → ℤ) :
    _root_.YangMills.Construction.TorusFields.supDist (siteOfInt (fun i => (ℓ.side : ℤ) * a i) : TorusSite (n * ℓ.side)) (siteOfInt fun i => (ℓ.side : ℤ) * b i) ≤
      ℓ.side * _root_.YangMills.Construction.TorusFields.supDist (siteOfInt a : TorusSite n) (siteOfInt b) := by
  rw [_root_.YangMills.Construction.TorusFields.supDist_le_iff]
  intro i
  set d : ZMod n := (siteOfInt a : TorusSite n) i - (siteOfInt b : TorusSite n) i with hd
  have hv : ((d.valMinAbs : ℤ) : ZMod n) = d := ZMod.coe_valMinAbs d
  have hdd : d = ((a i - b i : ℤ) : ZMod n) := by
    rw [hd]
    simp [siteOfInt]
  have hdiv : (n : ℤ) ∣ (a i - b i) - d.valMinAbs := by
    have h1 : ((a i - b i : ℤ) : ZMod n) = ((d.valMinAbs : ℤ) : ZMod n) := by rw [hv, hdd]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1.symm
  obtain ⟨q, hq⟩ := hdiv
  have h2 : (siteOfInt (fun i => (ℓ.side : ℤ) * a i) : TorusSite (n * ℓ.side)) i -
      (siteOfInt fun i => (ℓ.side : ℤ) * b i) i =
      (((ℓ.side : ℤ) * d.valMinAbs : ℤ) : ZMod (n * ℓ.side)) := by
    have h3 : (ℓ.side : ℤ) * a i - (ℓ.side : ℤ) * b i =
        (ℓ.side : ℤ) * d.valMinAbs + ((n * ℓ.side : ℕ) : ℤ) * q := by
      push_cast
      linear_combination (ℓ.side : ℤ) * hq
    simp only [siteOfInt]
    rw [← Int.cast_sub, h3, Int.cast_add, Int.cast_mul ((n * ℓ.side : ℕ) : ℤ), Int.cast_natCast, ZMod.natCast_self,
      zero_mul, add_zero]
  rw [h2]
  refine (_root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le _).trans ?_
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (Finset.le_sup (f := fun i =>
    (((siteOfInt a : TorusSite n) i - (siteOfInt b : TorusSite n) i).valMinAbs).natAbs) (Finset.mem_univ i))
private theorem le_supDist_of_ne {c M : ℕ} [NeZero (c * M)] (u : Fin 4 → ℤ) {k k' : Fin 4 → Fin M} (hk : k ≠ k') :
    c ≤ _root_.YangMills.Construction.TorusFields.supDist (siteOfInt (fun i => u i + c * ((k i : ℕ) : ℤ)) : TorusSite (c * M))
      (siteOfInt fun i => u i + c * ((k' i : ℕ) : ℤ)) := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ k' i := by
    by_contra hcon
    push_neg at hcon
    exact hk (funext hcon)
  have hne : ((k i : ℕ)) ≠ ((k' i : ℕ)) := fun h => hi (Fin.ext h)
  have hc0 : c ≠ 0 := fun h => by
    have := NeZero.ne (c * M)
    simp [h] at this
  set w : ℤ := (c : ℤ) * (((k i : ℕ) : ℤ) - ((k' i : ℕ) : ℤ)) with hw
  have e : (siteOfInt (fun i => u i + c * ((k i : ℕ) : ℤ)) : TorusSite (c * M)) i -
      (siteOfInt fun i => u i + c * ((k' i : ℕ) : ℤ)) i = ((w : ℤ) : ZMod (c * M)) := by
    simp only [siteOfInt, hw]
    push_cast
    ring
  have hle : (((w : ℤ) : ZMod (c * M)).valMinAbs).natAbs ≤
      _root_.YangMills.Construction.TorusFields.supDist (siteOfInt (fun i => u i + c * ((k i : ℕ) : ℤ)) : TorusSite (c * M))
        (siteOfInt fun i => u i + c * ((k' i : ℕ) : ℤ)) := by
    rw [← e]
    exact Finset.le_sup (f := fun i => (((siteOfInt (fun i => u i + c * ((k i : ℕ) : ℤ)) : TorusSite (c * M)) i -
      (siteOfInt (fun i => u i + c * ((k' i : ℕ) : ℤ)) : TorusSite (c * M)) i).valMinAbs).natAbs) (Finset.mem_univ i)
  refine le_trans ?_ hle
  set a : ℤ := ((w : ℤ) : ZMod (c * M)).valMinAbs with ha
  have hcast : ((a : ℤ) : ZMod (c * M)) = (w : ZMod (c * M)) := ZMod.coe_valMinAbs _
  have hdvd : ((c * M : ℕ) : ℤ) ∣ w - a := (ZMod.intCast_eq_intCast_iff_dvd_sub a w (c * M)).mp hcast
  have hcd : (c : ℤ) ∣ a := by
    have h1 : (c : ℤ) ∣ w - a := dvd_trans (by push_cast; exact Dvd.intro _ rfl) hdvd
    have h2 : (c : ℤ) ∣ w := Dvd.intro _ rfl
    have := dvd_sub h2 h1
    simpa using this
  by_cases h0 : a = 0
  · exfalso
    rw [h0, sub_zero] at hdvd
    have hMd : (M : ℤ) ∣ ((k i : ℕ) : ℤ) - ((k' i : ℕ) : ℤ) := by
      have hc' : (c : ℤ) ≠ 0 := by exact_mod_cast hc0
      have : (c : ℤ) * (M : ℤ) ∣ (c : ℤ) * (((k i : ℕ) : ℤ) - ((k' i : ℕ) : ℤ)) := by
        have h3 := hdvd
        push_cast at h3
        exact h3
      exact (mul_dvd_mul_iff_left hc').mp this
    have hz : ((k i : ℕ) : ℤ) - ((k' i : ℕ) : ℤ) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd hMd ?_
      have h1 := (k i).2
      have h2 := (k' i).2
      rw [abs_lt]
      constructor <;> omega
    omega
  · obtain ⟨q, hq⟩ := hcd
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp [hq] at h0
    rw [hq, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hq0)
private theorem cellCentreOnTorus_eq (y : (stepBlockFrame ℓ.side n).Cell) :
    cellCentreOnTorus ℓ.side y = (siteOfInt fun i => (ℓ.side : ℤ) * siteCoords y i : TorusSite (n * ℓ.side)) := by
  funext i
  have h : (stepBlockFrame ℓ.side n).period 0 i = n * ℓ.side := by
    simp [BlockFrame.period, stepBlockFrame, BlockFrame.top]
  show (((ZMod.cast ((((ℓ.side : ℤ) ^ ((stepBlockFrame ℓ.side n).top - 0) * siteCoords y i : ℤ)) :
    ZMod ((stepBlockFrame ℓ.side n).period 0 i))) : ℤ) : ZMod (n * ℓ.side)) = _
  rw [cast_intCast_of_eq h]
  simp [siteOfInt, stepBlockFrame, BlockFrame.top]
private theorem siteOfInt_siteCoords (y : (stepBlockFrame ℓ.side n).Cell) :
    (siteOfInt (siteCoords y) : TorusSite n) = toTorusSite n y := rfl
private theorem fieldsAgreeNear_of_agree (W W' : TorusField (n * ℓ.side)) (w : Fin 4 → ℤ) (r : ℕ)
    (h : ∀ x, _root_.YangMills.Construction.TorusFields.supDist x (siteOfInt fun i => (ℓ.side : ℤ) * w i : TorusSite (n * ℓ.side)) ≤ ℓ.side * r + 4 * ℓ.side →
      ∀ i, W x i = W' x i)
    (y : (stepBlockFrame ℓ.side n).Cell) (hy : _root_.YangMills.Construction.TorusFields.supDist (toTorusSite n y) (siteOfInt w) ≤ r + 1) :
    FieldsAgreeNear W W' (cellCentreOnTorus ℓ.side y) (cellCentreOnTorus ℓ.side y) (3 * ℓ.side) := by
  intro b hb
  refine h _ ?_ _
  have h1 := supDist_scale_le (ℓ := ℓ) (n := n) (siteCoords y) w
  rw [← cellCentreOnTorus_eq, siteOfInt_siteCoords] at h1
  have h2 : _root_.YangMills.Construction.TorusFields.supDist (cellCentreOnTorus ℓ.side y) (cellCentreOnTorus ℓ.side y + siteOfInt b.1) ≤ 3 * ℓ.side :=
    _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => by
      have := abs_le.mp (hb.1 i)
      omega
  have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle (cellCentreOnTorus ℓ.side y + siteOfInt b.1) (cellCentreOnTorus ℓ.side y)
    (siteOfInt fun i => (ℓ.side : ℤ) * w i : TorusSite (n * ℓ.side))
  have h2' : _root_.YangMills.Construction.TorusFields.supDist (cellCentreOnTorus ℓ.side y + siteOfInt b.1) (cellCentreOnTorus ℓ.side y) ≤ 3 * ℓ.side := by
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    exact h2
  have h4 : ℓ.side * _root_.YangMills.Construction.TorusFields.supDist (toTorusSite n y) (siteOfInt w : TorusSite n) ≤ ℓ.side * (r + 1) := Nat.mul_le_mul_left _ hy
  show _root_.YangMills.Construction.TorusFields.supDist (cellCentreOnTorus ℓ.side y + siteOfInt b.1) _ ≤ _
  linarith
private theorem step_factorize (hK : BondKernelProperties) (hL : BondKernelLocality)
    (hBE : BaseChoicesNonempty) (hfit : ℓ.Admissible) (hLam : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (x : ℝ) {c M r : ℕ}
    [NeZero (c * M)] (h16 : 16 ≤ c * M) (hr : 2 * r + 9 ≤ c) (u : Fin 4 → ℤ)
    (F : (Fin 4 → Fin M) → TorusField (c * M) → ENNReal) (hm : ∀ k, Measurable (F k))
    (hread : ∀ k, DependsOnlyNear (siteOfInt fun i => u i + c * ((k i : ℕ) : ℤ)) r (F k)) :
    (∀ W, stepExpectation ℓ x (fun V => ∏ k, F k V) W = ∏ k, stepExpectation ℓ x (F k) W) ∧
    ∀ k, DependsOnlyNear (siteOfInt fun i => (ℓ.side : ℤ) * (u i + c * ((k i : ℕ) : ℤ))) (ℓ.side * r + 4 * ℓ.side)
      (stepExpectation ℓ x (F k)) := by
  classical
  set zc : (Fin 4 → Fin M) → Fin 4 → ℤ := fun k i => u i + c * ((k i : ℕ) : ℤ) with hzc
  let A : (Fin 4 → Fin M) → Finset (TorusSite (c * M)) := fun k =>
    Finset.univ.filter fun z => _root_.YangMills.Construction.TorusFields.supDist z (siteOfInt (zc k)) ≤ r
  let S : (Fin 4 → Fin M) → Finset (stepBlockFrame ℓ.side (c * M)).Cell := fun k =>
    (Finset.univ.filter fun z : TorusSite (c * M) => _root_.YangMills.Construction.TorusFields.supDist z (siteOfInt (zc k)) ≤ r + 1).image cellEquivTorusSite.symm
  have hfar : ∀ k k', k ≠ k' → ∀ z : TorusSite (c * M), _root_.YangMills.Construction.TorusFields.supDist z (siteOfInt (zc k)) ≤ r + 1 →
      _root_.YangMills.Construction.TorusFields.supDist z (siteOfInt (zc k')) ≤ r + 1 → False := by
    intro k k' hk z h1 h2
    have h3 := le_supDist_of_ne (c := c) (M := M) u hk
    have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle (siteOfInt (zc k) : TorusSite (c * M)) z (siteOfInt (zc k'))
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm (siteOfInt (zc k) : TorusSite (c * M)) z] at h4
    have h5 : _root_.YangMills.Construction.TorusFields.supDist (siteOfInt (zc k) : TorusSite (c * M)) (siteOfInt (zc k')) ≥ c := h3
    omega
  have hAd : ∀ k k', k ≠ k' → Disjoint (A k) (A k') := by
    intro k k' hk
    refine Finset.disjoint_left.mpr fun z h1 h2 => hfar k k' hk z ?_ ?_
    · exact (Finset.mem_filter.mp h1).2.trans (Nat.le_succ r)
    · exact (Finset.mem_filter.mp h2).2.trans (Nat.le_succ r)
  have hSd : ∀ k k', k ≠ k' → Disjoint (S k) (S k') := by
    intro k k' hk
    refine Finset.disjoint_left.mpr fun y h1 h2 => ?_
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨z', hz', he⟩ := Finset.mem_image.mp h2
    have := cellEquivTorusSite.symm.injective he
    subst this
    exact hfar k k' hk z' (Finset.mem_filter.mp hz).2 (Finset.mem_filter.mp hz').2
  have hAr : ∀ k, DependsOnSites (A k) (F k) := fun k V V' h =>
    hread k V V' fun z hz i => by rw [h z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)]
  have hne : ∀ W : TorusField (c * M * ℓ.side), (baseChoices ℓ (fineLevelField ℓ (c * M) W)).Nonempty := fun W =>
    hBE ℓ hfit hLam (c * M) _
  have hpi : ∀ W : TorusField (c * M * ℓ.side), baseChoices ℓ (fineLevelField ℓ (c * M) W) =
      Fintype.piFinset (baseSitesAt ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ (c * M) W))) := fun W =>
    (hL ℓ hfit hLam (c * M) (c * M) h16 h16 W W 0 0).1
  have hone : ∀ W : TorusField (c * M * ℓ.side), ∀ y,
      (baseSitesAt ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ (c * M) W)) y).Nonempty := by
    intro W y
    obtain ⟨b, hb⟩ := hne W
    rw [hpi W] at hb
    exact ⟨b y, Fintype.mem_piFinset.mp hb y⟩
  have hstep : ∀ (z : TorusSite (c * M)) (i : Fin 4), (cellEquivTorusSite (L := ℓ.side)).symm z + BlockAverages.unitStep 1 i =
      cellEquivTorusSite.symm (z + TorusFields.unitStep (c * M) i) := by
    intro z i
    show torusToFrame (stepBlockFrame ℓ.side (c * M)) 1 z + BlockAverages.unitStep 1 i =
      torusToFrame (stepBlockFrame ℓ.side (c * M)) 1 (z + TorusFields.unitStep (c * M) i)
    rw [torusToFrame_add period_top, torusToFrame_unitStep period_top]
    rfl
  have hker : ∀ k (W W' : TorusField (c * M * ℓ.side)), (∀ z, _root_.YangMills.Construction.TorusFields.supDist z (siteOfInt (zc k)) ≤ r + 1 →
        FieldsAgreeNear W W' (cellCentreOnTorus ℓ.side (cellEquivTorusSite.symm z))
          (cellCentreOnTorus ℓ.side (cellEquivTorusSite.symm z)) (3 * ℓ.side)) →
      ∀ b ∈ Fintype.piFinset (baseSitesAt ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ (c * M) W))),
      ∀ b' ∈ Fintype.piFinset (baseSitesAt ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ (c * M) W'))),
      (∀ y ∈ S k, b y = b' y) → conditionalMean ℓ x (fineLevelField ℓ (c * M) W) b (F k) =
        conditionalMean ℓ x (fineLevelField ℓ (c * M) W') b' (F k) := by
    intro k W W' hag b hb b' hb' he
    refine conditionalMean_congr hK x _ _ b b' (A k) (hm k) (hAr k) fun z hz i g => ?_
    have hz1 : _root_.YangMills.Construction.TorusFields.supDist z (siteOfInt (zc k)) ≤ r := (Finset.mem_filter.mp hz).2
    have hz2 : _root_.YangMills.Construction.TorusFields.supDist (z + TorusFields.unitStep (c * M) i) (siteOfInt (zc k)) ≤ r + 1 := by
      have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle (z + TorusFields.unitStep (c * M) i) z (siteOfInt (zc k))
      have h2 : _root_.YangMills.Construction.TorusFields.supDist (z + TorusFields.unitStep (c * M) i) z ≤ 1 := by
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm, torusUnitStep_eq_siteOfInt]
        refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun j => ?_
        by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.single_eq_of_ne hj]
      omega
    have hs1 : cellEquivTorusSite.symm z ∈ S k :=
      Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz1.trans (Nat.le_succ r)⟩, rfl⟩
    have hs2 : cellEquivTorusSite.symm (z + TorusFields.unitStep (c * M) i) ∈ S k :=
      Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz2⟩, rfl⟩
    have h3 := hag (z + TorusFields.unitStep (c * M) i) hz2
    rw [← hstep] at h3 hs2
    exact bondDensity_congr hL hfit hLam h16 x W W' b b' hb hb' (cellEquivTorusSite.symm z) i
      (hag z (hz1.trans (Nat.le_succ r))) h3 (he _ hs1) (he _ hs2) g
  refine ⟨fun W => ?_, fun k W W' hag => ?_⟩
  · rw [stepExpectation_eq_uniformMean hK x (Finset.measurable_prod _ fun k _ => hm k) W (hne W)]
    simp only [stepExpectation_eq_uniformMean hK x (hm _) W (hne W)]
    simp only [fun b => conditionalMean_prod hK x (fineLevelField ℓ (c * M) W) b A hAd hm hAr]
    rw [hpi W]
    refine uniformMean_prod_of_dependsOn_disjoint _ (hone W) Finset.univ S (fun k _ k' _ hk => hSd k k' hk) _
      fun k _ b hb b' hb' he => ?_
    exact hker k W W (fun z _ _ _ => rfl) b hb b' hb' he
  · rw [stepExpectation_eq_uniformMean hK x (hm k) W (hne W), stepExpectation_eq_uniformMean hK x (hm k) W' (hne W'),
      hpi W, hpi W']
    have hag' : ∀ z, _root_.YangMills.Construction.TorusFields.supDist z (siteOfInt (zc k)) ≤ r + 1 →
        FieldsAgreeNear W W' (cellCentreOnTorus ℓ.side (cellEquivTorusSite.symm z))
          (cellCentreOnTorus ℓ.side (cellEquivTorusSite.symm z)) (3 * ℓ.side) := by
      intro z hz
      refine fieldsAgreeNear_of_agree W W' (zc k) r (fun x₀ hx₀ i => hag x₀ ?_ i) _ ?_
      · exact hx₀
      · have : toTorusSite (c * M) (cellEquivTorusSite (L := ℓ.side).symm z) = z := cellEquivTorusSite.apply_symm_apply z
        rw [this]
        exact hz
    refine uniformMean_congr_of_dependsOn _ _ (hone W) (hone W') (S k) ?_ _ _ (hker k W W' hag')
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact baseSitesAt_congr hL hfit hLam h16 W W' _ (hag' z (Finset.mem_filter.mp hz).2)
theorem chainExpectations_factorize (hK : BondKernelProperties) (hL : BondKernelLocality)
    (hBE : BaseChoicesNonempty) (hB : BondKernelBorel) : ChainExpectationsFactorizeForSeparatedCells := by
  intro ℓ hfit hLam x s
  have hL9 : 9 ≤ ℓ.side := by have := hfit.L_ge; omega
  induction s with
  | zero =>
    intro n c M r _ hn h16 hr u F hm hread
    refine ⟨fun U => rfl, fun k => ?_⟩
    have e : (siteOfInt fun i => (ℓ.side : ℤ) ^ 0 * (u i + c * ((k i : ℕ) : ℤ)) : TorusSite n) =
        siteOfInt fun i => u i + c * ((k i : ℕ) : ℤ) := by
      funext i
      simp [siteOfInt]
    show DependsOnlyNear (siteOfInt fun i => (ℓ.side : ℤ) ^ 0 * (u i + c * ((k i : ℕ) : ℤ)) : TorusSite n) r (F k)
    rw [e]
    exact hread k
  | succ s ih =>
    intro n c M r _ hn h16 hr u F hm hread
    subst hn
    obtain ⟨hp, hq⟩ := step_factorize hK hL hBE hfit hLam (x s) h16 hr u F hm hread
    have hside : c * M * ℓ.side = c * ℓ.side * M := by ring
    have h16' : 16 ≤ c * M * ℓ.side := h16.trans (Nat.le_mul_of_pos_right _ (by omega))
    have hr' : 2 * (ℓ.side * r + 4 * ℓ.side) + 9 ≤ c * ℓ.side := by nlinarith
    have hreads : ∀ k, DependsOnlyNear
        (siteOfInt fun i => ((fun i => (ℓ.side : ℤ) * u i) i) + ((c * ℓ.side : ℕ) : ℤ) * ((k i : ℕ) : ℤ))
        (ℓ.side * r + 4 * ℓ.side) (stepExpectation ℓ (x s) (F k)) := by
      intro k
      have e : (siteOfInt fun i => ((fun i => (ℓ.side : ℤ) * u i) i) + ((c * ℓ.side : ℕ) : ℤ) * ((k i : ℕ) : ℤ) :
          TorusSite (c * M * ℓ.side)) =
          siteOfInt fun i => (ℓ.side : ℤ) * (u i + c * ((k i : ℕ) : ℤ)) := by
        funext i
        simp only [siteOfInt]
        push_cast
        ring
      rw [e]
      exact hq k
    obtain ⟨i1, i2⟩ := ih (c * M * ℓ.side) (c * ℓ.side) M (ℓ.side * r + 4 * ℓ.side) hside h16' hr'
      (fun i => (ℓ.side : ℤ) * u i) (fun k => stepExpectation ℓ (x s) (F k))
      (fun k => measurable_stepExpectation hB _ (hm k)) hreads
    have e : stepExpectation ℓ (x s) (fun V => ∏ k, F k V) = fun W => ∏ k, stepExpectation ℓ (x s) (F k) W := funext hp
    refine ⟨fun U => ?_, fun k => ?_⟩
    · show chainExpectation ℓ x s (c * M * ℓ.side) (stepExpectation ℓ (x s) fun V => ∏ k, F k V) U = _
      rw [e]
      exact i1 U
    · have e2 : (siteOfInt fun i => (ℓ.side : ℤ) ^ (s + 1) * (u i + c * ((k i : ℕ) : ℤ)) :
          TorusSite (fineSide ℓ.side (s + 1) (c * M))) =
          siteOfInt fun i => (ℓ.side : ℤ) ^ s *
            ((fun i => (ℓ.side : ℤ) * u i) i + ((c * ℓ.side : ℕ) : ℤ) * ((k i : ℕ) : ℤ)) := by
        funext i
        simp only [siteOfInt]
        push_cast
        ring
      rw [e2]
      exact i2 k
end Kernel
end YangMills.Construction.WeightedResponses
end

import YangMills.Construction.TorusOrFourSpace.ContinuousPartialsAreContinuousDifferentiability
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefinedProof
import YangMills.Construction.TorusOrFourSpace.TwoSensesOfClassC1AtOnePoint
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.SingletonC1
open Kind
abbrev soleBlock : Fin ((1 : ℕ+) : ℕ) := ⟨0, (1 : ℕ+).pos⟩
theorem eq_soleBlock (i : Fin ((1 : ℕ+) : ℕ)) : i = soleBlock :=
  Fin.ext (by
    have hi : (i : ℕ) < 1 := i.2
    show (i : ℕ) = 0
    omega)
def toR4 (x : Coords 1) : Fin 4 → ℝ := x.block soleBlock
def ofR4 (a : Fin 4 → ℝ) : Coords 1 :=
  fun j => a ⟨j, by
    have hj := j.2
    simpa using hj⟩
theorem toR4_ofR4 (a : Fin 4 → ℝ) : toR4 (ofR4 a) = a := by
  funext μ
  exact congrArg a (Fin.ext (by simp))
theorem contDiff_toR4 : ContDiff ℝ 1 toR4 :=
  contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ _
theorem contDiff_ofR4 : ContDiff ℝ 1 ofR4 :=
  contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ _
abbrev coordIdx (μ : Fin 4) : Fin (4 * ((1 : ℕ+) : ℕ)) := ⟨μ, by have := μ.2; simp⟩
theorem toR4_add_smul (x v : Coords 1) (t : ℝ) :
    toR4 (x + t • v) = toR4 x + t • toR4 v := rfl
theorem toR4_single (μ : Fin 4) :
    toR4 (Pi.single (coordIdx μ) (1 : ℝ)) = Pi.single μ (1 : ℝ) := by
  funext ν
  have e : toR4 (Pi.single (coordIdx μ) (1 : ℝ)) ν =
      (Pi.single (coordIdx μ) (1 : ℝ) : Coords 1) (coordIdx ν) :=
    congrArg (Pi.single (coordIdx μ) (1 : ℝ) : Coords 1) (Fin.ext (by
      show 4 * 0 + (ν : ℕ) = ν
      omega))
  rw [e]
  by_cases h : ν = μ
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · have h' : coordIdx ν ≠ coordIdx μ := fun c => h (Fin.ext (congrArg Fin.val c))
    rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]
theorem foldr_iterate_single_of_not_mem {X ι : Type*} [DecidableEq ι] (c : ι → X → X) (j : ι)
    (G : X) (l : List ι) (h : j ∉ l) :
    l.foldr (fun k H => (c k)^[(Pi.single j 1 : ι → ℕ) k] H) G = G := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have haj : a ≠ j := fun e => h (e ▸ List.mem_cons_self)
    have ht : j ∉ t := fun e => h (List.mem_cons_of_mem _ e)
    simp [List.foldr_cons, Pi.single_eq_of_ne haj, ih ht]
theorem foldr_iterate_single_of_mem {X ι : Type*} [DecidableEq ι] (c : ι → X → X) (j : ι)
    (G : X) (l : List ι) (hl : l.Nodup) (h : j ∈ l) :
    l.foldr (fun k H => (c k)^[(Pi.single j 1 : ι → ℕ) k] H) G = c j G := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.1 hl
    by_cases e : a = j
    · subst e
      simp [List.foldr_cons, foldr_iterate_single_of_not_mem c a G t ha]
    · have hjt : j ∈ t := (List.mem_cons.1 h).resolve_left (Ne.symm e)
      simp [List.foldr_cons, Pi.single_eq_of_ne e, ih ht hjt]
theorem iterPartial_single (j : Fin (4 * ((1 : ℕ+) : ℕ))) (G : Coords 1 → ℂ) :
    Coords.iterPartial (Pi.single j 1) G = Coords.partialAlong j G :=
  foldr_iterate_single_of_mem _ j G _ (List.nodup_finRange _) (List.mem_finRange _)
variable (D : Params) (E : Kind)
theorem quotDist_nonneg (a b : E.Pt D) : 0 ≤ Kind.quotDist D E a b := by apply _root_.YangMills.Construction.PeriodicSpace.QuotientGeometry.quotDist_nonneg <;> assumption
theorem tupleDist_single (y z : E.Tuple D 1) :
    Kind.Tuple.tupleDist D E y z = Kind.quotDist D E (y soleBlock) (z soleBlock) := by
  unfold Kind.Tuple.tupleDist
  rw [Fintype.sum_eq_single soleBlock (fun i hi => absurd (eq_soleBlock i) hi),
    Real.sqrt_sq (quotDist_nonneg D E _ _)]
theorem proj_surjective (hq : Function.Surjective (E.quotMap D)) :
    Function.Surjective (Kind.Tuple.proj D E (p := 1)) := by
  intro y
  obtain ⟨a, ha⟩ := hq (y soleBlock)
  refine ⟨ofR4 a, ?_⟩
  funext i
  rw [eq_soleBlock i]
  show E.quotMap D (toR4 (ofR4 a)) = y soleBlock
  rw [toR4_ofR4, ha]
theorem isClassC_ofSingle_iff (hp : ContPartialsIffContDiff) (u : E.Pt D → ℝ) :
    Kind.Tuple.IsClassC D E 1 (Kind.Tuple.ofSingle D E fun y => (u y : ℂ)) ↔
      Kind.IsC1Fn D E u := by
  unfold Kind.Tuple.IsClassC Kind.IsC1Fn TestFunctions.IsC1R4
  rw [hp 1 1, Nat.cast_one]
  constructor
  · intro h
    have e : u ∘ E.quotMap D = Complex.reCLM ∘
        ((Kind.Tuple.ofSingle D E fun y => (u y : ℂ)) ∘ Kind.Tuple.proj D E) ∘ ofR4 := by
      funext a
      show u (E.quotMap D a) = ((u (E.quotMap D (toR4 (ofR4 a))) : ℂ)).re
      rw [toR4_ofR4, Complex.ofReal_re]
    rw [e]
    exact Complex.reCLM.contDiff.comp (h.comp contDiff_ofR4)
  · intro h
    have e : (Kind.Tuple.ofSingle D E fun y => (u y : ℂ)) ∘ Kind.Tuple.proj D E =
        Complex.ofRealCLM ∘ (u ∘ E.quotMap D) ∘ toR4 := rfl
    rw [e]
    exact Complex.ofRealCLM.contDiff.comp (h.comp contDiff_toR4)
theorem partialAlong_lift (f : (Fin 4 → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (μ : Fin 4)
    (x : Coords 1) :
    Coords.partialAlong (coordIdx μ) (fun x => (f (toR4 x) : ℂ)) x =
      ((TestFunctions.partialDerivR4 μ f (toR4 x) : ℝ) : ℂ) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg : DifferentiableAt ℝ (fun t : ℝ => f (toR4 x + t • Pi.single μ (1 : ℝ))) 0 := by
    have hl : DifferentiableAt ℝ (fun t : ℝ => toR4 x + t • Pi.single μ (1 : ℝ)) 0 := by
      fun_prop
    exact (hd _).comp (0 : ℝ) hl
  have e : (fun t : ℝ => ((f (toR4 (x + t • Pi.single (coordIdx μ) (1 : ℝ))) : ℝ) : ℂ)) =
      fun t : ℝ => ((f (toR4 x + t • Pi.single μ (1 : ℝ)) : ℝ) : ℂ) := by
    funext t
    rw [toR4_add_smul, toR4_single]
  show deriv (fun t : ℝ => ((f (toR4 (x + t • Pi.single (coordIdx μ) (1 : ℝ))) : ℝ) : ℂ)) 0 =
    ((deriv (fun t : ℝ => f (toR4 x + t • Pi.single μ (1 : ℝ))) 0 : ℝ) : ℂ)
  rw [e]
  exact hg.hasDerivAt.ofReal_comp.deriv
theorem partialDeriv_ofSingle (hq : Function.Surjective (E.quotMap D))
    (u : E.Pt D → ℝ) (hu : Kind.IsC1Fn D E u) (μ : Fin 4)
    (hμ : Kind.partialDeriv D E μ u ∘ E.quotMap D =
      TestFunctions.partialDerivR4 μ (u ∘ E.quotMap D)) :
    Kind.Tuple.partialDeriv D E (Pi.single (coordIdx μ) 1)
        (Kind.Tuple.ofSingle D E fun y => (u y : ℂ)) =
      Kind.Tuple.ofSingle D E fun y => (Kind.partialDeriv D E μ u y : ℂ) := by
  have hH : (Kind.Tuple.ofSingle D E fun y => (Kind.partialDeriv D E μ u y : ℂ)) ∘
        Kind.Tuple.proj D E =
      Coords.iterPartial (Pi.single (coordIdx μ) 1)
        ((Kind.Tuple.ofSingle D E fun y => (u y : ℂ)) ∘ Kind.Tuple.proj D E) := by
    rw [iterPartial_single]
    funext x
    have h := partialAlong_lift (u ∘ E.quotMap D) hu μ x
    refine Eq.trans ?_ h.symm
    show ((Kind.partialDeriv D E μ u (E.quotMap D (toR4 x)) : ℝ) : ℂ) = _
    rw [← hμ]
    rfl
  have hs := Classical.epsilon_spec
    (p := fun H : E.Tuple D 1 → ℂ => H ∘ Kind.Tuple.proj D E =
      Coords.iterPartial (Pi.single (coordIdx μ) 1)
        ((Kind.Tuple.ofSingle D E fun y => (u y : ℂ)) ∘ Kind.Tuple.proj D E))
    ⟨_, hH⟩
  have h2 := hs.trans hH.symm
  exact (proj_surjective D E hq).injective_comp_right h2
theorem supportT_ofSingle (u : E.Pt D → ℝ) :
    Kind.Tuple.supportT D E (Kind.Tuple.ofSingle D E fun y => (u y : ℂ)) =
      Kind.Tuple.singleSet D E (Kind.supportQ D E u) := by
  ext y
  constructor
  · intro h r hr
    obtain ⟨z, hz, hd⟩ := h r hr
    refine ⟨z soleBlock, ?_, ?_⟩
    · intro h0
      apply hz
      show ((u (z soleBlock) : ℝ) : ℂ) = 0
      rw [h0, Complex.ofReal_zero]
    · rw [← tupleDist_single]
      exact hd
  · intro h r hr
    obtain ⟨w, hw, hd⟩ := h r hr
    refine ⟨fun _ => w, ?_, ?_⟩
    · intro h0
      exact hw (Complex.ofReal_eq_zero.1 h0)
    · rw [tupleDist_single]
      exact hd
theorem statement_holds (contPartials : ContPartialsIffContDiff)
    (wellPosed : WellPosedness.WellPosed) : Statement := by
  intro D E u
  obtain ⟨⟨-, hq, -⟩, -, -, -, -, -, -, -, -, hw, -⟩ := wellPosed D E
  refine ⟨isClassC_ofSingle_iff D E contPartials u, fun hu => ⟨fun μ => ?_, supportT_ofSingle D E u⟩⟩
  exact partialDeriv_ofSingle D E hq u hu μ ((hw u hu).2 μ).2.2
end YangMills.Construction.PeriodicSpace.SingletonC1

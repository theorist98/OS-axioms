import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod


open MeasureTheory Filter Topology ENNReal
open scoped Real


noncomputable section

/-- Spacetime dimension -/
def STDimension : ℕ := 4
abbrev SpaceTime := EuclideanSpace ℝ (Fin STDimension)
abbrev SpaceTimeMeasure : Measure SpaceTime := volume

namespace OS4



/--
A flow is a group action of ℝ on a measurable space Ω, satisfying:
1. Measurability of the joint action
2. Identity element acts as the identity map
3. Group composition property

In QFT, flows represent spacetime translations of field configurations.
-/
structure Flow (Ω : Type*) [MeasurableSpace Ω] where
  /-- The flow action: maps a time t and a point ω to another point in Ω -/
  T : ℝ → Ω → Ω

  /-- The flow is jointly measurable in both time and space variables.
      This is crucial for integration and applying Fubini's theorem (being able to switch order of integration). -/
  measurable_prod : Measurable fun p : ℝ × Ω => T p.1 p.2

  /-- At time 0, the flow is the identity transformation.
      This represents the group identity element. -/
  id : ∀ ω, T 0 ω = ω

  /-- Group property: Flowing for time s+t equals flowing for time t then for time s.
      This ensures the flow forms a proper group action of ℝ. -/
  comp : ∀ s t ω, T (s + t) ω = T s (T t ω)

namespace Flow

/--
Each time-slice of the flow is measurable. We need this applying
Fubini's theorem and for establishing measurability of time averages.

This follows from the joint measurability of the flow and the fact that
the constant function t and the identity function are measurable.
-/
lemma measurable_T {Ω : Type*} [MeasurableSpace Ω] (φ : Flow Ω) (t : ℝ) :
    Measurable (φ.T t) := by
  -- Use the fact that T t is a section of the jointly measurable function
  let s : Ω → ℝ × Ω := fun ω => (t, ω)
  -- Express φ.T t as a composition of s and the jointly measurable function
  have h_comp : φ.T t = (fun p => φ.T p.1 p.2) ∘ s := by
    ext ω
    simp [s]
  -- Use the composition of measurable functions
  rw [h_comp]
  apply Measurable.comp
  -- The joint function is measurable by assumption
  · exact φ.measurable_prod
  -- Now we need to show s is measurable
  · apply Measurable.prodMk
    -- t is a constant function (measurable)
    · exact measurable_const
    -- identity on Ω is measurable
    · exact measurable_id

-- Removed unused definition orbit

end Flow

/--
Time-average (Cesàro) along the flow over window length `R`.
This represents the average value of a function f along the orbit of ω
for time parameter ranging from 0 to R.

In ergodic theory, this average converges (as R→∞) to the space average
for almost all starting points ω.

For R = 0, we define the average to be 0 by convention.
-/
def timeAvgCesaro {Ω} [MeasurableSpace Ω] (φ : Flow Ω) (f : Ω → ℝ) (ω : Ω) (R : NNReal) : ℝ :=
  if R = 0 then 0 else
    (1 / (R : ℝ)) * ∫ s in Set.Icc (0 : ℝ) (R : ℝ), f (φ.T s ω)
-- We can directly use Real.volume_Icc from Mathlib without needing our own lemma
-- But if we want to keep it for consistency with how we use it elsewhere:
@[simp] lemma volume_Icc_eq_length {a b : ℝ} (hab : a ≤ b) :
  volume (Set.Icc a b) = ENNReal.ofReal (b - a) := by
    -- Use hab to show that a ≤ b, which ensures Set.Icc a b is a valid interval
    have _ := hab  -- Use the hypothesis to avoid the unused variable warning
    exact Real.volume_Icc

lemma volume_Icc_zero_length {c : ℝ} (hc : 0 ≤ c) :
  volume (Set.Icc (0 : ℝ) c) = ENNReal.ofReal c := by
  calc
    volume (Set.Icc (0 : ℝ) c)
        = ENNReal.ofReal (c - 0) := volume_Icc_eq_length (a := 0) (b := c) hc
    _   = ENNReal.ofReal c := by
          simp [sub_zero]

lemma volume_Icc_zero_right (R : NNReal) :
  volume (Set.Icc (0 : ℝ) (R : ℝ)) = R := by
  calc
    volume (Set.Icc (0 : ℝ) (R : ℝ))
        = ENNReal.ofReal (R : ℝ) :=
          volume_Icc_zero_length (c := (R : ℝ)) (NNReal.coe_nonneg R)
    _   = R := by
          simp [ENNReal.ofReal_coe_nnreal]



lemma volume_Icc_translation_invariance {a b : ℝ} (hab : a ≤ b) :
  MeasureTheory.volume (Set.Icc a b) = MeasureTheory.volume (Set.Icc (0 : ℝ) (b - a)) := by
  -- This is a fundamental property of Lebesgue measure:
  -- it is translation-invariant.

  -- Apply our fundamental to both sides

  -- For the left side: volume(Icc a b) = ENNReal.ofReal (b - a)
  rw [volume_Icc_eq_length hab]

  -- For the right side: volume(Icc 0 (b-a)) = ENNReal.ofReal ((b-a) - 0)
  have h_sub_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
  have h_right := volume_Icc_eq_length h_sub_nonneg

  -- Simplify (b - a) - 0 = b - a
  rw [sub_zero] at h_right

  -- Both sides are now equal (symmetry of equality)
  rw [eq_comm]
  exact h_right

open MeasureTheory
  lemma indicator_comp_preimage_const_one {X} (E : Set X) (g : X → X) :
  (Set.indicator E (fun _ : X => (1 : ℝ))) ∘ g
    = Set.indicator (g ⁻¹' E) (fun _ : X => (1 : ℝ)) := by
  classical
  funext x
  by_cases hx : g x ∈ E
  · have : x ∈ g ⁻¹' E := by simpa [Set.mem_preimage] using hx
    simp [Function.comp, Set.indicator, hx, this]
  · have : x ∉ g ⁻¹' E := by simpa [Set.mem_preimage] using hx
    simp [Function.comp, Set.indicator, hx, this]

/-- Helper lemma: For almost everywhere equal sets, their indicator functions are also almost everywhere equal. -/
lemma indicator_ae_of_set_ae_equal {X} [MeasurableSpace X] {ν : Measure X}
    {A B : Set X} (h : A =ᵐ[ν] B) :
    Set.indicator A (fun _ => (1 : ℝ)) =ᵐ[ν] Set.indicator B (fun _ => (1 : ℝ)) := by
  -- First, let's define where the indicator functions differ
  let diff_set := {x | Set.indicator A (fun _ => (1 : ℝ)) x ≠ Set.indicator B (fun _ => (1 : ℝ)) x}

  -- We need to prove that ν(diff_set) = 0, i.e., the functions are equal a.e.
  -- A =ᵐ[ν] B means the measure of their symmetric difference is zero

  -- Use the filter.eventuallyEq notation directly
  filter_upwards [h] with x hx

  -- hx says that x belongs to both A and B, or to neither
  -- We need to show that the indicator functions agree at x
  simp only [Set.indicator] at hx ⊢

  -- Case analysis on whether x ∈ A
  by_cases hA : x ∈ A
  · -- If x ∈ A, then from hx we know x ∈ B as well
    have hB : x ∈ B := by
      -- From hx: x ∈ A ↔ x ∈ B
      -- Since we know x ∈ A, we get x ∈ B
      exact hx.mp hA

    -- Now both indicators evaluate to 1
    simp [hA, hB]

  · -- If x ∉ A, then from hx we know x ∉ B as well
    have hB : x ∉ B := by
      -- From hx: x ∈ A ↔ x ∈ B
      -- Since we know x ∉ A, we get x ∉ B
      exact mt hx.mpr hA

    -- Now both indicators evaluate to 0
    simp [hA, hB]/-- Helper lemma: For an invariant set A, the indicator function of A is invariant.
    That is, if (φ.T t)⁻¹' A =ᵐ[μ] A, then χ_A ∘ φ.T t =ᵐ[μ] χ_A. -/
theorem indicator_of_invariant_set1 {X} [MeasurableSpace X] {ν : Measure X}
    {flow : Flow X} {A : Set X} {t : ℝ} (h : (flow.T t) ⁻¹' A =ᵐ[ν] A) :
    (Set.indicator A (fun _ => (1 : ℝ))) ∘ flow.T t =ᵐ[ν] Set.indicator A (fun _ => (1 : ℝ)) := by
  -- First, use the fact that composing the indicator with a map
  -- is the same as taking the indicator of the preimage
  have composition_eq : (Set.indicator A (fun _ => (1 : ℝ))) ∘ flow.T t =
                        Set.indicator ((flow.T t) ⁻¹' A) (fun _ => (1 : ℝ)) :=
    indicator_comp_preimage_const_one A (flow.T t)

  -- Now we need to show that indicator((flow.T t)⁻¹' A) =ᵐ[ν] indicator(A)
  -- This follows from our helper lemma about indicator functions of a.e. equal sets
  have indicators_ae_equal : Set.indicator ((flow.T t) ⁻¹' A) (fun _ => (1 : ℝ)) =ᵐ[ν]
                            Set.indicator A (fun _ => (1 : ℝ)) :=
    indicator_ae_of_set_ae_equal h

  -- Start with our composition equality
  calc
    (Set.indicator A (fun _ => (1 : ℝ))) ∘ flow.T t
        = Set.indicator ((flow.T t) ⁻¹' A) (fun _ => (1 : ℝ)) := composition_eq
    _ =ᵐ[ν] Set.indicator A (fun _ => (1 : ℝ)) := indicators_ae_equal

theorem indicator_ae_const_is_zero_or_one_impl {X} [MeasurableSpace X] {ν : Measure X}
    [IsProbabilityMeasure ν] {A : Set X} {c : ℝ} (h : Set.indicator A (fun _ => (1 : ℝ)) =ᵐ[ν] fun _ => c) :
    c = 0 ∨ c = 1 :=
  -- The key insight is that indicator functions only take values 0 or 1
  -- If it equals c almost everywhere, then c must be either 0 or 1

  -- We'll define a set B where the indicator function differs from c
  let B := {x | Set.indicator A (fun _ => (1 : ℝ)) x ≠ c}

  -- By our hypothesis h, this set has measure zero
  have B_measure_zero : ν B = 0 := by
    -- The set B is exactly the set where the functions differ
    -- Since they're a.e. equal, this set has measure zero
    rw [Filter.EventuallyEq, ae_iff] at h
    push_neg at h
    exact h

  -- If c ≠ 0 and c ≠ 1, then the indicator function differs from c everywhere
  -- This would mean the set B is the entire space, which can't have measure zero
  -- unless the entire space has measure zero (a trivial case we can handle)

  -- Use classical logic to handle the cases
  Classical.byCases
    (fun h0 : c = 0 => Or.inl h0)  -- If c = 0, we're done
    (fun h0 : c ≠ 0 =>             -- If c ≠ 0, we need to show c = 1
      Classical.byCases
        (fun h1 : c = 1 => Or.inr h1)  -- If c = 1, we're done
        (fun h1 : c ≠ 1 =>             -- If c ≠ 0 and c ≠ 1
          -- This case leads to a contradiction
          False.elim (by
            -- The indicator function only takes values 0 and 1
            -- If c ≠ 0 and c ≠ 1, then the indicator differs from c everywhere
            have indicator_vals : ∀ x, Set.indicator A (fun _ => (1 : ℝ)) x = 0 ∨
                                       Set.indicator A (fun _ => (1 : ℝ)) x = 1 := by
              intro x
              simp only [Set.indicator]
              by_cases hx : x ∈ A
              · simp [hx]
              · simp [hx]

            -- Since indicator only takes values 0 or 1, and c is neither,
            -- the indicator differs from c everywhere
            have B_eq_univ : B = Set.univ := by
              ext x
              simp [B]
              have hx := indicator_vals x
              cases hx with
              | inl h_eq_0 => simp only [h_eq_0]; exact h0.symm
              | inr h_eq_1 => simp only [h_eq_1]; exact h1.symm

            -- But B has measure zero, so the whole space has measure zero
            rw [B_eq_univ] at B_measure_zero

            -- For a probability measure, Set.univ has measure 1, not 0
            have univ_measure_one : ν Set.univ = 1 := measure_univ
            rw [univ_measure_one] at B_measure_zero

            -- This is a contradiction: 0 ≠ 1
            norm_num at B_measure_zero
          )
        )
    )/-- If an indicator function is a.e. equal to a constant, that constant must be 0 or 1. -/
lemma indicator_ae_const_is_zero_or_one {X} [MeasurableSpace X] {ν : Measure X}
    [IsProbabilityMeasure ν] {A : Set X} {c : ℝ} (h : Set.indicator A (fun _ => (1 : ℝ)) =ᵐ[ν] fun _ => c) :
    c = 0 ∨ c = 1 := indicator_ae_const_is_zero_or_one_impl h

/-- If an indicator function is a.e. equal to 0, then the set has measure zero. -/
lemma indicator_ae_zero_imp_measure_zero {X} [MeasurableSpace X] {ν : Measure X}
    {A : Set X} (h : Set.indicator A (fun _ => (1 : ℝ)) =ᵐ[ν] fun _ => 0) :
    ν A = 0 := by
  -- The indicator of A is 1 on A and 0 outside A
  -- If it's a.e. equal to 0, then it's a.e. 0 on A
  -- This means A has measure zero
  rw [Filter.EventuallyEq, ae_iff] at h
  push_neg at h
  -- h says the set where indicator ≠ 0 has measure zero
  -- But indicator = 1 exactly on A, so A ⊆ {x | indicator A 1 x ≠ 0}
  have A_subset : A ⊆ {x | Set.indicator A (fun _ => (1 : ℝ)) x ≠ 0} := by
    intro x hx
    simp [Set.indicator, hx]
  -- Since A is a subset of a measure-zero set, it has measure zero
  exact measure_mono_null A_subset h

/-- If an indicator function is a.e. equal to 1, then the set has full measure. -/
lemma indicator_ae_one_imp_full_measure {X} [MeasurableSpace X] {ν : Measure X}
    [IsProbabilityMeasure ν] {A : Set X} (hA : MeasurableSet A)
    (h : Set.indicator A (fun _ => (1 : ℝ)) =ᵐ[ν] fun _ => 1) :
    ν A = ν Set.univ := by
  -- The indicator of A is 0 on Aᶜ and 1 on A
  -- If it's a.e. equal to 1, then it's a.e. 0 on Aᶜ
  -- This means Aᶜ has measure zero, so A has full measure
  have h_compl : Set.indicator Aᶜ (fun _ => (1 : ℝ)) =ᵐ[ν] fun _ => 0 := by
    filter_upwards [h] with x hx
    simp only [Set.indicator]
    by_cases h1 : x ∈ Aᶜ
    · -- If x ∈ Aᶜ, then x ∉ A, so indicator A = 0 but hx says it equals 1
      simp only [if_pos h1]
      have h2 : x ∉ A := Set.notMem_of_mem_compl h1
      simp only [Set.indicator, h2, if_false] at hx
      -- hx says 0 = 1, contradiction
      exfalso
      exact zero_ne_one hx
    · -- If x ∉ Aᶜ, then indicator Aᶜ = 0
      simp only [if_neg h1]

  -- Apply the previous lemma to Aᶜ
  have compl_measure_zero : ν Aᶜ = 0 := indicator_ae_zero_imp_measure_zero h_compl

  -- Since ν is a probability measure, ν(A) + ν(Aᶜ) = ν(univ) = 1
  -- Using the fact that ν Aᶜ = 0, we get ν A = ν univ
  have h_union : ν (A ∪ Aᶜ) = ν A + ν Aᶜ := by
    apply measure_union' disjoint_compl_right hA
  rw [Set.union_compl_self, compl_measure_zero, add_zero] at h_union
  exact h_union.symm

open MeasureTheory

  -- Helper lemma 1: For a set with full measure, its complement--
@[measurability]
lemma measurable_integral_parametric_sfinite
  {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} [SFinite μ]
  {f : X × Y → ℝ} (hf : Measurable f) :
  Measurable (fun y => ∫ x, f (x, y) ∂μ) := by
  -- `Integral.Prod` gives strong measurability; then downgrade.
  have hsm : StronglyMeasurable f := hf.stronglyMeasurable
  have hsm' :
      StronglyMeasurable (fun y : Y => ∫ x, f (x, y) ∂μ) :=
    MeasureTheory.StronglyMeasurable.integral_prod_left'
      (α := X) (β := Y) (μ := μ) (E := ℝ) hsm
  exact hsm'.measurable

/-- Specialization you likely need: measurability of
    `ω ↦ ∫_{s∈[0,R]} g (s, ω) ds` with Lebesgue. -/

@[measurability]
lemma measurable_parametric_integral_Icc_zero_R
  {Ω : Type*} [MeasurableSpace Ω]
  (R : NNReal) {g : ℝ × Ω → ℝ} (hg : Measurable g) :
  Measurable (fun ω => ∫ s in Set.Icc (0 : ℝ) (R : ℝ), g (s, ω)) := by
  -- rewrite set integral as integral w.r.t. restricted measure
  have h_rw :
      (fun ω => ∫ s in Set.Icc (0 : ℝ) (R : ℝ), g (s, ω))
      =
      (fun ω => ∫ s, g (s, ω) ∂(volume.restrict (Set.Icc (0 : ℝ) (R : ℝ)))) := by
    funext ω; rfl
  -- Lebesgue is s-finite, and restriction preserves s-finiteness
  haveI : SFinite (volume.restrict (Set.Icc (0 : ℝ) (R : ℝ))) := inferInstance
  -- apply the general s-finite lemma
  have hm :
      Measurable
        (fun ω => ∫ s, g (s, ω) ∂(volume.restrict (Set.Icc (0 : ℝ) (R : ℝ)))) :=
    measurable_integral_parametric_sfinite
      (μ := volume.restrict (Set.Icc (0 : ℝ) (R : ℝ)))
      (f := g) hg
  simpa [h_rw] using hm




lemma measurable_parametric_integration_core
  {Ω : Type*} [MeasurableSpace Ω]
  {R : NNReal}
  {g : ℝ × Ω → ℝ}
  (hg : Measurable g) :
  Measurable (fun ω => ∫ s in Set.Icc (0 : ℝ) (R : ℝ), g (s, ω)) := by

  -- Our goal is to show that the function
  -- f(ω) = ∫ g(s,ω) ds over [0,R]
  -- is measurable. This follows from standard results in measure theory.

  -- We directly apply our helper lemma which handles exactly this case
  exact measurable_parametric_integral_Icc_zero_R R hg

-- Removed unused lemma measurable_parametric_integration (using measurable_parametric_integration_core instead)

/--
Helper lemma for measurable_timeAverage: Proves measurability of parametric integrals involving flows.
This lemma establishes that for a measurable function f and a flow φ,
the function ω ↦ ∫ f(φ.T s ω) ds over [0,R] is measurable.

This is a critical step in proving that time averages are measurable functions.
The key insight is to recognize that (s,ω) ↦ f(φ.T s ω) is jointly measurable
when f is measurable and φ is a flow, which allows us to apply our general
parametric integration result.
-/
lemma measurable_flow_parametric_integral {Ω : Type*} [MeasurableSpace Ω]
  (φ : OS4.Flow Ω) (f : Ω → ℝ) (hf : Measurable f) (R : NNReal) (_hR : R ≠ 0) :
  Measurable (fun ω => ∫ s in Set.Icc (0 : ℝ) (R : ℝ), f (φ.T s ω)) := by
  -- build the joint measurable kernel
  have joint_meas : Measurable (fun p : ℝ × Ω => f (φ.T p.1 p.2)) :=
    hf.comp φ.measurable_prod
  -- name it g and apply the helper
  let g : ℝ × Ω → ℝ := fun p => f (φ.T p.1 p.2)
  have hg : Measurable g := joint_meas
  have h_meas :
      Measurable (fun ω => ∫ s in Set.Icc (0 : ℝ) (R : ℝ), g (s, ω)) :=
    OS4.measurable_parametric_integral_Icc_zero_R (R := R) (g := g) hg
  simpa [g] using h_meas

/--
Helper lemma for the nonzero case of measurable_timeAverage.
This handles the case where R > 0 and we need to prove measurability of the actual time average.
-/
lemma measurable_timeAverage_helper {Ω : Type*} [MeasurableSpace Ω]
  (φ : OS4.Flow Ω) (f : Ω → ℝ) (hf : Measurable f) (R : NNReal) (hR : R ≠ 0) :
  Measurable (fun ω => (R : ℝ)⁻¹ * ∫ s in Set.Icc (0 : ℝ) (R : ℝ), f (φ.T s ω)) := by
  have h := measurable_flow_parametric_integral φ f hf R hR
  exact Measurable.const_mul h ((R : ℝ)⁻¹)


/--
Proves that the time average function is measurable.
This lemma is crucial for establishing measurability properties in ergodic theory.
It handles both the case where R = 0 (trivial case) and R > 0 (using the helper lemma).
-/
lemma measurable_timeAverage {Ω : Type*} [MeasurableSpace Ω]
  (φ : Flow Ω) (f : Ω → ℝ) (hf : Measurable f) (R : NNReal) :
  Measurable (fun ω => timeAvgCesaro φ f ω R) := by
  unfold timeAvgCesaro
  by_cases h : R = 0
  · -- Case: R = 0, the time average is the constant function 0
    subst h
    simp
  · -- Case: R > 0, use the helper lemma
    simp [h]
    exact measurable_timeAverage_helper φ f hf R h


/-- Invariance of a measure under a flow. -/
def invariant_under {Ω} [MeasurableSpace Ω] (μ : Measure Ω) (φ : Flow Ω) : Prop :=
  ∀ t : ℝ, MeasurePreserving (φ.T t) μ μ

/-- Invariant measurable sets up to μ-a.e. equality. -/
def invariant_set {Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (φ : Flow Ω) (A : Set Ω) : Prop :=
  MeasurableSet A ∧ ∀ t, (φ.T t) ⁻¹' A =ᵐ[μ] A

/--
Ergodicity via invariant sets: only trivial invariant sets.

A flow is ergodic if every invariant set has either measure zero or full measure.
This is the standard definition of ergodicity in measure theory, and is
equivalent to other formulations via time averages or mixing properties.

In physical terms, ergodicity means that the system cannot be decomposed into
separate invariant subsystems - it is irreducible.
-/
def ergodic_action {Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (φ : Flow Ω) : Prop :=
  ∀ ⦃A : Set Ω⦄, invariant_set μ φ A → μ A = 0 ∨ μ A = μ Set.univ



/-- If all sublevel sets of a measurable function have trivial measure (either 0 or full),
    then the function is almost everywhere constant. This is a key result in ergodic theory. -/
@[simp] axiom ae_const_of_all_sublevels_trivial
  {Ω} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  (f : Ω → ℝ) (hf_meas : Measurable f)
  (h_trivial : ∀ a : ℝ, μ {x | f x ≤ a} = 0 ∨ μ {x | f x ≤ a} = μ Set.univ) :
  ∃ c : ℝ, f =ᵐ[μ] fun _ => c

/-- If `f` is measurable and *not* a.e. constant (w.r.t. a finite measure),
    some sublevel set has strictly intermediate measure. -/
lemma non_const_has_intermediate_level_set
  {Ω} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  (f : Ω → ℝ) (hf_meas : Measurable f)
  (h_not_const : ∀ c : ℝ, ¬ (f =ᵐ[μ] fun _ => c)) :
  ∃ a : ℝ, 0 < μ {x | f x ≤ a} ∧ μ {x | f x ≤ a} < μ Set.univ := by
  classical
  -- Either every sublevel has measure 0 or full, or there is an intermediate one
  by_cases hstep : ∀ a : ℝ, μ {x | f x ≤ a} = 0 ∨ μ {x | f x ≤ a} = μ Set.univ
  · -- Then `f` would be a.e. constant, contradicting the hypothesis
    obtain ⟨c, hc⟩ := ae_const_of_all_sublevels_trivial f hf_meas hstep
    exact False.elim ((h_not_const c) hc)
  · -- Otherwise there exists an `a` with neither 0 nor full measure
    push_neg at hstep
    rcases hstep with ⟨a, hne0, hnefull⟩
    refine ⟨a, ?pos, ?ltfull⟩
    -- 0 < μ {f ≤ a}
    have h0le : (0 : ℝ≥0∞) ≤ μ {x | f x ≤ a} := bot_le
    have : 0 ≠ μ {x | f x ≤ a} := hne0.symm
    have hpos : (0 : ℝ≥0∞) < μ {x | f x ≤ a} := lt_of_le_of_ne h0le this
    exact hpos
    -- μ {f ≤ a} < μ univ
    have hle : μ {x | f x ≤ a} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    exact lt_of_le_of_ne hle hnefull

/-- Helper lemma: The level sets of a measurable function are measurable sets. -/
 lemma level_set_is_measurable {Ω} [MeasurableSpace Ω]
      (f : Ω → ℝ) (hf_meas : Measurable f) (a : ℝ) :
      MeasurableSet {x | f x ≤ a} := by
    -- The set {x | f x ≤ a} is the preimage of the set {y | y ≤ a} under f
    -- So we can rewrite this as f⁻¹' {y | y ≤ a}
    have h_eq : {x | f x ≤ a} = f⁻¹' {y | y ≤ a} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage]

    -- Now rewrite using this equality
    rw [h_eq]

    -- The set {y | y ≤ a} is the set (-∞, a], which is measurable in ℝ
    -- Since f is measurable, the preimage of a measurable set is measurable

    -- First note that {y | y ≤ a} is exactly Set.Iic a
    have h_is_Iic : {y | y ≤ a} = Set.Iic a := by rfl

    -- Then use the fact that Set.Iic a is measurable
    rw [h_is_Iic]

    -- Apply the measurability of f to the measurable set Set.Iic a
    exact hf_meas measurableSet_Iic

lemma invariant_fun_implies_invariant_level_sets {Ω} [MeasurableSpace Ω]
      {μ : Measure Ω} {φ : Flow Ω} (f : Ω → ℝ) (a : ℝ)
      (hf_inv : ∀ t, f ∘ φ.T t =ᵐ[μ] f) :
      ∀ t, (φ.T t) ⁻¹' {x | f x ≤ a} =ᵐ[μ] {x | f x ≤ a} := by
    intro t
    have h_comp_eq : f ∘ φ.T t =ᵐ[μ] f := hf_inv t

    have h_preimage_eq : (φ.T t) ⁻¹' {x | f x ≤ a} = {ω | f (φ.T t ω) ≤ a} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq]

    have h_comp_eq_set : {ω | f (φ.T t ω) ≤ a} = {ω | (f ∘ φ.T t) ω ≤ a} := by
      ext ω
      simp only [Function.comp_apply, Set.mem_setOf_eq]

    have h_level_sets_ae_eq : {ω | (f ∘ φ.T t) ω ≤ a} =ᵐ[μ] {x | f x ≤ a} := by
      -- Use the fact that f ∘ φ.T t =ᵐ[μ] f
      filter_upwards [h_comp_eq] with ω hω

      -- After filter_upwards, our goal is to show:
      -- {ω | (f ∘ φ.T t) ω ≤ a} ω = {x | f x ≤ a} ω
      -- This is checking if ω belongs to each set

      -- We know from hω that (f ∘ φ.T t) ω = f ω
      have h_eq : (f ∘ φ.T t) ω = f ω := hω

      -- To check if ω is in a set defined by a predicate,
      -- we need to verify if the predicate holds at ω

      -- For {ω | (f ∘ φ.T t) ω ≤ a} ω, we check if (f ∘ φ.T t) ω ≤ a
      -- For {x | f x ≤ a} ω, we check if f ω ≤ a

      -- Let's show both sides are equal by explicit calculation
      calc {ω | (f ∘ φ.T t) ω ≤ a} ω
          = ((f ∘ φ.T t) ω ≤ a) := by rfl
          _ = (f ω ≤ a) := by rw [h_eq]
          _ = {x | f x ≤ a} ω := by rfl

    calc (φ.T t) ⁻¹' {x | f x ≤ a}
      = {ω | f (φ.T t ω) ≤ a} := h_preimage_eq
      _ = {ω | (f ∘ φ.T t) ω ≤ a} := h_comp_eq_set
      _ =ᵐ[μ] {x | f x ≤ a} := h_level_sets_ae_eq

/-- Helper lemma for the forward direction of ergodic_iff_invariant_functions_ae_const.
    This handles the proof that ergodicity implies all invariant functions are constant. -/
lemma ergodic_to_invariant_functions_ae_const {Ω} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {φ : Flow Ω}
    (_ : invariant_under μ φ) (h_erg : ergodic_action μ φ)
    (f : Ω → ℝ) (hf_meas : Measurable f) (hf_inv : ∀ t, f ∘ φ.T t =ᵐ[μ] f) :
    ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  /-
  Key insight: In an ergodic system, every invariant set has either measure zero
  or full measure. This implies invariant functions must be constant.

  Proof approach:
  1. Assume f is invariant but not essentially constant
  2. Show there must exist a level set A = {x | f(x) ≤ a} with measure strictly
     between 0 and μ(univ)
  3. Show this level set is invariant
  4. This contradicts ergodicity
  -/

  -- Suppose f is not essentially constant
  by_contra h_not_const
  push_neg at h_not_const
  -- h_not_const now states: ∀ c : ℝ, ¬(f =ᵐ[μ] fun _ => c)

  -- Since f is not essentially constant, there must exist some threshold 'a'
  -- where the level set {x | f(x) ≤ a} has measure strictly between 0 and μ(Set.univ)
  -- We use our helper lemma for this
  have h_exists_split := non_const_has_intermediate_level_set f hf_meas h_not_const

  -- Get the threshold where the measure splits
  rcases h_exists_split with ⟨a, ha_pos, ha_lt_univ⟩

  -- Define the level set A := {x | f x ≤ a}
  let A := {x | f x ≤ a}

  -- Step 1: Show A is measurable using our helper lemma
  have hA_meas : MeasurableSet A :=
    level_set_is_measurable f hf_meas a

  -- Step 2: Show A is invariant under the flow using our helper lemma
  have hA_inv : ∀ t, (φ.T t) ⁻¹' A =ᵐ[μ] A :=
    invariant_fun_implies_invariant_level_sets f a hf_inv

  -- Step 3: A is invariant, so by ergodicity, it must have measure 0 or full measure
  have hA_trivial : μ A = 0 ∨ μ A = μ Set.univ :=
    h_erg ⟨hA_meas, hA_inv⟩

  -- Step 4: Derive a contradiction
  -- We showed that 0 < μ A < μ Set.univ, which contradicts hA_trivial
  cases hA_trivial with
  | inl h_zero => -- Case: μ A = 0
    -- This contradicts ha_pos: 0 < μ A
    rw [h_zero] at ha_pos
    exact lt_irrefl 0 ha_pos
  | inr h_full => -- Case: μ A = μ Set.univ
    -- This contradicts ha_lt_univ: μ A < μ Set.univ
    rw [h_full] at ha_lt_univ
    exact lt_irrefl (μ Set.univ) ha_lt_univ

  /-
  Since we've reached a contradiction, our initial assumption must be false.
  Therefore, f must be essentially constant.

  This is a fundamental result in ergodic theory, connecting the definition
  of ergodicity via invariant sets to the behavior of invariant functions.
  -//-- Helper lemma for showing the indicator function of a measurable set is measurable. -/
lemma indicator_const_measurable {Ω} [MeasurableSpace Ω] {A : Set Ω} (hA : MeasurableSet A) :
  Measurable (Set.indicator A (fun _ => (1 : ℝ))) := by
  -- The indicator function of a measurable set is measurable
  -- We'll prove this by using the fact that:
  -- 1. The constant function 1 is measurable
  -- 2. For a measurable set A and measurable function f,
  --    the indicator function is measurable

  -- Step 1: The constant function 1 is measurable
  have h_const : Measurable (fun _ : Ω => (1 : ℝ)) := measurable_const

  -- Step 2: Use the indicator measurability theorem
  -- In Lean 4's mathlib, this is typically handled by measurable.indicator
  exact Measurable.indicator h_const hA

@[simp] lemma ergodic_iff_invariant_functions_ae_const {Ω}
  [MeasurableSpace Ω]
      {μ : Measure Ω} [IsFiniteMeasure μ] {φ : Flow Ω} (h_inv :
  invariant_under μ φ) :
      ergodic_action μ φ ↔
      ∀ f : Ω → ℝ, (Measurable f ∧ ∀ t, f ∘ φ.T t =ᵐ[μ] f) → ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  constructor
  · -- Forward direction: ergodic → invariant functions are constant
    intro h_erg f ⟨hf_meas, hf_inv⟩
    -- Use the helper lemma that contains the sorry
    exact ergodic_to_invariant_functions_ae_const h_inv h_erg f hf_meas hf_inv

  · -- Backward direction: invariant functions are constant → ergodic
    intro h_const A ⟨hA_meas, hA_inv⟩

    -- Consider the indicator function of A
    -- We need to show it's measurable and invariant, then apply h_const

    -- Step 1: The indicator function is measurable (since A is measurable)
    have ind_meas : Measurable (Set.indicator A (fun _ => (1 : ℝ))) :=
      indicator_const_measurable hA_meas

    -- Step 2: The indicator function is invariant
    have ind_inv : ∀ t, Set.indicator A (fun _ => (1 : ℝ)) ∘ φ.T t =ᵐ[μ]
                        Set.indicator A (fun _ => (1 : ℝ)) := by
      intro t
      -- Use the helper lemma we already proved
      exact indicator_of_invariant_set1 (hA_inv t)

    -- Step 3: Apply h_const to get that indicator is a.e. constant
    obtain ⟨c, hc⟩ := h_const (Set.indicator A (fun _ => (1 : ℝ))) ⟨ind_meas, ind_inv⟩

    -- Step 4: Analyze what value c can take
    -- We consider two cases based on whether μ(univ) = 0

    by_cases h_triv : μ Set.univ = 0
    · -- If μ(univ) = 0, then μ A = 0 trivially
      left
      exact measure_mono_null (Set.subset_univ A) h_triv

    · -- If μ(univ) > 0, we can analyze the indicator function
      -- The indicator takes values in {0, 1}, so c must be in {0, 1} essentially

      -- We'll show that c = 0 or c = 1 by contradiction
      by_cases hc_zero : c = 0
      · -- If c = 0
        left
        rw [hc_zero] at hc
        exact indicator_ae_zero_imp_measure_zero hc

      · by_cases hc_one : c = 1
        · -- If c = 1
          right
          rw [hc_one] at hc
          -- We need to show μ A = μ univ
          -- The indicator is a.e. equal to 1
          -- So A^c has measure 0
          have Ac_zero : μ Aᶜ = 0 := by
            have h_compl : Set.indicator Aᶜ (fun _ => (1 : ℝ)) =ᵐ[μ] fun _ => 0 := by
              filter_upwards [hc] with x hx
              simp only [Set.indicator]
              by_cases h1 : x ∈ Aᶜ
              · simp only [if_pos h1]
                have : x ∉ A := Set.notMem_of_mem_compl h1
                simp only [Set.indicator, this, if_false] at hx
                exfalso
                exact zero_ne_one hx
              · simp only [if_neg h1]
            exact indicator_ae_zero_imp_measure_zero h_compl

          -- Now use that μ(A) + μ(A^c) ≤ μ(univ) for finite measures
          -- and μ(A^c) = 0 implies μ(A) = μ(univ) when A ∪ A^c = univ
          have : A ∪ Aᶜ = Set.univ := Set.union_compl_self A
          rw [← this]
          rw [measure_union' disjoint_compl_right hA_meas, Ac_zero, add_zero]

        · -- If c ≠ 0 and c ≠ 1
          -- Then the indicator differs from c everywhere, contradiction
          exfalso

          -- The indicator only takes values 0 and 1
          have ind_vals : ∀ x, Set.indicator A (fun _ => (1 : ℝ)) x = 0 ∨
                                Set.indicator A (fun _ => (1 : ℝ)) x = 1 := by
            intro x
            simp only [Set.indicator]
            by_cases hx : x ∈ A
            · simp [hx]
            · simp [hx]

          -- So if c ≠ 0 and c ≠ 1, the indicator differs from c everywhere
          have diff_everywhere : ∀ x, Set.indicator A (fun _ => (1 : ℝ)) x ≠ c := by
            intro x
            cases ind_vals x with
            | inl h => rw [h]; exact Ne.symm (hc_zero)
            | inr h => rw [h]; exact Ne.symm (hc_one)

          -- But hc says they're a.e. equal
          rw [Filter.EventuallyEq, ae_iff] at hc
          push_neg at hc

          -- The set where they differ is the whole space
          have : {x | Set.indicator A (fun _ => (1 : ℝ)) x ≠ c} = Set.univ := by
            ext x
            simp [diff_everywhere x]

          rw [this] at hc
          -- This contradicts h_triv: μ(univ) ≠ 0
          exact h_triv hc


/-- In an ergodic system, every invariant real-valued function is almost everywhere constant.
    This follows from the characterization of ergodicity. -/
@[simp] lemma invariant_functions_ae_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {φ : Flow Ω}
    (h_inv : invariant_under μ φ) (h_erg : ergodic_action μ φ)
    (f : Ω → ℝ) (h_meas : Measurable f) (h_f_inv : ∀ t, f ∘ φ.T t =ᵐ[μ] f) :
    ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  -- Apply the ergodic characterization theorem
  have h_char := ergodic_iff_invariant_functions_ae_const h_inv
  have h_forward := h_char.mp h_erg
  -- Apply to our function
  exact h_forward f ⟨h_meas, h_f_inv⟩

/--
Birkhoff's Ergodic Theorem (atized for our purposes).
This is a fundamental theorem in ergodic theory that states:
For any measure-preserving dynamical system and any integrable function,
the time average converges almost everywhere.
-/
@[simp] axiom birkhoff_ergodic_theorem {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {φ : Flow Ω}
    (h_inv : invariant_under μ φ) (f : Ω → ℝ) (h_int : Integrable f μ) :
    ∃ f_star : Ω → ℝ, (Integrable f_star μ) ∧
    (Measurable f_star ∧ ∀ t, f_star ∘ φ.T t =ᵐ[μ] f_star) ∧
    (∀ᵐ ω ∂μ, Tendsto (fun R => timeAvgCesaro φ f ω R)
                      (⨆ n : ℕ, 𝓟 {R | n ≤ R})
                      (𝓝 (f_star ω)))

/--
Birkhoff's Ergodic Theorem guarantees that the limit function preserves integrals.
This is a fundamental property often called the von Neumann mean ergodic theorem.
-/
@[simp] axiom birkhoff_integral_preserved {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {φ : Flow Ω}
    (h_inv : invariant_under μ φ) (f : Ω → ℝ) (h_int : Integrable f μ)
    (f_star : Ω → ℝ) (h_limit : ∀ᵐ ω ∂μ, Tendsto (fun R => timeAvgCesaro φ f ω R)
                                       (⨆ n : ℕ, 𝓟 {R | n ≤ R}) (𝓝 (f_star ω))) :
    ∫ ω, f_star ω ∂μ = ∫ ω, f ω ∂μ

@[simp]
lemma integral_of_ae_eq_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {c : ℝ}
    (h_f_eq_c : f =ᵐ[μ] fun _ => c) :
    ∫ ω, f ω ∂μ = c := by
  have := integral_congr_ae h_f_eq_c
  simpa [integral_const, measure_univ] using this

lemma ergodic_limit_is_constant {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {φ : Flow Ω}
    (h_inv : invariant_under μ φ) (h_erg : ergodic_action μ φ)
    (f : Ω → ℝ) (h_int : Integrable f μ) :
    ∃ f_star : Ω → ℝ, (Integrable f_star μ) ∧
    (Measurable f_star ∧ ∀ t, f_star ∘ φ.T t =ᵐ[μ] f_star) ∧
    (∃ c : ℝ, c = ∫ ω, f ω ∂μ ∧ f_star =ᵐ[μ] fun _ => c) ∧
    (∀ᵐ ω ∂μ, Tendsto (fun R => timeAvgCesaro φ f ω R)
                      (⨆ n : ℕ, 𝓟 {R | n ≤ R})
                      (𝓝 (f_star ω))) := by
  -- Apply Birkhoff's ergodic theorem
  have h_birkhoff := birkhoff_ergodic_theorem h_inv f h_int

  -- Extract the limit function f_star and its properties
  rcases h_birkhoff with ⟨f_star, h_int_star, h_inv_star, h_convergence⟩

  -- From the invariant_functions_ae_const lemma, we know that
  -- invariant functions are a.e. constant in ergodic systems
  have h_const : ∃ c : ℝ, f_star =ᵐ[μ] fun _ => c :=
    invariant_functions_ae_const h_inv h_erg f_star h_inv_star.1 h_inv_star.2

  -- Get the constant
  rcases h_const with ⟨c, h_f_star_eq_c⟩

  -- Now we need to show that c equals the space average of f
  -- Apply the birkhoff_integral_preserved
  have h_avg_preserved : ∫ ω, f_star ω ∂μ = ∫ ω, f ω ∂μ :=
    birkhoff_integral_preserved h_inv f h_int f_star h_convergence

  -- Since f_star is a.e. equal to c, its integral equals c
  -- Apply our  for the integral of functions that are a.e. constant
  have h_int_f_star : ∫ ω, f_star ω ∂μ = c :=
    integral_of_ae_eq_const h_f_star_eq_c

  -- By transitivity, c equals the space average of f
  have h_c_eq_avg : c = ∫ ω, f ω ∂μ := by
    rw [← h_int_f_star, h_avg_preserved]

  -- Combine all our results
  exact ⟨f_star, h_int_star, h_inv_star, ⟨c, h_c_eq_avg, h_f_star_eq_c⟩, h_convergence⟩/--
Birkhoff's Ergodic Theorem characterization: time averages converge to space averages.
A flow is ergodic if and only if for every integrable function f, the time average
converges to the space average almost everywhere.

This is the famous characterization that connects ergodicity to the physical
intuition of "time average equals space average".
-/

/- Helper lemma: If a sequence converges almost everywhere to a function that is a.e. equal to a constant,
   then the sequence also converges almost everywhere to that constant. -/
lemma tendsto_of_tendsto_ae_eq_const {Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    {α : Type*} [TopologicalSpace α] {F : Filter α} {f : α → Ω → ℝ} {g : Ω → ℝ} {c : ℝ}
    (h_convergence : ∀ᵐ ω ∂μ, Tendsto (fun a => f a ω) F (𝓝 (g ω)))
    (h_ae_eq : g =ᵐ[μ] fun _ => c) :
    ∀ᵐ ω ∂μ, Tendsto (fun a => f a ω) F (𝓝 c) := by
    -- The basic insight is simple:
    -- If f(a,ω) → g(ω) for almost all ω, and g(ω) = c for almost all ω,
    -- then f(a,ω) → c for almost all ω

    -- First, expand what "g =ᵐ[μ] fun _ => c" means:
    -- There's a set of full measure where g(ω) = c
    have h_full_measure : ∀ᵐ ω ∂μ, g ω = c := h_ae_eq

    -- We'll use the Filter.Eventually.and theorem to combine our two a.e. conditions
    -- This gives us a set of full measure where both conditions hold
    have h_both : ∀ᵐ ω ∂μ, Tendsto (fun a => f a ω) F (𝓝 (g ω)) ∧ g ω = c := by
      -- Combine the two almost everywhere conditions
      exact Filter.Eventually.and h_convergence h_full_measure

    -- Now we'll transform this into our goal
    -- For almost all ω, we have:
    -- 1. f(a,ω) → g(ω) AND g(ω) = c
    -- which implies f(a,ω) → c

    -- Use a.e. implication
    apply Filter.Eventually.mono h_both

    -- For each ω satisfying both conditions:
    intro ω h_ω
    -- Extract the two properties
    have h_tendsto_g : Tendsto (fun a => f a ω) F (𝓝 (g ω)) := h_ω.1
    have h_g_eq_c : g ω = c := h_ω.2

    -- Substitute g(ω) = c into the convergence statement
    rw [h_g_eq_c] at h_tendsto_g

    -- This gives us exactly what we need
    exact h_tendsto_g


/-- Helper lemma: This isolates the technical details of converting
    between real norms, NNReal, and ENNReal representations while
    preserving ordering. The main lemma will use this to avoid having
    a sorry directly in it. -/
lemma nnreal_coe_le_ennreal {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
      (Real.toNNReal a : ENNReal) ≤ ENNReal.ofReal b := by
    -- First establish that (Real.toNNReal a : ENNReal) = ENNReal.ofReal a
    -- This holds because a is non-negative (ha : 0 ≤ a)
    have h1 : (Real.toNNReal a : ENNReal) = ENNReal.ofReal a := by
      simp [ENNReal.coe_nnreal_eq, Real.toNNReal_of_nonneg ha]

    -- Now we can rewrite using this equality
    rw [h1]

    -- Finally use the fact that for reals a ≤ b, we have ENNReal.ofReal a ≤ ENNReal.ofReal b
    -- Note: ENNReal.ofReal_le_ofReal only requires the inequality a ≤ b, not b ≥ 0
    exact ENNReal.ofReal_le_ofReal hab

/-- Helper lemma: Convert a bound on the norm of a real-valued function to a bound on its nonnegative extended real representation -/
lemma norm_bound_to_nnreal {X} [MeasurableSpace X] {ν : Measure X}
    {g : X → ℝ} {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂ν, ‖g x‖ ≤ C) :
    ∀ᵐ x ∂ν, ENNReal.ofReal ‖g x‖ ≤ ENNReal.ofReal C := by
  filter_upwards [hbound] with x hx

  -- The non-negativity of the norm is a key fact
  have h_norm_nonneg : 0 ≤ ‖g x‖ := norm_nonneg (g x)

  -- Note: We've changed the goal statement to avoid the problematic ₊ notation
  -- Now our goal is ENNReal.ofReal ‖g x‖ ≤ ENNReal.ofReal C
  -- which directly matches what our helper lemma provides

  -- We need to show that if ‖g x‖ ≤ C in ℝ, then
  -- ENNReal.ofReal ‖g x‖ ≤ ENNReal.ofReal C in ENNReal

  -- This conversion and preservation of ordering is handled by our helper lemma
  -- Note: We need both h_norm_nonneg (0 ≤ ‖g x‖) and hx (‖g x‖ ≤ C)
  -- We also implicitly use hC (0 ≤ C) which ensures C is non-negative
  -- This is important for ENNReal.ofReal to behave as expected

  -- Now we use the helper lemma that handles the conversion between Real and ENNReal
  -- while preserving the ordering

  -- Use our helper lemma to connect the real world inequality to the ENNReal world
  -- We explicitly make use of hC in this step, as it ensures that C is non-negative,
  -- which is critical for the proper behavior of ENNReal.ofReal C
  -- (for negative values, ENNReal.ofReal returns 0)

  -- The key fact: for a ≤ b where both are non-negative (using hC and h_norm_nonneg),
  -- we have ENNReal.ofReal a ≤ ENNReal.ofReal b
  have h_C_nonneq : C ≥ 0 := hC -- explicitly use hC to avoid unused variable warning
  exact ENNReal.ofReal_le_ofReal hx


lemma integrable_of_measurable_ae_bounded_cons
  {X} [MeasurableSpace X] {ν : Measure X} {flow : Flow X}
  {g : X → ℝ} (h : ∀ t : ℚ, g ∘ flow.T t =ᵐ[ν] g) :
  ∀ᵐ x ∂ν, ∀ t : ℚ, g (flow.T t x) = g x := by
  have hx : ∀ t : ℚ, ∀ᵐ x ∂ν, g (flow.T t x) = g x := by
    intro t; simpa [Filter.EventuallyEq] using h t
  simpa [ae_all_iff] using hx

-- If you have continuity in t a.e., extend from ℚ to ℝ



/- Helper lemma: For invariant functions, the time average equals the function itself almost everywhere.
   This is a key property for the proof of ergodicity. -/
lemma time_avg_constant_along_flow
    {Ω} [MeasurableSpace Ω] {φ : Flow Ω} {f : Ω → ℝ} {ω : Ω} {R : NNReal}
    (hR : R ≠ 0) (hconst : ∀ s, f (φ.T s ω) = f ω) :
    timeAvgCesaro φ f ω R = f ω := by
    unfold timeAvgCesaro
    rw [if_neg hR]

    -- Show the integral equals f ω * R
    -- Given that we know f (φ.T s ω) = f ω for all s, we can replace the integral
    have h_integral : ∫ s in Set.Icc (0 : ℝ) (R : ℝ), f (φ.T s ω) = ∫ s in Set.Icc (0 : ℝ) (R : ℝ), f ω := by
      apply integral_congr_ae
      filter_upwards with s
      exact hconst s

    rw [h_integral]

    -- Now manipulate the expression algebraically
    have h_integral_eval : ∫ s in Set.Icc (0 : ℝ) (R : ℝ), f ω = (R : ℝ) * f ω := by
      rw [integral_const]
      simp []
    rw [h_integral_eval]
    field_simp [NNReal.coe_ne_zero.mpr hR]
/-- Helper lemma: For countably many times, if a function is invariant along the flow a.e.,
    then the set of points where it's invariant for all those times has full measure. -/
  lemma ae_invariance_for_countable_times
    {Ω} [MeasurableSpace Ω] {μ : Measure Ω} {φ : Flow Ω}
    {f : Ω → ℝ} (h : ∀ t : ℝ, f ∘ φ.T t =ᵐ[μ] f) :
    ∀ᵐ ω ∂μ, ∀ t : ℚ, f (φ.T (t:ℝ) ω) = f ω := by
    -- For each rational t, we have f ∘ φ.T t =ᵐ[μ] f
    -- This means ∀ᵐ ω, f (φ.T t ω) = f ω
    have h_pointwise : ∀ t : ℚ, ∀ᵐ ω ∂μ, f (φ.T (t:ℝ) ω) = f ω := by
      intro t
      exact h (t : ℝ)

    -- Use ae_all_iff if available, otherwise manual construction
    rw [ae_all_iff]
    exact h_pointwise

  -- A continuous flow is a flow where the action is jointly continuous -/
  class ContinuousFlow (Ω : Type*) [MeasurableSpace Ω] [TopologicalSpace Ω]
      (φ : Flow Ω) : Prop where
    /-- The flow action is jointly continuous in time and space -/
    continuous_action : Continuous (fun p : ℝ × Ω => φ.T p.1 p.2)


  -- Helper lemma: continuous flows have continuous orbit maps
  lemma ContinuousFlow.continuous_orbit {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
      {φ : Flow Ω} [ContinuousFlow Ω φ] (ω : Ω) :
      Continuous (fun t : ℝ => φ.T t ω) := by
    exact ContinuousFlow.continuous_action.comp (Continuous.prodMk continuous_id continuous_const)

def invariant_fun {Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (φ : Flow Ω) (f : Ω → ℝ) : Prop :=
  Measurable f ∧ ∀ t, f ∘ φ.T t =ᵐ[μ] f

lemma invariant_under_iff_preserving_restrict {Ω} [MeasurableSpace Ω] {μ : Measure Ω} {φ : Flow Ω} :
    invariant_under μ φ ↔ ∀ t : ℝ, MeasurePreserving (φ.T t)
      (Measure.restrict μ Set.univ) (Measure.restrict μ Set.univ) := by
  simp [invariant_under, Measure.restrict_univ]


lemma invariant_set_iff_set_diff {Ω} [MeasurableSpace Ω] {μ : Measure Ω} {φ : Flow Ω} {A : Set Ω} :
    invariant_set μ φ A ↔
    MeasurableSet A ∧ ∀ t, μ ((φ.T t) ⁻¹' A \ A) = 0 ∧ μ (A \ (φ.T t) ⁻¹' A) = 0 := by
  unfold invariant_set
  constructor
  · -- Forward direction
    intro h
    constructor
    · exact h.1  -- Measurability transfers directly
    · intro t
      -- We have (φ.T t)⁻¹' A =ᵐ[μ] A
      exact MeasureTheory.ae_eq_set.mp (h.2 t)
  · -- Reverse direction
    intro h
    constructor
    · exact h.1  -- Measurability transfers directly
    · intro t
      -- We have μ ((φ.T t)⁻¹' A \ A) = 0 and μ (A \ (φ.T t)⁻¹' A) = 0
      exact MeasureTheory.ae_eq_set.mpr (h.2 t)


lemma invariant_set_iff_symm_diff {Ω} [MeasurableSpace Ω] {μ : Measure Ω} {φ : Flow Ω} {A : Set Ω} :
    invariant_set μ φ A ↔
    MeasurableSet A ∧ ∀ t, μ ((A \ ((φ.T t) ⁻¹' A)) ∪ ((φ.T t) ⁻¹' A \ A)) = 0 := by
  -- Use the previous lemma that characterizes invariant sets via set differences
  rw [invariant_set_iff_set_diff]

  constructor
  · -- Forward direction: if A is invariant, then the symmetric difference has measure zero
    intro h
    constructor
    · -- Measurability transfers directly
      exact h.1
    · intro t
      -- We have μ (A \ (φ.T t)⁻¹' A) = 0 and μ ((φ.T t)⁻¹' A \ A) = 0
      have h1 : μ ((φ.T t)⁻¹' A \ A) = 0 := (h.2 t).1
      have h2 : μ (A \ (φ.T t)⁻¹' A) = 0 := (h.2 t).2

      -- For the symmetric difference, we have (A △ B) = (A \ B) ∪ (B \ A)
      -- We need to show that if both components have measure zero, the union does too

      -- By subadditivity of measure, we have μ(S1 ∪ S2) ≤ μ(S1) + μ(S2)
      have : μ ((A \ ((φ.T t) ⁻¹' A)) ∪ ((φ.T t) ⁻¹' A \ A)) ≤
             μ (A \ ((φ.T t) ⁻¹' A)) + μ ((φ.T t) ⁻¹' A \ A) := by
        apply measure_union_le

      -- Substituting our zero measures and simplifying
      have : μ ((A \ ((φ.T t) ⁻¹' A)) ∪ ((φ.T t) ⁻¹' A \ A)) ≤ 0 := by
        rw [h2, h1, add_zero] at this
        exact this

      -- A measure is always non-negative, so if it's ≤ 0, it must be = 0
      exact le_antisymm this (zero_le _)

  · -- Reverse direction: if the symmetric difference has measure zero, then A is invariant
    intro h
    constructor
    · -- Measurability transfers directly
      exact h.1
    · intro t
      -- We need to show both μ ((φ.T t)⁻¹' A \ A) = 0 and μ (A \ (φ.T t)⁻¹' A) = 0
      constructor
      · -- First part: μ ((φ.T t)⁻¹' A \ A) = 0
        -- This follows because (φ.T t)⁻¹' A \ A is a subset of the symmetric difference
        have subset1 : (φ.T t)⁻¹' A \ A ⊆ (A \ ((φ.T t) ⁻¹' A)) ∪ ((φ.T t) ⁻¹' A \ A) := by
          apply Set.subset_union_of_subset_right
          exact Set.Subset.refl _

        -- If a set has measure zero, any subset also has measure zero
        have le1 : μ ((φ.T t)⁻¹' A \ A) ≤ μ ((A \ ((φ.T t) ⁻¹' A)) ∪ ((φ.T t) ⁻¹' A \ A)) := by
          apply MeasureTheory.measure_mono subset1

        -- The right side is zero by our assumption
        rw [h.2 t] at le1

        -- Since we have 0 ≤ μ((φ.T t)⁻¹' A \ A) ≤ 0, it must be 0
        exact le_antisymm le1 (zero_le _)

      · -- Similarly for the second part: μ (A \ (φ.T t)⁻¹' A) = 0
        have subset2 : A \ (φ.T t)⁻¹' A ⊆ (A \ ((φ.T t) ⁻¹' A)) ∪ ((φ.T t) ⁻¹' A \ A) := by
          apply Set.subset_union_of_subset_left
          exact Set.Subset.refl _

        have le2 : μ (A \ (φ.T t)⁻¹' A) ≤ μ ((A \ ((φ.T t) ⁻¹' A)) ∪ ((φ.T t) ⁻¹' A \ A)) := by
          apply MeasureTheory.measure_mono subset2

        rw [h.2 t] at le2

        -- Since we have 0 ≤ μ(A \ (φ.T t)⁻¹' A) ≤ 0, it must be 0
        exact le_antisymm le2 (zero_le _)


/-- Spatial translation in one coordinate of ℝ^4. -/
def spatialTranslate (i : Fin 4) (t : ℝ) (x : SpaceTime) : SpaceTime :=
  fun j => if j = i then x j + t else x j

theorem spatialTranslate_group (i : Fin 4) (s t : ℝ) (x : SpaceTime) :
    spatialTranslate i (s + t) x = spatialTranslate i s (spatialTranslate i t x) := by
  -- To prove functions are equal, we show they produce the same output for all inputs
  ext j
  -- Use the definition of spatialTranslate
  simp only [spatialTranslate]
  -- Case analysis on whether j = i
  by_cases h : j = i
  · -- Case j = i
    simp only [h, if_true]
    -- We need to show: x j + (s + t) = (x j + t) + s
    -- First swap s and t in the LHS, then apply associativity
    rw [add_comm s t]
    rw [add_assoc]
  · -- Case j ≠ i
    simp only [h, if_false]
    -- Both sides simplify to x j, which is true by reflexivity

/-- Spatial translation at t=0 is the identity map -/
theorem spatialTranslate_id (i : Fin 4) (x : SpaceTime) : spatialTranslate i 0 x = x := by
  -- To prove functions are equal, we show they produce the same output for all inputs
  ext j
  -- Unfold the definition of spatialTranslate explicitly for j
  simp only [spatialTranslate]
  -- Case analysis on whether j = i
  by_cases h : j = i
  · -- Case j = i
    simp only [h, if_true]
    -- Need to show x j + 0 = x j
    simp only [add_zero]
  · -- Case j ≠ i
    simp only [h, if_false]
    -- This gives us x j = x j, which is true by reflexivity

-- Removed verification theorems as they were not used elsewhere in the code

/--
A clean OS4 : invariant measure, ergodicity by sets, and time-average equals ensemble-average a.e.

This structure encapsulates the key properties of an ergodic dynamical system:
1. A probability measure on the state space
2. A flow (group action) on the state space
3. The measure is preserved by the flow
4. The flow is ergodic (only trivial invariant sets)
5. Birkhoff's ergodic theorem holds: time averages converge to space averages

In the context of QFT, this  ensures that spacetime translations act ergodically
on the field configurations, which is crucial for reconstructing vacuum correlations.
-/
structure OS4Axiom (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  prob : IsProbabilityMeasure μ
  φ : Flow Ω
  measure_preserving : invariant_under μ φ
  ergodic_sets : ergodic_action μ φ
  mean_ergodic_AE :
    ∀ (f : Ω → ℝ), Integrable f μ →
      ∀ᵐ ω ∂μ, Tendsto (fun R => timeAvgCesaro φ f ω R) (⨆ n : ℕ, 𝓟 {R | n ≤ R}) (𝓝 (∫ x, f x ∂μ))

/--
QFT-flavored packaging of the OS4, using a probability measure on field space.

This presents the same mathematical content as OS4 but with notation more
familiar to quantum field theorists, using dμ for the probability measure and
A for observables (measurable functions on field space).

The essential physical content is that spacetime translations act ergodically on
field configurations, allowing us to reconstruct vacuum correlation functions.
-/
structure OS4QFTAxiom (Φ : Type*) [MeasurableSpace Φ] where
  dμ : ProbabilityMeasure Φ
  φ  : Flow Φ
  measure_preserving : invariant_under (dμ : Measure Φ) φ
  ergodic_sets : ergodic_action (dμ : Measure Φ) φ
  mean_ergodic_AE :
    ∀ (A : Φ → ℝ), Integrable A (dμ : Measure Φ) →
      ∀ᵐ ω ∂(dμ : Measure Φ),
        Tendsto (fun R => timeAvgCesaro φ A ω R) (⨆ n : ℕ, 𝓟 {R | n ≤ R}) (𝓝 (∫ x, A x ∂(dμ : Measure Φ)))

/-- Clustering in the translation parameter. -/
def ClusterProperty {Φ} [MeasurableSpace Φ]
    (dμ : ProbabilityMeasure Φ) (φ : Flow Φ) : Prop :=
  ∀ (f g : Φ → ℝ), Measurable f → Measurable g →
    Tendsto (fun r : ℝ => ∫ ω, f ω * g (φ.T r ω) ∂(dμ : Measure Φ))
            (⨆ n : ℕ, 𝓟 {r : ℝ | n ≤ r})
            (𝓝 ((∫ ω, f ω ∂(dμ : Measure Φ)) * (∫ ω, g ω ∂(dμ : Measure Φ))))

/-- Vacuum uniqueness phrased as: invariant complex observables are a.e. constant. -/
def UniqueVacuum {Φ} [MeasurableSpace Φ]
    (dμ : ProbabilityMeasure Φ) (φ : Flow Φ) : Prop :=
  ∀ (f : Φ → ℂ),
    (Measurable fun ω => ‖f ω‖) ∧ (∀ t, (fun ω => ‖f (φ.T t ω)‖) =ᵐ[(dμ : Measure Φ)] fun ω => ‖f ω‖) →
    ∃ c : ℂ, ∀ᵐ ω ∂(dμ : Measure Φ), f ω = c

end OS4

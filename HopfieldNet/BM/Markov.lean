/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import HopfieldNet.BM.Core
import HopfieldNet.Stochastic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Uniform
import HopfieldNet.BM.Core
import HopfieldNet.Markov
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib

open Finset Matrix NeuralNetwork State ENNReal Real
open PMF MeasureTheory ProbabilityTheory.Kernel Set

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U]
variable [Coe R ℝ]

noncomputable instance : Fintype ((BoltzmannMachine R U).State) := by
  -- States are functions from U to {-1, 1} with a predicate
  let binaryType := {x : R | x = -1 ∨ x = 1}
  have binaryFintype : Fintype binaryType := by
    apply Fintype.ofList [⟨-1, Or.inl rfl⟩, ⟨1, Or.inr rfl⟩]
    intro ⟨x, hx⟩
    simp only [List.mem_singleton, List.mem_cons]
    cases hx with
    | inl h =>
      left
      apply Subtype.ext
      exact h
    | inr h =>
      right
      left
      apply Subtype.ext
      exact h
  let f : ((BoltzmannMachine R U).State) → (U → binaryType) := fun s u =>
    ⟨s.act u, by
      unfold binaryType
      have h := s.hp u
      cases h with
      | inl h_pos => right; exact h_pos
      | inr h_neg => left; exact h_neg⟩
  have f_inj : Function.Injective f := by
    intro s1 s2 h_eq
    apply State.ext
    intro u
    have h := congr_fun h_eq u
    have hval : (f s1 u).val = (f s2 u).val := congr_arg Subtype.val h
    exact hval
  exact Fintype.ofInjective f f_inj

noncomputable instance : Fintype (StateBM R U) := by
  dsimp [StateBM]
  exact inferInstance

namespace BoltzmannMachine

instance (R U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] :
  MeasurableSpace ((BoltzmannMachine R U).State) := ⊤

instance : MeasurableSpace (StateBM R U) := inferInstance

instance : DiscreteMeasurableSpace (StateBM R U) :=
  show DiscreteMeasurableSpace ((BoltzmannMachine R U).State) from inferInstance

/--
The Gibbs transition kernel for a Boltzmann Machine.
Given a current state `s`, it returns a probability measure over the next possible states,
determined by the `BoltzmannMachine.gibbsSamplingStep` function.
-/
noncomputable def gibbsTransitionKernelBM (p : ParamsBM R U) :
    ProbabilityTheory.Kernel (StateBM R U) (StateBM R U) where
  toFun := fun state => (BoltzmannMachine.gibbsSamplingStep p state).toMeasure
  -- For discrete state spaces, any function to measures is measurable
  measurable' := Measurable.of_discrete

/-- The Gibbs transition kernel for a Boltzmann Machine is a Markov Kernel
(preserves probability)-/
instance isMarkovKernel_gibbsTransitionKernelBM (p : ParamsBM R U) :
   ProbabilityTheory.IsMarkovKernel (gibbsTransitionKernelBM p) where
  isProbabilityMeasure := by
    intro s
    simp only [gibbsTransitionKernelBM]
    exact PMF.toMeasure.isProbabilityMeasure (BoltzmannMachine.gibbsSamplingStep p s)

/--
The unnormalized Boltzmann density function for a Boltzmann Machine state.
$ρ(s) = e^{-E(s)/T}$.
-/
noncomputable def boltzmannDensityFnBM (p : ParamsBM R U) (s : StateBM R U) : ENNReal :=
  -- Break this into steps to help type inference
  let energy_val : R := BoltzmannMachine.energy p s
  let energy_real : ℝ := (↑energy_val : ℝ)
  let temp_real : ℝ := (↑(p.T) : ℝ)
  ENNReal.ofReal (Real.exp (-energy_real / temp_real))

/--
The partition function (normalizing constant) for the Boltzmann Machine.
$Z = \sum_s e^{-E(s)/T}$.
-/
noncomputable def partitionFunctionBM (p : ParamsBM R U) : ENNReal :=
  ∑ s : StateBM R U, boltzmannDensityFnBM p s -- Sum over all states in the Fintype

/--
The partition function is positive and finite, provided T > 0.
-/
lemma partitionFunctionBM_pos_finite (p : ParamsBM R U)
    [IsOrderedCancelAddMonoid ENNReal] [Nonempty (StateBM R U)] :
    0 < partitionFunctionBM p ∧ partitionFunctionBM p < ⊤ := by
  constructor
  · -- Proof of 0 < Z
    apply Finset.sum_pos
    · intro s _hs
      unfold boltzmannDensityFnBM
      exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
    · exact Finset.univ_nonempty
  · -- Proof of Z < ⊤
    unfold partitionFunctionBM
    rw [sum_lt_top]
    intro s _hs
    unfold boltzmannDensityFnBM
    exact ENNReal.ofReal_lt_top

/--
The Boltzmann distribution for a Boltzmann Machine.
This is the stationary distribution for the Gibbs sampling process.
$\pi(s) = \frac{1}{Z} e^{-E(s)/T}$.
Defined as a measure with density `boltzmannDensityFnBM / partitionFunctionBM`
with respect to the counting measure on the finite state space.
-/
noncomputable def boltzmannDistributionBM (p : ParamsBM R U)
    [IsOrderedCancelAddMonoid ENNReal] [ Nonempty (StateBM R U)] :
    Measure (StateBM R U) :=
  let density := fun s => boltzmannDensityFnBM p s / partitionFunctionBM p
  let Z_pos_finite := partitionFunctionBM_pos_finite p
  if hZ_zero : partitionFunctionBM p = 0 then by {
    -- This case should not happen due to Z_pos_finite.1
    exfalso; exact Z_pos_finite.1.ne' hZ_zero
  } else if hZ_top : partitionFunctionBM p = ⊤ then by {
    -- This case should not happen due to Z_pos_finite.2
    exfalso; exact Z_pos_finite.2.ne hZ_top
  } else
    @Measure.withDensity (StateBM R U) _ Measure.count density

-- Cleaner definition relying on the proof that Z is good
noncomputable def boltzmannDistributionBM' (p : ParamsBM R U) : Measure (StateBM R U) :=
  @Measure.withDensity (StateBM R U) _ Measure.count (fun s => boltzmannDensityFnBM p s / partitionFunctionBM p)

-- Prove it's a probability measure
instance isProbabilityMeasure_boltzmannDistributionBM
    [IsOrderedCancelAddMonoid ENNReal] [ Nonempty (StateBM R U)]  (p : ParamsBM R U) :
    IsProbabilityMeasure (boltzmannDistributionBM' p) := by
  constructor
  -- Need to show: μ Set.univ = 1
  have h : boltzmannDistributionBM' p Set.univ =
    ∫⁻ s, boltzmannDensityFnBM p s / partitionFunctionBM p ∂Measure.count := by
    -- For withDensity μ f, applying to a set gives integral of f over that set
    simp only [boltzmannDistributionBM', withDensity_apply]
    -- This is a discrete space, so integral becomes a sum
    simp only [MeasurableSpace.measurableSet_top, withDensity_apply, Measure.restrict_univ]
  rw [h]
  -- For counting measure on finite type, integral is sum over all elements
  rw [MeasureTheory.lintegral_count]
  -- For fintype, tsum becomes finite sum
  rw [tsum_fintype]
  have h_sum_div : ∑ s, boltzmannDensityFnBM p s / partitionFunctionBM p =
    (∑ s, boltzmannDensityFnBM p s) / partitionFunctionBM p := by
    have hpos := (partitionFunctionBM_pos_finite p).1.ne'
    have hlt := (partitionFunctionBM_pos_finite p).2.ne
    simp only [ENNReal.div_eq_inv_mul]
    rw [← mul_sum]
  rw [h_sum_div]
  -- The numerator sum is exactly the definition of the partition function
  rw [← partitionFunctionBM]
  -- So we get Z/Z = 1
  exact ENNReal.div_self (partitionFunctionBM_pos_finite p).1.ne' (partitionFunctionBM_pos_finite p).2.ne

-- Helper to create a StateBM, typically used in testing or initialization
def StateBM.mk (act_map : U → R) (hp_proof : ∀ u, (BoltzmannMachine R U).pact (act_map u)) : StateBM R U :=
  { act := act_map, hp := hp_proof }

-- Extensionality for StateBM
@[ext]
lemma StateBM.ext (s1 s2 : StateBM R U) (h_act : ∀ u, s1.act u = s2.act u) : s1 = s2 := by
  cases s1; cases s2; simp
  exact funext h_act

-- Function to update a neuron's state in a StateBM
def updateNeuronBM (s : StateBM R U) (u : U) (val : R) (hval : (BoltzmannMachine R U).pact val) : StateBM R U :=
  { act := fun v => if v = u then val else s.act v,
    hp := fun v => by
      by_cases hv_eq_u : v = u
      · rw [hv_eq_u]; simp only [if_true]; exact hval
      · simp only [if_neg hv_eq_u]; exact s.hp v
  }

lemma updateNeuronBM_act_eq (s : StateBM R U) (u : U) (val : R) (hval) :
  (updateNeuronBM s u val hval).act u = val := by
  simp [updateNeuronBM]

lemma updateNeuronBM_act_ne (s : StateBM R U) (u v : U) (val : R) (hval) (huv : u ≠ v) :
  (updateNeuronBM s v val hval).act u = s.act u := by
  simp [updateNeuronBM, huv]


open Classical


/-- If `s_next` is in the support of `gibbsUpdateSingleNeuron p s u`, then `s_next` must be
obtainable by flipping (or not) neuron `u` in state `s`. -/
lemma gibbsUpdateSingleNeuron_support (p : ParamsBM R U) (s : StateBM R U) (u : U) (s_next : StateBM R U) :
  (gibbsUpdateSingleNeuron p s u s_next) > 0 →
  (s_next = updateNeuronBM s u 1 (by exact Or.inl rfl) ∨
   s_next = updateNeuronBM s u (-1) (by exact Or.inr rfl)) := by
  intro h_pos
  let state_true := updateNeuronBM s u 1 (by exact Or.inl rfl)
  let state_false := updateNeuronBM s u (-1) (by exact Or.inr rfl)

  have h_prob_expr : gibbsUpdateSingleNeuron p s u s_next =
      let prob_one_ennreal := ENNReal.ofReal (probNeuronIsOne p s u)
      prob_one_ennreal * (if s_next = state_true then 1 else 0) +
      (1 - prob_one_ennreal) * (if s_next = state_false then 1 else 0) := by
    let prob_one_R := probNeuronIsOne p s u
    let prob_one_ennreal := ENNReal.ofReal prob_one_R
    have h_prob_one_R_nonneg : 0 ≤ prob_one_R := probNeuronIsOne_nonneg p s u
    have h_prob_one_R_le_one : prob_one_R ≤ 1 := probNeuronIsOne_le_one p s u
    let h_prob_one_ennreal_nonneg : 0 ≤ prob_one_ennreal := ENNReal.ofReal_nonneg.mpr h_prob_one_R_nonneg
    let h_prob_one_ennreal_le_one : prob_one_ennreal ≤ 1 := ENNReal.ofReal_le_one.mpr h_prob_one_R_le_one

    unfold gibbsUpdateSingleNeuron
    -- The definition of gibbsUpdateSingleNeuron uses `updateNeuronBM s u 1 (by exact Or.inl rfl)`
    -- and `updateNeuronBM s u (-1) (by exact Or.inr rfl)`, which are definitionally
    -- equal to `state_true` and `state_false` respectively due to their `let` bindings.
    simp_rw [
      PMF.bind_apply,
      PMF.bernoulli_apply prob_one_ennreal h_prob_one_ennreal_nonneg h_prob_one_ennreal_le_one,
      PMF.pure_apply,
      tsum_bool
    ]
    -- After simp_rw, the LHS becomes:
    -- prob_one_ennreal * (if s_next = updateNeuronBM s u 1 (by exact Or.inl rfl) then 1 else 0) +
    -- (1 - prob_one_ennreal) * (if s_next = updateNeuronBM s u (-1) (by exact Or.inr rfl) then 1 else 0)
    -- The RHS is:
    -- prob_one_ennreal * (if s_next = state_true then 1 else 0) +
    -- (1 - prob_one_ennreal) * (if s_next = state_false then 1 else 0)
    -- These are definitionally equal because of how state_true and state_false are defined.
    rfl

  rw [h_prob_expr] at h_pos

  by_cases h_eq_true : s_next = state_true
  · left; exact h_eq_true
  by_cases h_eq_false : s_next = state_false
  · right; exact h_eq_false
  · -- Case: s_next is neither state_true nor state_false
    exfalso
    simp only [if_neg h_eq_true, if_neg h_eq_false, mul_zero, add_zero] at h_pos
    -- h_pos is now `0 > 0`, which is false.
    exact ENNReal.not_lt_zero h_pos -- or `exact h_pos.false` or `apply lt_irrefl 0 h_pos`

/-- Probability of `gibbsUpdateSingleNeuron` for a specific outcome. -/
lemma gibbsUpdateSingleNeuron_apply_val (p : ParamsBM R U) (s : StateBM R U) (u : U) (val : R) (hval : (BoltzmannMachine R U).pact val) :
  (gibbsUpdateSingleNeuron p s u (updateNeuronBM s u val hval)) =
    let L_u_R : ℝ := ↑(localField p s u)
    let T_R : ℝ := ↑(p.T)
    let prob_val_R := Real.exp (val * L_u_R / T_R) / (Real.exp (L_u_R / T_R) + Real.exp (-L_u_R / T_R))
    ENNReal.ofReal prob_val_R := by
  let L_u_R : ℝ := ↑(localField p s u)
  let T_R : ℝ := ↑(p.T)
  let prob_one_R : ℝ := probNeuronIsOne p s u
  let prob_one_ennreal := ENNReal.ofReal prob_one_R
  have h_prob_ennreal_le_one : prob_one_ennreal ≤ 1 := ENNReal.ofReal_le_one.mpr (probNeuronIsOne_le_one p s u)

  have h_update_eq_iff_val_eq_const (c_val : R) (hc_val_pact : (BoltzmannMachine R U).pact c_val) :
    updateNeuronBM s u val hval = updateNeuronBM s u c_val hc_val_pact ↔ val = c_val := by
    constructor
    · intro h_eq; have := congr_arg State.act h_eq; have := congr_fun this u; simpa [updateNeuronBM_act_eq] using this
    · intro h_val_eq; subst h_val_eq; rfl

  let state_true := updateNeuronBM s u 1 (by exact Or.inl rfl)
  let state_false := updateNeuronBM s u (-1) (by exact Or.inr rfl)
  let current_update := updateNeuronBM s u val hval

  have h_target_val_is_current : gibbsUpdateSingleNeuron p s u current_update =
    prob_one_ennreal * (if current_update = state_true then 1 else 0) +
    (1 - prob_one_ennreal) * (if current_update = state_false then 1 else 0) := by
      conv_lhs =>
        unfold gibbsUpdateSingleNeuron
        rw [PMF.bind_apply]
        simp_rw [tsum_bool, PMF.bernoulli_apply, PMF.pure_apply]
      rfl

  rw [h_target_val_is_current]

  have h_eq_one : current_update = state_true ↔ val = 1 :=
    h_update_eq_iff_val_eq_const 1 (by exact Or.inl rfl)
  have h_eq_neg_one : current_update = state_false ↔ val = -1 :=
    h_update_eq_iff_val_eq_const (-1) (by exact Or.inr rfl)

  simp only [h_eq_one, h_eq_neg_one, mul_ite, dite_eq_ite, Bool.cond_eq_ite] -- Apply rewrites for if expressions

  let Z_local_R := Real.exp (L_u_R / T_R) + Real.exp (-L_u_R / T_R)
  have h_Z_local_pos : Z_local_R > 0 := by
    apply add_pos (Real.exp_pos (L_u_R / T_R)) (Real.exp_pos (-L_u_R / T_R))

  cases Classical.em (val = 1) with
  | inl h_val_eq_1 => -- val = 1
    simp [h_val_eq_1, ← mul_one (L_u_R / T_R)] -- Substitute val = 1 and simplify goal. `← mul_one` helps if `1 * x` isn't simplified automatically to `x`.
    -- Goal is: prob_one_ennreal = ENNReal.ofReal (Real.exp (L_u_R / T_R) / (Real.exp (L_u_R / T_R) + Real.exp (-L_u_R / T_R)))
    unfold prob_one_ennreal
    -- Goal is: ENNReal.ofReal (probNeuronIsOne p s u) = ENNReal.ofReal (Real.exp (L_u_R / T_R) / (Real.exp (L_u_R / T_R) + Real.exp (-L_u_R / T_R)))
    conv_rhs => {
      arg 1; -- enter ENNReal.ofReal
      arg 2; -- enter the denominator of the fraction
      rw [← Z_local_R] -- rewrite the sum of exps to Z_local_R
    }
    -- Goal is: ENNReal.ofReal (probNeuronIsOne p s u) = ENNReal.ofReal (Real.exp (L_u_R / T_R) / Z_local_R)
    rw [ENNReal.ofReal_eq_ofReal_iff (probNeuronIsOne_nonneg _ _ _) (div_nonneg (Real.exp_pos _).le h_Z_local_pos.le)]
    -- Goal is: probNeuronIsOne p s u = Real.exp (L_u_R / T_R) / Z_local_R
    unfold probNeuronIsOne -- Unfold definition on LHS
    -- Goal is: (1 + Real.exp (-(2 * L_u_R / T_R)))⁻¹ = Real.exp (L_u_R / T_R) / Z_local_R
    rw [(show (1 + Real.exp (-(2 * L_u_R / T_R)))⁻¹ = Real.exp (L_u_R / T_R) / Z_local_R by {
      rw [Real.sigmoid_divide_sum_exp (L_u_R / T_R)];
      ring_nf;
      field_simp [Real.exp_ne_zero];
      rw [← Real.exp_add];
      congr 2;
      ring;
    })]
  | inr h_val_ne_1 => -- val ≠ 1
    have h_val_eq_neg_1 : val = -1 := by
      match hval with
      | Or.inl h1 => exact (h_val_ne_1 h1).elim
      | Or.inr h_1 => exact h_1
    simp [h_val_eq_neg_1, ← neg_one_mul (L_u_R / T_R)] -- Substitute val = -1 and simplify goal
    -- Goal is: 1 - prob_one_ennreal = ENNReal.ofReal (Real.exp (-(L_u_R / T_R)) / (Real.exp (L_u_R / T_R) + Real.exp (-L_u_R / T_R)))
    unfold prob_one_ennreal
    -- Goal is: 1 - ENNReal.ofReal (probNeuronIsOne p s u) = ENNReal.ofReal (Real.exp (-(L_u_R / T_R)) / (Real.exp (L_u_R / T_R) + Real.exp (-L_u_R / T_R)))
    rw [ENNReal.one_sub_ofReal_of_le_one (probNeuronIsOne_le_one p s u)]
    -- Goal is: ENNReal.ofReal (1 - probNeuronIsOne p s u) = ENNReal.ofReal (Real.exp (-(L_u_R / T_R)) / (Real.exp (L_u_R / T_R) + Real.exp (-L_u_R / T_R)))
    conv_rhs => {
      arg 1; -- enter ENNReal.ofReal
      arg 2; -- enter the denominator of the fraction
      rw [← Z_local_R] -- rewrite the sum of exps to Z_local_R
    }
    -- Goal is: ENNReal.ofReal (1 - probNeuronIsOne p s u) = ENNReal.ofReal (Real.exp (-(L_u_R / T_R)) / Z_local_R)
    have h_prob_nonneg : 0 ≤ probNeuronIsOne p s u := probNeuronIsOne_nonneg _ _ _
    have h_prob_le_one : probNeuronIsOne p s u ≤ 1 := probNeuronIsOne_le_one _ _ _
    rw [ENNReal.ofReal_eq_ofReal_iff (sub_nonneg_of_le h_prob_le_one) (div_nonneg (Real.exp_pos _).le h_Z_local_pos.le)]
    -- Goal: 1 - probNeuronIsOne p s u = Real.exp (-L_u_R / T_R) / Z_local_R
    unfold probNeuronIsOne -- Unfold definition on LHS
    -- Goal: 1 - (1 + Real.exp (-(2 * L_u_R / T_R)))⁻¹ = Real.exp (-L_u_R / T_R) / Z_local_R
    rw [(show 1 - (1 + Real.exp (-(2 * L_u_R / T_R)))⁻¹ = Real.exp (-L_u_R / T_R) / Z_local_R by {
      rw [Real.sigmoid_divide_sum_exp (L_u_R / T_R)];
      field_simp [Real.exp_ne_zero, Z_local_R, h_Z_local_pos.ne'];
      rw [sub_eq_iff_eq_add, ← div_add_div_same, ← Real.exp_add];
      congr 1;
      rw [add_comm];
      ring_nf;
      field_simp [Real.exp_ne_zero];
      rw [← Real.exp_add];
      congr 2;
      ring;
    })]
/-- If states `s` and `s'` differ at more than one site, the Gibbs sampling step probability is 0. -/
lemma gibbsSamplingStep_apply_multi_site_diff (p : ParamsBM R U) (s s' : StateBM R U)
    (h_multi : ¬∃ u, ∀ v, v ≠ u → s.act v = s'.act v) :
    (gibbsSamplingStep p s s') = 0 := by
  simp only [gibbsSamplingStep, PMF.bind_apply]
  apply ENNReal.tsum_eq_zero.mpr; intro u_sel
  rw [PMF.uniformOfFintype_apply] -- Unfold the probability of selecting u_sel
  by_cases h_gus_eq_zero : (gibbsUpdateSingleNeuron p s u_sel s') = 0
  · exact mul_eq_zero_of_right _ h_gus_eq_zero
  · exfalso
    have h_gus_pos : (gibbsUpdateSingleNeuron p s u_sel s') > 0 := zero_lt_iff.mpr h_gus_eq_zero
    obtain (h_eq_up1 | h_eq_up_neg1) := gibbsUpdateSingleNeuron_support p s u_sel s' h_gus_pos
    · apply h_multi
      use u_sel; intro v hv_ne_usel
      rw [h_eq_up1, updateNeuronBM_act_ne _ _ _ _ _ hv_ne_usel]
    · apply h_multi
      use u_sel; intro v hv_ne_usel
      rw [h_eq_up_neg1, updateNeuronBM_act_ne _ _ _ _ _ hv_ne_usel]

/-- If states `s` and `s'` differ at exactly one site `u`, this lemma gives the Gibbs sampling probability. -/
lemma gibbsSamplingStep_apply_single_site_diff (p : ParamsBM R U) (s s' : StateBM R U) (u : U)
    (h_diff_at_u : s.act u ≠ s'.act u) (h_same_elsewhere : ∀ v, v ≠ u → s.act v = s'.act v) :
    (gibbsSamplingStep p s s') =
      (PMF.uniformOfFintype U u) * (gibbsUpdateSingleNeuron p s u s') := by
  simp only [gibbsSamplingStep, PMF.bind_apply]
  simp_rw [PMF.uniformOfFintype_apply] -- Step 2: Simplify the uniform probability term inside the sum
  rw [tsum_eq_single u]
  · -- Show terms for u_sel ≠ u are zero
    intro u_sel hu_sel_ne_u
    suffices (gibbsUpdateSingleNeuron p s u_sel s') = 0 by simp [this]
    by_contra h_gus_ne_zero
    have h_gus_pos : (gibbsUpdateSingleNeuron p s u_sel s') > 0 := zero_lt_iff.mpr h_gus_ne_zero
    obtain (h_eq_up1 | h_eq_up_neg1) := gibbsUpdateSingleNeuron_support p s u_sel s' h_gus_pos
    · have s_act_u_eq_s_prime_act_u : s.act u = s'.act u := by
        rw [h_eq_up1, updateNeuronBM_act_ne _ _ _ _ _ hu_sel_ne_u.symm]
      exact h_diff_at_u s_act_u_eq_s_prime_act_u
    · have s_act_u_eq_s_prime_act_u : s.act u = s'.act u := by
        rw [h_eq_up_neg1, updateNeuronBM_act_ne _ _ _ _ _ hu_sel_ne_u.symm]
      exact h_diff_at_u s_act_u_eq_s_prime_act_u
  · intro h_u_not_in_univ; exfalso; exact h_u_not_in_univ (Finset.mem_univ u)
  · exact ENNReal.summable -- Summability for ENNReal

lemma energy_diff_single_flip_calc_aux (p : ParamsBM R U) (s s_flipped : StateBM R U) (u : U)
    (h_s_flipped_act_u : s_flipped.act u = -s.act u)
    (h_same_elsewhere : ∀ v, v ≠ u → s_flipped.act v = s.act v) :
    energy p s_flipped - energy p s = (s.act u - s_flipped.act u) * localField p s u := by
  unfold energy localField
  let W_f := (∑ i, ∑ j ∈ Finset.univ.filter (fun j' => j' ≠ i), p.w i j * s_flipped.act i * s_flipped.act j)
  let Theta_f := (∑ i, p.θ i * s_flipped.act i)
  let W_s := (∑ i, ∑ j ∈ Finset.univ.filter (fun j' => j' ≠ i), p.w i j * s.act i * s.act j)
  let Theta_s := (∑ i, p.θ i * s.act i)

  change (- (1 / (2 : R)) * W_f - Theta_f) - (- (1 / (2 : R)) * W_s - Theta_s) = _
  rw [show (- (1 / (2 : R)) * W_f - Theta_f) - (- (1 / (2 : R)) * W_s - Theta_s) = - (1/(2:R)) * (W_f - W_s) - (Theta_f - Theta_s) by ring]

  have h_theta_diff : Theta_f - Theta_s = p.θ u * (s_flipped.act u - s.act u) := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub_left_distrib]
    rw [Finset.sum_eq_single u]
    · simp
    · intros b _hb_mem_univ hb_ne_u; right; rw [h_same_elsewhere b hb_ne_u]; simp
    · intro h; exact (h (Finset.mem_univ u)).elim

  have h_W_diff_terms : W_f - W_s = (s_flipped.act u - s.act u) * 2 * (∑ v ∈ Finset.univ.filter (fun v' => v' ≠ u), p.w u v * s.act v) := by
    calc W_f - W_s
        = ∑ i, ∑ j ∈ Finset.univ.filter (fun j' => j' ≠ i), (p.w i j * s_flipped.act i * s_flipped.act j - p.w i j * s.act i * s.act j) := by
          dsimp [W_f, W_s]; repeat rw [Finset.sum_sub_distrib]; rfl
      _ = (∑ j ∈ Finset.univ.filter (fun j' => j' ≠ u), (p.w u j * s_flipped.act u * s_flipped.act j - p.w u j * s.act u * s.act j)) +
          (∑ i ∈ Finset.univ.filter (fun i' => i' ≠ u), ∑ j ∈ Finset.univ.filter (fun j' => j' ≠ i), (p.w i j * s_flipped.act i * s_flipped.act j - p.w i j * s.act i * s.act j)) := by
          rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ u)]
      _ = (∑ j ∈ Finset.univ.filter (fun j' => j' ≠ u), p.w u j * (s_flipped.act u * s_flipped.act j - s.act u * s.act j)) +
          (∑ i ∈ Finset.univ.filter (fun i' => i' ≠ u), (p.w i u * (s_flipped.act i * s_flipped.act u - s.act i * s.act u))) := by
          congr 1
          · apply Finset.sum_congr rfl; intros j hj; ring
          · apply Finset.sum_congr rfl; intros i hi_ne_u
            rw [Finset.sum_eq_single u] -- Sum over j
            · ring -- term for j = u
            · intros j' hj'_ne_i hj'_ne_u -- terms for j ≠ u and j ≠ i
              have hi_ne_u_val : i ≠ u := (Finset.mem_filter.mp hi_ne_u).2
              rw [h_same_elsewhere i hi_ne_u_val, h_same_elsewhere j' hj'_ne_u]
              simp
            · intro h_u_not_in_filter_j_neq_i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and_iff, not_ne_iff] at h_u_not_in_filter_j_neq_i
              subst h_u_not_in_filter_j_neq_i -- u = i
              simp [p.hpw.2 i] -- p.w i i = 0, so term is 0
      _ = (s_flipped.act u - s.act u) * (∑ j ∈ Finset.univ.filter (fun j' => j' ≠ u), p.w u j * s.act j) +
          (s_flipped.act u - s.act u) * (∑ i ∈ Finset.univ.filter (fun i' => i' ≠ u), p.w i u * s.act i) := by
          congr 1
          · rw [Finset.mul_sum] -- Apply mul_sum to handle Factor * Sum
            apply Finset.sum_congr rfl; intros j hj_filter
            obtain ⟨_, hj_ne_u⟩ := Finset.mem_filter.mp hj_filter
            rw [h_same_elsewhere j hj_ne_u]
            ring
          · rw [Finset.mul_sum] -- Apply mul_sum here as well
            apply Finset.sum_congr rfl; intros i hi_filter
            obtain ⟨_, hi_ne_u⟩ := Finset.mem_filter.mp hi_filter
            rw [h_same_elsewhere i hi_ne_u, p.hpw.1 i u]
            ring
      _ = (s_flipped.act u - s.act u) * 2 * (∑ v ∈ Finset.univ.filter (fun v' => v' ≠ u), p.w u v * s.act v) := by
          rw [← mul_add]
          have sum_j_eq : (∑ j ∈ Finset.univ.filter (fun j' => j' ≠ u), p.w u j * s.act j) =
                          (∑ v ∈ Finset.univ.filter (fun v' => v' ≠ u), p.w u v * s.act v) := rfl
          have sum_i_eq : (∑ i ∈ Finset.univ.filter (fun i' => i' ≠ u), p.w i u * s.act i) =
                          (∑ v ∈ Finset.univ.filter (fun v' => v' ≠ u), p.w v u * s.act v) := by
            apply Finset.sum_equiv (Equiv.refl U) <;> simp
          rw [sum_j_eq, sum_i_eq]
          conv_lhs => congr; skip; congr; funext v hv; rw [p.hpw.1 v u] -- Apply symmetry specifically
          rw [← Finset.sum_add_distrib, ←two_mul]
          ring
  rw [h_W_diff_terms, h_theta_diff]
  field_simp [(by norm_num : (2 : R) ≠ 0)]
  ring_nf

-- Let's use the version that DB needs: E(s') - E(s) = (s_u - s'_u)L_u = 2 s_u L_u
lemma energy_diff_single_flip_for_db_calc (p : ParamsBM R U) (s s_prime : StateBM R U) (u : U)
    (h_s_prime_act_u : s_prime.act u = -s.act u)
    (h_same_elsewhere : ∀ v, v ≠ u → s_prime.act v = s.act v) :
    energy p s_prime - energy p s = (s.act u - s_prime.act u) * (localField p s u) := by
  exact energy_diff_single_flip_calc_aux p s s_prime u h_s_prime_act_u h_same_elsewhere

/-- The local field at site `u` is the same for states `s` and `s'` if they only differ at `u`. -/
omit [Coe R ℝ] in
lemma localField_eq_if_single_diff (p : ParamsBM R U) (s s' : StateBM R U) (u : U)
    (_h_diff_at_u : s.act u ≠ s'.act u) (h_same_elsewhere : ∀ v, v ≠ u → s.act v = s'.act v) :
    localField p s u = localField p s' u := by
  unfold localField
  congr 1
  apply Finset.sum_congr rfl
  intro v hv_mem_filter
  rw [Finset.mem_filter] at hv_mem_filter
  specialize h_same_elsewhere v hv_mem_filter.2
  rw [h_same_elsewhere]
include [Coe R ℝ]

/-- Energy difference when a single spin `u` is flipped. `s_flipped` is `s` with neuron `u` flipped. -/
lemma energy_diff_single_flip (p : ParamsBM R U) (s s_flipped : StateBM R U) (u : U)
    (h_s_flipped_act_u : s_flipped.act u = -s.act u)
    (h_same_elsewhere : ∀ v, v ≠ u → s_flipped.act v = s.act v) :
    energy p s_flipped - energy p s = 2 * (s.act u) * (localField p s u) := by
  rw [energy_diff_single_flip_calc_aux p s s_flipped u h_s_flipped_act_u h_same_elsewhere]
  rw [h_s_flipped_act_u, show s.act u - (-s.act u) = 2 * s.act u by ring]

/-!
## Detailed Balance Theorem
-/

/--
The Boltzmann Machine satisfies detailed balance with respect to the Gibbs transition kernel
and the Boltzmann distribution.
$\pi(s) P(s'|s) = \pi(s') P(s|s')$
-/
theorem detailedBalanceBM (p : ParamsBM R U) (s s' : StateBM R U)
    [Nonempty (StateBM R U)] [IsOrderedCancelAddMonoid ENNReal] :
    (boltzmannDistributionBM' p Set.univ).toReal * (boltzmannDensityFnBM p s / partitionFunctionBM p).toReal * (gibbsTransitionKernelBM p s {s'}).toReal =
    (boltzmannDistributionBM' p Set.univ).toReal * (boltzmannDensityFnBM p s' / partitionFunctionBM p).toReal * (gibbsTransitionKernelBM p s' {s}).toReal := by
  suffices h_eq_ennreal : boltzmannDensityFnBM p s * (gibbsTransitionKernelBM p s {s'}) =
                           boltzmannDensityFnBM p s' * (gibbsTransitionKernelBM p s' {s}) by
    have Z_ne_zero : partitionFunctionBM p ≠ 0 := (partitionFunctionBM_pos_finite p).1.ne'
    have Z_ne_top : partitionFunctionBM p ≠ ⊤ := (partitionFunctionBM_pos_finite p).2.ne

    have h_factor_one : (boltzmannDistributionBM' p Set.univ).toReal = 1 := by
      rw [boltzmannDistributionBM'] -- def of boltzmannDistributionBM'
      rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ MeasurableSet.univ] -- univ is measurable
      rw [PMF.toOuterMeasure_apply]
      simp only [Set.indicator_univ, PMF.tsum_coe, ENNReal.one_toReal]

    rw [h_factor_one, one_mul, one_mul] at⊢ -- apply to main goal

    -- Check that arguments to toReal are not ⊤
    have h_num_s_finite : boltzmannDensityFnBM p s * gibbsTransitionKernelBM p s {s'} ≠ ⊤ :=
      mul_ne_top (boltzmannDensityFnBM_ne_top p s) (PMF.apply_ne_top _ _)
    have h_num_s'_finite : boltzmannDensityFnBM p s' * gibbsTransitionKernelBM p s' {s} ≠ ⊤ :=
      mul_ne_top (boltzmannDensityFnBM_ne_top p s') (PMF.apply_ne_top _ _)

    have h_lhs_finite : (boltzmannDensityFnBM p s * gibbsTransitionKernelBM p s {s'}) / partitionFunctionBM p ≠ ⊤ :=
      ENNReal.div_ne_top h_num_s_finite Z_ne_zero
    have h_rhs_finite : (boltzmannDensityFnBM p s' * gibbsTransitionKernelBM p s' {s}) / partitionFunctionBM p ≠ ⊤ :=
      ENNReal.div_ne_top h_num_s'_finite Z_ne_zero

    apply congr_arg ENNReal.toReal
    apply congr_arg (fun x => x / partitionFunctionBM p)
    exact h_eq_ennreal

  -- Proof of h_eq_ennreal
  simp_rw [gibbsTransitionKernelBM, PMF.toMeasure_apply_singleton _ (measurableSet_singleton _)]

  by_cases h_s_eq_s' : s = s'
  · rw [h_s_eq_s'];
  ·
    by_cases h_single_site_diff : ∃ u_diff, ∀ v, v ≠ u_diff → s.act v = s'.act v
    ·
      rcases h_single_site_diff with ⟨u, h_u_prop⟩
      have h_s_act_u_ne_s'_act_u : s.act u ≠ s'.act u := by
        intro heq_act_u_eq; apply h_s_eq_s'; ext v; by_cases hv_eq_u : v = u
        · rw [hv_eq_u]; exact heq_act_u_eq
        · exact h_u_prop v hv_eq_u
      have h_s'_act_u_eq_neg_s_act_u : s'.act u = -s.act u := by
        cases h_s_hp_u : s.hp u with
        | inl hs1 => -- s.act u = 1
          cases h_s'_hp_u : s'.hp u with
          | inl hs'1 => exfalso; exact h_s_act_u_ne_s'_act_u (by rw [h_s_hp_u, h_s'_hp_u, hs1, hs'1])
          | inr hs'_1 => rw [h_s_hp_u, h_s'_hp_u, hs1, hs'_1]; norm_num
        | inr hs_1 => -- s.act u = -1
          cases h_s'_hp_u : s'.hp u with
          | inl hs'1 => rw [h_s_hp_u, h_s'_hp_u, hs_1, hs'1]; norm_num
          | inr hs'_1 => exfalso; exact h_s_act_u_ne_s'_act_u (by rw [h_s_hp_u, h_s'_hp_u, hs_1, hs'_1])

      let N_ennreal := ENNReal.ofReal (Fintype.card U : ℝ)
      have h_N_pos_finite : N_ennreal > 0 ∧ N_ennreal < ⊤ := by
        constructor
        · simp [ENNReal.ofReal_pos, Nat.cast_pos, Fintype.card_pos]
        · simp [ENNReal.ofReal_lt_top]
      have h_N_inv_pos_finite : N_ennreal⁻¹ > 0 ∧ N_ennreal⁻¹ < ⊤ :=
        ENNReal.inv_pos_finite.mpr h_N_pos_finite

      have P_s_to_s' : gibbsSamplingStep p s s' = N_ennreal⁻¹ * gibbsUpdateSingleNeuron p s u s' := by
        rw [gibbsSamplingStep_apply_single_site_diff p s s' u h_s_act_u_ne_s'_act_u h_u_prop]
        rw [PMF.uniformOfFintype_apply, one_div]; congr
        exact ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr Fintype.card_pos)

      have P_s'_to_s : gibbsSamplingStep p s' s = N_ennreal⁻¹ * gibbsUpdateSingleNeuron p s' u s := by
        rw [gibbsSamplingStep_apply_single_site_diff p s' s u (Ne.symm h_s_act_u_ne_s'_act_u) (fun v hv ↦ (h_u_prop v hv).symm)]
        rw [PMF.uniformOfFintype_apply, one_div]; congr
        exact ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr Fintype.card_pos)

      rw [P_s_to_s', P_s'_to_s]
      suffices h_main_eq : boltzmannDensityFnBM p s * gibbsUpdateSingleNeuron p s u s' =
                           boltzmannDensityFnBM p s' * gibbsUpdateSingleNeuron p s' u s by
        rw [mul_assoc, mul_assoc, mul_left_inj' h_N_inv_pos_finite.1.ne.symm]
        exact h_main_eq

      let L_s_u := localField p s u
      let L_s'_u := localField p s' u
      have h_L_eq : L_s_u = L_s'_u := localField_eq_if_single_diff p s s' u h_s_act_u_ne_s'_act_u h_u_prop
      let L_u := L_s_u
      let T_R : ℝ := ↑(p.T)

      have h_s'_is_update : s' = updateNeuronBM s u (s'.act u) (s'.hp u) := by
        ext v; by_cases hv : v = u
        · rw [hv]; simp [updateNeuronBM_act_eq]
        · simp [updateNeuronBM_act_ne _ _ _ _ _ hv, h_u_prop v hv]
      have h_s_is_update : s = updateNeuronBM s' u (s.act u) (s.hp u) := by
        ext v; by_cases hv : v = u
        · rw [hv]; simp [updateNeuronBM_act_eq]
        · simp [updateNeuronBM_act_ne _ _ _ _ _ hv, (h_u_prop v hv).symm]

      rw [← h_s'_is_update]
      rw [gibbsUpdateSingleNeuron_apply_val p s u (s'.act u) (s'.hp u)]
      rw [← h_s_is_update]
      rw [gibbsUpdateSingleNeuron_apply_val p s' u (s.act u) (s.hp u)]

      unfold boltzmannDensityFnBM
      let Z_local_R_s_u := Real.exp (L_s_u / T_R) + Real.exp (-L_s_u / T_R)
      let Z_local_R_s'_u := Real.exp (L_s'_u / T_R) + Real.exp (-L_s'_u / T_R)
      have h_Z_local_eq : Z_local_R_s_u = Z_local_R_s'_u := by rw [h_L_eq]
      let Z_local_R := Z_local_R_s_u
      have h_Z_local_pos : Z_local_R > 0 := add_pos (Real.exp_pos _) (Real.exp_pos _)

      rw [ENNReal.ofReal_mul_ofReal (Real.exp_nonneg _) (div_nonneg (Real.exp_nonneg _) h_Z_local_pos.le),
          ENNReal.ofReal_mul_ofReal (Real.exp_nonneg _) (div_nonneg (Real.exp_nonneg _) h_Z_local_pos.le)]
      apply ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (Real.exp_nonneg _) (div_nonneg (Real.exp_nonneg _) h_Z_local_pos.le))
      rw [mul_div_assoc, mul_div_assoc]
      rw [div_eq_div_iff h_Z_local_pos.ne' h_Z_local_pos.ne']
      rw [← Real.exp_add, ← Real.exp_add]
      apply congr_arg Real.exp
      rw [div_eq_div_iff p.hT_pos.ne' p.hT_pos.ne']
      rw [eq_sub_iff_add_eq, ← sub_eq_add_neg, sub_eq_iff_eq_add]
      rw [add_comm (s'.act u * L_u) _, ← mul_sub]
      rw [show energy p s - energy p s' = (s.act u - s'.act u) * L_u by
        { rw [energy_diff_single_flip_for_db_calc p s' s u (by {rw [h_s'_act_u_eq_neg_s_act_u], simp}) (fun v hv => (h_u_prop v hv).symm)],
          rw [show localField p s' u = localField p s u by exact h_L_eq.symm],
          ring_nf,
          rw [h_s'_act_u_eq_neg_s_act_u],
          ring_nf,
        }]
      ring

    ·
      have P_s_to_s'_zero : gibbsSamplingStep p s s' = 0 :=
        gibbsSamplingStep_apply_multi_site_diff p s s' h_single_site_diff
      have P_s'_to_s_zero : gibbsSamplingStep p s' s = 0 :=
        gibbsSamplingStep_apply_multi_site_diff p s' s (by
          intro h_exists_rev
          apply h_single_site_diff
          rcases h_exists_rev with ⟨u_r, h_ur_prop⟩
          use u_r; intro v hv_ne_ur; exact (h_ur_prop v hv_ne_ur).symm
        )
      rw [P_s_to_s'_zero, P_s'_to_s_zero, mul_zero, mul_zero]

end BoltzmannMachine

#min_imports

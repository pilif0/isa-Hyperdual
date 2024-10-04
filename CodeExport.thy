theory CodeExport
  imports
    HyperdualFunctionExtension
    "HOL-Library.Code_Real_Approx_By_Float"
    "HOL-Library.Code_Target_Numeral"
begin

section\<open>Code Generation\<close>

text\<open>Disable any attempt to generate code for @{const hypext} directly\<close>
lemmas [code del] = hypext.code

subsection\<open>Extension of @{const exp}\<close>

primcorec hyp_exp :: "real hyperdual \<Rightarrow> real hyperdual"
  where
    "Base (hyp_exp x) = exp (Base x)"
  | "Eps1 (hyp_exp x) = Eps1 x * exp (Base x)"
  | "Eps2 (hyp_exp x) = Eps2 x * exp (Base x)"
  | "Eps12 (hyp_exp x) = Eps12 x * exp (Base x) + Eps1 x * Eps2 x * exp (Base x)"

lemma hypext_exp:
  "*h* exp = hyp_exp"
  apply standard
  apply (rule hyperdual_eqI)
     apply simp_all
  done

subsection\<open>Extension of @{const sin}\<close>

primcorec hyp_sin :: "real hyperdual \<Rightarrow> real hyperdual"
  where
    "Base (hyp_sin x) = sin (Base x)"
  | "Eps1 (hyp_sin x) = Eps1 x * cos (Base x)"
  | "Eps2 (hyp_sin x) = Eps2 x * cos (Base x)"
  | "Eps12 (hyp_sin x) = Eps12 x * cos (Base x) - Eps1 x * Eps2 x * sin (Base x)"

lemma hypext_sin:
  "*h* sin = hyp_sin"
  apply standard
  apply (rule hyperdual_eqI)
     apply simp_all
  done

subsection\<open>Extension of @{const cos}\<close>

primcorec hyp_cos :: "real hyperdual \<Rightarrow> real hyperdual"
  where
    "Base (hyp_cos x) = cos (Base x)"
  | "Eps1 (hyp_cos x) = - Eps1 x * sin (Base x)"
  | "Eps2 (hyp_cos x) = - Eps2 x * sin (Base x)"
  | "Eps12 (hyp_cos x) = - Eps12 x * sin (Base x) - Eps1 x * Eps2 x * cos (Base x)"

lemma hypext_cos:
  "*h* cos = hyp_cos"
  apply standard
  apply (rule hyperdual_eqI)
     apply simp_all
  done

subsection\<open>Extension of @{const sqrt}\<close>

primcorec hyp_sqrt :: "real hyperdual \<Rightarrow> real hyperdual"
  where
    "Base (hyp_sqrt x) = sqrt (Base x)"
  | "Eps1 (hyp_sqrt x) =
    ( if 0 < Base x then Eps1 x * inverse (sqrt (Base x)) / 2
      else if Base x < 0 then - Eps1 x * inverse (sqrt (Base x)) / 2
      else undefined)"
  | "Eps2 (hyp_sqrt x) =
    ( if 0 < Base x then Eps2 x * inverse (sqrt (Base x)) / 2
      else if Base x < 0 then - Eps2 x * inverse (sqrt (Base x)) / 2
      else undefined)"
  | "Eps12 (hyp_sqrt x) =
    ( if 0 < Base x then Eps12 x * inverse (sqrt (Base x)) / 2 - Eps1 x * Eps2 x * inverse (sqrt (Base x) ^ 3) / 4
      else if Base x < 0 then - Eps12 x * inverse (sqrt (Base x)) / 2 - Eps1 x * Eps2 x * inverse (sqrt (Base x) ^ 3) / 4
      else undefined)"

lemma hypext_sqrt:
  "*h* sqrt = hyp_sqrt"
  apply standard
  apply (rule hyperdual_eqI ; case_tac "0 < Base x" ; case_tac "Base x < 0")
         apply (simp_all add: not_less)
  (* To safely replace hyperdual extension of square root with a function, we need a value for first
      and second derivative at zero, where square root is not differentiable. *)
  oops

lemma hypext_sqrt:
  assumes "Base x \<noteq> 0"
    shows "(*h* sqrt) x = hyp_sqrt x"
proof (cases "0 < Base x")
  case True
  then show ?thesis
    by (intro hyperdual_eqI) simp_all
next
  case False
  then show ?thesis
    using assms by (intro hyperdual_eqI) simp_all
qed

subsection\<open>Analytic Test Function\<close>

text\<open>Base function, an example used by Fike and Alonso\<close>
definition fa_test :: "real \<Rightarrow> real"
  where "fa_test x = exp x / (sqrt (sin x ^ 3 + cos x ^ 3))"

text\<open>Its hyperdual extension can be derived where the square root argument is non-zero\<close>
lemma hypext_fa_test:
  assumes "sin (Base x) ^ 3 + cos (Base x) ^ 3 \<noteq> 0"
    shows "(*h* fa_test) x = ((*h* exp) x) / ((*h* sqrt) (((*h* sin) x) ^ 3 + ((*h* cos) x) ^ 3))"
proof -
  have "\<And>f. (\<lambda>x. (sin x) ^ 3) twice_field_differentiable_at Base x"
   and "\<And>f. (\<lambda>x. (cos x) ^ 3) twice_field_differentiable_at Base x"
    by (simp_all add: twice_field_differentiable_at_compose[OF _ twice_field_differentiable_at_power])
  then have "(*h* (\<lambda>x. sin x ^ 3 + cos x ^ 3)) x = (*h* sin) x ^ 3 + (*h* cos) x ^ 3"
        and d_sincos: "(\<lambda>x. sin x ^ 3 + cos x ^ 3) twice_field_differentiable_at Base x"
    using hypext_fun_add[of "\<lambda>x. sin x ^ 3" x "\<lambda>x. cos x ^ 3"]
    by (simp_all add: hypext_fun_power twice_field_differentiable_at_add)
  then have "(*h* (\<lambda>x. sqrt (sin x ^ 3 + cos x ^ 3))) x = (*h* sqrt) ((*h* sin) x ^ 3 + (*h* cos) x ^ 3)"
    using assms hypext_compose[of "\<lambda>x. sin x ^ 3 + cos x ^ 3" x]
    by (cases "0 < sin (Base x) ^ 3 + cos (Base x) ^ 3") simp_all
  moreover have d_sqrt: "(\<lambda>x. sqrt (sin x ^ 3 + cos x ^ 3)) twice_field_differentiable_at Base x"
    using d_sincos twice_field_differentiable_at_compose twice_field_differentiable_at_sqrt
          twice_field_differentiable_at_sqrt_neg
    using assms
    apply (cases "0 < sin (Base x) ^ 3 + cos (Base x) ^ 3")
     apply blast
    by (meson linorder_neqE_linordered_idom)
  ultimately have "(*h* (\<lambda>x. inverse (sqrt (sin x ^ 3 + cos x ^ 3)))) x = inverse ((*h* sqrt) ((*h* sin) x ^ 3 + (*h* cos) x ^ 3))"
    using assms hypext_fun_inverse[of "\<lambda>x. sqrt (sin x ^ 3 + cos x ^ 3)" x] by simp
  moreover have "(\<lambda>x. inverse (sqrt (sin x ^ 3 + cos x ^ 3))) twice_field_differentiable_at Base x"
    using assms d_sqrt real_sqrt_eq_zero_cancel_iff
          twice_field_differentiable_at_compose twice_field_differentiable_at_inverse
          less_numeral_extra(3)
    by force
  ultimately have
    "(*h* (\<lambda>x. exp x * inverse (sqrt (sin x ^ 3 + cos x ^ 3)))) x =
     (*h* exp) x * inverse ((*h* sqrt) ((*h* sin) x ^ 3 + (*h* cos) x ^ 3))"
    by (simp add: hypext_fun_mult)
  then have
    "(*h* (\<lambda>x. exp x / sqrt (sin x ^ 3 + cos x ^ 3))) x =
     (*h* exp) x / (*h* sqrt) ((*h* sin) x ^ 3 + (*h* cos) x ^ 3)"
    by (simp add: inverse_eq_divide hyp_divide_inverse)
  then show ?thesis
    unfolding fa_test_def .
qed

text\<open>To generate code for this extension, we need to guard against that case\<close>
definition hyp_fa_test_safe :: "real hyperdual \<Rightarrow> real hyperdual"
  where "hyp_fa_test_safe x =
  ( if sin (Base x) ^ 3 + cos (Base x) ^ 3 = 0 then undefined
    else ((*h* exp) x) / ((*h* sqrt) (((*h* sin) x) ^ 3 + ((*h* cos) x) ^ 3)))"

text\<open>
  At this point, we cannot directly generate code for @{const hyp_fa_test_safe} because it uses
  @{const hypext}.
  However, we can prove a code equation that uses implementations for those hyperdual extensions.
  Here the guard is shown as necessary to replace @{term "*h* sqrt"} with @{const hyp_sqrt}.
\<close>
lemma hyp_fa_test_safe_code [code]:
  " hyp_fa_test_safe x =
    ( if sin (Base x) ^ 3 + cos (Base x) ^ 3 = 0 then undefined
      else (hyp_exp x) / (hyp_sqrt ((hyp_sin x) ^ 3 + (hyp_cos x) ^ 3)))"
  unfolding hyp_fa_test_safe_def hypext_fa_test hypext_exp hypext_sin hypext_cos
  by (simp add: hypext_sqrt)

text\<open>As a result, we can generate code for it\<close>
export_code fa_test hyp_fa_test_safe in Haskell

end
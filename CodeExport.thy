theory CodeExport
  imports
    HyperdualFunctionExtension
    "HOL-Library.Code_Real_Approx_By_Float"
    "HOL-Library.Code_Target_Numeral"
    Sqrt_Babylonian.Sqrt_Babylonian
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

subsection\<open>Extension of @{const abs}\<close>

primcorec hyp_abs :: "real hyperdual \<Rightarrow> real hyperdual"
  where
    "Base (hyp_abs x) = abs (Base x)"
  | "Eps1 (hyp_abs x) = (if Base x > 0 then 1 else if Base x < 0 then - 1 else undefined) * Eps1 x"
  | "Eps2 (hyp_abs x) = (if Base x > 0 then 1 else if Base x < 0 then - 1 else undefined) * Eps2 x"
  | "Eps12 (hyp_abs x) = Eps12 x * (if Base x > 0 then 1 else if Base x < 0 then - 1 else undefined)
        + Eps1 x * Eps2 x * (if Base x > 0 then 0 else if Base x < 0 then 0 else undefined)"

lemma hypext_abs:
  "*h* abs = hyp_abs"
  apply standard
  apply (rule hyperdual_eqI ; case_tac "0 < Base x" ; case_tac "Base x < 0")
                 apply (simp_all add: not_less deriv_abs)
  (* To safely replace hyperdual extension of abs with a function, we need a value for first
      and second derivative at zero, where abs is not differentiable. *)
  oops

lemma hypext_abs:
  assumes "Base x \<noteq> 0"
    shows "(*h* abs) x = hyp_abs x"
proof (cases "0 < Base x")
  case True
  then show ?thesis
    by (intro hyperdual_eqI) (simp_all add: deriv_abs deriv_deriv_abs)
next
  case False
  then show ?thesis
    using assms by (intro hyperdual_eqI) (simp_all add: deriv_abs deriv_deriv_abs)
qed

subsection\<open>Babylonian Square Root\<close>

lemma hypext_If: (* conjecture! move if proved *)
  shows "(*h* (\<lambda>x. if P x then f x else g x)) = (\<lambda>x. if P (Base x) then (*h* f) x else (*h* g) x)"
  apply standard
  apply (simp add: hypext.code)
  apply safe
  sorry

(* need real normed field for hypext *)

partial_function (tailrec) hyp_sqrt_approx_main_impl :: "'a :: {linordered_field, real_normed_field} \<Rightarrow> 'a hyperdual \<Rightarrow> 'a hyperdual \<Rightarrow> 'a hyperdual"
  where [code]: "hyp_sqrt_approx_main_impl \<epsilon> n x =
  ( if Base (x * x - n) < \<epsilon>
      then x
      else hyp_sqrt_approx_main_impl \<epsilon> n ((n / x + x) / Hyperdual 2 0 0 0))"

locale hyp_sqrt_approximation =
  fixes \<epsilon> :: "'a :: {real_normed_field,floor_ceiling}"
  and n :: "'a hyperdual"
  assumes \<epsilon> : "\<epsilon> > 0"
  and n: "Base n > 0"
begin

function hyp_sqrt_approx_main :: "'a hyperdual \<Rightarrow> 'a hyperdual" where
  "hyp_sqrt_approx_main x =
  ( if Base x > 0
      then (if Base (x * x - n) < \<epsilon>
        then x
        else hyp_sqrt_approx_main ((n / x + x) / Hyperdual 2 0 0 0))
      else 0)"
  by pat_completeness auto

termination hyp_sqrt_approx_main
proof -
  define er where "er x = Base (x * x / n - 1)" for x :: "'a hyperdual"
  define c where "c = 2 * Base n / \<epsilon>"
  define m where "m x = nat \<lfloor> c * er x \<rfloor>" for x :: "'a hyperdual"
  have c: "c > 0" unfolding c_def using n \<epsilon> by auto
  show ?thesis
  proof
    show "wf (measures [m])" by simp
  next
    fix x :: "'a hyperdual"
    assume x: "0 < Base x" and xe: "\<not> Base (x * x - n) < \<epsilon>"
    define y where "y = (n / x + x) / Hyperdual 2 0 0 0"
    show "((n / x + x) / Hyperdual 2 0 0 0, x) \<in> measures [m]"
      unfolding y_def[symmetric]
    proof (rule measures_less)
      from n have inv_n: "1 / Base n > 0" by auto
      from xe have "Base (x * x - n) \<ge> \<epsilon>" by simp
      from this[unfolded mult_le_cancel_left_pos[OF inv_n, of \<epsilon>, symmetric]]
      have erxen: "er x \<ge> \<epsilon> / Base n" unfolding er_def using n by (simp add: field_simps)
      have en: "\<epsilon> / Base n > 0" and ne: "Base n / \<epsilon> > 0" using \<epsilon> n by auto
      from en erxen have erx: "er x > 0" by linarith
      have pos: "er x * 4 + er x * (er x * 4) > 0" using erx
        by (auto intro: add_pos_nonneg)
      have "Base 2 * Base 2 = (4 :: 'a)"
        by (metis numeral_Bit0_eq_double one_add_one one_hyperdual_simps(1) plus_hyperdual.simps(1))
      then have "er y = 1 / 4 * Base (n / (x * x) - Hyperdual 2 0 0 0  + x * x / n)" unfolding er_def y_def using x n
        by (simp add: field_simps)
      also have "\<dots> = 1 / 4 * er x * er x / (1 + er x)" unfolding er_def using x n
        by (simp add: field_simps)
      finally have "er y = 1 / 4 * er x * er x / (1 + er x)" .
      also have "\<dots> < 1 / 4 * (1 + er x) * er x / (1 + er x)" using erx erx pos
        by (auto simp: field_simps)
      also have "\<dots> = er x / 4" using erx by (simp add: field_simps)
      finally have er_y_x: "er y \<le> er x / 4" by linarith
      from erxen have "c * er x \<ge> 2" unfolding c_def mult_le_cancel_left_pos[OF ne, of _ "er x", symmetric]
        using n \<epsilon> by (auto simp: field_simps)
      hence pos: "\<lfloor>c * er x\<rfloor> > 0" "\<lfloor>c * er x\<rfloor> \<ge> 2" by auto
      show "m y < m x" unfolding m_def nat_mono_iff[OF pos(1)]
      proof -
        have "\<lfloor>c * er y\<rfloor> \<le> \<lfloor>c * (er x / 4)\<rfloor>"
          by (rule floor_mono, unfold mult_le_cancel_left_pos[OF c], rule er_y_x)
        also have "\<dots> < \<lfloor>c * er x / 4 + 1\<rfloor>" by auto
        also have "\<dots> \<le> \<lfloor>c * er x\<rfloor>"
          by (rule floor_mono, insert pos(2), simp add: field_simps)
        finally show "\<lfloor>c * er y\<rfloor> < \<lfloor>c * er x\<rfloor>" .
      qed
    qed
  qed
qed

lemma hyp_sqrt_approx_main_impl:
  "Base x > 0 \<Longrightarrow> hyp_sqrt_approx_main_impl \<epsilon> n x = hyp_sqrt_approx_main x"
proof (induct x rule: hyp_sqrt_approx_main.induct)
  case (1 x)
  hence x: "Base x > 0" by auto
  hence nx: "0 < Base ((n / x + x) / Hyperdual 2 0 0 0)" using n by (auto intro: pos_add_strict)
  note simps = hyp_sqrt_approx_main_impl.simps[of _ _ x] hyp_sqrt_approx_main.simps[of x]
  show ?case
  proof (cases "Base (x * x - n) < \<epsilon>")
    case True
    thus ?thesis unfolding simps using x by auto
  next
    case False
    show ?thesis using 1(1)[OF x False nx] unfolding simps using x False by auto
  qed
qed

(* TODO left out soundness proof *)

sublocale base_sqrt: sqrt_approximation \<epsilon> "Base n"
  using \<epsilon> n [[show_sorts]] by unfold_locales

lemma hypext_sqrt_approx_main:
  "(*h* base_sqrt.sqrt_approx_main) x = hyp_sqrt_approx_main x"
proof (induct x rule: hyp_sqrt_approx_main.induct)
  case (1 x)

  show ?case
    apply (cases "Base x = 0")
     apply (simp add: hypext_If of_comp_def)
    apply (subst hyp_sqrt_approx_main.simps)
    apply (subst base_sqrt.sqrt_approx_main.simps[abs_def])
    apply (unfold hypext_If)
    apply (simp del: hyp_sqrt_approx_main.simps base_sqrt.sqrt_approx_main.simps)
    apply safe
    using hypext_ident apply blast
      apply (simp add: zero_hyperdual_def)
     apply (subst 1[symmetric])
       apply simp
    apply simp
    sorry
qed


end

definition hyp_sqrt_approx :: "real \<Rightarrow> real hyperdual \<Rightarrow> real hyperdual"
  where "hyp_sqrt_approx \<epsilon> x =
  ( if \<epsilon> > 0
      then (if Base x = 0
        then 0
        else let xpos = hyp_abs x in hyp_sqrt_approx_main_impl \<epsilon> xpos (xpos + 1))
      else 0)"

lemma
  "(*h* sqrt_approx \<epsilon>) = hyp_sqrt_approx \<epsilon>"
proof standard
  fix x

  show "(*h* sqrt_approx \<epsilon>) x = hyp_sqrt_approx \<epsilon> x"
  proof (cases "0 < \<epsilon>")
    case \<epsilon>: True
    then show ?thesis
    proof (cases "Base x = 0")
      case True
      then show ?thesis
        using \<epsilon>
        unfolding sqrt_approx_def hyp_sqrt_approx_def
        by (simp add: hypext_If zero_hyperdual_def)
    next
      case False
      then show ?thesis
        using \<epsilon>
        unfolding sqrt_approx_def hyp_sqrt_approx_def
        apply (simp add: hypext_If zero_hyperdual_def Let_def)

        apply (subst (1 2) hypext_abs[OF False, symmetric])
        apply (subst hyp_sqrt_approximation.hyp_sqrt_approx_main_impl)
          apply (unfold_locales, assumption, simp, simp)
        apply (subst hyp_sqrt_approximation.hypext_sqrt_approx_main[symmetric])
          apply (unfold_locales, assumption, simp)
        using hypext_compose
        sorry
    qed
  next
    case False
    then show ?thesis
      unfolding sqrt_approx_def hyp_sqrt_approx_def
      by (simp add: zero_hyperdual_def)
  qed
qed

subsection\<open>Iterative Square Root\<close>

(* https://github.com/JuliaDiff/DualNumbers.jl/blob/5821433409922ebe7e7207167eb5d19fb114093c/test/automatic_differentiation_test.jl#L90 *)

function itsqrt' :: "real hyperdual \<Rightarrow> real hyperdual \<Rightarrow> real hyperdual"
  where "itsqrt' x it =
  ( if Base (hyp_abs (it * it - x)) > 1/10^13
      then itsqrt' x ((it + x/it) / Hyperdual 2 0 0 0)
      else it)"
  by pat_completeness auto
termination itsqrt'
  apply standard
  sorry

definition itsqrt :: "real hyperdual \<Rightarrow> real hyperdual"
  where "itsqrt x = itsqrt' x x"

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
export_code open
  (* Basic operations *)
  "(+) :: ('a :: plus) hyperdual \<Rightarrow> 'a hyperdual \<Rightarrow> 'a hyperdual"
  "(-) :: ('a :: minus) hyperdual \<Rightarrow> 'a hyperdual \<Rightarrow> 'a hyperdual"
  "(*) :: ('a :: {plus,times}) hyperdual \<Rightarrow> 'a hyperdual \<Rightarrow> 'a hyperdual"
  "scaleH :: ('a :: times) \<Rightarrow> 'a hyperdual \<Rightarrow> 'a hyperdual"
  "(/) :: ('a :: {inverse, ring_1}) hyperdual \<Rightarrow> 'a hyperdual \<Rightarrow> 'a hyperdual"
  "inverse :: ('a :: {inverse, ring_1}) hyperdual \<Rightarrow> 'a hyperdual"
  itsqrt
  (* Test function and its (safe) hyperdual extension *)
  fa_test hyp_fa_test_safe
  in Haskell file_prefix "haskell/isabelle/src" (root: Hyperdual.Isabelle string_classes)

end
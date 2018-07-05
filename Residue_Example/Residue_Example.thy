(*
    File: Residue_Example.thy
    Author: Wenda Li, University of Cambridge
*)

theory Residue_Example imports Analysis
begin 

text \<open>An example of applying @{thm Residue_theorem} to evaluate improper integrals\<close>

lemma tendsto_add_left_cong:
  fixes c :: "'a::real_normed_vector"
  assumes "(g \<longlongrightarrow> 0) F"
  shows "(f \<longlongrightarrow> c) F = ((\<lambda>x. g x + f x) \<longlongrightarrow> c) F" using assms
  by (auto intro:tendsto_add[where a=0,simplified] 
    tendsto_diff[of "(\<lambda>x. g x + f x)" _ _ g 0 ,simplified])

(*TODO: update*)
lemma winding_number_less_1:
  fixes z::complex
  shows
  "\<lbrakk>valid_path \<gamma>; z \<notin> path_image \<gamma>; w \<noteq> z;
    \<And>a::real. 0 < a \<Longrightarrow> z + a*(w - z) \<notin> path_image \<gamma>\<rbrakk>
   \<Longrightarrow> \<bar>Re(winding_number \<gamma> z)\<bar> < 1"
   by (auto simp: not_less dest: winding_number_big_meets)

lemma an_improper_integral_example:
  "Lim at_top (\<lambda>R. integral {- R..R} (\<lambda>x. 1 / (x\<^sup>2 + 1))) = pi"
proof -
  def f\<equiv>"\<lambda>x::real. 1/(x^2+1)"
  def f'\<equiv>"\<lambda>x::complex. 1/(x^2+1)"
  def CR\<equiv>"\<lambda>R. part_circlepath 0 R 0 pi"
  def L\<equiv>"\<lambda>R. linepath (complex_of_real (-R)) R"
  def g\<equiv>"\<lambda>R. CR R +++ L R"
  have f_int_on: "f integrable_on {- R .. R}" for R
    unfolding f_def
    apply (auto intro!:integrable_continuous_real continuous_intros)
    by (metis numeral_One power_one sum_power2_eq_zero_iff zero_neq_numeral)
  have f'_on_L: "f' contour_integrable_on (L R)"
      and L_sub_R:"path_image (L R) \<subseteq> \<real>" for R
  proof -
    show L_sub_R:"path_image (L R) \<subseteq> \<real>"  
    proof 
      fix x assume "x \<in> path_image (L R)"
      then obtain u where u_def:"x=(1 - u) *\<^sub>R (complex_of_real (- R)) + u *\<^sub>R complex_of_real R" 
              and "0\<le>u" "u\<le>1"
        unfolding L_def by (auto simp add:closed_segment_def)
      hence "x=complex_of_real (2*u*R - R)"
        by (auto simp add:scaleR_conv_of_real field_simps)
      thus "x\<in>\<real>" by auto
    qed               
    have "x^2+1\<noteq>0" when x_seg:"x\<in>path_image (L R)" for x::complex
    proof 
      assume "x\<^sup>2 + 1 = 0"
      hence "x^2 = -1" by (metis diff_0 diff_zero minus_diff_eq minus_unique)
      hence "x=\<i> \<or> x=-\<i>" using power2_eq_iff by fastforce
      hence "x\<notin>\<real>" by (auto simp add: complex_is_Real_iff)
      moreover have "x\<in>\<real>" using x_seg L_sub_R by auto
      ultimately show False by simp
    qed
    then show "f' contour_integrable_on (L R)" unfolding f'_def L_def
      apply (simp add:of_real_linepath)
      apply (intro contour_integrable_continuous_linepath)
      by (auto intro!: continuous_intros)
  qed
  have f'_on_CR:"f' contour_integrable_on (CR R)"
      and pole_CR: "\<i>\<notin>path_image (CR R)" "- \<i>\<notin>path_image (CR R)" when "R>1" for R 
  proof -
    show pole_CR: "\<i>\<notin>path_image (CR R)" "- \<i>\<notin>path_image (CR R)"
      unfolding CR_def using `R>1`
       apply auto
      by (drule_tac in_path_image_part_circlepath,auto)+
    have False when "x \<in> path_image (CR R)" "x\<^sup>2 + 1 = 0" for x
    proof -
      have "x^2 = -1" using that(2) by (metis diff_0 diff_zero minus_diff_eq minus_unique)
      hence "x=\<i> \<or> x=-\<i>" using power2_eq_iff by fastforce
      hence "cmod x=1" by auto
      moreover have "cmod x=R" 
        using in_path_image_part_circlepath[OF that(1)[unfolded CR_def]] `R>1` by auto
      ultimately show False using `R>1` by auto
    qed
    then show "f' contour_integrable_on (CR R)" unfolding CR_def f'_def
      apply (intro contour_integrable_continuous_part_circlepath)
      by (auto  intro!:continuous_intros)
  qed
  have int_eq:"integral {-R..R} f = contour_integral (L R) f'" when "R>1" for R::real  
  proof -
    obtain i where i_def:"(f has_integral i) {-R .. R}"
                and i_def_aux:"i=integral {-R..R} f" using f_int_on by auto
    obtain i' where i'_def:"(f' has_contour_integral i') (L R)"
                and i'_def_aux:"i'= contour_integral (L R) f'"
      using contour_integral_unique f'_on_L[of R] unfolding contour_integrable_on_def by blast
    hence  "((\<lambda>x. f' (L R x) * (2 * R)) has_integral i') {0..1}" unfolding L_def
      by (simp add:of_real_linepath has_contour_integral_linepath)
    hence "((\<lambda>x. f' ( (linepath (- R) R (x / (2 * R) + 1 / 2))) * (2 *  R)) has_integral
                  \<bar>2 * R\<bar> *\<^sub>R i') ((\<lambda>x. x * (2 * R) - R) ` {0..1})" 
      using `R>1` unfolding L_def
      apply (intro has_integral_affinity01[of _ i' "1/(2*R)" "1/2",simplified]) 
      by (auto simp add:of_real_linepath)
    moreover have "((\<lambda>x. x * (2 * R) - R) ` {0..1}) = {-R .. R}" using `R>1`
      apply (subst mult.commute)
      apply (subst image_affinity_atLeastAtMost_diff)
      by auto
    ultimately have " (((\<lambda>x. (2 * R) * f' x)) has_integral (2 * R) * i') {- R..R} " 
      unfolding linepath_def scaleR_conv_of_real using `R>1`
      by (simp add:field_simps)
    hence "(((\<lambda>x. f' x)) has_integral i') {- R..R} " using `R>1`
      apply (drule_tac has_integral_mult_right[where c="(1::complex)/(2*R)"])
      by (simp add:field_simps)
    moreover have "(complex_of_real o f) = (\<lambda>x. f' (complex_of_real x))" 
      unfolding f_def f'_def comp_def
      by auto
    ultimately have "(( complex_of_real \<circ> f) has_integral i') {- R..R} " by auto
    moreover have "((complex_of_real o f) has_integral i) {-R .. R}"
      using i_def
      by (auto elim: has_integral_linear simp add:bounded_linear_of_real)
    ultimately have "i'=i" using has_integral_unique by auto
    thus ?thesis using i'_def_aux i_def_aux unfolding L_def by (auto simp add:of_real_linepath)
  qed
  have "((\<lambda>R. integral {- R..R} f) \<longlongrightarrow> pi) at_top  
      = ((\<lambda>R. contour_integral (L R) f') \<longlongrightarrow> pi) at_top"
    apply (subst tendsto_of_real_iff[symmetric,where 'a=complex])
    apply (intro tendsto_cong)
    apply (subst eventually_at_top_dense)
    apply (intro exI[where x=1])
    by (simp add:int_eq)
  also have "... = ((\<lambda>R. contour_integral (CR R) f' + contour_integral (L R) f') \<longlongrightarrow> pi) at_top"
  proof (rule tendsto_add_left_cong)
    def h\<equiv>"\<lambda>R. pi * R / (R^2 -1)"
    have "cmod (contour_integral (CR R) f') \<le> h R" when "R>1" for R
    proof -
      obtain i where i_def:"(f' has_contour_integral i) (CR R)"
                              "i=contour_integral (CR R) f'" 
        using contour_integral_unique  f'_on_CR[OF `R>1`] unfolding contour_integrable_on_def by blast
      have "cmod i \<le> R * pi / (R\<^sup>2 - 1)"
      proof (rule has_contour_integral_bound_part_circlepath[OF i_def(1)[unfolded CR_def],
                of "1/(R^2-1)",simplified])
        show "1 \<le> R\<^sup>2" "0 < R" using `R>1` by auto
        show "cmod (f' x) \<le> 1 / (R\<^sup>2 - 1)" 
            when "x \<in> path_image (part_circlepath 0 R 0 pi)" for x
        proof -
          have "cmod x = R" using in_path_image_part_circlepath[OF that] `R>1` by auto
          hence "cmod(x^2+1)\<ge> R^2 - 1"
            by (metis norm_diff_ineq norm_one norm_power)
          moreover have "R^2 - 1 >0" using `R>1` by auto
          ultimately have "inverse (cmod (x^2+1))\<le> inverse (R^2 - 1)"
            by (auto elim:le_imp_inverse_le)
          hence "cmod (inverse(x^2+1))\<le> inverse (R^2 - 1)" 
            using norm_inverse by metis
          thus ?thesis 
            unfolding f'_def by (simp add:field_simps)
        qed
      qed
      thus ?thesis unfolding i_def(2) h_def by (simp add:algebra_simps)
    qed
    then have "\<forall>\<^sub>F x in at_top. cmod (contour_integral (CR x) f') \<le> h x" 
      unfolding eventually_at_top_dense by (intro exI[where x=1],auto)
    moreover have "(h \<longlongrightarrow> 0) at_top" unfolding h_def 
    proof (rule Deriv.lhospital_at_top_at_top[where f'="\<lambda>_. pi" and g'="\<lambda>x. 2*x"])
      have "LIM (R::real) at_top. (- 1) + R\<^sup>2 :> at_top" 
        apply (rule filterlim_tendsto_add_at_top)
        by (auto intro!:filterlim_pow_at_top filterlim_ident)
      then show "LIM (R::real) at_top. R\<^sup>2 - 1 :> at_top" by simp
    next
      show " \<forall>\<^sub>F R in at_top. 2 * R \<noteq> (0::real)"
        unfolding eventually_at_top_dense by (intro exI[where x=1],auto)
      show "\<forall>\<^sub>F R in at_top. (op * pi has_real_derivative pi) (at R)"
        unfolding eventually_at_top_dense by (intro exI[where x=1],auto)       
      show "\<forall>\<^sub>F R in at_top. ((\<lambda>x. x\<^sup>2 - 1) has_real_derivative 2 * R) (at R)"
        apply (intro eventuallyI)
        by (auto intro!:derivative_eq_intros)
      show "((\<lambda>R. pi / (2 * R)) \<longlongrightarrow> 0) at_top"
        by (auto intro!:  tendsto_divide_0 filterlim_at_top_imp_at_infinity 
              filterlim_tendsto_pos_mult_at_top[of "\<lambda>_. 2" 2] filterlim_ident)
    qed
    ultimately show "((\<lambda>x. contour_integral (CR x) f') \<longlongrightarrow> 0) at_top"
      using Lim_null_comparison[of "(\<lambda>R. contour_integral (CR R) f')" h at_top] by auto
  qed
  also have "... = ((\<lambda>R. contour_integral (g R) f') \<longlongrightarrow> pi) at_top"
    unfolding g_def
    apply (intro tendsto_cong)
    apply (subst eventually_at_top_dense)
    apply (auto intro!: exI[where x=1])
    apply (subst contour_integral_join)
    apply (simp_all add:f'_on_L f'_on_CR)
    by (simp_all add:CR_def L_def )
  also have "..."
  proof -
    have "contour_integral (g R) f' = complex_of_real pi" when "R>1" for R
    proof -
      have valid_g[simp]:"valid_path (g R)" and loop_g[simp]:"pathfinish (g R) = pathstart (g R)" 
        unfolding g_def CR_def L_def by (auto intro!: valid_path_join)
      have pole_g: "- \<i> \<notin> path_image (g R)" "\<i> \<notin> path_image (g R)"
      proof -
        note pole_CR[OF `R>1`]
        moreover have "- \<i> \<notin> \<real>" "\<i> \<notin> \<real>" by (auto simp add: complex_is_Real_iff)
        then have "-\<i> \<notin> path_image (L R)" "\<i> \<notin> path_image (L R)" using L_sub_R by auto
        ultimately show "- \<i> \<notin> path_image (g R)" "\<i> \<notin> path_image (g R)" 
          unfolding g_def using path_image_join_subset by auto
      qed
      have W1:"winding_number (g R) \<i> = 1" 
      proof -
        def CR'\<equiv>"\<lambda>R. part_circlepath 0 R pi (2*pi)"
        have "homotopic_paths (- {\<i>}) (CR' R) (L R)" 
        proof (rule homotopic_paths_linear)
          show "path (CR' R)" " path (L R)" "pathstart (L R) = pathstart (CR' R)" 
                "pathfinish (L R) = pathfinish (CR' R)"
            unfolding CR_def CR'_def L_def using `R>1` 
               apply simp_all 
            by (metis exp_two_pi_i mult.commute)
        next
          fix t::"real" assume "t\<in>{0..1}"
          have "\<i> \<notin> closed_segment (CR' R t) (L R t)" 
          proof 
            assume "\<i> \<in> closed_segment (CR' R t) (L R t)"
            then obtain u where "u\<ge>0" "u\<le>1" 
                            and u_def:"\<i>=(1 - u) *\<^sub>R CR' R t + u *\<^sub>R L R t" 
              unfolding closed_segment_def by auto
            have "Im ((1 - u) *\<^sub>R CR' R t + u *\<^sub>R L R t) = Im ((1 - u) *\<^sub>R CR' R t)"
            proof -
              have "L R t \<in> Reals" 
                using L_sub_R[of R] `t\<in>{0..1}` unfolding path_image_def by auto 
              thus ?thesis by (auto simp add: complex_is_Real_iff)
            qed
            also have "... \<le> 0" unfolding CR'_def part_circlepath_def 
              apply (auto simp add:Im_exp linepath_def field_simps)
              using `R>1` `u\<ge>0` `u\<le>1` `t\<in>{0..1}`
              by (simp add: mult_left_le_one_le mult_mono mult_right_le_one_le sin_ge_zero)
            finally have "Im \<i> \<le>0" using u_def by auto
            thus False by auto
          qed
          then show "closed_segment (CR' R t) (L R t) \<subseteq> - {\<i>}" by auto
        qed
        moreover have "homotopic_paths (- {\<i>}) (CR R) (CR R)"
          using homotopic_paths_refl pole_CR[OF `R>1`] by (auto simp add:CR_def)
        ultimately have "homotopic_paths (- {\<i>}) (CR R +++ CR' R) (CR R +++ L R)"  
          apply (intro homotopic_paths_join,simp_all)
          by (simp add: CR_def CR'_def)
        moreover have "CR R +++ CR' R = circlepath 0 R"
          unfolding CR_def CR'_def circlepath_def part_circlepath_def using `R>1`
          apply (intro ext)
          by (auto simp add:joinpaths_def algebra_simps linepath_def)
        ultimately have "homotopic_paths (- {\<i>}) (circlepath 0 R) (g R)"
          unfolding CR_def CR'_def g_def by auto
        thus ?thesis 
          using winding_number_homotopic_paths winding_number_circlepath[of \<i> 0 R,simplified] 
            `R>1`
          by auto
      qed
      have W0:"winding_number (g R) (- \<i>) = 0" 
      proof -
        have "\<bar>Re (winding_number (g R) (- \<i>))\<bar> < 1"
        proof (rule winding_number_less_1[OF valid_g pole_g(1), of"-R * \<i>"])
          show "complex_of_real (- R) * \<i> \<noteq> - \<i>" using `R>1` 
            by (metis complex_i_mult_minus i_squared less_numeral_extra(4) minus_minus 
                      mult.commute of_real_1 of_real_eq_iff of_real_minus)
        next
          def x\<equiv>"\<lambda>a. (a*(1-R)-1) *\<^sub>R \<i>"
          have "Im y \<ge>0" when "y \<in> path_image (g R)" for y
          proof -
            have "y \<in> path_image (CR R) \<Longrightarrow> ?thesis" 
              using `R>1` unfolding CR_def
              apply (auto simp add:path_image_part_circlepath Im_exp)
              by (simp add: sin_ge_zero)
            moreover have "y\<in>path_image (L R) \<Longrightarrow> ?thesis"  
              using L_sub_R[of R] using complex_is_Real_iff by auto 
            ultimately show ?thesis 
              using that path_image_join_subset unfolding g_def by auto
          qed
          moreover have "Im (x a)<0" when "a>0" for a
          proof -
            have "a*(1-R) < 0"
              using that `R>1` by (auto intro:mult_pos_neg)
            hence "a*(1-R) < 1" by auto
            thus ?thesis unfolding x_def by auto
          qed
          ultimately have "\<forall>a>0. x a \<notin> path_image (g R)" 
            by fastforce
          then show "- \<i> + complex_of_real a * (- R * \<i> - - \<i>) \<notin> path_image (g R)"
            when "a>0" for a using that  unfolding x_def scaleR_conv_of_real
            by (auto simp add:field_simps)
        qed
        moreover have "winding_number (g R) (- \<i>) \<in> \<int>" using pole_g
          by (auto intro!: integer_winding_number valid_g[THEN valid_path_imp_path])
        ultimately show ?thesis by (auto simp: Ints_def)
      qed
      def c\<equiv>"2 * pi * \<i>"
      have "contour_integral (g R) f' = c * (winding_number (g R) \<i> * residue f' \<i> 
              + winding_number (g R) (- \<i>) * residue f' (- \<i>))"
      proof (rule Residue_theorem[of "UNIV::complex set" "{\<i>,-\<i>}" f' "g R",folded c_def
                ,simplified])
        show "connected (UNIV::complex set)" by auto
        show "f' holomorphic_on UNIV - {\<i>, - \<i>}" 
          unfolding f'_def
          apply (intro holomorphic_intros)
          by (metis DiffE add_neg_numeral_special(8) add_right_cancel insertCI 
                  power2_eq_iff power2_i)
        show "path_image (g R) \<subseteq> UNIV - {\<i>, - \<i>}" using pole_g by auto
      qed
      also have "... =  c * residue f' \<i>" using W1 W0 by auto
      also have "... = pi" 
      proof -
        have "residue (\<lambda>w. inverse (w + \<i>) / (w - \<i>)) \<i> = - (\<i> / 2)"
        proof (rule residue_simple[of "-{-\<i>}" \<i> "\<lambda>w. inverse (w+\<i>)",simplified])
          show "open (- {- \<i>})" by auto
          show "(\<lambda>w. inverse (w + \<i>)) holomorphic_on - {- \<i>}"
            apply (auto intro!: holomorphic_intros)
            by (simp add: eq_neg_iff_add_eq_0)
        qed
        moreover have "(\<lambda>w. inverse (w + \<i>) / (w - \<i>)) = f'" unfolding f'_def
          apply (rule ext)
          by (auto simp add:field_simps power2_eq_square)
        ultimately show ?thesis unfolding c_def by auto
      qed
      finally show ?thesis .
    qed
    then show ?thesis
      apply (auto intro!: Lim_eventually simp add:eventually_at_top_dense)
      by auto
  qed
  finally have "((\<lambda>R. integral {- R..R} (\<lambda>x. 1 / (x\<^sup>2 + 1))) \<longlongrightarrow> pi) at_top" 
    unfolding f_def .
  then show ?thesis 
    by (auto intro!: tendsto_Lim simp add: trivial_limit_at_top_linorder)
qed


end
(* 
  File:   Projection.thy
  Author: Wenda Li, University of Cambridge
  
  The projection theorem of CAD in bivariate case
*)

section \<open>Bivariate Projection of CAD\<close>

theory Projection imports
  Analysis
  "../Winding_Number_Eval/Missing_Algebraic"
  "../Real_Algebraic_Numbers/Bivariate_Poly"
begin

subsection \<open>Misc\<close>

fun p_one::"nat \<Rightarrow> 'a::comm_semiring_1 poly" where
  "p_one 0 = 1" |
  "p_one (Suc n) = pCons 1 (p_one n)"

lemma degree_p_one[simp]:"degree (p_one n) = n"
  by (induct n,auto)

lemma coeff_p_one:"coeff (p_one n) i = (if i\<le>n then 1 else 0)"
  apply (induct n arbitrary:i)
  apply simp 
  apply (case_tac i)
  by auto

(*refined version?*)
lemma closed_sphere [iff]: "closed (sphere x e)" 
proof -
  have "closed (dist x -` {e})"
    by (intro closed_vimage closed_atMost continuous_intros)
  also have "dist x -` {e} = sphere x e"
    by auto
  finally show ?thesis .
qed

(*refined version?*)
lemma compact_sphere[simp]:
  fixes x::"'a::heine_borel"
  shows "compact (sphere x e)"
using closed_Int_compact[OF closed_sphere compact_cball,of x e x e] sphere_cball[of x e] 
by (simp add: inf_absorb1)

lemma sphere_empty_iff:
  fixes x :: "'a::euclidean_space"
  shows "sphere x e = {} \<longleftrightarrow> e<0" 
proof 
  show "e < 0 \<Longrightarrow> sphere x e = {}" by auto
next
  assume asm:"sphere x e = {}"
  have False when "e\<ge>0"
  proof -
    obtain r::'a where "norm r= e" using vector_choose_size[OF `e\<ge>0`] by auto       
    then have "x+r\<in>sphere x e" by (simp add: dist_norm)
    thus False using asm by auto
  qed
  then show "e<0" by fastforce
qed

lemma degree_normalize[simp]:
  "degree (normalize p) = degree p"
  apply (cases "p=0")
  subgoal by auto
  subgoal unfolding normalize_poly_eq_map_poly
    apply (rule map_poly_degree_eq)
    by (metis (no_types, lifting) coeff_normalize degree_mult_eq degree_pCons_eq_if 
        leading_coeff_0_iff normalize_eq_0_iff normalize_idem normalize_mult_unit_factor 
        unit_factor_eq_0_iff unit_factor_poly_def)
  done

lemma order_normalize[simp]:
  "order z (normalize p) = order z p"
by (metis dvd_normalize_iff normalize_eq_0_iff order_1 order_2 order_unique_lemma)

lemma gcd_order_min:
  assumes "p\<noteq>0" "q\<noteq>0"
  shows "order z (gcd p q) = min (order z p) (order z q)" using assms
proof (induct "degree(gcd p q)" arbitrary:p q rule:less_induct)
  case less
  define zgcd where "zgcd=[:- z, 1:] ^ order z (gcd p q)"
  have "gcd p q\<noteq>0" using \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> by auto
  then obtain r where decomp_r:"gcd p q = zgcd * r"
      and "\<not> [:- z, 1:] dvd r"
    using order_decomp[of "gcd p q" z] unfolding zgcd_def by auto
  have "order z (gcd p q) = 0 \<Longrightarrow> ?case" 
    using \<open>\<not> [:- z, 1:] dvd r\<close> order_0I poly_eq_0_iff_dvd gcd_factorial_greatest 
      decomp_r[unfolded zgcd_def] 
    by fastforce
  moreover have ?case when "order z (gcd p q) \<noteq> 0"
  proof -
    have "zgcd dvd p" "zgcd dvd q" using decomp_r dvdI 
      by (metis gcd_greatest_iff)+
    then obtain rp rq where p_rp:"p=zgcd * rp" and q_rq: "q=zgcd * rq" by (auto simp add:dvd_def)
    have [simp]: "rp \<noteq> 0" "rq \<noteq> 0" "zgcd\<noteq>0" "gcd rp rq \<noteq>0" 
      using \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> p_rp q_rq by auto
    have "order z (gcd rp rq) = min (order z rp) (order z rq)"
    proof (rule less.hyps)
      show "rp \<noteq> 0" "rq \<noteq> 0" by auto
    next
      have "degree zgcd > 0" unfolding zgcd_def
        using that by (simp add: degree_linear_power)
      then show "degree (gcd rp rq) < degree (gcd p q)"
        unfolding p_rp q_rq
        by (auto simp add:gcd_mult_left degree_mult_eq)
    qed
    thus ?case unfolding p_rp q_rq by (auto simp add:gcd_mult_left order_mult)
  qed
  ultimately show ?case by blast
qed

lemma constant_on_forall:
  "f constant_on S \<Longrightarrow> a\<in>S \<Longrightarrow> \<forall>x\<in>S. f x = f a" unfolding constant_on_def by auto

lemma constant_on_cong:
  "(\<And>x. x\<in>S \<Longrightarrow> f x = g x) \<Longrightarrow> g constant_on S \<Longrightarrow> f constant_on S" 
  unfolding constant_on_def by auto

lemma sum_bounded_below_equal:
  fixes g f::"_ \<Rightarrow> 'a::{comm_semiring_1_cancel,linordered_ring}"
  assumes lb: "\<And>i. i\<in>A \<Longrightarrow> g i \<le> f i" and ub:"sum f A \<le> sum g A" and "finite A"
  shows "\<forall>i\<in>A. f i=g i" 
proof (rule ccontr)
  assume "\<not> (\<forall>i\<in>A. f i = g i)"
  then obtain j where "j\<in>A" "f j\<noteq>g j" by auto
  hence "f j>g j" using lb[of j] by auto 
  have "sum f A \<le> sum g A" using ub .
  also have "... = sum g (A - {j}) + g j" using \<open>j\<in>A\<close> \<open>finite A\<close> by (simp add:sum.remove)
  also have "... \<le> sum f (A - {j}) + g j" 
    using sum_mono[OF lb, of "A-{j}"] by auto
  also have "... <  sum f (A - {j}) + f j" using \<open>f j>g j\<close> by auto
  also have "... = sum f A"  using \<open>j\<in>A\<close> \<open>finite A\<close> by (simp add:sum.remove)
  finally have "sum f A < sum f A" .
  thus False by simp
qed 

lemma card_UNION_equal:
  assumes card_eq:"\<forall>x\<in>F. card (A x) = card (B x)" and
    disj_A:"disjoint_family_on A F" and
    disj_B:"disjoint_family_on B F" and
    "finite F" and
    finite_A:"\<forall>x\<in>F. finite (A x)" and
    finite_B:"\<forall>x\<in>F. finite (B x)"
  shows "card (\<Union>x\<in>F. A x) =  card (\<Union>x\<in>F. B x)"
proof -
  have "card (\<Union>x\<in>F. A x) = (\<Sum>i\<in>F. card (A i)) "
    using card_UN_disjoint[OF \<open>finite F\<close> finite_A,folded disjoint_family_on_def, OF disj_A] .
  also have "... = (\<Sum>i\<in>F. card (B i))"
    using card_eq by auto
  also have "... = card (\<Union>x\<in>F. B x)"
    using card_UN_disjoint[OF \<open>finite F\<close> finite_B,folded disjoint_family_on_def, OF disj_B]
    by simp
  finally show ?thesis .
qed

lemma of_real_roots_within:
  fixes p::"real poly" 
  assumes "p\<noteq>0"
  shows "(of_real:: real \<Rightarrow> 'a::{real_algebra_1,field}) ` (proots p) = proots_within (of_real_poly p) \<real>"
    using assms
proof (induct rule:poly_root_induct[where p=p and P="\<lambda>_. True"])
  case 0
  then show ?case by simp
next
  case (no_roots p)
  moreover have False when non_empty:"proots_within (of_real_poly p) \<real> \<noteq>({}::'a set)" and "proots p={}"
  proof -
    obtain r::'a where "r\<in>proots_within (of_real_poly p) \<real>" using non_empty by blast
    then obtain r' where  "poly (of_real_poly p) (of_real r') = (0::'a)"
      using Reals_cases by (metis proots_within_iff)
    hence "poly p r' =0" using of_real_poly_poly
      by (metis of_real_eq_0_iff)
    hence "r'\<in>proots p" unfolding roots_within_def by auto
    thus False using \<open>proots p={}\<close> by auto
  qed
  ultimately show ?case unfolding proots_within_def by auto
next
  case (root a p)
  then have "p\<noteq>0" by auto
  moreover have "of_real ` proots [:a, - 1:] = proots_within [:of_real a, - 1:] (\<real>::'a set)"
    unfolding roots_within_def by auto
  ultimately show ?case 
    unfolding proots_within_times of_real_poly_mult image_Un by (auto simp add: root(2))
qed


lemma cnj_poly:
  "cnj (poly p x) = poly (map_poly cnj p) (cnj x)"
  apply (induct p)
  by (auto simp add:map_poly_pCons)

lemma dist_cnj[simp]:
  "dist (cnj x) (cnj y) = dist x y"
unfolding dist_norm by (metis complex_cnj_diff complex_mod_cnj)

text \<open>maybe be worth having a specialized version, though there exists a more generalized version 
@{thm Sup_class.SUP_cong} which is not easy to find\<close>
lemma UNION_cong: 
  "A=B \<Longrightarrow> (\<And>i. i\<in>A \<Longrightarrow> f i = g i) \<Longrightarrow> (\<Union>i\<in>A. f i) = (\<Union>i\<in>B. g i)"
by auto

subsection \<open>Extra lemmas about disjoint sets\<close>

lemma disjoint_ball_max:
  assumes disjoint:"ball x e1 \<inter> ball y e2 = {}" and "e1>0" "e2>0"
  shows "dist x y\<ge> max e1 e2" 
proof -
  have dist:"\<forall>z. dist x z\<ge>e1 \<or> dist y z\<ge>e2" 
    unfolding ball_def
    by (metis IntI disjoint empty_iff mem_ball not_le)
  have "dist x y \<ge>e1" using dist[rule_format,of y] \<open>e2>0\<close> by auto
  moreover have "dist x y \<ge> e2" using dist[rule_format, of x] \<open>e1>0\<close>  
    by (auto simp add:dist_commute)
  ultimately show ?thesis by auto
qed

lemma disjoint_ball_plus:
  fixes x::"'a::real_normed_vector"
  assumes disjoint:"ball x e1 \<inter> ball y e2 = {}" and "e1>0" "e2>0"
  shows "dist x y \<ge> e1 + e2" 
proof (rule ccontr)
  define d where "d=dist x y"
  assume "\<not> e1 + e2 \<le> d"
  hence "e1+e2 > d" by auto
  have "d>0" using disjoint assms unfolding d_def 
    by (metis IntI centre_in_ball dist_nz empty_iff)
  have "max 0 (1-e1/d) < min 1 (e2 / d)" using \<open>e1+e2>d\<close> \<open>d>0\<close>
    by (auto simp add:field_simps \<open>e1>0\<close> \<open>e2>0\<close> )
  then obtain u where  u:"u>0" "u<1" "u>1-e1/d" "u<e2/d"
    apply (drule_tac dense)
    by auto
  define z where "z=u *\<^sub>R x + (1-u) *\<^sub>R y"
  have "z\<in>ball x e1"
  proof -
    have "norm (x - (u *\<^sub>R x + (1 - u) *\<^sub>R y)) = norm ((1-u) *\<^sub>R (x-y))"
      by (auto simp add:algebra_simps simp del:norm_scaleR)
    also have "... = (1-u) * d" using \<open>u<1\<close> unfolding d_def
      by (auto simp add:dist_norm)
    also have "... < e1 " using u \<open>d>0\<close>
      by (auto simp add:field_simps)
    finally show ?thesis unfolding z_def
      by (auto simp add:dist_norm)
  qed
  moreover have "z\<in>ball y e2" 
  proof -
    have "norm (y - (u *\<^sub>R x + (1 - u) *\<^sub>R y)) = norm (u *\<^sub>R (y-x))"
      by (auto simp add:algebra_simps simp del:norm_scaleR)
    also have "... = u * d" using \<open>u>0\<close> unfolding d_def
      by (auto simp add:dist_norm norm_minus_commute)
    also have "... < e2 " using u \<open>d>0\<close>
      by (auto simp add:field_simps)
    finally show ?thesis unfolding z_def
      by (auto simp add:dist_norm)
  qed
  ultimately show False using disjoint by auto
qed

lemma disjoint_insert_Union:
  "disjoint (insert x F) \<Longrightarrow> x\<notin>F  \<Longrightarrow> x \<inter> \<Union> F ={}"
unfolding disjoint_def by auto

lemma disj_family_insert:
  "disjoint_family_on f (insert x F) 
  \<longleftrightarrow> ((\<forall>y. y \<in> F \<and> y \<noteq> x \<longrightarrow> (f y \<inter> f x = {})) \<and> disjoint_family_on f F)"
unfolding disjoint_family_on_def
by blast

lemma disj_family_insert_UNION:
  "disjoint_family_on f (insert x F) \<Longrightarrow> x\<notin>F \<Longrightarrow> f x \<inter> (\<Union>i\<in>F. f i) = {}"
  unfolding disjoint_family_on_def by auto

lemma proots_count_disj_UNION:
  assumes "disjoint_family_on f S" "finite S" "p\<noteq>0"
  shows "proots_count p (\<Union>i\<in>S. f i) = sum (\<lambda>i. proots_count p (f i)) S" 
  using \<open>disjoint_family_on f S\<close>
proof (induct rule:finite_induct[OF \<open>finite S\<close>])
  case 1
  show ?case by auto
next
  case (2 x F)
  have "proots_count p (\<Union>i\<in>insert x F. f i) = proots_count p (f x \<union> (\<Union>i\<in>F. f i))" by auto
  also have "... = proots_count p (f x) + proots_count p ((\<Union>i\<in>F. f i))" 
    using disj_family_insert_UNION[OF \<open>disjoint_family_on f (insert x F)\<close> \<open>x\<notin>F\<close>] 
      proots_count_disj[OF _ \<open>p\<noteq>0\<close>]
    by auto
  also have "... = proots_count p (f x) +  sum (\<lambda>i. proots_count p (f i)) F"
    using 2 by (simp add: disj_family_insert)
  also have "... = sum (\<lambda>i. proots_count p (f i)) (insert x F)" 
    using sum.insert[OF \<open>finite F\<close> \<open>x\<notin>F\<close>,of "\<lambda>i. proots_count p (f i)"] by simp
  finally show ?case .
qed

lemma proots_count_disj_Union:
  assumes "disjoint S" "finite S" "p\<noteq>0"
  shows "proots_count p (\<Union>S) = sum (\<lambda>s. proots_count p s) S"
using proots_count_disj_UNION[OF _ \<open>finite S\<close> \<open>p\<noteq>0\<close>, of id,simplified] 
  disjoint_image_disjoint_family_on[of id,simplified,OF \<open>disjoint S\<close>]
  by simp


lemma small_enough_cballs:
  assumes "finite S "
  shows "\<exists>\<epsilon>>0. \<forall>x\<in>S. cball x \<epsilon> \<inter> S = {x}" using assms 
proof (induct S)
  case empty
  show ?case by (auto intro:exI[where x=1])
next
  case (insert a S)
  then obtain \<epsilon>1 where "\<epsilon>1>0" and \<epsilon>1_Int: "\<forall>x\<in>S. cball x \<epsilon>1 \<inter> S = {x}" by auto
  obtain \<epsilon>2 where "\<epsilon>2>0" and \<epsilon>2_dist:"\<forall>x\<in>S. \<epsilon>2 \<le> dist a x" 
    using finite_set_avoid[OF \<open>finite S\<close>, of a] \<open>a\<notin>S\<close> by fast
  define \<epsilon> where "\<epsilon>=min \<epsilon>1 (\<epsilon>2/2)" 
  have "\<epsilon>>0" unfolding \<epsilon>_def using \<open>\<epsilon>1>0\<close> \<open>\<epsilon>2>0\<close> by auto
  moreover have "\<forall>x\<in>insert a S. cball x \<epsilon> \<inter> insert a S = {x}" 
  proof 
    fix x assume "x \<in> insert a S"
    have "cball x \<epsilon> \<inter> insert a S = {x}" when "x=a" 
      using \<epsilon>2_dist that \<open>\<epsilon>1>0\<close> \<open>\<epsilon>2>0\<close>  unfolding \<epsilon>_def by auto
    moreover have "cball x \<epsilon> \<inter> insert a S = {x}" when "x\<in>S" 
    proof (subst Int_insert_right_if0)
      show "a \<notin> cball x \<epsilon>" 
        unfolding \<epsilon>_def using \<epsilon>2_dist[rule_format,OF that] \<open>\<epsilon>1>0\<close> \<open>\<epsilon>2>0\<close>
        by (auto simp add:dist_commute)
    next
      show "cball x \<epsilon> \<inter> S = {x}"
        using \<epsilon>1_Int[rule_format,OF that] \<open>\<epsilon>1>0\<close> \<open>\<epsilon>2>0\<close> unfolding \<epsilon>_def by fastforce
    qed
    ultimately show "cball x \<epsilon> \<inter> insert a S = {x}" using \<open>x \<in> insert a S\<close> by blast 
  qed
  ultimately show ?case by auto
qed

lemma small_enough_disjoint:
  fixes S::"'a::metric_space set"
  assumes "finite S "
  shows "\<exists>\<epsilon>>0. \<forall>x\<in>S. \<forall>y\<in>S. x\<noteq>y \<longrightarrow> ball x \<epsilon> \<inter> ball y \<epsilon> = {}" using assms 
proof (induct S)
  case empty
  show ?case by (auto intro:exI[where x=1])
next
  case (insert a S)
  then obtain \<epsilon>1 where "\<epsilon>1>0" and \<epsilon>1_Int: "\<forall>x\<in>S. \<forall>y\<in>S. x \<noteq> y \<longrightarrow> ball x \<epsilon>1 \<inter> ball y \<epsilon>1 = {}" by auto
  obtain \<epsilon>2 where "\<epsilon>2>0" and \<epsilon>2_dist:"\<forall>x\<in>S. \<epsilon>2 \<le> dist a x" 
    using finite_set_avoid[OF \<open>finite S\<close>, of a] \<open>a\<notin>S\<close> by fast
  define \<epsilon> where "\<epsilon>=min \<epsilon>1 (\<epsilon>2/2)" 
  have "\<epsilon>>0" unfolding \<epsilon>_def using \<open>\<epsilon>1>0\<close> \<open>\<epsilon>2>0\<close> by auto
  moreover have "\<forall>x\<in>insert a S. \<forall>y\<in>insert a S. x \<noteq> y \<longrightarrow> ball x \<epsilon> \<inter> ball y \<epsilon> = {}"
  proof clarify
    fix x y assume asm:"x \<in> insert a S" "y \<in> insert a S" and "x \<noteq> y"
    let ?thesis="ball x \<epsilon> \<inter> ball y \<epsilon> = {}"      
    have avoid:"\<forall>y\<in>S. ball a \<epsilon> \<inter> ball y \<epsilon> = {}" 
      using \<epsilon>2_dist unfolding \<epsilon>_def
      using dist_triangle_half_l by fastforce
    have ?thesis when "x=a" "y\<in>S" using avoid that by auto
    moreover have ?thesis when "y=a" "x\<in>S" 
      using avoid[rule_format,OF \<open>x\<in>S\<close>] \<open>y=a\<close> by auto
    moreover have ?thesis when "x\<in>S" "y\<in>S" 
      using \<epsilon>1_Int[rule_format,OF that \<open>x\<noteq>y\<close>] unfolding \<epsilon>_def 
      by auto
    moreover have ?thesis when "x=a" "y=a" using \<open>x\<noteq>y\<close> that by auto
    ultimately show ?thesis using asm \<open>\<epsilon>>0\<close> by auto
  qed
  ultimately show ?case by auto
qed

lemma disjoint_family_UNION_distrib:
  assumes "disjoint_family_on f (S1\<union>S2)" 
  shows "(\<Union>i\<in>S1. f i) \<inter> (\<Union>i\<in>S2. f i) =  (\<Union>i\<in>S1 \<inter> S2. f i)"
 using assms
unfolding disjoint_family_on_def
apply auto
by (metis IntI UnCI empty_iff)

subsection \<open>Continuous dependence of polynomial roots on the coefficients\<close>

theorem continuous_dependence:
  fixes p::"complex poly" and \<epsilon>::real
  defines "n\<equiv>degree p"              
  assumes "\<epsilon>>0" and "p\<noteq>0" and
    disjoint_n:"\<forall>r\<in>proots p. proots_within p (cball r \<epsilon>) = {r}"
  shows "\<exists>\<delta>>0. \<forall>q. degree q=n \<and> q\<noteq>0 \<and> (\<forall>i\<le>n. cmod(coeff q i - coeff p i)<\<delta>) 
          \<longrightarrow> (\<forall>r\<in>proots p. proots_count q (ball r \<epsilon>) = order r p)" 
proof (cases "degree p=0")
  case True
  then obtain c where "p=[:c:]" using degree_eq_zeroE by auto
  then have "proots p = {}" and "n=0" and "c\<noteq>0" 
    unfolding n_def roots_within_def using `p\<noteq>0` by auto
  then show ?thesis by (auto intro:exI[where x=1])
next
  case False
  define C where  "C\<equiv>\<lambda>r::complex. sphere r \<epsilon>"
  define V1' where "V1'\<equiv>\<lambda>r. {cmod(poly p z) | z. z\<in>C r}"
  define V1 where "V1\<equiv>\<lambda>r. Inf {cmod(poly p z) | z. z\<in>C r}"
  define V2' where "V2'\<equiv>\<lambda>r. {\<Sum>i\<le>n. cmod (z^i) | z. z\<in>C r}"
  define V2 where  "V2\<equiv>\<lambda>r. Sup (V2' r)"  
  have "C r \<noteq> {}" for r unfolding C_def using `\<epsilon>>0` sphere_empty_iff order.asym by blast 
  have V1_pos:"V1 r>0" when "r\<in>proots p" for r
  proof -
    define f where  "f\<equiv>\<lambda>z. cmod (poly p z)"
    have False when "poly p z=0" and "z\<in>C r" for z
    proof -
      have "z\<in>proots_within p (cball r \<epsilon>)" using that unfolding C_def 
        by auto
       moreover have "r\<in>proots_within p (cball r \<epsilon>)" using `r\<in>proots p` `\<epsilon>>0` 
         by (auto simp add:proots_within_iff) 
       moreover have "r\<noteq>z" using `z\<in>C r` `\<epsilon>>0` unfolding C_def by auto
       ultimately show False using disjoint_n[rule_format,OF `r\<in>proots p`] by auto
    qed
    hence "\<forall>x\<in>f`C r. x>0" unfolding f_def by auto
    moreover have "Inf (f ` C r) \<in> f ` C r"
    proof (rule closed_contains_Inf)
      show "f ` C r \<noteq> {}" using `C r\<noteq>{}` by auto
    next
      have "compact (f ` C r)" 
      proof (rule compact_continuous_image)
        show "compact (C r)" unfolding C_def by auto
        show "continuous_on (C r) f" unfolding f_def by (intro continuous_intros)
      qed
      then show "closed (f ` C r)" and "bdd_below (f ` C r)" 
        by (auto simp add:compact_eq_bounded_closed bounded_imp_bdd_below)
    qed
    moreover have "Inf (f ` C r) = V1 r" unfolding V1_def f_def by (simp add: setcompr_eq_image)
    ultimately show ?thesis by auto
  qed
  have V2_pos:"V2 r>0" and V2_upper:"\<forall>x\<in>V2' r. x\<le>V2 r" for r
  proof -
    define f where "f\<equiv>\<lambda>z. \<Sum>i\<le>n. cmod (z ^ i)"
    have f_V2':"f ` C r = V2' r" unfolding V2'_def f_def by auto
    have "bounded (C r)"  
      unfolding C_def using `\<epsilon>>0`
      by (meson bounded_cball bounded_subset sphere_cball)
    then obtain lb where lb_bound:"\<forall>z\<in>C r. norm z \<le> lb" unfolding C_def using bounded_iff by blast
    have bdd:"bdd_above (f ` C r)"
    proof -
      have "\<exists>m. \<forall>z\<in> C r. f z\<le>m" unfolding f_def
      proof (induct n)
        case 0
        show ?case by (auto intro:exI[where x=2])
      next
        case (Suc n)
        then obtain m1 where m1_bound:"\<forall>z\<in>C r. (\<Sum>i\<le>n. cmod (z ^ i)) \<le> m1" by auto
        moreover have "\<forall>z\<in>C r. cmod (z * z ^ n) \<le> lb^(Suc n)" using lb_bound
          by (metis norm_ge_zero norm_power power_Suc power_mono)
        ultimately show ?case 
          apply (auto intro!:exI[where x="m1+lb^(Suc n)"])
          by fastforce
      qed
      then obtain m where "\<forall>z\<in> C r. f z\<le>m" by auto
      then show "bdd_above (f ` C r)" by (auto intro!: bdd_aboveI2) 
    qed
    show "\<forall>x\<in>V2' r. x\<le>V2 r"
      unfolding V2_def using cSup_upper[OF _ bdd,unfolded f_V2']
      by auto        
    have "Sup (f ` C r) > 0"
    proof (subst less_cSup_iff[OF _ bdd])
      show "f ` C r \<noteq> {}" using `C r \<noteq> {}` by auto
    next
      obtain z where "z\<in>C r" using `C r\<noteq>{}` by auto
      moreover have "1 \<le> f z" unfolding f_def 
        apply (induct n)
        apply auto
        using order_trans by fastforce
      ultimately show "Bex (f ` C r) (op < 0)" by (auto intro!: bexI[where x=z])
    qed
    then show "V2 r>0" using f_V2' unfolding V2_def by metis
  qed
  have "\<exists>\<delta>>0. \<forall>r\<in>proots p. \<delta> * V2 r \<le> V1 r" 
  proof -
    define f where "f\<equiv>\<lambda>r. V1 r / V2 r"
    define \<delta> where "\<delta>\<equiv>Min (f ` proots p)"
    have "finite (f ` proots p)" by (simp add: assms(3))
    moreover have "f ` proots p \<noteq> {}" 
    proof -
      have "\<not> constant (poly p)" using constant_degree False by force
      then have "\<exists>z. poly p z = 0" 
        using Fundamental_Theorem_Algebra.fundamental_theorem_of_algebra by auto
      then have "proots p\<noteq>{}" using roots_within_def by auto
      thus ?thesis by auto
    qed
    moreover have "\<forall>x\<in>f ` proots p. 0 < x" using V1_pos V2_pos unfolding f_def by auto
    ultimately have "\<delta>>0" unfolding \<delta>_def by simp
    moreover have "\<delta> * V2 r \<le> V1 r" when "r\<in>proots p" for r
    proof -
      have "\<delta>\<le>f r" unfolding \<delta>_def using `r\<in>proots p` \<open>finite (f ` proots p)\<close> by auto 
      thus ?thesis unfolding f_def using V1_pos[OF that] V2_pos[of r] 
        using pos_le_divide_eq by auto
    qed
    ultimately show ?thesis by auto
  qed
  then obtain \<delta> where "\<delta>>0" and \<delta>_def:"\<forall>r\<in>proots p. \<delta> * V2 r \<le> V1 r" by auto
  show ?thesis
  proof (intro exI[where x=\<delta>],auto simp add:\<open>\<delta>>0\<close>)
    fix q r assume "poly p r = 0"  and q_deg:"n=degree q" and "q\<noteq>0" 
        and "\<forall>i\<le>degree q. cmod (coeff q i - coeff p i) < \<delta>"
    then have coeff_diff:"\<forall>i\<le>n. cmod (coeff q i - coeff p i) < \<delta>" by auto
    define W where "W\<equiv>winding_number (circlepath r \<epsilon>)" 
    define R where "R\<equiv>\<lambda>p. proots_within p (ball r \<epsilon>)"
    have cmod_less:"\<forall>z\<in>sphere r \<epsilon>. cmod (poly q z - poly p z) < cmod (poly p z)" 
    proof 
      fix z assume "z \<in> sphere r \<epsilon> "
      hence "z\<in>C r" unfolding C_def using `\<epsilon>>0` by auto
      have "cmod (poly q z - poly p z) = cmod (\<Sum>i\<le>n. (coeff q i -coeff p i) * z^i)"
        unfolding poly_altdef q_deg n_def[symmetric]
        by (auto simp add:sum_subtractf[symmetric] algebra_simps)
      also have "... \<le> (\<Sum>i\<le>n. cmod ((coeff q i -coeff p i) * z^i))"
        by (simp add:norm_sum)
      also have "... \<le> (\<Sum>i\<le>n. cmod (coeff q i -coeff p i) * cmod (z^i))"
        using norm_mult_ineq by (rule sum_mono)
      also have "... < (\<Sum>i\<le>n. \<delta> * cmod (z^i))" using coeff_diff  
      proof -
        define f where "f\<equiv>\<lambda>i. cmod (coeff q i - coeff p i) * cmod (z ^ i)"
        define g where "g\<equiv>\<lambda>i. \<delta> * cmod (z ^ i)"
        have "f 0 < g 0" 
          unfolding f_def g_def using coeff_diff by simp
        moreover have " sum f {Suc 0..n} \<le>  sum g {Suc 0..n}" unfolding f_def g_def
          using coeff_diff by (auto intro!: sum_mono mult_right_mono)                
        ultimately have "f 0 + sum f {Suc 0..n} < g 0 + sum g {Suc 0..n}"
          by auto
        hence "sum f {..n} < sum g {..n}" 
          apply (subst (1 2) sum_head_Suc[of 0 n,unfolded atLeast0AtMost,simplified])
          by auto
        then show ?thesis unfolding f_def g_def .
      qed
      also have "... = \<delta> * (\<Sum>i\<le>n. cmod (z^i))"
        by (simp add: sum_distrib_left)
      also have "... \<le> \<delta> * V2 r" using `z\<in>C r`
        apply (intro mult_left_mono[OF _ less_imp_le[OF \<open>\<delta>>0\<close>]])
        apply (intro V2_upper[rule_format,unfolded V2'_def])
        by auto
      also have "... \<le> V1 r"
        using \<delta>_def \<open>poly p r=0\<close> by auto
      also have "... \<le> cmod (poly p z)" unfolding V1_def
      proof (rule cInf_lower)
        show "cmod (poly p z) \<in> {cmod (poly p z) |z. z \<in> C r}" 
          using `z \<in> C r` by blast
      next
        show "bdd_below {cmod (poly p z) |z. z \<in> C r}" unfolding bdd_below_def
          by (auto intro: exI[where x=0])
      qed
      finally show "cmod (poly q z - poly p z) < cmod (poly p z)" .
    qed
    have "(\<Sum>z | poly q z = 0. W z * zorder (poly q) z) 
            = (\<Sum>z | poly p z = 0. W z * zorder (poly p) z)"
      unfolding W_def roots_within_def
    proof (rule Rouche_theorem[of UNIV "poly p" "poly (q-p)" "circlepath r \<epsilon>",simplified])
      show "connected (UNIV::complex set)" using connected_UNIV by auto
      show "finite {z. poly q z = 0}" and "finite {z. poly p z = 0}" 
        using `q\<noteq>0` `p\<noteq>0` poly_roots_finite by auto
      show "\<forall>z\<in>sphere r \<bar>\<epsilon>\<bar>. cmod (poly q z - poly p z) < cmod (poly p z)"
        using cmod_less `\<epsilon>>0` by auto
    qed
    moreover have "(\<Sum>z | poly q z = 0. W z * zorder (poly q) z) = (\<Sum>x\<in>R q. of_nat (order x q))" 
    proof (rule sum.mono_neutral_cong_right)
      show "finite {z. poly q z = 0}" using poly_roots_finite `q\<noteq>0` by auto 
      show "R q \<subseteq> {z. poly q z = 0}" unfolding roots_within_def R_def by auto
      show "\<forall>i\<in>{z. poly q z = 0} - R q. W i * of_nat (zorder (poly q) i) = 0"
      proof 
        fix z assume "z \<in> {z. poly q z = 0} - R q"
        hence "poly q z=0" and "z\<notin>ball r \<epsilon>" unfolding roots_within_def R_def by auto
        have "z\<notin>sphere r \<epsilon>"
          using cmod_less `poly q z=0` diff_zero norm_minus_commute by fastforce
        hence "z\<notin>cball r \<epsilon>" using `z\<notin>ball r \<epsilon>` by auto  
        hence "W z=0"
          unfolding W_def using `\<epsilon>>0`
          by (intro winding_number_zero_outside[where s="cball r \<epsilon>"],auto)
        thus "W z * of_nat (zorder (poly q) z) = 0" by auto
      qed
      show "W z * of_nat (zorder (poly q) z) = of_nat (order z q)" when "z \<in> R q" for z
      proof -
        have "poly q z = 0" using that unfolding roots_within_def R_def by auto
        hence "order z q = zorder (poly q) z" using order_zorder[OF _ `q\<noteq>0`]
          by auto
        moreover have "W z=1" 
          using that unfolding W_def roots_within_def R_def
          by (intro winding_number_circlepath,auto simp add:dist_complex_def norm_minus_commute)
        ultimately show ?thesis by auto
      qed
    qed
    moreover have "(\<Sum>z | poly p z = 0. W z * zorder (poly p) z) = (\<Sum>x\<in>R p. of_nat (order x p))" 
      unfolding proots_count_def
    proof (rule sum.mono_neutral_cong_right)
      show "finite {z. poly p z = 0}" using poly_roots_finite `p\<noteq>0` by auto 
      show "R p \<subseteq> {z. poly p z = 0}" unfolding roots_within_def R_def by auto
      show "\<forall>i\<in>{z. poly p z = 0} - R p. W i * of_nat (zorder (poly p) i) = 0"
      proof 
        fix z assume "z \<in> {z. poly p z = 0} - R p"
        hence "poly p z=0" and "z\<notin>ball r \<epsilon>" unfolding roots_within_def R_def by auto
        have "z\<notin>sphere r \<epsilon>"
          using cmod_less `poly p z=0` diff_zero norm_minus_commute by fastforce
        hence "z\<notin>cball r \<epsilon>" using `z\<notin>ball r \<epsilon>` by auto  
        hence "W z=0"
          unfolding W_def using `\<epsilon>>0` 
          by (intro winding_number_zero_outside[where s="cball r \<epsilon>"],auto)
        thus "W z * of_nat (zorder (poly p) z) = 0" by auto
      qed
      show "W z * of_nat (zorder (poly p) z) = of_nat (order z p)" when "z \<in> R p" for z
      proof -
        have "poly p z = 0" using that unfolding roots_within_def R_def by auto
        hence "order z p = zorder (poly p) z" using order_zorder[OF _ `p\<noteq>0`]
          by auto
        moreover have "W z=1" 
          using that unfolding W_def roots_within_def R_def
          by (intro winding_number_circlepath,auto simp add:dist_complex_def norm_minus_commute)
        ultimately show ?thesis by auto
      qed
    qed            
    ultimately have "of_nat (\<Sum>x\<in>R q. (order x q)) = (of_nat (\<Sum>x\<in>R p. (order x p)) ::complex)" 
      by force
    then have "proots_count q (ball r \<epsilon>) = proots_count p (ball r \<epsilon>)" 
      unfolding proots_count_def R_def using of_nat_eq_iff by fast
    moreover have "proots_within p (ball r \<epsilon>) = {r}" 
    proof -
      have "proots_within p (ball r \<epsilon>) = proots_within p (cball r \<epsilon>) - proots_within p (sphere r \<epsilon>)"
        unfolding roots_within_def by auto
      moreover have "r\<notin>proots_within p (sphere r \<epsilon>)" 
        unfolding roots_within_def using \<open>\<epsilon>>0\<close> by auto
      moreover have "proots_within p (cball r \<epsilon>) = {r}"
        using disjoint_n \<open>poly p r=0\<close> by auto 
      ultimately show ?thesis by auto
    qed
    ultimately show "proots_count q (ball r \<epsilon>) = order r p"
      unfolding proots_count_def by auto
  qed
qed

theorem continuous_dependence_finite:
  fixes p::"complex poly" and \<epsilon>::real
  defines "n\<equiv>degree p"              
  assumes "\<epsilon>>0" and "finite S" and
    r_sub:"proots p \<subseteq> S" and
    disjoint:"\<forall>i\<in>S. \<forall>j\<in>S. i\<noteq>j \<longrightarrow> ball i \<epsilon> \<inter> ball j \<epsilon> = {}"
  shows "\<exists>\<delta>>0. \<forall>q. degree q=n \<and> q\<noteq>0 \<and> (\<forall>i\<le>n. cmod(coeff q i - coeff p i)<\<delta>) 
          \<longrightarrow> (\<forall>r\<in>S. proots_count q (ball r \<epsilon>) = order r p)"
proof -
  have "p\<noteq>0" 
    using \<open>finite S\<close> \<open>proots p \<subseteq> S\<close> infinite_UNIV_char_0 infinite_super by fastforce
  moreover have "\<forall>r\<in>proots p. proots_within p (cball r \<epsilon>) = {r}"
  proof 
    fix r assume "r\<in>proots p"
    then have "r\<in>proots_within p (cball r \<epsilon>)"
      unfolding roots_within_def using \<open>\<epsilon>>0\<close> by auto
    moreover have False when "r' \<in> proots_within p (cball r \<epsilon>)" "r'\<noteq>r" for r' 
    proof -
      have "r'\<in>S" using that(1) r_sub unfolding  roots_within_def by auto
      moreover have "r\<in>S" using r_sub \<open>r\<in>proots p\<close> by auto
      ultimately have  "ball r \<epsilon> \<inter> ball r' \<epsilon> = {}" using disjoint \<open>r'\<noteq>r\<close> by auto
      hence "dist r r' \<ge> 2*\<epsilon>" using disjoint_ball_plus[of r \<epsilon> r' \<epsilon>] \<open>\<epsilon>>0\<close> by auto
      hence "r' \<notin> cball r \<epsilon>" using \<open>\<epsilon>>0\<close> by auto
      thus False using that(1) unfolding roots_within_def by auto
    qed
    ultimately show "proots_within p (cball r \<epsilon>) = {r}" by blast
    qed
  ultimately obtain \<delta> where "\<delta>>0" and \<delta>_def:"\<forall>q. degree q = n \<and> q \<noteq> 0 
        \<and> (\<forall>i\<le>n. cmod (coeff q i - coeff p i) < \<delta>) 
      \<longrightarrow> (\<forall>r\<in>proots p. proots_count q (ball r \<epsilon>) = order r p)" 
    using continuous_dependence[OF \<open>\<epsilon>>0\<close>,of p] unfolding n_def by auto
  have "\<forall>r\<in>S. proots_count q (ball r \<epsilon>) = order r p" when 
       "degree q = n"  "q \<noteq> 0"  "\<forall>i\<le>degree q. cmod (coeff q i - coeff p i) < \<delta>"
    for q 
  proof -
    define U where "U \<equiv> \<Union>r\<in>proots p. ball r \<epsilon>" 
    have "proots_count q UNIV = n" 
      using degree_proots_count \<open>degree q=n\<close> by auto
    also have "... = proots_count p UNIV" 
      using degree_proots_count unfolding n_def by auto
    also have "... = sum (\<lambda>r. proots_count q (ball r \<epsilon>)) (proots p)" 
    proof -
      have "\<forall>r\<in>proots p. proots_count q (ball r \<epsilon>) = order r p"
        using \<delta>_def[rule_format,of q] that(1-3) by auto
      thus ?thesis unfolding proots_count_def by auto            
    qed
    also have "... = proots_count q U" unfolding U_def using \<open>proots p \<subseteq> S\<close>
    proof (induct rule:finite_induct[OF finite_proots[OF \<open>p\<noteq>0\<close>]])
      case 1
      thus ?case by auto
    next
      case (2 x F)
      then have "ball x \<epsilon> \<inter> ball i \<epsilon> = {}" when "i\<in>F" for i 
        by (intro disjoint[rule_format],auto simp add:that)
      then have "ball x \<epsilon> \<inter> (\<Union>x\<in>F. ball x \<epsilon>)= {}" 
        by (subst Int_UN_distrib,auto)
      then show ?case using 2 proots_count_disj[OF _ \<open>q\<noteq>0\<close>] by auto
    qed
    finally have "proots_count q UNIV = proots_count q U" .
    hence "proots_count q (- U) = 0"
      using proots_count_disj[of U "-U",simplified,OF \<open>q\<noteq>0\<close>] by auto
    moreover have "\<forall>r\<in>S-proots p. ball r \<epsilon> \<subseteq> - U" 
    proof 
      fix r assume "r \<in> S - proots p"
      then have "ball r \<epsilon> \<inter> ball r' \<epsilon> = {}" when "r'\<in>proots p" for r'
        using \<open>proots p \<subseteq> S\<close> that by (intro disjoint[rule_format], auto)
      then show "ball r \<epsilon> \<subseteq> - U" unfolding U_def
        by blast
    qed
    ultimately have non_root:"\<forall>r\<in>S-proots p. proots_count q (ball r \<epsilon>) = 0"
        using proots_count_subset[OF _ \<open>q\<noteq>0\<close>] by (metis le_zero_eq)
    show ?thesis
    proof (standard,case_tac "r\<in>proots p")
      fix r assume "r \<in> S" "r \<in> proots p"
      then show "proots_count q (ball r \<epsilon>) = order r p"  
        using \<delta>_def[rule_format, of q r] that(1-3) by auto
    next
      fix r assume "r \<in> S" "r \<notin> proots p"
      have "order r p = 0" 
        using \<open>r \<notin> proots p\<close> order_0I by auto
      moreover have "proots_count q (ball r \<epsilon>) = 0"
        using non_root \<open>r\<in>S\<close> \<open>r \<notin> proots p\<close> by auto
      ultimately show "proots_count q (ball r \<epsilon>) = order r p" by auto
    qed
  qed
  thus ?thesis using \<open>\<delta>>0\<close> by auto
qed

(*
lemma of_real_poly_poly_y:
  "of_real_poly (poly_y p y) = poly_y (of_real_bpoly p) (of_real y)"
unfolding of_real_bpoly_def
apply (induct p)
by (auto simp add:coeffs_map_pCons of_real_poly_poly)
*)

(*
lemma setsum_bounded_below_equal:
  fixes K::"'a::{comm_semiring_1_cancel,linordered_ring}"
  assumes lb: "\<And>i. i\<in>A \<Longrightarrow> K \<le> f i" and ub:"setsum f A \<le> of_nat (card A) * K" and "finite A"
  shows "\<forall>i\<in>A. f i=K"
proof (rule ccontr)
  assume "\<not> (\<forall>i\<in>A. f i = K)"
  then obtain j where "j\<in>A" "f j\<noteq>K" by auto
  hence "f j>K" using lb[of j]  by auto  
  have "of_nat (card A) * K <  of_nat (card A) * K + (f j - K)"
    using \<open>f j>K\<close>
    by auto
  also have "... = of_nat (card (A - {j})) * K + f j"
    using \<open>j\<in>A\<close> \<open>finite A\<close>
    apply (auto simp add:algebra_simps )
    by (metis Diff_empty One_nat_def card_Diff_insert empty_iff mult.commute setsum.remove 
      setsum_constant)
  also have "... \<le> setsum f (A - {j}) + f j"
    using setsum_bounded_below[of "A-{j}" K f] lb
    by (meson DiffD1 add_right_mono)
  also have "... = setsum f A "
    using setsum.union_disjoint[of "A-{j}" "{j}" f,simplified,OF \<open>finite A\<close>] \<open>j\<in>A\<close>
    by (simp add: insert_absorb)
  finally have "of_nat (card A) * K < setsum f A" .
  thus False using ub by simp
qed
*)


(*
lemma
  assumes 
    inter_eq: "\<forall>s\<in>S. card (s \<inter> A) = card (s \<inter> B)" and
    "disjoint S"
    "card (A - \<Union>S) = 0"
    "card (B - \<Union>S) = 0"
    "finite A" "finite B" "finite S"
  shows "card A = card B" using assms
proof -
  have "sum (\<lambda>s. card (s \<inter> A)) S = sum (\<lambda>s. card (s \<inter> B)) S"
    using inter_eq by auto  
  have "card (A \<inter> \<Union>S ) = card (B \<inter> \<Union>S)" using inter_eq \<open>disjoint S\<close>
    proof (induct rule:finite_induct[OF \<open>finite S\<close>])
      case 1
      show ?case by auto     
    next
      case (2 x F)
      have "card (A \<inter> \<Union>insert x F) = card ((A \<inter> x) \<union> (A \<inter> \<Union>F))"
        by (simp add: Int_Un_distrib)
      also have "... = card (A \<inter> x) + card (A \<inter> \<Union>F)" 
        apply (intro card_Un_disjoint)
        using \<open>x \<notin> F\<close> \<open>finite A\<close> \<open>finite B\<close> \<open>disjoint (insert x F)\<close> disjoint_insert_Union
        by auto
      also have "... = card (B \<inter> x) + card (B \<inter> \<Union>F)" using 2
        by (simp add: inf_commute pairwise_insert)
      also have "... = card (B \<inter> x \<union> B \<inter> \<Union>F)"
        apply (intro card_Un_disjoint[symmetric])
        using \<open>x \<notin> F\<close> \<open>finite A\<close> \<open>finite B\<close> \<open>disjoint (insert x F)\<close> disjoint_insert_Union
        by auto
      also have "... = card (B \<inter> \<Union>insert x F)"
        by (simp add: Int_Un_distrib)
      finally show ?case .
    qed
  moreover have "card (A \<inter> \<Union>S) = card A" 
    proof -
      have "card A = card (A \<inter> \<Union>S \<union> (A - \<Union>S)) " 
        by (simp add: Int_Diff_Un)  
      also have "... =  card (A \<inter> \<Union>S) + card (A - \<Union>S)"
        using \<open>finite A\<close> 
        apply (intro card_Un_disjoint)
        by auto 
      also have "... = card (A \<inter> \<Union> S)" using \<open>card (A - \<Union>S) = 0\<close> by auto
      finally show ?thesis by simp
    qed
  moreover have "card (B \<inter> \<Union>S) = card B" 
    proof -
      have "card B = card (B \<inter> \<Union>S \<union> (B - \<Union>S)) " 
        by (simp add: Int_Diff_Un)  
      also have "... =  card (B \<inter> \<Union>S) + card (B - \<Union>S)"
        using \<open>finite B\<close> 
        apply (intro card_Un_disjoint)
        by auto 
      also have "... = card (B \<inter> \<Union> S)" using \<open>card (B - \<Union>S) = 0\<close> by auto
      finally show ?thesis by simp
    qed 
  ultimately show ?thesis by auto
qed    
*)


(*
lemma 
  assumes "connected S"
      and opI: "\<And>a. a \<in> S \<Longrightarrow> 
      \<exists>T. open T \<and> a \<in> T \<inter> S \<and> (\<forall>x \<in> T \<inter> S. f x = f a)"
    shows "f constant_on S"
  apply (rule locally_constant_imp_constant[OF assms(1)])
  using opI open_subset by fast
*)

subsection \<open>The projection theorem of CAD (bivariate)\<close>

theorem bivariate_CAD_proj:
  fixes p q :: "real bpoly" and S::"real set"
  defines "pc\<equiv>\<lambda>y. map_poly complex_of_real (poly_y p y)"
  defines "qc\<equiv>\<lambda>y. map_poly complex_of_real (poly_y q y)"
  assumes 
    "connected S" and
    deg_p_inv:"(\<lambda>y. degree (poly_y p y)) constant_on S" and
    pzero_inv:"(\<lambda>y. poly_y p y = 0) constant_on S" and
    distinct_p_inv:
      "(\<lambda>y. (card (proots (pc y)))) constant_on S" and
    deg_q_inv:"(\<lambda>y. degree (poly_y q y)) constant_on S" and
    qzero_inv:"(\<lambda>y. poly_y q y = 0) constant_on S" and
    distinct_q_inv:
      "(\<lambda>y. (card ( proots (qc y)))) constant_on S" and
    common_pq_inv:"(\<lambda>y. degree (gcd (pc y) (qc y))) constant_on S"
  shows "(\<lambda>y. card (proots (poly_y (p*q) y))) constant_on S"
proof (rule locally_constant_imp_constant[OF \<open>connected S\<close>])
  fix a assume "a\<in>S"
  let ?goal = "\<lambda>T. openin (subtopology euclidean S) T \<and> a \<in> T 
    \<and> (\<forall>x\<in>T. card (proots (poly_y (p * q) x)) = card (proots (poly_y (p * q) a)))"  
  have "\<exists>T. ?goal T" when "poly_y p a = 0"
  proof -
    have "\<forall>y\<in>S. poly_y p y = 0" using pzero_inv constant_on_forall \<open>a\<in>S\<close> that 
      by fast
    hence "?goal S"
      by (auto simp add:poly_y_mult constant_on_def that \<open>a\<in>S\<close>)
    thus ?thesis by blast
  qed
  moreover have "\<exists>T. ?goal T" when "poly_y q a = 0" 
  proof -
    have "\<forall>y\<in>S. poly_y q y = 0" using qzero_inv constant_on_forall \<open>a\<in>S\<close> that 
      by fast
    hence "?goal S"
      by (auto simp add:poly_y_mult constant_on_def that \<open>a\<in>S\<close>)
    thus ?thesis by blast
  qed
  moreover have "\<exists>T. ?goal T" when "poly_y p a\<noteq>0" "poly_y q a\<noteq>0"
  proof -
    define pqc where "pqc \<equiv> \<lambda>y. (pc y) * (qc y)"
    define p_rts where "p_rts \<equiv> proots (pc a)"
    define q_rts where "q_rts \<equiv> proots (qc a)"
    define rts where "rts \<equiv> proots (pqc a)"  
    have "pc a\<noteq>0" "qc a\<noteq>0" using that unfolding pc_def qc_def pqc_def by auto
    then have "finite rts" "finite p_rts" "finite q_rts" 
        and "p_rts \<subseteq> rts" "q_rts \<subseteq> rts" 
    unfolding rts_def pqc_def proots_within_times p_rts_def q_rts_def by auto
    then obtain \<epsilon> where "\<epsilon>>0" and \<epsilon>_def:"\<forall>x\<in>rts. \<forall>y\<in>rts. x \<noteq> y \<longrightarrow> ball x \<epsilon> \<inter> ball y \<epsilon> = {}"
      using small_enough_disjoint[of rts] by auto
    have \<epsilon>_sub:"rts' \<inter> ball r \<epsilon> = {r}" when "r\<in>rts'" "rts'\<subseteq>rts" for r rts'  
    proof -
      have False when "r'\<in>rts' \<inter> (ball r \<epsilon>)" "r'\<noteq>r" for r' 
      proof -
        have "r'\<in>rts" using that(1) \<open>rts'\<subseteq>rts\<close> by auto
        moreover have "r\<in>rts" using \<open>r\<in>rts'\<close> \<open>rts'\<subseteq>rts\<close> by blast
        ultimately have "ball r \<epsilon> \<inter> ball r' \<epsilon> = {}" using \<epsilon>_def \<open>r'\<noteq>r\<close> by auto
        hence "dist r r' \<ge> 2*\<epsilon>" using disjoint_ball_plus[of r \<epsilon> r' \<epsilon>] \<open>\<epsilon>>0\<close> by auto
        hence "r' \<notin> cball r \<epsilon>" using \<open>\<epsilon>>0\<close> by auto
        thus False using that(1) unfolding roots_within_def by auto
      qed
      thus ?thesis using that using \<open>0 < \<epsilon>\<close> by fastforce
    qed
    obtain \<delta> where "\<delta>>0" and \<delta>_def:"\<forall>y\<in>S \<inter> ball a \<delta>. \<forall>r\<in>rts. 
            proots_count (pc y) (ball r \<epsilon>) = order r (pc a) \<and>
            proots_count (qc y) (ball r \<epsilon>) = order r (qc a)"
    proof -
      have "proots (pc a) \<subseteq> rts" "proots (qc a) \<subseteq> rts"  
        unfolding rts_def pqc_def using proots_within_times by auto
      then obtain \<delta>p \<delta>q where "\<delta>p>0" "\<delta>q>0" and 
              \<delta>p_def:"\<forall>q. degree q = degree (pc a) \<and> q \<noteq> 0 
                \<and> (\<forall>i\<le>degree (pc a). cmod (coeff q i - coeff (pc a) i) < \<delta>p) \<longrightarrow>
                (\<forall>r\<in>rts. proots_count q (ball r \<epsilon>) = order r (pc a))" and
              \<delta>q_def:"\<forall>q. degree q = degree (qc a) \<and> q \<noteq> 0 
                \<and> (\<forall>i\<le>degree (qc a). cmod (coeff q i - coeff (qc a) i) < \<delta>q) \<longrightarrow>
                (\<forall>r\<in>rts. proots_count q (ball r \<epsilon>) = order r (qc a))"
        using continuous_dependence_finite[OF \<open>\<epsilon>>0\<close> \<open>finite rts\<close> _ \<epsilon>_def, of "pc a"]
              continuous_dependence_finite[OF \<open>\<epsilon>>0\<close> \<open>finite rts\<close> _ \<epsilon>_def, of "qc a"]
        by auto
      obtain \<delta>p' \<delta>q' where \<delta>p'_pos:"\<delta>p' i>0" and \<delta>q'_pos:"\<delta>q' i>0"
              and \<delta>p'_def:"(\<forall>x\<in>S. dist x a <  \<delta>p' i \<longrightarrow> dist (coeff (pc x) i) (coeff (pc a) i) < \<delta>p)"
              and \<delta>q'_def:"(\<forall>x\<in>S. dist x a <  \<delta>q' i \<longrightarrow> dist (coeff (qc x) i) (coeff (qc a) i) < \<delta>q)"
              for i  
      proof -
        have "continuous_on S (\<lambda>y.  coeff (pc y) i) \<and> continuous_on S (\<lambda>y.  coeff (qc y) i)" for i
        proof -
          have "continuous_on S (\<lambda>x. coeff (poly_y p x) j)" for p j
            unfolding poly_y_def
            by (auto simp add:coeff_map_poly intro:continuous_intros)
          then show ?thesis
            unfolding  pqc_def pc_def qc_def
            by (auto simp add: coeff_mult coeff_of_real_poly)
        qed
        then have "(\<exists>d>0. \<forall>x'\<in>S. dist x' a < d \<longrightarrow> dist (coeff (pc x') i) (coeff (pc a) i) < \<delta>p)"
                  "(\<exists>d>0. \<forall>x'\<in>S. dist x' a < d \<longrightarrow> dist (coeff (qc x') i) (coeff (qc a) i) < \<delta>q)"
                  for i
          using \<open>\<delta>p>0\<close> \<open>\<delta>q>0\<close> \<open>a\<in>S\<close> continuous_on_iff[of S "(\<lambda>y.  coeff (pc y) i)"]
            continuous_on_iff[of S "(\<lambda>y.  coeff (qc y) i)"] by auto
        then show ?thesis using that by metis
      qed
      define \<delta> where "\<delta>= min (Min (\<delta>p' ` {0..degree (pc a)})) (Min (\<delta>q' ` {0..degree (qc a)}))"
      have "\<delta>>0" using \<delta>p'_pos \<delta>q'_pos unfolding \<delta>_def by auto
      moreover have "\<forall>y\<in>S \<inter> ball a \<delta>. \<forall>r\<in>rts. proots_count (pc y) (ball r \<epsilon>) = order r (pc a)"
      proof (standard,standard)
        fix y r assume "y \<in> S \<inter> ball a \<delta>" "r \<in> rts"
        then have "y\<in>S" and "dist y a < \<delta>" by (auto simp add:dist_commute)
        have "pc y \<noteq> 0"
          using pzero_inv \<open>y\<in>S\<close> \<open>a\<in>S\<close> \<open>pc a\<noteq>0\<close>
          unfolding constant_on_def pc_def by auto
        moreover have "degree (pc y) = degree (pc a)" 
          using deg_p_inv \<open>y\<in>S\<close> \<open>a\<in>S\<close> unfolding pc_def constant_on_def
          by auto
        moreover have "\<forall>i\<le>degree (pc a). cmod (coeff (pc y) i - coeff (pc a) i) < \<delta>p"
          using \<open>y\<in>S\<close> \<open>dist y a < \<delta>\<close>
          by (auto intro!:\<delta>p'_def[rule_format,unfolded dist_complex_def] simp add:\<delta>_def)
        ultimately show "proots_count (pc y) (ball r \<epsilon>) = order r (pc a) "
          by (intro \<delta>p_def[rule_format,OF _ \<open>r \<in> rts\<close>],auto)
      qed
      moreover have "\<forall>y\<in>S \<inter> ball a \<delta>. \<forall>r\<in>rts. proots_count (qc y) (ball r \<epsilon>) = order r (qc a)"
      proof (standard,standard)
        fix y r assume "y \<in> S \<inter> ball a \<delta>" "r \<in> rts"
        then have "y\<in>S" and "dist y a < \<delta>" by (auto simp add:dist_commute)
        have "qc y \<noteq> 0"
          using qzero_inv \<open>y\<in>S\<close> \<open>a\<in>S\<close> \<open>qc a\<noteq>0\<close>
          unfolding constant_on_def qc_def by auto
        moreover have "degree (qc y) = degree (qc a)" 
          using deg_q_inv \<open>y\<in>S\<close> \<open>a\<in>S\<close> unfolding qc_def constant_on_def
          by auto
        moreover have "\<forall>i\<le>degree (qc a). cmod (coeff (qc y) i - coeff (qc a) i) < \<delta>q"
          using \<open>y\<in>S\<close> \<open>dist y a < \<delta>\<close>
          by (auto intro!:\<delta>q'_def[rule_format,unfolded dist_complex_def] simp add:\<delta>_def)
        ultimately show "proots_count (qc y) (ball r \<epsilon>) = order r (qc a) "
          by (intro \<delta>q_def[rule_format,OF _ \<open>r \<in> rts\<close>],auto)
      qed
      ultimately show ?thesis using that by auto            
    qed

    have pc_rts:"\<forall>r\<in>p_rts. card (proots_within (pc y) (ball r \<epsilon>)) = 1" 
        "proots_within (pc y) (\<Union>r\<in>p_rts. ball r \<epsilon>) = proots (pc y)" when "y\<in>S \<inter> ball a \<delta>" for y
    proof -
      let ?r_at="\<lambda>r. proots_within (pc y) (ball r \<epsilon>)"
      have "pc y\<noteq>0" using pzero_inv \<open>pc a\<noteq>0\<close> \<open>a\<in>S\<close> that
        unfolding constant_on_def pc_def by auto
      have "1 \<le> int (card (?r_at r))" when "r \<in> p_rts" for r 
      proof (rule ccontr)
        assume "\<not> 1 \<le> int (card (?r_at r))"
        hence "card (?r_at r) = 0" by auto
        hence "?r_at r = {}" using \<open>pc y\<noteq>0\<close> by auto
        hence "0 = proots_count (pc y) (ball r \<epsilon>)" unfolding proots_count_def by auto
        also have "... = order r (pc a)" 
          using \<delta>_def[rule_format,OF \<open>y\<in>S \<inter> ball a \<delta>\<close>] that \<open>p_rts \<subseteq> rts\<close>
          unfolding p_rts_def by auto
        also have "... > 0"
          using that \<open>pc a\<noteq>0\<close> order_root unfolding roots_within_def p_rts_def by auto
        finally have "0 > 0" by simp
        thus False by auto
      qed
      moreover have "(\<Sum>r\<in>p_rts. card (?r_at r)) \<le> card p_rts" (is "?L \<le> ?R")
      proof -
        have "(\<Sum>r\<in>p_rts. card (?r_at r)) = card (\<Union>r\<in>p_rts. ?r_at r)" 
        proof (rule card_UN_disjoint[OF \<open>finite p_rts\<close>, symmetric]) 
          show "\<forall>r\<in>p_rts. finite (?r_at r)" using \<open>pc y \<noteq> 0\<close> by auto
          show "\<forall>i\<in>p_rts. \<forall>j\<in>p_rts. i \<noteq> j \<longrightarrow>?r_at i \<inter> ?r_at j = {}" 
          proof (clarify)
            fix i j assume "i\<in>p_rts" "j\<in>p_rts" "i \<noteq> j" 
            then have "ball i \<epsilon> \<inter> ball j \<epsilon> = {}" using \<open>p_rts \<subseteq> rts\<close>
              apply (intro \<epsilon>_def[rule_format,OF _ _ \<open>i\<noteq>j\<close>])
              by blast+
            then show "?r_at i \<inter> ?r_at j = {}" unfolding roots_within_def by auto
          qed
        qed
        also have " ... \<le> card (proots (pc y))" using \<open>pc y \<noteq> 0\<close> 
          by (auto intro!: card_mono)
        also have "... = card p_rts" 
          using distinct_p_inv that \<open>a\<in>S\<close>
          unfolding p_rts_def constant_on_def by auto
        finally show ?thesis .
      qed
      then have "(\<Sum>r\<in>p_rts. int (card (?r_at r))) \<le> int (card p_rts)" 
        by (metis int_sum of_nat_mono )
      moreover note \<open>finite p_rts\<close> 
      ultimately have "\<forall>r\<in>p_rts. int (card (?r_at r)) = 1"
        using sum_bounded_below_equal[of p_rts "\<lambda>_.1" "\<lambda>r. card (?r_at r)",simplified]
        by fastforce
      thus "\<forall>r\<in>p_rts. card (?r_at r) = 1" by auto
      show "proots_within (pc y) (\<Union>r\<in>p_rts. ball r \<epsilon>) = proots (pc y)"
      proof -
        have "proots_count (pc y) (\<Union>r\<in>p_rts. ball r \<epsilon>) = (\<Sum>r\<in>p_rts. proots_count (pc y) (ball r \<epsilon>))"
          using \<epsilon>_def[folded disjoint_family_on_def] \<open>p_rts \<subseteq> rts\<close> disjoint_family_on_mono
          apply (intro proots_count_disj_UNION[OF _ \<open>finite p_rts\<close> \<open>pc y\<noteq>0\<close>])
          by auto
        also have "... = (\<Sum>r\<in>p_rts. order r (pc a))"
          using \<delta>_def[rule_format, OF \<open>y\<in>S \<inter> ball a \<delta>\<close>] \<open>p_rts \<subseteq> rts\<close>
          apply (intro sum.cong)
          by auto
        also have "... = proots_count (pc a) UNIV"
          unfolding proots_count_def p_rts_def by simp
        also have "... = degree (pc a)"
          using degree_proots_count by simp
        also have "... = degree (pc y)"
          using \<open>a\<in>S\<close> \<open>y\<in>S \<inter> ball a \<delta>\<close> deg_p_inv
          unfolding constant_on_def pc_def by auto
        also have "... = proots_count (pc y) UNIV"
          using degree_proots_count by simp
        finally have "proots_count (pc y) (\<Union>r\<in>p_rts. ball r \<epsilon>) = proots_count (pc y) UNIV" .
        hence "(\<Sum>r\<in>proots (pc y) - proots_within (pc y) (\<Union>r\<in>p_rts. ball r \<epsilon>). order r (pc y)) = 0"
          unfolding proots_count_def using \<open>pc y\<noteq>0\<close>
          by (subst sum_diff_nat,auto)
        hence "proots_count (pc y) (UNIV - (\<Union>r\<in>p_rts. ball r \<epsilon>)) = 0"
          unfolding proots_count_def
          by (auto simp add:proots_within_inter Diff_Int_distrib)
        hence "proots_within (pc y) (UNIV - (\<Union>r\<in>p_rts. ball r \<epsilon>)) = {}"
          using proots_count_0_iff[OF \<open>pc y\<noteq>0\<close>] by blast
        thus ?thesis by (auto simp add:roots_within_def)
      qed
    qed
    have qc_rts:"\<forall>r\<in>q_rts. card (proots_within (qc y) (ball r \<epsilon>)) = 1"
          "proots_within (qc y) (\<Union>r\<in>q_rts. ball r \<epsilon>) = proots (qc y)"
        when "y\<in>S \<inter> ball a \<delta>" for y
    proof -
      let ?r_at="\<lambda>r. proots_within (qc y) (ball r \<epsilon>)"
      have "qc y\<noteq>0" using qzero_inv \<open>qc a\<noteq>0\<close> \<open>a\<in>S\<close> that
        unfolding constant_on_def qc_def by auto
      have "1 \<le> int (card (?r_at r))" when "r \<in> q_rts" for r 
      proof (rule ccontr)
        assume "\<not> 1 \<le> int (card (?r_at r))"
        hence "card (?r_at r) = 0" by auto
        hence "?r_at r = {}" using \<open>qc y\<noteq>0\<close> by auto
        hence "0 = proots_count (qc y) (ball r \<epsilon>)" unfolding proots_count_def by auto
        also have "... = order r (qc a)" 
          using \<delta>_def[rule_format,OF \<open>y\<in>S \<inter> ball a \<delta>\<close>] that \<open>q_rts \<subseteq> rts\<close>
          unfolding q_rts_def by auto
        also have "... > 0"
          using that \<open>qc a\<noteq>0\<close> order_root unfolding roots_within_def q_rts_def by auto
        finally have "0 > 0" by simp
        thus False by auto
      qed
      moreover have "(\<Sum>r\<in>q_rts. card (?r_at r)) \<le> card q_rts"
      proof -
        have "(\<Sum>r\<in>q_rts. card (?r_at r)) = card (\<Union>r\<in>q_rts. ?r_at r)" 
        proof (rule card_UN_disjoint[OF \<open>finite q_rts\<close>, symmetric]) 
          show "\<forall>r\<in>q_rts. finite (?r_at r)" using \<open>qc y \<noteq> 0\<close> by auto
          show "\<forall>i\<in>q_rts. \<forall>j\<in>q_rts. i \<noteq> j \<longrightarrow>?r_at i \<inter> ?r_at j = {}" 
          proof (clarify)
            fix i j assume "i\<in>q_rts" "j\<in>q_rts" "i \<noteq> j" 
            then have "ball i \<epsilon> \<inter> ball j \<epsilon> = {}" using \<open>q_rts \<subseteq> rts\<close>
              apply (intro \<epsilon>_def[rule_format,OF _ _ \<open>i\<noteq>j\<close>])
              by blast+
            then show "?r_at i \<inter> ?r_at j = {}" unfolding roots_within_def by auto
          qed
        qed
        also have " ... \<le> card (proots (qc y))" using \<open>qc y \<noteq> 0\<close> 
          by (auto intro!: card_mono)
        also have "... = card q_rts" 
          using distinct_q_inv that \<open>a\<in>S\<close>
          unfolding q_rts_def constant_on_def by auto
        finally show ?thesis .
      qed
      then have "(\<Sum>r\<in>q_rts. int (card (?r_at r))) \<le> int (card q_rts)" 
        by (metis int_sum of_nat_mono )
      moreover note \<open>finite q_rts\<close> 
      ultimately have "\<forall>r\<in>q_rts. int (card (?r_at r)) = 1"
        using sum_bounded_below_equal[of q_rts "\<lambda>_.1" "\<lambda>r. card (?r_at r)",simplified]
        by fastforce
      thus "\<forall>r\<in>q_rts. card (?r_at r) = 1" by auto
      show "proots_within (qc y) (\<Union>r\<in>q_rts. ball r \<epsilon>) = proots (qc y)"
      proof -
        have "proots_count (qc y) (\<Union>r\<in>q_rts. ball r \<epsilon>) 
            = (\<Sum>r\<in>q_rts. proots_count (qc y) (ball r \<epsilon>))"
          using \<epsilon>_def[folded disjoint_family_on_def] \<open>q_rts \<subseteq> rts\<close> disjoint_family_on_mono
          apply (intro proots_count_disj_UNION[OF _ \<open>finite q_rts\<close> \<open>qc y\<noteq>0\<close>])
          by auto
        also have "... = (\<Sum>r\<in>q_rts. order r (qc a))"
          using \<delta>_def[rule_format, OF \<open>y\<in>S \<inter> ball a \<delta>\<close>] \<open>q_rts \<subseteq> rts\<close>
          apply (intro sum.cong)
          by auto
        also have "... = proots_count (qc a) UNIV"
          unfolding proots_count_def q_rts_def by simp
        also have "... = degree (qc a)"
          using degree_proots_count by simp
        also have "... = degree (qc y)"
          using \<open>a\<in>S\<close> \<open>y\<in>S \<inter> ball a \<delta>\<close> deg_q_inv
          unfolding constant_on_def qc_def by auto
        also have "... = proots_count (qc y) UNIV"
          using degree_proots_count by simp
        finally have "proots_count (qc y) (\<Union>r\<in>q_rts. ball r \<epsilon>) = proots_count (qc y) UNIV" .
        hence "(\<Sum>r\<in>proots (qc y) - proots_within (qc y) (\<Union>r\<in>q_rts. ball r \<epsilon>). order r (qc y)) = 0"
          unfolding proots_count_def using \<open>qc y\<noteq>0\<close> by (subst sum_diff_nat,auto)
        hence "proots_count (qc y) (UNIV - (\<Union>r\<in>q_rts. ball r \<epsilon>)) = 0"
          unfolding proots_count_def
          by (auto simp add:proots_within_inter Diff_Int_distrib)
        hence "proots_within (qc y) (UNIV - (\<Union>r\<in>q_rts. ball r \<epsilon>)) = {}"
          using proots_count_0_iff[OF \<open>qc y\<noteq>0\<close>] by blast
        thus ?thesis by (auto simp add:roots_within_def)
      qed
    qed
     
    have card_1:"card (proots_within (pqc y) (ball r \<epsilon>)) = 1" when "r\<in>rts" "y\<in>S \<inter> ball a \<delta>" for r y
    proof -
      define cd_p where "cd_p\<equiv> card (proots_within (pc y) (ball r \<epsilon>))"
      define cd_q where "cd_q\<equiv> card (proots_within (qc y) (ball r \<epsilon>))"
      define cd_g where "cd_g\<equiv> card (proots_within (gcd (pc y) (qc y)) (ball r \<epsilon>))"
      define cd_pq where "cd_pq \<equiv> card (proots_within (pqc y) (ball r \<epsilon>))"              
          
      define g where "g\<equiv>\<lambda>y. gcd (pc y) (qc y)"
      define rc_b where "rc_b \<equiv> \<lambda>y r. proots_count (g y) (ball r \<epsilon>)"

      have "pc y \<noteq>0" "qc y\<noteq>0" "g a\<noteq>0" "g y\<noteq>0" 
        using pzero_inv qzero_inv \<open>poly_y p a\<noteq>0\<close> \<open>poly_y q a\<noteq>0\<close> \<open>a\<in>S\<close> \<open>y\<in>S \<inter> ball a \<delta>\<close>
        unfolding pc_def qc_def constant_on_def g_def by auto
      have gcd_card: "cd_g = 1" when "r\<in>p_rts \<inter> q_rts" 
      proof -
        let ?rc = "\<lambda>y r. proots_count (g y) (ball r \<epsilon>)"
        have "int (?rc y i) \<le> int (?rc a i)" when "i \<in> p_rts \<inter> q_rts" for i  
        proof -
          obtain r_p where r_p_def:"proots_within (pc y) (ball i \<epsilon>) = {r_p}"
            using pc_rts(1)[OF \<open>y\<in>S \<inter> ball a \<delta>\<close>,rule_format,of i] \<open>i\<in>p_rts \<inter> q_rts\<close> 
              card_1_singletonE 
            by blast
          obtain r_q where r_q_def:"proots_within (qc y) (ball i \<epsilon>) = {r_q}"
            using qc_rts(1)[OF \<open>y\<in>S \<inter> ball a \<delta>\<close>,rule_format,of i] \<open>i\<in>p_rts \<inter> q_rts\<close> 
              card_1_singletonE 
            by blast
          have "proots_within (g a) (ball i \<epsilon>) = {i}"
            using \<epsilon>_sub[OF \<open>i\<in>p_rts \<inter> q_rts\<close>] \<open>p_rts \<subseteq> rts\<close> \<open>q_rts \<subseteq> rts\<close>
            unfolding g_def proots_within_gcd p_rts_def q_rts_def
            by (auto simp add:proots_within_inter)    
          then have rc_ai:"?rc a i = min (order i (pc a)) (order i (qc a))"
            unfolding proots_count_def g_def using gcd_order_min[OF \<open>pc a\<noteq>0\<close> \<open>qc a\<noteq>0\<close>]
            by simp
          have "?rc y i<?rc a i" when "r_p\<noteq>r_q"
          proof -
            have "?rc y i = 0"
              using that r_p_def r_q_def unfolding proots_count_def g_def proots_within_gcd
              by auto
            moreover have "?rc a i>0"
              using rc_ai \<open>i \<in> p_rts \<inter> q_rts\<close> \<open>pc a\<noteq>0\<close> \<open>qc a\<noteq>0\<close> order_root
              unfolding p_rts_def q_rts_def roots_within_def by auto
            ultimately show ?thesis by auto
          qed
          moreover have "?rc y i=?rc a i" when "r_p=r_q"
          proof -
            have "?rc y i = min (proots_count (pc y) (ball i \<epsilon>)) (proots_count (qc y) (ball i \<epsilon>))"
              unfolding proots_count_def g_def proots_within_gcd
              using r_p_def r_q_def that gcd_order_min[OF \<open>pc y\<noteq>0\<close> \<open>qc y\<noteq>0\<close>]
              by auto
            also have "... = min (order i (pc a)) (order i (qc a))"
              using \<delta>_def[rule_format,OF \<open>y\<in>S \<inter> ball a \<delta>\<close>, of i] \<open>i \<in> p_rts \<inter> q_rts\<close>
                \<open>p_rts \<subseteq> rts\<close> \<open>q_rts \<subseteq> rts\<close>
              by fastforce
            also have "... = ?rc a i"
              using rc_ai by auto
            finally show ?thesis .
          qed
          ultimately show ?thesis by linarith
        qed
        moreover have "(\<Sum>i\<in>p_rts \<inter> q_rts. int (?rc a i)) \<le> (\<Sum>i\<in>p_rts \<inter> q_rts. int (?rc y i))"
        proof -
          have "(\<Sum>i\<in>p_rts \<inter> q_rts. ?rc a i) = proots_count (g a) (\<Union>i\<in>p_rts \<inter> q_rts. ball i \<epsilon>)"
          proof (rule proots_count_disj_UNION[symmetric,OF _ _ \<open>g a\<noteq>0\<close>])
            show "disjoint_family_on (\<lambda>i. ball i \<epsilon>) (p_rts \<inter> q_rts)"
              using \<epsilon>_def[folded disjoint_family_on_def] \<open>p_rts \<subseteq> rts\<close>
              by (auto elim!:disjoint_family_on_mono[rotated])  
            show "finite (p_rts \<inter> q_rts)" 
              by (simp add: \<open>finite q_rts\<close>)
          qed
          also have "... \<le> proots_count (g a) UNIV"
            using proots_count_subset[OF _ \<open>g a\<noteq>0\<close>] by auto
          also have "... = proots_count (g y) UNIV"
            using common_pq_inv[unfolded degree_proots_count] \<open>a\<in>S\<close> \<open>y\<in>S \<inter> ball a \<delta>\<close>
            unfolding g_def constant_on_def by auto
          also have "... = proots_count (g y) (\<Union>i\<in>p_rts \<inter> q_rts. ball i \<epsilon>)"
          proof -
            have "proots (pc y) = proots_within (pc y) (\<Union>i\<in>p_rts. ball i \<epsilon>)"
              using pc_rts(2)[OF \<open>y\<in>S \<inter> ball a \<delta>\<close>] by simp
            moreover have "proots (qc y) = proots_within (qc y) (\<Union>i\<in>q_rts. ball i \<epsilon>)"
              using qc_rts(2)[OF \<open>y\<in>S \<inter> ball a \<delta>\<close>] by simp
            moreover have "(\<Union>i\<in>p_rts \<inter> q_rts. ball i \<epsilon>) = 
                (\<Union>i\<in>p_rts. ball i \<epsilon>) \<inter> (\<Union>i\<in>q_rts. ball i \<epsilon>)"
              using \<epsilon>_def \<open>p_rts \<subseteq> rts\<close> \<open>q_rts \<subseteq> rts\<close>
              apply (intro disjoint_family_UNION_distrib[symmetric])
              by (auto simp add:disjoint_family_on_def)  
            ultimately have "proots (g y) = proots_within (g y) (\<Union>i\<in>p_rts \<inter> q_rts. ball i \<epsilon>)"
              unfolding g_def proots_within_gcd
              by (auto simp add:proots_within_inter)
            then show ?thesis unfolding proots_count_def
              unfolding proots_count_def by auto
          qed
          also have "... = (\<Sum>i\<in>p_rts \<inter> q_rts. ?rc y i)" 
            using \<epsilon>_def[folded disjoint_family_on_def] \<open>p_rts \<subseteq> rts\<close> \<open>q_rts \<subseteq> rts\<close> \<open>finite p_rts\<close>
            apply (intro proots_count_disj_UNION[OF _ _ \<open>g y\<noteq>0\<close>])
            by (auto elim!:disjoint_family_on_mono[rotated])
          finally have " (\<Sum>i\<in>p_rts \<inter> q_rts. ?rc a i) \<le>  (\<Sum>i\<in>p_rts \<inter> q_rts. ?rc y i)" .
          then have "int (\<Sum>i\<in>p_rts \<inter> q_rts. ?rc a i) \<le> int (\<Sum>i\<in>p_rts \<inter> q_rts. ?rc y i)" 
            using of_nat_mono by blast
          then show ?thesis using int_sum by auto
        qed
        ultimately have "\<forall>i\<in>p_rts \<inter> q_rts. int (?rc a i) = int (?rc y i)"
          using sum_bounded_below_equal[of "p_rts \<inter> q_rts" "\<lambda>r. ?rc y r" "\<lambda>r. ?rc a r"] 
            \<open>finite p_rts\<close> \<open>finite q_rts\<close>
          by blast
        moreover have "?rc a r \<noteq>0"
        proof -
          have "proots_within (g a) (ball r \<epsilon>) = {r}"
            using \<epsilon>_sub[OF \<open>r\<in>p_rts \<inter> q_rts\<close>] \<open>p_rts \<subseteq> rts\<close> \<open>q_rts \<subseteq> rts\<close>
            unfolding g_def proots_within_gcd p_rts_def q_rts_def
            by (auto simp add:proots_within_inter) 
          then have rc_ai:"?rc a r = min (order r (pc a)) (order r (qc a))"
            unfolding proots_count_def g_def
            using gcd_order_min[OF \<open>pc a\<noteq>0\<close> \<open>qc a\<noteq>0\<close>] by simp
          then show ?thesis
            using rc_ai \<open>r \<in> p_rts \<inter> q_rts\<close> \<open>pc a\<noteq>0\<close> \<open>qc a\<noteq>0\<close> order_root
            unfolding p_rts_def q_rts_def roots_within_def by auto
        qed
        ultimately have "proots_within (g y) (ball r \<epsilon>) \<noteq> {}"
          using that proots_count_0_iff[OF \<open>g y \<noteq> 0\<close>] 
          by (metis of_nat_eq_0_iff)
        then have "cd_g \<noteq> 0" using \<open>g y\<noteq>0\<close>
          unfolding cd_g_def g_def by auto
        moreover have "cd_g \<le>card (proots_within (pc y) (ball r \<epsilon>))"
          using \<open>pc y\<noteq>0\<close> unfolding cd_g_def proots_within_gcd
          by (auto intro!:card_mono)
        hence "cd_g \<le>1"
          using pc_rts(1)[OF \<open>y\<in>S \<inter> ball a \<delta>\<close>] that by auto
        ultimately show ?thesis by auto
      qed
      have cd:"cd_pq + cd_g  = cd_p  + cd_q "  
        unfolding cd_pq_def cd_g_def cd_p_def cd_q_def pqc_def proots_within_times proots_within_gcd
        apply (intro card_Un_Int[symmetric])
        by (auto simp add:\<open>pc y\<noteq>0\<close> \<open>qc y\<noteq>0\<close>)            
      have "cd_pq = 1" when "r\<in>p_rts" "r\<notin>q_rts"
      proof -
        have "cd_p =1" 
          using pc_rts(1)[rule_format, OF \<open>y\<in>S \<inter> ball a \<delta>\<close> that(1)] 
          unfolding cd_p_def . 
        moreover have "proots_within (qc y) (ball r \<epsilon>) = {}" 
        proof -
          have "proots_count (qc y) (ball r \<epsilon>) = order r (qc a)"
            using \<delta>_def[rule_format,OF \<open>y\<in>S \<inter> ball a \<delta>\<close>] \<open>r\<in>p_rts\<close> \<open>p_rts \<subseteq> rts\<close> by auto
          moreover have "order r (qc a) = 0"
            using \<open>r\<notin>q_rts\<close> order_root \<open>pc a\<noteq>0\<close> 
            unfolding q_rts_def roots_within_def by auto
          ultimately have "proots_count (qc y) (ball r \<epsilon>) = 0" by auto
          then show ?thesis using proots_count_0_iff[OF \<open>qc y\<noteq>0\<close>]  by simp
        qed       
        then have "cd_q  = 0" "cd_g  = 0"
          using proots_within_gcd[of "pc y"] unfolding cd_q_def cd_g_def by auto
        ultimately show ?thesis using cd by auto     
      qed
      moreover have "cd_pq = 1" when "r\<notin>p_rts" "r\<in>q_rts"
      proof -
        have "cd_q =1" 
          using qc_rts(1)[rule_format, OF \<open>y\<in>S \<inter> ball a \<delta>\<close> that(2)] 
          unfolding cd_q_def . 
        moreover have "proots_within (pc y) (ball r \<epsilon>) = {}" 
        proof -
          have "proots_count (pc y) (ball r \<epsilon>) = order r (pc a)"
            using \<delta>_def[rule_format,OF \<open>y\<in>S \<inter> ball a \<delta>\<close>] \<open>r\<in>q_rts\<close> \<open>q_rts \<subseteq> rts\<close> by auto
          moreover have "order r (pc a) = 0"
            using \<open>r\<notin>p_rts\<close> order_root \<open>qc a\<noteq>0\<close> 
            unfolding p_rts_def roots_within_def by auto
          ultimately have "proots_count (pc y) (ball r \<epsilon>) = 0" by auto
          then show ?thesis using proots_count_0_iff[OF \<open>pc y\<noteq>0\<close>]  by simp
        qed       
        then have "cd_p  = 0" "cd_g  = 0"
          using proots_within_gcd[of "pc y"] unfolding cd_p_def cd_g_def by auto
        ultimately show ?thesis using cd by auto     
      qed
      moreover have "cd_pq = 1" when "r\<in>p_rts" "r\<in>q_rts"
      proof -
        have "cd_p =1" 
          using pc_rts(1)[rule_format, OF \<open>y\<in>S \<inter> ball a \<delta>\<close> that(1)] 
          unfolding cd_p_def .
        moreover have "cd_q =1" 
          using qc_rts(1)[rule_format, OF \<open>y\<in>S \<inter> ball a \<delta>\<close> that(2)] 
          unfolding cd_q_def .
        moreover have "cd_g = 1"
          using gcd_card that by auto
        ultimately show ?thesis using cd by auto
      qed
      moreover have "r\<in>p_rts \<union> q_rts" using \<open>r\<in>rts\<close>
        unfolding rts_def p_rts_def q_rts_def pqc_def proots_within_times .
      ultimately show ?thesis unfolding cd_pq_def by auto
    qed
      
    have "card (proots (poly_y (p * q) y)) = card (proots (poly_y (p * q) a))"
      when "y\<in>S \<inter> ball a \<delta>" for y 
    proof -
      have "pc y\<noteq>0" "qc y\<noteq>0" 
        using pzero_inv qzero_inv \<open>poly_y p a\<noteq>0\<close> \<open>poly_y q a\<noteq>0\<close> \<open>a\<in>S\<close> \<open>y\<in>S \<inter> ball a \<delta>\<close>
        unfolding pc_def qc_def constant_on_def by auto
      obtain alr where alr_def:"proots_within (pqc y) (ball r \<epsilon>) = {alr r}"
              if "r\<in>rts" for r 
      proof -
        have "\<exists>r'. proots_within (pqc y) (ball r \<epsilon>) = {r'}"
          when "r\<in>rts" "y\<in>S \<inter> ball a \<delta>" for r y using card_1[OF that] by (meson card_1_singletonE)
        then have "\<exists>f. \<forall>y.\<forall>r. r\<in>rts \<longrightarrow> y\<in>S \<inter> ball a \<delta> \<longrightarrow> proots_within (pqc y) (ball r \<epsilon>) = {f y r}"
          using card_1 by (auto intro!: choice)
        thus ?thesis using that \<open>y\<in>S \<inter> ball a \<delta>\<close> by auto
      qed
      have "bij_betw alr (proots_within (pqc a) \<real>) (proots_within (pqc y) \<real>)"        
      proof -
        have "inj_on alr (proots (pqc a))" unfolding rts_def[symmetric]
        proof 
          fix x x' assume "x \<in> rts" "x' \<in> rts" "alr x = alr x'"
          have "alr x \<in> ball x \<epsilon>" using alr_def[OF \<open>x \<in> rts\<close>] by auto
          moreover have "alr x'\<in>ball x' \<epsilon>" using alr_def[OF \<open>x' \<in> rts\<close>] by auto
          ultimately show "x=x'" 
            using \<epsilon>_def[rule_format,OF \<open>x \<in> rts\<close> \<open>x' \<in> rts\<close>] \<open>\<epsilon>>0\<close> \<open>alr x = alr x'\<close> 
            by fastforce
        qed 
        moreover have "alr ` (proots (pqc a)) = proots (pqc y)" 
        proof -
          have "alr ` (proots (pqc a)) = alr ` (\<Union>r\<in>rts. {r})"
            unfolding rts_def by auto
          also have "... = (\<Union>r\<in>rts. alr ` {r})"
            by auto
          also have "...  = (\<Union>r\<in>rts. proots_within (pqc y) (ball r \<epsilon>))"
            using alr_def[symmetric] by (intro UNION_cong,auto)
          also have "...  = (\<Union>r\<in>rts. proots_within (pc y) (ball r \<epsilon>)) 
              \<union> (\<Union>r\<in>rts. proots_within (qc y) (ball r \<epsilon>))"
            unfolding pqc_def proots_within_times by auto
          also have "... = (proots_within (pc y) (\<Union>r\<in>rts. ball r \<epsilon>)) 
              \<union> (proots_within (qc y) (\<Union>r\<in>rts. ball r \<epsilon>))"
            by auto
          also have "... = (proots (pc y)) \<union> (proots (qc y) )"
          proof -
            have "(\<Union>r\<in>p_rts. ball r \<epsilon>) \<subseteq> (\<Union>r\<in>rts. ball r \<epsilon>)" 
              by (intro UN_mono[OF \<open>p_rts \<subseteq> rts\<close>],simp)
            then have "proots_within (pc y) (\<Union>r\<in>rts. ball r \<epsilon>) = proots (pc y)"                    
              using pc_rts(2)[OF \<open>y\<in>S \<inter> ball a \<delta>\<close>]
              by (metis (no_types, lifting) Un_commute proots_within_proots 
                  proots_within_union subset_Un_eq)
            moreover have "(\<Union>r\<in>q_rts. ball r \<epsilon>) \<subseteq> (\<Union>r\<in>rts. ball r \<epsilon>)" 
              by (intro UN_mono[OF \<open>q_rts \<subseteq> rts\<close>],simp)
            then have "proots_within (qc y) (\<Union>r\<in>rts. ball r \<epsilon>) = proots (qc y)"                    
              using qc_rts(2)[OF \<open>y\<in>S \<inter> ball a \<delta>\<close>]
              by (metis (no_types, lifting) Un_commute proots_within_proots 
                          proots_within_union subset_Un_eq)
            ultimately show ?thesis by auto
          qed
          also have "... = proots (pqc y)"
            unfolding pqc_def proots_within_times by auto
          finally show ?thesis .
        qed
        moreover have "r\<in>\<real> \<longleftrightarrow> alr r \<in> \<real>" when "r\<in>proots (pqc a)" for r 
        proof -
          have False when "alr r \<in> \<real>" "r \<notin> \<real>"  
          proof -
            define ar where "ar= alr r"
            define r' where "r'=cnj r"
            have "r\<noteq>r'" using Reals_cnj_iff \<open>r \<notin> \<real>\<close> unfolding r'_def
              by auto
            moreover have "r'\<in> proots (pqc a)"
            proof -
              have "poly (pqc a) r' = cnj (poly (pqc a) r)"
                unfolding pqc_def pc_def qc_def r'_def
                by (auto simp add:cnj_poly map_poly_map_poly comp_def simp del:of_real_poly_def[symmetric])
              also have "... = 0"
                using \<open>r \<in> proots (pqc a)\<close> by auto
              finally show ?thesis  by auto
            qed 
            moreover have "ar \<in> ball r \<epsilon>" 
              using alr_def[unfolded rts_def,OF \<open>r\<in>proots (pqc a)\<close>,folded ar_def]
              by auto
            moreover have "ar \<in> ball r' \<epsilon>"  
            proof -
              have "dist r' ar = dist r' (cnj ar) "
                using \<open>alr r\<in>\<real>\<close>
                by (simp add: Reals_cnj_iff ar_def) 
              also have "... = dist r ar"
                unfolding r'_def by auto
              also have "... < \<epsilon>"
                using \<open>ar\<in>ball r \<epsilon>\<close> by auto
              finally show ?thesis by auto
            qed
            ultimately show False using \<epsilon>_def[unfolded rts_def,rule_format,of r r']
                \<open>r\<in>proots (pqc a)\<close> by blast
          qed 
          moreover have False when "alr r \<notin> \<real>" "r \<in> \<real>" 
          proof -
            define ar where "ar = alr r"
            define ar' where "ar'= cnj ar"
            have "alr r \<in> proots (pqc y)" using \<open>alr ` (proots (pqc a)) = (proots (pqc y))\<close>
                \<open>r\<in>proots (pqc a)\<close> by auto
            have "ar'\<in>proots (pqc y)"
            proof -
              have "poly (pqc y) ar' = cnj (poly (pqc y) ar)"
                unfolding pqc_def pc_def qc_def ar'_def
                by (auto simp add:cnj_poly map_poly_map_poly comp_def 
                    simp del:of_real_poly_def[symmetric])
              also have "... = 0"
                using \<open>alr r \<in> proots (pqc y)\<close> unfolding ar_def by auto
              finally show ?thesis  by auto
            qed
            moreover have "ar'\<in>ball r \<epsilon>" 
            proof -
              have "r\<in>Reals" using that(2) by auto
              then have "dist r ar' = dist (cnj r) ar'"
                by (simp add: Reals_cnj_iff) 
              also have "... = dist r ar"
                unfolding ar'_def by auto
              also have "... < \<epsilon>"
                using alr_def[of r,folded ar_def] \<open>r\<in>proots (pqc a)\<close> 
                unfolding rts_def  by auto
              finally show ?thesis by auto
            qed
            ultimately have "ar' \<in> proots_within (pqc y) (ball r \<epsilon>)" by auto
            moreover have "ar'\<noteq>ar" using that(1) unfolding ar'_def ar_def
              by (simp add: Reals_cnj_iff)
            ultimately show False
              using alr_def[unfolded rts_def, OF \<open>r\<in>proots (pqc a)\<close>,folded ar_def] by auto
          qed
          ultimately show ?thesis by auto
        qed
        ultimately show ?thesis
          apply (intro bij_betw_imageI)
          apply (auto simp add: proots_within_inter simp del:proots_within_iff elim:subset_inj_on)  
          by fast  
      qed
      hence "card (proots_within (pqc y) \<real>) = card (proots_within (pqc a) \<real>)"
        using bij_betw_same_card by metis
      moreover have "proots_within (pqc y) \<real> = of_real ` proots (poly_y (p * q) y)" 
        using \<open>pc y\<noteq>0\<close> \<open>qc y\<noteq>0\<close> unfolding pqc_def pc_def qc_def 
        apply (subst of_real_roots_within)
        by (auto simp add:poly_y_mult)
      hence "card (proots_within (pqc y) \<real>) = card (proots (poly_y (p * q) y))"
        apply (auto, subst card_image)
        by (auto simp add: inj_on_def)
      moreover have "proots_within (pqc a) \<real> = of_real ` proots (poly_y (p * q) a)" 
        using \<open>pc a\<noteq>0\<close> \<open>qc a\<noteq>0\<close> unfolding pqc_def pc_def qc_def 
        apply (subst of_real_roots_within)
        by (auto simp add:poly_y_mult)
      hence "card (proots_within (pqc a) \<real>) = card (proots (poly_y (p * q) a))"
        apply (auto, subst card_image)
        by (auto simp add: inj_on_def)
      ultimately show ?thesis by presburger
    qed
    then have "?goal (S \<inter> ball a \<delta>)" 
      apply auto
      by (auto simp add: \<open>a\<in>S\<close> \<open>\<delta>>0\<close>)
    then show ?thesis by blast
  qed
  ultimately show "\<exists>T. ?goal T" by blast
qed

end
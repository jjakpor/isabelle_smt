theory Words      
  imports Main "HOL-Library.Sublist" "HOL-Library.List_Lexorder" HOL.Groups "HOL-Library.Multiset"
begin

type_synonym 'a word = "'a list"

no_notation append (infixr "@" 65)
notation append (infixr "\<cdot>" 65)
notation Nil ("\<epsilon>")

notation length ("\<bar>_\<bar>")
no_notation Groups.abs_class.abs ("\<bar>_\<bar>")

instantiation char::linorder begin

(* Just for convenience, so we can use literal chars for testing *)
definition less_char::"char \<Rightarrow> char \<Rightarrow> bool" where 
  "less_char a b \<equiv> ((of_char a)::nat) < ((of_char b)::nat)"

definition less_eq_char::"char \<Rightarrow> char \<Rightarrow> bool" where 
  "less_eq_char a b \<equiv> ((of_char a)::nat) \<le> ((of_char b)::nat)"

instance apply(standard)
  using less_char_def less_eq_char_def by auto

end

primrec concat_all:: "'a word list \<Rightarrow> 'a word" where
  "concat_all [] = \<epsilon>" |
  "concat_all (w#ws) = w\<cdot>(concat_all ws)"

fun factor:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where 
  "factor v w = sublist v w"

fun get_factor:: "'a word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a word" ("_[_;_]" 101) where 
  "get_factor w i j = (if i \<le> j then take (j-i) (drop i w) else \<epsilon>)"

primrec contains:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where
  "contains \<epsilon> v = (v = \<epsilon>)" |
  "contains (x#u) v = ((prefix v (x#u)) \<or> (contains u v))"

lemma contains_iff_factor:"contains w v \<longleftrightarrow> factor v w"
  by (induct w) (auto simp add: sublist_Cons_right)


subsection "Factorization"

lemma drop_append:
  assumes "n \<le> \<bar>w\<bar> \<and> x = drop n w"
  shows "\<exists>v. ((w = v\<cdot>x) \<and> (length v) = n)"
  using assms
proof (induct w)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a w)
  then show ?case
    by (metis antisym append_take_drop_id length_take min_def)
qed

lemma factor_iff: "factor v w \<longleftrightarrow> (\<exists>i. v = (w[i; i+\<bar>v\<bar>]))"
proof 
  show "factor v w \<Longrightarrow> \<exists>i. v = (w[i;i + \<bar>v\<bar>])"
    unfolding factor.simps get_factor.simps 
    by (metis append_eq_conv_conj diff_add_inverse le_add1 sublist_def)
next
  show "\<exists>i. v = (w[i;i + \<bar>v\<bar>]) \<Longrightarrow> factor v w"
    unfolding factor.simps get_factor.simps
    by (metis le_add1 sublist_drop sublist_order.order.trans sublist_take)
qed

lemma factorization: 
  assumes "i < \<bar>w\<bar>"
    and "i \<le> j"
  shows "\<exists>!v. (w[i; j]) = v \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = i \<and> \<bar>v\<bar> = min (j-i) (\<bar>w\<bar>-i))"
proof -
  have "\<exists>!v. take (j - i) (drop i w) = v \<and> (\<exists>x. (\<exists>y. w = x \<cdot> v \<cdot> y) \<and> \<bar>x\<bar> = i
          \<and> \<bar>v\<bar> = min (j - i) (\<bar>w\<bar> - i))"
    using assms by (metis  append_take_drop_id length_drop length_take min.absorb4 min.commute)
  then show ?thesis
    using assms by (simp split: if_splits)
qed

lemma factorize_if:"w = x\<cdot>v\<cdot>y \<Longrightarrow> w[\<bar>x\<bar>; \<bar>x\<bar>+\<bar>v\<bar>] = v" by auto

lemma prefix_iff_fac: "prefix v w \<longleftrightarrow> (w[0; \<bar>v\<bar>] = v)"
  by (metis append_eq_conv_conj diff_zero drop0 get_factor.elims prefix_def zero_order(1))

lemma suffix_iff_fac: "suffix v w \<longleftrightarrow> (w[\<bar>w\<bar> - \<bar>v\<bar>; \<bar>w\<bar>] = v)"
proof
  show "suffix v w \<Longrightarrow> w[\<bar>w\<bar> - \<bar>v\<bar>;\<bar>w\<bar>] = v"  
    unfolding suffix_def by auto
next
  show "w[\<bar>w\<bar> - \<bar>v\<bar>;\<bar>w\<bar>] = v \<Longrightarrow> suffix v w"
    by (metis diff_le_self get_factor.simps length_drop order_le_less suffix_drop take_all)
qed

lemma get_factor_01_is_take1: "w[0;1] = take 1 w"
  by auto

lemma empty_factor_if_i_geq_j: "i \<ge> j \<Longrightarrow> w[i;j] = \<epsilon>" 
  by auto

lemma empty_factor_if_i_geq_length: "i \<ge> (length w) \<Longrightarrow> w[i;j] = \<epsilon>" 
  by auto

lemma factor_epsilon: "\<epsilon>[i;j] = \<epsilon>" 
  by auto

lemma factor_suffix: "\<bar>w\<bar> \<le> m \<Longrightarrow> w[i; m] = drop i w" 
  by auto

lemma factor_len_0: "w[i;i] = \<epsilon>" 
  by auto

lemma factor_is_word_if_j_geq_length: "j \<ge> (length w) \<Longrightarrow> w[0;j] = w"
  by auto

lemma fac_nth:"i < (length w) \<Longrightarrow> w[i; i+1] = (w!i)#\<epsilon>"
  by (simp add: take_Suc_conv_app_nth)

lemma not_contains_no_fac_has_prefix:"(\<not>contains w d) \<Longrightarrow> w = x\<cdot>y \<Longrightarrow> (\<not> prefix d y)"
  by (auto simp add: contains_iff_factor sublist_append)

lemma if_contains_then_fac_has_prefix:"(contains w d) \<Longrightarrow> \<exists>x y. w = x\<cdot>y \<and> (prefix d y)"
  by (auto simp add: contains_iff_factor prefix_def sublist_def)

lemma epsilon_contains_epsilon[simp]: "contains \<epsilon> v \<Longrightarrow> v = \<epsilon>" 
  by auto

end

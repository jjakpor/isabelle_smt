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

abbreviation factor:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where 
  "factor \<equiv> sublist"

fun get_factor:: "'a word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a word" ("_[_;_]" 101) where 
  "get_factor w i j = (if i \<le> j then take (j-i) (drop i w) else \<epsilon>)"

primrec contains:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where
  "contains \<epsilon> v = (v = \<epsilon>)" |
  "contains (x#u) v = ((prefix v (x#u)) \<or> (contains u v))"

lemma contains_iff_factor:"contains w v \<longleftrightarrow> factor v w"
  apply(induct w)
   apply(simp)
  by (simp add: sublist_Cons_right)








subsection "Factorization"

lemma drop_append: "n \<le> \<bar>w\<bar> \<and> x = drop n w  \<Longrightarrow> \<exists>v. ((w = v\<cdot>x) \<and> (length v) = n)"
  apply(induct w)
   apply auto
  by (metis append_take_drop_id le_Suc_eq length_Cons length_take min_def not_less_eq_eq)

lemma factor_iff:"factor v w \<longleftrightarrow> (\<exists>i. v = (w[i; i+\<bar>v\<bar>]))"
  apply(auto)
  using append_eq_conv_conj sublist_def apply metis
  using append_take_drop_id  sublist_def by metis

lemma factorization:"i < \<bar>w\<bar> \<and> i\<le>j \<Longrightarrow> \<exists>!v. (w[i; j]) = v \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = i \<and> \<bar>v\<bar> = min (j-i) (\<bar>w\<bar>-i))"
  apply(simp split: if_splits)
  by (metis append_take_drop_id length_drop length_take min.absorb4 min.commute)

lemma factorize_if:"w = x\<cdot>v\<cdot>y \<Longrightarrow> w[\<bar>x\<bar>; \<bar>x\<bar>+\<bar>v\<bar>] = v" by auto

lemma prefix_iff_fac: "prefix v w \<longleftrightarrow> (w[0; \<bar>v\<bar>] = v)" 
  unfolding prefix_def
  apply auto
  using append_take_drop_id by metis

lemma suffix_iff_fac: "suffix v w \<longleftrightarrow> (w[\<bar>w\<bar> - \<bar>v\<bar>; \<bar>w\<bar>] = v)" 
  unfolding suffix_def
  apply auto
  using append_take_drop_id by metis

lemma []: "w[0;1] = take 1 w"
  by auto

lemma []: "i \<ge> j \<Longrightarrow> w[i;j] = \<epsilon>" 
  by auto

lemma []: "i\<ge> (length w) \<Longrightarrow> w[i;j] = \<epsilon>" 
  by auto

lemma factor_epsilon: "\<epsilon>[i;j] = \<epsilon>" 
  by auto

lemma factor_suffix: "\<bar>w\<bar> \<le> m \<Longrightarrow> w[i; m] = drop i w" 
  by (auto)

lemma factor_len_0: "w[i;i] = \<epsilon>" 
  by auto

lemma []: "j \<ge> (length w) \<Longrightarrow> w[0;j] = w" 
  by auto

lemma fac_nth:"i < (length w) \<Longrightarrow> w[i; i+1] = (w!i)#\<epsilon>"
  by (simp add: take_Suc_conv_app_nth)

lemma contains_iff_fac: "contains w v \<longleftrightarrow> factor v w"
  unfolding sublist_def
  apply(induct w)
   apply(auto simp add: prefix_def)+
   apply (metis append_Cons)
  by (metis append_eq_Cons_conv)

lemma not_contains_no_fac_has_prefix:"(\<not>contains w d) \<Longrightarrow> w = x\<cdot>y \<Longrightarrow> (\<not> prefix d y)"
  by (auto simp add: contains_iff_fac sublist_append)

lemma if_contains_then_fac_has_prefix:"(contains w d) \<Longrightarrow> \<exists>x y. w = x\<cdot>y \<and> (prefix d y)"
  by (auto simp add: contains_iff_fac prefix_def sublist_def)

lemma epsilon_contains_epsilon[simp]: "contains \<epsilon> v \<Longrightarrow> v = \<epsilon>" 
  by auto





end






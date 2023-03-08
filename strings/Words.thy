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

fun find_fac:: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word option" where
  "find_fac w v = List.find (prefix v) (rev (suffixes w))"

fun find_index:: "'a word \<Rightarrow> 'a word \<Rightarrow> nat option" where
  "find_index w v = (case find_fac w v of Some r \<Rightarrow>  Some ((length w) - (length r)) | None \<Rightarrow> None)"


fun replace:: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> 'a word" where
  "replace w v u = (case find_index w v of Some i \<Rightarrow> (take i w)\<cdot>u\<cdot>(drop (i+(length v)) w) | None => w)"

lemma drop_append: "n \<le> \<bar>w\<bar> \<and> x = drop n w  \<Longrightarrow> \<exists>v. ((w = v\<cdot>x) \<and> (length v) = n)"
  apply(induct w)
   apply auto
  by (metis append_take_drop_id le_Suc_eq length_Cons length_take min_def not_less_eq_eq)


fun factors:: "'a word \<Rightarrow> nat \<Rightarrow> 'a word list" where
  "factors w n  = [(w[i; i+n]). i\<leftarrow>[0..<\<bar>w\<bar>+1-n]]"

fun enum_factors:: "'a word \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a word) list"
  where "enum_factors w n = (enumerate 0 (factors w n))"

fun factor_index:: "'a word \<Rightarrow> 'a word \<Rightarrow> nat option" where
  "factor_index w v = map_option fst ((find (\<lambda>(i,v'). v'=v) (enum_factors w \<bar>v\<bar>)))"


subsection "Factorization"

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









subsection "Searching Factors"

lemma rev_suffixes:"set (suffixes w) = set (rev (suffixes w))"  
  by auto

lemma suffixes_set:"x \<in> set (suffixes w) \<Longrightarrow> suffix x w"
  by (auto simp add: suffix_def)

lemma suffixes_rev_set:"x \<in> set (rev (suffixes w)) \<Longrightarrow> suffix x w"
  by (auto simp add: suffix_def)

lemma first_suffix_is_word:"rev (suffixes w)!0 = w"
  by (metis Nil_is_rev_conv hd_conv_nth hd_rev last_suffixes suffixes_not_Nil)

lemma find_prefix: "find_fac (v\<cdot>w) v = Some (v\<cdot>w)"
  by (auto simp add:  find_Some_iff first_suffix_is_word prefix_def)

lemma find_fac_epsilon: "find_fac w \<epsilon> = Some w"
  unfolding prefix_def by (metis append_Nil find_prefix)

lemma find_fac_in_epsilon: "find_fac \<epsilon> w = Some v \<Longrightarrow> w = \<epsilon>"
  by (auto simp add:  split: if_splits)

lemma find_returns_factor_at:
  assumes "find_fac w v = Some s"
  shows "\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = (length w) - (length s)"
  using assms
  apply(auto simp add: prefix_def suffix_def)
  by (metis add_diff_cancel_right' find_Some_iff length_append nth_mem prefix_def suffix_def suffixes_rev_set)

lemma contains_iff_find_fac: "(\<exists>u. find_fac w v = Some u) \<longleftrightarrow> contains w v"
  apply(auto)
  using contains_iff_fac find_returns_factor_at  apply (metis find_fac.elims sublist_appendI) 
  apply(auto simp add: contains_iff_fac)
  by (metis find_None_iff2 in_set_suffixes not_Some_eq rev_suffixes sublist_altdef')

lemma suffixes_count: "length (suffixes w) = (length w) + 1"
  by (induct_tac w) auto

lemma suffixes_rev_count[simp]: "length (rev (suffixes w)) = (length (suffixes w))"
  by auto

lemma suffix_length: "i < length (suffixes w) \<Longrightarrow> length ((suffixes w)!i) = i"
  by (induct w) (auto simp add: nth_append)


lemma suffix_rev_length: "i < length (rev (suffixes w)) \<Longrightarrow> length ((rev (suffixes w))!i) = (length w) - i"
  apply(induct w)
  by (auto simp add: suffix_length  less_Suc_eq_0_disj  rev_nth, auto simp add: suffix_length)

lemma suffix_if:"v = rev ((suffixes w))!j \<and> j < length (rev ((suffixes w))) \<longleftrightarrow> (\<exists>x. w = x\<cdot>v \<and> (length x) = j)"
  apply auto
   apply (metis add_diff_cancel_right' add_diff_inverse_nat length_append length_rev length_suffixes not_less_eq nth_mem suffix_def suffix_rev_length suffixes_rev_set)
  by (simp add: first_suffix_is_word nth_append suffixes_append)

lemma find_fac_returns_first: "find_fac w v = Some s \<Longrightarrow> \<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = (length w) - (length s) \<and> (\<forall> x'. (length x')<(length x) \<longrightarrow> (\<nexists>y'. w = x'\<cdot>v\<cdot>y'))" 
  apply(auto simp add:  find_Some_iff prefix_def)
  by (metis add_diff_cancel_right' length_append length_rev length_suffixes suffix_if)

lemma find_finds_factor:"find_index w v = Some r \<Longrightarrow> \<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = r"
  apply(auto simp add:  option.case_eq_if split: if_splits)
  using find_returns_factor_at   by (metis find_fac.elims)

lemma contains_iff_find_index: "(\<exists>r. find_index w v = Some r) \<longleftrightarrow> contains w v"
  using contains_iff_find_fac by force+

lemma find_index_of_suffix:
  assumes "find_index (drop i w) v = Some r"
    and "i \<le> (length w)"
  shows "\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = r + i"
proof -
  from assms have "\<exists>s. find_fac (drop  i w) v = Some s"   
    using contains_iff_find_fac contains_iff_find_index by blast 
  then have "\<exists>s. find_fac (drop i w) v = Some s \<and> r = (length (drop i w)) - (length s)" 
    using find_index.elims assms by auto
  then have "\<exists>s x y. (drop  i w) = x\<cdot>v\<cdot>y \<and> (length x) = (length (drop  i w))-(length s)
               \<and> r = (length (drop  i w)) - (length s)"  
    by (metis Ex_list_of_length find_returns_factor_at)
  then have "\<exists>s x y. (drop  i w) = x\<cdot>v\<cdot>y \<and> (length x) = r \<and> r = (length (drop  i w)) - (length s)"  
    by auto
  then have "\<exists>s x y. (drop  i w) = x\<cdot>v\<cdot>y \<and> i \<le> (length w) \<and> (length x) = r \<and>
               r = (length (drop  i w)) - (length s)" 
    using assms by auto
  then have "\<exists>s x y. (\<exists>x'. w = x'\<cdot>x\<cdot>v\<cdot>y \<and> (length x') = i) \<and> (length x) = r \<and>
               r = (length (drop  i w)) - (length s)"  
    by (metis Words.drop_append)
  then have "\<exists>s x y x'. w = x'\<cdot>x\<cdot>v\<cdot>y \<and> (length x') = i \<and> (length x) = r \<and>
               r = (length (drop  i w)) - (length s)" 
    by auto
  then have "\<exists>x y x'. w = x'\<cdot>x\<cdot>v\<cdot>y \<and> (length x') = i \<and> (length x) = r" 
    by auto
  then have "\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = r + i" 
    by (metis add.commute append.assoc length_append)
  then show ?thesis 
    by simp
qed


lemma find_index_returns_first: 
  assumes "find_index w v = Some s"
  shows "\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = s \<and> (\<forall>x'. (length x') < s \<longrightarrow> (\<nexists>y'. w = x'\<cdot>v\<cdot>y'))" 
  apply(auto simp add:  find_index.elims  option.case_eq_if split: if_splits)
  using find_fac_returns_first find_index.elims assms 
  by (smt (verit, del_insts) option.case_eq_if option.distinct(1) option.exhaust_sel option.sel) (* todo *)

theorem find_prefix_is_word: "find_fac (v\<cdot>u) v = Some (v\<cdot>u)"
  by (auto simp add:  prefix_def find_Some_iff first_suffix_is_word)

theorem find_prefix_index_is_0: "find_index (v\<cdot>u) v = Some 0"
  using find_prefix_is_word find_index.elims by (metis diff_self_eq_0 option.simps(5))

lemma find_index_of_suffix_returns_first: 
  assumes "i \<le> (length w)"
    and "find_index (drop i w) v = Some s"
  shows "\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = (s+i) \<and>
           (\<forall>x'. ((length x') < (s+i) \<and> (length x') \<ge> i) \<longrightarrow> (\<nexists>y'. w = x'\<cdot>v\<cdot>y'))" 
proof -
  from assms have "\<exists>p u. w = p\<cdot>u \<and> length p = i \<and> find_index u v = Some s" 
    using drop_append by fastforce
  then have "\<exists>p u. w = p\<cdot>u \<and> length p = i \<and> (\<exists>x y. u = x\<cdot>v\<cdot>y \<and> (length x) = s \<and> 
               (\<forall>x'. (length x') < s \<longrightarrow> (\<nexists>y'. u = x'\<cdot>v\<cdot>y')))" 
    using find_index_returns_first by metis
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> u = x\<cdot>v\<cdot>y \<and> (length x) = s \<and>
               (\<forall>x'. (length x') < s \<longrightarrow> (\<nexists>y'. u = x'\<cdot>v\<cdot>y'))" 
    by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = (length p)+s \<and>
               (\<forall>x'. (length x') < s \<longrightarrow> (\<nexists>y'. u = x'\<cdot>v\<cdot>y'))" 
    by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and>
               (\<forall>x'. (length x') < s \<and> (length x') \<ge> 0 \<longrightarrow> (\<nexists>y'. u = x'\<cdot>v\<cdot>y'))" 
    by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and>
               (\<forall>x'. (length x') < s \<and> (length x') \<ge> 0 \<longrightarrow> (\<nexists>y'. p\<cdot>u = p\<cdot>x'\<cdot>v\<cdot>y'))" 
    by blast
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and>
               (\<forall>x'. (\<nexists>y'.  (length x') < s \<and> (length x') \<ge> 0 \<and>  p\<cdot>u = p\<cdot>x'\<cdot>v\<cdot>y'))" 
    by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and>
               (\<forall>x' p'. (\<nexists>y'.  (length p') = (length p) \<and> (length x') < s \<and>
                  (length x') \<ge> 0 \<and>  w = p'\<cdot>x'\<cdot>v\<cdot>y'))" 
    by (metis (no_types, opaque_lifting) append_eq_append_conv)
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and>
               (\<forall>x' p'. (\<nexists>y' x''.  (length p') = (length p) \<and> x''=p'\<cdot>x' \<and> (length x') < s \<and>
                  (length x') \<ge> 0 \<and>  w = x''\<cdot>v\<cdot>y'))" 
    by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and>
               (\<forall>x' p'. (\<nexists>y' x''.  (length p') = (length p) \<and> x''=p'\<cdot>x' \<and> (length x'') < s+i \<and>
                  (length x'') \<ge> i \<and>  w = x''\<cdot>v\<cdot>y'))" 
    by force
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and>
               (\<forall>x'. (\<nexists>y' x''.  (length x'') < s+i \<and> (length x'') \<ge> i \<and>  w = x''\<cdot>v\<cdot>y'))"  
    by (metis Words.drop_append)
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and>
               (\<forall>x''. (\<nexists>y'.  (length x'') < s+i \<and> (length x'') \<ge> i \<and>  w = x''\<cdot>v\<cdot>y'))"  
    by force
  then have "\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = i+s \<and>
               (\<forall>x''. (\<nexists>y'.  (length x'') < s+i \<and> (length x'') \<ge> i \<and> w = x''\<cdot>v\<cdot>y'))"  
    by (metis append.assoc)
  then have "\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = s+i \<and> 
               (\<forall>x'. (length x') < s+i \<and> (length x') \<ge> i \<longrightarrow> (\<nexists>y'.   w = x'\<cdot>v\<cdot>y'))"  
    by (metis add.commute)
  then show ?thesis .
qed


subsection "Replacement"

lemma replace_epsilon: "replace w \<epsilon> u = u\<cdot>w"
  apply(auto simp add: option.case_eq_if)
   apply (metis find_fac.elims find_fac_epsilon option.distinct(1))
  by (metis append_Nil cancel_comm_monoid_add_class.diff_cancel drop0 find_fac.simps find_fac_epsilon option.sel take0)

lemma replace_id_if_not_contains: "\<not>contains w v \<Longrightarrow> replace w v u = w"
  using contains_iff_find_index by fastforce

theorem replace_factor: "contains w v \<Longrightarrow> \<exists>x y. (w= x\<cdot>v\<cdot>y \<and> replace w v u = x\<cdot>u\<cdot>y)"
  apply(auto simp add: option.case_eq_if prefix_def )
   apply (metis contains_iff_find_fac find_fac.simps option.distinct(1))
  by (metis append.assoc append_eq_conv_conj find_fac.simps find_fac_returns_first length_append)

theorem replace_first_factor: "contains w v \<Longrightarrow> \<exists>x y. replace w v u = x\<cdot>u\<cdot>y \<and> w = x\<cdot>v\<cdot>y \<and> (\<forall> x'. (length x') < (length x) \<longrightarrow> (\<nexists>y'. w=x'\<cdot>v\<cdot>y'))"
  apply(auto simp add: option.case_eq_if find_returns_factor_at)
  apply (metis contains_iff_find_fac find_fac.simps option.distinct(1))
  using replace.elims find_fac.elims find_fac_returns_first  append_eq_conv_conj length_append 
  by (smt (verit, ccfv_threshold) append.assoc) (* todo *)




end






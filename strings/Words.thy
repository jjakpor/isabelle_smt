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

value "''abc'' \<le> ''d''"

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

definition find_fac:: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word option" where
  "find_fac w v = List.find (prefix v) (rev (suffixes w))"

definition find_index:: "'a word \<Rightarrow> 'a word \<Rightarrow> nat option" where
  "find_index w v = (case find_fac w v of Some r \<Rightarrow>  Some ((length w) - (length r)) | None \<Rightarrow> None)"


definition replace:: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> 'a word" where
  "replace w v u = (case find_index w v of Some i \<Rightarrow> (take i w)\<cdot>u\<cdot>(drop (i+(length v)) w) | None => w)"

lemma drop_append: "n \<le> \<bar>w\<bar> \<and> x = drop n w  \<Longrightarrow> \<exists>v. ((w = v\<cdot>x) \<and> (length v) = n)"
  apply(induct w)
   apply auto
  by (metis append_take_drop_id le_Suc_eq length_Cons length_take min_def not_less_eq_eq)


fun factors:: "'a word \<Rightarrow> nat \<Rightarrow> 'a word list" where
  "factors w n  = [(w[i; i+n]). i\<leftarrow>[0..<\<bar>w\<bar>+1-n]]"

definition enum_factors:: "'a word \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a word) list"
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
  by (auto simp add: find_fac_def find_Some_iff first_suffix_is_word prefix_def)

lemma find_fac_epsilon: "find_fac w \<epsilon> = Some w"
  unfolding prefix_def by (metis append_Nil find_prefix)

lemma find_fac_in_epsilon: "find_fac \<epsilon> w = Some v \<Longrightarrow> w = \<epsilon>"
  by (auto simp add: find_fac_def split: if_splits)

lemma find_returns_factor_at:
  assumes "find_fac w v = Some s"
  shows "\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = (length w) - (length s)"
  using assms
  apply(auto simp add: prefix_def suffix_def find_fac_def)
  by (metis add_diff_cancel_right' find_Some_iff length_append nth_mem prefix_def suffix_def suffixes_rev_set)

lemma contains_iff_find_fac: "(\<exists>u. find_fac w v = Some u) \<longleftrightarrow> contains w v"
  apply(auto)
  using contains_iff_fac find_returns_factor_at apply blast
  apply(auto simp add: contains_iff_fac)
  by (metis find_None_iff2 find_fac_def in_set_suffixes not_Some_eq rev_suffixes sublist_altdef')

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
  apply(auto simp add:  find_fac_def find_Some_iff prefix_def)
  by (metis add_diff_cancel_right' length_append length_rev length_suffixes suffix_if)

lemma find_finds_factor:"find_index w v = Some r \<Longrightarrow> \<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = r"
  unfolding find_index_def
  apply(auto simp add:  option.case_eq_if split: if_splits)
  using find_returns_factor_at by blast

lemma contains_iff_find_index: "(\<exists>r. find_index w v = Some r) \<longleftrightarrow> contains w v"
  apply(auto simp add: find_index_def)
  using contains_iff_find_fac by force+

lemma find_index_of_suffix:
  assumes "find_index (drop i w) v = Some r"
    and "i \<le> (length w)"
  shows "\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = r + i"
proof -
  from assms have "\<exists>s. find_fac (drop  i w) v = Some s"   
    by (metis find_index_def option.collapse option.distinct(1) option.simps(4)) 
  then have "\<exists>s. find_fac (drop i w) v = Some s \<and> r = (length (drop i w)) - (length s)"   
    by (metis assms(1) find_index_def option.case(2) option.inject)
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
  using assms unfolding find_index_def
  apply(auto simp add: option.case_eq_if split: if_splits)
  using find_fac_returns_first by metis

theorem find_prefix_is_word: "find_fac (v\<cdot>u) v = Some (v\<cdot>u)"
  by (auto simp add: find_fac_def  prefix_def find_Some_iff first_suffix_is_word)

theorem find_prefix_index_is_0: "find_index (v\<cdot>u) v = Some 0"
  unfolding find_index_def using find_prefix_is_word by (metis diff_self_eq_0 option.simps(5))

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
  unfolding replace_def
  apply(auto simp add: option.case_eq_if)
   apply (simp add: find_fac_epsilon find_index_def)
  by (metis append_Nil drop0 find_prefix_index_is_0 option.sel take_eq_Nil2)

lemma replace_id_if_not_contains: "\<not>contains w v \<Longrightarrow> replace w v u = w"
  unfolding replace_def using contains_iff_find_index by fastforce

theorem replace_factor: "contains w v \<Longrightarrow> \<exists>x y. (w= x\<cdot>v\<cdot>y \<and> replace w v u = x\<cdot>u\<cdot>y)"
  unfolding replace_def find_index_def
  apply(auto simp add: option.case_eq_if prefix_def )
   apply (metis contains_iff_find_fac option.distinct(1))
  by (metis append.assoc append_eq_conv_conj find_returns_factor_at length_append)

theorem replace_first_factor: "contains w v \<Longrightarrow> \<exists>x y. replace w v u = x\<cdot>u\<cdot>y \<and> w = x\<cdot>v\<cdot>y \<and> (\<forall> x'. (length x') < (length x) \<longrightarrow> (\<nexists>y'. w=x'\<cdot>v\<cdot>y'))"
  apply(auto simp add: contains_iff_find_index)
  unfolding replace_def
  apply(auto simp add: option.case_eq_if contains_iff_find_index)
   apply (metis contains_iff_find_index option.distinct(1))
proof -
  assume a: "contains w v"
  obtain aas :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" and aasa :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    f2: "\<forall>as asa n. length (aas n asa as) = n \<and> aas n asa as \<cdot> asa \<cdot> aasa n asa as = as \<or> find_index as asa \<noteq> Some n"
    by (metis (no_types) find_finds_factor)
  obtain nn :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
    f3: "find_index w v = Some (nn v w)"
    using a by (meson contains_iff_find_index)
  then have "drop (nn v w + length v) w = aasa (nn v w) v w"
    using f2 by (metis append.assoc append_eq_conv_conj length_append)
  then show "\<exists>as asa. take (the (find_index w v)) w \<cdot> u \<cdot> drop (the (find_index w v) + length v) w = as \<cdot> u \<cdot> asa \<and> w = as \<cdot> v \<cdot> asa \<and> (\<forall>asa. length asa < length as \<longrightarrow> (\<forall>as. w \<noteq> asa \<cdot> v \<cdot> as))"
    using f3 f2 by (metis append_eq_conv_conj find_index_returns_first option.sel)
qed

lemma get_factor_factorizes:"v=(w[i;i+n]) \<and> i\<le>\<bar>w\<bar> \<Longrightarrow> \<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = i" 
  apply(induct w)
   apply(auto)
  by (metis append_take_drop_id length_Cons length_take min.commute min_def)

lemma factors_len_ge_w:"n > \<bar>w\<bar> \<Longrightarrow> factors w n = []" 
  by auto
lemma factors_len_eq_w: "n = \<bar>w\<bar> \<Longrightarrow> factors w n = [w]" 
  by auto
lemma factors_len_0: "set (factors w 0) = {\<epsilon>}" 
  apply(induct w) by auto 

lemma factors_set:"n\<le>\<bar>w\<bar> \<Longrightarrow> set (factors w n) = {v|v i. i\<in>{..\<bar>w\<bar>-n} \<and> v=(w[i;i+n])}" 
  apply(induct n)
   apply(auto)
  by (metis Suc_diff_Suc less_Suc_eq_le less_imp_diff_less not_less_iff_gr_or_eq zero_less_diff)

lemma factor_start_index:"v = w[i; i+\<bar>v\<bar>] \<Longrightarrow> i\<le>\<bar>w\<bar>-\<bar>v\<bar> \<or> v = \<epsilon>"
  by (case_tac "i \<le> \<bar>w\<bar>-\<bar>v\<bar>", auto)


lemma factor_iff_in_factors: "v \<in> set (factors w \<bar>v\<bar>) \<longleftrightarrow> factor v w" 
proof 
  assume "v \<in> set (factors w \<bar>v\<bar>)"
  thus "factor v w" unfolding factor_iff by auto
next assume a:"factor v w"
  then have f1:"\<bar>v\<bar> \<le> \<bar>w\<bar>"  using sublist_length_le by blast
  from a have "\<exists>i. v = w[i; i+\<bar>v\<bar>]" by (auto simp add: factor_iff)
  then have "\<exists>i. v = w[i; i+\<bar>v\<bar>] \<and> i\<le>\<bar>w\<bar>-\<bar>v\<bar>" using factor_start_index by fastforce
  then have " v \<in> {u|u i. i\<in>{..\<bar>w\<bar>-\<bar>v\<bar>} \<and> u=(w[i;i+\<bar>v\<bar>])}"  using atMost_iff by blast
  thus " v \<in> set (factors w \<bar>v\<bar>)" using  factors_set f1 by blast
qed

lemma enum_factors_set:"n\<le>\<bar>w\<bar> \<Longrightarrow> set (enum_factors w n) = {(i,v)|v i. i\<in>{..\<bar>w\<bar>-n} \<and> v=(w[i;i+n])}" 
  unfolding enum_factors_def 
  by (auto simp add: in_set_enumerate_eq)


lemma factor_iff_in_enum_factors:"\<exists>i. (i, v) \<in> set (enum_factors w \<bar>v\<bar>) \<longleftrightarrow> v \<in> set (factors w \<bar>v\<bar>)"
  unfolding enum_factors_def 
  apply(auto simp add:  enumerate_eq_zip in_set_impl_in_set_zip2 in_set_zipE )
  by (metis (no_types, lifting) atLeastLessThan_upt in_set_impl_in_set_zip2 length_map list.set_map set_zip_rightD)

lemma enum_factors_atmost_len: "(i, v) \<in> set (enum_factors w n) \<Longrightarrow> i\<le>\<bar>w\<bar> \<and> \<bar>v\<bar> \<le> \<bar>w\<bar>"
  unfolding enum_factors_def
  apply(induct n)
   apply (auto simp add: in_set_enumerate_eq)
  by (metis diff_is_0_eq' length_map length_upt less_Suc_eq_le list.size(3) map_nth nth_Cons_0 nth_append nth_map_upt zero_less_Suc)



lemma factors_len: "n\<ge>1 \<Longrightarrow> \<bar>(factors w n)\<bar> \<le> \<bar>w\<bar>" 
  apply(induct w) by (auto)

lemma enum_factors_len: "\<bar>(factors w n)\<bar> = \<bar>(enum_factors w n)\<bar>"
  by (simp add: enum_factors_def)

lemma enum_factors_factorization:"(i, v) \<in> set(enum_factors w \<bar>v\<bar>) \<Longrightarrow> \<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = i"
proof -
  assume a:"(i, v) \<in> set(enum_factors w \<bar>v\<bar>)"
  then have f1:"i\<le>\<bar>w\<bar> \<and> \<bar>v\<bar> \<le> \<bar>w\<bar>" by (simp add: enum_factors_atmost_len)
  from a have "(i, v) \<in> {(i,v)|v i. i\<in>{..\<bar>w\<bar>-\<bar>v\<bar>} \<and> v=(w[i;i+\<bar>v\<bar>])}" using enum_factors_set f1 by blast
  then show ?thesis  using f1 get_factor_factorizes by blast
qed

lemma enum_factors_factorization2:"(i, v) \<notin> set(enum_factors w \<bar>v\<bar>) \<Longrightarrow> \<not>(\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = i)" 
proof (case_tac "\<bar>v\<bar> \<le> \<bar>w\<bar>")
  assume b:"\<not>(i, v) \<in> set(enum_factors w \<bar>v\<bar>)"
  assume a:"\<bar>v\<bar> \<le> \<bar>w\<bar>"
  then have "\<not> (i, v) \<in> {(i,v)|v i. i\<in>{..\<bar>w\<bar>-\<bar>v\<bar>} \<and> v=(w[i;i+\<bar>v\<bar>])}" using enum_factors_set b a by blast
  then have "\<forall>i' v'.  i\<in>{..\<bar>w\<bar>-\<bar>v\<bar>} \<and> v=(w[i;i+\<bar>v\<bar>]) \<longrightarrow> i'\<noteq>i \<or> v'\<noteq>v" using enum_factors_set a by blast
  then show "\<nexists>x y. w = x \<cdot> v \<cdot> y \<and> \<bar>x\<bar> = i" by auto
next 
  assume b:"\<not>(i, v) \<in> set(enum_factors w \<bar>v\<bar>)"
  assume a:"\<not>\<bar>v\<bar> \<le> \<bar>w\<bar>"
  then show "\<nexists>x y. w = x \<cdot> v \<cdot> y \<and> \<bar>x\<bar> = i" by auto
qed

lemma enum_factors_iff_factorization:"(i, v) \<in> set(enum_factors w \<bar>v\<bar>) \<longleftrightarrow> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = i)"
  by (meson enum_factors_factorization enum_factors_factorization2)


lemma enum_factors_nth: "i<\<bar>(enum_factors w n)\<bar> \<Longrightarrow> fst ((enum_factors w n) ! i) = i" 
  by (metis add_0 enum_factors_def enum_factors_len fstI nth_enumerate_eq)


lemma factor_index_some_iff: "factor_index w v = Some n \<Longrightarrow> find (\<lambda>(i,v'). v'=v) (enum_factors w \<bar>v\<bar>) = Some (n, v)"
  apply(auto)
  by (metis (mono_tags, lifting) find_Some_iff snd_conv split_beta)


lemma factor_index_first:"factor_index w v = Some n \<Longrightarrow> (\<forall>n'. n' < n \<longrightarrow> \<not>(\<exists>x' y'. w = x'\<cdot>v\<cdot>y' \<and> n' = \<bar>x'\<bar>))"
proof -
  assume "factor_index w v = Some n"
  then have "find (\<lambda>(i,v'). v'=v) (enum_factors w \<bar>v\<bar>) = Some (n, v)" using factor_index_some_iff by blast
  then have "(\<exists>k<\<bar>(enum_factors w \<bar>v\<bar>)\<bar>. (\<lambda>(i,v'). v'=v) ((enum_factors w \<bar>v\<bar>) ! k) \<and> (n, v) = (enum_factors w \<bar>v\<bar>) ! k \<and> (\<forall>j<k. \<not> (\<lambda>(i,v'). v'=v) ((enum_factors w \<bar>v\<bar>) ! j)))" using find_Some_iff  by (metis (no_types, lifting))
  then have "(\<exists>k<\<bar>(enum_factors w \<bar>v\<bar>)\<bar>. (n, v) = (enum_factors w \<bar>v\<bar>) ! k \<and> (\<forall>j<n. \<not> (\<lambda>(i,v'). v'=v) ((enum_factors w \<bar>v\<bar>) ! j)))" by (metis  enum_factors_nth fst_conv)
  then have "(\<exists>k<\<bar>(enum_factors w \<bar>v\<bar>)\<bar>. (n,v) \<in> set (enum_factors w \<bar>v\<bar>) \<and> (\<forall>j<n.  \<not> (j,v) \<in> set (enum_factors w \<bar>v\<bar>)))"  by (metis (mono_tags, lifting) case_prodI enum_factors_nth fst_conv in_set_conv_nth)
  then have "(\<forall>j<n.  \<not> (j,v) \<in> set (enum_factors w \<bar>v\<bar>))" by auto
  thus ?thesis  using enum_factors_iff_factorization sublist_length_le by blast
qed








end






theory Words      
  imports Main "HOL-Library.Sublist" "HOL-Library.List_Lexorder" HOL.Groups "HOL-Library.Multiset"
begin


type_synonym 'a word = "'a list"
no_notation append (infixr "@" 65)
notation append (infixr "\<cdot>" 65)
notation Nil ("\<epsilon>")

notation length ("\<bar>_\<bar>")
no_notation Groups.abs_class.abs  ("\<bar>_\<bar>")

instantiation char::linorder begin
definition less_char::"char \<Rightarrow> char \<Rightarrow> bool" where "less_char a b \<equiv> ((of_char a)::nat) < ((of_char b)::nat)" 
definition less_eq_char::"char \<Rightarrow> char \<Rightarrow> bool" where "less_eq_char a b \<equiv> ((of_char a)::nat) \<le> ((of_char b)::nat)"
instance apply(standard)
  using less_char_def less_eq_char_def by auto
end

value "''abc'' \<le> ''d''"

primrec concat_all:: "'a word list \<Rightarrow> 'a word"
  where
  "concat_all [] = \<epsilon>" |
  "concat_all (w#ws) = w\<cdot>(concat_all ws)"

abbreviation factor:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "factor \<equiv> sublist"

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




definition replace::"'a word \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> 'a word" where
"replace w v u = (case find_index w v of Some i \<Rightarrow> (take i w)\<cdot>u\<cdot>(drop (i+(length v)) w) | None => w)"

lemma drop_append:"n \<le> \<bar>w\<bar> \<and> x = drop n w  \<Longrightarrow> EX v. ((w = v\<cdot>x) \<and> (length v) = n)"
  apply(induct w)
   apply auto
  by (metis append_take_drop_id le_Suc_eq length_Cons length_take min_def not_less_eq_eq)



subsection "Factorization"


lemma factor_iff:"factor v w \<longleftrightarrow> (\<exists>i. v = (w[i; i+(length v)]))"
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

lemma []: "w[0;1] = take 1 w"  by auto
lemma []:"i \<ge> j \<Longrightarrow> w[i;j] = \<epsilon>" by auto
lemma []:"i\<ge> (length w) \<Longrightarrow> w[i;j] = \<epsilon>" by auto
lemma []: "\<epsilon>[i;j] = \<epsilon>" by auto
lemma []: "w[i;i] = \<epsilon>" by auto
lemma []: "j \<ge> (length w) \<Longrightarrow> w[0;j] = w" by auto
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
  
lemma if_contains_then_fac_has_prefix:"(contains w d) \<Longrightarrow> EX x y. w = x\<cdot>y \<and> (prefix d y)"
  by (auto simp add: contains_iff_fac prefix_def sublist_def)


lemma epsilon_contains_epsilon[simp]: "contains \<epsilon> v \<Longrightarrow> v = \<epsilon>" by auto


subsection "Searching Factors"


lemma rev_suffixes:"set (suffixes w) = set (rev (suffixes w))"  by auto

lemma suffixes_set:"x \<in> set (suffixes w) \<Longrightarrow> suffix x w"
  by (auto simp add: suffix_def)
  

lemma suffixes_rev_set:"x \<in> set (rev (suffixes w)) \<Longrightarrow> suffix x w"
  by (auto simp add: suffix_def)
  

lemma first_suffix_is_word:"rev (suffixes w)!0 = w"
  by (metis Nil_is_rev_conv hd_conv_nth hd_rev last_suffixes suffixes_not_Nil)

lemma find_prefix: "find_fac (v\<cdot>w) v = Some (v\<cdot>w)"
  apply(auto simp add: find_fac_def)
  by (auto simp add: find_Some_iff first_suffix_is_word prefix_def)
 

lemma find_fac_epsilon: "find_fac w \<epsilon> = Some w"
  unfolding  prefix_def
  by (metis append_Nil find_prefix)
  
lemma find_fac_in_epsilon: "find_fac \<epsilon> w = Some v \<Longrightarrow> w = \<epsilon>"
  by (auto simp add: find_fac_def split: if_splits)
  

lemma find_returns_factor_at:"find_fac w v = Some s \<Longrightarrow> EX x y. w = x\<cdot>v\<cdot>y \<and> (length x) = (length w)-(length s)"
  apply(auto simp add: prefix_def suffix_def find_fac_def)
  by (metis add_diff_cancel_right' find_Some_iff length_append nth_mem prefix_def suffix_def suffixes_rev_set)


lemma contains_iff_find_fac: "(EX u. find_fac w v = Some u) \<longleftrightarrow> contains w v"
  apply(auto)
  using contains_iff_fac find_returns_factor_at apply blast
  apply(auto simp add: contains_iff_fac)
  by (metis find_None_iff2 find_fac_def in_set_suffixes not_Some_eq rev_suffixes sublist_altdef')


lemma suffixes_count: "length (suffixes w) = (length w)+1"
  apply(induct_tac w) by(auto)

lemma suffixes_rev_count[simp]: "length (rev (suffixes w)) = (length (suffixes w))"
  by auto

lemma suffix_length: "i < length (suffixes w) \<Longrightarrow> length ((suffixes w)!i) = i"
  apply(auto)
  apply(induct w)
  by(auto simp add: nth_append)


lemma suffix_rev_length: "i < length (rev (suffixes w)) \<Longrightarrow> length ((rev (suffixes w))!i) = (length w) - i"
  apply(auto)
  apply(induct w)
  by (auto simp add: suffix_length  less_Suc_eq_0_disj  rev_nth, auto simp add: suffix_length)

lemma suffix_if:"v = rev ((suffixes w))!j \<and> j < length (rev ((suffixes w))) \<longleftrightarrow> (\<exists>x. w = x\<cdot>v \<and> (length x) = j)"
  apply(auto)
  apply (metis add_diff_cancel_right' add_diff_inverse_nat length_append length_rev length_suffixes not_less_eq nth_mem suffix_def suffix_rev_length suffixes_rev_set)
  by (simp add: first_suffix_is_word nth_append suffixes_append)


lemma find_fac_returns_first: "find_fac w v = Some s \<Longrightarrow> EX x y. w = x\<cdot>v\<cdot>y \<and> (length x) = (length w) - (length s) \<and> (\<forall> x'. (length x')<(length x) \<longrightarrow> (\<nexists>y'. w = x'\<cdot>v\<cdot>y'))" 
  apply(auto simp add:  find_fac_def find_Some_iff prefix_def)
  by (metis add_diff_cancel_right' length_append length_rev length_suffixes suffix_if)


lemma find_finds_factor:"find_index w v = Some r \<Longrightarrow> EX x y. w = x\<cdot>v\<cdot>y \<and> (length x) = r"
  unfolding find_index_def
  apply(auto simp add:  option.case_eq_if split: if_splits)
  using find_returns_factor_at by blast


lemma contains_iff_find_index: "(EX r. find_index w v = Some r) \<longleftrightarrow> contains w v"
  apply(auto simp add: find_index_def)
  using contains_iff_find_fac by force+


lemma find_index_of_suffix: "find_index (drop i w) v = Some r \<and> i \<le> (length w) \<Longrightarrow> \<exists>x y. w = x\<cdot>v\<cdot>y \<and>  (length x) = r+i"
proof -
  assume a:"find_index (drop i w) v  = Some r \<and> i \<le> (length w)"
  then have "EX s. find_fac (drop  i w) v = Some s"   by (metis find_index_def option.collapse option.distinct(1) option.simps(4)) 
  then have "EX s. find_fac (drop i w) v = Some s \<and> r = (length (drop i w)) - (length s)"   by (metis a find_index_def option.case(2) option.inject)
  then have "EX s x y. (drop  i w) = x\<cdot>v\<cdot>y \<and> (length x) = (length (drop  i w))-(length s) \<and>  r = (length (drop  i w)) - (length s)"  by (metis Ex_list_of_length find_returns_factor_at)
  then have "EX s x y. (drop  i w) = x\<cdot>v\<cdot>y \<and> (length x) = r \<and> r = (length (drop  i w)) - (length s)"  by auto
  then have "EX s x y. (drop  i w) = x\<cdot>v\<cdot>y \<and> i \<le> (length w) \<and> (length x) = r \<and> r = (length (drop  i w)) - (length s)" using a  by auto
  then have "EX s x y. (\<exists>x'. w = x'\<cdot>x\<cdot>v\<cdot>y \<and> (length x') = i) \<and> (length x) = r  \<and> r = (length (drop  i w)) - (length s)"  by (metis Words.drop_append)
  then have "EX s x y x'. w = x'\<cdot>x\<cdot>v\<cdot>y \<and> (length x') = i \<and> (length x) = r  \<and> r = (length (drop  i w)) - (length s)" by auto
  then have "EX x y x'. w = x'\<cdot>x\<cdot>v\<cdot>y \<and> (length x') = i \<and> (length x) = r" by auto
  then have "EX x y. w = x\<cdot>v\<cdot>y \<and> (length x) = r + i"  by (metis add.commute append.assoc length_append)
  then show ?thesis   by (simp)
qed


lemma find_index_returns_first: "find_index w v = Some s \<Longrightarrow> EX x y. w = x\<cdot>v\<cdot>y \<and> (length x) = s \<and> (\<forall>x'. (length x') < s \<longrightarrow> (\<nexists>y'. w = x'\<cdot>v\<cdot>y'))" 
  unfolding find_index_def
  apply(auto simp add: option.case_eq_if split: if_splits)
  using find_fac_returns_first by metis
  

theorem find_prefix_is_word: "find_fac (v\<cdot>u) v = Some (v\<cdot>u)"
  by (auto simp add:  find_fac_def  prefix_def find_Some_iff first_suffix_is_word)

theorem find_prefix_index_is_0: "find_index (v\<cdot>u) v = Some 0"
  unfolding find_index_def
  using find_prefix_is_word by (metis diff_self_eq_0 option.simps(5))



lemma find_index_of_suffix_returns_first: "i \<le> (length w) \<and> find_index (drop i w) v = Some s \<Longrightarrow> EX x y. w = x\<cdot>v\<cdot>y \<and> (length x) = (s+i) \<and> (\<forall>x'. ((length x') < (s+i) \<and> (length x') \<ge> i) \<longrightarrow> (\<nexists>y'. w = x'\<cdot>v\<cdot>y'))" 
proof -
  assume a:"i \<le> (length w) \<and> find_index (drop i w) v = Some s"
  then have "\<exists>p u. w = p\<cdot>u \<and> length p = i \<and> find_index u v = Some s" using drop_append by fastforce
  then have "\<exists>p u. w = p\<cdot>u \<and> length p = i \<and> (EX x y. u = x\<cdot>v\<cdot>y \<and> (length x) = s \<and> (\<forall>x'. (length x') < s \<longrightarrow> (\<nexists>y'. u = x'\<cdot>v\<cdot>y')))" using find_index_returns_first by metis
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> u = x\<cdot>v\<cdot>y \<and> (length x) = s \<and> (\<forall>x'. (length x') < s \<longrightarrow> (\<nexists>y'. u = x'\<cdot>v\<cdot>y'))" by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = (length p)+s \<and> (\<forall>x'. (length x') < s \<longrightarrow> (\<nexists>y'. u = x'\<cdot>v\<cdot>y'))" by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x'. (length x') < s \<and> (length x') \<ge> 0 \<longrightarrow> (\<nexists>y'. u = x'\<cdot>v\<cdot>y'))" by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x'. (length x') < s \<and> (length x') \<ge> 0 \<longrightarrow> (\<nexists>y'. p\<cdot>u = p\<cdot>x'\<cdot>v\<cdot>y'))" by blast
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x'. (\<nexists>y'.  (length x') < s \<and> (length x') \<ge> 0 \<and>  p\<cdot>u = p\<cdot>x'\<cdot>v\<cdot>y'))" by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x' p'. (\<nexists>y'.  (length p') = (length p) \<and> (length x') < s \<and> (length x') \<ge> 0 \<and>  w = p'\<cdot>x'\<cdot>v\<cdot>y'))" by (metis (no_types, opaque_lifting) append_eq_append_conv)
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x' p'. (\<nexists>y' x''.  (length p') = (length p) \<and> x''=p'\<cdot>x' \<and> (length x') < s \<and> (length x') \<ge> 0 \<and>  w = x''\<cdot>v\<cdot>y'))" by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x' p'. (\<nexists>y' x''.  (length p') = (length p) \<and> x''=p'\<cdot>x' \<and> (length x'') < s+i \<and> (length x'') \<ge> i \<and>  w = x''\<cdot>v\<cdot>y'))" by force
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x'. (\<nexists>y' x''.  (length x'') < s+i \<and> (length x'') \<ge> i \<and>  w = x''\<cdot>v\<cdot>y'))"  by (metis Words.drop_append)
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x''. (\<nexists>y'.  (length x'') < s+i \<and> (length x'') \<ge> i \<and>  w = x''\<cdot>v\<cdot>y'))"  by force
  then have "\<exists>x y.  w = x\<cdot>v\<cdot>y \<and> (length x) = i+s \<and> (\<forall>x''. (\<nexists>y'.  (length x'') < s+i \<and> (length x'') \<ge> i \<and>  w = x''\<cdot>v\<cdot>y'))"  by (metis append.assoc)
  then have "\<exists>x y.  w = x\<cdot>v\<cdot>y \<and> (length x) = s+i \<and> (\<forall>x'. (length x') < s+i \<and> (length x') \<ge> i \<longrightarrow>(\<nexists>y'.   w = x'\<cdot>v\<cdot>y'))"  by (metis add.commute)
  then show ?thesis  .
qed




subsection "Replacement"

lemma replace_epsilon: "replace w \<epsilon> u = u\<cdot>w"
  unfolding replace_def
  apply(auto simp add: option.case_eq_if)
   apply (simp add: find_fac_epsilon find_index_def)
  by (metis append_Nil drop0 find_prefix_index_is_0 option.sel take_eq_Nil2)

lemma replace_id_if_not_contains:"\<not>contains w v \<Longrightarrow> replace w v u = w"
  unfolding replace_def
  using contains_iff_find_index  by fastforce


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
  

end





